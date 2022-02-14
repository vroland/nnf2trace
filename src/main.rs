use clap::Parser;
use std::collections::{BTreeSet, HashMap};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

type NodeIndex = usize;
type ClauseIndex = usize;
type Lit = i64;
type Var = i64;

#[derive(Debug)]
enum NNFNode {
    Or {
        id: NodeIndex,
        children: Vec<NodeIndex>,
        entailed: Vec<ClauseIndex>,
    },
    And {
        id: NodeIndex,
        children: Vec<NodeIndex>,
        entailed: Vec<ClauseIndex>,
        lits: Vec<Lit>,
    },
    True(NodeIndex),
    False(NodeIndex),
}

impl NNFNode {
    pub fn add_child(&mut self, child: NodeIndex) {
        match self {
            NNFNode::Or {
                ref mut children, ..
            } => children.push(child),
            NNFNode::And {
                ref mut children, ..
            } => children.push(child),
            NNFNode::True(_) => panic! {"cannot add child to top node!"},
            NNFNode::False(_) => panic! {"cannot add child to bottom node!"},
        }
    }

    pub fn set_entailed_clauses(&mut self, clauses: &[ClauseIndex]) {
        match self {
            NNFNode::Or {
                ref mut entailed, ..
            } => entailed.extend_from_slice(clauses),
            NNFNode::And {
                ref mut entailed, ..
            } => entailed.extend_from_slice(clauses),
            NNFNode::True(_) => panic! {"top nodes don't have entailed clauses!"},
            NNFNode::False(_) => panic! {"bottom nodes don't have entailed clauses!"},
        }
    }

    pub fn children(&self) -> &[NodeIndex] {
        match self {
            NNFNode::Or { ref children, .. } => children,
            NNFNode::And { ref children, .. } => children,
            NNFNode::True(_) => &[],
            NNFNode::False(_) => &[],
        }
    }

    pub fn entailed(&self) -> &[ClauseIndex] {
        match self {
            NNFNode::Or { ref entailed, .. } => entailed,
            NNFNode::And { ref entailed, .. } => entailed,
            NNFNode::True(_) => &[],
            NNFNode::False(_) => &[],
        }
    }

    pub fn children_mut(&mut self) -> &mut [NodeIndex] {
        match self {
            NNFNode::Or {
                ref mut children, ..
            } => children,
            NNFNode::And {
                ref mut children, ..
            } => children,
            NNFNode::True(_) => &mut [],
            NNFNode::False(_) => &mut [],
        }
    }

    pub fn id(&self) -> NodeIndex {
        match self {
            NNFNode::Or { ref id, .. } => *id,
            NNFNode::And { ref id, .. } => *id,
            NNFNode::True(id) => *id,
            NNFNode::False(id) => *id,
        }
    }
}

#[derive(Debug)]
struct NNFTree {
    root: NodeIndex,
    nodes: HashMap<NodeIndex, NNFNode>,
    max_id: usize,
    clauses: Vec<Vec<Lit>>,
}

impl NNFTree {
    fn issue_new_id(&mut self) -> NodeIndex {
        self.max_id += 1;
        self.max_id
    }

    fn children_recursive(&self, node: NodeIndex) -> Vec<NodeIndex> {
        let mut stack = vec![node];
        let mut visited = vec![];
        while let Some(n) = stack.pop() {
            visited.push(n);
            stack.extend_from_slice(self.nodes.get(&n).unwrap().children());
        }
        visited
    }

    pub fn varsof(&self, node: NodeIndex) -> BTreeSet<Var> {
        let mut vars = BTreeSet::new();
        let nodes = self.children_recursive(node);
        for n in nodes {
            match self.nodes.get(&n).unwrap() {
                NNFNode::And { ref lits, .. } => vars.extend(lits.iter().map(|l| l.abs())),
                NNFNode::Or { .. } | NNFNode::True(_) | NNFNode::False(_) => (),
            }
        }
        vars
    }

    fn clone_subtree(&mut self, node: NodeIndex) -> NodeIndex {
        let new_id = self.issue_new_id();
        match self.nodes.get(&node).unwrap() {
            NNFNode::And {
                id: _,
                ref children,
                ref lits,
                ..
            } => {
                let new_node = NNFNode::And {
                    id: new_id,
                    lits: lits.clone(),
                    children: children
                        .clone()
                        .drain(..)
                        .map(|c| self.clone_subtree(c))
                        .collect(),
                    entailed: vec![],
                };
                self.nodes.insert(new_id, new_node);
                new_id
            }
            NNFNode::Or {
                id: _,
                ref children,
                ..
            } => {
                let new_node = NNFNode::Or {
                    id: new_id,
                    entailed: vec![],
                    children: children
                        .clone()
                        .drain(..)
                        .map(|c| self.clone_subtree(c))
                        .collect(),
                };
                self.nodes.insert(new_id, new_node);
                new_id
            }
            NNFNode::True(id) => *id,
            NNFNode::False(id) => *id,
        }
    }

    pub fn print_formula(&self, node: NodeIndex, depth: usize) {
        match self.nodes.get(&node).unwrap() {
            NNFNode::True(id) => println! {"{}{}: T", "  ".repeat(depth), id},
            NNFNode::False(id) => println! {"{}{}: F", "  ".repeat(depth), id},
            NNFNode::And {
                id,
                ref children,
                ref lits,
                ..
            } => {
                println! {"{}{}: A {:?}", "  ".repeat(depth), id, lits}
                for child in children {
                    self.print_formula(*child, depth + 1);
                }
            }
            NNFNode::Or {
                id, ref children, ..
            } => {
                println! {"{}{}: O", "  ".repeat(depth), id}
                for child in children {
                    self.print_formula(*child, depth + 1);
                }
            }
        }
    }

    fn satisfiable(&self, node: NodeIndex, assumption: &[Lit]) -> bool {
        match self.nodes.get(&node).unwrap() {
            NNFNode::True(_) => true,
            NNFNode::False(_) => false,
            NNFNode::And {
                ref children,
                ref lits,
                ..
            } => {
                if lits.iter().any(|l| assumption.contains(&-l)) {
                    false
                } else {
                    children.iter().all(|c| self.satisfiable(*c, assumption))
                }
            }
            NNFNode::Or { ref children, .. } => {
                children.iter().any(|c| self.satisfiable(*c, assumption))
            }
        }
    }

    pub fn is_entailed(&self, node: NodeIndex, clause: &[Lit]) -> bool {
        let negated: Vec<_> = clause.iter().map(|l| -l).collect();
        !self.satisfiable(node, &negated)
    }

    fn smooth_recurse(
        &mut self,
        node: NodeIndex,
        smooth_nodes: &HashMap<Var, NodeIndex>,
        missing: &BTreeSet<Var>,
    ) {
        match self.nodes.get(&node).unwrap() {
            NNFNode::And { ref children, .. } => {
                let mut partition: Vec<BTreeSet<Var>> =
                    children.iter().map(|_c| BTreeSet::new()).collect();

                // Partition missing variables according to children.
                // We assume assigned variables for each child are non-overlapping,
                // as explained in the paper.
                for (i, child) in children.iter().enumerate() {
                    for cl in self.nodes.get(child).unwrap().entailed() {
                        for var in self.clauses[*cl].iter().map(|l| l.abs()) {
                            if missing.contains(&var) {
                                partition[i].insert(var);
                            }
                        }
                    }
                }

                // variables to introduce now
                let introduce: Vec<_> = missing
                    .iter()
                    .filter(|v| partition.iter().all(|p| !p.contains(v)))
                    .collect();

                // is this a conflict node?
                let conflict = children
                    .iter()
                    .any(|c| matches! {self.nodes.get(c), Some(NNFNode::False(_))});

                if !conflict {
                    let original_children = children.clone();
                    for (i, child) in original_children.iter().enumerate() {
                        self.smooth_recurse(*child, smooth_nodes, &partition[i]);
                    }

                    for var in introduce {
                        let smooth_id = smooth_nodes.get(var).unwrap();
                        if !original_children.contains(smooth_id) {
                            self.nodes.get_mut(&node).unwrap().add_child(*smooth_id)
                        }
                    }
                }
            }

            NNFNode::Or { ref children, .. } => {
                if let [child1, child2] = &children[..] {
                    let (cid1, cid2) = (*child1, *child2);
                    let c1v = self.varsof(*child1);
                    let c2v = self.varsof(*child2);

                    let mut c1m: BTreeSet<Var> = c2v.difference(&c1v).copied().collect();
                    let mut c2m: BTreeSet<Var> = c1v.difference(&c2v).copied().collect();
                    c1m.extend(missing);
                    c2m.extend(missing);
                    self.smooth_recurse(cid1, smooth_nodes, &c1m);
                    self.smooth_recurse(cid2, smooth_nodes, &c2m);
                } else {
                    panic! {"a decision node must have exactly two children!"};
                }
            }
            NNFNode::True(_) | NNFNode::False(_) => (),
        }
    }

    pub fn smooth(&mut self, missing: BTreeSet<Var>) {
        let mut varnode_map = HashMap::new();
        let tn = NNFNode::True(self.issue_new_id());
        for v in missing.iter().chain(self.varsof(self.root).iter()).copied() {
            let child1 = NNFNode::And {
                id: self.issue_new_id(),
                children: vec![tn.id()],
                lits: vec![v],
                entailed: vec![],
            };
            let child2 = NNFNode::And {
                id: self.issue_new_id(),
                children: vec![tn.id()],
                lits: vec![-v],
                entailed: vec![],
            };
            let varnode = NNFNode::Or {
                id: self.issue_new_id(),
                children: vec![child1.id(), child2.id()],
                entailed: vec![],
            };
            self.nodes.insert(child1.id(), child1);
            self.nodes.insert(child2.id(), child2);
            varnode_map.insert(v, varnode.id());
            self.nodes.insert(varnode.id(), varnode);
        }
        self.nodes.insert(tn.id(), tn);
        self.smooth_recurse(self.root, &varnode_map, &missing);
    }

    pub fn entailment_annotate(&mut self, node: NodeIndex, clauses: &[ClauseIndex]) {
        let mut entailed_here = vec![];

        match self.nodes.get(&node).unwrap() {
            NNFNode::And {
                ref children,
                ref lits,
                ..
            } => {
                // split clauses that are solved
                // by the literals and remaining ones
                let mut solved = vec![];
                for cl in clauses.iter().copied() {
                    if self.clauses[cl].iter().any(|l| lits.contains(l)) {
                        solved.push(cl);
                    } else {
                        entailed_here.push(cl);
                    }
                }

                // annotate children
                for (i, child) in children.clone().into_iter().enumerate() {
                    if let NNFNode::And { ref entailed, .. } | NNFNode::Or { ref entailed, .. } =
                        self.nodes.get(&child).unwrap()
                    {
                        // this node was already encountered, do we
                        // need a clone?
                        if !entailed.is_empty() {
                            let child_entails = entailed_here
                                .iter()
                                .copied()
                                .filter(|cl| self.is_entailed(child, &self.clauses[*cl]))
                                .collect::<Vec<ClauseIndex>>();

                            // we need to clone the child
                            if entailed != &child_entails {
                                let new_child = self.clone_subtree(child);
                                eprintln! {"cloning {} to {}", child, new_child}
                                self.nodes.get_mut(&node).unwrap().children_mut()[i] = child;
                                self.entailment_annotate(new_child, &child_entails);
                            } else {
                                continue;
                            }
                        } else {
                            self.entailment_annotate(child, &entailed_here);
                        }
                    }
                }
            }
            NNFNode::Or {
                id,
                ref children,
                ref entailed,
                ..
            } => {
                entailed_here = clauses
                    .iter()
                    .copied()
                    .filter(|cl| self.is_entailed(*id, &self.clauses[*cl]))
                    .collect::<Vec<ClauseIndex>>();

                if !entailed.is_empty() {
                    eprintln! {"{}: {:?} vs {:?}", id, entailed, entailed_here}
                    assert! {&entailed_here == entailed};
                    return;
                }

                for child in children.clone() {
                    self.entailment_annotate(child, &entailed_here);
                }
            }
            NNFNode::True(_) | NNFNode::False(_) => return,
        }

        self.nodes
            .get_mut(&node)
            .unwrap()
            .set_entailed_clauses(&entailed_here[..]);
    }

    pub fn parse(clauses: Vec<Vec<Lit>>, lines: impl Iterator<Item = String>) -> Self {
        let mut nodes = HashMap::new();
        let mut arcs = vec![];
        let mut max_id = 0;

        // read lines
        for line in lines {
            if line.trim().is_empty() {
                continue;
            }

            // parse a line
            let mut split = line.split_ascii_whitespace();
            let t = split.next().unwrap();
            let id = split.next().unwrap().parse::<NodeIndex>().unwrap();
            let mut lits = split
                .map(|l| l.parse::<Lit>().unwrap())
                .collect::<Vec<Lit>>();

            // line is 0-termianted
            assert!(lits.pop() == Some(0));

            max_id = max_id.max(id);

            match t {
                "o" => nodes.insert(
                    id,
                    NNFNode::Or {
                        id,
                        children: vec![],
                        entailed: vec![],
                    },
                ),
                "a" => nodes.insert(
                    id,
                    NNFNode::And {
                        id,
                        children: vec![],
                        entailed: vec![],
                        lits,
                    },
                ),
                "t" => nodes.insert(id, NNFNode::True(id)),
                "f" => nodes.insert(id, NNFNode::False(id)),
                // no node, but an arc
                _ => {
                    let origin = t.parse::<NodeIndex>().unwrap();
                    arcs.push((origin, id, lits));
                    continue;
                }
            };
        }

        // build the tree structure
        for (origin, target, lits) in arcs.drain(..) {
            // implicit and node
            if !lits.is_empty() {
                max_id += 1;
                let id = max_id;
                let new_node = NNFNode::And {
                    id,
                    children: vec![target],
                    entailed: vec![],
                    lits,
                };
                nodes.insert(id, new_node);
                nodes.get_mut(&origin).unwrap().add_child(id);
            } else {
                nodes.get_mut(&origin).unwrap().add_child(target);
            }
        }

        let root = 1;

        // make sure the root node is a valid decision node
        if let [ref child] = nodes.get(&root).unwrap().children() {
            max_id += 1;
            let tf = NNFNode::False(max_id);
            max_id += 1;
            let root_lit = if let Some(NNFNode::And { ref lits, .. }) = nodes.get(child) {
                lits[0]
            } else {
                panic! {"root is not a decision node!"};
            };
            let otherbranch = NNFNode::And {
                id: max_id,
                children: vec![tf.id()],
                lits: vec![-root_lit],
                entailed: vec![],
            };
            nodes.get_mut(&root).unwrap().add_child(otherbranch.id());
            nodes.insert(tf.id(), tf);
            nodes.insert(otherbranch.id(), otherbranch);
        }

        NNFTree {
            root,
            clauses,
            nodes,
            max_id,
        }
    }
}

#[derive(Debug)]
struct CNFFormula {
    clauses: Vec<Vec<Lit>>,
    vars: usize,
}

impl CNFFormula {
    pub fn parse(lines: impl Iterator<Item = String>) -> Self {
        let mut formula = CNFFormula {
            clauses: vec![],
            vars: 0,
        };

        let mut expected_clauses = 0;

        for line in lines {
            if line.trim().is_empty() {
                continue;
            }

            // problem line
            if line.starts_with('p') {
                let mut split = line.split_whitespace();
                assert!(split.next() == Some("p"));
                assert!(split.next() == Some("cnf"));
                formula.vars = split.next().unwrap().parse().unwrap();
                expected_clauses = split.next().unwrap().parse().unwrap();
            // comment / weight line
            } else if line.starts_with('c') || line.starts_with('w') {
                continue;
            // clause
            } else {
                let mut clause = line
                    .split_ascii_whitespace()
                    .map(|s| s.parse().unwrap())
                    .collect::<Vec<Lit>>();
                assert!(clause.pop() == Some(0));
                formula.clauses.push(clause);
            }
        }
        if expected_clauses != formula.clauses.len() {
            panic! {"wrong number of clauses specified in CNF!"};
        }
        formula
    }
}

#[derive(Parser, Debug)]
#[clap(author, version, about)]
struct Args {
    /// Path to the CNF input formula.
    cnf: PathBuf,

    /// Path to the Decision-DNNF equivalent to the input formula.
    nnf: PathBuf,
}

fn main() -> std::io::Result<()> {
    let args = Args::parse();

    let formula = CNFFormula::parse(
        BufReader::new(File::open(args.cnf)?)
            .lines()
            .map(|l| l.unwrap()),
    );
    let mut nnf = NNFTree::parse(
        formula.clauses.clone(),
        BufReader::new(File::open(args.nnf)?)
            .lines()
            .map(|l| l.unwrap()),
    );

    let clause_indices: Vec<_> = formula.clauses.iter().enumerate().map(|(i, _)| i).collect();
    eprintln!("annotating...");
    nnf.entailment_annotate(nnf.root, &clause_indices);
    eprintln!("smoothing...");
    let nnf_vars = nnf.varsof(nnf.root);
    let missing = (1..=formula.vars)
        .map(|v| v as Var)
        .filter(|v| !nnf_vars.contains(v))
        .collect();
    println!("missing vars: {:?}", missing);
    nnf.smooth(missing);

    //nnf.print_formula(nnf.root, 0);
    eprintln! {"{:?}", formula};
    eprintln! {"{:?}", nnf.varsof(nnf.root)};

    Ok(())
}
