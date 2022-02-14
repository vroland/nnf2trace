use clap::Parser;
use num_bigint::BigUint;
use num_traits::identities::{One, Zero};
use std::collections::{BTreeSet, HashMap};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

type NodeIndex = usize;
type ClauseIndex = usize;
type ComponentId = usize;
type Lit = i64;
type Var = i64;

#[derive(Debug, Clone, PartialEq)]
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
            NNFNode::False(_) => panic! {"bottom nodes don't have entailed clauses!"},
        }
    }

    pub fn children(&self) -> &[NodeIndex] {
        match self {
            NNFNode::Or { ref children, .. } => children,
            NNFNode::And { ref children, .. } => children,
            NNFNode::False(_) => &[],
        }
    }

    pub fn entailed(&self) -> &[ClauseIndex] {
        match self {
            NNFNode::Or { ref entailed, .. } => entailed,
            NNFNode::And { ref entailed, .. } => entailed,
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
            NNFNode::False(_) => &mut [],
        }
    }

    pub fn id(&self) -> NodeIndex {
        match self {
            NNFNode::Or { ref id, .. } => *id,
            NNFNode::And { ref id, .. } => *id,
            NNFNode::False(id) => *id,
        }
    }
}

#[derive(Debug)]
struct NNFTree {
    root: NodeIndex,
    nodes: Vec<NNFNode>,
    max_id: usize,
    clauses: Vec<Vec<Lit>>,
}

impl NNFTree {
    fn issue_new_id(&mut self) -> NodeIndex {
        self.max_id += 1;
        self.max_id
    }

    fn add_node(&mut self, node: NNFNode) {
        if !self.nodes.len() == node.id() {
            panic! {"unordered node insert!"}
        }
        self.nodes.push(node);
    }

    fn children_recursive(&self, node: NodeIndex) -> Vec<NodeIndex> {
        let mut stack = vec![node];
        let mut visited = vec![];
        while let Some(n) = stack.pop() {
            visited.push(n);
            stack.extend_from_slice(self.nodes[n].children());
        }
        visited
    }

    pub fn varsof(&self, node: NodeIndex) -> BTreeSet<Var> {
        let mut vars = BTreeSet::new();
        let nodes = self.children_recursive(node);
        for n in nodes {
            match &self.nodes[n] {
                NNFNode::And { ref lits, .. } => vars.extend(lits.iter().map(|l| l.abs())),
                NNFNode::Or { .. } | NNFNode::False(_) => (),
            }
        }
        vars
    }

    fn clone_subtree(&mut self, node: NodeIndex) -> NodeIndex {
        let new_id = self.issue_new_id();
        match &self.nodes[node] {
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
                self.add_node(new_node);
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
                self.add_node(new_node);
                new_id
            }
            NNFNode::False(id) => *id,
        }
    }

    pub fn print_formula(&self, node: NodeIndex, depth: usize) {
        match &self.nodes[node] {
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
        match self.nodes[node] {
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
        match self.nodes[node] {
            NNFNode::And { ref children, .. } => {
                let mut partition: Vec<BTreeSet<Var>> =
                    children.iter().map(|_c| BTreeSet::new()).collect();

                // Partition missing variables according to children.
                // We assume assigned variables for each child are non-overlapping,
                // as explained in the paper.
                for (i, child) in children.iter().enumerate() {
                    for cl in self.nodes[*child].entailed() {
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
                    .any(|c| matches! {self.nodes[*c], NNFNode::False(_)});

                if !conflict {
                    let original_children = children.clone();
                    for (i, child) in original_children.iter().enumerate() {
                        self.smooth_recurse(*child, smooth_nodes, &partition[i]);
                    }

                    for var in introduce {
                        let smooth_id = smooth_nodes.get(var).unwrap();
                        if !original_children.contains(smooth_id) {
                            self.nodes[node].add_child(*smooth_id)
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
            NNFNode::False(_) => (),
        }
    }

    pub fn smooth(&mut self, missing: BTreeSet<Var>) {
        let mut varnode_map = HashMap::new();
        for v in missing.iter().chain(self.varsof(self.root).iter()).copied() {
            let child1 = NNFNode::And {
                id: self.issue_new_id(),
                children: vec![],
                lits: vec![v],
                entailed: vec![],
            };
            let child2 = NNFNode::And {
                id: self.issue_new_id(),
                children: vec![],
                lits: vec![-v],
                entailed: vec![],
            };
            let varnode = NNFNode::Or {
                id: self.issue_new_id(),
                children: vec![child1.id(), child2.id()],
                entailed: vec![],
            };
            varnode_map.insert(v, varnode.id());
            self.add_node(child1);
            self.add_node(child2);
            self.add_node(varnode);
        }
        self.smooth_recurse(self.root, &varnode_map, &missing);
    }

    pub fn entailment_annotate(&mut self, node: NodeIndex, clauses: &[ClauseIndex]) {
        let mut entailed_here = vec![];

        match &self.nodes[node] {
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
                        &self.nodes[child]
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
                                self.nodes[node].children_mut()[i] = child;
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
            NNFNode::False(_) => return,
        }

        self.nodes[node].set_entailed_clauses(&entailed_here[..]);
    }

    pub fn parse(clauses: Vec<Vec<Lit>>, lines: impl Iterator<Item = String>) -> Self {
        let mut nodes = vec![NNFNode::False(0)];
        let mut arcs = vec![];
        let mut max_id = 0;

        // list of "True" nodes omitted in our representation
        let mut true_nodes = vec![];

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

            // we have a new node with a larger ID
            if id > max_id && ["o", "a", "f"].contains(&t) {
                nodes.resize(id + 1, nodes[0].clone());
                max_id = id;
            }

            // slot not yet filled
            nodes[id] = match t {
                "o" => NNFNode::Or {
                    id,
                    children: vec![],
                    entailed: vec![],
                },
                "a" => NNFNode::And {
                    id,
                    children: vec![],
                    entailed: vec![],
                    lits,
                },
                "f" => NNFNode::False(id),
                "t" => {
                    true_nodes.push(id);
                    continue;
                }
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
                // omit "true" nodes
                let children = if true_nodes.contains(&target) {
                    vec![]
                } else {
                    vec![target]
                };
                let new_node = NNFNode::And {
                    id,
                    children,
                    entailed: vec![],
                    lits,
                };
                assert! {nodes.len() == new_node.id()}
                nodes.push(new_node);
                nodes[origin].add_child(id);
            } else {
                assert! {!true_nodes.contains(&target)};
                nodes[origin].add_child(target);
            }
        }

        let root = 1;

        // make sure the root node is a valid decision node
        if let [ref child] = nodes[root].children() {
            max_id += 1;
            let tf = NNFNode::False(max_id);
            max_id += 1;
            let root_lit = if let NNFNode::And { ref lits, .. } = &nodes[*child] {
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

            nodes[root].add_child(otherbranch.id());
            assert! {nodes.len() == tf.id()}
            nodes.push(tf);
            assert! {nodes.len() == otherbranch.id()}
            nodes.push(otherbranch);
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

struct NNFTracer<'l> {
    nnf: &'l NNFTree,
    exported_nodes: HashMap<NodeIndex, (ComponentId, BigUint)>,
    max_component: ComponentId,
}

impl<'l> NNFTracer<'l> {
    fn trace(nnf: &NNFTree) {
        let mut tracer = NNFTracer {
            nnf,
            exported_nodes: HashMap::new(),
            max_component: 0,
        };
        tracer.trace_recurse(tracer.nnf.root, 0, 0);
    }

    fn issue_comp_id(&mut self) -> ComponentId {
        self.max_component += 1;
        self.max_component
    }

    fn lstr<T: ToString>(input: impl Iterator<Item = T>) -> String {
        let slits: Vec<_> = input.map(|l| l.to_string()).collect();
        slits.join(" ")
    }

    fn trace_comp<'a>(
        id: ComponentId,
        parent: ComponentId,
        vars: impl Iterator<Item = &'a Var>,
        clauses: &[ClauseIndex],
    ) {
        println!(
            "d {} {} 0 {} 0",
            id,
            Self::lstr(vars),
            Self::lstr(clauses.iter().map(|c| c + 1))
        );
        if parent > 0 {
            println!("jc {} {} 0", id, parent);
        }
    }

    fn trace_recurse(
        &mut self,
        node: NodeIndex,
        parent: NodeIndex,
        parent_comp: ComponentId,
    ) -> BigUint {
        let vars = self.nnf.varsof(node);
        match &self.nnf.nodes[node] {
            NNFNode::And {
                id,
                children,
                lits,
                entailed,
            } => {
                // we export AND-nodes uniquely.
                assert! {!self.exported_nodes.contains_key(id)};

                let litvars: BTreeSet<_> = lits.iter().map(|l| l.abs()).collect();

                let join_comp = self.issue_comp_id();

                // trace a new join component
                println!("c AND component for {} {:?}", id, lits);
                Self::trace_comp(join_comp, parent_comp, vars.difference(&litvars), entailed);

                // leaf node
                let count = if children.is_empty() {
                    println!("m {} 1 {} 0", parent_comp, Self::lstr(litvars.iter()));
                    BigUint::one()
                // join children
                } else {
                    children
                        .iter()
                        .map(|child| self.trace_recurse(*child, node, join_comp))
                        .fold(BigUint::one(), |acc, c| acc * c)
                };

                if !lits.is_empty() {
                    // extend to parent component
                    if !children.is_empty() {
                        println!(
                            "e {} {} {} {} 0",
                            parent_comp,
                            join_comp,
                            count,
                            Self::lstr(lits.iter())
                        );
                    }

                    // we have to project-away assumption literals
                    if lits.len() > 1 {
                        let dec_lit = lits[0];
                        println!("xp {} {} 0", join_comp, parent_comp);

                        // FIXME: proof
                        println!(
                            "xf {} {} 0 {} 0",
                            join_comp,
                            Self::lstr(litvars.iter()),
                            dec_lit
                        );
                        println!("a {} {} {} 0", join_comp, count, dec_lit);
                    }
                }

                count
            }
            NNFNode::Or {
                id,
                children,
                entailed,
            } => {
                // node is already exported
                if let Some((comp, count)) = self.exported_nodes.get(id) {
                    println!("jc {} {}", comp, parent_comp);
                    return count.clone();
                }

                let compid = self.issue_comp_id();
                let (child1, child2) = match &children[..] {
                    [child1, child2] => (*child1, *child2),
                    _ => panic! {"decision node must have tow children!"},
                };

                let dec_lit = match &self.nnf.nodes[child1] {
                    NNFNode::And { lits, .. } => lits[0],
                    _ => panic! {"children of decision nodes must be AND nodes!"},
                };

                println!("c OR component for {}", id);
                Self::trace_comp(compid, parent_comp, vars.iter(), entailed);

                let c1 = self.trace_recurse(child1, node, compid);
                let c2 = self.trace_recurse(child2, node, compid);
                let count = c1 + c2;

                println!("xp {} {} 0", compid, compid);
                println!("xf {} {} 0 0", compid, dec_lit.abs());
                println!("a {} {} 0", compid, count);

                self.exported_nodes.insert(node, (compid, count.clone()));
                count
            }
            NNFNode::False(_) => {
                let compid = self.issue_comp_id();
                let parent_clauses = self.nnf.nodes[parent].entailed();

                println!("c UNSAT component for {}", compid);
                Self::trace_comp(compid, parent_comp, vars.iter(), parent_clauses);

                println!("xp {} {} 0", compid, compid);
                println!("xf {} 0 0", compid);
                println!("a {} 0 0", compid);

                BigUint::zero()
            }
        }
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

    NNFTracer::trace(&nnf);

    Ok(())
}
