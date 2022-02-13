use clap::Parser;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

type NodeIndex = usize;
type ClauseIndex = usize;
type Lit = i64;

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
}

impl NNFTree {
    fn issue_new_id(&mut self) -> NodeIndex {
        self.max_id += 1;
        self.max_id
    }

    pub fn parse(lines: impl Iterator<Item = String>) -> Self {
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
                "o" => {
                    nodes.insert(
                        id,
                        NNFNode::Or {
                            id,
                            children: vec![],
                            entailed: vec![],
                        },
                    );
                }
                "a" => {
                    nodes.insert(
                        id,
                        NNFNode::And {
                            id,
                            children: vec![],
                            entailed: vec![],
                            lits,
                        },
                    );
                }
                "t" => {
                    nodes.insert(id, NNFNode::True(id));
                }
                "f" => {
                    nodes.insert(id, NNFNode::False(id));
                }

                // no node, but an arc
                _ => {
                    let origin = t.parse::<NodeIndex>().unwrap();
                    arcs.push((origin, id, lits));
                }
            };
        }

        // build the tree structure
        for (origin, target, lits) in arcs.drain(..) {
            // implicit and node
            if !lits.is_empty() {
                max_id += 1;
                let new_node = NNFNode::And {
                    id: max_id,
                    children: vec![target],
                    entailed: vec![],
                    lits,
                };
                nodes.get_mut(&origin).unwrap().add_child(new_node.id());
            } else {
                nodes.get_mut(&origin).unwrap().add_child(target);
            }
        }

        NNFTree {
            root: 1,
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
            if line.starts_with("p") {
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
    let nnf = NNFTree::parse(
        BufReader::new(File::open(args.nnf)?)
            .lines()
            .map(|l| l.unwrap()),
    );
    println!("Hello, world!");
    eprintln! {"{:?}", formula};
    Ok(())
}
