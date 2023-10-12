use std::collections::{HashMap, HashSet};

#[derive(Eq, Ord, Hash)]
struct Node {
    id: usize,
    content: String,
    children: Vec<Node>,
}

impl Node {
    fn new<T: Into<String>>(id: usize, content: T, children: Vec<Node>) -> Node {
        Node {
            id,
            content: content.into(),
            children,
        }
    }

    fn depth_priority_vec(&self) -> Vec<&Node> {
        let mut children: Vec<&Node> = self
            .children
            .iter()
            .flat_map(|c| c.depth_priority_vec())
            .collect();

        children.insert(0, self);

        children
    }

    fn len(&self) -> usize {
        self.children.iter().map(|c| c.len()).sum::<usize>() + 1
    }
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let cmp = if self.id > other.id {
            std::cmp::Ordering::Greater
        } else if self.id < other.id {
            std::cmp::Ordering::Less
        } else {
            std::cmp::Ordering::Equal
        };

        Some(cmp)
    }
}

enum ChangeType {
    Delete,
    Insert,
    Update(usize),
    None,
}

type Mapping = std::collections::HashMap<usize, ChangeType>;
type Matrix<T> = HashMap<(usize, usize), T>;

fn main() {}

// fn zhang_shasha_algorithm(x: &Node, y: &Node) -> (Mapping, Mapping) {}

fn ted(x: &Node, y: &Node) -> (Matrix<usize>, Matrix<usize>) {
    let mut x_keyroots: Vec<&Node> = keyroots(x).into_iter().collect();
    let mut y_keyroots: Vec<&Node> = keyroots(y).into_iter().collect();
    x_keyroots.sort_by(|a, b| b.cmp(a));
    y_keyroots.sort_by(|a, b| b.cmp(a));
    let mut d: Matrix<usize> = Matrix::<usize>::new();
    let mut D: Matrix<usize> = Matrix::<usize>::new();

    let rep_cost: fn(x: &Node, y: &Node) -> usize = |x, y| {
        if x.content == y.content {
            0
        } else {
            1
        }
    };

    for k in x_keyroots.iter() {
        for l in y_keyroots.iter() {
            D.insert((rl(k).id + 1, rl(l).id + 1), 0);
            let k_tree = k.depth_priority_vec();
            let l_tree = l.depth_priority_vec();
            for i in k_tree.iter().rev() {
                let cost = D.get(&(i.id + 1, rl(l).id + 1)).unwrap() + 1;
                D.insert((i.id, rl(l).id + 1), cost);
            }

            for j in l_tree.iter().rev() {
                let cost = D.get(&(rl(k).id + 1, j.id + 1)).unwrap() + 1;
                D.insert((rl(k).id + 1, j.id), cost);
            }

            for i in k_tree.iter().rev() {
                for j in l_tree.iter().rev() {
                    if rl(i).id == rl(k).id && rl(j).id == rl(l).id {
                        let costs = [
                            D.get(&(i.id + 1, j.id)).unwrap() + 1,
                            D.get(&(i.id, j.id + 1)).unwrap() + 1,
                            D.get(&(i.id + 1, j.id + 1)).unwrap() + rep_cost(i, j),
                        ];
                        let cost = costs.into_iter().min().unwrap();
                        D.insert((i.id, j.id), cost);
                        d.insert((i.id, j.id), cost);
                    } else {
                        let costs = [
                            D.get(&(i.id + 1, j.id)).unwrap() + 1,
                            D.get(&(i.id, j.id + 1)).unwrap() + 1,
                            D.get(&(rl(i).id + 1, rl(j).id + 1)).unwrap()
                                + d.get(&(i.id, j.id)).unwrap(),
                        ];
                        let cost = costs.into_iter().min().unwrap();

                        D.insert((i.id, j.id), cost);
                    }
                }
            }
        }
    }

    return (D, d);
}

fn keyroots(root: &Node) -> HashSet<&Node> {
    let mut rls = HashSet::new();
    let mut krs = HashSet::new();
    let nodes = root.depth_priority_vec();
    for &n in nodes.iter() {
        let rl_node = rl(n);
        if !rls.contains(&rl_node.id) {
            rls.insert(rl_node.id);
            krs.insert(n);
        }
    }

    krs
}

fn rl(node: &Node) -> &Node {
    node.children.last().map(|c| rl(c)).unwrap_or(node)
}

#[cfg(test)]
mod test {
    use super::*;

    fn x_tree() -> Node {
        Node::new(
            0,
            "a",
            vec![
                Node::new(
                    1,
                    "b",
                    vec![Node::new(2, "c", vec![]), Node::new(3, "d", vec![])],
                ),
                Node::new(4, "e", vec![]),
            ],
        )
    }

    fn y_tree() -> Node {
        Node::new(0, "f", vec![Node::new(1, "g", vec![])])
    }

    #[test]
    fn rl_test() {
        let x = x_tree();

        assert_eq!(rl(&x).id, 4);
        assert_eq!(rl(&x.children[0]).id, 3);
        assert_eq!(rl(&x.children[0].children[0]).id, 2);
        assert_eq!(rl(&x.children[0].children[1]).id, 3);
    }

    #[test]
    fn keyroots_test() {
        let x = x_tree();
        let y = y_tree();

        let krs = keyroots(&x);
        let ids: Vec<usize> = krs.iter().map(|n| n.id).collect();
        assert!(ids.contains(&0), "keyroot ids: {:?}", &ids);
        assert!(ids.contains(&1), "keyroot ids: {:?}", &ids);
        assert_eq!(ids.len(), 3);

        let krs = keyroots(&y);
        let ids: Vec<usize> = krs.iter().map(|n| n.id).collect();

        assert_eq!(ids.len(), 1);
    }

    #[test]
    fn ted_test() {
        let x = x_tree();
        let y = y_tree();
        let (D, _) = ted(&x, &y);

        let mut result = String::new();
        for i in 0..x.len() + 1 {
            for j in 0..y.len() + 1 {
                result += format!("{}, ", &D.get(&(i, j)).unwrap()).as_str();
            }

            result += "\n";
        }

        println!("{}", result);
    }
}
