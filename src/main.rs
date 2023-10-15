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

#[derive(PartialEq)]
enum ChangeType<T: PartialEq> {
    Delete(T),
    Insert(T),
    Update(T, T),
    None,
}

type Mapping<T> = std::collections::HashMap<usize, ChangeType<T>>;
type Matrix<T> = Vec<Vec<T>>;

fn main() {}

// fn zhang_shasha_algorithm(x: &Node, y: &Node) -> (Mapping, Mapping) {}

fn rep_cost(x: &Node, y: &Node) -> usize {
    if x.content == y.content {
        0
    } else {
        1
    }
}

fn ted(x: &Node, y: &Node) -> (Matrix<usize>, Matrix<usize>) {
    let mut x_keyroots: Vec<&Node> = keyroots(x).into_iter().collect();
    let mut y_keyroots: Vec<&Node> = keyroots(y).into_iter().collect();
    x_keyroots.sort_by(|a, b| b.cmp(a));
    y_keyroots.sort_by(|a, b| b.cmp(a));
    let m = x.len();
    let n = x.len();
    let mut d: Matrix<usize> = vec![vec![0; n]; m];
    let mut D: Matrix<usize> = vec![vec![0; n + 1]; m + 1];

    for k in x_keyroots.iter() {
        for l in y_keyroots.iter() {
            D[rl(k).id + 1][rl(l).id + 1] = 0;
            let k_tree = k.depth_priority_vec();
            let l_tree = l.depth_priority_vec();
            for i in k_tree.iter().rev() {
                D[i.id][rl(l).id + 1] = D[i.id + 1][rl(l).id + 1] + 1;
            }

            for j in l_tree.iter().rev() {
                D[rl(k).id + 1][j.id] = D[rl(k).id + 1][j.id + 1] + 1;
            }

            for i in k_tree.iter().rev() {
                for j in l_tree.iter().rev() {
                    if rl(i).id == rl(k).id && rl(j).id == rl(l).id {
                        let costs = [
                            D[i.id + 1][j.id] + 1,
                            D[i.id][j.id + 1] + 1,
                            D[i.id + 1][j.id + 1] + rep_cost(i, j),
                        ];

                        let cost = costs.into_iter().min().unwrap();
                        D[i.id][j.id] = cost;
                        d[i.id][j.id] = cost;
                    } else {
                        let costs = [
                            D[i.id + 1][j.id] + 1,
                            D[i.id][j.id + 1] + 1,
                            D[rl(i).id + 1][rl(j).id + 1] + d[i.id][j.id],
                        ];

                        let cost = costs.into_iter().min().unwrap();
                        D[i.id][j.id] = cost;
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

fn backtrace<'a>(
    x: &'a Node,
    y: &'a Node,
    d: &mut Matrix<usize>,
    D: &mut Matrix<usize>,
) -> Vec<ChangeType<&'a Node>> {
    let mut map = vec![];
    backtr(x, y, d, D, &mut map, x, y);

    map
}

fn backtr<'a>(
    x: &Node,
    y: &Node,
    d: &mut Matrix<usize>,
    D: &mut Matrix<usize>,
    map: &mut Vec<ChangeType<&'a Node>>,
    k: &'a Node,
    l: &'a Node,
) {
    let k_nodes = k.depth_priority_vec();
    let l_nodes = l.depth_priority_vec();
    if k.id > 0 && l.id > 0 {
        for i in k_nodes.iter().rev() {
            D[i.id][rl(l).id + 1] = D[i.id + 1][rl(l).id + 1] + 1;
        }

        for j in l_nodes.iter().rev() {
            D[rl(k).id + 1][j.id] = D[rl(k).id + 1][j.id + 1] + 1;
        }

        for i in k_nodes.iter().rev() {
            for j in l_nodes.iter().rev() {
                if rl(i).id == rl(k).id && rl(j).id == rl(l).id {
                    D[i.id][j.id] = d[i.id][j.id] + D[rl(k).id + 1][rl(l).id + 1];
                } else {
                    let costs = [
                        D[i.id + 1][j.id] + 1,
                        D[i.id][j.id + 1] + 1,
                        D[rl(i).id + 1][rl(j).id + 1] + d[i.id][j.id],
                    ];

                    D[i.id][j.id] = costs.into_iter().min().unwrap();
                }
            }
        }
    }

    let k_nodes = k.depth_priority_vec();
    let l_nodes = l.depth_priority_vec();
    let mut k_nodes = k_nodes.iter();
    let mut l_nodes = l_nodes.iter();
    let mut i_node = k_nodes.next();
    let mut j_node = l_nodes.next();

    while let Some((i, j)) = i_node.zip(j_node) {
        if rl(i).id == rl(k).id && rl(j).id == rl(l).id {
            if D[i.id][j.id] == D[i.id + 1][j.id + 1] + rep_cost(i, j) {
                map.push(ChangeType::Update(i, j));
                i_node = k_nodes.next();
                j_node = l_nodes.next();
                continue;
            }
        } else {
            if D[i.id][j.id] == D[rl(i).id + 1][rl(j).id + 1] + d[i.id][j.id] {
                backtr(x, y, d, D, map, i, j);
                let rli = rl(i);
                let rlj = rl(j);

                i_node = if rli.id == i.id {
                    k_nodes.next()
                } else {
                    k_nodes.find(|n| n.id == rli.id)
                };
                j_node = if rlj.id == j.id {
                    l_nodes.next()
                } else {
                    l_nodes.find(|n| n.id == rlj.id)
                };

                continue;
            }
        }
        if D[i.id][j.id] == D[i.id + 1][j.id] + 1 {
            i_node = k_nodes.next();
            continue;
        } else if D[i.id][j.id] == D[i.id][j.id + 1] + 1 {
            j_node = l_nodes.next();
            continue;
        }
    }
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

    fn z_tree() -> Node {
        Node::new(
            0,
            "a",
            vec![
                Node::new(1, "c", vec![]),
                Node::new(2, "d", vec![]),
                Node::new(3, "e", vec![]),
            ],
        )
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
    }

    #[test]
    fn mapping_test() {
        let x = x_tree();
        let y = y_tree();
        let z = z_tree();
        let xs = x.depth_priority_vec();
        let ys = y.depth_priority_vec();
        let zs = z.depth_priority_vec();
        let (mut D, mut d) = ted(&x, &y);
        let m = backtrace(&x, &y, &mut d, &mut D);

        assert_eq!(m.len(), 2);
        assert!(m.contains(&ChangeType::Update(&xs[0], &ys[0])));
        assert!(m.contains(&ChangeType::Update(&xs[1], &ys[1])));

        let (mut D, mut d) = ted(&x, &z);
        let m = backtrace(&x, &z, &mut d, &mut D);
        assert_eq!(m.len(), 4);
        for (x, z) in [
            (xs[0], zs[0]),
            (xs[2], zs[1]),
            (xs[3], zs[2]),
            (xs[4], zs[3]),
        ] {
            assert!(m.contains(&ChangeType::Update(x, z)));
        }
    }
}
