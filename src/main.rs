use std::collections::{HashMap, HashSet};

#[derive(Eq, Ord, Hash)]
struct Node {
    index: usize,
    content: String,
    children: Vec<Node>,
}

impl Node {
    fn new<T: Into<String>>(content: T, children: Vec<Node>) -> Node {
        let mut node = Node {
            index: 0,
            content: content.into(),
            children,
        };

        node.set_index(&mut 0);

        node
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

    fn set_index(&mut self, base_index: &mut usize) {
        self.index = *base_index;

        for c in self.children.iter_mut() {
            *base_index = *base_index + 1;
            c.set_index(base_index)
        }
    }
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let cmp = if self.index > other.index {
            std::cmp::Ordering::Greater
        } else if self.index < other.index {
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
            D[rl(k).index + 1][rl(l).index + 1] = 0;
            let k_tree = k.depth_priority_vec();
            let l_tree = l.depth_priority_vec();
            for i in k_tree.iter().rev() {
                D[i.index][rl(l).index + 1] = D[i.index + 1][rl(l).index + 1] + 1;
            }

            for j in l_tree.iter().rev() {
                D[rl(k).index + 1][j.index] = D[rl(k).index + 1][j.index + 1] + 1;
            }

            for i in k_tree.iter().rev() {
                for j in l_tree.iter().rev() {
                    if rl(i).index == rl(k).index && rl(j).index == rl(l).index {
                        let costs = [
                            D[i.index + 1][j.index] + 1,
                            D[i.index][j.index + 1] + 1,
                            D[i.index + 1][j.index + 1] + rep_cost(i, j),
                        ];

                        let cost = costs.into_iter().min().unwrap();
                        D[i.index][j.index] = cost;
                        d[i.index][j.index] = cost;
                    } else {
                        let costs = [
                            D[i.index + 1][j.index] + 1,
                            D[i.index][j.index + 1] + 1,
                            D[rl(i).index + 1][rl(j).index + 1] + d[i.index][j.index],
                        ];

                        let cost = costs.into_iter().min().unwrap();
                        D[i.index][j.index] = cost;
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
        if !rls.contains(&rl_node.index) {
            rls.insert(rl_node.index);
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
    if k.index > 0 && l.index > 0 {
        for i in k_nodes.iter().rev() {
            D[i.index][rl(l).index + 1] = D[i.index + 1][rl(l).index + 1] + 1;
        }

        for j in l_nodes.iter().rev() {
            D[rl(k).index + 1][j.index] = D[rl(k).index + 1][j.index + 1] + 1;
        }

        for i in k_nodes.iter().rev() {
            for j in l_nodes.iter().rev() {
                if rl(i).index == rl(k).index && rl(j).index == rl(l).index {
                    D[i.index][j.index] = d[i.index][j.index] + D[rl(k).index + 1][rl(l).index + 1];
                } else {
                    let costs = [
                        D[i.index + 1][j.index] + 1,
                        D[i.index][j.index + 1] + 1,
                        D[rl(i).index + 1][rl(j).index + 1] + d[i.index][j.index],
                    ];

                    D[i.index][j.index] = costs.into_iter().min().unwrap();
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
        if rl(i).index == rl(k).index && rl(j).index == rl(l).index {
            if D[i.index][j.index] == D[i.index + 1][j.index + 1] + rep_cost(i, j) {
                map.push(ChangeType::Update(i, j));
                i_node = k_nodes.next();
                j_node = l_nodes.next();
                continue;
            }
        } else {
            if D[i.index][j.index] == D[rl(i).index + 1][rl(j).index + 1] + d[i.index][j.index] {
                backtr(x, y, d, D, map, i, j);
                let rli = rl(i);
                let rlj = rl(j);

                i_node = if rli.index == i.index {
                    k_nodes.next()
                } else {
                    k_nodes.find(|n| n.index == rli.index)
                };
                j_node = if rlj.index == j.index {
                    l_nodes.next()
                } else {
                    l_nodes.find(|n| n.index == rlj.index)
                };

                continue;
            }
        }
        if D[i.index][j.index] == D[i.index + 1][j.index] + 1 {
            i_node = k_nodes.next();
            continue;
        } else if D[i.index][j.index] == D[i.index][j.index + 1] + 1 {
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
            "a",
            vec![
                Node::new("b", vec![Node::new("c", vec![]), Node::new("d", vec![])]),
                Node::new("e", vec![]),
            ],
        )
    }

    fn y_tree() -> Node {
        Node::new("f", vec![Node::new("g", vec![])])
    }

    fn z_tree() -> Node {
        Node::new(
            "a",
            vec![
                Node::new("c", vec![]),
                Node::new("d", vec![]),
                Node::new("e", vec![]),
            ],
        )
    }

    #[test]
    fn index_test() {
        let x = x_tree();
        assert_eq!(x.index, 0);
        assert_eq!(x.children[0].index, 1);
        assert_eq!(x.children[0].children[0].index, 2);
        assert_eq!(x.children[0].children[1].index, 3);
        assert_eq!(x.children[1].index, 4);
    }

    #[test]
    fn rl_test() {
        let x = x_tree();

        assert_eq!(rl(&x).index, 4);
        assert_eq!(rl(&x.children[0]).index, 3);
        assert_eq!(rl(&x.children[0].children[0]).index, 2);
        assert_eq!(rl(&x.children[0].children[1]).index, 3);
    }

    #[test]
    fn keyroots_test() {
        let x = x_tree();
        let y = y_tree();

        let krs = keyroots(&x);
        let ids: Vec<usize> = krs.iter().map(|n| n.index).collect();
        assert!(ids.contains(&0), "keyroot ids: {:?}", &ids);
        assert!(ids.contains(&1), "keyroot ids: {:?}", &ids);
        assert_eq!(ids.len(), 3);

        let krs = keyroots(&y);
        let ids: Vec<usize> = krs.iter().map(|n| n.index).collect();

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
