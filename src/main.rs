use std::collections::{HashMap, HashSet};

#[derive(Eq, Ord, Hash)]
struct TreeNode {
    index: usize,
    content: String,
    children: Vec<TreeNode>,
}

impl TreeNode {
    fn new<T: Into<String>>(content: T, children: Vec<TreeNode>) -> TreeNode {
        let mut node = TreeNode {
            index: 0,
            content: content.into(),
            children,
        };

        node.set_index(&mut 0);

        node
    }

    fn depth_priority_vec(&self) -> Vec<&TreeNode> {
        let mut children: Vec<&TreeNode> = self
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

impl PartialEq for TreeNode {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl PartialOrd for TreeNode {
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

fn rep_cost(x: &TreeNode, y: &TreeNode) -> usize {
    if x.content == y.content {
        0
    } else {
        1
    }
}

fn ted(x: &TreeNode, y: &TreeNode) -> (Matrix<usize>, Matrix<usize>) {
    let mut x_keyroots: Vec<&TreeNode> = keyroots(x).into_iter().collect();
    let mut y_keyroots: Vec<&TreeNode> = keyroots(y).into_iter().collect();
    x_keyroots.sort_by(|a, b| b.cmp(a));
    y_keyroots.sort_by(|a, b| b.cmp(a));
    let x_keyroots = x_keyroots;
    let y_keyroots = y_keyroots;

    let xs = x.depth_priority_vec();
    let ys = y.depth_priority_vec();
    let m = xs.len();
    let n = ys.len();
    let mut d: Matrix<usize> = vec![vec![0; n]; m];
    let mut D: Matrix<usize> = vec![vec![0; n + 1]; m + 1];

    for k in x_keyroots.iter() {
        for l in y_keyroots.iter() {
            let rlk = rl(k);
            let rll = rl(l);

            D[rlk.index + 1][rll.index + 1] = 0;

            for i in (k.index..rlk.index + 1).rev() {
                D[i][rll.index + 1] = D[i + 1][rll.index + 1] + 1;
            }

            for j in (l.index..rll.index + 1).rev() {
                D[rlk.index + 1][j] = D[rlk.index + 1][j + 1] + 1;
            }

            for i in (k.index..rlk.index + 1).rev() {
                for j in (l.index..rll.index + 1).rev() {
                    let rli = rl(xs[i]);
                    let rlj = rl(ys[j]);
                    if rli.index == rlk.index && rlj.index == rll.index {
                        let costs = [
                            D[i + 1][j] + 1,
                            D[i][j + 1] + 1,
                            D[i + 1][j + 1] + rep_cost(xs[i], ys[j]),
                        ];

                        let cost = costs.into_iter().min().unwrap();
                        D[i][j] = cost;
                        d[i][j] = cost;
                    } else {
                        let costs = [
                            D[i + 1][j] + 1,
                            D[i][j + 1] + 1,
                            D[rli.index + 1][rlj.index + 1] + d[i][j],
                        ];

                        D[i][j] = costs.into_iter().min().unwrap();
                    }
                }
            }
        }
    }

    return (D, d);
}

fn keyroots(root: &TreeNode) -> HashSet<&TreeNode> {
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

fn rl(node: &TreeNode) -> &TreeNode {
    node.children.last().map(|c| rl(c)).unwrap_or(node)
}

fn backtrace<'a>(
    x: &'a TreeNode,
    y: &'a TreeNode,
    d: &mut Matrix<usize>,
    D: &mut Matrix<usize>,
) -> Vec<ChangeType<&'a TreeNode>> {
    let mut map = vec![];
    backtr(
        &x.depth_priority_vec(),
        &y.depth_priority_vec(),
        d,
        D,
        &mut map,
        0,
        0,
    );

    map
}

fn backtr<'a>(
    xs: &Vec<&'a TreeNode>,
    ys: &Vec<&'a TreeNode>,
    d: &mut Matrix<usize>,
    D: &mut Matrix<usize>,
    map: &mut Vec<ChangeType<&'a TreeNode>>,
    mut i: usize,
    mut j: usize,
) {
    let k = xs[i];
    let l = ys[j];
    let rlk = rl(k);
    let rll = rl(l);

    if i > 0 && j > 0 {
        for i in (k.index..rlk.index + 1).rev() {
            D[i][rll.index + 1] = D[i + 1][rll.index + 1] + 1;
        }

        for j in l.index..(rll.index + 1) {
            D[rlk.index + 1][j] = D[rlk.index + 1][j + 1] + 1;
        }

        for i in (k.index..rlk.index + 1).rev() {
            for j in (l.index..rll.index + 1).rev() {
                let rli = rl(xs[i]);
                let rlj = rl(ys[j]);
                if rli.index == rlk.index && rlj.index == rll.index {
                    D[i][j] = D[rlk.index + 1][rll.index + 1] + d[i][j];
                } else {
                    let costs = [
                        D[i + 1][j] + 1,
                        D[i][j + 1] + 1,
                        D[rli.index + 1][rlj.index + 1] + d[i][j],
                    ];
                    D[i][j] = costs.into_iter().min().unwrap();
                }
            }
        }
    }

    while i <= rlk.index && j <= rll.index {
        let rli = rl(xs[i]);
        let rlj = rl(ys[j]);
        if rli.index == rlk.index && rlj.index == rll.index {
            if D[i][j] == D[i + 1][j + 1] + rep_cost(xs[i], ys[j]) {
                map.push(ChangeType::Update(xs[i], ys[j]));
                i += 1;
                j += 1;
                continue;
            }
        } else {
            if D[i][j] == D[rli.index + 1][rlj.index + 1] + rep_cost(xs[i], ys[j]) {
                backtr(xs, ys, d, D, map, i, j);
                i = rli.index + 1;
                j = rlj.index + 1;
                continue;
            }
        }

        if D[i][j] == D[i + 1][j] + 1 {
            i = i + 1;
        } else if D[i][j] == D[i][j + 1] + 1 {
            j = j + 1;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn x_tree() -> TreeNode {
        TreeNode::new(
            "a",
            vec![
                TreeNode::new(
                    "b",
                    vec![TreeNode::new("c", vec![]), TreeNode::new("d", vec![])],
                ),
                TreeNode::new("e", vec![]),
            ],
        )
    }

    fn y_tree() -> TreeNode {
        TreeNode::new("f", vec![TreeNode::new("g", vec![])])
    }

    fn z_tree() -> TreeNode {
        TreeNode::new(
            "a",
            vec![
                TreeNode::new("c", vec![]),
                TreeNode::new("d", vec![]),
                TreeNode::new("e", vec![]),
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
        assert!(m.contains(&ChangeType::Update(&xs[2], &ys[1])));

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

    #[test]
    fn iter_test() {
        for i in (0..5).rev() {
            println!("{}", i);
        }
    }
}
