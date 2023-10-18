trait Node: PartialEq + PartialOrd + Sized {
    fn index(&self) -> usize;
    fn children(&self) -> &[Self];
}

fn depth_priority_vec<T: Node>(node: &T) -> Vec<&T> {
    let mut children: Vec<&T> = node
        .children()
        .iter()
        .flat_map(|c| depth_priority_vec(c))
        .collect();

    children.insert(0, node);

    children
}

#[derive(PartialEq, Debug)]
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

fn rep_cost<T: Node>(x: &T, y: &T) -> usize {
    if x == y {
        0
    } else {
        1
    }
}

fn ted<T: Node>(
    x: &T,
    y: &T,
    insert: fn(&T) -> usize,
    delete: fn(&T) -> usize,
    replace: fn(&T, &T) -> usize,
) -> (Matrix<usize>, Matrix<usize>) {
    let mut x_keyroots: Vec<&T> = keyroots(x).into_iter().collect();
    let mut y_keyroots: Vec<&T> = keyroots(y).into_iter().collect();
    x_keyroots.reverse();
    y_keyroots.reverse();
    let x_keyroots = x_keyroots;
    let y_keyroots = y_keyroots;

    let xs = depth_priority_vec(x);
    let ys = depth_priority_vec(y);
    let m = xs.len();
    let n = ys.len();
    let mut d: Matrix<usize> = vec![vec![0; n]; m];
    let mut D: Matrix<usize> = vec![vec![0; n + 1]; m + 1];

    for &k in x_keyroots.iter() {
        for &l in y_keyroots.iter() {
            let rlk = rl(k);
            let rll = rl(l);

            D[rlk.index() + 1][rll.index() + 1] = 0;

            for i in (k.index()..rlk.index() + 1).rev() {
                D[i][rll.index() + 1] = D[i + 1][rll.index() + 1] + delete(xs[i]);
            }

            for j in (l.index()..rll.index() + 1).rev() {
                D[rlk.index() + 1][j] = D[rlk.index() + 1][j + 1] + insert(ys[j]);
            }

            for i in (k.index()..rlk.index() + 1).rev() {
                for j in (l.index()..rll.index() + 1).rev() {
                    let rli = rl(xs[i]);
                    let rlj = rl(ys[j]);
                    if rli.index() == rlk.index() && rlj.index() == rll.index() {
                        let costs = [
                            D[i + 1][j] + delete(xs[i]),
                            D[i][j + 1] + insert(ys[j]),
                            D[i + 1][j + 1] + replace(xs[i], ys[j]),
                        ];

                        let cost = costs.into_iter().min().unwrap();
                        D[i][j] = cost;
                        d[i][j] = cost;
                    } else {
                        let costs = [
                            D[i + 1][j] + delete(xs[i]),
                            D[i][j + 1] + insert(ys[j]),
                            D[rli.index() + 1][rlj.index() + 1] + d[i][j],
                        ];

                        D[i][j] = costs.into_iter().min().unwrap();
                    }
                }
            }
        }
    }

    return (D, d);
}

fn keyroots<T: Node>(root: &T) -> Vec<&T> {
    let mut rls = Vec::new();
    let mut krs = Vec::new();
    let nodes = depth_priority_vec(root);
    for &n in nodes.iter() {
        let rl_node = rl(n);
        if !rls.contains(&rl_node.index()) {
            rls.push(rl_node.index());
            krs.push(n);
        }
    }

    krs
}

fn rl<T: Node>(node: &T) -> &T {
    node.children().last().map(|c| rl(c)).unwrap_or(node)
}

fn backtrace<'a, T: Node>(
    x: &'a T,
    y: &'a T,
    d: &mut Matrix<usize>,
    D: &mut Matrix<usize>,
    insert: fn(&T) -> usize,
    delete: fn(&T) -> usize,
    replace: fn(&T, &T) -> usize,
) -> Vec<ChangeType<&'a T>> {
    let mut map = vec![];
    backtr(
        &depth_priority_vec(x),
        &depth_priority_vec(y),
        d,
        D,
        &mut map,
        0,
        0,
        insert,
        delete,
        replace,
    );

    map
}

fn backtr<'a, T: Node>(
    xs: &Vec<&'a T>,
    ys: &Vec<&'a T>,
    d: &mut Matrix<usize>,
    D: &mut Matrix<usize>,
    map: &mut Vec<ChangeType<&'a T>>,
    mut i: usize,
    mut j: usize,
    insert: fn(&T) -> usize,
    delete: fn(&T) -> usize,
    replace: fn(&T, &T) -> usize,
) {
    let k = xs[i];
    let l = ys[j];
    let rlk = rl(k);
    let rll = rl(l);

    if i > 0 && j > 0 {
        for i in (k.index()..rlk.index() + 1).rev() {
            D[i][rll.index() + 1] = D[i + 1][rll.index() + 1] + delete(xs[i]);
        }

        for j in (l.index()..rll.index() + 1).rev() {
            D[rlk.index() + 1][j] = D[rlk.index() + 1][j + 1] + insert(ys[j]);
        }

        for i in (k.index()..rlk.index() + 1).rev() {
            for j in (l.index()..rll.index() + 1).rev() {
                let rli = rl(xs[i]);
                let rlj = rl(ys[j]);
                if rli.index() == rlk.index() && rlj.index() == rll.index() {
                    D[i][j] = D[rlk.index() + 1][rll.index() + 1] + d[i][j];
                } else {
                    let costs = [
                        D[i + 1][j] + delete(xs[i]),
                        D[i][j + 1] + insert(ys[j]),
                        D[rli.index() + 1][rlj.index() + 1] + d[i][j],
                    ];
                    D[i][j] = costs.into_iter().min().unwrap();
                }
            }
        }
    }

    while i <= rlk.index() && j <= rll.index() {
        let rli = rl(xs[i]);
        let rlj = rl(ys[j]);
        if rli.index() == rlk.index() && rlj.index() == rll.index() {
            if D[i][j] == D[i + 1][j + 1] + replace(xs[i], ys[j]) {
                map.push(ChangeType::Update(xs[i], ys[j]));
                i += 1;
                j += 1;
                continue;
            }
        } else {
            if D[i][j] == D[rli.index() + 1][rlj.index() + 1] + d[i][j] {
                backtr(xs, ys, d, D, map, i, j, insert, delete, replace);
                i = rli.index() + 1;
                j = rlj.index() + 1;
                continue;
            }
        }

        if D[i][j] == D[i + 1][j] + delete(xs[i]) {
            i = i + 1;
        } else if D[i][j] == D[i][j + 1] + insert(ys[j]) {
            j = j + 1;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Debug)]
    struct TreeNode {
        index: usize,
        content: String,
        children: Vec<TreeNode>,
    }

    impl Node for TreeNode {
        fn index(&self) -> usize {
            self.index
        }

        fn children(&self) -> &[Self] {
            &self.children[..]
        }
    }

    impl PartialEq for TreeNode {
        fn eq(&self, other: &Self) -> bool {
            self.content == other.content
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

        fn set_index(&mut self, base_index: &mut usize) {
            self.index = *base_index;

            for c in self.children.iter_mut() {
                *base_index = *base_index + 1;
                c.set_index(base_index)
            }
        }
    }

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

    fn a_tree() -> TreeNode {
        TreeNode::new("b", vec![TreeNode::new("d", vec![])])
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
        let (D, _) = ted(&x, &y, insert, delete, replace);
    }

    fn insert<T: Node>(n: &T) -> usize {
        1
    }

    fn delete<T: Node>(n: &T) -> usize {
        1
    }

    fn replace<T: Node>(x: &T, y: &T) -> usize {
        if x == y {
            0
        } else {
            1
        }
    }

    #[test]
    fn mapping_test() {
        let x = x_tree();
        let y = y_tree();
        let z = z_tree();
        let xs = depth_priority_vec(&x);
        let ys = depth_priority_vec(&y);
        let zs = depth_priority_vec(&z);
        let (mut D, mut d) = ted(&x, &y, insert, delete, replace);
        let m = backtrace(&x, &y, &mut d, &mut D, insert, delete, replace);

        assert_eq!(m.len(), 2);
        assert!(m.contains(&ChangeType::Update(&xs[0], &ys[0])));
        assert!(m.contains(&ChangeType::Update(&xs[1], &ys[1])));

        let (mut D, mut d) = ted(&x, &z, insert, delete, replace);
        let m = backtrace(&x, &z, &mut d, &mut D, insert, delete, replace);
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
    fn delete_root_node() {
        let x = TreeNode::new(
            "a",
            vec![TreeNode::new("b", vec![TreeNode::new("c", vec![])])],
        );
        let y = TreeNode::new("b", vec![TreeNode::new("c", vec![])]);
        let xs = depth_priority_vec(&x);
        let ys = depth_priority_vec(&y);

        let (mut D, mut d) = ted(&x, &y, insert, delete, replace);
        let m = backtrace(&x, &y, &mut d, &mut D, insert, delete, replace);
        assert_eq!(m.len(), 2);
        for (x, y) in [(xs[1], ys[0]), (xs[2], ys[1])] {
            assert!(m.contains(&ChangeType::Update(x, y)));
        }
    }

    #[test]
    fn replace_sibling_order() {
        let x = TreeNode::new(
            "a",
            vec![TreeNode::new("b", vec![]), TreeNode::new("c", vec![])],
        );

        let y = TreeNode::new(
            "a",
            vec![TreeNode::new("c", vec![]), TreeNode::new("b", vec![])],
        );

        let (mut D, mut d) = ted(&x, &y, insert, delete, replace);
        let m = backtrace(&x, &y, &mut d, &mut D, insert, delete, replace);
        assert_eq!(m.len(), 3);
        let xs = depth_priority_vec(&x);
        let ys = depth_priority_vec(&y);

        for (x, y) in [(xs[0], ys[0]), (xs[1], ys[1]), (xs[2], ys[2])] {
            assert!(m.contains(&ChangeType::Update(x, y)));
        }
    }

    fn rep0<T: Node>(a: &T, b: &T) -> usize {
        if a == b {
            0
        } else {
            3
        }
    }

    #[test]
    fn replace_ancestor_order() {
        let x = TreeNode::new("a", vec![TreeNode::new("b", vec![])]);
        let y = TreeNode::new("b", vec![TreeNode::new("a", vec![])]);
        let xs = depth_priority_vec(&x);
        let ys = depth_priority_vec(&y);

        let (mut D, mut d) = ted(&x, &y, insert, delete, replace);
        let m = backtrace(&x, &y, &mut d, &mut D, insert, delete, replace);
        assert_eq!(m.len(), 2);

        for (x, y) in [(xs[0], ys[0]), (xs[1], ys[1])] {
            assert!(m.contains(&ChangeType::Update(&x, &y)));
        }

        let (mut D, mut d) = ted(&x, &y, |_| 2, |_| 2, rep0);
        let m = backtrace(&x, &y, &mut d, &mut D, |_| 2, |_| 2, rep0);
        assert_eq!(m.len(), 1);
        assert_eq!(m[0], ChangeType::Update(xs[1], ys[0]));
    }
}
