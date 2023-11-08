pub trait Node: PartialEq + PartialOrd + Sized {
    //    fn index(&self) -> usize;
    fn children(&self) -> &[Self];
}

#[derive(PartialEq, Debug)]
pub enum ChangeType<T: PartialEq> {
    Delete(T),
    Insert(T),
    Update(T, T),
}

struct NodeWithIndex<'a, T: Node> {
    index: usize,
    node: &'a T,
    children: Vec<NodeWithIndex<'a, T>>,
}

impl<'a, T: Node> From<&'a T> for NodeWithIndex<'a, T> {
    fn from(node: &'a T) -> Self {
        convert(node, &mut 0)
    }
}

fn convert<'a, T: Node>(node: &'a T, index: &mut usize) -> NodeWithIndex<'a, T> {
    let node_index = *index;
    let children: Vec<NodeWithIndex<'a, T>> = node
        .children()
        .iter()
        .map(|c| {
            *index = *index + 1;
            let c = convert(c, index);

            c
        })
        .collect();

    NodeWithIndex {
        index: node_index,
        node,
        children,
    }
}

type Matrix<T> = Vec<Vec<T>>;

pub fn diff<'a, T: Node>(x: &'a T, y: &'a T) -> Vec<ChangeType<&'a T>> {
    diff_with_costfn(
        x,
        y,
        |_| 1,
        |_| 1,
        |x, y| {
            if x == y {
                0
            } else {
                1
            }
        },
    )
}

pub fn diff_with_costfn<'a, T: Node>(
    x: &'a T,
    y: &'a T,
    insert: fn(&T) -> usize,
    delete: fn(&T) -> usize,
    replace: fn(&T, &T) -> usize,
) -> Vec<ChangeType<&'a T>> {
    let x_with_index: NodeWithIndex<'a, T> = NodeWithIndex::from(x);
    let y_with_index: NodeWithIndex<'a, T> = NodeWithIndex::from(y);

    let (mut forest_ted, mut subtree_ted) =
        ted(&x_with_index, &y_with_index, insert, delete, replace);
    let mut map = backtrace(
        &x_with_index,
        &y_with_index,
        &mut subtree_ted,
        &mut forest_ted,
        insert,
        delete,
        replace,
    );
    push_insert_and_delete(&mut map, &x_with_index, &y_with_index);

    map
}

fn ted<'a, 'b: 'a, T: Node>(
    x: &'b NodeWithIndex<'a, T>,
    y: &'b NodeWithIndex<'a, T>,
    insert: fn(&T) -> usize,
    delete: fn(&T) -> usize,
    replace: fn(&T, &T) -> usize,
) -> (Matrix<usize>, Matrix<usize>) {
    let mut x_keyroots: Vec<&NodeWithIndex<'a, T>> = keyroots(x).into_iter().collect();
    let mut y_keyroots: Vec<&NodeWithIndex<'a, T>> = keyroots(y).into_iter().collect();
    x_keyroots.reverse();
    y_keyroots.reverse();
    let x_keyroots = x_keyroots;
    let y_keyroots = y_keyroots;

    let xs = depth_priority_vec(x);
    let ys = depth_priority_vec(y);
    let m = xs.len();
    let n = ys.len();
    let mut subtree_ted: Matrix<usize> = vec![vec![0; n]; m];
    let mut forest_ted: Matrix<usize> = vec![vec![0; n + 1]; m + 1];

    for &k in x_keyroots.iter() {
        for &l in y_keyroots.iter() {
            let rlk = rl(k);
            let rll = rl(l);

            forest_ted[rlk.index + 1][rll.index + 1] = 0;

            for i in (k.index..rlk.index + 1).rev() {
                forest_ted[i][rll.index + 1] =
                    forest_ted[i + 1][rll.index + 1] + delete(xs[i].node);
            }

            for j in (l.index..rll.index + 1).rev() {
                forest_ted[rlk.index + 1][j] =
                    forest_ted[rlk.index + 1][j + 1] + insert(ys[j].node);
            }

            for i in (k.index..rlk.index + 1).rev() {
                for j in (l.index..rll.index + 1).rev() {
                    let rli = rl(xs[i]);
                    let rlj = rl(ys[j]);
                    if rli.index == rlk.index && rlj.index == rll.index {
                        let costs = [
                            forest_ted[i + 1][j] + delete(xs[i].node),
                            forest_ted[i][j + 1] + insert(ys[j].node),
                            forest_ted[i + 1][j + 1] + replace(xs[i].node, ys[j].node),
                        ];

                        let cost = costs.into_iter().min().unwrap();
                        forest_ted[i][j] = cost;
                        subtree_ted[i][j] = cost;
                    } else {
                        let costs = [
                            forest_ted[i + 1][j] + delete(xs[i].node),
                            forest_ted[i][j + 1] + insert(ys[j].node),
                            forest_ted[rli.index + 1][rlj.index + 1] + subtree_ted[i][j],
                        ];

                        forest_ted[i][j] = costs.into_iter().min().unwrap();
                    }
                }
            }
        }
    }

    return (forest_ted, subtree_ted);
}

fn keyroots<'a, 'b: 'a, T: Node>(root: &'b NodeWithIndex<'a, T>) -> Vec<&'b NodeWithIndex<'a, T>> {
    let mut rls = Vec::new();
    let mut krs = Vec::new();
    let nodes = depth_priority_vec(root);
    for &n in nodes.iter() {
        let rl_node = rl(n);
        if !rls.contains(&rl_node.index) {
            rls.push(rl_node.index);
            krs.push(n);
        }
    }

    krs
}

fn rl<'a, T: Node>(node: &'a NodeWithIndex<'a, T>) -> &'a NodeWithIndex<'a, T> {
    node.children.last().map(|c| rl(c)).unwrap_or(node)
}

fn backtrace<'a: 'b, 'b, T: Node>(
    x: &'b NodeWithIndex<'a, T>,
    y: &'b NodeWithIndex<'a, T>,
    subtree_ted: &mut Matrix<usize>,
    forest_ted: &mut Matrix<usize>,
    insert: fn(&T) -> usize,
    delete: fn(&T) -> usize,
    replace: fn(&T, &T) -> usize,
) -> Vec<ChangeType<&'a T>> {
    let mut map = vec![];
    backtr(
        &depth_priority_vec(x),
        &depth_priority_vec(y),
        subtree_ted,
        forest_ted,
        &mut map,
        0,
        0,
        insert,
        delete,
        replace,
    );

    map
}

fn backtr<'a: 'b, 'b, T: Node>(
    xs: &Vec<&'b NodeWithIndex<'a, T>>,
    ys: &Vec<&'b NodeWithIndex<'a, T>>,
    subtree_ted: &mut Matrix<usize>,
    forest_ted: &mut Matrix<usize>,
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
        for i in (k.index..rlk.index + 1).rev() {
            forest_ted[i][rll.index + 1] = forest_ted[i + 1][rll.index + 1] + delete(xs[i].node);
        }

        for j in (l.index..rll.index + 1).rev() {
            forest_ted[rlk.index + 1][j] = forest_ted[rlk.index + 1][j + 1] + insert(ys[j].node);
        }

        for i in (k.index..rlk.index + 1).rev() {
            for j in (l.index..rll.index + 1).rev() {
                let rli = rl(xs[i]);
                let rlj = rl(ys[j]);
                if rli.index == rlk.index && rlj.index == rll.index {
                    forest_ted[i][j] = forest_ted[rlk.index + 1][rll.index + 1] + subtree_ted[i][j];
                } else {
                    let costs = [
                        forest_ted[i + 1][j] + delete(xs[i].node),
                        forest_ted[i][j + 1] + insert(ys[j].node),
                        forest_ted[rli.index + 1][rlj.index + 1] + subtree_ted[i][j],
                    ];
                    forest_ted[i][j] = costs.into_iter().min().unwrap();
                }
            }
        }
    }

    while i <= rlk.index && j <= rll.index {
        let rli = rl(xs[i]);
        let rlj = rl(ys[j]);
        if rli.index == rlk.index && rlj.index == rll.index {
            if forest_ted[i][j] == forest_ted[i + 1][j + 1] + replace(xs[i].node, ys[j].node) {
                map.push(ChangeType::Update(xs[i].node, ys[j].node));
                i += 1;
                j += 1;
                continue;
            }
        } else {
            if forest_ted[i][j] == forest_ted[rli.index + 1][rlj.index + 1] + subtree_ted[i][j] {
                backtr(
                    xs,
                    ys,
                    subtree_ted,
                    forest_ted,
                    map,
                    i,
                    j,
                    insert,
                    delete,
                    replace,
                );
                i = rli.index + 1;
                j = rlj.index + 1;
                continue;
            }
        }

        if forest_ted[i][j] == forest_ted[i + 1][j] + delete(xs[i].node) {
            i = i + 1;
        } else if forest_ted[i][j] == forest_ted[i][j + 1] + insert(ys[j].node) {
            j = j + 1;
        }
    }
}

fn depth_priority_vec<'a: 'b, 'b, T: Node>(
    node: &'b NodeWithIndex<'a, T>,
) -> Vec<&'b NodeWithIndex<'a, T>> {
    let mut children: Vec<&'b NodeWithIndex<'a, T>> = node
        .children
        .iter()
        .flat_map(|c| depth_priority_vec(c))
        .collect();

    children.insert(0, node);

    children
}

fn push_insert_and_delete<'a: 'b, 'b, T: Node>(
    map: &mut Vec<ChangeType<&'a T>>,
    x: &'b NodeWithIndex<'a, T>,
    y: &'b NodeWithIndex<'a, T>,
) {
    let xs = depth_priority_vec(x);
    let ys = depth_priority_vec(y);
    let mut xs = xs.iter();
    let mut ys = ys.iter();
    let mut additional_map = Vec::new();
    for m in map.iter() {
        if let &ChangeType::Update(x, y) = m {
            for &x_node in &mut xs {
                if std::ptr::eq(x_node.node, x as *const T) {
                    break;
                }

                additional_map.push(ChangeType::Delete(x_node.node));
            }

            for &y_node in &mut ys {
                if std::ptr::eq(y_node.node, y as *const T) {
                    break;
                }

                additional_map.push(ChangeType::Insert(y_node.node));
            }
        }
    }

    for &x in xs {
        additional_map.push(ChangeType::Delete(x.node));
    }

    for &y in ys {
        additional_map.push(ChangeType::Insert(y.node));
    }

    map.append(&mut additional_map);
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
        let x = NodeWithIndex::from(&x);

        assert_eq!(rl(&x).index, 4);
        assert_eq!(rl(&x.children[0]).index, 3);
        assert_eq!(rl(&x.children[0].children[0]).index, 2);
        assert_eq!(rl(&x.children[0].children[1]).index, 3);
    }

    #[test]
    fn keyroots_test() {
        let x = x_tree();
        let y = y_tree();
        let x = NodeWithIndex::from(&x);
        let y = NodeWithIndex::from(&y);

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
        let x = NodeWithIndex::from(&x);
        let y = NodeWithIndex::from(&y);
        let (_, _) = ted(&x, &y, insert, delete, replace);
    }

    fn insert<T: Node>(_: &T) -> usize {
        1
    }

    fn delete<T: Node>(_: &T) -> usize {
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
        let x = NodeWithIndex::from(&x);
        let y = NodeWithIndex::from(&y);
        let z = NodeWithIndex::from(&z);
        let xs = depth_priority_vec(&x);
        let ys = depth_priority_vec(&y);
        let zs = depth_priority_vec(&z);
        let (mut forest_ted, mut subtree_ted) = ted(&x, &y, insert, delete, replace);
        let m = backtrace(
            &x,
            &y,
            &mut subtree_ted,
            &mut forest_ted,
            insert,
            delete,
            replace,
        );

        assert_eq!(m.len(), 2);
        assert!(m.contains(&ChangeType::Update(xs[0].node, ys[0].node)));
        assert!(m.contains(&ChangeType::Update(xs[1].node, ys[1].node)));

        let (mut forest_ted, mut subtree_ted) = ted(&x, &z, insert, delete, replace);
        let m = backtrace(
            &x,
            &z,
            &mut subtree_ted,
            &mut forest_ted,
            insert,
            delete,
            replace,
        );
        assert_eq!(m.len(), 4);
        for (x, z) in [
            (xs[0], zs[0]),
            (xs[2], zs[1]),
            (xs[3], zs[2]),
            (xs[4], zs[3]),
        ] {
            assert!(m.contains(&ChangeType::Update(x.node, z.node)));
        }
    }

    #[test]
    fn delete_root_node() {
        let x = TreeNode::new(
            "a",
            vec![TreeNode::new("b", vec![TreeNode::new("c", vec![])])],
        );
        let y = TreeNode::new("b", vec![TreeNode::new("c", vec![])]);
        let x = NodeWithIndex::from(&x);
        let y = NodeWithIndex::from(&y);

        let xs = depth_priority_vec(&x);
        let ys = depth_priority_vec(&y);

        let (mut forest_ted, mut subtree_ted) = ted(&x, &y, insert, delete, replace);
        let m = backtrace(
            &x,
            &y,
            &mut subtree_ted,
            &mut forest_ted,
            insert,
            delete,
            replace,
        );
        assert_eq!(m.len(), 2);
        for (x, y) in [(xs[1], ys[0]), (xs[2], ys[1])] {
            assert!(m.contains(&ChangeType::Update(x.node, y.node)));
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

        let x = NodeWithIndex::from(&x);
        let y = NodeWithIndex::from(&y);

        let (mut forest_ted, mut subtree_ted) = ted(&x, &y, insert, delete, replace);
        let m = backtrace(
            &x,
            &y,
            &mut subtree_ted,
            &mut forest_ted,
            insert,
            delete,
            replace,
        );
        assert_eq!(m.len(), 3);
        let xs = depth_priority_vec(&x);
        let ys = depth_priority_vec(&y);

        for (x, y) in [(xs[0], ys[0]), (xs[1], ys[1]), (xs[2], ys[2])] {
            assert!(m.contains(&ChangeType::Update(x.node, y.node)));
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
        let x = NodeWithIndex::from(&x);
        let y = NodeWithIndex::from(&y);
        let xs = depth_priority_vec(&x);
        let ys = depth_priority_vec(&y);

        let (mut forest_ted, mut subtree_ted) = ted(&x, &y, insert, delete, replace);
        let m = backtrace(
            &x,
            &y,
            &mut subtree_ted,
            &mut forest_ted,
            insert,
            delete,
            replace,
        );
        assert_eq!(m.len(), 2);

        for (x, y) in [(xs[0], ys[0]), (xs[1], ys[1])] {
            assert!(m.contains(&ChangeType::Update(x.node, y.node)));
        }

        let (mut forest_ted, mut subtree_ted) = ted(&x, &y, |_| 2, |_| 2, rep0);
        let m = backtrace(
            &x,
            &y,
            &mut subtree_ted,
            &mut forest_ted,
            |_| 2,
            |_| 2,
            rep0,
        );
        assert_eq!(m.len(), 1);
        assert_eq!(m[0], ChangeType::Update(xs[1].node, ys[0].node));
    }

    #[test]
    fn diff_basic_tree() {
        let x = x_tree();
        let y = y_tree();
        let x = NodeWithIndex::from(&x);
        let y = NodeWithIndex::from(&y);
        let xs = depth_priority_vec(&x);
        let ys = depth_priority_vec(&y);
        let m = diff(x.node, y.node);

        assert_eq!(m.len(), 5);
        assert!(m.contains(&ChangeType::Update(xs[0].node, ys[0].node)));
        assert!(m.contains(&ChangeType::Update(xs[1].node, ys[1].node)));
        assert!(m.contains(&ChangeType::Delete(xs[2].node)));
        assert!(m.contains(&ChangeType::Delete(xs[3].node)));
        assert!(m.contains(&ChangeType::Delete(xs[4].node)));
    }
}
