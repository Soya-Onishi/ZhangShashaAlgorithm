use zhang_shasha_diff as zsdiff;

struct N {
    index: usize,
    content: &'static str,
    children: Vec<N>,
}

impl N {
    fn new(index: usize, content: &'static str, children: Vec<N>) -> N {
        N {
            index,
            content,
            children,
        }
    }
}

impl zsdiff::Node for N {
    fn children(&self) -> &[Self] {
        &self.children[..]
    }

    fn index(&self) -> usize {
        self.index
    }
}

impl PartialEq for N {
    fn eq(&self, other: &Self) -> bool {
        self.content == other.content
    }
}

impl PartialOrd for N {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.index.cmp(&other.index))
    }
}

fn main() {
    let x = N::new(
        0,
        "a",
        vec![
            N::new(1, "b", vec![N::new(2, "c", vec![]), N::new(3, "d", vec![])]),
            N::new(4, "e", vec![]),
        ],
    );

    let y = N::new(0, "f", vec![N::new(1, "g", vec![])]);

    let map = zsdiff::diff(&x, &y);

    for diff in map {
        match diff {
            zsdiff::ChangeType::Delete(x) => println!("Delete: {}({})", x.content, x.index),
            zsdiff::ChangeType::Insert(y) => println!("Insert: {}({})", y.content, y.index),
            zsdiff::ChangeType::Update(x, y) => println!(
                "Update: {}({}) => {}({})",
                x.content, x.index, y.content, y.index
            ),
        }
    }
}
