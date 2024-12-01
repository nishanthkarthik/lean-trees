use std::boxed::Box;

type OptNode = Option<Box<Node>>;

struct Node {
    left: OptNode,
    right: OptNode,
    val: usize,
}

struct Tree {
    root: OptNode,
}

fn max(a: usize, b: usize) -> usize {
    if a >= b { a } else { b }
}

fn max_val(t: &OptNode) -> usize {
    match t {
        None => 0,
        Some(e) => max(e.val, max(max_val(&e.left), max_val(&e.right))),
    }
}
