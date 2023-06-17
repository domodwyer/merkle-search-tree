//! Output the structure of a [`MerkleSearchTree`] formatted using [Graphviz]
//! DOT grammar.
//!
//! [`MerkleSearchTree`]: crate::MerkleSearchTree
//! [Graphviz]: https://graphviz.org/

use std::fmt::{Display, Write};

use crate::{node::Node, page::Page};

use super::Visitor;

#[derive(Debug, Clone)]
enum Parent {
    Node(String),
    Page(String, usize),
}

/// Serialise a tree into [Graphviz DOT language][dot] output to be rendered as a
/// diagram.
///
/// [dot]: https://graphviz.org/doc/info/lang.html
#[derive(Debug)]
pub struct DotVisitor {
    buf: String,

    /// Total number of pages visited so far (1-based)
    page_count: usize,

    /// The stack of parent node keys / page records, most recently visited last.
    link_stack: Vec<Parent>,

    /// A set of per-page buffers, populated incrementally and merged into `buf`
    /// once complete.
    page_bufs: Vec<String>,
}

impl Default for DotVisitor {
    fn default() -> Self {
        Self {
            buf: "digraph g {\n".to_string(),
            page_count: Default::default(),
            link_stack: vec![],
            page_bufs: vec![],
        }
    }
}

impl<'a, const N: usize, K> Visitor<'a, N, K> for DotVisitor
where
    K: Display,
{
    fn visit_page(&mut self, page: &'a Page<N, K>, high_page: bool) -> bool {
        let mut buf = String::new();

        self.page_count += 1;

        // Write the link directly to the buffer.
        match self.link_stack.last() {
            // If this is the first page, render a pseudo root node
            None if self.page_count == 1 => {
                writeln!(buf, "\troot [shape=diamond style=dotted];").unwrap();
                writeln!(buf, "\troot -> page_{}:head", self.page_count)
            }
            Some(Parent::Page(p, _)) => writeln!(
                buf,
                "\t{} -> page_{}:high_page [fontcolor=red color=red label=\"high page\"];",
                p, self.page_count
            ),
            Some(Parent::Node(n)) if !high_page => {
                writeln!(buf, "\t{} -> page_{}:head;", n, self.page_count)
            }
            _ => Ok(()),
        }
        .unwrap();

        write!(
            buf,
            "\tpage_{} [shape=record, label=\"<head>Level {}|",
            self.page_count,
            page.level(),
        )
        .unwrap();

        self.link_stack.push(Parent::Page(
            format!("page_{}:head", self.page_count),
            self.page_count,
        ));

        self.page_bufs.push(buf);

        true
    }

    fn post_visit_page(&mut self, page: &'a Page<N, K>) -> bool {
        let mut buf = self.page_bufs.pop().unwrap();

        // Remove the trailing | from the node field
        let _ = buf.pop();

        let me = match self.link_stack.pop().unwrap() {
            Parent::Node(_) => panic!("pop should yield visited page"),
            Parent::Page(_, id) => id,
        };

        // If this page has a high page, it'll be visited next.
        if page.high_page().is_some() {
            // Add a high page to this record
            writeln!(buf, r#"|<high_page>·"]"#).unwrap();

            // Link the high page to the referenced page
            writeln!(
                buf,
                "\tpage_{}:high_page -> page_{}:head [fontcolor=red color=red label=\"high page\"];",
                me,
                self.page_count + 1,
            )
            .unwrap();
        } else {
            // No high page, terminate record without it.
            writeln!(buf, r#""]"#).unwrap();
        }

        writeln!(self.buf, "{}", buf).unwrap();

        true
    }

    fn pre_visit_node(&mut self, node: &'a Node<N, K>) -> bool {
        // Find the ID of the last visited page, which will be the parent of
        // this node.
        let page_id = self
            .link_stack
            .iter()
            .rev()
            .filter_map(|v| match v {
                Parent::Node(_) => None,
                Parent::Page(_, id) => Some(id),
            })
            .next()
            .unwrap();

        let name = clean_name(node.key());
        self.link_stack
            .push(Parent::Node(format!("page_{}:{}", page_id, &name)));

        true
    }

    fn visit_node(&mut self, node: &'a Node<N, K>) -> bool {
        let buf = self.page_bufs.last_mut().unwrap();

        // Add this node to the page record
        let name = clean_name(node.key());
        write!(buf, "<{}>·|{}|", &name, name).unwrap();

        true
    }

    fn post_visit_node(&mut self, _node: &'a Node<N, K>) -> bool {
        self.link_stack.pop();
        true
    }
}

impl DotVisitor {
    /// Consume this visitor, yielding the generated DOT representation.
    pub fn finalise(self) -> String {
        assert!(self.page_bufs.is_empty());
        assert!(self.link_stack.is_empty());

        format!("{}}}\n", self.buf)
    }
}

fn clean_name<'a, T: 'a>(name: T) -> String
where
    T: std::fmt::Display,
{
    name.to_string()
        .chars()
        .map(|v| match v {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '.' | '_' => v,
            _ => '_',
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::{
        assert_tree,
        digest::{
            mock::{LevelKey, MockHasher},
            Digest, ValueDigest,
        },
        MerkleSearchTree,
    };

    use super::*;

    const MOCK_VALUE: ValueDigest<32> = ValueDigest::new(Digest::new([0; 32]));

    #[test]
    fn test_dot_flat() {
        let p = Page::new(
            42,
            vec![
                Node::new(&"k1", MOCK_VALUE, None),
                Node::new(&"k2", MOCK_VALUE, None),
            ],
        );

        assert_tree!(page = p);
    }

    #[test]
    fn test_dot_high_page() {
        let h = Page::new(0, vec![Node::new(&"z_high1", MOCK_VALUE, None)]);

        let mut p = Page::new(
            42,
            vec![
                Node::new(&"k1", MOCK_VALUE, None),
                Node::new(&"k2", MOCK_VALUE, None),
            ],
        );
        p.insert_high_page(Box::new(h));

        assert_tree!(page = p);
    }

    #[test]
    fn test_dot_lt_pointer() {
        let lt_page_1 = Page::new(1, vec![Node::new(&"lt1", MOCK_VALUE, None)]);
        let lt_page_2 = Page::new(
            2,
            vec![Node::new(&"lt2", MOCK_VALUE, Some(Box::new(lt_page_1)))],
        );

        let p = Page::new(
            42,
            vec![
                Node::new(&"z_k1", MOCK_VALUE, Some(Box::new(lt_page_2))),
                Node::new(&"z_k2", MOCK_VALUE, None),
            ],
        );

        assert_tree!(page = p);
    }

    #[test]
    fn test_dot_high_page_lt_pointer() {
        let lt_page_1 = Page::new(10, vec![Node::new(&"lt1", MOCK_VALUE, None)]);
        let lt_page_2 = Page::new(
            11,
            vec![Node::new(&"lt2", MOCK_VALUE, Some(Box::new(lt_page_1)))],
        );

        let h1 = Page::new(0, vec![Node::new(&"zz_h1", MOCK_VALUE, None)]);
        let h2 = Page::new(1, vec![Node::new(&"zz_h2", MOCK_VALUE, Some(Box::new(h1)))]);

        let mut p = Page::new(
            42,
            vec![
                Node::new(&"z_k1", MOCK_VALUE, Some(Box::new(lt_page_2))),
                Node::new(&"z_k2", MOCK_VALUE, None),
            ],
        );
        p.insert_high_page(Box::new(h2));

        assert_tree!(page = p);
    }

    #[test]
    fn test_parent_lookup() {
        const MOCK_VALUE_1: ValueDigest<1> = ValueDigest::new(Digest::new([0; 1]));

        let mut p = Page::new(1, vec![Node::new(4, MOCK_VALUE_1, None)]);

        p.upsert(&3, 0, MOCK_VALUE_1);
        p.upsert(&1, 0, MOCK_VALUE_1);
        p.upsert(&2, 1, MOCK_VALUE_1);

        assert_tree!(page = p);
    }

    #[test]
    fn test_linear_children() {
        let mut t = MerkleSearchTree::new_with_hasher(MockHasher::default());

        t.upsert(&LevelKey::new("I", 2), &"bananas");
        t.upsert(&LevelKey::new("E", 1), &"bananas");
        t.upsert(&LevelKey::new("F", 0), &"bananas");

        assert_tree!(t);
    }
}
