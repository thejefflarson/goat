//! A hash of the memory layout of an interactive program's model, so a host
//! that swaps in a recompiled module can tell whether the old model's heap
//! objects still mean the same thing to it (ADR 0015, addendum).

use std::collections::HashMap;

use crate::mir::{HeapKind, Layout, LayoutId, MTy};

/// The model's layout as FNV-1a over a canonical walk of its type: scalar
/// kinds, record slot order, and each variant's tag numbers and payload slots.
/// Layouts are numbered by first visit rather than by `LayoutId`, so adding an
/// unrelated type elsewhere does not change the hash.
pub fn model_fingerprint(layouts: &[Layout], model: MTy) -> u64 {
    let mut walk = Walk {
        layouts,
        seen: HashMap::new(),
        bytes: Vec::new(),
    };
    walk.ty(model);
    walk.bytes
        .iter()
        .fold(0xcbf2_9ce4_8422_2325, |hash, &byte| {
            (hash ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3)
        })
}

struct Walk<'a> {
    layouts: &'a [Layout],
    seen: HashMap<LayoutId, u32>,
    bytes: Vec<u8>,
}

impl Walk<'_> {
    fn ty(&mut self, ty: MTy) {
        let (mark, id) = match ty {
            MTy::Int => return self.bytes.push(b'i'),
            MTy::Float => return self.bytes.push(b'f'),
            MTy::Bool => return self.bytes.push(b'b'),
            MTy::Unit => return self.bytes.push(b'u'),
            MTy::Ptr(HeapKind::Str) => return self.bytes.push(b's'),
            MTy::Ptr(HeapKind::Closure(_)) => return self.bytes.push(b'c'),
            MTy::Ptr(HeapKind::Record(id)) => (b'r', id),
            MTy::Ptr(HeapKind::Variant(id)) => (b'v', id),
            MTy::Ptr(HeapKind::List(id)) => (b'l', id),
        };
        self.bytes.push(mark);
        if let Some(&number) = self.seen.get(&id) {
            self.bytes.push(b'@');
            self.bytes.extend(number.to_le_bytes());
            return;
        }
        let number = self.seen.len() as u32;
        self.seen.insert(id, number);
        let layouts = self.layouts;
        match layouts.get(id.0 as usize) {
            Some(Layout::Record(fields)) => {
                self.bytes.extend((fields.len() as u32).to_le_bytes());
                fields.iter().for_each(|&field| self.ty(field));
            }
            Some(Layout::Variant(tags)) => {
                self.bytes.extend((tags.len() as u32).to_le_bytes());
                for (tag, fields) in tags {
                    self.bytes.extend(tag.to_le_bytes());
                    self.bytes.extend((fields.len() as u32).to_le_bytes());
                    fields.iter().for_each(|&field| self.ty(field));
                }
            }
            None => self.bytes.push(b'!'),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn record(fields: Vec<MTy>) -> Layout {
        Layout::Record(fields)
    }

    fn model(layouts: Vec<Layout>) -> u64 {
        model_fingerprint(&layouts, MTy::Ptr(HeapKind::Record(LayoutId(0))))
    }

    #[test]
    fn equal_layouts_hash_equal_and_a_changed_field_type_does_not() {
        let numbers = || model(vec![record(vec![MTy::Float, MTy::Float])]);
        assert_eq!(numbers(), numbers());
        assert_ne!(numbers(), model(vec![record(vec![MTy::Float, MTy::Bool])]));
        assert_ne!(numbers(), model(vec![record(vec![MTy::Float])]));
    }

    #[test]
    fn layout_ids_do_not_matter_only_structure() {
        let inner = MTy::Ptr(HeapKind::Record(LayoutId(1)));
        let shifted = MTy::Ptr(HeapKind::Record(LayoutId(2)));
        let a = vec![record(vec![inner]), record(vec![MTy::Int])];
        let b = vec![
            record(vec![shifted]),
            record(vec![MTy::Bool]),
            record(vec![MTy::Int]),
        ];
        assert_eq!(model(a), model(b));
    }

    #[test]
    fn a_variant_tag_number_changes_the_hash() {
        let tags = |tag: u32| {
            let variant = Layout::Variant(BTreeMap::from([(tag, vec![MTy::Float])]));
            let field = MTy::Ptr(HeapKind::Variant(LayoutId(1)));
            model(vec![record(vec![field]), variant])
        };
        assert_eq!(tags(3), tags(3));
        assert_ne!(tags(3), tags(4));
    }

    #[test]
    fn a_recursive_layout_terminates() {
        let list = Layout::Variant(BTreeMap::from([
            (0, vec![]),
            (1, vec![MTy::Float, MTy::Ptr(HeapKind::List(LayoutId(1)))]),
        ]));
        let field = MTy::Ptr(HeapKind::List(LayoutId(1)));
        assert_eq!(
            model(vec![record(vec![field]), list.clone()]),
            model(vec![record(vec![field]), list])
        );
    }
}
