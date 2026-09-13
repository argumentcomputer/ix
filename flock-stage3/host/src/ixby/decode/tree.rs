use super::{
  bytes::{Bits, Decoder},
  scalar::ScalarBits,
};
use crate::ixby::{
  byte_value::ByteDecodeLayout,
  object_value::ObjectLayout,
  value::{CTOR_TAG, ERASED_TAG},
};

pub(super) struct TreeContext<'a> {
  pub layout: ObjectLayout,
  pub bytes: ByteDecodeLayout,
  pub declarations: &'a [Bits],
}

pub(super) struct TreeBits {
  pub value: ScalarBits,
  pub bytes: Vec<Bits>,
  pub objects: Vec<Bits>,
  pub nodes: Vec<usize>,
}

impl Decoder {
  /// Fixed preorder positions own allocations, but only actual nodes consume
  /// bytes or node budget. A sibling cannot reset either budget.
  pub(super) fn tree(
    &mut self,
    enabled: usize,
    depth: usize,
    slot: usize,
    context: &TreeContext<'_>,
  ) -> TreeBits {
    let layout = context.layout;
    let tag = self.byte(enabled);
    let variants: Vec<_> =
      [0, 1, 3].map(|tag_value| self.eq_const(&tag, tag_value)).into();
    let valid = self.sum(&variants);
    self.require(enabled, valid);
    let scalar = self.and(enabled, variants[0]);
    let ctor = self.and(enabled, variants[1]);
    let erased = self.and(enabled, variants[2]);
    let value = self.scalar_with_bytes(scalar, context.bytes, slot);
    let first = self.read(128, &[(ctor, 16)]);
    let second = self.read(128, &[(ctor, 16)]);
    let member = self.u32(ctor);
    let ctor_tag = self.u32(ctor);
    let id = [first, second, self.pack(&[&member, &ctor_tag])];
    let fields = self.u32(ctor);
    let counts = self.bounded(&fields, layout.fields, ctor);
    let mut matches = Vec::new();
    for index in 0..layout.capacity.constructors() {
      let decl = &context.declarations[1 + 4 * index..5 + 4 * index];
      let mut matched = ctor;
      for (actual, expected) in id.iter().zip(decl) {
        let same = self.equal(actual, expected);
        matched = self.and(matched, same);
      }
      matched = self.and(matched, decl[3][32]);
      matches.push(matched);
      let same = self.equal(&fields, &decl[3][..32]);
      self.require(matched, same);
    }
    let found = self.sum(&matches);
    self.require(ctor, found);
    let mut index = vec![self.zero; 32];
    for (i, flag) in matches.iter().enumerate() {
      for (bit, target) in index.iter_mut().enumerate() {
        if i & (1 << bit) != 0 {
          *target = self.sum(&[*target, *flag]);
        }
      }
    }
    let mut object = vec![self.pack(&[&index, &fields, &[ctor]])];
    let mut bytes = value.bytes.clone();
    let mut children_objects = Vec::new();
    let mut nodes = vec![enabled];
    if depth == 1 {
      self.require_zero(ctor, &fields);
      object.resize(layout.record_words(), vec![self.zero; 128]);
    } else {
      for field in 0..layout.fields {
        let live = self.live(&counts, field, ctor);
        let child = self.tree(
          live,
          depth - 1,
          slot + 1 + field * layout.tree_slots(depth - 1),
          context,
        );
        object.extend([child.value.tag, child.value.payload]);
        bytes.extend(child.bytes);
        children_objects.extend(child.objects);
        nodes.extend(child.nodes);
      }
    }
    object.extend(children_objects);
    let ctor_tag = self.constant(128, CTOR_TAG);
    let erased_tag = self.constant(128, ERASED_TAG);
    let tag = self.choose(&[
      (self.one, &value.tag),
      (ctor, &ctor_tag),
      (erased, &erased_tag),
    ]);
    let handle = self.constant(128, slot as u64);
    let payload = self.choose(&[(self.one, &value.payload), (ctor, &handle)]);
    TreeBits {
      value: ScalarBits { tag, payload, bytes: Vec::new() },
      bytes,
      objects: object,
      nodes,
    }
  }
}
