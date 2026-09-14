use super::{
  bytes::{Bits, Decoder},
  scalar::ScalarBits,
};
use crate::ixby::{
  byte_value::ByteDecodeLayout,
  object_value::ObjectLayout,
  value::{CTOR_TAG, ERASED_TAG, PAP_TAG},
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
    let mut variants: Vec<_> =
      [0, 1, 3].map(|tag_value| self.eq_const(&tag, tag_value)).into();
    if layout.applications {
      variants.push(self.eq_const(&tag, 2));
    }
    let valid = self.sum(&variants);
    self.require(enabled, valid);
    let scalar = self.and(enabled, variants[0]);
    let ctor = self.and(enabled, variants[1]);
    let erased = self.and(enabled, variants[2]);
    let pap = if layout.applications {
      self.and(enabled, variants[3])
    } else {
      self.zero
    };
    let aggregate =
      if layout.applications { self.sum(&[ctor, pap]) } else { ctor };
    let value = self.scalar_with_bytes(scalar, context.bytes, slot);
    let first = self.read(128, &[(ctor, 16)]);
    let second = self.read(128, &[(ctor, 16)]);
    let member = self.u32(ctor);
    let ctor_tag = self.u32(ctor);
    let id = [first, second, self.pack(&[&member, &ctor_tag])];
    // PAP wire payload is function index followed by the captured-value vector.
    // The constructor identity above consumes no bytes on this branch.
    let function =
      if layout.applications { self.u32(pap) } else { vec![self.zero; 32] };
    let fields = self.u32(aggregate);
    let counts = self.bounded(&fields, layout.fields, aggregate);
    if layout.applications {
      let table = &context.declarations[layout.declaration_words()..];
      let in_range = self.less(&function, &table[0][32..64]);
      self.require(pap, in_range);
      let selectors: Vec<_> = (0..layout.functions)
        .map(|index| {
          let same = self.eq_const(&function, index as u64);
          self.and(pap, same)
        })
        .collect();
      let sources: Vec<_> = selectors
        .iter()
        .enumerate()
        .map(|(index, flag)| (*flag, &table[1 + index][..32]))
        .collect();
      let arity = self.choose(&sources);
      let unsaturated = self.less(&fields, &arity);
      self.require(pap, unsaturated);
    }
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
    let mut object = if layout.applications {
      let index = self.choose(&[(self.one, &index), (self.one, &function)]);
      vec![self.pack(&[&index, &fields, &[aggregate, pap]])]
    } else {
      vec![self.pack(&[&index, &fields, &[ctor]])]
    };
    let mut bytes = value.bytes.clone();
    let mut children_objects = Vec::new();
    let mut nodes = vec![enabled];
    if depth == 1 {
      self.require_zero(aggregate, &fields);
      object.resize(layout.record_words(), vec![self.zero; 128]);
    } else {
      for field in 0..layout.fields {
        let live = self.live(&counts, field, aggregate);
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
    let pap_tag = self.constant(128, PAP_TAG);
    let mut tag_sources =
      vec![(self.one, &value.tag), (ctor, &ctor_tag), (erased, &erased_tag)];
    if layout.applications {
      tag_sources.push((pap, &pap_tag));
    }
    let tag = self.choose(
      &tag_sources
        .iter()
        .map(|(flag, bits)| (*flag, bits.as_slice()))
        .collect::<Vec<_>>(),
    );
    let handle = self.constant(128, slot as u64);
    let payload =
      self.choose(&[(self.one, &value.payload), (aggregate, &handle)]);
    TreeBits {
      value: ScalarBits { tag, payload, bytes: Vec::new() },
      bytes,
      objects: object,
      nodes,
    }
  }
}
