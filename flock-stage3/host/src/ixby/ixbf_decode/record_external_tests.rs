//! Original-source record and grammar differentials. An independent AST
//! supplies the expected event schedule; each event now also satisfies the
//! constrained control relation, chaining its complete state through EOF.
//! This test traversal is not source/registry authentication or a complete
//! image proof, and the AST is never a verifier acceptance oracle.
use super::*;
use crate::ixby::ixbf::{
  self, Instruction as I, Operand as A, Operation as O, Scalar as S,
};
use flock_prover::{field::F128, r1cs::BlockR1cs};
use num_bigint::BigUint;
use std::{collections::BTreeSet, ffi::OsStr};

fn integer(value: &BigUint) -> u128 {
  let value = external_tests::word(value);
  u128::from(value.lo) | (u128::from(value.hi) << 64)
}

fn identity(id: &ixbf::ConstructorId, count: u128) -> [u128; 5] {
  [
    u128::from_le_bytes(id.block[..16].try_into().unwrap()),
    u128::from_le_bytes(id.block[16..].try_into().unwrap()),
    integer(&id.member),
    integer(&id.tag),
    count,
  ]
}

struct Tables {
  records: Vec<(RecordDecodeGate, BlockR1cs)>,
  links: Vec<(RecordLinkGate, BlockR1cs)>,
  natural: (NaturalDecodeGate, BlockR1cs),
  natural_limit: (NaturalLimitGate, BlockR1cs),
  payload: (PayloadCursorGate, BlockR1cs),
  utf8: (Utf8ChunkGate, BlockR1cs),
  span: (ByteArraySpanGate, BlockR1cs),
}

impl Tables {
  fn new() -> Self {
    let records = RecordKind::ALL
      .into_iter()
      .map(|kind| {
        let gate = RecordDecodeGate::new(3, kind).unwrap();
        let r1cs = gate.r1cs();
        (gate, r1cs)
      })
      .collect();
    let links = RecordLinkKind::ALL
      .into_iter()
      .map(|kind| {
        let gate = RecordLinkGate::new(3, kind).unwrap();
        let r1cs = gate.r1cs();
        (gate, r1cs)
      })
      .collect();
    let natural =
      NaturalDecodeGate::new(3, NaturalCapacity::new(4096).unwrap()).unwrap();
    let span = ByteArraySpanGate::new(3).unwrap();
    let natural_limit = NaturalLimitGate::new(3, natural.capacity()).unwrap();
    let payload = PayloadCursorGate::new(3).unwrap();
    let utf8 = Utf8ChunkGate::new(3).unwrap();
    Self {
      records,
      links,
      natural: (natural.clone(), natural.r1cs()),
      natural_limit: (natural_limit.clone(), natural_limit.r1cs()),
      payload: (payload.clone(), payload.r1cs()),
      utf8: (utf8.clone(), utf8.r1cs()),
      span: (span.clone(), span.r1cs()),
    }
  }
}

#[derive(Default, Debug)]
struct Census {
  records: [usize; 13],
  links: [usize; 5],
  naturals: usize,
  strings: usize,
  bytes: usize,
  grammar_steps: usize,
  payload_steps: usize,
  natural_limit_steps: usize,
  utf8_steps: usize,
}

struct Check<'a, 'b> {
  source: &'a [u8],
  cursor: usize,
  artifact: &'b ixbf::Artifact<'b>,
  tables: &'b Tables,
  census: &'b mut Census,
  grammar: grammar_tests::Trace,
}

impl Check<'_, '_> {
  fn payload(&mut self, length: F128) -> [F128; 4] {
    let (gate, r1cs) = &self.tables.payload;
    let input = [self.grammar.state[0], length, F128::ONE];
    let output = payload::evaluate(&input);
    assert_eq!(output[3], F128::ZERO);
    scalar_payload_tests::checked(gate.plan(), r1cs, &input, &output);
    self.census.payload_steps += 1;
    output
  }
  fn record(
    &mut self,
    kind: RecordKind,
    bounds: [u128; 3],
    expected: &[u128],
  ) -> [F128; RECORD_FIELDS] {
    let (gate, r1cs) = &self.tables.records[kind as usize];
    let input = record_tests::input(
      self.source,
      self.cursor,
      bounds.map(record_tests::word),
    );
    assert!(
      tests::satisfies(r1cs, &record_tests::bits(gate, &input)),
      "{kind:?} at {}",
      self.cursor
    );
    let output = record::evaluate(kind, &input);
    let mut fields = [F128::ZERO; RECORD_FIELDS];
    for (target, expected) in fields.iter_mut().zip(expected) {
      *target = record_tests::word(*expected);
    }
    assert_eq!(output[..RECORD_FIELDS], fields, "{kind:?} at {}", self.cursor);
    assert_eq!(
      output[RECORD_FIELDS + 1],
      F128::ZERO,
      "{kind:?} at {}",
      self.cursor
    );
    assert_eq!(output[RECORD_FIELDS].hi, self.source.len() as u64);
    assert_eq!(self.grammar.state[0].lo as usize, self.cursor);
    self.grammar.step(
      GrammarEvent::Record(kind),
      bounds.map(record_tests::word),
      &output[..RECORD_FIELDS],
      output[RECORD_FIELDS],
    );
    self.cursor = output[RECORD_FIELDS].lo as usize;
    self.census.records[kind as usize] += 1;
    output[..RECORD_FIELDS].try_into().unwrap()
  }
  fn link(&mut self, kind: RecordLinkKind, left: [u128; 5], right: [u128; 5]) {
    let (gate, r1cs) = &self.tables.links[kind as usize];
    let input = link_tests::input(left, right);
    assert!(tests::satisfies(r1cs, &link_tests::bits(gate, &input)));
    assert_eq!(link::evaluate(kind, &input), F128::ZERO);
    self.census.links[kind as usize] += 1;
  }
  fn scalar(&mut self, value: &S<'_>) {
    let start = self.cursor;
    let (tag, payload) = match value {
      S::Nat(_) => (0, 0),
      S::String(_) => (1, 0),
      S::Bool(value) => (2, u128::from(*value)),
      S::Word32(value) => (3, u128::from(*value)),
      S::Goldilocks(value) => (4, u128::from(*value)),
      S::Extension(value) => {
        (5, u128::from(value[0]) | (u128::from(value[1]) << 64))
      },
      S::Bytes(_) => (6, 0),
    };
    self.record(RecordKind::Scalar, [0; 3], &[tag, payload]);
    match value {
      S::Nat(value) => {
        let canonical = tests::natural_bytes(value);
        let raw = &self.source[self.cursor..self.cursor + canonical.len()];
        assert_eq!(raw, canonical);
        let length = F128::new(raw.len() as u64, 0);
        let payload = self.payload(length);
        let (gate, r1cs) = &self.tables.natural;
        let input = tests::input(gate, raw, true);
        assert_eq!(input[0], payload[0]);
        assert!(tests::satisfies(r1cs, &tests::bits(gate, &input)));
        let mut magnitude = natural::evaluate(gate.capacity(), &input);
        assert_eq!(magnitude.pop(), Some(F128::ZERO));
        let (limit_gate, limit_r1cs) = &self.tables.natural_limit;
        let mut input =
          vec![self.grammar.state[grammar::LIMITS + 7], F128::ONE];
        assert_eq!(
          input[0],
          external_tests::word(&self.artifact.limits().nat_bits)
        );
        input.extend(magnitude);
        let output = natural_limit::evaluate(limit_gate.capacity(), &input);
        assert_eq!(output, [F128::new(value.bits(), 0), F128::ZERO]);
        scalar_payload_tests::checked(
          limit_gate.plan(),
          limit_r1cs,
          &input,
          &output,
        );
        self.grammar.step(
          GrammarEvent::Natural,
          [F128::ZERO; 3],
          &[length],
          payload[2],
        );
        self.cursor += raw.len();
        self.census.naturals += 1;
        self.census.natural_limit_steps += 1;
      },
      S::String(value) => {
        let count = self.record(
          RecordKind::Count,
          [integer(&self.artifact.limits().string_bytes), 0, 0],
          &[value.len() as u128],
        );
        assert_eq!(
          &self.source[self.cursor..self.cursor + value.len()],
          value.as_bytes()
        );
        // Use the actual Count output for both consumers. Proof tests share
        // the same circuit wire, not just this native differential's value.
        let payload = self.payload(count[0]);
        let mut state = count[0];
        let mut cursor = self.grammar.state[0];
        loop {
          let (gate, r1cs) = &self.tables.utf8;
          let input =
            scalar_payload_tests::utf8_input(self.source, cursor, state, true);
          let output = utf8::evaluate(&input);
          assert_eq!(output[2], F128::ZERO);
          scalar_payload_tests::checked(gate.plan(), r1cs, &input, &output);
          cursor = output[0];
          state = output[1];
          self.census.utf8_steps += 1;
          if state.lo == 0 {
            break;
          }
        }
        assert_eq!(state, F128::ZERO);
        assert_eq!(cursor, payload[2]);
        if !value.is_empty() {
          self.grammar.step(
            GrammarEvent::StringPayload,
            [F128::ZERO; 3],
            &[],
            payload[2],
          );
        }
        self.cursor += value.len();
        self.census.strings += 1;
      },
      S::Bytes(value) => {
        let (gate, r1cs) = &self.tables.span;
        let input = byte_span_tests::input(
          self.source,
          start,
          external_tests::word(&self.artifact.limits().byte_array_bytes),
        );
        assert!(tests::satisfies(r1cs, &byte_span_tests::bits(gate, &input)));
        let output = byte_span::evaluate(&input);
        assert_eq!(output[2], F128::ZERO);
        assert_eq!(output[0].hi, value.len() as u64);
        assert_eq!(
          &self.source[output[0].lo as usize..output[1].lo as usize],
          *value
        );
        let count = self.record(
          RecordKind::Count,
          [integer(&self.artifact.limits().byte_array_bytes), 0, 0],
          &[value.len() as u128],
        );
        assert_eq!(self.cursor as u64, output[0].lo);
        let payload = self.payload(count[0]);
        assert_eq!(payload[1..3], output[..2]);
        if !value.is_empty() {
          self.grammar.step(
            GrammarEvent::BytesPayload,
            [F128::ZERO; 3],
            &[],
            output[1],
          );
        }
        self.cursor = output[1].lo as usize;
        self.census.bytes += 1;
      },
      _ => {},
    }
  }
  fn operand(&mut self, locals: u128, value: &A<'_>) {
    let fields = match value {
      A::Local(index) => [0, integer(index)],
      A::Literal(_) => [1, 0],
      A::Erased => [2, 0],
    };
    self.record(RecordKind::Operand, [locals, 0, 0], &fields);
    if let A::Literal(value) = value {
      self.scalar(value);
    }
  }
  fn args(&mut self, locals: u128, args: &[A<'_>], count: bool) {
    if count {
      self.record(
        RecordKind::Count,
        [integer(&self.artifact.limits().operands), 0, 0],
        &[args.len() as u128],
      );
    }
    for arg in args {
      self.operand(locals, arg);
    }
  }
  fn arity(&mut self, target: usize, count: usize, partial: bool) {
    let arity = integer(&self.artifact.functions()[target].arity);
    self.link(
      if partial {
        RecordLinkKind::PartialArity
      } else {
        RecordLinkKind::ExactArity
      },
      [target as u128, count as u128, 0, 0, 0],
      [target as u128, arity, 0, 0, 0],
    );
  }
  fn frame(
    &mut self,
    function: usize,
    target: usize,
    locals: u128,
    added: u128,
  ) {
    let target_locals =
      integer(&self.artifact.functions()[function].blocks[target].locals);
    let limit = integer(&self.artifact.limits().locals);
    self.link(
      RecordLinkKind::SuccessorFrame,
      [target as u128, locals, added, 0, 0],
      [target as u128, target_locals, limit, 0, 0],
    );
  }
  fn target(&mut self, function: usize, target: usize) {
    let bound = self.artifact.functions()[function].blocks.len() as u128;
    self.record(RecordKind::Index, [bound, 0, 0], &[target as u128]);
  }
  fn operation(&mut self, function: usize, locals: u128, op: &O<'_>) {
    let limits = self.artifact.limits();
    let bounds = [
      integer(&limits.operands),
      self.artifact.constructors().len() as u128,
      self.artifact.functions().len() as u128,
    ];
    let fields = match op {
      O::Copy(_) => [0, 0, 0, 0, 0],
      O::Primitive(primitive, args) => [
        1,
        u128::from(primitive.opcode()),
        0,
        args.len() as u128,
        primitive.arity() as u128,
      ],
      O::Construct(target, args) => {
        [2, 0, *target as u128, args.len() as u128, 0]
      },
      O::Project(_, _) => [3, 0, 0, 0, 0],
      O::Closure(target, args) => {
        [4, 0, *target as u128, args.len() as u128, 0]
      },
      O::Call(target, args) => [5, 0, *target as u128, args.len() as u128, 0],
      O::CallSelf(args) => [6, 0, 0, args.len() as u128, 0],
      O::Apply(_, _) => [7, 0, 0, 0, 0],
    };
    self.record(RecordKind::Operation, bounds, &fields);
    match op {
      O::Copy(value) => self.operand(locals, value),
      O::Primitive(_, args) => self.args(locals, args, false),
      O::Construct(target, args) => {
        self.args(locals, args, false);
        let fields = integer(&self.artifact.constructors()[*target].fields);
        self.link(
          RecordLinkKind::ExactArity,
          [*target as u128, args.len() as u128, 0, 0, 0],
          [*target as u128, fields, 0, 0, 0],
        );
      },
      O::Project(value, field) => {
        self.operand(locals, value);
        self.record(RecordKind::Metadata, [0; 3], &[integer(field)]);
      },
      O::Closure(target, args) | O::Call(target, args) => {
        self.args(locals, args, false);
        self.arity(*target, args.len(), matches!(op, O::Closure(_, _)));
      },
      O::CallSelf(args) => {
        self.args(locals, args, false);
        self.arity(function, args.len(), false);
      },
      O::Apply(value, args) => {
        self.operand(locals, value);
        self.args(locals, args, true);
      },
    }
  }
  fn instruction(
    &mut self,
    function: usize,
    locals: u128,
    instruction: &I<'_>,
  ) {
    match instruction {
      I::Let(op, next) => {
        self.operation(function, locals, op);
        self.target(function, *next);
        self.frame(function, *next, locals, 1);
      },
      I::Return(value) => self.operand(locals, value),
      I::TailCall(target, args) => {
        self.record(
          RecordKind::Index,
          [self.artifact.functions().len() as u128, 0, 0],
          &[*target as u128],
        );
        self.args(locals, args, true);
        self.arity(*target, args.len(), false);
      },
      I::TailCallSelf(args) => {
        self.args(locals, args, true);
        self.arity(function, args.len(), false);
      },
      I::TailApply(value, args) => {
        self.operand(locals, value);
        self.args(locals, args, true);
      },
      I::CaseConstructor(value, alternatives) => {
        self.operand(locals, value);
        self.record(
          RecordKind::Count,
          [integer(&self.artifact.limits().constructors), 0, 0],
          &[alternatives.len() as u128],
        );
        let mut seen = BTreeSet::new();
        for alternative in alternatives {
          // The set check is native fixture validation, not a constrained
          // duplicate-alternative/global-coverage argument.
          assert!(seen.insert(alternative.constructor));
          let bounds = [
            self.artifact.constructors().len() as u128,
            self.artifact.functions()[function].blocks.len() as u128,
            0,
          ];
          self.record(
            RecordKind::Alternative,
            bounds,
            &[alternative.constructor as u128, alternative.target as u128],
          );
          let fields = integer(
            &self.artifact.constructors()[alternative.constructor].fields,
          );
          self.frame(function, alternative.target, locals, fields);
        }
      },
      I::CaseNat(value, first, second) | I::Branch(value, first, second) => {
        self.operand(locals, value);
        self.target(function, *first);
        self.target(function, *second);
        self.frame(function, *first, locals, 0);
        self.frame(
          function,
          *second,
          locals,
          u128::from(matches!(instruction, I::CaseNat(_, _, _))),
        );
      },
    }
  }
}

fn instruction_tag(instruction: &I<'_>) -> u128 {
  match instruction {
    I::Let(_, _) => 0,
    I::Return(_) => 1,
    I::TailCall(_, _) => 2,
    I::TailCallSelf(_) => 3,
    I::TailApply(_, _) => 4,
    I::CaseConstructor(_, _) => 5,
    I::CaseNat(_, _, _) => 6,
    I::Branch(_, _, _) => 7,
  }
}

fn program(bytes: &[u8], tables: &Tables, census: &mut Census) {
  let artifact =
    ixbf::decode_program(bytes, ixbf::DecodeLimits::default()).unwrap();
  let header = HeaderDecodeGate::new(3).unwrap();
  let input = header_tests::input(bytes, bytes.len() as u64);
  assert!(tests::satisfies(
    &header.r1cs(),
    &header_tests::bits(&header, &input)
  ));
  let output = header::evaluate(&input);
  assert_eq!(output[..14], external_tests::expected_header(&artifact));
  assert_eq!(output[14], F128::ZERO);
  let mut initial = [F128::ZERO; GRAMMAR_STATE_WORDS];
  initial[0] = F128::new(0, bytes.len() as u64);
  let mut grammar = grammar_tests::Trace::new(GrammarKind::Program, initial);
  grammar.step(
    GrammarEvent::Header,
    [F128::new(bytes.len() as u64, 0), F128::ZERO, F128::ZERO],
    &output[..13],
    output[13],
  );
  let mut check = Check {
    source: bytes,
    cursor: output[13].lo as usize,
    artifact: &artifact,
    tables,
    census,
    grammar,
  };
  for declaration in artifact.constructors() {
    check.record(
      RecordKind::Constructor,
      [integer(&artifact.limits().operands), 0, 0],
      &identity(&declaration.id, integer(&declaration.fields)),
    );
  }
  for (index, first) in artifact.constructors().iter().enumerate() {
    for second in &artifact.constructors()[..index] {
      check.link(
        RecordLinkKind::DistinctConstructors,
        identity(&first.id, integer(&first.fields)),
        identity(&second.id, integer(&second.fields)),
      );
    }
  }
  check.record(
    RecordKind::Count,
    [integer(&artifact.limits().functions), 0, 0],
    &[artifact.functions().len() as u128],
  );
  for (index, function) in artifact.functions().iter().enumerate() {
    let limits = artifact.limits();
    check.record(
      RecordKind::Function,
      [
        integer(&limits.operands),
        integer(&limits.locals),
        integer(&limits.blocks),
      ],
      &[
        integer(&function.arity),
        function.entry as u128,
        function.blocks.len() as u128,
      ],
    );
    check.frame(index, function.entry, integer(&function.arity), 0);
    for block in &function.blocks {
      assert_eq!(check.cursor, block.encoded.start, "original block start");
      let locals = integer(&block.locals);
      check.record(
        RecordKind::Block,
        [integer(&limits.locals), 0, 0],
        &[locals, instruction_tag(&block.instruction)],
      );
      check.instruction(index, locals, &block.instruction);
      assert_eq!(
        check.cursor, block.encoded.end,
        "complete original block coverage"
      );
    }
  }
  check.grammar.finish();
  check.census.grammar_steps += check.grammar.steps;
  assert_eq!(
    check.grammar.state[grammar::FUNCTION_INDEX].lo as usize,
    artifact.functions().len()
  );
  assert_eq!(
    check.grammar.state[grammar::ENTRY_ARITY],
    external_tests::word(&artifact.functions()[artifact.entry()].arity)
  );
  // The event schedule is independent host test preparation. The component
  // relation enforces its grammar/EOF; complete-image proof wiring and source
  // authentication remain separate from this differential.
  assert_eq!(check.cursor, bytes.len());
}

fn forest(
  artifact: &ixbf::Artifact<'_>,
  source: &[u8],
  forest: &ixbf::ValueForest<'_>,
  is_input: bool,
  tables: &Tables,
  census: &mut Census,
) {
  let mut initial = [F128::ZERO; GRAMMAR_STATE_WORDS];
  initial[0] = F128::new(0, source.len() as u64);
  initial[grammar::CTORS] = F128::new(artifact.constructors().len() as u64, 0);
  initial[grammar::FUNCTIONS] = F128::new(artifact.functions().len() as u64, 0);
  let header = external_tests::expected_header(artifact);
  initial[grammar::LIMITS..grammar::LIMITS + 10].copy_from_slice(&header[..10]);
  initial[grammar::ENTRY] = F128::new(artifact.entry() as u64, 0);
  initial[grammar::ENTRY_ARITY] =
    external_tests::word(&artifact.functions()[artifact.entry()].arity);
  initial[grammar::FUEL] = external_tests::word(artifact.max_steps());
  let grammar = grammar_tests::Trace::new(
    if is_input { GrammarKind::Input } else { GrammarKind::Output },
    initial,
  );
  let mut check =
    Check { source, cursor: 0, artifact, tables, census, grammar };
  let limits = artifact.limits();
  let nodes = integer(&limits.input_nodes);
  if is_input {
    check.record(
      RecordKind::Input,
      [
        integer(&limits.operands),
        integer(&artifact.functions()[artifact.entry()].arity),
        nodes,
      ],
      &[forest.roots().len() as u128],
    );
  } else {
    check.record(RecordKind::Output, [nodes, 0, 0], &[1]);
  }
  for (index, node) in forest.nodes().iter().enumerate() {
    let mut fields = [0u128; RECORD_FIELDS];
    match &node.kind {
      ixbf::ValueKind::Scalar(_) => {},
      ixbf::ValueKind::Constructor(id) => {
        fields[0] = 1;
        fields[1..].copy_from_slice(&identity(id, node.children.len() as u128));
      },
      ixbf::ValueKind::PartialApplication(function) => {
        fields[0] = 2;
        fields[1] = *function as u128;
        fields[5] = node.children.len() as u128;
      },
      ixbf::ValueKind::Erased => fields[0] = 3,
    }
    check.record(
      RecordKind::Value,
      [
        integer(&limits.operands),
        artifact.functions().len() as u128,
        nodes - index as u128 - 1,
      ],
      &fields,
    );
    match &node.kind {
      ixbf::ValueKind::Scalar(value) => check.scalar(value),
      ixbf::ValueKind::Constructor(id) => {
        let declaration = artifact
          .constructors()
          .iter()
          .find(|declaration| declaration.id == *id)
          .unwrap();
        check.link(
          RecordLinkKind::ConstructorValue,
          identity(id, node.children.len() as u128),
          identity(&declaration.id, integer(&declaration.fields)),
        );
      },
      ixbf::ValueKind::PartialApplication(function) => {
        check.arity(*function, node.children.len(), true)
      },
      ixbf::ValueKind::Erased => {},
    }
  }
  assert_eq!(check.cursor, source.len());
  check.grammar.finish();
  assert_eq!(
    check.grammar.state[grammar::SEEN].lo as usize,
    forest.nodes().len()
  );
  check.census.grammar_steps += check.grammar.steps;
}

#[test]
#[ignore = "requires the independent compiler corpus and exact Init image for original body-record and reference differentials"]
fn original_compiler_corpus_and_full_init_body_records_match_constraints() {
  let tables = Tables::new();
  let directory = external_tests::path("IXBY_IXBF_CORPUS");
  let mut files: Vec<_> = std::fs::read_dir(&directory)
    .unwrap()
    .map(|entry| entry.unwrap())
    .filter(|entry| {
      entry.file_type().unwrap().is_file()
        && entry.path().extension() == Some(OsStr::new("ixby"))
    })
    .map(|entry| entry.path())
    .collect();
  files.sort();
  assert!(files.len() >= 81);
  let mut corpus = Census::default();
  for file in &files {
    program(&external_tests::read(file), &tables, &mut corpus);
  }
  let image =
    external_tests::read(&external_tests::path("IXBY_IXBF_STAGE2_IMAGE"));
  assert_eq!(
    blake3::hash(&image).to_hex().as_str(),
    "a661dfede7c18bfb915d031393ffb258e65c21940d48039cdf44ab16428fe301"
  );
  let mut init = Census::default();
  program(&image, &tables, &mut init);
  assert_eq!(init.records[RecordKind::Constructor as usize], 146);
  assert_eq!(init.records[RecordKind::Function as usize], 681);
  assert_eq!(init.records[RecordKind::Block as usize], 6763);
  assert_eq!(init.naturals, 608);
  assert_eq!(init.bytes, 6);
  assert_eq!(init.natural_limit_steps, 608);
  assert_eq!(init.payload_steps, 614);
  assert_eq!(init.utf8_steps, 0);
  assert_eq!(corpus.natural_limit_steps, corpus.naturals);
  assert_eq!(
    corpus.payload_steps,
    corpus.naturals + corpus.strings + corpus.bytes
  );
  eprintln!(
    "original-source records: {} corpus programs: {corpus:?}; exact Init: {init:?}",
    files.len()
  );
  eprintln!(
    "body records, complete grammar transitions and local reference constraints pass; source/lookup authentication and whole-image admission are not proved"
  );
}

#[test]
#[ignore = "requires independent identity and retained Init transports for original value-prefix and arity-link differentials"]
fn original_identity_and_init_transport_value_records_match_constraints() {
  let tables = Tables::new();
  let directory = external_tests::path("IXBY_IXBF_CORPUS");
  let mut census = Census::default();
  for init in [false, true] {
    let (program, input, output) = if init {
      (
        external_tests::read(&external_tests::path("IXBY_IXBF_STAGE2_IMAGE")),
        external_tests::read(&external_tests::path("IXBY_IXBF_INIT_INPUT")),
        external_tests::read(&external_tests::path("IXBY_IXBF_INIT_OUTPUT")),
      )
    } else {
      (
        external_tests::read(&directory.join("identity.ixby")),
        external_tests::read(&directory.join("identity.ixbi")),
        external_tests::read(&directory.join("identity.ixbo")),
      )
    };
    if init {
      for (bytes, hash) in [
        (
          &program,
          "a661dfede7c18bfb915d031393ffb258e65c21940d48039cdf44ab16428fe301",
        ),
        (
          &input,
          "713a6a0b72dbaad673192c38c6e10115b1386482394cc22a945837c1a03f11c8",
        ),
        (
          &output,
          "3e6cb8264cfb6d253c41f22aa05221805a58f857d73877305adfed0781115a28",
        ),
      ] {
        assert_eq!(blake3::hash(bytes).to_hex().as_str(), hash);
      }
    }
    let artifact =
      ixbf::decode_program(&program, ixbf::DecodeLimits::default()).unwrap();
    let input_model =
      ixbf::decode_input(&artifact, &input, ixbf::DecodeLimits::default())
        .unwrap();
    let output_model =
      ixbf::decode_output(&artifact, &output, ixbf::DecodeLimits::default())
        .unwrap();
    forest(&artifact, &input, input_model.values(), true, &tables, &mut census);
    forest(
      &artifact,
      &output,
      output_model.values(),
      false,
      &tables,
      &mut census,
    );
  }
  eprintln!(
    "original identity/Init value records and complete forest control: {census:?}; payload/registry authentication remain unproved"
  );
}
