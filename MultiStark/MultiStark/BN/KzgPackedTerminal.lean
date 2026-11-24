import MultiStark.BN.KzgPackedProgram

/-! Terminal verification of one fixed predecessor key. The key is part of
this program's fixed tables, so the terminal's own circuit (and therefore its
verifying key) commits to it: no key digest is hashed or exposed. Only the
claims digest is public.

The key's circuits section (graph nodes, constraint roots, lookups, shapes and
copy counts) is parsed at export by `parseKey`, which applies every check of
the packed verifier's in-circuit grammar (`KzgPackedDeserialize::circuits`),
and is stored as structured tables. The terminal rebuilds from them exactly
the `KzgDeserialize::Circuit` list that grammar returns for these bytes,
except that each circuit's constraint graph stays in `node_values` and its
node list holds only the graph's base index there. `verify_key` is
`KzgPackedVerifier::verify` with the `KzgAlgebra` graph evaluation reading
nodes from that table; nothing else in the verifier reads node lists. The
remaining key bytes (header, seed, anchors and fixed commitment) are still a
word table parsed in circuit. -/
namespace MultiStark.Source

def kzgPackedTerminal : Aiur.Modules.Program Nat := aiur⟦
module KzgPackedTerminal {
  -- Replaced, with every table below, by `withKey`.
  const KEY_WORDS: Field = 0;
  const KEY_OFFSET: Field = 0;
  const CIRCUITS: Field = 0;
  table key_inputs: (Field,) {}
  table key_values: [Field; 4] {}
  map key_word(index: Field) -> [Field; 4] = key_inputs => key_values;
  -- One row per constructor, in tag order; `withKey` instantiates them.
  table node_templates: KzgDeserialize::Node {
    KzgDeserialize::Node::Const(0), KzgDeserialize::Node::Var(0, 0, 0), KzgDeserialize::Node::Public(0),
    KzgDeserialize::Node::First, KzgDeserialize::Node::Last, KzgDeserialize::Node::Transition,
    KzgDeserialize::Node::Add(0, 0), KzgDeserialize::Node::Sub(0, 0), KzgDeserialize::Node::Mul(0, 0),
    KzgDeserialize::Node::Neg(0) }
  table node_inputs: (Field,) {}
  table node_values: KzgDeserialize::Node {}
  map key_node(index: Field) -> KzgDeserialize::Node = node_inputs => node_values;
  table id_inputs: (Field,) {}
  table id_values: [Field; 1] {}
  map key_id(index: Field) -> [Field; 1] = id_inputs => id_values;
  -- Multiplicity node, first argument id, argument count.
  table lookup_inputs: (Field,) {}
  table lookup_values: [Field; 3] {}
  map key_lookup(index: Field) -> [Field; 3] = lookup_inputs => lookup_values;
  -- Shape (8), node base and count, root base and count, lookup base and
  -- count, main and fixed next-row flags, copy count.
  table circuit_inputs: (Field,) {}
  table circuit_values: [Field; 17] {}
  map key_circuit(index: Field) -> [Field; 17] = circuit_inputs => circuit_values;

  fn key_words(index: Field, remaining: Field) -> KzgIO::Words {
    match remaining {
      0 => &(Lists::Node::Nil),
      _ => &(Lists::Node::Cons(UInt32::from_fields(key_word(index)), key_words(index + 1, remaining - 1))),
    }
  }

  fn ids(index: Field, count: Field) -> Lists::List<Field> {
    match count {
      0 => &(Lists::Node::Nil),
      _ => {let id = key_id(index); &(Lists::Node::Cons(id[0], ids(index + 1, count - 1)))},
    }
  }

  fn lookups(index: Field, count: Field) -> Lists::List<KzgDeserialize::Lookup> {
    match count {
      0 => &(Lists::Node::Nil),
      _ => {
        let v = key_lookup(index);
        &(Lists::Node::Cons(KzgDeserialize::Lookup::Mk(v[0], ids(v[1], v[2])), lookups(index + 1, count - 1)))
      },
    }
  }

  fn circuits(index: Field, count: Field) -> Lists::List<KzgDeserialize::Circuit> {
    match count {
      0 => &(Lists::Node::Nil),
      _ => {
        let v = key_circuit(index);
        -- The graph stays in `node_values`: its node list holds only the
        -- base index there, read by `verify_frames`.
        let base = &(Lists::Node::Cons(KzgDeserialize::Node::Const(v[8]), &(Lists::Node::Nil)));
        let circuit = KzgDeserialize::Circuit::Mk([v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]],
          base, ids(v[10], v[11]), lookups(v[12], v[13]), v[14], v[15]);
        KzgPackedDeserialize::copies_of(circuit, v[16], circuits(index + 1, count - 1))
      },
    }
  }

  -- `KzgPackedDeserialize::key` on the remaining bytes, with the circuits
  -- section taken from the tables.
  fn key() -> KzgPackedDeserialize::Key {
    let input = (key_words(0, KEY_WORDS), KEY_OFFSET);
    let input = KzgIO::magic(input, [73,88,65,85,83,75,48,50]);
    let (seed, input) = KzgIO::blob(input);
    let (max_log, input) = KzgIO::u32(input);
    assert_eq!(UInt32::less_than_fields(max_log, 29), 1, "packed trace cap exceeds Fr domain");
    assert_eq!(UInt32::less_than_fields(0, max_log), 1, "packed trace cap below two rows");
    let (budget, input) = KzgIO::u32(input); KzgDeserialize::supported_power(budget, 1, 28);
    let (generator, input) = KzgIO::point(input);
    let (anchors, input) = KzgIO::read_bytes(input, 128);
    let circuits = circuits(0, CIRCUITS);
    KzgPackedDeserialize::Key::Mk(seed, max_log, budget, generator, anchors, circuits,
      KzgPackedDeserialize::fixed(input, Lists::length(circuits)))
  }

  -- `KzgAlgebra::eval_at`, with node `index` of the graph at `base` read from
  -- `node_values` instead of a node list.
  fn eval_at(base: Field, index: Field, context: KzgAlgebra::Context) -> Field {
    let (main,main_next,fixed,fixed_next,stage2,stage2_next,publics,first,last,transition) = *context;
    match key_node(base + index) {
      KzgDeserialize::Node::Const(value) => value,
      KzgDeserialize::Node::Var(source,offset,column) => {
        let row = match source+source+offset {0=>fixed,1=>fixed_next,2=>main,3=>main_next,4=>stage2,5=>stage2_next};
        Lists::lookup(row,column)
      },
      KzgDeserialize::Node::Public(index) => match index {0=>publics[0],1=>publics[1],2=>publics[2],3=>publics[3]},
      KzgDeserialize::Node::First => first,
      KzgDeserialize::Node::Last => last,
      KzgDeserialize::Node::Transition => transition,
      KzgDeserialize::Node::Add(a,b) => eval_at(base,a,context)+eval_at(base,b,context),
      KzgDeserialize::Node::Sub(a,b) => eval_at(base,a,context)-eval_at(base,b,context),
      KzgDeserialize::Node::Mul(a,b) => eval_at(base,a,context)*eval_at(base,b,context),
      KzgDeserialize::Node::Neg(a) => 0-eval_at(base,a,context),
    }
  }

  -- `KzgAlgebra::fold_roots`, `lookup_fingerprint`, `group_summary` and
  -- `fold_lookups` over the graph at `base`.
  fn fold_roots(roots: Lists::List<Field>, base: Field, context: KzgAlgebra::Context, alpha: Field, accumulator: Field) -> Field {
    match *roots {
      Lists::Node::Nil=>accumulator,
      Lists::Node::Cons(root,rest)=>fold_roots(rest,base,context,alpha,accumulator*alpha+eval_at(base,root,context)),
    }
  }

  fn lookup_fingerprint(args: Lists::List<Field>, base: Field, context: KzgAlgebra::Context, gamma: Field) -> Field {
    match *args {Lists::Node::Nil=>0,
      Lists::Node::Cons(arg,rest)=>eval_at(base,arg,context)+gamma*lookup_fingerprint(rest,base,context,gamma)}
  }

  fn group_summary(lookups: Lists::List<KzgDeserialize::Lookup>, remaining: Field,
      base: Field, context: KzgAlgebra::Context, beta: Field, gamma: Field, product: Field, numerator: Field)
      -> (Field,Field,Lists::List<KzgDeserialize::Lookup>) {
    match remaining {
      0=>(product,numerator,lookups),
      _=>match *lookups {
        Lists::Node::Nil=>(product,numerator,lookups),
        Lists::Node::Cons(lookup,rest)=>{
          let KzgDeserialize::Lookup::Mk(multiplicity,args)=lookup;
          let message=beta+lookup_fingerprint(args,base,context,gamma);
          group_summary(rest,remaining-1,base,context,beta,gamma,
            product*message,numerator*message+eval_at(base,multiplicity,context)*product)
        },
      },
    }
  }

  fn fold_lookups(lookups: Lists::List<KzgDeserialize::Lookup>, size: Field, index: Field,
      base: Field, context: KzgAlgebra::Context, beta: Field, gamma: Field, alpha: Field,
      current: Lists::List<Field>, next: Lists::List<Field>, injection: Field, accumulator: Field) -> Field {
    match *lookups {
      Lists::Node::Nil=>accumulator*alpha+Lists::lookup(next,0)-Lists::lookup(current,0)+injection,
      _=>{
        let (product,numerator,rest)=group_summary(lookups,size,base,context,beta,gamma,1,0);
        let last=Lists::is_empty(rest);
        let target=match last {1=>Lists::lookup(next,0)+injection,0=>Lists::lookup(current,index+1)};
        let value=product*(target-Lists::lookup(current,index))-numerator;
        let accumulator=accumulator*alpha+value;
        match last {1=>accumulator,0=>fold_lookups(rest,size,index+1,base,context,beta,gamma,alpha,current,next,injection,accumulator)}
      },
    }
  }

  -- `KzgPackedShape::verify_frames` over the tabled graphs.
  fn verify_frames(frames:Lists::List<KzgPackedShape::Frame>,beta:Field,gamma:Field,alpha:Field,zeta:Field,accumulator:Field)->() {
    match *frames {
      Lists::Node::Nil=>{assert_eq!(accumulator,0,"packed unbalanced final accumulator");()},
      Lists::Node::Cons(frame,rest)=>{
        let KzgPackedShape::Frame::Mk(circuit,log,next_accumulator,mo,so,qo,fo,_owns)=frame;
        let KzgDeserialize::Circuit::Mk(shape,nodes,roots,lookups,_mn,_fn)=circuit;
        let Lists::Node::Cons(head,_none)=*nodes;
        let KzgDeserialize::Node::Const(base)=head;
        let z_n=KzgAlgebra::exp_power2(zeta,log);let vanishing=z_n-1;
        assert_eq!(Fields::is_zero(vanishing),0,"packed challenge lies on trace domain");
        let g=KzgAlgebra::two_adic_gen(log);let transition=zeta-1/g;
        let first=vanishing/(zeta-1);let last=vanishing/transition;
        let current=KzgAlgebra::first_row(so);let next=KzgAlgebra::next_row(so);
        let context=&(KzgAlgebra::first_row(mo),KzgAlgebra::next_row(mo),KzgAlgebra::first_row(fo),KzgAlgebra::next_row(fo),
          current,next,[beta,gamma,accumulator,next_accumulator],first,last,transition);
        let folded=fold_roots(roots,base,context,alpha,0);
        let injection=last*(next_accumulator-accumulator)/(KzgShape::power2(log)*g);
        let folded=fold_lookups(lookups,shape[6],0,base,context,beta,gamma,alpha,current,next,injection,folded);
        let quotient=KzgAlgebra::polynomial(KzgAlgebra::first_row(qo),z_n);
        assert_eq!(folded,vanishing*quotient,"packed quotient relation");
        verify_frames(rest,beta,gamma,alpha,zeta,next_accumulator)
      },
    }
  }

  -- `KzgPackedVerifier::verify` with the tabled `verify_frames`.
  fn verify_key(key:KzgPackedDeserialize::Key,proof:KzgPackedDeserialize::Proof,claims:Lists::List<Lists::List<Field>>)
      ->(KzgTranscript::Transcript,BN254G1::Point,BN254G1::Point) {
    let frames=KzgPackedShape::frames(key,proof);
    let KzgPackedDeserialize::Key::Mk(seed,max_log,_budget,generator,_anchors,circuits,fixed)=key;
    let KzgPackedDeserialize::Proof::Mk(active,logs,main,stage2,quotient,accumulators,_mo,_so,_qo,_fo,extras,w1,w2)=proof;
    let transcript=KzgPackedVerifier::observe_key(seed,circuits,active,fixed);
    let transcript=KzgTranscript::observe_input(transcript,KzgPcsPacked::commitment_bytes(main));
    let transcript=KzgTranscript::observe_fields(transcript,logs);
    let transcript=KzgTranscript::observe_claims(transcript,claims);
    let (beta,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_field(transcript,beta);
    let (gamma,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_field(transcript,gamma);
    let initial=KzgAlgebra::claims_accumulator(claims,beta,gamma);
    let transcript=KzgTranscript::observe_input(transcript,KzgPcsPacked::commitment_bytes(stage2));
    let transcript=KzgTranscript::observe_fields(transcript,accumulators);
    let (alpha,transcript)=KzgTranscript::sample(transcript);
    let transcript=KzgTranscript::observe_input(transcript,KzgPcsPacked::commitment_bytes(quotient));
    let (zeta,transcript)=KzgTranscript::sample(transcript);
    assert_eq!(Fields::is_zero(zeta),0,"zero packed evaluation challenge");
    verify_frames(frames,beta,gamma,alpha,zeta,initial);
    let rounds=KzgPcsPacked::rounds(frames,main,stage2,quotient,fixed);
    KzgPcsPacked::reduce(transcript,rounds,extras,w1,w2,zeta,generator,max_log)
  }

  fn verify(expected_claims: KzgIO::Digest) -> [Field; 4] {
    KzgIO::digest_bytes(expected_claims);
    let (claims_bytes, claims_length) = KzgIO::sized_channel(2);
    let proof_bytes = KzgIO::channel(3);
    assert_eq!(Blake3::pack_digest(KzgBlake3::hash_input(claims_bytes, claims_length)), expected_claims,
      "packed claims digest mismatch");
    let (_transcript, a, b) = verify_key(key(), KzgPackedDeserialize::proof(proof_bytes), KzgDeserialize::claims(claims_bytes));
    KzgAccumulator::pack(a, b)
  }
}
⟧

end MultiStark.Source

namespace MultiStark.BN.PackedTerminal
open Aiur

def entry := "KzgPackedTerminal::verify"

#aiur_check MultiStark.BN.libraries.append MultiStark.BN.source |>.append MultiStark.BN.Packed.source
  |>.append MultiStark.Source.kzgPackedTerminal

/-! Export-side parser of a packed key (`KzgPackedDeserialize::key`'s grammar). -/

inductive Node where
  | const (value : Nat)
  | var (source offset column : Nat)
  | publicInput (index : Nat)
  | first | last | transition
  | add (a b : Nat) | sub (a b : Nat) | mul (a b : Nat)
  | neg (a : Nat)

structure Circuit where
  shape : Array Nat
  nodes : Array Node
  roots : Array Nat
  lookups : Array (Nat × Array Nat)
  mainNext : Nat
  fixedNext : Nat
  copies : Nat

structure ParsedKey where
  /-- The key bytes without the circuit count and circuits. -/
  rest : ByteArray
  circuits : Array Circuit

abbrev Parse := StateT Nat (Except String)

def byte (key : ByteArray) : Parse Nat := do
  let p ← get
  unless p < key.size do throw "packed key truncated"
  set (p + 1)
  pure (key.get! p).toNat

def u32 (key : ByteArray) : Parse Nat := do
  let a ← byte key; let b ← byte key; let c ← byte key; let d ← byte key
  pure (a + 256 * b + 65536 * c + 16777216 * d)

def skip (key : ByteArray) (count : Nat) : Parse Unit := do
  let p ← get
  unless p + count ≤ key.size do throw "packed key truncated"
  set (p + count)

def scalar (key : ByteArray) : Parse Nat := do
  let mut value := 0
  for i in [0:32] do
    value := value + (← byte key) * 256 ^ i
  unless value < MultiStark.BN.modulus do throw "noncanonical KZG Fr encoding"
  pure value

def node (key : ByteArray) (index : Nat) (widths : Array Nat) : Parse (Node × Bool × Bool) := do
  let child (key : ByteArray) : Parse Nat := do
    let c ← u32 key
    unless c < index do throw "KZG graph child does not precede parent"
    pure c
  match ← byte key with
  | 0 => pure (.const (← scalar key), false, false)
  | 1 =>
    let source ← byte key
    let offset ← byte key
    let column ← u32 key
    unless offset ≤ 1 do throw "KZG graph row offset"
    let bound ← match source with
      | 0 => pure widths[3]! | 1 => pure widths[4]! | 2 => pure widths[5]!
      | _ => throw "KZG graph source"
    unless column < bound do throw "KZG graph column"
    pure (.var source offset column, source == 1 && offset == 1, source == 0 && offset == 1)
  | 2 =>
    let i ← u32 key
    unless i < 4 do throw "KZG public column"
    pure (.publicInput i, false, false)
  | 3 => pure (.first, false, false)
  | 4 => pure (.last, false, false)
  | 5 => pure (.transition, false, false)
  | 9 => pure (.neg (← child key), false, false)
  | 6 => do let a ← child key; let b ← child key; pure (.add a b, false, false)
  | 7 => do let a ← child key; let b ← child key; pure (.sub a b, false, false)
  | 8 => do let a ← child key; let b ← child key; pure (.mul a b, false, false)
  | _ => throw "unknown KZG graph node"

partial def quotientDegree (degree candidate : Nat) : Nat :=
  if degree < candidate + 2 then candidate else quotientDegree degree (candidate * 2)

def ids (key : ByteArray) (count bound : Nat) : Parse (Array Nat) := do
  let mut out := #[]
  for _ in [0:count] do
    let id ← u32 key
    unless id < bound do throw "KZG graph child does not precede parent"
    out := out.push id
  pure out

def circuit (key : ByteArray) (budget copies : Nat) : Parse Circuit := do
  let mut shape := #[]
  for _ in [0:8] do shape := shape.push (← u32 key)
  unless 0 < shape[6]! do throw "zero KZG lookup group size"
  unless shape[6]! < 9 do throw "KZG lookup group too large"
  unless shape[1]! < budget + 2 do throw "KZG quotient budget exceeded"
  unless shape[7]! == quotientDegree shape[1]! 1 do throw "KZG quotient degree metadata"
  unless (shape[2]! == 0) == (shape[3]! == 0) do throw "KZG fixed shape metadata"
  let nodeCount ← u32 key
  let mut nodes := #[]
  let mut mainNext := false
  let mut fixedNext := false
  for index in [0:nodeCount] do
    let (n, m, f) ← node key index shape
    nodes := nodes.push n
    mainNext := mainNext || m
    fixedNext := fixedNext || f
  let rootCount ← u32 key
  let roots ← ids key rootCount nodeCount
  let lookupCount ← u32 key
  let mut lookups := #[]
  for _ in [0:lookupCount] do
    let multiplicity ← u32 key
    unless multiplicity < nodeCount do throw "KZG graph child does not precede parent"
    let width ← u32 key
    lookups := lookups.push (multiplicity, ← ids key width nodeCount)
  let groups := max 1 ((lookupCount + shape[6]! - 1) / shape[6]!)
  unless shape[5]! == groups do throw "KZG stage-two width metadata"
  unless shape[0]! == rootCount + groups do throw "KZG constraint count metadata"
  pure { shape, nodes, roots, lookups, copies,
         mainNext := if mainNext then 1 else 0, fixedNext := if fixedNext then 1 else 0 }

def parseKey (key : ByteArray) : Except String ParsedKey := do
  let parse : Parse (Nat × Nat × Array Circuit) := do
    unless (key.extract 0 8).data.toList.map (·.toNat) == [73,88,65,85,83,75,48,50] do
      throw "KZG wire version mismatch"
    skip key 8
    let seed ← u32 key; skip key seed
    let _maxLog ← u32 key
    let budget ← u32 key
    skip key 32
    skip key 128
    let start ← get
    let count ← u32 key
    unless count != 0 do throw "empty packed system"
    let mut circuits := #[]
    for _ in [0:count] do
      let copies ← u32 key
      unless copies != 0 do throw "packed circuit without copies"
      circuits := circuits.push (← circuit key budget copies)
    pure (start, ← get, circuits)
  let ((start, stop, circuits), _) ← parse.run 0
  pure { rest := (key.extract 0 start).append (key.extract stop key.size), circuits }

/-- The terminal module with `key`'s tables and constants. -/
def withKey (key : ByteArray) : Except String (Modules.Program Nat) := do
  let parsed ← parseKey key
  -- Leading zero bytes, skipped by the input offset, make whole words.
  let pad := (4 - parsed.rest.size % 4) % 4
  let rest := (ByteArray.mk (Array.replicate pad 0)).append parsed.rest
  let words := rest.size / 4
  let literal (n : Nat) : Generic.Expr Nat := .literal n
  let index (count : Nat) : List (Generic.Expr Nat) := (List.range count).map fun i => .tuple [literal i]
  let row (values : List Nat) : Generic.Expr Nat := .array (values.map literal)
  let source := MultiStark.Source.kzgPackedTerminal
  let templates ← match source.modules.findSome? fun m => match m.body with
      | .definitions d => d.program.tables.find? (·.name == "node_templates")
      | _ => none with
    | some t => pure t.rows.toArray
    | none => throw "missing node templates"
  let instantiate (tag : Nat) (values : List Nat) : Except String (Generic.Expr Nat) :=
    match templates[tag]? with
    | some (.construct name types ctor args) =>
      if args.length == values.length then pure (.construct name types ctor (values.map literal))
      else throw "node template arity"
    | _ => throw "node template is not a constructor"
  let mut nodeRows := #[]
  let mut idRows := #[]
  let mut lookupRows := #[]
  let mut circuitRows := #[]
  for c in parsed.circuits do
    let nodeBase := nodeRows.size
    for n in c.nodes do
      let r ← match n with
        | .const v => instantiate 0 [v]
        | .var s o col => instantiate 1 [s, o, col]
        | .publicInput i => instantiate 2 [i]
        | .first => instantiate 3 []
        | .last => instantiate 4 []
        | .transition => instantiate 5 []
        | .add a b => instantiate 6 [a, b]
        | .sub a b => instantiate 7 [a, b]
        | .mul a b => instantiate 8 [a, b]
        | .neg a => instantiate 9 [a]
      nodeRows := nodeRows.push r
    let rootBase := idRows.size
    idRows := idRows ++ c.roots.map fun i => row [i]
    let lookupBase := lookupRows.size
    for (multiplicity, args) in c.lookups do
      lookupRows := lookupRows.push (row [multiplicity, idRows.size, args.size])
      idRows := idRows ++ args.map fun i => row [i]
    circuitRows := circuitRows.push (row (c.shape.toList ++
      [nodeBase, c.nodes.size, rootBase, c.roots.size, lookupBase, c.lookups.size, c.mainNext, c.fixedNext, c.copies]))
  let tables : List (Generic.Table Nat) := [
    ⟨"key_inputs", .tuple [.field], index words⟩,
    ⟨"key_values", .array .field 4, (List.range words).map fun i =>
      row ((List.range 4).map fun j => (rest.get! (4 * i + j)).toNat)⟩,
    ⟨"node_inputs", .tuple [.field], index nodeRows.size⟩,
    ⟨"node_values", .named "KzgDeserialize::Node" [], nodeRows.toList⟩,
    ⟨"id_inputs", .tuple [.field], index idRows.size⟩,
    ⟨"id_values", .array .field 1, idRows.toList⟩,
    ⟨"lookup_inputs", .tuple [.field], index lookupRows.size⟩,
    ⟨"lookup_values", .array .field 3, lookupRows.toList⟩,
    ⟨"circuit_inputs", .tuple [.field], index circuitRows.size⟩,
    ⟨"circuit_values", .array .field 17, circuitRows.toList⟩]
  let consts := [("KEY_WORDS", words), ("KEY_OFFSET", pad), ("CIRCUITS", parsed.circuits.size)]
  pure { source with modules := source.modules.map fun m =>
    { m with body := match m.body with
      | .definitions d => .definitions { d with program := { d.program with
          tables := d.program.tables.filterMap fun t =>
            if t.name == "node_templates" then none
            else some { t with rows := (tables.find? (·.name == t.name)).elim t.rows (·.rows) }
          consts := d.program.consts.map fun c =>
            match consts.find? (·.1 == c.name) with
            | some (_, v) => ⟨c.name, .literal v⟩
            | none => c } }
      | body => body } }

def program (key : ByteArray) : Except String (Modules.Program MultiStark.BN.F) := do
  pure (MultiStark.BN.Packed.program.append ((← withKey key).toField MultiStark.BN.F))

def compilePackage (key : ByteArray) (entries : List String := [entry]) : IO ByteArray := do
  let program ← IO.ofExcept (program key)
  let prepared ← IO.ofExcept (Modules.prepare program entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, circuits) ← Trace.exportPlanParallelWide MultiStark.BN.modulus ZMod.val
    prepared.environment.source prepared.entries exported
  IO.ofExcept (Artifact.packageWide exported MultiStark.BN.modulus ZMod.val (some circuits))

/-- Little-endian u32 words of a 32-byte digest, as `Blake3::pack_digest`. -/
def digestWords (digest : ByteArray) : List Nat :=
  (List.range 8).map fun i =>
    (List.range 4).foldl (fun acc j => acc + (digest.get! (4 * i + j)).toNat * 256 ^ j) 0

end MultiStark.BN.PackedTerminal
