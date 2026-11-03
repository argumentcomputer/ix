import Aiur.Trace.FFI
import AiurTests.Execution

namespace AiurTraceTests
open Aiur Lean
abbrev F := AiurExecutionTests.F

def extras : Modules.Program Nat := aiur_modules% "
module Extra {
  enum Stored { Empty, Value(Field) }
  enum Wrapper { Wrap(Field) }
  fn width_capacity(x: Field) -> Field {
    let a = &x;
    let b = &(x, 0);
    let c = &();
    let p = &a;
    *(*p)
  }
  fn typed_sharing(x: Field) -> (Field, Field) {
    let a = &x;
    let b = &Wrapper::Wrap(x);
    let aa = &a;
    let bb = &b;
    (*(*aa), match *(*bb) { Wrapper::Wrap(y) => y })
  }
  fn local_widths(x: Field) -> (Field, Field) {
    let a = &x;
    let b = &(x, 0);
    let c = &Stored::Value(x);
    (*a, match *c { Stored::Value(y) => y, _ => 0 })
  }
  fn store_input(x: Stored) -> Stored { let p = &x; *p }
  fn store_hint() -> Stored { let p = &hint::<Stored>(\"stored\", ()); *p }
  fn keep(x: Stored) -> Stored { x }
  fn make(x: Field) -> Stored { Stored::Value(x) }
  fn advice_enum() -> Stored { hint::<Stored>(\"stored\", ()) }
  fn forwarded(x: Stored) -> Stored { keep(x) }
  fn returned(x: Field) -> Stored { keep(make(x)) }
  fn hinted() -> Stored { keep(advice_enum()) }
  fn recurse(n: Field, x: Stored) -> Stored { match n { 0 => x, _ => recurse(n - 1, x) } }
  fn recursive(x: Stored) -> Stored { recurse(3, x) }
  fn high(a: Field, b: Field) -> Field { let x = (a + b) * (a - b); (x * x * x + x) / b }
  fn branches(x: Field, y: Field) -> Field {
    match x { 0 => match y { 0 => 7, _ => y / y }, _ => match y { 0 => x / x, _ => x * y } }
  }
  fn disjoint(x: Field, y: Field) -> Field {
    match (x, y) { (0, 0) => 7, (1, 1) => 8, _ => 9 }
  }
  fn partial_overlap(x: Field, y: Field) -> Field {
    match (x, y) { (0, 0) => 7, (0, _) => 8, _ => 9 }
  }
  fn overlap(x: Field, y: Field) -> Field {
    match (x, y) { (0, _) => 7, (_, 1) => 8, _ => 9 }
  }
  fn conflicting_component(x: Field, y: Field) -> Field {
    match (x, y) { (0, 0) => 7, (1, _) => 8, _ => 9 }
  }
  fn repeated(x: Field, y: Field) -> Field {
    match (x, y) { (0, _) => 7, (0, 1) => 9, (_, 1) => 8, _ => 9 }
  }
  fn advice1(x: Field) -> Field { hint::<Field>(1) }
  fn advice2(x: Field) -> Field { hint::<Field>(2) }
  fn different() -> Field { advice1(3) + advice2(3) }
  fn sites(x: Field) -> (Field, Field) {
    let first = match x { 0 => hint::<Field>(1), _ => hint::<Field>(2), 9 => hint::<Field>(9) };
    (first, hint::<Field>(49))
  }
}
"

def mergeCases : Modules.Program Nat := aiur_modules% "
module Merge {
  enum Binary { Off, On }
  enum Ternary { A, B, C }
  enum Wrapper { Wrap(Field) }
  enum ListA { Nil, Cons(Field, &ListA) }
  enum ListB { Nil, Cons(Field, &ListB) }
  fn field_id(x: Field) -> Field { x }
  fn binary_id(x: Binary) -> Binary { x }
  fn ternary_id(x: Ternary) -> Ternary { x }
  fn wrapper_id(x: Wrapper) -> Wrapper { x }
  fn pair_sum(x: (Field, Field)) -> Field { let (a, b) = x; a + b }
  fn two_sum(a: Field, b: Field) -> Field { a + b }
  fn len_a(p: &ListA) -> Field {
    match *p { ListA::Nil => 0, ListA::Cons(_, tail) => 1 + len_a(tail) }
  }
  fn len_b(p: &ListB) -> Field {
    match *p { ListB::Nil => 0, ListB::Cons(_, tail) => 1 + len_b(tail) }
  }
  fn binary_hint() -> Binary { hint::<Binary>(\"binary\", ()) }
  fn ternary_hint() -> Ternary { hint::<Ternary>(\"ternary\", ()) }
  fn identities(x: Field) -> (Field, Binary, Ternary, Wrapper) {
    (field_id(x), binary_id(Binary::On), ternary_id(Ternary::C), wrapper_id(Wrapper::Wrap(x)))
  }
  fn grouping(x: Field, y: Field) -> (Field, Field) { (pair_sum((x,y)), two_sum(x,y)) }
  fn lists(x: Field) -> (Field, Field) {
    let a = &ListA::Cons(x, &ListA::Cons(2, &ListA::Nil));
    let b = &ListB::Cons(x, &ListB::Cons(2, &ListB::Nil));
    (len_a(a), len_b(b))
  }
  fn hints() -> (Binary, Ternary) { (binary_hint(), ternary_hint()) }
  fn public_binary(x: Binary) -> Binary { x }
  fn public_ternary(x: Ternary) -> Ternary { x }
}
"

def run : IO Unit := do
  let source := { AiurExecutionTests.source with modules :=
    AiurExecutionTests.source.modules ++ AiurExecutionHintTests.source.modules ++ extras.modules ++ mergeCases.modules }
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F)
    (AiurExecutionTests.entries ++ AiurExecutionHintTests.entries ++
      ["Extra::high", "Extra::branches", "Extra::different", "Extra::sites",
        "Extra::typed_sharing", "Extra::local_widths",
        "Extra::store_input", "Extra::store_hint", "Extra::forwarded", "Extra::returned",
        "Extra::hinted", "Extra::recursive", "Extra::disjoint", "Extra::partial_overlap",
        "Extra::overlap", "Extra::conflicting_component", "Extra::repeated",
        "Merge::identities", "Merge::grouping", "Merge::lists", "Merge::hints",
        "Merge::public_binary", "Merge::public_ternary"]))
  let exported ← IO.ofExcept prepared.exportExecution
  let named := fun name => Generic.Ty.named ("Witness::" ++ name) []
  let unit := fun name => Execution.DataValue.construct (F := F) (named name) "Unit" []
  let hints : Array (Execution.HintEntry F) := #[
    ⟨.named "Merge::Binary" [], .tuple [], .construct (.named "Merge::Binary" []) "On" [], "binary"⟩,
    ⟨.named "Merge::Ternary" [], .tuple [], .construct (.named "Merge::Ternary" []) "C" [], "ternary"⟩,
    ⟨.named "Extra::Stored" [], .tuple [],
      .construct (.named "Extra::Stored" []) "Value" [7], "stored"⟩,
    ⟨.field, 49, 7, ""⟩, ⟨.field, 9, 17, ""⟩, ⟨.field, 7, 1, ""⟩, ⟨.field, .tuple [7], 2, ""⟩,
    ⟨.field, 1, 7, ""⟩, ⟨.field, 2, 8, ""⟩,
    ⟨.field, unit "Unit", 3, ""⟩, ⟨.field, unit "Other", 4, ""⟩, ⟨.field, .tuple [], 5, ""⟩,
    ⟨.tuple [.field], 7, .tuple [2], "singleton"⟩,
    ⟨named "Outer", .record (named "Pair") [("right", 4), ("left", 3)],
      .construct (named "Outer") "Wrap" [.construct (named "Choice") "Some" [.array .field [5,6]]], ""⟩,
    ⟨.named "Witness::Box" [named "Numbers"], 7,
      .record (.named "Witness::Box" [named "Numbers"]) [("value", .array .field [8,9])], "boxed"⟩,
    ⟨.tuple [named "Unit", .array (named "Unit") 2, .array .field 0], .tuple [],
      .tuple [unit "Unit", .array (named "Unit") [unit "Unit", unit "Unit"], .array .field []], "zero"⟩, ⟨.field, 49, 7, "sample"⟩]
  let cases : List (String × Array Nat) := [
    ("Merge::identities", #[7]), ("Merge::grouping", #[3,4]), ("Merge::lists", #[9]),
    ("Merge::hints", #[]), ("Merge::public_binary", #[1]), ("Merge::public_ternary", #[2]),
    ("Extra::typed_sharing", #[0]), ("Extra::typed_sharing", #[7]),
    ("Extra::local_widths", #[0]), ("Extra::local_widths", #[7]),
    ("Extra::store_input", #[0,0]), ("Extra::store_input", #[1,7]), ("Extra::store_hint", #[]),
    ("Extra::forwarded", #[0,0]), ("Extra::forwarded", #[1,7]), ("Extra::returned", #[9]),
    ("Extra::hinted", #[]), ("Extra::recursive", #[0,0]), ("Extra::recursive", #[1,7]),
    ("Test::sharing", #[4]), ("Test::fib", #[8]), ("Test::memory", #[3]),
    ("Test::table", #[1, 1]), ("Test::arithmetic", #[7, 3]),
    ("Test::choose", #[0]), ("Test::choose", #[1]), ("Test::choose", #[2]),
    ("Test::choice", #[0, 0, 0, 0]), ("Test::choice", #[1, 0, 9, 0]),
    ("Test::choice", #[1, 3, 9, 0]), ("Test::choice", #[2, 2, 3, 4]),
    ("Test::nested", #[1, 1, 0, 9, 0, 0, 0, 0, 0]),
    ("Test::unit", #[]), ("Test::empty_secret", #[]), ("Test::pointer", #[]),
    ("Test::lazy", #[0]), ("Test::refutable", #[3]), ("Test::asserted", #[4]),
    ("Witness::repeated", #[49]), ("Witness::typed_keys", #[]), ("Witness::typed_results", #[]),
    ("Witness::nested", #[3,4]), ("Witness::boxed", #[7]), ("Witness::zero", #[]),
    ("Witness::inlined", #[49]), ("Witness::key_effects", #[4]),
    ("Witness::lazy", #[0]), ("Witness::lazy", #[49]),
    ("Extra::high", #[7,3]), ("Extra::branches", #[0,0]), ("Extra::branches", #[0,3]),
    ("Extra::branches", #[3,0]), ("Extra::branches", #[3,3]),
    ("Extra::different", #[]), ("Extra::sites", #[0]), ("Extra::sites", #[1])] ++
    ["Extra::disjoint", "Extra::partial_overlap", "Extra::overlap", "Extra::conflicting_component",
      "Extra::repeated"].flatMap
      (fun name => [0, 1, 2].flatMap fun x => [0, 1, 2].map fun y => (name, #[x, y]))
  for config in ([{}, {propagateValues := false},
      {shareAuxiliaries := false, eliminateSelectors := false, propagateScopes := false,
       simplifyConstraints := false, propagateValues := false, mergeLookups := false,
       deduplicate := false}] : List Optimized.Config) do
    let compiled ← IO.ofExcept (prepared.compileOptimized config)
    let artifact := compiled.circuit.artifact
    let physical ← IO.ofExcept (Optimized.Physical.prepare artifact)
    if config.deduplicate then
      for (left, right) in [("field_id", "binary_id"), ("field_id", "ternary_id"),
          ("field_id", "wrapper_id"), ("pair_sum", "two_sum"), ("len_a", "len_b")] do
        unless physical.representative ("Merge::" ++ left) == physical.representative ("Merge::" ++ right) do
          throw (IO.userError s!"representation-identical functions did not merge: {left}, {right}")
    if physical.representative "Merge::binary_hint" == physical.representative "Merge::ternary_hint" then
      throw (IO.userError "different hint canonicality checks were merged")
    for entry in ["Merge::public_binary", "Merge::public_ternary"] do
      unless physical.representative entry == entry do throw (IO.userError "public entrypoint was merged")
    -- Same layout, different canonical tags: test the constraints directly,
    -- bypassing the interpreter's own input validation.
    let some binary := physical.system.findChip? "Merge::public_binary" | throw (IO.userError "missing binary entry")
    let some ternary := physical.system.findChip? "Merge::public_ternary" | throw (IO.userError "missing ternary entry")
    unless binary.constraints != ternary.constraints do throw (IO.userError "public canonicality checks disappeared")
    let plan ← IO.ofExcept (Trace.exportPreparedJson 97 ZMod.val compiled.circuit.inlined.program artifact physical exported.bytecode)
    for (name, args) in cases do
      for pad in [false, true] do
        let result ← IO.ofExcept (← Trace.run exported plan name args hints pad)
        let rows ← IO.ofExcept (result.rows 97)
        let rom ← IO.ofExcept (result.widthROM 97)
        for weighted in ← IO.ofExcept (result.paddedRows 97) do
          let some source := physical.system.findChip? weighted.row.chip
            | throw (IO.userError "unknown padded chip")
          let padded := Optimized.Activation.compile source
          let _ ← IO.ofExcept ((padded.checkRow (Circuit.Erasure.rawROM rom) weighted.row).mapError reprStr)
        let some selection := prepared.find? name | throw (IO.userError "missing test entry")
        let some chip := artifact.system.findChip? selection.resolved.name | throw (IO.userError "missing test chip")
        let mut offset := 0
        let mut inputs := []
        for wire in chip.inputs do
          let count := wire.words.length
          let value := (args.toList.drop offset |>.take count).map (fun n => (n : F))
          offset := offset + count
          inputs := inputs ++ [WireValue.mk wire.type value]
        let root := Circuit.Message.mk selection.resolved.name inputs
          ⟨chip.output.type, result.execution.output.toList.map Nat.cast⟩
        match physical.checkMemo rom root rows with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"Lean trace check failed for {name}, pad={pad}: {e}")
        if name == "Merge::public_binary" then
          let some row := rows.find? (·.row.chip == name) | throw (IO.userError "missing binary row")
          let some column := (binary.inputs.flatMap WireValue.words).head? | throw (IO.userError "missing binary input")
          let forged := { row.row with values := row.row.values.set column 2 }
          if (binary.checkRow (Circuit.Erasure.rawROM rom) forged).isOk then
            throw (IO.userError "physical entry accepted a tag canonical only for the other enum")
        if name == "Merge::hints" then
          let hintName := physical.representative "Merge::binary_hint"
          let some hintChip := physical.system.findChip? hintName | throw (IO.userError "missing hint circuit")
          let some row := rows.find? (·.row.chip == hintName) | throw (IO.userError "missing hint row")
          let some (.var column) := hintChip.output.words.head? | throw (IO.userError "missing hint output")
          let forged := { row.row with values := row.row.values.set column 2 }
          if (hintChip.checkRow (Circuit.Erasure.rawROM rom) forged).isOk then
            throw (IO.userError "physical hint accepted a tag canonical only for the other enum")
        -- Independently exercise rejection in the certified physical checker.
        if let some first := rows.head? then
          if (physical.checkMemo rom root ({ first with multiplicity := first.multiplicity + 1 } :: rows.tail!)).isOk then
            throw (IO.userError "Lean checker accepted a mutated provide count")
    IO.println s!"Trace: {cases.length * 2} executions accepted by Lean checkMemo ({reprStr config})"

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def runSmallField : IO Unit := do
  let prepared ← IO.ofExcept (Modules.prepare (extras.toField (ZMod 2))
    ["Extra::high", "Extra::branches", "Extra::disjoint", "Extra::partial_overlap", "Extra::overlap",
      "Extra::conflicting_component", "Extra::repeated", "Extra::width_capacity"])
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept (prepared.compileOptimized {})
  let artifact := compiled.circuit.artifact
  let physical ← IO.ofExcept (Optimized.Physical.prepare artifact)
  let plan ← IO.ofExcept (Trace.exportPreparedJson 2 ZMod.val compiled.circuit.inlined.program artifact physical exported.bytecode)
  let cases : List (String × Array Nat) := [
    ("Extra::width_capacity", #[0]), ("Extra::width_capacity", #[1]),
    ("Extra::high", #[1,1]), ("Extra::branches", #[0,0]),
      ("Extra::branches", #[0,1]), ("Extra::branches", #[1,0]), ("Extra::branches", #[1,1])] ++
    ["Extra::disjoint", "Extra::partial_overlap", "Extra::overlap", "Extra::conflicting_component",
      "Extra::repeated"].flatMap
      (fun name => [0, 1].flatMap fun x => [0, 1].map fun y => (name, #[x, y]))
  for (name, args) in cases do
    for pad in [false, true] do
      let result ← IO.ofExcept (← Trace.run exported plan name args #[] pad)
      let rows ← IO.ofExcept (result.rows 2)
      let rom ← IO.ofExcept (result.widthROM 2)
      for weighted in ← IO.ofExcept (result.paddedRows 2) do
        let some source := physical.system.findChip? weighted.row.chip
          | throw (IO.userError "unknown padded chip")
        let padded := Optimized.Activation.compile source
        let _ ← IO.ofExcept ((padded.checkRow (Circuit.Erasure.rawROM rom) weighted.row).mapError reprStr)
      let root := Circuit.Message.mk name (args.toList.map fun n => WireValue.field (n : ZMod 2))
        (WireValue.field ((result.execution.output[0]?.getD 0 : Nat) : ZMod 2))
      IO.ofExcept (physical.checkMemo rom root rows)
  IO.println s!"Trace: {cases.length * 2} executions accepted by Lean checkMemo over F₂"

end AiurTraceTests
