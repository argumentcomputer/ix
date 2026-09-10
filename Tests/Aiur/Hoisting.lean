module

public import Tests.Aiur.Common
public import Ix.Aiur.Meta
public import Ix.Aiur.Semantics.SourceEval
public import Ix.Aiur.Semantics.BytecodeEval

/-! Regression tests for source normalization: check explicit expectations
against the original source, normalized source, bytecode evaluator, and native
execution. Proving is opt-in so the ordinary suite stays inexpensive. -/

public section

open LSpec Aiur

namespace AiurTests.Hoisting

def toplevel : Source.Toplevel := ⟦
  enum Choice { Left(G), Right(G) }
  fn pair(a: G, b: G) -> (G, G) { (a, b) }
  fn emit(x: G) -> G { io_write(0, [x]); x }
  fn twice(x: G) -> G { let tmp = x + x; tmp }
  fn zero(x: G) -> G { assert_eq!(x, 0, "left operand"); x }
  fn choose(c: Choice) -> G {
    match c { Choice.Left(x) | Choice.Right(x) => x, }
  }
  fn guarded_match(x: G) -> G {
    assert_eq!(x, 0, "guarded match");
    let y = @choose(Choice.Left(7));
    y
  }

  pub fn assert_shadow(x: G) -> G {
    assert_eq!(x, 0, "original x");
    let x = 0;
    x
  }
  pub fn assert_order(x: G) -> G {
    assert_eq!(x, 0, "before read");
    let ys = io_read(0, 0, 1);
    ys[0]
  }
  pub fn write_read(x: G) -> G {
    io_write(0, [x]);
    let ys = io_read(0, 0, 1);
    ys[0]
  }
  pub fn set_get(x: G) -> (G, G) {
    io_set_info(0, [x], 3, 4);
    let (i, n) = io_get_info(0, [x]);
    (i, n)
  }
  pub fn write_shadow(x: G) -> G {
    let channel = 0;
    io_write(channel, [x]);
    let channel = 1;
    io_write(channel, [x + 1]);
    x
  }
  pub fn rhs_shadow(x: G) -> (G, G) {
    let y = (let x = 2; x);
    (x, y)
  }
  pub fn operand_shadow(x: G) -> G { x + (let x = 2; x) }
  pub fn array_shadow(x: G) -> [G; 2] { [(let x = 2; x), x] }
  pub fn call_shadow(x: G) -> (G, G) { pair((let x = 2; x), x) }
  pub fn match_shadow(x: G) -> G {
    match (let x = 0; x) { 0 => x, _ => 99, }
  }
  pub fn argument_order() -> G { emit(1) + (let x = emit(2); x) }
  pub fn argument_cores() -> (G, G) {
    pair((let x = 1; emit(x)), (let x = emit(2); x))
  }
  pub fn array_order() -> [G; 2] { [emit(1), (let x = emit(2); x)] }
  pub fn inline_shadow(x: G) -> G { x + @twice((let x = 2; x)) }
  pub fn inline_order() -> G { emit(1) + @twice(emit(2)) }
  pub fn guarded_operand(x: G) -> G { @guarded_match(x) + 1 }
  pub fn guarded_rhs(x: G) -> G { let y = @guarded_match(x); y + 1 }
  pub fn return_guarded(x: G) -> G { return @guarded_match(x) }
  pub fn write_then_branch(x: G) -> G {
    let y = (io_write(0, [x]); let z = @choose(Choice.Right(x)); z);
    y + 1
  }
  pub fn metadata_then_branch(x: G) -> G {
    let y = (io_set_info(0, [x], 3, 4); let z = @choose(Choice.Right(x)); z);
    y + 1
  }
  pub fn debug_then_branch(x: G) -> G {
    let y = (dbg!("hoisting branch", x); let z = @choose(Choice.Right(x)); z);
    y + 1
  }
  pub fn assert_argument_order() -> G {
    assert_eq!(emit(1), (let ignored = emit(2); 1));
    7
  }
  pub fn io_argument_order() -> G {
    io_write(emit(0), [(let ignored = emit(1); 2)]);
    7
  }
  pub fn info_argument_order() -> (G, G) {
    io_set_info(emit(0), [(let ignored = emit(1); 7)],
      (let ignored = emit(2); 3), (let ignored = emit(3); 4));
    let info = io_get_info(0, [7]);
    info
  }
  pub fn left_failure(x: G) -> G { zero(x) + (let ys = io_read(0, 0, 1); ys[0]) }
  pub fn allocation_order() -> (G, G) {
    (ptr_val(store(1)), (let p = store(2); ptr_val(p)))
  }
  pub fn or_inline() -> (G, G) { (@choose(Choice.Left(4)), @choose(Choice.Right(6))) }
  pub fn or_shadow(x: G) -> G {
    match (2, x) { (0, y) | (2, y) => y, _ => 99, }
  }
  pub fn return_continuation(x: G) -> G {
    assert_eq!(x, 0, "return assertion");
    let x = 7;
    return x
  }
  pub fn lazy_arm(x: G) -> G {
    match x {
      0 => 7,
      _ => assert_eq!(0, 1, "inactive arm"); let x = emit(9); x,
    }
  }
⟧

-- The source language supports local function values, but native lowering
-- currently has no indirect-call operation. Test normalization/typechecking
-- at that boundary, without claiming new native higher-order support.
def localFunctionSource : Source.Toplevel := ⟦
  fn twice(x: G) -> G { x * 2 }
  fn apply(f: fn(G) -> G, x: G) -> G { f(x) }
  pub fn local_function(x: G) -> G {
    let f = .twice;
    f(x) + @apply(f, x)
  }
⟧

private def dataIO (xs : Array Aiur.G) : IOBuffer :=
  { data := ({} : Std.HashMap Aiur.G (Array Aiur.G)).insert 0 xs, map := {} }

def cases : List AiurTestCase := [
  .interp `assert_shadow #[0] #[0],
  { AiurTestCase.interp `assert_order #[0] #[5] with
    inputIOBuffer := dataIO #[5], expectedIOBuffer := dataIO #[5] },
  { AiurTestCase.interp `write_read #[7] #[7] with expectedIOBuffer := dataIO #[7] },
  { AiurTestCase.interp `set_get #[7] #[3, 4] with
    expectedIOBuffer := { data := {}, map :=
      ({} : Std.HashMap (Aiur.G × Array Aiur.G) IOKeyInfo).insert (0, #[7]) ⟨3, 4⟩ } },
  { AiurTestCase.interp `write_shadow #[7] #[7] with
    expectedIOBuffer := { data := (dataIO #[7]).data.insert 1 #[8], map := {} } },
  .interp `rhs_shadow #[9] #[9, 2],
  .interp `operand_shadow #[9] #[11],
  .interp `array_shadow #[9] #[2, 9],
  .interp `call_shadow #[9] #[2, 9],
  .interp `match_shadow #[9] #[9],
  { AiurTestCase.interp `argument_order #[] #[3] with expectedIOBuffer := dataIO #[1, 2] },
  { AiurTestCase.interp `argument_cores #[] #[1, 2] with expectedIOBuffer := dataIO #[1, 2] },
  { AiurTestCase.interp `array_order #[] #[1, 2] with expectedIOBuffer := dataIO #[1, 2] },
  .interp `inline_shadow #[9] #[13],
  { AiurTestCase.interp `inline_order #[] #[5] with expectedIOBuffer := dataIO #[1, 2] },
  .interp `guarded_operand #[0] #[8],
  .interp `guarded_rhs #[0] #[8],
  .interp `return_guarded #[0] #[7],
  .interp `debug_then_branch #[7] #[8],
  { AiurTestCase.interp `write_then_branch #[7] #[8] with expectedIOBuffer := dataIO #[7] },
  { AiurTestCase.interp `metadata_then_branch #[7] #[8] with
    expectedIOBuffer := { data := {}, map :=
      ({} : Std.HashMap (Aiur.G × Array Aiur.G) IOKeyInfo).insert (0, #[7]) ⟨3, 4⟩ } },
  { AiurTestCase.interp `assert_argument_order #[] #[7] with expectedIOBuffer := dataIO #[1, 2] },
  { AiurTestCase.interp `io_argument_order #[] #[7] with expectedIOBuffer := dataIO #[0, 1, 2] },
  { AiurTestCase.interp `info_argument_order #[] #[3, 4] with
    expectedIOBuffer := { dataIO #[0, 1, 2, 3] with map :=
      ({} : Std.HashMap (Aiur.G × Array Aiur.G) IOKeyInfo).insert (0, #[7]) ⟨3, 4⟩ } },
  .interp `allocation_order #[] #[0, 1],
  .interp `or_inline #[] #[4, 6],
  .interp `or_shadow #[9] #[9],
  .interp `return_continuation #[0] #[7],
  .interp `lazy_arm #[0] #[7]
]

private def referenceCheck (label : String) (decls : Source.Decls)
    (env : AiurTestEnv) (tc : AiurTestCase) : TestSeq :=
  let name := Global.mk tc.functionName
  let inputs := unflattenInputs decls tc.input <|
    match decls.getByKey name with | some (.function f) => f.inputs.map (·.2) | _ => []
  match Source.Eval.runFunction decls name inputs tc.inputIOBuffer 100 with
  | .error e => test s!"{tc.label}: {label} succeeds ({repr e})" false
  | .ok (v, io) =>
    test s!"{tc.label}: {label} expected value"
      (flattenValue decls (fun g => env.compiled.nameMap[g]?) v == tc.expectedOutput) ++
    test s!"{tc.label}: {label} expected IO" (io == tc.expectedIOBuffer)

private def successChecks (env : AiurTestEnv) (normalized : Source.Decls)
    (withProof : Bool) (tc : AiurTestCase) : TestSeq :=
  let idx := env.compiled.getFuncIdx tc.functionName |>.get!
  let bytecode := match Bytecode.Eval.runFunction env.compiled.bytecode idx
      tc.input tc.inputIOBuffer 100 with
    | .error e => test s!"{tc.label}: bytecode succeeds ({repr e})" false
    | .ok (v, io) =>
      test s!"{tc.label}: bytecode expected value" (v == tc.expectedOutput) ++
      test s!"{tc.label}: bytecode expected IO" (io == tc.expectedIOBuffer)
  referenceCheck "original source" env.decls env tc ++
  referenceCheck "normalized source" normalized env tc ++ bytecode ++
  env.runTestCase { tc with withProof }

private def localFunctionChecks (env : AiurTestEnv) : TestSeq :=
  withExceptOk "local function original declarations" localFunctionSource.mkDecls fun decls =>
  withExceptOk "local function normalization" localFunctionSource.inlineCalls fun normalized =>
  withExceptOk "local function normalized declarations" normalized.mkDecls fun decls' =>
  withExceptOk "local function normalized typechecking" normalized.checkAndSimplify fun _ =>
    let tc := AiurTestCase.interp `local_function #[9] #[36]
    referenceCheck "original local call" decls env tc ++
    referenceCheck "normalized local call" decls' env tc ++
    test "native indirect calls remain unsupported" (!localFunctionSource.compile.isOk)

private def rawEntry (input : Local) (body : Source.Term) : Source.Function :=
  .monoEntry (.init "raw_entry") [(input, .field)] .field body
    (by simp [Source.sigPointerFree, Typ.hasPointer])

private def bodyHoisted (t : Source.Toplevel) : Source.Toplevel :=
  { t with functions := t.functions.map fun f => { f with body := f.body.hoistLets } }

/-- Names that cannot be written as ordinary surface identifiers are still
legal Source IR. No generated-name spelling (or indexed local) is reserved. -/
private def rawNameChecks (withProof : Bool) : TestSeq :=
  [Local.str "x", .str "inl#0", .str "inl#1", .str "inl#42",
    .str "inl#1000000000000000000000000000000000000000", .idx 0, .idx 42].foldl
    (init := .done) fun acc input =>
    let identity := Source.Function.monoNonEntry (.init "raw_identity")
      [(.str "inl#0", .field)] .field (.var (.str "inl#0"))
    let body : Source.Term := .add
      (.app identity.name [.let (.var input) (.field 2) (.var input)] .inlined) (.var input)
    let t : Source.Toplevel := ⟨#[], #[], #[identity, rawEntry input body]⟩
    acc ++ withExceptOk s!"raw name {repr input}: compile" (AiurTestEnv.build (pure t)) fun env =>
    withExceptOk "raw name: normalize" t.inlineCalls fun t' =>
    withExceptOk "raw name: normalized declarations" t'.mkDecls fun decls =>
    withExceptOk "raw name: body-only declarations" (bodyHoisted t).mkDecls fun bodyDecls =>
      let tc := AiurTestCase.interp `raw_entry #[9] #[11] s!"raw name {repr input}"
      referenceCheck "body-only hoisting" bodyDecls env tc ++
      successChecks env decls withProof tc

private def globalNameChecks (withProof : Bool) : TestSeq :=
  let g := Source.Function.monoNonEntry (.init "inl#0") [] .field (.field 7)
  let body : Source.Term := .add
    (.let (.var (.str "y")) (.field 2) (.var (.str "y"))) (.app g.name [] .normal)
  let t : Source.Toplevel := ⟨#[], #[], #[g, rawEntry (.str "x") body]⟩
  withExceptOk "generated-looking global: compile" (AiurTestEnv.build (pure t)) fun env =>
  withExceptOk "generated-looking global: normalize" t.inlineCalls fun t' =>
  withExceptOk "generated-looking global: declarations" t'.mkDecls fun decls =>
  withExceptOk "generated-looking global: body-only declarations" (bodyHoisted t).mkDecls fun bodyDecls =>
    let tc := AiurTestCase.interp `raw_entry #[0] #[9] "generated-looking global call"
    referenceCheck "body-only hoisting" bodyDecls env tc ++ successChecks env decls withProof tc

private def unboundNameChecks : TestSeq :=
  [Local.str "inl#0", .str "inl#1", .str "inl#42", .idx 0].foldl (init := .done)
    fun acc free =>
    let body : Source.Term := .add
      (.let (.var (.str "y")) (.field 2) (.var (.str "y"))) (.var free)
    let t : Source.Toplevel := ⟨#[], #[], #[rawEntry (.str "x") body]⟩
    acc ++ withExceptOk "unbound name: normalize" t.inlineCalls fun normalized =>
      [t, bodyHoisted t, normalized].foldl (init := .done) fun acc candidate =>
      acc ++ withExceptOk "unbound name: declarations" candidate.mkDecls fun decls =>
        let rejected : Bool := match Source.Eval.runFunction decls (.init "raw_entry") [9] default 100 with
          | .error (.unboundVar x) => x == free
          | _ => false
        test s!"unbound {repr free} stays unbound" rejected ++
        test "unbound source is rejected by compilation" (!candidate.compile.isOk)

private def invalidPatternChecks : TestSeq :=
  let duplicate : Source.Toplevel := ⟦
    pub fn duplicate(x: G) -> G { let (y, y) = (x, x); y }
  ⟧
  let alternatives : Source.Toplevel := ⟦
    pub fn alternatives(x: G) -> G { match (x, x) { (0, y) | (z, 1) => 0, _ => 1, } }
  ⟧
  let rejectsDuplicate (t : Source.Toplevel) : Bool :=
    match t.checkAndSimplify with | .error (.duplicatedBind _) => true | _ => false
  let rejectsAlternatives (t : Source.Toplevel) : Bool :=
    match t.checkAndSimplify with | .error (.differentBindings _ _) => true | _ => false
  withExceptOk "duplicate pattern: normalize" duplicate.inlineCalls fun duplicate' =>
  withExceptOk "alternative bindings: normalize" alternatives.inlineCalls fun alternatives' =>
    test "original duplicate pattern rejected" (rejectsDuplicate duplicate) ++
    test "normalized duplicate pattern still rejected" (rejectsDuplicate duplicate') ++
    test "original alternative binding mismatch rejected" (rejectsAlternatives alternatives) ++
    test "normalized alternative binding mismatch still rejected" (rejectsAlternatives alternatives')

private def rejectionChecks (env : AiurTestEnv) (normalized : Source.Decls)
    (name : Lean.Name) (msg : String) : TestSeq := Id.run do
  let g := Global.mk name
  let idx := env.compiled.getFuncIdx name |>.get!
  let src (label : String) (decls : Source.Decls) :=
    let rejects : Bool :=
      match Source.Eval.runFunction decls g [1] default 100 with
      | .error (.typeMismatch s) => s == s!"assertEq: {msg}"
      | _ => false
    test s!"{name}: {label} rejects at the original assertion" rejects
  let native := match env.compiled.bytecode.execute idx #[1] default with
    | .error e => test s!"{name}: native rejects at {msg} ({e})" (e.contains msg)
    | .ok _ => test s!"{name}: native rejects" false
  -- The low-level Rust prover panics on execution errors. Negative fixtures
  -- stop at native execution, the same preflight gate used by IxBy.
  let bytecodeRejects : Bool :=
    match Bytecode.Eval.runFunction env.compiled.bytecode idx #[1] default 100 with
    | .error .assertFailed => true | _ => false
  let interpreterRejects : Bool :=
    match Aiur.runFunction env.decls g [1] default with
    | (.error e, _) => (toString e).contains msg | _ => false
  return src "original source" env.decls ++ src "normalized source" normalized ++
    test s!"{name}: bytecode rejects at an assertion" bytecodeRejects ++
    test s!"{name}: interpreter rejects at {msg}" interpreterRejects ++ native

def suite (withProof : Bool := false) : IO UInt32 := do
  IO.println "aiur-hoisting"
  match AiurTestEnv.build (pure toplevel), toplevel.inlineCalls.bind
      (fun t => t.mkDecls.mapError toString) with
  | .error e, _ | _, .error e => IO.eprintln s!"hoisting setup failed: {e}"; return 1
  | .ok env, .ok normalized =>
    LSpec.lspecIO (.ofList [("aiur-hoisting", [
      cases.foldl (fun acc tc => acc ++ successChecks env normalized withProof tc) .done ++
      localFunctionChecks env ++
      rawNameChecks withProof ++ globalNameChecks withProof ++
      unboundNameChecks ++ invalidPatternChecks ++
      rejectionChecks env normalized `assert_shadow "original x" ++
      rejectionChecks env normalized `assert_order "before read" ++
      rejectionChecks env normalized `left_failure "left operand" ++
      rejectionChecks env normalized `guarded_operand "guarded match" ++
      rejectionChecks env normalized `guarded_rhs "guarded match" ++
      rejectionChecks env normalized `return_guarded "guarded match" ++
      rejectionChecks env normalized `return_continuation "return assertion"
    ])]) []

end AiurTests.Hoisting

end
