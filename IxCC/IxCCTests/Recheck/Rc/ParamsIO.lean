import IxCC.Recheck
import IxCC.Recheck.Rc.Produce

/-! # The parameter total (`Anf.maxParamTotal`) through the verifier

Parameters cost no Anf node, so the node budgets do not bound them, while the source-domain check
(`Own.Plain.programDomain`) walks every one. Certificate admission (`Own.Plain.Certificate.admit`,
`admitContract`) refuses a program whose functions and join points have more than
`Anf.maxParamTotal` parameters in all (`paramTotal`) before it decodes the certificate, and
`Recheck.runWithContracts` before its domain check. The producer cannot reach the limit from an
artifact (after its last `prune`, every parameter of a function but a root is matched by an
argument at a call, which costs Anf nodes; an argument from the code, not a proof), so the inputs
over it are made by hand:

* **at the boundary, hand-made Fir** with a certificate of no action, through the verifier's text
  admission (`Certificate.ofText`): function parameters (512 functions of 2,048, `trap` bodies) and
  join parameters (64 functions each declaring 8 joins of 2,048), exactly at the limit admitted and
  then lowered (`Cfg.Rc.generate`, `checkScopedProgram`, `Public.lower`); one parameter more
  refused with `own.cert.params`, the total and the limit; the over-limit function form admitted at
  a limit equal to its total (monotonicity, `admit_params_mono`); `ofTextContract` refuses too;
* **a registered root** (`Closures.stateLoop`, the corpus's largest total, 240): its plain-RC
  certificate refused by `admit` at a limit of 239 and admitted as the same program at 240 and at
  the default; its zero-RC certificate refused by `runWithContracts` at 239 and accepted, with the
  same object, at 240 and at the default. -/

set_option autoImplicit false
namespace IxCCTests.Recheck.Rc.ParamsIO
open IxCC Lean System
open IxCC.Fir (Var)

def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

def fun1 (params : List Var) (body : Fir.Code) (vars : Nat) : Fir.Fun :=
  { (default : Fir.Fun) with params := params.map (·, .tobj), body, vars }

def prog (fs : List Fir.Fun) : Fir.Program :=
  { funs := Src.NatMap.ofList (fs.zipIdx.map fun (f, i) => (i, f)), size := fs.length,
    exports := [0], ctors := [], known := {} }

/-- A body declaring a chain of joins, one per entry of `widths` (that many fresh parameters each,
numbered from `base`), never jumped to; each join's body and the last continuation `trap`. -/
def joinChain (base : Nat) : List Nat → Fir.Code
  | [] => .trap
  | w :: ws => .jp ws.length ((List.range w).map (base + ·)) false .trap (joinChain (base + w) ws)

/-- The map with no action for a program whose bodies are join chains and `trap`s: every join
captures nothing (a `trap` may leak, so the checker accepts it). -/
def noActions : Fir.Code → Own.Plain.Code
  | .jp j ps rec b k => .jp j ps [] rec (noActions b) (noActions k)
  | _ => .trap

def certText (F : Fir.Program) : String :=
  Own.Plain.Certificate.toText (F.funs.map fun fd => noActions fd.body)

/-- `G` functions of `P` parameters whose bodies are `trap`, then one of `extra` parameters. -/
def functionForm (P G extra : Nat) : Fir.Program :=
  prog (List.replicate G (fun1 (List.range P) .trap P) ++
    (if extra = 0 then [] else [fun1 (List.range extra) .trap extra]))

/-- `G` functions without parameters, each declaring `J` joins of `P` parameters, then one
declaring a join of `extra`. -/
def joinForm (P J G extra : Nat) : Fir.Program :=
  let widths := List.replicate J P
  prog (List.replicate G (fun1 [] (joinChain 0 widths) (P * J)) ++
    (if extra = 0 then [] else [fun1 [] (joinChain 0 [extra]) extra]))

def limit : Nat := Anf.maxParamTotal

/-- At the limit: admitted from text and lowered. -/
def atLimit (label : String) (F : Fir.Program) : IO Unit := do
  let total := Own.Plain.Certificate.paramTotal F
  unless total == limit do fail s!"{label}: parameter total {total}, expected the limit {limit}"
  let t0 ← IO.monoMsNow
  let own ← match Own.Plain.Certificate.ofText F (certText F) with
    | .ok own => pure own
    | .error e => fail s!"{label}: refused at the limit: {e}"
  let some cand := Cfg.Rc.generate F own.bodies | fail s!"{label}: generate declined"
  unless Cfg.Rc.checkScopedProgram F own.bodies cand do fail s!"{label}: checkScopedProgram refused"
  match Cfg.Rc.Public.lower {} F own.bodies cand with
  | .ok _ => pure ()
  | .error e => fail s!"{label}: lowering refused: {e}"
  IO.println s!"PASS parameter total at the limit ({label}, {total}): admitted from text and lowered ({(← IO.monoMsNow) - t0} ms)"

/-- One parameter past the limit: refused, by both admissions, naming the total and the limit;
admitted at a limit equal to the total when `admitAtTotal`. -/
def pastLimit (label : String) (F : Fir.Program) (admitAtTotal : Bool) : IO Unit := do
  let total := Own.Plain.Certificate.paramTotal F
  unless total == limit + 1 do fail s!"{label}: parameter total {total}, expected {limit + 1}"
  let want := s!"own.cert.params: the program has {total} parameters (of its functions and join points together), past the limit {limit} (Anf.maxParamTotal)"
  let text := certText F
  match Own.Plain.Certificate.ofText F text with
  | .ok _ => fail s!"{label}: admitted past the limit"
  | .error e => unless e == want do fail s!"{label}: expected «{want}», got «{e}»"
  match Own.Plain.Certificate.ofTextContract F text with
  | .ok _ => fail s!"{label}: contract-aware admission accepted past the limit"
  | .error e => unless e == want do fail s!"{label} (contract-aware): expected «{want}», got «{e}»"
  if admitAtTotal then
    match Own.Plain.Certificate.ofText F text (params := total) with
    | .ok _ => pure ()
    | .error e => fail s!"{label}: refused at a limit equal to its total: {e}"
  IO.println s!"PASS parameter total past the limit ({label}, {total} > {limit}): refused by both admissions with the total and the limit{if admitAtTotal then s!", admitted at a limit of {total}" else ""}"

def boundary : IO Unit := do
  atLimit "512 functions of 2,048 parameters" (functionForm 2048 512 0)
  pastLimit "512 functions of 2,048 parameters and one of 1" (functionForm 2048 512 1) true
  atLimit "64 functions each declaring 8 joins of 2,048 parameters" (joinForm 2048 8 64 0)
  pastLimit "64 functions each declaring 8 joins of 2,048 parameters, and one join of 1"
    (joinForm 2048 8 64 1) false

/-! ## A registered root -/

def closuresDir : FilePath := "fixtures/corpus/phase2-closures"
def rootName : String := "Closures.stateLoop"
/-- Its parameter total (function parameters; it declares no join with parameters): the corpus's
largest, which the docs cite. -/
def rootTotal : Nat := 240

def registered : IO Unit := do
  let bytes ← IO.FS.readBinFile (closuresDir / "closures.ixe")
  let equations ← IO.ofExcept (Json.parse (← IO.FS.readFile (closuresDir / "closures.equations.json")))
  let input ← IO.ofExcept ((Recheck.ingress bytes equations [rootName]).mapError (·.render))
  let cfg0 : Recheck.Config := { names := ["stateLoop"] }
  let cfg := cfg0.forInput input
  -- plain RC: `admit`
  let fr ← IO.ofExcept ((Recheck.RcReplay.produceFir cfg input).mapError (·.render))
  let total := Own.Plain.Certificate.paramTotal fr.fir
  unless total == rootTotal do fail s!"{rootName}: parameter total {total}, expected {rootTotal}"
  let (cert, _) ← IO.ofExcept ((Recheck.RcReplay.produce cfg0 input).mapError (·.render))
  match Own.Plain.Certificate.admit fr.fir cert.own (params := total - 1) with
  | .ok _ => fail s!"{rootName}: admitted at a limit of {total - 1}"
  | .error e => unless e.startsWith s!"own.cert.params: the program has {total} parameters" do
      fail s!"{rootName}: at a limit of {total - 1}: {e}"
  let some p := (Own.Plain.Certificate.admit fr.fir cert.own (params := total)).toOption |
    fail s!"{rootName}: refused at a limit equal to its total"
  let some p' := (Own.Plain.Certificate.admit fr.fir cert.own).toOption |
    fail s!"{rootName}: refused at the default limit"
  unless Own.Plain.bodyMapEq p.bodies p'.bodies do
    fail s!"{rootName}: admitted as different programs at two limits"
  -- zero RC: `runWithContracts`
  let zcert ← IO.ofExcept ((Recheck.produce cfg input).mapError (·.render))
  match Recheck.runWithContracts cfg input.program zcert (params := total - 1) with
  | .ok _ => fail s!"{rootName}: runWithContracts accepted at a limit of {total - 1}"
  | .error e =>
    unless e.stage == .cert && e.code == "own.plain" &&
        e.message.startsWith s!"own.cert.params: the program has {total} parameters" do
      fail s!"{rootName}: runWithContracts at a limit of {total - 1}: {e.render}"
  let a ← IO.ofExcept ((Recheck.runWithContracts cfg input.program zcert (params := total)).mapError
    fun e => s!"{rootName}: runWithContracts refused at a limit equal to its total: {e.render}")
  let a' ← IO.ofExcept ((Recheck.runWithContracts cfg input.program zcert).mapError
    fun e => s!"{rootName}: runWithContracts refused at the default limit: {e.render}")
  unless a.object == a'.object do fail s!"{rootName}: two objects at two limits"
  IO.println s!"PASS parameter total of a registered root ({rootName}, {total}): admit and runWithContracts refuse at {total - 1}, accept the same program at {total} and at the default {limit}"

def run : IO Unit := do
  boundary
  registered

end IxCCTests.Recheck.Rc.ParamsIO
