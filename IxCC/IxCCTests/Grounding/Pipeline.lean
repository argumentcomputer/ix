import IxCC.Recheck.Produce
import IxCC.Recheck.Proof.Front
import IxCCCorrect.GroundCheck
import IxCCCorrect.GroundShape
import IxCCCorrect.Unique
import IxCCCorrect.UniqueIota
import IxCCCorrect.UniqueNat
import IxCCCorrect.UniqueEnum

/-! # `tests-grounding pipeline`: the pipeline's grounding check on every committed root

`IxCC.Correct.groundCheck` (`IxCCCorrect.GroundCheck`) is the function a `compile` calls after the
certificate checker accepts: its acceptance is the hypothesis `GroundOk` of the composed theorems
(`IxCCCorrect.Compose`, `IxCCCorrect.ComposeExe`). This report runs it root by root on the
committed families `tests-shape` measures (same directories, same closures, same root labels, so
the two reports can be joined by line), and on three more (`phase1-decline`, `src-words`,
`src-diag`).

For each closure: ingress with every sidecar root (the kernel's acceptance), then the compiler
(`Recheck.compileInputRetry`). Where it compiles, the check reads what the certificate checker
checked: the artifact's source and checked annotation, the certificate's annotation, and root
`i`'s view. Where the compiler declines the closure (a root it refuses fails all of them), the
check reads the checked source the front end builds (as `tests-grounding`'s loaders do) and a
stand-in view that tags a constructor by its declared index; such closures are marked
`source only`, and the view matters only at an enumeration result. Root `i` is checked as root 0
of the program with that root alone, at its own address as the claimed target.

One line per root: `accept` with the calling convention the check returns, or `refuse` with the
first refusal (`groundRefusal`). Then a table per family and a histogram of first refusals. It
reports; it asserts nothing. `GROUND_ONLY=<family>` runs one family. -/

namespace IxCCTests.Grounding.Pipeline

open IxCC IxCC.Src IxCC.Sem IxCC.Correct

/-- The committed families: a label and the directory of its closures (the first fifteen are
`tests-shape`'s, in its order). -/
def families : List (String × String) :=
  [("bench-k1", "fixtures/ixon-v4/bench-k1"),
   ("k1", "fixtures/ixon-v4/k1"),
   ("phase1-scalar", "fixtures/corpus/phase1-scalar"),
   ("phase1-abi", "fixtures/corpus/phase1-abi"),
   ("phase1-boundary", "fixtures/corpus/phase1-boundary"),
   ("phase1-machines", "fixtures/corpus/phase1-machines"),
   ("phase1-resource", "fixtures/corpus/phase1-resource"),
   ("phase2-arity", "fixtures/corpus/phase2-arity"),
   ("phase2-closures", "fixtures/corpus/phase2-closures"),
   ("grounding", "fixtures/corpus/grounding"),
   ("ownership", "fixtures/ownership"),
   ("rc-budget", "fixtures/rc/budget"),
   ("rc-deep", "fixtures/rc/deep"),
   ("rc-real-source", "fixtures/rc/real-source"),
   ("fold", "fixtures/fold"),
   ("phase1-decline", "fixtures/corpus/phase1-decline"),
   ("src-words", "fixtures/ixon-v4/src-words"),
   ("src-diag", "fixtures/ixon-v4/src-diag")]

/-- The closures of a directory: each `.ixe` with its sidecar (`<stem>.equations.json`, else
`consumer.equations.json`, else `equations.json`). -/
def closuresOf (dir : String) : IO (List (String × String × String)) := do
  let entries ← System.FilePath.readDir dir
  let names := (entries.toList.map fun e => e.fileName).filter fun n => n.endsWith ".ixe"
  let names := names.mergeSort fun a b => a ≤ b
  let mut out := []
  for n in names do
    let stem := n.replace ".ixe" ""
    let cands := [s!"{dir}/{stem}.equations.json", s!"{dir}/consumer.equations.json",
      s!"{dir}/equations.json"]
    let mut eqs := none
    for c in cands do
      if eqs.isNone && (← System.FilePath.pathExists c) then eqs := some c
    match eqs with
    | some e => out := out ++ [(stem, s!"{dir}/{n}", e)]
    | none => IO.println s!"{dir}/{n}: no sidecar found, skipped"
  return out

/-- A stand-in for a root's view where the compiler declines the closure: a number as itself, a
field-less constructor at its declared index. -/
def standInView (p : Program) : View := fun o =>
  match o with
  | some (.nat n) => some (some (.nat n))
  | some (.ctor cid []) => some (some (.ctor (IxCC.Grounding.readTag p cid) []))
  | _ => none

/-- What the check reads of a closure. -/
structure Loaded where
  kernel : Src.KernelFront.Kernel
  names : List String
  src : Program
  checked : Relevance.Checked
  ann : Relevance.Ann
  view : Nat → View
  mode : String

def load (ixe eqs : String) : IO Loaded := do
  let bytes ← IO.FS.readBinFile ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let k ← match Recheck.ingress bytes json [] with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"ingress: {e.render}")
  match Recheck.compileInputRetry {} k with
  | .ok (c, a) =>
    return { kernel := k.kernel, names := k.names, src := a.src, checked := a.checked,
             ann := c.relevance, view := fun i => a.front.view i, mode := "compiled" }
  | .error e =>
    let cfg : Recheck.Config := {}
    let cfg := cfg.forInput k
    let P := k.program
    let (table, _, _) := Src.Table.build cfg.table P k.hints.proposals
    let p0 := { P with table }
    let ann ← IO.ofExcept (k.kernel.annotateChecked p0)
    match Src.Recheck.annotation p0 ann with
    | .ok (src, checked) =>
      return { kernel := k.kernel, names := k.names, src, checked, ann,
               view := fun _ => standInView src, mode := s!"source only: compiler {e.code}" }
    | .error _ => throw (IO.userError "the annotation was refused")

def showAbi (abi : Abi) : String :=
  let res := match abi.result with
    | .nat => "Nat"
    | .enum cs => s!"enum of {cs.length}"
    | .word bits _ => s!"word of {bits} bits"
  s!"{abi.params.length} Nat -> {res}"

def bump (key : String) : List (String × Nat) → List (String × Nat)
  | [] => [(key, 1)]
  | (k, n) :: rest => if k == key then (k, n + 1) :: rest else (k, n) :: bump key rest

/-- **The exact check, per root**: ingress with this root alone (the program a claim on this root
compiles), the compiler, and `groundShapeCheckP` on what it produced, at root 0's address: the
function `recheck_agrees_shaped`, `plain_exe_tier1Stdout_shaped` and `tier1Check_sound` are about
(with the producer's certificate). -/
def exactOf (bytes : ByteArray) (json : Lean.Json) (name : String) : Except String Abi :=
  match Recheck.ingress bytes json [name] with
  | .error e => .error s!"ingress: {e.render}"
  | .ok k =>
    match Recheck.compileInputRetry {} k with
    | .error e => .error s!"compiler: {e.code}"
    | .ok (c, a) =>
      match a.src.roots.head? with
      | none => .error "noRoot"
      | some (addr, _) => groundShapeCheckP k c a addr

/-- **Why `declOk` refuses** a root: the recursors of its closure whose class the check does not
admit, with their parameter count, their class, and per rule the kernel's firing mode and whether
the ι step compares parameters (`RecRule.compareParams`). -/
def declOkDiag (k : Src.KernelFront.Kernel) (src : Program) (root : CId) : String :=
  let κ := keyMap k.rd
  let Sl := closureOf src root
  let env' := IxCC.Grounding.selEnv src k.acc.env κ Sl
  let bad := Sl.filter fun c => !IxCC.Grounding.declOkB src env' κ IxCC.Grounding.admittedClasses c
  let show1 := fun (c : CId) =>
    let np := match src.decl? c with
      | some (.recr _ _ _ np _ _ _ _ _ _) => s!"{np}"
      | some (.quot ..) => "quot"
      | _ => "?"
    let cls := match IxCC.Grounding.recClassB src env' κ c with
      | some cl => s!"{repr cl}"
      | none => "none"
    let rules : List String := match env'.find? (κ c) with
      | some (.recInfo _ _ _ rs) => rs.map fun (rl : Ix.Kernel.RecRule .anon) =>
          let f : String := match rl.fire with
            | .plain => "plain"
            | .nested .. => "nested"
            | .inert => "inert"
          s!"{f}/cmp={rl.compareParams}"
      | _ => []
    s!"{c} np={np} class={cls} rules={rules}"
  ", ".intercalate (bad.map show1)

/-- The bases of the modeled-route members (for the report). -/
def modeledBases (env : IxCC.Grounding.KEnv) : List String :=
  (env.consts.filterMap fun ci => match ci.name with
    | .aux b .model => some s!"{repr b}"
    | _ => none).eraseDups

/-- How many constants of the environment the kernel installed through the modeled route (a
member's `_model`) and through the nested modeller (`pack` transports): where `CtorCanon` would
have to be argued through generated models rather than the direct routes' leaves. -/
def modeledCount (env : IxCC.Grounding.KEnv) : Nat × Nat :=
  env.consts.foldl (fun acc ci => match ci.name with
    | .aux _ .model => (acc.1 + 1, acc.2)
    | .aux _ (.pack _) => (acc.1, acc.2 + 1)
    | _ => acc) (0, 0)

/-- **Whether an enumeration answer is unique** (`agrees_unique_enum`): the enumeration and its
recursor found from the claim's constructor keys, then checked by `enumUniqueB`. -/
def enumUnique? (acc : Src.KernelFront.Accepted) (cs : List Ixon.Address) : Bool :=
  let keys := cs.filterMap (keyOf acc)
  match keys.head? with
  | none => false
  | some k0 =>
    match acc.env.find? k0 with
    | some (.ctorInfo cv _ _) =>
      match cv.type with
      | .const D [] =>
        acc.env.consts.any fun ci => match ci with
          | .recInfo _ _ _ rules =>
            (keys.all fun k => rules.any (·.ctor == k)) &&
              enumUniqueB acc cs D (rules.map (·.ctor)) ci.name
          | _ => false
      | _ => false
    | _ => false

/-- A stored constant of type `Bool.true = Bool.false → False` (the witness `numeralBasisB` asks
for), if the environment has one. -/
def neKey? (env : IxCC.Grounding.KEnv) : Option IxCC.Grounding.KKey :=
  let cands := env.consts.filter fun ci => match ci.toConstantVal.type with
    | .forallE _ (.const f []) _ => f == Ix.Kernel.falseName
    | _ => false
  (cands.find? fun ci => IxCC.Grounding.boolTrueNeFalseB env ci.name).map (·.name)

/-- A stored constant of type `Bool.false = Bool.true → False` (the other orientation, which
`numeralBasisB` does not accept: reported only). -/
def neKeyRev? (env : IxCC.Grounding.KEnv) : Option IxCC.Grounding.KKey :=
  let d := IxCC.Grounding.eqE (.succ .zero) (.const IxCC.Grounding.boolKey [])
    (.const Ix.Kernel.boolFalseName []) (.const Ix.Kernel.boolTrueName [])
  (env.consts.find? fun ci => match ci.toConstantVal.type with
    | .forallE d' (.const f []) _ => decide (d' = d) && f == Ix.Kernel.falseName
    | _ => false).map (·.name)

def run : IO Bool := do
  let only ← IO.getEnv "GROUND_ONLY"
  let out ← IO.getStdout
  let fast := (← IO.getEnv "GROUND_FAST").isSome
  let mut rows : List (String × Nat × Nat × Nat × Nat) := []
  let mut hist : List (String × Nat) := []
  let mut shapeHist : List (String × Nat) := []
  let mut unloadable : List String := []
  let mut witnessed : List String := []
  for (family, dir) in families do
    if only.isSome && only != some family then continue
    let mut total := 0
    let mut accepted := 0
    let mut escapeFree := 0
    let mut separated := 0
    for (stem, ixe, eqs) in ← closuresOf dir do
      let label := s!"{family} {stem}"
      let loaded ← try
        let ld ← load ixe eqs
        pure (some ld)
      catch e =>
        IO.println s!"{label}: not loaded: {(toString e).take 300}"
        pure none
      match loaded with
      | none => unloadable := unloadable ++ [label]
      | some ld =>
        let bytes ← IO.FS.readBinFile ixe
        let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
        let env := ld.kernel.acc.env
        let ne := neKey? env
        let sepW := match ne with
          | some kNe => numeralBasisB env kNe
          | none => false
        let sep := sepW || numeralBasisIB env || numeralBasisNB env
        let parts := s!"nat {IxCC.Grounding.natBasisB env}, bool {IxCC.Grounding.boolBasisB env}, Nat.beq {IxCC.Grounding.natBeqStoredB env}, litDefs {IxCC.Grounding.litDefsB env}, Bool.rec {boolRecB env}, Nat.rec {natRecB env}"
        if ne.isSome || (neKeyRev? env).isSome then
          witnessed := witnessed ++ [s!"{label} (true≠false: {ne.isSome}, false≠true: {(neKeyRev? env).isSome})"]
        let mc := modeledCount env
        if mc.1 > 0 then IO.println s!"  modeled bases: {(modeledBases env).take 10}"
        IO.println s!"{label}: {ld.src.roots.length} roots, {ld.mode}, numerals separated: {sep} ({parts}); modeled-route constants {mc.1}, nested packs {mc.2}"
        for (name, i) in ld.names.zipIdx do
          let some r := ld.src.roots[i]? | continue
          total := total + 1
          let srcI := { ld.src with roots := [r] }
          let t0 ← IO.monoMsNow
          match groundCheck ld.kernel srcI ld.checked ld.ann (ld.view i) r.1 with
          | .ok abi =>
            accepted := accepted + 1
            let natRes := abi.result == ResTy.nat
            if sep && natRes then separated := separated + 1
            else match abi.result with
              | .enum cs => if enumUnique? ld.kernel.acc cs then separated := separated + 1
              | _ => pure ()
            let efS ← match (if fast then .error "skipped (GROUND_FAST)" else exactOf bytes json name) with
              | .ok _ =>
                escapeFree := escapeFree + 1
                pure "escape-free"
              | .error reason =>
                shapeHist := bump (reason.take 80).toString shapeHist
                pure s!"not escape-free: {reason.take 200}"
            IO.println s!"{label} {name}: accept, {showAbi abi}; {efS} ({(← IO.monoMsNow) - t0} ms)"
          | .error reason =>
            hist := bump reason hist
            IO.println s!"{label} {name}: refuse, {reason} ({(← IO.monoMsNow) - t0} ms)"
            if reason.startsWith "check: declOk" then
              IO.println s!"  declOk: {declOkDiag ld.kernel srcI r.2}"
          out.flush
    rows := rows ++ [(family, total, accepted, escapeFree, separated)]
  IO.println "family: roots, accepted by groundCheck, escape-free (groundShapeCheck: also compiled and shaped), unique (a Nat result in an environment that separates numerals)"
  let mut tot := (0, 0, 0, 0)
  for (family, n, a, e, s) in rows do
    IO.println s!"  {family}: {n}, {a}, {e}, {s}"
    tot := (tot.1 + n, tot.2.1 + a, tot.2.2.1 + e, tot.2.2.2 + s)
  IO.println s!"  all: {tot.1}, {tot.2.1}, {tot.2.2.1}, {tot.2.2.2}"
  IO.println "first refusals of groundCheck:"
  for (k, n) in hist.mergeSort fun a b => a.2 ≥ b.2 do
    IO.println s!"  {n}  {k}"
  IO.println "accepted by groundCheck, not escape-free:"
  for (k, n) in shapeHist.mergeSort fun a b => a.2 ≥ b.2 do
    IO.println s!"  {n}  {k}"
  IO.println s!"closures storing a Bool.true/Bool.false separation: {witnessed}"
  if !unloadable.isEmpty then IO.println s!"not loaded: {unloadable}"
  IO.println s!"tests-grounding (pipeline): groundCheck accepted {tot.2.1} of {tot.1} roots, {tot.2.2.1} escape-free"
  return true

end IxCCTests.Grounding.Pipeline
