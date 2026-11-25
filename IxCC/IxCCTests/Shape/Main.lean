import IxCC.Recheck.Produce
import IxCCCorrect.Shape2Produce
import IxCCCorrect.ShapeHook

/-! # `tests-shape`: the shape producer and the shape check on committed closures

For each closure of the committed families listed in `families` and each of its sidecar roots: the kernel accepts the
closure (`Recheck.ingress`), the front end builds the checked source SrcEval runs (the
table, the annotation, lazification, as `tests-grounding` does), the untrusted producer
proposes a shape certificate (`IxCC.Correct.Shape2.Produce.produce`), and the decision
`IxCC.Correct.Shape2.certOk` is run on it. One line per root: `accept` with the root's shape, or `reject` with the
class of the first instance the decision refuses (`why`, a diagnosis for reading) and that
instance. Then a table per family and a histogram of the classes. The suite reports; it
asserts nothing and always exits 0. `SHAPE_ONLY=<family>` runs one family; `SHAPE_DETAIL=1`
prints a refused instance's body. -/

open IxCC IxCC.Src IxCC.Correct.Shape2

namespace IxCCTests.Shape

/-- The checked source of a closure, with every sidecar root. -/
def loadSrc (ixe eqs : String) : IO Src.Program := do
  let stem := ixe
  let bytes ← IO.FS.readBinFile ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let k ← match Recheck.ingress bytes json [] with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"{stem}: ingress: {e.render}")
  let cfg : Recheck.Config := {}
  let cfg := cfg.forInput k
  let P := k.program
  let (table, _, _) := Src.Table.build cfg.table P k.hints.proposals
  let p0 := { P with table }
  let ann ← IO.ofExcept (k.kernel.annotateChecked p0)
  match Src.Recheck.annotation p0 ann with
  | .ok r => pure r.1
  | .error _ => throw (IO.userError s!"{stem}: the annotation was refused")

/-- What kind of constant `c` is, as SrcEval resolves it. -/
def kindOf (p : Src.Program) (c : CId) : String :=
  match p.table.resolveOf c with
  | some (.prim op) => s!"prim {op.name}"
  | some (.word _ _ _) => "word"
  | some (.csimp _ _ _) => "csimp"
  | some (.eqn _ _) => "eqn"
  | some (.case _) => "case"
  | none =>
    match p.decl? c with
    | some (.recr _ _ _ np nmot nmin ni _ _ _) =>
      let kind := match p.table.recKindOf c with
        | some .ordinary => "ordinary"
        | some (.subsingleton _ _) => "subsingleton"
        | some .empty => "empty"
        | none => "no kind"
      s!"recursor ({kind}, {np} params, {nmot} motives, {nmin} minors, {ni} indices)"
    | some d => d.kindName
    | none => "no declaration"

def hex (a : Ixon.Address) : String := a.toHex

/-- The constants a term names, in order, without repeats. -/
def constsIn : Src.Term → List CId → List CId
  | .const c _, acc => if acc.contains c then acc else acc ++ [c]
  | .app f a _ _, acc => constsIn a (constsIn f acc)
  | .lam _ _ t, acc => constsIn t acc
  | .letE _ _ _ _ v b, acc => constsIn b (constsIn v acc)
  | .proj _ _ e, acc => constsIn e acc
  | _, acc => acc

/-- The term SrcEval runs for a constant, if it unfolds one. -/
def bodyOf (p : Src.Program) (c : CId) : Option Src.Term :=
  match p.table.resolveOf c with
  | some (.eqn _ body) => some body
  | some _ => none
  | none =>
    match p.decl? c with
    | some (.defn .defn .safe _ _ v) => some v
    | _ => none

/-- A shape on one line. -/
def showShape : Shape → String
  | .nat => "N"
  | .enum i => s!"E{i}"
  | .data d => s!"D{d}"
  | .irr => "_"
  | .any => "*"
  | .inter a b => s!"({showShape a} & {showShape b})"
  | .fn a b => s!"({showShape a} -> {showShape b})"

/-- A term on one line: `#i` a variable, `cN` a constant, `~a` an argument irrelevant at `ls`,
`'a` a by-name one, `\` a λ (`\~` irrelevant binder), `T` a type or sort. -/
def showTerm (ls : Levels) : Src.Term → String
  | .var i => s!"#{i}"
  | .sort _ => "S"
  | .pi _ _ _ => "T"
  | .const c _ => s!"c{c}"
  | .natLit n => s!"{n}"
  | .strLit _ => "str"
  | .proj s i e => s!"{showTerm ls e}.{i}@{s}"
  | .lam b _ t => (if b.rel.irrAt ls then "\\~" else "\\") ++ (if b.propWhen.allowsBeta ls then "" else "!") ++ showTerm ls t
  | .letE _ _ r _ v t => s!"let{if r.irrAt ls then "~" else ""} {showTerm ls v}; {showTerm ls t}"
  | .app f a m r =>
    let arg := if r.irrAt ls then "~" else (if m == .byName then "'" else "") ++ showTerm ls a
    s!"({showTerm ls f} {arg})"

/-- Detail of a refused instance, for reading: its body and the constants it names. -/
def detail (p : Src.Program) (cert : Cert) (c : CId) (ls : Levels) : String :=
  match bodyOf p c with
  | some t =>
    let cs := constsIn t []
    let lines := cs.map fun d =>
      let shapes := (cert.insts.filter fun e => e.1 == d).map fun e => s!"{e.2.1}:{showShape e.2.2}"
      s!"    #{d} {kindOf p d} {(hex (p.addr d)).take 12} {shapes}"
    s!"  body: {(showTerm ls t).take 1500}\n  names:\n" ++ "\n".intercalate lines
  | none => s!"  (no body; levels {ls})"

/-- A coarse class of a constant, for the histogram of refusals. -/
def kindClass (p : Src.Program) (c : CId) : String :=
  let recClass (r : CId) (what : String) : String :=
    match p.decl? r with
    | some (.recr _ _ _ np nmot _ ni _ _ _) =>
      let kind := match p.table.recKindOf r with
        | some .ordinary => ""
        | some (.subsingleton _ _) => ", subsingleton"
        | some .empty => ", empty"
        | none => ", no kind"
      s!"{what}{kind}{if np > 0 then ", parameters" else ""}\
        {if ni > 0 then ", indices" else ""}{if nmot > 1 then ", several motives" else ""}"
    | _ => what
  match p.table.resolveOf c with
  | some (.prim _) => "primitive"
  | some (.word _ _ _) => "word operation"
  | some (.csimp _ _ _) => "csimp"
  | some (.eqn _ _) => "definition"
  | some (.case r) => recClass r "case"
  | none =>
    match p.decl? c with
    | some (.recr ..) => recClass c "recursor"
    | some d => d.kindName
    | none => "undeclared"

/-- Why synthesis gives a term no shape: a class and a detail. A diagnosis for reading;
nothing depends on it. It follows `synth` and reports the first subterm that fails. -/
def why (p : Src.Program) (cert : Cert) (ls : Levels) :
    List Shape → Src.Term → Exp → Option (String × String)
  | Γ, .var i, _ => if (Γ[i]?).isSome then none else some ("variable out of scope", s!"#{i}")
  | _, .const c us, _ =>
    if (instsOf cert.insts c (us.map (evalUniv ls))).isEmpty then
      some (s!"no instance proposed: {kindClass p c}", s!"c{c}")
    else none
  | _, .strLit _, _ => some ("string literal", "")
  | Γ, .app f a _ r, _ =>
    let irrArg := r.irrAt ls
    let argShapes := if irrArg then [Shape.irr] else synth cert.insts cert.datas cert.lets ls Γ a .none
    let isLam := match f with
      | .lam _ _ _ => true
      | _ => false
    let fShapes :=
      if isLam then argShapes.flatMap fun σ => synth cert.insts cert.datas cert.lets ls Γ f (.dom σ)
      else synth cert.insts cert.datas cert.lets ls Γ f .none
    match fShapes with
    | [] =>
      if isLam then
        match argShapes with
        | [] => (why p cert ls Γ a .none).orElse fun _ =>
            some ("applied λ whose argument needs an expected shape", "")
        | σ :: _ => (why p cert ls Γ f (.dom σ)).orElse fun _ => some ("applied λ has no shape", "")
      else (why p cert ls Γ f .none).orElse fun _ => some ("function has no shape", "")
    | s :: _ =>
      match s with
      | .fn σ _ =>
        if irrArg then
          if σ = .irr then none
          else some ("irrelevant argument at a relevant domain", showShape σ)
        else if σ ∈ synth cert.insts cert.datas cert.lets ls Γ a (.full σ) then none
        else (why p cert ls Γ a (.full σ)).orElse fun _ =>
          some ("argument shape mismatch", s!"expected {showShape σ}, has \
            {(synth cert.insts cert.datas cert.lets ls Γ a .none).map showShape}")
      | .irr => some ("applies a value of unknown shape", "")
      | s => some ("applies a value that is not a function", showShape s)
  | Γ, .lam b _ body, e =>
    match e with
    | .full (.fn σ τ) =>
      if !b.propWhen.allowsBeta ls then some ("λ whose binder forbids β at these levels", "")
      else if τ ∈ synth cert.insts cert.datas cert.lets ls (σ :: Γ) body (.full τ) then none
      else (why p cert ls (σ :: Γ) body (.full τ)).orElse fun _ =>
        some ("result shape mismatch", s!"expected {showShape τ}, has \
          {(synth cert.insts cert.datas cert.lets ls (σ :: Γ) body .none).map showShape}")
    | .full s => some ("λ where a value that is not a function is expected", showShape s)
    | .dom σ =>
      if !b.propWhen.allowsBeta ls then some ("λ whose binder forbids β at these levels", "")
      else why p cert ls (σ :: Γ) body .none
    | .none => some ("λ with no expected shape", "")
  | Γ, .letE _ _ r _ v body, e =>
    if r.irrAt ls then why p cert ls (.irr :: Γ) body e
    else
      match synth cert.insts cert.datas cert.lets ls Γ v .none with
      | [] => (why p cert ls Γ v .none).orElse fun _ => some ("let value has no shape", "")
      | σ :: _ => why p cert ls (σ :: Γ) body e
  | Γ, .proj s i e', _ =>
    match synth cert.insts cert.datas cert.lets ls Γ e' .none with
    | [] => (why p cert ls Γ e' .none).orElse fun _ => some ("projection subject has no shape", "")
    | σ :: _ =>
      if (projRes cert.datas s i σ).isEmpty then
        some ("projection from a value that is not a structure entry", showShape σ)
      else none
  | _, _, _ => none

/-- The class and detail of a refused instance. -/
def reason (p : Src.Program) (cert : Cert) (d : CId) (ls : Levels) (σ : Shape) : String × String :=
  match bodyOf p d with
  | some t =>
    match why p cert ls [] t (.full σ) with
    | some r => r
    | none => ("result shape mismatch", s!"expected {showShape σ}, has \
        {(synth cert.insts cert.datas cert.lets ls [] t .none).map showShape}")
  | none => (s!"refused instance of a {kindClass p d}", showShape σ)

/-- Is this the shape of a root the immortal path's corollaries cover: `Nat` parameters,
a `Nat` or enumeration result? -/
def viewedShape : Shape → Bool
  | .nat => true
  | .enum _ => true
  | .fn .nat τ => viewedShape τ
  | _ => false

/-- For the fields of a certificate taken from their uses: how many have 0, 1, 2, … use shapes. -/
def useCounts (fields : List (Nat × Nat × Nat)) : List (Nat × Nat) :=
  let m := fields.foldl (fun m f => max m f.2.2) 0
  (List.range (m + 1)).filterMap fun k =>
    let n := (fields.filter fun f => f.2.2 == k).length
    if n == 0 then none else some (k, n)

/-- The outcome on one root. -/
inductive Outcome where
  /-- `certOk`, at a root shape `neverWrong_of_cert_nat` or `_enum` reads -/
  | viewed
  /-- `certOk`, at another root shape (`run_ok_vals` only) -/
  | unviewed
  /-- refused, with the class of the first refused instance -/
  | refused (cls : String)

/-- Run the producer and the decision on root `i` of `p`. -/
def runRoot (label : String) (p : Src.Program) (i : Nat) (name : String) : IO Outcome := do
  let some (_, c) := p.roots[i]? | do
    IO.println s!"{label} {name}: no such root"
    return .refused "no such root"
  let out ← IO.getStdout
  IO.print s!"{label} {name}: "
  out.flush
  let t0 ← IO.monoMsNow
  let (cert, fields) := Produce.produceWith p c
  let n := cert.insts.length
  IO.print s!"produced {n}"
  out.flush
  let tp ← IO.monoMsNow
  IO.print s!" in {tp - t0} ms; "
  out.flush
  if n > 4000 then
    IO.println s!"reject [the producer did not converge: {n} instances, not checked]"
    return .refused "the producer did not converge (more than 4000 instances)"
  let size := s!"{cert.insts.length} instances, {cert.enums.length} enumerations, \
    {cert.datas.length} data entries, fields by uses {useCounts fields}"
  if (← IO.getEnv "SHAPE_DUMP").isSome then
    IO.println ""
    for (D, d) in cert.datas.zipIdx do
      IO.println s!"  D{d} = #{D.ind} {(hex (p.addr D.ind)).take 8} struct={D.struct} \
        {D.ctors.map fun e => (e.1, e.2.map showShape)}"
    for (d, ls, σ) in cert.insts do
      IO.println s!"  #{d} {kindOf p d} {(hex (p.addr d)).take 8} {ls} : {showShape σ}\n      \
        {match bodyOf p d with | some t => (showTerm ls t).take 700 | none => ""}"
  let ok := certOk p cert
  let t1 ← IO.monoMsNow
  if ok then
    let rootShape := match cert.insts.head? with
      | some e => e.2.2
      | none => .irr
    IO.println s!"accept, root shape {showShape rootShape} ({size}; {t1 - t0} ms)"
    return if viewedShape rootShape then .viewed else .unviewed
  else
    match cert.insts.find? fun e => !entryOk p cert e.1 e.2.1 e.2.2 with
    | some (d, ls, σ) =>
      let (cls, det) := reason p cert d ls σ
      IO.println s!"reject [{cls}] {det} ({size}; {t1 - t0} ms); first refused \
        instance: {kindOf p d} {(hex (p.addr d)).take 16} at levels {ls}, shape {showShape σ}"
      if (← IO.getEnv "SHAPE_DETAIL").isSome then IO.println (detail p cert d ls)
      return .refused cls
    | none =>
      IO.println s!"reject [table entry refused] ({size}; {t1 - t0} ms)"
      return .refused "table entry refused"

/-- The committed families: a label and the directory of its closures. Not listed, because
their roots are meant to be declined: `fixtures/corpus/phase1-decline` and
`fixtures/ixon-v4/src-diag`. -/
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
   ("fold", "fixtures/fold")]

/-- The closures of a directory: each `.ixe` with its sidecar (`<stem>.equations.json`,
else `consumer.equations.json`, else `equations.json`). -/
def closuresOf (dir : String) : IO (List (String × String × String)) := do
  let entries ← System.FilePath.readDir dir
  let names := (entries.toList.map fun e => e.fileName).filter fun n => n.endsWith ".ixe"
  let names := names.mergeSort fun a b => a ≤ b
  let mut out := []
  for n in names do
    let stem := (n.dropRight 4)
    let cands := [s!"{dir}/{stem}.equations.json", s!"{dir}/consumer.equations.json",
      s!"{dir}/equations.json"]
    let mut eqs := none
    for c in cands do
      if eqs.isNone && (← System.FilePath.pathExists c) then eqs := some c
    match eqs with
    | some e => out := out ++ [(stem, s!"{dir}/{n}", e)]
    | none => IO.println s!"{dir}/{n}: no sidecar found, skipped"
  return out

/-- How many `Nat` parameters a root shape starts with. -/
def natParams : Shape → Nat
  | .fn .nat τ => natParams τ + 1
  | _ => 0

/-- **The whole checked path on one closure**: the recheck producer and `Recheck.run`,
the shape producer on the checked source the run made (one certificate for all roots),
and `runShaped` (`IxCCCorrect.ShapeHook`), whose acceptance is the hypothesis of
`runShaped_sound`. -/
def endToEnd (label ixe eqs : String) : IO Bool := do
  let bytes ← IO.FS.readBinFile ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let k ← match Recheck.ingress bytes json [] with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"{label}: ingress: {e.render}")
  let cfg : Recheck.Config := {}
  let cfg := cfg.forInput k
  let out ← IO.getStdout
  IO.print s!"{label}: "
  out.flush
  match Recheck.produce cfg k with
  | .error e =>
    IO.println s!"the recheck producer declines: {(e.render).take 160}"
    return false
  | .ok c =>
    match Recheck.run cfg k.program c with
    | .error e =>
      IO.println s!"Recheck.run declines: {(e.render).take 160}"
      return false
    | .ok a =>
      IO.print "run; "
      out.flush
      let roots := a.src.roots.map fun r => r.2
      let sc := Produce.produceAll a.src roots
      IO.print s!"{sc.insts.length} instances; "
      out.flush
      if sc.insts.length > 4000 then
        IO.println "the shape producer did not converge on some root; not checked"
        return false
      let arities := roots.map fun root =>
        match sc.insts.find? fun e => e.1 == root with
        | some e => natParams e.2.2
        | none => 0
      let t0 ← IO.monoMsNow
      match runShaped cfg k.program c sc arities with
      | .ok _ =>
        IO.println s!"runShaped accepts: {roots.length} roots at {arities} parameters, \
          {sc.insts.length} instances, {sc.datas.length} data entries ({(← IO.monoMsNow) - t0} ms)"
        return true
      | .error (.recheck e) =>
        IO.println s!"runShaped: Recheck.run declines: {(e.render).take 160}"
        return false
      | .error .shape =>
        IO.println s!"runShaped refuses the shape certificate or a root \
          (arities {arities}, certOk {certOk a.src sc})"
        return false

def bump (key : String) : List (String × Nat) → List (String × Nat)
  | [] => [(key, 1)]
  | (k, n) :: rest => if k == key then (k, n + 1) :: rest else (k, n) :: bump key rest

def run : IO UInt32 := do
  let only ← IO.getEnv "SHAPE_ONLY"
  let rootOnly ← IO.getEnv "SHAPE_ROOT"
  let mut rows : List (String × Nat × Nat × Nat × Nat) := []
  let mut hist : List (String × Nat) := []
  let mut unloadable : List String := []
  for (family, dir) in families do
    if only.isSome && only != some family then continue
    let mut total := 0
    let mut viewed := 0
    let mut unviewed := 0
    let mut refused := 0
    for (stem, ixe, eqs) in ← closuresOf dir do
      let label := s!"{family} {stem}"
      let loaded ← try
        let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
        let names := match Src.Hints.ofK1Json json with
          | .ok h => h.roots.toList.map fun (r : Ixon.Address × Option String) => r.2.getD "?"
          | .error _ => []
        let p ← loadSrc ixe eqs
        pure (some (p, names))
      catch e =>
        IO.println s!"{label}: not loaded: {(toString e).take 300}"
        pure none
      match loaded with
      | none => unloadable := unloadable ++ [label]
      | some (p, names) =>
        for (name, i) in names.zipIdx do
          if let some want := rootOnly then
            if name != want then continue
          total := total + 1
          match ← runRoot label p i name with
          | .viewed => viewed := viewed + 1
          | .unviewed => unviewed := unviewed + 1
          | .refused cls =>
            refused := refused + 1
            hist := bump cls hist
    rows := rows ++ [(family, total, viewed, unviewed, refused)]
  IO.println "family: roots, accepted at a Nat or enumeration root shape, accepted at another \
    root shape, refused"
  let mut tot := (0, 0, 0, 0)
  for (family, n, v, u, r) in rows do
    IO.println s!"  {family}: {n}, {v}, {u}, {r}"
    tot := (tot.1 + n, tot.2.1 + v, tot.2.2.1 + u, tot.2.2.2 + r)
  IO.println s!"  all: {tot.1}, {tot.2.1}, {tot.2.2.1}, {tot.2.2.2}"
  IO.println "first refusals by class:"
  for (k, n) in hist.mergeSort fun a b => a.2 ≥ b.2 do
    IO.println s!"  {n}  {k}"
  if !unloadable.isEmpty then IO.println s!"not loaded: {unloadable}"
  IO.println s!"accepted {tot.2.1 + tot.2.2.1} of {tot.1} roots"
  if (← IO.getEnv "SHAPE_E2E").isSome then
    IO.println "the whole checked path (Recheck.run, then runShaped):"
    let mut ok := 0
    let mut n := 0
    for (family, dir) in families do
      if only.isSome && only != some family then continue
      for (stem, ixe, eqs) in ← closuresOf dir do
        n := n + 1
        let r ← try endToEnd s!"  {family} {stem}" ixe eqs catch e => do
          IO.println s!"  {family} {stem}: {(toString e).take 200}"
          pure false
        if r then ok := ok + 1
    IO.println s!"runShaped accepted {ok} of {n} closures"
  return 0

end IxCCTests.Shape

def main : IO UInt32 := IxCCTests.Shape.run
