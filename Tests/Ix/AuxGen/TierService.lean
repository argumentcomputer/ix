import LSpec
import Ix.Meta
import Ix.AuxGen.IxcScope
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.Kernel.TierIndDefs
import Tests.Ix.AuxGen.BelowIxc
import Batteries.Data.MLList.Basic

/-! # The Source service's tier and an unsafe block's oracle (`lake test -- auxgen-tier-service`)

AuxGen on IxC, M7 Q1 (T2), on the fixtures of `Tests.Ix.Kernel.TierIndDefs`:

1. **The service's tier.** The unsafe inductive `U` and the unsafe definitions
   `kdef` and `qIota` are installed by the tier (`tier unsafe`), the partial
   companion `spin._unsafe_rec` too (`tier partial`), the safe family `PF` is
   accepted, and none of the tier groups is accepted; the report counts them
   apart. A safe definition planted over `kdef` stays blocked behind it (the
   fence).
2. **`U`'s oracle** says it is an unsafe block and answers over the answer
   view, as Lean's kernel does: `qIota`'s value is `true` (ι on `U.rec`), and
   `kdef` reduces to `true` (δ on a tier definition).
3. **A generated definition** of `U`'s, admitted by the tier through σ,
   reduces through δ and ι on the oracle `admitBelow` returns.
4. **`withFamily`** installs `PF`'s former and constructor under fresh names
   with no recursor; the oracle over it infers `PF.t : PF true`. -/

namespace Tests.Ix.AuxGen.TierService

open LSpec
open _root_.Ix.AuxGen
open _root_.Ix.AuxGen.Source (Service Status)
open Tests.Ix.Kernel.SourceIngress (envOf)
open Tests.Ix.Kernel.SourceIngressStep (condense)

def defsModule : Lean.Name := `Tests.Ix.Kernel.TierIndDefs

def ixn (s : String) : Ix.Name := Ix.Name.fromLeanName (defsModule ++ s.toName)

def cnst (n : Ix.Name) : Ix.Expr := Ix.Expr.mkConst n #[]

def boolT : Ix.Expr := cnst (Ix.Name.fromLeanName ``Bool)

def boolTrue : Ix.Expr := cnst (Ix.Name.fromLeanName ``Bool.true)

def valueOf (env : Ix.Environment) (n : Ix.Name) : Except String Ix.Expr :=
  match env.get? n with
  | some (.defnInfo v) => .ok v.value
  | _ => .error s!"{n.pretty}: not a definition"

/-- The weak head normal form of `e` in a fresh scope of `o`, compared with
`want`. -/
def whnfIs (o : AuxOracle) (e want : Ix.Expr) : Except String Bool := do
  let (w, _) ← (← o.newScope #[] #[]).whnf e
  pure (Ix.Compile.ExactKey.exprEq w want)

def evaluate : IO (Array String × Array String) := do
  let leanEnv ← getCompileEnv #[defsModule]
  let env ← envOf leanEnv
    (#["U", "kdef", "qIota", "PF", "spin._unsafe_rec"].map (defsModule ++ ·.toName))
  -- the fence: a safe definition over the tier constant `kdef`
  let fenced := ixn "fenced"
  let env := { env with consts := env.consts.insert fenced (.defnInfo
    { cnst := { name := fenced, levelParams := #[], type := boolT }, value := cnst (ixn "kdef"),
      hints := .abbrev, safety := .safe, all := #[fenced] }) }
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let svc := (Service.create pre env (condense env)
    (evidence := some (Ix.RoleEvidence.bundleEvidence ()))).ensureNames
      (#["U", "kdef", "qIota", "PF", "spin._unsafe_rec", "fenced"].map ixn)
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  -- 1. the statuses
  let expect : List (String × (Status → Bool)) := [
    ("U", (· == .tier "unsafe")), ("kdef", (· == .tier "unsafe")), ("qIota", (· == .tier "unsafe")),
    ("spin._unsafe_rec", (· == .tier "partial")), ("PF", (· == .accepted)),
    ("fenced", fun | .blocked _ => true | _ => false)]
  for (n, ok) in expect do
    match svc.statusOf? (ixn n) with
    | some st =>
      let shown := match st with
        | .tier w => s!"tier {w}" | .accepted => "accepted" | .blocked _ => "blocked"
        | .refused why => s!"refused: {why}" | .pending => "pending"
      lines := lines.push s!"{n}: {shown}"
      unless ok st do errors := errors.push s!"{n}: {shown}"
    | none => errors := errors.push s!"{n}: not met"
  if (svc.firstUnaccepted? #[ixn "U"]).isNone then errors := errors.push "U: counted accepted"
  let report := ({ service := .ok svc } : Source.Run).report
  lines := lines.push s!"report: {report.summary}"
  unless report.groupsTier ≥ 4 do errors := errors.push s!"report: {report.groupsTier} tier groups"
  -- 2. U's oracle, over the answer view
  let oracle (members : Array String) : AuxOracle :=
    Ixc.oracleOf .failClosed false { members := members.map ixn, lookup := env.get? } none 4
      fun _ => .ok svc
  let o := oracle #["U"]
  unless o.blockStatus () == some "an unsafe block (tier-installed)" do
    errors := errors.push s!"U: block status {o.blockStatus ()}"
  match valueOf env (ixn "qIota") with
  | .error e => errors := errors.push e
  | .ok qIota =>
    match (do let (q, _) ← (← o.newScope #[] #[]).isDefEq qIota boolTrue; pure q) with
    | .ok true => lines := lines.push "qIota ≡ true: ι over the answer view"
    | r => errors := errors.push s!"qIota ≡ true: {r.toOption}"
    match whnfIs o (cnst (ixn "kdef")) boolTrue with
    | .ok true => lines := lines.push "kdef ⇝ true: δ over the answer view"
    | r => errors := errors.push s!"kdef ⇝ true: {r.toOption}"
    -- 3. a generated definition of U's, by the tier
    -- name, level parameters, type, value, unsafe
    let gen : BelowDef := ⟨ixn "U.gen", #[], boolT, qIota, true⟩
    match o.admitBelow #[gen] with
    | .ok (o', 1, 0) =>
      match whnfIs o' (cnst (ixn "U.gen")) boolTrue with
      | .ok true => lines := lines.push "U.gen ⇝ true: admitted by the tier, δ then ι"
      | r => errors := errors.push s!"U.gen ⇝ true: {r.toOption}"
    | .ok (_, ok, bad) => errors := errors.push s!"U.gen: {ok} admitted, {bad} refused"
    | .error e => errors := errors.push s!"U.gen: {e}"
  -- 4. withFamily: PF's former and constructor, no recursor
  match env.get? (ixn "PF"), env.get? (ixn "PF.t") with
  | some (.inductInfo v), some (.ctorInfo c) =>
    match (do
        let of ← (oracle #["PF"]).withFamily #[(v, #[c])]
        let (t, _) ← (← of.newScope #[] #[]).infer (cnst (ixn "PF.t"))
        pure t) with
    | .ok t =>
      if Ix.Compile.ExactKey.exprEq t (Ix.Expr.mkApp (cnst (ixn "PF")) boolTrue) then
        lines := lines.push "withFamily: PF.t : PF true, over the fresh family"
      else errors := errors.push "withFamily: PF.t's type is not PF true"
    | .error e => errors := errors.push s!"withFamily: {e}"
  | _, _ => errors := errors.push "PF: missing"
  return (lines, errors)

def tierService : TestSeq :=
  .individualIO "the Source service's tier and an unsafe block's oracle (M7 Q1)" none (do
    let (lines, errors) ← evaluate
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, lines.size, 0, msg)) .done

/-- The real polymorphic unsafe block that exposed the universe-order bug:
its service status stays outside acceptance, while all AuxGen questions agree
with the old kernel. This exercises the actual nested recursor and .below. -/
def mlListService : TestSeq :=
  .individualIO "MLList: tier install and every shadow answer" none (do
    let leanEnv ← getCompileEnv #[`Batteries.Data.MLList.Basic]
    let n := Lean.Name.str (Lean.Name.str (Lean.Name.num `_private.Batteries.Data.MLList.Basic 0)
      "MLList") "MLListImpl"
    let key := Ix.Name.fromLeanName n
    let env ← envOf leanEnv #[n]
    let blocks := condense env
    let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
    let svc := (Service.create pre env blocks
      (evidence := some (Ix.RoleEvidence.bundleEvidence ()))).ensureNames #[key]
    let some (.tier "unsafe") := svc.statusOf? key
      | return (false, 0, 0, some "MLList was not installed by the unsafe tier")
    if (svc.firstUnaccepted? #[key]).isNone then
      return (false, 0, 0, some "MLList was incorrectly counted accepted")
    let (_, _, cenv) ← IO.ofExcept (← IO.lazyPure fun _ =>
      Ix.CompileM.compileEnvFold env blocks (width := 4))
    unless cenv.ungrounded.isEmpty do
      return (false, 0, 0, some s!"MLList closure: {cenv.ungrounded.size} failed blocks")
    let some (lo, members) := (Tests.Ix.AuxGen.FlatBlockSource.inductiveBlocks env blocks).find?
      (fun (_, members) => members.any (Ix.Compile.ExactKey.nameEq · key))
      | return (false, 0, 0, some "MLList block missing")
    let oracle := Ixc.oracleOf .shadow false
      { members, recursors := true, lookup := env.get? } none 4 (fun _ => .ok svc)
    let some (st, _) ← IO.ofExcept (← IO.lazyPure fun _ =>
      Tests.Ix.AuxGen.BelowIxc.tailStats cenv lo members oracle)
      | return (false, 0, 0, some "MLList tail missing")
    let counts := Tests.Ix.AuxGen.BelowIxc.statsLine st
    IO.println s!"MLList: tier unsafe, not accepted; {counts}"
    let ok := st.queries > 0 && st.answered == st.queries && st.equal == st.queries &&
      st.recWhnf > 0 && st.recEqual == st.recWhnf && st.elim > 0 && st.elimEqual == st.elim &&
      st.belowAdmitted > 0 && [st.differ, st.refused, st.scopesRefused, st.flatRefused,
        st.decisionsDiffer, st.recDiffer, st.recDecisionDiffer, st.recSkipDiffer,
        st.elimDiffer, st.leanRecDiffer, st.belowRefused, st.recRefused, st.elimRefused,
        st.familyRefused].all (· == 0)
    return (ok, st.queries + st.recWhnf + st.elim, 0,
      if ok then none else some (counts ++ "\n" ++ "\n".intercalate st.samples.toList))) .done

def suite : List TestSeq := [tierService, mlListService]

end Tests.Ix.AuxGen.TierService
