import IxCCTests.Recheck.ErasedArity
import IxCCTests.Recheck.P1Twin.Pass

/-! The P1 twin's hooks into the erased-position test parts (`Erased.Hooks`) and its planted
programs: each plant is a program the front end's relevance checks decide, run through the twin and
the mutant pass where they accept it. The plants for the reproductions of the statements repaired at
P1's definitions landing assert the verdict that closes each one. -/

namespace IxCCTests.Recheck.P1Twin
open IxCC IxCC.Src IxCC.Src.Relevance

def kRun : Nat := 100000

initialize gAgg : IO.Ref (Option Agg) ← IO.mkRef none
initialize gCfg : IO.Ref PassCfg ← IO.mkRef {}
initialize gPass : IO.Ref Bool ← IO.mkRef true
/-- Violations (`MISMATCH`, `VIOLATION …`) on the runs of programs the checks accept, by key. -/
initialize gAccViol : IO.Ref (List (String × Nat)) ← IO.mkRef []

def theAgg : IO Agg := do
  match ← gAgg.get with
  | some a => pure a
  | none => do
    let a ← Agg.new
    gAgg.set (some a)
    pure a

/-- A twin context for a program the checks accept: with the mutant pass unless it is off. -/
def acceptedCx (label : String) (p : Program) (ann : Ann) (ch : Checked) : IO TCx := do
  if ← gPass.get then passCx (← theAgg) (← gCfg.get) label p ann ch else newCx p ann ch

/-- Add a run's violation keys (of a program the checks accept) to `gAccViol`. -/
def recordAccepted (x : TCx) : IO Unit := do
  for (k, n) in ← x.counts.get do
    if k.startsWith "VIOLATION" || k.startsWith "MISMATCH" then
      gAccViol.modify fun vs => vs ++ [(k, n)]

/-- A refused program: install it and run every root with the twin (no pass: no `Facts`). -/
def hookRefused (label : String) (Pt : Program) (ann : Ann) : IO Unit := do
  match Relevance.install Pt ann with
  | .error _ => IO.println s!"TWIN refused program {label}: install refuses"
  | .ok Pi =>
    let x ← newCx Pi ann (looseChecked ann)
    for (_, r) in Pi.roots do twinRun x kRun r []
    report s!"refused program: {label}" x

def hookAccepted (label : String) (art : Recheck.Artifact) (ann : Ann) (main : CId) : IO Unit := do
  let x ← acceptedCx label art.src ann art.checked
  twinRun x kRun main []
  recordAccepted x
  report s!"accepted program: {label}" x

def hooks : IxCCTests.Recheck.Erased.Hooks := { refused := hookRefused, accepted := hookAccepted }

end IxCCTests.Recheck.P1Twin


namespace IxCCTests.Recheck.P1Twin.Plants
open IxCCTests.Recheck.P1Twin
open IxCC IxCC.Src
open IxCCTests.Recheck.Hostile (mkCert)
open IxCCTests.Recheck.Erased (objMain srcMain installed keyProg fProg mapArg eraseParam withNode withCtor withConst)
open IxCCTests.Recheck.ErasedBlocks (setBody)
open IxCCTests.Src (Assert expect)

/-- Refused at relevance, every error naming `needle` (the check alone). -/
def refusedBy (v : Option (List String)) (needle : String) : Bool :=
  match v with
  | some ms => !ms.isEmpty && ms.all (·.contains needle)
  | none => false

/-- Refused at relevance, some error naming `needle`. -/
def refusedWith (v : Option (List String)) (needle : String) : Bool :=
  match v with
  | some ms => ms.any (·.contains needle)
  | none => false

/-- The relevance verdict on a planted program: `none` where `Src.Recheck.annotation` accepts it (it
is then run through the twin with the pass), the errors where it refuses it at relevance (the twin
then runs it without), `["install or table"]` otherwise. -/
def direct (label : String) (Pt : Program) (ann : Relevance.Ann) (main : CId) : IO (Option (List String)) := do
  match Src.Recheck.annotation Pt ann with
  | .ok (src, ch) =>
    IO.println s!"PLANT {label}: Src.Recheck.annotation ACCEPTS (tiers S, C, checkCanonical)"
    let x ← acceptedCx label src ann ch
    twinRun x kRun main []
    report s!"planted: {label}" x
    return none
  | .error (.relevance errs) =>
    let ms := errs.toList.map (·.render Pt)
    IO.println s!"PLANT {label}: annotation refuses: {ms.take 3}"
    hookRefused label Pt ann
    return some ms
  | .error _ =>
    IO.println s!"PLANT {label}: refused at install"
    return some ["install or table"]

/-- `direct` with the table built from the certificate `tc`, then `Recheck.run`'s verdict printed. -/
def verdicts (label : String) (cfg : Recheck.Config) (P : Program) (tc : Src.Table.TableCert)
    (ann : Relevance.Ann) (main : CId) : IO (Option (List String)) := do
  match Src.Table.ofCert cfg.table P tc with
  | .error m =>
    IO.println s!"PLANT {label}: the table refuses: {m}"
    return some ["install or table"]
  | .ok table =>
    let v ← direct label { P with table } ann main
    match mkCert cfg P tc ann with
    | .error e => IO.println s!"PLANT {label}: no certificate: {(e.render.take 120).toString}"
    | .ok cert =>
      match Recheck.run cfg P cert with
      | .error e => IO.println s!"PLANT {label}: Recheck.run refuses: {(e.render.take 160).toString}"
      | .ok art =>
        IO.println s!"PLANT {label}: Recheck.run ACCEPTS; object {repr (objMain art)}; SrcEval {resultShape (Src.run art.src kRun main [])}, readback {repr (srcMain art main)}"
    return v

/-- `ShapeOk.rules`: `Key.mk`'s field `b` written erased, `Key.rec`'s rule 0 naming `c₀` (another
inductive's constructor) as its constructor and returning field `b`. -/
def rulesSwap : IO Unit := do
  let (h, elimId, mkId, main, _, majorPos) ← keyProg "plant: rule constructor" false
  let Pi ← installed h
  let some (.defn dk ds dl mty mval) := Pi.decl? main | throw (IO.userError "main")
  let some (.ctor x1 x2 x3 x4 np nf mkTy) := Pi.decl? mkId | throw (IO.userError "mk")
  let some (.recr sf kk lv rnp nmot nmin ni ind rules rty) := Pi.decl? elimId | throw (IO.userError "rec")
  let some rule := rules[0]? | throw (IO.userError "rule")
  let some (major, _, _) := mval.spineL.2[majorPos]? | throw (IO.userError "major")
  let some ((Term.const c0 _), _, _) := major.spineL.2[0]? | throw (IO.userError "c0")
  let Pe := Pi.setDecl mkId (.ctor x1 x2 x3 x4 np nf (eraseParam 1 mkTy))
  let dropB := mapArg elimId majorPos fun (x, m, r) => (mapArg mkId 1 (fun (y, m', _) => (y, m', Src.Rel.prf)) x, m, r)
  let total := rnp + nmot + nmin + rule.fields
  for (what, rule') in [("honest rule, field b written erased", rule),
      ("rule 0 names c₀ and returns field b", { rule with ctor := c0, rhs := setBody (.var 1) total rule.rhs })] do
    let Pb := (Pe.setDecl elimId (.recr sf kk lv rnp nmot nmin ni ind (rules.set 0 rule') rty)).setDecl main
      (.defn dk ds dl mty (dropB mval))
    let _ ← verdicts s!"ShapeOk.rules: {what}" h.cfg Pb h.cert.table (withCtor h.cert.relevance Pb mkId) main

/-- `SortAgree` (b): `main : E := Sort 0` (ill typed; no relevance check refuses it). -/
def sortMain : IO Unit := do
  let (h, _, _, main) ← fProg "plant: sort" {}
  let some (.defn dk ds dl mty _) := h.inp.program.decl? main | throw (IO.userError "main")
  let P := h.inp.program.setDecl main (.defn dk ds dl mty (.sort .zero))
  let _ ← verdicts "SortAgree (b): main : E := Sort 0" h.cfg P h.cert.table (withNode h.cert.relevance (.value main) []) main

/-- `EnvOk`'s shielding: a marker under a relevant binder, passed to a head that reads it (not
shielded) or ignores it (shielded). -/
def env : IO Unit := do
  let p : Program := {}
  let irr : Slot := .val (.irr none [] [])
  let t : Term := .app (.var 1) (.var 0) .strict .rel
  for (what, b) in [("head reads it", ({} : Binder)), ("head ignores it (shielded)", { rel := .type })] do
    let body : Term := if b.rel == .rel then .var 0 else .natLit 7
    let head : Slot := .val (.clo b (.sort .zero) body [] [])
    IO.println s!"PLANT EnvOk, {what}: eval = {resultShape (eval p 100 [] [irr, head] t)}"


/-- The tags of an installed term, in installation order. -/
def tagsOf (t : Term) : List Relevance.Tag := (t.tagOrderRev []).reverse

/-- `t`'s spine head replaced by constant `c'` (its universe arguments kept). -/
def setHead (c' : CId) (t : Term) : Term :=
  match t.spine with
  | (.const _ us, args) => Term.mkApps (.const c' us) args
  | _ => t

/-- Argument `pos` of `t`'s spine tagged `r`. -/
def tagArg (pos : Nat) (r : Rel) (t : Term) : Term :=
  let (h, args) := t.spine
  Term.mkApps h (args.zipIdx.map fun ((x, m, r'), i) => if i == pos then (x, m, r) else (x, m, r'))

/-- `ShapeOk.ctorUnique`: a second constructor `mk'` of `Key` at index 0, whose field `b` is written
erased (dropped), builds `main`'s major. F2 selects rule 0, `mk`'s, which forwards field `b` to the
minor `useG`, which returns it. No relevance check sees a mismatch (rule 0's constructor `mk`
writes nothing erased); erasure's `ProgWF.ctorIn` refuses `mk'` (not listed by `Key` at 0). -/
def ctorUniq : IO Unit := do
  let (h, elimId, mkId, main, _, majorPos) ← keyProg "plant: ctorUnique" false
  let Pi ← installed h
  let some (.defn dk ds dl mty mval) := Pi.decl? main | throw (IO.userError "main")
  let some (.ctor x1 x2 ind cidx np nf mkTy) := Pi.decl? mkId | throw (IO.userError "mk")
  let c' := Pi.size
  let ta := IxCCTests.Src.Builder.fakeAddr (Pi.size + 4000000)
  let Pc := Pi.push { ref := .member ta 0, addr := ta, decl := .ctor x1 x2 ind cidx np nf (eraseParam (np + 1) mkTy) }
  let (hd, args) := mval.spine
  let args' := args.zipIdx.map fun ((x, m, r), i) =>
    if i == majorPos then (setHead c' (tagArg (np + 1) Rel.prf x), m, r) else (x, m, r)
  let v' := Term.mkApps hd args'
  let Pm := Pc.setDecl main (.defn dk ds dl mty v')
  let ann := withNode (withCtor h.cert.relevance Pm c') (.value main) (tagsOf v')
  let _ ← verdicts "ShapeOk.ctorUnique: a second constructor at Key's index 0 writing field b erased" h.cfg Pm
    h.cert.table ann main

/-- `Live.con`'s read fields: `main := (mk c₀ c₁ c₂).2` (`c₁`), honest, and with the argument of the
kept field `b` tagged irrelevant (a marker in a kept field, then projected): C2 refuses it. -/
def liveCon : IO Unit := do
  let (h, elimId, mkId, main, _, majorPos) ← keyProg "plant: Live.con" false
  let Pi ← installed h
  let some (.defn dk ds dl mty mval) := Pi.decl? main | throw (IO.userError "main")
  let some (.ctor _ _ ind _ np _ _) := Pi.decl? mkId | throw (IO.userError "mk")
  let some (major, _, _) := mval.spine.2[majorPos]? | throw (IO.userError "major")
  for (what, mj) in [("honest", major), ("field b's argument a marker", tagArg (np + 1) Rel.prf major)] do
    let v' := Term.proj ind 1 mj
    let Pm := Pi.setDecl main (.defn dk ds dl mty v')
    let _ ← verdicts s!"Live.con: (mk c₀ c₁ c₂).2, {what}" h.cfg Pm h.cert.table
      (withNode h.cert.relevance (.value main) (tagsOf v')) main

/-- `ShapeOk.ctorUnique`, the field count: `Key.mk`'s field `b` written erased (below the kernel),
and a second constructor `mk'` at `Key`'s index 0 with only the fields `a`, `0 b`. `main :=
Key.rec (λ _. E) (λ a (0 b) c. a) (mk' c₀ □)`: F2 runs rule 0, `mk`'s, on two field slots, so the
rule's body under four λs is `λ c. minor a b c`, a closure holding the marker at `b`'s relevant rule
λ: not `Live` by provenance, though nothing reads the marker, and `SortAgree` holds (`b` is written
erased in rule 0's constructor). Erasure's `ProgWF.ctorIn` refuses `mk'`. -/
def ctorUniqCount : IO Unit := do
  let (h, _, mkId, main, minorPos, majorPos) ← keyProg "plant: ctorUnique, count" false
  let Pi ← installed h
  let some (.defn dk ds dl mty mval) := Pi.decl? main | throw (IO.userError "main")
  let some (.ctor x1 x2 ind cidx np nf mkTy) := Pi.decl? mkId | throw (IO.userError "mk")
  let mkTyE := eraseParam (np + 1) mkTy
  let Pe := Pi.setDecl mkId (.ctor x1 x2 ind cidx np nf mkTyE)
  let (bs, concl) := mkTyE.pis
  let tyC : Term := (bs.take (np + 2)).foldr (fun (b, d) acc => .pi b {} d acc) concl
  let c' := Pe.size
  let ta := IxCCTests.Src.Builder.fakeAddr (Pe.size + 4100000)
  let Pc := Pe.push { ref := .member ta 0, addr := ta, decl := .ctor x1 x2 ind 0 np 2 tyC }
  let some (_, eTy) := bs[np]? | throw (IO.userError "E")
  let erasedB : Binder := { contract := .erased, rel := Rel.prf }
  let minor : Term := .lam {} eTy (.lam erasedB eTy (.lam {} eTy (.var 2)))
  let some (major, _, _) := mval.spine.2[majorPos]? | throw (IO.userError "major")
  let (mkHead, margs) := major.spine
  let some a0 := margs[np]? | throw (IO.userError "a")
  let some a1 := margs[np + 1]? | throw (IO.userError "b")
  let head' : Term := match mkHead with
    | .const _ us => .const c' us
    | t => t
  let major' := Term.mkApps head' ((margs.take np) ++ [a0, (a1.1, a1.2.1, Rel.prf)])
  let (hd, args) := mval.spine
  let args' := args.zipIdx.map fun ((x, m, r), i) =>
    if i == majorPos then (major', m, r) else if i == minorPos then (minor, m, r) else (x, m, r)
  let v' := Term.mkApps hd args'
  let Pm := Pc.setDecl main (.defn dk ds dl mty v')
  let ann := withNode (withCtor (withCtor h.cert.relevance Pm mkId) Pm c') (.value main) (tagsOf v')
  let _ ← verdicts "ShapeOk.ctorUnique: a second constructor at Key's index 0 with one field fewer" h.cfg Pm
    h.cert.table ann main

def resShow : IxCC.Sem.Result Value → String
  | .ok v => valShort 4 v
  | r => resultShape r

/-- Keep `n` leading λs of `t`, with `body` under them. -/
def keepLams : Nat → Term → Term → Term
  | 0, _, body => body
  | n + 1, .lam b d t, body => .lam b d (keepLams n t body)
  | _ + 1, _, body => body

/-- (iii) A reached recursor with a table entry (`Key.rec ↦ useG3`, a `csimp` redirect), whose rule 0
(no check reads it: `runtimeKeys` omits the rules) has the body `Sort 0` under its λs. -/
def recTableEntry (a : Assert) : IO Unit := do
  let (h, elimId, _, main, minorPos, _) ← keyProg "plant: recursor with a table entry" false
  let Pi ← installed h
  let some (.defn _ _ _ _ mval) := Pi.decl? main | throw (IO.userError "main")
  let some ((Term.const useG _), _, _) := mval.spineL.2[minorPos]? | throw (IO.userError "useG")
  let some (.recr sf kk lv np nmot nmin ni ind rules rty) := Pi.decl? elimId | throw (IO.userError "rec")
  let some rule0 := rules[0]? | throw (IO.userError "rule")
  let rhs' := keepLams (np + nmot + nmin + rule0.fields) rule0.rhs (.sort .zero)
  let P1 := Pi.setDecl elimId (.recr sf kk lv np nmot nmin ni ind (rules.set 0 { rule0 with rhs := rhs' }) rty)
  match Src.Table.ofCert h.cfg.table P1 h.cert.table with
  | .error m => IO.println s!"PLANT (iii): the table refuses: {m}"
  | .ok table =>
    let ann := withNode h.cert.relevance (.rule elimId 0) (tagsOf rhs')
    let tbl := { table with resolve := table.resolve.insert elimId (.csimp useG [] elimId) }
    let v ← direct "(iii) Key.rec with a csimp entry, rule 0's body Sort 0" { P1 with table := tbl } ann main
    let c ← direct "(iii) control: Key.rec with rule 0's body Sort 0, no table entry" { P1 with table } ann main
    expect a (v.isNone && refusedWith c "[relevance C7]") "plant (iii): accepted with the csimp entry, refused by C7 without"

/-- (iv) and (v) on `Quot.lift E (Eq E) E (λ x. x) h (Quot.mk E (Eq E) c₁)`: (iv) a second quot
constructor declaration writing its element erased, unreached, with its canonical record; (v)
`Quot.lift` also a root, so reached at the empty profile, where its function is a proof. -/
def quotPlants (a : Assert) : IO Unit := do
  let q ← IxCCTests.Recheck.ErasedArity.quotProg
  let one : IxCC.Ixon.Univ := .succ .zero
  let mkV := Term.mkApps (.const q.mkId [one]) [(q.eT, .strict, .type), (q.eqT, .strict, .type), (.const q.c1 [], .strict, .rel)]
  let idL : Term := .lam {} q.eT (.var 0)
  let v := Term.mkApps (.const q.liftId [one, one]) [(q.eT, .strict, .type), (q.eqT, .strict, .type),
    (q.eT, .strict, .type), (idL, .strict, .rel), (.sort .zero, .strict, Rel.prf), (mkV, .strict, .rel)]
  let (Q, ann) := IxCCTests.Recheck.ErasedArity.quotWith q q.Pi v
  let v0 ← verdicts "Quot.lift (λ x. x) h (Quot.mk c₁), honest" q.h.cfg Q q.h.cert.table ann q.mainId
  let some (.quot .ctor l ty) := Q.decl? q.mkId | throw (IO.userError "Quot.mk")
  let c'' := Q.size
  let ta := IxCCTests.Src.Builder.fakeAddr (Q.size + 4200000)
  let Q4 := Q.push { ref := .member ta 0, addr := ta, decl := .quot .ctor l (eraseParam 2 ty) }
  let v4 ← verdicts "(iv) a second Quot.mk declaration writing its element erased (unreached, with its record)"
    q.h.cfg Q4 q.h.cert.table (withConst ann Q4 c'') q.mainId
  let Q5 := { Q with roots := Q.roots ++ [(Q.addr q.liftId, q.liftId)] }
  let v5 ← verdicts "(v) Quot.lift also a root (reached at the empty profile)" q.h.cfg Q5 q.h.cert.table ann q.mainId
  expect a (v0.isNone && v4.isNone) "plants (iv): the honest program or the second Quot.mk refused"
  expect a (refusedBy v5 "argument 3 is forced and applied") s!"plant (v), Quot.lift a root: not refused by appliedAt alone: {v5}"

/-- (v) for a `case` key: `Key.casesOn` also a root, reached at the empty profile (its minors proofs). -/
def caseRoot (a : Assert) : IO Unit := do
  let (h, elimId, _, main, _, _) ← keyProg "plant: Key.casesOn a root" true
  let Pi ← installed h
  let P := { Pi with roots := Pi.roots ++ [(Pi.addr elimId, elimId)] }
  let v ← verdicts "(v) Key.casesOn also a root (reached at the empty profile)" h.cfg P h.cert.table h.cert.relevance main
  expect a (refusedWith v "[relevance C6]") s!"plant (v), Key.casesOn a root: not refused by C6: {v}"


/-- (v) for a `case` key through a `csimp` target: `main := E.casesOn.{1} (λ _. E) c₁ c₀ c₂ c₁` (Erased's
`casesEnv`, field-less constructors), the root `r₁ := c₁` given a `csimp` entry `r₁ ↦ E.casesOn.{0}`, so the
key is reached at the profile where its minors are proofs; with and without a `csimp` entry on `E.rec`
(`E.rec ↦ r₀`), which keeps the checks from walking `E.rec`'s rules at that profile. -/
def caseCsimp (a : Assert) : IO Unit := do
  let (e, co, roots) ← IxCCTests.Recheck.Erased.casesEnv .many
  let h ← IxCCTests.Recheck.Erased.ingest "plant: case key a csimp target" e roots
  let P := h.inp.program
  let some (_, main) := P.roots.head? | throw (IO.userError "no root")
  let coId ← IxCCTests.Recheck.Erased.lookup P co "casesOn"
  let some (_, r0) := P.roots[1]? | throw (IO.userError "no r₀")
  let some (_, r1) := P.roots[2]? | throw (IO.userError "no r₁")
  let Pi ← installed h
  match Src.Table.ofCert h.cfg.table Pi h.cert.table with
  | .error m => IO.println s!"PLANT (v) case csimp: the table refuses: {m}"
  | .ok table =>
    let some (.case recId) := table.resolveOf coId | throw (IO.userError "no case entry")
    let t1 := { table with resolve := table.resolve.insert r1 (.csimp coId [.zero] r1) }
    let va ← direct "(v) case key: r₁ ↦ E.casesOn.{0} (csimp)" { Pi with table := t1 } h.cert.relevance main
    let t2 := { t1 with resolve := t1.resolve.insert recId (.csimp r0 [] recId) }
    let vb ← direct "(v) case key: r₁ ↦ E.casesOn.{0} and E.rec ↦ r₀ (csimp)" { Pi with table := t2 } h.cert.relevance main
    -- the recursor's table entry alone: the key reached at the profile of `main` only (its minors relevant
    -- there, so `appliedAt` passes), its recursor's rules read by no check
    let t3 := { table with resolve := table.resolve.insert recId (.csimp r0 [] recId) }
    let vc ← direct "(v) case key: E.rec ↦ r₀ (csimp) alone, the key at main's profile" { Pi with table := t3 } h.cert.relevance main
    expect a (refusedWith va "[relevance C6]" && refusedBy vb "argument 2 is forced and applied" && vc.isNone)
      s!"plant (v), case key: C6 first, then appliedAt alone, the variant accepted: {va} {vb} {vc}"
    -- plant (b)'s run: SrcEval on `main` and on the root `r₁`; the certificate path (the table's checks
    -- of the two csimp entries); erasure on the program as the annotation leaves it
    let Pb : Program := { Pi with table := t2 }
    let verdictB : String := match Src.Recheck.annotation Pb h.cert.relevance with
      | .ok _ => "accepted"
      | .error (.relevance errs) => (((errs.toList.map (·.render Pb)).headD "").take 220).toString
      | .error _ => "refused at install"
    IO.println s!"PLANT (v) case key (b): at Src.Recheck.annotation: {verdictB}"
    match IxCCTests.Src.annotationNoCanonical Pb h.cert.relevance with
    | .ok (src, ch) =>
      IO.println s!"PLANT (v) case key (b): SrcEval main = {resShow (Src.run src kRun main [])}; root r₁ = {resShow (Src.run src kRun r1 [])}"
      match Lam.erase src ch with
      | .ok _ => IO.println "PLANT (v) case key (b): Lam.erase accepts the program"
      | .error e => IO.println s!"PLANT (v) case key (b): Lam.erase refuses: {(e.render.take 300).toString}"
    | .error _ => IO.println "PLANT (v) case key (b): annotation refuses"
    let tc : Src.Table.TableCert := { h.cert.table with
      resolve := (r1, .csimp coId r1) :: (recId, .csimp r0 recId) :: h.cert.table.resolve }
    match mkCert h.cfg Pi tc h.cert.relevance with
    | .error e => IO.println s!"PLANT (v) case key (b): no certificate: {(e.render.take 300).toString}"
    | .ok cert =>
      match Recheck.run h.cfg Pi cert with
      | .error e => IO.println s!"PLANT (v) case key (b): Recheck.run refuses: {(e.render.take 300).toString}"
      | .ok art => IO.println s!"PLANT (v) case key (b): Recheck.run ACCEPTS; object {repr (objMain art)}"


/-- Route 12 (`tests-recheck`'s `Shape.subRecord`): Form B, `T : Prop` with large elimination over two
fields written erased, `mk` unreached and without a constructor record; refused by `subRecords` alone. -/
def subRecord (a : Assert) : IO Unit := do
  let (h, rId, tId, mkId, main, _, _) ← IxCCTests.Recheck.Shape.subProg
  let (Pi, ann) ← IxCCTests.Recheck.Shape.formB h rId tId mkId main
  let v ← verdicts "route 12, Form B (T : Prop with large elimination, mk without a record)" h.cfg Pi
    h.cert.table ann main
  expect a (refusedBy v "a subsingleton eliminator's rule 0 is for a constructor without a constructor record")
    s!"plant route 12: not refused by subRecords alone: {v}"

def run (a : Assert) : IO Unit := do
  for (n, act) in [("rules", rulesSwap), ("sort", sortMain), ("env", env), ("ctorUnique", ctorUniq),
      ("ctorUniqueCount", ctorUniqCount), ("liveCon", liveCon), ("recTableEntry", recTableEntry a),
      ("quot", quotPlants a), ("caseRoot", caseRoot a), ("caseCsimp", caseCsimp a),
      ("subRecord", subRecord a)] do
    try act catch e => do
      IO.println s!"PLANT {n}: ERROR {e}"
      expect a false s!"plant {n}: {e}"

end IxCCTests.Recheck.P1Twin.Plants
