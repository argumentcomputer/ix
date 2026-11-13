import IxCCTests.Recheck.ErasedBlocks

/-! # A type at a data position (C7), and the structure the kernel ensures, checked by IxCC

SrcEval evaluates a sort or a Π to the irrelevance marker (rule E2) and erasure turns one into □.
A program with a type at a relevant position is ill typed, so the kernel refuses it; but
`Recheck.sound` does not assume the kernel's acceptance, and before C7 no relevance check refused
one: `def main : E := Sort 0`, below the kernel, passed every check and `Recheck.run`, and its
object returned constructor 0 while SrcEval returned the marker (engineer RN's finding,
`plans/resource-cert/P1.md`). C7 (`Check.sortRule`, in the walk and at a spine's head) refuses it.

`checkCanonical` also decides six facts about the program's structure that relevance preservation
reads and that only the kernel, ingress or erasure ensured (erasure only where it erased: `ruleAlt`,
`erase-univs`): no constant or table entry at or above the program's size; rule `j` of a reached
eliminator's recursor is for constructor `j` (`rulesShape?`); universe-argument counts at the
positions SrcEval may evaluate (`univsOk`); a record for every reached constructor; F3's field
sources as many as the rule's constructor has fields (`subsingletonSrcs?`); and, where a word entry
is reached, the pinned `Fin.mk`'s proof field dropped at the empty profile.

Each part plants one violation in an honest program below the kernel and asserts that the front
end refuses it, by name, with no error from any other check (`refusedOnly`), and that `Recheck.run`
refuses it at the relevance stage on the honest certificate given the planted annotation; the
honest program compiles and its object and SrcEval return the value it means. Where a planted
program cannot reach the check through `Recheck.run` because the table's construction rules it
out, the part says so and plants it at `Src.Recheck.annotation`, the step `Recheck.run` calls. -/

namespace IxCCTests.Recheck.Shape

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.Src (Assert expect)
open IxCCTests.Recheck.Hostile (defn driver ofErr)
open IxCCTests.IxonV3.Builder (store)
open IxCCTests.Support.Bound (loadBase addEnum)
open IxCCTests.Recheck.Erased (E Honest objMain srcMain lookup ingest ctorRoots withNode withConst
  withCtor fProg)

abbrev X := IxCC.Ixon.V3.Expr

/-! ## The harness -/

/-- The front end's verdict on a program and annotation (the table from `tc`). -/
def verdict (cfg : Recheck.Config) (P : Src.Program) (tc : Src.Table.TableCert)
    (ann : Src.Relevance.Ann) : IO (Except Src.Recheck.Error (Src.Program × Src.Relevance.Checked)) := do
  let table ← match Src.Table.ofCert cfg.table P tc with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"the table refused it: {m}")
  return Src.Recheck.annotation { P with table } ann

/-- `Src.Recheck.annotation` refuses `Pt` with `ann` at the relevance checks, and every error names
every needle: no other check fires. -/
def annotationOnly (a : Assert) (label : String) (Pt : Src.Program) (ann : Src.Relevance.Ann)
    (needles : List String) : IO String :=
  match Src.Recheck.annotation Pt ann with
  | .ok _ => do expect a false s!"{label}: accepted by Src.Recheck.annotation"; return ""
  | .error (.relevance errs) => do
    let ms := errs.toList.map (·.render Pt)
    expect a (!ms.isEmpty && ms.all fun m => needles.all (m.contains ·))
      s!"{label}: refused, but not by this check alone: {ms}"
    return ms.headD ""
  | .error _ => do expect a false s!"{label}: refused at install or table"; return ""

/-- Refused by name with no other error (`annotationOnly`), and by `Recheck.run` at the relevance
stage on the honest certificate `cert` given the planted table certificate and annotation. -/
def refusedOnly (a : Assert) (label : String) (cfg : Recheck.Config) (cert : Recheck.Cert)
    (P : Src.Program) (tc : Src.Table.TableCert) (ann : Src.Relevance.Ann) (needles : List String) :
    IO String := do
  let table ← match Src.Table.ofCert cfg.table P tc with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"{label}: the table refused it: {m}")
  let shown ← annotationOnly a label { P with table } ann needles
  match Recheck.run cfg P { cert with table := tc, relevance := ann } with
  | .ok _ => expect a false s!"{label}: Recheck.run accepted it"
  | .error e =>
    expect a (e.stage == .relevance && needles.all (e.message.contains ·))
      s!"{label}: Recheck.run refused it otherwise: {e.render}"
  return s!"{label}: {shown}"

/-- What erasure did with the planted program before the check: tiers S and C accept it
(`annotationNoCanonical`), and erasure declines it with `code`. -/
def erasureDeclined (a : Assert) (label : String) (cfg : Recheck.Config) (P : Src.Program)
    (tc : Src.Table.TableCert) (ann : Src.Relevance.Ann) (code : String) : IO Unit := do
  let table ← match Src.Table.ofCert cfg.table P tc with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"{label}: the table refused it: {m}")
  match IxCCTests.Src.annotationNoCanonical { P with table } ann with
  | .ok (src, ch) =>
    match Lam.erase src ch with
    | .ok _ => expect a false s!"{label}: erasure accepted it"
    | .error e => expect a (e.code == code) s!"{label}: erasure declined it otherwise: {e.render}"
  | .error _ => expect a false s!"{label}: tiers S and C refused it"

/-- The value args `xs` of root `i` in the object and in SrcEval (read back). -/
def runBoth (art : Recheck.Artifact) (i : Nat) (main : Src.CId) (xs : List Nat) :
    Option Sem.Obs × Option Sem.Obs :=
  let obj := match (art.linked driver).run (i, xs) 1000000 with
    | .ok o => o
    | _ => none
  let src := match Src.run art.src 1000000 main (xs.map .lit) with
    | .ok v => Src.readback art.src art.checked.keeps v
    | _ => none
  (obj, src)

/-- The arguments of `main`'s value spine, and its head. -/
def mainSpine (P : Src.Program) (main : Src.CId) :
    IO (Src.Decl × Src.Term × List Src.Term.Arg) := do
  let some d := P.decl? main | throw (IO.userError "main")
  let .defn _ _ _ _ v := d | throw (IO.userError "main is no definition")
  let (hd, args) := v.spine
  return (d, hd, args)

/-- `main`'s declaration with value `v`. -/
def withValue (P : Src.Program) (main : Src.CId) (v : Src.Term) : Src.Program :=
  match P.decl? main with
  | some (.defn k s l ty _) => P.setDecl main (.defn k s l ty v)
  | _ => P

/-! ## C7: a sort or a Π at a relevant position -/

/-- `fProg`'s `main := f c₁ c₂` (`c₂`) with its value made a sort, a Π, and a spine headed by a
sort. -/
def sorts (a : Assert) : IO (Array String) := do
  let c₂ : Sem.Obs := .ctor 2 []
  let (h, _, _, main) ← fProg "C7" {}
  expect a (objMain h.art == some c₂ && srcMain h.art main == some c₂) "C7: the honest program is not c₂"
  let P := h.inp.program
  let (d, _, args) ← mainSpine P main
  let some (c₁, _, _) := args[0]? | throw (IO.userError "c₁")
  let ns := [s!"in the value of {P.short main}", "[relevance C7]", "a type (a sort or Π)"]
  let mut out := #[]
  let cases : List (String × Src.Term × List Src.Relevance.Tag) :=
    [("main : E := Sort 0", .sort .zero, []),
     ("main : E := E → E", Src.Term.pi {} {} d.type d.type, []),
     ("main : E := (Sort 0) c₁, a sort at a spine's head",
       Src.Term.app (.sort .zero) c₁ .strict .rel, [Src.Relevance.Tag.arg .rel])]
  for (what, v, tags) in cases do
    out := out.push (← refusedOnly a s!"C7, {what}" h.cfg h.cert (withValue P main v) h.cert.table
      (withNode h.cert.relevance (.value main) tags) ns)
  return out.push "C7: the honest main compiles to c₂ (object and SrcEval)"

/-! ## `rules`: rule `j` of a reached eliminator's recursor is for constructor `j` -/

/-- `E` (`c₀ c₁ c₂`) and `main := E.rec (λ _. E) c₂ c₀ c₁ c₀` (`c₂`). -/
def recProg (label : String) : IO (Honest × Src.CId × Src.CId) := do
  let (e, en) := addEnum (← loadBase) 3
  let motive : X := .lam .many (.ref 0 #[]) (.ref 0 #[])
  let body : X :=
    .app (.app (.app (.app (.app (.ref 1 #[0]) motive) (.ref 4 #[])) (.ref 2 #[])) (.ref 3 #[]))
      (.ref 2 #[])
  let (e, main) := store e ⟨defn E body, #[],
    #[en.ind, en.recursor, en.ctors[0]!, en.ctors[1]!, en.ctors[2]!], #[.succ .zero]⟩
  let (e, rs) := ctorRoots e en.ind en.ctors
  let h ← ingest label e ([("main", main)] ++ rs)
  let P := h.inp.program
  return (h, ← lookup P en.recursor "E.rec", ← lookup P main "main")

def rules (a : Assert) : IO (Array String) := do
  let c₂ : Sem.Obs := .ctor 2 []
  let (h, recId, main) ← recProg "rules"
  expect a (objMain h.art == some c₂ && srcMain h.art main == some c₂)
    "rules: the honest program is not c₂"
  let P := h.inp.program
  let some (.recr sf k lv np nmot nmin ni ind rs ty) := P.decl? recId | throw (IO.userError "E.rec")
  let [r0, r1, r2] := rs | throw (IO.userError "E.rec's rules")
  -- rules 0 and 1 swapped: on the major `c₀` SrcEval runs rule 0, now `c₁`'s, which returns minor 1
  let Ps := P.setDecl recId (.recr sf k lv np nmot nmin ni ind [r1, r0, r2] ty)
  let ns := [s!"({P.short recId})", "rule 0 of the recursor is not for constructor 0"]
  erasureDeclined a "rules, rules 0 and 1 of E.rec swapped" h.cfg Ps h.cert.table h.cert.relevance
    "erase-recursor"
  let shown ← refusedOnly a "rules, rules 0 and 1 of E.rec swapped" h.cfg h.cert Ps h.cert.table
    h.cert.relevance ns
  return #[shown, "rules: the honest main compiles to c₂ (object and SrcEval); the swapped program \
    passed tiers S and C before and erasure declined it (erase-recursor)"]

/-! ## `univs`, `dense`, `ctorRecords` on `fProg`'s `main := f c₁ c₂` -/

def univsDenseRecords (a : Assert) : IO (Array String) := do
  let (h, f, _, main) ← fProg "univs, dense, ctorRecords" {}
  let P := h.inp.program
  let (_, hd, args) ← mainSpine P main
  let .const fId us := hd | throw (IO.userError "main's head")
  expect a (fId == f && us.isEmpty) "main's head is not f"
  -- `f.{0} c₁ c₂`: `f` has no universe parameter
  let Pu := withValue P main (Src.Term.mkApps (.const f [.zero]) args)
  erasureDeclined a "univs, f given a universe argument" h.cfg Pu h.cert.table h.cert.relevance
    "erase-univs"
  let univ ← refusedOnly a "univs, f given a universe argument" h.cfg h.cert Pu h.cert.table
    h.cert.relevance [s!"in the value of {P.short main}", "more universe arguments than its declaration"]
  -- a copy of `f` at `P.size`, outside the program's size, called by `main` with its record: the
  -- closure walk skips it, SrcEval would run it. At `Src.Recheck.annotation` only `dense` refuses
  -- it; `Recheck.run` refuses it before, since the annotation names a constant outside the program
  -- (`Recheck.checkRelevanceKeys`), and without that record S1 refuses the reference
  let some ef := P.entry? f | throw (IO.userError "f")
  let big := P.size
  let Pd := withValue { P with consts := P.consts.insert big ef } main
    (Src.Term.mkApps (.const big []) args)
  let annD := withConst h.cert.relevance Pd big
  let tableD ← match Src.Table.ofCert h.cfg.table Pd h.cert.table with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"dense: the table refused it: {m}")
  let dense ← annotationOnly a "dense, main calls a constant at the program's size" { Pd with table := tableD }
    annD ["at or above the program's size"]
  match Recheck.run h.cfg Pd { h.cert with relevance := annD } with
  | .ok _ => expect a false "dense: Recheck.run accepted it"
  | .error e =>
    expect a (e.stage == .relevance && e.message.contains "names a constant outside the program")
      s!"dense: Recheck.run refused it otherwise: {e.render}"
  match Src.Recheck.annotation { Pd with table := tableD } h.cert.relevance with
  | .error (.relevance errs) =>
    expect a (errs.any (·.message == "constant without a record"))
      "dense, without the record: S1 does not refuse the reference"
  | _ => expect a false "dense, without the record: not refused at relevance"
  -- `c₂`'s constructor record removed: `c₂` is reached as `f`'s argument, not at a spine head
  let some (Src.Term.const c₂ _, _, _) := args[1]? | throw (IO.userError "c₂")
  let annR := { h.cert.relevance with ctors := h.cert.relevance.ctors.erase c₂ }
  let record ← refusedOnly a "ctorRecords, c₂'s record removed" h.cfg h.cert P h.cert.table annR
    [s!"({P.short c₂})", "a reached constructor without a constructor record"]
  return #[univ, s!"dense, main calls a constant at the program's size: {dense}; Recheck.run \
    refuses it at its annotation keys, and S1 without its record", record,
    "univs: the planted program passed tiers S and C before and erasure \
    declined it (erase-univs)"]

/-! ## `subsingletonFields` and `finProof` on committed closures -/

/-- A committed closure at roots `chosen`: ingress, the producer's table and the kernel
annotator's annotation, and its compilation (`produce`, `Recheck.run`). -/
structure Fixture where
  cfg : Recheck.Config
  P : Src.Program
  tc : Src.Table.TableCert
  ann : Src.Relevance.Ann
  cert : Recheck.Cert
  art : Recheck.Artifact
  main : Src.CId

def fixture (label : String) (clo eqs : System.FilePath) (chosen : List String) : IO Fixture := do
  let raw ← IO.FS.readBinFile clo
  let sc ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let inp ← ofErr s!"{label}: ingress" (Recheck.ingress raw sc chosen)
  let cfg := Recheck.Config.forInput {} inp
  let P := inp.program
  let some (_, main) := P.roots.head? | throw (IO.userError s!"{label}: no root")
  let cert ← ofErr s!"{label}: produce" (Recheck.produce cfg inp)
  let art ← ofErr s!"{label}: Recheck.run" (Recheck.run cfg P cert)
  return { cfg, P, tc := cert.table, ann := cert.relevance, cert, art, main }

/-- Π domain `i` of a telescope replaced by `d'`. -/
def setDom : Nat → Src.Term → Src.Term → Src.Term
  | 0, d', .pi b r _ body => .pi b r d' body
  | n + 1, d', .pi b r d body => .pi b r d (setDom n d' body)
  | _, _, t => t

def wordsDir : System.FilePath := "fixtures/ixon-v4/src-words"

/-- `Words.u8` (a word entry reached, so the towers' constructors are): `Fin.mk`'s proof field
given type `Nat` below the kernel, with the canonical record for that type (the field kept), so
that only `finProof` refuses it; and `Fin.mk`'s record removed, which S1 refuses first at a projection. -/
def finProof (a : Assert) (fx : Fixture) : IO (Array String) := do
  let (obj, src) := runBoth fx.art 0 fx.main [0, 3, 4]
  expect a (obj == some (.nat 7) && src == some (.nat 7))
    s!"finProof: Words.u8 0 3 4 is not 7 (object {repr obj}, SrcEval {repr src})"
  let some fin := fx.P.known.finMk | throw (IO.userError "no pinned Fin.mk")
  let some natId := fx.P.known.nat | throw (IO.userError "no pinned Nat")
  let some (.ctor x1 x2 x3 x4 np nf ty) := fx.P.decl? fin | throw (IO.userError "Fin.mk")
  let Pf := fx.P.setDecl fin (.ctor x1 x2 x3 x4 np nf (setDom (np + 1) (.const natId []) ty))
  let kept ← refusedOnly a "finProof, Fin.mk's proof field of type Nat (kept)" fx.cfg fx.cert Pf fx.tc
    (withCtor fx.ann Pf fin) [s!"({fx.P.short fin})", "Fin.mk's proof field"]
  let annR := { fx.ann with ctors := fx.ann.ctors.erase fin }
  let table ← match Src.Table.ofCert fx.cfg.table fx.P fx.tc with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"finProof: the table: {m}")
  -- Without `Fin.mk`'s record a tier-S check refuses first here: `Words.u8` projects out of
  -- `Fin` (S1 at the projection), so `check` fails and `checkCanonical` does not run
  let both ← match Src.Recheck.annotation { fx.P with table } annR with
    | .error (.relevance errs) =>
      let ms := errs.toList.map (·.render { fx.P with table })
      expect a (ms.any (·.contains "projection of a structure without a constructor record"))
        s!"finProof, Fin.mk's record removed: not refused by S1 at a projection: {ms}"
      pure s!"finProof, Fin.mk's record removed: refused first by S1 at a projection out of Fin \
        ({ms.length} errors)"
    | _ => do expect a false "finProof, Fin.mk's record removed: not refused at relevance"; pure ""
  return #[kept, both, "finProof: Words.u8 0 3 4 = 7 (object and SrcEval)"]

/-- A reached eliminator of a subsingleton kind in the committed closure `clo` at root `chosen`:
its sources given one more (a proof). Through `Recheck.run` the table certificate's `recKind`
column is derived from the declarations (`Table.recKindOfCert`, `deriveRecKind`: one source per
field of rule 0's constructor), which this part asserts of the honest table, so the violation is
planted in the table `Src.Recheck.annotation` reads, the step `Recheck.run` calls. -/
def subsingleton (a : Assert) (label : String) (fx : Fixture) (xs : List Nat) :
    IO (Array String) := do
  let (obj, src) := runBoth fx.art 0 fx.main xs
  expect a (obj.isSome && obj == src) s!"{label}: object {repr obj}, SrcEval {repr src}"
  let table ← match Src.Table.ofCert fx.cfg.table fx.P fx.tc with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"{label}: the table: {m}")
  let Pt := { fx.P with table }
  let .ok (_, ch) := Src.Recheck.annotation Pt fx.ann | throw (IO.userError s!"{label}: refused")
  let found := ch.reached.filterMap fun c => do
    let shape ← Src.Relevance.Check.elimShape? Pt c
    let .subsingleton w srcs ← Pt.table.recKindOf shape.recr | none
    let .recr _ _ _ _ _ _ _ _ rules _ ← Pt.decl? shape.recr | none
    let rule ← rules[0]?
    let .ctor _ _ _ _ _ nf _ ← Pt.decl? rule.ctor | none
    pure (shape.recr, w, srcs, nf)
  let some (r, w, srcs, nf) := found.head? | throw (IO.userError s!"{label}: no subsingleton eliminator")
  expect a (found.all fun (_, _, srcs, nf) => srcs.length == nf)
    s!"{label}: a derived kind has a source count other than its constructor's field count"
  let Pp := { Pt with table := { table with recKind := table.recKind.insert r (.subsingleton w (srcs ++ [.proof])) } }
  let shown ← annotationOnly a s!"{label}, one more source" Pp fx.ann
    [s!"({Pt.short r})", s!"takes {srcs.length + 1} field sources", s!"has {nf} fields"]
  return #[s!"{label}, one more source: {shown}", s!"{label}: {found.length} reached subsingleton \
    eliminators, each with its derived sources one per field; the honest root runs alike in the \
    object and SrcEval"]

def run (a : Assert) : IO (Array String) := do
  let words ← fixture "Words.u8" (wordsDir / "words.ixe") (wordsDir / "words.equations.json") ["Words.u8"]
  return (← sorts a) ++ (← rules a) ++ (← univsDenseRecords a) ++
    (← subsingleton a "subsingletonFields, Words.u8" words [0, 3, 4]) ++ (← finProof a words)

end IxCCTests.Recheck.Shape
