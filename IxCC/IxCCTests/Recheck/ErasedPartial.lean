import IxCCTests.Recheck.ErasedBlocks

/-! # An eliminator over a constructor field written erased, away from a saturated spine

C3 compares each minor premise with the constructor whose fields it receives, and sees the
minors only at a saturated eliminator spine (`Check.knownHead`). An eliminator applied to fewer
arguments (bound by a `let`, passed to a β-redex, the value of a definition, not applied at all)
receives its minors later at a variable head, and a `csimp` redirect to a `case` key (a target the
table admits) passes its callers' minors to the eliminator without a walked term: in both, an
η-short minor over a field written erased met no check, the rule (F2) or the `case` entry (F5)
applied it to `irr`, and the object returned a wrong constructor (the eighth route; the lead's
`plans/resource-cert/P1.md`). C3 now refuses such an eliminator wherever its minors would escape
it (`Check.erasedMinors`; `Check.partialElim` at a shorter spine and on a bare occurrence,
`Check.Canonical.redirectsErased?` on a `csimp` redirect).

The programs are `Erased.lean`'s `Key | mk (a b c : E)` with field `b` written erased and the
η-short minor `useG3 a b c := b`, meaning `c₁`: below the kernel (the honest program ingested,
the mark planted in the Src program) and through the certified kernel (the mark in the bytes,
which the kernel accepts; the certificate the kernel annotator's annotation with `mk`'s record
made canonical, since that annotator keeps a field written erased, an open capability item); and
the committed `erased-blocks` closure's `B.rec`, a mutual block's second recursor. Each honest
twin compiles to `c₁` (object and SrcEval). -/

namespace IxCCTests.Recheck.ErasedPartial

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.Src (Assert expect)
open IxCCTests.Recheck.Hostile (defn sidecar ofErr)
open IxCCTests.IxonV3.Builder (store block arrow lambda)
open IxCCTests.Support.Bound (loadBase addEnum simpleRecursor Field Ind)
open IxCCTests.Recheck.Erased (objMain srcMain lookup ingest ctorRoots installed keyProg keyCasesOn
  mapArg eraseParam withNode withCtor withConst accepted refused)

abbrev X := IxCC.Ixon.V3.Expr

/-- What C3 says at an eliminator applied to fewer arguments than its arity, or bare. -/
def partialMsg : String := "is applied to fewer arguments than its arity"

/-- `(λ g. g aₙ …) (head a₀ … aₙ₋₁)`: the eliminator spine `v` with its head applied to its first
`n` arguments, the rest supplied at a variable head (`dom` is the λ's domain). -/
def viaBeta (dom : Src.Term) (n : Nat) (v : Src.Term) : Src.Term :=
  let (hd, args) := v.spine
  Src.Term.app (.lam {} dom (Src.Term.mkApps (.var 0) (args.drop n))) (Src.Term.mkApps hd (args.take n))
    .strict .rel

/-- `let g := head a₀ … aₙ₋₁; g aₙ …`. -/
def viaLet (dom : Src.Term) (n : Nat) (v : Src.Term) : Src.Term :=
  let (hd, args) := v.spine
  Src.Term.letE { nonDep := false } .rel dom (Src.Term.mkApps hd (args.take n))
    (Src.Term.mkApps (.var 0) (args.drop n))

/-- Below the kernel, at `Key.rec` and at `Key.casesOn`'s `case` entry. -/
def below (a : Assert) (viaCase : Bool) : IO (Array String) := do
  let route := if viaCase then "case entry" else "recursor"
  let (h, eId, mkId, main, _, majorPos) ← keyProg s!"partial, {route}" viaCase
  let Pi ← installed h
  let some (.defn dk ds dl mty mval) := Pi.decl? main | throw (IO.userError "main")
  let some (.ctor x1 x2 x3 x4 np nf mkTy) := Pi.decl? mkId | throw (IO.userError "mk")
  let mut out := #[]
  -- honest: the eliminator partially applied, by a β-redex and by a `let`
  for (what, v) in [("β-redex", viaBeta mty 1 mval), ("let", viaLet mty 1 mval)] do
    accepted a s!"{route} partially applied ({what}), no field erased" h.cfg (Pi.setDecl main (.defn dk ds dl mty v))
      h.cert.table (withNode h.cert.relevance (.value main) v.tagOrder) main (.ctor 1 [])
    out := out.push s!"{route} partially applied ({what}), honest: accepted, c₁ (object and SrcEval)"
  -- field 1 of mk written erased, the major passing □ for it
  let Pe := Pi.setDecl mkId (.ctor x1 x2 x3 x4 np nf (eraseParam 1 mkTy))
  let dropB := mapArg eId majorPos fun (x, m, r) =>
    (mapArg mkId 1 (fun (y, m', _) => (y, m', Src.Rel.prf)) x, m, r)
  let annE := withCtor h.cert.relevance Pe mkId
  let v0 := dropB mval
  let P := Pe.setDecl main (.defn dk ds dl mty v0)
  out := out.push (← refused a s!"{route} saturated, η-short minor over field 1 written erased (C3's η-short clause)"
    h.cfg P h.cert.table (withNode annE (.value main) v0.tagOrder)
    [s!"in the value of {P.short main}", "minor 0 does not bind field 1, which is written erased"])
  for (what, v) in [("partially applied, a β-redex's argument", viaBeta mty 1 v0),
      ("bare, a β-redex's argument", viaBeta mty 0 v0), ("partially applied, let-bound", viaLet mty 1 v0)] do
    let P := Pe.setDecl main (.defn dk ds dl mty v)
    out := out.push (← refused a s!"{route} {what}, η-short minor over field 1 written erased" h.cfg P
      h.cert.table (withNode annE (.value main) v.tagOrder) [s!"in the value of {P.short main}", partialMsg])
  return out

/-- A `csimp` redirect of `f.{u}` (with `Key.casesOn`'s type) to `Key.casesOn`, a `case` key:
`main := f (λ _. E) (mk c₀ c₁ c₂) useG3`, saturated at `f`, which C3 does not see as an eliminator. -/
def csimpCase (a : Assert) : IO (Array String) := do
  let (h, cId, mkId, main, _, majorPos) ← keyProg "csimp to a case key" true
  let Pi ← installed h
  let some (.defn dk ds dl mty mval) := Pi.decl? main | throw (IO.userError "main")
  let some (.ctor x1 x2 x3 x4 np nf mkTy) := Pi.decl? mkId | throw (IO.userError "mk")
  let some (.defn _ _ cl cTy _) := Pi.decl? cId | throw (IO.userError "Key.casesOn")
  let some eq := Pi.known.eq | throw (IO.userError "Eq")
  let Pe := Pi.setDecl mkId (.ctor x1 x2 x3 x4 np nf (eraseParam 1 mkTy))
  let dropB := mapArg cId majorPos fun (x, m, r) =>
    (mapArg mkId 1 (fun (y, m', _) => (y, m', Src.Rel.prf)) x, m, r)
  let us := Src.Table.paramUnivs cl
  let mut out := #[]
  for erased in [false, true] do
    let (Pb, annB, vb) := if erased then (Pe, withCtor h.cert.relevance Pe mkId, dropB mval)
      else (Pi, h.cert.relevance, mval)
    let f := Pb.size
    let fa := IxCCTests.Src.Builder.fakeAddr (f + 4000000)
    let Pf := Pb.push { ref := .member fa 0, addr := fa, decl := .defn .defn .safe cl cTy (.const cId us) }
    let thm := Pf.size
    let ta := IxCCTests.Src.Builder.fakeAddr (thm + 4000000)
    let stmt := Src.Term.mkApps (.const eq [.succ .zero])
      [(cTy, .strict, .rel), (.const f us, .strict, .rel), (.const cId us, .strict, .rel)]
    let Pf := Pf.push { ref := .member ta 0, addr := ta, decl := .defn .thm .safe cl stmt (.natLit 0) }
    let (hd, args) := vb.spine
    let hd' := match hd with
      | .const _ vs => Src.Term.const f vs
      | t => t
    let v := Src.Term.mkApps hd' args
    let Pf := Pf.setDecl main (.defn dk ds dl mty v)
    let ann := withNode (withConst annB Pf f) (.value main) v.tagOrder
    let tc := { h.cert.table with resolve := (f, .csimp cId thm) :: h.cert.table.resolve }
    if erased then
      out := out.push (← refused a "csimp f ↦ Key.casesOn, η-short minor over field 1 written erased" h.cfg Pf tc ann
        [s!"({Pf.short f})", s!"the csimp redirect to {Pf.short cId}",
         "an eliminator over a constructor that writes a field erased"])
    else
      accepted a "csimp f ↦ Key.casesOn, no field erased" h.cfg Pf tc ann main (.ctor 1 [])
      out := out.push "csimp f ↦ Key.casesOn, honest: accepted, c₁ (object and SrcEval)"
  return out

/-- The committed closure's `B.rec`, a mutual block's second recursor, partially applied
(`viaBeta` after the motives): honest, and with `b1`'s field written erased below the kernel. -/
def mutualBlock (a : Assert) : IO (Array String) := do
  let l ← IxCCTests.Recheck.ErasedBlocks.load "mainB"
  let some (.defn dk ds dl mty mval) := l.Pi.decl? l.main | throw (IO.userError "main")
  let v := viaBeta mty 2 mval
  accepted a "B.rec partially applied, no field erased" l.cfg (l.Pi.setDecl l.main (.defn dk ds dl mty v)) l.tc
    (withNode l.ann (.value l.main) v.tagOrder) l.main (.ctor 1 [])
  let (Q, ann, _, _) ← IxCCTests.Recheck.ErasedBlocks.plant l [6] 0 []
  let some (.defn dk ds dl mty qv) := Q.decl? l.main | throw (IO.userError "main")
  let v := viaBeta mty 2 qv
  let Q := Q.setDecl l.main (.defn dk ds dl mty v)
  let line ← refused a "B.rec partially applied, η-short minor over b1's field written erased" l.cfg Q l.tc
    (withNode ann (.value l.main) v.tagOrder) [s!"in the value of {Q.short l.main}", partialMsg]
  return #["B.rec partially applied, honest: accepted, c₁ (object and SrcEval)", line]

/-- `Key | mk (a : E) (b : E) (c : E)`, `b` written erased when `erased`. -/
def keyBlock (eAddr : IxCC.Ixon.Address) (erased : Bool) : Constant :=
  let eRef : X := .ref 0 #[]
  let b1 : BinderContract := if erased then .erased else .many
  let ty : X := .all .many .shared eRef (.all b1 .shared eRef (.all .many .shared eRef (.recur 0 #[])))
  ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 3, ty⟩]⟩], #[], #[eAddr], #[.succ .zero]⟩

/-- Through the certified kernel. `variant`: 0 `Key.rec` partially applied (a β-redex's
argument), 1 `Key.casesOn` partially applied, 2 the η-reduced definition
`myRec : (E → E → E → E) → Key → E := Key.rec.{1} (λ _. E)` with `main := myRec useG3 major`. -/
def kernel (a : Assert) (label : String) (variant : Nat) (erased : Bool) : IO String := do
  let (e, en) := addEnum (← loadBase) 3
  let (e, blk) := block e (keyBlock en.ind erased)
  let fields : Array (Array Field) := #[#[.ext en.ind, .ext en.ind, .ext en.ind]]
  let (e, rec) := store e (simpleRecursor blk fields)
  let key : Ind := { block := blk, ind := indcProjAddr blk 0, ctors := #[ctorProjAddr blk 0 0], recursor := rec, existing := false }
  let (e, elim) := if variant == 1 then store e (keyCasesOn key en.ind) else (e, rec)
  let E : X := .ref 0 #[]
  let (e, useG) := store e ⟨defn (arrow E (arrow E (arrow E E))) (lambda E (lambda E (lambda E (.var 1)))), #[],
    #[en.ind], #[]⟩
  -- refs: 0 E, 1 the eliminator, 2 Key, 3 useG3, 4 mk, 5-7 c₀ c₁ c₂, 8 myRec (variant 2)
  let keyT : X := .ref 2 #[]
  let motive : X := .lam .many keyT E
  let major : X := .app (.app (.app (.ref 4 #[]) (.ref 5 #[])) (.ref 6 #[])) (.ref 7 #[])
  let gTy : X := arrow (arrow E (arrow E (arrow E E))) (arrow keyT E)
  let (e, myRec) := store e ⟨defn gTy (.app (.ref 1 #[0]) motive), #[], #[en.ind, rec, key.ind], #[.succ .zero]⟩
  let mainBody : X := match variant with
    | 1 => .app (lambda (arrow keyT (arrow (arrow E (arrow E (arrow E E))) E))
        (.app (.app (.var 0) major) (.ref 3 #[]))) (.app (.ref 1 #[0]) motive)
    | 2 => .app (.app (.ref 8 #[]) (.ref 3 #[])) major
    | _ => .app (lambda gTy (.app (.app (.var 0) (.ref 3 #[])) major)) (.app (.ref 1 #[0]) motive)
  let refs := #[en.ind, elim, key.ind, useG, key.ctors[0]!, en.ctors[0]!, en.ctors[1]!, en.ctors[2]!] ++
    (if variant == 2 then #[myRec] else #[])
  let (e, main) := store e ⟨defn E mainBody, #[], refs, #[.succ .zero]⟩
  let (e, rs) := ctorRoots e en.ind en.ctors
  if !erased then
    let h ← ingest label e ([("main", main)] ++ rs)
    let mainId ← lookup h.art.src main "main"
    expect a (objMain h.art == some (.ctor 1 []) && srcMain h.art mainId == some (.ctor 1 []))
      s!"{label}: object {repr (objMain h.art)}, SrcEval {repr (srcMain h.art mainId)}"
    return s!"{label}: kernel, produce, Recheck.run accept; c₁ (object and SrcEval)"
  let inp ← ofErr s!"{label}: ingress" (Recheck.ingress (IxCCTests.Support.Bound.write e) (sidecar ([("main", main)] ++ rs)) [])
  let cfg := Recheck.Config.forInput {} inp
  let P := inp.program
  let (table, _, _) := Src.Table.build cfg.table P inp.hints.proposals
  let mkId ← lookup P key.ctors[0]! "mk"
  let mainId ← lookup P main "main"
  let ann ← match inp.kernel.annotateChecked { P with table } with
    | .ok ann => pure ann
    | .error m => throw (IO.userError s!"{label}: the kernel annotator: {m}")
  -- the open capability item: the annotator's record keeps the field its type writes erased
  expect a ((ann.ctorRel? mkId).map (·.fields) == some [.keep, .keep, .keep])
    s!"{label}: the kernel annotator's record of mk changed: {repr (ann.ctorRel? mkId)}"
  let needles := match variant with
    | 2 => [partialMsg]
    | _ => [s!"in the value of {P.short mainId}", partialMsg]
  match Recheck.produce cfg inp with
  | .ok _ => expect a false s!"{label}: produce accepted it"
  | .error err => expect a (needles.all (err.render.contains ·)) s!"{label}: produce refused it otherwise: {err.render}"
  refused a s!"{label} (the record made canonical)" cfg P (Src.Table.TableCert.ofTable table) (withCtor ann P mkId)
    needles

def run (a : Assert) : IO (Array String) := do
  let mut out := (← below a false) ++ (← below a true) ++ (← csimpCase a) ++ (← mutualBlock a)
  for (label, variant) in [("bytes, Key.rec partially applied", 0), ("bytes, Key.casesOn partially applied", 1),
      ("bytes, myRec := Key.rec (λ _. E)", 2)] do
    out := out.push (← kernel a s!"{label}, no field erased" variant false)
    out := out.push (← kernel a s!"{label}, field b written erased" variant true)
  return out

end IxCCTests.Recheck.ErasedPartial
