import IxCCTests.Recheck.Shape

/-! # A position at or past a special head's arity, written erased (the eleventh route)

A special head (a constructor, `Quot.mk`, `Quot.lift`, a recursor, a `case` key, a primitive, a
word operation) fires once its arity of arguments has arrived; an argument past the arity is
applied to the value it fires to. `checkCanonical`'s `readsErased?` compared the positions a
special head's type writes erased with those the head reads (`headReadsWith`), but not with the
arity: `Quot.lift` reads only its function and its quotient, so a stored type of `Quot.lift` with a
seventh Π written erased passed every check. Over-applied, `Quot.lift` fires to its function's
result and the caller passes that result the irrelevance marker for the seventh argument: below
the kernel (the front end does not check `Quot.lift`'s stored type), `main := Quot.lift.{1,1} E
(Eq E) (E → E) g h (Quot.mk E (Eq E) c₁) c₂` with `g := λ e y. y`, which means `c₂`, passed
`Src.Recheck.annotation` and `Recheck.run`, its object returned `c₀` and SrcEval the marker
(engineer PB's finding, `plans/resource-cert/P1.md`). `readsAt` now reads every position at or
past the head's arity (`Check.Canonical.headArityOf`, SrcEval's `Program.headArity`), and L1 gains
`erased_lt_arity`.

What the other special heads did past their arity, read before and asserted here: a constructor
and `Quot.mk` fire to a constructor value, and SrcEval is stuck applying one; a recursor, a
primitive and a word operation read every argument, so any position written erased was refused
already; a `case` key reads every position from `np + 1` (the major and the minors), and its
parameters and motive may be written erased. Each of these is now refused at or past the arity by
the same rule. -/

namespace IxCCTests.Recheck.ErasedArity

open IxCC IxCC.Ixon IxCC.Ixon.V3
open IxCCTests.Src (Assert expect)
open IxCCTests.Recheck.Hostile (defn sidecar ofErr)
open IxCCTests.IxonV3.Builder (store arrow lambda)
open IxCCTests.Support.Bound (loadBase addEnum)
open IxCCTests.Recheck.Erased (E X Honest objMain srcMain lookup ingest ctorRoots installed withNode
  withConst quotAddrs eraseParam casesEnv refused accepted)
open IxCCTests.Recheck.Shape (refusedOnly recProg fixture wordsDir Fixture)

/-- Put a Π `(x :⁰ dom)` after the first `n` Π binders of a telescope, above its conclusion
(`dom` closed). -/
def appendErasedPi (dom : Src.Term) : Nat → Src.Term → Src.Term
  | 0, concl => .pi { contract := .erased } {} dom (Src.Relevance.Check.Canonical.liftTerm 1 0 concl)
  | n + 1, .pi b r d body => .pi b r d (appendErasedPi dom n body)
  | _, t => t

/-- SrcEval on `main` of `P` with `ann`, past tiers S and C and without `checkCanonical`. -/
def srcNoCanonical (cfg : Recheck.Config) (P : Src.Program) (tc : Src.Table.TableCert)
    (ann : Src.Relevance.Ann) (main : Src.CId) : IO (Sem.Result Src.Value) := do
  let table ← match Src.Table.ofCert cfg.table P tc with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"the table refused it: {m}")
  match IxCCTests.Src.annotationNoCanonical { P with table } ann with
  | .ok (src, _) => pure (Src.run src 100000 main [])
  | .error _ => throw (IO.userError "tiers S and C refused it")

def isMarker : Sem.Result Src.Value → Bool
  | .ok v => v.isIrr
  | _ => false

def isStuck : Sem.Result Src.Value → Bool
  | .stuck => true
  | _ => false

/-- `Src.Recheck.annotation` on `Pt` (its table built) refuses it at the relevance checks, one
error naming every needle (others may fire too). -/
def annotationNamed (a : Assert) (hk : IxCCTests.Recheck.Erased.Hooks) (label : String) (Pt : Src.Program) (ann : Src.Relevance.Ann)
    (needles : List String) : IO String := do
  hk.refused label Pt ann
  match Src.Recheck.annotation Pt ann with
  | .ok _ => do expect a false s!"{label}: accepted by Src.Recheck.annotation"; return ""
  | .error (.relevance errs) => do
    let ms := errs.toList.map (·.render Pt)
    let shown := (ms.find? fun m => needles.all (m.contains ·)).getD ""
    expect a (!shown.isEmpty) s!"{label}: refused without naming {needles}: {ms}"
    return s!"{label}: {shown}"
  | .error _ => do expect a false s!"{label}: refused at install or table"; return ""

/-! ## `Quot.lift` and `Quot.mk` over-applied -/

/-- The ingested quotient program (`Erased.quot`'s, with `g : E → E → E := λ e y. y`). -/
structure QuotProg where
  h : Honest
  Pi : Src.Program
  mainId : Src.CId
  liftId : Src.CId
  mkId : Src.CId
  gId : Src.CId
  c0 : Src.CId
  c1 : Src.CId
  c2 : Src.CId
  eT : Src.Term
  eqT : Src.Term

def quotProg : IO QuotProg := do
  let env0 ← loadBase
  let qs := quotAddrs env0
  let some qty := qs.lookup .type | throw (IO.userError "no Quot in the base")
  let some qmkA := qs.lookup .ctor | throw (IO.userError "no Quot.mk in the base")
  let some qliftA := qs.lookup .lift | throw (IO.userError "no Quot.lift in the base")
  let (e, en) := addEnum env0 3
  let (e, gA) := store e ⟨defn (arrow E (arrow E E)) (lambda E (lambda E (.var 0))), #[], #[en.ind], #[]⟩
  let (e0, m0) := store e ⟨defn E (.ref 1 #[]), #[], #[en.ind, en.ctors[1]!], #[]⟩
  let inp0 ← ofErr "arity, quot: first ingress"
    (Recheck.ingress (IxCCTests.Support.Bound.write e0) (sidecar [("main", m0)]) [])
  let some eq0 := inp0.program.known.eq | throw (IO.userError "no Eq")
  let eqA := inp0.program.addr eq0
  let eqE : X := .app (.ref 2 #[0]) E
  let hDom : X := .all .many .shared E (.all .many .shared E (.all .many .shared
    (.app (.app (.app (.ref 2 #[0]) E) (.var 1)) (.var 0))
    (.app (.app (.app (.ref 2 #[0]) E) (.app (.var 3) (.var 2))) (.app (.var 3) (.var 1)))))
  let qlTy : X := .all .many .shared (arrow E E) (.all .many .shared hDom
    (.all .many .shared (.app (.app (.ref 3 #[0]) E) eqE) E))
  let (e, ql) := store e ⟨.defn ⟨.defn, .safe, 0, qlTy, .app (.app (.app (.ref 1 #[0, 0]) E) eqE) E⟩, #[],
    #[en.ind, qliftA, eqA, qty], #[.succ .zero]⟩
  let (e, qm) := store e ⟨.defn ⟨.defn, .safe, 0, .app (.app (.ref 3 #[0]) E) eqE,
    .app (.app (.app (.ref 1 #[0]) E) eqE) (.ref 4 #[])⟩, #[], #[en.ind, qmkA, eqA, qty, en.ctors[1]!],
    #[.succ .zero]⟩
  let (e, main) := store e ⟨defn E (.ref 1 #[]), #[], #[en.ind, en.ctors[1]!], #[]⟩
  let (e, rs) := ctorRoots e en.ind en.ctors
  let h ← ingest "arity, quot" e ([("main", main)] ++ rs ++ [("ql", ql), ("qm", qm), ("g", gA)])
    (["main"] ++ rs.map (·.1))
  let P := h.inp.program
  let eId ← lookup P en.ind "E"
  let some eqId := P.known.eq | throw (IO.userError "no Eq")
  let eT : Src.Term := .const eId []
  return { h, Pi := ← installed h, mainId := ← lookup P main "main", liftId := ← lookup P qliftA "Quot.lift"
           mkId := ← lookup P qmkA "Quot.mk", gId := ← lookup P gA "g", c0 := ← lookup P en.ctors[0]! "c₀"
           c1 := ← lookup P en.ctors[1]! "c₁", c2 := ← lookup P en.ctors[2]! "c₂", eT
           eqT := .app (.const eqId [.succ .zero]) eT .strict .type }

/-- `main := v` with the records of `Quot.lift`, `Quot.mk` and `g` from `Q`'s types. -/
def quotWith (q : QuotProg) (Q : Src.Program) (v : Src.Term) : Src.Program × Src.Relevance.Ann :=
  let Q := Q.setDecl q.mainId (.defn .defn .safe 0 q.eT v)
  let ann := withConst (withConst (withConst q.h.cert.relevance Q q.liftId) Q q.mkId) Q q.gId
  (Q, withNode (withNode ann (.value q.mainId) v.tagOrder) (.value q.gId) [.lam .rel .never, .lam .rel .never])

def setQuotType (P : Src.Program) (c : Src.CId) (f : Src.Term → Src.Term) : Src.Program :=
  match P.decl? c with
  | some (.quot qk l ty) => P.setDecl c (.quot qk l (f ty))
  | _ => P

def quot (a : Assert) (hk : IxCCTests.Recheck.Erased.Hooks) : IO (Array String) := do
  let q ← quotProg
  let one : IxCC.Ixon.Univ := .succ .zero
  let mkV := Src.Term.mkApps (.const q.mkId [one])
    [(q.eT, .strict, .type), (q.eqT, .strict, .type), (.const q.c1 [], .strict, .rel)]
  /- `Quot.lift E (Eq E) (E → E) g h (Quot.mk E (Eq E) c₁) c₂`, its last argument tagged `last` -/
  let lift := fun (last : Src.Rel) => Src.Term.mkApps (.const q.liftId [one, one])
    [(q.eT, .strict, .type), (q.eqT, .strict, .type), (.pi {} {} q.eT q.eT, .strict, .type),
     (.const q.gId [], .strict, .rel), (.sort .zero, .strict, Src.Rel.prf), (mkV, .strict, .rel),
     (.const q.c2 [], .strict, last)]
  let (P0, ann0) := quotWith q q.Pi (lift .rel)
  accepted a hk "Quot.lift over-applied, g c₁ c₂" q.h.cfg P0 q.h.cert.table ann0 q.mainId (.ctor 2 [])
  -- the stored type of `Quot.lift` with a seventh Π `(x :⁰ E)`, the program's argument for it `prf`
  let (P1, ann1) := quotWith q (setQuotType q.Pi q.liftId (appendErasedPi q.eT 6)) (lift Src.Rel.prf)
  let r1 ← srcNoCanonical q.h.cfg P1 q.h.cert.table ann1 q.mainId
  expect a (isMarker r1) "Quot.lift with a seventh Π written erased: SrcEval does not return the marker"
  let lift7 ← refusedOnly a hk "Quot.lift over-applied at a seventh Π written erased" q.h.cfg q.h.cert P1
    q.h.cert.table ann1 [s!"({q.Pi.short q.liftId})", "parameter 6 is written erased",
      "the value Quot.lift fires to", "at or past the arity 6"]
  -- `Quot.mk E (Eq E) c₁ c₂` with a fourth Π `(x :⁰ E)` on `Quot.mk`: SrcEval was stuck applying
  -- the constructor value
  let mk4 := Src.Term.app mkV (.const q.c2 []) .strict Src.Rel.prf
  let (P2, ann2) := quotWith q (setQuotType q.Pi q.mkId (appendErasedPi q.eT 3)) mk4
  let r2 ← srcNoCanonical q.h.cfg P2 q.h.cert.table ann2 q.mainId
  expect a (isStuck r2) "Quot.mk over-applied: SrcEval is not stuck"
  let mk ← refused a hk "Quot.mk over-applied at a fourth Π written erased" q.h.cfg P2 q.h.cert.table ann2
    [s!"({q.Pi.short q.mkId})", "parameter 3 is written erased", "the value Quot.mk fires to",
      "at or past the arity 3"]
  -- a constructor of `E` (arity 0) with a Π `(x :⁰ E)`, applied: SrcEval was stuck
  let c0V := Src.Term.app (.const q.c0 []) (.const q.c2 []) .strict Src.Rel.prf
  let Pc := match q.Pi.decl? q.c0 with
    | some (.ctor x1 x2 x3 x4 np nf ty) => q.Pi.setDecl q.c0 (.ctor x1 x2 x3 x4 np nf (appendErasedPi q.eT 0 ty))
    | _ => q.Pi
  let (P3, ann3) := quotWith q Pc c0V
  let ann3 := withConst ann3 P3 q.c0
  let r3 ← srcNoCanonical q.h.cfg P3 q.h.cert.table ann3 q.mainId
  expect a (isStuck r3) "a constructor over-applied: SrcEval is not stuck"
  let ctor ← refused a hk "a constructor of arity 0 over-applied at a Π written erased" q.h.cfg P3
    q.h.cert.table ann3 [s!"({q.Pi.short q.c0})", "parameter 0 is written erased",
      "the value the constructor fires to", "at or past the arity 0"]
  return #["Quot.lift over-applied (g c₁ c₂): accepted, c₂ (object and SrcEval)",
    "Quot.lift with a seventh Π written erased: SrcEval returns the marker without the check", lift7,
    "Quot.mk and a constructor over-applied: SrcEval stuck without the check", mk, ctor]

/-! ## A recursor, a primitive, a word operation: every position read -/

/-- `E.rec` (arity 5) with a sixth Π written erased. -/
def recursor (a : Assert) (hk : IxCCTests.Recheck.Erased.Hooks) : IO String := do
  let (h, recId, _) ← recProg "arity, recursor"
  let Pi ← installed h
  let some (.recr sf k lv np nmot nmin ni ind rs ty) := Pi.decl? recId | throw (IO.userError "E.rec")
  let some (.pi _ _ dom _) := some ty | throw (IO.userError "E.rec's type")
  let Pr := Pi.setDecl recId (.recr sf k lv np nmot nmin ni ind rs (appendErasedPi dom 5 ty))
  refused a hk "a recursor with a Π written erased past its arity" h.cfg Pr h.cert.table
    (withConst h.cert.relevance Pr recId)
    [s!"({Pi.short recId})", "parameter 5 is written erased", "the value the recursor",
      "at or past the arity 5"]

/-- `Nat.add` (a `prim` entry, arity 2) with a third Π written erased; `main := Nat.add 2 3`. -/
def primitive (a : Assert) (hk : IxCCTests.Recheck.Erased.Hooks) : IO String := do
  let (e, en) := addEnum (← loadBase) 3
  let (e, main) := store e ⟨defn E (.ref 1 #[]), #[], #[en.ind, en.ctors[1]!], #[]⟩
  let (e, rs) := ctorRoots e en.ind en.ctors
  let h ← ingest "arity, primitive" e ([("main", main)] ++ rs)
  let P := h.inp.program
  let mainId ← lookup P main "main"
  let some natId := P.known.nat | throw (IO.userError "no Nat")
  let some addN := P.known.pins.prims.lookup .add | throw (IO.userError "no Nat.add pin")
  let some addId := (List.range P.size).find? fun c => IxCC.Src.Pinned.addrNat (P.addr c) == addN
    | throw (IO.userError "Nat.add is not in the program read")
  let Pi ← installed h
  let natT : Src.Term := .const natId []
  let tc := if h.cert.table.resolve.any (·.1 == addId) then h.cert.table
    else { h.cert.table with resolve := (addId, .prim .add) :: h.cert.table.resolve }
  let table ← match Src.Table.ofCert h.cfg.table Pi tc with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"arity, primitive: the table: {m}")
  let v := Src.Term.mkApps (.const addId []) [(.natLit 2, .strict, .rel), (.natLit 3, .strict, .rel)]
  let Q := Pi.setDecl mainId (.defn .defn .safe 0 natT v)
  let Q := match Q.decl? addId with
    | some (.defn dk ds dl ty dv) => Q.setDecl addId (.defn dk ds dl (appendErasedPi natT 2 ty) dv)
    | _ => Q
  let ann := withNode (withConst h.cert.relevance Q addId) (.value mainId) v.tagOrder
  annotationNamed a hk "the primitive Nat.add with a Π written erased past its arity" { Q with table } ann
    [s!"({P.short addId})", "parameter 2 is written erased", "the value the primitive Nat.add fires to",
      "at or past the arity 2"]

/-- A reached word entry of `Words.u8` with a Π written erased past its operation's arity. -/
def word (a : Assert) (hk : IxCCTests.Recheck.Erased.Hooks) : IO String := do
  let fx ← fixture "Words.u8" (wordsDir / "words.ixe") (wordsDir / "words.equations.json") ["Words.u8"]
  let table ← match Src.Table.ofCert fx.cfg.table fx.P fx.tc with
    | .ok t => pure t
    | .error m => throw (IO.userError s!"arity, word: the table: {m}")
  let Pt := { fx.P with table }
  let .ok (_, ch) := Src.Recheck.annotation Pt fx.ann | throw (IO.userError "arity, word: refused")
  let found := ch.reached.filterMap fun c =>
    match Pt.table.resolveOf c, Pt.decl? c with
    | some (.word w op _), some d => some (c, w, op, d)
    | _, _ => none
  let some (c, _, op, d) := found.head? | throw (IO.userError "arity, word: no word entry reached")
  let dom := match d.type with
    | .pi _ _ dom _ => dom
    | t => t
  let d' : Src.Decl := match d with
    | .defn dk ds dl ty dv => .defn dk ds dl (appendErasedPi dom op.arity ty) dv
    | d => d
  let Q := Pt.setDecl c d'
  annotationNamed a hk "a word operation with a Π written erased past its arity" Q (withConst fx.ann Q c)
    [s!"({Pt.short c})", s!"parameter {op.arity} is written erased", "the value the word operation",
      s!"at or past the arity {op.arity}"]

/-! ## A `case` key: its parameters and motive unread, every position from `np + 1` read -/

/-- `E.casesOn` (`np = 0`, arity 5) of `Erased.casesEnv`: the motive (parameter 0) written erased is
accepted and runs; the major (parameter 1 = `np + 1`) and a Π past the arity written erased are
refused. -/
def caseKey (a : Assert) (hk : IxCCTests.Recheck.Erased.Hooks) : IO (Array String) := do
  let (e, co, roots) ← casesEnv .many
  let h ← ingest "arity, casesOn" e roots
  let P := h.inp.program
  let some (_, main) := P.roots.head? | throw (IO.userError "no root")
  let coId ← lookup P co "casesOn"
  let Pi ← installed h
  let some (.defn dk ds dl ty dv) := Pi.decl? coId | throw (IO.userError "casesOn")
  let some (.defn mk ms ml mty mval) := Pi.decl? main | throw (IO.userError "main")
  let withTy := fun (ty' : Src.Term) (v : Src.Term) =>
    let Q := (Pi.setDecl coId (.defn dk ds dl ty' dv)).setDecl main (.defn mk ms ml mty v)
    (Q, withNode (withConst h.cert.relevance Q coId) (.value main) v.tagOrder)
  let (P0, ann0) := withTy (eraseParam 0 ty) mval
  accepted a hk "casesOn with its motive written erased" h.cfg P0 h.cert.table ann0 main (.ctor 2 [])
  -- `main := E.casesOn (λ _. E)`: a saturated call would pass an irrelevant major, which C4 refuses
  -- first; partially applied (no constructor of `E` has a field) the key is still reached
  let (hd, args) := mval.spine
  let v1 := Src.Term.mkApps hd (args.take 1)
  let (P1, ann1) := withTy (eraseParam 1 ty) v1
  let major ← refused a hk "casesOn with its major written erased" h.cfg P1 h.cert.table ann1
    [s!"({P.short coId})", "parameter 1 is written erased", "its case entry"]
  let dom := match ty with
    | .pi _ _ _ (.pi _ _ dom _) => dom
    | t => t
  let (P5, ann5) := withTy (appendErasedPi dom 5 ty) mval
  let past ← refused a hk "casesOn with a Π written erased past its arity" h.cfg P5 h.cert.table ann5
    [s!"({P.short coId})", "parameter 5 is written erased", "at or past the arity 5"]
  return #["casesOn with its motive (parameter 0 = np) written erased: accepted, c₂ (object and SrcEval)",
    major, past]

def run (a : Assert) (hk : IxCCTests.Recheck.Erased.Hooks := {}) : IO (Array String) := do
  return (← quot a hk) ++ #[← recursor a hk, ← primitive a hk, ← word a hk] ++ (← caseKey a hk)

end IxCCTests.Recheck.ErasedArity
