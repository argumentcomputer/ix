import IxCCGrounding.WordFire
import IxCCGrounding.Check
import IxCC.Src.Table.Word

/-!
# The word check (`IxCCGrounding.WordCheck`, step W)

**`wordB`** decides the word clause `WordFacts` on a closure `Sl`, fail-closed: an entry whose
operation has no formula (a decision), whose keys the program does not pin, or whose stored shapes
differ in any way from those the word case reads is refused. Per width (computed once for each of the
four): the keys of the program's pins (`towKeys?`), the bridge theorem of the width's `ofNat` entry and
`Nat.le`'s two constructors (`bridgeKeys?`), the bridge stored with exactly `bridgeK`'s statement over
the role key of `Nat.mod` (`bridgeB`), the tower's stored shapes (`towerB`, at the keys `towAux?` reads
off the constructors' stored types and a search of the reading for `BitVec.toFin`), and the tower's
constructors in `Sl` without level parameters. Per entry: the head stored without level parameters
with a binder for every argument, the `Eq` basis, both widths' facts, and the theorem's stored
statement exactly `wordStmtK` (at `ofNat`, the operation the bridge's own). Every comparison of a
stored term is `decide` of an equality with a term built over keys; binder data are read off the
stored term (`piMetas`) and compared with it as part of that equality. **`wordFacts_of_check`**: the
decision is sound.
-/

namespace IxCC.Grounding

open Ix.Kernel
open IxCC.Src (Value Slot Term CId Program Levels Width WordOp WordResult)

/-- A placeholder binder datum. -/
def bm0 : BinderMeta := { pw := .never }

/-- The binder data of a term's first `n` `∀`s (read off the stored term, so that a comparison with
a term built over them decides the shape up to nothing). -/
def piMetas : Nat → KExpr → List BinderMeta
  | 0, _ => []
  | n + 1, .forallE _ b m => m :: piMetas n b
  | _ + 1, _ => []

/-- The binder data of a term's first `n` `λ`s. -/
def lamMetas : Nat → KExpr → List BinderMeta
  | 0, _ => []
  | n + 1, .lam _ b m => m :: lamMetas n b
  | _ + 1, _ => []

/-- The `i`-th datum, `bm0` past the list. -/
def bmAt (ms : List BinderMeta) (i : Nat) : BinderMeta := ms.getD i bm0

section Deciders

variable (env : KEnv)

/-- A key stored without level parameters. -/
def keyStoredB (k : KKey) : Bool :=
  match env.find? k with
  | some ci => decide (ci.toConstantVal.levelParams = [])
  | none => false

/-- `Nat.le` and its two constructors, exactly as `NatLeBasis` reads them. -/
def natLeB (kLe kR kS : KKey) : Bool :=
  (match env.find? kLe with
    | some (.indInfo cv _) =>
      let ms := piMetas 2 cv.type
      decide (cv.levelParams = [] ∧
        cv.type = .forallE natK (.forallE natK (.sort .zero) (bmAt ms 1)) (bmAt ms 0))
    | _ => false) &&
  (match env.find? kR with
    | some (.ctorInfo cv 1 0) =>
      decide (cv.type = .forallE natK (leApp kLe (.bvar 0) (.bvar 0)) (bmAt (piMetas 1 cv.type) 0))
    | _ => false) &&
  (match env.find? kS with
    | some (.ctorInfo cv 1 2) =>
      let ms := piMetas 3 cv.type
      decide (cv.type = .forallE natK (.forallE natK (.forallE (leApp kLe (.bvar 1) (.bvar 0))
        (leApp kLe (.bvar 2) (.app (.const natSuccName []) (.bvar 1))) (bmAt ms 2)) (bmAt ms 1))
        (bmAt ms 0))
    | _ => false)

/-- **The bridge, exactly** (`BridgeStored`): the theorem's statement is `bridgeK` over the keys and
the role key of `Nat.mod`, `Nat.le` as read, the keys the statement names stored. -/
def bridgeB (tk : TowKeys) (W S : Nat) (kThm kR kS : KKey) : Bool :=
  (match env.find? kThm with
    | some (.thmInfo cv _) =>
      let ms := piMetas 2 cv.type
      decide (cv.type = bridgeK tk W S (bmAt ms 0) (bmAt ms 1))
    | _ => false) &&
  natLeB env tk.le kR kS &&
  [tk.ofNat, tk.u, tk.b, tk.f, primKey .mod].all (keyStoredB env) &&
  decide (0 < S)

/-- An inductive `Nat → Sort _` with a graph-regime binder, no level parameter anywhere. -/
def famB (k : KKey) : Bool :=
  match env.find? k with
  | some (.indInfo cv _) =>
    match cv.type with
    | .forallE A (.sort _) m =>
      decide (cv.levelParams = [] ∧ A = natK ∧ m.pw = .never ∧ cv.type.hasLevelParam = false)
    | _ => false
  | none => false
  | some _ => false

/-- A projection-table entry of the given constructor and counts whose structure is never a
proposition. -/
def projEntryB (e : ProjEntry .anon) (kC : KKey) (np nf : Nat) : Bool :=
  decide (e.ctor = kC ∧ e.numParams = np ∧ e.numFields = nf) &&
    match e.structSort with
    | .succ _ => true
    | _ => false

/-- A closed type without level parameters. -/
def closedTyB (T : KExpr) : Bool :=
  bvarsLt 0 T && !T.hasLevelParam && T.allLevelParamsDefined []

/-- `LT.lt`'s type: four graph-regime `∀`s ending in `Sort 0`. -/
def lt4B : KExpr → Bool
  | .forallE _ (.forallE _ (.forallE _ (.forallE _ (.sort .zero) m4) m3) m2) m1 =>
    decide (m1.pw = .never ∧ m2.pw = .never ∧ m3.pw = .never ∧ m4.pw = .never)
  | _ => false

/-- **The tower's stored shapes** (`TowerStored`), at the keys `ta`. -/
def towerB (tk : TowKeys) (ta : TowAux) : Bool :=
  famB env ta.bv && famB env ta.fin &&
  (match env.findProj? ta.bv 0 with
    | some e => projEntryB e tk.b 1 1
    | none => false) &&
  (match env.findProj? ta.fin 0, env.findProj? ta.fin 1 with
    | some e0, some e1 => projEntryB e0 tk.f 1 2 && projEntryB e1 tk.f 1 2 && decide (e0.off = e1.off)
    | _, _ => false) &&
  (match env.find? tk.u with
    | some (.ctorInfo cv 0 1) =>
      match cv.type with
      | .forallE (.app (.const kbv []) N8) _ m =>
        decide (cv.levelParams = [] ∧ kbv = ta.bv ∧
          cv.type = piTele [(.app (.const ta.bv []) N8, m)] (.const tk.ty []) ∧ m.pw = .never) &&
          closedTyB cv.type
      | _ => false
    | _ => false) &&
  (match env.find? tk.b with
    | some (.ctorInfo cv 1 1) =>
      match cv.type with
      | .forallE _ (.forallE (.app (.const _ []) Pe) _ m2) m1 =>
        decide (cv.levelParams = [] ∧
          cv.type = piTele [(natK, m1), (.app (.const ta.fin []) Pe, m2)]
            (.app (.const ta.bv []) (.bvar 1)) ∧ m1.pw = .never ∧ m2.pw = .never) &&
          closedTyB cv.type &&
          (match env.find? ta.toFin with
            | some (.defnInfo cvF val _) =>
              let ls := lamMetas 2 val
              let ms := piMetas 2 cvF.type
              decide (val = .lam natK (.lam (.app (.const ta.bv []) (.bvar 0)) (.proj ta.bv 0 (.bvar 0))
                  (bmAt ls 1)) (bmAt ls 0) ∧ cvF.levelParams = [] ∧
                cvF.type = .forallE natK (.forallE (.app (.const ta.bv []) (.bvar 0))
                  ((Expr.app (.const ta.fin []) Pe).liftLooseBVars 1 0) (bmAt ms 1)) (bmAt ms 0))
            | _ => false)
      | _ => false
    | _ => false) &&
  (match env.find? tk.f with
    | some (.ctorInfo cv 1 2) =>
      match cv.type with
      | .forallE _ (.forallE _ (.forallE
          (.app (.app (.app (.app (.const _ ls) a1) a2) (.bvar 0)) (.bvar 1)) _ m3) m2) m1 =>
        decide (cv.levelParams = [] ∧
          cv.type = piTele [(natK, m1), (natK, m2), (ltSpine ta ls a1 a2, m3)]
            (.app (.const ta.fin []) (.bvar 2)) ∧
          m1.pw = .never ∧ m2.pw = .never ∧ m3.pw = .never) &&
          closedTyB cv.type &&
          (match env.find? ta.lt with
            | some ci => decide (ls.length = ci.toConstantVal.levelParams.length) &&
                lt4B ci.toConstantVal.type
            | none => false)
      | _ => false
    | _ => false)

/-- `BitVec.toFin`'s key: the first stored definition of the projection function's value shape
(a candidate only: `towerB` decides it by the key). -/
def toFinKey? (kbv : KKey) : Option KKey :=
  env.consts.findSome? fun ci =>
    match ci with
    | .defnInfo cv (.lam A (.lam B (.proj s 0 (.bvar 0)) _) _) _ =>
      if decide (A = natK ∧ B = .app (.const kbv []) (.bvar 0) ∧ s = kbv) then some cv.name else none
    | _ => none

/-- The tower's other keys, read off the constructors' stored types (`BitVec` from `ofBitVec`'s
domain, `Fin` from `ofFin`'s field domain, `LT.lt` from `Fin.mk`'s proof domain) and the search for
`BitVec.toFin`. -/
def towAux? (tk : TowKeys) : Option TowAux := do
  let kbv ← match env.find? tk.u with
    | some (.ctorInfo cv _ _) =>
      match cv.type with
      | .forallE (.app (.const k _) _) _ _ => some k
      | _ => none
    | _ => none
  let kfin ← match env.find? tk.b with
    | some (.ctorInfo cv _ _) =>
      match cv.type with
      | .forallE _ (.forallE (.app (.const k _) _) _ _) _ => some k
      | _ => none
    | _ => none
  let klt ← match env.find? tk.f with
    | some (.ctorInfo cv _ _) =>
      match cv.type with
      | .forallE _ (.forallE _ (.forallE (.app (.app (.app (.app (.const k _) _) _) _) _) _ _) _) _ =>
        some k
      | _ => none
    | _ => none
  let ktf ← toFinKey? env kbv
  pure ⟨kbv, kfin, ktf, klt⟩

end Deciders

section Program

variable (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat) (Sl : List CId)

/-- The keys of a width's tower, from the program's pins. -/
def towKeys? (w : Width) : Option TowKeys := do
  let cT ← IxCC.Src.Table.pinnedId p (p.known.pins.wordTypes.lookup w)
  let cO ← IxCC.Src.Table.wordOpId p w .ofNat
  let cU ← p.wordCtor? w
  let cB ← p.known.bitVecOfFin
  let cF ← p.known.finMk
  let cL ← IxCC.Src.Table.pinnedId p p.known.pins.natLe
  pure ⟨κ cT, κ cO, κ cU, κ cB, κ cF, κ cL⟩

/-- The bridge theorem of a width's `ofNat` entry, and `Nat.le`'s two constructors (the program's
declaration of the pinned `Nat.le`). -/
def bridgeKeys? (w : Width) : Option (KKey × KKey × KKey) := do
  let cO ← IxCC.Src.Table.wordOpId p w .ofNat
  let thmO ← match p.table.resolveOf cO with
    | some (.word _ .ofNat thm) => some thm
    | _ => none
  let cL ← IxCC.Src.Table.pinnedId p p.known.pins.natLe
  match p.decl? cL with
  | some (.induct _ _ _ _ _ [cR, cS]) => some (κ thmO, κ cR, κ cS)
  | _ => none

/-- The tower's constructors in `Sl`, without level parameters. -/
def towInSB (w : Width) : Bool :=
  [p.wordCtor? w, p.known.bitVecOfFin, p.known.finMk].all fun o =>
    match o with
    | some c => decide (c ∈ Sl ∧ lpsOf c = [])
    | none => false

/-- **A width's facts** (`WidthFacts`). -/
def widthB (w : Width) : Bool :=
  match towKeys? p κ w, bridgeKeys? p κ w with
  | some tk, some (kB, kR, kS) =>
    bridgeB env tk w.bits w.size kB kR kS &&
    (match towAux? env tk with
      | some ta => towerB env tk ta
      | none => false) &&
    towInSB p lpsOf Sl w
  | _, _ => false

/-- A word head stored without level parameters, with a binder for every argument. -/
def headB (k : KKey) (op : WordOp) : Bool :=
  match env.find? k with
  | some ci => decide (ci.toConstantVal.levelParams = [] ∧ op.arity ≤ kPis ci.toConstantVal.type)
  | none => false

/-- **An entry's statement** (`WordStmt`): at `ofNat` the operation is the bridge's (its result width
its own); otherwise the operation has a formula, whose `Nat` operations are stored, and the theorem's
statement is exactly `wordStmtK`. -/
def wordStmtB (kc kThm : KKey) (w : Width) (op : WordOp) (tk tk' : TowKeys) : Bool :=
  if op = .ofNat then decide (kc = tk.ofNat ∧ tk' = tk)
  else
    match spec w op with
    | some f =>
      f.ops.all (fun o => keyStoredB env (primKey o)) &&
      (match env.find? kThm with
        | some (.thmInfo cv _) =>
          let ms := piMetas 2 cv.type
          decide (cv.type = wordStmtK kc op tk tk' f (bmAt ms 0) (bmAt ms 1))
        | _ => false)
    | none => false

/-- **One entry's facts** (`WordEntryFacts`), the widths' decided once (`wok`). -/
def wordEntryB (wok : Width → Bool) (c : CId) (w : Width) (op : WordOp) (thm : CId) : Bool :=
  headB env (κ c) op && eqBasisB env && wok w && wok (op.resultWidth w) &&
  match towKeys? p κ w, towKeys? p κ (op.resultWidth w) with
  | some tk, some tk' => wordStmtB env (κ c) (κ thm) w op tk tk'
  | _, _ => false

/-- The four widths' facts, decided once. -/
def widthTable : List (Width × Bool) := Width.all.map fun w => (w, widthB p env κ lpsOf Sl w)

/-- **The word check** (`WordFacts`, fail-closed): every word entry of `Sl` has its facts. -/
def wordB : Bool :=
  let tab := widthTable p env κ lpsOf Sl
  let wok : Width → Bool := fun w => (tab.lookup w).getD false
  Sl.all fun c =>
    match p.table.resolveOf c with
    | some (.word w op thm) => wordEntryB p env κ wok c w op thm
    | _ => true

end Program

/-! ## Soundness -/

section Sound

variable {env : KEnv}

theorem keyStored_of {k : KKey} (h : keyStoredB env k = true) : KeyStored env k := by
  unfold keyStoredB at h
  split at h
  · rename_i ci hf
    exact ⟨ci, hf, of_decide_eq_true h⟩
  · cases h

theorem natLe_of {kLe kR kS : KKey} (h : natLeB env kLe kR kS = true) : NatLeBasis env kLe kR kS := by
  simp only [natLeB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · split at h1
    · rename_i cv caps hf
      obtain ⟨hl, ht⟩ := of_decide_eq_true h1
      exact ⟨cv, caps, _, _, hf, hl, ht⟩
    · cases h1
  · split at h2
    · rename_i cv hf
      exact ⟨cv, _, hf, of_decide_eq_true h2⟩
    · cases h2
  · split at h3
    · rename_i cv hf
      exact ⟨cv, _, _, _, hf, of_decide_eq_true h3⟩
    · cases h3

theorem bridge_of {tk : TowKeys} {W S : Nat} {kThm kR kS : KKey}
    (h : bridgeB env tk W S kThm kR kS = true) : BridgeStored env tk W S kThm kR kS := by
  simp only [bridgeB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, natLe_of h2, fun k hk => keyStored_of (List.all_eq_true.mp h3 k hk),
    of_decide_eq_true h4⟩
  split at h1
  · rename_i cv pf hf
    exact ⟨cv, pf, _, _, hf, of_decide_eq_true h1⟩
  · cases h1

theorem fam_of {k : KKey} (h : famB env k = true) :
    ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon) (u : Level) (m : BinderMeta),
      env.find? k = some (.indInfo cv caps) ∧ cv.levelParams = [] ∧
      cv.type = .forallE natK (.sort u) m ∧ m.pw = .never ∧ cv.type.hasLevelParam = false := by
  unfold famB at h
  split at h
  · rename_i cv caps hf
    split at h
    · rename_i A u m ht
      obtain ⟨hl, rfl, hm, hlp⟩ := of_decide_eq_true h
      exact ⟨cv, caps, u, m, hf, hl, ht, hm, hlp⟩
    · cases h
  · cases h
  · cases h

theorem projEntry_of {e : ProjEntry .anon} {kC : KKey} {np nf : Nat}
    (h : projEntryB e kC np nf = true) :
    e.ctor = kC ∧ e.numParams = np ∧ e.numFields = nf ∧ ∀ ψ, Level.eval ψ e.structSort ≠ 0 := by
  simp only [projEntryB, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨a, b, c⟩ := of_decide_eq_true h1
  refine ⟨a, b, c, fun ψ => ?_⟩
  split at h2
  · rename_i l hl
    rw [hl]
    simp [Level.eval]
  · cases h2

theorem closedTy_of {T : KExpr} (h : closedTyB T = true) :
    bvarsLt 0 T = true ∧ T.hasLevelParam = false ∧ T.allLevelParamsDefined [] = true := by
  simp only [closedTyB, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lt4_of {T : KExpr} (h : lt4B T = true) :
    ∃ bs : List (KExpr × BinderMeta), T = piTele bs (.sort .zero) ∧ bs.length = 4 ∧
      ∀ bm ∈ bs, bm.2.pw = .never := by
  unfold lt4B at h
  split at h
  · rename_i A1 A2 A3 A4 m4 m3 m2 m1
    obtain ⟨h1, h2, h3, h4⟩ := of_decide_eq_true h
    refine ⟨[(A1, m1), (A2, m2), (A3, m3), (A4, m4)], rfl, rfl, ?_⟩
    intro bm hbm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbm
    rcases hbm with rfl | rfl | rfl | rfl <;> assumption
  · cases h

theorem tower_of {tk : TowKeys} {ta : TowAux} (h : towerB env tk ta = true) :
    TowerStored env tk ta := by
  simp only [towerB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hbv, hfin⟩, hpb⟩, hpf⟩, hu⟩, hb⟩, hf⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fam_of hbv
  · split at hpb
    · rename_i e he
      obtain ⟨a, b, c, d⟩ := projEntry_of hpb
      exact ⟨e, he, a, b, c, d⟩
    · cases hpb
  · exact fam_of hfin
  · split at hpf
    · rename_i e0 e1 he0 he1
      simp only [Bool.and_eq_true] at hpf
      obtain ⟨⟨h0, h1⟩, hoff⟩ := hpf
      obtain ⟨a0, b0, c0, d0⟩ := projEntry_of h0
      obtain ⟨a1, b1, c1, d1⟩ := projEntry_of h1
      refine ⟨e0.off, fun i hi => ?_⟩
      rcases i with _ | _ | i
      · exact ⟨e0, he0, a0, b0, c0, rfl, d0⟩
      · exact ⟨e1, he1, a1, b1, c1, (of_decide_eq_true hoff).symm, d1⟩
      · omega
    · cases hpf
  · split at hu
    · rename_i cv hfu
      split at hu
      · rename_i kbv N8 C m hty
        simp only [Bool.and_eq_true] at hu
        obtain ⟨h1, h2⟩ := hu
        obtain ⟨hl, -, ht, hm⟩ := of_decide_eq_true h1
        obtain ⟨c1, c2, c3⟩ := closedTy_of h2
        exact ⟨cv, N8, m, hfu, hl, ht, hm, c1, c2, c3⟩
      · cases hu
    · cases hu
  · split at hb
    · rename_i cv hfb
      split at hb
      · rename_i A k0 Pe C m2 m1 hty
        simp only [Bool.and_eq_true] at hb
        obtain ⟨⟨h1, h2⟩, h3⟩ := hb
        obtain ⟨hl, ht, hm1, hm2⟩ := of_decide_eq_true h1
        obtain ⟨c1, c2, c3⟩ := closedTy_of h2
        split at h3
        · rename_i cvF val hint hff
          obtain ⟨hv, hlF, htF⟩ := of_decide_eq_true h3
          rw [hv] at hff
          exact ⟨cv, Pe, m1, m2, hfb, hl, ht, hm1, hm2, c1, c2, c3, cvF, hint, _, _, _, _, hff, hlF,
            htF⟩
        · cases h3
      · cases hb
    · cases hb
  · split at hf
    · rename_i cv hff
      split at hf
      · rename_i A1 A2 k0 ls a1 a2 C m3 m2 m1 hty
        simp only [Bool.and_eq_true] at hf
        obtain ⟨⟨h1, h2⟩, h3⟩ := hf
        obtain ⟨hl, ht, hm1, hm2, hm3⟩ := of_decide_eq_true h1
        obtain ⟨c1, c2, c3⟩ := closedTy_of h2
        split at h3
        · rename_i ci hfl
          simp only [Bool.and_eq_true] at h3
          obtain ⟨h4, h5⟩ := h3
          obtain ⟨bs, hbs, hbl, hbn⟩ := lt4_of h5
          exact ⟨cv, ls, a1, a2, m1, m2, m3, hff, hl, ht, hm1, hm2, hm3, c1, c2, c3, ci, bs, hfl,
            of_decide_eq_true h4, hbs, hbl, hbn⟩
        · cases h3
      · cases hf
    · cases hf

end Sound

section SoundProgram

variable {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat} {Sl : List CId}

theorem towPins_of {w : Width} {tk : TowKeys} (h : towKeys? p κ w = some tk) : TowPins p κ w tk := by
  simp only [towKeys?, Option.bind_eq_bind, Option.pure_def] at h
  cases h1 : IxCC.Src.Table.pinnedId p (p.known.pins.wordTypes.lookup w) <;> rw [h1] at h <;>
    simp only [Option.bind_none, Option.bind_some, reduceCtorEq] at h
  cases h2 : IxCC.Src.Table.wordOpId p w .ofNat <;> rw [h2] at h <;>
    simp only [Option.bind_none, Option.bind_some, reduceCtorEq] at h
  cases h3 : p.wordCtor? w <;> rw [h3] at h <;>
    simp only [Option.bind_none, Option.bind_some, reduceCtorEq] at h
  cases h4 : p.known.bitVecOfFin <;> rw [h4] at h <;>
    simp only [Option.bind_none, Option.bind_some, reduceCtorEq] at h
  cases h5 : p.known.finMk <;> rw [h5] at h <;>
    simp only [Option.bind_none, Option.bind_some, reduceCtorEq] at h
  cases h6 : IxCC.Src.Table.pinnedId p p.known.pins.natLe <;> rw [h6] at h <;>
    simp only [Option.bind_none, Option.bind_some, reduceCtorEq, Option.some.injEq] at h
  subst h
  exact ⟨⟨_, h3, rfl⟩, ⟨_, h4, rfl⟩, ⟨_, h5, rfl⟩⟩

theorem towIn_of {w : Width} (h : towInSB p lpsOf Sl w = true) :
    ∀ c, (p.wordCtor? w = some c ∨ p.known.bitVecOfFin = some c ∨ p.known.finMk = some c) →
      c ∈ Sl ∧ lpsOf c = [] := by
  intro c hc
  have hall := List.all_eq_true.mp h
  have key : ∀ o, o = some c → o ∈ [p.wordCtor? w, p.known.bitVecOfFin, p.known.finMk] →
      c ∈ Sl ∧ lpsOf c = [] := by
    intro o ho hm
    have := hall o hm
    subst ho
    exact of_decide_eq_true this
  rcases hc with hc | hc | hc
  · exact key _ hc (by simp)
  · exact key _ hc (by simp)
  · exact key _ hc (by simp)

theorem width_of {w : Width} {tk : TowKeys} (h : widthB p env κ lpsOf Sl w = true)
    (hk : towKeys? p κ w = some tk) : WidthFacts p env κ lpsOf (· ∈ Sl) w tk := by
  unfold widthB at h
  rw [hk] at h
  split at h
  · rename_i tk0 kB kR kS heq1 heq2
    cases heq1
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨towPins_of hk, ⟨kB, kR, kS, bridge_of h1⟩, ?_, towIn_of h3⟩
    split at h2
    · rename_i ta _
      exact ⟨ta, tower_of h2⟩
    · cases h2
  · cases h

theorem head_of {k : KKey} {op : WordOp} (h : headB env k op = true) :
    ∃ ci : ConstantInfo .anon, env.find? k = some ci ∧ ci.toConstantVal.levelParams = [] ∧
      op.arity ≤ kPis ci.toConstantVal.type := by
  unfold headB at h
  split at h
  · rename_i ci hf
    obtain ⟨a, b⟩ := of_decide_eq_true h
    exact ⟨ci, hf, a, b⟩
  · cases h

theorem stmt_of {kc kThm : KKey} {w : Width} {op : WordOp} {tk tk' : TowKeys}
    (h : wordStmtB env kc kThm w op tk tk' = true) : WordStmt env kc kThm w op tk tk' := by
  unfold wordStmtB at h
  by_cases hO : op = .ofNat
  · rw [ite_eq_left hO] at h
    obtain ⟨a, b⟩ := of_decide_eq_true h
    exact .inl ⟨hO, a, b⟩
  · rw [ite_eq_right hO] at h
    split at h
    · rename_i f hf
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      refine .inr ⟨hO, f, hf, fun o ho => keyStored_of (List.all_eq_true.mp h1 o ho), ?_⟩
      split at h2
      · rename_i cv pf hft
        exact ⟨cv, pf, _, _, hft, of_decide_eq_true h2⟩
      · cases h2
    · cases h

theorem widthTable_lookup (w : Width) :
    (widthTable p env κ lpsOf Sl).lookup w = some (widthB p env κ lpsOf Sl w) := by
  cases w <;> rfl

/-- **The word check is sound**: it establishes the word clause. -/
theorem wordFacts_of_check (h : wordB p env κ lpsOf Sl = true) :
    WordFacts p env κ lpsOf (· ∈ Sl) := by
  intro c w op thm hc hr
  unfold wordB at h
  have h1 := List.all_eq_true.mp h c hc
  simp only [hr] at h1
  unfold wordEntryB at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨hh, hE⟩, hw⟩, hw'⟩, hs⟩ := h1
  have hwok : ∀ w, (fun w => ((widthTable p env κ lpsOf Sl).lookup w).getD false) w = true →
      widthB p env κ lpsOf Sl w = true := by
    intro w hw
    simpa [widthTable_lookup] using hw
  split at hs
  · rename_i tk tk' hk hk'
    exact ⟨head_of hh, eqBasis_of_check hE, tk, tk', width_of (hwok _ hw) hk,
      width_of (hwok _ hw') hk', stmt_of hs⟩
  · cases hs

end SoundProgram

end IxCC.Grounding
