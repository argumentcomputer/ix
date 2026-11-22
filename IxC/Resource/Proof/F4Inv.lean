import IxC.Resource.Proof.Heap
import IxC.Resource.Proof.ModeOk
import IxC.Resource.Proof.EvalS

/-!
# F4 Simulation Invariants & Behavioral Logical Relation (`F4Inv`)

Defines the invariants connecting concrete runtime states/values (`Eval.lean` / `EvalS.lean`)
to step-free abstract states/values (`ModeOk.lean`):

1. **Base value/state predicates:** `DeepLeafUntainted`, `DeepTaintsBounded`, `ValBaseOk`,
   `NoOnceCell`, `RegsOk`, `RegsFuture`, `SameLoc`, `SameShapeOn`, `StaticStrLoc`, `ArrayExtends`,
   `ClsSafe`.
2. **Behavioral step-indexed logical relation `FunOkAt`:** indexed directly on the linear
   evaluation budget `B : Nat` via `applyOneS`, parameterized by an exclusive mutable footprint
   `OwnFoot : Nat → Prop` (empty when `onceOnly = false`). Together with `CtorFieldsOk` and
   `StOk`, proved monotone in `B`, invariant under `PreservesLocs` and `SameShapeOn` (`renew`),
   plus `FunOkAt_imm_irr`, `FunOkAt_nonCallable_*`, and `FunOkAt_once_wrap`.
3. **Region interpretation & environment simulation:** `Interp`, `InterpOk`, `RegUnique`,
   `Transferable`, `VSim`, `Sim`, `ValEnvDisj`, plus state-evolution and framing lemmas.
-/

namespace IxC.Resource.Proof

open IxC.Resource Ixon

/-! ## 1. Base Value & State Predicates -/

/-- Every value reachable from `v` (including `v` itself) satisfies `LeafUntainted` (finalized L1). -/
def DeepLeafUntainted (h : Heap) (v : Val) : Prop :=
  ∀ w, HeldBy h v w → LeafUntainted h w

/-- Every taint anywhere in `v`'s reachable graph is strictly below `bound`. -/
def DeepTaintsBounded (h : Heap) (bound : Nat) (v : Val) : Prop :=
  ∀ w, HeldBy h v w → ∀ r ∈ w.taint, r < bound

/-- Core concrete well-formedness of a runtime value `v` in state `st`. -/
def ValBaseOk (st : St) (v : Val) : Prop :=
  DeepLive st.heap v ∧
  AcyclicFrom st.heap v ∧
  DeepLeafUntainted st.heap v ∧
  DeepTaintsBounded st.heap st.nextRegion v

/-- No `.once` cell is reachable from `v` in `h`. -/
def NoOnceCell (h : Heap) (v : Val) : Prop :=
  ∀ l o, Reach h v l → h.objs[l]? = some o → ∀ t sp, o.cell ≠ .once t sp

/-- Concrete open-region well-formedness: `0` is reserved for root, open regions are distinct
and strictly below `st.nextRegion`. -/
def RegsOk (st : St) : Prop :=
  0 < st.nextRegion ∧
  st.regions.Nodup ∧
  ∀ r ∈ st.regions, 0 < r ∧ r < st.nextRegion

/-- Region monotonicity across arbitrary execution steps: `nextRegion` never shrinks and no
closed region `< st₁.nextRegion` ever re-opens. -/
def RegsFuture (st₁ st₂ : St) : Prop :=
  st₁.nextRegion ≤ st₂.nextRegion ∧
  ∀ r ∈ st₂.regions, r ∈ st₁.regions ∨ st₁.nextRegion ≤ r

/-- Two values denote the same immediate or the same heap location (ignoring cap and outer taint). -/
def SameLoc : Val → Val → Prop
  | .imm i₁, .imm i₂ => i₁ = i₂
  | .ref l₁ _ _, .ref l₂ _ _ => l₁ = l₂
  | _, _ => False

/-- Every location in `S` keeps its `CellSameShape` from `h₁` to `h₂`. -/
def SameShapeOn (S : Nat → Prop) (h₁ h₂ : Heap) : Prop :=
  ∀ l o₁, S l → h₁.objs[l]? = some o₁ → ∃ o₂, h₂.objs[l]? = some o₂ ∧ CellSameShape o₁.cell o₂.cell

/-- Append-only extension of an array (`st.statics`, `st.strs`). -/
def ArrayExtends {α : Type} (a₁ a₂ : Array α) : Prop :=
  a₁.size ≤ a₂.size ∧ ∀ i, i < a₁.size → a₂[i]? = a₁[i]?

/-- Heap locations reachable from cached statics or interned strings in `st`. -/
def StaticStrLoc (st : St) (l : Nat) : Prop :=
  (∃ r v, (r, v) ∈ st.statics.toList ∧ Reach st.heap v l) ∨
  (∃ s v, (s, v) ∈ st.strs.toList ∧ Reach st.heap v l)

/-! ### Basic lemmas for Section 1 -/

theorem DeepLive.exists_obj {h : Heap} {v : Val} {l : Nat}
    (hdl : DeepLive h v) (hr : Reach h v l) : ∃ o, h.objs[l]? = some o := by
  induction hr with
  | @here loc cap t =>
    obtain ⟨o, ho, _⟩ := hdl.self.1
    exact ⟨o, ho⟩
  | @step loc cap t o w l' ho hw _ ih =>
    exact ih (hdl.sub (HeldBy_of_mem_vals ho hw))

theorem ArrayExtends.refl {α : Type} (a : Array α) : ArrayExtends a a :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem ArrayExtends.trans {α : Type} {a₁ a₂ a₃ : Array α}
    (h12 : ArrayExtends a₁ a₂) (h23 : ArrayExtends a₂ a₃) : ArrayExtends a₁ a₃ :=
  ⟨Nat.le_trans h12.1 h23.1, fun i hi => by
    rw [h23.2 i (Nat.lt_of_lt_of_le hi h12.1), h12.2 i hi]⟩

theorem ArrayExtends.push {α : Type} (a : Array α) (x : α) : ArrayExtends a (a.push x) :=
  ⟨by simp, fun i hi => by rw [Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]⟩

theorem ArrayExtends.mem {α : Type} {a₁ a₂ : Array α} (he : ArrayExtends a₁ a₂)
    {x : α} (hx : x ∈ a₁.toList) : x ∈ a₂.toList := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hi₁ : i < a₁.size := by simpa using hi
  have h2 := he.2 i hi₁
  rw [Array.getElem?_eq_getElem hi₁] at h2
  have hi₂ : i < a₂.size := Nat.lt_of_lt_of_le hi₁ he.1
  rw [Array.getElem?_eq_getElem hi₂] at h2
  have hget : a₂[i] = a₁[i] := Option.some.inj h2
  exact List.mem_iff_getElem.mpr ⟨i, by simpa using hi₂, by simp [hget]⟩

theorem StaticStrLoc.mono {st₁ st₂ : St} {l : Nat}
    (hstat : ArrayExtends st₁.statics st₂.statics)
    (hstr : ArrayExtends st₁.strs st₂.strs)
    (hp : PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap)
    (h : StaticStrLoc st₁ l) : StaticStrLoc st₂ l := by
  rcases h with ⟨r, v, hm, hr⟩ | ⟨s, v, hm, hr⟩
  · left
    exact ⟨r, v, hstat.mem hm,
      (Reach_congr (hp.mono fun x hx => Or.inl ⟨r, v, hm, hx⟩) l).mpr hr⟩
  · right
    exact ⟨s, v, hstr.mem hm,
      (Reach_congr (hp.mono fun x hx => Or.inr ⟨s, v, hm, hx⟩) l).mpr hr⟩

/-- A heap location holding an immutable boxed number (`.num n`) cell.
Number cells are leaves: never mutated by `renew` or `ExternOk`, never in `OwnReach`,
and never part of an exclusive once-footprint. -/
def NumLoc (h : Heap) (l : Nat) : Prop :=
  ∃ o n, h.objs[l]? = some o ∧ o.cell = .num n

theorem OwnReach_not_numLoc {P : Prog} {h : Heap} {v : Val} {l : Nat}
    (hr : OwnReach P h v l) : ¬ NumLoc h l := by
  intro ⟨o, n, ho, hnum⟩
  induction hr with
  | here ho' hnn =>
    rw [ho] at ho'; cases ho'
    rcases hnn with h1 | h2
    · rw [hnum] at h1; cases h1
    · exact h2 rfl
  | step _ _ _ _ ih => exact ih ho

theorem NumLoc_congr {h₁ h₂ : Heap} {S : Nat → Prop} {l : Nat}
    (hp : PreservesLocs S h₁ h₂) (hl : S l) :
    NumLoc h₁ l ↔ NumLoc h₂ l := by
  simp only [NumLoc, hp l hl]

theorem NumLoc_sameShape {h₁ h₂ : Heap} {S : Nat → Prop} {l : Nat}
    (hsh : SameShapeOn S h₁ h₂) (hl : S l) (hlt : l < h₁.objs.size) :
    NumLoc h₁ l ↔ NumLoc h₂ l := by
  cases ho₁ : h₁.objs[l]? with
  | none => exact absurd (Array.getElem?_eq_none_iff.mp ho₁) (Nat.not_le_of_lt hlt)
  | some o₁ =>
    obtain ⟨o₂, ho₂, hcs⟩ := hsh l o₁ hl ho₁
    constructor
    · rintro ⟨o, n, ho, hnum⟩
      rw [ho₁] at ho; cases ho; rw [hnum] at hcs
      cases hc₂ : o₂.cell with
      | num m => exact ⟨o₂, m, ho₂, hc₂⟩
      | ctor _ _ | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ => rw [hc₂] at hcs; cases hcs
    · rintro ⟨o, n, ho, hnum⟩
      rw [ho₂] at ho; cases ho; rw [hnum] at hcs
      cases hc₁ : o₁.cell with
      | num m => exact ⟨o₁, m, ho₁, hc₁⟩
      | ctor _ _ | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ => rw [hc₁] at hcs; cases hcs

/-- Any newly added static/string location in `st₂` is either freshly allocated (`≥ st₁.heap.objs.size`),
already in `StaticStrLoc st₁`, or an immutable `.num` cell (e.g. a `PapArgOk` ref inside a fresh extern `.pap`). -/
def StaticStrFresh (st₁ st₂ : St) : Prop :=
  ∀ l, StaticStrLoc st₂ l → st₁.heap.objs.size ≤ l ∨ StaticStrLoc st₁ l ∨ NumLoc st₂.heap l

theorem StaticStrFresh.refl (st : St) : StaticStrFresh st st :=
  fun _ h => Or.inr (Or.inl h)

theorem StaticStrFresh.trans {st₁ st₂ st₃ : St}
    (hsz : st₁.heap.objs.size ≤ st₂.heap.objs.size)
    (hpSS : PreservesLocs (StaticStrLoc st₂) st₂.heap st₃.heap)
    (h12 : StaticStrFresh st₁ st₂) (h23 : StaticStrFresh st₂ st₃) :
    StaticStrFresh st₁ st₃ := by
  intro l h3
  rcases h23 l h3 with hnew | h2 | hnum3
  · exact Or.inl (Nat.le_trans hsz hnew)
  · rcases h12 l h2 with hnew1 | h1 | hnum2
    · exact Or.inl hnew1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ((NumLoc_congr hpSS h2).mp hnum2))
  · exact Or.inr (Or.inr hnum3)

theorem StaticStrFresh.not_staticStrLoc {st₁ st₂ : St} {l : Nat}
    (hf : StaticStrFresh st₁ st₂) (hlt : l < st₁.heap.objs.size)
    (hnot : ¬ StaticStrLoc st₁ l) (hnotNum : ¬ NumLoc st₂.heap l) :
    ¬ StaticStrLoc st₂ l := by
  intro h2
  rcases hf l h2 with hge | h1 | hnum
  · omega
  · exact hnot h1
  · exact hnotNum hnum

/-- Every `.once` cell in `h₁` stays a `.once` cell with the same capability in `h₂`
(only its `spent` flag or target contents may change). -/
def PreservesOnceShell (h₁ h₂ : Heap) : Prop :=
  ∀ (l : Nat) (o₁ : Obj) (tgt₁ : Val) (sp₁ : Bool),
    h₁.objs[l]? = some o₁ → o₁.cell = .once tgt₁ sp₁ →
    ∃ (o₂ : Obj) (tgt₂ : Val) (sp₂ : Bool),
      h₂.objs[l]? = some o₂ ∧ o₂.cap = o₁.cap ∧ o₂.cell = .once tgt₂ sp₂

theorem PreservesOnceShell.refl (h : Heap) : PreservesOnceShell h h :=
  fun _ o₁ tgt₁ sp₁ ho hcell => ⟨o₁, tgt₁, sp₁, ho, rfl, hcell⟩

theorem PreservesOnceShell.trans {h₁ h₂ h₃ : Heap}
    (h12 : PreservesOnceShell h₁ h₂) (h23 : PreservesOnceShell h₂ h₃) :
    PreservesOnceShell h₁ h₃ := by
  intro l o₁ tgt₁ sp₁ ho₁ hcell₁
  obtain ⟨o₂, tgt₂, sp₂, ho₂, hcap₂, hcell₂⟩ := h12 l o₁ tgt₁ sp₁ ho₁ hcell₁
  obtain ⟨o₃, tgt₃, sp₃, ho₃, hcap₃, hcell₃⟩ := h23 l o₂ tgt₂ sp₂ ho₂ hcell₂
  exact ⟨o₃, tgt₃, sp₃, ho₃, hcap₃.trans hcap₂, hcell₃⟩

theorem PreservesOnceShell.of_preservesLocs {h₁ h₂ : Heap}
    (hp : PreservesLocs (fun l => ∃ o tgt sp, h₁.objs[l]? = some o ∧ o.cell = .once tgt sp) h₁ h₂) :
    PreservesOnceShell h₁ h₂ := by
  intro l o₁ tgt₁ sp₁ ho₁ hcell₁
  exact ⟨o₁, tgt₁, sp₁, (hp l ⟨o₁, tgt₁, sp₁, ho₁, hcell₁⟩).trans ho₁, rfl, hcell₁⟩

theorem PreservesOnceShell.of_alloc (c : Cell) (h : Heap) :
    PreservesOnceShell h { objs := h.objs.push ⟨c, h.nextCap⟩, nextCap := h.nextCap + 1 } := by
  intro l o₁ tgt₁ sp₁ ho₁ hcell₁
  have hlt : l < h.objs.size := (Array.getElem?_eq_some_iff.mp ho₁).1
  refine ⟨o₁, tgt₁, sp₁, ?_, rfl, hcell₁⟩
  rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]
  exact ho₁

theorem PreservesOnceShell.of_setObj_once {h : Heap} {loc : Nat} {o : Obj} {t₁ t₂ : Val} {s₁ s₂ : Bool}
    (ho : h.objs[loc]? = some o) (_hc : o.cell = .once t₁ s₁) :
    PreservesOnceShell h { h with objs := h.objs.set! loc { o with cell := .once t₂ s₂ } } := by
  intro l o₁ tgt₁ sp₁ ho₁ hcell₁
  by_cases heq : l = loc
  · subst heq
    rw [ho] at ho₁; cases ho₁
    have hlt : l < h.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
    refine ⟨{ o with cell := .once t₂ s₂ }, t₂, s₂, ?_, rfl, rfl⟩
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]
    simp only [hlt, ↓reduceIte]
  · refine ⟨o₁, tgt₁, sp₁, ?_, rfl, hcell₁⟩
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm heq)]
    exact ho₁

/-- Safe shell invariant for a (possibly spent) `@once` binding: either `.imm .irr` or a live
reference to a `.once` cell whose own capability still matches. -/
def SpentOnceSafe (h : Heap) (v : Val) : Prop :=
  v = .imm .irr ∨
  ∃ loc cap t o tgt sp, v = .ref loc cap t ∧ h.objs[loc]? = some o ∧ o.cap = cap ∧ o.cell = .once tgt sp

theorem SpentOnceSafe.irr (h : Heap) : SpentOnceSafe h (.imm .irr) := Or.inl rfl

theorem SpentOnceSafe.of_once {h : Heap} {loc cap : Nat} {t : List Nat} {o : Obj} {tgt : Val} {sp : Bool}
    (ho : h.objs[loc]? = some o) (hcap : o.cap = cap) (hcell : o.cell = .once tgt sp) :
    SpentOnceSafe h (.ref loc cap t) :=
  Or.inr ⟨loc, cap, t, o, tgt, sp, rfl, ho, hcap, hcell⟩

theorem SpentOnceSafe.of_preservesOnceShell {h₁ h₂ : Heap} {v : Val}
    (hp : PreservesOnceShell h₁ h₂) (hs : SpentOnceSafe h₁ v) : SpentOnceSafe h₂ v := by
  rcases hs with rfl | ⟨loc, cap, t, o₁, tgt₁, sp₁, rfl, ho₁, hcap₁, hcell₁⟩
  · exact Or.inl rfl
  · obtain ⟨o₂, tgt₂, sp₂, ho₂, hcap₂, hcell₂⟩ := hp loc o₁ tgt₁ sp₁ ho₁ hcell₁
    exact Or.inr ⟨loc, cap, t, o₂, tgt₂, sp₂, rfl, ho₂, hcap₂.trans hcap₁, hcell₂⟩

theorem SpentOnceSafe.addTaint {h : Heap} {s : Nat} {v : Val}
    (hs : SpentOnceSafe h v) : SpentOnceSafe h (addTaint s v) := by
  rcases hs with rfl | ⟨loc, cap, t, o, tgt, sp, rfl, ho, hcap, hcell⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨loc, cap, _, o, tgt, sp, rfl, ho, hcap, hcell⟩

theorem SpentOnceSafe.renameTaint {h : Heap} {s cur : Nat} {v : Val}
    (hs : SpentOnceSafe h v) : SpentOnceSafe h (renameTaint s cur v) := by
  rcases hs with rfl | ⟨loc, cap, t, o, tgt, sp, rfl, ho, hcap, hcell⟩
  · exact Or.inl rfl
  · simp only [IxC.Resource.renameTaint]
    split
    · exact Or.inr ⟨loc, cap, _, o, tgt, sp, rfl, ho, hcap, hcell⟩
    · exact Or.inr ⟨loc, cap, t, o, tgt, sp, rfl, ho, hcap, hcell⟩

theorem SameLoc.refl : ∀ v, SameLoc v v
  | .imm _ => rfl
  | .ref _ _ _ => rfl

theorem SameLoc.symm {v₁ v₂ : Val} (h : SameLoc v₁ v₂) : SameLoc v₂ v₁ := by
  cases v₁ <;> cases v₂ <;> simp [SameLoc] at h ⊢ <;> exact h.symm

theorem SameLoc.trans {v₁ v₂ v₃ : Val} (h1 : SameLoc v₁ v₂) (h2 : SameLoc v₂ v₃) : SameLoc v₁ v₃ := by
  cases v₁ <;> cases v₂ <;> cases v₃ <;> simp [SameLoc] at h1 h2 ⊢ <;> exact h1.trans h2

theorem SameLoc.of_valSameShape {v₁ v₂ : Val} (h : ValSameShape v₁ v₂) : SameLoc v₁ v₂ := by
  cases v₁ <;> cases v₂ <;> simp [ValSameShape, SameLoc] at h ⊢
  · exact h
  · exact h.1

theorem SameLoc.addTaint_right (s : Nat) (v : Val) : SameLoc v (addTaint s v) := by
  cases v <;> simp [addTaint, SameLoc]

theorem SameLoc.renameTaint_right (s cur : Nat) (v : Val) : SameLoc v (renameTaint s cur v) := by
  cases v with
  | imm _ => rfl
  | ref l c t =>
    simp only [renameTaint]
    split <;> rfl

theorem SameShapeOn.refl (S : Nat → Prop) (h : Heap) : SameShapeOn S h h :=
  fun _ o₁ _ ho => ⟨o₁, ho, CellSameShape.refl _⟩

theorem SameShapeOn.mono {S₁ S₂ : Nat → Prop} {h₁ h₂ : Heap}
    (hsub : ∀ l, S₁ l → S₂ l) (h : SameShapeOn S₂ h₁ h₂) : SameShapeOn S₁ h₁ h₂ :=
  fun l o₁ hs ho => h l o₁ (hsub l hs) ho

theorem SameShapeOn.of_preserves {S : Nat → Prop} {h₁ h₂ : Heap}
    (hp : PreservesLocs S h₁ h₂) : SameShapeOn S h₁ h₂ :=
  fun l o₁ hs ho => ⟨o₁, (hp l hs).trans ho, CellSameShape.refl _⟩

theorem SameShapeOn.of_heapSameShape (S : Nat → Prop) {h₁ h₂ : Heap}
    (hh : HeapSameShape h₁ h₂) : SameShapeOn S h₁ h₂ := by
  intro l o₁ _ ho₁
  obtain ⟨o₂, ho₂, hcs⟩ := hh.getElem?_some ho₁
  exact ⟨o₂, ho₂, hcs⟩

theorem Reach_of_sameShapeOn {h₁ h₂ : Heap} {v₁ v₂ : Val} {l : Nat}
    (hs : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hloc : SameLoc v₁ v₂)
    (hr : Reach h₁ v₁ l) : Reach h₂ v₂ l := by
  induction hr generalizing v₂ with
  | @here loc cap t =>
    cases v₂ with
    | imm _ => cases hloc
    | ref l₂ c₂ t₂ =>
      simp only [SameLoc] at hloc
      subst hloc
      exact .here
  | @step loc cap t o₁ w₁ l' ho₁ hw₁ _ ih =>
    cases v₂ with
    | imm _ => cases hloc
    | ref l₂ c₂ t₂ =>
      simp only [SameLoc] at hloc
      subst hloc
      obtain ⟨o₂, ho₂, hcs⟩ := hs loc o₁ .here ho₁
      obtain ⟨w₂, hw₂, hvs⟩ := hcs.vals_fwd hw₁
      have hs' : SameShapeOn (Reach h₁ w₁) h₁ h₂ :=
        hs.mono fun x hx => .step ho₁ hw₁ hx
      exact .step ho₂ hw₂ (ih hs' (SameLoc.of_valSameShape hvs))

theorem Reach_of_sameShapeOn_rev {h₁ h₂ : Heap} {v₁ v₂ : Val} {l : Nat}
    (hdl : DeepLive h₁ v₁) (hs : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hloc : SameLoc v₁ v₂)
    (hr : Reach h₂ v₂ l) : Reach h₁ v₁ l := by
  induction hr generalizing v₁ with
  | @here loc cap t =>
    cases v₁ with
    | imm _ => cases hloc
    | ref l₁ c₁ t₁ =>
      simp only [SameLoc] at hloc
      subst hloc
      exact .here
  | @step loc cap t o₂ w₂ l' ho₂ hw₂ _ ih =>
    cases v₁ with
    | imm _ => cases hloc
    | ref l₁ c₁ t₁ =>
      simp only [SameLoc] at hloc
      subst hloc
      obtain ⟨o₁, ho₁, _⟩ := hdl.self.1
      obtain ⟨o₂', ho₂', hcs⟩ := hs l₁ o₁ .here ho₁
      rw [ho₂] at ho₂'
      cases ho₂'
      obtain ⟨w₁, hw₁, hvs⟩ := hcs.symm.vals_fwd hw₂
      have hdl' : DeepLive h₁ w₁ := hdl.sub (HeldBy_of_mem_vals ho₁ hw₁)
      have hs' : SameShapeOn (Reach h₁ w₁) h₁ h₂ := hs.mono fun x hx => .step ho₁ hw₁ hx
      exact .step ho₁ hw₁ (ih hdl' hs' (SameLoc.of_valSameShape hvs.symm))

theorem SameShapeOn.trans_reach {h₁ h₂ h₃ : Heap} {v₁ v₂ : Val}
    (hs12 : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hloc : SameLoc v₁ v₂)
    (hs23 : SameShapeOn (Reach h₂ v₂) h₂ h₃) :
    SameShapeOn (Reach h₁ v₁) h₁ h₃ := by
  intro l o₁ hr₁ ho₁
  obtain ⟨o₂, ho₂, hcs12⟩ := hs12 l o₁ hr₁ ho₁
  have hr₂ : Reach h₂ v₂ l := Reach_of_sameShapeOn hs12 hloc hr₁
  obtain ⟨o₃, ho₃, hcs23⟩ := hs23 l o₂ hr₂ ho₂
  exact ⟨o₃, ho₃, hcs12.trans hcs23⟩

theorem RegsFuture.refl (st : St) : RegsFuture st st :=
  ⟨Nat.le_refl _, fun _ hr => Or.inl hr⟩

theorem RegsFuture.trans {st₁ st₂ st₃ : St} (h12 : RegsFuture st₁ st₂) (h23 : RegsFuture st₂ st₃) :
    RegsFuture st₁ st₃ := by
  refine ⟨Nat.le_trans h12.1 h23.1, fun r hr => ?_⟩
  rcases h23.2 r hr with hr2 | hge2
  · exact h12.2 r hr2
  · exact Or.inr (Nat.le_trans h12.1 hge2)

theorem RegsFuture.same_regions {st₁ st₂ : St} (hnr : st₁.nextRegion ≤ st₂.nextRegion)
    (hreg : st₂.regions = st₁.regions) : RegsFuture st₁ st₂ :=
  ⟨hnr, fun r hr => Or.inl (by rwa [← hreg])⟩

theorem RegsFuture.openRegion (st : St) :
    RegsFuture st { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions } := by
  refine ⟨Nat.le_succ _, fun r hr => ?_⟩
  rcases List.mem_cons.mp hr with rfl | hr'
  · exact Or.inr (Nat.le_refl _)
  · exact Or.inl hr'

theorem RegsFuture.closeRegion (st : St) (s : Nat) :
    RegsFuture st { st with regions := st.regions.filter (· != s) } :=
  ⟨Nat.le_refl _, fun _ hr => Or.inl (List.mem_filter.mp hr).1⟩

theorem RegsOk.openRegion {st : St} (hok : RegsOk st) :
    RegsOk { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions } := by
  obtain ⟨hpos, hnd, hlt⟩ := hok
  have hnot : ¬ (st.nextRegion ∈ st.regions) := fun hm => Nat.lt_irrefl _ (hlt _ hm).2
  refine ⟨Nat.lt_succ_of_lt hpos, List.nodup_cons.mpr ⟨hnot, hnd⟩, fun r hr => ?_⟩
  rcases List.mem_cons.mp hr with rfl | hr'
  · exact ⟨hpos, Nat.lt_succ_self _⟩
  · have := hlt r hr'; exact ⟨this.1, Nat.lt_succ_of_lt this.2⟩

theorem RegsOk.closeRegion {st : St} (hok : RegsOk st) (s : Nat) :
    RegsOk { st with regions := st.regions.filter (· != s) } := by
  obtain ⟨hpos, hnd, hlt⟩ := hok
  exact ⟨hpos, hnd.filter _, fun r hr => hlt r (List.mem_filter.mp hr).1⟩

theorem RegsOk_init (h : Heap) : RegsOk { heap := h } :=
  ⟨Nat.zero_lt_one, List.nodup_nil, fun _ hm => by cases hm⟩

theorem DeepLeafUntainted.sub {h : Heap} {v w : Val}
    (hd : DeepLeafUntainted h v) (hw : HeldBy h v w) : DeepLeafUntainted h w :=
  fun u hu => hd u (HeldBy.trans hw hu)

theorem DeepTaintsBounded.sub {h : Heap} {b : Nat} {v w : Val}
    (hd : DeepTaintsBounded h b v) (hw : HeldBy h v w) : DeepTaintsBounded h b w :=
  fun u hu => hd u (HeldBy.trans hw hu)

theorem DeepTaintsBounded.mono {h : Heap} {b₁ b₂ : Nat} {v : Val}
    (hle : b₁ ≤ b₂) (hd : DeepTaintsBounded h b₁ v) : DeepTaintsBounded h b₂ v :=
  fun w hw r hr => Nat.lt_of_lt_of_le (hd w hw r hr) hle

theorem ValBaseOk.sub {st : St} {v w : Val} (hv : ValBaseOk st v) (hw : HeldBy st.heap v w) :
    ValBaseOk st w :=
  ⟨hv.1.sub hw, hv.2.1.sub hw, hv.2.2.1.sub hw, hv.2.2.2.sub hw⟩

theorem NoOnceCell.sub {h : Heap} {v w : Val} (hn : NoOnceCell h v) (hw : HeldBy h v w) :
    NoOnceCell h w :=
  fun l o hr ho => hn l o (Reach_of_HeldBy hw hr) ho

theorem DeepOpenUnder_of_regsFuture {h : Heap} {st₁ st₂ : St} {A : List Nat} {v : Val}
    (hb : DeepTaintsBounded h st₁.nextRegion v)
    (ho : DeepOpenUnder h st₁.regions A v)
    (hf : RegsFuture st₁ st₂) :
    DeepOpenUnder h st₂.regions A v := by
  intro w hw r hr hopen
  have hlt : r < st₁.nextRegion := hb w hw r hr
  rcases hf.2 r hopen with hin | hge
  · exact ho w hw r hr hin
  · exact absurd hlt (Nat.not_lt.mpr hge)

theorem DeepLeafUntainted_congr {h h' : Heap} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') (hd : DeepLeafUntainted h v) :
    DeepLeafUntainted h' v := by
  intro w hw
  have hw₁ : HeldBy h v w := (HeldBy_congr hp w).mp hw
  exact (LeafUntainted_congr (hp.mono fun l hl => Reach_of_HeldBy hw₁ hl)).mpr (hd w hw₁)

theorem DeepTaintsBounded_congr {h h' : Heap} {b : Nat} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') (hd : DeepTaintsBounded h b v) :
    DeepTaintsBounded h' b v :=
  fun w hw => hd w ((HeldBy_congr hp w).mp hw)

theorem ValBaseOk_congr {st st' : St} {v : Val}
    (hp : PreservesLocs (Reach st.heap v) st.heap st'.heap)
    (hnr : st.nextRegion ≤ st'.nextRegion)
    (hv : ValBaseOk st v) : ValBaseOk st' v :=
  ⟨(DeepLive_congr hp).mpr hv.1, (AcyclicFrom_congr hp).mpr hv.2.1,
   DeepLeafUntainted_congr hp hv.2.2.1,
   (DeepTaintsBounded_congr hp hv.2.2.2).mono hnr⟩

theorem NoOnceCell_congr {h h' : Heap} {v : Val}
    (hdl : DeepLive h v) (hp : PreservesLocs (Reach h v) h h') (hn : NoOnceCell h v) :
    NoOnceCell h' v := by
  intro l o hr ho
  have hr₁ : Reach h v l := (Reach_congr hp l).mp hr
  obtain ⟨o₁, ho₁⟩ := hdl.exists_obj hr₁
  have ho₁' : h'.objs[l]? = some o₁ := (hp l hr₁).trans ho₁
  rw [ho] at ho₁'
  cases ho₁'
  exact hn l o hr₁ ho₁

theorem NoOnceCell_of_sameShape {h₁ h₂ : Heap} {v₁ v₂ : Val}
    (hdl : DeepLive h₁ v₁) (hs : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hloc : SameLoc v₁ v₂)
    (hn : NoOnceCell h₁ v₁) : NoOnceCell h₂ v₂ := by
  intro l o₂ hr₂ ho₂ t sp heq
  have hr₁ : Reach h₁ v₁ l := Reach_of_sameShapeOn_rev hdl hs hloc hr₂
  obtain ⟨o₁, ho₁⟩ := hdl.exists_obj hr₁
  obtain ⟨o₂', ho₂', hcs⟩ := hs l o₁ hr₁ ho₁
  rw [ho₂] at ho₂'
  cases ho₂'
  rw [heq] at hcs
  cases hc₁ : o₁.cell with
  | once t₁ sp₁ => exact hn l o₁ hr₁ ho₁ t₁ sp₁ hc₁
  | ctor _ _ | num _ | str _ | clo _ _ _ _ _ _ | pap _ _ =>
    rw [hc₁] at hcs
    exact hcs

theorem ValBaseOk_of_sameShape {st₁ st₂ : St} {v₁ v₂ : Val}
    (hh : HeapSameShape st₁.heap st₂.heap) (hvs : ValSameShape v₁ v₂)
    (hdl₂ : DeepLive st₂.heap v₂) (hnr : st₁.nextRegion ≤ st₂.nextRegion)
    (hv₁ : ValBaseOk st₁ v₁) : ValBaseOk st₂ v₂ := by
  refine ⟨hdl₂, AcyclicFrom_of_sameShape hh hvs hv₁.2.1, fun w₂ hw₂ => (hdl₂ w₂ hw₂).2, ?_⟩
  intro w₂ hw₂ r hr
  rcases hw₂ with rfl | ⟨l, o₂, hr₂, ho₂, hmem₂⟩
  · rw [← hvs.taint_eq] at hr
    exact Nat.lt_of_lt_of_le (hv₁.2.2.2 v₁ (HeldBy.refl _ _) r hr) hnr
  · have hr₁ : Reach st₁.heap v₁ l := (Reach_iff_sameShape hh hvs l).mpr hr₂
    obtain ⟨o₁, ho₁, hcs⟩ := hh.symm.getElem?_some ho₂
    obtain ⟨w₁, hmem₁, hvsW⟩ := hcs.vals_fwd hmem₂
    rw [hvsW.taint_eq] at hr
    exact Nat.lt_of_lt_of_le (hv₁.2.2.2 w₁ (Or.inr ⟨l, o₁, hr₁, ho₁, hmem₁⟩) r hr) hnr

theorem ValBaseOk_imm (st : St) (i : Imm) : ValBaseOk st (.imm i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases hw with rfl | ⟨_, _, hr, _, _⟩
    · exact ⟨trivial, trivial⟩
    · cases hr
  · intro l o w hr _ _ _
    cases hr
  · intro w hw
    rcases hw with rfl | ⟨_, _, hr, _, _⟩
    · trivial
    · cases hr
  · intro w hw r hr
    rcases hw with rfl | ⟨_, _, hreach, _, _⟩
    · cases hr
    · cases hreach

theorem NoOnceCell_imm (h : Heap) (i : Imm) : NoOnceCell h (.imm i) :=
  fun _ _ hr => by cases hr

/-- Class safety: either `.imm .irr` (universal bottom value, safe at every class) or `ClsOk`. -/
def ClsSafe (h : Heap) (c : Cls) (v : Val) : Prop :=
  v = .imm .irr ∨ ClsOk h c v

theorem ClsSafe.of_clsOk {h : Heap} {c : Cls} {v : Val} (hc : ClsOk h c v) : ClsSafe h c v :=
  Or.inr hc

theorem ClsSafe.irr (h : Heap) (c : Cls) : ClsSafe h c (.imm .irr) :=
  Or.inl rfl

theorem ClsSafe_congr {h h' : Heap} {c : Cls} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') (hc : ClsSafe h c v) : ClsSafe h' c v := by
  rcases hc with rfl | hc
  · exact Or.inl rfl
  · exact Or.inr ((ClsOk_congr hp).mpr hc)

theorem ClsSafe_taint_nil {h : Heap} {c : Cls} {v : Val} (hne : c ≠ .val) (hc : ClsSafe h c v) :
    v.taint = [] := by
  rcases hc with rfl | hc
  · rfl
  · cases c with
    | irr => rw [hc]; rfl
    | imm => obtain ⟨_, rfl⟩ := hc; rfl
    | leaf => obtain ⟨_, _, _, _, rfl, _⟩ := hc; rfl
    | val => exact absurd rfl hne

theorem ClsSafe_deepOpenUnder_nil {h : Heap} {rs A : List Nat} {c : Cls} {v : Val}
    (hne : c ≠ .val) (hc : ClsSafe h c v) : DeepOpenUnder h rs A v := by
  rcases hc with rfl | hc
  · intro w hw r hr
    rcases hw with rfl | ⟨_, _, hreach, _, _⟩
    · cases hr
    · cases hreach
  · cases c with
    | irr =>
      rw [hc]
      intro w hw r hr
      rcases hw with rfl | ⟨_, _, hreach, _, _⟩
      · cases hr
      · cases hreach
    | imm =>
      obtain ⟨i, rfl⟩ := hc
      intro w hw r hr
      rcases hw with rfl | ⟨_, _, hreach, _, _⟩
      · cases hr
      · cases hreach
    | leaf =>
      obtain ⟨loc, cap, o, n, rfl, ho, hnum, _⟩ := hc
      intro w hw r hr
      rcases hw with rfl | ⟨l, o', hreach, ho', hmem⟩
      · cases hr
      · cases hreach with
        | here =>
          rw [ho] at ho'; cases ho'; rw [hnum] at hmem; cases hmem
        | step ho1 hmem1 _ =>
          rw [ho] at ho1; cases ho1; rw [hnum] at hmem1; cases hmem1
    | val => exact absurd rfl hne

theorem ClsSafe_not_ownReach {P : Prog} {h : Heap} {c : Cls} {v : Val} {l : Nat}
    (hne : c ≠ .val) (hc : ClsSafe h c v) : ¬ OwnReach P h v l := by
  intro hr
  rcases hc with rfl | hc
  · cases hr
  · cases c with
    | irr => rw [hc] at hr; cases hr
    | imm => obtain ⟨_, rfl⟩ := hc; cases hr
    | leaf =>
      obtain ⟨loc, cap, o, n, rfl, ho, hnum, _⟩ := hc
      cases hr with
      | here ho' hnn =>
        rw [ho] at ho'; cases ho'
        rcases hnn with h1 | h2
        · rw [hnum] at h1; cases h1
        · exact h2 rfl
      | step ho' hmem _ _ =>
        rw [ho] at ho'; cases ho'
        rw [hnum] at hmem; cases hmem
    | val => exact absurd rfl hne

theorem ClsSafe_noOnceCell {h : Heap} {c : Cls} {v : Val}
    (hne : c ≠ .val) (hc : ClsSafe h c v) : NoOnceCell h v := by
  intro l o hr ho t sp hcell
  rcases hc with rfl | hc
  · cases hr
  · cases c with
    | irr => rw [hc] at hr; cases hr
    | imm => obtain ⟨_, rfl⟩ := hc; cases hr
    | leaf =>
      obtain ⟨loc, cap, o₀, n, rfl, ho₀, hnum, _⟩ := hc
      cases hr with
      | here =>
        rw [ho₀] at ho; cases ho; rw [hnum] at hcell; cases hcell
      | step ho1 hmem1 _ =>
        rw [ho₀] at ho1; cases ho1; rw [hnum] at hmem1; cases hmem1
    | val => exact absurd rfl hne

/-! ## 2. Behavioral Step-Indexed Logical Relation `FunOkAt`, `CtorFieldsOk`, `StOk` -/

/-- Unpack an arrow skeleton (treating any non-arrow skeleton as a default `.many → .shared` arrow). -/
def arrowParts : Skel → BinderMode × Skel × ResultMode × Skel
  | .arrow m d r c => (m, d, r, c)
  | _ => (.many, .unknown, .shared, .unknown)

/-- Whether a skeleton is syntactically an `.arrow`. -/
def isArrowSkel : Skel → Bool
  | .arrow .. => true
  | _ => false

/-- Every value stored inside any `.ctor` cell reachable from `v` has `NoOnceCell` and default
`FunOkAt` with empty footprint. -/
def CtorFieldsOkWith (funOk : St → Skel → Bool → (Nat → Prop) → Val → Prop) (st : St) (v : Val) :
    Prop :=
  ∀ l o r fs w, Reach st.heap v l → st.heap.objs[l]? = some o → o.cell = .ctor r fs →
    w ∈ fs.toList → NoOnceCell st.heap w ∧ funOk st .unknown false (fun _ => False) w

/-- Runtime state invariant parameterized by `funOk` (at current budget `B`). -/
def StOkWith (P : Prog) (funOk : St → Skel → Bool → (Nat → Prop) → Val → Prop) (st : St) : Prop :=
  CapsOk st.heap ∧
  RegsOk st ∧
  (∀ r v, (r, v) ∈ st.statics.toList →
    ∃ rc rs body, P.find? r = some (.body #[] .shared rc rs body) ∧
      ValBaseOk st v ∧ ClsSafe st.heap rc v ∧
      DeepOpenUnder st.heap st.regions [] v ∧
      NoOnceCell st.heap v ∧ funOk st rs false (fun _ => False) v ∧
      CtorFieldsOkWith funOk st v) ∧
  (∀ s v, (s, v) ∈ st.strs.toList →
    ∃ loc cap o, v = .ref loc cap [] ∧ st.heap.objs[loc]? = some o ∧
      o.cap = cap ∧ o.cell = .str s)

/-- Allowed open regions on the result of `applyOne f a c`. -/
def applyResultRegs (st : St) (res : ResultMode) (c : Cls) (fRegs aRegs : List Nat) : List Nat :=
  if c != .val then []
  else match res with
    | .unique => fRegs
    | .uniqueBorrowed | .borrowed =>
      match st.regions with
      | [] => aRegs ++ fRegs
      | cur :: _ => cur :: (aRegs ++ fRegs)
    | .shared => aRegs ++ fRegs

/-- Single application followed by `conform c`, matching `EvalS.applyAllS`:
non-final steps pass `c = .val` (where `conform .val` is identity), and the final
step passes `c` followed immediately by `applyAllS ... [] c` (`conform c`). -/
def applyOneConformS (P : Prog) (ext : ExternOracle) (fuel : Nat) (f a : Val) (c : Cls) : MS Val := do
  let g ← applyOneS P ext fuel f a c
  liftM (conform c g)

/-- **Behavioral step-indexed logical relation** for callable (and non-callable) values,
indexed strictly on linear budget `B : Nat`. -/
def FunOkAt (P : Prog) (ext : ExternOracle) :
    Nat → St → Skel → Bool → (Nat → Prop) → Val → Prop
  | 0, _, _, _, _, _ => True
  | B + 1, st₀, sk, onceOnly, OwnFoot, f₀ =>
    let (m_in, dom, res, cod) := arrowParts sk
    ∀ (B_call fuel : Nat) (st : St) (f a : Val) (c : Cls)
      (Frame : Nat → Prop) (fRegs aRegs : List Nat) (aOnceOnly : Bool) (aOwnFoot : Nat → Prop),
      B_call ≤ B →
      StOkWith P (FunOkAt P ext B_call) st →
      (∀ l, StaticStrLoc st l → Frame l) →
      (∀ l, Frame l → l < st.heap.objs.size) →
      SameLoc f₀ f →
      SameShapeOn (Reach st₀.heap f₀) st₀.heap st.heap →
      RegsFuture st₀ st →
      ValBaseOk st f →
      DeepOpenUnder st.heap st.regions fRegs f →
      CtorFieldsOkWith (FunOkAt P ext B_call) st f →
      ValBaseOk st a →
      DeepOpenUnder st.heap st.regions aRegs a →
      CtorFieldsOkWith (FunOkAt P ext B_call) st a →
      (∀ l, Frame l → ¬ OwnFoot l) →
      (∀ l, Frame l → ¬ aOwnFoot l) →
      (∀ l, OwnFoot l → ¬ aOwnFoot l) →
      (∀ l, Reach st.heap f l → ¬ aOwnFoot l) →
      (∀ l, Reach st.heap a l → ¬ OwnFoot l) →
      ((∀ l, aOwnFoot l → Reach st.heap a l ∧ ¬ NumLoc st.heap l) ∧ (m_in = .erased → NoOnceCell st.heap a)) →
      (m_in ≠ .erased →
        (m_in.usage = .once → FunOkAt P ext B_call st dom aOnceOnly aOwnFoot a) ∧
        (m_in.usage ≠ .once →
          NoOnceCell st.heap a ∧ aOnceOnly = false ∧ (∀ l, ¬ aOwnFoot l) ∧
          FunOkAt P ext B_call st dom false (fun _ => False) a) ∧
        (m_in.isUnique = true →
          OwnTreeFull P st.heap a ∧
          (∀ l, OwnReach P st.heap a l → ¬ Frame l ∧ ¬ Reach st.heap f l) ∧
          (m_in.isBorrowed = false → DeepOpenUnder st.heap st.regions [] a)) ∧
        ((res = .unique ∧ c = .val ∧ (m_in = .many ∨ m_in = .once)) →
          DeepOpenUnder st.heap st.regions [] a)) →
      (∀ k, (applyOneConformS P ext fuel f a c).run (st, B_call) ≠ .error (.violation k)) ∧
      ∀ rv st' B',
        (applyOneConformS P ext fuel f a c).run (st, B_call) = .ok (rv, (st', B')) →
          ∃ (_ : B' ≤ B_call),
            StOkWith P (FunOkAt P ext B') st' ∧
            st.heap.objs.size ≤ st'.heap.objs.size ∧
            st.heap.nextCap ≤ st'.heap.nextCap ∧
            st'.regions = st.regions ∧
            st.nextRegion ≤ st'.nextRegion ∧
            ArrayExtends st.statics st'.statics ∧
            ArrayExtends st.strs st'.strs ∧
            PreservesLocs Frame st.heap st'.heap ∧
            PreservesOnceShell st.heap st'.heap ∧
            StaticStrFresh st st' ∧
            ValBaseOk st' rv ∧
            ClsSafe st'.heap c rv ∧
            DeepOpenUnder st'.heap st'.regions (applyResultRegs st res c fRegs aRegs) rv ∧
            CtorFieldsOkWith (FunOkAt P ext B') st' rv ∧
            (∀ l, Reach st'.heap rv l →
              st.heap.objs.size ≤ l ∨ Reach st.heap f l ∨ Reach st.heap a l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l) ∧
            (let resOnce := isArrowSkel cod && (onceOnly || m_in.isUnique || m_in.usage == .once)
             (resOnce = false →
               NoOnceCell st'.heap rv ∧ FunOkAt P ext B' st' cod false (fun _ => False) rv) ∧
             (resOnce = true →
               ∃ resFoot,
                 (∀ l, resFoot l → Reach st'.heap rv l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st' l ∧ ¬ NumLoc st'.heap l) ∧
                 FunOkAt P ext B' st' cod true resFoot rv)) ∧
            (res.isUnique = true ∧ c = .val →
              OwnTreeFull P st'.heap rv ∧
              (∀ l, OwnReach P st'.heap rv l → ¬ Frame l ∧ ¬ StaticStrLoc st' l) ∧
              (res = .unique → (m_in.isBorrowed = true ∨ m_in = .erased) →
                ∀ l, Reach st'.heap rv l →
                  st.heap.objs.size ≤ l ∨ Reach st.heap f l ∨ StaticStrLoc st l ∨ NumLoc st'.heap l))
termination_by B => B
decreasing_by all_goals omega

abbrev CtorFieldsOk (P : Prog) (ext : ExternOracle) (B : Nat) :=
  CtorFieldsOkWith (FunOkAt P ext B)

abbrev StOk (P : Prog) (ext : ExternOracle) (B : Nat) :=
  StOkWith P (FunOkAt P ext B)

/-! ## 3. Fundamental Properties of `FunOkAt`, `CtorFieldsOk`, `StOk` -/

theorem FunOkAt_mono {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat}
    {st : St} {sk : Skel} {onceOnly : Bool} {Foot : Nat → Prop} {f : Val}
    (hle : B₁ ≤ B₂) (hf : FunOkAt P ext B₂ st sk onceOnly Foot f) :
    FunOkAt P ext B₁ st sk onceOnly Foot f := by
  cases B₁ with
  | zero => rw [FunOkAt]; trivial
  | succ b₁ =>
    cases B₂ with
    | zero => omega
    | succ b₂ =>
      rw [FunOkAt] at hf ⊢
      intro B_call fuel st' f' a c Frame fRegs aRegs aOnce aFoot hB
      exact hf B_call fuel st' f' a c Frame fRegs aRegs aOnce aFoot (by omega)

theorem CtorFieldsOk_mono {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st : St} {v : Val}
    (hle : B₁ ≤ B₂) (hc : CtorFieldsOk P ext B₂ st v) : CtorFieldsOk P ext B₁ st v :=
  fun l o r fs w hr ho hcell hw =>
    let ⟨hno, hf⟩ := hc l o r fs w hr ho hcell hw
    ⟨hno, FunOkAt_mono hle hf⟩

theorem StOk_mono {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st : St}
    (hle : B₁ ≤ B₂) (hs : StOk P ext B₂ st) : StOk P ext B₁ st := by
  obtain ⟨hcaps, hregs, hstat, hstr⟩ := hs
  refine ⟨hcaps, hregs, ?_, hstr⟩
  intro r v hm
  obtain ⟨rc, rs, body, hfind, hbase, hcls, hopen, hno, hfun, hcf⟩ := hstat r v hm
  exact ⟨rc, rs, body, hfind, hbase, hcls, hopen, hno, FunOkAt_mono hle hfun, CtorFieldsOk_mono hle hcf⟩

theorem FunOkAt_weaken_foot {P : Prog} {ext : ExternOracle} {B : Nat}
    {st : St} {sk : Skel} {onceOnly : Bool} {Foot₁ Foot₂ : Nat → Prop} {f : Val}
    (hsub : ∀ l, Foot₁ l → Foot₂ l)
    (hf : FunOkAt P ext B st sk onceOnly Foot₁ f) :
    FunOkAt P ext B st sk onceOnly Foot₂ f := by
  cases B with
  | zero => rw [FunOkAt]; trivial
  | succ b =>
    rw [FunOkAt] at hf ⊢
    intro B_call fuel st' f' a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt hloc hsh hrf
      hfBase hfOpen hfCf haBase haOpen haCf hF1 hFa h1a hfa ha1 haNum harg
    exact hf B_call fuel st' f' a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt hloc hsh hrf
      hfBase hfOpen hfCf haBase haOpen haCf
      (fun l hF h1 => hF1 l hF (hsub l h1))
      hFa
      (fun l h1 => h1a l (hsub l h1))
      hfa
      (fun l ha h1 => ha1 l ha (hsub l h1))
      haNum
      harg

theorem FunOkAt_weaken_onceOnly {P : Prog} {ext : ExternOracle} :
    ∀ {B : Nat} {st : St} {sk : Skel} {f : Val},
      FunOkAt P ext B st sk false (fun _ => False) f →
      FunOkAt P ext B st sk true (fun _ => False) f
  | 0, _, _, _, _ => by rw [FunOkAt]; trivial
  | B + 1, st₀, sk, f₀, hf => by
    rw [FunOkAt] at hf ⊢
    rcases hap : arrowParts sk with ⟨m_in, dom, res, cod⟩
    simp only [hap] at hf ⊢
    intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt hloc hsh hrf
      hfBase hfOpen hfCf haBase haOpen haCf hFf hFa hfa1 hfa2 hfa3 haNum harg
    obtain ⟨hnoViol, hok⟩ := hf B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt
      hloc hsh hrf hfBase hfOpen hfCf haBase haOpen haCf hFf hFa hfa1 hfa2 hfa3 haNum harg
    refine ⟨hnoViol, fun rv st' B' hrun => ?_⟩
    obtain ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf, hbase, hcls, hopen, hcf,
      hrb, ⟨hroF, hroT⟩, huniq⟩ := hok rv st' B' hrun
    refine ⟨hB', hst', hsz, hcap, hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf, hbase, hcls, hopen, hcf,
      hrb, ⟨?_, ?_⟩, huniq⟩
    · intro hfalse
      have hf0 : (isArrowSkel cod && (false || m_in.isUnique || (m_in.usage == .once))) = false := by
        cases h : isArrowSkel cod <;> simp [h] at hfalse ⊢
      exact hroF hf0
    · intro htrue
      by_cases h0 : (isArrowSkel cod && (false || m_in.isUnique || (m_in.usage == .once))) = true
      · exact hroT h0
      · have h0f : (isArrowSkel cod && (false || m_in.isUnique || (m_in.usage == .once))) = false := by
          cases h : (isArrowSkel cod && (false || m_in.isUnique || (m_in.usage == .once)))
          · rfl
          · exact absurd h h0
        obtain ⟨_, hfun⟩ := hroF h0f
        exact ⟨fun _ => False, fun _ h => False.elim h, FunOkAt_weaken_onceOnly hfun⟩
termination_by B => B
decreasing_by omega

theorem FunOkAt_preserve_sameShape {P : Prog} {ext : ExternOracle} {B : Nat}
    {st₀ st₁ : St} {sk : Skel} {onceOnly : Bool} {Foot : Nat → Prop} {f₀ f₁ : Val}
    (hloc : SameLoc f₀ f₁)
    (hsh : SameShapeOn (Reach st₀.heap f₀) st₀.heap st₁.heap)
    (hrf : RegsFuture st₀ st₁)
    (hf : FunOkAt P ext B st₀ sk onceOnly Foot f₀) :
    FunOkAt P ext B st₁ sk onceOnly Foot f₁ := by
  cases B with
  | zero => rw [FunOkAt]; trivial
  | succ b =>
    rw [FunOkAt] at hf ⊢
    intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt hloc1 hsh1 hrf1
    exact hf B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt
      (hloc.trans hloc1) (hsh.trans_reach hloc hsh1) (hrf.trans hrf1)

theorem FunOkAt_preserve_locs {P : Prog} {ext : ExternOracle} {B : Nat}
    {st₀ st₁ : St} {sk : Skel} {onceOnly : Bool} {Foot : Nat → Prop} {f : Val}
    (hp : PreservesLocs (Reach st₀.heap f) st₀.heap st₁.heap)
    (hrf : RegsFuture st₀ st₁)
    (hf : FunOkAt P ext B st₀ sk onceOnly Foot f) :
    FunOkAt P ext B st₁ sk onceOnly Foot f :=
  FunOkAt_preserve_sameShape (SameLoc.refl f) (SameShapeOn.of_preserves hp) hrf hf

theorem CtorFieldsOk.sub {P : Prog} {ext : ExternOracle} {B : Nat} {st : St} {v w : Val}
    (hc : CtorFieldsOk P ext B st v) (hw : HeldBy st.heap v w) : CtorFieldsOk P ext B st w :=
  fun l o r fs u hr ho hcell hu => hc l o r fs u (Reach_of_HeldBy hw hr) ho hcell hu

theorem CtorFieldsOk_imm (P : Prog) (ext : ExternOracle) (B : Nat) (st : St) (i : Imm) :
    CtorFieldsOk P ext B st (.imm i) :=
  fun _ _ _ _ _ hr => by cases hr

theorem CtorFieldsOk_congr {P : Prog} {ext : ExternOracle} {B : Nat} {st st' : St} {v : Val}
    (hdl : DeepLive st.heap v)
    (hp : PreservesLocs (Reach st.heap v) st.heap st'.heap)
    (hrf : RegsFuture st st')
    (hc : CtorFieldsOk P ext B st v) : CtorFieldsOk P ext B st' v := by
  intro l o r fs w hr ho hcell hw
  have hr₁ : Reach st.heap v l := (Reach_congr hp l).mp hr
  obtain ⟨o₁, ho₁⟩ := hdl.exists_obj hr₁
  have ho₁' : st'.heap.objs[l]? = some o₁ := (hp l hr₁).trans ho₁
  rw [ho] at ho₁'
  cases ho₁'
  obtain ⟨hno, hfun⟩ := hc l o r fs w hr₁ ho₁ hcell hw
  have hmem : w ∈ o.cell.vals := by rw [hcell]; exact hw
  have hpW : PreservesLocs (Reach st.heap w) st.heap st'.heap :=
    hp.mono fun x hx => Reach.step_trans hr₁ ho₁ hmem hx
  have hdlW : DeepLive st.heap w := hdl.sub (Or.inr ⟨l, o, hr₁, ho₁, hmem⟩)
  exact ⟨NoOnceCell_congr hdlW hpW hno, FunOkAt_preserve_locs hpW hrf hfun⟩

theorem CtorFieldsOk_of_sameShape {P : Prog} {ext : ExternOracle} {B : Nat} {st₁ st₂ : St}
    {v₁ v₂ : Val}
    (hdl₁ : DeepLive st₁.heap v₁)
    (hs : SameShapeOn (Reach st₁.heap v₁) st₁.heap st₂.heap)
    (hloc : SameLoc v₁ v₂)
    (hrf : RegsFuture st₁ st₂)
    (hc : CtorFieldsOk P ext B st₁ v₁) : CtorFieldsOk P ext B st₂ v₂ := by
  intro l o₂ r fs₂ w₂ hr₂ ho₂ hcell₂ hw₂
  have hr₁ : Reach st₁.heap v₁ l := Reach_of_sameShapeOn_rev hdl₁ hs hloc hr₂
  obtain ⟨o₁, ho₁⟩ := hdl₁.exists_obj hr₁
  obtain ⟨o₂', ho₂', hcs⟩ := hs l o₁ hr₁ ho₁
  rw [ho₂] at ho₂'
  cases ho₂'
  rw [hcell₂] at hcs
  cases hc₁ : o₁.cell with
  | num _ | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ =>
    rw [hc₁] at hcs; cases hcs
  | ctor r₁ fs₁ =>
    rw [hc₁] at hcs
    obtain ⟨rfl, hsz, hfs⟩ := hcs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw₂
    have hi₂ : i < fs₂.size := by simpa using hi
    have hi₁ : i < fs₁.size := by omega
    have hvs : ValSameShape fs₁[i] fs₂[i] := hfs i hi₁ hi₂
    have hw₁ : fs₁[i] ∈ fs₁.toList := List.mem_iff_getElem.mpr ⟨i, by simpa using hi₁, rfl⟩
    obtain ⟨hno, hfun⟩ := hc l o₁ r₁ fs₁ fs₁[i] hr₁ ho₁ hc₁ hw₁
    have hmem₁ : fs₁[i] ∈ o₁.cell.vals := by rw [hc₁]; exact hw₁
    have hdlW : DeepLive st₁.heap fs₁[i] := hdl₁.sub (Or.inr ⟨l, o₁, hr₁, ho₁, hmem₁⟩)
    have hsW : SameShapeOn (Reach st₁.heap fs₁[i]) st₁.heap st₂.heap :=
      hs.mono fun x hx => Reach.step_trans hr₁ ho₁ hmem₁ hx
    have hlocW : SameLoc fs₁[i] fs₂[i] := SameLoc.of_valSameShape hvs
    exact ⟨NoOnceCell_of_sameShape hdlW hsW hlocW hno,
      FunOkAt_preserve_sameShape hlocW hsW hrf hfun⟩

theorem applyOneS_fuel_zero (P : Prog) (ext : ExternOracle) (f a : Val) (c : Cls) (st : St) (B : Nat) :
    (applyOneS P ext 0 f a c).run (st, B) = .error .outOfFuel := by
  rw [applyOneS]
  cases B with
  | zero => rw [MS_bind_run, MS_spend_zero]
  | succ b => rw [MS_bind_run, MS_spend_succ]; rfl

theorem applyOneS_budget_zero (P : Prog) (ext : ExternOracle) (fuel : Nat) (f a : Val) (c : Cls) (st : St) :
    (applyOneS P ext fuel f a c).run (st, 0) = .error .outOfFuel := by
  cases fuel with
  | zero => exact applyOneS_fuel_zero P ext f a c st 0
  | succ n => unfold applyOneS; rw [MS_bind_run, MS_spend_zero]

theorem FunOkAt_imm_irr (P : Prog) (ext : ExternOracle) :
    ∀ (B : Nat) (st : St) (sk : Skel),
      FunOkAt P ext B st sk false (fun _ => False) (.imm .irr)
  | 0, _, _ => by rw [FunOkAt]; trivial
  | B + 1, st₀, sk => by
    rw [FunOkAt]
    intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst _ _ hloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    cases f with
    | ref _ _ _ => cases hloc
    | imm i =>
      simp only [SameLoc] at hloc
      subst hloc
      cases fuel with
      | zero =>
        simp only [applyOneConformS, MS_bind_run, applyOneS_fuel_zero]
        exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
      | succ n =>
        cases B_call with
        | zero =>
          simp only [applyOneConformS, MS_bind_run, applyOneS_budget_zero]
          exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
        | succ b' =>
          have hrun1 : (applyOneS P ext (n + 1) (.imm .irr) a c).run (st, b' + 1) =
              .ok (.imm .irr, (st, b')) := by
            rw [applyOneS, MS_bind_run, MS_spend_succ]; rfl
          have hrunC : (applyOneConformS P ext (n + 1) (.imm .irr) a c).run (st, b' + 1) =
              match (conform c (.imm .irr)).run st with
              | .ok (v, st') => .ok (v, (st', b'))
              | .error e => .error e := by
            rw [applyOneConformS, MS_bind_run, hrun1]; dsimp only; rw [MS_liftM_run]
            cases (conform c (.imm .irr)).run st <;> rfl
          have hokC_irr : (conform .irr (.imm .irr)).run st = .ok (.imm .irr, st) := rfl
          have hokC_imm : (conform .imm (.imm .irr)).run st = .ok (.imm .irr, st) := rfl
          have hokC_val : (conform .val (.imm .irr)).run st = .ok (.imm .irr, st) := rfl
          have hokC_leaf : (conform .leaf (.imm .irr)).run st = .error .stuck := rfl
          cases c with
          | leaf =>
            rw [hrunC, hokC_leaf]
            exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
          | irr | imm | val =>
            rw [hrunC]
            first | rw [hokC_irr] | rw [hokC_imm] | rw [hokC_val]
            refine ⟨fun k h => (by cases h), fun rv st' B' h => ?_⟩
            cases h
            refine ⟨Nat.le_succ _, StOk_mono (Nat.le_succ _) hst, Nat.le_refl _, Nat.le_refl _,
              rfl, Nat.le_refl _, ArrayExtends.refl _, ArrayExtends.refl _, PreservesLocs.refl _ _,
              PreservesOnceShell.refl _, StaticStrFresh.refl _,
              ValBaseOk_imm st .irr, ClsSafe.irr st.heap _,
              ClsSafe_deepOpenUnder_nil (c := .irr) (by decide) (ClsSafe.irr st.heap .irr),
              CtorFieldsOk_imm P ext b' st .irr,
              fun _ hr => (by cases hr),
              ⟨fun _ => ⟨NoOnceCell_imm st.heap .irr, FunOkAt_imm_irr P ext b' st _⟩,
               fun _ => ⟨fun _ => False, fun _ hf => False.elim hf,
                 FunOkAt_weaken_onceOnly (FunOkAt_imm_irr P ext b' st _)⟩⟩,
              fun _ => ⟨⟨fun _ _ _ _ _ _ _ _ _ _ _ hr => (by cases hr),
                         fun _ _ _ _ _ _ _ hr => (by cases hr)⟩,
                        fun _ hr => (by cases hr),
                        fun _ _ _ hr => (by cases hr)⟩⟩
termination_by B => B
decreasing_by all_goals omega

/-- Non-callable immediates (`.con`, `.bits`) and non-callable heap cells (`.ctor`, `.num`, `.str`)
immediately return `.error .stuck` under `applyOneConformS`, so they satisfy `FunOkAt` vacuously. -/
theorem FunOkAt_nonCallable_imm (P : Prog) (ext : ExternOracle) (B : Nat) (st : St) (sk : Skel)
    {i : Imm} (hne : i ≠ .irr) :
    FunOkAt P ext B st sk false (fun _ => False) (.imm i) := by
  cases B with
  | zero => rw [FunOkAt]; trivial
  | succ b =>
    rw [FunOkAt]
    intro B_call fuel st' f a c Frame fRegs aRegs aOnce aFoot _ _ _ _ hloc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    cases f with
    | ref _ _ _ => cases hloc
    | imm i' =>
      simp only [SameLoc] at hloc
      subst hloc
      cases fuel with
      | zero =>
        simp only [applyOneConformS, MS_bind_run, applyOneS_fuel_zero]
        exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
      | succ n =>
        cases B_call with
        | zero =>
          simp only [applyOneConformS, MS_bind_run, applyOneS_budget_zero]
          exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
        | succ b' =>
          cases i with
          | irr => exact absurd rfl hne
          | con r =>
            have hrun : (applyOneConformS P ext (n + 1) (.imm (.con r)) a c).run (st', b' + 1) = .error .stuck := by
              unfold applyOneConformS applyOneS; rw [MS_bind_run, MS_bind_run, MS_spend_succ]; rfl
            exact ⟨fun _ h => (by rw [hrun] at h; cases h), fun _ _ _ h => (by rw [hrun] at h; cases h)⟩
          | bits k =>
            have hrun : (applyOneConformS P ext (n + 1) (.imm (.bits k)) a c).run (st', b' + 1) = .error .stuck := by
              unfold applyOneConformS applyOneS; rw [MS_bind_run, MS_bind_run, MS_spend_succ]; rfl
            exact ⟨fun _ h => (by rw [hrun] at h; cases h), fun _ _ _ h => (by rw [hrun] at h; cases h)⟩

theorem FunOkAt_nonCallable_ref (P : Prog) (ext : ExternOracle) (B : Nat) (st₀ : St) (sk : Skel)
    {loc cap : Nat} {t : List Nat} {o₀ : Obj}
    (ho₀ : st₀.heap.objs[loc]? = some o₀)
    (hnc : match o₀.cell with | .ctor .. | .num _ | .str _ => True | _ => False) :
    FunOkAt P ext B st₀ sk false (fun _ => False) (.ref loc cap t) := by
  cases B with
  | zero => rw [FunOkAt]; trivial
  | succ b =>
    rw [FunOkAt]
    intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot _ _ _ _ hloc hsh _ hfBase _ _ _ _ _ _ _ _ _ _ _ _
    cases f with
    | imm _ => cases hloc
    | ref loc' cap' t' =>
      simp only [SameLoc] at hloc
      subst hloc
      cases fuel with
      | zero =>
        simp only [applyOneConformS, MS_bind_run, applyOneS_fuel_zero]
        exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
      | succ n =>
        cases B_call with
        | zero =>
          simp only [applyOneConformS, MS_bind_run, applyOneS_budget_zero]
          exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
        | succ b' =>
          obtain ⟨o, ho, hcap⟩ := hfBase.1.self.1
          obtain ⟨o₂, ho₂, hcs⟩ := hsh loc o₀ .here ho₀
          rw [ho] at ho₂
          cases ho₂
          have hrun : (applyOneConformS P ext (n + 1) (.ref loc cap' t') a c).run (st, b' + 1) = .error .stuck := by
            rw [applyOneConformS, MS_bind_run, applyOneS, MS_bind_run, MS_spend_succ]
            dsimp only
            rw [MS_bind_run, MS_liftM_run, obj_ok ho]
            have hbeq : (o.cap == cap') = true := by rw [hcap]; simp
            simp only [hbeq, ↓reduceIte]
            cases hc₀ : o₀.cell <;> rw [hc₀] at hnc hcs <;> try cases hnc
            · cases hc : o.cell <;> rw [hc] at hcs <;> try cases hcs
              rfl
            · cases hc : o.cell <;> rw [hc] at hcs <;> try cases hcs
              rfl
            · cases hc : o.cell <;> rw [hc] at hcs <;> try cases hcs
              rfl
          exact ⟨fun _ h => (by rw [hrun] at h; cases h), fun _ _ _ h => (by rw [hrun] at h; cases h)⟩

theorem ClsSafe_funOkAt (P : Prog) (ext : ExternOracle) (B : Nat) (st : St) (sk : Skel)
    {c : Cls} {v : Val} (hne : c ≠ .val) (hc : ClsSafe st.heap c v) :
    FunOkAt P ext B st sk false (fun _ => False) v := by
  rcases hc with rfl | hc
  · exact FunOkAt_imm_irr P ext B st sk
  · cases c with
    | irr => rw [hc]; exact FunOkAt_imm_irr P ext B st sk
    | imm =>
      obtain ⟨i, rfl⟩ := hc
      cases i with
      | irr => exact FunOkAt_imm_irr P ext B st sk
      | con _ => exact FunOkAt_nonCallable_imm P ext B st sk (by intro h; cases h)
      | bits _ => exact FunOkAt_nonCallable_imm P ext B st sk (by intro h; cases h)
    | leaf =>
      obtain ⟨loc, cap, o, n, rfl, ho, hnum, _⟩ := hc
      exact FunOkAt_nonCallable_ref P ext B st sk ho (by rw [hnum]; trivial)
    | val => exact absurd rfl hne

theorem ClsSafe_ctorFieldsOk (P : Prog) (ext : ExternOracle) (B : Nat) (st : St)
    {c : Cls} {v : Val} (hne : c ≠ .val) (hc : ClsSafe st.heap c v) :
    CtorFieldsOk P ext B st v := by
  intro l o r fs w hr ho hcell _
  rcases hc with rfl | hc
  · cases hr
  · cases c with
    | irr => rw [hc] at hr; cases hr
    | imm => obtain ⟨_, rfl⟩ := hc; cases hr
    | leaf =>
      obtain ⟨loc, cap, o₀, n, rfl, ho₀, hnum, _⟩ := hc
      cases hr with
      | here => rw [ho₀] at ho; cases ho; rw [hnum] at hcell; cases hcell
      | step ho1 hm1 _ => rw [ho₀] at ho1; cases ho1; rw [hnum] at hm1; cases hm1
    | val => exact absurd rfl hne

/-! ### `StOk` state-evolution lemmas -/

theorem StOk_preserve {P : Prog} {ext : ExternOracle} {B : Nat} {st st' : St}
    (hst : StOk P ext B st)
    (hcaps : CapsOk st'.heap)
    (hregs : RegsOk st')
    (hrf : RegsFuture st st')
    (hstatEq : st'.statics = st.statics)
    (hstrEq : st'.strs = st.strs)
    (hp : PreservesLocs (StaticStrLoc st) st.heap st'.heap) :
    StOk P ext B st' := by
  obtain ⟨_, _, hstat, hstr⟩ := hst
  refine ⟨hcaps, hregs, ?_, ?_⟩
  · intro r v hm
    rw [hstatEq] at hm
    obtain ⟨rc, rs, body, hfind, hbase, hcls, hopen, hno, hfun, hcf⟩ := hstat r v hm
    have hpV : PreservesLocs (Reach st.heap v) st.heap st'.heap :=
      hp.mono fun l hl => Or.inl ⟨r, v, hm, hl⟩
    refine ⟨rc, rs, body, hfind,
      ValBaseOk_congr hpV hrf.1 hbase,
      ClsSafe_congr hpV hcls,
      (DeepOpenUnder_congr hpV).mpr (DeepOpenUnder_of_regsFuture hbase.2.2.2 hopen hrf),
      NoOnceCell_congr hbase.1 hpV hno,
      FunOkAt_preserve_locs hpV hrf hfun,
      CtorFieldsOk_congr hbase.1 hpV hrf hcf⟩
  · intro s v hm
    rw [hstrEq] at hm
    obtain ⟨loc, cap, o, rfl, ho, hcap, hcell⟩ := hstr s v hm
    have ho' : st'.heap.objs[loc]? = some o :=
      (hp loc (Or.inr ⟨s, .ref loc cap [], hm, .here⟩)).trans ho
    exact ⟨loc, cap, o, rfl, ho', hcap, hcell⟩

theorem StOk_openRegion {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    (hst : StOk P ext B st) :
    StOk P ext B { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions } :=
  StOk_preserve hst hst.1 hst.2.1.openRegion (RegsFuture.openRegion st) rfl rfl (PreservesLocs.refl _ _)

theorem StOk_closeRegion {P : Prog} {ext : ExternOracle} {B : Nat} {st : St} (s : Nat)
    (hst : StOk P ext B st) :
    StOk P ext B { st with regions := st.regions.filter (· != s) } :=
  StOk_preserve hst hst.1 (hst.2.1.closeRegion s) (RegsFuture.closeRegion st s) rfl rfl (PreservesLocs.refl _ _)

theorem StOk_setObj_outside {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {loc : Nat} {o : Obj}
    (hst : StOk P ext B st)
    (hcap : o.cap < st.heap.nextCap)
    (hnot : ¬ StaticStrLoc st loc) :
    StOk P ext B { st with heap := { st.heap with objs := st.heap.objs.set! loc o } } := by
  have hcaps' : CapsOk { st.heap with objs := st.heap.objs.set! loc o } := by
    intro l o' ho'
    by_cases heq : l = loc
    · subst heq
      by_cases hlt : l < st.heap.objs.size
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self] at ho'
        simp only [hlt, ↓reduceIte] at ho'
        cases ho'; exact hcap
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self] at ho'
        simp only [hlt, ↓reduceIte] at ho'
        cases ho'
    · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm heq)] at ho'
      exact hst.1 l o' ho'
  have hp : PreservesLocs (StaticStrLoc st) st.heap { st.heap with objs := st.heap.objs.set! loc o } := by
    intro l hss
    have hne : l ≠ loc := fun heq => hnot (heq ▸ hss)
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
  exact StOk_preserve hst hcaps' hst.2.1 (RegsFuture.refl st) rfl rfl hp

theorem StOk_alloc {P : Prog} {ext : ExternOracle} {B : Nat} {st : St} (c : Cell) :
    StOk P ext B st →
    StOk P ext B { st with heap := { objs := st.heap.objs.push ⟨c, st.heap.nextCap⟩,
                                     nextCap := st.heap.nextCap + 1 } } := by
  intro hst
  have hcaps' : CapsOk { objs := st.heap.objs.push ⟨c, st.heap.nextCap⟩,
                         nextCap := st.heap.nextCap + 1 } :=
    alloc_capsOk hst.1
  have hp : PreservesLocs (StaticStrLoc st) st.heap
      { objs := st.heap.objs.push ⟨c, st.heap.nextCap⟩, nextCap := st.heap.nextCap + 1 } :=
    (alloc_preserves_old c [] st).mono fun l hl => by
      rcases hl with ⟨r, v, hm, hr⟩ | ⟨s, v, hm, hr⟩
      · obtain ⟨_, _, _, _, hbase, _⟩ := hst.2.2.1 r v hm
        obtain ⟨o, ho⟩ := hbase.1.exists_obj hr
        exact (Array.getElem?_eq_some_iff.mp ho).1
      · obtain ⟨loc, cap, o, rfl, ho, _, hcell⟩ := hst.2.2.2 s v hm
        cases hr with
        | here => exact (Array.getElem?_eq_some_iff.mp ho).1
        | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hcell] at hm1; cases hm1
  exact StOk_preserve hst hcaps' hst.2.1 (RegsFuture.refl st) rfl rfl hp

theorem StOk_pushStatic {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {r : Ref} {rc : Cls} {rs : Skel} {body : Term} {v : Val}
    (hst : StOk P ext B st)
    (hfind : P.find? r = some (.body #[] .shared rc rs body))
    (hbase : ValBaseOk st v)
    (hcls : ClsSafe st.heap rc v)
    (hopen : DeepOpenUnder st.heap st.regions [] v)
    (hno : NoOnceCell st.heap v)
    (hfun : FunOkAt P ext B st rs false (fun _ => False) v)
    (hcf : CtorFieldsOk P ext B st v) :
    StOk P ext B { st with statics := st.statics.push (r, v) } := by
  let st' : St := { st with statics := st.statics.push (r, v) }
  have hrf : RegsFuture st st' := RegsFuture.same_regions (Nat.le_refl _) rfl
  obtain ⟨hcaps, hregs, hstat, hstr⟩ := hst
  refine ⟨hcaps, hregs, ?_, hstr⟩
  intro r' v' hm
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | heq
  · obtain ⟨rc', rs', body', hf', hb', hc', ho', hn', hfun', hcf'⟩ := hstat r' v' hm
    exact ⟨rc', rs', body', hf', hb', hc', ho', hn',
      FunOkAt_preserve_locs (st₀ := st) (st₁ := st') (PreservesLocs.refl _ _) hrf hfun',
      CtorFieldsOk_congr (st := st) (st' := st') hb'.1 (PreservesLocs.refl _ _) hrf hcf'⟩
  · cases heq
    exact ⟨rc, rs, body, hfind, hbase, hcls, hopen, hno,
      FunOkAt_preserve_locs (st₀ := st) (st₁ := st') (PreservesLocs.refl _ _) hrf hfun,
      CtorFieldsOk_congr (st := st) (st' := st') hbase.1 (PreservesLocs.refl _ _) hrf hcf⟩

theorem StOk_pushStr {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {s : String} {loc cap : Nat} {o : Obj}
    (hst : StOk P ext B st)
    (ho : st.heap.objs[loc]? = some o)
    (hcap : o.cap = cap)
    (hcell : o.cell = .str s) :
    StOk P ext B { st with strs := st.strs.push (s, .ref loc cap []) } := by
  let st' : St := { st with strs := st.strs.push (s, .ref loc cap []) }
  have hrf : RegsFuture st st' := RegsFuture.same_regions (Nat.le_refl _) rfl
  obtain ⟨hcaps, hregs, hstat, hstr⟩ := hst
  refine ⟨hcaps, hregs, ?_, ?_⟩
  · intro r' v' hm
    obtain ⟨rc', rs', body', hf', hb', hc', ho', hn', hfun', hcf'⟩ := hstat r' v' hm
    exact ⟨rc', rs', body', hf', hb', hc', ho', hn',
      FunOkAt_preserve_locs (st₀ := st) (st₁ := st') (PreservesLocs.refl _ _) hrf hfun',
      CtorFieldsOk_congr (st := st) (st' := st') hb'.1 (PreservesLocs.refl _ _) hrf hcf'⟩
  · intro s' v' hm
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | heq
    · exact hstr s' v' hm
    · cases heq
      exact ⟨loc, cap, o, rfl, ho, hcap, hcell⟩

/-! ### `FunOkAt_once_wrap`: wrapping a function in an unspent `.once` cell -/

theorem FunOkAt_once_wrap {P : Prog} {ext : ExternOracle} {B : Nat}
    {st₀ : St} {sk : Skel} {tFoot : Nat → Prop} {loc cap : Nat} {t₀ : List Nat}
    {o₀ : Obj} {target₀ : Val}
    (ho₀ : st₀.heap.objs[loc]? = some o₀)
    (hcell₀ : o₀.cell = .once target₀ false)
    (hfT : FunOkAt P ext B st₀ sk true tFoot target₀) :
    FunOkAt P ext B st₀ sk true (fun l => l = loc ∨ tFoot l) (.ref loc cap t₀) := by
  cases B with
  | zero => rw [FunOkAt]; trivial
  | succ b =>
    rw [FunOkAt] at hfT ⊢
    intro B_call fuel st f a c Frame fRegs aRegs aOnce aFoot hB hst hstat hFlt hloc hsh hrf
      hfBase hfOpen hfCf haBase haOpen haCf hFf hFa hfa1 hfa2 hfa3 haNum harg
    cases f with
    | imm _ => cases hloc
    | ref loc' cap' t' =>
      simp only [SameLoc] at hloc
      subst hloc
      cases fuel with
      | zero =>
        simp only [applyOneConformS, MS_bind_run, applyOneS_fuel_zero]
        exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
      | succ n =>
        cases B_call with
        | zero =>
          simp only [applyOneConformS, MS_bind_run, applyOneS_budget_zero]
          exact ⟨fun _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
        | succ b' =>
          obtain ⟨o, ho, hcap⟩ := hfBase.1.self.1
          obtain ⟨o₂, ho₂, hcs⟩ := hsh loc o₀ .here ho₀
          rw [ho] at ho₂
          cases ho₂
          rw [hcell₀] at hcs
          cases hc : o.cell with
          | ctor _ _ | num _ | str _ | clo _ _ _ _ _ _ | pap _ _ =>
            rw [hc] at hcs; cases hcs
          | once target sp =>
            rw [hc] at hcs
            obtain ⟨hsp, hvsT⟩ := hcs
            subst hsp
            let st₁ : St := { st with heap := { st.heap with objs := st.heap.objs.set! loc { o with cell := .once target true } } }
            have hstep : (applyOneConformS P ext (n + 1) (.ref loc cap' t') a c).run (st, b' + 1) =
                (applyOneConformS P ext n target a c).run (st₁, b') := by
              rw [applyOneConformS, applyOneConformS, MS_bind_run, MS_bind_run]
              have hstep1 : (applyOneS P ext (n + 1) (.ref loc cap' t') a c).run (st, b' + 1) =
                  (applyOneS P ext n target a c).run (st₁, b') := by
                rw [applyOneS, MS_bind_run, MS_spend_succ]
                dsimp only
                rw [MS_bind_run, MS_liftM_run, obj_ok ho]
                have hbeq : (o.cap == cap') = true := by rw [hcap]; simp
                simp only [hbeq, ↓reduceIte, hc, Bool.false_eq_true]
                rw [MS_bind_run, MS_liftM_run, setObj_run]
              rw [hstep1]
            have hlocNotF : ¬ Frame loc := fun h => hFf loc h (Or.inl rfl)
            have hlocNotSS : ¬ StaticStrLoc st loc := fun h => hlocNotF (hstat loc h)
            have hmemT : target ∈ o.cell.vals := by rw [hc]; exact List.mem_singleton_self _
            have hlocNotT : ¬ Reach st.heap target loc :=
              hfBase.2.1 loc o target .here ho hmemT
            have hlocNotA : ¬ Reach st.heap a loc := fun h => hfa3 loc h (Or.inl rfl)
            have hpOutside : PreservesLocs (fun l => l ≠ loc) st.heap st₁.heap := by
              intro l hne
              dsimp only [st₁]
              rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
            have hpFrame : PreservesLocs Frame st.heap st₁.heap :=
              hpOutside.mono fun l hl heq => hlocNotF (heq ▸ hl)
            have hpT : PreservesLocs (Reach st.heap target) st.heap st₁.heap :=
              hpOutside.mono fun l hl heq => hlocNotT (heq ▸ hl)
            have hpA : PreservesLocs (Reach st.heap a) st.heap st₁.heap :=
              hpOutside.mono fun l hl heq => hlocNotA (heq ▸ hl)
            have hst₁ : StOk P ext b' st₁ :=
              StOk_setObj_outside (StOk_mono (Nat.le_succ _) hst) (hst.1 loc o ho) hlocNotSS
            have hssEq : ∀ l, StaticStrLoc st₁ l → StaticStrLoc st l := by
              intro l hss
              rcases hss with ⟨r, v, hm, hr⟩ | ⟨s, v, hm, hr⟩
              · left
                have hpV : PreservesLocs (Reach st.heap v) st.heap st₁.heap :=
                  hpFrame.mono fun x hx => hstat x (Or.inl ⟨r, v, hm, hx⟩)
                exact ⟨r, v, hm, (Reach_congr hpV l).mp hr⟩
              · right
                have hpV : PreservesLocs (Reach st.heap v) st.heap st₁.heap :=
                  hpFrame.mono fun x hx => hstat x (Or.inr ⟨s, v, hm, hx⟩)
                exact ⟨s, v, hm, (Reach_congr hpV l).mp hr⟩
            have hshT0 : SameShapeOn (Reach st₀.heap target₀) st₀.heap st₁.heap := by
              have hmem0 : target₀ ∈ o₀.cell.vals := by rw [hcell₀]; exact List.mem_singleton_self _
              have hsh01 : SameShapeOn (Reach st₀.heap target₀) st₀.heap st.heap :=
                hsh.mono fun x hx => .step ho₀ hmem0 hx
              exact hsh01.trans_reach (SameLoc.of_valSameShape hvsT) (SameShapeOn.of_preserves hpT)
            have htBase : ValBaseOk st₁ target :=
              ValBaseOk_congr hpT (Nat.le_refl _) (hfBase.sub (HeldBy_of_mem_vals ho hmemT))
            have htOpen : DeepOpenUnder st₁.heap st₁.regions fRegs target :=
              (DeepOpenUnder_congr hpT).mpr (hfOpen.sub (HeldBy_of_mem_vals ho hmemT))
            have htCf : CtorFieldsOk P ext b' st₁ target :=
              CtorFieldsOk_congr (hfBase.sub (HeldBy_of_mem_vals ho hmemT)).1 hpT (RegsFuture.refl st)
                (CtorFieldsOk_mono (Nat.le_succ _) (CtorFieldsOk.sub hfCf (HeldBy_of_mem_vals ho hmemT)))
            have haBase1 : ValBaseOk st₁ a := ValBaseOk_congr hpA (Nat.le_refl _) haBase
            have haOpen1 : DeepOpenUnder st₁.heap st₁.regions aRegs a :=
              (DeepOpenUnder_congr hpA).mpr haOpen
            have haCf1 : CtorFieldsOk P ext b' st₁ a :=
              CtorFieldsOk_congr haBase.1 hpA (RegsFuture.refl st) (CtorFieldsOk_mono (Nat.le_succ _) haCf)
            have hreachT_sub : ∀ l, Reach st₁.heap target l → Reach st.heap (.ref loc cap' t') l :=
              fun l hr => .step ho hmemT ((Reach_congr hpT l).mp hr)
            have harg1 : (arrowParts sk).1 ≠ .erased →
                ((arrowParts sk).1.usage = .once → FunOkAt P ext b' st₁ (arrowParts sk).2.1 aOnce aFoot a) ∧
                ((arrowParts sk).1.usage ≠ .once →
                  NoOnceCell st₁.heap a ∧ aOnce = false ∧ (∀ l, ¬ aFoot l) ∧
                  FunOkAt P ext b' st₁ (arrowParts sk).2.1 false (fun _ => False) a) ∧
                ((arrowParts sk).1.isUnique = true →
                  OwnTreeFull P st₁.heap a ∧
                  (∀ l, OwnReach P st₁.heap a l → ¬ Frame l ∧ ¬ Reach st₁.heap target l) ∧
                  ((arrowParts sk).1.isBorrowed = false → DeepOpenUnder st₁.heap st₁.regions [] a)) ∧
                (((arrowParts sk).2.2.1 = .unique ∧ c = .val ∧
                  ((arrowParts sk).1 = .many ∨ (arrowParts sk).1 = .once)) →
                  DeepOpenUnder st₁.heap st₁.regions [] a) := by
              intro hne
              obtain ⟨ho1, ho2, ho3, ho4⟩ := harg hne
              refine ⟨fun hu => FunOkAt_preserve_locs hpA (RegsFuture.refl st) (FunOkAt_mono (Nat.le_succ _) (ho1 hu)),
                fun hnu => ?_, fun hu => ?_, fun hrep => (DeepOpenUnder_congr hpA).mpr (ho4 hrep)⟩
              · obtain ⟨hno, haO, haF, hfun⟩ := ho2 hnu
                exact ⟨NoOnceCell_congr haBase.1 hpA hno, haO, haF,
                  FunOkAt_preserve_locs hpA (RegsFuture.refl st) (FunOkAt_mono (Nat.le_succ _) hfun)⟩
              · obtain ⟨htree, hdisj, hopen⟩ := ho3 hu
                refine ⟨(OwnTreeFull_congr hpA).mpr htree, fun l hl => ?_,
                  fun hnb => (DeepOpenUnder_congr hpA).mpr (hopen hnb)⟩
                have hl0 : OwnReach P st.heap a l := (OwnReach_congr hpA l).mp hl
                have ⟨h1, h2⟩ := hdisj l hl0
                exact ⟨h1, fun hrt => h2 (hreachT_sub l hrt)⟩
            obtain ⟨hnoViol, hok⟩ := hfT b' n st₁ target a c Frame fRegs aRegs aOnce aFoot
              (by omega) hst₁ (fun l h => hstat l (hssEq l h))
              (fun l hF => by simpa [st₁] using hFlt l hF)
              (SameLoc.of_valSameShape hvsT) hshT0 hrf
              htBase htOpen htCf haBase1 haOpen1 haCf1
              (fun l hF ht => hFf l hF (Or.inr ht))
              hFa
              (fun l ht => hfa1 l (Or.inr ht))
              (fun l hrt => hfa2 l (hreachT_sub l hrt))
              (fun l hra ht => hfa3 l ((Reach_congr hpA l).mp hra) (Or.inr ht))
              ⟨fun l haF => ⟨(Reach_congr hpA l).mpr (haNum.1 l haF).1, fun hnum1 => by
                apply (haNum.1 l haF).2
                obtain ⟨o1, n1, ho1, hcell1⟩ := hnum1
                by_cases hll : l = loc
                · subst hll
                  dsimp only [st₁] at ho1
                  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self] at ho1
                  have hlt : l < st.heap.objs.size :=
                    Nat.lt_of_not_ge fun hge => by rw [Array.getElem?_eq_none hge] at ho; cases ho
                  simp only [hlt, ↓reduceIte] at ho1; cases ho1; cases hcell1
                · dsimp only [st₁] at ho1
                  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hll)] at ho1
                  exact ⟨o1, n1, ho1, hcell1⟩⟩,
               fun her => NoOnceCell_congr haBase.1 hpA (haNum.2 her)⟩
              harg1
            rw [hstep]
            refine ⟨hnoViol, fun rv st' B' hrun => ?_⟩
            obtain ⟨hB', hst', hsz, hcap', hreg, hnr, hstatExt, hstrExt, hpres, honceSh, hssf, hbase, hcls, hopen, hcf,
              hrb, hro, huniq⟩ := hok rv st' B' hrun
            have hsz_eq : st₁.heap.objs.size = st.heap.objs.size := by
              dsimp only [st₁]; simp [Array.set!_eq_setIfInBounds]
            have honceSh01 : PreservesOnceShell st.heap st₁.heap :=
              PreservesOnceShell.of_setObj_once ho hc
            have hssf0 : StaticStrFresh st st' := by
              intro l hl
              rcases hssf l hl with hnew | h1 | hnum
              · exact Or.inl (by omega)
              · exact Or.inr (Or.inl (hssEq l h1))
              · exact Or.inr (Or.inr hnum)
            refine ⟨by omega, hst', by omega, hcap', hreg, hnr, hstatExt, hstrExt,
              hpFrame.trans hpres, honceSh01.trans honceSh, hssf0, hbase, hcls, hopen, hcf, ?_, hro, ?_⟩
            · intro l hr
              rcases hrb l hr with hnew | hrt | hra | hss | hnum
              · exact Or.inl (by omega)
              · exact Or.inr (Or.inl (hreachT_sub l hrt))
              · exact Or.inr (Or.inr (Or.inl ((Reach_congr hpA l).mp hra)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (hssEq l hss))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr hnum)))
            · intro hrc
              obtain ⟨htr, hownD, hnoArg⟩ := huniq hrc
              refine ⟨htr, hownD, fun hru hbe l hr => ?_⟩
              rcases hnoArg hru hbe l hr with hnew | hrt | hss | hnum
              · exact Or.inl (by omega)
              · exact Or.inr (Or.inl (hreachT_sub l hrt))
              · exact Or.inr (Or.inr (Or.inl (hssEq l hss)))
              · exact Or.inr (Or.inr (Or.inr hnum))

theorem FunOkAt_once_wrap_plain {P : Prog} {ext : ExternOracle} {B : Nat}
    {st₀ : St} {sk : Skel} {loc cap : Nat} {t₀ : List Nat}
    {o₀ : Obj} {target₀ : Val}
    (ho₀ : st₀.heap.objs[loc]? = some o₀)
    (hcell₀ : o₀.cell = .once target₀ false)
    (hfT : FunOkAt P ext B st₀ sk false (fun _ => False) target₀) :
    FunOkAt P ext B st₀ sk true (fun l => l = loc) (.ref loc cap t₀) :=
  FunOkAt_weaken_foot (fun _ h => h.elim id False.elim)
    (FunOkAt_once_wrap ho₀ hcell₀ (FunOkAt_weaken_onceOnly hfT))

/-! ## 4. Region Interpretation & Environment Simulation (`Interp`, `VSim`, `Sim`) -/

/-- Maps abstract region ids (`1` = caller's open regions, `r ≥ 2` = local regions) to concrete
region lists. -/
structure Interp where
  reg : Nat → List Nat

/-- Concrete regions corresponding to a list of abstract region ids. -/
def Interp.regsOf (I : Interp) (rs : List Nat) : List Nat :=
  rs.flatMap I.reg

/-- Extend `I` by mapping fresh abstract region `s_a` to singleton concrete region `[s_c]`. -/
def Interp.extend (I : Interp) (s_a s_c : Nat) : Interp :=
  ⟨fun r => if r == s_a then [s_c] else I.reg r⟩

theorem Interp.mem_regsOf {I : Interp} {rs : List Nat} {c : Nat} :
    c ∈ I.regsOf rs ↔ ∃ r ∈ rs, c ∈ I.reg r :=
  List.mem_flatMap

theorem Interp.regsOf_nil (I : Interp) : I.regsOf [] = [] := rfl

theorem Interp.mem_regsOf_natUnion {I : Interp} {a b : List Nat} {c : Nat} :
    c ∈ I.regsOf (natUnion a b) ↔ c ∈ I.regsOf a ∨ c ∈ I.regsOf b := by
  simp only [Interp.mem_regsOf, mem_natUnion]
  constructor
  · rintro ⟨r, ha | hb, hc⟩
    · exact Or.inl ⟨r, ha, hc⟩
    · exact Or.inr ⟨r, hb, hc⟩
  · rintro (⟨r, ha, hc⟩ | ⟨r, hb, hc⟩)
    · exact ⟨r, Or.inl ha, hc⟩
    · exact ⟨r, Or.inr hb, hc⟩

theorem Interp.regsOf_extend_lt {I : Interp} {s_a s_c : Nat} {rs : List Nat}
    (hlt : ∀ r ∈ rs, r < s_a) :
    (I.extend s_a s_c).regsOf rs = I.regsOf rs := by
  unfold Interp.regsOf
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.flatMap_cons]
    have hne : (r == s_a) = false := beq_false_of_ne (Nat.ne_of_lt (hlt r (List.mem_cons_self ..)))
    have hrest := ih fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    rw [hrest]
    simp only [Interp.extend, hne, Bool.false_eq_true, ↓reduceIte]

/-- Region interpretation well-formedness relative to abstract `σ` and concrete `st`. -/
def InterpOk (σ : AState) (st : St) (I : Interp) : Prop :=
  (∀ r, r < σ.nextRegion → ∀ c ∈ I.reg r, c < st.nextRegion) ∧
  (∀ c, st.regions.head? = some c → c ∈ I.reg (σ.regions.headD 1))

/-- Separation witness for an open region pair `(s_a, s_c)`: `s_a` maps to `[s_c]` and no other
abstract region `< σ.nextRegion` contains `s_c`. -/
def RegUnique (I : Interp) (σ : AState) (s_a s_c : Nat) : Prop :=
  I.reg s_a = [s_c] ∧ ∀ r, r < σ.nextRegion → r ≠ s_a → ¬ (s_c ∈ I.reg r)

theorem InterpOk.openRegion {σ : AState} {st : St} {I : Interp}
    (hok : InterpOk σ st I) :
    let st' := { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions }
    InterpOk σ.openReg.2 st' (I.extend σ.openReg.1 st.nextRegion) ∧
    RegUnique (I.extend σ.openReg.1 st.nextRegion) σ.openReg.2 σ.openReg.1 st.nextRegion := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr c hc
    dsimp [AState.openReg, Interp.extend] at hr hc ⊢
    by_cases heq : r = σ.nextRegion
    · subst heq
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_singleton] at hc
      subst hc; exact Nat.lt_succ_self _
    · have hbf : (r == σ.nextRegion) = false := beq_false_of_ne heq
      simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hc
      exact Nat.lt_succ_of_lt (hok.1 r (by omega) c hc)
  · intro c hc
    dsimp [AState.openReg, Interp.extend] at hc ⊢
    cases hc
    simp
  · dsimp [AState.openReg, Interp.extend]
    simp
  · intro r hr hne hc
    dsimp [AState.openReg, Interp.extend] at hr hne hc
    have hbf : (r == σ.nextRegion) = false := beq_false_of_ne hne
    simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hc
    exact Nat.lt_irrefl _ (hok.1 r (by omega) st.nextRegion hc)

theorem RegUnique.not_mem_regsOf {I : Interp} {σ : AState} {s_a s_c : Nat} {rs : List Nat}
    (hu : RegUnique I σ s_a s_c)
    (hlt : ∀ r ∈ rs, r < σ.nextRegion)
    (hnot : ¬ (s_a ∈ rs)) :
    ¬ (s_c ∈ I.regsOf rs) := by
  intro hc
  obtain ⟨r, hr, hmem⟩ := Interp.mem_regsOf.mp hc
  have hne : r ≠ s_a := fun heq => hnot (heq ▸ hr)
  exact hu.2 r (hlt r hr) hne hmem

theorem RegUnique.extend_other {I : Interp} {σ : AState} {s_a s_c s_a' s_c' : Nat}
    (hu : RegUnique I σ s_a s_c)
    (hneA : s_a ≠ s_a') (hneC : s_c ≠ s_c')
    (hsa' : s_a' = σ.nextRegion) :
    RegUnique (I.extend s_a' s_c') { σ with nextRegion := σ.nextRegion + 1 } s_a s_c := by
  refine ⟨?_, ?_⟩
  · dsimp [Interp.extend]
    rw [beq_false_of_ne hneA]; exact hu.1
  · intro r hr hne hc
    dsimp [Interp.extend] at hr hc
    by_cases heq : r = s_a'
    · subst heq
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_singleton] at hc
      exact hneC hc
    · have hbf : (r == s_a') = false := beq_false_of_ne heq
      simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hc
      exact hu.2 r (by omega) hne hc

/-! ### Abstract-concrete value & environment simulation -/

/-- A concrete value safe for any non-`.val` abstract class (`.irr`, `.imm`, `.leaf`): either an
immediate or a live untainted `.num` cell. -/
def NonValSafe (h : Heap) (v : Val) : Prop :=
  (∃ i, v = .imm i) ∨
  ∃ loc cap o n, v = .ref loc cap [] ∧ h.objs[loc]? = some o ∧ o.cap = cap ∧ o.cell = .num n

theorem ClsSafe.to_nonValSafe {h : Heap} {c : Cls} {v : Val}
    (hne : c ≠ .val) (hc : ClsSafe h c v) (hlive : LiveRef h v) : NonValSafe h v := by
  rcases hc with rfl | hc
  · exact Or.inl ⟨.irr, rfl⟩
  · cases c with
    | irr => exact Or.inl ⟨.irr, hc⟩
    | imm => exact Or.inl hc
    | leaf =>
      obtain ⟨loc, cap, o, n, rfl, ho, hnum, _⟩ := hc
      obtain ⟨o', ho', hcap⟩ := hlive
      rw [ho] at ho'; cases ho'
      exact Or.inr ⟨loc, cap, o, n, rfl, ho, hcap, hnum⟩
    | val => exact absurd rfl hne

theorem NonValSafe.congr {h₁ h₂ : Heap} {v : Val}
    (hp : PreservesLocs (Reach h₁ v) h₁ h₂) (hn : NonValSafe h₁ v) : NonValSafe h₂ v := by
  rcases hn with h | ⟨loc, cap, o, n, rfl, ho, hcap, hnum⟩
  · exact Or.inl h
  · exact Or.inr ⟨loc, cap, o, n, rfl, (hp loc .here).trans ho, hcap, hnum⟩

theorem NonValSafe.of_sameShape {h₁ h₂ : Heap} {v₁ v₂ : Val}
    (hsh : SameShapeOn (Reach h₁ v₁) h₁ h₂) (hvs : ValSameShape v₁ v₂)
    (hlive : LiveRef h₂ v₂) (hn : NonValSafe h₁ v₁) : NonValSafe h₂ v₂ := by
  rcases hn with ⟨i, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, _, hnum⟩
  · cases v₂ with
    | imm i₂ => exact Or.inl ⟨i₂, rfl⟩
    | ref _ _ _ => cases hvs
  · cases v₂ with
    | imm _ => cases hvs
    | ref loc₂ cap₂ t₂ =>
      obtain ⟨rfl, rfl⟩ := hvs
      obtain ⟨o₂, ho₂, hcs⟩ := hsh loc o .here ho
      obtain ⟨o₂', ho₂', hcap₂⟩ := hlive
      rw [ho₂] at ho₂'; cases ho₂'
      rw [hnum] at hcs
      cases hc₂ : o₂.cell <;> rw [hc₂] at hcs <;> try cases hcs
      exact Or.inr ⟨loc, cap₂, o₂, n, rfl, ho₂, hcap₂, hc₂⟩

theorem NonValSafe.deepOpenUnder_nil {h : Heap} {rs A : List Nat} {v : Val}
    (hn : NonValSafe h v) : DeepOpenUnder h rs A v := by
  intro w hw r hr _
  rcases hn with ⟨i, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, _, hnum⟩
  · rcases hw with rfl | ⟨_, _, h, _, _⟩
    · cases hr
    · cases h
  · rcases hw with rfl | ⟨l, o', hrl, ho', hm'⟩
    · cases hr
    · cases hrl with
      | here => rw [ho] at ho'; cases ho'; rw [hnum] at hm'; cases hm'
      | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hnum] at hm1; cases hm1

theorem NonValSafe.noOnceCell {h : Heap} {v : Val} (hn : NonValSafe h v) : NoOnceCell h v := by
  intro l o hr ho t sp hc
  rcases hn with ⟨i, rfl⟩ | ⟨loc, cap, o₀, n, rfl, ho₀, _, hnum⟩
  · cases hr
  · cases hr with
    | here => rw [ho₀] at ho; cases ho; rw [hnum] at hc; cases hc
    | step ho1 hm1 _ => rw [ho₀] at ho1; cases ho1; rw [hnum] at hm1; cases hm1

theorem NonValSafe.ownTreeFull {P : Prog} {h : Heap} {v : Val} (hn : NonValSafe h v) :
    OwnTreeFull P h v ∧ ∀ l, ¬ OwnReach P h v l := by
  have hnoOwn : ∀ l, ¬ OwnReach P h v l := by
    intro l hor
    rcases hn with ⟨i, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, _, hnum⟩
    · cases hor
    · cases hor with
      | here ho' hnot =>
        rw [ho] at ho'; cases ho'
        rcases hnot with h1 | h2
        · rw [hnum] at h1; cases h1
        · exact h2 rfl
      | step ho' hm' _ _ => rw [ho] at ho'; cases ho'; rw [hnum] at hm'; cases hm'
  exact ⟨⟨fun p₁ _ _ _ _ _ _ _ _ _ _ hp₁ => False.elim (hnoOwn p₁ hp₁),
          fun p _ _ _ _ _ _ hp => False.elim (hnoOwn p hp)⟩, hnoOwn⟩

theorem NonValSafe.funOkAt (P : Prog) (ext : ExternOracle) (B : Nat) (st : St) (sk : Skel)
    {v : Val} (hn : NonValSafe st.heap v) : FunOkAt P ext B st sk false (fun _ => False) v := by
  rcases hn with ⟨i, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, _, hnum⟩
  · cases i with
    | irr => exact FunOkAt_imm_irr P ext B st sk
    | con _ => exact FunOkAt_nonCallable_imm P ext B st sk (by intro h; cases h)
    | bits _ => exact FunOkAt_nonCallable_imm P ext B st sk (by intro h; cases h)
  · exact FunOkAt_nonCallable_ref P ext B st sk ho (by rw [hnum]; trivial)

theorem NonValSafe.ctorFieldsOk (P : Prog) (ext : ExternOracle) (B : Nat) (st : St)
    {v : Val} (hn : NonValSafe st.heap v) : CtorFieldsOk P ext B st v := by
  intro l o r fs w hr ho hc _
  rcases hn with ⟨i, rfl⟩ | ⟨loc, cap, o₀, n, rfl, ho₀, _, hnum⟩
  · cases hr
  · cases hr with
    | here => rw [ho₀] at ho; cases ho; rw [hnum] at hc; cases hc
    | step ho1 hm1 _ => rw [ho₀] at ho1; cases ho1; rw [hnum] at hm1; cases hm1

theorem NonValSafe.reach_numLoc {h : Heap} {v : Val} {l : Nat}
    (hn : NonValSafe h v) (hr : Reach h v l) : NumLoc h l := by
  rcases hn with ⟨i, rfl⟩ | ⟨loc, cap, o, n, rfl, ho, _, hnum⟩
  · cases hr
  · cases hr with
    | here => exact ⟨o, n, ho, hnum⟩
    | step ho1 hm1 _ => rw [ho] at ho1; cases ho1; rw [hnum] at hm1; cases hm1

/-- No binding id in `deps` is `.dead`, and all are in bounds of `σ.st`. -/
def ValidDeps (σ : AState) (deps : List Nat) : Prop :=
  ∀ d ∈ deps, d < σ.st.size ∧ σ.st[d]? ≠ some .dead

/-- Every binding id in `deps` is `.live` and allowed to be killed (`¬ NoKill d`). -/
def LiveDeps (σ : AState) (NoKill : Nat → Prop) (deps : List Nat) : Prop :=
  ∀ d ∈ deps, σ.st[d]? = some .live ∧ ¬ NoKill d

/-- `av` was read directly from a `@once` binding. -/
def IsOnceSrc (σ : AState) (av : AVal) : Prop :=
  ∃ id, av.src = some id ∧ σ.once[id]? = some true

/-- `av` is currently eligible for a unique transfer (`.val`, `.uniq`, not once-only or read from a
`@once` binding, and all deps `.live` & killable). -/
def Transferable (σ : AState) (NoKill : Nat → Prop) (av : AVal) : Prop :=
  av.cls = .val ∧ av.own = .uniq ∧ av.onceOnly = false ∧ ¬ IsOnceSrc σ av ∧ LiveDeps σ NoKill av.deps

/-- Every `@once` binding id in `deps` is still unspent. -/
def UnspentOnceDeps (σ : AState) (deps : List Nat) : Prop :=
  ∀ d ∈ deps, σ.once[d]? = some true → σ.spent[d]? = some false

/-- Effective `AVal` of a binding `ab` as read by `readVar`. -/
def effVal (ab : ABnd) : AVal :=
  { ab.val with deps := ab.id :: ab.val.deps.filter (· != ab.id), src := some ab.id }

/-- Whether `av` is actively live (no `.dead` deps, and if read from a `@once` binding, still unspent). -/
def ActiveVal (σ : AState) (av : AVal) : Prop :=
  ValidDeps σ av.deps ∧ (IsOnceSrc σ av → UnspentOnceDeps σ av.deps)

/-- Whether a binding/value's exclusive mutable footprint is currently active. -/
def FootActive (σ : AState) (av : AVal) : Prop :=
  av.onceOnly = true ∨ (IsOnceSrc σ av ∧ UnspentOnceDeps σ av.deps)

/-- `NoKill` bindings are never `.dead` in `σ`. -/
def NoKillOk (NoKill : Nat → Prop) (σ : AState) : Prop :=
  ∀ d, NoKill d → σ.st[d]? ≠ some .dead

/-- `NoSpend` bindings are never marked `spent = true` in `σ`. -/
def NoSpendOk (NoSpend : Nat → Prop) (σ : AState) : Prop :=
  ∀ d, NoSpend d → σ.spent[d]? ≠ some true

/-- Every accessible non-erased binding in `env` that remains `ActiveVal` in `σ₂` has its entire
reachable heap subgraph preserved from `h₁` to `h₂`. -/
def PreservesActiveEnv (Scope : Nat → Prop) (env : List Bnd) (aenv : List ABnd) (σ₂ : AState)
    (h₁ h₂ : Heap) : Prop :=
  ∀ (i : Nat) (b : Bnd) (ab : ABnd), Scope i → env[i]? = some b → aenv[i]? = some ab →
    ab.mode ≠ .erased → ActiveVal σ₂ (effVal ab) →
    PreservesLocs (Reach h₁ b.val) h₁ h₂

/-- **Value simulation (`VSim`)**: relates a concrete runtime value `v` (with exclusive mutable
footprint `Foot`) to its abstract `AVal` `av` in `(st, Frame, NoKill, NoSpend, σ, I)` at budget `B`. -/
def VSim (P : Prog) (ext : ExternOracle) (B : Nat) (st : St)
    (Frame : Nat → Prop) (NoKill NoSpend : Nat → Prop) (σ : AState) (I : Interp)
    (Foot : Nat → Prop) (av : AVal) (v : Val) : Prop :=
  (∀ r ∈ av.regs, r < σ.nextRegion) ∧
  (∀ d ∈ av.deps, d < σ.st.size) ∧
  (∀ x, av.src = some x → x < σ.st.size ∧ x ∈ av.deps) ∧
  (ValidDeps σ av.deps → IsOnceSrc σ av → SpentOnceSafe st.heap v) ∧
  (ActiveVal σ av →
    ValBaseOk st v ∧
    DeepOpenUnder st.heap st.regions (I.regsOf av.regs) v ∧
    CtorFieldsOk P ext B st v ∧
    (¬ IsOnceSrc σ av → av.cls ≠ .val → NonValSafe st.heap v) ∧
    (¬ IsOnceSrc σ av ∧ av.onceOnly = false →
      NoOnceCell st.heap v ∧ (∀ l, ¬ Foot l) ∧
      FunOkAt P ext B st av.skel false (fun _ => False) v) ∧
    (av.onceOnly = true →
      (∀ l, Foot l → Reach st.heap v l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l) ∧
      ((∀ x, av.src = some x → ¬ NoKill x) → ∀ l, Foot l → ¬ Frame l) ∧
      (∀ loc cap t o r fs, v = .ref loc cap t → st.heap.objs[loc]? = some o → o.cell = .ctor r fs →
        ∀ l, ¬ Foot l) ∧
      FunOkAt P ext B st av.skel true Foot v) ∧
    (IsOnceSrc σ av →
      (∀ l, Foot l → Reach st.heap v l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l) ∧
      ((∀ d ∈ av.deps, σ.once[d]? = some true → ¬ NoSpend d) → ∀ l, Foot l → ¬ Frame l) ∧
      FunOkAt P ext B st av.skel true Foot v) ∧
    (Transferable σ NoKill av →
      OwnTreeFull P st.heap v ∧
      ∀ l, OwnReach P st.heap v l → ¬ Frame l ∧ ¬ StaticStrLoc st l))

/-- **Environment simulation (`Sim`)**: relates concrete `env` to abstract `aenv` on accessible
de Bruijn indices `Scope`, including pairwise unique-ownership and exclusive-footprint
disjointness across all active bindings. -/
def Sim (P : Prog) (ext : ExternOracle) (B : Nat) (st : St)
    (Frame : Nat → Prop) (NoKill NoSpend : Nat → Prop) (Scope : Nat → Prop)
    (env : List Bnd) (aenv : List ABnd) (σ : AState) (I : Interp)
    (envFoot : Nat → Nat → Prop) : Prop :=
  env.length = aenv.length ∧
  AStateOk σ ∧
  InterpOk σ st I ∧
  (∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ab.id < σ.st.size) ∧
  (∀ (i j : Nat) (ab₁ ab₂ : ABnd), aenv[i]? = some ab₁ → aenv[j]? = some ab₂ → ab₁.id = ab₂.id → i = j) ∧
  (∀ (i : Nat) (b : Bnd) (ab : ABnd), Scope i → env[i]? = some b → aenv[i]? = some ab →
    b.mode = ab.mode ∧
    (ab.mode ≠ .erased →
      σ.once[ab.id]? = some (ab.mode.usage == .once) ∧
      VSim P ext B st Frame NoKill NoSpend σ I (envFoot i) (effVal ab) b.val)) ∧
  (∀ (i j : Nat) (b₁ b₂ : Bnd) (ab₁ ab₂ : ABnd), i ≠ j → Scope i → Scope j →
    env[i]? = some b₁ → aenv[i]? = some ab₁ →
    env[j]? = some b₂ → aenv[j]? = some ab₂ →
    ab₁.mode ≠ .erased → ab₂.mode ≠ .erased →
    (ActiveVal σ (effVal ab₁) → Transferable σ NoKill (effVal ab₁) → ActiveVal σ (effVal ab₂) →
      (∀ d, d ∈ (effVal ab₁).deps → ¬ (d ∈ (effVal ab₂).deps)) →
      ∀ l, OwnReach P st.heap b₁.val l → ¬ Reach st.heap b₂.val l) ∧
    (ActiveVal σ (effVal ab₁) → FootActive σ (effVal ab₁) → ActiveVal σ (effVal ab₂) →
      ∀ l, envFoot i l → ¬ Reach st.heap b₂.val l))

/-- Pairwise disjointness between an evaluated value `(rv, av, Foot)` and all active accessible
bindings in `(env, aenv, envFoot)`. -/
def ValEnvDisj (P : Prog) (st : St) (NoKill : Nat → Prop) (Scope : Nat → Prop)
    (env : List Bnd) (aenv : List ABnd) (σ : AState) (envFoot : Nat → Nat → Prop)
    (Foot : Nat → Prop) (av : AVal) (rv : Val) : Prop :=
  ∀ (i : Nat) (b : Bnd) (ab : ABnd), Scope i → env[i]? = some b → aenv[i]? = some ab → ab.mode ≠ .erased →
    (ActiveVal σ av → Transferable σ NoKill av → ActiveVal σ (effVal ab) →
      (∀ d, d ∈ av.deps → ¬ (d ∈ (effVal ab).deps)) →
      ∀ l, OwnReach P st.heap rv l → ¬ Reach st.heap b.val l) ∧
    (ActiveVal σ (effVal ab) → Transferable σ NoKill (effVal ab) → ActiveVal σ av →
      (∀ d, d ∈ (effVal ab).deps → ¬ (d ∈ av.deps)) →
      ∀ l, OwnReach P st.heap b.val l → ¬ Reach st.heap rv l) ∧
    (ActiveVal σ av → FootActive σ av → ActiveVal σ (effVal ab) →
      av.src ≠ some ab.id → ∀ l, Foot l → ¬ Reach st.heap b.val l) ∧
    (ActiveVal σ (effVal ab) → FootActive σ (effVal ab) → ActiveVal σ av →
      av.src ≠ some ab.id → ∀ l, envFoot i l → ¬ Reach st.heap rv l) ∧
    (ActiveVal σ av → FootActive σ av → av.src = some ab.id → ∀ l, Foot l → envFoot i l) ∧
    (av.src = some ab.id → ab.val.onceOnly = true → av.onceOnly = true) ∧
    (ActiveVal σ av → av.src = some ab.id → SameLoc b.val rv ∨ ∀ l, Reach st.heap rv l → NumLoc st.heap l)

/-! ### Monotonicity & framing lemmas for `VSim`, `Sim`, `ValEnvDisj` -/

theorem ValidDeps.of_AStateLe {σ₁ σ₂ : AState} {deps : List Nat}
    (hle : AStateLe σ₁ σ₂) (hbnd : ∀ d ∈ deps, d < σ₁.st.size)
    (hv₂ : ValidDeps σ₂ deps) : ValidDeps σ₁ deps := by
  intro d hd
  have hlt := hbnd d hd
  refine ⟨hlt, fun hdead => ?_⟩
  have h1 := hle.2.2.1 d hlt
  rw [hdead] at h1
  have ⟨_, hne2⟩ := hv₂ d hd
  cases h2 : σ₂.st[d]? with
  | none => rw [h2] at h1; exact h1
  | some b₂ =>
    rw [h2] at h1
    cases b₂ with
    | dead => exact hne2 h2
    | live | shared => exact h1

theorem LiveDeps.of_AStateLe {σ₁ σ₂ : AState} {NoKill : Nat → Prop} {deps : List Nat}
    (hle : AStateLe σ₁ σ₂) (hbnd : ∀ d ∈ deps, d < σ₁.st.size)
    (hl₂ : LiveDeps σ₂ NoKill deps) : LiveDeps σ₁ NoKill deps := by
  intro d hd
  have hlt := hbnd d hd
  have ⟨hlive₂, hnk⟩ := hl₂ d hd
  have h1 := hle.2.2.1 d hlt
  rw [hlive₂] at h1
  cases hst₁ : σ₁.st[d]? with
  | none => rw [hst₁] at h1; exact False.elim h1
  | some b₁ =>
    rw [hst₁] at h1
    cases b₁ with
    | live => exact ⟨rfl, hnk⟩
    | shared | dead => exact False.elim h1

theorem IsOnceSrc.iff_AStateLe {σ₁ σ₂ : AState} {av : AVal}
    (hok₁ : AStateOk σ₁) (hle : AStateLe σ₁ σ₂)
    (hsrc : ∀ x, av.src = some x → x < σ₁.st.size) :
    IsOnceSrc σ₁ av ↔ IsOnceSrc σ₂ av := by
  constructor
  · rintro ⟨id, hs, ho⟩
    have hlt : id < σ₁.once.size := by rw [← hok₁.1]; exact hsrc id hs
    exact ⟨id, hs, by rw [hle.2.2.2.1 id hlt]; exact ho⟩
  · rintro ⟨id, hs, ho⟩
    have hlt : id < σ₁.once.size := by rw [← hok₁.1]; exact hsrc id hs
    exact ⟨id, hs, by rw [← hle.2.2.2.1 id hlt]; exact ho⟩

theorem UnspentOnceDeps.of_AStateLe {σ₁ σ₂ : AState} {deps : List Nat}
    (hok₁ : AStateOk σ₁) (hle : AStateLe σ₁ σ₂)
    (hbnd : ∀ d ∈ deps, d < σ₁.st.size)
    (hu₂ : UnspentOnceDeps σ₂ deps) : UnspentOnceDeps σ₁ deps := by
  intro d hd ho₁
  have hlt : d < σ₁.st.size := hbnd d hd
  have hltOnce : d < σ₁.once.size := by rw [← hok₁.1]; exact hlt
  have hltSp : d < σ₁.spent.size := by rw [← hok₁.2.1]; exact hlt
  have ho₂ : σ₂.once[d]? = some true := by rw [hle.2.2.2.1 d hltOnce]; exact ho₁
  have hsp₂ : σ₂.spent[d]? = some false := hu₂ d hd ho₂
  cases hsp₁ : σ₁.spent[d]? with
  | none =>
    have := Array.getElem?_eq_none_iff.mp hsp₁
    omega
  | some b =>
    cases b with
    | false => rfl
    | true =>
      have htrue₂ := hle.2.2.2.2 d hltSp hsp₁
      rw [hsp₂] at htrue₂
      cases htrue₂

theorem ActiveVal.of_AStateLe {σ₁ σ₂ : AState} {av : AVal}
    (hok₁ : AStateOk σ₁) (hle : AStateLe σ₁ σ₂)
    (hdeps : ∀ d ∈ av.deps, d < σ₁.st.size)
    (hsrc : ∀ x, av.src = some x → x < σ₁.st.size)
    (ha₂ : ActiveVal σ₂ av) : ActiveVal σ₁ av :=
  ⟨ValidDeps.of_AStateLe hle hdeps ha₂.1,
   fun his₁ => UnspentOnceDeps.of_AStateLe hok₁ hle hdeps
     (ha₂.2 ((IsOnceSrc.iff_AStateLe hok₁ hle hsrc).mp his₁))⟩

theorem Transferable.of_AStateLe {σ₁ σ₂ : AState} {NoKill₁ NoKill₂ : Nat → Prop} {av : AVal}
    (hok₁ : AStateOk σ₁) (hle : AStateLe σ₁ σ₂)
    (hdeps : ∀ d ∈ av.deps, d < σ₁.st.size)
    (hsrc : ∀ x, av.src = some x → x < σ₁.st.size)
    (hnk : ∀ d, NoKill₁ d → NoKill₂ d)
    (htr₂ : Transferable σ₂ NoKill₂ av) : Transferable σ₁ NoKill₁ av := by
  refine ⟨htr₂.1, htr₂.2.1, htr₂.2.2.1,
    fun his₁ => htr₂.2.2.2.1 ((IsOnceSrc.iff_AStateLe hok₁ hle hsrc).mp his₁),
    fun d hd => ?_⟩
  have ⟨hlive₁, hnk₂⟩ := LiveDeps.of_AStateLe hle hdeps htr₂.2.2.2.2 d hd
  exact ⟨hlive₁, fun hnk₁ => hnk₂ (hnk d hnk₁)⟩

theorem FootActive.of_AStateLe {σ₁ σ₂ : AState} {av : AVal}
    (hok₁ : AStateOk σ₁) (hle : AStateLe σ₁ σ₂)
    (hdeps : ∀ d ∈ av.deps, d < σ₁.st.size)
    (hsrc : ∀ x, av.src = some x → x < σ₁.st.size)
    (hf₂ : FootActive σ₂ av) : FootActive σ₁ av := by
  rcases hf₂ with ho | ⟨his₂, husp₂⟩
  · exact Or.inl ho
  · exact Or.inr ⟨(IsOnceSrc.iff_AStateLe hok₁ hle hsrc).mpr his₂,
      UnspentOnceDeps.of_AStateLe hok₁ hle hdeps husp₂⟩

theorem NoKillOk.of_AStateLe {σ₁ σ₂ : AState} {NoKill : Nat → Prop}
    (hle : AStateLe σ₁ σ₂) (hbnd : ∀ d, NoKill d → d < σ₁.st.size)
    (hok₂ : NoKillOk NoKill σ₂) : NoKillOk NoKill σ₁ := by
  intro d hnk hdead
  have hlt := hbnd d hnk
  have h1 := hle.2.2.1 d hlt
  rw [hdead] at h1
  cases h2 : σ₂.st[d]? with
  | none => rw [h2] at h1; exact h1
  | some b₂ =>
    rw [h2] at h1
    cases b₂ with
    | dead => exact hok₂ d hnk h2
    | live | shared => exact h1

theorem NoSpendOk.of_AStateLe {σ₁ σ₂ : AState} {NoSpend : Nat → Prop}
    (hok₁ : AStateOk σ₁) (hle : AStateLe σ₁ σ₂) (hbnd : ∀ d, NoSpend d → d < σ₁.st.size)
    (hsp₂ : NoSpendOk NoSpend σ₂) : NoSpendOk NoSpend σ₁ := by
  intro d hns htrue
  have hlt : d < σ₁.spent.size := by rw [← hok₁.2.1]; exact hbnd d hns
  exact hsp₂ d hns (hle.2.2.2.2 d hlt htrue)

theorem PreservesActiveEnv.refl (Scope : Nat → Prop) (env : List Bnd) (aenv : List ABnd)
    (σ : AState) (h : Heap) : PreservesActiveEnv Scope env aenv σ h h :=
  fun _ _ _ _ _ _ _ _ => PreservesLocs.refl _ _

theorem PreservesActiveEnv.trans {Scope : Nat → Prop} {env : List Bnd} {aenv : List ABnd}
    {σ₂ σ₃ : AState} {h₁ h₂ h₃ : Heap}
    (hok₂ : AStateOk σ₂) (hle₂₃ : AStateLe σ₂ σ₃)
    (hbnd₂ : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ∀ d ∈ (effVal ab).deps, d < σ₂.st.size)
    (hid₂ : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ab.id < σ₂.st.size)
    (hp₁₂ : PreservesActiveEnv Scope env aenv σ₂ h₁ h₂)
    (hp₂₃ : PreservesActiveEnv Scope env aenv σ₃ h₂ h₃) :
    PreservesActiveEnv Scope env aenv σ₃ h₁ h₃ := by
  intro i b ab hsc hbi habi hne ha₃
  have ha₂ : ActiveVal σ₂ (effVal ab) :=
    ActiveVal.of_AStateLe hok₂ hle₂₃ (hbnd₂ i ab habi) (fun x hx => by
      dsimp [effVal] at hx; cases hx; exact hid₂ i ab habi) ha₃
  have h1 := hp₁₂ i b ab hsc hbi habi hne ha₂
  have h2 := hp₂₃ i b ab hsc hbi habi hne ha₃
  intro l hr₁
  exact (h2 l ((Reach_congr h1 l).mpr hr₁)).trans (h1 l hr₁)

theorem LiveRef.lt_size {h : Heap} {loc cap : Nat} {t : List Nat}
    (hl : LiveRef h (.ref loc cap t)) : loc < h.objs.size := by
  obtain ⟨_, ho, _⟩ := hl
  exact (Array.getElem?_eq_some_iff.mp ho).1

theorem DeepLive.reach_lt_size {h : Heap} {v : Val} {l : Nat}
    (hd : DeepLive h v) (hr : Reach h v l) : l < h.objs.size := by
  obtain ⟨_, ho⟩ := hd.exists_obj hr
  exact (Array.getElem?_eq_some_iff.mp ho).1

/-- `VSim` is preserved under budget decrease, `AStateLe`, `RegsFuture`, `PreservesOnceShell`,
`StaticStrFresh`, `PreservesLocs` on `v`, and changing `(Frame, NoKill, NoSpend)`. -/
theorem VSim_evolve {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat}
    {st₁ st₂ : St} {Frame₁ Frame₂ NoKill₁ NoKill₂ NoSpend₁ NoSpend₂ : Nat → Prop}
    {σ₁ σ₂ : AState} {I₁ I₂ : Interp} {Foot : Nat → Prop} {av : AVal} {v : Val}
    (hB : B₂ ≤ B₁)
    (hok₁ : AStateOk σ₁)
    (hle : AStateLe σ₁ σ₂)
    (hrf : RegsFuture st₁ st₂)
    (honceSh : PreservesOnceShell st₁.heap st₂.heap)
    (hssf : StaticStrFresh st₁ st₂)
    (hI : ∀ r ∈ av.regs, ∀ c ∈ I₁.reg r, c ∈ I₂.reg r)
    (hnk : ∀ d, NoKill₁ d → NoKill₂ d)
    (hp : ActiveVal σ₂ av → PreservesLocs (Reach st₁.heap v) st₁.heap st₂.heap)
    (hFootOnceOnly : ActiveVal σ₂ av → av.onceOnly = true →
      (∀ x, av.src = some x → ¬ NoKill₂ x) → ∀ l, Foot l → ¬ Frame₂ l)
    (hFootOnceSrc : ActiveVal σ₂ av → IsOnceSrc σ₂ av →
      (∀ d ∈ av.deps, σ₂.once[d]? = some true → ¬ NoSpend₂ d) → ∀ l, Foot l → ¬ Frame₂ l)
    (hOwnFrame : ActiveVal σ₂ av → Transferable σ₂ NoKill₂ av →
      ∀ l, OwnReach P st₁.heap v l → ¬ Frame₂ l)
    (hv : VSim P ext B₁ st₁ Frame₁ NoKill₁ NoSpend₁ σ₁ I₁ Foot av v) :
    VSim P ext B₂ st₂ Frame₂ NoKill₂ NoSpend₂ σ₂ I₂ Foot av v := by
  obtain ⟨hregs, hdeps, hsrc, hspent, hbody⟩ := hv
  have hsrcLt : ∀ x, av.src = some x → x < σ₁.st.size := fun x hx => (hsrc x hx).1
  have hisOnceIff : IsOnceSrc σ₁ av ↔ IsOnceSrc σ₂ av :=
    IsOnceSrc.iff_AStateLe hok₁ hle hsrcLt
  refine ⟨fun r hr => Nat.lt_of_lt_of_le (hregs r hr) hle.2.1,
    fun d hd => Nat.lt_of_lt_of_le (hdeps d hd) hle.1,
    fun x hx => let ⟨hlt, hm⟩ := hsrc x hx; ⟨Nat.lt_of_lt_of_le hlt hle.1, hm⟩,
    fun hv₂ his₂ => (hspent (ValidDeps.of_AStateLe hle hdeps hv₂) (hisOnceIff.mpr his₂)).of_preservesOnceShell honceSh,
    fun ha₂ => ?_⟩
  have ha₁ : ActiveVal σ₁ av := ActiveVal.of_AStateLe hok₁ hle hdeps hsrcLt ha₂
  obtain ⟨hbase, hopen, hcf, hcls, hplain, honceOnly, honceSrc, htrans⟩ := hbody ha₁
  have hpV : PreservesLocs (Reach st₁.heap v) st₁.heap st₂.heap := hp ha₂
  refine ⟨ValBaseOk_congr hpV hrf.1 hbase, ?_,
    CtorFieldsOk_mono hB (CtorFieldsOk_congr hbase.1 hpV hrf hcf),
    fun hno hne => (hcls (fun h1 => hno (hisOnceIff.mp h1)) hne).congr hpV,
    ?_, ?_, ?_, ?_⟩
  · have hopen2 : DeepOpenUnder st₁.heap st₂.regions (I₁.regsOf av.regs) v :=
      DeepOpenUnder_of_regsFuture hbase.2.2.2 hopen hrf
    have hopen3 : DeepOpenUnder st₁.heap st₂.regions (I₂.regsOf av.regs) v :=
      hopen2.mono fun c hc => by
        obtain ⟨r, hr, hcr⟩ := Interp.mem_regsOf.mp hc
        exact Interp.mem_regsOf.mpr ⟨r, hr, hI r hr c hcr⟩
    exact (DeepOpenUnder_congr hpV).mpr hopen3
  · rintro ⟨hno2, hoO⟩
    obtain ⟨hnoOnce, hnoFoot, hfun⟩ := hplain ⟨fun h1 => hno2 (hisOnceIff.mp h1), hoO⟩
    exact ⟨NoOnceCell_congr hbase.1 hpV hnoOnce, hnoFoot,
      FunOkAt_mono hB (FunOkAt_preserve_locs hpV hrf hfun)⟩
  · intro hoO
    obtain ⟨hfoot1, _, hctor1, hfun⟩ := honceOnly hoO
    refine ⟨fun l hl => ?_, hFootOnceOnly ha₂ hoO, ?_,
      FunOkAt_mono hB (FunOkAt_preserve_locs hpV hrf hfun)⟩
    · have ⟨hr1, hss1, hnum1⟩ := hfoot1 l hl
      have hlt1 := hbase.1.reach_lt_size hr1
      have hnotNum2 : ¬ NumLoc st₂.heap l := fun hnum2 => hnum1 ((NumLoc_congr hpV hr1).mpr hnum2)
      exact ⟨(Reach_congr hpV l).mpr hr1, hssf.not_staticStrLoc hlt1 hss1 hnotNum2, hnotNum2⟩
    · intro loc cap t o r fs hvEq ho₂ hcell l hft
      subst hvEq
      have ho₁ : st₁.heap.objs[loc]? = some o := by
        rw [← hpV loc .here]; exact ho₂
      exact hctor1 loc cap t o r fs rfl ho₁ hcell l hft
  · intro his2
    have his1 : IsOnceSrc σ₁ av := hisOnceIff.mpr his2
    obtain ⟨hfoot1, _, hfun⟩ := honceSrc his1
    refine ⟨fun l hl => ?_, hFootOnceSrc ha₂ his2,
      FunOkAt_mono hB (FunOkAt_preserve_locs hpV hrf hfun)⟩
    have ⟨hr1, hss1, hnum1⟩ := hfoot1 l hl
    have hlt1 := hbase.1.reach_lt_size hr1
    have hnotNum2 : ¬ NumLoc st₂.heap l := fun hnum2 => hnum1 ((NumLoc_congr hpV hr1).mpr hnum2)
    exact ⟨(Reach_congr hpV l).mpr hr1, hssf.not_staticStrLoc hlt1 hss1 hnotNum2, hnotNum2⟩
  · intro htr2
    have htr1 : Transferable σ₁ NoKill₁ av :=
      Transferable.of_AStateLe hok₁ hle hdeps hsrcLt hnk htr2
    obtain ⟨htree, hdisj1⟩ := htrans htr1
    refine ⟨(OwnTreeFull_congr hpV).mpr htree, fun l hl => ?_⟩
    have hl1 : OwnReach P st₁.heap v l := (OwnReach_congr hpV l).mp hl
    have hr1 : Reach st₁.heap v l := OwnReach_toReach hl1
    exact ⟨hOwnFrame ha₂ htr2 l hl1,
      hssf.not_staticStrLoc (hbase.1.reach_lt_size hr1) (hdisj1 l hl1).2 (OwnReach_not_numLoc hl)⟩

/-- Specialized `VSim_evolve` when `Frame`, `NoKill`, `NoSpend` are unchanged. -/
theorem VSim_step {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat}
    {st₁ st₂ : St} {Frame NoKill NoSpend : Nat → Prop}
    {σ₁ σ₂ : AState} {I₁ I₂ : Interp} {Foot : Nat → Prop} {av : AVal} {v : Val}
    (hB : B₂ ≤ B₁) (hok₁ : AStateOk σ₁) (hle : AStateLe σ₁ σ₂)
    (hrf : RegsFuture st₁ st₂) (honceSh : PreservesOnceShell st₁.heap st₂.heap)
    (hssf : StaticStrFresh st₁ st₂)
    (hI : ∀ r ∈ av.regs, ∀ c ∈ I₁.reg r, c ∈ I₂.reg r)
    (hp : ActiveVal σ₂ av → PreservesLocs (Reach st₁.heap v) st₁.heap st₂.heap)
    (hv : VSim P ext B₁ st₁ Frame NoKill NoSpend σ₁ I₁ Foot av v) :
    VSim P ext B₂ st₂ Frame NoKill NoSpend σ₂ I₂ Foot av v := by
  have hdeps := hv.2.1
  have hsrcLt : ∀ x, av.src = some x → x < σ₁.st.size := fun x hx => (hv.2.2.1 x hx).1
  refine VSim_evolve hB hok₁ hle hrf honceSh hssf hI (fun _ h => h) hp ?_ ?_ ?_ hv
  · intro ha₂ hoO hnk l hl
    have ha₁ := ActiveVal.of_AStateLe hok₁ hle hdeps hsrcLt ha₂
    exact ((hv.2.2.2.2 ha₁).2.2.2.2.2.1 hoO).2.1 hnk l hl
  · intro ha₂ his₂ hns l hl
    have ha₁ := ActiveVal.of_AStateLe hok₁ hle hdeps hsrcLt ha₂
    have his₁ := (IsOnceSrc.iff_AStateLe hok₁ hle hsrcLt).mpr his₂
    refine ((hv.2.2.2.2 ha₁).2.2.2.2.2.2.1 his₁).2.1 (fun d hd ho₁ => ?_) l hl
    have hltOnce : d < σ₁.once.size := by rw [← hok₁.1]; exact hdeps d hd
    exact hns d hd (by rw [hle.2.2.2.1 d hltOnce]; exact ho₁)
  · intro ha₂ htr₂ l hl₁
    have ha₁ := ActiveVal.of_AStateLe hok₁ hle hdeps hsrcLt ha₂
    have htr₁ : Transferable σ₁ NoKill av :=
      Transferable.of_AStateLe hok₁ hle hdeps hsrcLt (fun _ h => h) htr₂
    exact (((hv.2.2.2.2 ha₁).2.2.2.2.2.2.2 htr₁).2 l hl₁).1

/-- Evolve `Sim` across state/heap transition (unchanged `Frame`, `NoKill`, `NoSpend`). -/
theorem Sim_step {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat}
    {st₁ st₂ : St} {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ₁ σ₂ : AState} {I₁ I₂ : Interp}
    {envFoot : Nat → Nat → Prop}
    (hB : B₂ ≤ B₁) (hle : AStateLe σ₁ σ₂) (hok₂ : AStateOk σ₂) (hIok₂ : InterpOk σ₂ st₂ I₂)
    (hrf : RegsFuture st₁ st₂) (honceSh : PreservesOnceShell st₁.heap st₂.heap)
    (hssf : StaticStrFresh st₁ st₂)
    (hI : ∀ r, r < σ₁.nextRegion → ∀ c ∈ I₁.reg r, c ∈ I₂.reg r)
    (hpEnv : PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap)
    (hsim : Sim P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ₁ I₁ envFoot) :
    Sim P ext B₂ st₂ Frame NoKill NoSpend Scope env aenv σ₂ I₂ envFoot := by
  obtain ⟨hlen, hok₁, _, hids, huniqId, hbnds, hdisj⟩ := hsim
  refine ⟨hlen, hok₂, hIok₂,
    fun i ab hab => Nat.lt_of_lt_of_le (hids i ab hab) hle.1,
    huniqId, ?_, ?_⟩
  · intro i b ab hsc hbi habi
    obtain ⟨hmode, hneBody⟩ := hbnds i b ab hsc hbi habi
    refine ⟨hmode, fun hne => ?_⟩
    obtain ⟨honce, hv⟩ := hneBody hne
    have hltOnce : ab.id < σ₁.once.size := by rw [← hok₁.1]; exact hids i ab habi
    refine ⟨by rw [hle.2.2.2.1 ab.id hltOnce]; exact honce,
      VSim_step hB hok₁ hle hrf honceSh hssf (fun r hr => hI r (hv.1 r hr))
        (fun ha₂ => hpEnv i b ab hsc hbi habi hne ha₂) hv⟩
  · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    obtain ⟨_, hneB1⟩ := hbnds i b₁ ab₁ hsi hb₁ hab₁
    obtain ⟨_, hneB2⟩ := hbnds j b₂ ab₂ hsj hb₂ hab₂
    have hv₁ := (hneB1 hne₁).2
    have hv₂ := (hneB2 hne₂).2
    have hsrc1 : ∀ x, (effVal ab₁).src = some x → x < σ₁.st.size := fun x hx => (hv₁.2.2.1 x hx).1
    have hsrc2 : ∀ x, (effVal ab₂).src = some x → x < σ₁.st.size := fun x hx => (hv₂.2.2.1 x hx).1
    obtain ⟨hdU, hdF⟩ := hdisj i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    refine ⟨?_, ?_⟩
    · intro ha₁₂ htr₁₂ ha₂₂ hdd l hor₂ hrb₂
      have ha₁₁ := ActiveVal.of_AStateLe hok₁ hle hv₁.2.1 hsrc1 ha₁₂
      have ha₂₁ := ActiveVal.of_AStateLe hok₁ hle hv₂.2.1 hsrc2 ha₂₂
      have htr₁₁ : Transferable σ₁ NoKill (effVal ab₁) :=
        Transferable.of_AStateLe hok₁ hle hv₁.2.1 hsrc1 (fun _ h => h) htr₁₂
      have hp1 := hpEnv i b₁ ab₁ hsi hb₁ hab₁ hne₁ ha₁₂
      have hp2 := hpEnv j b₂ ab₂ hsj hb₂ hab₂ hne₂ ha₂₂
      exact hdU ha₁₁ htr₁₁ ha₂₁ hdd l ((OwnReach_congr hp1 l).mp hor₂) ((Reach_congr hp2 l).mp hrb₂)
    · intro ha₁₂ hf₁₂ ha₂₂ l hft hrb₂
      have ha₁₁ := ActiveVal.of_AStateLe hok₁ hle hv₁.2.1 hsrc1 ha₁₂
      have ha₂₁ := ActiveVal.of_AStateLe hok₁ hle hv₂.2.1 hsrc2 ha₂₂
      have hf₁₁ := FootActive.of_AStateLe hok₁ hle hv₁.2.1 hsrc1 hf₁₂
      have hp2 := hpEnv j b₂ ab₂ hsj hb₂ hab₂ hne₂ ha₂₂
      exact hdF ha₁₁ hf₁₁ ha₂₁ l hft ((Reach_congr hp2 l).mp hrb₂)

/-- Evolve `ValEnvDisj` across state/heap transition preserving active env bindings and `rv`. -/
theorem ValEnvDisj_step {P : Prog} {st₁ st₂ : St} {NoKill Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ₁ σ₂ : AState}
    {envFoot : Nat → Nat → Prop} {Foot : Nat → Prop} {av : AVal} {rv : Val}
    (hok₁ : AStateOk σ₁) (hle : AStateLe σ₁ σ₂)
    (hdepsV : ∀ d ∈ av.deps, d < σ₁.st.size)
    (hsrcV : ∀ x, av.src = some x → x < σ₁.st.size)
    (hdepsE : ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ d ∈ (effVal ab).deps, d < σ₁.st.size)
    (hids : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ab.id < σ₁.st.size)
    (hpEnv : PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap)
    (hpV : ActiveVal σ₂ av → PreservesLocs (Reach st₁.heap rv) st₁.heap st₂.heap)
    (hdisj : ValEnvDisj P st₁ NoKill Scope env aenv σ₁ envFoot Foot av rv) :
    ValEnvDisj P st₂ NoKill Scope env aenv σ₂ envFoot Foot av rv := by
  intro i b ab hsi hbi habi hne
  have hdepsB := hdepsE i ab hsi habi hne
  have hsrcB : ∀ x, (effVal ab).src = some x → x < σ₁.st.size := fun x hx => by
    dsimp [effVal] at hx; cases hx; exact hids i ab habi
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hdisj i b ab hsi hbi habi hne
  refine ⟨?_, ?_, ?_, ?_, ?_, h6, ?_⟩
  · intro haV₂ htrV₂ haB₂ hdd l hor hrB
    have haV₁ := ActiveVal.of_AStateLe hok₁ hle hdepsV hsrcV haV₂
    have haB₁ := ActiveVal.of_AStateLe hok₁ hle hdepsB hsrcB haB₂
    have htrV₁ : Transferable σ₁ NoKill av :=
      Transferable.of_AStateLe hok₁ hle hdepsV hsrcV (fun _ h => h) htrV₂
    exact h1 haV₁ htrV₁ haB₁ hdd l ((OwnReach_congr (hpV haV₂) l).mp hor)
      ((Reach_congr (hpEnv i b ab hsi hbi habi hne haB₂) l).mp hrB)
  · intro haB₂ htrB₂ haV₂ hdd l hor hrV
    have haV₁ := ActiveVal.of_AStateLe hok₁ hle hdepsV hsrcV haV₂
    have haB₁ := ActiveVal.of_AStateLe hok₁ hle hdepsB hsrcB haB₂
    have htrB₁ : Transferable σ₁ NoKill (effVal ab) :=
      Transferable.of_AStateLe hok₁ hle hdepsB hsrcB (fun _ h => h) htrB₂
    exact h2 haB₁ htrB₁ haV₁ hdd l
      ((OwnReach_congr (hpEnv i b ab hsi hbi habi hne haB₂) l).mp hor)
      ((Reach_congr (hpV haV₂) l).mp hrV)
  · intro haV₂ hfV₂ haB₂ hns l hft hrB
    have haV₁ := ActiveVal.of_AStateLe hok₁ hle hdepsV hsrcV haV₂
    have haB₁ := ActiveVal.of_AStateLe hok₁ hle hdepsB hsrcB haB₂
    have hfV₁ := FootActive.of_AStateLe hok₁ hle hdepsV hsrcV hfV₂
    exact h3 haV₁ hfV₁ haB₁ hns l hft ((Reach_congr (hpEnv i b ab hsi hbi habi hne haB₂) l).mp hrB)
  · intro haB₂ hfB₂ haV₂ hns l hft hrV
    have haV₁ := ActiveVal.of_AStateLe hok₁ hle hdepsV hsrcV haV₂
    have haB₁ := ActiveVal.of_AStateLe hok₁ hle hdepsB hsrcB haB₂
    have hfB₁ := FootActive.of_AStateLe hok₁ hle hdepsB hsrcB hfB₂
    exact h4 haB₁ hfB₁ haV₁ hns l hft ((Reach_congr (hpV haV₂) l).mp hrV)
  · intro haV₂ hfV₂ hsrcEq l
    exact h5 (ActiveVal.of_AStateLe hok₁ hle hdepsV hsrcV haV₂)
      (FootActive.of_AStateLe hok₁ hle hdepsV hsrcV hfV₂) hsrcEq l
  · intro haV₂ hsrcEq
    have haV₁ := ActiveVal.of_AStateLe hok₁ hle hdepsV hsrcV haV₂
    rcases h7 haV₁ hsrcEq with hloc | hnum
    · exact Or.inl hloc
    · exact Or.inr fun l hr₂ =>
        (NumLoc_congr (hpV haV₂) ((Reach_congr (hpV haV₂) l).mp hr₂)).mp
          (hnum l ((Reach_congr (hpV haV₂) l).mp hr₂))

/-- Shrink `Scope` in `Sim`. -/
theorem Sim_weaken_scope {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope₁ Scope₂ : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    (hsub : ∀ i, Scope₂ i → Scope₁ i)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope₁ env aenv σ I envFoot) :
    Sim P ext B st Frame NoKill NoSpend Scope₂ env aenv σ I envFoot :=
  ⟨hsim.1, hsim.2.1, hsim.2.2.1, hsim.2.2.2.1, hsim.2.2.2.2.1,
   fun i b ab hsc => hsim.2.2.2.2.2.1 i b ab (hsub i hsc),
   fun i j b₁ b₂ ab₁ ab₂ hij hsi hsj => hsim.2.2.2.2.2.2 i j b₁ b₂ ab₁ ab₂ hij (hsub i hsi) (hsub j hsj)⟩

theorem AStateLe_openReg (σ : AState) : AStateLe σ σ.openReg.2 := by
  refine ⟨Nat.le_refl _, Nat.le_succ _, fun i hi => ?_, fun _ _ => rfl, fun _ _ h => h⟩
  dsimp [AState.openReg]
  cases h : σ.st[i]? with
  | none => exact absurd (Array.getElem?_eq_none_iff.mp h) (Nat.not_le_of_lt hi)
  | some b => exact BSt.le_refl b

theorem AStateLe_closeReg (s : Nat) (σ : AState) : AStateLe σ (σ.closeReg s) := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, fun i hi => ?_, fun _ _ => rfl, fun _ _ h => h⟩
  dsimp [AState.closeReg]
  cases h : σ.st[i]? with
  | none => exact absurd (Array.getElem?_eq_none_iff.mp h) (Nat.not_le_of_lt hi)
  | some b => exact BSt.le_refl b

/-- Open a fresh region pair `(σ.openReg.1, st.nextRegion)` in `Sim`. -/
theorem Sim_openRegion {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    let st' := { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions }
    let I' := I.extend σ.openReg.1 st.nextRegion
    Sim P ext B st' Frame NoKill NoSpend Scope env aenv σ.openReg.2 I' envFoot ∧
    RegUnique I' σ.openReg.2 σ.openReg.1 st.nextRegion := by
  have hok₁ := hsim.2.1
  have hIok₁ := hsim.2.2.1
  obtain ⟨hIok', hregU⟩ := hIok₁.openRegion
  have hle : AStateLe σ σ.openReg.2 := AStateLe_openReg σ
  have hok₂ : AStateOk σ.openReg.2 := hok₁.openReg.1
  have hIext : ∀ r, r < σ.nextRegion → ∀ c ∈ I.reg r, c ∈ (I.extend σ.openReg.1 st.nextRegion).reg r := by
    intro r hr c hc
    dsimp [AState.openReg, Interp.extend]
    have hbf : (r == σ.nextRegion) = false := beq_false_of_ne (Nat.ne_of_lt hr)
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    exact hc
  exact ⟨Sim_step (Nat.le_refl B) hle hok₂ hIok' (RegsFuture.openRegion st)
    (PreservesOnceShell.refl _) (StaticStrFresh.refl _) hIext
    (PreservesActiveEnv.refl _ _ _ _ _) hsim, hregU⟩

/-- Push an erased binding onto `env`/`aenv` in `Sim`. -/
theorem Sim_push_erased {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    let res := σ.pushBnd { cls := .irr } false
    let ab : ABnd := { id := res.1, mode := .erased, val := { cls := .irr } }
    let Scope' : Nat → Prop := fun i => match i with | 0 => True | k + 1 => Scope k
    let envFoot' : Nat → Nat → Prop := fun i => match i with | 0 => fun _ => False | k + 1 => envFoot k
    Sim P ext B st Frame NoKill NoSpend Scope' (⟨.imm .irr, .erased⟩ :: env) (ab :: aenv) res.2 I envFoot' := by
  have hok₁ := hsim.2.1
  have hle : AStateLe σ (σ.pushBnd { cls := .irr } false).2 := (hok₁.pushBnd _ false).2
  have hok₂ : AStateOk (σ.pushBnd { cls := .irr } false).2 := (hok₁.pushBnd _ false).1
  have hIok₂ : InterpOk (σ.pushBnd { cls := .irr } false).2 st I := hsim.2.2.1
  have hsim₂ := Sim_step (Nat.le_refl B) hle hok₂ hIok₂ (RegsFuture.refl st)
    (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
    (PreservesActiveEnv.refl _ _ _ _ _) hsim
  obtain ⟨hlen, _, _, hids, huniqId, hbnds, hdisj⟩ := hsim₂
  refine ⟨by simp [hlen], hok₂, hIok₂, ?_, ?_, ?_, ?_⟩
  · intro i ab hab
    cases i with
    | zero => simp at hab; subst hab; dsimp [AState.pushBnd]; simp
    | succ k => exact hids k ab (by simpa using hab)
  · intro i j ab₁ ab₂ hab₁ hab₂ heq
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ k =>
        simp at hab₁ hab₂
        subst hab₁
        have hlt := hsim.2.2.2.1 k ab₂ hab₂
        dsimp [AState.pushBnd] at heq
        omega
    | succ k =>
      cases j with
      | zero =>
        simp at hab₁ hab₂
        subst hab₂
        have hlt := hsim.2.2.2.1 k ab₁ hab₁
        dsimp [AState.pushBnd] at heq
        omega
      | succ m =>
        exact congrArg Nat.succ (huniqId k m ab₁ ab₂ (by simpa using hab₁) (by simpa using hab₂) heq)
  · intro i b ab hsc hbi habi
    cases i with
    | zero =>
      simp at hbi habi; subst hbi; subst habi
      exact ⟨rfl, fun h => absurd rfl h⟩
    | succ k =>
      exact hbnds k b ab hsc (by simpa using hbi) (by simpa using habi)
  · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    cases i with
    | zero => simp at hab₁; subst hab₁; exact absurd rfl hne₁
    | succ k =>
      cases j with
      | zero => simp at hab₂; subst hab₂; exact absurd rfl hne₂
      | succ m =>
        exact hdisj k m b₁ b₂ ab₁ ab₂ (fun h => hij (congrArg Nat.succ h)) hsi hsj
          (by simpa using hb₁) (by simpa using hab₁) (by simpa using hb₂) (by simpa using hab₂) hne₁ hne₂

/-- Helper: if `ab.id` is fresh (`ab.id = σ.st.size`), `ValidDeps` of `effVal ab` in `σ.pushBnd`
implies `ValidDeps` of `ab.val` in `σ`, and similarly for `ActiveVal`/`Transferable`/`FootActive`. -/
private theorem mem_effVal_deps_iff {ab : ABnd} {d : Nat} :
    d ∈ (effVal ab).deps ↔ d = ab.id ∨ (d ∈ ab.val.deps ∧ d ≠ ab.id) := by
  simp only [effVal, List.mem_cons, List.mem_filter, bne_iff_ne]

/-- Push a non-erased binding `(b, bv)` onto `env`/`aenv` in `Sim`, given `VSim` of `(bv, b.val)` and
`ValEnvDisj` against `env`. -/
theorem Sim_push_bnd {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {bFoot : Nat → Prop}
    {b : Bnd} {bv : AVal}
    (hsrcNone : bv.src = none)
    (hNotOnce : bv.onceOnly = false → b.mode.usage ≠ .once → ∀ l, ¬ bFoot l)
    (hOnceSpent : b.mode.usage = .once → SpentOnceSafe st.heap b.val)
    (hOnceFun : b.mode.usage = .once →
      (∀ l, bFoot l → Reach st.heap b.val l ∧ ¬ Frame l ∧ ¬ StaticStrLoc st l ∧ ¬ NumLoc st.heap l) ∧
      FunOkAt P ext B st bv.skel true bFoot b.val)
    (hOnceFootEnv : b.mode.usage = .once →
      ∀ i b₂ ab₂, Scope i → env[i]? = some b₂ → aenv[i]? = some ab₂ → ab₂.mode ≠ .erased →
        ActiveVal σ (effVal ab₂) → ∀ l, bFoot l → ¬ Reach st.heap b₂.val l)
    (hv : VSim P ext B st Frame NoKill NoSpend σ I bFoot bv b.val)
    (hdisjV : ValEnvDisj P st NoKill Scope env aenv σ envFoot bFoot bv b.val)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    let isOnce := b.mode.usage == .once
    let res := σ.pushBnd bv isOnce
    let ab : ABnd := { id := res.1, mode := b.mode, val := bv }
    let Scope' : Nat → Prop := fun i => match i with | 0 => True | k + 1 => Scope k
    let envFoot' : Nat → Nat → Prop := fun i => match i with | 0 => bFoot | k + 1 => envFoot k
    Sim P ext B st Frame NoKill NoSpend Scope' (b :: env) (ab :: aenv) res.2 I envFoot' := by
  intro isOnce res ab Scope' envFoot'
  have hok₁ := hsim.2.1
  have hle : AStateLe σ res.2 := (hok₁.pushBnd bv isOnce).2
  have hok₂ : AStateOk res.2 := (hok₁.pushBnd bv isOnce).1
  have hIok₂ : InterpOk res.2 st I := hsim.2.2.1
  have hsim₂ := Sim_step (Nat.le_refl B) hle hok₂ hIok₂ (RegsFuture.refl st)
    (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
    (PreservesActiveEnv.refl _ _ _ _ _) hsim
  have honceNew : res.2.once[ab.id]? = some isOnce := by
    dsimp [res, ab, AState.pushBnd]
    rw [hok₁.1, Array.getElem?_push_size]
  have hdepsLt : ∀ d ∈ bv.deps, d < σ.st.size := hv.2.1
  have hNotSrc1 : ¬ IsOnceSrc σ bv := by rintro ⟨_, hs, _⟩; rw [hsrcNone] at hs; cases hs
  have hValidToOld : ValidDeps res.2 (effVal ab).deps → ValidDeps σ bv.deps := by
    intro hv2 d hd
    exact ValidDeps.of_AStateLe hle hdepsLt (fun x hx =>
      hv2 x (mem_effVal_deps_iff.mpr (Or.inr ⟨hx, Nat.ne_of_lt (hdepsLt x hx)⟩))) d hd
  have hActiveToOld : ActiveVal res.2 (effVal ab) → ActiveVal σ bv :=
    fun ha2 => ⟨hValidToOld ha2.1, fun his => absurd his hNotSrc1⟩
  have hTransToOld : Transferable res.2 NoKill (effVal ab) → Transferable σ NoKill bv := by
    intro ⟨hcls, hown, hoo, _, hlive⟩
    refine ⟨hcls, hown, hoo, hNotSrc1, LiveDeps.of_AStateLe hle hdepsLt (fun d hd => ?_)⟩
    exact hlive d (mem_effVal_deps_iff.mpr (Or.inr ⟨hd, Nat.ne_of_lt (hdepsLt d hd)⟩))
  have hVSimNew : VSim P ext B st Frame NoKill NoSpend res.2 I bFoot (effVal ab) b.val := by
    obtain ⟨hregs, hdeps, _, _, hbody⟩ := hv
    refine ⟨hregs, ?_, ?_, ?_, ?_⟩
    · intro d hd
      rcases mem_effVal_deps_iff.mp hd with rfl | ⟨hd1, _⟩
      · dsimp [res, ab, AState.pushBnd]; simp
      · exact Nat.lt_of_lt_of_le (hdeps d hd1) hle.1
    · intro x hx
      dsimp [effVal] at hx; cases hx
      exact ⟨by dsimp [res, ab, AState.pushBnd]; simp, List.mem_cons_self ..⟩
    · intro _ his2
      obtain ⟨id, hsrc, honce⟩ := his2
      dsimp [effVal] at hsrc; cases hsrc
      rw [honceNew] at honce
      have hu : b.mode.usage = .once := by
        have hEq : isOnce = true := Option.some.inj honce
        simpa [isOnce] using hEq
      exact hOnceSpent hu
    · intro ha2
      have ha1 := hActiveToOld ha2
      obtain ⟨hbase, hopen, hcf, hcls, hplain, honceOnly, _, htrans⟩ := hbody ha1
      refine ⟨hbase, hopen, hcf, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ hne
        exact hcls hNotSrc1 hne
      · rintro ⟨hnotOnce2, hoO⟩
        have hnotU : b.mode.usage ≠ .once := by
          intro hu
          apply hnotOnce2
          exact ⟨ab.id, rfl, by rw [honceNew]; simp [isOnce, hu]⟩
        obtain ⟨hnoOnce, _, hfun⟩ := hplain ⟨hNotSrc1, hoO⟩
        exact ⟨hnoOnce, hNotOnce hoO hnotU, hfun⟩
      · intro hoO
        obtain ⟨hft, hnkF, hctor, hfun⟩ := honceOnly hoO
        exact ⟨hft, fun _ => hnkF (fun _ hs => by rw [hsrcNone] at hs; cases hs), hctor, hfun⟩
      · intro his2
        obtain ⟨id, hsrc, honce⟩ := his2
        dsimp [effVal] at hsrc; cases hsrc
        rw [honceNew] at honce
        have hu : b.mode.usage = .once := by
          have hEq : isOnce = true := Option.some.inj honce
          simpa [isOnce] using hEq
        obtain ⟨hft, hfun⟩ := hOnceFun hu
        exact ⟨fun l hl => ⟨(hft l hl).1, (hft l hl).2.2⟩, fun _ l hl => (hft l hl).2.1, hfun⟩
      · intro htr2
        exact htrans (hTransToOld htr2)
  obtain ⟨hlen, _, _, hids, huniqId, hbnds, hdisj⟩ := hsim₂
  refine ⟨by simp [hlen], hok₂, hIok₂, ?_, ?_, ?_, ?_⟩
  · intro i ab' hab'
    cases i with
    | zero => simp at hab'; subst hab'; dsimp [res, ab, AState.pushBnd]; simp
    | succ k => exact hids k ab' (by simpa using hab')
  · intro i j ab₁ ab₂ hab₁ hab₂ heq
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ k =>
        simp at hab₁ hab₂; subst hab₁
        have hlt := hsim.2.2.2.1 k ab₂ hab₂
        dsimp [ab, res, AState.pushBnd] at heq
        omega
    | succ k =>
      cases j with
      | zero =>
        simp at hab₁ hab₂; subst hab₂
        have hlt := hsim.2.2.2.1 k ab₁ hab₁
        dsimp [ab, res, AState.pushBnd] at heq
        omega
      | succ m =>
        exact congrArg Nat.succ (huniqId k m ab₁ ab₂ (by simpa using hab₁) (by simpa using hab₂) heq)
  · intro i b' ab' hsc hbi habi
    cases i with
    | zero =>
      simp at hbi habi; subst hbi; subst habi
      exact ⟨rfl, fun _ => ⟨honceNew, hVSimNew⟩⟩
    | succ k =>
      exact hbnds k b' ab' hsc (by simpa using hbi) (by simpa using habi)
  · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ m =>
        simp at hb₁ hab₁; subst hb₁; subst hab₁
        have hb₂' : env[m]? = some b₂ := by simpa using hb₂
        have hab₂' : aenv[m]? = some ab₂ := by simpa using hab₂
        obtain ⟨_, hneB2⟩ := hsim.2.2.2.2.2.1 m b₂ ab₂ hsj hb₂' hab₂'
        have hv₂ := (hneB2 hne₂).2
        have hsrc2 : ∀ x, (effVal ab₂).src = some x → x < σ.st.size := fun x hx => (hv₂.2.2.1 x hx).1
        obtain ⟨hd1, _, hd3, _, _, _, _⟩ := hdisjV m b₂ ab₂ hsj hb₂' hab₂' hne₂
        refine ⟨?_, ?_⟩
        · intro ha₁₂ htr₁₂ ha₂₂ hdd l hor hr₂
          have ha₁₁ := hActiveToOld ha₁₂
          have ha₂₁ := ActiveVal.of_AStateLe hok₁ hle hv₂.2.1 hsrc2 ha₂₂
          have htr₁₁ := hTransToOld htr₁₂
          have hdd' : ∀ d, d ∈ bv.deps → ¬ (d ∈ (effVal ab₂).deps) := fun d hd =>
            hdd d (mem_effVal_deps_iff.mpr (Or.inr ⟨hd, Nat.ne_of_lt (hdepsLt d hd)⟩))
          exact hd1 ha₁₁ htr₁₁ ha₂₁ hdd' l hor hr₂
        · intro ha₁₂ _ ha₂₂ l hft hr₂
          have ha₁₁ := hActiveToOld ha₁₂
          have ha₂₁ := ActiveVal.of_AStateLe hok₁ hle hv₂.2.1 hsrc2 ha₂₂
          by_cases hu : b.mode.usage = .once
          · exact hOnceFootEnv hu m b₂ ab₂ hsj hb₂' hab₂' hne₂ ha₂₁ l hft hr₂
          · by_cases hoO : bv.onceOnly = true
            · exact hd3 ha₁₁ (Or.inl hoO) ha₂₁ (by rw [hsrcNone]; simp) l hft hr₂
            · exact False.elim (hNotOnce (Bool.eq_false_iff.mpr hoO) hu l hft)
    | succ k =>
      cases j with
      | zero =>
        simp at hb₂ hab₂; subst hb₂; subst hab₂
        have hb₁' : env[k]? = some b₁ := by simpa using hb₁
        have hab₁' : aenv[k]? = some ab₁ := by simpa using hab₁
        obtain ⟨_, hneB1⟩ := hsim.2.2.2.2.2.1 k b₁ ab₁ hsi hb₁' hab₁'
        have hv₁ := (hneB1 hne₁).2
        have hsrc1 : ∀ x, (effVal ab₁).src = some x → x < σ.st.size := fun x hx => (hv₁.2.2.1 x hx).1
        obtain ⟨_, hd2, _, hd4, _, _, _⟩ := hdisjV k b₁ ab₁ hsi hb₁' hab₁' hne₁
        refine ⟨?_, ?_⟩
        · intro ha₁₂ htr₁₂ ha₂₂ hdd l hor hr₂
          have ha₁₁ := ActiveVal.of_AStateLe hok₁ hle hv₁.2.1 hsrc1 ha₁₂
          have ha₂₁ := hActiveToOld ha₂₂
          have htr₁₁ : Transferable σ NoKill (effVal ab₁) :=
            Transferable.of_AStateLe hok₁ hle hv₁.2.1 hsrc1 (fun _ h => h) htr₁₂
          have hdd' : ∀ d, d ∈ (effVal ab₁).deps → ¬ (d ∈ bv.deps) := fun d hd1 hd2 =>
            hdd d hd1 (mem_effVal_deps_iff.mpr (Or.inr ⟨hd2, Nat.ne_of_lt (hdepsLt d hd2)⟩))
          exact hd2 ha₁₁ htr₁₁ ha₂₁ hdd' l hor hr₂
        · intro ha₁₂ hf₁₂ ha₂₂ l hft hr₂
          have ha₁₁ := ActiveVal.of_AStateLe hok₁ hle hv₁.2.1 hsrc1 ha₁₂
          have ha₂₁ := hActiveToOld ha₂₂
          have hf₁₁ := FootActive.of_AStateLe hok₁ hle hv₁.2.1 hsrc1 hf₁₂
          exact hd4 ha₁₁ hf₁₁ ha₂₁ (by rw [hsrcNone]; simp) l hft hr₂
      | succ m =>
        exact hdisj k m b₁ b₂ ab₁ ab₂ (fun h => hij (congrArg Nat.succ h)) hsi hsj
          (by simpa using hb₁) (by simpa using hab₁) (by simpa using hb₂) (by simpa using hab₂) hne₁ hne₂

/-- Close a region pair `(s_a, s_c)` in `Sim`. -/
theorem Sim_closeRegion {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} (s_a s_c : Nat) (hsa : s_a ≠ 1)
    (hIok' : InterpOk (σ.closeReg s_a) { st with regions := st.regions.filter (· != s_c) } I)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    Sim P ext B { st with regions := st.regions.filter (· != s_c) } Frame NoKill NoSpend Scope
      env aenv (σ.closeReg s_a) I envFoot :=
  Sim_step (Nat.le_refl B) (AStateLe_closeReg s_a σ) (hsim.2.1.closeReg hsa) hIok'
    (RegsFuture.closeRegion st s_c) (PreservesOnceShell.refl _) (StaticStrFresh.refl _)
    (fun _ _ _ h => h) (PreservesActiveEnv.refl _ _ _ _ _) hsim

/-- Extend `(Frame, NoKill, NoSpend)` in `Sim` to protect an already-evaluated value `(v, av, Foot)`
whenever `ActiveVal σ_end av` holds in a future state `σ_end` (used for sequential evaluation `e₁; e₂`). -/
theorem Sim_frame_extend {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ σ_end : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {Foot : Nat → Prop} {av : AVal} {v : Val}
    (hle : AStateLe σ σ_end)
    (hdepsV : ∀ d ∈ av.deps, d < σ.st.size)
    (hsrcV : ∀ x, av.src = some x → x < σ.st.size ∧ x ∈ av.deps)
    (hdisjV : ValEnvDisj P st NoKill Scope env aenv σ envFoot Foot av v)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    let Frame' : Nat → Prop := fun l => Frame l ∨ (ActiveVal σ_end av ∧ Reach st.heap v l)
    let NoKill' : Nat → Prop := fun d => NoKill d ∨ (ActiveVal σ_end av ∧ d ∈ av.deps)
    let NoSpend' : Nat → Prop :=
      fun d => NoSpend d ∨ (ActiveVal σ_end av ∧ IsOnceSrc σ_end av ∧ d ∈ av.deps ∧ σ.once[d]? = some true)
    Sim P ext B st Frame' NoKill' NoSpend' Scope env aenv σ I envFoot := by
  intro Frame' NoKill' NoSpend'
  obtain ⟨hlen, hok, hIok, hids, huniqId, hbnds, hdisj⟩ := hsim
  have hsrcLt : ∀ x, av.src = some x → x < σ.st.size := fun x hx => (hsrcV x hx).1
  refine ⟨hlen, hok, hIok, hids, huniqId, ?_, ?_⟩
  · intro i b ab hsc hbi habi
    obtain ⟨hmode, hneBody⟩ := hbnds i b ab hsc hbi habi
    refine ⟨hmode, fun hne => ?_⟩
    obtain ⟨honce, hv⟩ := hneBody hne
    refine ⟨honce, VSim_evolve (Nat.le_refl B) hok (AStateLe.refl σ) (RegsFuture.refl st)
      (PreservesOnceShell.refl _) (StaticStrFresh.refl _) (fun _ _ _ h => h)
      (fun _ h => Or.inl h) (fun _ => PreservesLocs.refl _ _) ?_ ?_ ?_ hv⟩
    · intro ha hoO hnk' l hl hF'
      rcases hF' with hF | ⟨haEnd, hrV⟩
      · exact ((hv.2.2.2.2 ha).2.2.2.2.2.1 hoO).2.1 (fun x hx hnk => hnk' x hx (Or.inl hnk)) l hl hF
      · have hsrcNe : av.src ≠ some ab.id := by
          intro heq
          have hmem : ab.id ∈ av.deps := (hsrcV ab.id heq).2
          exact hnk' ab.id rfl (Or.inr ⟨haEnd, hmem⟩)
        have haV1 := ActiveVal.of_AStateLe hok hle hdepsV hsrcLt haEnd
        exact (hdisjV i b ab hsc hbi habi hne).2.2.2.1 ha (Or.inl hoO) haV1 hsrcNe l hl hrV
    · intro ha his hns' l hl hF'
      rcases hF' with hF | ⟨haEnd, hrV⟩
      · exact ((hv.2.2.2.2 ha).2.2.2.2.2.2.1 his).2.1 (fun d hd ho hns => hns' d hd ho (Or.inl hns)) l hl hF
      · have haV1 := ActiveVal.of_AStateLe hok hle hdepsV hsrcLt haEnd
        have hsrcNe : av.src ≠ some ab.id := by
          intro heq
          have hmem : ab.id ∈ av.deps := (hsrcV ab.id heq).2
          obtain ⟨id, hsrcB, honceB⟩ := his
          dsimp [effVal] at hsrcB; cases hsrcB
          have hisEnd : IsOnceSrc σ_end av :=
            (IsOnceSrc.iff_AStateLe hok hle hsrcLt).mp ⟨ab.id, heq, honceB⟩
          exact hns' ab.id (List.mem_cons_self ..) honceB (Or.inr ⟨haEnd, hisEnd, hmem, honceB⟩)
        exact (hdisjV i b ab hsc hbi habi hne).2.2.2.1 ha (Or.inr ⟨his, ha.2 his⟩) haV1 hsrcNe l hl hrV
    · intro ha htr' l hor hF'
      have htr : Transferable σ NoKill (effVal ab) :=
        ⟨htr'.1, htr'.2.1, htr'.2.2.1, htr'.2.2.2.1,
         fun d hd => ⟨(htr'.2.2.2.2 d hd).1, fun hnk => (htr'.2.2.2.2 d hd).2 (Or.inl hnk)⟩⟩
      rcases hF' with hF | ⟨haEnd, hrV⟩
      · exact (((hv.2.2.2.2 ha).2.2.2.2.2.2.2 htr).2 l hor).1 hF
      · have haV1 := ActiveVal.of_AStateLe hok hle hdepsV hsrcLt haEnd
        have hdd : ∀ d, d ∈ (effVal ab).deps → ¬ (d ∈ av.deps) :=
          fun d hd hdv => (htr'.2.2.2.2 d hd).2 (Or.inr ⟨haEnd, hdv⟩)
        exact (hdisjV i b ab hsc hbi habi hne).2.1 ha htr haV1 hdd l hor hrV
  · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    obtain ⟨hdU, hdF⟩ := hdisj i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    refine ⟨fun ha₁ htr₁' => ?_, hdF⟩
    have htr₁ : Transferable σ NoKill (effVal ab₁) :=
      ⟨htr₁'.1, htr₁'.2.1, htr₁'.2.2.1, htr₁'.2.2.2.1,
       fun d hd => ⟨(htr₁'.2.2.2.2 d hd).1, fun hnk => (htr₁'.2.2.2.2 d hd).2 (Or.inl hnk)⟩⟩
    exact hdU ha₁ htr₁

/-- Helper: `StateJoinGe pre post σ_join` acts like `AStateLe` on all bindings `< pre.st.size`. -/
theorem ValidDeps.of_StateJoinGe {pre post σ_join : AState} {deps : List Nat}
    (hge : StateJoinGe pre post σ_join)
    (hbnd : ∀ d ∈ deps, d < pre.st.size)
    (hvJ : ValidDeps σ_join deps) : ValidDeps post deps := by
  intro d hd
  have hlt := hbnd d hd
  have h1 := hge.2.2.2.2.2.1 d hlt
  have ⟨_, hneJ⟩ := hvJ d hd
  cases hp : post.st[d]? with
  | none => rw [hp] at h1; exact False.elim h1
  | some bp =>
    rw [hp] at h1
    have hltP : d < post.st.size := (Array.getElem?_eq_some_iff.mp hp).1
    refine ⟨hltP, fun hdead => ?_⟩
    cases hdead
    cases hj : σ_join.st[d]? with
    | none => rw [hj] at h1; exact h1
    | some bj =>
      rw [hj] at h1
      cases bj with
      | dead => exact hneJ hj
      | live | shared => exact h1

theorem LiveDeps.of_StateJoinGe {pre post σ_join : AState} {NoKill : Nat → Prop} {deps : List Nat}
    (hge : StateJoinGe pre post σ_join)
    (hbnd : ∀ d ∈ deps, d < pre.st.size)
    (hlJ : LiveDeps σ_join NoKill deps) : LiveDeps post NoKill deps := by
  intro d hd
  have hlt := hbnd d hd
  have ⟨hliveJ, hnk⟩ := hlJ d hd
  have h1 := hge.2.2.2.2.2.1 d hlt
  rw [hliveJ] at h1
  cases hp : post.st[d]? with
  | none => rw [hp] at h1; exact False.elim h1
  | some bp =>
    rw [hp] at h1
    cases bp with
    | live => exact ⟨rfl, hnk⟩
    | shared | dead => exact False.elim h1

theorem IsOnceSrc.iff_StateJoinGe {pre post σ_join : AState} {av : AVal}
    (hokPre : AStateOk pre) (hlePP : AStateLe pre post) (hge : StateJoinGe pre post σ_join)
    (hsrc : ∀ x, av.src = some x → x < pre.st.size) :
    IsOnceSrc post av ↔ IsOnceSrc σ_join av := by
  constructor
  · rintro ⟨id, hs, ho⟩
    have hlt : id < pre.once.size := by rw [← hokPre.1]; exact hsrc id hs
    have hEq := hlePP.2.2.2.1 id hlt
    exact ⟨id, hs, by rw [hge.2.1, ← hEq]; exact ho⟩
  · rintro ⟨id, hs, ho⟩
    have hlt : id < pre.once.size := by rw [← hokPre.1]; exact hsrc id hs
    have hEq := hlePP.2.2.2.1 id hlt
    exact ⟨id, hs, by rw [hEq, ← hge.2.1]; exact ho⟩

theorem UnspentOnceDeps.of_StateJoinGe {pre post σ_join : AState} {deps : List Nat}
    (hokPre : AStateOk pre) (hokPost : AStateOk post) (hlePP : AStateLe pre post)
    (hge : StateJoinGe pre post σ_join) (hbnd : ∀ d ∈ deps, d < pre.st.size)
    (huJ : UnspentOnceDeps σ_join deps) : UnspentOnceDeps post deps := by
  intro d hd hoP
  have hlt : d < pre.st.size := hbnd d hd
  have hltOnce : d < pre.once.size := by rw [← hokPre.1]; exact hlt
  have hltSpPre : d < pre.spent.size := by rw [← hokPre.2.1]; exact hlt
  have hltSpPost : d < post.spent.size := by rw [← hokPost.2.1]; exact Nat.lt_of_lt_of_le hlt hlePP.1
  have hoJ : σ_join.once[d]? = some true := by
    rw [hge.2.1, ← hlePP.2.2.2.1 d hltOnce]; exact hoP
  have hspJ : σ_join.spent[d]? = some false := huJ d hd hoJ
  cases hspP : post.spent[d]? with
  | none =>
    have := Array.getElem?_eq_none_iff.mp hspP
    omega
  | some b =>
    cases b with
    | false => rfl
    | true =>
      have htrueJ := hge.2.2.2.2.2.2 d hltSpPre hspP
      rw [hspJ] at htrueJ
      cases htrueJ

/-- Lift `Sim` from a case alternative's post-state `post` to the joined state `σ_join`
via `StateJoinGe pre post σ_join`. -/
theorem Sim_of_StateJoinGe {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {pre post σ_join : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    (hokPre : AStateOk pre) (hlePP : AStateLe pre post) (hge : StateJoinGe pre post σ_join)
    (hokJoin : AStateOk σ_join) (hIokJoin : InterpOk σ_join st I)
    (hidsPre : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ab.id < pre.st.size)
    (hdepsPre : ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ d ∈ (effVal ab).deps, d < pre.st.size)
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv post I envFoot) :
    Sim P ext B st Frame NoKill NoSpend Scope env aenv σ_join I envFoot := by
  obtain ⟨hlen, hokPost, _, _, huniqId, hbnds, hdisj⟩ := hsim
  have hActive : ∀ i ab, Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ActiveVal σ_join (effVal ab) → ActiveVal post (effVal ab) := by
    intro i ab hsc habi hne haJ
    have hdPre := hdepsPre i ab hsc habi hne
    have hsrcPre : ∀ x, (effVal ab).src = some x → x < pre.st.size := fun x hx => by
      dsimp [effVal] at hx; cases hx; exact hidsPre i ab habi
    refine ⟨ValidDeps.of_StateJoinGe hge hdPre haJ.1, fun hisP => ?_⟩
    exact UnspentOnceDeps.of_StateJoinGe hokPre hokPost hlePP hge hdPre
      (haJ.2 ((IsOnceSrc.iff_StateJoinGe hokPre hlePP hge hsrcPre).mp hisP))
  refine ⟨hlen, hokJoin, hIokJoin,
    fun i ab hab => by rw [hge.1]; exact hidsPre i ab hab,
    huniqId, ?_, ?_⟩
  · intro i b ab hsc hbi habi
    obtain ⟨hmode, hneBody⟩ := hbnds i b ab hsc hbi habi
    refine ⟨hmode, fun hne => ?_⟩
    obtain ⟨honceP, hvP⟩ := hneBody hne
    have hltOncePre : ab.id < pre.once.size := by rw [← hokPre.1]; exact hidsPre i ab habi
    have honceJ : σ_join.once[ab.id]? = some (ab.mode.usage == .once) := by
      rw [hge.2.1, ← hlePP.2.2.2.1 ab.id hltOncePre]; exact honceP
    refine ⟨honceJ, ?_⟩
    obtain ⟨hregs, _, _, hspent, hbody⟩ := hvP
    have hdPre := hdepsPre i ab hsc habi hne
    have hsrcPre : ∀ x, (effVal ab).src = some x → x < pre.st.size := fun x hx => by
      dsimp [effVal] at hx; cases hx; exact hidsPre i ab habi
    have hisIff := IsOnceSrc.iff_StateJoinGe hokPre hlePP hge hsrcPre
    refine ⟨fun r hr => Nat.lt_of_lt_of_le (hregs r hr) hge.2.2.2.2.1,
      fun d hd => by rw [hge.1]; exact hdPre d hd,
      fun x hx => by dsimp [effVal] at hx; cases hx; exact ⟨by rw [hge.1]; exact hidsPre i ab habi, List.mem_cons_self ..⟩,
      fun hvJ hisJ => hspent (ValidDeps.of_StateJoinGe hge hdPre hvJ) (hisIff.mpr hisJ),
      fun haJ => ?_⟩
    have haP := hActive i ab hsc habi hne haJ
    obtain ⟨hbase, hopen, hcf, hcls, hplain, honceOnly, honceSrc, htrans⟩ := hbody haP
    refine ⟨hbase, hopen, hcf,
      fun hnoJ hne => hcls (fun hP => hnoJ (hisIff.mp hP)) hne,
      fun ⟨hnoJ, hoO⟩ => hplain ⟨fun hP => hnoJ (hisIff.mp hP), hoO⟩,
      honceOnly,
      fun hisJ => ?_,
      fun htrJ => htrans ⟨htrJ.1, htrJ.2.1, htrJ.2.2.1, fun hP => htrJ.2.2.2.1 (hisIff.mp hP),
        LiveDeps.of_StateJoinGe hge hdPre htrJ.2.2.2.2⟩⟩
    obtain ⟨hft, hnsP, hfun⟩ := honceSrc (hisIff.mpr hisJ)
    refine ⟨hft, fun hnsJ => hnsP fun d hd hoP => ?_, hfun⟩
    have hltO : d < pre.once.size := by rw [← hokPre.1]; exact hdPre d hd
    exact hnsJ d hd (by rw [hge.2.1, ← hlePP.2.2.2.1 d hltO]; exact hoP)
  · intro i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    obtain ⟨hdU, hdF⟩ := hdisj i j b₁ b₂ ab₁ ab₂ hij hsi hsj hb₁ hab₁ hb₂ hab₂ hne₁ hne₂
    have hdPre1 := hdepsPre i ab₁ hsi hab₁ hne₁
    have hsrcPre1 : ∀ x, (effVal ab₁).src = some x → x < pre.st.size := fun x hx => by
      dsimp [effVal] at hx; cases hx; exact hidsPre i ab₁ hab₁
    refine ⟨?_, ?_⟩
    · intro ha₁J htr₁J ha₂J hdd l hor hr₂
      have ha₁P := hActive i ab₁ hsi hab₁ hne₁ ha₁J
      have ha₂P := hActive j ab₂ hsj hab₂ hne₂ ha₂J
      have htr₁P : Transferable post NoKill (effVal ab₁) :=
        ⟨htr₁J.1, htr₁J.2.1, htr₁J.2.2.1,
         fun hP => htr₁J.2.2.2.1 ((IsOnceSrc.iff_StateJoinGe hokPre hlePP hge hsrcPre1).mp hP),
         LiveDeps.of_StateJoinGe hge hdPre1 htr₁J.2.2.2.2⟩
      exact hdU ha₁P htr₁P ha₂P hdd l hor hr₂
    · intro ha₁J hf₁J ha₂J l hft hr₂
      have ha₁P := hActive i ab₁ hsi hab₁ hne₁ ha₁J
      have ha₂P := hActive j ab₂ hsj hab₂ hne₂ ha₂J
      have hf₁P : FootActive post (effVal ab₁) := by
        rcases hf₁J with ho | ⟨hisJ, huspJ⟩
        · exact Or.inl ho
        · exact Or.inr ⟨(IsOnceSrc.iff_StateJoinGe hokPre hlePP hge hsrcPre1).mpr hisJ,
            UnspentOnceDeps.of_StateJoinGe hokPre hokPost hlePP hge hdPre1 huspJ⟩
      exact hdF ha₁P hf₁P ha₂P l hft hr₂

/-- Lift `VSim` of a case alternative's result `r_j` (in `post`) to the joined result `r_join`
(in `σ_join`), using Bug #11's `valid r_j` + `isUniq` own-demotion before `deps.filter`. -/
theorem VSim_of_ValJoinGe {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend : Nat → Prop}
    {pre post σ_join : AState} {I : Interp} {r_j r_join : AVal} {v : Val}
    (hge : StateJoinGe pre post σ_join)
    (hclsEq : r_join.cls = r_j.cls)
    (hsrcNone : r_join.src = none)
    (hoJ : r_j.onceOnly = false) (hoJoin : r_join.onceOnly = false)
    (hnotOnceJ : ¬ IsOnceSrc post r_j)
    (hvalidJ : ValidDeps post r_j.deps)
    (huniq : r_join.own = .uniq → r_j.own = .uniq ∧ ∀ d ∈ r_j.deps, post.st[d]? = some .live)
    (hregsBnd : ∀ r ∈ r_join.regs, r < σ_join.nextRegion)
    (hregsSub : ∀ r ∈ r_j.regs, r ∈ r_join.regs)
    (hdepsBnd : ∀ d ∈ r_join.deps, d < pre.st.size)
    (hdepsSub : ∀ d ∈ r_j.deps, d < pre.st.size → d ∈ r_join.deps)
    (hnkBnd : ∀ d, NoKill d → d < pre.st.size)
    (hfunCoerce : FunOkAt P ext B st r_j.skel false (fun _ => False) v →
      FunOkAt P ext B st r_join.skel false (fun _ => False) v)
    (hv : VSim P ext B st Frame NoKill NoSpend post I (fun _ => False) r_j v) :
    VSim P ext B st Frame NoKill NoSpend σ_join I (fun _ => False) r_join v := by
  have hnotOnceJoin : ¬ IsOnceSrc σ_join r_join := by
    rintro ⟨_, hs, _⟩; rw [hsrcNone] at hs; cases hs
  have haJ : ActiveVal post r_j := ⟨hvalidJ, fun his => absurd his hnotOnceJ⟩
  obtain ⟨hbase, hopen, hcf, hcls, hplain, _, _, htrans⟩ := hv.2.2.2.2 haJ
  obtain ⟨hnoOnce, _, hfunJ⟩ := hplain ⟨hnotOnceJ, hoJ⟩
  refine ⟨hregsBnd,
    fun d hd => by rw [hge.1]; exact hdepsBnd d hd,
    fun _ hs => (by rw [hsrcNone] at hs; cases hs),
    fun _ his => absurd his hnotOnceJoin,
    fun _ => ?_⟩
  refine ⟨hbase, ?_, hcf,
    fun _ hne => hcls hnotOnceJ (by rw [← hclsEq]; exact hne),
    fun _ => ⟨hnoOnce, fun _ h => h, hfunCoerce hfunJ⟩,
    fun ho => (by rw [hoJoin] at ho; cases ho),
    fun his => absurd his hnotOnceJoin,
    fun htr => ?_⟩
  · exact hopen.mono fun c hc => by
      obtain ⟨r, hr, hcr⟩ := Interp.mem_regsOf.mp hc
      exact Interp.mem_regsOf.mpr ⟨r, hregsSub r hr, hcr⟩
  · obtain ⟨hclsVal, hownJoin, _, _, hliveJoin⟩ := htr
    obtain ⟨hownJ, hlivePost⟩ := huniq hownJoin
    have htrJ : Transferable post NoKill r_j := by
      refine ⟨by rw [← hclsEq]; exact hclsVal, hownJ, hoJ, hnotOnceJ,
        fun d hd => ⟨hlivePost d hd, fun hnk => ?_⟩⟩
      exact (hliveJoin d (hdepsSub d hd (hnkBnd d hnk))).2 hnk
    exact htrans htrJ

/-- Lift `ValEnvDisj` of a case alternative's result `r_j` (in `post`) to `r_join` (in `σ_join`). -/
theorem ValEnvDisj_of_ValJoinGe {P : Prog} {st : St} {NoKill Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {pre post σ_join : AState}
    {envFoot : Nat → Nat → Prop} {r_j r_join : AVal} {rv : Val}
    (hokPre : AStateOk pre) (hokPost : AStateOk post) (hlePP : AStateLe pre post)
    (hge : StateJoinGe pre post σ_join)
    (hclsEq : r_join.cls = r_j.cls)
    (hsrcNone : r_join.src = none)
    (hoJ : r_j.onceOnly = false)
    (hnotOnceJ : ¬ IsOnceSrc post r_j)
    (hvalidJ : ValidDeps post r_j.deps)
    (huniq : r_join.own = .uniq → r_j.own = .uniq ∧ ∀ d ∈ r_j.deps, post.st[d]? = some .live)
    (hdepsSub : ∀ d ∈ r_j.deps, d < pre.st.size → d ∈ r_join.deps)
    (hnkBnd : ∀ d, NoKill d → d < pre.st.size)
    (hidsPre : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ab.id < pre.st.size)
    (hdepsPre : ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ d ∈ (effVal ab).deps, d < pre.st.size)
    (hdisj : ValEnvDisj P st NoKill Scope env aenv post envFoot (fun _ => False) r_j rv) :
    ValEnvDisj P st NoKill Scope env aenv σ_join envFoot (fun _ => False) r_join rv := by
  have haJ : ActiveVal post r_j := ⟨hvalidJ, fun his => absurd his hnotOnceJ⟩
  intro i b ab hsi hbi habi hne
  have hdPre := hdepsPre i ab hsi habi hne
  have hsrcPre : ∀ x, (effVal ab).src = some x → x < pre.st.size := fun x hx => by
    dsimp [effVal] at hx; cases hx; exact hidsPre i ab habi
  have hActiveB : ActiveVal σ_join (effVal ab) → ActiveVal post (effVal ab) := fun haB =>
    ⟨ValidDeps.of_StateJoinGe hge hdPre haB.1, fun hisP =>
      UnspentOnceDeps.of_StateJoinGe hokPre hokPost hlePP hge hdPre
        (haB.2 ((IsOnceSrc.iff_StateJoinGe hokPre hlePP hge hsrcPre).mp hisP))⟩
  obtain ⟨h1, h2, _, h4, _, h6, _⟩ := hdisj i b ab hsi hbi habi hne
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ htrJoin haB hdd l hor hrB
    obtain ⟨hclsVal, hownJoin, _, _, hliveJoin⟩ := htrJoin
    obtain ⟨hownJ, hlivePost⟩ := huniq hownJoin
    have htrJ : Transferable post NoKill r_j := by
      refine ⟨by rw [← hclsEq]; exact hclsVal, hownJ, hoJ, hnotOnceJ,
        fun d hd => ⟨hlivePost d hd, fun hnk => ?_⟩⟩
      exact (hliveJoin d (hdepsSub d hd (hnkBnd d hnk))).2 hnk
    have hddJ : ∀ d, d ∈ r_j.deps → ¬ (d ∈ (effVal ab).deps) := fun d hd hdB =>
      hdd d (hdepsSub d hd (hdPre d hdB)) hdB
    exact h1 haJ htrJ (hActiveB haB) hddJ l hor hrB
  · intro haB htrB _ hdd l hor hrV
    have htrBP : Transferable post NoKill (effVal ab) :=
      ⟨htrB.1, htrB.2.1, htrB.2.2.1,
       fun hP => htrB.2.2.2.1 ((IsOnceSrc.iff_StateJoinGe hokPre hlePP hge hsrcPre).mp hP),
       LiveDeps.of_StateJoinGe hge hdPre htrB.2.2.2.2⟩
    have hddJ : ∀ d, d ∈ (effVal ab).deps → ¬ (d ∈ r_j.deps) := fun d hdB hdJ =>
      hdd d hdB (hdepsSub d hdJ (hdPre d hdB))
    exact h2 (hActiveB haB) htrBP haJ hddJ l hor hrV
  · intro _ _ _ _ _ h; exact False.elim h
  · intro haB hfB _ _ l hft hrV
    have hfBP : FootActive post (effVal ab) := by
      rcases hfB with ho | ⟨hisJ, huspJ⟩
      · exact Or.inl ho
      · exact Or.inr ⟨(IsOnceSrc.iff_StateJoinGe hokPre hlePP hge hsrcPre).mpr hisJ,
          UnspentOnceDeps.of_StateJoinGe hokPre hokPost hlePP hge hdPre huspJ⟩
    have hsrcNe : r_j.src ≠ some ab.id := by
      intro hEq
      rcases hfBP with ho | ⟨⟨id, hs, ho⟩, _⟩
      · have htrue : r_j.onceOnly = true := h6 hEq ho
        rw [hoJ] at htrue; cases htrue
      · dsimp [effVal] at hs; cases hs
        exact hnotOnceJ ⟨ab.id, hEq, ho⟩
    exact h4 (hActiveB haB) hfBP haJ hsrcNe l hft hrV
  · intro _ _ hs; rw [hsrcNone] at hs; cases hs
  · intro hs _; rw [hsrcNone] at hs; cases hs
  · intro _ hs; rw [hsrcNone] at hs; cases hs

end IxC.Resource.Proof
