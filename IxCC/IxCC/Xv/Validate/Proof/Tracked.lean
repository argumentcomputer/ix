import IxCC.Xv.Validate.Check
import IxCC.Xv.Validate.Proof.State

/-!
# The tracked walk is the validator's walk

`checkBlock` walks a block on `Tracked`: the state with the registers it may hold and the
outgoing cells that may hold something. With the invariant `Tracked.Inv` (the state canonical,
its rows nonempty, every register of a row listed, every outgoing cell holding something listed,
and only outgoing cells listed), each of `Tracked`'s operations gives exactly the state
`AState`'s gives (`Tracked.Inv.forget`, `.clearOutArgs`, `.define`, `.stepMove`, `ofList_st`):
a register no row holds is forgotten by doing nothing, and erasing the listed cells is clearing
every outgoing cell. So every step of the walk gives the plain walk's result or error
(`Tracks`), and `checkBlock` is `checkBlockList` (`checkBlock_eq_list`).
-/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg Operand)
open IxCC.Xv.Alloc (Edit Output BlockOut takeAt editsOrdered)
open NatMap (Canon)

/-! ## Lookups of the operations -/

theorem find?_addRegs (m : NatMap Unit) (vs : List VReg) (v : VReg) :
    (Tracked.addRegs m vs).find? v = if v ∈ vs then some () else m.find? v := by
  induction vs generalizing m with
  | nil => simp [Tracked.addRegs]
  | cons w ws ih =>
    have e : Tracked.addRegs m (w :: ws) = Tracked.addRegs (m.insert w ()) ws := rfl
    rw [e, ih, NatMap.find?_insert']
    by_cases h1 : v ∈ ws
    · rw [if_pos h1, if_pos (List.mem_cons_of_mem w h1)]
    · rw [if_neg h1]
      by_cases h2 : v = w
      · rw [if_pos h2, if_pos (by rw [h2]; exact List.mem_cons_self)]
      · rw [if_neg h2, if_neg (fun hm => (List.mem_cons.1 hm).elim h2 h1)]

theorem AState.find?_set (a : AState) (l : Loc) (vs : VSet) (k : Nat) :
    (a.set l vs).find? k = if k = locKey l then (if vs = [] then none else some vs) else a.find? k := by
  unfold AState.set
  cases vs with
  | nil =>
    rw [NatMap.find?_erase']
    by_cases h : k = locKey l
    · rw [if_pos h, if_pos h, if_pos rfl]
    · rw [if_neg h, if_neg h]
  | cons v vs =>
    simp only
    rw [NatMap.find?_insert']
    by_cases h : k = locKey l
    · rw [if_pos h, if_pos h, if_neg (List.cons_ne_nil v vs)]
    · rw [if_neg h, if_neg h]

theorem AState.canon_set {a : AState} (h : Canon a) (l : Loc) (vs : VSet) : Canon (a.set l vs) := by
  unfold AState.set
  cases vs with
  | nil => exact h.erase _
  | cons _ _ => exact h.insert _ _

theorem find?_foldl_erase (ks : List Nat) (m : AState) (k : Nat) :
    (ks.foldl (fun a k => a.erase k) m).find? k = if k ∈ ks then none else m.find? k := by
  induction ks generalizing m with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [ih, NatMap.find?_erase']
    by_cases h1 : k ∈ js
    · rw [if_pos h1, if_pos (List.mem_cons_of_mem j h1)]
    · rw [if_neg h1]
      by_cases h2 : k = j
      · rw [if_pos h2, if_pos (by rw [h2]; exact List.mem_cons_self)]
      · rw [if_neg h2, if_neg (fun hm => (List.mem_cons.1 hm).elim h2 h1)]

theorem canon_foldl_erase (ks : List Nat) {m : AState} (h : Canon m) :
    Canon (ks.foldl (fun a k => a.erase k) m) := by
  induction ks generalizing m with
  | nil => exact h
  | cons j js ih => exact ih (h.erase j)

/-! ## The invariant -/

/-- What the tracked walk keeps true. -/
structure Tracked.Inv (s : Tracked) : Prop where
  canon : Canon s.st
  nonempty : ∀ k vs, s.st.find? k = some vs → vs ≠ []
  regs : ∀ k vs, s.st.find? k = some vs → ∀ v ∈ vs, s.regs.find? v ≠ none
  outs : ∀ k, isOutArgKey k = true → s.st.find? k ≠ none → k ∈ s.outs
  outsOut : ∀ k ∈ s.outs, isOutArgKey k = true

theorem Tracked.Inv.empty : Tracked.empty.Inv where
  canon := .leaf
  nonempty := by simp [Tracked.empty, AState.empty]
  regs := by simp [Tracked.empty, AState.empty]
  outs := by simp [Tracked.empty, AState.empty]
  outsOut := by simp [Tracked.empty]

theorem mem_noteOut {outs : List Nat} {l : Loc} {k : Nat} :
    k ∈ Tracked.noteOut outs l ↔ (k = locKey l ∧ isOutArgKey (locKey l) = true) ∨ k ∈ outs := by
  unfold Tracked.noteOut
  split <;> simp_all

theorem Tracked.Inv.setRow {s : Tracked} (h : s.Inv) (l : Loc) (vs : VSet) : (s.setRow l vs).Inv where
  canon := AState.canon_set h.canon l vs
  nonempty := fun k ws hk => by
    simp only [Tracked.setRow, AState.find?_set] at hk
    split at hk
    · split at hk
      · simp at hk
      · next hne => cases hk; exact hne
    · exact h.nonempty k ws hk
  regs := fun k ws hk v hv => by
    simp only [Tracked.setRow, AState.find?_set] at hk
    simp only [Tracked.setRow, find?_addRegs]
    split at hk
    · split at hk
      · simp at hk
      · cases hk; simp [hv]
    · split
      · simp
      · exact h.regs k ws hk v hv
  outs := fun k hk hne => by
    simp only [Tracked.setRow, AState.find?_set] at hne
    simp only [Tracked.setRow, mem_noteOut]
    split at hne
    · next he => subst he; exact .inl ⟨rfl, hk⟩
    · exact .inr (h.outs k hk hne)
  outsOut := fun k hk => by
    simp only [Tracked.setRow, mem_noteOut] at hk
    rcases hk with ⟨rfl, ho⟩ | hk
    · exact ho
    · exact h.outsOut k hk

/-! ## Each operation is `AState`'s -/

theorem Tracked.ofList_inv (facts : List (Loc × List VReg)) :
    (Tracked.ofList facts).Inv ∧ (Tracked.ofList facts).st = AState.ofList facts := by
  suffices ∀ (fs : List (Loc × List VReg)) (s : Tracked), s.Inv →
      (fs.foldl (fun s (l, vs) => s.setRow l (VSet.ofList (vs ++ s.st.get l))) s).Inv ∧
      (fs.foldl (fun s (l, vs) => s.setRow l (VSet.ofList (vs ++ s.st.get l))) s).st =
        fs.foldl (fun a (l, vs) => a.set l (VSet.ofList (vs ++ a.get l))) s.st from
    this facts _ Tracked.Inv.empty
  intro fs
  induction fs with
  | nil => intro s h; exact ⟨h, rfl⟩
  | cons f fs ih =>
    intro s h
    obtain ⟨l, vs⟩ := f
    exact ih _ (h.setRow _ _)

theorem AState.forget_unlisted {s : Tracked} (h : s.Inv) {v : VReg} (hv : s.regs.find? v = none) :
    s.st.forget v = s.st := by
  apply NatMap.ext (Canon.filterMap _ _) h.canon
  intro k
  rw [NatMap.find?_filterMap']
  cases hk : s.st.find? k with
  | none => rfl
  | some vs =>
    have hnot : v ∉ vs := fun hm => h.regs k vs hk v hm hv
    have he : VSet.erase v vs = vs := by
      unfold VSet.erase
      exact List.filter_eq_self.2 fun x hx => by
        have : x ≠ v := fun e => hnot (e ▸ hx)
        simpa using this
    have hne := h.nonempty k vs hk
    cases vs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp only [Option.bind_some, he]

theorem AState.find?_forget (a : AState) (v : VReg) (k : Nat) :
    (a.forget v).find? k =
      (a.find? k).bind fun vs => if VSet.erase v vs = [] then none else some (VSet.erase v vs) := by
  unfold AState.forget
  rw [NatMap.find?_filterMap']
  cases a.find? k with
  | none => rfl
  | some vs =>
    simp only [Option.bind_some]
    split <;> simp_all

theorem Tracked.Inv.forget {s : Tracked} (h : s.Inv) (v : VReg) :
    (s.forget v).Inv ∧ (s.forget v).st = s.st.forget v := by
  unfold Tracked.forget
  split
  · next hv =>
    refine ⟨⟨Canon.filterMap _ _, ?_, ?_, ?_, h.outsOut⟩, rfl⟩
    · intro k ws hk
      rw [AState.find?_forget] at hk
      cases hk' : s.st.find? k with
      | none => simp [hk'] at hk
      | some vs =>
        simp only [hk', Option.bind_some] at hk
        split at hk
        · simp at hk
        · next hne => cases hk; exact hne
    · intro k ws hk w hw
      rw [AState.find?_forget] at hk
      cases hk' : s.st.find? k with
      | none => simp [hk'] at hk
      | some vs =>
        simp only [hk', Option.bind_some] at hk
        have hw' : w ∈ VSet.erase v vs := by
          split at hk
          · simp at hk
          · cases hk; exact hw
        rw [VSet.mem_erase] at hw'
        rw [NatMap.find?_erase']
        simp only [hw'.2, ↓reduceIte]
        exact h.regs k vs hk' w hw'.1
    · intro k hk hne
      apply h.outs k hk
      rw [AState.find?_forget] at hne
      intro e; simp [e] at hne
  · next hv => exact ⟨h, (AState.forget_unlisted h hv).symm⟩

theorem Tracked.Inv.clearOutArgs {s : Tracked} (h : s.Inv) :
    (s.clearOutArgs).Inv ∧ (s.clearOutArgs).st = s.st.clearOutArgs := by
  have hfind : ∀ k, (s.clearOutArgs).st.find? k = s.st.clearOutArgs.find? k := by
    intro k
    simp only [Tracked.clearOutArgs, find?_foldl_erase, AState.clearOutArgs, NatMap.find?_filterMap']
    by_cases ho : isOutArgKey k = true
    · by_cases hm : k ∈ s.outs
      · simp [hm, ho]
      · have : s.st.find? k = none := by
          cases hf : s.st.find? k with
          | none => rfl
          | some _ => exact absurd (h.outs k ho (by simp [hf])) hm
        simp [hm, this]
    · have hm : k ∉ s.outs := fun hm => ho (h.outsOut k hm)
      cases s.st.find? k <;> simp [hm, ho]
  refine ⟨⟨canon_foldl_erase _ h.canon, ?_, ?_, ?_, by simp [Tracked.clearOutArgs]⟩, ?_⟩
  · intro k vs hk
    simp only [Tracked.clearOutArgs, find?_foldl_erase] at hk
    split at hk
    · simp at hk
    · exact h.nonempty k vs hk
  · intro k vs hk
    simp only [Tracked.clearOutArgs, find?_foldl_erase] at hk
    split at hk
    · simp at hk
    · exact h.regs k vs hk
  · intro k hk hne
    exfalso
    rw [hfind] at hne
    simp [AState.clearOutArgs, NatMap.find?_filterMap', hk] at hne
  · exact NatMap.ext (canon_foldl_erase _ h.canon) (Canon.filterMap _ _) hfind

theorem Tracked.Inv.clear {s : Tracked} (h : s.Inv) (l : Loc) : (s.clear l).Inv where
  canon := h.canon.erase _
  nonempty := fun k vs hk => by
    simp only [Tracked.clear, AState.clear, NatMap.find?_erase'] at hk
    split at hk
    · simp at hk
    · exact h.nonempty k vs hk
  regs := fun k vs hk => by
    simp only [Tracked.clear, AState.clear, NatMap.find?_erase'] at hk
    split at hk
    · simp at hk
    · exact h.regs k vs hk
  outs := fun k hk hne => by
    simp only [Tracked.clear, AState.clear, NatMap.find?_erase'] at hne
    split at hne
    · simp at hne
    · exact h.outs k hk hne
  outsOut := h.outsOut

theorem Tracked.Inv.define {s : Tracked} (h : s.Inv) (defs : List (VReg × Loc)) (clobbers : List Loc) :
    (s.define defs clobbers).Inv ∧ (s.define defs clobbers).st = s.st.define defs clobbers := by
  have h1 : ∀ (ds : List (VReg × Loc)) (s : Tracked), s.Inv →
      (ds.foldl (fun s (v, _) => s.forget v) s).Inv ∧
      (ds.foldl (fun s (v, _) => s.forget v) s).st = ds.foldl (fun a (v, _) => a.forget v) s.st := by
    intro ds
    induction ds with
    | nil => intro s h; exact ⟨h, rfl⟩
    | cons d ds ih =>
      intro s h
      obtain ⟨v, l⟩ := d
      obtain ⟨h', e⟩ := h.forget v
      simp only [List.foldl_cons]
      rw [← e]
      exact ih _ h'
  have h2 : ∀ (cs : List Loc) (s : Tracked), s.Inv →
      (cs.foldl Tracked.clear s).Inv ∧ (cs.foldl Tracked.clear s).st = cs.foldl AState.clear s.st := by
    intro cs
    induction cs with
    | nil => intro s h; exact ⟨h, rfl⟩
    | cons c cs ih => intro s h; exact ih _ (h.clear c)
  have h3 : ∀ (ds : List (VReg × Loc)) (s : Tracked), s.Inv →
      (ds.foldl (fun s (v, l) => s.setRow l [v]) s).Inv ∧
      (ds.foldl (fun s (v, l) => s.setRow l [v]) s).st = ds.foldl (fun a (v, l) => a.set l [v]) s.st := by
    intro ds
    induction ds with
    | nil => intro s h; exact ⟨h, rfl⟩
    | cons d ds ih =>
      intro s h
      obtain ⟨v, l⟩ := d
      exact ih _ (h.setRow l [v])
  obtain ⟨ha, ea⟩ := h1 defs s h
  obtain ⟨hb, eb⟩ := h2 clobbers _ ha
  obtain ⟨hc, ec⟩ := h3 defs _ hb
  refine ⟨hc, ?_⟩
  simp only [Tracked.define, AState.define]
  rw [ec, eb, ea]

theorem Tracked.Inv.stepMove {s : Tracked} (h : s.Inv) (dst src : Loc) : (s.stepMove dst src).Inv where
  canon := AState.canon_set h.canon _ _
  nonempty := fun k vs hk => by
    simp only [Tracked.stepMove, AState.stepMove, AState.find?_set] at hk
    split at hk
    · split at hk
      · simp at hk
      · next hne => cases hk; exact hne
    · exact h.nonempty k vs hk
  regs := fun k vs hk v hv => by
    simp only [Tracked.stepMove, AState.stepMove, AState.find?_set] at hk
    split at hk
    · split at hk
      · simp at hk
      · cases hk
        simp only [AState.get] at hv
        cases hs : s.st.find? (locKey src) with
        | none => simp [hs] at hv
        | some ws => simp only [hs, Option.getD_some] at hv; exact h.regs _ ws hs v hv
    · exact h.regs k vs hk v hv
  outs := fun k hk hne => by
    simp only [Tracked.stepMove, AState.stepMove, AState.find?_set] at hne
    simp only [Tracked.stepMove, mem_noteOut]
    split at hne
    · next he => subst he; exact .inl ⟨rfl, hk⟩
    · exact .inr (h.outs k hk hne)
  outsOut := fun k hk => by
    simp only [Tracked.stepMove, mem_noteOut] at hk
    rcases hk with ⟨rfl, ho⟩ | hk
    · exact ho
    · exact h.outsOut k hk


/-! ## The walk -/

/-- A tracked step and a plain one agree: the same error, or a tracked state that keeps the
invariant and whose state is the plain one. -/
def Tracks {ε : Type} : Except ε Tracked → Except ε AState → Prop
  | .ok s, .ok a => s.Inv ∧ s.st = a
  | .error e, .error e' => e = e'
  | _, _ => False

theorem tracks_ok {ε : Type} {s : Tracked} (h : s.Inv) : Tracks (ε := ε) (.ok s) (.ok s.st) := ⟨h, rfl⟩

theorem Tracked.Inv.callState {a : Tracked} (h : a.Inv) (defs : List (VReg × Loc)) (clobbers : List Loc) :
    ((a.clearOutArgs).define defs clobbers).Inv ∧
      ((a.clearOutArgs).define defs clobbers).st = (a.st.clearOutArgs).define defs clobbers := by
  obtain ⟨h1, e1⟩ := h.clearOutArgs
  obtain ⟨h2, e2⟩ := h1.define defs clobbers
  exact ⟨h2, by rw [e2, e1]⟩

theorem stepOperandsT_tracks (c : Ctx) {a : Tracked} (h : a.Inv) (ops : List (Operand VReg)) (ls : List Loc)
    (row : Bool) : Tracks (stepOperandsT c a ops ls row) (stepOperands c a.st ops ls row) := by
  unfold stepOperandsT stepOperands
  obtain ⟨h', e⟩ := h.define (defsOfPairs (ops.zip ls)) []
  cases h1 : (ops.length == ls.length) <;> cases h2 : operandCode c (ops.zip ls) row <;>
    cases h3 : usesHold a.st (ops.zip ls) <;>
    simp_all [Tracks, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem stepInstT_tracks (c : Ctx) {a : Tracked} (h : a.Inv) (inst : Inst VReg) (ls : List Loc) :
    Tracks (stepInstT c a inst ls) (stepInst c a.st inst ls) := by
  cases inst with
  | call g args rets =>
    unfold stepInstT stepInst
    obtain ⟨h', e⟩ := h.callState (rets.zip (resultLocs rets.length)) ((c.env.clobbers g).map Loc.reg)
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    repeat' split
    all_goals first | exact ⟨h', e⟩ | exact rfl | (simp_all [Tracks]; done) | (exfalso; simp_all; done)
  | move dst src =>
    unfold stepInstT stepInst
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    repeat' split
    all_goals first | exact stepOperandsT_tracks c h _ _ _ | exact rfl | (simp_all [Tracks]; done) | (exfalso; simp_all; done)
  | zero d => exact stepOperandsT_tracks c h _ _ _
  | op o defs args =>
    unfold stepInstT stepInst
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    repeat' split
    all_goals first | exact stepOperandsT_tracks c h _ _ _ | exact rfl | (simp_all [Tracks]; done) | (exfalso; simp_all; done)
  | fused p pargs q defs qargs =>
    unfold stepInstT stepInst
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    repeat' split
    all_goals first | exact stepOperandsT_tracks c h _ _ _ | exact rfl | (simp_all [Tracks]; done) | (exfalso; simp_all; done)

theorem stepTermT_tracks (c : Ctx) {a : Tracked} (h : a.Inv) (t : Term VReg) (ls : List Loc) :
    Tracks (stepTermT c a t ls) (stepTerm c a.st t ls) := by
  cases t <;>
  { unfold stepTermT stepTerm
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    repeat' split
    all_goals first | exact stepOperandsT_tracks c h _ _ _ | exact rfl | exact tracks_ok h | (simp_all [Tracks]; done) | (exfalso; simp_all; done) }

theorem stepEditT_tracks (c : Ctx) {a : Tracked} (h : a.Inv) (e : Edit) :
    Tracks (stepEditT c a e) (stepEdit c a.st e) := by
  cases e with
  | move dst src =>
    unfold stepEditT stepEdit
    have hm := h.stepMove dst src
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    repeat' split
    all_goals first | exact ⟨hm, rfl⟩ | exact rfl | (simp_all [Tracks]; done) | (exfalso; simp_all; done)

theorem stepEditsT_tracks (c : Ctx) : ∀ {a : Tracked}, a.Inv → ∀ (es : List Edit),
    Tracks (stepEditsT c a es) (stepEdits c a.st es)
  | a, h, [] => tracks_ok h
  | a, h, e :: es => by
    simp only [stepEditsT, stepEdits, bind, Except.bind]
    have he := stepEditT_tracks c h e
    cases h1 : stepEditT c a e with
    | error x =>
      rw [h1] at he
      cases h2 : stepEdit c a.st e with
      | error y => rw [h2] at he; simp only [Tracks] at he ⊢; exact he
      | ok _ => rw [h2] at he; exact he.elim
    | ok s =>
      rw [h1] at he
      cases h2 : stepEdit c a.st e with
      | error y => rw [h2] at he; exact he.elim
      | ok b =>
        rw [h2] at he
        obtain ⟨hs, rfl⟩ := he
        exact stepEditsT_tracks c hs es

/-- `Tracks` for a step that also returns a value. -/
def Tracks2 {ε β : Type} : Except ε (Tracked × β) → Except ε (AState × β) → Prop
  | .ok (s, x), .ok (a, y) => s.Inv ∧ s.st = a ∧ x = y
  | .error e, .error e' => e = e'
  | _, _ => False

/-- Continue two agreeing steps, whose errors are mapped alike, with continuations that agree. -/
theorem Tracks.bind {ε ε' β γ : Type} {x : Except ε Tracked} {y : Except ε AState} (hxy : Tracks x y)
    (k : ε → ε') {R : Except ε' β → Except ε' γ → Prop} (herr : ∀ e, R (.error e) (.error e))
    {f : Tracked → Except ε' β} {g : AState → Except ε' γ} (hfg : ∀ s, s.Inv → R (f s) (g s.st)) :
    R ((x.mapError k) >>= f) ((y.mapError k) >>= g) := by
  cases x with
  | error e =>
    cases y with
    | error e' => cases hxy; exact herr _
    | ok _ => exact hxy.elim
  | ok s =>
    cases y with
    | error _ => exact hxy.elim
    | ok a => obtain ⟨hs, rfl⟩ := hxy; exact hfg s hs

theorem tracks2_err {ε β : Type} (e : ε) : Tracks2 (β := β) (.error e) (.error e) := rfl

theorem walkBodyT_tracks (c : Ctx) : ∀ {a : Tracked}, a.Inv →
    ∀ (insts : List (Inst VReg)) (lss : List (List Loc)) (es : List (Nat × Edit)) (i : Nat),
      Tracks2 (walkBodyT c a insts lss es i) (walkBody c a.st insts lss es i)
  | a, h, [], [], es, _ => ⟨h, rfl, rfl⟩
  | a, h, inst :: insts, ls :: lss, es, i => by
    simp only [walkBodyT, walkBody]
    cases ht : takeAt i es with
    | mk now later =>
      exact Tracks.bind (stepEditsT_tracks c h now) _ tracks2_err fun s hs =>
        Tracks.bind (stepInstT_tracks c hs inst ls) _ tracks2_err fun s' hs' =>
          walkBodyT_tracks c hs' insts lss later (i + 1)
  | _, _, [], _ :: _, _, i => rfl
  | _, _, _ :: _, [], _, i => rfl

theorem checkBlock_eq_list (c : Ctx) (info : BlockInfo) (b : Block VReg) (o : BlockOut) :
    checkBlock c info b o = checkBlockList c info b o := by
  unfold checkBlock checkBlockList
  obtain ⟨h0, e0⟩ := Tracked.ofList_inv o.cert
  have hw := walkBodyT_tracks c h0 b.body.toList o.locs o.edits 0
  rw [e0] at hw
  simp only [bind, Except.bind]
  split <;> (try rfl)
  split <;> (try rfl)
  cases hT : walkBodyT c (Tracked.ofList o.cert) b.body.toList o.locs o.edits 0 with
  | error e =>
    cases hP : walkBody c (AState.ofList o.cert) b.body.toList o.locs o.edits 0 with
    | error e' => rw [hT, hP] at hw; cases hw; rfl
    | ok _ => rw [hT, hP] at hw; exact hw.elim
  | ok r =>
    cases hP : walkBody c (AState.ofList o.cert) b.body.toList o.locs o.edits 0 with
    | error _ => rw [hT, hP] at hw; exact hw.elim
    | ok r' =>
      rw [hT, hP] at hw
      obtain ⟨s, left⟩ := r
      obtain ⟨a, left'⟩ := r'
      obtain ⟨hs, rfl, rfl⟩ := hw
      simp only
      cases hk : takeAt b.body.toList.length left with
      | mk now rest =>
        simp only
        split <;> (try rfl)
        exact Tracks.bind (stepEditsT_tracks c hs now) _ (R := Eq) (fun _ => rfl) fun s1 hs1 =>
          Tracks.bind (stepTermT_tracks c hs1 b.term o.termLocs) _ (R := Eq) (fun _ => rfl) fun s2 _ => rfl

end IxCC.Xv.Validate
