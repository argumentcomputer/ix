import IxCC.Anf.Specialize
import IxCC.Anf.Proof.Pass.Prune

/-! # P4: the pass's state and what a caller's definitions say

The specialiser (`Anf.Specialize`, P4) runs in `StateT St (Except String)`;
these lemmas invert a successful run. A state keeps a dense program
with at least the input's ids (`StOk`); a later state keeps the
specialisations of an earlier one (`Grows`), and the output program has
those of every state of the run (`Pre`).

A caller's definitions describe its source environment (`DefsOk`): a level
holds a constructor of lower levels' values, a literal, a function global's
closure, or a local function's closure over the environment of its
definition. A binding's definition (`DfOk`) holds of the value the binding
gives. Every variable that occurs in a term is free in it (`occ_free`). -/

set_option autoImplicit false

namespace IxCC.Anf.Specialize.Proof

open IxCC.Sem (Result)

/-! ## The monad -/

theorem run_bind_ok {α β : Type} {x : M α} {f : α → M β} {s s'' : St} {b : β}
    (h : (x >>= f).run s = .ok (b, s'')) : ∃ a s', x.run s = .ok (a, s') ∧ (f a).run s' = .ok (b, s'') := by
  simp only [StateT.run_bind] at h
  cases hx : x.run s with
  | error e => rw [hx] at h; cases h
  | ok p =>
    obtain ⟨a, s'⟩ := p
    rw [hx] at h
    exact ⟨a, s', rfl, h⟩

theorem run_pure_ok {α : Type} {a b : α} {s s' : St} (h : (pure a : M α).run s = .ok (b, s')) :
    a = b ∧ s = s' := by
  simp only [StateT.run_pure] at h
  cases h
  exact ⟨rfl, rfl⟩

theorem run_throw_ok {α : Type} {e : String} {s : St} {r : α × St}
    (h : (throw e : M α).run s = .ok r) : False := by
  cases h

theorem run_map_ok {α β : Type} {g : α → β} {x : M α} {s s' : St} {b : β}
    (h : (g <$> x).run s = .ok (b, s')) : ∃ a, x.run s = .ok (a, s') ∧ g a = b := by
  simp only [StateT.run_map] at h
  cases hx : x.run s with
  | error e => rw [hx] at h; cases h
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [hx] at h
    cases h
    exact ⟨a, rfl, rfl⟩

theorem run_get_ok {s s' r : St} (h : (get : M St).run s = .ok (r, s')) : r = s ∧ s' = s := by
  cases h; exact ⟨rfl, rfl⟩

theorem run_set_ok {s s' t : St} {u : PUnit} (h : (set t : M PUnit).run s = .ok (u, s')) : s' = t := by
  cases h; rfl

theorem run_modifyGet_ok {α : Type} {f : St → α × St} {s s' : St} {a : α}
    (h : (modifyGet f : M α).run s = .ok (a, s')) : (a, s') = f s := by
  have e : (modifyGet f : M α).run s = .ok (f s) := rfl
  rw [e] at h
  exact (Except.ok.inj h).symm

/-- A site's charge changes only the work counter. -/
theorem run_charge_ok {cost : Nat → Nat → Nat × Nat} {s s' : St} {u : Unit} (h : (charge cost).run s = .ok (u, s')) :
    s'.prog = s.prog := by
  change (if s.work + (cost s.prog.size s.specs).1 > maxWork ||
      s.nodes + (cost s.prog.size s.specs).2 > maxNodes then
    (.error "specialize: work budget exhausted" : Except String (Unit × St))
    else .ok ((), { s with work := s.work + (cost s.prog.size s.specs).1
                           nodes := s.nodes + (cost s.prog.size s.specs).2 })) = .ok (u, s') at h
  split at h
  · cases h
  · cases h
    rfl

theorem run_liftM_ok {α : Type} {x : Except String α} {s s' : St} {a : α}
    (h : (specialize.liftM x).run s = .ok (a, s')) : x = .ok a ∧ s' = s := by
  unfold specialize.liftM at h
  cases x with
  | error e => cases h
  | ok a' => cases h; exact ⟨rfl, rfl⟩

/-! ## States -/

variable (P Q : Program)

/-- A state's program has the input's ids at least, densely. -/
def StOk (st : St) : Prop := st.prog.WF ∧ P.size ≤ st.prog.size

/-- The output program has a state's specialisations. -/
def Pre (st : St) : Prop := ∀ s, P.size ≤ s → s < st.prog.size → Q.global? s = st.prog.global? s

/-- A later state keeps the specialisations (ids from the input's size up)
of an earlier one. -/
def SGrows (st st' : St) : Prop :=
  st.prog.size ≤ st'.prog.size ∧
    ∀ s, P.size ≤ s → s < st.prog.size → st'.prog.global? s = st.prog.global? s

/-- A later state of a caller's rewrite keeps every global of an earlier
one, its pinned constructors, its roots and its constructor table. -/
def Grows (st st' : St) : Prop :=
  st.prog.size ≤ st'.prog.size ∧ (∀ s, s < st.prog.size → st'.prog.global? s = st.prog.global? s) ∧
    st'.prog.known = st.prog.known ∧ st'.prog.roots = st.prog.roots ∧
    st'.prog.ctors = st.prog.ctors

variable {P Q}

theorem Grows.refl (st : St) : Grows st st := ⟨Nat.le_refl _, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Grows.trans {st₁ st₂ st₃ : St} (h₁ : Grows st₁ st₂) (h₂ : Grows st₂ st₃) : Grows st₁ st₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun s hlt => by rw [h₂.2.1 s (Nat.lt_of_lt_of_le hlt h₁.1), h₁.2.1 s hlt],
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩

theorem Grows.sgrows {st st' : St} (h : Grows st st') : SGrows P st st' :=
  ⟨h.1, fun s _ hlt => h.2.1 s hlt⟩

theorem SGrows.refl (st : St) : SGrows P st st := ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

theorem SGrows.trans {st₁ st₂ st₃ : St} (h₁ : SGrows P st₁ st₂) (h₂ : SGrows P st₂ st₃) : SGrows P st₁ st₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun s hs hlt => by
    rw [h₂.2 s hs (Nat.lt_of_lt_of_le hlt h₁.1), h₁.2 s hs hlt]⟩

theorem Pre.of_sgrows {st st' : St} (h : SGrows P st st') (hp : Pre P Q st') : Pre P Q st :=
  fun s hs hlt => by rw [hp s hs (Nat.lt_of_lt_of_le hlt h.1), h.2 s hs hlt]

theorem Pre.of_grows {st st' : St} (h : Grows st st') (hp : Pre P Q st') : Pre P Q st :=
  hp.of_sgrows h.sgrows

/-- A state whose program only changed its fresh-function counter. -/
theorem Grows.of_prog {st st' : St} (h : st'.prog = st.prog) : Grows st st' :=
  ⟨by rw [h]; exact Nat.le_refl _, fun _ _ => by rw [h], by rw [h], by rw [h], by rw [h]⟩

/-! ## Programs rebuilt from their global list -/

/-- A dense program's global list holds its globals at their ids. -/
theorem globalList_get {R : Program} (hw : R.WF) (i : Nat) :
    (R.globalList.map (·.2))[i]? = R.global? i := by
  unfold Program.globalList
  rw [List.map_filterMap]
  by_cases hi : i < R.size
  · obtain ⟨gd, hgd⟩ := hw.2 i hi
    rw [Prune.Proof.filterMap_getElem? (fun x hx => ?_) i]
    · rw [List.getElem?_range hi]; simp [hgd]
    · obtain ⟨gdx, hgdx⟩ := hw.2 x (List.mem_range.1 hx)
      exact ⟨gdx, by simp [hgdx]⟩
  · have hlen : ((List.range R.size).filterMap fun g => ((R.global? g).map (g, ·)).map (·.2)).length ≤ R.size := by
      refine Nat.le_trans (List.length_filterMap_le _ _) ?_
      simp
    rw [List.getElem?_eq_none (by omega)]
    cases hg : R.global? i with
    | none => rfl
    | some gd => exact absurd (hw.1 i gd hg) hi

theorem globalList_length {R : Program} (hw : R.WF) : (R.globalList.map (·.2)).length = R.size := by
  apply Nat.le_antisymm
  · unfold Program.globalList
    rw [List.length_map]
    refine Nat.le_trans (List.length_filterMap_le _ _) ?_
    simp
  · refine Nat.le_of_not_lt fun hlt => ?_
    have hi : R.size - 1 < R.size := by omega
    obtain ⟨gd, hgd⟩ := hw.2 _ hi
    have := globalList_get hw (R.size - 1)
    rw [hgd, List.getElem?_eq_none (by omega)] at this
    cases this

/-- A program rebuilt from a list has the list's globals at their ids. -/
theorem withGlobals_wf (R : Program) (gs : List GDef) : (R.withGlobals gs).WF := by
  refine ⟨fun g gd hg => ?_, fun g hg => ?_⟩
  · rw [Prune.Proof.withGlobals_global] at hg
    exact (List.getElem?_eq_some_iff.1 hg).1
  · exact ⟨gs[g]'hg, by rw [Prune.Proof.withGlobals_global, List.getElem?_eq_getElem hg]⟩

/-! ## Levels and atoms -/

theorem lvl_lt {ρ : List Val} {l : Nat} {v : Val} (h : (Opd.lvl l).val ρ = some v) : l < ρ.length := by
  simp only [Opd.val] at h
  split at h
  · assumption
  · cases h

theorem lvl_val {ρ : List Val} {l : Nat} (hl : l < ρ.length) : (Opd.lvl l).val ρ = ρ[ρ.length - 1 - l]? := by
  simp [Opd.val, hl]

/-- The value at the top level after a push. -/
theorem lvl_push (ρ : List Val) (v : Val) : (Opd.lvl ρ.length).val (v :: ρ) = some v := Opd.val_lvl_top ρ v

theorem atom_opd_val {ρ : List Val} {a : Atom} {v : Val} (h : a.eval ρ = some v) :
    (a.opd ρ.length).val ρ = some v := by
  cases a with
  | var i =>
    simp only [Atom.eval] at h
    have hi : i < ρ.length := (List.getElem?_eq_some_iff.1 h).1
    simp only [Atom.opd, Opd.val]
    rw [if_pos (by omega)]
    rw [show ρ.length - 1 - (ρ.length - 1 - i) = i by omega]
    exact h
  | lit l => exact h
  | box => exact h

theorem atoms_opd_val {ρ : List Val} : ∀ {as : List Atom} {vs : List Val}, evalAtoms ρ as = some vs →
    (as.map (·.opd ρ.length)).mapM (·.val ρ) = some vs
  | [], vs, h => by simp [evalAtoms] at h; subst h; rfl
  | a :: as, vs, h => by
    rw [evalAtoms_cons] at h
    cases ha : a.eval ρ with
    | none => rw [ha] at h; cases h
    | some v =>
      rw [ha] at h
      cases hs : evalAtoms ρ as with
      | none => rw [hs] at h; cases h
      | some ws =>
        rw [hs] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp [List.mapM_cons, atom_opd_val ha, atoms_opd_val hs]

/-- Each atom of a list that evaluates evaluates to its value. -/
theorem evalAtoms_get {ρ : List Val} : ∀ {as : List Atom} {vs : List Val}, evalAtoms ρ as = some vs →
    ∀ {j : Nat} {a : Atom}, as[j]? = some a → ∃ v, a.eval ρ = some v ∧ vs[j]? = some v
  | [], _, _, _, _, ha => by simp at ha
  | a :: as, vs, h, j, b, ha => by
    rw [evalAtoms_cons] at h
    cases hb : a.eval ρ with
    | none => rw [hb] at h; cases h
    | some v =>
      rw [hb] at h
      cases hs : evalAtoms ρ as with
      | none => rw [hs] at h; cases h
      | some ws =>
        rw [hs] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        cases j with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at ha; subst ha; exact ⟨v, hb, rfl⟩
        | succ j => simpa using evalAtoms_get hs (by simpa using ha)

/-- An operand that reads only levels below `d`. -/
def InRange (d : Nat) : Opd → Prop
  | .lvl l => l < d
  | _ => True

theorem inRange_of_val {ρ : List Val} {o : Opd} {v : Val} (h : o.val ρ = some v) : InRange ρ.length o := by
  cases o with
  | lvl l => exact lvl_lt h
  | lit _ => trivial
  | box => trivial

/-! ## What a caller's definitions say -/

variable (P) in
/-- What a definition says of level `l` of a source environment. -/
def DefOk (ρ : List Val) (l : Nat) : Def → Prop
  | .con c fs => (∀ j, Opd.lvl j ∈ fs → j < l) ∧
      ∃ vs, fs.mapM (·.val ρ) = some vs ∧ (Opd.lvl l).val ρ = some (.con c vs)
  | .lit n => (Opd.lvl l).val ρ = some (.lit (.nat n))
  | .glob g => ∃ gd, P.global? g = some gd ∧ gd.ps ≠ [] ∧
      (Opd.lvl l).val ρ = some (.clos [] gd.ps.length gd.body [])
  | .fn df ps b _ => df ≤ l ∧ ps ≠ [] ∧
      (Opd.lvl l).val ρ = some (.clos (ρ.drop (ρ.length - df)) ps.length b [])
  | .blank => True

variable (P) in
/-- Every definition holds. -/
def DefsOk (defs : Src.NatMap Def) (ρ : List Val) : Prop :=
  ∀ l df, defs.get? l = some df → DefOk P ρ l df

variable (P) in
/-- A binding's definition holds of the value it gives, whenever the
definitions hold. -/
def DfOk (defs : Src.NatMap Def) (d : Nat) (b : Bind) (df : Def) : Prop :=
  ∀ (ρ : List Val) (k : Nat) (v : Val), DefsOk P defs ρ → ρ.length = d → evalBind P k ρ b = .ok v →
    DefOk P (v :: ρ) d df

theorem opds_append {ρ : List Val} (ext : List Val) : ∀ {os : List Opd} {ws : List Val},
    os.mapM (·.val ρ) = some ws → os.mapM (·.val (ext ++ ρ)) = some ws
  | [], ws, h => h
  | o :: os, ws, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨w, hw, ws', hws, rfl⟩ := h
    exact ⟨w, Opd.val_append ext hw, ws', opds_append ext hws, rfl⟩

theorem drop_append_of_le {ρ : List Val} (ext : List Val) {df : Nat} (h : df ≤ ρ.length) :
    (ext ++ ρ).drop ((ext ++ ρ).length - df) = ρ.drop (ρ.length - df) := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega), List.nil_append]
  congr 1; simp; omega

theorem DefOk.append {ρ : List Val} (ext : List Val) {l : Nat} :
    ∀ {df : Def}, DefOk P ρ l df → DefOk P (ext ++ ρ) l df
  | .con _ _, ⟨hlt, vs, hvs, hl⟩ => ⟨hlt, vs, opds_append ext hvs, Opd.val_append ext hl⟩
  | .lit _, h => Opd.val_append ext h
  | .glob _, ⟨gd, hg, hps, hl⟩ => ⟨gd, hg, hps, Opd.val_append ext hl⟩
  | .fn df ps b _, ⟨hle, hps, hl⟩ => by
    refine ⟨hle, hps, ?_⟩
    rw [drop_append_of_le ext (Nat.le_trans hle (Nat.le_of_lt (lvl_lt hl)))]
    exact Opd.val_append ext hl
  | .blank, _ => trivial

theorem DefsOk.append {defs : Src.NatMap Def} {ρ : List Val} (h : DefsOk P defs ρ) (ext : List Val) :
    DefsOk P defs (ext ++ ρ) := fun l df hl => (h l df hl).append ext

/-- A level's definition describes a copy of its value at the top. -/
theorem DefOk.copy {ρ : List Val} {l : Nat} {v : Val} (hv : (Opd.lvl l).val ρ = some v) :
    ∀ {df : Def}, DefOk P ρ l df → DefOk P (v :: ρ) ρ.length df
  | .con _ _, ⟨hlt, vs, hvs, hl⟩ =>
    ⟨fun j hj => Nat.lt_trans (hlt j hj) (lvl_lt hv), vs, opds_append [v] hvs,
      (lvl_push ρ v).trans (hv.symm.trans hl)⟩
  | .lit _, hl => (lvl_push ρ v).trans (hv.symm.trans hl)
  | .glob _, ⟨gd, hg, hps, hl⟩ => ⟨gd, hg, hps, (lvl_push ρ v).trans (hv.symm.trans hl)⟩
  | .fn df ps b _, ⟨hle, hps, hl⟩ => by
    have hle' := Nat.le_trans hle (Nat.le_of_lt (lvl_lt hv))
    refine ⟨hle', hps, ?_⟩
    have := drop_append_of_le [v] hle'
    rw [show [v] ++ ρ = v :: ρ from rfl] at this
    rw [this]; exact (lvl_push ρ v).trans (hv.symm.trans hl)
  | .blank, _ => trivial

/-- Definitions under one more binding with a definition of its value. -/
theorem DefsOk.insert {defs : Src.NatMap Def} {ρ : List Val} (h : DefsOk P defs ρ) {v : Val} {df : Def}
    (hdf : DefOk P (v :: ρ) ρ.length df) : DefsOk P (defs.insert ρ.length df) (v :: ρ) := by
  intro l df' hl
  rw [Src.NatMap.get?_insert] at hl
  split at hl
  · next he => subst he; cases hl; exact hdf
  · have := (h l df' hl).append [v]
    simpa using this

/-- Blank definitions for `n` levels from `base`. -/
def blankDefs (defs : Src.NatMap Def) (base n : Nat) : Src.NatMap Def :=
  (List.range n).foldl (fun m i => m.insert (base + i) Def.blank) defs

theorem blankDefs_get (base : Nat) : ∀ (xs : List Nat) (defs : Src.NatMap Def) (l : Nat) (df : Def),
    (xs.foldl (fun m i => m.insert (base + i) Def.blank) defs).get? l = some df →
      df = .blank ∨ defs.get? l = some df
  | [], _, _, _, h => .inr h
  | x :: xs, defs, l, df, h => by
    rw [List.foldl_cons] at h
    rcases blankDefs_get base xs _ l df h with h' | h'
    · exact .inl h'
    · rw [Src.NatMap.get?_insert] at h'
      split at h'
      · cases h'; exact .inl rfl
      · exact .inr h'

theorem DefsOk.blank {defs : Src.NatMap Def} {ρ : List Val} (h : DefsOk P defs ρ) (n : Nat)
    (ext : List Val) : DefsOk P (blankDefs defs ρ.length n) (ext ++ ρ) := by
  intro l df hl
  rcases blankDefs_get ρ.length _ defs l df hl with rfl | h'
  · trivial
  · exact (h l df h').append ext

/-- Definitions that are all blank. -/
theorem DefsOk.ofBlanks (xs : List Nat) (ρ : List Val) :
    DefsOk P (Src.NatMap.ofList (xs.map (·, Def.blank))) ρ := by
  intro l df hl
  have : ∀ (ys : List (Nat × Def)) (m : Src.NatMap Def), (∀ p ∈ ys, p.2 = .blank) →
      (∀ l df, m.get? l = some df → df = .blank) →
      ∀ l df, (ys.foldl (fun m (k, x) => m.insert k x) m).get? l = some df → df = .blank := by
    intro ys
    induction ys with
    | nil => intro m _ hm; exact hm
    | cons p ys ih =>
      intro m hys hm
      refine ih _ (fun q hq => hys q (List.mem_cons_of_mem _ hq)) fun l df hl => ?_
      rw [Src.NatMap.get?_insert] at hl
      split at hl
      · cases hl; exact hys p List.mem_cons_self
      · exact hm l df hl
  have hb := this (xs.map (·, Def.blank)) .leaf (fun p hp => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp; rfl) (fun l df h => by simp [Src.NatMap.get?] at h) l df hl
  subst hb; trivial

/-! ## Occurrences are free variables -/

theorem atom_occ_free (a : Atom) (n j : Nat) (h : a.occ (n + j) ≠ 0) : j ∈ a.free n := by
  cases a with
  | var i =>
    simp only [Atom.occ] at h
    split at h
    · next he =>
      simp only [beq_iff_eq] at he
      subst he
      simp [Atom.free]
    · exact absurd rfl h
  | lit _ => simp [Atom.occ] at h
  | box => simp [Atom.occ] at h

theorem atoms_occ_free : ∀ (as : List Atom) (n j : Nat), Atom.occList (n + j) as ≠ 0 →
    j ∈ Atom.freeList n as
  | [], _, _, h => by simp [Atom.occList] at h
  | a :: as, n, j, h => by
    simp only [Atom.occList] at h
    simp only [Atom.freeList, List.mem_append]
    by_cases ha : a.occ (n + j) = 0
    · exact .inr (atoms_occ_free as n j (by omega))
    · exact .inl (atom_occ_free a n j ha)

mutual

theorem occ_free : ∀ (e : Exp) (n j : Nat), e.occ (n + j) ≠ 0 → j ∈ e.free n
  | .bind _ b e, n, j, h => by
    simp only [Exp.occ] at h
    simp only [Exp.free, List.mem_append]
    by_cases hb : b.occ (n + j) = 0
    · refine .inr (occ_free e (n + 1) j ?_)
      rw [show n + 1 + j = n + j + 1 by omega]; omega
    · exact .inl (bind_occ_free b n j hb)
  | .join m _ b e, n, j, h => by
    simp only [Exp.occ] at h
    simp only [Exp.free, List.mem_append]
    by_cases hb : b.occ (n + j + m) = 0
    · exact .inr (occ_free e n j (by omega))
    · refine .inl (occ_free b (n + m) j ?_)
      rw [show n + m + j = n + j + m by omega]; exact hb
  | .jump _ as, n, j, h => by
    simp only [Exp.occ] at h
    simpa [Exp.free] using atoms_occ_free as n j h
  | .case x alts d, n, j, h => by
    simp only [Exp.occ] at h
    simp only [Exp.free, List.mem_append]
    by_cases hx : x.occ (n + j) = 0
    · by_cases ha : Exp.altsOcc (n + j) alts = 0
      · exact .inr (opt_occ_free d n j (by omega))
      · exact .inl (.inr (alts_occ_free alts n j ha))
    · exact .inl (.inl (atom_occ_free x n j hx))
  | .ret a, n, j, h => by
    simp only [Exp.occ] at h
    simpa [Exp.free] using atom_occ_free a n j h
  | .tick e, n, j, h => by
    simp only [Exp.occ] at h
    simpa [Exp.free] using occ_free e n j h
  | .trap, _, _, h => by simp [Exp.occ] at h

theorem bind_occ_free : ∀ (b : Bind) (n j : Nat), b.occ (n + j) ≠ 0 → j ∈ b.free n
  | .atom a, n, j, h => by simpa [Bind.occ, Bind.free] using atom_occ_free a n j (by simpa [Bind.occ] using h)
  | .proj _ _ a, n, j, h => by
    simpa [Bind.occ, Bind.free] using atom_occ_free a n j (by simpa [Bind.occ] using h)
  | .con _ as, n, j, h => by
    simpa [Bind.free] using atoms_occ_free as n j (by simpa [Bind.occ] using h)
  | .prim _ as, n, j, h => by
    simpa [Bind.free] using atoms_occ_free as n j (by simpa [Bind.occ] using h)
  | .call _ as, n, j, h => by
    simpa [Bind.free] using atoms_occ_free as n j (by simpa [Bind.occ] using h)
  | .app f as, n, j, h => by
    simp only [Bind.occ] at h
    simp only [Bind.free, List.mem_append]
    by_cases hf : f.occ (n + j) = 0
    · exact .inr (atoms_occ_free as n j (by omega))
    · exact .inl (atom_occ_free f n j hf)
  | .glob _, _, _, h => by simp [Bind.occ] at h
  | .fn ps b, n, j, h => by
    simp only [Bind.occ] at h
    simp only [Bind.free]
    refine occ_free b (n + ps.length) j ?_
    rw [show n + ps.length + j = n + j + ps.length by omega]; exact h

theorem alts_occ_free : ∀ (alts : List Alt) (n j : Nat), Exp.altsOcc (n + j) alts ≠ 0 →
    j ∈ Exp.altsFree n alts
  | [], _, _, h => by simp [Exp.altsOcc] at h
  | .mk _ m b :: as, n, j, h => by
    simp only [Exp.altsOcc] at h
    simp only [Exp.altsFree, List.mem_append]
    by_cases hb : b.occ (n + j + m) = 0
    · exact .inr (alts_occ_free as n j (by omega))
    · refine .inl (occ_free b (n + m) j ?_)
      rw [show n + m + j = n + j + m by omega]; exact hb

theorem opt_occ_free : ∀ (d : Option Exp) (n j : Nat), Exp.optOcc (n + j) d ≠ 0 → j ∈ Exp.optFree n d
  | none, _, _, h => by simp [Exp.optOcc] at h
  | some e, n, j, h => by simpa [Exp.optFree] using occ_free e n j (by simpa [Exp.optOcc] using h)

end

/-! ## Lists of levels -/

theorem mem_dedup_aux : ∀ (xs acc : List Nat) (y : Nat),
    y ∈ xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) acc ↔ y ∈ acc ∨ y ∈ xs
  | [], acc, y => by simp
  | x :: xs, acc, y => by
    rw [List.foldl_cons, mem_dedup_aux xs _ y]
    split
    · next hc =>
      simp only [List.contains_iff_mem] at hc
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact .inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inl hc
          · exact .inr h
    · simp only [List.mem_cons]
      constructor
      · rintro ((rfl | h) | h)
        · exact .inr (.inl rfl)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | (rfl | h))
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr h

theorem mem_dedup {xs : List Nat} {y : Nat} : y ∈ dedup xs ↔ y ∈ xs := by
  unfold dedup
  rw [List.mem_reverse, mem_dedup_aux]
  simp

theorem mem_insertSorted {x y : Nat} : ∀ {ys : List Nat}, y ∈ insertSorted x ys ↔ y = x ∨ y ∈ ys
  | [] => by simp [insertSorted]
  | z :: zs => by
    unfold insertSorted
    split
    · simp
    · simp only [List.mem_cons, mem_insertSorted (ys := zs)]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)

theorem sorted_insertSorted (x : Nat) : ∀ {ys : List Nat}, ys.Pairwise (· ≤ ·) →
    (insertSorted x ys).Pairwise (· ≤ ·)
  | [], _ => by simp [insertSorted]
  | z :: zs, h => by
    unfold insertSorted
    split
    · next hxz =>
      refine List.Pairwise.cons (fun a ha => ?_) h
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hxz
      · exact Nat.le_trans hxz (List.rel_of_pairwise_cons h ha)
    · next hxz =>
      have h' := List.pairwise_cons.1 h
      refine List.Pairwise.cons (fun a ha => ?_) (sorted_insertSorted x h'.2)
      rcases mem_insertSorted.1 ha with rfl | ha
      · omega
      · exact h'.1 a ha

theorem mem_sortNats_aux : ∀ (xs acc : List Nat) (y : Nat),
    y ∈ xs.foldl (fun acc x => insertSorted x acc) acc ↔ y ∈ acc ∨ y ∈ xs
  | [], acc, y => by simp
  | x :: xs, acc, y => by
    rw [List.foldl_cons, mem_sortNats_aux xs _ y, mem_insertSorted]
    simp only [List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h

theorem mem_sortNats {xs : List Nat} {y : Nat} : y ∈ sortNats xs ↔ y ∈ xs := by
  unfold sortNats
  rw [mem_sortNats_aux]
  simp

theorem sorted_sortNats_aux : ∀ (xs acc : List Nat), acc.Pairwise (· ≤ ·) →
    (xs.foldl (fun acc x => insertSorted x acc) acc).Pairwise (· ≤ ·)
  | [], _, h => h
  | x :: xs, acc, h => by
    rw [List.foldl_cons]
    exact sorted_sortNats_aux xs _ (sorted_insertSorted x h)

theorem sorted_sortNats (xs : List Nat) : (sortNats xs).Pairwise (· ≤ ·) :=
  sorted_sortNats_aux xs [] List.Pairwise.nil

end IxCC.Anf.Specialize.Proof
