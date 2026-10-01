import Compilatrix.Fir.Proof.Rel
import Compilatrix.Fir.Proof.Lowering

/-! # Environments and join points across Anf → Fir

The lowering names each Anf de Bruijn index (`ρ : List Var`); Fir's
environment is a map on those names. `EnvR live ρ ρa ρf`: the names and
Anf's environment have one entry per index, and every index the current
Anf code reads (`live`, from `Anf.Exp.occ`) names a Fir variable bound to a
related value. Indices the code does not read need not be bound: a `case`
arm projects only the fields its body uses (`Lower.projections`).

Join points: Anf keeps nested join closures (each captures the join
environment of its definition), Fir a stack of entries (each run with the
stack below it). `JRel J cs Ja Jf` relates them position by position: the
lowering's join ids `J` (distinct, so Fir's lookup by id finds the
position Anf's index names), the cost `cs` of jumping to each (what Anf
charges that Fir does not: `0` for a recursive jump inside the join point's
own body, a charged Fir entry; else `1 +` the body's tick depth), and per
position an `EntryR`: the body lowered under the entry's parameters and
the names of its definition, the definition environments related on the
body's free variables, and the tick-bound facts the timeout clause needs. -/

set_option autoImplicit false

namespace Compilatrix.Fir.Proof

open Compilatrix.Fir.Lower

variable {A : Anf.Program}

/-! ## Binding names -/

theorem bindAll_get_notin {ρf : Env} {x : Var} :
    ∀ {xs : List Var} {ws : List Val}, x ∉ xs → (bindAll ρf xs ws).get? x = ρf.get? x
  | [], _, _ => by cases ‹List Val› <;> rfl
  | y :: xs, [], _ => rfl
  | y :: xs, w :: ws, hx => by
    simp only [List.mem_cons, not_or] at hx
    simp only [bindAll]
    rw [bindAll_get_notin hx.2, Src.NatMap.get?_insert_ne _ _ hx.1]

theorem bindAll_get_mem {ρf : Env} :
    ∀ {xs : List Var} {ws : List Val} {j : Nat} {x : Var}, xs.Nodup → xs.length = ws.length →
      xs[j]? = some x → (bindAll ρf xs ws).get? x = ws[j]?
  | [], _, _, _, _, _, h => by simp at h
  | y :: xs, [], _, _, _, hl, _ => by simp at hl
  | y :: xs, w :: ws, j, x, hn, hl, hj => by
    rw [List.nodup_cons] at hn
    simp only [bindAll]
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [bindAll_get_notin hn.1, Src.NatMap.get?_insert_self]
      rfl
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj ⊢
      exact bindAll_get_mem hn.2 (by simpa using hl) hj

/-! ## Environments -/

/-- The lowering's names relate Anf's environment to Fir's on every live
index. -/
def EnvR (A : Anf.Program) (live : Nat → Prop) (ρ : List Var) (ρa : List Anf.Val) (ρf : Env) : Prop :=
  ρ.length = ρa.length ∧
    ∀ i x v, live i → ρ[i]? = some x → ρa[i]? = some v → ∃ w, ρf.get? x = some w ∧ VR A v w

namespace EnvR

variable {live live' : Nat → Prop} {ρ : List Var} {ρa : List Anf.Val} {ρf : Env}

theorem mono (h : EnvR A live ρ ρa ρf) (hl : ∀ i, live' i → live i) : EnvR A live' ρ ρa ρf :=
  ⟨h.1, fun i x v hi => h.2 i x v (hl i hi)⟩

/-- A fresh name bound in Fir only (a temporary). -/
theorem insert (h : EnvR A live ρ ρa ρf) {x : Var} (hx : x ∉ ρ) (w : Val) :
    EnvR A live ρ ρa (ρf.insert x w) := by
  refine ⟨h.1, fun i y v hi hy hv => ?_⟩
  obtain ⟨w', hw', hvw⟩ := h.2 i y v hi hy hv
  have : y ≠ x := fun e => hx (e ▸ List.mem_of_getElem? hy)
  exact ⟨w', by rw [Src.NatMap.get?_insert_ne _ _ this]; exact hw', hvw⟩

/-- Fresh distinct names for `n` new indices (a binding, join parameters,
a function's parameters). -/
theorem push {n : Nat} (h : EnvR A (fun i => live (i + n)) ρ ρa ρf) {ps : List Var}
    (hps : ps.Nodup) (hfresh : ∀ p ∈ ps, p ∉ ρ) (hn : ps.length = n) {vs : List Anf.Val}
    {ws : List Val} (hvs : VRs A vs ws) (hvl : vs.length = n) :
    EnvR A live (ps.reverse ++ ρ) (vs.reverse ++ ρa) (bindAll ρf ps ws) := by
  have hwl : ws.length = n := hvs.length ▸ hvl
  refine ⟨by simp [h.1, hn, hvl], fun i x v hi hx hv => ?_⟩
  by_cases hin : i < n
  · rw [List.getElem?_append_left (by simpa [hn] using hin), List.getElem?_reverse (by omega)] at hx
    rw [List.getElem?_append_left (by simpa [hvl] using hin), List.getElem?_reverse (by omega)] at hv
    rw [hn] at hx
    rw [hvl] at hv
    obtain ⟨w, hw, hvw⟩ := hvs.get hv
    exact ⟨w, by rw [bindAll_get_mem hps (by rw [hn, hwl]) hx]; exact hw, hvw⟩
  · rw [List.getElem?_append_right (by simp [hn]; omega)] at hx
    rw [List.getElem?_append_right (by simp [hvl]; omega)] at hv
    simp only [List.length_reverse, hn, hvl] at hx hv
    obtain ⟨w, hw, hvw⟩ := h.2 (i - n) x v (by simpa [Nat.sub_add_cancel (by omega : n ≤ i)] using hi)
      hx hv
    have hxps : x ∉ ps := fun hm => hfresh x hm (List.mem_of_getElem? hx)
    exact ⟨w, by rw [bindAll_get_notin hxps]; exact hw, hvw⟩

/-- One new index (a `bind`). -/
theorem push1 (h : EnvR A (fun i => live (i + 1)) ρ ρa ρf) {x : Var} (hx : x ∉ ρ) {v : Anf.Val}
    {w : Val} (hvw : VR A v w) : EnvR A live (x :: ρ) (v :: ρa) (ρf.insert x w) := by
  have := h.push (ps := [x]) (by simp) (by simpa using hx) rfl (.cons hvw .nil) rfl
  simpa [bindAll] using this

end EnvR

/-! ## Atoms -/

theorem atom_rel {live : Nat → Prop} {ρ : List Var} {ρa : List Anf.Val} {ρf : Env}
    (h : EnvR A live ρ ρa ρf) {g : Anf.GlobalId} {a : Anf.Atom} {arg : Arg}
    (ha : atom g ρ a = .ok arg) (hl : ∀ i, a.occ i > 0 → live i) {v : Anf.Val}
    (hv : a.eval ρa = some v) : ∃ w, arg.eval ρf = some w ∧ VR A v w := by
  cases a with
  | var i =>
    obtain ⟨x, hx, rfl⟩ := atom_var ha
    exact h.2 i x v (hl i (by simp [Anf.Atom.occ])) hx hv
  | lit l =>
    rw [atom_lit ha]
    simp only [Anf.Atom.eval, Option.some.injEq] at hv
    subst hv
    exact ⟨_, rfl, .lit l⟩
  | box =>
    rw [atom_box ha]
    simp only [Anf.Atom.eval, Option.some.injEq] at hv
    subst hv
    exact ⟨_, rfl, .box⟩

theorem atoms_rel {live : Nat → Prop} {ρ : List Var} {ρa : List Anf.Val} {ρf : Env}
    (h : EnvR A live ρ ρa ρf) {g : Anf.GlobalId} :
    ∀ {as : List Anf.Atom} {args : List Arg}, atoms g ρ as = .ok args →
      (∀ i, Anf.Atom.occList i as > 0 → live i) → ∀ {vs : List Anf.Val}, Anf.evalAtoms ρa as = some vs →
      ∃ ws, evalArgs ρf args = some ws ∧ VRs A vs ws
  | [], args, ha, _, vs, hv => by
    rw [atoms_nil ha]
    simp only [Anf.evalAtoms, Option.some.injEq] at hv
    subst hv
    exact ⟨[], rfl, .nil⟩
  | a :: as, args, ha, hl, vs, hv => by
    obtain ⟨arg, args', ha1, has, rfl⟩ := atoms_cons ha
    rw [Anf.evalAtoms_cons] at hv
    cases hva : a.eval ρa with
    | none => rw [hva] at hv; cases hv
    | some v =>
      rw [hva] at hv
      cases hvs : Anf.evalAtoms ρa as with
      | none => rw [hvs] at hv; cases hv
      | some vs' =>
        rw [hvs] at hv
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hv
        subst hv
        obtain ⟨w, hw, hvw⟩ := atom_rel h ha1 (fun i hi => hl i (by simp [Anf.Atom.occList]; omega)) hva
        obtain ⟨ws, hws, hvws⟩ := atoms_rel h has
          (fun i hi => hl i (by simp [Anf.Atom.occList]; omega)) hvs
        exact ⟨w :: ws, by rw [evalArgs_cons, hw, hws]; rfl, .cons hvw hvws⟩

/-! ## Join points -/

/-- A join closure and the Fir entry for it (see the module comment). `J`,
`cs`, `Ja`: the join ids, costs and Anf join environment of its
definition; `cost`: what a jump to it costs Anf that Fir does not
charge. -/
def EntryR (A : Anf.Program) (N : Nat) (g : Anf.GlobalId) (J : List JoinId) (cs : List Nat)
    (Ja : List Anf.JClo) (jc : Anf.JClo) (e : JEntry) (cost : Nat) : Prop :=
  ∃ (ρa : List Anf.Val) (n : Nat) (b : Anf.Exp) (names : List Var) (s₀ : Nat) (st st' : St),
    jc = .mk ρa Ja n b e.isRec ∧ (e.charged = true → e.isRec = true) ∧
    e.params = List.range' s₀ n ∧ (∀ y ∈ names, y < s₀) ∧ s₀ + n ≤ st.vars ∧
    (∀ j ∈ (if e.isRec then e.id :: J else J), j < st.joins) ∧
    exp A g (e.params.reverse ++ names) (if e.isRec then e.id :: J else J) st b = .ok (e.body, st') ∧
    EnvR A (fun i => 0 < b.occ (i + n)) names ρa e.env ∧
    (TickBound.exp (if e.isRec then 0 :: cs else cs) b).2 < N ∧
    (e.isRec = true → (TickBound.exp (0 :: cs) b).1 < N) ∧
    cost = (if e.charged then 0 else (TickBound.exp (if e.isRec then 0 :: cs else cs) b).1 + 1)

/-- Anf's join environment against Fir's join stack, position by position. -/
inductive JRel (A : Anf.Program) (N : Nat) (g : Anf.GlobalId) :
    List JoinId → List Nat → List Anf.JClo → List JEntry → Prop
  | nil : JRel A N g [] [] [] []
  | cons {j : JoinId} {J : List JoinId} {cost : Nat} {cs : List Nat} {jc : Anf.JClo}
      {Ja : List Anf.JClo} {e : JEntry} {Jf : List JEntry} :
      JRel A N g J cs Ja Jf → e.id = j → j ∉ J → EntryR A N g J cs Ja jc e cost →
      JRel A N g (j :: J) (cost :: cs) (jc :: Ja) (e :: Jf)

namespace JRel

variable {N : Nat} {g : Anf.GlobalId}

/-- A jump: Anf's index and Fir's lookup by the lowered id find the same
position. -/
theorem lookup {J : List JoinId} {cs : List Nat} {Ja : List Anf.JClo} {Jf : List JEntry}
    (h : JRel A N g J cs Ja Jf) :
    ∀ {j : Nat} {j' : JoinId}, J[j]? = some j' →
      ∃ jc e, Ja[j]? = some jc ∧ lookupJ j' Jf = some (e, Jf.drop (j + 1)) ∧
        EntryR A N g (J.drop (j + 1)) (cs.drop (j + 1)) (Ja.drop (j + 1)) jc e (cs.getD j 0) ∧
        JRel A N g (J.drop (j + 1)) (cs.drop (j + 1)) (Ja.drop (j + 1)) (Jf.drop (j + 1)) ∧
        e.id = j' ∧ j' ∉ J.drop (j + 1) := by
  induction h with
  | nil => intro j j' hj; simp at hj
  | @cons j₀ J cost cs jc Ja e Jf hrest hid hnot hent ih =>
    intro j j' hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      refine ⟨jc, e, rfl, ?_, by simpa using hent, by simpa using hrest, hid, by simpa using hnot⟩
      simp [lookupJ, hid]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      obtain ⟨jc', e', hjc, hl, hent', hrest', hid', hnot'⟩ := ih hj
      refine ⟨jc', e', by simpa using hjc, ?_, by simpa using hent', by simpa using hrest', hid', by simpa using hnot'⟩
      have hne : e.id ≠ j' := by
        rw [hid]
        intro e
        subst e
        exact hnot (List.mem_of_getElem? hj)
      simp only [lookupJ, hne, ↓reduceIte, List.drop_succ_cons]
      exact hl

/-- The join stack a jump runs the body with (`JEntry.after`). -/
theorem after {J : List JoinId} {cs : List Nat} {Ja : List Anf.JClo} {Jf : List JEntry}
    (h : JRel A N g J cs Ja Jf) {jc : Anf.JClo} {e : JEntry} {cost : Nat}
    (he : EntryR A N g J cs Ja jc e cost) (hnot : e.id ∉ J) :
    JRel A N g (if e.isRec then e.id :: J else J) (if e.isRec then 0 :: cs else cs)
      (if e.isRec then jc :: Ja else Ja) (e.after Jf) := by
  unfold JEntry.after
  cases hr : e.isRec with
  | false => simpa using h
  | true =>
    simp only [↓reduceIte]
    obtain ⟨ρa, n, b, names, s₀, st, st', hjc, _, hps, hnm, hs₀, hjs, hlow, henv, hs, hd, _⟩ := he
    refine .cons h rfl hnot ⟨ρa, n, b, names, s₀, st, st', ?_, fun _ => rfl, hps, hnm, hs₀, ?_, ?_, henv,
      ?_, ?_, by simp⟩
    · simpa [hr] using hjc
    · simpa [hr] using hjs
    · simpa [hr] using hlow
    · simpa [hr] using hs
    · simpa [hr] using hd

end JRel

end Compilatrix.Fir.Proof
