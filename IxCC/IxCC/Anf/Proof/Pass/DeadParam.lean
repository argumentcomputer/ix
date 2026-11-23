import IxCC.Anf.DeadParam
import IxCC.Anf.WellFormed
import IxCC.Anf.Proof.Rel.Fund
import IxCC.Anf.Proof.Lang
import IxCC.Anf.Proof.Pass.Basic
import IxCC.Anf.Proof.Convert.Rel

/-! # P5 dead / erased parameter stripping is correct

`DeadParam.run` splits every non-root, non-dispatcher function global with
unused parameters into a slim worker taking only the kept parameters (with
parameter indices remapped and calls redirected) and a wrapper at the original
id and arity that forwards its kept parameters to the worker.

The proof defines a structural value relation `DV` with closures for rewritten
bodies (`clos`, under either identity or masked outer environments) and wrapped
globals (`wrap`), proves the fundamental lemma for `rewriteExp` at every clock
bound, and obtains `run_refines : P.WF → (run P).WF ∧ Sem.Refines P (run P)`. -/

set_option autoImplicit false

namespace IxCC.Anf.DeadParam.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Anf.Rel (Pw)

/-! ## Mask and remapping algebra -/

theorem filterMask_length {α : Type} : ∀ (m : List Bool) (xs : List α),
    m.length = xs.length → (filterMask m xs).length = countTrue m
  | [], [], _ => rfl
  | true :: bs, _ :: xs, h => by
    simp only [filterMask, countTrue, List.length_cons] at h ⊢
    rw [filterMask_length bs xs (by omega)]
  | false :: bs, _ :: xs, h => by
    simp only [filterMask, countTrue, List.length_cons] at h ⊢
    exact filterMask_length bs xs (by omega)

theorem countTrue_append : ∀ (a b : List Bool), countTrue (a ++ b) = countTrue a + countTrue b
  | [], b => by simp [countTrue]
  | true :: a, b => by simp only [List.cons_append, countTrue, countTrue_append a b]; omega
  | false :: a, b => by simp only [List.cons_append, countTrue, countTrue_append a b]

theorem countTrue_reverse : ∀ (m : List Bool), countTrue m.reverse = countTrue m
  | [] => rfl
  | true :: bs => by simp [countTrue, countTrue_append, countTrue_reverse bs]
  | false :: bs => by simp [countTrue, countTrue_append, countTrue_reverse bs]

theorem filterMask_append {α : Type} : ∀ (a b : List Bool) (xs ys : List α),
    a.length = xs.length → filterMask (a ++ b) (xs ++ ys) = filterMask a xs ++ filterMask b ys
  | [], b, [], ys, _ => rfl
  | true :: a, b, x :: xs, ys, h => by
    simp only [List.cons_append, filterMask, List.length_cons] at h ⊢
    rw [filterMask_append a b xs ys (by omega)]
  | false :: a, b, _ :: xs, ys, h => by
    simp only [List.cons_append, filterMask, List.length_cons] at h ⊢
    exact filterMask_append a b xs ys (by omega)

theorem filterMask_reverse {α : Type} : ∀ (m : List Bool) (xs : List α),
    m.length = xs.length → (filterMask m xs).reverse = filterMask m.reverse xs.reverse
  | [], [], _ => rfl
  | true :: bs, x :: xs, h => by
    simp only [filterMask, List.reverse_cons, List.length_cons] at h ⊢
    have hl : bs.reverse.length = xs.reverse.length := by simp; omega
    rw [filterMask_append bs.reverse [true] xs.reverse [x] hl, filterMask_reverse bs xs (by omega)]
    rfl
  | false :: bs, x :: xs, h => by
    simp only [filterMask, List.reverse_cons, List.length_cons] at h ⊢
    have hl : bs.reverse.length = xs.reverse.length := by simp; omega
    rw [filterMask_append bs.reverse [false] xs.reverse [x] hl, filterMask_reverse bs xs (by omega)]
    simp [filterMask]

theorem filterMask_map {α β : Type} (f : α → β) : ∀ (m : List Bool) (xs : List α),
    filterMask m (xs.map f) = (filterMask m xs).map f
  | [], _ => rfl
  | _ :: _, [] => rfl
  | true :: bs, x :: xs => by simp [filterMask, filterMask_map f bs xs]
  | false :: bs, _ :: xs => filterMask_map f bs xs

theorem filterMask_pw {α β : Type} {R : α → β → Prop} : ∀ (m : List Bool) {xs : List α} {ys : List β},
    Pw R xs ys → Pw R (filterMask m xs) (filterMask m ys)
  | [], _, _, _ => .nil
  | _ :: _, _, _, .nil => .nil
  | true :: bs, _, _, .cons h hs => .cons h (filterMask_pw bs hs)
  | false :: bs, _, _, .cons _ hs => filterMask_pw bs hs

theorem getElem?_filterMask_true {α : Type} : ∀ (m : List Bool) (xs : List α) (idx : Nat),
    m.length = xs.length → m[idx]? = some true →
    (filterMask m xs)[countTrue (m.take idx)]? = xs[idx]?
  | [], [], _, _, h => by simp at h
  | true :: _, x :: _, 0, _, _ => rfl
  | false :: _, _ :: _, 0, _, h => by simp at h
  | true :: bs, _ :: xs, idx + 1, hl, hm => by
    simp only [List.length_cons] at hl
    simp only [List.getElem?_cons_succ] at hm ⊢
    simp only [List.take_succ_cons, countTrue, filterMask, List.getElem?_cons_succ]
    exact getElem?_filterMask_true bs xs idx (by omega) hm
  | false :: bs, _ :: xs, idx + 1, hl, hm => by
    simp only [List.length_cons] at hl
    simp only [List.getElem?_cons_succ] at hm ⊢
    simp only [List.take_succ_cons, countTrue, filterMask]
    exact getElem?_filterMask_true bs xs idx (by omega) hm

theorem remapAtoms_length (rmask : List Bool) (d : Nat) : ∀ as : List Atom,
    (remapAtoms rmask d as).length = as.length
  | [] => rfl
  | _ :: as => by simp [remapAtoms, remapAtoms_length rmask d as]

theorem keepMask_length (gd : GDef) : (keepMask gd).length = gd.ps.length := by
  unfold keepMask
  dsimp only
  split
  · simp
  · cases h : gd.ps.length <;> simp

theorem keepMask_dead (gd : GDef) : ∀ idx, (keepMask gd).reverse[idx]? = some false →
    gd.body.occ idx = 0 := by
  intro idx hidx
  have hl : (keepMask gd).length = gd.ps.length := keepMask_length gd
  have hlt : idx < gd.ps.length := by
    have : idx < (keepMask gd).reverse.length := (List.getElem?_eq_some_iff.1 hidx).1
    simpa [hl] using this
  have hrev : (keepMask gd)[gd.ps.length - 1 - idx]? = some false := by
    rw [List.getElem?_reverse (by omega)] at hidx
    simpa [hl] using hidx
  unfold keepMask at hrev
  dsimp only at hrev
  split at hrev
  · simp only [List.getElem?_map, List.getElem?_range (show gd.ps.length - 1 - idx < gd.ps.length by omega),
      Option.map_some, Option.some.injEq, decide_eq_false_iff_not] at hrev
    have heq : gd.ps.length - 1 - (gd.ps.length - 1 - idx) = idx := by omega
    rw [heq] at hrev
    omega
  · next hany =>
    have hall : ∀ i < gd.ps.length, gd.body.occ (gd.ps.length - 1 - i) = 0 := by
      intro i hi
      by_cases h0 : gd.body.occ (gd.ps.length - 1 - i) = 0
      · exact h0
      · exfalso
        have : ((List.range gd.ps.length).map fun i => decide (gd.body.occ (gd.ps.length - 1 - i) > 0)).any id = true :=
          List.any_eq_true.2 ⟨true, List.mem_map.2 ⟨i, List.mem_range.2 hi, by simp; omega⟩, rfl⟩
        exact hany this
    have := hall (gd.ps.length - 1 - idx) (by omega)
    have heq : gd.ps.length - 1 - (gd.ps.length - 1 - idx) = idx := by omega
    rw [heq] at this
    exact this

theorem evalAtoms_filterMask {ρ : List Val} : ∀ (m : List Bool) {as : List Atom} {vs : List Val},
    evalAtoms ρ as = some vs → evalAtoms ρ (filterMask m as) = some (filterMask m vs)
  | [], _, _, _ => rfl
  | _ :: _, [], vs, h => by
    simp only [evalAtoms, Option.some.injEq] at h; subst h; rfl
  | true :: bs, a :: as, vs, h => by
    rw [evalAtoms_cons] at h
    cases ha : a.eval ρ with
    | none => simp [ha] at h
    | some v =>
      cases has : evalAtoms ρ as with
      | none => simp [ha, has] at h
      | some vs' =>
        simp only [ha, has, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [filterMask, evalAtoms_cons, ha, evalAtoms_filterMask bs has,
          Option.bind_some, Option.map_some]
  | false :: bs, a :: as, vs, h => by
    rw [evalAtoms_cons] at h
    cases ha : a.eval ρ with
    | none => simp [ha] at h
    | some v =>
      cases has : evalAtoms ρ as with
      | none => simp [ha, has] at h
      | some vs' =>
        simp only [ha, has, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        exact evalAtoms_filterMask bs has

theorem evalAtoms_keptParamAtoms {vs : List Val} (m : List Bool) :
    evalAtoms vs.reverse (keptParamAtoms vs.length m) = some (filterMask m vs) := by
  unfold keptParamAtoms
  have hall : evalAtoms vs.reverse ((List.range vs.length).map fun i => Atom.var (vs.length - 1 - i)) = some vs := by
    suffices ∀ (k : Nat) (pre suf : List Val), k = suf.length →
        evalAtoms (suf.reverse ++ pre) ((List.range k).map fun i => Atom.var (k - 1 - i)) = some suf by
      simpa using this vs.length [] vs rfl
    intro k
    induction k with
    | zero =>
      intro pre suf h
      cases suf with
      | nil => rfl
      | cons _ _ => simp at h
    | succ k ih =>
      intro pre suf h
      cases suf with
      | nil => simp at h
      | cons v suf' =>
        simp only [List.length_cons] at h
        have hk : k = suf'.length := by omega
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, evalAtoms_cons]
        have h0 : (Atom.var (k + 1 - 1 - 0)).eval ((v :: suf').reverse ++ pre) = some v := by
          simp only [Nat.add_sub_cancel, Nat.sub_zero, Atom.eval, List.reverse_cons, List.append_assoc]
          have hlen : suf'.reverse.length = k := by simp [hk]
          rw [List.getElem?_append_right (Nat.le_of_eq hlen), hlen]
          simp
        have hmap : (List.map ((fun i => Atom.var (k + 1 - 1 - i)) ∘ Nat.succ) (List.range k)) =
            (List.range k).map fun i => Atom.var (k - 1 - i) := by
          apply List.map_congr_left
          intro i _; simp only [Function.comp_apply]; congr 1; omega
        have hrest : evalAtoms ((v :: suf').reverse ++ pre) ((List.range k).map fun i => Atom.var (k - 1 - i)) = some suf' := by
          rw [List.reverse_cons, List.append_assoc]
          exact ih (v :: pre) suf' hk
        rw [h0, hmap, hrest]
        rfl
  exact evalAtoms_filterMask m hall

/-! ## Dead-freeness -/

def DeadFree (m : List Bool) (d : Nat) (e : Exp) : Prop :=
  ∀ idx, m[idx]? = some false → e.occ (d + idx) = 0

def DeadFreeBind (m : List Bool) (d : Nat) (b : Bind) : Prop :=
  ∀ idx, m[idx]? = some false → b.occ (d + idx) = 0

def DeadFreeAtom (m : List Bool) (d : Nat) (a : Atom) : Prop :=
  ∀ idx, m[idx]? = some false → a.occ (d + idx) = 0

def DeadFreeAtoms (m : List Bool) (d : Nat) (as : List Atom) : Prop :=
  ∀ idx, m[idx]? = some false → Atom.occList (d + idx) as = 0

theorem DeadFree.bind {m : List Bool} {d : Nat} {c : Ixon.V3.LetMode} {b : Bind} {e : Exp}
    (h : DeadFree m d (.bind c b e)) : DeadFreeBind m d b ∧ DeadFree m (d + 1) e :=
  ⟨fun idx hi => by have := h idx hi; simp only [Exp.occ] at this; omega,
   fun idx hi => by have := h idx hi; simp only [Exp.occ] at this; rw [show d + 1 + idx = d + idx + 1 by omega]; omega⟩

theorem DeadFree.join {m : List Bool} {d n : Nat} {r : Bool} {b e : Exp}
    (h : DeadFree m d (.join n r b e)) : DeadFree m (d + n) b ∧ DeadFree m d e :=
  ⟨fun idx hi => by have := h idx hi; simp only [Exp.occ] at this; rw [show d + n + idx = d + idx + n by omega]; omega,
   fun idx hi => by have := h idx hi; simp only [Exp.occ] at this; omega⟩

theorem DeadFree.jump {m : List Bool} {d j : Nat} {as : List Atom}
    (h : DeadFree m d (.jump j as)) : DeadFreeAtoms m d as := h

theorem DeadFree.case {m : List Bool} {d : Nat} {x : Atom} {alts : List Alt} {dflt : Option Exp}
    (h : DeadFree m d (.case x alts dflt)) :
    DeadFreeAtom m d x ∧
    (∀ a ∈ alts, DeadFree m (d + a.arity) a.body) ∧
    (∀ e, dflt = some e → DeadFree m d e) := by
  refine ⟨fun idx hi => by have := h idx hi; simp only [Exp.occ] at this; omega, ?_, ?_⟩
  · intro a ha idx hi
    have h0 := h idx hi
    simp only [Exp.occ] at h0
    have halts : Exp.altsOcc (d + idx) alts = 0 := by omega
    clear h h0
    revert ha halts
    induction alts with
    | nil => intro ha; cases ha
    | cons a' rest ih =>
      intro ha halts
      cases a' with
      | mk k n b =>
        simp only [Exp.altsOcc] at halts
        rcases List.mem_cons.1 ha with rfl | hmem
        · simp only [Alt.arity, Alt.body]
          rw [show d + n + idx = d + idx + n by omega]; omega
        · exact ih hmem (by omega)
  · intro e he idx hi
    have h0 := h idx hi
    rw [he] at h0
    simp only [Exp.occ, Exp.optOcc] at h0
    omega

theorem DeadFree.ret {m : List Bool} {d : Nat} {a : Atom}
    (h : DeadFree m d (.ret a)) : DeadFreeAtom m d a := h

theorem DeadFree.tick {m : List Bool} {d : Nat} {e : Exp}
    (h : DeadFree m d (.tick e)) : DeadFree m d e := h

theorem DeadFreeBind.app {m : List Bool} {d : Nat} {f : Atom} {as : List Atom}
    (h : DeadFreeBind m d (.app f as)) : DeadFreeAtom m d f ∧ DeadFreeAtoms m d as :=
  ⟨fun idx hi => by have := h idx hi; simp only [Bind.occ] at this; omega,
   fun idx hi => by have := h idx hi; simp only [Bind.occ] at this; omega⟩

theorem DeadFreeBind.fn {m : List Bool} {d : Nat} {ps : List Ixon.V3.BinderMode} {b : Exp}
    (h : DeadFreeBind m d (.fn ps b)) : DeadFree m (d + ps.length) b :=
  fun idx hi => by have := h idx hi; simp only [Bind.occ] at this; rw [show d + ps.length + idx = d + idx + ps.length by omega]; exact this

/-! ## Setting and value relation -/

structure Setting where
  P : Program
  Q : Program
  plan : Plan
  known : Q.known = P.known
  oldGlob : ∀ g gd, P.global? g = some gd →
    match plan.get? g with
    | some (w, keep) =>
      Q.global? g = some { gd with body := wrapperBody w gd.ps.length keep } ∧
      keep.length = gd.ps.length ∧
      keep.any id = true ∧
      DeadFree keep.reverse 0 gd.body ∧
      Q.global? w = some { key := .worker gd.key keep
                           ps := filterMask keep gd.ps
                           result := gd.result
                           body := rewriteExp plan (some keep.reverse) 0 gd.body }
    | none =>
      Q.global? g = some { gd with body := rewriteExp plan none 0 gd.body }

mutual

inductive DV (X : Setting) : Val → Val → Prop
  | lit {l : Lam.Lit} : DV X (.lit l) (.lit l)
  | box : DV X .box .box
  | con {c : Key.CtorKey} {vs ws : List Val} : DVs X vs ws → DV X (.con c vs) (.con c ws)
  | closId {ρ ρ' got got' : List Val} {n : Nat} {b : Exp} :
      DVs X ρ ρ' → DVs X got got' →
      DV X (.clos ρ n b got) (.clos ρ' n (rewriteExp X.plan none (ρ.length + n) b) got')
  | closMask {loc loc' tail ws got got' : List Val} {m : List Bool} {n : Nat} {b : Exp} :
      DVs X loc loc' → DVs X tail ws → DVs X got got' →
      m.length = tail.length →
      DeadFree m (loc.length + n) b →
      DV X (.clos (loc ++ tail) n b got)
           (.clos (loc' ++ filterMask m ws) n (rewriteExp X.plan (some m) (loc.length + n) b) got')
  | wrap {got got' : List Val} {g w : GlobalId} {gd : GDef} {keep : List Bool} :
      DVs X got got' →
      X.P.global? g = some gd →
      X.plan.get? g = some (w, keep) →
      DV X (.clos [] gd.ps.length gd.body got)
           (.clos [] gd.ps.length (wrapperBody w gd.ps.length keep) got')

inductive DVs (X : Setting) : List Val → List Val → Prop
  | nil : DVs X [] []
  | cons {v w : Val} {vs ws : List Val} : DV X v w → DVs X vs ws → DVs X (v :: vs) (w :: ws)

end

variable {X : Setting}

theorem pw_of : ∀ {vs ws : List Val}, DVs X vs ws → Pw (DV X) vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (pw_of hs)

theorem of_pw : ∀ {vs ws : List Val}, Pw (DV X) vs ws → DVs X vs ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (of_pw hs)

theorem base : Rel.Base (DV X) where
  lit _ := .lit
  box := .box
  con _ _ _ h := .con (of_pw h)
  invLit l w h := by cases h; rfl
  invBox w h := by cases h; rfl
  invCon c vs w h := by cases h with | con h => exact ⟨_, rfl, pw_of h⟩
  invClos ρ n b got w h := by
    cases h with
    | closId _ _ => exact ⟨_, _, _, _, rfl⟩
    | closMask _ _ _ _ _ => exact ⟨_, _, _, _, rfl⟩
    | wrap _ _ _ => exact ⟨_, _, _, _, rfl⟩

mutual

theorem dv_obs : ∀ {v w : Val}, DV X v w → obsV v = obsV w
  | _, _, .lit => rfl
  | _, _, .box => rfl
  | _, _, .con h => by
    rename_i c _ _
    cases c with
    | src c => simp only [obsV, dvs_obs h]
    | clo f j => rfl
  | _, _, .closId .. => rfl
  | _, _, .closMask .. => rfl
  | _, _, .wrap .. => rfl

theorem dvs_obs : ∀ {vs ws : List Val}, DVs X vs ws → obsList vs = obsList ws
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [obsList, dv_obs h, dvs_obs hs]

end

/-- Environment relation under optional outer parameter mask. -/
def EnvRel (X : Setting) (rmask : Option (List Bool)) (d : Nat) (ρ ρ' : List Val) : Prop :=
  match rmask with
  | none => Pw (DV X) ρ ρ' ∧ ρ.length = d
  | some m => ∃ loc loc' tail ws, ρ = loc ++ tail ∧ ρ' = loc' ++ filterMask m ws ∧
      Pw (DV X) loc loc' ∧ Pw (DV X) tail ws ∧ loc.length = d ∧ m.length = tail.length

theorem EnvRel.push {rmask : Option (List Bool)} {d : Nat} {ρ ρ' : List Val} {v w : Val}
    (h : EnvRel X rmask d ρ ρ') (hvw : DV X v w) : EnvRel X rmask (d + 1) (v :: ρ) (w :: ρ') := by
  cases rmask with
  | none => exact ⟨.cons hvw h.1, by simp [h.2]⟩
  | some m =>
    obtain ⟨loc, loc', tail, ws, rfl, rfl, hl, ht, hd, hm⟩ := h
    exact ⟨v :: loc, w :: loc', tail, ws, rfl, rfl, .cons hvw hl, ht, by simp [hd], hm⟩

theorem EnvRel.pushList {rmask : Option (List Bool)} {d : Nat} {ρ ρ' vs ws : List Val}
    (h : EnvRel X rmask d ρ ρ') (hvs : Pw (DV X) vs ws) :
    EnvRel X rmask (d + vs.length) (vs ++ ρ) (ws ++ ρ') := by
  cases rmask with
  | none => exact ⟨hvs.append h.1, by simp [h.2]; omega⟩
  | some m =>
    obtain ⟨loc, loc', tail, tws, rfl, rfl, hl, ht, hd, hm⟩ := h
    exact ⟨vs ++ loc, ws ++ loc', tail, tws, by simp, by simp, hvs.append hl, ht, by simp [hd]; omega, hm⟩

/-- Atom evaluation under `EnvRel` and `DeadFreeAtom`. -/
theorem atom_rel {rmask : Option (List Bool)} {d : Nat} {ρ ρ' : List Val}
    (h : EnvRel X rmask d ρ ρ') (a : Atom)
    (hdf : ∀ m, rmask = some m → DeadFreeAtom m d a) :
    (a.eval ρ = none ∧ (match rmask with | some m => remapAtom m d a | none => a).eval ρ' = none) ∨
    ∃ v w, a.eval ρ = some v ∧
      (match rmask with | some m => remapAtom m d a | none => a).eval ρ' = some w ∧ DV X v w := by
  cases rmask with
  | none => exact Rel.atom_eval_rel base h.1 a
  | some m =>
    obtain ⟨loc, loc', tail, ws, rfl, rfl, hl, ht, hd, hm⟩ := h
    have hll : loc'.length = d := by rw [hl.length, hd]
    have htl : ws.length = m.length := by rw [ht.length, hm]
    cases a with
    | lit l => exact .inr ⟨_, _, rfl, rfl, .lit⟩
    | box => exact .inr ⟨_, _, rfl, rfl, .box⟩
    | var j =>
      simp only [remapAtom]
      by_cases hj : j < d
      · simp only [hj, ↓reduceIte]
        simp only [Atom.eval, List.getElem?_append_left (show j < loc.length by omega),
          List.getElem?_append_left (show j < loc'.length by omega)]
        exact hl.get j
      · simp only [hj, ↓reduceIte]
        by_cases hi : j - d < m.length
        · simp only [hi, ↓reduceIte]
          let idx := j - d
          have hmget : m[idx]? = some true := by
            cases hmi : m[idx]? with
            | none => exact absurd (List.getElem?_eq_none_iff.1 hmi) (by omega)
            | some b =>
              cases b with
              | true => rfl
              | false =>
                have hocc := hdf m rfl idx hmi
                simp only [Atom.occ, show d + idx = j by omega, beq_self_eq_true, ↓reduceIte] at hocc
                cases hocc
          have h1 : (loc ++ tail)[j]? = tail[j - d]? := by
            rw [List.getElem?_append_right (by omega), hd]
          have h2 : (loc' ++ filterMask m ws)[d + countTrue (m.take (j - d))]? = (filterMask m ws)[countTrue (m.take (j - d))]? := by
            rw [List.getElem?_append_right (by omega), hll, Nat.add_sub_cancel_left]
          have h3 : (filterMask m ws)[countTrue (m.take (j - d))]? = ws[j - d]? :=
            getElem?_filterMask_true m ws (j - d) htl.symm hmget
          simp only [Atom.eval, h1, h2, h3]
          exact ht.get (j - d)
        · simp only [hi, ↓reduceIte]
          have h1 : (loc ++ tail)[j]? = none :=
            List.getElem?_eq_none (by simp only [List.length_append]; omega)
          have h2 : (loc' ++ filterMask m ws)[d + countTrue m + (j - d - m.length)]? = none := by
            apply List.getElem?_eq_none
            rw [List.length_append, hll, filterMask_length m ws htl.symm]
            omega
          exact .inl ⟨h1, h2⟩

theorem atoms_rel {rmask : Option (List Bool)} {d : Nat} {ρ ρ' : List Val}
    (h : EnvRel X rmask d ρ ρ') : ∀ (as : List Atom),
    (∀ m, rmask = some m → DeadFreeAtoms m d as) →
    (evalAtoms ρ as = none ∧ evalAtoms ρ' (match rmask with | some m => remapAtoms m d as | none => as) = none) ∨
    ∃ vs ws, evalAtoms ρ as = some vs ∧
      evalAtoms ρ' (match rmask with | some m => remapAtoms m d as | none => as) = some ws ∧ Pw (DV X) vs ws
  | [], _ => by cases rmask <;> exact .inr ⟨[], [], rfl, rfl, .nil⟩
  | a :: as, hdf => by
    have ha := atom_rel h a fun m hm idx hi => by
      have := hdf m hm idx hi; simp only [Atom.occList] at this; omega
    have has := atoms_rel h as fun m hm idx hi => by
      have := hdf m hm idx hi; simp only [Atom.occList] at this; omega
    cases rmask with
    | none =>
      simp only [evalAtoms_cons]
      rcases ha with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
      · left; simp [h1, h2]
      · rcases has with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
        · left; simp [h1, h2, h3, h4]
        · right; exact ⟨v :: vs, w :: ws, by simp [h1, h3], by simp [h2, h4], .cons hvw hvs⟩
    | some m =>
      simp only [remapAtoms, evalAtoms_cons]
      rcases ha with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
      · left; simp [h1, h2]
      · rcases has with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
        · left; simp [h1, h2, h3, h4]
        · right; exact ⟨v :: vs, w :: ws, by simp [h1, h3], by simp [h2, h4], .cons hvw hvs⟩

/-- Join environments related under `rewriteExp`. -/
inductive DJ (X : Setting) : List JClo → List JClo → Prop
  | nil : DJ X [] []
  | cons {rmask : Option (List Bool)} {d n : Nat} {r : Bool} {b : Exp}
      {ρ ρ' : List Val} {J0 J0' J J' : List JClo} :
      EnvRel X rmask d ρ ρ' →
      DJ X J0 J0' →
      (∀ m, rmask = some m → DeadFree m (d + n) b) →
      DJ X J J' →
      DJ X (.mk ρ J0 n b r :: J) (.mk ρ' J0' n (rewriteExp X.plan rmask (d + n) b) r :: J')

theorem DJ.get : ∀ {J J' : List JClo}, DJ X J J' → ∀ (j : Nat),
    (J[j]? = none ∧ J'[j]? = none) ∨
    ∃ rmask d n r b ρ ρ' J0 J0',
      J[j]? = some (.mk ρ J0 n b r) ∧
      J'[j]? = some (.mk ρ' J0' n (rewriteExp X.plan rmask (d + n) b) r) ∧
      EnvRel X rmask d ρ ρ' ∧ DJ X J0 J0' ∧ (∀ m, rmask = some m → DeadFree m (d + n) b)
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons hρ hJ0 hdf _, 0 => .inr ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, hρ, hJ0, hdf⟩
  | _, _, .cons _ _ _ hJ, j + 1 => by simpa using hJ.get j

/-- Fundamental lemma statement at clock bound `n`. -/
def FundAt (X : Setting) (n : Nat) : Prop :=
  ∀ {rmask : Option (List Bool)} {d : Nat} {ρ ρ' : List Val} {J J' : List JClo} (e : Exp),
    EnvRel X rmask d ρ ρ' → DJ X J J' → (∀ m, rmask = some m → DeadFree m d e) →
    SimUpTo (DV X) n (fun k => eval X.P k ρ J e)
      (fun k => eval X.Q k ρ' J' (rewriteExp X.plan rmask d e))

/-- Calling a worker on filtered arguments simulates calling the source global. -/
theorem worker_call_sim {n : Nat} (hlow : ∀ m < n, FundAt X m) {g w : GlobalId} {gd : GDef}
    {keep : List Bool} {vs ws : List Val}
    (hP : X.P.global? g = some gd) (hplan : X.plan.get? g = some (w, keep))
    (hvs : Pw (DV X) vs ws) (hl : vs.length = gd.ps.length) :
    SimUpTo (DV X) n
      (fun k => callVal X.P k gd vs)
      (fun k => (Result.ofOption (X.Q.global? w)).bind (callVal X.Q k · (filterMask keep ws))) := by
  have hspec := X.oldGlob g gd hP
  rw [hplan] at hspec
  obtain ⟨_, hkl, _, hdead, hQw⟩ := hspec
  have hwl : ws.length = gd.ps.length := by rw [hvs.length, hl]
  have hfl : (filterMask keep ws).length = (filterMask keep gd.ps).length := by
    rw [filterMask_length keep ws (by omega), filterMask_length keep gd.ps hkl]
  refine (SimUpTo.later
    (c₁ := fun k => eval X.P k vs.reverse [] gd.body)
    (c₂ := fun k => eval X.Q k (filterMask keep ws).reverse [] (rewriteExp X.plan (some keep.reverse) 0 gd.body))
    fun i hi => ?_).congr (fun k => ?_) (fun k => ?_)
  · have hrev : (filterMask keep ws).reverse = filterMask keep.reverse ws.reverse :=
      filterMask_reverse keep ws (by omega)
    have henv : EnvRel X (some keep.reverse) 0 vs.reverse (filterMask keep ws).reverse :=
      ⟨[], [], vs.reverse, ws.reverse, rfl, by simp [hrev], .nil, hvs.reverse, rfl, by simp [hkl, hl]⟩
    exact hlow i (by omega) gd.body henv .nil fun m hm => by cases hm; exact hdead
  · simp [callVal, hl]
  · rw [hQw]; simp [Result.ofOption, callVal, hfl]

theorem app_at {n : Nat} (hlow : ∀ m < n, FundAt X m) : Rel.AppSim X.P X.Q (DV X) n := by
  suffices H : ∀ len, ∀ ⦃f g : Val⦄ ⦃vs ws : List Val⦄, vs.length ≤ len → DV X f g →
      Pw (DV X) vs ws → SimUpTo (DV X) n (fun k => applyN X.P k f vs) (fun k => applyN X.Q k g ws) by
    intro f g vs ws hfg hvs; exact H _ (Nat.le_refl _) hfg hvs
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
  intro f g vs ws hlen hfg hvs
  have hnc : ∀ ⦃f g : Val⦄, (∀ ρ n b got, f ≠ .clos ρ n b got) → (∀ ρ n b got, g ≠ .clos ρ n b got) →
      DV X f g → SimUpTo (DV X) n (fun k => applyN X.P k f vs) (fun k => applyN X.Q k g ws) := by
    intro f g hf hg hfg
    cases vs with
    | nil =>
      cases hvs
      exact (SimUpTo.ok hfg).congr (fun k => applyN_nil' X.P k f) (fun k => applyN_nil' X.Q k g)
    | cons v vs' =>
      cases hvs with
      | cons _ _ =>
        exact (SimUpTo.stuck _).congr (fun k => applyN_not_clos X.P k f v vs' hf)
          (fun k => applyN_not_clos X.Q k g _ _ hg)
  cases hfg with
  | lit => exact hnc (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) .lit
  | box => exact hnc (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) .box
  | con h => exact hnc (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (.con h)
  | closId hρ hgot =>
    rename_i ρ ρ' got got' m b
    have hρ' := pw_of hρ
    have hgot' := pw_of hgot
    have hgl := hgot'.length
    have hvl := hvs.length
    cases vs with
    | nil =>
      cases hvs
      exact (SimUpTo.ok (.closId hρ hgot)).congr (fun k => applyN_nil' X.P k _) (fun k => applyN_nil' X.Q k _)
    | cons v vs' =>
      obtain ⟨w, ws', rfl⟩ : ∃ w ws', ws = w :: ws' := by cases ws with | nil => cases hvs | cons w ws' => exact ⟨w, ws', rfl⟩
      by_cases hg : got.length < m
      · by_cases hu : got.length + (v :: vs').length < m
        · have hu' : got'.length + (w :: ws').length < m := by simp at hvl hu ⊢; omega
          refine (SimUpTo.later fun _ _ => SimUpTo.ok (.closId (n := m) (b := b) hρ (of_pw (hgot'.append hvs)))).congr
            (fun k => by rw [applyN_clos]; simp only [hg, hu, ↓reduceIte])
            (fun k => by rw [applyN_clos]; simp only [show got'.length < m by omega, hu', ↓reduceIte])
        · have hall := hgot'.append hvs
          have htk : ((got ++ v :: vs').take m).reverse.length = m := by
            simp only [List.length_cons] at hu
            simp only [List.length_reverse, List.length_take, List.length_append, List.length_cons]; omega
          refine (SimUpTo.bind (d := fun r k => applyN X.P k r ((got ++ v :: vs').drop m))
            (d' := fun r k => applyN X.Q k r ((got' ++ w :: ws').drop m))
            (ClockMono.later (eval_mono X.Q _ [] _)) (fun r => applyN_mono X.Q r _)
            (SimUpTo.later fun i hi => hlow i (by omega) b (rmask := none) (d := ρ.length + m)
              ⟨(hall.take m).reverse.append hρ', by simp [htk]; omega⟩ .nil (fun _ h => nomatch h))
            fun r r' hr => ?_).congr (fun k => ?_) (fun k => ?_)
          · by_cases hnil : ((got ++ v :: vs').drop m) = []
            · have : ((got' ++ w :: ws').drop m) = [] := by
                rw [List.drop_eq_nil_iff] at hnil ⊢; simp at hnil hvl ⊢; omega
              rw [hnil, this]
              exact (SimUpTo.ok hr).congr (fun k => applyN_nil' X.P k r) (fun k => applyN_nil' X.Q k r')
            · exact ih _ (by simp at hnil hlen ⊢; omega) (Nat.le_refl _) hr (hall.drop m)
          · rw [applyN_clos]; simp only [hg, hu, ↓reduceIte]
            cases k with
            | zero => rfl
            | succ k => simp [later_succ, enter]
          · rw [applyN_clos]
            simp only [show got'.length < m by omega, ↓reduceIte,
              show ¬ (got'.length + (w :: ws').length < m) by simp at hvl hu ⊢; omega]
            cases k with
            | zero => rfl
            | succ k => simp [later_succ, enter]
      · refine (SimUpTo.later (c₁ := fun _ => (.stuck : Result Val)) (c₂ := fun _ => .stuck)
          fun _ _ => SimUpTo.stuck _).congr
          (fun k => by rw [applyN_clos]; simp [hg])
          (fun k => by rw [applyN_clos]; simp [show ¬ got'.length < m by omega])
  | closMask hloc htail hgot hml hdf =>
    rename_i loc loc' tail tws got got' mask m b
    have hloc' := pw_of hloc
    have htail' := pw_of htail
    have hgot' := pw_of hgot
    have hgl := hgot'.length
    have hvl := hvs.length
    cases vs with
    | nil =>
      cases hvs
      exact (SimUpTo.ok (.closMask hloc htail hgot hml hdf)).congr
        (fun k => applyN_nil' X.P k _) (fun k => applyN_nil' X.Q k _)
    | cons v vs' =>
      obtain ⟨w, ws', rfl⟩ : ∃ w ws', ws = w :: ws' := by cases ws with | nil => cases hvs | cons w ws' => exact ⟨w, ws', rfl⟩
      by_cases hg : got.length < m
      · by_cases hu : got.length + (v :: vs').length < m
        · have hu' : got'.length + (w :: ws').length < m := by simp at hvl hu ⊢; omega
          refine (SimUpTo.later fun _ _ => SimUpTo.ok (.closMask hloc htail (of_pw (hgot'.append hvs)) hml hdf)).congr
            (fun k => by rw [applyN_clos]; simp only [hg, hu, ↓reduceIte])
            (fun k => by rw [applyN_clos]; simp only [show got'.length < m by omega, hu', ↓reduceIte])
        · have hall := hgot'.append hvs
          have htk : ((got ++ v :: vs').take m).reverse.length = m := by
            simp only [List.length_cons] at hu
            simp only [List.length_reverse, List.length_take, List.length_append, List.length_cons]; omega
          have henv : EnvRel X (some mask) (loc.length + m)
              (((got ++ v :: vs').take m).reverse ++ (loc ++ tail))
              (((got' ++ w :: ws').take m).reverse ++ (loc' ++ filterMask mask tws)) :=
            ⟨((got ++ v :: vs').take m).reverse ++ loc, ((got' ++ w :: ws').take m).reverse ++ loc',
             tail, tws, by simp, by simp, (hall.take m).reverse.append hloc', htail', by simp [htk]; omega, hml⟩
          refine (SimUpTo.bind (d := fun r k => applyN X.P k r ((got ++ v :: vs').drop m))
            (d' := fun r k => applyN X.Q k r ((got' ++ w :: ws').drop m))
            (ClockMono.later (eval_mono X.Q _ [] _)) (fun r => applyN_mono X.Q r _)
            (SimUpTo.later fun i hi => hlow i (by omega) b henv .nil fun _ hm => by cases hm; exact hdf)
            fun r r' hr => ?_).congr (fun k => ?_) (fun k => ?_)
          · by_cases hnil : ((got ++ v :: vs').drop m) = []
            · have : ((got' ++ w :: ws').drop m) = [] := by
                rw [List.drop_eq_nil_iff] at hnil ⊢; simp at hnil hvl ⊢; omega
              rw [hnil, this]
              exact (SimUpTo.ok hr).congr (fun k => applyN_nil' X.P k r) (fun k => applyN_nil' X.Q k r')
            · exact ih _ (by simp at hnil hlen ⊢; omega) (Nat.le_refl _) hr (hall.drop m)
          · rw [applyN_clos]; simp only [hg, hu, ↓reduceIte]
            cases k with
            | zero => rfl
            | succ k => simp [later_succ, enter]
          · rw [applyN_clos]
            simp only [show got'.length < m by omega, ↓reduceIte,
              show ¬ (got'.length + (w :: ws').length < m) by simp at hvl hu ⊢; omega]
            cases k with
            | zero => rfl
            | succ k => simp [later_succ, enter]
      · refine (SimUpTo.later (c₁ := fun _ => (.stuck : Result Val)) (c₂ := fun _ => .stuck)
          fun _ _ => SimUpTo.stuck _).congr
          (fun k => by rw [applyN_clos]; simp [hg])
          (fun k => by rw [applyN_clos]; simp [show ¬ got'.length < m by omega])
  | wrap hgot hPg hplan =>
    rename_i got got' g0 w0 gd keep
    have hgot' := pw_of hgot
    have hgl := hgot'.length
    have hvl := hvs.length
    have hspec := X.oldGlob g0 gd hPg
    rw [hplan] at hspec
    obtain ⟨_, hkl, _, hdead, hQw⟩ := hspec
    cases vs with
    | nil =>
      cases hvs
      exact (SimUpTo.ok (.wrap hgot hPg hplan)).congr
        (fun k => applyN_nil' X.P k _) (fun k => applyN_nil' X.Q k _)
    | cons v vs' =>
      obtain ⟨w, ws', rfl⟩ : ∃ w ws', ws = w :: ws' := by cases ws with | nil => cases hvs | cons w ws' => exact ⟨w, ws', rfl⟩
      by_cases hg : got.length < gd.ps.length
      · by_cases hu : got.length + (v :: vs').length < gd.ps.length
        · have hu' : got'.length + (w :: ws').length < gd.ps.length := by simp at hvl hu ⊢; omega
          refine (SimUpTo.later fun _ _ => SimUpTo.ok (.wrap (of_pw (hgot'.append hvs)) hPg hplan)).congr
            (fun k => by rw [applyN_clos]; simp only [hg, hu, ↓reduceIte])
            (fun k => by rw [applyN_clos]; simp only [show got'.length < gd.ps.length by omega, hu', ↓reduceIte])
        · have hall := hgot'.append hvs
          have htkV : ((got ++ v :: vs').take gd.ps.length).length = gd.ps.length := by
            simp only [List.length_cons] at hu
            simp only [List.length_take, List.length_append, List.length_cons]; omega
          have htkW : ((got' ++ w :: ws').take gd.ps.length).length = gd.ps.length := by
            rw [(hall.take gd.ps.length).length, htkV]
          have hbodySim : ∀ i < n, SimUpTo (DV X) i
              (fun k => eval X.P k ((got ++ v :: vs').take gd.ps.length).reverse [] gd.body)
              (fun k => eval X.Q k ((got' ++ w :: ws').take gd.ps.length).reverse [] (wrapperBody w0 gd.ps.length keep)) := by
            intro i hi
            let wsTake := (got' ++ w :: ws').take gd.ps.length
            have htkW' : wsTake.length = gd.ps.length := htkW
            have hfl : (filterMask keep wsTake).length = (filterMask keep gd.ps).length := by
              rw [filterMask_length keep _ (by omega), filterMask_length keep gd.ps hkl]
            have hrev : (filterMask keep wsTake).reverse = filterMask keep.reverse wsTake.reverse :=
              filterMask_reverse keep _ (by omega)
            have henv : EnvRel X (some keep.reverse) 0
                ((got ++ v :: vs').take gd.ps.length).reverse (filterMask keep wsTake).reverse :=
              ⟨[], [], ((got ++ v :: vs').take gd.ps.length).reverse, wsTake.reverse,
               rfl, by simp [hrev], .nil, (hall.take gd.ps.length).reverse, rfl, by simp [hkl, htkV]⟩
            have hka : evalAtoms wsTake.reverse (keptParamAtoms gd.ps.length keep) = some (filterMask keep wsTake) := by
              rw [← htkW']; exact evalAtoms_keptParamAtoms keep
            have hinner := hlow i (by omega) gd.body henv .nil fun _ hm => by cases hm; exact hdead
            refine (SimUpTo.laterR (eval_mono X.Q _ [] _) hinner).congr
              (fun _ => rfl) (fun k => ?_)
            unfold wrapperBody
            rw [eval_bind, evalBind_call, hka, hQw]
            simp only [Result.ofOption, Result.bind_ok, callVal, hfl, ↓reduceIte]
            cases k with
            | zero => rfl
            | succ k =>
              simp only [later_succ]
              cases eval X.Q k (filterMask keep wsTake).reverse []
                  (rewriteExp X.plan (some keep.reverse) 0 gd.body) with
              | ok val => simp [eval_ret', Atom.eval, Result.ofOption]
              | timeout | resource _ | trap | stuck => rfl
          refine (SimUpTo.bind (d := fun r k => applyN X.P k r ((got ++ v :: vs').drop gd.ps.length))
            (d' := fun r k => applyN X.Q k r ((got' ++ w :: ws').drop gd.ps.length))
            (ClockMono.later (eval_mono X.Q _ [] _)) (fun r => applyN_mono X.Q r _)
            (SimUpTo.later fun i hi => by
              simpa [List.append_nil] using hbodySim i hi)
            fun r r' hr => ?_).congr (fun k => ?_) (fun k => ?_)
          · by_cases hnil : ((got ++ v :: vs').drop gd.ps.length) = []
            · have : ((got' ++ w :: ws').drop gd.ps.length) = [] := by
                rw [List.drop_eq_nil_iff] at hnil ⊢; simp at hnil hvl ⊢; omega
              rw [hnil, this]
              exact (SimUpTo.ok hr).congr (fun k => applyN_nil' X.P k r) (fun k => applyN_nil' X.Q k r')
            · exact ih _ (by simp at hnil hlen ⊢; omega) (Nat.le_refl _) hr (hall.drop gd.ps.length)
          · rw [applyN_clos]; simp only [hg, hu, ↓reduceIte]
            cases k with
            | zero => rfl
            | succ k => simp [later_succ, enter]
          · rw [applyN_clos]
            simp only [show got'.length < gd.ps.length by omega, ↓reduceIte,
              show ¬ (got'.length + (w :: ws').length < gd.ps.length) by simp at hvl hu ⊢; omega]
            cases k with
            | zero => rfl
            | succ k => simp [later_succ, enter]
      · refine (SimUpTo.later (c₁ := fun _ => (.stuck : Result Val)) (c₂ := fun _ => .stuck)
          fun _ _ => SimUpTo.stuck _).congr
          (fun k => by rw [applyN_clos]; simp [hg])
          (fun k => by rw [applyN_clos]; simp [show ¬ got'.length < gd.ps.length by omega])

mutual

theorem rewriteExp_none_depth (plan : Plan) : ∀ (d₁ d₂ : Nat) (e : Exp),
    rewriteExp plan none d₁ e = rewriteExp plan none d₂ e
  | d₁, d₂, .bind c b e => by
    simp only [rewriteExp, rewriteBind_none_depth plan d₁ d₂ b, rewriteExp_none_depth plan (d₁ + 1) (d₂ + 1) e]
  | d₁, d₂, .join n r b e => by
    simp only [rewriteExp, rewriteExp_none_depth plan (d₁ + n) (d₂ + n) b, rewriteExp_none_depth plan d₁ d₂ e]
  | _, _, .jump j as => by simp only [rewriteExp]
  | d₁, d₂, .case x alts d => by
    simp only [rewriteExp, rewriteAlts_none_depth plan d₁ d₂ alts, rewriteOpt_none_depth plan d₁ d₂ d]
  | _, _, .ret a => by simp only [rewriteExp]
  | d₁, d₂, .tick e => by simp only [rewriteExp, rewriteExp_none_depth plan d₁ d₂ e]
  | _, _, .trap => rfl

theorem rewriteBind_none_depth (plan : Plan) : ∀ (d₁ d₂ : Nat) (b : Bind),
    rewriteBind plan none d₁ b = rewriteBind plan none d₂ b
  | _, _, .atom a => by simp only [rewriteBind]
  | _, _, .con c as => by simp only [rewriteBind]
  | _, _, .proj c i x => by simp only [rewriteBind]
  | _, _, .prim p as => by simp only [rewriteBind]
  | _, _, .glob g => rfl
  | _, _, .call g as => by simp only [rewriteBind]
  | _, _, .app f as => by simp only [rewriteBind]
  | d₁, d₂, .fn ps b => by
    simp only [rewriteBind, rewriteExp_none_depth plan (d₁ + ps.length) (d₂ + ps.length) b]

theorem rewriteAlts_none_depth (plan : Plan) : ∀ (d₁ d₂ : Nat) (alts : List Alt),
    rewriteAlts plan none d₁ alts = rewriteAlts plan none d₂ alts
  | _, _, [] => rfl
  | d₁, d₂, .mk k n b :: rest => by
    simp only [rewriteAlts, rewriteExp_none_depth plan (d₁ + n) (d₂ + n) b, rewriteAlts_none_depth plan d₁ d₂ rest]

theorem rewriteOpt_none_depth (plan : Plan) : ∀ (d₁ d₂ : Nat) (o : Option Exp),
    rewriteOpt plan none d₁ o = rewriteOpt plan none d₂ o
  | _, _, none => rfl
  | d₁, d₂, some e => by simp only [rewriteOpt, rewriteExp_none_depth plan d₁ d₂ e]

end

theorem call_at {n : Nat} (hlow : ∀ m < n, FundAt X m) : Rel.CallSim X.P X.Q (DV X) n := by
  intro g vs ws hvs
  cases hP : X.P.global? g with
  | none => exact (SimUpTo.stuck _).congr (fun _ => rfl) (fun _ => rfl)
  | some gd =>
    have hspec := X.oldGlob g gd hP
    have hvl := hvs.length
    cases hpl : X.plan.get? g with
    | none =>
      rw [hpl] at hspec
      rw [hspec]
      simp only [Result.ofOption, Result.bind_ok]
      by_cases hl : vs.length = gd.ps.length
      · have hl' : ws.length = gd.ps.length := by rw [hvl, hl]
        refine (SimUpTo.later fun i hi => hlow i (by omega) gd.body (rmask := none) (d := gd.ps.length)
          ⟨hvs.reverse, by simp [hl]⟩ .nil (fun _ h => nomatch h)).congr
          (fun _ => by simp [callVal, hl])
          (fun _ => by rw [rewriteExp_none_depth X.plan 0 gd.ps.length gd.body]; simp [callVal, hl'])
      · refine (SimUpTo.stuck _).congr (fun _ => by simp [callVal, hl]) (fun _ => rfl)
    | some wk =>
      obtain ⟨w, keep⟩ := wk
      rw [hpl] at hspec
      obtain ⟨hQg, hkl, _, hdead, hQw⟩ := hspec
      rw [hQg]
      simp only [Result.ofOption, Result.bind_ok]
      by_cases hl : vs.length = gd.ps.length
      · have hwl : ws.length = gd.ps.length := by rw [hvl, hl]
        have hfl : (filterMask keep ws).length = (filterMask keep gd.ps).length := by
          rw [filterMask_length keep ws (by omega), filterMask_length keep gd.ps hkl]
        have hrev : (filterMask keep ws).reverse = filterMask keep.reverse ws.reverse :=
          filterMask_reverse keep ws (by omega)
        have henv : EnvRel X (some keep.reverse) 0 vs.reverse (filterMask keep ws).reverse :=
          ⟨[], [], vs.reverse, ws.reverse, rfl, by simp [hrev], .nil, hvs.reverse, rfl, by simp [hkl, hl]⟩
        have hka : evalAtoms ws.reverse (keptParamAtoms gd.ps.length keep) = some (filterMask keep ws) := by
          rw [← hwl]; exact evalAtoms_keptParamAtoms keep
        have hbodySim : ∀ i < n, SimUpTo (DV X) i
            (fun k => eval X.P k vs.reverse [] gd.body)
            (fun k => eval X.Q k ws.reverse [] (wrapperBody w gd.ps.length keep)) := by
          intro i hi
          refine (SimUpTo.laterR (eval_mono X.Q _ [] _)
            (hlow i (by omega) gd.body henv .nil fun _ hm => by cases hm; exact hdead)).congr
            (fun _ => rfl) (fun k => ?_)
          unfold wrapperBody
          rw [eval_bind, evalBind_call, hka, hQw]
          simp only [Result.ofOption, Result.bind_ok, callVal, hfl, ↓reduceIte]
          cases k with
          | zero => rfl
          | succ k =>
            simp only [later_succ]
            cases eval X.Q k (filterMask keep ws).reverse [] (rewriteExp X.plan (some keep.reverse) 0 gd.body) with
            | ok val => simp [eval_ret', Atom.eval, Result.ofOption]
            | timeout | resource _ | trap | stuck => rfl
        refine (SimUpTo.later fun i hi => hbodySim i hi).congr
          (fun _ => by simp [callVal, hl])
          (fun _ => by simp [callVal, hwl])
      · refine (SimUpTo.stuck _).congr (fun _ => by simp [callVal, hl]) (fun _ => rfl)

theorem glob_at {n : Nat} (hlow : ∀ m < n, FundAt X m) : Rel.GlobSim X.P X.Q (DV X) n := by
  intro g
  cases hP : X.P.global? g with
  | none => exact (SimUpTo.stuck _).congr (fun _ => rfl) (fun _ => rfl)
  | some gd =>
    have hspec := X.oldGlob g gd hP
    cases hpl : X.plan.get? g with
    | none =>
      rw [hpl] at hspec
      rw [hspec]
      simp only [Result.ofOption, Result.bind_ok]
      unfold globVal
      cases hps : gd.ps with
      | nil =>
        exact SimUpTo.later fun i hi => hlow i (by omega) gd.body (rmask := none) ⟨.nil, rfl⟩ .nil (fun _ h => nomatch h)
      | cons bm bms =>
        have hrew : rewriteExp X.plan none 0 gd.body = rewriteExp X.plan none (([] : List Val).length + (bm :: bms).length) gd.body :=
          rewriteExp_none_depth X.plan 0 _ gd.body
        rw [hrew]
        exact SimUpTo.ok (DV.closId (ρ := []) (ρ' := []) (got := []) (got' := []) .nil .nil)
    | some wk =>
      obtain ⟨w, keep⟩ := wk
      rw [hpl] at hspec
      obtain ⟨hQg, hkl, hka, hdead, hQw⟩ := hspec
      rw [hQg]
      simp only [Result.ofOption, Result.bind_ok]
      unfold globVal
      cases hps : gd.ps with
      | nil =>
        have : keep = [] := List.eq_nil_of_length_eq_zero (by rw [hkl, hps]; rfl)
        subst this; simp at hka
      | cons bm bms =>
        have hlen : (bm :: bms).length = gd.ps.length := by rw [hps]
        rw [hlen]
        exact SimUpTo.ok (DV.wrap .nil hP hpl)

mutual

theorem fund_exp {n : Nat} (hlow : ∀ m < n, FundAt X m) (happ : Rel.AppSim X.P X.Q (DV X) n)
    (hcall : Rel.CallSim X.P X.Q (DV X) n) (hglob : Rel.GlobSim X.P X.Q (DV X) n) :
    ∀ (e : Exp) {rmask : Option (List Bool)} {d : Nat} {ρ ρ' : List Val} {J J' : List JClo},
      EnvRel X rmask d ρ ρ' → DJ X J J' → (∀ m, rmask = some m → DeadFree m d e) →
      SimUpTo (DV X) n (fun k => eval X.P k ρ J e)
        (fun k => eval X.Q k ρ' J' (rewriteExp X.plan rmask d e))
  | .bind c b e, rmask, d, ρ, ρ', J, J', hρ, hJ, hdf => by
    have hb := fund_bind hlow happ hcall hglob b hρ fun m hm => (hdf m hm).bind.1
    refine (SimUpTo.bind (evalBind_mono X.Q ρ' _) (fun w => eval_mono X.Q (w :: ρ') J' _) hb fun v w hvw =>
      fund_exp hlow happ hcall hglob e (hρ.push hvw) hJ fun m hm => (hdf m hm).bind.2).congr
      (fun k => eval_bind X.P k ρ J c b e)
      (fun k => eval_bind X.Q k ρ' J' c (rewriteBind X.plan rmask d b) (rewriteExp X.plan rmask (d + 1) e))
  | .join ar r b e, rmask, d, ρ, ρ', J, J', hρ, hJ, hdf => by
    have hJ' : DJ X (.mk ρ J ar b r :: J) (.mk ρ' J' ar (rewriteExp X.plan rmask (d + ar) b) r :: J') :=
      .cons hρ hJ (fun m hm => (hdf m hm).join.1) hJ
    refine (fund_exp hlow happ hcall hglob e hρ hJ' fun m hm => (hdf m hm).join.2).congr
      (fun k => eval_join' X.P k ρ J ar r b e)
      (fun k => eval_join' X.Q k ρ' J' ar r (rewriteExp X.plan rmask (d + ar) b) (rewriteExp X.plan rmask d e))
  | .jump j as, rmask, d, ρ, ρ', J, J', hρ, hJ, hdf => by
    have has := atoms_rel hρ as fun m hm => (hdf m hm).jump
    rcases hJ.get j with ⟨hj1, hj2⟩ | ⟨rmj, dj, nj, rj, bj, ρj, ρj', J0, J0', hj1, hj2, hρj, hJ0, hdfj⟩
    · refine (SimUpTo.stuck _).congr (fun k => by rw [eval_jump, hj1]; rfl) (fun _ => rfl)
    · rcases has with ⟨ha1, ha2⟩ | ⟨vs, ws, ha1, ha2, hvs⟩
      · refine (SimUpTo.stuck _).congr (fun k => by rw [eval_jump, hj1, ha1]; rfl) (fun _ => rfl)
      · by_cases hl : vs.length = nj
        · have hl' : ws.length = nj := by rw [hvs.length, hl]
          have hJ'' : DJ X (if rj then .mk ρj J0 nj bj rj :: J0 else J0)
              (if rj then .mk ρj' J0' nj (rewriteExp X.plan rmj (dj + nj) bj) rj :: J0' else J0') := by
            cases rj <;> simp [hJ0, DJ.cons hρj hJ0 hdfj hJ0]
          have hρ'' : EnvRel X rmj (dj + nj) (vs.reverse ++ ρj) (ws.reverse ++ ρj') := by
            have := hρj.pushList hvs.reverse
            simpa [hl] using this
          refine (SimUpTo.later fun i hi => hlow i (by omega) bj hρ'' hJ'' hdfj).congr
            (fun k => by rw [eval_jump, hj1, ha1]; simp [Result.ofOption, jumpTo, hl])
            (fun k => by
              cases rmask with
              | none => simp only [rewriteExp]; rw [eval_jump, hj2]; simp only [Result.ofOption, Result.bind_ok]; rw [ha2]; simp [Result.ofOption, jumpTo, hl']
              | some m => simp only [rewriteExp]; rw [eval_jump, hj2]; simp only [Result.ofOption, Result.bind_ok]; rw [ha2]; simp [Result.ofOption, jumpTo, hl'])
        · refine (SimUpTo.stuck _).congr
            (fun k => by rw [eval_jump, hj1, ha1]; simp [Result.ofOption, jumpTo, hl]) (fun _ => rfl)
  | .case x alts dflt, rmask, d, ρ, ρ', J, J', hρ, hJ, hdf => by
    have hx := atom_rel hρ x fun m hm => (hdf m hm).case.1
    rcases hx with ⟨hx1, hx2⟩ | ⟨v, w, hx1, hx2, hvw⟩
    · refine (SimUpTo.stuck _).congr (fun k => by rw [eval_case, hx1]; rfl) (fun _ => rfl)
    · rcases Rel.asCtor_rel base X.P.known hvw with hnone | ⟨c, vfs, wfs, hvc, hwc, hfs⟩
      · refine (SimUpTo.stuck _).congr (fun k => by rw [eval_case, hx1]; simp [Result.ofOption, hnone])
          (fun _ => rfl)
      · have hwc' : w.asCtor X.Q.known = some (c, wfs) := by rw [X.known]; exact hwc
        have hdflt : SimUpTo (DV X) n (fun k => evalAlts X.P k ρ J c vfs [] dflt)
            (fun k => evalAlts X.Q k ρ' J' c wfs [] (rewriteOpt X.plan rmask d dflt)) :=
          match dflt, fun e he m hm => (hdf m hm).case.2.2 e he with
          | none, _ =>
            (SimUpTo.stuck _).congr (fun _ => by rw [evalAlts_nil]) (fun _ => by rw [rewriteOpt, evalAlts_nil])
          | some e, hdfE =>
            (fund_exp hlow happ hcall hglob e hρ hJ (hdfE e rfl)).congr
              (fun _ => by rw [evalAlts_nil]) (fun _ => by rw [rewriteOpt, evalAlts_nil])
        refine (fund_alts hlow happ hcall hglob alts dflt c vfs wfs hfs hρ hJ
          (fun a ha m hm => (hdf m hm).case.2.1 a ha) hdflt).congr
          (fun k => by rw [eval_case, hx1]; simp [Result.ofOption, hvc])
          (fun k => by
            cases rmask with
            | none => simp only [rewriteExp]; rw [eval_case, hx2]; simp [Result.ofOption, hwc']
            | some m => simp only [rewriteExp]; rw [eval_case, hx2]; simp [Result.ofOption, hwc'])
  | .ret a, rmask, d, ρ, ρ', J, J', hρ, _, hdf =>
    (Rel.sim_ofOption (atom_rel hρ a fun m hm => (hdf m hm).ret)).congr
      (fun k => eval_ret' X.P k ρ J a)
      (fun k => eval_ret' X.Q k ρ' J' _)
  | .tick e, rmask, d, ρ, ρ', J, J', hρ, hJ, hdf =>
    (SimUpTo.later fun i hi => hlow i (by omega) e hρ hJ fun m hm => (hdf m hm).tick).congr
      (fun k => eval_tick X.P k ρ J e)
      (fun k => eval_tick X.Q k ρ' J' (rewriteExp X.plan rmask d e))
  | .trap, _, _, ρ, ρ', J, J', _, _, _ =>
    SimUpTo.trap.congr (fun k => eval_trap' X.P k ρ J) (fun k => eval_trap' X.Q k ρ' J')

theorem fund_alts {n : Nat} (hlow : ∀ m < n, FundAt X m) (happ : Rel.AppSim X.P X.Q (DV X) n)
    (hcall : Rel.CallSim X.P X.Q (DV X) n) (hglob : Rel.GlobSim X.P X.Q (DV X) n) :
    ∀ (alts : List Alt) (dflt : Option Exp) {rmask : Option (List Bool)} {d : Nat}
      {ρ ρ' : List Val} {J J' : List JClo} (c : Key.CtorKey) (vfs wfs : List Val),
      Pw (DV X) vfs wfs → EnvRel X rmask d ρ ρ' → DJ X J J' →
      (∀ a ∈ alts, ∀ m, rmask = some m → DeadFree m (d + a.arity) a.body) →
      SimUpTo (DV X) n (fun k => evalAlts X.P k ρ J c vfs [] dflt)
        (fun k => evalAlts X.Q k ρ' J' c wfs [] (rewriteOpt X.plan rmask d dflt)) →
      SimUpTo (DV X) n (fun k => evalAlts X.P k ρ J c vfs alts dflt)
        (fun k => evalAlts X.Q k ρ' J' c wfs (rewriteAlts X.plan rmask d alts) (rewriteOpt X.plan rmask d dflt))
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd => hd
  | .mk key ar b :: rest, dflt, rmask, d, ρ, ρ', J, J', c, vfs, wfs, hfs, hρ, hJ, ha, hd => by
    have hfl := hfs.length
    by_cases hm : key = c ∧ ar = vfs.length
    · have hm' : key = c ∧ ar = wfs.length := ⟨hm.1, by omega⟩
      have hρ' : EnvRel X rmask (d + ar) (vfs.reverse ++ ρ) (wfs.reverse ++ ρ') := by
        have := hρ.pushList hfs.reverse
        simpa [hm.2] using this
      refine (fund_exp hlow happ hcall hglob b hρ' hJ (ha (.mk key ar b) List.mem_cons_self)).congr
        (fun k => by rw [evalAlts_cons, if_pos hm])
        (fun k => by rw [rewriteAlts, evalAlts_cons, if_pos hm'])
    · have hm' : ¬ (key = c ∧ ar = wfs.length) := fun h => hm ⟨h.1, by omega⟩
      refine (fund_alts hlow happ hcall hglob rest dflt c vfs wfs hfs hρ hJ
        (fun a hmem => ha a (List.mem_cons_of_mem _ hmem)) hd).congr
        (fun k => by rw [evalAlts_cons, if_neg hm])
        (fun k => by rw [rewriteAlts, evalAlts_cons, if_neg hm'])

theorem fund_bind {n : Nat} (hlow : ∀ m < n, FundAt X m) (happ : Rel.AppSim X.P X.Q (DV X) n)
    (hcall : Rel.CallSim X.P X.Q (DV X) n) (hglob : Rel.GlobSim X.P X.Q (DV X) n) :
    ∀ (b : Bind) {rmask : Option (List Bool)} {d : Nat} {ρ ρ' : List Val},
      EnvRel X rmask d ρ ρ' → (∀ m, rmask = some m → DeadFreeBind m d b) →
      SimUpTo (DV X) n (fun k => evalBind X.P k ρ b)
        (fun k => evalBind X.Q k ρ' (rewriteBind X.plan rmask d b))
  | .atom a, rmask, d, ρ, ρ', hρ, hdf =>
    (Rel.sim_ofOption (atom_rel hρ a hdf)).congr
      (fun k => evalBind_atom X.P k ρ a) (fun k => evalBind_atom X.Q k ρ' _)
  | .con c as, rmask, d, ρ, ρ', hρ, hdf => by
    rcases atoms_rel hρ as hdf with ⟨h1, h2⟩ | ⟨vs, ws, h1, h2, hvs⟩
    · refine (SimUpTo.stuck _).congr (fun k => by rw [evalBind_con, h1]; rfl) (fun _ => rfl)
    · refine (SimUpTo.ok (.con (of_pw hvs))).congr
        (fun k => by rw [evalBind_con, h1]; rfl)
        (fun k => by cases rmask <;> simp only [rewriteBind, evalBind_con, h2, Result.ofOption, Result.bind_ok])
  | .proj c i x, rmask, d, ρ, ρ', hρ, hdf => by
    rcases atom_rel hρ x hdf with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
    · refine (SimUpTo.stuck _).congr (fun k => by rw [evalBind_proj, h1]; rfl) (fun _ => rfl)
    · cases v with
      | con c' vs =>
        obtain ⟨ws, rfl, hvs⟩ := base.invCon c' vs w hvw
        by_cases hc : c' = c
        · refine (Rel.sim_ofOption (hvs.get i)).congr
            (fun k => by rw [evalBind_proj, h1]; simp [Result.ofOption, projVal, hc])
            (fun k => by cases rmask <;> simp only [rewriteBind, evalBind_proj, h2, Result.ofOption, Result.bind_ok, projVal, hc, beq_self_eq_true, ↓reduceIte])
        · refine (SimUpTo.stuck _).congr
            (fun k => by rw [evalBind_proj, h1]; simp [Result.ofOption, projVal, hc]) (fun _ => rfl)
      | lit _ | box | clos _ _ _ _ =>
        refine (SimUpTo.stuck _).congr (fun k => by rw [evalBind_proj, h1]; rfl) (fun _ => rfl)
  | .prim p as, rmask, d, ρ, ρ', hρ, hdf => by
    rcases atoms_rel hρ as hdf with ⟨h1, h2⟩ | ⟨vs, ws, h1, h2, hvs⟩
    · refine (SimUpTo.stuck _).congr (fun k => by rw [evalBind_prim, h1]; rfl) (fun _ => rfl)
    · refine (Rel.prim_rel base X.P.known p hvs).congr
        (fun k => by rw [evalBind_prim, h1]; rfl)
        (fun k => by cases rmask <;> simp only [rewriteBind, evalBind_prim, h2, X.known, Result.ofOption, Result.bind_ok])
  | .glob g, _, _, ρ, ρ', _, _ =>
    (hglob g).congr (fun k => evalBind_glob X.P k ρ g) (fun k => evalBind_glob X.Q k ρ' g)
  | .call g as, rmask, d, ρ, ρ', hρ, hdf => by
    rcases atoms_rel hρ as hdf with ⟨h1, h2⟩ | ⟨vs, ws, h1, h2, hvs⟩
    · refine (SimUpTo.stuck _).congr
        (fun k => by rw [evalBind_call, h1]; cases X.P.global? g <;> rfl) (fun _ => rfl)
    · have hcall_same : ∀ (as' : List Atom), evalAtoms ρ' as' = some ws →
          SimUpTo (DV X) n (fun k => evalBind X.P k ρ (.call g as))
            (fun k => evalBind X.Q k ρ' (.call g as')) := fun as' ha' =>
        (hcall g hvs).congr
          (fun k => by rw [evalBind_call]; cases X.P.global? g <;> simp [Result.ofOption, h1])
          (fun k => by rw [evalBind_call]; cases X.Q.global? g <;> simp [Result.ofOption, ha'])
      have hcall_plan : ∀ (as' : List Atom), as'.length = as.length → evalAtoms ρ' as' = some ws →
          SimUpTo (DV X) n (fun k => evalBind X.P k ρ (.call g as))
            (fun k => evalBind X.Q k ρ'
              (match X.plan.get? g with
               | some (w, keep) => if as'.length == keep.length then .call w (filterMask keep as') else .call g as'
               | none => .call g as')) := by
        intro as' hasl ha'
        cases hpl : X.plan.get? g with
        | none => exact hcall_same as' ha'
        | some wk =>
          obtain ⟨w, keep⟩ := wk
          dsimp only
          by_cases hlen : (as'.length == keep.length) = true
          · rw [if_pos hlen]
            have hkl : as.length = keep.length := by rw [← hasl]; exact beq_iff_eq.1 hlen
            cases hPg : X.P.global? g with
            | none =>
              refine (SimUpTo.stuck _).congr (fun k => by rw [evalBind_call, hPg]; rfl) (fun _ => rfl)
            | some gd =>
              have hspec := X.oldGlob g gd hPg
              rw [hpl] at hspec
              have hvl : vs.length = gd.ps.length :=
                (evalAtoms_length ρ h1).trans (hkl.trans hspec.2.1)
              have hf2 : evalAtoms ρ' (filterMask keep as') = some (filterMask keep ws) :=
                evalAtoms_filterMask keep ha'
              refine (worker_call_sim hlow hPg hpl hvs hvl).congr
                (fun k => by rw [evalBind_call, hPg]; simp [Result.ofOption, h1])
                (fun k => by rw [evalBind_call]; cases X.Q.global? w <;> simp [Result.ofOption, hf2])
          · rw [if_neg hlen]
            exact hcall_same as' ha'
      cases rmask with
      | none => exact hcall_plan as rfl h2
      | some m => exact hcall_plan (remapAtoms m d as) (remapAtoms_length m d as) h2
  | .app f as, rmask, d, ρ, ρ', hρ, hdf => by
    rcases atom_rel hρ f (fun m hm => (hdf m hm).app.1) with ⟨h1, h2⟩ | ⟨fv, fw, h1, h2, hfw⟩
    · refine (SimUpTo.stuck _).congr (fun k => by rw [evalBind_app, h1]; rfl) (fun _ => rfl)
    · rcases atoms_rel hρ as (fun m hm => (hdf m hm).app.2) with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
      · refine (SimUpTo.stuck _).congr (fun k => by rw [evalBind_app, h1, h3]; rfl) (fun _ => rfl)
      · refine (happ hfw hvs).congr
          (fun k => by rw [evalBind_app, h1, h3]; rfl)
          (fun k => by cases rmask <;> simp only [rewriteBind, evalBind_app, h2, h4, Result.ofOption, Result.bind_ok])
  | .fn ps b, rmask, d, ρ, ρ', hρ, hdf => by
    cases hps : ps with
    | nil =>
      refine (SimUpTo.stuck _).congr
        (fun k => evalBind_fn_nil X.P k ρ b) (fun _ => rfl)
    | cons p ps' =>
      have hne : (p :: ps') ≠ [] := List.cons_ne_nil p ps'
      cases rmask with
      | none =>
        have hlen : d = ρ.length := hρ.2.symm
        rw [hlen]
        refine (SimUpTo.ok (DV.closId (n := (p :: ps').length) (b := b) (of_pw hρ.1) .nil)).congr
          (fun k => evalBind_fn X.P k ρ (p :: ps') b hne)
          (fun k => by rw [rewriteBind, evalBind_fn X.Q k ρ' (p :: ps') _ hne])
      | some m =>
        obtain ⟨loc, loc', tail, tws, rfl, rfl, hl, ht, hd, hm⟩ := hρ
        have hfn : DeadFree m (loc.length + (p :: ps').length) b := by
          rw [hd, ← hps]; exact (hdf m rfl).fn
        rw [← hd]
        refine (SimUpTo.ok (DV.closMask (n := (p :: ps').length) (b := b) (of_pw hl) (of_pw ht) .nil hm hfn)).congr
          (fun k => evalBind_fn X.P k (loc ++ tail) (p :: ps') b hne)
          (fun k => by rw [rewriteBind, evalBind_fn X.Q k (loc' ++ filterMask m tws) (p :: ps') _ hne])

end

theorem levels (X : Setting) : ∀ n, FundAt X n ∧ Rel.AppSim X.P X.Q (DV X) n ∧
    Rel.CallSim X.P X.Q (DV X) n ∧ Rel.GlobSim X.P X.Q (DV X) n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  have hlow : ∀ m < n, FundAt X m := fun m hm => (ih m hm).1
  have happ := app_at hlow
  have hcall := call_at hlow
  have hglob := glob_at hlow
  exact ⟨fun e hρ hJ hdf => fund_exp hlow happ hcall hglob e hρ hJ hdf, happ, hcall, hglob⟩

theorem pw_lits (ns : List Nat) : Pw (DV X) (ns.map fun n => .lit (.nat n)) (ns.map fun n => .lit (.nat n)) := by
  induction ns with
  | nil => exact .nil
  | cons _ _ ih => exact .cons .lit ih

theorem setting_refines (X : Setting) (hroots : X.Q.roots = X.P.roots) : Sem.Refines X.P X.Q := by
  refine Sem.Refines.of_sim (R := DV X) (fun _ _ h => dv_obs h) fun ⟨i, xs⟩ => ⟨id, SimUpTo.sim fun n => ?_⟩
  show SimUpTo (DV X) n (anfRun X.P (i, xs)) (anfRun X.Q (i, xs))
  unfold anfRun
  rw [hroots]
  cases X.P.roots[i]? with
  | none => exact SimUpTo.stuck _
  | some r =>
    refine (SimUpTo.bind (evalBind_mono X.Q [] (.glob r)) (fun w => applyN_mono X.Q w _)
      (((levels X n).2.2.2 r).congr (fun k => evalBind_glob X.P k [] r)
        (fun k => evalBind_glob X.Q k [] r))
      fun v w hvw => (levels X n).2.1 hvw (pw_lits xs)).congr
      (fun k => run_eq X.P k r _) (fun k => run_eq X.Q k r _)

/-! ## `DeadParam.run` satisfies `Setting`, `WF`, `tables`, and `FirstOrder` -/

theorem candidate_spec {P : Program} {g : GlobalId} {gd : GDef} {keep : List Bool}
    (h : candidate P g gd = some keep) :
    keep = keepMask gd ∧ keep.length = gd.ps.length ∧ keep.any id = true ∧
      DeadFree keep.reverse 0 gd.body := by
  unfold candidate at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hc
      refine ⟨rfl, keepMask_length gd, hc.2, fun idx hi => ?_⟩
      simpa using keepMask_dead gd idx hi
    · cases h

theorem buildPlan_wf (P : Program) : ∀ (next : GlobalId) (gs : List (GlobalId × GDef)),
    (∀ x ∈ gs, x.1 < next ∧ P.global? x.1 = some x.2) → (gs.map (·.1)).Nodup →
    let es := buildPlan P next gs
    (∀ e ∈ es, e.1 ∈ gs.map (·.1) ∧ P.global? e.1 = some e.2.2.1 ∧
      candidate P e.1 e.2.2.1 = some e.2.2.2 ∧ next ≤ e.2.1 ∧ e.2.1 < next + es.length) ∧
    (es.map (·.1)).Nodup ∧
    (es.map (·.2.1)) = (List.range es.length).map (next + ·)
  | _, [], _, _ => by simp [buildPlan]
  | next, (g, gd) :: rest, hlt, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hrestLt : ∀ x ∈ rest, x.1 < next ∧ P.global? x.1 = some x.2 :=
      fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    dsimp only [buildPlan]
    cases hc : candidate P g gd with
    | none =>
      simp only
      obtain ⟨h1, h2, h3⟩ := buildPlan_wf P next rest hrestLt hnd.2
      refine ⟨fun e he => ?_, h2, h3⟩
      obtain ⟨hm, hg, hce, hlo, hhi⟩ := h1 e he
      exact ⟨List.mem_cons_of_mem _ hm, hg, hce, hlo, hhi⟩
    | some keep =>
      simp only
      have hrestLt' : ∀ x ∈ rest, x.1 < next + 1 ∧ P.global? x.1 = some x.2 :=
        fun x hx => ⟨Nat.lt_succ_of_lt (hrestLt x hx).1, (hrestLt x hx).2⟩
      obtain ⟨h1, h2, h3⟩ := buildPlan_wf P (next + 1) rest hrestLt' hnd.2
      refine ⟨fun e he => ?_, ?_, ?_⟩
      · rcases List.mem_cons.1 he with rfl | hm
        · refine ⟨List.mem_cons_self, (hlt (g, gd) List.mem_cons_self).2, hc, Nat.le_refl _, ?_⟩
          simp only [List.length_cons]
          exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
        · obtain ⟨hmem, hg, hce, hlo, hhi⟩ := h1 e hm
          refine ⟨List.mem_cons_of_mem _ hmem, hg, hce, Nat.le_of_succ_le hlo, ?_⟩
          simp only [List.length_cons]
          rw [← Nat.add_assoc, Nat.add_right_comm]
          exact hhi
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, h2⟩
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
        exact hnd.1 (h1 e he).1
      · simp only [List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_map,
          Nat.add_zero, List.cons.injEq, true_and]
        rw [h3]
        apply List.map_congr_left
        intro i _; simp only [Function.comp_apply, Nat.succ_eq_add_one]
        rw [Nat.add_assoc, Nat.add_comm 1 i]

theorem run_tables (P : Program) : (run P).known = P.known ∧ (run P).ctors = P.ctors := by
  unfold run
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

theorem run_roots (P : Program) : (run P).roots = P.roots := by
  unfold run
  dsimp only
  split <;> rfl

mutual

theorem rewriteExp_firstOrder {plan : Plan} {isFn : GlobalId → Bool} :
    ∀ {rmask : Option (List Bool)} {d : Nat} (e : Exp),
      Exp.firstOrder isFn e = true → Exp.firstOrder isFn (rewriteExp plan rmask d e) = true
  | rmask, d, .bind _ b e, h => by
    simp only [rewriteExp, Exp.firstOrder, Bool.and_eq_true] at h ⊢
    exact ⟨rewriteBind_firstOrder b h.1, rewriteExp_firstOrder e h.2⟩
  | rmask, d, .join n r b e, h => by
    simp only [rewriteExp, Exp.firstOrder, Bool.and_eq_true] at h ⊢
    exact ⟨rewriteExp_firstOrder b h.1, rewriteExp_firstOrder e h.2⟩
  | _, _, .jump .., _ => rfl
  | rmask, d, .case x alts dflt, h => by
    simp only [rewriteExp, Exp.firstOrder, Bool.and_eq_true] at h ⊢
    exact ⟨rewriteAlts_firstOrder alts h.1, rewriteOpt_firstOrder dflt h.2⟩
  | _, _, .ret _, _ => rfl
  | rmask, d, .tick e, h => rewriteExp_firstOrder e h
  | _, _, .trap, _ => rfl

theorem rewriteBind_firstOrder {plan : Plan} {isFn : GlobalId → Bool} :
    ∀ {rmask : Option (List Bool)} {d : Nat} (b : Bind),
      Bind.firstOrder isFn b = true → Bind.firstOrder isFn (rewriteBind plan rmask d b) = true
  | _, _, .atom _, _ => rfl
  | _, _, .con .., _ => rfl
  | _, _, .proj .., _ => rfl
  | _, _, .prim .., _ => rfl
  | _, _, .glob _, h => h
  | _, _, .call g as, _ => by
    simp only [rewriteBind]
    split
    · split <;> (split <;> rfl)
    · rfl
  | _, _, .app .., h => by simp [Bind.firstOrder] at h
  | _, _, .fn .., h => by simp [Bind.firstOrder] at h

theorem rewriteAlts_firstOrder {plan : Plan} {isFn : GlobalId → Bool} :
    ∀ {rmask : Option (List Bool)} {d : Nat} (alts : List Alt),
      Exp.altsFirstOrder isFn alts = true → Exp.altsFirstOrder isFn (rewriteAlts plan rmask d alts) = true
  | _, _, [], _ => rfl
  | rmask, d, .mk _ _ b :: rest, h => by
    simp only [rewriteAlts, Exp.altsFirstOrder, Bool.and_eq_true] at h ⊢
    exact ⟨rewriteExp_firstOrder b h.1, rewriteAlts_firstOrder rest h.2⟩

theorem rewriteOpt_firstOrder {plan : Plan} {isFn : GlobalId → Bool} :
    ∀ {rmask : Option (List Bool)} {d : Nat} (o : Option Exp),
      Exp.optFirstOrder isFn o = true → Exp.optFirstOrder isFn (rewriteOpt plan rmask d o) = true
  | _, _, none, _ => rfl
  | rmask, d, some e, h => rewriteExp_firstOrder e h

end

mutual

theorem exp_firstOrder_congr_below {isFn₁ isFn₂ : GlobalId → Bool} {bound : Nat}
    (heq : ∀ g, g < bound → isFn₁ g = isFn₂ g) :
    ∀ (e : Exp), globBelow bound e = true →
      Exp.firstOrder isFn₁ e = Exp.firstOrder isFn₂ e
  | .bind _ b e, h => by
    simp only [globBelow, Bool.and_eq_true] at h
    simp only [Exp.firstOrder, bind_firstOrder_congr_below heq b h.1, exp_firstOrder_congr_below heq e h.2]
  | .join _ _ b e, h => by
    simp only [globBelow, Bool.and_eq_true] at h
    simp only [Exp.firstOrder, exp_firstOrder_congr_below heq b h.1, exp_firstOrder_congr_below heq e h.2]
  | .jump .., _ | .ret _, _ | .trap, _ => rfl
  | .case _ alts d, h => by
    simp only [globBelow, Bool.and_eq_true] at h
    simp only [Exp.firstOrder, alts_firstOrder_congr_below heq alts h.1, opt_firstOrder_congr_below heq d h.2]
  | .tick e, h => exp_firstOrder_congr_below heq e h

theorem bind_firstOrder_congr_below {isFn₁ isFn₂ : GlobalId → Bool} {bound : Nat}
    (heq : ∀ g, g < bound → isFn₁ g = isFn₂ g) :
    ∀ (b : Bind), globBelowBind bound b = true →
      Bind.firstOrder isFn₁ b = Bind.firstOrder isFn₂ b
  | .glob g, h => by
    simp only [globBelowBind, decide_eq_true_eq] at h
    simp [Bind.firstOrder, heq g h]
  | .atom _, _ | .con .., _ | .proj .., _ | .prim .., _ | .call .., _ | .app .., _ | .fn .., _ => rfl

theorem alts_firstOrder_congr_below {isFn₁ isFn₂ : GlobalId → Bool} {bound : Nat}
    (heq : ∀ g, g < bound → isFn₁ g = isFn₂ g) :
    ∀ (alts : List Alt), globBelowAlts bound alts = true →
      Exp.altsFirstOrder isFn₁ alts = Exp.altsFirstOrder isFn₂ alts
  | [], _ => rfl
  | .mk _ _ b :: rest, h => by
    simp only [globBelowAlts, Bool.and_eq_true] at h
    simp only [Exp.altsFirstOrder, exp_firstOrder_congr_below heq b h.1, alts_firstOrder_congr_below heq rest h.2]

theorem opt_firstOrder_congr_below {isFn₁ isFn₂ : GlobalId → Bool} {bound : Nat}
    (heq : ∀ g, g < bound → isFn₁ g = isFn₂ g) :
    ∀ (o : Option Exp), globBelowOpt bound o = true →
      Exp.optFirstOrder isFn₁ o = Exp.optFirstOrder isFn₂ o
  | none, _ => rfl
  | some e, h => exp_firstOrder_congr_below heq e h

end

theorem globalList_keys_nodup (P : Program) : (P.globalList.map (·.1)).Nodup := by
  have hsub : List.Sublist (P.globalList.map (·.1)) (List.range P.size) := by
    unfold Program.globalList
    generalize List.range P.size = rs
    induction rs with
    | nil => simp
    | cons r rs ih =>
      simp only [List.filterMap_cons]
      cases P.global? r with
      | none => exact ih.trans (List.sublist_cons_self r rs)
      | some gd => simpa using List.Sublist.cons_cons r ih
  exact hsub.nodup List.nodup_range

theorem mem_globalList_iff {P : Program} {g : GlobalId} {gd : GDef} :
    (g, gd) ∈ P.globalList ↔ g < P.size ∧ P.global? g = some gd := by
  unfold Program.globalList
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]
  constructor
  · rintro ⟨g', hg', gd', hgd', hpair⟩
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨hg', hgd'⟩
  · rintro ⟨hlt, hgd⟩
    exact ⟨g, hlt, gd, hgd, rfl⟩

/-- Key lookup lemma for the assembled global map of `DeadParam.run`. -/
theorem run_spec {P : Program} (hw : P.WF) :
    run P = P ∨
    (let es := buildPlan P P.size P.globalList
     let plan : Plan := Src.NatMap.ofList (es.map fun (g, w, _, keep) => (g, (w, keep)))
     (run P).WF ∧
     (∀ g gd, P.global? g = some gd →
       match plan.get? g with
       | some (w, keep) =>
         (run P).global? g = some { gd with body := wrapperBody w gd.ps.length keep } ∧
         keep.length = gd.ps.length ∧
         keep.any id = true ∧
         DeadFree keep.reverse 0 gd.body ∧
         (run P).global? w = some { key := .worker gd.key keep
                                    ps := filterMask keep gd.ps
                                    result := gd.result
                                    body := rewriteExp plan (some keep.reverse) 0 gd.body }
       | none =>
         (run P).global? g = some { gd with body := rewriteExp plan none 0 gd.body }) ∧
     (∀ g, g < P.size → (run P).arity? g = P.arity? g) ∧
     (∀ w gd', P.size ≤ w → (run P).global? w = some gd' →
       ∃ g gd keep, P.global? g = some gd ∧ plan.get? g = some (w, keep) ∧
         gd' = { key := .worker gd.key keep
                 ps := filterMask keep gd.ps
                 result := gd.result
                 body := rewriteExp plan (some keep.reverse) 0 gd.body }) ∧
     (∀ x ∈ P.globalList, globBelow P.size x.2.body = true)) := by
  let es := buildPlan P P.size P.globalList
  let plan : Plan := Src.NatMap.ofList (es.map fun (g, w, _, keep) => (g, (w, keep)))
  have hglAll : ∀ x ∈ P.globalList, x.1 < P.size ∧ P.global? x.1 = some x.2 :=
    fun x hx => mem_globalList_iff.1 hx
  obtain ⟨hes, hesNodup, hesW⟩ := buildPlan_wf P P.size P.globalList hglAll (globalList_keys_nodup P)
  have hplanNodup : ((es.map fun (g, w, _, keep) => (g, (w, keep))).map (·.1)).Nodup := by
    rw [List.map_map]
    exact hesNodup
  have hplanMem : ∀ g w keep, plan.get? g = some (w, keep) ↔
      ∃ gd, (g, w, gd, keep) ∈ es := by
    intro g w keep
    constructor
    · intro h
      have hm := Convert.Proof.natMap_ofList_mem hplanNodup h
      obtain ⟨⟨g', w', gd', keep'⟩, he, hp⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      exact ⟨gd', he⟩
    · rintro ⟨gd, he⟩
      exact Src.NatMap.get?_ofList hplanNodup (List.mem_map.2 ⟨(g, w, gd, keep), he, rfl⟩)
  unfold run
  dsimp only
  split
  · exact .inl rfl
  · next hne =>
    right
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hne
    have hgb : ∀ x ∈ P.globalList, globBelow P.size x.2.body = true := by
      have : P.globalList.all (fun (_, gd) => globBelow P.size gd.body) = true := by
        cases h : P.globalList.all (fun (_, gd) => globBelow P.size gd.body) with
        | true => rfl
        | false => exact absurd h hne.2
      exact fun x hx => List.all_eq_true.1 this x hx
    let oldGs := P.globalList.map fun (g, gd) =>
      match plan.get? g with
      | some (w, keep) => (g, { gd with body := wrapperBody w gd.ps.length keep })
      | none => (g, { gd with body := rewriteExp plan none 0 gd.body })
    let workers : List (GlobalId × GDef) := es.map fun (_, w, gd, keep) =>
      (w, { key := .worker gd.key keep
            ps := filterMask keep gd.ps
            result := gd.result
            body := rewriteExp plan (some keep.reverse) 0 gd.body })
    have hOldKeys : oldGs.map (·.1) = P.globalList.map (·.1) := by
      simp only [oldGs, List.map_map]
      apply List.map_congr_left
      intro x _; simp only [Function.comp_apply]; cases plan.get? x.1 <;> rfl
    have hWorkKeys : workers.map (·.1) = (List.range es.length).map (P.size + ·) := by
      rw [List.map_map]
      exact hesW
    have hWorkNodup : (workers.map (·.1)).Nodup := by
      rw [hWorkKeys]
      exact List.Pairwise.map (P.size + ·) (fun _ _ h heq => h (Nat.add_left_cancel heq)) List.nodup_range
    have hDisj : ∀ k ∈ oldGs.map (·.1), k ∉ workers.map (·.1) := by
      intro k hk hm
      rw [hOldKeys] at hk
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
      have hlt := (hglAll x hx).1
      rw [hWorkKeys] at hm
      obtain ⟨i, _, hi⟩ := List.mem_map.1 hm
      exact Nat.not_lt.2 (Nat.le_add_right P.size i) (hi ▸ hlt)
    have hAllNodup : ((oldGs ++ workers).map (·.1)).Nodup := by
      rw [List.map_append]
      exact List.nodup_append.2 ⟨by rw [hOldKeys]; exact globalList_keys_nodup P, hWorkNodup,
        fun a ha b hb hab => by subst hab; exact hDisj a ha hb⟩
    have hGet : ∀ id gd', (Src.NatMap.ofList (oldGs ++ workers)).get? id = some gd' ↔
        (id, gd') ∈ oldGs ∨ (id, gd') ∈ workers := by
      intro id gd'
      constructor
      · intro h
        exact List.mem_append.1 (Convert.Proof.natMap_ofList_mem hAllNodup h)
      · intro h
        exact Src.NatMap.get?_ofList hAllNodup (List.mem_append.2 h)
    have hOldGet : ∀ g gd, P.global? g = some gd →
        (Src.NatMap.ofList (oldGs ++ workers)).get? g = some (match plan.get? g with
          | some (w, keep) => { gd with body := wrapperBody w gd.ps.length keep }
          | none => { gd with body := rewriteExp plan none 0 gd.body }) := by
      intro g gd hPg
      apply (hGet g _).2
      left
      have hmem : (g, gd) ∈ P.globalList := mem_globalList_iff.2 ⟨hw.1 g gd hPg, hPg⟩
      have : (g, match plan.get? g with
          | some (w, keep) => { gd with body := wrapperBody w gd.ps.length keep }
          | none => { gd with body := rewriteExp plan none 0 gd.body }) =
          (fun (p : GlobalId × GDef) => match plan.get? p.1 with
            | some (w, keep) => (p.1, { p.2 with body := wrapperBody w p.2.ps.length keep })
            | none => (p.1, { p.2 with body := rewriteExp plan none 0 p.2.body })) (g, gd) := by
        dsimp only; cases plan.get? g <;> rfl
      rw [this]
      exact List.mem_map.2 ⟨(g, gd), hmem, rfl⟩
    have hWorkGet : ∀ g w gd keep, (g, w, gd, keep) ∈ es →
        (Src.NatMap.ofList (oldGs ++ workers)).get? w = some
          { key := .worker gd.key keep
            ps := filterMask keep gd.ps
            result := gd.result
            body := rewriteExp plan (some keep.reverse) 0 gd.body } := by
      intro g w gd keep he
      apply (hGet w _).2
      right
      exact List.mem_map.2 ⟨(g, w, gd, keep), he, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, hgb⟩
    · intro id gd' h
      rcases (hGet id gd').1 h with ho | hwk
      · obtain ⟨⟨g, gd⟩, hm, hp⟩ := List.mem_map.1 ho
        have hid : g = id := by
          dsimp only at hp
          cases hpl : plan.get? g <;> (rw [hpl] at hp; simp only [Prod.mk.injEq] at hp; exact hp.1)
        subst hid
        exact Nat.lt_of_lt_of_le (hglAll _ hm).1 (Nat.le_add_right _ _)
      · obtain ⟨⟨g, w, gd, keep⟩, he, hp⟩ := List.mem_map.1 hwk
        simp only [Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        exact (hes _ he).2.2.2.2
    · intro id hid
      by_cases hlt : id < P.size
      · obtain ⟨gd, hgd⟩ := hw.2 id hlt
        exact ⟨_, hOldGet id gd hgd⟩
      · change id < P.size + es.length at hid
        have hi : id - P.size < es.length := by omega
        have hmem : id ∈ es.map (·.2.1) := by
          rw [hesW]
          exact List.mem_map.2 ⟨id - P.size, List.mem_range.2 hi, by omega⟩
        obtain ⟨⟨g, w, gd, keep⟩, he, rfl⟩ := List.mem_map.1 hmem
        exact ⟨_, hWorkGet g w gd keep he⟩
    · intro g gd hPg
      have ho := hOldGet g gd hPg
      cases hpl : plan.get? g with
      | none =>
        rw [hpl] at ho
        exact ho
      | some wk =>
        obtain ⟨w, keep⟩ := wk
        rw [hpl] at ho
        obtain ⟨gd', he⟩ := (hplanMem g w keep).1 hpl
        have hgd' := (hes _ he).2.1
        rw [hPg] at hgd'
        have hEq : gd' = gd := (Option.some.inj hgd').symm
        subst hEq
        obtain ⟨_, hkl, hka, hdead⟩ := candidate_spec (hes _ he).2.2.1
        exact ⟨ho, hkl, hka, hdead, hWorkGet g w gd' keep he⟩
    · intro g hg
      obtain ⟨gd, hgd⟩ := hw.2 g hg
      have ho := hOldGet g gd hgd
      show Option.map GDef.arity ((Src.NatMap.ofList (oldGs ++ workers)).get? g) = Option.map GDef.arity (P.global? g)
      rw [hgd, ho]
      cases plan.get? g <;> rfl
    · intro w gd' hge hgw
      rcases (hGet w gd').1 hgw with ho | hwk
      · obtain ⟨⟨g, gd⟩, hm, hp⟩ := List.mem_map.1 ho
        have hid : g = w := by
          dsimp only at hp
          cases hpl : plan.get? g <;> (rw [hpl] at hp; simp only [Prod.mk.injEq] at hp; exact hp.1)
        subst hid
        exact absurd (hglAll _ hm).1 (Nat.not_lt.2 hge)
      · obtain ⟨⟨g, w', gd, keep⟩, he, hp⟩ := List.mem_map.1 hwk
        simp only [Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨g, gd, keep, (hes _ he).2.1, (hplanMem g w' keep).2 ⟨gd, he⟩, rfl⟩

/-- **P5 preserves `WF`**. -/
theorem run_wf {P : Program} (hw : P.WF) : (run P).WF := by
  rcases run_spec hw with h | ⟨hw', -⟩
  · rw [h]; exact hw
  · exact hw'

/-- **P5 preserves `FirstOrder`**. -/
theorem run_firstOrder {P : Program} (hw : P.WF) (hfo : FirstOrder P) : FirstOrder (run P) := by
  rcases run_spec hw with h | ⟨hw', hglob, har, hwork, hgb⟩
  · rw [h]; exact hfo
  · unfold FirstOrder firstOrder at hfo ⊢
    rw [List.all_eq_true] at hfo ⊢
    have hisFn : ∀ g, g < P.size →
        ((run P).arity? g).any (· > 0) = (P.arity? g).any (· > 0) :=
      fun g hg => by rw [har g hg]
    intro ⟨id, gd'⟩ hmem
    obtain ⟨hlt, hgid⟩ := mem_globalList_iff.1 hmem
    by_cases hltP : id < P.size
    · obtain ⟨gd, hgd⟩ := hw.2 id hltP
      have hmemP : (id, gd) ∈ P.globalList := mem_globalList_iff.2 ⟨hltP, hgd⟩
      have hfoG : gd.body.firstOrder (fun g => (P.arity? g).any (· > 0)) = true := hfo (id, gd) hmemP
      have hfoG' : gd.body.firstOrder (fun g => ((run P).arity? g).any (· > 0)) = true := by
        rw [exp_firstOrder_congr_below hisFn gd.body (hgb (id, gd) hmemP)]; exact hfoG
      have hspec := hglob id gd hgd
      cases hpl : (Src.NatMap.ofList ((buildPlan P P.size P.globalList).map fun (g, w, _, keep) => (g, (w, keep)))).get? id with
      | none =>
        rw [hpl] at hspec
        rw [hspec, Option.some.injEq] at hgid
        subst hgid
        exact rewriteExp_firstOrder gd.body hfoG'
      | some wk =>
        obtain ⟨w, keep⟩ := wk
        rw [hpl] at hspec
        rw [hspec.1, Option.some.injEq] at hgid
        subst hgid
        rfl
    · obtain ⟨g, gd, keep, hPg, _, rfl⟩ := hwork id gd' (Nat.le_of_not_lt hltP) hgid
      have hmemP : (g, gd) ∈ P.globalList := mem_globalList_iff.2 ⟨hw.1 g gd hPg, hPg⟩
      have hfoG : gd.body.firstOrder (fun h => (P.arity? h).any (· > 0)) = true := hfo (g, gd) hmemP
      have hfoG' : gd.body.firstOrder (fun h => ((run P).arity? h).any (· > 0)) = true := by
        rw [exp_firstOrder_congr_below hisFn gd.body (hgb (g, gd) hmemP)]; exact hfoG
      exact rewriteExp_firstOrder gd.body hfoG'

/-- **P5 is correct**: `DeadParam.run` preserves `WF` and refines its input. -/
theorem run_refines {P : Program} (hw : P.WF) : (run P).WF ∧ Sem.Refines P (run P) := by
  rcases run_spec hw with h | ⟨hw', hglob, _, _, _⟩
  · rw [h]; exact ⟨hw, Sem.Refines.refl P⟩
  · exact ⟨hw', setting_refines { P, Q := run P, plan := _, known := (run_tables P).1, oldGlob := hglob }
      (run_roots P)⟩

end IxCC.Anf.DeadParam.Proof
