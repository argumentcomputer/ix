import IxC.Resource.Proof.F4Rules
import IxC.Resource.Proof.F4Inputs

/-!
# Checker Unpackers & Simulation Bridges (`F4Check`)

Part 1 (Sections 1–2): Complete relational unpackers for the remaining compound
`Check.lean` `CM` operations (`unknownCall`, `anCtor`, `papVal`, `callResult`,
`applyValue`), reusing `F4Rules.lean`'s `Runs_flowTo`, `CM_valid_ok`, `CM_isUniq_ok`,
`CM_notOnceSrc_ok`, `CM_killSrc_ok`.

Part 2 (Section 3): High-level `Sim`/`VSim`/`ValEnvDisj` bridge theorems connecting
`F4Rules` operational specs and `F4Check` checker unpackers to `F4.lean`'s main
budget induction.
-/

namespace IxC.Resource.Proof

open IxC.Resource

attribute [local instance] Classical.propDecidable

/-! ## 1. Generic `CM` `forIn` / `zipIdx` Helpers -/

theorem CM_forIn_array_eq_list {α β : Type} (arr : Array α) (init : β)
    (f : α → β → CM (ForInStep β)) (s : CSt) :
    (forIn (m := CM) arr init f).run s = (forIn (m := CM) arr.toList init f).run s := by
  rw [← Array.forIn_toList]

/-- Prefix-indexed fold invariant for a `List` `forIn` loop in `CM` that only yields. -/
theorem CM_forIn_list_prefix {α β : Type}
    {f : α → β → CM (ForInStep β)}
    (Inv : List α → β → CSt → Prop)
    (hstep : ∀ done x acc s acc' s',
      Inv done acc s →
      (f x acc).run s = .ok (.yield acc', s') →
      Inv (done ++ [x]) acc' s')
    (hnoDone : ∀ done x acc s acc' s',
      Inv done acc s →
      (f x acc).run s = .ok (.done acc', s') →
      False) :
    ∀ (xs done : List α) (acc acc' : β) (s s' : CSt),
      Inv done acc s →
      (forIn (m := CM) xs acc f).run s = .ok (acc', s') →
      Inv (done ++ xs) acc' s' := by
  intro xs
  induction xs with
  | nil =>
    intro done acc acc' s s' hinv h
    simp only [List.forIn_nil] at h
    rw [CM_pure_run] at h; cases h
    simpa using hinv
  | cons x rest ih =>
    intro done acc acc' s s' hinv h
    simp only [List.forIn_cons] at h
    rw [CM_bind_run] at h
    cases hfx : (f x acc).run s with
    | error e => rw [hfx] at h; cases h
    | ok p =>
      rcases p with ⟨step, s1⟩
      rw [hfx] at h; dsimp only at h
      cases step with
      | done a1 => exact False.elim (hnoDone done x acc s a1 s1 hinv hfx)
      | yield a1 =>
        have hinv1 := hstep done x acc s a1 s1 hinv hfx
        have hres := ih (done ++ [x]) a1 acc' s1 s' hinv1 h
        simpa [List.append_assoc] using hres

/-- Variant of `CM_forIn_list_prefix` tracking `Pairwise R` ordering across `(done ++ xs)`. -/
theorem CM_forIn_list_prefix_pairwise {α β : Type} {R : α → α → Prop}
    {f : α → β → CM (ForInStep β)}
    (Inv : List α → β → CSt → Prop)
    (hstep : ∀ done x acc s acc' s',
      Inv done acc s →
      (∀ y ∈ done, R y x) →
      (f x acc).run s = .ok (.yield acc', s') →
      Inv (done ++ [x]) acc' s')
    (hnoDone : ∀ done x acc s acc' s',
      Inv done acc s →
      (∀ y ∈ done, R y x) →
      (f x acc).run s = .ok (.done acc', s') →
      False) :
    ∀ (xs done : List α) (acc acc' : β) (s s' : CSt),
      List.Pairwise R (done ++ xs) →
      Inv done acc s →
      (forIn (m := CM) xs acc f).run s = .ok (acc', s') →
      Inv (done ++ xs) acc' s' := by
  intro xs
  induction xs with
  | nil =>
    intro done acc acc' s s' _ hinv h
    simp only [List.forIn_nil] at h
    rw [CM_pure_run] at h; cases h
    simpa using hinv
  | cons x rest ih =>
    intro done acc acc' s s' hpw hinv h
    have hR : ∀ y ∈ done, R y x := by
      have h1 := List.pairwise_append.mp hpw
      exact fun y hy => h1.2.2 y hy x (List.mem_cons_self ..)
    simp only [List.forIn_cons] at h
    rw [CM_bind_run] at h
    cases hfx : (f x acc).run s with
    | error e => rw [hfx] at h; cases h
    | ok p =>
      rcases p with ⟨step, s1⟩
      rw [hfx] at h; dsimp only at h
      cases step with
      | done a1 => exact False.elim (hnoDone done x acc s a1 s1 hinv hR hfx)
      | yield a1 =>
        have hinv1 := hstep done x acc s a1 s1 hinv hR hfx
        have hpw1 : List.Pairwise R ((done ++ [x]) ++ rest) := by
          simpa [List.append_assoc] using hpw
        have hres := ih (done ++ [x]) a1 acc' s1 s' hpw1 hinv1 h
        simpa [List.append_assoc] using hres

theorem list_zipIdx_pairwise_lt {α : Type} :
    ∀ (xs : List α) (n : Nat),
      List.Pairwise (fun a b : α × Nat => a.2 < b.2) (xs.zipIdx n)
  | [], _ => .nil
  | _ :: rest, n => by
    simp only [List.zipIdx_cons]
    refine List.Pairwise.cons ?_ (list_zipIdx_pairwise_lt rest (n + 1))
    intro b hb
    have hge := (List.mem_zipIdx hb).1
    omega

theorem mem_array_zipIdx_iff {α : Type} {arr : Array α} {p : α} {i : Nat} :
    (p, i) ∈ arr.toList.zipIdx ↔ arr[i]? = some p := by
  rw [List.mem_zipIdx_iff_getElem?]
  simp

theorem list_pairwise_filter_map_lt {α : Type} {xs : List (α × Nat)} {P : α × Nat → Bool}
    (hpw : List.Pairwise (fun a b : α × Nat => a.2 < b.2) xs) :
    List.Pairwise (· < ·) ((xs.filter P).map (·.2)) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    cases hpw with
    | cons hhead htail =>
      simp only [List.filter_cons]
      cases hP : P x with
      | false => exact ih htail
      | true =>
        refine List.Pairwise.cons ?_ (ih htail)
        intro y hy
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
        exact hhead b (List.mem_filter.mp hb).1

/-- `Check.flowTo` never modifies `CSt.steps`. -/
theorem CM_flowTo_steps {d : Dest} {exp : Skel} {v : AVal} {w : String} {s s' : CSt}
    (h : (flowTo d exp v w).run s = .ok ((), s')) :
    s'.steps = s.steps := by
  unfold flowTo at h
  rw [CM_bind_run] at h
  cases hval : (valid v w).run s with
  | error e => rw [hval] at h; cases h
  | ok p1 =>
    rcases p1 with ⟨⟨⟩, s1⟩
    obtain ⟨hs1Eq, _⟩ := CM_valid_ok hval
    rw [hval, hs1Eq] at h; dsimp only at h
    have h1 : ((do
          match d with
          | .once => do
              for x in v.deps do
                if (← isOnceBnd x) && (← isSpent x) then
                  refuseM s!"onceReentry: a once binding passed on after it was called or passed on: {w}"
          | _ => do
              if v.onceOnly then refuseM s!"onceReentry: a once-only closure where it may be called again: {w}"
              notOnceSrc v w
          for x in v.deps do
            if ← isOnceBnd x then markSpent x
          match d with
          | .lend => pure ()
          | .share => do
              if v.onceOnly then refuseM s!"onceReentry: a once-only closure where it may be called again: {w}"
              if v.cls == .val then
                for x in v.deps do
                  if (← stOf x) == BSt.live then setSt x BSt.shared
          | .once => do
              if v.cls == .val then
                for x in v.deps do
                  if (← stOf x) == BSt.live then setSt x BSt.shared
          | .uniq b => do
              if v.onceOnly then refuseM s!"onceReentry: a once-only closure given away: {w}"
              if v.cls == .val then
                unless ← isUniq v do refuseM s!"revokedUse: a value that may be shared, at a unique position: {w}"
                if !b && !v.regs.isEmpty then refuseM s!"borrowEscape: a borrowed value given away: {w}"
                for x in v.deps do setSt x BSt.dead
          killSrc v) : CM Unit).run s = .ok ((), s') := by
      cases d with
      | once =>
        dsimp only at h
        cases ha : exp.admitsNA v.skel with
        | true => simp only [ha, ↓reduceIte] at h; exact h
        | false => simp only [ha, Bool.false_eq_true, ↓reduceIte] at h; rw [CM_bind_run, CM_refuseM_run] at h; cases h
      | lend | share | uniq _ =>
        dsimp only at h
        cases hoo : v.onceOnly with
        | true =>
          simp only [hoo, ↓reduceIte] at h
          cases ha : exp.admitsNA v.skel with
          | true => simp only [ha, ↓reduceIte] at h; exact h
          | false => simp only [ha, Bool.false_eq_true, ↓reduceIte] at h; rw [CM_bind_run, CM_refuseM_run] at h; cases h
        | false =>
          simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h
          cases ha : exp.admits v.skel with
          | true => simp only [ha, ↓reduceIte] at h; exact h
          | false => simp only [ha, Bool.false_eq_true, ↓reduceIte] at h; rw [CM_bind_run, CM_refuseM_run] at h; cases h
    have h2 : ((do
          for x in v.deps do
            if ← isOnceBnd x then markSpent x
          match d with
          | .lend => pure ()
          | .share => do
              if v.onceOnly then refuseM s!"onceReentry: a once-only closure where it may be called again: {w}"
              if v.cls == .val then
                for x in v.deps do
                  if (← stOf x) == BSt.live then setSt x BSt.shared
          | .once => do
              if v.cls == .val then
                for x in v.deps do
                  if (← stOf x) == BSt.live then setSt x BSt.shared
          | .uniq b => do
              if v.onceOnly then refuseM s!"onceReentry: a once-only closure given away: {w}"
              if v.cls == .val then
                unless ← isUniq v do refuseM s!"revokedUse: a value that may be shared, at a unique position: {w}"
                if !b && !v.regs.isEmpty then refuseM s!"borrowEscape: a borrowed value given away: {w}"
                for x in v.deps do setSt x BSt.dead
          killSrc v) : CM Unit).run s = .ok ((), s') := by
      cases d with
      | once =>
        dsimp only at h1; rw [CM_bind_run] at h1
        cases hl : StateT.run (forIn (m := CM) v.deps PUnit.unit _) s with
        | error e => rw [hl] at h1; cases h1
        | ok p =>
          rcases p with ⟨⟨⟩, s2⟩
          obtain ⟨hs2Eq, _⟩ := CM_forIn_checkOnceUnspent hl
          rw [hl, hs2Eq] at h1; exact h1
      | lend | share | uniq _ =>
        dsimp only at h1
        cases hoo : v.onceOnly with
        | true => simp only [hoo, ↓reduceIte] at h1; rw [CM_bind_run, CM_refuseM_run] at h1; cases h1
        | false =>
          simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h1; rw [CM_bind_run] at h1
          cases hno : (notOnceSrc v w).run s with
          | error e => rw [hno] at h1; cases h1
          | ok p =>
            rcases p with ⟨⟨⟩, s2⟩
            obtain ⟨hs2Eq, _⟩ := CM_notOnceSrc_ok hno
            rw [hno, hs2Eq] at h1; exact h1
    rw [CM_bind_run] at h2
    cases hms : StateT.run (forIn (m := CM) v.deps PUnit.unit fun x _ => do
        if ← isOnceBnd x then markSpent x
        pure (ForInStep.yield PUnit.unit)) s with
    | error e => rw [hms] at h2; cases h2
    | ok p3 =>
      rcases p3 with ⟨⟨⟩, s3⟩
      rw [hms] at h2; dsimp only at h2
      obtain ⟨_, _, _, _, hsteps3, _, _⟩ := CM_forIn_markSpentOnce hms
      cases d with
      | lend =>
        dsimp only at h2
        obtain ⟨_, _, _, _, hsteps4, _, _⟩ := CM_killSrc_ok h2
        exact hsteps4.trans hsteps3
      | share =>
        dsimp only at h2
        cases hoo : v.onceOnly with
        | true => simp only [hoo, ↓reduceIte] at h2; rw [CM_bind_run, CM_refuseM_run] at h2; cases h2
        | false =>
          simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h2
          cases hcv : (v.cls == .val) with
          | false =>
            simp only [hcv, Bool.false_eq_true, ↓reduceIte] at h2
            exact (CM_killSrc_ok h2).2.2.2.2.1.trans hsteps3
          | true =>
            simp only [hcv, ↓reduceIte] at h2; rw [CM_bind_run] at h2
            cases hl : StateT.run (forIn (m := CM) v.deps PUnit.unit _) s3 with
            | error e => rw [hl] at h2; cases h2
            | ok p4 =>
              rcases p4 with ⟨⟨⟩, s4⟩
              rw [hl] at h2; dsimp only at h2
              exact (CM_killSrc_ok h2).2.2.2.2.1.trans ((CM_forIn_shareDeps hl).2.2.2.2.1.trans hsteps3)
      | once =>
        dsimp only at h2
        cases hcv : (v.cls == .val) with
        | false =>
          simp only [hcv, Bool.false_eq_true, ↓reduceIte] at h2
          exact (CM_killSrc_ok h2).2.2.2.2.1.trans hsteps3
        | true =>
          simp only [hcv, ↓reduceIte] at h2; rw [CM_bind_run] at h2
          cases hl : StateT.run (forIn (m := CM) v.deps PUnit.unit _) s3 with
          | error e => rw [hl] at h2; cases h2
          | ok p4 =>
            rcases p4 with ⟨⟨⟩, s4⟩
            rw [hl] at h2; dsimp only at h2
            exact (CM_killSrc_ok h2).2.2.2.2.1.trans ((CM_forIn_shareDeps hl).2.2.2.2.1.trans hsteps3)
      | uniq b =>
        dsimp only at h2
        cases hoo : v.onceOnly with
        | true => simp only [hoo, ↓reduceIte] at h2; rw [CM_bind_run, CM_refuseM_run] at h2; cases h2
        | false =>
          simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h2
          cases hcv : (v.cls == .val) with
          | false =>
            simp only [hcv, Bool.false_eq_true, ↓reduceIte] at h2
            exact (CM_killSrc_ok h2).2.2.2.2.1.trans hsteps3
          | true =>
            simp only [hcv, ↓reduceIte] at h2; rw [CM_bind_run] at h2
            cases hiu : (isUniq v).run s3 with
            | error e => rw [hiu] at h2; cases h2
            | ok pu =>
              rcases pu with ⟨uRes, su⟩
              obtain ⟨hsuEq, _⟩ := CM_isUniq_ok hiu
              rw [hiu, hsuEq] at h2; dsimp only at h2
              cases uRes with
              | false => simp only [Bool.false_eq_true, ↓reduceIte] at h2; rw [CM_bind_run, CM_refuseM_run] at h2; cases h2
              | true =>
                simp only [↓reduceIte] at h2
                cases hbr : (!b && !v.regs.isEmpty) with
                | true => simp only [hbr, ↓reduceIte] at h2; rw [CM_bind_run, CM_refuseM_run] at h2; cases h2
                | false =>
                  simp only [hbr, Bool.false_eq_true, ↓reduceIte] at h2; rw [CM_bind_run] at h2
                  cases hl : StateT.run (forIn (m := CM) v.deps PUnit.unit _) s3 with
                  | error e => rw [hl] at h2; cases h2
                  | ok p4 =>
                    rcases p4 with ⟨⟨⟩, s4⟩
                    rw [hl] at h2; dsimp only at h2
                    exact (CM_killSrc_ok h2).2.2.2.2.1.trans ((CM_forIn_killDeps hl).2.2.2.2.1.trans hsteps3)

/-- Lift a raw `(flowTo d exp v w).run s = .ok ((), s')` with `s.steps = 0` into `Runs_flowTo`. -/
theorem CM_flowTo_runs {d : Dest} {exp : Skel} {v : AVal} {w : String} {s s' : CSt}
    (hsteps : s.steps = 0)
    (h : (flowTo d exp v w).run s = .ok ((), s')) :
    s'.steps = 0 ∧ Runs (flowTo d exp v w) (AState.ofCSt s) () (AState.ofCSt s') := by
  have hs' : s'.steps = 0 := (CM_flowTo_steps h).trans hsteps
  refine ⟨hs', ?_⟩
  unfold Runs
  rw [show (AState.ofCSt s).toCSt 0 = s by rw [← hsteps, AState.toCSt_ofCSt],
      show (AState.ofCSt s').toCSt 0 = s' by rw [← hs', AState.toCSt_ofCSt]]
  exact h

/-! ## 2. Unpacking `unknownCall`, `anCtor`, `papVal`, `callResult`, `applyValue` -/

/-- Complete unpacking of `Check.unknownCall`. -/
theorem Runs_unknownCall {avs : Array (Option AVal)} {c : Cls} {σ σ' : AState} {res : AVal}
    (hok : AStateOk σ) (h : Runs (unknownCall avs c) σ res σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧
    σ'.st.size = σ.st.size ∧ σ'.once = σ.once ∧ σ'.spent.size = σ.spent.size ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion ∧
    res.cls = c ∧ res.own = .shared ∧ res.skel = .unknown ∧
    res.onceOnly = false ∧ res.src = none ∧
    (∀ a, some a ∈ avs.toList →
      ValidDeps σ a.deps ∧ Skel.unknown.admits a.skel = true ∧
      a.onceOnly = false ∧ ¬ IsOnceSrc σ a ∧
      (c = .val → (∀ d ∈ a.deps, d ∈ res.deps) ∧ (∀ r ∈ a.regs, r ∈ res.regs))) ∧
    (∀ d ∈ res.deps, c = .val ∧ ∃ a, some a ∈ avs.toList ∧ d ∈ a.deps) ∧
    (∀ r ∈ res.regs, c = .val ∧ ∃ a, some a ∈ avs.toList ∧ r ∈ a.regs) ∧
    (∀ i, i < σ.spent.size →
      σ'.spent[i]? = if (∃ a, some a ∈ avs.toList ∧ i ∈ a.deps) ∧ σ.once[i]? = some true
        then some true else σ.spent[i]?) ∧
    (∀ i, i < σ.st.size →
      σ'.st[i]? = if (∃ a, some a ∈ avs.toList ∧ a.cls = .val ∧ i ∈ a.deps) ∧ σ.st[i]? = some .live
        then some .shared else σ.st[i]?) := by
  unfold Runs unknownCall at h
  rw [CM_bind_run, CM_forIn_array_eq_list] at h
  cases hl : StateT.run (forIn (m := CM) avs.toList ([], []) _) (σ.toCSt 0) with
  | error e => rw [hl] at h; cases h
  | ok p =>
    rcases p with ⟨⟨deps, regs⟩, s1⟩
    rw [hl] at h; dsimp only at h
    rw [CM_pure_run] at h; cases h
    let Inv : List (Option AVal) → List Nat × List Nat → CSt → Prop := fun done acc s =>
      let ds := acc.1; let rs := acc.2
      s.steps = 0 ∧
      AStateOk (AState.ofCSt s) ∧ AStateLe σ (AState.ofCSt s) ∧
      s.st.size = σ.st.size ∧ s.once = σ.once ∧ s.spent.size = σ.spent.size ∧
      s.regions = σ.regions ∧ s.nextRegion = σ.nextRegion ∧
      (∀ a, some a ∈ done →
        ValidDeps σ a.deps ∧ Skel.unknown.admits a.skel = true ∧
        a.onceOnly = false ∧ ¬ IsOnceSrc σ a) ∧
      (∀ d, d ∈ ds ↔ ∃ a, some a ∈ done ∧ d ∈ a.deps) ∧
      (∀ r, r ∈ rs ↔ ∃ a, some a ∈ done ∧ r ∈ a.regs) ∧
      (∀ i, i < σ.spent.size →
        s.spent[i]? = if (∃ a, some a ∈ done ∧ i ∈ a.deps) ∧ σ.once[i]? = some true
          then some true else σ.spent[i]?) ∧
      (∀ i, i < σ.st.size →
        s.st[i]? = if (∃ a, some a ∈ done ∧ a.cls = .val ∧ i ∈ a.deps) ∧ σ.st[i]? = some .live
          then some .shared else σ.st[i]?)
    have hinv0 : Inv [] ([], []) (σ.toCSt 0) :=
      ⟨rfl, by rw [AState.ofCSt_toCSt]; exact hok, by rw [AState.ofCSt_toCSt]; exact AStateLe.refl σ,
        rfl, rfl, rfl, rfl, rfl, fun _ h => (by cases h),
        by simp, by simp, fun i _ => by simp [AState.toCSt], fun i _ => by simp [AState.toCSt]⟩
    have hinv := CM_forIn_list_prefix Inv
      (fun done opt acc s acc' s' hI hfx => by
        obtain ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, hdone, hds, hrs, hspS, hstS⟩ := hI
        cases opt with
        | none =>
          dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
          refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr,
            fun a ha => hdone a (by simpa using ha),
            fun d => by simpa using hds d, fun r => by simpa using hrs r,
            fun i hi => by simpa using hspS i hi, fun i hi => by simpa using hstS i hi⟩
        | some a =>
          dsimp only at hfx; rw [CM_bind_run] at hfx
          cases hfl : (flowTo .share .unknown a "an argument of an unknown function").run s with
          | error e => rw [hfl] at hfx; cases hfx
          | ok pf =>
            rcases pf with ⟨⟨⟩, sf⟩
            rw [hfl] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
            obtain ⟨hstepsF, hflR⟩ := CM_flowTo_runs hsteps hfl
            obtain ⟨hokF, hleF, hszStF, honceF, hszSpF, hregF, hnrF, hvdF, _, hnonOnce, hspF, _, hstShF, _, _⟩ :=
              Runs_flowTo hokS hflR
            dsimp only [AState.ofCSt] at hszStF honceF hszSpF hregF hnrF hspF hstShF
            have ⟨hadm, hoo, hnotOnceS⟩ := hnonOnce (fun hc => by cases hc)
            have hvd0 : ValidDeps σ a.deps := by
              intro d hd
              have ⟨hltS, hneD⟩ := hvdF d hd
              have hlt0 : d < σ.st.size := by rw [← hszSt]; exact hltS
              refine ⟨hlt0, fun hdead => hneD ?_⟩
              have h1 := hstS d hlt0
              rw [hdead] at h1; simp only [Option.some.injEq, reduceCtorEq, and_false, ↓reduceIte] at h1
              exact h1
            have hnotOnce0 : ¬ IsOnceSrc σ a := by
              rintro ⟨id, hsrc, ho⟩
              exact hnotOnceS ⟨id, hsrc, by dsimp [AState.ofCSt]; rw [honce]; exact ho⟩
            refine ⟨hstepsF, hokF, hleS.trans hleF, hszStF.trans hszSt, honceF.trans honce,
              hszSpF.trans hszSp, hregF.trans hreg, hnrF.trans hnr, ?_, ?_, ?_, ?_, ?_⟩
            · intro a' ha'
              rcases List.mem_append.mp ha' with h1 | h2
              · exact hdone a' h1
              · simp at h2; subst h2; exact ⟨hvd0, hadm, hoo, hnotOnce0⟩
            · intro d
              rw [mem_natUnion, hds d]
              constructor
              · rintro (⟨a', ha', hd⟩ | hd)
                · exact ⟨a', List.mem_append_left _ ha', hd⟩
                · exact ⟨a, List.mem_append_right _ (by simp), hd⟩
              · rintro ⟨a', ha', hd⟩
                rcases List.mem_append.mp ha' with h1 | h2
                · exact Or.inl ⟨a', h1, hd⟩
                · simp at h2; subst h2; exact Or.inr hd
            · intro r
              rw [mem_natUnion, hrs r]
              constructor
              · rintro (⟨a', ha', hr⟩ | hr)
                · exact ⟨a', List.mem_append_left _ ha', hr⟩
                · exact ⟨a, List.mem_append_right _ (by simp), hr⟩
              · rintro ⟨a', ha', hr⟩
                rcases List.mem_append.mp ha' with h1 | h2
                · exact Or.inl ⟨a', h1, hr⟩
                · simp at h2; subst h2; exact Or.inr hr
            · intro i hi
              rw [hspF i (by rw [hszSp]; exact hi)]
              simp only [honce]
              rw [hspS i hi]
              by_cases hcNew : i ∈ a.deps ∧ σ.once[i]? = some true
              · have hcAll : (∃ a', some a' ∈ done ++ [some a] ∧ i ∈ a'.deps) ∧ σ.once[i]? = some true :=
                  ⟨⟨a, List.mem_append_right _ (by simp), hcNew.1⟩, hcNew.2⟩
                simp only [hcNew, hcAll, and_self, ↓reduceIte]
              · simp only [hcNew, ↓reduceIte]
                by_cases hcOld : (∃ a', some a' ∈ done ∧ i ∈ a'.deps) ∧ σ.once[i]? = some true
                · have hcAll : (∃ a', some a' ∈ done ++ [some a] ∧ i ∈ a'.deps) ∧ σ.once[i]? = some true :=
                    ⟨let ⟨a', ha', hd⟩ := hcOld.1; ⟨a', List.mem_append_left _ ha', hd⟩, hcOld.2⟩
                  simp only [hcOld, hcAll, and_self, ↓reduceIte]
                · have hnotAll : ¬ ((∃ a', some a' ∈ done ++ [some a] ∧ i ∈ a'.deps) ∧ σ.once[i]? = some true) := by
                    rintro ⟨⟨a', ha', hd⟩, ho⟩
                    rcases List.mem_append.mp ha' with h1 | h2
                    · exact hcOld ⟨⟨a', h1, hd⟩, ho⟩
                    · simp at h2; subst h2; exact hcNew ⟨hd, ho⟩
                  simp only [hcOld, hnotAll, ↓reduceIte]
            · intro i hi
              rw [hstShF rfl i (by rw [hszSt]; exact hi)]
              simp only [hstS i hi]
              by_cases hcOld : (∃ a', some a' ∈ done ∧ a'.cls = .val ∧ i ∈ a'.deps) ∧ σ.st[i]? = some .live
              · have hcAll : (∃ a', some a' ∈ done ++ [some a] ∧ a'.cls = .val ∧ i ∈ a'.deps) ∧ σ.st[i]? = some .live :=
                  ⟨let ⟨a', ha', hc', hd⟩ := hcOld.1; ⟨a', List.mem_append_left _ ha', hc', hd⟩, hcOld.2⟩
                simp only [hcOld, hcAll, and_self, ↓reduceIte, Option.some.injEq, reduceCtorEq, and_false]
              · simp only [hcOld, ↓reduceIte]
                by_cases hcNew : a.cls = .val ∧ i ∈ a.deps ∧ σ.st[i]? = some .live
                · have hcAll : (∃ a', some a' ∈ done ++ [some a] ∧ a'.cls = .val ∧ i ∈ a'.deps) ∧ σ.st[i]? = some .live :=
                    ⟨⟨a, List.mem_append_right _ (by simp), hcNew.1, hcNew.2.1⟩, hcNew.2.2⟩
                  simp only [hcNew, hcAll, and_self, ↓reduceIte]
                · have hnotAll : ¬ ((∃ a', some a' ∈ done ++ [some a] ∧ a'.cls = .val ∧ i ∈ a'.deps) ∧ σ.st[i]? = some .live) := by
                    rintro ⟨⟨a', ha', hc', hd⟩, hlv⟩
                    rcases List.mem_append.mp ha' with h1 | h2
                    · exact hcOld ⟨⟨a', h1, hc', hd⟩, hlv⟩
                    · simp at h2; subst h2; exact hcNew ⟨hc', hd, hlv⟩
                  simp only [hcNew, hnotAll, ↓reduceIte])
      (fun _ opt _ _ _ _ _ hfx => by
        cases opt with
        | none => dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
        | some a =>
          dsimp only at hfx; rw [CM_bind_run] at hfx
          cases hfl : (flowTo .share .unknown a "an argument of an unknown function").run _ with
          | error e => rw [hfl] at hfx; cases hfx
          | ok pf => rw [hfl] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx)
      avs.toList [] ([], []) (deps, regs) (σ.toCSt 0) (σ'.toCSt 0) hinv0 hl
    simp only [List.nil_append] at hinv
    obtain ⟨_, hok', hle', hszSt, honce, hszSp, hreg, hnr, hdone, hds, hrs, hsp', hst'⟩ := hinv
    dsimp only [AState.ofCSt, AState.toCSt] at hok' hle' hszSt honce hszSp hreg hnr hsp' hst'
    refine ⟨by simpa [AState.ofCSt_toCSt] using hok', by simpa [AState.ofCSt_toCSt] using hle',
      hszSt, honce, hszSp, hreg, hnr, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, hsp', hst'⟩
    · intro a ha
      obtain ⟨h1, h2, h3, h4⟩ := hdone a ha
      refine ⟨h1, h2, h3, h4, fun hc => ?_⟩
      subst hc
      have hvv : (Cls.val == Cls.val) = true := rfl
      exact ⟨fun d hd => by simp only [hvv, ↓reduceIte]; exact (hds d).mpr ⟨a, ha, hd⟩,
        fun r hr => by simp only [hvv, ↓reduceIte]; exact (hrs r).mpr ⟨a, ha, hr⟩⟩
    · intro d hd
      cases c with
      | val =>
        have hvv : (Cls.val == Cls.val) = true := rfl
        simp only [hvv, ↓reduceIte] at hd
        exact ⟨rfl, (hds d).mp hd⟩
      | irr => have hf : (Cls.irr == Cls.val) = false := rfl; simp only [hf, Bool.false_eq_true, ↓reduceIte] at hd; cases hd
      | imm => have hf : (Cls.imm == Cls.val) = false := rfl; simp only [hf, Bool.false_eq_true, ↓reduceIte] at hd; cases hd
      | leaf => have hf : (Cls.leaf == Cls.val) = false := rfl; simp only [hf, Bool.false_eq_true, ↓reduceIte] at hd; cases hd
    · intro r hr
      cases c with
      | val =>
        have hvv : (Cls.val == Cls.val) = true := rfl
        simp only [hvv, ↓reduceIte] at hr
        exact ⟨rfl, (hrs r).mp hr⟩
      | irr => have hf : (Cls.irr == Cls.val) = false := rfl; simp only [hf, Bool.false_eq_true, ↓reduceIte] at hr; cases hr
      | imm => have hf : (Cls.imm == Cls.val) = false := rfl; simp only [hf, Bool.false_eq_true, ↓reduceIte] at hr; cases hr
      | leaf => have hf : (Cls.leaf == Cls.val) = false := rfl; simp only [hf, Bool.false_eq_true, ↓reduceIte] at hr; cases hr

/-- Complete unpacking of `Check.anCtor` (both partial `< nP + fields.size` and saturated). -/
theorem Runs_anCtor {nP : Nat} {fields : Array Field} {avs : Array (Option AVal)} {c : Cls}
    {σ σ' : AState} {res : AVal}
    (hok : AStateOk σ) (h : Runs (anCtor nP fields avs c) σ res σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧
    σ'.st.size = σ.st.size ∧ σ'.once = σ.once ∧ σ'.spent.size = σ.spent.size ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion ∧
    (avs.size < nP + fields.size →
      res.cls = .val ∧ res.own = .shared ∧ res.skel = .unknown ∧
      res.onceOnly = false ∧ res.src = none ∧
      (∀ a, some a ∈ avs.toList →
        ValidDeps σ a.deps ∧ Skel.unknown.admits a.skel = true ∧
        a.onceOnly = false ∧ ¬ IsOnceSrc σ a ∧
        (∀ d ∈ a.deps, d ∈ res.deps) ∧ (∀ r ∈ a.regs, r ∈ res.regs)) ∧
      (∀ d ∈ res.deps, ∃ a, some a ∈ avs.toList ∧ d ∈ a.deps) ∧
      (∀ r ∈ res.regs, ∃ a, some a ∈ avs.toList ∧ r ∈ a.regs) ∧
      (∀ i, i < σ.spent.size →
        σ'.spent[i]? = if (∃ a, some a ∈ avs.toList ∧ i ∈ a.deps) ∧ σ.once[i]? = some true
          then some true else σ.spent[i]?) ∧
      (∀ i, i < σ.st.size →
        σ'.st[i]? = if (∃ a, some a ∈ avs.toList ∧ a.cls = .val ∧ i ∈ a.deps) ∧ σ.st[i]? = some .live
          then some .shared else σ.st[i]?)) ∧
    (nP + fields.size ≤ avs.size →
      let kept := (fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)
      (kept.isEmpty = true → σ' = σ ∧ res = { cls := .imm }) ∧
      (kept.isEmpty = false → ((c == .imm || c == .leaf) && kept.size == 1) = true →
        σ' = σ ∧
        match avs[nP + kept[0]!]? with
        | some (some v) => ValidDeps σ v.deps ∧ res = { v with cls := c, src := none }
        | _ => res = { cls := c }) ∧
      (kept.isEmpty = false → ((c == .imm || c == .leaf) && kept.size == 1) = false →
        res.cls = .val ∧ res.skel = .unknown ∧ res.onceOnly = false ∧ res.src = none ∧
        (∀ k ∈ kept.toList, ∀ v f, avs[nP + k]? = some (some v) → fields[k]? = some f →
          ValidDeps σ v.deps ∧ v.onceOnly = false ∧ Skel.unknown.admits v.skel = true ∧
          (∀ r ∈ v.regs, r ∈ res.regs) ∧
          (f.fmode = .shared → (∀ r ∈ v.regs, r = 1) ∧ ¬ IsOnceSrc σ v) ∧
          (f.fmode = .inherited → v.cls = .val → ¬ IsOnceSrc σ v ∧ (∀ d ∈ v.deps, d ∈ res.deps))) ∧
        (res.own = .uniq →
          (∀ k ∈ kept.toList, ∀ v f, avs[nP + k]? = some (some v) → fields[k]? = some f →
            f.fmode = .inherited → v.cls = .val →
              v.own = .uniq ∧ (∀ d ∈ v.deps, σ.st[d]? = some .live)) ∧
          (∀ k₁ ∈ kept.toList, ∀ k₂ ∈ kept.toList, k₁ ≠ k₂ →
            ∀ v₁ f₁ v₂ f₂, avs[nP + k₁]? = some (some v₁) → fields[k₁]? = some f₁ →
            avs[nP + k₂]? = some (some v₂) → fields[k₂]? = some f₂ →
            f₁.fmode = .inherited → v₁.cls = .val → f₂.fmode = .inherited → v₂.cls = .val →
            ∀ d ∈ v₁.deps, d ∉ v₂.deps)) ∧
        (∀ d ∈ res.deps, ∃ k ∈ kept.toList, ∃ v f,
          avs[nP + k]? = some (some v) ∧ fields[k]? = some f ∧ f.fmode = .inherited ∧ v.cls = .val ∧ d ∈ v.deps) ∧
        (∀ r ∈ res.regs, ∃ k ∈ kept.toList, ∃ v f,
          avs[nP + k]? = some (some v) ∧ fields[k]? = some f ∧ r ∈ v.regs) ∧
        (∀ i, i < σ.spent.size →
          σ'.spent[i]? = if (∃ k ∈ kept.toList, ∃ v f,
              avs[nP + k]? = some (some v) ∧ fields[k]? = some f ∧ f.fmode = .shared ∧ i ∈ v.deps) ∧
              σ.once[i]? = some true
            then some true else σ.spent[i]?) ∧
        (∀ i, i < σ.st.size →
          σ'.st[i]? = if (∃ k ∈ kept.toList, ∃ v f,
              avs[nP + k]? = some (some v) ∧ fields[k]? = some f ∧ f.fmode = .shared ∧
              v.cls = .val ∧ i ∈ v.deps) ∧ σ.st[i]? = some .live
            then some .shared else σ.st[i]?))) := by
  unfold Runs anCtor at h
  by_cases hlt : avs.size < nP + fields.size
  · simp only [hlt, ↓reduceIte] at h
    rw [CM_bind_run, CM_forIn_array_eq_list] at h
    cases hl : StateT.run (forIn (m := CM) avs.toList ([], []) _) (σ.toCSt 0) with
    | error e => rw [hl] at h; cases h
    | ok p =>
      rcases p with ⟨⟨deps, regs⟩, s1⟩
      rw [hl] at h; dsimp only at h; rw [CM_pure_run] at h; cases h
      let Inv : List (Option AVal) → List Nat × List Nat → CSt → Prop := fun done acc s =>
        s.steps = 0 ∧
        AStateOk (AState.ofCSt s) ∧ AStateLe σ (AState.ofCSt s) ∧
        s.st.size = σ.st.size ∧ s.once = σ.once ∧ s.spent.size = σ.spent.size ∧
        s.regions = σ.regions ∧ s.nextRegion = σ.nextRegion ∧
        (∀ a, some a ∈ done →
          ValidDeps σ a.deps ∧ Skel.unknown.admits a.skel = true ∧
          a.onceOnly = false ∧ ¬ IsOnceSrc σ a) ∧
        (∀ d, d ∈ acc.1 ↔ ∃ a, some a ∈ done ∧ d ∈ a.deps) ∧
        (∀ r, r ∈ acc.2 ↔ ∃ a, some a ∈ done ∧ r ∈ a.regs) ∧
        (∀ i, i < σ.spent.size →
          s.spent[i]? = if (∃ a, some a ∈ done ∧ i ∈ a.deps) ∧ σ.once[i]? = some true
            then some true else σ.spent[i]?) ∧
        (∀ i, i < σ.st.size →
          s.st[i]? = if (∃ a, some a ∈ done ∧ a.cls = .val ∧ i ∈ a.deps) ∧ σ.st[i]? = some .live
            then some .shared else σ.st[i]?)
      have hinv0 : Inv [] ([], []) (σ.toCSt 0) :=
        ⟨rfl, by rw [AState.ofCSt_toCSt]; exact hok, by rw [AState.ofCSt_toCSt]; exact AStateLe.refl σ,
          rfl, rfl, rfl, rfl, rfl,
          fun _ h => (by cases h), by simp, by simp, fun _ _ => by simp [AState.toCSt], fun _ _ => by simp [AState.toCSt]⟩
      have hinv := CM_forIn_list_prefix Inv
        (fun done opt acc s acc' s' hI hfx => by
          obtain ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, hdone, hds, hrs, hspS, hstS⟩ := hI
          cases opt with
          | none =>
            dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
            refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr,
              fun a ha => hdone a (by simpa using ha),
              fun d => by simpa using hds d, fun r => by simpa using hrs r,
              fun i hi => by simpa using hspS i hi, fun i hi => by simpa using hstS i hi⟩
          | some a =>
            dsimp only at hfx; rw [CM_bind_run] at hfx
            cases hfl : (flowTo .share .unknown a "a constructor's partial application").run s with
            | error e => rw [hfl] at hfx; cases hfx
            | ok pf =>
              rcases pf with ⟨⟨⟩, sf⟩
              rw [hfl] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
              obtain ⟨hstepsF, hflR⟩ := CM_flowTo_runs hsteps hfl
              obtain ⟨hokF, hleF, hszStF, honceF, hszSpF, hregF, hnrF, hvdF, _, hnonOnce, hspF, _, hstShF, _, _⟩ :=
                Runs_flowTo hokS hflR
              dsimp only [AState.ofCSt] at hszStF honceF hszSpF hregF hnrF hspF hstShF
              have ⟨hadm, hoo, hnotOnceS⟩ := hnonOnce (fun hc => by cases hc)
              have hvd0 : ValidDeps σ a.deps := by
                intro d hd
                have ⟨hltS, hneD⟩ := hvdF d hd
                have hlt0 : d < σ.st.size := by rw [← hszSt]; exact hltS
                refine ⟨hlt0, fun hdead => hneD ?_⟩
                have h1 := hstS d hlt0
                rw [hdead] at h1; simp only [Option.some.injEq, reduceCtorEq, and_false, ↓reduceIte] at h1
                exact h1
              have hnotOnce0 : ¬ IsOnceSrc σ a := fun ⟨id, hs, ho⟩ =>
                hnotOnceS ⟨id, hs, by dsimp [AState.ofCSt]; rw [honce]; exact ho⟩
              refine ⟨hstepsF, hokF, hleS.trans hleF, hszStF.trans hszSt, honceF.trans honce,
                hszSpF.trans hszSp, hregF.trans hreg, hnrF.trans hnr, ?_, ?_, ?_, ?_, ?_⟩
              · intro a' ha'
                rcases List.mem_append.mp ha' with h1 | h2
                · exact hdone a' h1
                · simp at h2; subst h2; exact ⟨hvd0, hadm, hoo, hnotOnce0⟩
              · intro d; rw [mem_natUnion, hds d]
                constructor
                · rintro (⟨a', ha', hd⟩ | hd)
                  · exact ⟨a', List.mem_append_left _ ha', hd⟩
                  · exact ⟨a, List.mem_append_right _ (by simp), hd⟩
                · rintro ⟨a', ha', hd⟩
                  rcases List.mem_append.mp ha' with h1 | h2
                  · exact Or.inl ⟨a', h1, hd⟩
                  · simp at h2; subst h2; exact Or.inr hd
              · intro r; rw [mem_natUnion, hrs r]
                constructor
                · rintro (⟨a', ha', hr⟩ | hr)
                  · exact ⟨a', List.mem_append_left _ ha', hr⟩
                  · exact ⟨a, List.mem_append_right _ (by simp), hr⟩
                · rintro ⟨a', ha', hr⟩
                  rcases List.mem_append.mp ha' with h1 | h2
                  · exact Or.inl ⟨a', h1, hr⟩
                  · simp at h2; subst h2; exact Or.inr hr
              · intro i hi
                rw [hspF i (by rw [hszSp]; exact hi)]
                simp only [honce]
                rw [hspS i hi]
                by_cases hcNew : i ∈ a.deps ∧ σ.once[i]? = some true
                · have hcAll : (∃ a', some a' ∈ done ++ [some a] ∧ i ∈ a'.deps) ∧ σ.once[i]? = some true :=
                    ⟨⟨a, List.mem_append_right _ (by simp), hcNew.1⟩, hcNew.2⟩
                  simp only [hcNew, hcAll, and_self, ↓reduceIte]
                · simp only [hcNew, ↓reduceIte]
                  by_cases hcOld : (∃ a', some a' ∈ done ∧ i ∈ a'.deps) ∧ σ.once[i]? = some true
                  · have hcAll : (∃ a', some a' ∈ done ++ [some a] ∧ i ∈ a'.deps) ∧ σ.once[i]? = some true :=
                      ⟨let ⟨a', ha', hd⟩ := hcOld.1; ⟨a', List.mem_append_left _ ha', hd⟩, hcOld.2⟩
                    simp only [hcOld, hcAll, and_self, ↓reduceIte]
                  · have hnotAll : ¬ ((∃ a', some a' ∈ done ++ [some a] ∧ i ∈ a'.deps) ∧ σ.once[i]? = some true) := by
                      rintro ⟨⟨a', ha', hd⟩, ho⟩
                      rcases List.mem_append.mp ha' with h1 | h2
                      · exact hcOld ⟨⟨a', h1, hd⟩, ho⟩
                      · simp at h2; subst h2; exact hcNew ⟨hd, ho⟩
                    simp only [hcOld, hnotAll, ↓reduceIte]
              · intro i hi
                rw [hstShF rfl i (by rw [hszSt]; exact hi)]
                simp only [hstS i hi]
                by_cases hcOld : (∃ a', some a' ∈ done ∧ a'.cls = .val ∧ i ∈ a'.deps) ∧ σ.st[i]? = some .live
                · have hcAll : (∃ a', some a' ∈ done ++ [some a] ∧ a'.cls = .val ∧ i ∈ a'.deps) ∧ σ.st[i]? = some .live :=
                    ⟨let ⟨a', ha', hc', hd⟩ := hcOld.1; ⟨a', List.mem_append_left _ ha', hc', hd⟩, hcOld.2⟩
                  simp only [hcOld, hcAll, and_self, ↓reduceIte, Option.some.injEq, reduceCtorEq, and_false]
                · simp only [hcOld, ↓reduceIte]
                  by_cases hcNew : a.cls = .val ∧ i ∈ a.deps ∧ σ.st[i]? = some .live
                  · have hcAll : (∃ a', some a' ∈ done ++ [some a] ∧ a'.cls = .val ∧ i ∈ a'.deps) ∧ σ.st[i]? = some .live :=
                      ⟨⟨a, List.mem_append_right _ (by simp), hcNew.1, hcNew.2.1⟩, hcNew.2.2⟩
                    simp only [hcNew, hcAll, and_self, ↓reduceIte]
                  · have hnotAll : ¬ ((∃ a', some a' ∈ done ++ [some a] ∧ a'.cls = .val ∧ i ∈ a'.deps) ∧ σ.st[i]? = some .live) := by
                      rintro ⟨⟨a', ha', hc', hd⟩, hlv⟩
                      rcases List.mem_append.mp ha' with h1 | h2
                      · exact hcOld ⟨⟨a', h1, hc', hd⟩, hlv⟩
                      · simp at h2; subst h2; exact hcNew ⟨hc', hd, hlv⟩
                    simp only [hcNew, hnotAll, ↓reduceIte])
        (fun _ opt _ _ _ _ _ hfx => by
          cases opt with
          | none => dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
          | some a =>
            dsimp only at hfx; rw [CM_bind_run] at hfx
            cases hfl : (flowTo .share .unknown a "a constructor's partial application").run _ with
            | error e => rw [hfl] at hfx; cases hfx
            | ok pf => rw [hfl] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx)
        avs.toList [] ([], []) (deps, regs) (σ.toCSt 0) (σ'.toCSt 0) hinv0 hl
      simp only [List.nil_append] at hinv
      obtain ⟨_, hok', hle', hszSt, honce, hszSp, hreg, hnr, hdone, hds, hrs, hsp', hst'⟩ := hinv
      dsimp only [AState.ofCSt, AState.toCSt] at hok' hle' hszSt honce hszSp hreg hnr hsp' hst'
      refine ⟨by simpa [AState.ofCSt_toCSt] using hok', by simpa [AState.ofCSt_toCSt] using hle',
        hszSt, honce, hszSp, hreg, hnr, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun d hd => (hds d).mp hd,
          fun r hr => (hrs r).mp hr, hsp', hst'⟩, fun hge => absurd hlt (Nat.not_lt.mpr hge)⟩
      intro a ha
      obtain ⟨h1, h2, h3, h4⟩ := hdone a ha
      exact ⟨h1, h2, h3, h4, fun d hd => (hds d).mpr ⟨a, ha, hd⟩, fun r hr => (hrs r).mpr ⟨a, ha, hr⟩⟩
  · simp only [hlt, ↓reduceIte] at h
    let kept := (fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)
    cases hke : kept.isEmpty with
    | true =>
      have hke' : ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).isEmpty = true := hke
      simp only [hke', ↓reduceIte] at h
      rw [CM_pure_run] at h
      obtain ⟨hres, hst⟩ := Prod.mk.inj (Except.ok.inj h)
      have hσ : σ' = σ := (AState.toCSt_inj hst).symm
      exact ⟨hσ ▸ hok, hσ ▸ AStateLe.refl σ, by rw [hσ], by rw [hσ], by rw [hσ], by rw [hσ], by rw [hσ],
        fun hl => absurd hl hlt,
        fun _ => ⟨fun _ => ⟨hσ, hres.symm⟩, fun hf => (by rw [hke] at hf; cases hf), fun hf => (by rw [hke] at hf; cases hf)⟩⟩
    | false =>
      have hke' : ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).isEmpty = false := hke
      simp only [hke', Bool.false_eq_true, ↓reduceIte] at h
      cases hwr : ((c == .imm || c == .leaf) && kept.size == 1) with
      | true =>
        have hwr' : ((c == .imm || c == .leaf) && ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).size == 1) = true := hwr
        simp only [hwr', ↓reduceIte] at h
        cases hav : avs[nP + kept[0]!]? with
        | none =>
          have hav' : avs[nP + ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2))[0]!]? = none := hav
          simp only [hav'] at h; rw [CM_pure_run] at h
          obtain ⟨hres, hst⟩ := Prod.mk.inj (Except.ok.inj h)
          have hσ : σ' = σ := (AState.toCSt_inj hst).symm
          exact ⟨hσ ▸ hok, hσ ▸ AStateLe.refl σ, by rw [hσ], by rw [hσ], by rw [hσ], by rw [hσ], by rw [hσ],
            fun hl => absurd hl hlt,
            fun _ => ⟨fun ht => (by rw [hke] at ht; cases ht), fun _ _ => ⟨hσ, by rw [hav]; exact hres.symm⟩, fun _ hf => (by rw [hwr] at hf; cases hf)⟩⟩
        | some optv =>
          cases optv with
          | none =>
            have hav' : avs[nP + ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2))[0]!]? = some none := hav
            simp only [hav'] at h; rw [CM_pure_run] at h
            obtain ⟨hres, hst⟩ := Prod.mk.inj (Except.ok.inj h)
            have hσ : σ' = σ := (AState.toCSt_inj hst).symm
            exact ⟨hσ ▸ hok, hσ ▸ AStateLe.refl σ, by rw [hσ], by rw [hσ], by rw [hσ], by rw [hσ], by rw [hσ],
              fun hl => absurd hl hlt,
              fun _ => ⟨fun ht => (by rw [hke] at ht; cases ht), fun _ _ => ⟨hσ, by rw [hav]; exact hres.symm⟩, fun _ hf => (by rw [hwr] at hf; cases hf)⟩⟩
          | some v =>
            have hav' : avs[nP + ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2))[0]!]? = some (some v) := hav
            simp only [hav'] at h; rw [CM_bind_run] at h
            cases hval : (valid v "a wrapper's field").run (σ.toCSt 0) with
            | error e => rw [hval] at h; cases h
            | ok pv =>
              rcases pv with ⟨⟨⟩, sv⟩
              obtain ⟨rfl, hvd⟩ := CM_valid_ok hval
              dsimp only [AState.toCSt] at hvd
              rw [hval] at h; dsimp only at h; rw [CM_pure_run] at h
              obtain ⟨hres, hst⟩ := Prod.mk.inj (Except.ok.inj h)
              have hσ : σ' = σ := (AState.toCSt_inj hst).symm
              exact ⟨hσ ▸ hok, hσ ▸ AStateLe.refl σ, by rw [hσ], by rw [hσ], by rw [hσ], by rw [hσ], by rw [hσ],
                fun hl => absurd hl hlt,
                fun _ => ⟨fun ht => (by rw [hke] at ht; cases ht), fun _ _ => ⟨hσ, by rw [hav]; exact ⟨hvd, hres.symm⟩⟩,
                  fun _ hf => (by rw [hwr] at hf; cases hf)⟩⟩
      | false =>
        have hwr' : ((c == .imm || c == .leaf) && ((fields.zipIdx.filter fun (f, _) => f.kept).map (·.2)).size == 1) = false := hwr
        simp only [hwr', Bool.false_eq_true, ↓reduceIte] at h
        rw [CM_bind_run, CM_forIn_array_eq_list] at h
        cases hl : StateT.run (forIn (m := CM) kept.toList (Own.uniq, [], []) _) (σ.toCSt 0) with
        | error e => rw [hl] at h; cases h
        | ok p =>
          rcases p with ⟨⟨own, deps, regs⟩, s1⟩
          rw [hl] at h; dsimp only at h; rw [CM_pure_run] at h; cases h
          have hpwKept : List.Pairwise (· < ·) kept.toList := by
            have h1 : kept.toList = ((fields.toList.zipIdx.filter fun (f, _) => f.kept).map (·.2)) := by
              simp [kept, Array.toList_zipIdx]
            rw [h1]
            exact list_pairwise_filter_map_lt (list_zipIdx_pairwise_lt fields.toList 0)
          let Inv : List Nat → Own × List Nat × List Nat → CSt → Prop := fun done acc s =>
            let o := acc.1; let ds := acc.2.1; let rs := acc.2.2
            s.steps = 0 ∧
            AStateOk (AState.ofCSt s) ∧ AStateLe σ (AState.ofCSt s) ∧
            s.st.size = σ.st.size ∧ s.once = σ.once ∧ s.spent.size = σ.spent.size ∧
            s.regions = σ.regions ∧ s.nextRegion = σ.nextRegion ∧
            (∀ k ∈ done, ∀ v f, avs[nP + k]? = some (some v) → fields[k]? = some f →
              ValidDeps σ v.deps ∧ v.onceOnly = false ∧ Skel.unknown.admits v.skel = true ∧
              (f.fmode = .shared → (∀ r ∈ v.regs, r = 1) ∧ ¬ IsOnceSrc σ v) ∧
              (f.fmode = .inherited → v.cls = .val → ¬ IsOnceSrc σ v)) ∧
            (o = .uniq →
              (∀ k ∈ done, ∀ v f, avs[nP + k]? = some (some v) → fields[k]? = some f →
                f.fmode = .inherited → v.cls = .val →
                  v.own = .uniq ∧ (∀ d ∈ v.deps, σ.st[d]? = some .live)) ∧
              (∀ k₁ ∈ done, ∀ k₂ ∈ done, k₁ ≠ k₂ →
                ∀ v₁ f₁ v₂ f₂, avs[nP + k₁]? = some (some v₁) → fields[k₁]? = some f₁ →
                avs[nP + k₂]? = some (some v₂) → fields[k₂]? = some f₂ →
                f₁.fmode = .inherited → v₁.cls = .val → f₂.fmode = .inherited → v₂.cls = .val →
                ∀ d ∈ v₁.deps, d ∉ v₂.deps)) ∧
            (∀ d, d ∈ ds ↔ ∃ k ∈ done, ∃ v f,
              avs[nP + k]? = some (some v) ∧ fields[k]? = some f ∧ f.fmode = .inherited ∧ v.cls = .val ∧ d ∈ v.deps) ∧
            (∀ r, r ∈ rs ↔ ∃ k ∈ done, ∃ v f,
              avs[nP + k]? = some (some v) ∧ fields[k]? = some f ∧ r ∈ v.regs) ∧
            (∀ i, i < σ.spent.size →
              s.spent[i]? = if (∃ k ∈ done, ∃ v f,
                  avs[nP + k]? = some (some v) ∧ fields[k]? = some f ∧ f.fmode = .shared ∧ i ∈ v.deps) ∧
                  σ.once[i]? = some true
                then some true else σ.spent[i]?) ∧
            (∀ i, i < σ.st.size →
              s.st[i]? = if (∃ k ∈ done, ∃ v f,
                  avs[nP + k]? = some (some v) ∧ fields[k]? = some f ∧ f.fmode = .shared ∧
                  v.cls = .val ∧ i ∈ v.deps) ∧ σ.st[i]? = some .live
                then some .shared else σ.st[i]?)
          have hinv0 : Inv [] (.uniq, [], []) (σ.toCSt 0) :=
            ⟨rfl, by rw [AState.ofCSt_toCSt]; exact hok, by rw [AState.ofCSt_toCSt]; exact AStateLe.refl σ,
              rfl, rfl, rfl, rfl, rfl,
              fun _ hk => (by cases hk), fun _ => ⟨fun _ hk => (by cases hk), fun _ hk => (by cases hk)⟩,
              by simp, by simp, fun _ _ => by simp [AState.toCSt], fun _ _ => by simp [AState.toCSt]⟩
          have hinv := CM_forIn_list_prefix_pairwise (R := (· < ·)) Inv
            (fun done k acc s acc' s' hI hltDone hfx => by
              rcases acc with ⟨o, ds, rs⟩
              obtain ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, hdone, huniqD, hds, hrs, hspS, hstS⟩ := hI
              dsimp only at hfx
              cases havk : avs[nP + k]? with
              | none =>
                simp only [havk] at hfx; rw [CM_pure_run] at hfx; cases hfx
                refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · intro k' hk' v f hav' hf'
                  rcases List.mem_append.mp hk' with h1 | h2
                  · exact hdone k' h1 v f hav' hf'
                  · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                · intro ho; obtain ⟨hu1, hu2⟩ := huniqD ho
                  refine ⟨fun k' hk' v f hav' hf' => ?_, fun k₁ hk₁ k₂ hk₂ hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂ => ?_⟩
                  · rcases List.mem_append.mp hk' with h1 | h2
                    · exact hu1 k' h1 v f hav' hf'
                    · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                  · rcases List.mem_append.mp hk₁ with h1 | h1
                    · rcases List.mem_append.mp hk₂ with h2 | h2
                      · exact hu2 k₁ h1 k₂ h2 hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂
                      · simp at h2; subst h2; rw [havk] at hav₂; cases hav₂
                    · simp at h1; subst h1; rw [havk] at hav₁; cases hav₁
                · intro d; rw [hds d]
                  constructor
                  · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                  · rintro ⟨k', hk', v, f, hav', rest⟩
                    rcases List.mem_append.mp hk' with h1 | h2
                    · exact ⟨k', h1, v, f, hav', rest⟩
                    · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                · intro r; rw [hrs r]
                  constructor
                  · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                  · rintro ⟨k', hk', v, f, hav', rest⟩
                    rcases List.mem_append.mp hk' with h1 | h2
                    · exact ⟨k', h1, v, f, hav', rest⟩
                    · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                · intro i hi; rw [hspS i hi]
                  have heq : (∃ k' ∈ done, ∃ v f, avs[nP + k']? = some (some v) ∧ fields[k']? = some f ∧ f.fmode = .shared ∧ i ∈ v.deps) ↔
                      (∃ k' ∈ done ++ [k], ∃ v f, avs[nP + k']? = some (some v) ∧ fields[k']? = some f ∧ f.fmode = .shared ∧ i ∈ v.deps) := by
                    constructor
                    · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                    · rintro ⟨k', hk', v, f, hav', rest⟩
                      rcases List.mem_append.mp hk' with h1 | h2
                      · exact ⟨k', h1, v, f, hav', rest⟩
                      · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                  simp only [heq]
                · intro i hi; rw [hstS i hi]
                  have heq : (∃ k' ∈ done, ∃ v f, avs[nP + k']? = some (some v) ∧ fields[k']? = some f ∧ f.fmode = .shared ∧ v.cls = .val ∧ i ∈ v.deps) ↔
                      (∃ k' ∈ done ++ [k], ∃ v f, avs[nP + k']? = some (some v) ∧ fields[k']? = some f ∧ f.fmode = .shared ∧ v.cls = .val ∧ i ∈ v.deps) := by
                    constructor
                    · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                    · rintro ⟨k', hk', v, f, hav', rest⟩
                      rcases List.mem_append.mp hk' with h1 | h2
                      · exact ⟨k', h1, v, f, hav', rest⟩
                      · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                  simp only [heq]
              | some optv =>
                cases optv with
                | none =>
                  simp only [havk] at hfx; rw [CM_pure_run] at hfx; cases hfx
                  refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · intro k' hk' v f hav' hf'
                    rcases List.mem_append.mp hk' with h1 | h2
                    · exact hdone k' h1 v f hav' hf'
                    · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                  · intro ho; obtain ⟨hu1, hu2⟩ := huniqD ho
                    refine ⟨fun k' hk' v f hav' hf' => ?_, fun k₁ hk₁ k₂ hk₂ hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂ => ?_⟩
                    · rcases List.mem_append.mp hk' with h1 | h2
                      · exact hu1 k' h1 v f hav' hf'
                      · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                    · rcases List.mem_append.mp hk₁ with h1 | h1
                      · rcases List.mem_append.mp hk₂ with h2 | h2
                        · exact hu2 k₁ h1 k₂ h2 hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂
                        · simp at h2; subst h2; rw [havk] at hav₂; cases hav₂
                      · simp at h1; subst h1; rw [havk] at hav₁; cases hav₁
                  · intro d; rw [hds d]
                    constructor
                    · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                    · rintro ⟨k', hk', v, f, hav', rest⟩
                      rcases List.mem_append.mp hk' with h1 | h2
                      · exact ⟨k', h1, v, f, hav', rest⟩
                      · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                  · intro r; rw [hrs r]
                    constructor
                    · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                    · rintro ⟨k', hk', v, f, hav', rest⟩
                      rcases List.mem_append.mp hk' with h1 | h2
                      · exact ⟨k', h1, v, f, hav', rest⟩
                      · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                  · intro i hi; rw [hspS i hi]
                    have heq : (∃ k' ∈ done, ∃ v f, avs[nP + k']? = some (some v) ∧ fields[k']? = some f ∧ f.fmode = .shared ∧ i ∈ v.deps) ↔
                        (∃ k' ∈ done ++ [k], ∃ v f, avs[nP + k']? = some (some v) ∧ fields[k']? = some f ∧ f.fmode = .shared ∧ i ∈ v.deps) := by
                      constructor
                      · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                      · rintro ⟨k', hk', v, f, hav', rest⟩
                        rcases List.mem_append.mp hk' with h1 | h2
                        · exact ⟨k', h1, v, f, hav', rest⟩
                        · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                    simp only [heq]
                  · intro i hi; rw [hstS i hi]
                    have heq : (∃ k' ∈ done, ∃ v f, avs[nP + k']? = some (some v) ∧ fields[k']? = some f ∧ f.fmode = .shared ∧ v.cls = .val ∧ i ∈ v.deps) ↔
                        (∃ k' ∈ done ++ [k], ∃ v f, avs[nP + k']? = some (some v) ∧ fields[k']? = some f ∧ f.fmode = .shared ∧ v.cls = .val ∧ i ∈ v.deps) := by
                      constructor
                      · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                      · rintro ⟨k', hk', v, f, hav', rest⟩
                        rcases List.mem_append.mp hk' with h1 | h2
                        · exact ⟨k', h1, v, f, hav', rest⟩
                        · simp at h2; subst h2; rw [havk] at hav'; cases hav'
                    simp only [heq]
                | some v =>
                  cases hfk : fields[k]? with
                  | none =>
                    simp only [havk, hfk] at hfx; rw [CM_pure_run] at hfx; cases hfx
                    refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · intro k' hk' v' f' hav' hf'
                      rcases List.mem_append.mp hk' with h1 | h2
                      · exact hdone k' h1 v' f' hav' hf'
                      · simp at h2; subst h2; rw [hfk] at hf'; cases hf'
                    · intro ho; obtain ⟨hu1, hu2⟩ := huniqD ho
                      refine ⟨fun k' hk' v' f' hav' hf' => ?_, fun k₁ hk₁ k₂ hk₂ hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂ => ?_⟩
                      · rcases List.mem_append.mp hk' with h1 | h2
                        · exact hu1 k' h1 v' f' hav' hf'
                        · simp at h2; subst h2; rw [hfk] at hf'; cases hf'
                      · rcases List.mem_append.mp hk₁ with h1 | h1
                        · rcases List.mem_append.mp hk₂ with h2 | h2
                          · exact hu2 k₁ h1 k₂ h2 hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂
                          · simp at h2; subst h2; rw [hfk] at hf₂; cases hf₂
                        · simp at h1; subst h1; rw [hfk] at hf₁; cases hf₁
                    · intro d; rw [hds d]
                      constructor
                      · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                      · rintro ⟨k', hk', v', f', hav', hf', rest⟩
                        rcases List.mem_append.mp hk' with h1 | h2
                        · exact ⟨k', h1, v', f', hav', hf', rest⟩
                        · simp at h2; subst h2; rw [hfk] at hf'; cases hf'
                    · intro r; rw [hrs r]
                      constructor
                      · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                      · rintro ⟨k', hk', v', f', hav', hf', rest⟩
                        rcases List.mem_append.mp hk' with h1 | h2
                        · exact ⟨k', h1, v', f', hav', hf', rest⟩
                        · simp at h2; subst h2; rw [hfk] at hf'; cases hf'
                    · intro i hi; rw [hspS i hi]
                      have heq : (∃ k' ∈ done, ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ i ∈ v'.deps) ↔
                          (∃ k' ∈ done ++ [k], ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ i ∈ v'.deps) := by
                        constructor
                        · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                        · rintro ⟨k', hk', v', f', hav', hf', rest⟩
                          rcases List.mem_append.mp hk' with h1 | h2
                          · exact ⟨k', h1, v', f', hav', hf', rest⟩
                          · simp at h2; subst h2; rw [hfk] at hf'; cases hf'
                      simp only [heq]
                    · intro i hi; rw [hstS i hi]
                      have heq : (∃ k' ∈ done, ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ i ∈ v'.deps) ↔
                          (∃ k' ∈ done ++ [k], ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ i ∈ v'.deps) := by
                        constructor
                        · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                        · rintro ⟨k', hk', v', f', hav', hf', rest⟩
                          rcases List.mem_append.mp hk' with h1 | h2
                          · exact ⟨k', h1, v', f', hav', hf', rest⟩
                          · simp at h2; subst h2; rw [hfk] at hf'; cases hf'
                      simp only [heq]
                  | some f =>
                    simp only [havk, hfk] at hfx
                    rw [CM_bind_run] at hfx
                    cases hval : (valid v "a constructor field").run s with
                    | error e => rw [hval] at hfx; cases hfx
                    | ok pv =>
                      rcases pv with ⟨⟨⟩, sv⟩
                      obtain ⟨hsvEq, hvdS⟩ := CM_valid_ok hval
                      rw [hval, hsvEq] at hfx; dsimp only at hfx
                      have hoo : v.onceOnly = false := by
                        cases ho : v.onceOnly with
                        | false => rfl
                        | true => simp only [ho, ↓reduceIte] at hfx; rw [CM_bind_run, CM_refuseM_run] at hfx; cases hfx
                      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at hfx
                      have hadm : Skel.unknown.admits v.skel = true := by
                        cases ha : Skel.unknown.admits v.skel with
                        | true => rfl
                        | false => simp only [ha, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_bind_run, CM_refuseM_run] at hfx; cases hfx
                      simp only [hadm, ↓reduceIte] at hfx
                      have hvd0 : ValidDeps σ v.deps := by
                        intro d hd
                        have ⟨hltS, hneD⟩ := hvdS d hd
                        have hlt0 : d < σ.st.size := by rw [← hszSt]; exact hltS
                        refine ⟨hlt0, fun hdead => hneD ?_⟩
                        have h1 := hstS d hlt0
                        rw [hdead] at h1; simp only [Option.some.injEq, reduceCtorEq, and_false, ↓reduceIte] at h1
                        exact h1
                      have hrs' : ∀ r, r ∈ natUnion rs v.regs ↔ ∃ k' ∈ done ++ [k], ∃ v' f',
                          avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ r ∈ v'.regs := by
                        intro r; rw [mem_natUnion, hrs r]
                        constructor
                        · rintro (⟨k', hk', rest⟩ | hr)
                          · exact ⟨k', List.mem_append_left _ hk', rest⟩
                          · exact ⟨k, List.mem_append_right _ (by simp), v, f, havk, hfk, hr⟩
                        · rintro ⟨k', hk', v', f', hav', hf', hr⟩
                          rcases List.mem_append.mp hk' with h1 | h2
                          · exact Or.inl ⟨k', h1, v', f', hav', hf', hr⟩
                          · simp at h2; subst h2; rw [havk] at hav'; rw [hfk] at hf'; cases hav'; cases hf'; exact Or.inr hr
                      cases hfm : f.fmode with
                      | shared =>
                        have hshEq : (Ixon.FieldMode.shared == Ixon.FieldMode.shared) = true := rfl
                        simp only [hfm, hshEq, ↓reduceIte] at hfx
                        have hfilt : (v.regs.filter (· != 1)).isEmpty = true := by
                          cases hfe : (v.regs.filter (· != 1)).isEmpty with
                          | true => rfl
                          | false => simp only [hfe, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_bind_run, CM_refuseM_run] at hfx; cases hfx
                        have hregs1 : ∀ r ∈ v.regs, r = 1 := by
                          intro r hr
                          have hnil : v.regs.filter (· != 1) = [] := List.isEmpty_iff.mp hfilt
                          by_cases hr1 : r = 1
                          · exact hr1
                          · have hne : (r != 1) = true := by simp [hr1]
                            have hmem : r ∈ v.regs.filter (· != 1) := List.mem_filter.mpr ⟨hr, hne⟩
                            rw [hnil] at hmem; cases hmem
                        simp only [hfilt, ↓reduceIte] at hfx
                        rw [CM_bind_run] at hfx
                        cases hfl : (flowTo .share v.skel v "a shared field").run s with
                        | error e => rw [hfl] at hfx; cases hfx
                        | ok pf =>
                          rcases pf with ⟨⟨⟩, sf⟩
                          rw [hfl] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
                          obtain ⟨hstepsF, hflR⟩ := CM_flowTo_runs hsteps hfl
                          obtain ⟨hokF, hleF, hszStF, honceF, hszSpF, hregF, hnrF, _, _, hnonOnce, hspF, _, hstShF, _, _⟩ :=
                            Runs_flowTo hokS hflR
                          dsimp only [AState.ofCSt] at hszStF honceF hszSpF hregF hnrF hspF hstShF
                          have hnotOnce0 : ¬ IsOnceSrc σ v := fun ⟨id, hs, ho⟩ =>
                            (hnonOnce (fun hc => by cases hc)).2.2 ⟨id, hs, by dsimp [AState.ofCSt]; rw [honce]; exact ho⟩
                          refine ⟨hstepsF, hokF, hleS.trans hleF, hszStF.trans hszSt, honceF.trans honce,
                            hszSpF.trans hszSp, hregF.trans hreg, hnrF.trans hnr, ?_, ?_, ?_, hrs', ?_, ?_⟩
                          · intro k' hk' v' f' hav' hf'
                            rcases List.mem_append.mp hk' with h1 | h2
                            · exact hdone k' h1 v' f' hav' hf'
                            · simp at h2; subst h2; rw [havk] at hav'; rw [hfk] at hf'; cases hav'; cases hf'
                              exact ⟨hvd0, hoo, hadm, fun _ => ⟨hregs1, hnotOnce0⟩, fun hi => by rw [hfm] at hi; cases hi⟩
                          · intro ho; obtain ⟨hu1, hu2⟩ := huniqD ho
                            refine ⟨fun k' hk' v' f' hav' hf' hfi => ?_, fun k₁ hk₁ k₂ hk₂ hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂ hfi₁ hv₁ hfi₂ hv₂ => ?_⟩
                            · rcases List.mem_append.mp hk' with h1 | h2
                              · exact hu1 k' h1 v' f' hav' hf' hfi
                              · simp at h2; subst h2; rw [hfk] at hf'; cases hf'; rw [hfm] at hfi; cases hfi
                            · rcases List.mem_append.mp hk₁ with h1 | h1
                              · rcases List.mem_append.mp hk₂ with h2 | h2
                                · exact hu2 k₁ h1 k₂ h2 hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂ hfi₁ hv₁ hfi₂ hv₂
                                · simp at h2; subst h2; rw [hfk] at hf₂; cases hf₂; rw [hfm] at hfi₂; cases hfi₂
                              · simp at h1; subst h1; rw [hfk] at hf₁; cases hf₁; rw [hfm] at hfi₁; cases hfi₁
                          · intro d; rw [hds d]
                            constructor
                            · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                            · rintro ⟨k', hk', v', f', hav', hf', hfi, rest⟩
                              rcases List.mem_append.mp hk' with h1 | h2
                              · exact ⟨k', h1, v', f', hav', hf', hfi, rest⟩
                              · simp at h2; subst h2; rw [hfk] at hf'; cases hf'; rw [hfm] at hfi; cases hfi
                          · intro i hi
                            rw [hspF i (by rw [hszSp]; exact hi)]
                            simp only [honce]
                            rw [hspS i hi]
                            by_cases hcNew : i ∈ v.deps ∧ σ.once[i]? = some true
                            · have hcAll : (∃ k' ∈ done ++ [k], ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ i ∈ v'.deps) ∧ σ.once[i]? = some true :=
                                ⟨⟨k, List.mem_append_right _ (by simp), v, f, havk, hfk, hfm, hcNew.1⟩, hcNew.2⟩
                              simp only [hcNew, hcAll, and_self, ↓reduceIte]
                            · simp only [hcNew, ↓reduceIte]
                              by_cases hcOld : (∃ k' ∈ done, ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ i ∈ v'.deps) ∧ σ.once[i]? = some true
                              · have hcAll : (∃ k' ∈ done ++ [k], ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ i ∈ v'.deps) ∧ σ.once[i]? = some true :=
                                  ⟨let ⟨k', hk', rest⟩ := hcOld.1; ⟨k', List.mem_append_left _ hk', rest⟩, hcOld.2⟩
                                simp only [hcOld, hcAll, and_self, ↓reduceIte]
                              · have hnotAll : ¬ ((∃ k' ∈ done ++ [k], ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ i ∈ v'.deps) ∧ σ.once[i]? = some true) := by
                                  rintro ⟨⟨k', hk', v', f', hav', hf', hfm', hd'⟩, ho⟩
                                  rcases List.mem_append.mp hk' with h1 | h2
                                  · exact hcOld ⟨⟨k', h1, v', f', hav', hf', hfm', hd'⟩, ho⟩
                                  · simp at h2; subst h2; rw [havk] at hav'; cases hav'; exact hcNew ⟨hd', ho⟩
                                simp only [hcOld, hnotAll, ↓reduceIte]
                          · intro i hi
                            rw [hstShF rfl i (by rw [hszSt]; exact hi)]
                            simp only [hstS i hi]
                            by_cases hcOld : (∃ k' ∈ done, ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ i ∈ v'.deps) ∧ σ.st[i]? = some .live
                            · have hcAll : (∃ k' ∈ done ++ [k], ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ i ∈ v'.deps) ∧ σ.st[i]? = some .live :=
                                ⟨let ⟨k', hk', rest⟩ := hcOld.1; ⟨k', List.mem_append_left _ hk', rest⟩, hcOld.2⟩
                              simp only [hcOld, hcAll, and_self, ↓reduceIte, Option.some.injEq, reduceCtorEq, and_false]
                            · simp only [hcOld, ↓reduceIte]
                              by_cases hcNew : v.cls = .val ∧ i ∈ v.deps ∧ σ.st[i]? = some .live
                              · have hcAll : (∃ k' ∈ done ++ [k], ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ i ∈ v'.deps) ∧ σ.st[i]? = some .live :=
                                  ⟨⟨k, List.mem_append_right _ (by simp), v, f, havk, hfk, hfm, hcNew.1, hcNew.2.1⟩, hcNew.2.2⟩
                                simp only [hcNew, hcAll, and_self, ↓reduceIte]
                              · have hnotAll : ¬ ((∃ k' ∈ done ++ [k], ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ i ∈ v'.deps) ∧ σ.st[i]? = some .live) := by
                                  rintro ⟨⟨k', hk', v', f', hav', hf', hfm', hc', hd'⟩, hlv⟩
                                  rcases List.mem_append.mp hk' with h1 | h2
                                  · exact hcOld ⟨⟨k', h1, v', f', hav', hf', hfm', hc', hd'⟩, hlv⟩
                                  · simp at h2; subst h2; rw [havk] at hav'; cases hav'; exact hcNew ⟨hc', hd', hlv⟩
                                simp only [hcNew, hnotAll, ↓reduceIte]
                      | inherited =>
                        have hshNe : (Ixon.FieldMode.inherited == Ixon.FieldMode.shared) = false := rfl
                        simp only [hfm, hshNe, Bool.false_eq_true, ↓reduceIte] at hfx
                        have hspEq : ∀ i, i < σ.spent.size →
                            s.spent[i]? = if (∃ k' ∈ done ++ [k], ∃ v' f',
                                avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ i ∈ v'.deps) ∧
                                σ.once[i]? = some true
                              then some true else σ.spent[i]? := by
                          intro i hi; rw [hspS i hi]
                          have heq : (∃ k' ∈ done, ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ i ∈ v'.deps) ↔
                              (∃ k' ∈ done ++ [k], ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ i ∈ v'.deps) := by
                            constructor
                            · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                            · rintro ⟨k', hk', v', f', hav', hf', hsh', hd'⟩
                              rcases List.mem_append.mp hk' with h1 | h2
                              · exact ⟨k', h1, v', f', hav', hf', hsh', hd'⟩
                              · simp at h2; subst h2; rw [hfk] at hf'; cases hf'; rw [hfm] at hsh'; cases hsh'
                          simp only [heq]
                        have hstEq : ∀ i, i < σ.st.size →
                            s.st[i]? = if (∃ k' ∈ done ++ [k], ∃ v' f',
                                avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧
                                v'.cls = .val ∧ i ∈ v'.deps) ∧ σ.st[i]? = some .live
                              then some .shared else σ.st[i]? := by
                          intro i hi; rw [hstS i hi]
                          have heq : (∃ k' ∈ done, ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ i ∈ v'.deps) ↔
                              (∃ k' ∈ done ++ [k], ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ i ∈ v'.deps) := by
                            constructor
                            · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                            · rintro ⟨k', hk', v', f', hav', hf', hsh', hc', hd'⟩
                              rcases List.mem_append.mp hk' with h1 | h2
                              · exact ⟨k', h1, v', f', hav', hf', hsh', hc', hd'⟩
                              · simp at h2; subst h2; rw [hfk] at hf'; cases hf'; rw [hfm] at hsh'; cases hsh'
                          simp only [heq]
                        cases hcv : (v.cls == .val) with
                        | false =>
                          have hneV : v.cls ≠ .val := fun heq => by rw [heq] at hcv; cases hcv
                          simp only [hcv, Bool.false_eq_true, ↓reduceIte] at hfx
                          rw [CM_pure_run] at hfx; cases hfx
                          refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, ?_, ?_, ?_, hrs', hspEq, hstEq⟩
                          · intro k' hk' v' f' hav' hf'
                            rcases List.mem_append.mp hk' with h1 | h2
                            · exact hdone k' h1 v' f' hav' hf'
                            · simp at h2; subst h2; rw [havk] at hav'; rw [hfk] at hf'; cases hav'; cases hf'
                              exact ⟨hvd0, hoo, hadm, (fun hs => by rw [hfm] at hs; cases hs), (fun _ hc => absurd hc hneV)⟩
                          · intro ho; obtain ⟨hu1, hu2⟩ := huniqD ho
                            refine ⟨fun k' hk' v' f' hav' hf' hfi hv' => ?_, fun k₁ hk₁ k₂ hk₂ hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂ hfi₁ hv₁ hfi₂ hv₂ => ?_⟩
                            · rcases List.mem_append.mp hk' with h1 | h2
                              · exact hu1 k' h1 v' f' hav' hf' hfi hv'
                              · simp at h2; subst h2; rw [havk] at hav'; cases hav'; exact absurd hv' hneV
                            · rcases List.mem_append.mp hk₁ with h1 | h1
                              · rcases List.mem_append.mp hk₂ with h2 | h2
                                · exact hu2 k₁ h1 k₂ h2 hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂ hfi₁ hv₁ hfi₂ hv₂
                                · simp at h2; subst h2; rw [havk] at hav₂; cases hav₂; exact absurd hv₂ hneV
                              · simp at h1; subst h1; rw [havk] at hav₁; cases hav₁; exact absurd hv₁ hneV
                          · intro d; rw [hds d]
                            constructor
                            · rintro ⟨k', hk', rest⟩; exact ⟨k', List.mem_append_left _ hk', rest⟩
                            · rintro ⟨k', hk', v', f', hav', hf', hfi, hv', hd'⟩
                              rcases List.mem_append.mp hk' with h1 | h2
                              · exact ⟨k', h1, v', f', hav', hf', hfi, hv', hd'⟩
                              · simp at h2; subst h2; rw [havk] at hav'; cases hav'; exact absurd hv' hneV
                        | true =>
                          have hcvEq : v.cls = .val := by
                            cases hc : v.cls <;> try rfl
                            all_goals (rw [hc] at hcv; cases hcv)
                          simp only [hcv, ↓reduceIte] at hfx
                          rw [CM_bind_run] at hfx
                          cases hno : (notOnceSrc v "a constructor field").run s with
                          | error e => rw [hno] at hfx; cases hfx
                          | ok pno =>
                            rcases pno with ⟨⟨⟩, sno⟩
                            obtain ⟨hsnoEq, hnotOnceS⟩ := CM_notOnceSrc_ok hno
                            have hnotOnce0 : ¬ IsOnceSrc σ v := fun ⟨id, hs, ho⟩ =>
                              hnotOnceS ⟨id, hs, by dsimp [AState.ofCSt]; rw [honce]; exact ho⟩
                            rw [hno, hsnoEq] at hfx; dsimp only at hfx; rw [CM_bind_run] at hfx
                            cases hiu : (isUniq v).run s with
                            | error e => rw [hiu] at hfx; cases hfx
                            | ok piu =>
                              rcases piu with ⟨uRes, siu⟩
                              obtain ⟨hsiuEq, huIff⟩ := CM_isUniq_ok hiu
                              rw [hiu, hsiuEq] at hfx; dsimp only at hfx
                              -- Extract final `(own', natUnion ds v.deps, natUnion rs v.regs)` and `s' = s`
                              have hfin : s' = s ∧ acc'.2.1 = natUnion ds v.deps ∧ acc'.2.2 = natUnion rs v.regs ∧
                                  (acc'.1 = .uniq → o = .uniq ∧ uRes = true ∧ v.deps.any ds.contains = false) := by
                                cases uRes with
                                | false =>
                                  simp only [Bool.false_eq_true, ↓reduceIte] at hfx
                                  cases hany : v.deps.any ds.contains with
                                  | true => simp only [hany, ↓reduceIte] at hfx; rw [CM_pure_run] at hfx; cases hfx; exact ⟨rfl, rfl, rfl, fun hc => by cases hc⟩
                                  | false => simp only [hany, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_pure_run] at hfx; cases hfx; exact ⟨rfl, rfl, rfl, fun hc => by cases hc⟩
                                | true =>
                                  simp only [↓reduceIte] at hfx
                                  cases hany : v.deps.any ds.contains with
                                  | true => simp only [hany, ↓reduceIte] at hfx; rw [CM_pure_run] at hfx; cases hfx; exact ⟨rfl, rfl, rfl, fun hc => by cases hc⟩
                                  | false => simp only [hany, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_pure_run] at hfx; cases hfx; exact ⟨rfl, rfl, rfl, fun ho => ⟨ho, rfl, rfl⟩⟩
                              obtain ⟨rfl, hdsAcc, hrsAcc, hownAcc⟩ := hfin
                              have hds' : ∀ d, d ∈ acc'.2.1 ↔ ∃ k' ∈ done ++ [k], ∃ v' f',
                                  avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .inherited ∧ v'.cls = .val ∧ d ∈ v'.deps := by
                                intro d; rw [hdsAcc, mem_natUnion, hds d]
                                constructor
                                · rintro (⟨k', hk', rest⟩ | hd)
                                  · exact ⟨k', List.mem_append_left _ hk', rest⟩
                                  · exact ⟨k, List.mem_append_right _ (by simp), v, f, havk, hfk, hfm, hcvEq, hd⟩
                                · rintro ⟨k', hk', v', f', hav', hf', hfi, hc', hd⟩
                                  rcases List.mem_append.mp hk' with h1 | h2
                                  · exact Or.inl ⟨k', h1, v', f', hav', hf', hfi, hc', hd⟩
                                  · simp at h2; subst h2; rw [havk] at hav'; cases hav'; exact Or.inr hd
                              refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, ?_, ?_, hds',
                                by rw [hrsAcc]; exact hrs', hspEq, hstEq⟩
                              · intro k' hk' v' f' hav' hf'
                                rcases List.mem_append.mp hk' with h1 | h2
                                · exact hdone k' h1 v' f' hav' hf'
                                · simp at h2; subst h2; rw [havk] at hav'; rw [hfk] at hf'; cases hav'; cases hf'
                                  exact ⟨hvd0, hoo, hadm, (fun hs => by rw [hfm] at hs; cases hs), (fun _ _ => hnotOnce0)⟩
                              · intro ho'
                                obtain ⟨ho, huT, hnoAny⟩ := hownAcc ho'
                                obtain ⟨hu1, hu2⟩ := huniqD ho
                                have ⟨hownV, hliveS⟩ : v.own = .uniq ∧ ∀ d ∈ v.deps, s'.st[d]? = some .live := by
                                  rcases huIff.mp huT with hne | hokU
                                  · exact absurd hcvEq hne
                                  · exact hokU
                                have hlive0 : ∀ d ∈ v.deps, σ.st[d]? = some .live := by
                                  intro d hd
                                  have hlS := hliveS d hd
                                  have hlt0 := (hvd0 d hd).1
                                  have h1 := hstS d hlt0
                                  rw [hlS] at h1
                                  by_cases hcS : (∃ k' ∈ done, ∃ v' f', avs[nP + k']? = some (some v') ∧ fields[k']? = some f' ∧ f'.fmode = .shared ∧ v'.cls = .val ∧ d ∈ v'.deps) ∧ σ.st[d]? = some .live
                                  · exact hcS.2
                                  · simp only [hcS, ↓reduceIte] at h1; exact h1.symm
                                have hdisjNew : ∀ d ∈ v.deps, d ∉ ds := by
                                  intro d hd hmem
                                  have hcont : ds.contains d = true := by simpa using hmem
                                  have hany : v.deps.any ds.contains = true := List.any_eq_true.mpr ⟨d, hd, hcont⟩
                                  rw [hnoAny] at hany; cases hany
                                refine ⟨?_, ?_⟩
                                · intro k' hk' v' f' hav' hf' hfi hv'
                                  rcases List.mem_append.mp hk' with h1 | h2
                                  · exact hu1 k' h1 v' f' hav' hf' hfi hv'
                                  · simp at h2; subst h2; rw [havk] at hav'; cases hav'; exact ⟨hownV, hlive0⟩
                                · intro k₁ hk₁ k₂ hk₂ hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂ hfi₁ hv₁ hfi₂ hv₂ d hd₁ hd₂
                                  rcases List.mem_append.mp hk₁ with h1 | h1
                                  · rcases List.mem_append.mp hk₂ with h2 | h2
                                    · exact hu2 k₁ h1 k₂ h2 hne v₁ f₁ v₂ f₂ hav₁ hf₁ hav₂ hf₂ hfi₁ hv₁ hfi₂ hv₂ d hd₁ hd₂
                                    · simp at h2; subst h2; rw [havk] at hav₂; cases hav₂
                                      exact hdisjNew d hd₂ ((hds d).mpr ⟨k₁, h1, v₁, f₁, hav₁, hf₁, hfi₁, hv₁, hd₁⟩)
                                  · simp at h1; subst h1
                                    rcases List.mem_append.mp hk₂ with h2 | h2
                                    · rw [havk] at hav₁; cases hav₁
                                      exact hdisjNew d hd₁ ((hds d).mpr ⟨k₂, h2, v₂, f₂, hav₂, hf₂, hfi₂, hv₂, hd₂⟩)
                                    · simp at h2; exact absurd h2.symm hne)
            (fun _ k _ _ _ _ _ _ hfx => by
              cases havk : avs[nP + k]? with
              | none => simp only [havk] at hfx; rw [CM_pure_run] at hfx; cases hfx
              | some optv => cases optv with
                | none => simp only [havk] at hfx; rw [CM_pure_run] at hfx; cases hfx
                | some v =>
                  cases hfk : fields[k]? with
                  | none => simp only [havk, hfk] at hfx; rw [CM_pure_run] at hfx; cases hfx
                  | some f =>
                    simp only [havk, hfk] at hfx; rw [CM_bind_run] at hfx
                    cases hval : (valid v "a constructor field").run _ with
                    | error e => rw [hval] at hfx; cases hfx
                    | ok pv =>
                      rcases pv with ⟨⟨⟩, sv⟩; rw [hval] at hfx; dsimp only at hfx
                      cases ho : v.onceOnly with
                      | true => simp only [ho, ↓reduceIte] at hfx; rw [CM_bind_run, CM_refuseM_run] at hfx; cases hfx
                      | false =>
                        simp only [ho, Bool.false_eq_true, ↓reduceIte] at hfx
                        cases ha : Skel.unknown.admits v.skel with
                        | false => simp only [ha, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_bind_run, CM_refuseM_run] at hfx; cases hfx
                        | true =>
                          simp only [ha, ↓reduceIte] at hfx
                          cases hfm : f.fmode with
                          | shared =>
                            have hsh : (Ixon.FieldMode.shared == Ixon.FieldMode.shared) = true := rfl
                            simp only [hfm, hsh, ↓reduceIte] at hfx
                            cases hfe : (v.regs.filter (· != 1)).isEmpty with
                            | false => simp only [hfe, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_bind_run, CM_refuseM_run] at hfx; cases hfx
                            | true =>
                              simp only [hfe, ↓reduceIte] at hfx; rw [CM_bind_run] at hfx
                              cases hfl : (flowTo .share v.skel v "a shared field").run sv with
                              | error e => rw [hfl] at hfx; cases hfx
                              | ok pf => rw [hfl] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
                          | inherited =>
                            have hsh : (Ixon.FieldMode.inherited == Ixon.FieldMode.shared) = false := rfl
                            simp only [hfm, hsh, Bool.false_eq_true, ↓reduceIte] at hfx
                            cases hcv : (v.cls == .val) with
                            | false => simp only [hcv, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_pure_run] at hfx; cases hfx
                            | true =>
                              simp only [hcv, ↓reduceIte] at hfx; rw [CM_bind_run] at hfx
                              cases hno : (notOnceSrc v "a constructor field").run sv with
                              | error e => rw [hno] at hfx; cases hfx
                              | ok pno =>
                                rw [hno] at hfx; dsimp only at hfx; rw [CM_bind_run] at hfx
                                cases hiu : (isUniq v).run pno.2 with
                                | error e => rw [hiu] at hfx; cases hfx
                                | ok piu =>
                                  rcases piu with ⟨uRes, siu⟩
                                  rw [hiu] at hfx; dsimp only at hfx
                                  cases uRes with
                                  | false =>
                                    simp only [Bool.false_eq_true, ↓reduceIte] at hfx
                                    split at hfx <;> (rw [CM_pure_run] at hfx; cases hfx)
                                  | true =>
                                    simp only [↓reduceIte] at hfx
                                    split at hfx <;> (rw [CM_pure_run] at hfx; cases hfx))
            kept.toList [] (.uniq, [], []) (own, deps, regs) (σ.toCSt 0) (σ'.toCSt 0)
            (by simpa using hpwKept) hinv0 hl
          simp only [List.nil_append] at hinv
          obtain ⟨_, hok', hle', hszSt, honce, hszSp, hreg, hnr, hdone, huniqD, hds, hrs, hsp', hst'⟩ := hinv
          dsimp only [AState.ofCSt, AState.toCSt] at hok' hle' hszSt honce hszSp hreg hnr hsp' hst'
          refine ⟨by simpa [AState.ofCSt_toCSt] using hok', by simpa [AState.ofCSt_toCSt] using hle',
            hszSt, honce, hszSp, hreg, hnr, fun hl => absurd hl hlt, fun _ => ⟨fun ht => (by rw [hke] at ht; cases ht),
              fun _ ht => (by rw [hwr] at ht; cases ht), fun _ _ => ⟨rfl, rfl, rfl, rfl, ?_, huniqD,
                fun d hd => (hds d).mp hd, fun r hr => (hrs r).mp hr, hsp', hst'⟩⟩⟩
          intro k hk v f hav hf
          obtain ⟨h1, h2, h3, h4, h5⟩ := hdone k hk v f hav hf
          exact ⟨h1, h2, h3, fun r hr => (hrs r).mpr ⟨k, hk, v, f, hav, hf, hr⟩,
            h4, fun hi hcv => ⟨h5 hi hcv, fun d hd => (hds d).mpr ⟨k, hk, v, f, hav, hf, hi, hcv, hd⟩⟩⟩

/-- Complete unpacking of `Check.papVal` (`Runs (papVal ifc avs w) σ res σ'`). -/
theorem Runs_papVal {ifc : Iface} {avs : Array (Option AVal)} {w : String}
    {σ σ' : AState} {res : AVal}
    (hok : AStateOk σ) (h : Runs (papVal ifc avs w) σ res σ') :
    AStateOk σ' ∧ AStateLe σ σ' ∧
    σ'.st.size = σ.st.size ∧ σ'.once = σ.once ∧ σ'.spent.size = σ.spent.size ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion ∧
    res.cls = .val ∧ res.own = .shared ∧ res.src = none ∧
    res.skel = ifaceSkel (ifc.params.toList.drop avs.size) ifc.res ifc.resSkel ∧
    (res.onceOnly = true ↔ ∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧
      captureTransfers p.mode = true) ∧
    (∀ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p → avs[i]? = some (some a) →
      ValidDeps σ a.deps ∧ a.onceOnly = false ∧ ¬ IsOnceSrc σ a ∧
      p.skel.admits a.skel = true ∧ (∀ r ∈ a.regs, r ∈ res.regs) ∧
      (captureTransfers p.mode = true → a.cls = .val →
        a.own = .uniq ∧ (∀ x ∈ a.deps, σ.st[x]? = some .live) ∧
        (p.mode.isBorrowed = false → a.regs = [])) ∧
      (captureTransfers p.mode = false → ∀ d ∈ a.deps, d ∈ res.deps)) ∧
    (∀ (i j : Nat) (pi pj : Param) (ai aj : AVal), i ≠ j →
      ifc.params[i]? = some pi → avs[i]? = some (some ai) →
      ifc.params[j]? = some pj → avs[j]? = some (some aj) →
      captureTransfers pi.mode = true → ai.cls = .val →
      (i < j ∨ aj.cls = .val) →
      ∀ d ∈ ai.deps, d ∉ aj.deps) ∧
    (∀ d ∈ res.deps, ∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧
      captureTransfers p.mode = false ∧ d ∈ a.deps) ∧
    (∀ r ∈ res.regs, ∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ r ∈ a.regs) ∧
    (∀ x, x < σ.spent.size →
      σ'.spent[x]? = if (∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ x ∈ a.deps) ∧
          σ.once[x]? = some true
        then some true else σ.spent[x]?) ∧
    (∀ x, x < σ.st.size →
      σ'.st[x]? =
        if ∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧
            captureTransfers p.mode = true ∧ a.cls = .val ∧ x ∈ a.deps
        then some .dead
        else if (∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧
            captureTransfers p.mode = false ∧ a.cls = .val ∧ x ∈ a.deps) ∧ σ.st[x]? = some .live
        then some .shared
        else σ.st[x]?) := by
  unfold Runs papVal at h
  rw [CM_bind_run, CM_forIn_array_eq_list] at h
  cases hl : StateT.run (forIn (m := CM) ifc.params.zipIdx.toList ([], [], false) _) (σ.toCSt 0) with
  | error e => rw [hl] at h; cases h
  | ok p =>
    rcases p with ⟨⟨deps, regs, once⟩, s1⟩
    rw [hl] at h; dsimp only at h; rw [CM_pure_run] at h; cases h
    have hzipList : ifc.params.zipIdx.toList = ifc.params.toList.zipIdx := by simp [Array.toList_zipIdx]
    rw [hzipList] at hl
    let Inv : List (Param × Nat) → List Nat × List Nat × Bool → CSt → Prop := fun done acc s =>
      let ds := acc.1; let rs := acc.2.1; let oo := acc.2.2
      s.steps = 0 ∧
      AStateOk (AState.ofCSt s) ∧ AStateLe σ (AState.ofCSt s) ∧
      s.st.size = σ.st.size ∧ s.once = σ.once ∧ s.spent.size = σ.spent.size ∧
      s.regions = σ.regions ∧ s.nextRegion = σ.nextRegion ∧
      (oo = true ↔ ∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧ captureTransfers p.mode = true) ∧
      (∀ p i a, (p, i) ∈ done → avs[i]? = some (some a) →
        ValidDeps σ a.deps ∧ a.onceOnly = false ∧ ¬ IsOnceSrc σ a ∧
        p.skel.admits a.skel = true ∧
        (captureTransfers p.mode = true → a.cls = .val →
          a.own = .uniq ∧ (∀ x ∈ a.deps, σ.st[x]? = some .live) ∧
          (p.mode.isBorrowed = false → a.regs = []))) ∧
      (∀ pi i pj j ai aj, i ≠ j →
        (pi, i) ∈ done → avs[i]? = some (some ai) →
        (pj, j) ∈ done → avs[j]? = some (some aj) →
        captureTransfers pi.mode = true → ai.cls = .val →
        (i < j ∨ aj.cls = .val) →
        ∀ d ∈ ai.deps, d ∉ aj.deps) ∧
      (∀ d, d ∈ ds ↔ ∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧
        captureTransfers p.mode = false ∧ d ∈ a.deps) ∧
      (∀ r, r ∈ rs ↔ ∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧ r ∈ a.regs) ∧
      (∀ x, x < σ.spent.size →
        s.spent[x]? = if (∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧ x ∈ a.deps) ∧
            σ.once[x]? = some true
          then some true else σ.spent[x]?) ∧
      (∀ x, x < σ.st.size →
        s.st[x]? =
          if ∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧
              captureTransfers p.mode = true ∧ a.cls = .val ∧ x ∈ a.deps
          then some .dead
          else if (∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧
              captureTransfers p.mode = false ∧ a.cls = .val ∧ x ∈ a.deps) ∧ σ.st[x]? = some .live
          then some .shared
          else σ.st[x]?)
    have hinv0 : Inv [] ([], [], false) (σ.toCSt 0) :=
      ⟨rfl, by rw [AState.ofCSt_toCSt]; exact hok, by rw [AState.ofCSt_toCSt]; exact AStateLe.refl σ,
        rfl, rfl, rfl, rfl, rfl,
        by simp, fun _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ h => (by cases h),
        by simp, by simp, fun _ _ => by simp [AState.toCSt], fun _ _ => by simp [AState.toCSt]⟩
    have hinv := CM_forIn_list_prefix_pairwise (R := fun a b => a.2 < b.2) Inv
      (fun done piPair acc s acc' s' hI hltDone hfx => by
        rcases piPair with ⟨p, i⟩
        rcases acc with ⟨ds, rs, oo⟩
        obtain ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, hooIff, hdone, hdisj, hds, hrs, hspS, hstS⟩ := hI
        dsimp only at hfx
        cases havi : avs[i]? with
        | none =>
          simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
          refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hooIff]; constructor
            · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
            · rintro ⟨p', i', a', hm, hav', rest⟩
              rcases List.mem_append.mp hm with h1 | h2
              · exact ⟨p', i', a', h1, hav', rest⟩
              · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
          · intro p' i' a' hm hav'
            rcases List.mem_append.mp hm with h1 | h2
            · exact hdone p' i' a' h1 hav'
            · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
          · intro p₁ i₁ p₂ i₂ a₁ a₂ hne hm₁ hav₁ hm₂ hav₂
            rcases List.mem_append.mp hm₁ with h1 | h1
            · rcases List.mem_append.mp hm₂ with h2 | h2
              · exact hdisj p₁ i₁ p₂ i₂ a₁ a₂ hne h1 hav₁ h2 hav₂
              · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav₂; cases hav₂
            · simp at h1; rcases h1 with ⟨rfl, rfl⟩; rw [havi] at hav₁; cases hav₁
          · intro d; rw [hds d]; constructor
            · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
            · rintro ⟨p', i', a', hm, hav', rest⟩
              rcases List.mem_append.mp hm with h1 | h2
              · exact ⟨p', i', a', h1, hav', rest⟩
              · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
          · intro r; rw [hrs r]; constructor
            · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
            · rintro ⟨p', i', a', hm, hav', rest⟩
              rcases List.mem_append.mp hm with h1 | h2
              · exact ⟨p', i', a', h1, hav', rest⟩
              · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
          · intro x hx; rw [hspS x hx]
            have heq : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ↔
                (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) := by
              constructor
              · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
              · rintro ⟨p', i', a', hm, hav', rest⟩
                rcases List.mem_append.mp hm with h1 | h2
                · exact ⟨p', i', a', h1, hav', rest⟩
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            simp only [heq]
          · intro x hx; rw [hstS x hx]
            have heq1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps) ↔
                (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps) := by
              constructor
              · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
              · rintro ⟨p', i', a', hm, hav', rest⟩
                rcases List.mem_append.mp hm with h1 | h2
                · exact ⟨p', i', a', h1, hav', rest⟩
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            have heq2 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) ↔
                (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) := by
              constructor
              · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
              · rintro ⟨p', i', a', hm, hav', rest⟩
                rcases List.mem_append.mp hm with h1 | h2
                · exact ⟨p', i', a', h1, hav', rest⟩
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            simp only [heq1, heq2]
        | some opta => cases opta with
          | none =>
            simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
            refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hooIff]; constructor
              · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
              · rintro ⟨p', i', a', hm, hav', rest⟩
                rcases List.mem_append.mp hm with h1 | h2
                · exact ⟨p', i', a', h1, hav', rest⟩
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            · intro p' i' a' hm hav'
              rcases List.mem_append.mp hm with h1 | h2
              · exact hdone p' i' a' h1 hav'
              · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            · intro p₁ i₁ p₂ i₂ a₁ a₂ hne hm₁ hav₁ hm₂ hav₂
              rcases List.mem_append.mp hm₁ with h1 | h1
              · rcases List.mem_append.mp hm₂ with h2 | h2
                · exact hdisj p₁ i₁ p₂ i₂ a₁ a₂ hne h1 hav₁ h2 hav₂
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav₂; cases hav₂
              · simp at h1; rcases h1 with ⟨rfl, rfl⟩; rw [havi] at hav₁; cases hav₁
            · intro d; rw [hds d]; constructor
              · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
              · rintro ⟨p', i', a', hm, hav', rest⟩
                rcases List.mem_append.mp hm with h1 | h2
                · exact ⟨p', i', a', h1, hav', rest⟩
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            · intro r; rw [hrs r]; constructor
              · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
              · rintro ⟨p', i', a', hm, hav', rest⟩
                rcases List.mem_append.mp hm with h1 | h2
                · exact ⟨p', i', a', h1, hav', rest⟩
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            · intro x hx; rw [hspS x hx]
              have heq : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ↔
                  (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) := by
                constructor
                · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                · rintro ⟨p', i', a', hm, hav', rest⟩
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact ⟨p', i', a', h1, hav', rest⟩
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
              simp only [heq]
            · intro x hx; rw [hstS x hx]
              have heq1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps) ↔
                  (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps) := by
                constructor
                · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                · rintro ⟨p', i', a', hm, hav', rest⟩
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact ⟨p', i', a', h1, hav', rest⟩
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
              have heq2 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) ↔
                  (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) := by
                constructor
                · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                · rintro ⟨p', i', a', hm, hav', rest⟩
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact ⟨p', i', a', h1, hav', rest⟩
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
              simp only [heq1, heq2]
          | some a =>
            simp only [havi] at hfx
            have hrs' : ∀ r, r ∈ natUnion rs a.regs ↔ ∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧
                avs[i']? = some (some a') ∧ r ∈ a'.regs := by
              intro r; rw [mem_natUnion, hrs r]
              constructor
              · rintro (⟨p', i', a', hm, hr⟩ | hr)
                · exact ⟨p', i', a', List.mem_append_left _ hm, hr⟩
                · exact ⟨p, i, a, List.mem_append_right _ (by simp), havi, hr⟩
              · rintro ⟨p', i', a', hm, hav', hr⟩
                rcases List.mem_append.mp hm with h1 | h2
                · exact Or.inl ⟨p', i', a', h1, hav', hr⟩
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact Or.inr hr
            cases hct : captureTransfers p.mode with
            | true =>
              simp only [hct, ↓reduceIte] at hfx; rw [CM_bind_run] at hfx
              cases hfl : (flowTo (.uniq p.mode.isBorrowed) p.skel a w).run s with
              | error e => rw [hfl] at hfx; cases hfx
              | ok pf =>
                rcases pf with ⟨⟨⟩, sf⟩
                rw [hfl] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
                obtain ⟨hstepsF, hflR⟩ := CM_flowTo_runs hsteps hfl
                obtain ⟨hokF, hleF, hszStF, honceF, hszSpF, hregF, hnrF, hvdS, _, hnonOnce, hspF, _, _, _, huniqF⟩ :=
                  Runs_flowTo hokS hflR
                obtain ⟨huProps, hstUF⟩ := huniqF _ rfl
                dsimp only [AState.ofCSt] at hszStF honceF hszSpF hregF hnrF hspF hstUF
                have ⟨hadm, hoo, hnotOnceS⟩ := hnonOnce (fun hc => by cases hc)
                have hvd0 : ValidDeps σ a.deps := by
                  intro d hd
                  have ⟨hltS, hneD⟩ := hvdS d hd
                  have hlt0 : d < σ.st.size := by rw [← hszSt]; exact hltS
                  refine ⟨hlt0, fun hdead => hneD ?_⟩
                  have h1 := hstS d hlt0
                  by_cases hc1 : ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ d ∈ a'.deps
                  · simp only [hc1, ↓reduceIte] at h1; exact h1
                  · simp only [hc1, ↓reduceIte, hdead, Option.some.injEq, reduceCtorEq, and_false] at h1; exact h1
                have hnoDeadPrev : ∀ d ∈ a.deps, ¬ ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧
                    captureTransfers p'.mode = true ∧ a'.cls = .val ∧ d ∈ a'.deps := by
                  intro d hd hex
                  have ⟨hltS, hneD⟩ := hvdS d hd
                  have h1 := hstS d (by rw [← hszSt]; exact hltS)
                  simp only [hex, ↓reduceIte] at h1
                  exact hneD h1
                have hnotOnce0 : ¬ IsOnceSrc σ a := fun ⟨id, hs, ho⟩ =>
                  hnotOnceS ⟨id, hs, by dsimp [AState.ofCSt]; rw [honce]; exact ho⟩
                have hu0 : a.cls = .val → a.own = .uniq ∧ (∀ x ∈ a.deps, σ.st[x]? = some .live) ∧
                    (p.mode.isBorrowed = false → a.regs = []) := by
                  intro hcv
                  obtain ⟨hown, hlvS, hregNil⟩ := huProps hcv
                  refine ⟨hown, fun x hx => ?_, hregNil⟩
                  have hlt0 := (hvd0 x hx).1
                  have h1 := hstS x hlt0
                  have hlx := hlvS x hx
                  dsimp only [AState.ofCSt] at hlx
                  rw [hlx] at h1
                  by_cases hc1 : ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps
                  · simp only [hc1, ↓reduceIte] at h1; cases h1
                  · simp only [hc1, ↓reduceIte] at h1
                    by_cases hc2 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) ∧ σ.st[x]? = some .live
                    · exact hc2.2
                    · simp only [hc2, ↓reduceIte] at h1; exact h1.symm
                have hnoAnyPrevVal : a.cls = .val → ∀ d ∈ a.deps, ∀ p' i' a', (p', i') ∈ done →
                    avs[i']? = some (some a') → a'.cls = .val → d ∉ a'.deps := by
                  intro hcv d hd p' i' a' hm' hav' hcv' hd'
                  have hlx := (huProps hcv).2.1 d hd
                  dsimp only [AState.ofCSt] at hlx
                  have hlt0 := (hvd0 d hd).1
                  have h1 := hstS d hlt0
                  rw [hlx] at h1
                  cases hct' : captureTransfers p'.mode with
                  | true =>
                    have hex : ∃ p₁ i₁ a₁, (p₁, i₁) ∈ done ∧ avs[i₁]? = some (some a₁) ∧ captureTransfers p₁.mode = true ∧ a₁.cls = .val ∧ d ∈ a₁.deps :=
                      ⟨p', i', a', hm', hav', hct', hcv', hd'⟩
                    simp only [hex, ↓reduceIte] at h1; cases h1
                  | false =>
                    by_cases hc1 : ∃ p₁ i₁ a₁, (p₁, i₁) ∈ done ∧ avs[i₁]? = some (some a₁) ∧ captureTransfers p₁.mode = true ∧ a₁.cls = .val ∧ d ∈ a₁.deps
                    · simp only [hc1, ↓reduceIte] at h1; cases h1
                    · have hlv0 := (hu0 hcv).2.1 d hd
                      have hc2 : (∃ p₁ i₁ a₁, (p₁, i₁) ∈ done ∧ avs[i₁]? = some (some a₁) ∧ captureTransfers p₁.mode = false ∧ a₁.cls = .val ∧ d ∈ a₁.deps) ∧ σ.st[d]? = some .live :=
                        ⟨⟨p', i', a', hm', hav', hct', hcv', hd'⟩, hlv0⟩
                      simp only [hc1, hc2, and_self, ↓reduceIte] at h1; cases h1
                refine ⟨hstepsF, hokF, hleS.trans hleF, hszStF.trans hszSt, honceF.trans honce,
                  hszSpF.trans hszSp, hregF.trans hreg, hnrF.trans hnr, ?_, ?_, ?_, ?_, hrs', ?_, ?_⟩
                · exact ⟨fun _ => ⟨p, i, a, List.mem_append_right _ (by simp), havi, hct⟩, fun _ => rfl⟩
                · intro p' i' a' hm hav'
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact hdone p' i' a' h1 hav'
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
                    exact ⟨hvd0, hoo, hnotOnce0, hadm, fun _ => hu0⟩
                · intro p₁ i₁ p₂ i₂ a₁ a₂ hne hm₁ hav₁ hm₂ hav₂ hct₁ hcv₁ hcond d hd₁ hd₂
                  rcases List.mem_append.mp hm₁ with h1 | h1
                  · rcases List.mem_append.mp hm₂ with h2 | h2
                    · exact hdisj p₁ i₁ p₂ i₂ a₁ a₂ hne h1 hav₁ h2 hav₂ hct₁ hcv₁ hcond d hd₁ hd₂
                    · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav₂; cases hav₂
                      exact hnoDeadPrev d hd₂ ⟨p₁, i₁, a₁, h1, hav₁, hct₁, hcv₁, hd₁⟩
                  · simp at h1; rcases h1 with ⟨rfl, rfl⟩; rw [havi] at hav₁; cases hav₁
                    rcases List.mem_append.mp hm₂ with h2 | h2
                    · rcases hcond with hlt12 | hcv₂
                      · have hlt21 : i₂ < i₁ := hltDone (p₂, i₂) h2
                        omega
                      · exact hnoAnyPrevVal hcv₁ d hd₁ p₂ i₂ a₂ h2 hav₂ hcv₂ hd₂
                    · simp at h2; exact absurd h2.2.symm hne
                · intro d; rw [hds d]; constructor
                  · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                  · rintro ⟨p', i', a', hm, hav', hctf, hd'⟩
                    rcases List.mem_append.mp hm with h1 | h2
                    · exact ⟨p', i', a', h1, hav', hctf, hd'⟩
                    · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [hct] at hctf; cases hctf
                · intro x hx
                  rw [hspF x (by rw [hszSp]; exact hx)]
                  simp only [honce]
                  rw [hspS x hx]
                  by_cases hcNew : x ∈ a.deps ∧ σ.once[x]? = some true
                  · have hcAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true :=
                      ⟨⟨p, i, a, List.mem_append_right _ (by simp), havi, hcNew.1⟩, hcNew.2⟩
                    simp only [hcNew, hcAll, and_self, ↓reduceIte]
                  · simp only [hcNew, ↓reduceIte]
                    by_cases hcOld : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true
                    · have hcAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true :=
                        ⟨let ⟨p', i', a', hm, rest⟩ := hcOld.1; ⟨p', i', a', List.mem_append_left _ hm, rest⟩, hcOld.2⟩
                      simp only [hcOld, hcAll, and_self, ↓reduceIte]
                    · have hnotAll : ¬ ((∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true) := by
                        rintro ⟨⟨p', i', a', hm, hav', hd'⟩, ho⟩
                        rcases List.mem_append.mp hm with h1 | h2
                        · exact hcOld ⟨⟨p', i', a', h1, hav', hd'⟩, ho⟩
                        · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact hcNew ⟨hd', ho⟩
                      simp only [hcOld, hnotAll, ↓reduceIte]
                · intro x hx
                  rw [hstUF x (by rw [hszSt]; exact hx), hstS x hx]
                  by_cases hcNew : a.cls = .val ∧ x ∈ a.deps
                  · have hcAll : ∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps :=
                      ⟨p, i, a, List.mem_append_right _ (by simp), havi, hct, hcNew.1, hcNew.2⟩
                    simp only [hcNew, hcAll, and_self, ↓reduceIte]
                  · simp only [hcNew, ↓reduceIte]
                    have heq1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps) ↔
                        (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps) := by
                      constructor
                      · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                      · rintro ⟨p', i', a', hm, hav', hct', hcv', hd'⟩
                        rcases List.mem_append.mp hm with h1 | h2
                        · exact ⟨p', i', a', h1, hav', hct', hcv', hd'⟩
                        · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact absurd ⟨hcv', hd'⟩ hcNew
                    have heq2 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) ↔
                        (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) := by
                      constructor
                      · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                      · rintro ⟨p', i', a', hm, hav', hctf, hcv', hd'⟩
                        rcases List.mem_append.mp hm with h1 | h2
                        · exact ⟨p', i', a', h1, hav', hctf, hcv', hd'⟩
                        · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [hct] at hctf; cases hctf
                    simp only [heq1, heq2]
            | false =>
              simp only [hct, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_bind_run] at hfx
              cases hfl : (flowTo .share p.skel a w).run s with
              | error e => rw [hfl] at hfx; cases hfx
              | ok pf =>
                rcases pf with ⟨⟨⟩, sf⟩
                rw [hfl] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
                obtain ⟨hstepsF, hflR⟩ := CM_flowTo_runs hsteps hfl
                obtain ⟨hokF, hleF, hszStF, honceF, hszSpF, hregF, hnrF, hvdS, _, hnonOnce, hspF, _, hstShF, _, _⟩ :=
                  Runs_flowTo hokS hflR
                dsimp only [AState.ofCSt] at hszStF honceF hszSpF hregF hnrF hspF hstShF
                have ⟨hadm, hoo, hnotOnceS⟩ := hnonOnce (fun hc => by cases hc)
                have hvd0 : ValidDeps σ a.deps := by
                  intro d hd
                  have ⟨hltS, hneD⟩ := hvdS d hd
                  have hlt0 : d < σ.st.size := by rw [← hszSt]; exact hltS
                  refine ⟨hlt0, fun hdead => hneD ?_⟩
                  have h1 := hstS d hlt0
                  by_cases hc1 : ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ d ∈ a'.deps
                  · simp only [hc1, ↓reduceIte] at h1; exact h1
                  · simp only [hc1, ↓reduceIte, hdead, Option.some.injEq, reduceCtorEq, and_false] at h1; exact h1
                have hnoDeadPrev : ∀ d ∈ a.deps, ¬ ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧
                    captureTransfers p'.mode = true ∧ a'.cls = .val ∧ d ∈ a'.deps := by
                  intro d hd hex
                  have ⟨hltS, hneD⟩ := hvdS d hd
                  have h1 := hstS d (by rw [← hszSt]; exact hltS)
                  simp only [hex, ↓reduceIte] at h1
                  exact hneD h1
                have hnotOnce0 : ¬ IsOnceSrc σ a := fun ⟨id, hs, ho⟩ =>
                  hnotOnceS ⟨id, hs, by dsimp [AState.ofCSt]; rw [honce]; exact ho⟩
                refine ⟨hstepsF, hokF, hleS.trans hleF, hszStF.trans hszSt, honceF.trans honce,
                  hszSpF.trans hszSp, hregF.trans hreg, hnrF.trans hnr, ?_, ?_, ?_, ?_, hrs', ?_, ?_⟩
                · rw [hooIff]; constructor
                  · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                  · rintro ⟨p', i', a', hm, hav', hct'⟩
                    rcases List.mem_append.mp hm with h1 | h2
                    · exact ⟨p', i', a', h1, hav', hct'⟩
                    · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [hct] at hct'; cases hct'
                · intro p' i' a' hm hav'
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact hdone p' i' a' h1 hav'
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
                    exact ⟨hvd0, hoo, hnotOnce0, hadm, fun ht => by rw [hct] at ht; cases ht⟩
                · intro p₁ i₁ p₂ i₂ a₁ a₂ hne hm₁ hav₁ hm₂ hav₂ hct₁ hcv₁ hcond d hd₁ hd₂
                  rcases List.mem_append.mp hm₁ with h1 | h1
                  · rcases List.mem_append.mp hm₂ with h2 | h2
                    · exact hdisj p₁ i₁ p₂ i₂ a₁ a₂ hne h1 hav₁ h2 hav₂ hct₁ hcv₁ hcond d hd₁ hd₂
                    · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav₂; cases hav₂
                      exact hnoDeadPrev d hd₂ ⟨p₁, i₁, a₁, h1, hav₁, hct₁, hcv₁, hd₁⟩
                  · simp at h1; rcases h1 with ⟨rfl, rfl⟩; rw [hct] at hct₁; cases hct₁
                · intro d; rw [mem_natUnion, hds d]
                  constructor
                  · rintro (⟨p', i', a', hm, rest⟩ | hd)
                    · exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                    · exact ⟨p, i, a, List.mem_append_right _ (by simp), havi, hct, hd⟩
                  · rintro ⟨p', i', a', hm, hav', hctf, hd⟩
                    rcases List.mem_append.mp hm with h1 | h2
                    · exact Or.inl ⟨p', i', a', h1, hav', hctf, hd⟩
                    · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact Or.inr hd
                · intro x hx
                  rw [hspF x (by rw [hszSp]; exact hx)]
                  simp only [honce]
                  rw [hspS x hx]
                  by_cases hcNew : x ∈ a.deps ∧ σ.once[x]? = some true
                  · have hcAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true :=
                      ⟨⟨p, i, a, List.mem_append_right _ (by simp), havi, hcNew.1⟩, hcNew.2⟩
                    simp only [hcNew, hcAll, and_self, ↓reduceIte]
                  · simp only [hcNew, ↓reduceIte]
                    by_cases hcOld : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true
                    · have hcAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true :=
                        ⟨let ⟨p', i', a', hm, rest⟩ := hcOld.1; ⟨p', i', a', List.mem_append_left _ hm, rest⟩, hcOld.2⟩
                      simp only [hcOld, hcAll, and_self, ↓reduceIte]
                    · have hnotAll : ¬ ((∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true) := by
                        rintro ⟨⟨p', i', a', hm, hav', hd'⟩, ho⟩
                        rcases List.mem_append.mp hm with h1 | h2
                        · exact hcOld ⟨⟨p', i', a', h1, hav', hd'⟩, ho⟩
                        · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact hcNew ⟨hd', ho⟩
                      simp only [hcOld, hnotAll, ↓reduceIte]
                · intro x hx
                  rw [hstShF rfl x (by rw [hszSt]; exact hx)]
                  simp only [hstS x hx]
                  have heq1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps) ↔
                      (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps) := by
                    constructor
                    · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                    · rintro ⟨p', i', a', hm, hav', hct', hcv', hd'⟩
                      rcases List.mem_append.mp hm with h1 | h2
                      · exact ⟨p', i', a', h1, hav', hct', hcv', hd'⟩
                      · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [hct] at hct'; cases hct'
                  by_cases hc1 : ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps
                  · have hc1' := heq1.mp hc1
                    simp only [hc1, hc1', ↓reduceIte, Option.some.injEq, reduceCtorEq, and_false]
                  · have hc1' : ¬ (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = true ∧ a'.cls = .val ∧ x ∈ a'.deps) :=
                      fun h => hc1 (heq1.mpr h)
                    simp only [hc1, hc1', ↓reduceIte]
                    by_cases hcOld : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) ∧ σ.st[x]? = some .live
                    · have hcAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) ∧ σ.st[x]? = some .live :=
                        ⟨let ⟨p', i', a', hm, rest⟩ := hcOld.1; ⟨p', i', a', List.mem_append_left _ hm, rest⟩, hcOld.2⟩
                      simp only [hcOld, hcAll, and_self, ↓reduceIte, Option.some.injEq, reduceCtorEq, and_false]
                    · simp only [hcOld, ↓reduceIte]
                      by_cases hcNew : a.cls = .val ∧ x ∈ a.deps ∧ σ.st[x]? = some .live
                      · have hcAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) ∧ σ.st[x]? = some .live :=
                          ⟨⟨p, i, a, List.mem_append_right _ (by simp), havi, hct, hcNew.1, hcNew.2.1⟩, hcNew.2.2⟩
                        simp only [hcNew, hcAll, and_self, ↓reduceIte]
                      · have hnotAll : ¬ ((∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ captureTransfers p'.mode = false ∧ a'.cls = .val ∧ x ∈ a'.deps) ∧ σ.st[x]? = some .live) := by
                          rintro ⟨⟨p', i', a', hm, hav', hctf, hcv', hd'⟩, hlv⟩
                          rcases List.mem_append.mp hm with h1 | h2
                          · exact hcOld ⟨⟨p', i', a', h1, hav', hctf, hcv', hd'⟩, hlv⟩
                          · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact hcNew ⟨hcv', hd', hlv⟩
                        simp only [hcNew, hnotAll, ↓reduceIte])
      (fun _ piPair _ _ _ _ _ _ hfx => by
        rcases piPair with ⟨p, i⟩; dsimp only at hfx
        cases havi : avs[i]? with
        | none => simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
        | some opta => cases opta with
          | none => simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
          | some a =>
            simp only [havi] at hfx
            cases hct : captureTransfers p.mode with
            | true =>
              simp only [hct, ↓reduceIte] at hfx; rw [CM_bind_run] at hfx
              cases hfl : (flowTo (.uniq p.mode.isBorrowed) p.skel a w).run _ with
              | error e => rw [hfl] at hfx; cases hfx
              | ok pf => rw [hfl] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
            | false =>
              simp only [hct, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_bind_run] at hfx
              cases hfl : (flowTo .share p.skel a w).run _ with
              | error e => rw [hfl] at hfx; cases hfx
              | ok pf => rw [hfl] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx)
      ifc.params.toList.zipIdx [] ([], [], false) (deps, regs, once) (σ.toCSt 0) (σ'.toCSt 0)
      (by simpa using list_zipIdx_pairwise_lt ifc.params.toList 0) hinv0 hl
    simp only [List.nil_append] at hinv
    obtain ⟨_, hok', hle', hszSt, honce, hszSp, hreg, hnr, hooIff, hdone, hdisj, hds, hrs, hsp', hst'⟩ := hinv
    dsimp only [AState.ofCSt, AState.toCSt] at hok' hle' hszSt honce hszSp hreg hnr hsp' hst'
    refine ⟨by simpa [AState.ofCSt_toCSt] using hok', by simpa [AState.ofCSt_toCSt] using hle',
      hszSt, honce, hszSp, hreg, hnr, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hooIff]; constructor
      · rintro ⟨p, i, a, hm, rest⟩; exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
      · rintro ⟨i, p, a, hp, rest⟩; exact ⟨p, i, a, mem_array_zipIdx_iff.mpr hp, rest⟩
    · intro i p a hp hav
      have hm := mem_array_zipIdx_iff.mpr hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := hdone p i a hm hav
      exact ⟨h1, h2, h3, h4, fun r hr => (hrs r).mpr ⟨p, i, a, hm, hav, hr⟩,
        h5, fun hctf d hd => (hds d).mpr ⟨p, i, a, hm, hav, hctf, hd⟩⟩
    · intro i j pi pj ai aj hne hpi hai hpj haj
      exact hdisj pi i pj j ai aj hne (mem_array_zipIdx_iff.mpr hpi) hai (mem_array_zipIdx_iff.mpr hpj) haj
    · intro d hd; obtain ⟨p, i, a, hm, rest⟩ := (hds d).mp hd
      exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
    · intro r hr; obtain ⟨p, i, a, hm, rest⟩ := (hrs r).mp hr
      exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
    · intro x hx; rw [hsp' x hx]
      have heq : (∃ p i a, (p, i) ∈ ifc.params.toList.zipIdx ∧ avs[i]? = some (some a) ∧ x ∈ a.deps) ↔
          (∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ x ∈ a.deps) := by
        constructor
        · rintro ⟨p, i, a, hm, rest⟩; exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
        · rintro ⟨i, p, a, hp, rest⟩; exact ⟨p, i, a, mem_array_zipIdx_iff.mpr hp, rest⟩
      simp only [heq]
    · intro x hx; rw [hst' x hx]
      have heq1 : (∃ p i a, (p, i) ∈ ifc.params.toList.zipIdx ∧ avs[i]? = some (some a) ∧ captureTransfers p.mode = true ∧ a.cls = .val ∧ x ∈ a.deps) ↔
          (∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ captureTransfers p.mode = true ∧ a.cls = .val ∧ x ∈ a.deps) := by
        constructor
        · rintro ⟨p, i, a, hm, rest⟩; exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
        · rintro ⟨i, p, a, hp, rest⟩; exact ⟨p, i, a, mem_array_zipIdx_iff.mpr hp, rest⟩
      have heq2 : (∃ p i a, (p, i) ∈ ifc.params.toList.zipIdx ∧ avs[i]? = some (some a) ∧ captureTransfers p.mode = false ∧ a.cls = .val ∧ x ∈ a.deps) ↔
          (∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ captureTransfers p.mode = false ∧ a.cls = .val ∧ x ∈ a.deps) := by
        constructor
        · rintro ⟨p, i, a, hm, rest⟩; exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
        · rintro ⟨i, p, a, hp, rest⟩; exact ⟨p, i, a, mem_array_zipIdx_iff.mpr hp, rest⟩
      simp only [heq1, heq2]

/-- Binding `x` is killed (`.dead`) by `flowTo (destOf p lendPlain)` on argument `a`. -/
def callKills (lendPlain : Bool) (p : Param) (a : AVal) (x : Nat) : Prop :=
  (∃ b, destOf p lendPlain = .uniq b ∧ a.cls = .val ∧ x ∈ a.deps) ∨
  (destOf p lendPlain = .once ∧ a.onceOnly = true ∧ a.src = some x)

/-- Binding `x` (if `.live`) is shared (`.shared`) by `flowTo (destOf p lendPlain)` on argument `a`. -/
def callShares (lendPlain : Bool) (p : Param) (a : AVal) (x : Nat) : Prop :=
  (destOf p lendPlain = .share ∨ destOf p lendPlain = .once) ∧ a.cls = .val ∧ x ∈ a.deps

/-- Helper: `destOf` is `.uniq` iff `p.mode ≠ .erased ∧ p.mode.isUnique = true`. -/
theorem destOf_isUniq_iff (p : Param) (lendPlain : Bool) :
    (∃ b, destOf p lendPlain = .uniq b) ↔ p.mode.isUnique = true := by
  unfold destOf
  cases p.mode <;> cases lendPlain <;> simp [Ixon.BinderMode.isUnique, Ixon.BinderMode.usage, Ixon.BinderMode.isBorrowed]

theorem destOf_once_iff (p : Param) (lendPlain : Bool) :
    destOf p lendPlain = .once ↔ p.mode.usage = .once := by
  unfold destOf
  cases p.mode <;> cases lendPlain <;> simp [Ixon.BinderMode.isUnique, Ixon.BinderMode.usage, Ixon.BinderMode.isBorrowed]

/-- Complete unpacking of `Check.callResult` (Pass 1 + Pass 2 Bug #9b + return construction). -/
theorem Runs_callResult {ifc : Iface} {avs : Array (Option AVal)} {w : String}
    {σ σ' : AState} {res : AVal}
    (hok : AStateOk σ) (h : Runs (callResult ifc avs w) σ res σ') :
    let lendPlain := ifc.resCls != .val
    AStateOk σ' ∧ AStateLe σ σ' ∧
    σ'.st.size = σ.st.size ∧ σ'.once = σ.once ∧ σ'.spent.size = σ.spent.size ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion ∧
    res.cls = ifc.resCls ∧ res.skel = ifc.resSkel ∧ res.onceOnly = false ∧ res.src = none ∧
    -- Per-argument validity, skeleton, once, uniqueness, and repair U properties
    (∀ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p → avs[i]? = some (some a) →
      ValidDeps σ a.deps ∧
      (destOf p lendPlain = .once → p.skel.admitsNA a.skel = true ∧ UnspentOnceDeps σ a.deps) ∧
      (destOf p lendPlain ≠ .once → p.skel.admits a.skel = true ∧ a.onceOnly = false ∧ ¬ IsOnceSrc σ a) ∧
      (∀ b, destOf p lendPlain = .uniq b → a.cls = .val →
        a.own = .uniq ∧ (∀ x ∈ a.deps, σ.st[x]? = some .live) ∧ (b = false → a.regs = [])) ∧
      (ifc.res = .unique → ifc.resCls = .val → a.cls ≠ .leaf → p.cls ≠ .leaf →
        (destOf p lendPlain = .share ∨ destOf p lendPlain = .once) → a.regs = [])) ∧
    -- Pairwise disjointness across distinct call arguments (Pass 1 + Pass 2 Bug #9b)
    (∀ (i j : Nat) (pi pj : Param) (ai aj : AVal), i ≠ j →
      ifc.params[i]? = some pi → avs[i]? = some (some ai) →
      ifc.params[j]? = some pj → avs[j]? = some (some aj) →
      -- Unique `ai` (class `.val`) is disjoint from `aj` for ALL `j ≠ i` when `i < j ∨ lend ∨ aj.cls = .val`
      ((∀ b, destOf pi lendPlain = .uniq b → ai.cls = .val →
        (i < j ∨ destOf pj lendPlain = .lend ∨ aj.cls = .val) →
        ∀ x ∈ ai.deps, x ∉ aj.deps)) ∧
      -- Once-only `ai` killed at `x` is disjoint from `aj` for all `j > i` and all `.lend` `j < i`
      ((destOf pi lendPlain = .once → ai.onceOnly = true → ∀ x, ai.src = some x →
        (i < j ∨ destOf pj lendPlain = .lend) → x ∉ aj.deps)) ∧
      -- Once arg `aj` after `ai` (`i < j`) has no once-dep in common with `ai`
      ((i < j → destOf pj lendPlain = .once →
        ∀ x ∈ aj.deps, σ.once[x]? = some true → x ∉ ai.deps))) ∧
    -- Exact `res` shape (`own`, `deps`, `regs`)
    (ifc.resCls = .irr ∨ ifc.resCls = .imm → res = { cls := ifc.resCls, skel := ifc.resSkel }) ∧
    (ifc.resCls = .leaf →
      res = { cls := .leaf, skel := ifc.resSkel,
              own := if ifc.res.isUnique then .uniq else .shared }) ∧
    (ifc.resCls = .val →
      (ifc.res = .unique → res = { cls := .val, own := .uniq, skel := ifc.resSkel }) ∧
      (ifc.res = .uniqueBorrowed →
        res.own = .uniq ∧
        (∀ d, d ∈ res.deps ↔ ∃ (i : Nat) (p : Param) (a : AVal),
          ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ a.cls = .val ∧ d ∈ a.deps) ∧
        (∀ r, r ∈ res.regs ↔ r = σ.regions.headD 1 ∨ ∃ (i : Nat) (p : Param) (a : AVal),
          ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ r ∈ a.regs)) ∧
      (ifc.res = .borrowed →
        res.own = .shared ∧
        (∀ d, d ∈ res.deps ↔ ∃ (i : Nat) (p : Param) (a : AVal),
          ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ a.cls = .val ∧ d ∈ a.deps) ∧
        (∀ r, r ∈ res.regs ↔ r = σ.regions.headD 1 ∨ ∃ (i : Nat) (p : Param) (a : AVal),
          ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ r ∈ a.regs)) ∧
      (ifc.res = .shared →
        res.own = .shared ∧
        (∀ d, d ∈ res.deps ↔ ∃ (i : Nat) (p : Param) (a : AVal),
          ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ destOf p false = .share ∧ d ∈ a.deps) ∧
        (∀ r, r ∈ res.regs ↔ ∃ (i : Nat) (p : Param) (a : AVal),
          ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ r ∈ a.regs))) ∧
    -- Pointwise `spent` and `st` transitions
    (∀ x, x < σ.spent.size →
      σ'.spent[x]? = if (∃ (i : Nat) (p : Param) (a : AVal),
          ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ x ∈ a.deps) ∧ σ.once[x]? = some true
        then some true else σ.spent[x]?) ∧
    (∀ x, x < σ.st.size →
      σ'.st[x]? =
        if ∃ (i : Nat) (p : Param) (a : AVal),
            ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ callKills lendPlain p a x
        then some .dead
        else if (∃ (i : Nat) (p : Param) (a : AVal),
            ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ callShares lendPlain p a x) ∧
            σ.st[x]? = some .live
        then some .shared
        else σ.st[x]?) := by
  intro lendPlain
  unfold Runs callResult at h
  rw [CM_bind_run, CM_forIn_array_eq_list] at h
  cases hl1 : StateT.run (forIn (m := CM) ifc.params.zipIdx.toList ([], [], []) _) (σ.toCSt 0) with
  | error e => rw [hl1] at h; cases h
  | ok p1 =>
    rcases p1 with ⟨⟨deps, sdeps, regs⟩, s1⟩
    rw [hl1] at h; dsimp only at h
    rw [CM_bind_run, CM_forIn_array_eq_list] at h
    cases hl2 : StateT.run (forIn (m := CM) ifc.params.zipIdx.toList PUnit.unit _) s1 with
    | error e => rw [hl2] at h; cases h
    | ok p2 =>
      rcases p2 with ⟨⟨⟩, s2⟩
      rw [hl2] at h; dsimp only at h
      have hzipList : ifc.params.zipIdx.toList = ifc.params.toList.zipIdx := by simp [Array.toList_zipIdx]
      rw [hzipList] at hl1 hl2
      -- Pass 1 invariant
      let Inv : List (Param × Nat) → List Nat × List Nat × List Nat → CSt → Prop := fun done acc s =>
        let ds := acc.1; let sds := acc.2.1; let rs := acc.2.2
        s.steps = 0 ∧
        AStateOk (AState.ofCSt s) ∧ AStateLe σ (AState.ofCSt s) ∧
        s.st.size = σ.st.size ∧ s.once = σ.once ∧ s.spent.size = σ.spent.size ∧
        s.regions = σ.regions ∧ s.nextRegion = σ.nextRegion ∧
        (∀ p i a, (p, i) ∈ done → avs[i]? = some (some a) →
          ValidDeps σ a.deps ∧
          (destOf p lendPlain = .once → p.skel.admitsNA a.skel = true ∧ UnspentOnceDeps σ a.deps) ∧
          (destOf p lendPlain ≠ .once → p.skel.admits a.skel = true ∧ a.onceOnly = false ∧ ¬ IsOnceSrc σ a) ∧
          (∀ b, destOf p lendPlain = .uniq b → a.cls = .val →
            a.own = .uniq ∧ (∀ x ∈ a.deps, σ.st[x]? = some .live) ∧ (b = false → a.regs = [])) ∧
          (ifc.res = .unique → ifc.resCls = .val → a.cls ≠ .leaf → p.cls ≠ .leaf →
            (destOf p lendPlain = .share ∨ destOf p lendPlain = .once) → a.regs = [])) ∧
        (∀ pi i pj j ai aj, i < j →
          (pi, i) ∈ done → avs[i]? = some (some ai) →
          (pj, j) ∈ done → avs[j]? = some (some aj) →
          (∀ x, callKills lendPlain pi ai x → x ∉ aj.deps) ∧
          (∀ b, destOf pj lendPlain = .uniq b → aj.cls = .val →
            destOf pi lendPlain ≠ .lend → ai.cls = .val → ∀ x ∈ aj.deps, x ∉ ai.deps) ∧
          (destOf pj lendPlain = .once → ∀ x ∈ aj.deps, σ.once[x]? = some true → x ∉ ai.deps)) ∧
        (∀ d, d ∈ ds ↔ ∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧ a.cls = .val ∧ d ∈ a.deps) ∧
        (∀ d, d ∈ sds ↔ ∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧ destOf p lendPlain = .share ∧ d ∈ a.deps) ∧
        (∀ r, r ∈ rs ↔ ∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧ r ∈ a.regs) ∧
        (∀ x, x < σ.spent.size →
          s.spent[x]? = if (∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧ x ∈ a.deps) ∧
              σ.once[x]? = some true
            then some true else σ.spent[x]?) ∧
        (∀ x, x < σ.st.size →
          s.st[x]? =
            if ∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧ callKills lendPlain p a x
            then some .dead
            else if (∃ p i a, (p, i) ∈ done ∧ avs[i]? = some (some a) ∧ callShares lendPlain p a x) ∧
                σ.st[x]? = some .live
            then some .shared
            else σ.st[x]?)
      have hinv0 : Inv [] ([], [], []) (σ.toCSt 0) :=
        ⟨rfl, by rw [AState.ofCSt_toCSt]; exact hok, by rw [AState.ofCSt_toCSt]; exact AStateLe.refl σ,
          rfl, rfl, rfl, rfl, rfl,
          fun _ _ _ hm => (by cases hm), fun _ _ _ _ _ _ _ hm => (by cases hm),
          by simp, by simp, by simp, fun _ _ => by simp [AState.toCSt], fun _ _ => by simp [AState.toCSt]⟩
      have hinv1 := CM_forIn_list_prefix_pairwise (R := fun a b => a.2 < b.2) Inv
        (fun done piPair acc s acc' s' hI hltDone hfx => by
          rcases piPair with ⟨p, i⟩
          rcases acc with ⟨ds, sds, rs⟩
          obtain ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, hdone, hord, hds, hsds, hrs, hspS, hstS⟩ := hI
          cases havi : avs[i]? with
          | none =>
            simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
            refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro p' i' a' hm hav'
              rcases List.mem_append.mp hm with h1 | h2
              · exact hdone p' i' a' h1 hav'
              · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            · intro p₁ i₁ p₂ i₂ a₁ a₂ hlt12 hm₁ hav₁ hm₂ hav₂
              rcases List.mem_append.mp hm₁ with h1 | h1
              · rcases List.mem_append.mp hm₂ with h2 | h2
                · exact hord p₁ i₁ p₂ i₂ a₁ a₂ hlt12 h1 hav₁ h2 hav₂
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav₂; cases hav₂
              · simp at h1; rcases h1 with ⟨rfl, rfl⟩; rw [havi] at hav₁; cases hav₁
            · intro d; rw [hds d]; constructor
              · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
              · rintro ⟨p', i', a', hm, hav', rest⟩
                rcases List.mem_append.mp hm with h1 | h2
                · exact ⟨p', i', a', h1, hav', rest⟩
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            · intro d; rw [hsds d]; constructor
              · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
              · rintro ⟨p', i', a', hm, hav', rest⟩
                rcases List.mem_append.mp hm with h1 | h2
                · exact ⟨p', i', a', h1, hav', rest⟩
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            · intro r; rw [hrs r]; constructor
              · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
              · rintro ⟨p', i', a', hm, hav', rest⟩
                rcases List.mem_append.mp hm with h1 | h2
                · exact ⟨p', i', a', h1, hav', rest⟩
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
            · intro x hx; rw [hspS x hx]
              have heq : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ↔
                  (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) := by
                constructor
                · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                · rintro ⟨p', i', a', hm, hav', rest⟩
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact ⟨p', i', a', h1, hav', rest⟩
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
              simp only [heq]
            · intro x hx; rw [hstS x hx]
              have heq1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) ↔
                  (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) := by
                constructor
                · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                · rintro ⟨p', i', a', hm, hav', rest⟩
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact ⟨p', i', a', h1, hav', rest⟩
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
              have heq2 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ↔
                  (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) := by
                constructor
                · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                · rintro ⟨p', i', a', hm, hav', rest⟩
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact ⟨p', i', a', h1, hav', rest⟩
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
              simp only [heq1, heq2]
          | some opta => cases opta with
            | none =>
              simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
              refine ⟨hsteps, hokS, hleS, hszSt, honce, hszSp, hreg, hnr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro p' i' a' hm hav'
                rcases List.mem_append.mp hm with h1 | h2
                · exact hdone p' i' a' h1 hav'
                · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
              · intro p₁ i₁ p₂ i₂ a₁ a₂ hlt12 hm₁ hav₁ hm₂ hav₂
                rcases List.mem_append.mp hm₁ with h1 | h1
                · rcases List.mem_append.mp hm₂ with h2 | h2
                  · exact hord p₁ i₁ p₂ i₂ a₁ a₂ hlt12 h1 hav₁ h2 hav₂
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav₂; cases hav₂
                · simp at h1; rcases h1 with ⟨rfl, rfl⟩; rw [havi] at hav₁; cases hav₁
              · intro d; rw [hds d]; constructor
                · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                · rintro ⟨p', i', a', hm, hav', rest⟩
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact ⟨p', i', a', h1, hav', rest⟩
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
              · intro d; rw [hsds d]; constructor
                · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                · rintro ⟨p', i', a', hm, hav', rest⟩
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact ⟨p', i', a', h1, hav', rest⟩
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
              · intro r; rw [hrs r]; constructor
                · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                · rintro ⟨p', i', a', hm, hav', rest⟩
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact ⟨p', i', a', h1, hav', rest⟩
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
              · intro x hx; rw [hspS x hx]
                have heq : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ↔
                    (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) := by
                  constructor
                  · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                  · rintro ⟨p', i', a', hm, hav', rest⟩
                    rcases List.mem_append.mp hm with h1 | h2
                    · exact ⟨p', i', a', h1, hav', rest⟩
                    · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
                simp only [heq]
              · intro x hx; rw [hstS x hx]
                have heq1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) ↔
                    (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) := by
                  constructor
                  · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                  · rintro ⟨p', i', a', hm, hav', rest⟩
                    rcases List.mem_append.mp hm with h1 | h2
                    · exact ⟨p', i', a', h1, hav', rest⟩
                    · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
                have heq2 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ↔
                    (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) := by
                  constructor
                  · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                  · rintro ⟨p', i', a', hm, hav', rest⟩
                    rcases List.mem_append.mp hm with h1 | h2
                    · exact ⟨p', i', a', h1, hav', rest⟩
                    · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
                simp only [heq1, heq2]
            | some a =>
              simp only [havi] at hfx
              let d := destOf p lendPlain
              rw [CM_bind_run] at hfx
              cases hfl : (flowTo (destOf p lendPlain) p.skel a w).run s with
              | error e => rw [hfl] at hfx; cases hfx
              | ok pf =>
                rcases pf with ⟨⟨⟩, sf⟩
                rw [hfl] at hfx; dsimp only at hfx
                obtain ⟨hstepsF, hflR⟩ := CM_flowTo_runs hsteps hfl
                obtain ⟨hokF, hleF, hszStF, honceF, hszSpF, hregF, hnrF, hvdS, honceFProps, hnonOnceF,
                  hspF, hstLendF, hstShF, hstOnceF, huniqF⟩ := Runs_flowTo hokS hflR
                dsimp only [AState.ofCSt] at hszStF honceF hszSpF hregF hnrF hspF hstLendF hstShF hstOnceF
                -- Unpack Repair U check + accumulator update
                have hrepU_fin :
                    (ifc.res = .unique → ifc.resCls = .val → a.cls ≠ .leaf → p.cls ≠ .leaf →
                      (destOf p lendPlain = .share ∨ destOf p lendPlain = .once) → a.regs = []) ∧
                    s' = sf ∧
                    acc'.1 = (if a.cls == .val then natUnion ds a.deps else ds) ∧
                    acc'.2.1 = (match destOf p lendPlain with | .share => natUnion sds a.deps | _ => sds) ∧
                    acc'.2.2 = natUnion rs a.regs := by
                  have hcond_eq :
                      (ifc.res == Ixon.ResultMode.unique && ifc.resCls == Cls.val && !a.regs.isEmpty && a.cls != Cls.leaf && p.cls != Cls.leaf) =
                      true → (destOf p lendPlain = .share ∨ destOf p lendPlain = .once) → False := by
                    intro hc hdso
                    simp only [hc, ↓reduceIte] at hfx
                    rcases hdso with hdEq | hdEq <;>
                      (rw [hdEq] at hfx; dsimp only at hfx; rw [CM_bind_run, CM_refuseM_run] at hfx; cases hfx)
                  have hrepU : ifc.res = .unique → ifc.resCls = .val → a.cls ≠ .leaf → p.cls ≠ .leaf →
                      (destOf p lendPlain = .share ∨ destOf p lendPlain = .once) → a.regs = [] := by
                    intro hru hrc hac hpc hdso
                    cases hr : a.regs with
                    | nil => rfl
                    | cons r0 rs0 =>
                      have hc : (ifc.res == Ixon.ResultMode.unique && ifc.resCls == Cls.val && !a.regs.isEmpty && a.cls != Cls.leaf && p.cls != Cls.leaf) = true := by
                        rw [hru, hrc, hr]
                        have h2 : (Cls.val == Cls.val) = true := rfl
                        have h3 : (a.cls != Cls.leaf) = true := by
                          cases hcA : a.cls <;> try rfl
                          exact absurd hcA hac
                        have h4 : (p.cls != Cls.leaf) = true := by
                          cases hcP : p.cls <;> try rfl
                          exact absurd hcP hpc
                        simp [h2, h3, h4]
                      exact False.elim (hcond_eq hc hdso)
                  refine ⟨hrepU, ?_⟩
                  by_cases hc : (ifc.res == Ixon.ResultMode.unique && ifc.resCls == Cls.val && !a.regs.isEmpty && a.cls != Cls.leaf && p.cls != Cls.leaf) = true
                  · simp only [hc, ↓reduceIte] at hfx
                    cases hdEq : destOf p lendPlain with
                    | share => exact False.elim (hcond_eq hc (Or.inl hdEq))
                    | once => exact False.elim (hcond_eq hc (Or.inr hdEq))
                    | lend | uniq _ =>
                      rw [hdEq] at hfx; dsimp only at hfx
                      cases hcv : (a.cls == .val) <;>
                        (simp only [hcv, Bool.false_eq_true, ↓reduceIte] at hfx ⊢; rw [CM_pure_run] at hfx; cases hfx; exact ⟨rfl, rfl, rfl, rfl⟩)
                  · have hcf := Bool.eq_false_iff.mpr hc
                    simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hfx
                    cases hdEq : destOf p lendPlain with
                    | share | once | lend | uniq _ =>
                      rw [hdEq] at hfx; dsimp only at hfx
                      cases hcv : (a.cls == .val) <;>
                        (simp only [hcv, Bool.false_eq_true, ↓reduceIte] at hfx ⊢; rw [CM_pure_run] at hfx; cases hfx; exact ⟨rfl, rfl, rfl, rfl⟩)
                obtain ⟨hrepU, rfl, hdsAcc, hsdsAcc, hrsAcc⟩ := hrepU_fin
                -- Lift per-arg properties back to `σ`
                have hvd0 : ValidDeps σ a.deps := by
                  intro x hx
                  have ⟨hltS, hneD⟩ := hvdS x hx
                  have hlt0 : x < σ.st.size := by rw [← hszSt]; exact hltS
                  refine ⟨hlt0, fun hdead => hneD ?_⟩
                  have h1 := hstS x hlt0
                  by_cases hk1 : ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x
                  · simp only [hk1, ↓reduceIte] at h1; exact h1
                  · simp only [hk1, ↓reduceIte, hdead, Option.some.injEq, reduceCtorEq, and_false] at h1; exact h1
                have hnoKillPrev : ∀ x ∈ a.deps, ¬ ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧
                    callKills lendPlain p' a' x := by
                  intro x hx hex
                  have ⟨hltS, hneD⟩ := hvdS x hx
                  have h1 := hstS x (by rw [← hszSt]; exact hltS)
                  simp only [hex, ↓reduceIte] at h1
                  exact hneD h1
                have honce0 : d = .once → p.skel.admitsNA a.skel = true ∧ UnspentOnceDeps σ a.deps := by
                  intro hdo
                  obtain ⟨hadm, hunspS⟩ := honceFProps hdo
                  refine ⟨hadm, fun x hx ho => ?_⟩
                  have hspFalse := hunspS x hx (by dsimp [AState.ofCSt]; rw [honce]; exact ho)
                  dsimp only [AState.ofCSt] at hspFalse
                  have hlt0 : x < σ.spent.size := by
                    have h1 := (hvd0 x hx).1; have h2 := hok.2.1; omega
                  have h1 := hspS x hlt0
                  rw [hspFalse] at h1
                  by_cases hc : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true
                  · simp only [hc, and_self, ↓reduceIte] at h1; cases h1
                  · simp only [hc, ↓reduceIte] at h1; exact h1.symm
                have hnoPrevOnceDep : d = .once → ∀ x ∈ a.deps, σ.once[x]? = some true →
                    ∀ p' i' a', (p', i') ∈ done → avs[i']? = some (some a') → x ∉ a'.deps := by
                  intro hdo x hx ho p' i' a' hm' hav' hx'
                  have hspFalse := (honceFProps hdo).2 x hx (by dsimp [AState.ofCSt]; rw [honce]; exact ho)
                  dsimp only [AState.ofCSt] at hspFalse
                  have hlt0 : x < σ.spent.size := by have h1 := (hvd0 x hx).1; have h2 := hok.2.1; omega
                  have h1 := hspS x hlt0
                  have hc : (∃ p₁ i₁ a₁, (p₁, i₁) ∈ done ∧ avs[i₁]? = some (some a₁) ∧ x ∈ a₁.deps) ∧ σ.once[x]? = some true :=
                    ⟨⟨p', i', a', hm', hav', hx'⟩, ho⟩
                  simp only [hc, and_self, ↓reduceIte] at h1
                  rw [hspFalse] at h1; cases h1
                have hnonOnce0 : d ≠ .once → p.skel.admits a.skel = true ∧ a.onceOnly = false ∧ ¬ IsOnceSrc σ a := by
                  intro hne
                  obtain ⟨hadm, hoo, hnotOnceS⟩ := hnonOnceF hne
                  exact ⟨hadm, hoo, fun ⟨id, hs, ho⟩ => hnotOnceS ⟨id, hs, by dsimp [AState.ofCSt]; rw [honce]; exact ho⟩⟩
                have huniq0 : ∀ b, d = .uniq b → a.cls = .val →
                    a.own = .uniq ∧ (∀ x ∈ a.deps, σ.st[x]? = some .live) ∧ (b = false → a.regs = []) := by
                  intro b hdu hcv
                  obtain ⟨hown, hlvS, hregNil⟩ := (huniqF b hdu).1 hcv
                  refine ⟨hown, fun x hx => ?_, hregNil⟩
                  have hlt0 := (hvd0 x hx).1
                  have h1 := hstS x hlt0
                  have hlx := hlvS x hx; dsimp only [AState.ofCSt] at hlx
                  rw [hlx] at h1
                  by_cases hk1 : ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x
                  · simp only [hk1, ↓reduceIte] at h1; cases h1
                  · simp only [hk1, ↓reduceIte] at h1
                    by_cases hs1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ∧ σ.st[x]? = some .live
                    · exact hs1.2
                    · simp only [hs1, ↓reduceIte] at h1; exact h1.symm
                have hnoPrevNonLendVal : ∀ b, d = .uniq b → a.cls = .val →
                    ∀ p' i' a', (p', i') ∈ done → avs[i']? = some (some a') →
                    destOf p' lendPlain ≠ .lend → a'.cls = .val → ∀ x ∈ a.deps, x ∉ a'.deps := by
                  intro b hdu hcv p' i' a' hm' hav' hneL hcv' x hx hx'
                  have hlx := ((huniqF b hdu).1 hcv).2.1 x hx; dsimp only [AState.ofCSt] at hlx
                  have hlt0 := (hvd0 x hx).1
                  have h1 := hstS x hlt0; rw [hlx] at h1
                  cases hd' : destOf p' lendPlain with
                  | lend => exact absurd hd' hneL
                  | uniq b' =>
                    have hk1 : ∃ p₁ i₁ a₁, (p₁, i₁) ∈ done ∧ avs[i₁]? = some (some a₁) ∧ callKills lendPlain p₁ a₁ x :=
                      ⟨p', i', a', hm', hav', Or.inl ⟨b', hd', hcv', hx'⟩⟩
                    simp only [hk1, ↓reduceIte] at h1; cases h1
                  | share =>
                    by_cases hk1 : ∃ p₁ i₁ a₁, (p₁, i₁) ∈ done ∧ avs[i₁]? = some (some a₁) ∧ callKills lendPlain p₁ a₁ x
                    · simp only [hk1, ↓reduceIte] at h1; cases h1
                    · have hlv0 := (huniq0 b hdu hcv).2.1 x hx
                      have hcs : callShares lendPlain p' a' x := ⟨Or.inl hd', hcv', hx'⟩
                      have hs1 : (∃ p₁ i₁ a₁, (p₁, i₁) ∈ done ∧ avs[i₁]? = some (some a₁) ∧ callShares lendPlain p₁ a₁ x) ∧ σ.st[x]? = some .live :=
                        ⟨⟨p', i', a', hm', hav', hcs⟩, hlv0⟩
                      simp only [hk1, hs1, and_self, ↓reduceIte] at h1; cases h1
                  | once =>
                    by_cases hk1 : ∃ p₁ i₁ a₁, (p₁, i₁) ∈ done ∧ avs[i₁]? = some (some a₁) ∧ callKills lendPlain p₁ a₁ x
                    · simp only [hk1, ↓reduceIte] at h1; cases h1
                    · have hlv0 := (huniq0 b hdu hcv).2.1 x hx
                      have hcs : callShares lendPlain p' a' x := ⟨Or.inr hd', hcv', hx'⟩
                      have hs1 : (∃ p₁ i₁ a₁, (p₁, i₁) ∈ done ∧ avs[i₁]? = some (some a₁) ∧ callShares lendPlain p₁ a₁ x) ∧ σ.st[x]? = some .live :=
                        ⟨⟨p', i', a', hm', hav', hcs⟩, hlv0⟩
                      simp only [hk1, hs1, and_self, ↓reduceIte] at h1; cases h1
                refine ⟨hstepsF, hokF, hleS.trans hleF, hszStF.trans hszSt, honceF.trans honce,
                  hszSpF.trans hszSp, hregF.trans hreg, hnrF.trans hnr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · intro p' i' a' hm hav'
                  rcases List.mem_append.mp hm with h1 | h2
                  · exact hdone p' i' a' h1 hav'
                  · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
                    exact ⟨hvd0, honce0, hnonOnce0, huniq0, hrepU⟩
                · intro p₁ i₁ p₂ i₂ a₁ a₂ hlt12 hm₁ hav₁ hm₂ hav₂
                  rcases List.mem_append.mp hm₁ with h1 | h1
                  · rcases List.mem_append.mp hm₂ with h2 | h2
                    · exact hord p₁ i₁ p₂ i₂ a₁ a₂ hlt12 h1 hav₁ h2 hav₂
                    · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav₂; cases hav₂
                      exact ⟨fun x hkill hx => hnoKillPrev x hx ⟨p₁, i₁, a₁, h1, hav₁, hkill⟩,
                        fun b hdu hcv hneL hcv₁ x hx => hnoPrevNonLendVal b hdu hcv p₁ i₁ a₁ h1 hav₁ hneL hcv₁ x hx,
                        fun hdo x hx ho => hnoPrevOnceDep hdo x hx ho p₁ i₁ a₁ h1 hav₁⟩
                  · simp at h1; rcases h1 with ⟨rfl, rfl⟩
                    rcases List.mem_append.mp hm₂ with h2 | h2
                    · have hlt21 : i₂ < i₁ := hltDone (p₂, i₂) h2
                      omega
                    · simp at h2; omega
                · intro x; rw [hdsAcc]
                  cases hcv : (a.cls == .val) with
                  | false =>
                    have hneV : a.cls ≠ .val := fun heq => by rw [heq] at hcv; cases hcv
                    simp only [Bool.false_eq_true, ↓reduceIte, hds x]
                    constructor
                    · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                    · rintro ⟨p', i', a', hm, hav', hc', hx'⟩
                      rcases List.mem_append.mp hm with h1 | h2
                      · exact ⟨p', i', a', h1, hav', hc', hx'⟩
                      · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact absurd hc' hneV
                  | true =>
                    have hcvEq : a.cls = .val := by
                      cases hc : a.cls <;> try rfl
                      all_goals (rw [hc] at hcv; cases hcv)
                    simp only [↓reduceIte, mem_natUnion, hds x]
                    constructor
                    · rintro (⟨p', i', a', hm, rest⟩ | hx)
                      · exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                      · exact ⟨p, i, a, List.mem_append_right _ (by simp), havi, hcvEq, hx⟩
                    · rintro ⟨p', i', a', hm, hav', hc', hx⟩
                      rcases List.mem_append.mp hm with h1 | h2
                      · exact Or.inl ⟨p', i', a', h1, hav', hc', hx⟩
                      · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact Or.inr hx
                · intro x; rw [hsdsAcc]
                  cases hdEq : destOf p lendPlain with
                  | share =>
                    dsimp only; rw [mem_natUnion, hsds x]
                    constructor
                    · rintro (⟨p', i', a', hm, rest⟩ | hx)
                      · exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                      · exact ⟨p, i, a, List.mem_append_right _ (by simp), havi, hdEq, hx⟩
                    · rintro ⟨p', i', a', hm, hav', hsh', hx⟩
                      rcases List.mem_append.mp hm with h1 | h2
                      · exact Or.inl ⟨p', i', a', h1, hav', hsh', hx⟩
                      · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact Or.inr hx
                  | lend | once | uniq _ =>
                    dsimp only; rw [hsds x]
                    constructor
                    · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                    · rintro ⟨p', i', a', hm, hav', hsh', hx⟩
                      rcases List.mem_append.mp hm with h1 | h2
                      · exact ⟨p', i', a', h1, hav', hsh', hx⟩
                      · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [hdEq] at hsh'; cases hsh'
                · intro r; rw [hrsAcc, mem_natUnion, hrs r]
                  constructor
                  · rintro (⟨p', i', a', hm, hr⟩ | hr)
                    · exact ⟨p', i', a', List.mem_append_left _ hm, hr⟩
                    · exact ⟨p, i, a, List.mem_append_right _ (by simp), havi, hr⟩
                  · rintro ⟨p', i', a', hm, hav', hr⟩
                    rcases List.mem_append.mp hm with h1 | h2
                    · exact Or.inl ⟨p', i', a', h1, hav', hr⟩
                    · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact Or.inr hr
                · intro x hx
                  rw [hspF x (by rw [hszSp]; exact hx)]; simp only [honce]; rw [hspS x hx]
                  by_cases hcNew : x ∈ a.deps ∧ σ.once[x]? = some true
                  · have hcAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true :=
                      ⟨⟨p, i, a, List.mem_append_right _ (by simp), havi, hcNew.1⟩, hcNew.2⟩
                    simp only [hcNew, hcAll, and_self, ↓reduceIte]
                  · simp only [hcNew, ↓reduceIte]
                    by_cases hcOld : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true
                    · have hcAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true :=
                        ⟨let ⟨p', i', a', hm, rest⟩ := hcOld.1; ⟨p', i', a', List.mem_append_left _ hm, rest⟩, hcOld.2⟩
                      simp only [hcOld, hcAll, and_self, ↓reduceIte]
                    · have hnotAll : ¬ ((∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ x ∈ a'.deps) ∧ σ.once[x]? = some true) := by
                        rintro ⟨⟨p', i', a', hm, hav', hx'⟩, ho⟩
                        rcases List.mem_append.mp hm with h1 | h2
                        · exact hcOld ⟨⟨p', i', a', h1, hav', hx'⟩, ho⟩
                        · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'; exact hcNew ⟨hx', ho⟩
                      simp only [hcOld, hnotAll, ↓reduceIte]
                · intro x hx
                  have hxS : x < s.st.size := by rw [hszSt]; exact hx
                  cases hdEq : d with
                  | lend =>
                    rw [hstLendF hdEq, hstS x hx]
                    have hdEq' : destOf p lendPlain = .lend := hdEq
                    have heq1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) ↔
                        (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) := by
                      constructor
                      · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                      · rintro ⟨p', i', a', hm, hav', hk⟩
                        rcases List.mem_append.mp hm with h1 | h2
                        · exact ⟨p', i', a', h1, hav', hk⟩
                        · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rcases hk with ⟨_, hu, _⟩ | ⟨ho, _⟩
                          · rw [hdEq'] at hu; cases hu
                          · rw [hdEq'] at ho; cases ho
                    have heq2 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ↔
                        (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) := by
                      constructor
                      · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                      · rintro ⟨p', i', a', hm, hav', hsh⟩
                        rcases List.mem_append.mp hm with h1 | h2
                        · exact ⟨p', i', a', h1, hav', hsh⟩
                        · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rcases hsh.1 with hs | ho
                          · rw [hdEq'] at hs; cases hs
                          · rw [hdEq'] at ho; cases ho
                    simp only [heq1, heq2]
                  | share =>
                    rw [hstShF hdEq x hxS]; simp only [hstS x hx]
                    have hdEq' : destOf p lendPlain = .share := hdEq
                    have heq1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) ↔
                        (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) := by
                      constructor
                      · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                      · rintro ⟨p', i', a', hm, hav', hk⟩
                        rcases List.mem_append.mp hm with h1 | h2
                        · exact ⟨p', i', a', h1, hav', hk⟩
                        · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rcases hk with ⟨_, hu, _⟩ | ⟨ho, _⟩
                          · rw [hdEq'] at hu; cases hu
                          · rw [hdEq'] at ho; cases ho
                    by_cases hk1 : ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x
                    · have hk1' := heq1.mp hk1
                      simp only [hk1, hk1', ↓reduceIte, Option.some.injEq, reduceCtorEq, and_false]
                    · have hk1' : ¬ (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) :=
                        fun h => hk1 (heq1.mpr h)
                      simp only [hk1, hk1', ↓reduceIte]
                      by_cases hsOld : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ∧ σ.st[x]? = some .live
                      · have hsAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ∧ σ.st[x]? = some .live :=
                          ⟨let ⟨p', i', a', hm, rest⟩ := hsOld.1; ⟨p', i', a', List.mem_append_left _ hm, rest⟩, hsOld.2⟩
                        simp only [hsOld, hsAll, and_self, ↓reduceIte, Option.some.injEq, reduceCtorEq, and_false]
                      · simp only [hsOld, ↓reduceIte]
                        by_cases hsNew : a.cls = .val ∧ x ∈ a.deps ∧ σ.st[x]? = some .live
                        · have hsAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ∧ σ.st[x]? = some .live :=
                            ⟨⟨p, i, a, List.mem_append_right _ (by simp), havi, ⟨Or.inl hdEq, hsNew.1, hsNew.2.1⟩⟩, hsNew.2.2⟩
                          simp only [hsNew, hsAll, and_self, ↓reduceIte]
                        · have hnotAll : ¬ ((∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ∧ σ.st[x]? = some .live) := by
                            rintro ⟨⟨p', i', a', hm, hav', hsh'⟩, hlv⟩
                            rcases List.mem_append.mp hm with h1 | h2
                            · exact hsOld ⟨⟨p', i', a', h1, hav', hsh'⟩, hlv⟩
                            · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
                              exact hsNew ⟨hsh'.2.1, hsh'.2.2, hlv⟩
                          simp only [hsNew, hnotAll, ↓reduceIte]
                  | once =>
                    rw [hstOnceF hdEq x hxS]; simp only [hstS x hx]
                    have hdEq' : destOf p lendPlain = .once := hdEq
                    by_cases hkNew : a.onceOnly = true ∧ a.src = some x
                    · have hkAll : ∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x :=
                        ⟨p, i, a, List.mem_append_right _ (by simp), havi, Or.inr ⟨hdEq, hkNew.1, hkNew.2⟩⟩
                      simp only [hkNew, hkAll, and_self, ↓reduceIte]
                    · simp only [hkNew, ↓reduceIte]
                      have heq1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) ↔
                          (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) := by
                        constructor
                        · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                        · rintro ⟨p', i', a', hm, hav', hk⟩
                          rcases List.mem_append.mp hm with h1 | h2
                          · exact ⟨p', i', a', h1, hav', hk⟩
                          · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
                            rcases hk with ⟨_, hu, _⟩ | ⟨_, hoo', hsrc'⟩
                            · rw [hdEq'] at hu; cases hu
                            · exact absurd ⟨hoo', hsrc'⟩ hkNew
                      by_cases hk1 : ∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x
                      · have hk1' := heq1.mp hk1
                        simp only [hk1, hk1', ↓reduceIte, Option.some.injEq, reduceCtorEq, and_false]
                      · have hk1' : ¬ (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) :=
                          fun h => hk1 (heq1.mpr h)
                        simp only [hk1, hk1', ↓reduceIte]
                        by_cases hsOld : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ∧ σ.st[x]? = some .live
                        · have hsAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ∧ σ.st[x]? = some .live :=
                            ⟨let ⟨p', i', a', hm, rest⟩ := hsOld.1; ⟨p', i', a', List.mem_append_left _ hm, rest⟩, hsOld.2⟩
                          simp only [hsOld, hsAll, and_self, ↓reduceIte, Option.some.injEq, reduceCtorEq, and_false]
                        · simp only [hsOld, ↓reduceIte]
                          by_cases hsNew : a.cls = .val ∧ x ∈ a.deps ∧ σ.st[x]? = some .live
                          · have hsAll : (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ∧ σ.st[x]? = some .live :=
                              ⟨⟨p, i, a, List.mem_append_right _ (by simp), havi, ⟨Or.inr hdEq, hsNew.1, hsNew.2.1⟩⟩, hsNew.2.2⟩
                            simp only [hsNew, hsAll, and_self, ↓reduceIte]
                          · have hnotAll : ¬ ((∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ∧ σ.st[x]? = some .live) := by
                              rintro ⟨⟨p', i', a', hm, hav', hsh'⟩, hlv⟩
                              rcases List.mem_append.mp hm with h1 | h2
                              · exact hsOld ⟨⟨p', i', a', h1, hav', hsh'⟩, hlv⟩
                              · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
                                exact hsNew ⟨hsh'.2.1, hsh'.2.2, hlv⟩
                            simp only [hsNew, hnotAll, ↓reduceIte]
                  | uniq b =>
                    have hstU := (huniqF b hdEq).2 x hxS
                    dsimp only [AState.ofCSt] at hstU
                    rw [hstU, hstS x hx]
                    have hdEq' : destOf p lendPlain = .uniq b := hdEq
                    by_cases hkNew : a.cls = .val ∧ x ∈ a.deps
                    · have hkAll : ∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x :=
                        ⟨p, i, a, List.mem_append_right _ (by simp), havi, Or.inl ⟨b, hdEq, hkNew.1, hkNew.2⟩⟩
                      simp only [hkNew, hkAll, and_self, ↓reduceIte]
                    · simp only [hkNew, ↓reduceIte]
                      have heq1 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) ↔
                          (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x) := by
                        constructor
                        · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                        · rintro ⟨p', i', a', hm, hav', hk⟩
                          rcases List.mem_append.mp hm with h1 | h2
                          · exact ⟨p', i', a', h1, hav', hk⟩
                          · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rw [havi] at hav'; cases hav'
                            rcases hk with ⟨_, _, hcv', hx'⟩ | ⟨ho, _⟩
                            · exact absurd ⟨hcv', hx'⟩ hkNew
                            · rw [hdEq'] at ho; cases ho
                      have heq2 : (∃ p' i' a', (p', i') ∈ done ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) ↔
                          (∃ p' i' a', (p', i') ∈ done ++ [(p, i)] ∧ avs[i']? = some (some a') ∧ callShares lendPlain p' a' x) := by
                        constructor
                        · rintro ⟨p', i', a', hm, rest⟩; exact ⟨p', i', a', List.mem_append_left _ hm, rest⟩
                        · rintro ⟨p', i', a', hm, hav', hsh⟩
                          rcases List.mem_append.mp hm with h1 | h2
                          · exact ⟨p', i', a', h1, hav', hsh⟩
                          · simp at h2; rcases h2 with ⟨rfl, rfl⟩; rcases hsh.1 with hs | ho
                            · rw [hdEq'] at hs; cases hs
                            · rw [hdEq'] at ho; cases ho
                      simp only [heq1, heq2])
        (fun _ piPair _ _ _ _ _ _ hfx => by
          rcases piPair with ⟨p, i⟩; dsimp only at hfx
          cases havi : avs[i]? with
          | none => simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
          | some opta => cases opta with
            | none => simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
            | some a =>
              simp only [havi] at hfx; rw [CM_bind_run] at hfx
              cases hfl : (flowTo (destOf p lendPlain) p.skel a w).run _ with
              | error e => rw [hfl] at hfx; cases hfx
              | ok pf =>
                rw [hfl] at hfx; dsimp only at hfx
                by_cases hc : (ifc.res == .unique && ifc.resCls == .val && !a.regs.isEmpty && a.cls != .leaf && p.cls != .leaf) = true
                · simp only [hc, ↓reduceIte] at hfx
                  cases hdEq : destOf p lendPlain with
                  | share | once => rw [hdEq] at hfx; dsimp only at hfx; rw [CM_bind_run, CM_refuseM_run] at hfx; cases hfx
                  | lend | uniq _ =>
                    rw [hdEq] at hfx; dsimp only at hfx
                    cases hcv : (a.cls == .val) <;>
                      (simp only [hcv, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_pure_run] at hfx; cases hfx)
                · have hcf := Bool.eq_false_iff.mpr hc
                  simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hfx
                  cases hdEq : destOf p lendPlain <;> (rw [hdEq] at hfx; dsimp only at hfx) <;>
                    (cases hcv : (a.cls == .val) <;>
                      (simp only [hcv, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_pure_run] at hfx; cases hfx)))
        ifc.params.toList.zipIdx [] ([], [], []) (deps, sdeps, regs) (σ.toCSt 0) s1
        (by simpa using list_zipIdx_pairwise_lt ifc.params.toList 0) hinv0 hl1
      simp only [List.nil_append] at hinv1
      -- Pass 2 (Bug #9b): read-only `.lend` `valid` loop
      have hpass2 : s1 = s2 ∧
          ∀ p i a, (p, i) ∈ ifc.params.toList.zipIdx → destOf p lendPlain = .lend →
            avs[i]? = some (some a) → ValidDeps (AState.ofCSt s1) a.deps := by
        have hchk := CM_forIn_unit_check
          (P := fun (pi : Param × Nat) (st : CSt) =>
            destOf pi.1 lendPlain = .lend → ∀ a, avs[pi.2]? = some (some a) →
              ValidDeps (AState.ofCSt st) a.deps)
          (fun pi st => by
            rcases pi with ⟨p, i⟩
            refine ⟨fun st1 hfx => ?_, fun st1 hfx => ?_⟩
            · cases hd : destOf p lendPlain with
              | share | once | uniq _ =>
                rw [hd] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
                exact ⟨rfl, fun h => by cases h⟩
              | lend =>
                rw [hd] at hfx; dsimp only at hfx
                cases havi : avs[i]? with
                | none =>
                  simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
                  exact ⟨rfl, fun _ _ h => (by cases h)⟩
                | some opta => cases opta with
                  | none =>
                    simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
                    exact ⟨rfl, fun _ _ h => (by cases h)⟩
                  | some a =>
                    simp only [havi] at hfx; rw [CM_bind_run] at hfx
                    cases hval : (valid a w).run st with
                    | error e => rw [hval] at hfx; cases hfx
                    | ok pv =>
                      rcases pv with ⟨⟨⟩, sv⟩
                      obtain ⟨hsvEq, hvd⟩ := CM_valid_ok hval
                      rw [hval, hsvEq] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
                      exact ⟨rfl, fun _ a' ha' => by cases ha'; exact hvd⟩
            · cases hd : destOf p lendPlain with
              | share | once | uniq _ =>
                rw [hd] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx
              | lend =>
                rw [hd] at hfx; dsimp only at hfx
                cases havi : avs[i]? with
                | none => simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
                | some opta => cases opta with
                  | none => simp only [havi] at hfx; rw [CM_pure_run] at hfx; cases hfx
                  | some a =>
                    simp only [havi] at hfx; rw [CM_bind_run] at hfx
                    cases hval : (valid a w).run st with
                    | error e => rw [hval] at hfx; cases hfx
                    | ok pv =>
                      rcases pv with ⟨⟨⟩, sv⟩
                      rw [hval] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx)
          ifc.params.toList.zipIdx s1 s2 hl2
        exact ⟨hchk.2.symm, fun p i a hm hdl hav => hchk.1 (p, i) hm hdl a hav⟩
      rcases hpass2 with ⟨rfl, hlendValid⟩
      -- Extract final `res` and `s1 = σ'.toCSt 0`
      obtain ⟨hsteps1, hok1, hle1, hszSt1, honce1, hszSp1, hreg1, hnr1, hdone1, hord1, hds1, hsds1, hrs1, hsp1, hst1⟩ := hinv1
      have hret :
          s1 = σ'.toCSt 0 ∧
          res.cls = ifc.resCls ∧ res.skel = ifc.resSkel ∧ res.onceOnly = false ∧ res.src = none ∧
          (ifc.resCls = .irr ∨ ifc.resCls = .imm → res = { cls := ifc.resCls, skel := ifc.resSkel }) ∧
          (ifc.resCls = .leaf → res = { cls := .leaf, skel := ifc.resSkel, own := if ifc.res.isUnique then .uniq else .shared }) ∧
          (ifc.resCls = .val →
            (ifc.res = .unique → res = { cls := .val, own := .uniq, skel := ifc.resSkel }) ∧
            (ifc.res = .uniqueBorrowed → res = { cls := .val, own := .uniq, deps, regs := natUnion regs [s1.regions.headD 1], skel := ifc.resSkel }) ∧
            (ifc.res = .borrowed → res = { cls := .val, deps, regs := natUnion regs [s1.regions.headD 1], skel := ifc.resSkel }) ∧
            (ifc.res = .shared → res = { cls := .val, deps := sdeps, regs, skel := ifc.resSkel })) := by
        cases hrc : ifc.resCls with
        | irr =>
          have h1 : (Cls.irr == Cls.irr || Cls.irr == Cls.imm) = true := rfl
          simp only [hrc, h1, ↓reduceIte] at h; rw [CM_pure_run] at h; cases h
          exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun h => (by cases h), fun h => (by cases h)⟩
        | imm =>
          have h1 : (Cls.imm == Cls.irr || Cls.imm == Cls.imm) = true := rfl
          simp only [hrc, h1, ↓reduceIte] at h; rw [CM_pure_run] at h; cases h
          exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun h => (by cases h), fun h => (by cases h)⟩
        | leaf =>
          have h1 : (Cls.leaf == Cls.irr || Cls.leaf == Cls.imm) = false := rfl
          have h2 : (Cls.leaf == Cls.leaf) = true := rfl
          simp only [hrc, h1, h2, Bool.false_eq_true, ↓reduceIte] at h; rw [CM_pure_run] at h; cases h
          cases hrm : ifc.res with
          | unique | uniqueBorrowed | shared | borrowed =>
            exact ⟨rfl, rfl, rfl, rfl, rfl, fun h => (by rcases h with h | h <;> cases h), fun _ => rfl, fun h => (by cases h)⟩
        | val =>
          have h1 : (Cls.val == Cls.irr || Cls.val == Cls.imm) = false := rfl
          have h2 : (Cls.val == Cls.leaf) = false := rfl
          simp only [hrc, h1, h2, Bool.false_eq_true, ↓reduceIte] at h
          rw [CM_bind_run, CM_innermost_run] at h; dsimp only at h
          cases hrm : ifc.res with
          | unique =>
            simp only [hrm] at h; rw [CM_pure_run] at h; cases h
            exact ⟨rfl, rfl, rfl, rfl, rfl, fun h => (by rcases h with h | h <;> cases h), fun h => (by cases h),
              fun _ => ⟨fun _ => rfl, fun h => (by cases h), fun h => (by cases h), fun h => (by cases h)⟩⟩
          | uniqueBorrowed =>
            simp only [hrm] at h; rw [CM_pure_run] at h; cases h
            exact ⟨rfl, rfl, rfl, rfl, rfl, fun h => (by rcases h with h | h <;> cases h), fun h => (by cases h),
              fun _ => ⟨fun h => (by cases h), fun _ => rfl, fun h => (by cases h), fun h => (by cases h)⟩⟩
          | borrowed =>
            simp only [hrm] at h; rw [CM_pure_run] at h; cases h
            exact ⟨rfl, rfl, rfl, rfl, rfl, fun h => (by rcases h with h | h <;> cases h), fun h => (by cases h),
              fun _ => ⟨fun h => (by cases h), fun h => (by cases h), fun _ => rfl, fun h => (by cases h)⟩⟩
          | shared =>
            simp only [hrm] at h; rw [CM_pure_run] at h; cases h
            exact ⟨rfl, rfl, rfl, rfl, rfl, fun h => (by rcases h with h | h <;> cases h), fun h => (by cases h),
              fun _ => ⟨fun h => (by cases h), fun h => (by cases h), fun h => (by cases h), fun _ => rfl⟩⟩
      obtain ⟨hs1Eq, hclsR, hskelR, hooR, hsrcR, hirrImm, hleaf, hvalR⟩ := hret
      subst hs1Eq
      dsimp only [AState.ofCSt, AState.toCSt] at hok1 hle1 hszSt1 honce1 hszSp1 hreg1 hnr1 hsp1 hst1 hlendValid
      refine ⟨by simpa [AState.ofCSt_toCSt] using hok1, by simpa [AState.ofCSt_toCSt] using hle1,
        hszSt1, honce1, hszSp1, hreg1, hnr1, hclsR, hskelR, hooR, hsrcR, ?_, ?_, hirrImm, hleaf, ?_, ?_, ?_⟩
      · intro i p a hp hav
        exact hdone1 p i a (mem_array_zipIdx_iff.mpr hp) hav
      · intro i j pi pj ai aj hne hpi hai hpj haj
        have hmi := mem_array_zipIdx_iff.mpr hpi
        have hmj := mem_array_zipIdx_iff.mpr hpj
        refine ⟨?_, ?_, ?_⟩
        · intro b hdu hcv hcond x hx hx'
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
          · exact (hord1 pi i pj j ai aj hlt hmi hai hmj haj).1 x (Or.inl ⟨b, hdu, hcv, hx⟩) hx'
          · rcases hcond with hlt | hdl | hcvj
            · omega
            · have ⟨hltJ, hneDead⟩ := hlendValid pj j aj hmj hdl haj x hx'
              have h1 := hst1 x (by rw [← hszSt1]; exact hltJ)
              have hk : ∃ p' i' a', (p', i') ∈ ifc.params.toList.zipIdx ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x :=
                ⟨pi, i, ai, hmi, hai, Or.inl ⟨b, hdu, hcv, hx⟩⟩
              simp only [hk, ↓reduceIte] at h1
              exact hneDead h1
            · by_cases hdl : destOf pj lendPlain = .lend
              · have ⟨hltJ, hneDead⟩ := hlendValid pj j aj hmj hdl haj x hx'
                have h1 := hst1 x (by rw [← hszSt1]; exact hltJ)
                have hk : ∃ p' i' a', (p', i') ∈ ifc.params.toList.zipIdx ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x :=
                  ⟨pi, i, ai, hmi, hai, Or.inl ⟨b, hdu, hcv, hx⟩⟩
                simp only [hk, ↓reduceIte] at h1
                exact hneDead h1
              · exact (hord1 pj j pi i aj ai hgt hmj haj hmi hai).2.1 b hdu hcv hdl hcvj x hx hx'
        · intro hdo hoo x hsrc hcond hx'
          rcases hcond with hlt | hdl
          · exact (hord1 pi i pj j ai aj hlt hmi hai hmj haj).1 x (Or.inr ⟨hdo, hoo, hsrc⟩) hx'
          · have ⟨hltJ, hneDead⟩ := hlendValid pj j aj hmj hdl haj x hx'
            have h1 := hst1 x (by rw [← hszSt1]; exact hltJ)
            have hk : ∃ p' i' a', (p', i') ∈ ifc.params.toList.zipIdx ∧ avs[i']? = some (some a') ∧ callKills lendPlain p' a' x :=
              ⟨pi, i, ai, hmi, hai, Or.inr ⟨hdo, hoo, hsrc⟩⟩
            simp only [hk, ↓reduceIte] at h1
            exact hneDead h1
        · intro hlt hdo x hx ho
          exact (hord1 pi i pj j ai aj hlt hmi hai hmj haj).2.2 hdo x hx ho
      · intro hrc
        obtain ⟨hu, hub, hb, hsh⟩ := hvalR hrc
        have hlpF : lendPlain = false := by dsimp [lendPlain]; rw [hrc]; rfl
        have hds' : ∀ d, d ∈ deps ↔ ∃ (i : Nat) (p : Param) (a : AVal),
            ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ a.cls = .val ∧ d ∈ a.deps := by
          intro d; rw [hds1 d]; constructor
          · rintro ⟨p, i, a, hm, rest⟩; exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
          · rintro ⟨i, p, a, hp, rest⟩; exact ⟨p, i, a, mem_array_zipIdx_iff.mpr hp, rest⟩
        have hsds' : ∀ d, d ∈ sdeps ↔ ∃ (i : Nat) (p : Param) (a : AVal),
            ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ destOf p false = .share ∧ d ∈ a.deps := by
          intro d; rw [hsds1 d, hlpF]; constructor
          · rintro ⟨p, i, a, hm, rest⟩; exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
          · rintro ⟨i, p, a, hp, rest⟩; exact ⟨p, i, a, mem_array_zipIdx_iff.mpr hp, rest⟩
        have hrs' : ∀ r, r ∈ regs ↔ ∃ (i : Nat) (p : Param) (a : AVal),
            ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ r ∈ a.regs := by
          intro r; rw [hrs1 r]; constructor
          · rintro ⟨p, i, a, hm, rest⟩; exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
          · rintro ⟨i, p, a, hp, rest⟩; exact ⟨p, i, a, mem_array_zipIdx_iff.mpr hp, rest⟩
        refine ⟨hu, ?_, ?_, ?_⟩
        · intro hrm; rw [hub hrm]; dsimp only [AState.toCSt]; simp only [hreg1, mem_natUnion, List.mem_singleton, hds', hrs']
          exact ⟨trivial, fun _ => trivial, fun r => or_comm⟩
        · intro hrm; rw [hb hrm]; dsimp only [AState.toCSt]; simp only [hreg1, mem_natUnion, List.mem_singleton, hds', hrs']
          exact ⟨trivial, fun _ => trivial, fun r => or_comm⟩
        · intro hrm; rw [hsh hrm]; exact ⟨rfl, hsds', hrs'⟩
      · intro x hx; rw [hsp1 x hx]
        have heq : (∃ p i a, (p, i) ∈ ifc.params.toList.zipIdx ∧ avs[i]? = some (some a) ∧ x ∈ a.deps) ↔
            (∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ x ∈ a.deps) := by
          constructor
          · rintro ⟨p, i, a, hm, rest⟩; exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
          · rintro ⟨i, p, a, hp, rest⟩; exact ⟨p, i, a, mem_array_zipIdx_iff.mpr hp, rest⟩
        simp only [heq]
      · intro x hx; rw [hst1 x hx]
        have heq1 : (∃ p i a, (p, i) ∈ ifc.params.toList.zipIdx ∧ avs[i]? = some (some a) ∧ callKills lendPlain p a x) ↔
            (∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ callKills lendPlain p a x) := by
          constructor
          · rintro ⟨p, i, a, hm, rest⟩; exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
          · rintro ⟨i, p, a, hp, rest⟩; exact ⟨p, i, a, mem_array_zipIdx_iff.mpr hp, rest⟩
        have heq2 : (∃ p i a, (p, i) ∈ ifc.params.toList.zipIdx ∧ avs[i]? = some (some a) ∧ callShares lendPlain p a x) ↔
            (∃ (i : Nat) (p : Param) (a : AVal), ifc.params[i]? = some p ∧ avs[i]? = some (some a) ∧ callShares lendPlain p a x) := by
          constructor
          · rintro ⟨p, i, a, hm, rest⟩; exact ⟨i, p, a, mem_array_zipIdx_iff.mp hm, rest⟩
          · rintro ⟨i, p, a, hp, rest⟩; exact ⟨p, i, a, mem_array_zipIdx_iff.mpr hp, rest⟩
        simp only [heq1, heq2]

/-- Complete unpacking of `Check.applyValue` (`Runs (applyValue f a c w) σ res σ'`). -/
theorem Runs_applyValue {f a : AVal} {c : Cls} {w : String} {σ σ' : AState} {res : AVal}
    (hok : AStateOk σ) (h : Runs (applyValue f a c w) σ res σ') :
    let (m, dom, resM, cod) := arrowParts f.skel
    let p : Param := { mode := m, cls := a.cls, skel := dom }
    let d := destOf p (c != .val)
    AStateOk σ' ∧ AStateLe σ σ' ∧
    σ'.st.size = σ.st.size ∧ σ'.once = σ.once ∧ σ'.spent.size = σ.spent.size ∧
    σ'.regions = σ.regions ∧ σ'.nextRegion = σ.nextRegion ∧
    ValidDeps σ f.deps ∧
    UnspentOnceDeps σ f.deps ∧
    ValidDeps σ a.deps ∧
    (d = .once → dom.admitsNA a.skel = true ∧ UnspentOnceDeps σ a.deps ∧
      ∀ x ∈ a.deps, σ.once[x]? = some true → x ∉ f.deps) ∧
    (d ≠ .once → dom.admits a.skel = true ∧ a.onceOnly = false ∧ ¬ IsOnceSrc σ a) ∧
    (∀ b, d = .uniq b → a.cls = .val →
      a.own = .uniq ∧ (∀ x ∈ a.deps, σ.st[x]? = some .live) ∧ (b = false → a.regs = []) ∧
      (∀ x ∈ a.deps, x ∉ f.deps)) ∧
    (d = .once → a.onceOnly = true → ∀ x, a.src = some x → x ∉ f.deps) ∧
    (resM = .unique → c = .val → a.cls ≠ .leaf → (d = .share ∨ d = .once) → a.regs = []) ∧
    res.cls = c ∧ res.skel = cod ∧ res.src = none ∧
    (res.onceOnly = true ↔ c = .val ∧ mayBePap cod = true ∧
      (f.onceOnly = true ∨ (∃ x ∈ f.deps, σ.once[x]? = some true) ∨ m.isUnique = true ∨ m.usage = .once)) ∧
    (c = .val →
      (resM = .unique → res.own = .uniq ∧ (∀ x, x ∈ res.deps ↔ x ∈ f.deps ∨ x ∈ a.deps) ∧
        (∀ r, r ∈ res.regs ↔ r ∈ f.regs)) ∧
      (resM = .uniqueBorrowed → res.own = .uniq ∧ (∀ x, x ∈ res.deps ↔ x ∈ f.deps ∨ x ∈ a.deps) ∧
        (∀ r, r ∈ res.regs ↔ r = σ.regions.headD 1 ∨ r ∈ f.regs ∨ r ∈ a.regs)) ∧
      (resM = .borrowed → res.own = .shared ∧ (∀ x, x ∈ res.deps ↔ x ∈ f.deps ∨ x ∈ a.deps) ∧
        (∀ r, r ∈ res.regs ↔ r = σ.regions.headD 1 ∨ r ∈ f.regs ∨ r ∈ a.regs)) ∧
      (resM = .shared → res.own = .shared ∧ (∀ x, x ∈ res.deps ↔ x ∈ f.deps ∨ x ∈ a.deps) ∧
        (∀ r, r ∈ res.regs ↔ r ∈ f.regs ∨ r ∈ a.regs))) ∧
    (c ≠ .val → res.deps = [] ∧ res.regs = []) ∧
    (∀ x, x < σ.spent.size →
      σ'.spent[x]? = if (x ∈ f.deps ∨ x ∈ a.deps) ∧ σ.once[x]? = some true
        then some true else σ.spent[x]?) ∧
    (∀ x, x < σ.st.size →
      σ'.st[x]? =
        if (f.onceOnly = true ∧ f.src = some x) ∨ callKills (c != .val) p a x
        then some .dead
        else if callShares (c != .val) p a x ∧ σ.st[x]? = some .live
        then some .shared
        else σ.st[x]?) := by
  rcases hap : arrowParts f.skel with ⟨m, dom, resM, cod⟩
  dsimp only
  let p : Param := { mode := m, cls := a.cls, skel := dom }
  let d := destOf p (c != .val)
  unfold Runs applyValue at h
  rw [CM_bind_run] at h
  cases hvf1 : (valid f w).run (σ.toCSt 0) with
  | error e => rw [hvf1] at h; cases h
  | ok pv1 =>
    rcases pv1 with ⟨⟨⟩, sv1⟩
    obtain ⟨hsv1Eq, hvdF⟩ := CM_valid_ok hvf1
    dsimp only [AState.toCSt] at hvdF
    rw [hvf1, hsv1Eq] at h; dsimp only at h
    -- Loop 1: check and mark once-deps of `f.deps`
    rw [CM_bind_run] at h
    cases hl : StateT.run (forIn (m := CM) f.deps false _) (σ.toCSt 0) with
    | error e => rw [hl] at h; cases h
    | ok pl =>
      rcases pl with ⟨fHasOnceDep, s1⟩
      rw [hl] at h; dsimp only at h
      let InvF : List Nat → Bool → CSt → Prop := fun done flag s =>
        s.steps = 0 ∧ s.st = σ.st ∧ s.once = σ.once ∧ s.spent.size = σ.spent.size ∧
        s.regions = σ.regions ∧ s.nextRegion = σ.nextRegion ∧
        (flag = true ↔ ∃ x ∈ done, σ.once[x]? = some true) ∧
        (∀ x ∈ done, σ.once[x]? = some true → σ.spent[x]? = some false) ∧
        (∀ i, i < σ.spent.size →
          s.spent[i]? = if i ∈ done ∧ σ.once[i]? = some true then some true else σ.spent[i]?)
      have hinvF0 : InvF [] false (σ.toCSt 0) :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp, fun _ hm => (by cases hm), fun _ _ => by simp [AState.toCSt]⟩
      have hinvF := CM_forIn_list_prefix InvF
        (fun done x flag s flag' s' hI hfx => by
          obtain ⟨hsteps, hst, honce, hszSp, hreg, hnr, hflIff, hunsp, hspS⟩ := hI
          rw [CM_bind_run, CM_isOnceBnd_run] at hfx; dsimp only at hfx
          cases ho : s.once[x]? with
          | none =>
            simp only [ho, Option.getD_none, Bool.false_eq_true, ↓reduceIte] at hfx
            rw [CM_pure_run] at hfx; cases hfx
            have ho0 : σ.once[x]? = none := by rw [← honce]; exact ho
            refine ⟨hsteps, hst, honce, hszSp, hreg, hnr, ?_, ?_, ?_⟩
            · rw [hflIff]; constructor
              · rintro ⟨y, hy, hoy⟩; exact ⟨y, List.mem_append_left _ hy, hoy⟩
              · rintro ⟨y, hy, hoy⟩
                rcases List.mem_append.mp hy with h1 | h2
                · exact ⟨y, h1, hoy⟩
                · simp at h2; subst h2; rw [ho0] at hoy; cases hoy
            · intro y hy hoy
              rcases List.mem_append.mp hy with h1 | h2
              · exact hunsp y h1 hoy
              · simp at h2; subst h2; rw [ho0] at hoy; cases hoy
            · intro i hi; rw [hspS i hi]
              by_cases hix : i = x
              · subst hix; simp [ho0]
              · have heq : (i ∈ done) ↔ (i ∈ done ++ [x]) := by simp [hix]
                simp only [heq]
          | some b =>
            cases b with
            | false =>
              simp only [ho, Option.getD_some, Bool.false_eq_true, ↓reduceIte] at hfx
              rw [CM_pure_run] at hfx; cases hfx
              have ho0 : σ.once[x]? = some false := by rw [← honce]; exact ho
              refine ⟨hsteps, hst, honce, hszSp, hreg, hnr, ?_, ?_, ?_⟩
              · rw [hflIff]; constructor
                · rintro ⟨y, hy, hoy⟩; exact ⟨y, List.mem_append_left _ hy, hoy⟩
                · rintro ⟨y, hy, hoy⟩
                  rcases List.mem_append.mp hy with h1 | h2
                  · exact ⟨y, h1, hoy⟩
                  · simp at h2; subst h2; rw [ho0] at hoy; cases hoy
              · intro y hy hoy
                rcases List.mem_append.mp hy with h1 | h2
                · exact hunsp y h1 hoy
                · simp at h2; subst h2; rw [ho0] at hoy; cases hoy
              · intro i hi; rw [hspS i hi]
                by_cases hix : i = x
                · subst hix; simp [ho0]
                · have heq : (i ∈ done) ↔ (i ∈ done ++ [x]) := by simp [hix]
                  simp only [heq]
            | true =>
              simp only [ho, Option.getD_some, ↓reduceIte] at hfx
              rw [CM_bind_run, CM_isSpent_run] at hfx; dsimp only at hfx
              have ho0 : σ.once[x]? = some true := by rw [← honce]; exact ho
              have hltX : x < σ.spent.size := by
                have hltO : x < σ.once.size :=
                  Nat.lt_of_not_ge fun hge => by rw [Array.getElem?_eq_none hge] at ho0; cases ho0
                have h1 := hok.1; have h2 := hok.2.1; omega
              cases hspX : s.spent[x]? with
              | none => exact absurd (Array.getElem?_eq_none_iff.mp hspX) (Nat.not_le_of_lt (by rw [hszSp]; exact hltX))
              | some sp =>
                cases sp with
                | true =>
                  simp only [hspX, Option.getD_some, ↓reduceIte] at hfx
                  rw [CM_bind_run, CM_refuseM_run] at hfx; cases hfx
                | false =>
                  simp only [hspX, Option.getD_some, Bool.false_eq_true, ↓reduceIte] at hfx
                  rw [CM_bind_run, CM_markSpent_run] at hfx; dsimp only at hfx
                  rw [CM_pure_run] at hfx; cases hfx
                  have hsp0X : σ.spent[x]? = some false := by
                    have h1 := hspS x hltX; rw [hspX] at h1
                    by_cases hxd : x ∈ done
                    · simp only [hxd, ho0, and_self, ↓reduceIte] at h1; cases h1
                    · simp only [hxd, false_and, ↓reduceIte] at h1; exact h1.symm
                  have hsz' : (s.spent.set! x true).size = σ.spent.size := by
                    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hszSp
                  refine ⟨hsteps, hst, honce, hsz', hreg, hnr,
                    ⟨fun _ => ⟨x, List.mem_append_right _ (by simp), ho0⟩, fun _ => rfl⟩, ?_, ?_⟩
                  · intro y hy hoy
                    rcases List.mem_append.mp hy with h1 | h2
                    · exact hunsp y h1 hoy
                    · simp at h2; subst h2; exact hsp0X
                  · intro i hi
                    by_cases hix : i = x
                    · subst hix
                      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]
                      have hiS : i < s.spent.size := by rw [hszSp]; exact hi
                      simp [hiS, ho0]
                    · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hix), hspS i hi]
                      have heq : (i ∈ done) ↔ (i ∈ done ++ [x]) := by simp [hix]
                      simp only [heq])
        (fun _ x _ s _ _ _ hfx => by
          rw [CM_bind_run, CM_isOnceBnd_run] at hfx; dsimp only at hfx
          cases ho : s.once[x]? with
          | none => simp only [ho, Option.getD_none, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_pure_run] at hfx; cases hfx
          | some b => cases b with
            | false => simp only [ho, Option.getD_some, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_pure_run] at hfx; cases hfx
            | true =>
              simp only [ho, Option.getD_some, ↓reduceIte] at hfx; rw [CM_bind_run, CM_isSpent_run] at hfx; dsimp only at hfx
              cases hsp : s.spent[x]?.getD false with
              | true => simp only [hsp, ↓reduceIte] at hfx; rw [CM_bind_run, CM_refuseM_run] at hfx; cases hfx
              | false => simp only [hsp, Bool.false_eq_true, ↓reduceIte] at hfx; rw [CM_bind_run, CM_markSpent_run] at hfx; dsimp only at hfx; rw [CM_pure_run] at hfx; cases hfx)
        f.deps [] false fHasOnceDep (σ.toCSt 0) s1 hinvF0 hl
      simp only [List.nil_append] at hinvF
      obtain ⟨hsteps1, hst1, honce1, hszSp1, hreg1, hnr1, hflagIff, hunspF, hsp1⟩ := hinvF
      -- Build `AStateOk (AState.ofCSt s1)` and `AStateLe σ (AState.ofCSt s1)`
      have ⟨hok1, hle1⟩ := AStateOk_AStateLe_of_pointwise (σ' := AState.ofCSt s1) hok
        (by dsimp [AState.ofCSt]; rw [hst1]) (by dsimp [AState.ofCSt]; exact honce1)
        (by dsimp [AState.ofCSt]; exact hszSp1) (by dsimp [AState.ofCSt]; exact hreg1)
        (by dsimp [AState.ofCSt]; exact hnr1)
        (fun i hi => by dsimp [AState.ofCSt]; rw [hst1, Array.getElem?_eq_getElem hi]; exact BSt.le_refl _)
        (fun i hi hsp => by
          dsimp [AState.ofCSt]; rw [hsp1 i hi]
          by_cases hc : i ∈ f.deps ∧ σ.once[i]? = some true <;> simp [hc, hsp])
      -- Step 2: `callResult` on single-element interface
      let ifc : Iface := { params := #[p], res := resM, resCls := c, resSkel := cod }
      have h' : (do
          let r ← callResult ifc #[some a] w
          valid f w
          if f.onceOnly then
            if let some x := f.src then setSt x BSt.dead
          let regs := if c == Cls.val then natUnion r.regs f.regs else r.regs
          let deps := if c == Cls.val then natUnion (natUnion r.deps f.deps) a.deps else r.deps
          let onceOnly := r.onceOnly ||
            (c == Cls.val && mayBePap cod && (f.onceOnly || fHasOnceDep || m.isUnique || m.usage == Ixon.Usage.once))
          pure { r with cls := c, regs, deps, onceOnly }).run s1 = .ok (res, σ'.toCSt 0) := by
        cases hsk : f.skel <;> rw [hsk] at hap h <;> cases hap <;> exact h
      rw [CM_bind_run] at h'
      cases hcr : (callResult ifc #[some a] w).run s1 with
      | error e => rw [hcr] at h'; cases h'
      | ok pcr =>
        rcases pcr with ⟨r, s2⟩
        rw [hcr] at h'; dsimp only at h'
        -- Step 3 (Bug #9a): `valid f w` on `s2`
        rw [CM_bind_run] at h'
        cases hvf2 : (valid f w).run s2 with
        | error e => rw [hvf2] at h'; cases h'
        | ok pv2 =>
          rcases pv2 with ⟨⟨⟩, sv2⟩
          obtain ⟨hsv2Eq, hvdF2⟩ := CM_valid_ok hvf2
          rw [hvf2, hsv2Eq] at h'; dsimp only at h'
          -- Step 4: `if f.onceOnly then if let some x := f.src then setSt x .dead`
          have hkillStep :
              σ'.st.size = s2.st.size ∧ σ'.once = s2.once ∧ σ'.spent = s2.spent ∧
              σ'.regions = s2.regions ∧ σ'.nextRegion = s2.nextRegion ∧ s2.steps = 0 ∧
              (∀ i, i < s2.st.size →
                σ'.st[i]? = if f.onceOnly = true ∧ f.src = some i then some .dead else s2.st[i]?) ∧
              res = { r with
                cls := c,
                regs := if c == .val then natUnion r.regs f.regs else r.regs,
                deps := if c == .val then natUnion (natUnion r.deps f.deps) a.deps else r.deps,
                onceOnly := r.onceOnly ||
                  (c == .val && mayBePap cod && (f.onceOnly || fHasOnceDep || m.isUnique || m.usage == .once)) } := by
            have h := h'
            cases hfoo : f.onceOnly with
            | false =>
              simp only [hfoo, Bool.false_eq_true, ↓reduceIte] at h
              rw [CM_pure_run] at h
              obtain ⟨hres, hstEq⟩ := Prod.mk.inj (Except.ok.inj h)
              have hs2 : s2 = σ'.toCSt 0 := hstEq
              subst hs2
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => by simp [AState.toCSt], hres.symm⟩
            | true =>
              simp only [hfoo, ↓reduceIte] at h
              cases hfsrc : f.src with
              | none =>
                simp only [hfsrc] at h
                rw [CM_pure_run] at h
                obtain ⟨hres, hstEq⟩ := Prod.mk.inj (Except.ok.inj h)
                have hs2 : s2 = σ'.toCSt 0 := hstEq
                subst hs2
                exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => by simp [AState.toCSt], hres.symm⟩
              | some xf =>
                simp only [hfsrc] at h
                rw [CM_bind_run, CM_setSt_run] at h; dsimp only at h
                rw [CM_pure_run] at h
                obtain ⟨hres, hstEq⟩ := Prod.mk.inj (Except.ok.inj h)
                have hst' : σ'.st = s2.st.set! xf .dead := by
                  have h1 := congrArg CSt.st hstEq; exact h1.symm
                have honce' : σ'.once = s2.once := (congrArg CSt.once hstEq).symm
                have hsp' : σ'.spent = s2.spent := (congrArg CSt.spent hstEq).symm
                have hreg' : σ'.regions = s2.regions := (congrArg CSt.regions hstEq).symm
                have hnr' : σ'.nextRegion = s2.nextRegion := (congrArg CSt.nextRegion hstEq).symm
                have hsteps' : s2.steps = 0 := congrArg CSt.steps hstEq
                have hsz' : σ'.st.size = s2.st.size := by
                  rw [hst', Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
                refine ⟨hsz', honce', hsp', hreg', hnr', hsteps', fun i hi => ?_, hres.symm⟩
                rw [hst', Array.set!_eq_setIfInBounds]
                by_cases hix : i = xf
                · subst hix; rw [Array.getElem?_setIfInBounds_self]; simp [hi]
                · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hix)]
                  have hne : ¬ (some xf = some i) := fun h1 => hix (Option.some.inj h1).symm
                  simp [hne]
          obtain ⟨hszStK, honceK, hspK, hregK, hnrK, hsteps2, hstK, hresEq⟩ := hkillStep
          -- Unpack `Runs_callResult` on `s1 → s2`
          have hcrR : Runs (callResult ifc #[some a] w) (AState.ofCSt s1) r (AState.ofCSt s2) := by
            unfold Runs
            rw [show (AState.ofCSt s1).toCSt 0 = s1 by rw [← hsteps1, AState.toCSt_ofCSt],
                show (AState.ofCSt s2).toCSt 0 = s2 by rw [← hsteps2, AState.toCSt_ofCSt]]
            exact hcr
          obtain ⟨hok2, hle2, hszSt2, honce2, hszSp2, hreg2, hnr2, hclsR, hskelR, hooR, hsrcR,
            hargs2, _, hirrImm2, hleaf2, hval2, hsp2, hst2⟩ := Runs_callResult hok1 hcrR
          dsimp only [AState.ofCSt] at hszSt2 honce2 hszSp2 hreg2 hnr2 hsp2 hst2
          have harg0 := hargs2 0 p a (by simp [ifc]) (by simp)
          obtain ⟨hvdA1, honceA1, hnonOnceA1, huniqA1, hrepUA1⟩ := harg0
          dsimp only [AState.ofCSt] at hvdA1 honceA1 hnonOnceA1 huniqA1
          have hvdA0 : ValidDeps σ a.deps := by
            intro x hx; have ⟨hlt, hne⟩ := hvdA1 x hx; rw [hst1] at hlt hne; exact ⟨hlt, hne⟩
          have hspPt : ∀ x, x < σ.spent.size →
              σ'.spent[x]? = if (x ∈ f.deps ∨ x ∈ a.deps) ∧ σ.once[x]? = some true
                then some true else σ.spent[x]? := by
            intro x hx
            rw [hspK, hsp2 x (by rw [hszSp1]; exact hx)]
            simp only [honce1]
            rw [hsp1 x hx]
            have hex : (∃ (i : Nat) (p' : Param) (a' : AVal), ifc.params[i]? = some p' ∧ (#[some a] : Array (Option AVal))[i]? = some (some a') ∧ x ∈ a'.deps) ↔ x ∈ a.deps := by
              constructor
              · rintro ⟨i, p', a', hp', ha', hx'⟩
                cases i with
                | zero => simp at ha'; subst ha'; exact hx'
                | succ k => simp [ifc] at hp'
              · intro hx'; exact ⟨0, p, a, by simp [ifc], by simp, hx'⟩
            simp only [hex]
            by_cases hxa : x ∈ a.deps ∧ σ.once[x]? = some true
            · simp [hxa.1, hxa.2]
            · by_cases hxf : x ∈ f.deps ∧ σ.once[x]? = some true
              · simp [hxf.1, hxf.2]
              · have hnot : ¬ ((x ∈ f.deps ∨ x ∈ a.deps) ∧ σ.once[x]? = some true) := by
                  rintro ⟨hf | ha, ho⟩
                  · exact hxf ⟨hf, ho⟩
                  · exact hxa ⟨ha, ho⟩
                simp [hxa, hxf, hnot]
          have hst2Pt : ∀ x, x < σ.st.size →
              s2.st[x]? =
                if callKills (c != .val) p a x then some .dead
                else if callShares (c != .val) p a x ∧ σ.st[x]? = some .live then some .shared
                else σ.st[x]? := by
            intro x hx
            rw [hst2 x (by rw [hst1]; exact hx)]; simp only [hst1]
            have hkIff : (∃ (i : Nat) (p' : Param) (a' : AVal), ifc.params[i]? = some p' ∧ (#[some a] : Array (Option AVal))[i]? = some (some a') ∧ callKills (ifc.resCls != .val) p' a' x) ↔
                callKills (c != .val) p a x := by
              constructor
              · rintro ⟨i, p', a', hp', ha', hk⟩
                cases i with
                | zero => simp [ifc] at hp' ha'; rcases hp' with rfl; subst ha'; exact hk
                | succ k => simp [ifc] at hp'
              · intro hk; exact ⟨0, p, a, by simp [ifc], by simp, hk⟩
            have hsIff : (∃ (i : Nat) (p' : Param) (a' : AVal), ifc.params[i]? = some p' ∧ (#[some a] : Array (Option AVal))[i]? = some (some a') ∧ callShares (ifc.resCls != .val) p' a' x) ↔
                callShares (c != .val) p a x := by
              constructor
              · rintro ⟨i, p', a', hp', ha', hs⟩
                cases i with
                | zero => simp [ifc] at hp' ha'; rcases hp' with rfl; subst ha'; exact hs
                | succ k => simp [ifc] at hp'
              · intro hs; exact ⟨0, p, a, by simp [ifc], by simp, hs⟩
            simp only [hkIff, hsIff]
          have hstPt : ∀ x, x < σ.st.size →
              σ'.st[x]? =
                if (f.onceOnly = true ∧ f.src = some x) ∨ callKills (c != .val) p a x
                then some .dead
                else if callShares (c != .val) p a x ∧ σ.st[x]? = some .live
                then some .shared
                else σ.st[x]? := by
            intro x hx
            rw [hstK x (by rw [hszSt2, hst1]; exact hx), hst2Pt x hx]
            by_cases hfK : f.onceOnly = true ∧ f.src = some x
            · simp [hfK]
            · by_cases haK : callKills (c != .val) p a x
              · simp [hfK, haK]
              · simp [hfK, haK]
          have ⟨hok', hle'⟩ := AStateOk_AStateLe_of_pointwise hok
            (by rw [hszStK, hszSt2, hst1]) (honceK.trans (honce2.trans honce1))
            (by rw [hspK, hszSp2]; exact hszSp1) (hregK.trans (hreg2.trans hreg1))
            (hnrK.trans (hnr2.trans hnr1))
            (fun x hx => by
              rw [hstPt x hx]
              cases h0 : σ.st[x]? with
              | none => exact absurd (Array.getElem?_eq_none_iff.mp h0) (Nat.not_le_of_lt hx)
              | some b0 =>
                by_cases hc1 : (f.onceOnly = true ∧ f.src = some x) ∨ callKills (c != .val) p a x
                · simp only [hc1, ↓reduceIte]; cases b0 <;> trivial
                · simp only [hc1, ↓reduceIte]
                  by_cases hc2 : callShares (c != .val) p a x ∧ some b0 = some .live
                  · simp only [hc2, and_self, ↓reduceIte]; cases hc2.2; exact trivial
                  · simp only [hc2, ↓reduceIte]; exact BSt.le_refl b0)
            (fun x hx hsp => by
              rw [hspPt x hx]
              by_cases hc : (x ∈ f.deps ∨ x ∈ a.deps) ∧ σ.once[x]? = some true <;> simp [hc, hsp])
          refine ⟨hok', hle', by rw [hszStK, hszSt2, hst1], honceK.trans (honce2.trans honce1),
            by rw [hspK, hszSp2]; exact hszSp1, hregK.trans (hreg2.trans hreg1),
            hnrK.trans (hnr2.trans hnr1), hvdF, hunspF, hvdA0, ?_, ?_, ?_, ?_, ?_,
            by rw [hresEq], by rw [hresEq]; exact hskelR, by rw [hresEq]; exact hsrcR, ?_, ?_, ?_, hspPt, hstPt⟩
          · intro hdo
            obtain ⟨hadm, hunsp1⟩ := honceA1 hdo
            refine ⟨hadm, fun x hx ho => ?_, fun x hx ho hxf => ?_⟩
            · have hspF1 := hunsp1 x hx (by rw [honce1]; exact ho)
              have hlt : x < σ.spent.size := by have h1 := (hvdA0 x hx).1; have h2 := hok.2.1; omega
              have h1 := hsp1 x hlt; rw [hspF1] at h1
              by_cases hc : x ∈ f.deps ∧ σ.once[x]? = some true
              · simp only [hc, and_self, ↓reduceIte] at h1; cases h1
              · simp only [hc, ↓reduceIte] at h1; exact h1.symm
            · have hspF1 := hunsp1 x hx (by rw [honce1]; exact ho)
              have hlt : x < σ.spent.size := by have h1 := (hvdA0 x hx).1; have h2 := hok.2.1; omega
              have h1 := hsp1 x hlt; simp only [hxf, ho, and_self, ↓reduceIte] at h1
              rw [hspF1] at h1; cases h1
          · intro hne
            obtain ⟨hadm, hoo, hnotOnce1⟩ := hnonOnceA1 hne
            exact ⟨hadm, hoo, fun ⟨id, hs, ho⟩ => hnotOnce1 ⟨id, hs, by dsimp [AState.ofCSt]; rw [honce1]; exact ho⟩⟩
          · intro b hdu hcv
            obtain ⟨hown, hlv1, hregNil⟩ := huniqA1 b hdu hcv
            refine ⟨hown, fun x hx => by have h1 := hlv1 x hx; rw [hst1] at h1; exact h1, hregNil, fun x hx hxf => ?_⟩
            have ⟨hlt2, hneDead⟩ := hvdF2 x hxf
            have h1 := hst2Pt x (by rw [← hst1, ← hszSt2]; exact hlt2)
            have hk : callKills (c != .val) p a x := Or.inl ⟨b, hdu, hcv, hx⟩
            simp only [hk, ↓reduceIte] at h1
            exact hneDead h1
          · intro hdo hoo x hsrc hxf
            have ⟨hlt2, hneDead⟩ := hvdF2 x hxf
            have h1 := hst2Pt x (by rw [← hst1, ← hszSt2]; exact hlt2)
            have hk : callKills (c != .val) p a x := Or.inr ⟨hdo, hoo, hsrc⟩
            simp only [hk, ↓reduceIte] at h1
            exact hneDead h1
          · intro hru hcv hac hdso
            exact hrepUA1 hru hcv hac hac hdso
          · rw [hresEq]; dsimp only; rw [hooR, Bool.false_or]
            simp only [Bool.and_eq_true, Bool.or_eq_true, hflagIff]
            have hcvIff : (c == .val) = true ↔ c = .val := by cases c <;> decide
            have huIff : (m.usage == .once) = true ↔ m.usage = .once := by cases m <;> decide
            rw [hcvIff, huIff]
            constructor
            · rintro ⟨⟨h1, h2⟩, h3⟩
              refine ⟨h1, h2, ?_⟩
              rcases h3 with ((h3a | h3b) | h3c) | h3d
              · exact Or.inl h3a
              · exact Or.inr (Or.inl h3b)
              · exact Or.inr (Or.inr (Or.inl h3c))
              · exact Or.inr (Or.inr (Or.inr h3d))
            · rintro ⟨h1, h2, h3⟩
              refine ⟨⟨h1, h2⟩, ?_⟩
              rcases h3 with h3a | h3b | h3c | h3d
              · exact Or.inl (Or.inl (Or.inl h3a))
              · exact Or.inl (Or.inl (Or.inr h3b))
              · exact Or.inl (Or.inr h3c)
              · exact Or.inr h3d
          · intro hcv
            obtain ⟨hu, hub, hb, hsh⟩ := hval2 hcv
            have hcvT : (c == .val) = true := by rw [hcv]; rfl
            have hresVal :
                res.own = r.own ∧
                (∀ x, x ∈ res.deps ↔ x ∈ r.deps ∨ x ∈ f.deps ∨ x ∈ a.deps) ∧
                (∀ r0, r0 ∈ res.regs ↔ r0 ∈ r.regs ∨ r0 ∈ f.regs) := by
              rw [hresEq]; dsimp only; simp only [hcvT, ↓reduceIte, mem_natUnion]
              refine ⟨trivial, fun x => ?_, fun _ => trivial⟩
              constructor
              · rintro ((h1 | h2) | h3)
                · exact Or.inl h1
                · exact Or.inr (Or.inl h2)
                · exact Or.inr (Or.inr h3)
              · rintro (h1 | h2 | h3)
                · exact Or.inl (Or.inl h1)
                · exact Or.inl (Or.inr h2)
                · exact Or.inr h3
            obtain ⟨hownEq, hdepsEq, hregsEq⟩ := hresVal
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro hrm
              have hrEq := hu hrm
              refine ⟨by rw [hownEq, hrEq], fun x => by rw [hdepsEq, hrEq]; simp,
                fun r0 => by rw [hregsEq, hrEq]; simp⟩
            · intro hrm
              obtain ⟨hownR, hdepsR, hregsR⟩ := hub hrm
              refine ⟨hownEq.trans hownR, fun x => ?_, fun r0 => ?_⟩
              · rw [hdepsEq, hdepsR]; constructor
                · rintro (⟨i, p', a', hp', ha', _, hx⟩ | hxf | hxa)
                  · cases i with
                    | zero => simp at ha'; subst ha'; exact Or.inr hx
                    | succ _ => simp [ifc] at hp'
                  · exact Or.inl hxf
                  · exact Or.inr hxa
                · rintro (hxf | hxa)
                  · exact Or.inr (Or.inl hxf)
                  · exact Or.inr (Or.inr hxa)
              · dsimp only [AState.ofCSt] at hregsR; rw [hregsEq, hregsR, hreg1]; constructor
                · rintro ((rfl | ⟨i, p', a', hp', ha', hr⟩) | hrf)
                  · exact Or.inl rfl
                  · cases i with
                    | zero => simp at ha'; subst ha'; exact Or.inr (Or.inr hr)
                    | succ _ => simp [ifc] at hp'
                  · exact Or.inr (Or.inl hrf)
                · rintro (rfl | hrf | hra)
                  · exact Or.inl (Or.inl rfl)
                  · exact Or.inr hrf
                  · exact Or.inl (Or.inr ⟨0, p, a, by simp [ifc], by simp, hra⟩)
            · intro hrm
              obtain ⟨hownR, hdepsR, hregsR⟩ := hb hrm
              refine ⟨hownEq.trans hownR, fun x => ?_, fun r0 => ?_⟩
              · rw [hdepsEq, hdepsR]; constructor
                · rintro (⟨i, p', a', hp', ha', _, hx⟩ | hxf | hxa)
                  · cases i with
                    | zero => simp at ha'; subst ha'; exact Or.inr hx
                    | succ _ => simp [ifc] at hp'
                  · exact Or.inl hxf
                  · exact Or.inr hxa
                · rintro (hxf | hxa)
                  · exact Or.inr (Or.inl hxf)
                  · exact Or.inr (Or.inr hxa)
              · dsimp only [AState.ofCSt] at hregsR; rw [hregsEq, hregsR, hreg1]; constructor
                · rintro ((rfl | ⟨i, p', a', hp', ha', hr⟩) | hrf)
                  · exact Or.inl rfl
                  · cases i with
                    | zero => simp at ha'; subst ha'; exact Or.inr (Or.inr hr)
                    | succ _ => simp [ifc] at hp'
                  · exact Or.inr (Or.inl hrf)
                · rintro (rfl | hrf | hra)
                  · exact Or.inl (Or.inl rfl)
                  · exact Or.inr hrf
                  · exact Or.inl (Or.inr ⟨0, p, a, by simp [ifc], by simp, hra⟩)
            · intro hrm
              obtain ⟨hownR, hdepsR, hregsR⟩ := hsh hrm
              refine ⟨hownEq.trans hownR, fun x => ?_, fun r0 => ?_⟩
              · rw [hdepsEq, hdepsR]; constructor
                · rintro (⟨i, p', a', hp', ha', _, hx⟩ | hxf | hxa)
                  · cases i with
                    | zero => simp at ha'; subst ha'; exact Or.inr hx
                    | succ _ => simp [ifc] at hp'
                  · exact Or.inl hxf
                  · exact Or.inr hxa
                · rintro (hxf | hxa)
                  · exact Or.inr (Or.inl hxf)
                  · exact Or.inr (Or.inr hxa)
              · rw [hregsEq, hregsR]; constructor
                · rintro (⟨i, p', a', hp', ha', hr⟩ | hrf)
                  · cases i with
                    | zero => simp at ha'; subst ha'; exact Or.inr hr
                    | succ _ => simp [ifc] at hp'
                  · exact Or.inl hrf
                · rintro (hrf | hra)
                  · exact Or.inr hrf
                  · exact Or.inl ⟨0, p, a, by simp [ifc], by simp, hra⟩
          · intro hne
            have hcvF : (c == .val) = false := by
              cases c with
              | val => exact absurd rfl hne
              | irr | imm | leaf => rfl
            rw [hresEq]; dsimp only; simp only [hcvF, Bool.false_eq_true, ↓reduceIte]
            cases c with
            | val => exact absurd rfl hne
            | irr => rw [hirrImm2 (Or.inl rfl)]; exact ⟨rfl, rfl⟩
            | imm => rw [hirrImm2 (Or.inr rfl)]; exact ⟨rfl, rfl⟩
            | leaf => rw [hleaf2 rfl]; exact ⟨rfl, rfl⟩

/-! ## 3. Shared Bridge Predicates (`NoReachForbid`, `EnvNoReachForbid`, `ArgListOk`) -/

/-- Value-level non-reachability of `Forbid`: if `av` carries no `BadReg` region and no `BadDep` dep,
then `v` reaches no non-static, non-num location in `Forbid`. -/
def NoReachForbid (st : St) (Forbid BadReg BadDep : Nat → Prop) (av : AVal) (v : Val) : Prop :=
  (∀ r ∈ av.regs, ¬ BadReg r) → (∀ d ∈ av.deps, ¬ BadDep d) →
    ∀ l, Reach st.heap v l → ¬ StaticStrLoc st l → ¬ NumLoc st.heap l → ¬ Forbid l

/-- Every active non-erased in-scope binding in `(env, aenv)` satisfies `NoReachForbid`. -/
def EnvNoReachForbid (st : St) (Scope : Nat → Prop) (env : List Bnd) (aenv : List ABnd)
    (σ : AState) (Forbid BadReg BadDep : Nat → Prop) : Prop :=
  ∀ (i : Nat) (b : Bnd) (ab : ABnd), Scope i → env[i]? = some b → aenv[i]? = some ab →
    ab.mode ≠ .erased → ActiveVal σ (effVal ab) →
    NoReachForbid st Forbid BadReg BadDep (effVal ab) b.val

/-- Unified invariant on a list of evaluated (optional) arguments `(v, av, Foot)` in `(st, σ, I)`:
per-argument `VSim`, `ValEnvDisj`, `NoReachForbid`, plus pairwise unique-tree and exclusive-footprint
disjointness. -/
def ArgListOk (P : Prog) (ext : ExternOracle) (B : Nat) (st : St)
    (Frame NoKill NoSpend Scope : Nat → Prop)
    (env : List Bnd) (aenv : List ABnd) (σ : AState) (I : Interp)
    (envFoot : Nat → Nat → Prop)
    (Forbid BadReg BadDep : Nat → Prop)
    (args : List (Option (Val × AVal × (Nat → Prop)))) : Prop :=
  (∀ (i : Nat) (v : Val) (av : AVal) (ft : Nat → Prop),
    args[i]? = some (some (v, av, ft)) →
    VSim P ext B st Frame NoKill NoSpend σ I ft av v ∧
    ValEnvDisj P st NoKill Scope env aenv σ envFoot ft av v ∧
    (ActiveVal σ av → NoReachForbid st Forbid BadReg BadDep av v) ∧
    (ValidDeps σ av.deps → av.cls ≠ .val → ValBaseOk st v ∧ NonValSafe st.heap v)) ∧
  (∀ (i j : Nat) (v₁ v₂ : Val) (av₁ av₂ : AVal) (ft₁ ft₂ : Nat → Prop),
    i ≠ j →
    args[i]? = some (some (v₁, av₁, ft₁)) →
    args[j]? = some (some (v₂, av₂, ft₂)) →
    (ActiveVal σ av₁ → Transferable σ NoKill av₁ → ActiveVal σ av₂ →
      (∀ d, d ∈ av₁.deps → ¬ (d ∈ av₂.deps)) →
      ∀ l, OwnReach P st.heap v₁ l → ¬ Reach st.heap v₂ l) ∧
    (ActiveVal σ av₁ → FootActive σ av₁ → ActiveVal σ av₂ →
      (av₁.src = none ∨ av₁.src ≠ av₂.src) →
      ∀ l, ft₁ l → ¬ Reach st.heap v₂ l))

theorem Sim_deps_lt {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ d ∈ (effVal ab).deps, d < σ.st.size := by
  intro i ab hsc habi hne d hd
  have hi : i < aenv.length := (List.getElem?_eq_some_iff.mp habi).1
  have hiE : i < env.length := by rw [hsim.1]; exact hi
  exact ((hsim.2.2.2.2.2.1 i env[i] ab hsc (List.getElem?_eq_getElem hiE) habi).2 hne).2.2.1 d hd

theorem Sim_src_lt {P : Prog} {ext : ExternOracle} {B : Nat} {st : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    (hsim : Sim P ext B st Frame NoKill NoSpend Scope env aenv σ I envFoot) :
    ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab →
      ∀ x, (effVal ab).src = some x → x < σ.st.size := by
  intro i ab habi x hx
  dsimp [effVal] at hx; cases hx
  exact hsim.2.2.2.1 i ab habi

theorem StaticStrLoc_mono {st₁ st₂ : St}
    (hstatExt : ArrayExtends st₁.statics st₂.statics)
    (hstrExt : ArrayExtends st₁.strs st₂.strs)
    (hpSS : PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap)
    {l : Nat} (hl : StaticStrLoc st₁ l) : StaticStrLoc st₂ l := by
  rcases hl with ⟨r, v, hm, hr⟩ | ⟨s, v, hm, hr⟩
  · have hm₂ : (r, v) ∈ st₂.statics.toList := by
      obtain ⟨i, hi, heq⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hm)
      have h1 := hstatExt.2 i hi
      rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le hi hstatExt.1)] at h1
      have h2 := Option.some.inj h1
      rw [heq] at h2; rw [← h2]; exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
    have hpV : PreservesLocs (Reach st₁.heap v) st₁.heap st₂.heap :=
      hpSS.mono fun x hx => Or.inl ⟨r, v, hm, hx⟩
    exact Or.inl ⟨r, v, hm₂, (Reach_congr hpV l).mpr hr⟩
  · have hm₂ : (s, v) ∈ st₂.strs.toList := by
      obtain ⟨i, hi, heq⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hm)
      have h1 := hstrExt.2 i hi
      rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le hi hstrExt.1)] at h1
      have h2 := Option.some.inj h1
      rw [heq] at h2; rw [← h2]; exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
    have hpV : PreservesLocs (Reach st₁.heap v) st₁.heap st₂.heap :=
      hpSS.mono fun x hx => Or.inr ⟨s, v, hm, hx⟩
    exact Or.inr ⟨s, v, hm₂, (Reach_congr hpV l).mpr hr⟩

theorem Sim_preserves_of_old {P : Prog} {ext : ExternOracle} {B : Nat} {st₁ st₂ : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ₁ σ₂ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop}
    (hle : AStateLe σ₁ σ₂)
    (hp : PreservesLocs (fun l => l < st₁.heap.objs.size) st₁.heap st₂.heap)
    (hsim : Sim P ext B st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot) :
    PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap := by
  intro i b ab hsc hbi habi hne ha₂
  have hv := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
  have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv.2.1 (fun x hx => (hv.2.2.1 x hx).1) ha₂
  have hdl := (hv.2.2.2.2 ha₁).1.1
  exact hp.mono fun l hr => hdl.reach_lt_size hr

theorem Sim_preserves_of_outside_own {P : Prog} {ext : ExternOracle} {B : Nat} {st₁ st₂ : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ₁ σ₂ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {Foot : Nat → Prop} {av : AVal} {v : Val}
    (hle : AStateLe σ₁ σ₂)
    (haV₁ : ActiveVal σ₁ av) (htrV₁ : Transferable σ₁ NoKill av)
    (hkilled : ∀ d ∈ av.deps, σ₂.st[d]? = some .dead)
    (hdisjV : ValEnvDisj P st₁ NoKill Scope env aenv σ₁ envFoot Foot av v)
    (hp : PreservesLocs (fun l => l < st₁.heap.objs.size ∧ ¬ OwnReach P st₁.heap v l) st₁.heap st₂.heap)
    (hsim : Sim P ext B st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot) :
    PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap := by
  intro i b ab hsc hbi habi hne ha₂
  have hv := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
  have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv.2.1 (fun x hx => (hv.2.2.1 x hx).1) ha₂
  have hdl := (hv.2.2.2.2 ha₁).1.1
  have hdd : ∀ d, d ∈ av.deps → ¬ (d ∈ (effVal ab).deps) := fun d hd hdb =>
    (ha₂.1 d hdb).2 (hkilled d hd)
  exact hp.mono fun l hr => ⟨hdl.reach_lt_size hr, fun hor =>
    (hdisjV i b ab hsc hbi habi hne).1 haV₁ htrV₁ ha₁ hdd l hor hr⟩

theorem Sim_preserves_of_outside_foot {P : Prog} {ext : ExternOracle} {B : Nat} {st₁ st₂ : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ₁ σ₂ : AState} {I : Interp}
    {envFoot : Nat → Nat → Prop} {Foot : Nat → Prop} {av : AVal} {v : Val}
    (hle : AStateLe σ₁ σ₂)
    (haV₁ : ActiveVal σ₁ av) (hfV₁ : FootActive σ₁ av)
    (hdead : ∀ i ab, Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ActiveVal σ₂ (effVal ab) → av.src ≠ some ab.id)
    (hdisjV : ValEnvDisj P st₁ NoKill Scope env aenv σ₁ envFoot Foot av v)
    (hp : PreservesLocs (fun l => l < st₁.heap.objs.size ∧ ¬ Foot l) st₁.heap st₂.heap)
    (hsim : Sim P ext B st₁ Frame NoKill NoSpend Scope env aenv σ₁ I envFoot) :
    PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap := by
  intro i b ab hsc hbi habi hne ha₂
  have hv := ((hsim.2.2.2.2.2.1 i b ab hsc hbi habi).2 hne).2
  have ha₁ := ActiveVal.of_AStateLe hsim.2.1 hle hv.2.1 (fun x hx => (hv.2.2.1 x hx).1) ha₂
  have hdl := (hv.2.2.2.2 ha₁).1.1
  exact hp.mono fun l hr => ⟨hdl.reach_lt_size hr, fun hft =>
    (hdisjV i b ab hsc hbi habi hne).2.2.1 haV₁ hfV₁ ha₁ (hdead i ab hsc habi hne ha₂) l hft hr⟩

theorem NoReachForbid_step {st₁ st₂ : St} {Forbid BadReg BadDep : Nat → Prop}
    {av : AVal} {v : Val}
    (hstatExt : ArrayExtends st₁.statics st₂.statics)
    (hstrExt : ArrayExtends st₁.strs st₂.strs)
    (hpSS : PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap)
    (hpV : PreservesLocs (Reach st₁.heap v) st₁.heap st₂.heap)
    (hnrf : NoReachForbid st₁ Forbid BadReg BadDep av v) :
    NoReachForbid st₂ Forbid BadReg BadDep av v := by
  intro hregs hdeps l hr₂ hnotSS₂ hnotNum₂ hF
  have hr₁ : Reach st₁.heap v l := (Reach_congr hpV l).mp hr₂
  have hnotSS₁ : ¬ StaticStrLoc st₁ l := fun hss₁ => hnotSS₂ (StaticStrLoc_mono hstatExt hstrExt hpSS hss₁)
  have hnotNum₁ : ¬ NumLoc st₁.heap l := fun hnum₁ => hnotNum₂ ((NumLoc_congr hpV hr₁).mp hnum₁)
  exact hnrf hregs hdeps l hr₁ hnotSS₁ hnotNum₁ hF

theorem EnvNoReachForbid_step {st₁ st₂ : St} {Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ₁ σ₂ : AState}
    {Forbid BadReg BadDep : Nat → Prop}
    (hok₁ : AStateOk σ₁) (hle : AStateLe σ₁ σ₂)
    (hdepsE : ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ d ∈ (effVal ab).deps, d < σ₁.st.size)
    (hids : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ab.id < σ₁.st.size)
    (hstatExt : ArrayExtends st₁.statics st₂.statics)
    (hstrExt : ArrayExtends st₁.strs st₂.strs)
    (hpSS : PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap)
    (hpEnv : PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap)
    (henv : EnvNoReachForbid st₁ Scope env aenv σ₁ Forbid BadReg BadDep) :
    EnvNoReachForbid st₂ Scope env aenv σ₂ Forbid BadReg BadDep := by
  intro i b ab hsc hbi habi hne ha₂
  have hsrc : ∀ x, (effVal ab).src = some x → x < σ₁.st.size := fun x hx => by
    dsimp [effVal] at hx; cases hx; exact hids i ab habi
  have ha₁ := ActiveVal.of_AStateLe hok₁ hle (hdepsE i ab hsc habi hne) hsrc ha₂
  exact NoReachForbid_step hstatExt hstrExt hpSS (hpEnv i b ab hsc hbi habi hne ha₂)
    (henv i b ab hsc hbi habi hne ha₁)

theorem ArgListOk_step {P : Prog} {ext : ExternOracle} {B₁ B₂ : Nat} {st₁ st₂ : St}
    {Frame NoKill NoSpend Scope : Nat → Prop}
    {env : List Bnd} {aenv : List ABnd} {σ₁ σ₂ : AState} {I₁ I₂ : Interp}
    {envFoot : Nat → Nat → Prop} {Forbid BadReg BadDep : Nat → Prop}
    {args : List (Option (Val × AVal × (Nat → Prop)))}
    (hB : B₂ ≤ B₁) (hok₁ : AStateOk σ₁) (hle : AStateLe σ₁ σ₂)
    (hrf : RegsFuture st₁ st₂) (honceSh : PreservesOnceShell st₁.heap st₂.heap)
    (hssf : StaticStrFresh st₁ st₂)
    (hstatExt : ArrayExtends st₁.statics st₂.statics)
    (hstrExt : ArrayExtends st₁.strs st₂.strs)
    (hpSS : PreservesLocs (StaticStrLoc st₁) st₁.heap st₂.heap)
    (hI : ∀ r, r < σ₁.nextRegion → ∀ c ∈ I₁.reg r, c ∈ I₂.reg r)
    (hdepsE : ∀ (i : Nat) (ab : ABnd), Scope i → aenv[i]? = some ab → ab.mode ≠ .erased →
      ∀ d ∈ (effVal ab).deps, d < σ₁.st.size)
    (hids : ∀ (i : Nat) (ab : ABnd), aenv[i]? = some ab → ab.id < σ₁.st.size)
    (hpEnv : PreservesActiveEnv Scope env aenv σ₂ st₁.heap st₂.heap)
    (hpArgs : ∀ (i : Nat) (v : Val) (av : AVal) (ft : Nat → Prop),
      args[i]? = some (some (v, av, ft)) → ActiveVal σ₂ av →
      PreservesLocs (Reach st₁.heap v) st₁.heap st₂.heap)
    (hpNum : ∀ (l : Nat) (o : Obj) (n : Nat), st₁.heap.objs[l]? = some o → o.cell = Cell.num n → st₂.heap.objs[l]? = some o)
    (hargs : ArgListOk P ext B₁ st₁ Frame NoKill NoSpend Scope env aenv σ₁ I₁ envFoot Forbid BadReg BadDep args) :
    ArgListOk P ext B₂ st₂ Frame NoKill NoSpend Scope env aenv σ₂ I₂ envFoot Forbid BadReg BadDep args := by
  obtain ⟨hsingle, hpair⟩ := hargs
  refine ⟨fun i v av ft hget => ?_, fun i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂ => ?_⟩
  · obtain ⟨hv, hdisj, hnrf, hnv⟩ := hsingle i v av ft hget
    have hpV := hpArgs i v av ft hget
    have hsrcV : ∀ x, av.src = some x → x < σ₁.st.size := fun x hx => (hv.2.2.1 x hx).1
    refine ⟨VSim_step hB hok₁ hle hrf honceSh hssf (fun r hr => hI r (hv.1 r hr)) hpV hv,
      ValEnvDisj_step hok₁ hle hv.2.1 hsrcV hdepsE hids hpEnv hpV hdisj,
      fun ha₂ => NoReachForbid_step hstatExt hstrExt hpSS (hpV ha₂)
        (hnrf (ActiveVal.of_AStateLe hok₁ hle hv.2.1 hsrcV ha₂)),
      fun hval₂ hne => ?_⟩
    obtain ⟨hbv₁, hnv₁⟩ := hnv (ValidDeps.of_AStateLe hle hv.2.1 hval₂) hne
    have hpNumV : PreservesLocs (Reach st₁.heap v) st₁.heap st₂.heap := fun l hr => by
      obtain ⟨o, n, ho, hcell⟩ := hnv₁.reach_numLoc hr
      rw [ho, hpNum l o n ho hcell]
    exact ⟨ValBaseOk_congr hpNumV hrf.1 hbv₁, hnv₁.congr hpNumV⟩
  · obtain ⟨hv₁, _, _, _⟩ := hsingle i v₁ av₁ ft₁ hg₁
    obtain ⟨hv₂, _, _, _⟩ := hsingle j v₂ av₂ ft₂ hg₂
    have hsrc₁ : ∀ x, av₁.src = some x → x < σ₁.st.size := fun x hx => (hv₁.2.2.1 x hx).1
    have hsrc₂ : ∀ x, av₂.src = some x → x < σ₁.st.size := fun x hx => (hv₂.2.2.1 x hx).1
    obtain ⟨hdU, hdF⟩ := hpair i j v₁ v₂ av₁ av₂ ft₁ ft₂ hij hg₁ hg₂
    refine ⟨?_, ?_⟩
    · intro ha₁₂ htr₁₂ ha₂₂ hdd l hor₂ hr₂
      have ha₁₁ := ActiveVal.of_AStateLe hok₁ hle hv₁.2.1 hsrc₁ ha₁₂
      have ha₂₁ := ActiveVal.of_AStateLe hok₁ hle hv₂.2.1 hsrc₂ ha₂₂
      have htr₁₁ : Transferable σ₁ NoKill av₁ :=
        Transferable.of_AStateLe hok₁ hle hv₁.2.1 hsrc₁ (fun _ h => h) htr₁₂
      exact hdU ha₁₁ htr₁₁ ha₂₁ hdd l
        ((OwnReach_congr (hpArgs i v₁ av₁ ft₁ hg₁ ha₁₂) l).mp hor₂)
        ((Reach_congr (hpArgs j v₂ av₂ ft₂ hg₂ ha₂₂) l).mp hr₂)
    · intro ha₁₂ hf₁₂ ha₂₂ hsrc l hft hr₂
      have ha₁₁ := ActiveVal.of_AStateLe hok₁ hle hv₁.2.1 hsrc₁ ha₁₂
      have ha₂₁ := ActiveVal.of_AStateLe hok₁ hle hv₂.2.1 hsrc₂ ha₂₂
      have hf₁₁ := FootActive.of_AStateLe hok₁ hle hv₁.2.1 hsrc₁ hf₁₂
      exact hdF ha₁₁ hf₁₁ ha₂₁ hsrc l hft ((Reach_congr (hpArgs j v₂ av₂ ft₂ hg₂ ha₂₂) l).mp hr₂)

end IxC.Resource.Proof
