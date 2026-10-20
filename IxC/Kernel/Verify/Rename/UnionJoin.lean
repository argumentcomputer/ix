module

public import IxC.Kernel.Verify.Rename.UnionRun

@[expose] public section

/-!
# The union of two accepted lists (S1, part 2c): `AcceptsRef.union`

Two accepted lists sharing one front (the prelude's declarations), each the
front followed by units (`Rename/UnionRun.lean`), are accepted together: the
first list, then the second's units the first does not have, under the first
list's evidence. The union's environment answers every lookup either list's
environment answers, as it does.

**The proof.** Both runs pass through the front's one environment `E`
(`foldlM_det`). After it:
- **Shared units install alike** (`UnionSetting.shared`, by induction along
  the second list). A unit both lists hold is checked over the two prefixes'
  join `B.join A`, each prefix framed into it at the scope of its own names
  so far: the prefixes agree over every base both have named (the induction:
  such a base is a shared unit's, earlier in both), and over the front's. The
  unit's cores run to one environment over the join, so the two runs' results
  agree over the unit's bases.
- **The union fold** (`UnionSetting.union_aux`, along the second list): the
  union's environment `U` answers as the second run's `B` over every base the
  second list has named so far. A shared unit leaves `U` as it is (its
  installs are the first list's, by the above); any other is framed from `B`
  into `U` at the scope of its names, and installs no operation, so its
  evidence is the first list's as well as any other.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md : Mode}

/-! ## One side -/

/-- **One side of the union**: the front's environment `E` (its lookups good
at, and over, the front's names), the units run from it to `env`, the units
well formed after the front and closed after it. -/
structure RunSide (μ : CheckMode) (F : Nat) (ev : Evidences md)
    (front : List (Declaration md)) (us : List (List (Declaration md))) (E env : Env md) :
    Prop where
  good : FindGood (nameScope (namesOf front)) E
  keys : FindOver (namesOf front) E
  run : us.flatten.foldlM (checkDecl μ (fueledOps μ F) ev) E = .ok env
  units : UnitsOk front us
  closed : ClosedFrom (namesOf front) us.flatten

/-- **One side at a split** `us = xs ++ u :: ys`: the environments before
(`B`) and after (`B'`) the unit `u`. -/
structure SideAt (μ : CheckMode) (F : Nat) (ev : Evidences md) (front : List (Declaration md))
    (xs : List (List (Declaration md))) (u : List (Declaration md))
    (ys : List (List (Declaration md))) (E env B B' : Env md) : Prop where
  pre : xs.flatten.foldlM (checkDecl μ (fueledOps μ F) ev) E = .ok B
  step : u.foldlM (checkDecl μ (fueledOps μ F) ev) B = .ok B'
  post : ys.flatten.foldlM (checkDecl μ (fueledOps μ F) ev) B' = .ok env
  good : FindGood (nameScope (namesOf front ++ namesOf xs.flatten)) B
  keys : FindOver (namesOf front ++ namesOf xs.flatten) B
  ugood : ∀ d ∈ u, d.Good (nameScope (namesOf front ++ namesOf xs.flatten ++ namesOf u))
  gpre : Grows (OverN (namesOf xs.flatten)) E B
  gstep : Grows (OverN (namesOf u)) B B'
  gpost : Grows (OverN (namesOf ys.flatten)) B' env

theorem UnitsOk.not_sub {front : List (Declaration md)} {us vs : List (List (Declaration md))}
    (h : UnitsOk front us) (hsub : ∀ v ∈ vs, v ∈ us) {j : Key md}
    (hj : j ∈ basesOf front ∨ IsPre j) : j ∉ basesOf vs.flatten := by
  intro hm
  obtain ⟨v, hv, hjv⟩ := mem_basesOf_flatten.mp hm
  rcases hj with hj | hj
  · exact h.front v (hsub v hv) j hjv hj
  · exact h.pre v (hsub v hv) j hjv hj

/-- Over the names before and at a unit: a front or prelude base, or one of
the earlier units', or the unit's own. -/
theorem over_split {front : List (Declaration md)} {xs : List (List (Declaration md))}
    {u : List (Declaration md)} {k : Key md}
    (h : Over (namesOf front ++ namesOf xs.flatten ++ namesOf u) k) :
    (k.base ∈ basesOf front ∨ IsPre k.base) ∨ k.base ∈ basesOf xs.flatten ∨
      k.base ∈ basesOf u := by
  rcases h with h | h
  · simp only [List.map_append, List.mem_append] at h
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (Or.inr h)

/-- Over the names before a unit. -/
theorem over_split' {front : List (Declaration md)} {xs : List (List (Declaration md))}
    {k : Key md} (h : Over (namesOf front ++ namesOf xs.flatten) k) :
    (k.base ∈ basesOf front ∨ IsPre k.base) ∨ k.base ∈ basesOf xs.flatten := by
  rcases h with h | h
  · simp only [List.map_append, List.mem_append] at h
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · exact Or.inl (Or.inr h)

/-- A key over a unit's base is good at the scope of the names through it. -/
theorem good_unit {front : List (Declaration md)} {xs : List (List (Declaration md))}
    {u : List (Declaration md)} {k : Key md} (hk : k.base ∈ basesOf u) :
    k.Good (nameScope (namesOf front ++ namesOf xs.flatten ++ namesOf u)) :=
  Key.good_nameScope.mpr (Or.inl (by
    simp only [List.map_append, List.mem_append]; exact Or.inr hk))

/-- A key over the names before a unit is over the names through it. -/
theorem over_extend {front : List (Declaration md)} {xs : List (List (Declaration md))}
    {u : List (Declaration md)} {k : Key md} (h : Over (namesOf front ++ namesOf xs.flatten) k) :
    Over (namesOf front ++ namesOf xs.flatten ++ namesOf u) k :=
  h.mono fun _ hn => List.mem_append_left _ hn

namespace RunSide

variable {μ : CheckMode} {F : Nat} {ev : Evidences md} {front : List (Declaration md)}
  {us : List (List (Declaration md))} {E env : Env md}

/-- **The side at a split.** -/
theorem at_ (hs : RunSide μ F ev front us E env) {xs ys : List (List (Declaration md))}
    {u : List (Declaration md)} (h : us = xs ++ u :: ys) :
    ∃ B B', SideAt μ F ev front xs u ys E env B B' := by
  have hrun := hs.run
  rw [h, List.flatten_append, List.flatten_cons] at hrun
  obtain ⟨B, hB, hrun⟩ := foldlM_append_ok hrun
  obtain ⟨B', hB', hrun⟩ := foldlM_append_ok hrun
  have hcl := hs.closed
  rw [h, List.flatten_append, List.flatten_cons] at hcl
  obtain ⟨hcx, hcu⟩ := hcl.append
  obtain ⟨hcu, -⟩ := hcu.append
  obtain ⟨hg, ho⟩ := run_good μ F ev (namesOf front) xs.flatten E B hs.good hs.keys hcx hB
  have hfree := hs.units.free_flatten
  have hmem : ∀ d, d ∈ xs.flatten ∨ d ∈ u ∨ d ∈ ys.flatten → d ∈ us.flatten := by
    intro d hd
    rw [h, List.flatten_append, List.flatten_cons]
    simp only [List.mem_append]
    exact hd
  refine ⟨B, B', hB, hB', hrun, hg, ho, hcu.good, ?_, ?_, ?_⟩
  · exact run_free μ _ ev _ (fun d hd => hfree d (hmem d (Or.inl hd))) E B hB
  · exact run_free μ _ ev _ (fun d hd => hfree d (hmem d (Or.inr (Or.inl hd)))) B B' hB'
  · exact run_free μ _ ev _ (fun d hd => hfree d (hmem d (Or.inr (Or.inr hd)))) B' env hrun

/-- **The side's final environment**: its lookups good at, and over, all the
names. -/
theorem final (hs : RunSide μ F ev front us E env) :
    FindGood (nameScope (namesOf front ++ namesOf us.flatten)) env ∧
      FindOver (namesOf front ++ namesOf us.flatten) env :=
  run_good μ F ev (namesOf front) us.flatten E env hs.good hs.keys hs.closed hs.run

/-- **Front and prelude keys** answer as in `E`. -/
theorem front_env (hs : RunSide μ F ev front us E env) {k : Key md}
    (hk : k.base ∈ basesOf front ∨ IsPre k.base) : env.find? k = E.find? k :=
  (run_free μ _ ev _ hs.units.free_flatten E env hs.run).keep
    (hs.units.not_sub (fun _ hv => hv) hk)

end RunSide

namespace SideAt

variable {μ : CheckMode} {F : Nat} {ev : Evidences md} {front : List (Declaration md)}
  {us xs ys : List (List (Declaration md))} {u : List (Declaration md)} {E env B B' : Env md}

theorem mem_u (h : us = xs ++ u :: ys) : u ∈ us := by
  rw [h]; simp

/-- Front and prelude keys: `B` answers as `E`. -/
theorem front_B (a : SideAt μ F ev front xs u ys E env B B') (hs : RunSide μ F ev front us E env)
    (h : us = xs ++ u :: ys) {k : Key md} (hk : k.base ∈ basesOf front ∨ IsPre k.base) :
    B.find? k = E.find? k :=
  a.gpre.keep (hs.units.not_sub (fun v hv => by rw [h]; simp [hv]) hk)

/-- `B` holds nothing over the unit's bases. -/
theorem none_u (a : SideAt μ F ev front xs u ys E env B B') (hs : RunSide μ F ev front us E env)
    (h : us = xs ++ u :: ys) {k : Key md} (hk : k.base ∈ basesOf u) : B.find? k = none := by
  cases hB : B.find? k with
  | none => rfl
  | some c =>
    exfalso
    have hu := mem_u h
    rcases over_split' (a.keys k c hB) with (hf | hp) | hx
    · exact hs.units.front u hu _ hk hf
    · exact hs.units.pre u hu _ hk hp
    · exact (hs.units.split h).1 _ hk hx

/-- Over an earlier unit's base, the final environment answers as `B`. -/
theorem env_x (a : SideAt μ F ev front xs u ys E env B B') (hs : RunSide μ F ev front us E env)
    (h : us = xs ++ u :: ys) {k : Key md} (hk : k.base ∈ basesOf xs.flatten) :
    env.find? k = B.find? k := by
  have hsp := hs.units.split h
  rw [a.gpost.keep (hsp.2.2 _ hk), a.gstep.keep (fun hu => hsp.1 _ hu hk)]

/-- Over the unit's bases, the final environment answers as `B'`. -/
theorem env_u (a : SideAt μ F ev front xs u ys E env B B') (hs : RunSide μ F ev front us E env)
    (h : us = xs ++ u :: ys) {k : Key md} (hk : k.base ∈ basesOf u) :
    env.find? k = B'.find? k :=
  a.gpost.keep ((hs.units.split h).2.1 _ hk)

/-- Outside the unit's bases, `B'` answers as `B`. -/
theorem B'_out (a : SideAt μ F ev front xs u ys E env B B') {k : Key md}
    (hk : k.base ∉ basesOf u) : B'.find? k = B.find? k :=
  a.gstep.keep hk

end SideAt

/-! ## Both sides -/

/-- **The union's setting**: one front and its environment `E`, the two
sides, and the units' agreement. -/
structure UnionSetting (μ : CheckMode) (F : Nat) (ev₁ ev₂ : Evidences md)
    (front : List (Declaration md)) (us₁ us₂ : List (List (Declaration md)))
    (E env₁ env₂ : Env md) : Prop where
  side₁ : RunSide μ F ev₁ front us₁ E env₁
  side₂ : RunSide μ F ev₂ front us₂ E env₂
  agree : UnitsAgree us₁ us₂

namespace UnionSetting

variable {μ : CheckMode} {F : Nat} {ev₁ ev₂ : Evidences md} {front : List (Declaration md)}
  {us₁ us₂ : List (List (Declaration md))} {E env₁ env₂ : Env md}

/-- **A shared unit installs alike**: given the agreement over every earlier
shared unit's bases, the two final environments agree over the unit's. -/
theorem se_step (hs : UnionSetting μ F ev₁ ev₂ front us₁ us₂ E env₁ env₂)
    {xs ys : List (List (Declaration md))} {u : List (Declaration md)}
    (h : us₂ = xs ++ u :: ys) (hu₁ : u ∈ us₁)
    (ih : ∀ v ∈ xs, v ∈ us₁ → ∀ j ∈ basesOf v, AgreeOn env₂ env₁ j) :
    ∀ j ∈ basesOf u, AgreeOn env₂ env₁ j := by
  obtain ⟨pre₁, post₁, h₁⟩ := List.append_of_mem hu₁
  obtain ⟨B, B', sB⟩ := hs.side₂.at_ h
  obtain ⟨A, A', sA⟩ := hs.side₁.at_ h₁
  -- the two prefixes agree over every key over both scopes
  have hAB : ∀ k, Over (namesOf front ++ namesOf xs.flatten ++ namesOf u) k →
      Over (namesOf front ++ namesOf pre₁.flatten ++ namesOf u) k → A.find? k = B.find? k := by
    intro k h2 h1
    by_cases hf : k.base ∈ basesOf front ∨ IsPre k.base
    · rw [sA.front_B hs.side₁ h₁ hf, sB.front_B hs.side₂ h hf]
    · by_cases hku : k.base ∈ basesOf u
      · rw [sA.none_u hs.side₁ h₁ hku, sB.none_u hs.side₂ h hku]
      · have hx : k.base ∈ basesOf xs.flatten := by
          rcases over_split h2 with hf' | hx | hu
          · exact absurd hf' hf
          · exact hx
          · exact absurd hu hku
        have hp : k.base ∈ basesOf pre₁.flatten := by
          rcases over_split h1 with hf' | hx | hu
          · exact absurd hf' hf
          · exact hx
          · exact absurd hu hku
        obtain ⟨v, hv, hjv⟩ := mem_basesOf_flatten.mp hx
        obtain ⟨v', hv', hjv'⟩ := mem_basesOf_flatten.mp hp
        have hv₁ : v' ∈ us₁ := by rw [h₁]; exact List.mem_append_left _ hv'
        have hv₂ : v ∈ us₂ := by rw [h]; exact List.mem_append_left _ hv
        have he : v' = v := hs.agree v' hv₁ v hv₂ ⟨k.base, hjv', hjv⟩
        rw [he] at hv₁
        have hag := ih v hv hv₁ k.base hjv
        rw [← sA.env_x hs.side₁ h₁ hp, ← sB.env_x hs.side₂ h hx]
        exact hag k rfl
  -- each prefix, framed into the join at its own scope
  have fB : EnvFrame (nameScope (namesOf front ++ namesOf xs.flatten ++ namesOf u)) B
      (B.join A) := EnvFrame.mk
    (fun k hk => by
      rw [Env.find?_join]
      cases hb : B.find? k with
      | some c => rfl
      | none =>
        cases ha : A.find? k with
        | none => rfl
        | some c =>
          have := hAB k (Key.good_nameScope.mp hk) (over_extend (sA.keys k c ha))
          rw [ha, hb] at this
          exact nomatch this)
    (fun k c _ hc => ConstantInfo.Good.mono
      (nameScope_le fun _ hn => List.mem_append_left _ hn) (sB.good k c hc))
    (fun _ hr => (sB.keys.mono fun _ hn => List.mem_append_left _ hn).absent hr)
    (nameScope_pre _)
  have fA : EnvFrame (nameScope (namesOf front ++ namesOf pre₁.flatten ++ namesOf u)) A
      (B.join A) := EnvFrame.mk
    (fun k hk => by
      rw [Env.find?_join]
      cases hb : B.find? k with
      | none => rfl
      | some c =>
        rw [hAB k (over_extend (sB.keys k c hb)) (Key.good_nameScope.mp hk), hb]
        rfl)
    (fun k c _ hc => ConstantInfo.Good.mono
      (nameScope_le fun _ hn => List.mem_append_left _ hn) (sA.good k c hc))
    (fun _ hr => (sA.keys.mono fun _ hn => List.mem_append_left _ hn).absent hr)
    (nameScope_pre _)
  -- the unit's cores over the join: one run
  obtain ⟨G₂, hG₂, hr₂⟩ := foldlM_core_frame μ F u fB sB.ugood (foldlM_core μ F ev₂ u sB.step)
  obtain ⟨G₁, hG₁, hr₁⟩ := foldlM_core_frame μ F u fA sA.ugood (foldlM_core μ F ev₁ u sA.step)
  rw [hG₂] at hG₁
  cases Except.ok.inj hG₁
  intro j hj k hk
  have hku : k.base ∈ basesOf u := hk ▸ hj
  rw [sA.env_u hs.side₁ h₁ hku, sB.env_u hs.side₂ h hku, ← hr₁.find_eq (good_unit hku),
    hr₂.find_eq (good_unit hku)]

/-- **Shared units install alike**, along the second list. -/
theorem shared_from (hs : UnionSetting μ F ev₁ ev₂ front us₁ us₂ E env₁ env₂) :
    ∀ (ys xs : List (List (Declaration md))), us₂ = xs ++ ys →
      (∀ v ∈ xs, v ∈ us₁ → ∀ j ∈ basesOf v, AgreeOn env₂ env₁ j) →
      ∀ v ∈ ys, v ∈ us₁ → ∀ j ∈ basesOf v, AgreeOn env₂ env₁ j
  | [], _, _, _ => fun _ h => nomatch h
  | u :: ys, xs, h, ih => by
    have hu : u ∈ us₁ → ∀ j ∈ basesOf u, AgreeOn env₂ env₁ j := fun hu₁ => hs.se_step h hu₁ ih
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hu
    · refine shared_from hs ys (xs ++ [u]) (by rw [h]; simp) (fun w hw => ?_) v hv
      rcases List.mem_append.mp hw with hw | hw
      · exact ih w hw
      · rw [List.mem_singleton.mp hw]; exact hu

/-- **Shared units install alike.** -/
theorem shared (hs : UnionSetting μ F ev₁ ev₂ front us₁ us₂ E env₁ env₂) {v : List (Declaration md)}
    (hv₂ : v ∈ us₂) (hv₁ : v ∈ us₁) : ∀ j ∈ basesOf v, AgreeOn env₂ env₁ j :=
  hs.shared_from us₂ [] rfl (fun _ h => nomatch h) v hv₂ hv₁

end UnionSetting

end Ix.Kernel
