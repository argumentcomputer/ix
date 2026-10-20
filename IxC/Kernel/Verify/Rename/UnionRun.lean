module

public import IxC.Kernel.Verify.Rename.UnionFold

@[expose] public section

/-!
# The union of two accepted lists (S1, part 2c): runs of units

What the union fold (`Rename/UnionJoin.lean`) runs on.

- **Basis-free declarations install over their own names**
  (`checkDecl_post_free`): no pinned basis route, so no prelude-role escape
  (`OverN`, not `Over`).
- **Determinism across evidence** (`foldlM_det`): two accepted runs of one
  list from one environment, under any two evidence tables, install the same
  environment (each step installs its core, `checkDecl_core`).
- **Runs of cores, framed** (`foldlM_core_frame`), and runs of declarations
  installing no operation, framed under any two evidence tables
  (`foldlM_frame_noop`).
- **Ordered closure** of a list splits at a cons and an append
  (`closedFrom_cons`, `ClosedFrom.append`).
- **Units**: a list of declarations whose bases no other unit declares (one
  record's lowering: a mutual or nested block's generated model records,
  then its `indDecl`; any other record's one declaration). `UnitsOk` (bases
  pairwise disjoint across units and from the front's, never a prelude role;
  every declaration basis-free) and `UnitsAgree` (two units declaring a
  common base are one).
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md : Mode}

/-! ## Bases -/

@[simp] theorem Key.base_base : ∀ k : Key md, k.base.base = k.base
  | .id _ => rfl
  | .role _ => rfl
  | .aux k _ => by simpa using Key.base_base k

/-- A base that is a prelude role. -/
def IsPre (j : Key md) : Prop := ∃ r ∈ preludeRoles, j = .role r

/-- The names a list declares. -/
abbrev namesOf (ds : List (Declaration md)) : List (Key md) := ds.flatMap Declaration.names

/-- The bases of the names a list declares. -/
abbrev basesOf (ds : List (Declaration md)) : List (Key md) := (namesOf ds).map Key.base

theorem namesOf_append (as bs : List (Declaration md)) :
    namesOf (as ++ bs) = namesOf as ++ namesOf bs := List.flatMap_append

theorem namesOf_cons (d : Declaration md) (ds : List (Declaration md)) :
    namesOf (d :: ds) = d.names ++ namesOf ds := List.flatMap_cons

theorem mem_basesOf {ds : List (Declaration md)} {j : Key md} :
    j ∈ basesOf ds ↔ ∃ d ∈ ds, ∃ n ∈ d.names, n.base = j := by
  simp only [basesOf, namesOf, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨n, ⟨d, hd, hn⟩, rfl⟩; exact ⟨d, hd, n, hn, rfl⟩
  · rintro ⟨d, hd, n, hn, rfl⟩; exact ⟨n, ⟨d, hd, hn⟩, rfl⟩

theorem mem_basesOf_flatten {us : List (List (Declaration md))} {j : Key md} :
    j ∈ basesOf us.flatten ↔ ∃ u ∈ us, j ∈ basesOf u := by
  simp only [mem_basesOf, List.mem_flatten]
  constructor
  · rintro ⟨d, ⟨u, hu, hd⟩, n, hn, rfl⟩; exact ⟨u, hu, d, hd, n, hn, rfl⟩
  · rintro ⟨u, hu, d, hd, n, hn, rfl⟩; exact ⟨d, ⟨u, hu, hd⟩, n, hn, rfl⟩

theorem basesOf_append (as bs : List (Declaration md)) :
    basesOf (as ++ bs) = basesOf as ++ basesOf bs := by
  simp [basesOf, namesOf_append]

/-- Over a list of names, by bases. -/
theorem over_iff {ns : List (Key md)} {k : Key md} :
    Over ns k ↔ k.base ∈ ns.map Key.base ∨ IsPre k.base := Iff.rfl

/-! ## Basis-free declarations install over their own names -/

/-- **A basis-free declaration**: it takes no pinned basis route. -/
def Declaration.BasisFree : Declaration md → Prop
  | .basisDecl _ => False
  | .indDecl block _ => basisPinHit block = none
  | .quotDecl k cv => ¬ (k = .type ∧ quotPinHit k cv = true)
  | _ => True

/-- **Strictly over a list of names**: a key whose base is one of theirs. -/
def OverN (ns : List (Key md)) (k : Key md) : Prop := k.base ∈ ns.map Key.base

theorem OverN.of_mem {ns : List (Key md)} {k : Key md} (h : k ∈ ns) : OverN ns k :=
  List.mem_map_of_mem h

theorem OverN.auxKey {ns : List (Key md)} {k : Key md} (h : OverN ns k) (d : Derived) :
    OverN ns (auxKey k d) := by
  simpa [OverN] using h

theorem OverN.over {ns : List (Key md)} {k : Key md} (h : OverN ns k) : Over ns k := Or.inl h

theorem OverN.mono {ns ns' : List (Key md)} (hs : ∀ k ∈ ns, k ∈ ns') {k : Key md}
    (h : OverN ns k) : OverN ns' k := by
  obtain ⟨k', hk', he⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨k', hs k' hk', he⟩

section Values

variable {ops : (CheckerOps md) (CheckM md)}

/-- **The install lemma, basis-free**: an accepted basis-free declaration
extends the environment only by constants over its own names. -/
theorem checkDecl_post_free (mode : CheckMode) (ops : (CheckerOps md) (CheckM md))
    (ev : Evidences md) (env : Env md) {d : Declaration md} (hfree : d.BasisFree) :
    ExPost (checkDecl mode ops ev env d) (Grows (OverN d.names) env) := by
  cases d with
  | defnDecl cv value hint =>
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    rw [ExPost.post_bind]
    refine ExPost.mono (fun env2 h2 => ?_) (checkDefnVal_post env cvA value hint)
    obtain ⟨v, rfl⟩ := h2
    have hg : Grows (OverN (Declaration.names (.defnDecl cv value hint))) env
        ⟨.defnInfo cvA v hint :: env.consts⟩ :=
      Grows.push (OverN.of_mem (by simp [Declaration.names, ConstantInfo.name,
        ConstantInfo.toConstantVal, h]))
        (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, h])
    simp [hg]
    intro _ _ _ _
    split <;> simp [hg]
  | thmDecl cv value =>
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    refine ExPost.mono (fun e he => ?_) (checkThmVal_post env cvA value)
    obtain ⟨v, rfl⟩ := he
    exact Grows.push (OverN.of_mem (by simp [Declaration.names, ConstantInfo.name,
      ConstantInfo.toConstantVal, h]))
      (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, h])
  | opaqueDecl cv value =>
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    refine ExPost.mono (fun e he => ?_) (checkOpaqueVal_post env cvA value)
    subst he
    exact Grows.push (OverN.of_mem (by simp [Declaration.names, ConstantInfo.name,
      ConstantInfo.toConstantVal, h]))
      (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, h])
  | axiomDecl cv =>
    unfold checkDecl
    simp only [ExPost.post_ite, ExPost.post_pure, ExPost.post_throw, imp_true_iff, and_true,
      ExPost.post_bind]
    refine ⟨fun _ _ => Grows.refl _ env, fun _ => ?_⟩
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    have hg : Grows (OverN (Declaration.names (.axiomDecl cv))) env
        ⟨.axiomInfo cvA :: env.consts⟩ :=
      Grows.push (OverN.of_mem (by simp [Declaration.names, ConstantInfo.name,
        ConstantInfo.toConstantVal, h]))
        (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, h])
    simp [hg, Grows.refl]
  | basisDecl kind => exact (hfree : False).elim
  | indDecl block nP =>
    have hb : basisPinHit block = none := hfree
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.of_forall fun _ => ?_
    split
    · rename_i kind hk
      rw [hb] at hk
      exact nomatch hk
    · simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
      intro _
      have hn : Declaration.names (.indDecl block nP) = block.map (·.name) := rfl
      split
      · rename_i p hp
        obtain ⟨hT, hR, hC⟩ := nativeParts?_names hp
        rw [hn]
        exact checkNative_post env p (OverN.of_mem hT) (OverN.of_mem hR)
          (fun c hc => OverN.of_mem (hC c hc)) ((OverN.of_mem hT).auxKey _)
      · rw [hn]
        exact checkModeled_post env block
          (fun ci hci => OverN.of_mem (List.mem_map_of_mem hci))
          (fun ci hci i => (OverN.of_mem (List.mem_map_of_mem hci)).auxKey _)
  | quotDecl k cv =>
    unfold checkDecl
    simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
    intro hpin
    cases k with
    | type => exact absurd ⟨rfl, hpin⟩ hfree
    | _ => simp [Grows.refl]

end Values

/-- **A basis-free run installs over its list's names.** -/
theorem run_free (μ : CheckMode) (ops : (CheckerOps md) (CheckM md)) (ev : Evidences md)
    (ds : List (Declaration md)) (hfree : ∀ d ∈ ds, d.BasisFree) (env : Env md) :
    ExPost (ds.foldlM (checkDecl μ ops ev) env) (Grows (OverN (namesOf ds)) env) :=
  foldlM_grows _ ds env fun e d hd =>
    ExPost.mono (fun _ h => h.mono fun _ hk =>
      hk.mono fun _ hn => List.mem_flatMap.mpr ⟨d, hd, hn⟩)
      (checkDecl_post_free μ ops ev e (hfree d hd))

/-- **A lookup outside a growth's bases** is unchanged. -/
theorem Grows.keep {ns : List (Key md)} {X Y : Env md} (hg : Grows (OverN ns) X Y)
    {k : Key md} (hk : k.base ∉ ns.map Key.base) : Y.find? k = X.find? k :=
  hg.find_eq hk

/-! ## Folds -/

/-- A fold over an append, accepted. -/
theorem foldlM_append_ok {α : Type} {step : Env md → α → CheckM md (Env md)} {as bs : List α}
    {env env' : Env md} (h : (as ++ bs).foldlM step env = .ok env') :
    ∃ e, as.foldlM step env = .ok e ∧ bs.foldlM step e = .ok env' := by
  rw [List.foldlM_append] at h
  cases he : as.foldlM step env with
  | error x => rw [he] at h; exact nomatch h
  | ok e => rw [he] at h; exact ⟨e, rfl, h⟩

theorem foldlM_append_of_ok {α : Type} {step : Env md → α → CheckM md (Env md)}
    {as bs : List α} {env e env' : Env md} (h₁ : as.foldlM step env = .ok e)
    (h₂ : bs.foldlM step e = .ok env') : (as ++ bs).foldlM step env = .ok env' := by
  rw [List.foldlM_append, h₁]; exact h₂

/-- **Two accepted checks of one declaration over one environment**, under any
two evidence tables, install the same environment. -/
theorem checkDecl_det (μ : CheckMode) (F : Nat) (ev ev' : Evidences md) {env e e' : Env md}
    {d : Declaration md} (h : checkDecl μ (fueledOps μ F) ev env d = .ok e)
    (h' : checkDecl μ (fueledOps μ F) ev' env d = .ok e') : e = e' := by
  have := checkDecl_core μ F ev h
  rw [checkDecl_core μ F ev' h'] at this
  exact (Except.ok.inj this).symm

/-- **Two accepted runs of one list from one environment**, under any two
evidence tables, install the same environment. -/
theorem foldlM_det (μ : CheckMode) (F : Nat) (ev ev' : Evidences md) :
    ∀ (ds : List (Declaration md)) {env e e' : Env md},
      ds.foldlM (checkDecl μ (fueledOps μ F) ev) env = .ok e →
      ds.foldlM (checkDecl μ (fueledOps μ F) ev') env = .ok e' → e = e'
  | [], _, _, _, h, h' => by
    simp only [List.foldlM_nil] at h h'
    cases h; cases h'; rfl
  | d :: ds, env, e, e', h, h' => by
    obtain ⟨x, hx, h⟩ := foldlM_cons_ok h
    obtain ⟨x', hx', h'⟩ := foldlM_cons_ok h'
    cases checkDecl_det μ F ev ev' hx hx'
    exact foldlM_det μ F ev ev' ds h h'

/-- **An accepted run installs the run of its cores.** -/
theorem foldlM_core (μ : CheckMode) (F : Nat) (ev : Evidences md) :
    ∀ (ds : List (Declaration md)) {env e : Env md},
      ds.foldlM (checkDecl μ (fueledOps μ F) ev) env = .ok e →
      ds.foldlM (checkDeclCore μ (fueledOps μ F)) env = .ok e
  | [], _, _, h => h
  | d :: ds, env, e, h => by
    obtain ⟨x, hx, h⟩ := foldlM_cons_ok h
    rw [List.foldlM_cons, checkDecl_core μ F ev hx]
    exact foldlM_core μ F ev ds h

/-- **A run of cores, framed.** -/
theorem foldlM_core_frame (μ : CheckMode) (F : Nat) {P : KeyScope md} :
    ∀ (ds : List (Declaration md)) {B U B' : Env md}, EnvFrame P B U →
      (∀ d ∈ ds, d.Good P) → ds.foldlM (checkDeclCore μ (fueledOps μ F)) B = .ok B' →
      ∃ U', ds.foldlM (checkDeclCore μ (fueledOps μ F)) U = .ok U' ∧ EnvFrame P B' U'
  | [], B, U, B', hE, _, h => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨U, rfl, hE⟩
  | d :: ds, B, U, B', hE, hds, h => by
    obtain ⟨x, hx, h⟩ := foldlM_cons_ok h
    obtain ⟨y, hy, hxy⟩ := checkDeclCore_frame μ F hE (hds d List.mem_cons_self) x hx
    obtain ⟨U', hU', hr⟩ := foldlM_core_frame μ F ds hxy
      (fun d' h' => hds d' (List.mem_cons_of_mem _ h')) h
    refine ⟨U', ?_, hr⟩
    rw [List.foldlM_cons, hy]
    exact hU'

/-- **A declaration installing no operation, framed**, under any two evidence
tables. -/
theorem frame_noop (μ : CheckMode) (F : Nat) (ev ev' : Evidences md) {P : KeyScope md}
    {B U B' : Env md} {d : Declaration md} (hE : EnvFrame P B U) (hd : d.Good P)
    (hop : d.NoOp) (h : checkDecl μ (fueledOps μ F) ev B d = .ok B') :
    ∃ U', checkDecl μ (fueledOps μ F) ev' U d = .ok U' ∧ EnvFrame P B' U' := by
  rw [checkDecl_ev_irrel μ F ev [] B hop] at h
  have hev : Evidences.Good P ([] : Evidences md) := fun _ h => nomatch h
  obtain ⟨U', hU', hr⟩ := checkDecl_frame μ F hev hE hd (Or.inl hop) B' h
  rw [checkDecl_ev_irrel μ F [] ev' U hop] at hU'
  exact ⟨U', hU', hr⟩

/-- **A run installing no operation, framed**, under any two evidence tables. -/
theorem foldlM_frame_noop (μ : CheckMode) (F : Nat) (ev ev' : Evidences md) {P : KeyScope md} :
    ∀ (ds : List (Declaration md)) {B U B' : Env md}, EnvFrame P B U →
      (∀ d ∈ ds, d.Good P ∧ d.NoOp) → ds.foldlM (checkDecl μ (fueledOps μ F) ev) B = .ok B' →
      ∃ U', ds.foldlM (checkDecl μ (fueledOps μ F) ev') U = .ok U' ∧ EnvFrame P B' U'
  | [], B, U, B', hE, _, h => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨U, rfl, hE⟩
  | d :: ds, B, U, B', hE, hds, h => by
    obtain ⟨x, hx, h⟩ := foldlM_cons_ok h
    have hd := hds d List.mem_cons_self
    obtain ⟨y, hy, hxy⟩ := frame_noop μ F ev ev' hE hd.1 hd.2 hx
    obtain ⟨U', hU', hr⟩ := foldlM_frame_noop μ F ev ev' ds hxy
      (fun d' h' => hds d' (List.mem_cons_of_mem _ h')) h
    refine ⟨U', ?_, hr⟩
    rw [List.foldlM_cons, hy]
    exact hU'

/-! ## Ordered closure, split -/

theorem closedFrom_cons {pre : List (Key md)} {d : Declaration md} {ds : List (Declaration md)} :
    ClosedFrom pre (d :: ds) ↔
      d.Good (nameScope (pre ++ d.names)) ∧ ClosedFrom (pre ++ d.names) ds := by
  constructor
  · intro hc
    refine ⟨?_, ?_⟩
    · have h0 := hc 0 (by simp)
      simp only [List.take_succ_cons, List.take_zero, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at h0
      exact h0
    · intro i hi
      have h1 := hc (i + 1) (by simp; omega)
      simp only [List.take_succ_cons, List.flatMap_cons, List.append_assoc] at h1
      rw [List.append_assoc]; exact h1
  · rintro ⟨hd, hc⟩ i hi
    cases i with
    | zero =>
      simp only [List.take_succ_cons, List.take_zero, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      exact hd
    | succ i =>
      have h1 := hc i (by simp at hi; omega)
      simp only [List.take_succ_cons, List.flatMap_cons]
      rw [List.append_assoc] at h1; exact h1

theorem ClosedFrom.append : ∀ {pre : List (Key md)} {as bs : List (Declaration md)},
    ClosedFrom pre (as ++ bs) → ClosedFrom pre as ∧ ClosedFrom (pre ++ namesOf as) bs
  | pre, [], bs, h => ⟨fun i hi => absurd hi (by simp), by simpa using h⟩
  | pre, a :: as, bs, h => by
    rw [List.cons_append, closedFrom_cons] at h
    obtain ⟨ha, h⟩ := h
    obtain ⟨h1, h2⟩ := ClosedFrom.append h
    refine ⟨closedFrom_cons.mpr ⟨ha, h1⟩, ?_⟩
    simpa [namesOf_cons, List.append_assoc] using h2

/-- **Every declaration of a closed list is good at the scope of all its
names.** -/
theorem ClosedFrom.good : ∀ {pre : List (Key md)} {ds : List (Declaration md)},
    ClosedFrom pre ds → ∀ d ∈ ds, d.Good (nameScope (pre ++ namesOf ds))
  | _, [], _, _, h => nomatch h
  | pre, a :: as, h, d, hd => by
    rw [closedFrom_cons] at h
    have hsub : ∀ n ∈ pre ++ a.names, n ∈ pre ++ namesOf (a :: as) := by
      intro n hn
      rw [namesOf_cons, ← List.append_assoc]
      exact List.mem_append_left _ hn
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Declaration.Good.mono (nameScope_le hsub) h.1
    · have := ClosedFrom.good h.2 d hd
      rw [namesOf_cons, ← List.append_assoc]; exact this

/-! ## Units -/

/-- **Units, well formed after a front**: their bases pairwise disjoint and
disjoint from the front's, never a prelude role; every declaration basis-free. -/
structure UnitsOk (front : List (Declaration md)) (us : List (List (Declaration md))) : Prop where
  disj : us.Pairwise fun u v => ∀ j ∈ basesOf u, j ∉ basesOf v
  front : ∀ u ∈ us, ∀ j ∈ basesOf u, j ∉ basesOf front
  pre : ∀ u ∈ us, ∀ j ∈ basesOf u, ¬ IsPre j
  free : ∀ u ∈ us, ∀ d ∈ u, d.BasisFree

/-- **Units agree**: two units declaring a common base are one. -/
def UnitsAgree (us₁ us₂ : List (List (Declaration md))) : Prop :=
  ∀ u₁ ∈ us₁, ∀ u₂ ∈ us₂, (∃ j ∈ basesOf u₁, j ∈ basesOf u₂) → u₁ = u₂

namespace UnitsOk

variable {front : List (Declaration md)} {us : List (List (Declaration md))}

theorem free_flatten (h : UnitsOk front us) : ∀ d ∈ us.flatten, d.BasisFree := by
  intro d hd
  obtain ⟨u, hu, hd⟩ := List.mem_flatten.mp hd
  exact h.free u hu d hd

/-- A front or prelude base is no unit's. -/
theorem not_flatten (h : UnitsOk front us) {j : Key md} (hj : j ∈ basesOf front ∨ IsPre j) :
    j ∉ basesOf us.flatten := by
  intro hm
  obtain ⟨u, hu, hju⟩ := mem_basesOf_flatten.mp hm
  rcases hj with hj | hj
  · exact h.front u hu j hju hj
  · exact h.pre u hu j hju hj

/-- At a split `us = xs ++ u :: ys`: `u`'s bases are neither `xs`'s nor
`ys`'s, and `xs`'s are not `ys`'s. -/
theorem split (h : UnitsOk front us) {xs ys : List (List (Declaration md))}
    {u : List (Declaration md)} (hs : us = xs ++ u :: ys) :
    (∀ j ∈ basesOf u, j ∉ basesOf xs.flatten) ∧ (∀ j ∈ basesOf u, j ∉ basesOf ys.flatten) ∧
      (∀ j ∈ basesOf xs.flatten, j ∉ basesOf ys.flatten) := by
  have hp := h.disj
  rw [hs, List.pairwise_append, List.pairwise_cons] at hp
  obtain ⟨-, ⟨hu, -⟩, hx⟩ := hp
  refine ⟨fun j hj hm => ?_, fun j hj hm => ?_, fun j hj hm => ?_⟩
  · obtain ⟨v, hv, hjv⟩ := mem_basesOf_flatten.mp hm
    exact hx v hv u List.mem_cons_self j hjv hj
  · obtain ⟨v, hv, hjv⟩ := mem_basesOf_flatten.mp hm
    exact hu v hv j hj hjv
  · obtain ⟨v, hv, hjv⟩ := mem_basesOf_flatten.mp hj
    obtain ⟨w, hw, hjw⟩ := mem_basesOf_flatten.mp hm
    exact hx v hv w (List.mem_cons_of_mem _ hw) j hjv hjw

end UnitsOk

end Ix.Kernel
