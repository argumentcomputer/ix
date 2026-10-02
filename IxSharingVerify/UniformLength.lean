import IxSharingVerify.UniformOptimizer

/-!
# Materialized length

Every expression `Prep.build` emits has the length of the option it chose
(Share priced by the dictionary width, telescopes by the merged-header
rule). Consequently, when every table index has Share width `w`, the
serialized length of the uniform optimizer's output (`variableBytes`) is its
model length (`modelBytes = uniformCost`).
-/

namespace Ix.Sharing.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Sharing.Verify.SharingExact (bind_eq_ok sizeInfoWith_app_full sizeInfoWith_app_appCont
  sizeInfoWith_lam_full sizeInfoWith_lam_lamCont sizeInfoWith_all_full sizeInfoWith_all_allCont
  toNat_toUInt64_of_lt mapM_ok_forall₂ forall₂_getElem array_mapM_forall₂ materializeDependent_parts
  pickOption_mem pickOption_filter_ne_share child_eq_getElem indexOfTable_spec)

/-- The continuation of a telescope family in size facts (`(0, full)` for
non-telescopes). -/
def famCont (F : Family) (si : SizeInfo) : Nat × Nat :=
  match F with
  | .app => si.appCont
  | .lam => si.lamCont
  | .all => si.allCont
  | .none => (0, si.full)

/-- A size-fact record that continues no telescope except possibly `F`. -/
def OnlyCont (F : Family) (si : SizeInfo) : Prop :=
  ∀ F', F' ≠ F → famCont F' si = (0, si.full)

theorem rebuild_size (sc : Nat → Nat) {n : Node} {inner side e : Ixon.Expr} {F : Family}
    (hF : n.head.family = F) (hre : rebuildSpineNode n inner side = .ok e) :
    famCont F (sizeInfoWith sc e) =
        ((famCont F (sizeInfoWith sc inner)).1 + 1,
          n.sideExtra + (sizeInfoWith sc side).full + (famCont F (sizeInfoWith sc inner)).2) ∧
      (sizeInfoWith sc e).full = tag4Size ((famCont F (sizeInfoWith sc inner)).1 + 1) +
          (n.sideExtra + (sizeInfoWith sc side).full + (famCont F (sizeInfoWith sc inner)).2) ∧
      OnlyCont F (sizeInfoWith sc e) := by
  unfold rebuildSpineNode at hre
  cases hh : n.head <;> simp only [hh] at hre <;> try cases hre
  all_goals simp only [hh, Head.family] at hF
  all_goals subst hF
  · refine ⟨?_, ?_, ?_⟩
    · simp only [famCont, sizeInfoWith_app_appCont, Node.sideExtra, hh]; congr 1; omega
    · simp only [famCont, sizeInfoWith_app_full, Node.sideExtra, hh]; omega
    · intro F' hF'; cases F' <;> first | exact absurd rfl hF' | rfl
  · refine ⟨?_, ?_, ?_⟩
    · simp only [famCont, sizeInfoWith_lam_lamCont, Node.sideExtra, hh]
    · simp only [famCont, sizeInfoWith_lam_full, Node.sideExtra, hh]
    · intro F' hF'; cases F' <;> first | exact absurd rfl hF' | rfl
  · refine ⟨?_, ?_, ?_⟩
    · simp only [famCont, sizeInfoWith_all_allCont, Node.sideExtra, hh]
    · simp only [famCont, sizeInfoWith_all_full, Node.sideExtra, hh]
    · intro F' hF'; cases F' <;> first | exact absurd rfl hF' | rfl

/-- A telescope rebuilt by `build` around a tail of another family: its
continuation counts the spine nodes and sums their side bytes and the
tail. -/
theorem spineFold_size (sc : Nat → Nat) (F : Family)
    (buildSide : Node → Except SharingError Ixon.Expr) (sz : Node → Nat) :
    ∀ (ns : List Node) (tail e : Ixon.Expr),
      (∀ n ∈ ns, n.head.family = F) →
      (∀ n ∈ ns, ∀ e', buildSide n = .ok e' → (sizeInfoWith sc e').full = sz n) →
      famCont F (sizeInfoWith sc tail) = (0, (sizeInfoWith sc tail).full) →
      ns.foldrM (fun n acc => do let side ← buildSide n; rebuildSpineNode n acc side) tail =
        .ok e →
      famCont F (sizeInfoWith sc e) =
        (ns.length, (ns.map fun n => n.sideExtra + sz n).sum + (sizeInfoWith sc tail).full) ∧
      (ns ≠ [] → (sizeInfoWith sc e).full = tag4Size ns.length +
        ((ns.map fun n => n.sideExtra + sz n).sum + (sizeInfoWith sc tail).full)) ∧
      (ns ≠ [] → OnlyCont F (sizeInfoWith sc e)) := by
  intro ns
  induction ns with
  | nil =>
    intro tail e _ _ htail h
    simp only [List.foldrM_nil] at h
    cases h
    exact ⟨by simp [htail], fun h => absurd rfl h, fun h => absurd rfl h⟩
  | cons n ns ih =>
    intro tail e hfam hsz htail h
    rw [List.foldrM_cons] at h
    obtain ⟨acc, hacc, hstep⟩ := bind_eq_ok h
    obtain ⟨side, hs, hre⟩ := bind_eq_ok hstep
    obtain ⟨hc, _, _⟩ := ih tail acc (fun m hm => hfam m (List.mem_cons_of_mem _ hm))
      (fun m hm => hsz m (List.mem_cons_of_mem _ hm)) htail hacc
    obtain ⟨hc', hfull', honly'⟩ := rebuild_size sc (hfam n List.mem_cons_self) hre
    have hside := hsz n List.mem_cons_self side hs
    rw [hc] at hc' hfull'
    simp only at hc' hfull'
    refine ⟨?_, fun _ => ?_, fun _ => honly'⟩
    · rw [hc', hside]
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      congr 1
      omega
    · rw [hfull', hside]
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-! ## Spine walks and option lists -/

theorem spineWalk_eq (p : Prep) : ∀ (j t : Nat),
    p.spineWalk j t = ((List.range j).map fun k => p.dag.node (spineAt p t k), spineAt p t j) := by
  intro j
  induction j with
  | zero => intro t; rfl
  | succ j ih =>
    intro t
    simp only [Prep.spineWalk, ih]
    congr 1
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    rfl

theorem prefixSides_eq_sum (p : Prep) (cost : Nat → Nat) : ∀ (j t : Nat),
    prefixSides p cost t j = ((List.range j).map fun k => sideCost p cost (spineAt p t k)).sum := by
  intro j
  induction j with
  | zero => intro t; rfl
  | succ j ih =>
    intro t
    simp only [prefixSides, ih, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    rfl

/-- The internal cuts with their choices. -/
def cutsFromC (p : Prep) (w : Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j : Nat) :
    List (Choice × Nat) :=
  (List.range' j (p.spineLen[t]! - j)).filterMap fun j' =>
    if avail (spineAt p t j') then some (.cut j', cutCost p w cost t j') else none

theorem mem_cutsFromC {p : Prep} {w : Nat} {avail : Nat → Bool} {cost : Nat → Nat} {t j : Nat}
    {ch : Choice} {c : Nat} (h : (ch, c) ∈ cutsFromC p w avail cost t j) :
    ∃ k, j ≤ k ∧ k < p.spineLen[t]! ∧ avail (spineAt p t k) = true ∧ ch = .cut k ∧
      c = cutCost p w cost t k := by
  unfold cutsFromC at h
  obtain ⟨k, hk, hkv⟩ := List.mem_filterMap.mp h
  rw [List.mem_range'_1] at hk
  split at hkv
  · rename_i hav
    simp only [Option.some.injEq, Prod.mk.injEq] at hkv
    exact ⟨k, hk.1, by omega, hav, hkv.1.symm, hkv.2.symm⟩
  · cases hkv

theorem cutsFromC_split (p : Prep) (w : Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j k : Nat)
    (hjk : j ≤ k) (hk : k < p.spineLen[t]!) (hav : avail (spineAt p t k) = true)
    (hnone : ∀ k', j ≤ k' → k' < k → avail (spineAt p t k') = false) :
    cutsFromC p w avail cost t j =
      (Choice.cut k, cutCost p w cost t k) :: cutsFromC p w avail cost t (k + 1) := by
  unfold cutsFromC
  rw [show p.spineLen[t]! - j = (k - j) + (1 + (p.spineLen[t]! - (k + 1))) by omega,
    ← List.range'_append_1, ← List.range'_append_1, List.filterMap_append,
    List.filterMap_append]
  have hpre : (List.range' j (k - j)).filterMap (fun j' =>
      if avail (spineAt p t j') then some (Choice.cut j', cutCost p w cost t j') else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro a ha
    rw [List.mem_range'_1] at ha
    rw [hnone a ha.1 (by omega)]
    rfl
  rw [hpre, show j + (k - j) = k by omega]
  simp [hav]

theorem cutsFromC_nil (p : Prep) (w : Nat) (avail : Nat → Bool) (cost : Nat → Nat) (t j : Nat)
    (hnone : ∀ k, j ≤ k → k < p.spineLen[t]! → avail (spineAt p t k) = false) :
    cutsFromC p w avail cost t j = [] := by
  unfold cutsFromC
  rw [List.filterMap_eq_nil_iff]
  intro a ha
  rw [List.mem_range'_1] at ha
  rw [hnone a ha.1 (by omega)]
  rfl

/-- The internal-cut options found by `Prep.cutOptions`, with their choices. -/
theorem PrepWF.cutOptions_pairs {p : Prep} (hp : PrepWF p) {w : Nat} {avail : Nat → Bool}
    (ev : DictEval) (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some w else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u)
    {t : Nat} (ht : t < p.dag.size) (hf : p.family[t]! ≠ .none) (flag : UInt8)
    (hsides : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      ev.sides[spineAt p t k]! =
        prefixSides p (uCost p w avail) (spineAt p t k) (p.spineLen[t]! - k))
    (hbelow : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
      FirstAvail p avail (spineAt p t k) 1 ev.below[spineAt p t k]!) :
    ∀ (fuel j : Nat) (cur : Option Nat) (opts : Array (Choice × Nat × ByteArray)),
      1 ≤ j → j ≤ p.spineLen[t]! → p.spineLen[t]! - j ≤ fuel → FirstAvail p avail t j cur →
      ∃ L : List (Choice × Nat × ByteArray),
        (p.cutOptions ev index width flag p.spineLen[t]!
          (prefixSides p (uCost p w avail) t p.spineLen[t]!) fuel cur opts).toList =
          opts.toList ++ L ∧
        L.map (fun o => (o.1, o.2.1)) = cutsFromC p w avail (uCost p w avail) t j := by
  obtain ⟨_, hk, _, _, _⟩ := hp.spine t ht hf
  intro fuel
  induction fuel with
  | zero =>
    intro j cur opts _ hj hfuel _
    refine ⟨[], by simp [Prep.cutOptions], ?_⟩
    unfold cutsFromC
    rw [show p.spineLen[t]! - j = 0 by omega]
    rfl
  | succ fuel ih =>
    intro j cur opts hj1 hj hfuel hcur
    cases cur with
    | none =>
      exact ⟨[], by simp [Prep.cutOptions], by rw [cutsFromC_nil p w avail _ t j hcur]; rfl⟩
    | some u =>
      obtain ⟨k, hjk, hkl, rfl, hav, hnone⟩ := hcur
      obtain ⟨_, _, hlenk, _⟩ := hk k hkl
      have hcand : tag4Size (p.spineLen[t]! - p.spineLen[spineAt p t k]!) +
          (prefixSides p (uCost p w avail) t p.spineLen[t]! - ev.sides[spineAt p t k]!) +
          (widthOf width (spineAt p t k)).getD 0 = cutCost p w (uCost p w avail) t k := by
        rw [hlenk, hsides k (by omega) hkl, hwidth, ite_eq_left hav]
        have hsplit := prefixSides_add p (uCost p w avail) k (p.spineLen[t]! - k) t
        rw [show k + (p.spineLen[t]! - k) = p.spineLen[t]! by omega] at hsplit
        unfold cutCost
        rw [show p.spineLen[t]! - (p.spineLen[t]! - k) = k by omega, hsplit]
        simp
      have hidx : (index[spineAt p t k]?.getD none).isSome = true := by rw [hindex]; exact hav
      simp only [Prep.cutOptions, hidx, ite_true]
      obtain ⟨L, hL, hcost⟩ := ih (k + 1) _ _ (by omega) (by omega) (by omega)
        (FirstAvail.shift hlenk (hbelow k (by omega) hkl))
      refine ⟨(Choice.cut (p.spineLen[t]! - p.spineLen[spineAt p t k]!),
        tag4Size (p.spineLen[t]! - p.spineLen[spineAt p t k]!) +
          (prefixSides p (uCost p w avail) t p.spineLen[t]! - ev.sides[spineAt p t k]!) +
          (widthOf width (spineAt p t k)).getD 0,
        tag4Bytes flag (p.spineLen[t]! - p.spineLen[spineAt p t k]!)) :: L, ?_, ?_⟩
      · rw [hL]; simp
      · rw [List.map_cons, hcost, cutsFromC_split p w avail _ t j k hjk hkl hav hnone]
        simp only
        rw [hcand, hlenk, show p.spineLen[t]! - (p.spineLen[t]! - k) = k by omega]

/-- The options of a term: its Share (if stored), its inline node, or a
telescope cut of `j` spine nodes, with the model costs. -/
theorem PrepWF.options_mem {p : Prep} (hp : PrepWF p)
    (hempty : p.empty.cost.size = p.dag.size ∧ p.empty.sides.size = p.dag.size ∧
      p.empty.below.size = p.dag.size)
    {w : Nat} {avail : Nat → Bool} (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some w else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u) {t : Nat} (ht : t < p.dag.size)
    {ch : Choice} {c : Nat} {b : ByteArray}
    (h : (ch, c, b) ∈ (p.options (p.evalAll width) index width t).toList) :
    (ch = .share ∧ c = w ∧ avail t = true) ∨
      (ch = .inline ∧ p.family[t]! = .none ∧ c = uInl p w avail t) ∨
      (∃ j, ch = .cut j ∧ p.family[t]! ≠ .none ∧ 1 ≤ j ∧ j ≤ p.spineLen[t]! ∧
        ((j = p.spineLen[t]! ∧ c = naturalCost p (uCost p w avail) t) ∨
          (j < p.spineLen[t]! ∧ avail (spineAt p t j) = true ∧
            c = cutCost p w (uCost p w avail) t j))) := by
  have hrow : ∀ t', t' < p.dag.size → EvalRow p w avail (p.evalAll width) t' :=
    hp.evalFrom_spec width hwidth p.empty hempty _ (fun t ht => by simp [ht])
  have hcost : ∀ c, (p.evalAll width).cost[c]! = uCost p w avail c :=
    fun c => hp.evalAll_cost hempty width hwidth c
  -- the base: the Share option, if any
  have hbase : ∀ x ∈ (match index[t]?.getD none with
      | some i => #[(Choice.share, (widthOf width t).getD 0, tag4Bytes Ixon.Expr.FLAG_SHARE i)]
      | none => (#[] : Array (Choice × Nat × ByteArray))).toList,
      x.1 = .share ∧ x.2.1 = w ∧ avail t = true := by
    intro x hx
    split at hx
    · rename_i i hi
      simp only [List.mem_singleton] at hx
      have hav : avail t = true := by rw [← hindex, hi]; rfl
      subst hx
      exact ⟨rfl, by simp [hwidth, hav], hav⟩
    · simp at hx
  unfold Prep.options at h
  by_cases hf : p.family[t]! = .none
  · have hfb : (p.family[t]! == Family.none) = true := by simp [hf]
    simp only [hfb, ite_true, Array.toList_push, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · obtain ⟨h1, h2, h3⟩ := hbase _ h
      exact Or.inl ⟨h1, h2, h3⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, _⟩ := h
      refine Or.inr (Or.inl ⟨rfl, hf, ?_⟩)
      unfold uInl inlOf
      rw [ite_eq_left hf]
      exact foldl_add_congr _ _ fun c _ => hcost c
  · have hfb : (p.family[t]! == Family.none) = false := by simpa using hf
    simp only [hfb, Bool.false_eq_true, ite_false] at h
    obtain ⟨hs, hb⟩ := (hrow t ht).2 hf
    obtain ⟨hl1, hk, _, htl, _⟩ := hp.spine t ht hf
    have hspine : ∀ k, 1 ≤ k → k < p.spineLen[t]! →
        EvalRow p w avail (p.evalAll width) (spineAt p t k) ∧
          p.family[spineAt p t k]! ≠ .none ∧
          p.spineLen[spineAt p t k]! = p.spineLen[t]! - k := by
      intro k h1 h2
      have hlt' := hp.spineAt_lt ht hf h1 h2
      obtain ⟨_, hkf, hklen, _⟩ := hk k h2
      exact ⟨hrow _ (by omega), by rw [hkf]; exact hf, hklen⟩
    obtain ⟨L, hL, hLc⟩ := hp.cutOptions_pairs (p.evalAll width) index width hwidth
      hindex ht hf (p.dag.node t).head.flag
      (fun k h1 h2 => by
        obtain ⟨hr, hfk, hlenk⟩ := hspine k h1 h2
        rw [(hr.2 hfk).1, hlenk])
      (fun k h1 h2 => by
        obtain ⟨hr, hfk, _⟩ := hspine k h1 h2
        exact (hr.2 hfk).2)
      p.spineLen[t]! 1 _ ((match index[t]?.getD none with
        | some i => #[(Choice.share, (widthOf width t).getD 0, tag4Bytes Ixon.Expr.FLAG_SHARE i)]
        | none => #[]).push (Choice.cut p.spineLen[t]!,
          tag4Size p.spineLen[t]! + (p.evalAll width).sides[t]! +
            (p.evalAll width).cost[p.tail[t]!]!,
          tag4Bytes (p.dag.node t).head.flag p.spineLen[t]!)) (Nat.le_refl _) (by omega)
        (by omega) hb
    rw [← hs] at hL
    have h' := hL ▸ h
    simp only [List.mem_append, Array.toList_push, List.mem_singleton] at h'
    rcases h' with (h' | h') | h'
    · obtain ⟨h1, h2, h3⟩ := hbase _ h'
      exact Or.inl ⟨h1, h2, h3⟩
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, _⟩ := h'
      refine Or.inr (Or.inr ⟨_, rfl, hf, hl1, Nat.le_refl _, Or.inl ⟨rfl, ?_⟩⟩)
      rw [hs, hcost]
      rfl
    · have hm : (ch, c) ∈ cutsFromC p w avail (uCost p w avail) t 1 := by
        rw [← hLc]
        exact List.mem_map.mpr ⟨_, h', rfl⟩
      obtain ⟨k, hk1, hkl, hav, rfl, rfl⟩ := mem_cutsFromC hm
      exact Or.inr (Or.inr ⟨k, rfl, hf, hk1, by omega, Or.inr ⟨hkl, hav, rfl⟩⟩)

theorem share_onlyCont (sc : Nat → Nat) (x : UInt64) (F : Family) :
    OnlyCont F (sizeInfoWith sc (.share x)) := by
  intro F' _; cases F' <;> rfl

theorem children_toList {n : Node} {m : Nat} (h : n.children.size = m) :
    n.children.toList = (List.range m).map n.child := by
  apply List.ext_getElem (by simp [h])
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  rw [child_eq_getElem n k (by simp at h1; omega)]

/-- Every expression `build` emits has the length of the model: its entry
cost for an entry body, its standalone cost otherwise (Shares priced `w`),
and it continues no telescope of another family. -/
theorem PrepWF.build_size {p : Prep} (hp : PrepWF p)
    (hempty : p.empty.cost.size = p.dag.size ∧ p.empty.sides.size = p.dag.size ∧
      p.empty.below.size = p.dag.size)
    {w : Nat} {avail : Nat → Bool} (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some w else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u)
    (sc : Nat → Nat)
    (hsc : ∀ (u i : Nat), index[u]?.getD none = some i → i < UInt64.size ∧ sc i = w) :
    ∀ (fuel : Nat) (entry : Bool) (t : Nat) (e : Ixon.Expr), t < p.dag.size →
      p.build (p.evalAll width) index width entry fuel t = .ok e →
      (sizeInfoWith sc e).full = (if entry then uInl p w avail t else uCost p w avail t) ∧
        OnlyCont p.family[t]! (sizeInfoWith sc e) := by
  have hcost : ∀ c, (p.evalAll width).cost[c]! = uCost p w avail c :=
    fun c => hp.evalAll_cost hempty width hwidth c
  have hshare : ∀ (u i : Nat), index[u]?.getD none = some i →
      (sizeInfoWith sc (.share i.toUInt64)).full = w := by
    intro u i hi
    obtain ⟨hlt, hw⟩ := hsc u i hi
    simp only [sizeInfoWith, SizeInfo.plain, toNat_toUInt64_of_lt hlt, hw]
  intro fuel
  induction fuel with
  | zero => intro entry t e _ h; simp [Prep.build] at h
  | succ fuel ih =>
    intro entry t e ht h
    simp only [Prep.build] at h
    split at h
    · rename_i choice c hpick
      split at h
      · rename_i hcheck
        -- the chosen option and its cost
        obtain ⟨b, hb⟩ := pickOption_mem _ hpick
        have hmem : (choice, c, b) ∈ (p.options (p.evalAll width) index width t).toList := by
          split at hb
          · rw [Array.toList_filter] at hb; exact (List.mem_filter.mp hb).1
          · exact hb
        have hc : (if entry then uInl p w avail t else uCost p w avail t) = c := by
          cases entry with
          | false =>
            simp only [Bool.false_or, beq_iff_eq] at hcheck
            simp only [Bool.false_eq_true, ite_false]
            rw [← hcost, hcheck]
          | true =>
            simp only [ite_true]
            rw [← hp.inlineCost_eq hempty index width hwidth hindex t ht]
            unfold Prep.inlineCost
            simp only [ite_true] at hpick
            rw [hpick]
            rfl
        rw [hc]
        have hopt := hp.options_mem hempty index width hwidth hindex ht hmem
        split at h
        · -- Share
          obtain ⟨_, rfl, _⟩ | ⟨h1, _⟩ | ⟨j, h1, _⟩ := hopt
          · split at h
            · rename_i i hi
              cases h
              exact ⟨hshare t i hi, share_onlyCont sc _ _⟩
            · cases h
          · cases h1
          · cases h1
        · -- inline node
          obtain ⟨h1, _⟩ | ⟨_, hf, hcv⟩ | ⟨j, h1, _⟩ := hopt
          · cases h1
          · rw [hcv]
            unfold uInl inlOf
            rw [ite_eq_left hf]
            have har := hp.dag.arity t ht
            rw [← dag_node_eq ht] at har
            cases hh : (p.dag.node t).head <;> simp only [hh] at h har
            case prj ti f =>
              obtain ⟨v, hv, hpure⟩ := bind_eq_ok h
              cases hpure
              have hc0 : (p.dag.node t).child 0 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              obtain ⟨hvs, _⟩ := ih false _ v (by omega) hv
              simp only [Bool.false_eq_true, ite_false] at hvs
              refine ⟨?_, fun F' _ => by cases F' <;> rfl⟩
              rw [← Array.foldl_toList, children_toList (m := 1) (by simpa [Head.arity] using har)]
              simp [sizeInfoWith, SizeInfo.plain, hvs, Head.ownBytes] <;> omega
            case letE lc =>
              obtain ⟨ty, hty, h2⟩ := bind_eq_ok h
              obtain ⟨v, hv, h3⟩ := bind_eq_ok h2
              obtain ⟨bd, hbd, hpure⟩ := bind_eq_ok h3
              cases hpure
              have hc0 : (p.dag.node t).child 0 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              have hc1 : (p.dag.node t).child 1 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              have hc2 : (p.dag.node t).child 2 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              obtain ⟨hs0, _⟩ := ih false _ ty (by omega) hty
              obtain ⟨hs1, _⟩ := ih false _ v (by omega) hv
              obtain ⟨hs2, _⟩ := ih false _ bd (by omega) hbd
              simp only [Bool.false_eq_true, ite_false] at hs0 hs1 hs2
              refine ⟨?_, fun F' _ => by cases F' <;> rfl⟩
              rw [← Array.foldl_toList, children_toList (m := 3) (by simpa [Head.arity] using har)]
              simp [sizeInfoWith, SizeInfo.plain, hs0, hs1, hs2, Head.ownBytes,
                List.range_succ] <;> omega
            all_goals first
              | (cases h; done)
              | (cases h
                 simp only [Node.toExpr, hh]
                 refine ⟨?_, fun F' _ => by cases F' <;> rfl⟩
                 rw [← Array.foldl_toList,
                   children_toList (m := 0) (by simpa [Head.arity] using har)]
                 simp [sizeInfoWith, SizeInfo.plain, Head.ownBytes])
          · cases h1
        · -- telescope cut
          rename_i j
          obtain ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨j', hj', hf, hj1, hjl, hcase⟩ := hopt
          · cases h1
          · cases h1
          cases hj'
          obtain ⟨_, hk, hend, htl, htf⟩ := hp.spine t ht hf
          have hfam : ∀ n ∈ (List.range j).map (fun k => p.dag.node (spineAt p t k)),
              n.head.family = p.family[t]! := by
            intro n hn
            obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hn
            rw [List.mem_range] at hk'
            obtain ⟨hle, hkf, _, _⟩ := hk k (by omega)
            rw [← hp.family _ (by omega), hkf]
          have hsz : ∀ n ∈ (List.range j).map (fun k => p.dag.node (spineAt p t k)), ∀ e',
              p.build (p.evalAll width) index width false fuel n.sideChild = .ok e' →
              (sizeInfoWith sc e').full = uCost p w avail n.sideChild := by
            intro n hn e' he'
            obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hn
            rw [List.mem_range] at hk'
            obtain ⟨hle, hkf, _, _⟩ := hk k (by omega)
            have hs := hp.sideChild_lt (t := spineAt p t k) (by omega) (by rw [hkf]; exact hf)
            have := (ih false _ e' (by omega) he').1
            simpa using this
          have hsum : (((List.range j).map (fun k => p.dag.node (spineAt p t k))).map
              (fun n => n.sideExtra + uCost p w avail n.sideChild)).sum =
              prefixSides p (uCost p w avail) t j := by
            rw [prefixSides_eq_sum, List.map_map]
            rfl
          have hlen : ((List.range j).map (fun k => p.dag.node (spineAt p t k))).length = j := by
            simp
          have hne : (List.range j).map (fun k => p.dag.node (spineAt p t k)) ≠ [] := by
            intro h0
            have := congrArg List.length h0
            simp at this
            omega
          rw [spineWalk_eq] at h
          split at h
          · cases h
          split at h
          · -- the prefix ends in a Share
            rename_i _ hjlt
            split at h
            · rename_i i hi
              obtain ⟨tl, htl', hfold⟩ := bind_eq_ok h
              cases htl'
              obtain ⟨_, hfull, honly⟩ := spineFold_size sc p.family[t]! _
                (fun n => uCost p w avail n.sideChild) _ _ _ hfam hsz
                (by cases p.family[t]! <;> rfl) hfold
              refine ⟨?_, honly hne⟩
              rw [hfull hne, hlen, hsum, hshare _ i hi]
              rcases hcase with ⟨hjl', _⟩ | ⟨_, _, hcv⟩
              · omega
              · rw [hcv]
                unfold cutCost
                omega
            · obtain ⟨tl, htl', _⟩ := bind_eq_ok h
              cases htl'
          · -- the full spine ends in the natural tail
            rename_i _ hjlt
            have hjeq : j = p.spineLen[t]! := by omega
            obtain ⟨tl, htl', hfold⟩ := bind_eq_ok h
            simp only at htl'
            rw [hjeq, hend] at htl'
            obtain ⟨htfull, htonly⟩ := ih false _ tl (by omega) htl'
            simp only [Bool.false_eq_true, ite_false] at htfull
            obtain ⟨_, hfull, honly⟩ := spineFold_size sc p.family[t]! _
              (fun n => uCost p w avail n.sideChild) _ _ _ hfam hsz
              (htonly _ (Ne.symm htf)) hfold
            refine ⟨?_, honly hne⟩
            rw [hfull hne, hlen, hsum, htfull]
            rcases hcase with ⟨_, hcv⟩ | ⟨hjl', _, _⟩
            · rw [hcv, hjeq]
              unfold naturalCost
              omega
            · omega
      · cases h
    · cases h
theorem forall₂_sum {α β : Type} {R : α → β → Prop} {f : α → Nat} {g : β → Nat} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      (∀ a ∈ xs, ∀ b, R a b → g b = f a) → (ys.map g).sum = (xs.map f).sum
  | _, _, .nil, _ => rfl
  | _, _, .cons hr hs, hfg => by
    simp only [List.map_cons, List.sum_cons, hfg _ List.mem_cons_self _ hr,
      forall₂_sum hs (fun a ha b h => hfg a (List.mem_cons_of_mem _ ha) b h)]

theorem exprsSize_eq_sum (es : Array Ixon.Expr) :
    exprsSize es = (es.toList.map exprSize).sum := by
  unfold exprsSize
  exact array_foldl_add_sum exprSize es

/-- **Serialized length = model length.** When every table index of the
output has Share width `w`, the serialized variable length of the uniform
optimizer's output equals its model length `uniformCost` of the stored set. -/
theorem optimizeUniform_variableBytes {w : Nat} {limits : Limits} {ex : Expanded}
    {res : UniformSharingResult} (h : optimizeUniformExpanded w limits ex = .ok res)
    (hwidth : ∀ i, i < res.result.sharing.size → shareWidth i = w) :
    res.result.variableBytes = res.result.modelBytes := by
  obtain ⟨_, hwf, hroots, _, _, c, _, hfin⟩ := optimizeUniform_parts h
  obtain ⟨hin, _, hstored, _, hmodel, work, hmat, hvar⟩ := uniformFinish_spec hfin
  obtain ⟨hperm, hmodelEq⟩ := optimizeUniform_modelBytes h
  have hp := prepWF_ofDag hwf
  have hempty := ofDag_empty_size ex.dag
  let p := Prep.ofDag ex.dag
  let order := pinnedOrder ex.dag c.facts.deg c.stored
  have hperm' : order.toList.Perm c.stored.toList := pinnedOrder_perm _ _ _
  have hin' : ∀ t ∈ order.toList, t < p.dag.size := fun t ht => hin t (hperm'.subset ht)
  let avail := fun t => decide (t ∈ c.stored.toList)
  have hw : ∀ u, widthOf (c.stored.foldl (fun acc t => acc.set! t (some w))
      (Array.replicate ex.dag.size none)) u = if avail u then some w else none := by
    intro u
    rw [← Array.foldl_toList]
    exact widthOfStored ex.dag.size w c.stored.toList hin u
  have hindex : ∀ u, ((indexOfPairs p.dag.size order.toList.zipIdx)[u]?.getD none).isSome =
      avail u := by
    intro u
    rw [indexOfTable_isSome _ order hin' u]
    simp only [avail, decide_eq_decide]
    exact hperm'.mem_iff
  obtain ⟨hsize, hes, hrs⟩ := materializeDependent_parts p order ex.roots _ limits hmat
  have hlen : res.result.sharing.size = order.size := by
    have := (forall₂_getElem hes).1
    simp only [Array.length_toList] at this
    exact this.symm
  have hsc : ∀ (u i : Nat), (indexOfPairs p.dag.size order.toList.zipIdx)[u]?.getD none = some i →
      i < UInt64.size ∧ tag4Size i = w := by
    intro u i hi
    have hi' := indexOfTable_spec p.dag.size order u i hi
    have hlt := (Array.getElem?_eq_some_iff.mp hi').1
    exact ⟨by omega, hwidth i (by omega)⟩
  have hentries : (res.result.sharing.toList.map exprSize).sum =
      (order.toList.map (uInl p w avail)).sum :=
    forall₂_sum hes (fun t ht e he => by
      have := (hp.build_size hempty _ _ hw hindex tag4Size hsc _ true t e (hin' t ht) he).1
      simpa [exprSize, sizeInfo] using this)
  have hrootsum : (res.result.roots.toList.map exprSize).sum =
      (ex.roots.toList.map (uCost p w avail)).sum :=
    forall₂_sum hrs (fun r hr e he => by
      have := (hp.build_size hempty _ _ hw hindex tag4Size hsc _ false r e (hroots r hr) he).1
      simpa [exprSize, sizeInfo] using this)
  rw [hvar, hmodelEq, exprsSize_eq_sum, exprsSize_eq_sum, hentries, hrootsum, hlen, hstored]
  unfold uniformCost
  have hl : order.size = c.stored.toList.length := by
    rw [← Array.length_toList]; exact hperm'.length_eq
  rw [hl, List.Perm.sum_nat (hperm'.map _)]

end Ix.Sharing.Verify.UniformModel
