import Ix.Compile.Verify.TieredPhase3

/-!
# Tiered construction: phase 3 is never longer than phase 1

The phase-1 bodies and roots are writings of their terms (`gBuild_tree`);
every body only references terms that the allocated order places before it
(`allocate_spec`), so it is also a writing under each prefix dictionary of
phase 3. A writing's length is linear in its Share widths
(`WTree.gcost_eq`), so the phase-1 writings priced at the phase-3 indices
cost the phase-1 layout length minus the reference cost of the phase-1
order plus that of the allocated order, which the guard keeps no larger.
Each phase-3 part is a minimum for its dictionary (`materializeTable_min`),
hence `rematerialize`'s length check can never fail
(`phase3_le_phase1`).
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact

/-! ## Leaves and the length of a writing -/

mutual
/-- The Share leaves of a writing, left to right. -/
def WTree.leaves : WTree → List Nat
  | .share x => [x]
  | .node _ kids => WTree.leavesL kids
  | .tele _ _ sides tail => WTree.leavesL sides ++ WTree.leaves tail
/-- The Share leaves of a list of writings. -/
def WTree.leavesL : List WTree → List Nat
  | [] => []
  | k :: ks => WTree.leaves k ++ WTree.leavesL ks
end

mutual
/-- The length of a writing without its Shares. -/
def WTree.base (p : Prep) : WTree → Nat
  | .share _ => 0
  | .node x kids => (p.dag.node x).head.ownBytes + WTree.baseL p kids
  | .tele x j sides tail =>
    tag4Size j + j * (p.dag.node x).sideExtra + WTree.baseL p sides + WTree.base p tail
/-- The total base length of a list of writings. -/
def WTree.baseL (p : Prep) : List WTree → Nat
  | [] => 0
  | k :: ks => WTree.base p k + WTree.baseL p ks
end

mutual
/-- **Linearity.** A writing's length is its base length plus the widths of
its Share leaves. -/
theorem WTree.gcost_eq (p : Prep) (wd : Nat → Nat) :
    ∀ T : WTree, T.gcost p wd = T.base p + (T.leaves.map wd).sum
  | .share x => by simp [WTree.gcost, WTree.base, WTree.leaves]
  | .node x kids => by
    simp only [WTree.gcost, WTree.base, WTree.leaves, WTree.gcosts_eq' p wd kids]
    omega
  | .tele x j sides tail => by
    simp only [WTree.gcost, WTree.base, WTree.leaves, WTree.gcosts_eq' p wd sides,
      WTree.gcost_eq p wd tail, List.map_append, List.sum_append]
    omega
theorem WTree.gcosts_eq' (p : Prep) (wd : Nat → Nat) :
    ∀ L : List WTree, WTree.gcosts p wd L = WTree.baseL p L + ((WTree.leavesL L).map wd).sum
  | [] => by simp [WTree.gcosts, WTree.baseL, WTree.leavesL]
  | k :: ks => by
    simp only [WTree.gcosts, WTree.baseL, WTree.leavesL, WTree.gcost_eq p wd k,
      WTree.gcosts_eq' p wd ks, List.map_append, List.sum_append]
    omega
end

theorem mem_leavesL_iff {L : List WTree} {y : Nat} :
    y ∈ WTree.leavesL L ↔ ∃ i, ∃ h : i < L.length, y ∈ (L[i]).leaves := by
  induction L with
  | nil => simp [WTree.leavesL]
  | cons a L ih =>
    simp only [WTree.leavesL, List.mem_append, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨0, by simp, h⟩
      · exact ⟨i + 1, by simp; omega, by simpa using h⟩
    · rintro ⟨i, hi, h⟩
      cases i with
      | zero => exact Or.inl h
      | succ i => exact Or.inr ⟨i, by simp at hi; omega, by simpa using h⟩

theorem mem_leavesL {L : List WTree} {k : Nat} (hk : k < L.length) {y : Nat}
    (hy : y ∈ (L[k]).leaves) : y ∈ WTree.leavesL L := by
  induction L generalizing k with
  | nil => cases hk
  | cons a L ih =>
    simp only [WTree.leavesL, List.mem_append]
    cases k with
    | zero => exact Or.inl hy
    | succ k => exact Or.inr (ih (by simp at hk; omega) hy)

/-- A writing stays valid when only its Share leaves are known available. -/
theorem Valid.mono_leaves {p : Prep} {S S' : Nat → Bool} {x : Nat} {T : WTree}
    (h : Valid p S x T) (hS : ∀ y ∈ T.leaves, S' y = true) : Valid p S' x T := by
  induction h with
  | share _ => exact .share (hS _ (by simp [WTree.leaves]))
  | node hf hlen _ ih =>
    exact .node hf hlen fun i hi => ih i hi fun y hy =>
      hS y (by simp only [WTree.leaves]; exact mem_leavesL hi hy)
  | teleCut hf hj1 hj hlen _ _ ih =>
    refine .teleCut hf hj1 hj hlen (fun k hk => ih k hk fun y hy => hS y ?_) (hS _ ?_)
    · simp only [WTree.leaves, List.mem_append]; exact Or.inl (mem_leavesL hk hy)
    · simp [WTree.leaves]
  | teleFull hf hlen _ _ ih iht =>
    refine .teleFull hf hlen (fun k hk => ih k hk fun y hy => hS y ?_)
      (iht fun y hy => hS y ?_)
    · simp only [WTree.leaves, List.mem_append]; exact Or.inl (mem_leavesL hk hy)
    · simp only [WTree.leaves, List.mem_append]; exact Or.inr hy

/-! ## Share lists -/

/-- The Share indices of an expression, left to right. -/
def shareList (e : Ixon.Expr) : List Nat := (shareIndices e #[]).toList

theorem shareIndices_acc : ∀ (e : Ixon.Expr) (acc : Array Nat),
    (shareIndices e acc).toList = acc.toList ++ shareList e := by
  intro e
  induction e with
  | share i => intro acc; simp [shareIndices, shareList]
  | prj _ _ v ih => intro acc; simp only [shareIndices, shareList]; rw [ih, ih #[]]; simp
  | app f a ihf iha =>
    intro acc
    simp only [shareIndices, shareList]
    rw [iha, ihf, iha (shareIndices f #[]), ihf #[]]
    simp
  | lam _ t b iht ihb =>
    intro acc
    simp only [shareIndices, shareList]
    rw [ihb, iht, ihb (shareIndices t #[]), iht #[]]
    simp
  | all _ _ t b iht ihb =>
    intro acc
    simp only [shareIndices, shareList]
    rw [ihb, iht, ihb (shareIndices t #[]), iht #[]]
    simp
  | letE _ t v b iht ihv ihb =>
    intro acc
    simp only [shareIndices, shareList]
    rw [ihb, ihv, iht, ihb (shareIndices v (shareIndices t #[])), ihv (shareIndices t #[]),
      iht #[]]
    simp
  | sort _ | var _ | ref _ _ | recur _ _ | str _ | nat _ =>
    intro acc; simp [shareIndices, shareList]

theorem shareList_app (f a : Ixon.Expr) : shareList (.app f a) = shareList f ++ shareList a := by
  unfold shareList; simp only [shareIndices]; rw [shareIndices_acc]; rfl
theorem shareList_lam (c : Ixon.BinderContract) (t b : Ixon.Expr) :
    shareList (.lam c t b) = shareList t ++ shareList b := by
  unfold shareList; simp only [shareIndices]; rw [shareIndices_acc]; rfl
theorem shareList_all (c : Ixon.BinderContract) (r : Ixon.ValueContract) (t b : Ixon.Expr) :
    shareList (.all c r t b) = shareList t ++ shareList b := by
  unfold shareList; simp only [shareIndices]; rw [shareIndices_acc]; rfl
theorem shareList_prj (ti f : UInt64) (v : Ixon.Expr) : shareList (.prj ti f v) = shareList v := by
  unfold shareList; simp only [shareIndices]
theorem shareList_letE (c : Ixon.LetContract) (t v b : Ixon.Expr) :
    shareList (.letE c t v b) = shareList t ++ shareList v ++ shareList b := by
  unfold shareList; simp only [shareIndices]; rw [shareIndices_acc, shareIndices_acc]; rfl
theorem shareList_share (i : UInt64) : shareList (.share i) = [i.toNat] := by
  simp [shareList, shareIndices]

theorem rebuild_shares {n : Node} {inner side e : Ixon.Expr} (h : rebuildSpineNode n inner side = .ok e) :
    (shareList e).Perm (shareList side ++ shareList inner) := by
  unfold rebuildSpineNode at h
  cases hh : n.head <;> simp only [hh] at h <;> try cases h
  · rw [shareList_app]; exact List.perm_append_comm
  · rw [shareList_lam]
  · rw [shareList_all]

/-- The Shares of a rebuilt telescope are those of its sides and its tail. -/
theorem spineFold_shares' (buildSide : Node → Except SharingError Ixon.Expr) (S : Node → List Nat) :
    ∀ (ns : List Node) (tail e : Ixon.Expr),
      (∀ n ∈ ns, ∀ e', buildSide n = .ok e' → (shareList e').Perm (S n)) →
      ns.foldrM (fun n acc => do let side ← buildSide n; rebuildSpineNode n acc side) tail =
        .ok e →
      (shareList e).Perm (ns.flatMap S ++ shareList tail) := by
  intro ns
  induction ns with
  | nil => intro tail e _ h; simp only [List.foldrM_nil] at h; cases h; simp
  | cons n ns ih =>
    intro tail e hS h
    rw [List.foldrM_cons] at h
    obtain ⟨acc, hacc, hstep⟩ := Ix.Compile.Verify.SharingExact.bind_eq_ok h
    obtain ⟨side, hs, hre⟩ := Ix.Compile.Verify.SharingExact.bind_eq_ok hstep
    have h1 := ih tail acc (fun m hm => hS m (List.mem_cons_of_mem _ hm)) hacc
    have h2 := rebuild_shares hre
    have h3 := hS n List.mem_cons_self side hs
    refine h2.trans ?_
    simp only [List.flatMap_cons, List.append_assoc]
    exact h3.append h1

/-- Every side of a successfully rebuilt telescope was built. -/
theorem spineFold_sides_ok (buildSide : Node → Except SharingError Ixon.Expr) :
    ∀ (ns : List Node) (tail e : Ixon.Expr),
      ns.foldrM (fun n acc => do let side ← buildSide n; rebuildSpineNode n acc side) tail =
        .ok e → ∀ n ∈ ns, ∃ e', buildSide n = .ok e' := by
  intro ns
  induction ns with
  | nil => intro _ _ _ n hn; cases hn
  | cons m ns ih =>
    intro tail e h n hn
    rw [List.foldrM_cons] at h
    obtain ⟨acc, hacc, hstep⟩ := Ix.Compile.Verify.SharingExact.bind_eq_ok h
    obtain ⟨side, hs, _⟩ := Ix.Compile.Verify.SharingExact.bind_eq_ok hstep
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨side, hs⟩
    · exact ih tail acc hacc n hn

theorem leavesL_map (f : Nat → Nat) :
    ∀ L : List WTree, (WTree.leavesL L).map f = L.flatMap fun T => T.leaves.map f
  | [] => by simp [WTree.leavesL]
  | k :: ks => by simp [WTree.leavesL, leavesL_map f ks]

/-! ## The writing a build emits -/

/-- `T` is the writing of the expression `e` built for `t`: a valid writing
with the dictionary `avail`, inline if it is an entry body, with the Shares
of `e` as its leaves (by index), and with the length of `e` under every Share
pricing `sc` that matches leaf widths `wd'`. -/
def TreeOf (p : Prep) (avail : Nat → Bool) (index : Array (Option Nat)) (entry : Bool) (t : Nat)
    (e : Ixon.Expr) (T : WTree) : Prop :=
  Valid p avail t T ∧ (entry = true → T.isShare = false) ∧
    (T.leaves.map fun u => (index[u]?.getD none).getD 0).Perm (shareList e) ∧
    ∀ (sc wd' : Nat → Nat), (∀ (u i : Nat), index[u]?.getD none = some i → sc i = wd' u) →
      (sizeInfoWith sc e).full = T.gcost p wd' ∧ OnlyCont p.family[t]! (sizeInfoWith sc e)

open Ix.Compile.Verify.SharingExact (bind_eq_ok toNat_toUInt64_of_lt pickOption_mem
  pickOption_filter_ne_share) in
/-- **The writing of a build.** Every expression `build` emits (against an
evaluation with the model rows of the dictionary) is a writing of its term
whose length, under any Share pricing, is the writing's length at the
matching leaf widths, and whose leaves are its Shares. -/
theorem PrepWF.gBuild_tree {p : Prep} (hp : PrepWF p)
    {wd : Nat → Nat} {avail : Nat → Bool} (ev : DictEval) (hev : GEvalOK p wd avail ev)
    (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (hindex : ∀ (u : Nat), (index[u]?.getD none).isSome = avail u)
    (hidx : ∀ (u i : Nat), index[u]?.getD none = some i → i < UInt64.size) :
    ∀ (fuel : Nat) (entry : Bool) (t : Nat) (e : Ixon.Expr), t < p.dag.size →
      p.build ev index width entry fuel t = .ok e → ∃ T, TreeOf p avail index entry t e T := by
  have hshare : ∀ (u i : Nat) (sc wd' : Nat → Nat), index[u]?.getD none = some i →
      (∀ (u i : Nat), index[u]?.getD none = some i → sc i = wd' u) →
      (sizeInfoWith sc (.share i.toUInt64)).full = wd' u := by
    intro u i sc wd' hi hsc
    simp only [sizeInfoWith, SizeInfo.plain, toNat_toUInt64_of_lt (hidx u i hi), hsc u i hi]
  have hleaf : ∀ (u i : Nat), index[u]?.getD none = some i →
      ([u].map fun u => (index[u]?.getD none).getD 0).Perm (shareList (.share i.toUInt64)) := by
    intro u i hi
    rw [shareList_share, toNat_toUInt64_of_lt (hidx u i hi)]
    simp [hi]
  intro fuel
  induction fuel with
  | zero => intro entry t e _ h; simp [Prep.build] at h
  | succ fuel ih =>
    intro entry t e ht h
    -- the writings of the children, chosen once per term
    have hex : ∀ c e', c < p.dag.size → p.build ev index width false fuel c = .ok e' →
        ∃ T, TreeOf p avail index false c e' T := fun c e' hc he => ih false c e' hc he
    classical
    let Tof : Nat → WTree := fun c =>
      if hc : ∃ e', c < p.dag.size ∧ p.build ev index width false fuel c = .ok e' then
        Classical.choose (hex c (Classical.choose hc) (Classical.choose_spec hc).1
          (Classical.choose_spec hc).2)
      else default
    have hTof : ∀ c e', c < p.dag.size → p.build ev index width false fuel c = .ok e' →
        TreeOf p avail index false c e' (Tof c) := by
      intro c e' hc he
      have hc' : ∃ e', c < p.dag.size ∧ p.build ev index width false fuel c = .ok e' :=
        ⟨e', hc, he⟩
      simp only [Tof, dif_pos hc']
      have hsame : Classical.choose hc' = e' := by
        have h2 : (Except.ok (Classical.choose hc') : Except SharingError Ixon.Expr) = .ok e' :=
          (Classical.choose_spec hc').2.symm.trans he
        exact Except.ok.inj h2
      have := Classical.choose_spec (hex c (Classical.choose hc') (Classical.choose_spec hc').1
        (Classical.choose_spec hc').2)
      have key : ∀ x T, x = e' → TreeOf p avail index false c x T → TreeOf p avail index false c e' T := by
        intro x T hx hT; subst hx; exact hT
      exact key _ _ hsame this
    simp only [Prep.build] at h
    split at h
    · rename_i choice c hpick
      have hent : entry = true → choice ≠ .share := by
        intro he
        subst he
        simp only [if_true] at hpick
        exact pickOption_filter_ne_share _ hpick
      split at h
      · rename_i hcheck
        obtain ⟨b, hb⟩ := pickOption_mem _ hpick
        have hmem : (choice, c, b) ∈ (p.options ev index width t).toList := by
          split at hb
          · rw [Array.toList_filter] at hb; exact (List.mem_filter.mp hb).1
          · exact hb
        have hopt := hp.gOptions_mem ev hev index width hwidth hindex ht hmem
        split at h
        · -- Share
          split at h
          · rename_i i hi
            cases h
            refine ⟨.share t, .share (by rw [← hindex, hi]; rfl), fun he => absurd rfl (hent he),
              hleaf t i hi, fun sc wd' hsc => ⟨hshare t i sc wd' hi hsc, share_onlyCont sc _ _⟩⟩
          · cases h
        · -- inline node
          obtain ⟨h1, _⟩ | ⟨_, hf, _⟩ | ⟨j, h1, _⟩ := hopt
          · cases h1
          · have har := hp.dag.arity t ht
            rw [← dag_node_eq ht] at har
            cases hh : (p.dag.node t).head <;> simp only [hh] at h har
            case prj ti f =>
              obtain ⟨v, hv, hpure⟩ := bind_eq_ok h
              cases hpure
              have hc0 : (p.dag.node t).child 0 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              obtain ⟨hvV, -, hvL, hvS⟩ := hTof _ v (by omega) hv
              refine ⟨.node t [Tof ((p.dag.node t).child 0)],
                .node hf (by simp [hh, Head.arity]) (fun i hi => ?_), fun _ => rfl, ?_,
                fun sc wd' hsc => ⟨?_, fun F' _ => by cases F' <;> rfl⟩⟩
              · have : i = 0 := by simpa using hi
                subst this
                exact hvV
              · simp only [WTree.leaves, WTree.leavesL, List.append_nil, shareList_prj]
                exact hvL
              · simp [WTree.gcost, WTree.gcosts, sizeInfoWith, SizeInfo.plain, Head.ownBytes, hh,
                  (hvS sc wd' hsc).1] <;> omega
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
              obtain ⟨h0V, -, h0L, h0S⟩ := hTof _ ty (by omega) hty
              obtain ⟨h1V, -, h1L, h1S⟩ := hTof _ v (by omega) hv
              obtain ⟨h2V, -, h2L, h2S⟩ := hTof _ bd (by omega) hbd
              refine ⟨.node t [Tof ((p.dag.node t).child 0), Tof ((p.dag.node t).child 1),
                  Tof ((p.dag.node t).child 2)],
                .node hf (by simp [hh, Head.arity]) (fun i hi => ?_), fun _ => rfl, ?_,
                fun sc wd' hsc => ⟨?_, fun F' _ => by cases F' <;> rfl⟩⟩
              · simp only [List.length_cons, List.length_nil] at hi
                rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
                · exact h0V
                · exact h1V
                · exact h2V
              · simp only [WTree.leaves, WTree.leavesL, List.append_nil, shareList_letE,
                  List.map_append]
                rw [List.append_assoc]
                exact h0L.append (h1L.append h2L)
              · simp [WTree.gcost, WTree.gcosts, sizeInfoWith, SizeInfo.plain, Head.ownBytes, hh,
                  (h0S sc wd' hsc).1, (h1S sc wd' hsc).1, (h2S sc wd' hsc).1] <;> omega
            all_goals first
              | (cases h; done)
              | (cases h
                 simp only [Node.toExpr, hh]
                 refine ⟨.node t [], .node hf (by simp [hh, Head.arity])
                   (fun i hi => absurd hi (by simp)), fun _ => rfl, ?_,
                   fun sc wd' hsc => ⟨?_, fun F' _ => by cases F' <;> rfl⟩⟩
                 · simp [WTree.leaves, WTree.leavesL, shareList, shareIndices]
                 · simp [WTree.gcost, WTree.gcosts, hh, sizeInfoWith, SizeInfo.plain,
                     Head.ownBytes])
          · cases h1
        · -- telescope cut
          rename_i j
          obtain ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨j', hj', hf, hj1, hjl, hcase⟩ := hopt
          · cases h1
          · cases h1
          cases hj'
          obtain ⟨_, hk, hend, htl, htf⟩ := hp.spine t ht hf
          let ns := (List.range j).map (fun k => p.dag.node (spineAt p t k))
          let sides := (List.range j).map (fun k => Tof (sideAt p t k))
          let idx : Nat → Nat := fun u => (index[u]?.getD none).getD 0
          have hfam : ∀ n ∈ ns, n.head.family = p.family[t]! := by
            intro n hn
            obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hn
            rw [List.mem_range] at hk'
            obtain ⟨hle, hkf, _, _⟩ := hk k (by omega)
            rw [← hp.family _ (by omega), hkf]
          have hsideLt : ∀ k, k < j → sideAt p t k < p.dag.size := fun k hk' => by
            have := hp.sideAt_lt ht hf (k := k) (by omega); omega
          have hlen : ns.length = j := by simp [ns]
          have hne : ns ≠ [] := by
            intro h0
            have := congrArg List.length h0
            simp [ns] at this
            omega
          -- the side writings
          have hsideTree : ∀ n ∈ ns, ∀ e',
              p.build ev index width false fuel n.sideChild = .ok e' →
              TreeOf p avail index false n.sideChild e' (Tof n.sideChild) := by
            intro n hn e' he'
            obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hn
            rw [List.mem_range] at hk'
            exact hTof _ e' (hsideLt k hk') he'
          have hsum : ∀ (wd' : Nat → Nat), (ns.map fun n =>
              n.sideExtra + (Tof n.sideChild).gcost p wd').sum =
              j * (p.dag.node t).sideExtra + WTree.gcosts p wd' sides := by
            intro wd'
            have : ∀ k ∈ List.range j, (p.dag.node (spineAt p t k)).sideExtra +
                (Tof (p.dag.node (spineAt p t k)).sideChild).gcost p wd' =
                (p.dag.node t).sideExtra + (Tof (sideAt p t k)).gcost p wd' := by
              intro k hk'
              rw [List.mem_range] at hk'
              rw [hp.sideExtra_spine ht hf (by omega)]
              rfl
            simp only [ns, List.map_map]
            rw [show ((fun n : Node => n.sideExtra + (Tof n.sideChild).gcost p wd') ∘
                fun k => p.dag.node (spineAt p t k)) = fun k =>
                (p.dag.node (spineAt p t k)).sideExtra +
                  (Tof (p.dag.node (spineAt p t k)).sideChild).gcost p wd' from rfl,
              List.map_congr_left this, sum_map_const_add, WTree.gcosts_eq]
            simp [sides, List.map_map]
            rfl
          have hflat : ns.flatMap (fun n => (Tof n.sideChild).leaves.map idx) =
              (WTree.leavesL sides).map idx := by
            rw [leavesL_map]
            simp only [ns, sides, List.flatMap_map]
            rfl
          have hsidesValid : ∀ (k : Nat) (h : k < sides.length),
              (∃ e', p.build ev index width false fuel (sideAt p t k) = .ok e') →
              Valid p avail (sideAt p t k) sides[k] := by
            intro k hk' ⟨e', he'⟩
            simp only [sides, List.getElem_map, List.getElem_range]
            exact (hTof _ e' (hsideLt k (by simpa [sides] using hk')) he').1
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
              have hsideOK : ∀ (k : Nat), k < j →
                  ∃ e', p.build ev index width false fuel (sideAt p t k) = .ok e' := by
                intro k hk'
                exact spineFold_sides_ok _ ns _ _ hfold _
                  (List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩)
              have hcur : avail (spineAt p t j) = true := by rw [← hindex, hi]; rfl
              refine ⟨.tele t j sides (.share (spineAt p t j)),
                .teleCut hf hj1 hjlt (by simp [sides])
                  (fun k hk' => hsidesValid k hk' (hsideOK k (by simpa [sides] using hk'))) hcur,
                fun _ => rfl, ?_, fun sc wd' hsc => ?_⟩
              · have hsh := spineFold_shares' _ (fun n => (Tof n.sideChild).leaves.map idx) ns _ _
                  (fun n hn e' he' => ((hsideTree n hn e' he').2.2.1).symm) hfold
                simp only [WTree.leaves, List.map_append]
                rw [← hflat]
                refine List.Perm.trans ?_ hsh.symm
                exact List.Perm.append (List.Perm.refl _) (hleaf _ i hi)
              · obtain ⟨_, hfull, honly⟩ := spineFold_size sc p.family[t]! _
                  (fun n => (Tof n.sideChild).gcost p wd') _ _ _ hfam
                  (fun n hn e' he' => ((hsideTree n hn e' he').2.2.2 sc wd' hsc).1)
                  (by cases p.family[t]! <;> rfl) hfold
                refine ⟨?_, honly hne⟩
                rw [hfull hne, hlen, hsum wd', hshare _ i sc wd' hi hsc]
                simp only [WTree.gcost]
                omega
            · obtain ⟨tl, htl', _⟩ := bind_eq_ok h
              cases htl'
          · -- the full spine ends in the natural tail
            rename_i _ hjlt
            have hjeq : j = p.spineLen[t]! := by omega
            obtain ⟨tl, htl', hfold⟩ := bind_eq_ok h
            simp only at htl'
            rw [hjeq, hend] at htl'
            have hsideOK : ∀ (k : Nat), k < j →
                ∃ e', p.build ev index width false fuel (sideAt p t k) = .ok e' := by
              intro k hk'
              exact spineFold_sides_ok _ ns _ _ hfold _
                (List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩)
            obtain ⟨htV, -, htL, htS⟩ := hTof _ tl (by omega) htl'
            have hvalid : Valid p avail t (.tele t p.spineLen[t]! sides (Tof p.tail[t]!)) :=
              .teleFull hf (by simp [sides, hjeq])
                (fun k hk' => hsidesValid k hk' (hsideOK k (by simpa [sides] using hk'))) htV
            rw [← hjeq] at hvalid
            refine ⟨.tele t j sides (Tof p.tail[t]!), hvalid, fun _ => rfl, ?_,
              fun sc wd' hsc => ?_⟩
            · have hsh := spineFold_shares' _ (fun n => (Tof n.sideChild).leaves.map idx) ns _ _
                (fun n hn e' he' => ((hsideTree n hn e' he').2.2.1).symm) hfold
              simp only [WTree.leaves, List.map_append]
              rw [← hflat]
              exact List.Perm.trans (List.Perm.append (List.Perm.refl _) htL) hsh.symm
            · obtain ⟨htfull, htonly⟩ := htS sc wd' hsc
              obtain ⟨_, hfull, honly⟩ := spineFold_size sc p.family[t]! _
                (fun n => (Tof n.sideChild).gcost p wd') _ _ _ hfam
                (fun n hn e' he' => ((hsideTree n hn e' he').2.2.2 sc wd' hsc).1)
                (htonly _ (Ne.symm htf)) hfold
              refine ⟨?_, honly hne⟩
              rw [hfull hne, hlen, hsum wd', htfull]
              simp only [WTree.gcost]
              omega

      · cases h
    · cases h

/-- The leaves of a valid writing are available. -/
theorem Valid.leaves_avail {p : Prep} {S : Nat → Bool} {x : Nat} {T : WTree}
    (h : Valid p S x T) : ∀ y ∈ T.leaves, S y = true := by
  induction h with
  | share hS => intro y hy; simp [WTree.leaves] at hy; subst hy; exact hS
  | node _ _ _ ih =>
    intro y hy
    simp only [WTree.leaves] at hy
    obtain ⟨i, hi, hyi⟩ := mem_leavesL_iff.mp hy
    exact ih i hi y hyi
  | teleCut _ _ _ _ _ hS ih =>
    intro y hy
    simp only [WTree.leaves, List.mem_append] at hy
    rcases hy with hy | hy
    · obtain ⟨i, hi, hyi⟩ := mem_leavesL_iff.mp hy
      exact ih i hi y hyi
    · simp [WTree.leaves] at hy; subst hy; exact hS
  | teleFull _ _ _ _ ih iht =>
    intro y hy
    simp only [WTree.leaves, List.mem_append] at hy
    rcases hy with hy | hy
    · obtain ⟨i, hi, hyi⟩ := mem_leavesL_iff.mp hy
      exact ih i hi y hyi
    · exact iht y hy

/-! ## The phase-1 writings -/

open Ix.Compile.Verify.SharingExact (materializeDependent_parts indexOfTable_spec) in
/-- The phase-1 table bodies and roots are writings with the phase-1
dictionary (its stored set, Shares by phase-1 index). -/
theorem phase1_trees {w : Nat} {limits : Limits} {ex : Expanded} {u : UniformSharingResult}
    (hu : optimizeUniformExpanded w limits ex = .ok u) :
    DagWF ex.dag ∧ (∀ r ∈ ex.roots.toList, r < ex.dag.size) ∧
    (∀ t ∈ u.result.tableTerms.toList, t < ex.dag.size) ∧
    u.result.tableTerms.size < UInt64.size ∧
    (∀ t, ((indexOfPairs ex.dag.size u.result.tableTerms.toList.zipIdx)[t]?.getD none).isSome =
      decide (t ∈ u.result.tableTerms.toList)) ∧
    List.Forall₂ (fun t e => ∃ T, TreeOf (Prep.ofDag ex.dag)
        (fun t => decide (t ∈ u.result.tableTerms.toList))
        (indexOfPairs ex.dag.size u.result.tableTerms.toList.zipIdx) true t e T)
      u.result.tableTerms.toList u.result.sharing.toList ∧
    List.Forall₂ (fun r e => ∃ T, TreeOf (Prep.ofDag ex.dag)
        (fun t => decide (t ∈ u.result.tableTerms.toList))
        (indexOfPairs ex.dag.size u.result.tableTerms.toList.zipIdx) false r e T)
      ex.roots.toList u.result.roots.toList := by
  obtain ⟨_, hwf, hroots, _, _, c, _, hfin⟩ := optimizeUniform_parts hu
  obtain ⟨hin, _, _, htable, _, work, hmat, _⟩ := uniformFinish_spec hfin
  have hp := prepWF_ofDag hwf
  have hperm : u.result.tableTerms.toList.Perm c.stored.toList := by
    rw [htable]; exact pinnedOrder_perm _ _ _
  have hin' : ∀ t ∈ u.result.tableTerms.toList, t < ex.dag.size :=
    fun t ht => hin t (hperm.subset ht)
  obtain ⟨hsize, hents, hrts⟩ := materializeDependent_parts _ _ _ _ _ hmat
  rw [← htable] at hsize hents hrts
  let width1 := c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)
  let avail1 := fun t => decide (t ∈ u.result.tableTerms.toList)
  let index1 := indexOfPairs ex.dag.size u.result.tableTerms.toList.zipIdx
  have hwidth : ∀ t, widthOf width1 t = if avail1 t then some w else none := by
    intro t
    simp only [width1, avail1]
    rw [← Array.foldl_toList, widthOfStored ex.dag.size w c.stored.toList hin t]
    simp only [hperm.mem_iff]
  have hindex : ∀ t, (index1[t]?.getD none).isSome = avail1 t :=
    fun t => indexOfTable_isSome _ _ hin' t
  have hidx : ∀ (t i : Nat), index1[t]?.getD none = some i → i < UInt64.size := by
    intro t i hi
    have := indexOfTable_spec _ _ t i hi
    have := (Array.getElem?_eq_some_iff.mp this).1
    omega
  have hev := hp.evalAll_ok (ofDag_empty_size ex.dag) (wd := fun _ => w) (avail := avail1)
    width1 hwidth
  refine ⟨hwf, hroots, hin', hsize, hindex, ?_, ?_⟩
  · refine Ix.Compile.Verify.Tiered.forall₂_imp_mem hents fun t ht e he => ?_
    exact hp.gBuild_tree _ hev index1 width1 hwidth hindex hidx _ true t e (hin' t ht) he
  · refine Ix.Compile.Verify.Tiered.forall₂_imp_mem hrts fun r hr e he => ?_
    exact hp.gBuild_tree _ hev index1 width1 hwidth hindex hidx _ false r e (hroots r hr) he

end Ix.Compile.Verify.UniformModel

namespace Ix.Compile.Verify.Tiered

open Ix.Sharing.Exact
open Ix.Compile.Verify.UniformModel
open Ix.Compile.Verify.SharingExact (indexOfPrefix_spec indexOfTable_spec)

/-! ## Sums -/

theorem sum_range_array (arr : Array Nat) (F : Nat → Nat) :
    ((List.range arr.size).map fun i => F arr[i]!).sum = (arr.toList.map F).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  rw [getElem!_pos arr i (by simpa using h1)]

theorem refCost_eq_sum (layout : ShareLayout) (weight : Nat → Nat) (ord : Array Nat) :
    refCost layout weight ord =
      ((List.range ord.size).map fun k => weight ord[k]! * layout.widthAt k).sum := by
  unfold refCost
  rw [← Array.foldl_toList, Ix.Compile.Verify.UniformModel.foldl_add_eq_sum, Nat.zero_add]
  congr 1
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range, Array.toList_zipIdx, List.getElem_zipIdx]
  rw [getElem!_pos ord k (by simpa using h2)]
  simp

theorem sum_map_zero : ∀ (l : List Nat), (l.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: l => by simp [sum_map_zero l]

theorem sum_count (N : Nat) (g : Nat → Nat) :
    ∀ (A : List Nat), (∀ j ∈ A, j < N) →
      ((List.range N).map fun i => A.count i * g i).sum = (A.map g).sum := by
  intro A
  induction A with
  | nil => intro _; simp only [List.count_nil, Nat.zero_mul, List.map_nil, List.sum_nil]; exact sum_map_zero _
  | cons a A ih =>
    intro hA
    have ha := hA a List.mem_cons_self
    have h1 : ((List.range N).map fun i => (a :: A).count i * g i) =
        List.zipWith (· + ·) ((List.range N).map fun i => A.count i * g i)
          ((List.range N).map fun i => if a = i then g i else 0) := by
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.count_cons]
      by_cases hai : a = i
      · subst hai; simp [Nat.add_mul]
      · simp [hai, Ne.symm hai]
    have hsplit : ∀ (l1 l2 : List Nat), l1.length = l2.length →
        (List.zipWith (· + ·) l1 l2).sum = l1.sum + l2.sum := by
      intro l1
      induction l1 with
      | nil => intro l2 h; cases l2 <;> simp_all
      | cons x xs ih' =>
        intro l2 h
        cases l2 with
        | nil => simp at h
        | cons y ys =>
          simp only [List.zipWith_cons_cons, List.sum_cons]
          rw [ih' ys (by simpa using h)]
          omega
    have hone : ((List.range N).map fun i => if a = i then g i else 0).sum = g a := by
      have : ∀ M, a < M → ((List.range M).map fun i => if a = i then g i else 0).sum = g a := by
        intro M
        induction M with
        | zero => intro h; omega
        | succ M ihM =>
          intro h
          rw [List.range_succ, List.map_append, List.sum_append]
          by_cases haM : a = M
          · subst haM
            have : ((List.range a).map fun i => if a = i then g i else 0).sum = 0 := by
              rw [List.map_congr_left (g := fun _ => 0) (fun i hi => by
                rw [List.mem_range] at hi; simp [show a ≠ i by omega])]
              exact sum_map_zero _
            simp [this]
          · rw [ihM (by omega)]
            simp [haM]
      exact this N ha
    rw [h1, hsplit _ _ (by simp), ih (fun j hj => hA j (List.mem_cons_of_mem _ hj)), hone]
    simp
    omega

theorem sum_map_flatMap {α : Type} (f : α → List Nat) (g : Nat → Nat) :
    ∀ (L : List α), ((L.flatMap f).map g).sum = (L.map fun x => ((f x).map g).sum).sum
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_map_flatMap f g xs]

/-! ## Parts and prefix lookups -/

/-- One part: a re-materialized part no longer than any writing for its
dictionary, against a phase-1 writing whose leaves are in that dictionary. -/
theorem part_le {P : Prep} {S S' : Nat → Bool} {t : Nat} {T : WTree} {wd1 wd3 : Nat → Nat}
    {size1 size3 : Nat} (hT : Valid P S t T) (hleaves : ∀ l ∈ T.leaves, S' l = true)
    (hmin : ∀ T', Valid P S' t T' → size3 ≤ T'.gcost P wd3) (h1 : size1 = T.gcost P wd1) :
    size3 + (T.leaves.map wd1).sum ≤ size1 + (T.leaves.map wd3).sum := by
  have := hmin T (hT.mono_leaves hleaves)
  rw [WTree.gcost_eq] at this h1
  omega

/-- In a table without repeats, the prefix dictionary of `k` entries maps
entry `j < k` to `j`. -/
theorem prefix_lookup {n : Nat} {table : Array Nat} (hnd : table.toList.Nodup)
    {j k d : Nat} (hj : table[j]? = some d) (hjk : j < k) (hd : d < n) :
    (indexOfPrefix n table k)[d]?.getD none = some j := by
  have hjs : j < table.size := (Array.getElem?_eq_some_iff.mp hj).1
  have hsome : ((indexOfPrefix n table k)[d]?.getD none).isSome = true := by
    unfold indexOfPrefix indexOfPairs
    apply indexOfPairs_isSome _ _ d (by simp; exact hd)
    refine Or.inr ⟨j, List.mem_zipIdx_iff_getElem?.mpr ?_⟩
    simp only [List.getElem?_take]
    rw [if_pos hjk]
    simpa using hj
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hik, hti⟩ := indexOfPrefix_spec n table k d i hi
  have his : i < table.size := (Array.getElem?_eq_some_iff.mp hti).1
  have : i = j := getBang_inj hnd his hjs (by
    rw [getElem!_pos table i his, getElem!_pos table j hjs]
    have h1 := (Array.getElem?_eq_some_iff.mp hti).2
    have h2 := (Array.getElem?_eq_some_iff.mp hj).2
    rw [h1, h2])
  rw [hi, this]

/-! ## Phase 3 is never longer than phase 1 -/

/-- **Phase 3 ≤ phase 1, by construction.** After a successful phase 1 and
phase 2, the re-materialized table and roots are at most as long, priced by
the layout, as the phase-1 output: every phase-1 body and root is a writing
for its phase-3 dictionary (the allocated order places every body reference
first), each phase-3 part is a minimum for its dictionary, and the guard
keeps the reference cost of the allocated order at most the phase-1
order's. So `rematerialize`'s length check never fails. -/
theorem phase3_le_phase1 {layout : ShareLayout} {limits : Limits} {ex : Expanded} {w : Nat}
    {u : UniformSharingResult} {a : Allocation} {entries rs : Array Ixon.Expr}
    {predicted work : Nat}
    (hu : optimizeUniformExpanded w limits ex = .ok u)
    (ha : allocate layout limits ex.dag (graphFacts ex.dag ex.roots).deg u.result.tableTerms
      u.result.sharing u.result.roots = .ok a)
    (hm : materializeTable (Prep.ofDag ex.dag) a.order ex.roots limits layout.widthAt =
      .ok (entries, rs, predicted, work)) :
    predicted ≤ layoutBytes layout u.result.sharing u.result.roots := by
  obtain ⟨hwf, hroots, hin1, hsize1, hindex1, hents, hrts⟩ := phase1_trees hu
  obtain ⟨hnd1, -, hperm, hback, -, -, -, -, -, -⟩ := allocate_spec ha
  have hrcEq := (allocate_spec ha).2.2.2.2.2.1
  have hrfEq := (allocate_spec ha).2.2.2.2.2.2.1
  have hrcLe := (allocate_spec ha).2.2.2.2.2.2.2.1
  obtain ⟨hsz3, -, hr3, hpred⟩ := materializeTable_spec hwf hroots hm
  obtain ⟨hmin3, hrmin3⟩ := materializeTable_min hwf hroots hm
  -- names
  generalize ho1 : u.result.tableTerms = order1 at *
  generalize he1 : u.result.sharing = entries1 at *
  generalize hr1 : u.result.roots = roots1 at *
  generalize ho : a.order = order at *
  let n := ex.dag.size
  let N := order1.size
  let index1 := indexOfPairs n order1.toList.zipIdx
  let idx1 : Nat → Nat := fun t => (index1[t]?.getD none).getD 0
  let avail1 : Nat → Bool := fun t => decide (t ∈ order1.toList)
  let pos3 : Nat → Nat := fun t => ((indexOfPrefix n order order.size)[t]?.getD none).getD 0
  let wA : Nat → Nat := fun j => layout.widthAt j
  let wB : Nat → Nat := fun j => layout.widthAt (pos3 order1[j]!)
  have hnd : order.toList.Nodup := hperm.nodup_iff.mpr hnd1
  have hNsz : order.size = N := by
    have := hperm.length_eq; simpa using this
  -- available terms are table terms at their index
  have hK1 : ∀ l, avail1 l = true → idx1 l < N ∧ order1[idx1 l]! = l := by
    intro l hl
    have hs : (index1[l]?.getD none).isSome = true := by rw [hindex1 l]; exact hl
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs
    have h2 := indexOfTable_spec n order1 l i hi
    have hi' : idx1 l = i := by simp only [idx1, hi]; rfl
    rw [hi']
    exact ⟨(Array.getElem?_eq_some_iff.mp h2).1, by
      rw [getElem!_pos order1 i (Array.getElem?_eq_some_iff.mp h2).1]
      exact (Array.getElem?_eq_some_iff.mp h2).2⟩
  have hidxSelf : ∀ i, i < N → idx1 order1[i]! = i := by
    intro i hi
    have hmem : order1[i]! ∈ order1.toList := by
      rw [getElem!_pos order1 i hi]; simp
    obtain ⟨hlt, heq⟩ := hK1 order1[i]! (by simp only [avail1]; exact decide_eq_true hmem)
    exact getBang_inj hnd1 hlt hi heq
  -- the writing facts per phase-1 expression
  have hTreeFacts : ∀ (entry : Bool) (t : Nat) (e : Ixon.Expr) (T : WTree),
      TreeOf (Prep.ofDag ex.dag) avail1 index1 entry t e T →
      (∀ j ∈ shareList e, j < N) ∧
      (∀ f : Nat → Nat, (T.leaves.map f).sum = ((shareList e).map fun j => f order1[j]!).sum) ∧
      (∀ l ∈ T.leaves, ∃ j ∈ shareList e, order1[j]! = l ∧ j < N) := by
    intro entry t e T hT
    obtain ⟨hV, -, hL, -⟩ := hT
    have hav := hV.leaves_avail
    refine ⟨fun j hj => ?_, fun f => ?_, fun l hl => ?_⟩
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (hL.mem_iff.mpr hj)
      exact (hK1 l (hav l hl)).1
    · have : T.leaves.map f = (T.leaves.map idx1).map fun j => f order1[j]! := by
        rw [List.map_map]
        apply List.map_congr_left
        intro l hl
        simp only [Function.comp]
        rw [(hK1 l (hav l hl)).2]
      rw [this]
      exact (hL.map _).sum_nat
    · exact ⟨idx1 l, hL.mem_iff.mp (List.mem_map_of_mem hl), (hK1 l (hav l hl)).2,
        (hK1 l (hav l hl)).1⟩
  let s : Ixon.Expr → Nat := fun e => (sizeInfoWith layout.widthAt e).full
  let A : Ixon.Expr → Nat := fun e => ((shareList e).map wA).sum
  let B : Ixon.Expr → Nat := fun e => ((shareList e).map wB).sum
  -- per-expression inequality from a phase-1 writing
  have hpart : ∀ (entry : Bool) (t : Nat) (e : Ixon.Expr) (T : WTree) (S' : Nat → Bool)
      (wd3 : Nat → Nat) (size3 : Nat),
      TreeOf (Prep.ofDag ex.dag) avail1 index1 entry t e T →
      (∀ l ∈ T.leaves, S' l = true ∧ wd3 l = layout.widthAt (pos3 l)) →
      (∀ T', Valid (Prep.ofDag ex.dag) S' t T' → size3 ≤ T'.gcost (Prep.ofDag ex.dag) wd3) →
      size3 + A e ≤ s e + B e := by
    intro entry t e T S' wd3 size3 hT hleaf hmin
    obtain ⟨hall, hsum, -⟩ := hTreeFacts entry t e T hT
    have h1 : s e = T.gcost (Prep.ofDag ex.dag) (fun l => layout.widthAt (idx1 l)) :=
      (hT.2.2.2 layout.widthAt _ (fun v i hi => by simp only [idx1, hi]; rfl)).1
    have hle := part_le hT.1 (fun l hl => (hleaf l hl).1) hmin h1
    have hA : (T.leaves.map fun l => layout.widthAt (idx1 l)).sum = A e := by
      rw [hsum]
      simp only [A, wA]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [hidxSelf j (hall j hj)]
    have hB : (T.leaves.map wd3).sum = B e := by
      rw [List.map_congr_left (fun l hl => (hleaf l hl).2), hsum]
    rw [hA, hB] at hle
    exact hle
  -- shares of phase-1 expressions lie in the table
  have hshN : ∀ (entry : Bool) (t : Nat) (e : Ixon.Expr) (T : WTree),
      TreeOf (Prep.ofDag ex.dag) avail1 index1 entry t e T → ∀ j ∈ shareList e, j < N :=
    fun entry t e T hT => (hTreeFacts entry t e T hT).1
  -- table terms are in range and at their phase-3 position
  have hpos : ∀ k, k < order.size → pos3 order[k]! = k := by
    intro k hk
    have hd : order[k]! ∈ order1.toList := by
      rw [getElem!_pos order k hk]; exact hperm.subset (by simp)
    have := prefix_lookup (n := n) hnd (j := k) (k := order.size) (d := order[k]!)
      (by rw [getElem!_pos order k hk]; simp [hk]) hk (hin1 _ hd)
    simp only [pos3, this]
    rfl
  -- the indexed phase-1 writings
  obtain ⟨hlenE, hgetE⟩ := Ix.Compile.Verify.SharingExact.forall₂_getElem hents
  obtain ⟨hlenR, hgetR⟩ := Ix.Compile.Verify.SharingExact.forall₂_getElem hrts
  obtain ⟨hlenR3, hgetR3⟩ := Ix.Compile.Verify.SharingExact.forall₂_getElem hrmin3
  simp only [Array.length_toList] at hlenE hlenR hlenR3
  -- entries
  have hentry : ∀ k, k < N →
      s entries[k]! + A entries1[idx1 order[k]!]! ≤
        s entries1[idx1 order[k]!]! + B entries1[idx1 order[k]!]! := by
    intro k hk
    have hk3 : k < order.size := by omega
    have hke : k < entries.size := by omega
    have hd : order[k]! ∈ order1.toList := by
      rw [getElem!_pos order k hk3]; exact hperm.subset (by simp)
    obtain ⟨hiN, hti⟩ := hK1 order[k]! (by simp only [avail1]; exact decide_eq_true hd)
    have hiN' : idx1 order[k]! < entries1.size := by simp only [N] at hiN; omega
    obtain ⟨T, hT⟩ := hgetE (idx1 order[k]!) (by simpa using hiN) (by simpa using hiN')
    simp only [Array.getElem_toList] at hT
    rw [← getElem!_pos order1 _ hiN, hti, ← getElem!_pos entries1 _ (by omega)] at hT
    refine hpart true _ _ T (prefixAvail n order k) (prefixWd n order layout.widthAt k)
      (s entries[k]!) hT (fun l hl => ?_) (fun T' hT' => ?_)
    · obtain ⟨j, hj, hjl, hjN⟩ := (hTreeFacts true _ _ T hT).2.2 l hl
      have hdep : l ∈ (tierDeps order1 entries1).getD order[k]! [] := by
        rw [← hti, getElem!_pos order1 _ hiN, tierDeps_spec hnd1 entries1 hiN]
        rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [mem_bodyRefs]
        refine ⟨j, ?_, ?_⟩
        · rw [← getElem!_pos entries1 _ (by omega)]; exact hj
        · rw [← hjl, getElem!_pos order1 j hjN]; simp
      obtain ⟨j', hj'k, hj'⟩ := hback k hk3 l (by rw [← getElem!_pos order k hk3]; exact hdep)
      have hl1 : l ∈ order1.toList := by rw [← hjl, getElem!_pos order1 j hjN]; simp
      have hlook := prefix_lookup (n := n) hnd hj' hj'k (hin1 l hl1)
      have hlook' := prefix_lookup (n := n) hnd hj' (k := order.size)
        (Array.getElem?_eq_some_iff.mp hj').1 (hin1 l hl1)
      refine ⟨by simp only [prefixAvail, hlook]; rfl, ?_⟩
      simp only [prefixWd, pos3, hlook, hlook']
      rfl
    · have := (hmin3 k hke).1 T' hT'
      rw [getElem!_pos entries k hke]
      exact this
  -- roots
  have hroot : ∀ r, r < ex.roots.size →
      s rs[r]! + A roots1[r]! ≤ s roots1[r]! + B roots1[r]! := by
    intro r hr
    have hr1 : r < roots1.size := by omega
    have hr3 : r < rs.size := by omega
    obtain ⟨T, hT⟩ := hgetR r (by simpa using hr) (by simpa using hr1)
    have hmin := (hgetR3 r (by simpa using hr) (by simpa using hr3)).1
    simp only [Array.getElem_toList] at hT hmin
    rw [← getElem!_pos roots1 r hr1] at hT
    refine hpart false _ _ T (prefixAvail n order order.size)
      (prefixWd n order layout.widthAt order.size) (s rs[r]!) hT (fun l hl => ?_) (fun T' hT' => ?_)
    · have hl1 : l ∈ order1.toList := by
        have := hT.1.leaves_avail l hl
        simpa [avail1] using this
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hperm.mem_iff.mpr hl1)
      have hj' : order[j]? = some l := by simpa using hj
      have hjk : j < order.size := (Array.getElem?_eq_some_iff.mp hj').1
      have hlook := prefix_lookup (n := n) hnd hj' hjk (hin1 l hl1)
      refine ⟨by simp only [prefixAvail, hlook]; rfl, ?_⟩
      simp only [prefixWd, pos3, hlook]
      rfl
    · rw [getElem!_pos rs r hr3]
      exact hmin T' hT'
  -- sums over the entries, reindexed by the phase-1 order
  have hreindex : ∀ (F : Ixon.Expr → Nat),
      ((List.range N).map fun k => F entries1[idx1 order[k]!]!).sum = (entries1.toList.map F).sum := by
    intro F
    rw [show N = order.size from hNsz.symm, sum_range_array order (fun t => F entries1[idx1 t]!),
      List.Perm.sum_nat (hperm.map _), ← sum_range_array order1 (fun t => F entries1[idx1 t]!)]
    rw [show order1.size = entries1.size by omega]
    apply sum_range_eq F entries1
    intro j hj
    rw [hidxSelf j (by simp only [N]; omega), getElem!_pos entries1 j hj]
  have hsumE : (entries.toList.map s).sum + (entries1.toList.map A).sum ≤
      (entries1.toList.map s).sum + (entries1.toList.map B).sum := by
    have h := Ix.Compile.Verify.UniformModel.sum_le_sum_of_le (List.range N) (fun k hk =>
      hentry k (List.mem_range.mp hk))
    rw [Ix.Compile.Verify.SharingExact.sum_map_add, Ix.Compile.Verify.SharingExact.sum_map_add,
      hreindex A, hreindex s, hreindex B] at h
    have hE : ((List.range N).map fun k => s entries[k]!).sum = (entries.toList.map s).sum := by
      rw [show N = entries.size by omega]
      exact sum_range_eq s entries fun j hj => by rw [getElem!_pos entries j hj]
    rw [hE] at h
    exact h
  have hsumR : (rs.toList.map s).sum + (roots1.toList.map A).sum ≤
      (roots1.toList.map s).sum + (roots1.toList.map B).sum := by
    have h := Ix.Compile.Verify.UniformModel.sum_le_sum_of_le (List.range ex.roots.size)
      (fun k hk => hroot k (List.mem_range.mp hk))
    rw [Ix.Compile.Verify.SharingExact.sum_map_add, Ix.Compile.Verify.SharingExact.sum_map_add] at h
    have h1 : ∀ (F : Ixon.Expr → Nat), ((List.range ex.roots.size).map fun k => F roots1[k]!).sum =
        (roots1.toList.map F).sum := by
      intro F
      rw [show ex.roots.size = roots1.size by omega]
      exact sum_range_eq F roots1 fun j hj => by rw [getElem!_pos roots1 j hj]
    have h2 : ((List.range ex.roots.size).map fun k => s rs[k]!).sum = (rs.toList.map s).sum := by
      rw [show ex.roots.size = rs.size by omega]
      exact sum_range_eq s rs fun j hj => by rw [getElem!_pos rs j hj]
    rw [h1 A, h1 s, h1 B, h2] at h
    exact h
  -- all Shares of the phase-1 output, counted per index
  have hallN : ∀ j ∈ (entries1.toList ++ roots1.toList).flatMap shareList, j < N := by
    intro j hj
    obtain ⟨e, he, hje⟩ := List.mem_flatMap.mp hj
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      obtain ⟨T, hT⟩ := hgetE i (by simp at hi ⊢; omega) hi
      exact hshN _ _ _ T hT j hje
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      obtain ⟨T, hT⟩ := hgetR i (by simp at hi ⊢; omega) hi
      exact hshN _ _ _ T hT j hje
  have hsumAll : ∀ g : Nat → Nat,
      (((entries1.toList ++ roots1.toList).flatMap shareList).map g).sum =
        (entries1.toList.map fun e => ((shareList e).map g).sum).sum +
          (roots1.toList.map fun e => ((shareList e).map g).sum).sum := by
    intro g
    rw [sum_map_flatMap, List.map_append, List.sum_append]
  let weight : Nat → Nat := fun t => (tierWeights order1 entries1 roots1).getD t 0
  have hW : ∀ i, i < N → weight order1[i]! =
      ((entries1.toList ++ roots1.toList).flatMap shareList).count i := by
    intro i hi
    simp only [weight]
    rw [getElem!_pos order1 i hi, tierWeights_spec hnd1 entries1 roots1 hi]
    rfl
  have hAall : (entries1.toList.map A).sum + (roots1.toList.map A).sum =
      refCost layout weight order1 := by
    simp only [A]
    rw [← hsumAll, ← sum_count N wA _ hallN, refCost_eq_sum]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [hW i hi]
  have hBall : (entries1.toList.map B).sum + (roots1.toList.map B).sum =
      refCost layout weight order := by
    simp only [B]
    rw [← hsumAll, ← sum_count N wB _ hallN, refCost_eq_sum]
    have h1 : ((List.range N).map fun i =>
        ((entries1.toList ++ roots1.toList).flatMap shareList).count i * wB i) =
        (List.range order1.size).map fun i =>
          (fun t => weight t * layout.widthAt (pos3 t)) order1[i]! := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [← hW i hi]
    rw [h1, sum_range_array order1 (fun t => weight t * layout.widthAt (pos3 t)),
      ← List.Perm.sum_nat (hperm.map _), ← sum_range_array order]
    congr 1
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    show weight order[k]! * layout.widthAt (pos3 order[k]!) = _
    rw [hpos k hk]
  -- conclude
  have hlenE' : entries1.size = N := by simp only [N]; omega
  have hlen3 : entries.size = N := by omega
  have htag : tag0Size entries.size = tag0Size entries1.size := by rw [hlen3, hlenE']
  rw [layoutBytes_eq, hpred, htag]
  have hrc : a.refCostFinal ≤ a.refCost1 := hrcLe
  rw [hrfEq, hrcEq] at hrc
  simp only [weight] at hAall hBall
  simp only [s] at hsumE hsumR
  omega




/-! ## Optimality of the allocation in the 2-byte tier -/

open Ix.Compile.Verify.SharingExact (tagNWidth_rung1 tagNRung1End_eq) in
/-- Both layouts price a Share by the TagN (`f = 4`) width (`shareWidth = tag4Size =
Ixon.tagNByteWidth 4 = tagNWidth`). -/
theorem widthAt_lt8 (layout : ShareLayout) {k : Nat} (hk : k < 8) : layout.widthAt k = 1 := by
  cases layout with
  | tag4 => exact tagNWidth_rung1 (by rw [tagNRung1End_eq]; exact hk)
  | tagN => exact tagNWidth_rung1 (by rw [tagNRung1End_eq]; exact hk)

open Ix.Compile.Verify.SharingExact (tagNWidth_rung2 tagNRung1End_eq tagNRung2End_eq) in
theorem widthAt_tier2 (layout : ShareLayout) {k : Nat} (h1 : 8 ≤ k) (h2 : k < layout.tier2End) :
    layout.widthAt k = 2 := by
  cases layout with
  | tag4 =>
    simp only [ShareLayout.tier2End] at h2
    exact tagNWidth_rung2 (by rw [tagNRung1End_eq]; exact h1) (by rw [tagNRung2End_eq]; omega)
  | tagN => exact tagNWidth_rung2 (by rw [tagNRung1End_eq]; exact h1) h2

/-- The reference cost of an order of at most `tier2End` terms: the first
`min 8 N` entries cost one byte per reference, the others two. -/
theorem refCost_tier2 (layout : ShareLayout) (weight : Nat → Nat) (ρ : Array Nat)
    (hsmall : ρ.size ≤ layout.tier2End) :
    refCost layout weight ρ + ((List.range (min 8 ρ.size)).map fun k => weight ρ[k]!).sum =
      2 * ((List.range ρ.size).map fun k => weight ρ[k]!).sum := by
  rw [refCost_eq_sum]
  suffices h : ∀ M, M ≤ ρ.size →
      ((List.range M).map fun k => weight ρ[k]! * layout.widthAt k).sum +
        ((List.range (min 8 M)).map fun k => weight ρ[k]!).sum =
      2 * ((List.range M).map fun k => weight ρ[k]!).sum from h ρ.size (Nat.le_refl _)
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro hM
    have ih' := ih (by omega)
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    by_cases h8 : M < 8
    · rw [widthAt_lt8 layout h8, show min 8 (M + 1) = min 8 M + 1 by omega, List.range_succ,
        List.map_append, List.sum_append, show min 8 M = M by omega]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [show min 8 M = M by omega] at ih'
      omega
    · rw [widthAt_tier2 layout (by omega) (by omega), show min 8 (M + 1) = min 8 M by omega]
      omega

theorem take_feasible {deps : Nat → List Nat} {order1 π : Array Nat} {m : Nat}
    (hperm : π.toList.Perm order1.toList) (hnd : order1.toList.Nodup)
    (hback : ∀ k (hk : k < π.size), ∀ d ∈ deps π[k], ∃ j, j < k ∧ π[j]? = some d) :
    Feasible deps order1.toList m (π.toList.take m) := by
  have hndπ : π.toList.Nodup := hperm.nodup_iff.mpr hnd
  refine ⟨hndπ.sublist (List.take_sublist _ _), fun x hx => hperm.subset
    (List.mem_of_mem_take hx), fun u hu d hd => ?_, by simp; omega⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hu
  have hk' : k < π.size := by simp at hk; omega
  have hkm : k < m := by simp at hk; omega
  rw [List.getElem_take, Array.getElem_toList] at hd
  obtain ⟨j, hjk, hj⟩ := hback k hk' d hd
  have hjs : j < π.size := (Array.getElem?_eq_some_iff.mp hj).1
  rw [List.mem_iff_getElem]
  refine ⟨j, by simp; omega, ?_⟩
  rw [List.getElem_take, Array.getElem_toList]
  exact (Array.getElem?_eq_some_iff.mp hj).2

theorem wsum_take (weight : Nat → Nat) (π : Array Nat) (m : Nat) :
    wsum weight (π.toList.take m) =
      ((List.range (min m π.size)).map fun k => weight π[k]!).sum := by
  unfold wsum
  congr 1
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_take, Array.getElem_toList, List.getElem_range]
  simp at h1
  rw [getElem!_pos π k (by omega)]

/-- **Optimality of the allocation when the table fits the 2-byte tier.**
With the reference counts fixed, if the phase-1 table has at most
`tier2End` entries (so every index from 8 on has width 2), the allocated
order has the minimum reference cost `Σ ref · widthAt (index)` among all
orders of the table that place every body reference before its user. -/
theorem allocate_optimal {layout : ShareLayout} {limits : Limits} {dag : Dag} {deg : Array Nat}
    {order1 : Array Nat} {entries1 roots1 : Array Ixon.Expr} {a : Allocation}
    (h : allocate layout limits dag deg order1 entries1 roots1 = .ok a)
    (hsmall : order1.size ≤ layout.tier2End) :
    ∀ π : Array Nat, π.toList.Perm order1.toList →
      (∀ k (hk : k < π.size), ∀ d ∈ (tierDeps order1 entries1).getD π[k] [],
        ∃ j, j < k ∧ π[j]? = some d) →
      a.refCostFinal ≤ refCost layout (fun t => (tierWeights order1 entries1 roots1).getD t 0) π := by
  intro π hπ hπback
  obtain ⟨hnd, ⟨hFfeas, -, hFmax, -⟩, -, -, -, -, -, -, hperm2, hle2⟩ := allocate_spec h
  generalize hw : (fun t => (tierWeights order1 entries1 roots1).getD t 0) = weight at *
  generalize ho2 : pinnedOrder dag deg a.tier ++ kahnOrder weight
    (fun t => (tierDeps order1 entries1).getD t [])
    ((order1.toList.mergeSort (· ≤ ·)).toArray.filter (!a.tier.contains ·)) = order2 at *
  have hNπ : π.size = order1.size := by simpa using hπ.length_eq
  have hN2 : order2.size = order1.size := by simpa using hperm2.length_eq
  -- both orders split their cost by the weight of their first `min 8 N` entries
  have hsplitπ := refCost_tier2 layout weight π (by omega)
  have hsplit2 := refCost_tier2 layout weight order2 (by omega)
  have htot : ∀ ρ : Array Nat, ρ.toList.Perm order1.toList →
      ((List.range ρ.size).map fun k => weight ρ[k]!).sum = wsum weight order1.toList := by
    intro ρ hρ
    rw [sum_range_array ρ weight, wsum]
    exact (hρ.map _).sum_nat
  rw [htot π hπ] at hsplitπ
  rw [htot order2 hperm2] at hsplit2
  -- the first entries of `π` form a closed set of at most `min 8 N` terms
  have hfeas := take_feasible (deps := fun t => (tierDeps order1 entries1).getD t [])
    (m := min 8 order1.size) hπ hnd hπback
  have hπle := hFmax _ hfeas
  rw [wsum_take, show min (min 8 order1.size) π.size = min 8 π.size by omega] at hπle
  -- the first entries of the pinned order contain the first tier
  have htier : wsum weight a.tier.toList ≤
      ((List.range (min 8 order2.size)).map fun k => weight order2[k]!).sum := by
    rw [← wsum_take]
    have hlenT : a.tier.size ≤ min 8 order2.size := by
      have := hFfeas.2.2.2; simp at this; omega
    have hpin : (pinnedOrder dag deg a.tier).toList.Perm a.tier.toList := pinnedOrder_perm _ _ _
    have hpsz : (pinnedOrder dag deg a.tier).size = a.tier.size := by
      simpa using hpin.length_eq
    rw [← ho2, Array.toList_append, List.take_append, wsum_append,
      List.take_of_length_le (by simp; omega), wsum_perm hpin]
    exact Nat.le_add_right _ _
  omega

end Ix.Compile.Verify.Tiered
