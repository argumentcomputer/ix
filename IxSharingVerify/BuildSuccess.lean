import IxSharingVerify.TieredModel
import IxC.Kernel.Audit.Axioms

/-!
# Materialization never refuses a model evaluation

`Prep.build` writes the chosen encoding of a term and refuses on every
inconsistency between the options it is offered and the evaluation it is
given. Over the evaluation of a dictionary (`GEvalOK`), with the Share
indices and widths of that dictionary, none of these refusals is reachable:
there is always an option, the standalone pick costs exactly the evaluated
cost, a Share is offered only for an indexed term, an inline writing only
outside a telescope, and a cut only at an available spine node or at the
natural end of the spine. Every recursive call is on a smaller term, so
`dag.size + 1` fuel suffices (`PrepWF.build_ok`).
-/

namespace Ix.Sharing.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Sharing.Verify.SharingExact (pickOption_mem child_eq_getElem)

theorem list_mapM_ok {α β ε : Type} (f : α → Except ε β) :
    ∀ (l : List α), (∀ x ∈ l, ∃ y, f x = .ok y) → ∃ ys, l.mapM f = .ok ys
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := list_mapM_ok f l (fun z hz => h z (List.mem_cons_of_mem _ hz))
    exact ⟨y :: ys, by rw [List.mapM_cons, hy, hys]; rfl⟩

theorem array_mapM_ok {α β ε : Type} (f : α → Except ε β) (xs : Array α)
    (h : ∀ x ∈ xs.toList, ∃ y, f x = .ok y) : ∃ ys, xs.mapM f = .ok ys := by
  obtain ⟨ys, hys⟩ := list_mapM_ok f xs.toList h
  exact ⟨ys.toArray, by rw [Array.mapM_eq_mapM_toList, hys]; rfl⟩

theorem foldl_min_assoc (a : Nat) :
    ∀ (L : List Nat) (b : Nat), L.foldl min (min a b) = min a (L.foldl min b)
  | [], _ => rfl
  | x :: L, b => by
    simp only [List.foldl_cons]
    rw [Nat.min_assoc]
    exact foldl_min_assoc a L (min b x)

theorem cutOptions_size_le (p : Prep) (ev : DictEval) (index width : Array (Option Nat))
    (flag : UInt8) (l s : Nat) :
    ∀ (fuel : Nat) (cur : Option Nat) (opts : Array (Choice × Nat × ByteArray)),
      opts.size ≤ (p.cutOptions ev index width flag l s fuel cur opts).size
  | 0, _, _ => Nat.le_refl _
  | _ + 1, none, _ => Nat.le_refl _
  | fuel + 1, some u, opts => by
    simp only [Prep.cutOptions]
    split
    · exact Nat.le_trans (by simp) (cutOptions_size_le p ev index width flag l s fuel _ _)
    · exact cutOptions_size_le p ev index width flag l s fuel _ _

/-- The options written inline are never empty. -/
theorem optRest_cons (p : Prep) (ev : DictEval) (index width : Array (Option Nat)) (t : Nat) :
    ∃ y L, (optRest p ev index width t).toList = y :: L := by
  have size : (optRest p ev index width t).size ≠ 0 := by
    unfold optRest
    dsimp only
    split
    · simp
    · exact Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (by simp) (cutOptions_size_le _ _ _ _ _ _ _ _ _ _))
  cases h : (optRest p ev index width t).toList with
  | nil => exact absurd (by simpa using congrArg List.length h) size
  | cons y L => exact ⟨y, L, rfl⟩

/-- The standalone pick costs the evaluated cost of the term. -/
theorem PrepWF.pick_cost {p : Prep} (hp : PrepWF p)
    {wd : Nat → Nat} {avail : Nat → Bool} (ev : DictEval) (hev : GEvalOK p wd avail ev)
    (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u) {t : Nat} (ht : t < p.dag.size)
    {ch : Choice} {c : Nat} (h : pickOption (p.options ev index width t) = some (ch, c)) :
    c = gCost p wd avail t := by
  obtain ⟨y, L, hrest⟩ := optRest_cons p ev index width t
  have inline := hp.gInlineCost_eq ev hev index width hwidth hindex t ht
  unfold Prep.inlineCost at inline
  rw [options_filter, pickOption_cost _ y L hrest] at inline
  have whole : ((pickOption (p.options ev index width t)).map (·.2)).getD 0 = c := by
    rw [h]; rfl
  have split := options_split p ev index width t
  rw [hp.gCost_eq wd avail t ht]
  unfold gCostOf
  cases hav : avail t with
  | true =>
    have some : (index[t]?.getD none).isSome = true := by rw [hindex t, hav]
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp some
    have shareOpt : optShare index width t =
        #[(Choice.share, wd t, tag4Bytes Ixon.Expr.FLAG_SHARE i)] := by
      unfold optShare
      rw [hi, hwidth t, hav]
      rfl
    have list : (p.options ev index width t).toList =
        (Choice.share, wd t, tag4Bytes Ixon.Expr.FLAG_SHARE i) :: y :: L := by
      rw [split, Array.toList_append, shareOpt, hrest]
      rfl
    rw [pickOption_cost _ _ _ list] at whole
    simp only [List.map_cons, List.foldl_cons] at whole
    rw [foldl_min_assoc] at whole
    simp only [ite_true]
    rw [← whole, inline, Nat.min_comm]
    rfl
  | false =>
    have none : index[t]?.getD none = none := by
      have h1 := hindex t
      rw [hav] at h1
      cases hi : index[t]?.getD none with
      | none => rfl
      | some i => rw [hi] at h1; cases h1
    have shareOpt : optShare index width t = #[] := by
      unfold optShare
      rw [none]
    have list : (p.options ev index width t).toList = y :: L := by
      rw [split, Array.toList_append, shareOpt, hrest]
      rfl
    rw [pickOption_cost _ _ _ list] at whole
    simp only [Bool.false_eq_true, ite_false]
    rw [← whole, inline]
    rfl

theorem rebuild_ok (n : Node) (inner side : Ixon.Expr) (h : n.head.family ≠ .none) :
    ∃ e, rebuildSpineNode n inner side = .ok e := by
  unfold rebuildSpineNode
  cases hh : n.head with
  | app => exact ⟨_, rfl⟩
  | lam _ => exact ⟨_, rfl⟩
  | all _ _ => exact ⟨_, rfl⟩
  | _ => rw [hh] at h; exact absurd rfl h

theorem spineFold_ok (buildSide : Node → Except SharingError Ixon.Expr) :
    ∀ (ns : List Node) (tail : Ixon.Expr),
      (∀ n ∈ ns, (∃ e, buildSide n = .ok e) ∧ n.head.family ≠ .none) →
      ∃ e, ns.foldrM (fun n acc => do let side ← buildSide n; rebuildSpineNode n acc side) tail = .ok e
  | [], tail, _ => ⟨tail, rfl⟩
  | n :: ns, tail, h => by
    obtain ⟨acc, hacc⟩ := spineFold_ok buildSide ns tail (fun m hm => h m (List.mem_cons_of_mem _ hm))
    obtain ⟨⟨side, hside⟩, hfam⟩ := h n List.mem_cons_self
    obtain ⟨e, he⟩ := rebuild_ok n acc side hfam
    refine ⟨e, ?_⟩
    rw [List.foldrM_cons, hacc]
    change (buildSide n >>= fun side => rebuildSpineNode n acc side) = .ok e
    rw [hside]
    exact he

/-- **`build` never refuses** an evaluation of the model at the dictionary's
widths, with the dictionary's indices, given more fuel than the term ID. -/
theorem PrepWF.build_ok {p : Prep} (hp : PrepWF p)
    {wd : Nat → Nat} {avail : Nat → Bool} (ev : DictEval) (hev : GEvalOK p wd avail ev)
    (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u) :
    ∀ (fuel : Nat) (entry : Bool) (t : Nat), t < p.dag.size → t < fuel →
      ∃ e, p.build ev index width entry fuel t = .ok e := by
  intro fuel
  induction fuel with
  | zero => intro _ t _ h; omega
  | succ fuel ih =>
    intro entry t ht hfuel
    obtain ⟨y, L, hrest⟩ := optRest_cons p ev index width t
    have restSize : (optRest p ev index width t).size ≠ 0 := by
      have := congrArg List.length hrest
      simp only [Array.length_toList, List.length_cons] at this
      omega
    have nonempty : (if entry then (p.options ev index width t).filter (·.1 != .share)
        else p.options ev index width t).size ≠ 0 := by
      cases entry
      · simp only [Bool.false_eq_true, ite_false]
        rw [options_split, Array.size_append]
        omega
      · simp only [ite_true]
        rw [options_filter]
        exact restSize
    obtain ⟨ch, c, hpick⟩ := pickOption_isSome _ nonempty
    obtain ⟨b, hb⟩ := pickOption_mem _ hpick
    have hmem : (ch, c, b) ∈ (p.options ev index width t).toList := by
      cases entry
      · simpa using hb
      · simp only [ite_true] at hb
        rw [Array.toList_filter] at hb
        exact (List.mem_filter.mp hb).1
    have hcheck : (entry || c == ev.cost[t]!) = true := by
      cases entry
      · simp only [Bool.false_eq_true, ite_false] at hpick
        rw [Bool.false_or, hev.cost t, hp.pick_cost ev hev index width hwidth hindex ht hpick]
        exact beq_self_eq_true _
      · rfl
    have hopt := hp.gOptions_mem ev hev index width hwidth hindex ht hmem
    simp only [Prep.build]
    split
    · rename_i choice c' found
      rw [hpick] at found
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      split
      case isFalse unchecked => exact absurd hcheck unchecked
      try simp only [pure_bind]
      · split
        · -- a Share
          obtain ⟨_, _, hav⟩ | ⟨h1, _⟩ | ⟨j, h1, _⟩ := hopt
          · split
            · exact ⟨_, rfl⟩
            · rename_i missing
              have := hindex t
              rw [missing, hav] at this
              cases this
          · cases h1
          · cases h1
        · -- an inline node
          obtain ⟨h1, _⟩ | ⟨_, hf, _⟩ | ⟨j, h1, _⟩ := hopt
          · cases h1
          · have har := hp.dag.arity t ht
            rw [← dag_node_eq ht] at har
            have fam := hp.family t ht
            rw [hf] at fam
            cases hh : (p.dag.node t).head with
            | prj ti f =>
              simp only
              have c0 : (p.dag.node t).child 0 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              obtain ⟨v, hv⟩ := ih false ((p.dag.node t).child 0) (by omega) (by omega)
              rw [hv]
              exact ⟨_, rfl⟩
            | letE lc =>
              simp only
              have c0 : (p.dag.node t).child 0 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              have c1 : (p.dag.node t).child 1 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              have c2 : (p.dag.node t).child 2 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              obtain ⟨v0, h0⟩ := ih false ((p.dag.node t).child 0) (by omega) (by omega)
              obtain ⟨v1, h1⟩ := ih false ((p.dag.node t).child 1) (by omega) (by omega)
              obtain ⟨v2, h2⟩ := ih false ((p.dag.node t).child 2) (by omega) (by omega)
              rw [h0]
              change ∃ e, (p.build ev index width false fuel ((p.dag.node t).child 1) >>= fun v =>
                p.build ev index width false fuel ((p.dag.node t).child 2) >>= fun b =>
                  pure (Ixon.Expr.letE lc v0 v b)) = .ok e
              rw [h1, h2]
              exact ⟨_, rfl⟩
            | app => rw [hh] at fam; cases fam
            | lam _ => rw [hh] at fam; cases fam
            | all _ _ => rw [hh] at fam; cases fam
            | _ => simp only; exact ⟨_, rfl⟩
          · cases h1
        · -- a telescope cut
          rename_i j
          obtain ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨j', hj', hf, hj1, hjl, hcase⟩ := hopt
          · cases h1
          · cases h1
          cases hj'
          obtain ⟨_, hk, hend, htl, _⟩ := hp.spine t ht hf
          rw [ite_eq_right (show ¬ j = 0 by omega), spineWalk_eq]
          have sides : ∀ n ∈ (List.range j).map (fun k => p.dag.node (spineAt p t k)),
              (∃ e, p.build ev index width false fuel n.sideChild = .ok e) ∧ n.head.family ≠ .none := by
            intro n hn
            obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hn
            rw [List.mem_range] at hk'
            obtain ⟨hle, hkf, _, _⟩ := hk k (by omega)
            have kf : p.family[spineAt p t k]! ≠ .none := by rw [hkf]; exact hf
            have hs := hp.sideChild_lt (t := spineAt p t k) (by omega) kf
            refine ⟨ih false _ (by omega) (by omega), ?_⟩
            rw [← hp.family _ (by omega)]
            exact kf
          by_cases short : j < p.spineLen[t]!
          · rcases hcase with ⟨eq, _⟩ | ⟨_, hav, _⟩
            · omega
            have some : (index[spineAt p t j]?.getD none).isSome = true := by rw [hindex, hav]
            obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp some
            simp only [ite_eq_left short, hi]
            exact spineFold_ok _ _ _ sides
          · have full : j = p.spineLen[t]! := by omega
            have tailLt : spineAt p t j < t := by rw [full, hend]; exact htl
            obtain ⟨tl, htl'⟩ := ih false (spineAt p t j) (by omega) (by omega)
            simp only [ite_eq_right short, htl']
            exact spineFold_ok _ _ _ sides
    · rename_i missing
      rw [hpick] at missing
      exact (missing ch c rfl).elim

end Ix.Sharing.Verify.UniformModel

#guard_kernel_axioms Ix.Sharing.Verify.UniformModel.PrepWF.pick_cost [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.UniformModel.PrepWF.build_ok [propext, Classical.choice, Quot.sound]
