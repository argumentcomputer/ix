import IxSharingVerify.BuildSuccess
import IxC.Kernel.Audit.Axioms

/-!
# Built expressions are in the wire domain

The re-materialization refuses an expression whose `UInt64` counts (the
telescope lengths at the top of each node and the universe vectors of
references) are not representable (`wireCounts`). Every telescope `build`
writes is a run of one term's spine, so its length is at most that spine's
length and hence at most the DAG size; universe vectors are those of the
DAG's nodes. On a DAG of fewer than `2^64` terms whose references carry fewer
than `2^64` universes, every built expression passes (`PrepWF.build_wire`).
-/

namespace Ix.Sharing.Verify.UniformModel

open Ix.Sharing.Exact

/-- A node head whose universe vector fits the wire's count word. -/
def HeadFits : Head → Prop
  | .ref _ us => us.size < UInt64.size
  | .recur _ us => us.size < UInt64.size
  | _ => True

/-- The telescope count of a family at the top of an expression. -/
def famCount : Family → Nat × Nat × Nat → Nat
  | .app, c => c.1
  | .lam, c => c.2.1
  | .all, c => c.2.2
  | .none, _ => 0

/-- The top counts of an expression of family `F`: only `F`'s telescope is
open, of length at most `bound`. -/
def TopOK (F : Family) (bound : Nat) (c : Nat × Nat × Nat) : Prop :=
  (F ≠ .app → c.1 = 0) ∧ (F ≠ .lam → c.2.1 = 0) ∧ (F ≠ .all → c.2.2 = 0) ∧ famCount F c ≤ bound

theorem topOK_zero (F : Family) (bound : Nat) : TopOK F bound (0, 0, 0) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  cases F <;> simp [famCount]

theorem famCount_zero {F G : Family} {bound : Nat} {c : Nat × Nat × Nat} (h : TopOK G bound c)
    (ne : F ≠ G) : famCount F c = 0 := by
  obtain ⟨a, l, al, _⟩ := h
  cases F with
  | app => exact a (fun e => ne e.symm)
  | lam => exact l (fun e => ne e.symm)
  | all => exact al (fun e => ne e.symm)
  | none => rfl

theorem PrepWF.spineLen_le {p : Prep} (hp : PrepWF p) :
    ∀ t, t < p.dag.size → p.spineLen[t]! ≤ t + 1 := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    by_cases hf : p.family[t]! = .none
    · have := ((hp.row t ht).2 hf).1
      omega
    · have hlt := hp.snext_lt ht hf
      rcases hp.spine_step ht hf with ⟨_, hl, _⟩ | ⟨_, hl, _⟩
      · have := ih _ hlt (by omega)
        omega
      · omega

/-- Rebuilding one spine node of family `F` around a continuation with `k`
open nodes of `F` opens `k + 1`, and closes every other telescope. -/
theorem rebuild_wire {F : Family} {n : Node} (hfam : n.head.family = F) {acc side res : Ixon.Expr}
    {ca cs : Nat × Nat × Nat} (hacc : wireCounts acc = some ca) (hside : wireCounts side = some cs)
    (room : famCount F ca + 1 < UInt64.size) (h : rebuildSpineNode n acc side = .ok res) :
    ∃ c, wireCounts res = some c ∧ famCount F c = famCount F ca + 1 ∧
      TopOK F (famCount F ca + 1) c := by
  obtain ⟨a, l, al⟩ := ca
  unfold rebuildSpineNode at h
  cases hh : n.head with
  | app =>
    rw [hh] at h hfam
    cases h
    subst hfam
    simp only [famCount, Head.family] at room ⊢
    refine ⟨(a + 1, 0, 0), ?_, rfl, fun e => absurd rfl e, fun _ => rfl, fun _ => rfl, Nat.le_refl _⟩
    simp only [wireCounts, hacc, hside, room, ↓reduceIte]
  | lam bc =>
    rw [hh] at h hfam
    cases h
    subst hfam
    simp only [famCount, Head.family] at room ⊢
    refine ⟨(0, l + 1, 0), ?_, rfl, fun _ => rfl, fun e => absurd rfl e, fun _ => rfl, Nat.le_refl _⟩
    simp only [wireCounts, hacc, hside, room, ↓reduceIte]
  | all bc r =>
    rw [hh] at h hfam
    cases h
    subst hfam
    simp only [famCount, Head.family] at room ⊢
    refine ⟨(0, 0, al + 1), ?_, rfl, fun _ => rfl, fun _ => rfl, fun e => absurd rfl e, Nat.le_refl _⟩
    simp only [wireCounts, hacc, hside, room, ↓reduceIte]
  | _ => rw [hh] at h; cases h

/-- A spine of `F` nodes over a tail that opens no `F` telescope opens one
node per spine node. -/
theorem spineFold_wire (F : Family) (buildSide : Node → Except SharingError Ixon.Expr) :
    ∀ (ns : List Node) (tail res : Ixon.Expr) (c0 : Nat × Nat × Nat),
      (∀ n ∈ ns, n.head.family = F) →
      (∀ n ∈ ns, ∀ e, buildSide n = .ok e → (wireCounts e).isSome) →
      wireCounts tail = some c0 → famCount F c0 = 0 → ns.length < UInt64.size →
      ns.foldrM (fun n acc => do let side ← buildSide n; rebuildSpineNode n acc side) tail =
        .ok res →
      ∃ c, wireCounts res = some c ∧ famCount F c = ns.length ∧
        (ns ≠ [] → TopOK F ns.length c)
  | [], tail, res, c0, _, _, htail, hzero, _, h => by
    cases h
    exact ⟨c0, htail, hzero, fun e => absurd rfl e⟩
  | n :: ns, tail, res, c0, hfam, hsides, htail, hzero, hlen, h => by
    rw [List.foldrM_cons] at h
    obtain ⟨acc, hacc, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
    obtain ⟨side, hside, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
    obtain ⟨ca, hca, hcount, -⟩ := spineFold_wire F buildSide ns tail acc c0
      (fun m hm => hfam m (List.mem_cons_of_mem _ hm))
      (fun m hm => hsides m (List.mem_cons_of_mem _ hm)) htail hzero
      (by simp at hlen; omega) hacc
    obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.mp (hsides n List.mem_cons_self side hside)
    simp only [List.length_cons] at hlen ⊢
    obtain ⟨c, hc, hcF, top⟩ := rebuild_wire (hfam n List.mem_cons_self) hca hcs (by omega) h
    rw [hcount] at hcF top
    exact ⟨c, hc, hcF, fun _ => top⟩

theorem topOK_mono {F : Family} {a b : Nat} {c : Nat × Nat × Nat} (h : TopOK F a c) (le : a ≤ b) :
    TopOK F b c :=
  ⟨h.1, h.2.1, h.2.2.1, Nat.le_trans h.2.2.2 le⟩

/-- **Built expressions are in the wire domain**, with the top counts of
their term's family. -/
theorem PrepWF.build_wire {p : Prep} (hp : PrepWF p)
    (fits : ∀ t, t < p.dag.size → HeadFits (p.dag.node t).head) (small : p.dag.size < UInt64.size)
    {wd : Nat → Nat} {avail : Nat → Bool} (ev : DictEval) (hev : GEvalOK p wd avail ev)
    (index width : Array (Option Nat))
    (hwidth : ∀ u, widthOf width u = if avail u then some (wd u) else none)
    (hindex : ∀ u, (index[u]?.getD none).isSome = avail u) :
    ∀ (fuel : Nat) (entry : Bool) (t : Nat) (e : Ixon.Expr), t < p.dag.size →
      p.build ev index width entry fuel t = .ok e →
      ∃ c, wireCounts e = some c ∧ TopOK p.family[t]! p.spineLen[t]! c := by
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
        obtain ⟨b, hb⟩ := Ix.Sharing.Verify.SharingExact.pickOption_mem _ hpick
        have hmem : (choice, c, b) ∈ (p.options ev index width t).toList := by
          split at hb
          · rw [Array.toList_filter] at hb; exact (List.mem_filter.mp hb).1
          · exact hb
        have hopt := hp.gOptions_mem ev hev index width hwidth hindex ht hmem
        split at h
        · -- a Share
          split at h
          · cases h
            exact ⟨(0, 0, 0), rfl, topOK_zero _ _⟩
          · cases h
        · -- an inline node
          obtain ⟨h1, _⟩ | ⟨_, hf, _⟩ | ⟨j, h1, _⟩ := hopt
          · cases h1
          · have har := hp.dag.arity t ht
            rw [← dag_node_eq ht] at har
            have fit := fits t ht
            cases hh : (p.dag.node t).head <;> simp only [hh, HeadFits] at h har fit
            case prj ti f =>
              obtain ⟨v, hv, hpure⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
              cases hpure
              have hc0 : (p.dag.node t).child 0 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              obtain ⟨cv, hcv, _⟩ := ih false _ v (by omega) hv
              exact ⟨(0, 0, 0), by simp [wireCounts, hcv], topOK_zero _ _⟩
            case letE lc =>
              obtain ⟨ty, hty, h2⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
              obtain ⟨v, hv, h3⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h2
              obtain ⟨bd, hbd, hpure⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h3
              cases hpure
              have hc0 : (p.dag.node t).child 0 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              have hc1 : (p.dag.node t).child 1 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              have hc2 : (p.dag.node t).child 2 < t :=
                hp.dag.childAt_lt ht (by simp [hh, Head.arity])
              obtain ⟨c0, h0, _⟩ := ih false _ ty (by omega) hty
              obtain ⟨c1, h1', _⟩ := ih false _ v (by omega) hv
              obtain ⟨c2, h2', _⟩ := ih false _ bd (by omega) hbd
              exact ⟨(0, 0, 0), by simp [wireCounts, h0, h1', h2'], topOK_zero _ _⟩
            case ref r us =>
              cases h
              exact ⟨(0, 0, 0), by simp [Node.toExpr, hh, wireCounts, fit], topOK_zero _ _⟩
            case recur r us =>
              cases h
              exact ⟨(0, 0, 0), by simp [Node.toExpr, hh, wireCounts, fit], topOK_zero _ _⟩
            all_goals first
              | (cases h; done)
              | (cases h
                 exact ⟨(0, 0, 0), by simp [Node.toExpr, hh, wireCounts], topOK_zero _ _⟩)
          · cases h1
        · -- a telescope cut
          rename_i j
          obtain ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨j', hj', hf, hj1, hjl, hcase⟩ := hopt
          · cases h1
          · cases h1
          cases hj'
          obtain ⟨_, hk, hend, htl, htf⟩ := hp.spine t ht hf
          have lenLe := hp.spineLen_le t ht
          have hfam : ∀ n ∈ (List.range j).map (fun k => p.dag.node (spineAt p t k)),
              n.head.family = p.family[t]! := by
            intro n hn
            obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hn
            rw [List.mem_range] at hk'
            obtain ⟨hle, hkf, _, _⟩ := hk k (by omega)
            rw [← hp.family _ (by omega), hkf]
          have hsides : ∀ n ∈ (List.range j).map (fun k => p.dag.node (spineAt p t k)), ∀ e',
              p.build ev index width false fuel n.sideChild = .ok e' → (wireCounts e').isSome := by
            intro n hn e' he'
            obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hn
            rw [List.mem_range] at hk'
            obtain ⟨hle, hkf, _, _⟩ := hk k (by omega)
            have hs := hp.sideChild_lt (t := spineAt p t k) (by omega) (by rw [hkf]; exact hf)
            obtain ⟨c', hc', _⟩ := ih false _ e' (by omega) he'
            simp [hc']
          have hlen : ((List.range j).map fun k => p.dag.node (spineAt p t k)).length = j := by simp
          rw [spineWalk_eq] at h
          split at h
          · cases h
          split at h
          · -- the prefix ends in a Share
            split at h
            · obtain ⟨tl, htl', hfold⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
              cases htl'
              obtain ⟨c, hc, hcount, top⟩ := spineFold_wire p.family[t]! _ _ _ _ (0, 0, 0) hfam
                hsides rfl (by cases p.family[t]! <;> rfl) (by rw [hlen]; omega) hfold
              rw [hlen] at hcount top
              exact ⟨c, hc, topOK_mono (top (by simp; omega)) hjl⟩
            · obtain ⟨tl, htl', _⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
              cases htl'
          · -- the full spine ends in the natural tail
            rename_i _ hjlt
            have hjeq : j = p.spineLen[t]! := by omega
            obtain ⟨tl, htl', hfold⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
            simp only at htl'
            rw [hjeq, hend] at htl'
            obtain ⟨ct, hct, topT⟩ := ih false _ tl (by omega) htl'
            obtain ⟨c, hc, hcount, top⟩ := spineFold_wire p.family[t]! _ _ _ _ ct hfam hsides hct
              (famCount_zero topT (Ne.symm htf)) (by rw [hlen]; omega) hfold
            rw [hlen] at hcount top
            exact ⟨c, hc, topOK_mono (top (by simp; omega)) hjl⟩
      · cases h
    · cases h

end Ix.Sharing.Verify.UniformModel

#guard_kernel_axioms Ix.Sharing.Verify.UniformModel.PrepWF.build_wire [propext, Quot.sound]
