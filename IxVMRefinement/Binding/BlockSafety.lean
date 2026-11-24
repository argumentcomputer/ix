import IxVMRefinement.Assembly.RolePreludeBridge
import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.Assembly.RecordReadBare
import IxVMRefinement.Assembly.ConstructorHashes
import IxVM.Obs.KernelCheck
import IxVMRefinement.StatementRel.LoadedReads
import IxC.Ixon.Verify.ConstantBounds

/-! # A block whose member-kind check passed is in Lean's logic when one of its constants is

`KernelCheck::check_block_member_kinds` counts the constants of a block (members and
constructors) and those outside Lean's logic (`KernelCheck::muts_safety_counts`), and asserts
`n_unsafe * (n_all - n_unsafe) = 0`. The counts are below `2^33` (the block's bytes are fewer
than `2^32`), so in the field the product vanishes only if no constant is outside the logic or
all are.

* `block_inLogic_of_member_kinds`: over a run store, an observed member-kind check of a block
  with one member that has a constant in Lean's logic (`MemberHasLogic`) makes the block's
  record `InLogic`.
* `safetyDecline_none_of_unsafe_ci_zero`: a converted definition on which
  `KernelCheck::is_unsafe_ci` answers `0` is one the reader accepts.

The counting specifications are those of `IxVMRefinement.Assembly.SafeRefsBridge`
(`check_block_member_kinds_inLogic`), which keeps them private and states its conclusion under a
collision-free view; they are restated here over a run store, with a public premise.
-/

set_option maxHeartbeats 1600000

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

private theorem field_zero_ne_one : (Value.field (0 : F) : SourceValue F) ≠ .field 1 := by
  intro h
  injection h with h01
  exact zero_ne_one h01


/-- Unsafe flag weight (`0` or `1`) of a constructor in `KernelCheck::ctors_safety_counts`. -/
private def ctorUnsafeBit (ct : Ixon.Constructor) : Nat :=
  if ct.isUnsafe then 1 else 0

/-- Unsafe weight of a mutual block member in `KernelCheck::muts_safety_counts`. -/
private def mutUnsafeCount : Ixon.MutConst → Nat
  | .defn d => if (Ix.Kernel.Reader.safetyDecline d).isNone then 0 else 1
  | .indc ind => (if ind.isUnsafe then 1 else 0) + (ind.ctors.toList.map ctorUnsafeBit).sum
  | .recr rc => if rc.isUnsafe then 1 else 0

/-- Total member + constructor count of a mutual block member in `KernelCheck::muts_safety_counts`. -/
private def mutConstCount : Ixon.MutConst → Nat
  | .defn _ => 1
  | .indc ind => 1 + ind.ctors.toList.length
  | .recr _ => 1

private theorem sum_ctorUnsafeBit_le_length :
    ∀ (cs : List Ixon.Constructor), (cs.map ctorUnsafeBit).sum ≤ cs.length
  | [] => Nat.le_refl 0
  | ct :: rest => by
    have hih := sum_ctorUnsafeBit_le_length rest
    simp only [List.map_cons, List.sum_cons, List.length_cons, ctorUnsafeBit]
    cases ct.isUnsafe <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem sum_ctorUnsafeBit_eq_zero_iff :
    ∀ (cs : List Ixon.Constructor),
      (cs.map ctorUnsafeBit).sum = 0 ↔ ∀ ct ∈ cs, ct.isUnsafe = false
  | [] => by simp
  | ct₀ :: rest => by
    rw [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff, sum_ctorUnsafeBit_eq_zero_iff rest]
    constructor
    · rintro ⟨hct, hrest⟩ c hc
      rcases List.mem_cons.mp hc with rfl | hm
      · cases h : c.isUnsafe <;> simp [ctorUnsafeBit, h] at hct ⊢
      · exact hrest c hm
    · intro hall
      refine ⟨?_, fun c hm => hall c (List.mem_cons_of_mem _ hm)⟩
      have h0 := hall ct₀ List.mem_cons_self
      simp [ctorUnsafeBit, h0]

private theorem sum_ctorUnsafeBit_lt_length_of_mem :
    ∀ {cs : List Ixon.Constructor} {ct : Ixon.Constructor},
      ct ∈ cs → ct.isUnsafe = false → (cs.map ctorUnsafeBit).sum < cs.length
  | [], _, hm, _ => nomatch hm
  | c :: rest, ct, hm, hsafe => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rcases List.mem_cons.mp hm with rfl | hmem
    · have hle := sum_ctorUnsafeBit_le_length rest
      simp [ctorUnsafeBit, hsafe]; omega
    · have hlt := sum_ctorUnsafeBit_lt_length_of_mem hmem hsafe
      simp only [ctorUnsafeBit]
      cases c.isUnsafe <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem mutUnsafeCount_le_mutConstCount (m : Ixon.MutConst) :
    mutUnsafeCount m ≤ mutConstCount m := by
  cases m with
  | defn d =>
    simp only [mutUnsafeCount, mutConstCount]
    cases (Ix.Kernel.Reader.safetyDecline d).isNone <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  | indc ind =>
    have hle := sum_ctorUnsafeBit_le_length ind.ctors.toList
    simp only [mutUnsafeCount, mutConstCount]
    cases ind.isUnsafe <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  | recr rc =>
    simp only [mutUnsafeCount, mutConstCount]
    cases rc.isUnsafe <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem mutUnsafeCount_eq_zero_iff (m : Ixon.MutConst) :
    mutUnsafeCount m = 0 ↔ IxVM.Consistency.InLogicMut m := by
  cases m with
  | defn d =>
    simp only [mutUnsafeCount, IxVM.Consistency.InLogicMut]
    cases h : Ix.Kernel.Reader.safetyDecline d <;> simp
  | indc ind =>
    simp only [mutUnsafeCount, IxVM.Consistency.InLogicMut, Nat.add_eq_zero_iff,
      sum_ctorUnsafeBit_eq_zero_iff]
    cases ind.isUnsafe <;> simp
  | recr rc =>
    simp only [mutUnsafeCount, IxVM.Consistency.InLogicMut]
    cases rc.isUnsafe <;> simp

private theorem sum_mutUnsafeCount_eq_zero_iff :
    ∀ (ms : List Ixon.MutConst),
      (ms.map mutUnsafeCount).sum = 0 ↔ ∀ m ∈ ms, IxVM.Consistency.InLogicMut m
  | [] => by simp
  | m :: rest => by
    rw [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff, mutUnsafeCount_eq_zero_iff,
      sum_mutUnsafeCount_eq_zero_iff rest]
    constructor
    · rintro ⟨hm, hrest⟩ x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hm
      · exact hrest x hmem
    · intro hall
      exact ⟨hall m List.mem_cons_self, fun x hmem => hall x (List.mem_cons_of_mem _ hmem)⟩

private theorem sum_mutUnsafeCount_lt_of_mem :
    ∀ {ms : List Ixon.MutConst} {m : Ixon.MutConst},
      m ∈ ms → mutUnsafeCount m < mutConstCount m →
      (ms.map mutUnsafeCount).sum < (ms.map mutConstCount).sum
  | [], _, hm, _ => nomatch hm
  | x :: rest, m, hm, hlt => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hm with rfl | hmem
    · have hle : (rest.map mutUnsafeCount).sum ≤ (rest.map mutConstCount).sum := by
        clear hm hlt
        induction rest with
        | nil => exact Nat.le_refl 0
        | cons y ys ih =>
          have hy := mutUnsafeCount_le_mutConstCount y
          simp only [List.map_cons, List.sum_cons]; omega
      omega
    · have hih := sum_mutUnsafeCount_lt_of_mem hmem hlt
      have hx := mutUnsafeCount_le_mutConstCount x
      omega

private theorem sum_ctor_resourceSize_ge_length :
    ∀ (cs : List Ixon.Constructor), cs.length ≤ (cs.map Ixon.Constructor.resourceSize).sum
  | [] => Nat.le_refl 0
  | ct :: rest => by
    have hih := sum_ctor_resourceSize_ge_length rest
    simp only [List.length_cons, List.map_cons, List.sum_cons, Ixon.Constructor.resourceSize]
    omega

private theorem mutConstCount_le_resourceSize (m : Ixon.MutConst) :
    mutConstCount m ≤ m.resourceSize := by
  cases m with
  | defn d => simp [mutConstCount, Ixon.MutConst.resourceSize, Ixon.Definition.resourceSize]
  | indc ind =>
    have hct := sum_ctor_resourceSize_ge_length ind.ctors.toList
    simp only [mutConstCount, Ixon.MutConst.resourceSize, Ixon.Inductive.resourceSize]
    omega
  | recr rc => simp [mutConstCount, Ixon.MutConst.resourceSize, Ixon.Recursor.resourceSize]

private theorem sum_mutConstCount_le_resourceSum :
    ∀ (ms : List Ixon.MutConst),
      (ms.map mutConstCount).sum ≤ (ms.map Ixon.MutConst.resourceSize).sum
  | [] => Nat.le_refl 0
  | m :: rest => by
    have hm := mutConstCount_le_resourceSize m
    have hih := sum_mutConstCount_le_resourceSum rest
    simp only [List.map_cons, List.sum_cons]; omega

private theorem sum_mutConstCount_lt_bound {rawBytes : ByteArray} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst}
    (hsz : rawBytes.size < 4294967296)
    (hdeExact : Ixon.deConstantExact rawBytes = .ok cb)
    (hms : cb.info = .muts ms) :
    (ms.toList.map mutConstCount).sum < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes cb hdeExact
  have hsum := sum_mutConstCount_le_resourceSum ms.toList
  have hinfo : (ms.toList.map Ixon.MutConst.resourceSize).sum ≤ cb.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    rw [hms]
    dsimp [Ixon.ConstantInfo.resourceSize]
    omega
  omega

private theorem mul_sub_eq_zero_nat {u n : Nat} (hun : u ≤ n) (hn : n < 8589934592)
    (h : ((u : F)) * (((n : F)) - ((u : F))) = 0) : u = 0 ∨ u = n := by
  rcases mul_eq_zero.mp h with hu0 | hsub0
  · refine .inl ?_
    have heq : (u : F) = ((0 : Nat) : F) := by simpa using hu0
    rw [ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega),
      Nat.mod_eq_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)] at heq
    exact heq
  · refine .inr ?_
    have heq : (n : F) = (u : F) := sub_eq_zero.mp hsub0
    rw [ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega),
      Nat.mod_eq_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)] at heq
    exact heq.symm

private theorem repBool_false_of_zero {b : Bool} {v : SourceValue F}
    (hb : Claim.RepBool b v) (hv : v = .field 0) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd (hb.symm.trans hv) (fun h => one_ne_zero (Value.field.inj h))

private theorem repBool_true_of_ne_zero {b : Bool} {v : SourceValue F}
    (hb : Claim.RepBool b v) (hv : v ≠ .field 0) : b = true := by
  cases b with
  | false => exact absurd hb hv
  | true => rfl

private theorem defn_is_unsafe_ci_count_spec {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
    {x_kind x_safety r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hk : Claim.RepDefKind kind x_kind)
    (hs : Claim.RepDefinitionSafety safety x_safety)
    (ev : ObsFn Core.W "Ingress::defn_is_unsafe_ci" [x_kind, x_safety] h r h' cs) :
    h' = h ∧
      r = .field (((if (Ix.Kernel.Reader.safetyDeclineOf kind safety).isNone then 0 else 1 : Nat) : F)) := by
  rcases Obs.«Ingress::defn_is_unsafe_ci».obs ev with
    ⟨hv15, rfl, rfl, -⟩ |
    ⟨_, hv25, hv41, rfl, rfl, -⟩ |
    ⟨_, hv25, hne46, rfl, rfl, -⟩ |
    ⟨_, _, hv58, hv74, rfl, rfl, -⟩ |
    ⟨_, _, hv58, hne79, rfl, rfl, -⟩
  · cases kind with
    | defn => simp [Claim.RepDefKind] at hk; rw [hk] at hv15; simp at hv15
    | opaq => simp [Claim.RepDefKind] at hk; rw [hk] at hv15; simp at hv15
    | thm =>
      refine ⟨rfl, ?_⟩
      have hd : (Ix.Kernel.Reader.safetyDeclineOf .thm safety).isNone = true := by
        cases safety <;> decide
      rw [hd]; simp
  · cases kind with
    | defn => simp [Claim.RepDefKind] at hk; rw [hk] at hv25; simp at hv25
    | thm => simp [Claim.RepDefKind] at hk; rw [hk] at hv25; simp at hv25
    | opaq =>
      cases safety with
      | safe => simp [Claim.RepDefinitionSafety] at hs; rw [hs] at hv41; simp at hv41
      | part => simp [Claim.RepDefinitionSafety] at hs; rw [hs] at hv41; simp at hv41
      | unsaf =>
        have hd : (Ix.Kernel.Reader.safetyDeclineOf .opaq .unsaf).isNone = false := by decide
        exact ⟨rfl, by rw [hd]; simp⟩
  · cases kind with
    | defn => simp [Claim.RepDefKind] at hk; rw [hk] at hv25; simp at hv25
    | thm => simp [Claim.RepDefKind] at hk; rw [hk] at hv25; simp at hv25
    | opaq =>
      cases safety with
      | unsaf => simp [Claim.RepDefinitionSafety] at hs; exact absurd hs (hne46 [] rfl)
      | safe =>
        have hd : (Ix.Kernel.Reader.safetyDeclineOf .opaq .safe).isNone = true := by decide
        exact ⟨rfl, by rw [hd]; simp⟩
      | part =>
        have hd : (Ix.Kernel.Reader.safetyDeclineOf .opaq .part).isNone = true := by decide
        exact ⟨rfl, by rw [hd]; simp⟩
  · cases kind with
    | opaq => simp [Claim.RepDefKind] at hk; rw [hk] at hv58; simp at hv58
    | thm => simp [Claim.RepDefKind] at hk; rw [hk] at hv58; simp at hv58
    | defn =>
      cases safety with
      | unsaf => simp [Claim.RepDefinitionSafety] at hs; rw [hs] at hv74; simp at hv74
      | part => simp [Claim.RepDefinitionSafety] at hs; rw [hs] at hv74; simp at hv74
      | safe =>
        have hd : (Ix.Kernel.Reader.safetyDeclineOf .defn .safe).isNone = true := by decide
        exact ⟨rfl, by rw [hd]; simp⟩
  · cases kind with
    | opaq => simp [Claim.RepDefKind] at hk; rw [hk] at hv58; simp at hv58
    | thm => simp [Claim.RepDefKind] at hk; rw [hk] at hv58; simp at hv58
    | defn =>
      cases safety with
      | safe => simp [Claim.RepDefinitionSafety] at hs; exact absurd hs (hne79 [] rfl)
      | unsaf =>
        have hd : (Ix.Kernel.Reader.safetyDeclineOf .defn .unsaf).isNone = false := by decide
        exact ⟨rfl, by rw [hd]; simp⟩
      | part =>
        have hd : (Ix.Kernel.Reader.safetyDeclineOf .defn .part).isNone = false := by decide
        exact ⟨rfl, by rw [hd]; simp⟩

private theorem ctors_safety_counts_spec (cs : List Ixon.Constructor) :
    ∀ {h h' : Heap F} {x_cs r : SourceValue F} {calls : List (Call F)} (u n : Nat),
      Aiur.Library.List.RepList Obs.Names.«Lists::Node<Ixon::Constructor>»
        Claim.RepConstructor h cs x_cs →
      ObsFn Core.W "KernelCheck::ctors_safety_counts"
        [x_cs, .field (u : F), .field (n : F)] h r h' calls →
      h' = h ∧
        r = .tuple [.field (((u + (cs.map ctorUnsafeBit).sum : Nat) : F)),
                    .field (((n + cs.length : Nat) : F))] := by
  induction cs with
  | nil =>
    intro h h' x_cs r calls u n rep ev
    cases Obs.«KernelCheck::ctors_safety_counts».obs ev with
    | Nil ld12 he24 he39 _ =>
      exact ⟨he39, by simpa using he24⟩
    | Cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
  | cons ct rest ih =>
    intro h h' x_cs r calls u n rep ev
    cases Obs.«KernelCheck::ctors_safety_counts».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load rep ld12
    | Cons x_rest x_is_unsafe _ _ _ _ _ _ v139 m140 _ _ v155 v156 ld12 sg147 op177 op193 ev153 _ =>
      obtain ⟨ct', rest', heq, hct, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with h1 h2
      subst ct' rest'
      obtain ⟨uVal, _, _, hv, hu, _, _⟩ := hct
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      have hu_eq : uVal = x_is_unsafe := hargs.1.symm
      have hv156 : v156 = .field (((n + 1 : Nat) : F)) := by
        simpa [Nat.cast_add] using Ingress.binop_add op193
      subst v156
      cases sg147 with
      | n0 hv128 he129 he130 _ =>
        subst he130 he129
        have hfalse := repBool_false_of_zero hu (hu_eq.trans hv128)
        have hv155 : v155 = .field (((u + 0 : Nat) : F)) := by
          simpa [Nat.cast_add] using Ingress.binop_add op177
        subst v155
        obtain ⟨hh', hr⟩ := ih (u + 0) (n + 1) hrest ev153
        refine ⟨hh', ?_⟩
        rw [hr]
        simp only [List.map_cons, List.sum_cons, List.length_cons, ctorUnsafeBit, hfalse,
          Bool.false_eq_true, ↓reduceIte]
        congr 2 <;> [skip; congr 1] <;> congr 1 <;> congr 1 <;> omega
      | other hne132 he136 he137 _ =>
        subst he137 he136
        have htrue := repBool_true_of_ne_zero hu (fun h0 => hne132 (hu_eq.symm.trans h0))
        have hv155 : v155 = .field (((u + 1 : Nat) : F)) := by
          simpa [Nat.cast_add] using Ingress.binop_add op177
        subst v155
        obtain ⟨hh', hr⟩ := ih (u + 1) (n + 1) hrest ev153
        refine ⟨hh', ?_⟩
        rw [hr]
        simp only [List.map_cons, List.sum_cons, List.length_cons, ctorUnsafeBit, htrue, ↓reduceIte]
        congr 2 <;> [skip; congr 1] <;> congr 1 <;> congr 1 <;> omega

private theorem muts_safety_counts_spec (ms : List Ixon.MutConst) :
    ∀ {h h' : Heap F} {x_ms r : SourceValue F} {calls : List (Call F)} (u n : Nat),
      Aiur.Library.List.RepList Obs.Names.«Lists::Node<Ixon::MutConst>»
        Claim.RepMutConst h ms x_ms →
      ObsFn Core.W "KernelCheck::muts_safety_counts"
        [x_ms, .field (u : F), .field (n : F)] h r h' calls →
      Heap.Extends h h' ∧
        r = .tuple [.field (((u + (ms.map mutUnsafeCount).sum : Nat) : F)),
                    .field (((n + (ms.map mutConstCount).sum : Nat) : F))] := by
  induction ms with
  | nil =>
    intro h h' x_ms r calls u n rep ev
    cases Obs.«KernelCheck::muts_safety_counts».obs ev with
    | Nil ld12 he24 he39 _ =>
      exact ⟨by rw [he39], by simpa using he24⟩
    | Cons_Defn _ _ _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _
    | Cons_Indc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ _ _ _
    | Cons_Recr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
  | cons m rest ih =>
    intro h h' x_ms r calls u n rep ev
    cases Obs.«KernelCheck::muts_safety_counts».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load rep ld12
    | Cons_Defn x_rest x_kind x_safety _ _ _ _ _ v136 v137 m146 y152 _ ld12 ev165 op158 op195 ev134 _ =>
      obtain ⟨m', rest', heq, hm, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with h1 h2
      subst m' rest'
      cases m with
      | indc _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | recr _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | defn d =>
        obtain ⟨dv, hv_m, kVal, sVal, _, _, _, hv_d, hk, hs, _, _, _⟩ := hm
        injection hv_m with _ _ hargs_m
        simp only [List.cons.injEq, and_true] at hargs_m
        rw [← hargs_m] at hv_d
        injection hv_d with _ _ hargs_d
        simp only [List.cons.injEq] at hargs_d
        rcases hargs_d with ⟨rfl, rfl, _⟩
        obtain ⟨hm146, hy152⟩ := defn_is_unsafe_ci_count_spec hk hs ev165
        subst m146 hy152
        have hv136 : v136 = .field (((u + mutUnsafeCount (.defn d) : Nat) : F)) := by
          simpa [mutUnsafeCount, Ix.Kernel.Reader.safetyDecline, Nat.cast_add] using Ingress.binop_add op158
        have hv137 : v137 = .field (((n + 1 : Nat) : F)) := by
          simpa [Nat.cast_add] using Ingress.binop_add op195
        subst v136 v137
        obtain ⟨hext, hr⟩ := ih (u + mutUnsafeCount (.defn d)) (n + 1) hrest ev134
        refine ⟨hext, ?_⟩
        rw [hr]
        simp only [List.map_cons, List.sum_cons, mutConstCount]
        congr 2 <;> [skip; congr 1] <;> congr 1 <;> congr 1 <;> omega
    | Cons_Indc x_rest x_is_unsafe _ _ _ _ x_ctors v285 m286 _ m295 _ x_cu x_cn _ v350 v351 x365 x390
        ld12 sg293 ev307 op380 op372 op405 op397 ev348 _ =>
      obtain ⟨m', rest', heq, hm, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with h1 h2
      subst m' rest'
      cases m with
      | defn _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | recr _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | indc ind =>
        obtain ⟨iv, hv_m, uVal, _, ctorsPtr, hv_i, hu, _, hctors⟩ := hm
        injection hv_m with _ _ hargs_m
        simp only [List.cons.injEq, and_true] at hargs_m
        rw [← hargs_m] at hv_i
        injection hv_i with _ _ hargs_i
        simp only [List.cons.injEq, and_true] at hargs_i
        rcases hargs_i with ⟨rfl, _, _, _, _, rfl⟩
        have hiu : m286 = h ∧ v285 = .field (((if ind.isUnsafe then 1 else 0 : Nat) : F)) := by
          cases sg293 with
          | n0 hv274 he275 he276 _ =>
            have hf := repBool_false_of_zero hu hv274
            exact ⟨he276, by simpa [hf] using he275⟩
          | other hne278 he282 he283 _ =>
            have ht := repBool_true_of_ne_zero hu hne278
            exact ⟨he283, by simpa [ht] using he282⟩
        obtain ⟨rfl, hv285⟩ := hiu
        subst hv285
        obtain ⟨rfl, hct_tup⟩ := ctors_safety_counts_spec ind.ctors.toList 0 0 hctors ev307
        simp only [Nat.zero_add, Value.tuple.injEq, List.cons.injEq, and_true] at hct_tup
        rcases hct_tup with ⟨rfl, rfl⟩
        have hx365 : x365 = .field (((u + (if ind.isUnsafe then 1 else 0) : Nat) : F)) := by
          simpa [Nat.cast_add] using Ingress.binop_add op380
        subst hx365
        have hv350 : v350 = .field (((u + mutUnsafeCount (.indc ind) : Nat) : F)) := by
          rw [Ingress.binop_add op372]
          simp only [mutUnsafeCount, Nat.cast_add, add_assoc]
        have hx390 : x390 = .field (((n + 1 : Nat) : F)) := by
          simpa [Nat.cast_add] using Ingress.binop_add op405
        subst hx390
        have hv351 : v351 = .field (((n + mutConstCount (.indc ind) : Nat) : F)) := by
          rw [Ingress.binop_add op397]
          simp only [mutConstCount, Nat.cast_add, Nat.cast_one, add_assoc]
        subst hv350 hv351
        obtain ⟨hext, hr⟩ := ih (u + mutUnsafeCount (.indc ind)) (n + mutConstCount (.indc ind)) hrest ev348
        refine ⟨hext, ?_⟩
        rw [hr]
        simp only [List.map_cons, List.sum_cons]
        congr 2 <;> [skip; congr 1] <;> congr 1 <;> congr 1 <;> omega
    | Cons_Recr x_rest _ x_is_unsafe _ _ _ _ _ _ _ v515 m516 _ _ v531 v532
        ld12 sg523 op553 op569 ev529 _ =>
      obtain ⟨m', rest', heq, hm, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with h1 h2
      subst m' rest'
      cases m with
      | defn _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | indc _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | recr rc =>
        obtain ⟨rv, hv_m, _, uVal, _, _, hv_r, _, hu, _, _⟩ := hm
        injection hv_m with _ _ hargs_m
        simp only [List.cons.injEq, and_true] at hargs_m
        rw [← hargs_m] at hv_r
        injection hv_r with _ _ hargs_r
        simp only [List.cons.injEq] at hargs_r
        rcases hargs_r with ⟨_, rfl, _⟩
        have hru : m516 = h ∧ v515 = .field (((if rc.isUnsafe then 1 else 0 : Nat) : F)) := by
          cases sg523 with
          | n0 hv504 he505 he506 _ =>
            have hf := repBool_false_of_zero hu hv504
            exact ⟨he506, by simpa [hf] using he505⟩
          | other hne508 he512 he513 _ =>
            have ht := repBool_true_of_ne_zero hu hne508
            exact ⟨he513, by simpa [ht] using he512⟩
        obtain ⟨rfl, hv515⟩ := hru
        subst hv515
        have hv531 : v531 = .field (((u + mutUnsafeCount (.recr rc) : Nat) : F)) := by
          simpa [mutUnsafeCount, Nat.cast_add] using Ingress.binop_add op553
        have hv532 : v532 = .field (((n + 1 : Nat) : F)) := by
          simpa [Nat.cast_add] using Ingress.binop_add op569
        subst hv531 hv532
        obtain ⟨hext, hr⟩ := ih (u + mutUnsafeCount (.recr rc)) (n + 1) hrest ev529
        refine ⟨hext, ?_⟩
        rw [hr]
        simp only [List.map_cons, List.sum_cons, mutConstCount]
        congr 2 <;> [skip; congr 1] <;> congr 1 <;> congr 1 <;> omega

/-- **A block member with a constant in Lean's logic**: a definition the reader accepts, an
inductive that is safe or has a safe constructor, a safe recursor. -/
def MemberHasLogic : Ixon.MutConst → Prop
  | .defn d => Ix.Kernel.Reader.safetyDecline d = none
  | .indc ind => ind.isUnsafe = false ∨ ∃ ct ∈ ind.ctors.toList, ct.isUnsafe = false
  | .recr rc => rc.isUnsafe = false

private theorem mutUnsafeCount_lt_of_memberHasLogic {m : Ixon.MutConst}
    (h : MemberHasLogic m) : mutUnsafeCount m < mutConstCount m := by
  cases m with
  | defn d =>
    simp only [MemberHasLogic] at h
    simp [mutUnsafeCount, mutConstCount, h]
  | indc ind =>
    simp only [MemberHasLogic] at h
    rcases h with hs | ⟨ct, hct, hs⟩
    · have hle := sum_ctorUnsafeBit_le_length ind.ctors.toList
      simp only [mutUnsafeCount, mutConstCount, hs, Bool.false_eq_true, ↓reduceIte]
      omega
    · have hlt := sum_ctorUnsafeBit_lt_length_of_mem hct hs
      simp only [mutUnsafeCount, mutConstCount]
      cases ind.isUnsafe <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  | recr rc =>
    simp only [MemberHasLogic] at h
    simp [mutUnsafeCount, mutConstCount, h]

/-- **A block whose member-kind check the run observed is in Lean's logic when one of its
members has a constant in Lean's logic**: `KernelCheck::check_block_member_kinds` asserts that
the block's constants are all in Lean's logic or all outside it. Over a run store, at the block
record the store holds. -/
theorem block_inLogic_of_member_kinds {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀)
    {blk : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {x_block_addr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : Core.BaseSeams.addr h x_block_addr blk)
    (ev : ObsFn Core.W "KernelCheck::check_block_member_kinds" [x_block_addr] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hrec_blk : Ix.Cert.recordAt E₀ blk = some cb)
    (hcb : cb.info = .muts ms)
    (hmem : ∃ m ∈ ms.toList, MemberHasLogic m) :
    IxVM.Consistency.InLogic cb := by
  cases Obs.«KernelCheck::check_block_member_kinds».obs ev with
  | other m2 cs12 x_info _ _ _ _ ev14 hne329 _ _ hc335 =>
    obtain ⟨_, rawBytes, c_ld, _, hh_ld, hblk_ld, _, hexact_ld, hrep, _⟩ :=
      Claim.load_verified_constant_de ha ev14
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc335]; simp [hcl])
    have hcb_eq : c_ld = cb :=
      hS.record_eq hrec_blk (Claim.hashed_mono hsub12 hh_ld) hblk_ld hexact_ld
    subst c_ld
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1, hcb] at hinfo
    obtain ⟨mv, hmv, _⟩ := hinfo
    exact absurd hmv (hne329 [mv] rfl)
  | Muts m2 cs12 _ _ _ _ x_members _ m90 _ _ m132 _ _ _ _ x_n_unsafe x_n_all v234 y243 _ _ _ _
      _ _ _ _ _ _ _
      ev14 ev102 ev151 _ _ ev187 op258 op249 heq267 _ _ _ _ _ _ _ _ _ hc328 =>
    obtain ⟨_, rawBytes, c_ld, hsz, hh_ld, hblk_ld, _, hexact_ld, hrep, _⟩ :=
      Claim.load_verified_constant_de ha ev14
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc328]; simp [hcl])
    have hcb_eq : c_ld = cb :=
      hS.record_eq hrec_blk (Claim.hashed_mono hsub12 hh_ld) hblk_ld hexact_ld
    subst c_ld
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1, hcb] at hinfo
    obtain ⟨mv, hmv, hms_rep⟩ := hinfo
    injection hmv with _ _ hmv_args
    simp only [List.cons.injEq, and_true] at hmv_args
    subst hmv_args
    have ext_m2_132 : Heap.Extends m2 m132 := ev102.heap_extends.trans ev151.heap_extends
    have hms_rep132 :=
      Aiur.Library.List.repList_heapMono₂ _ Claim.repMutConst_heapMono₂ ext_m2_132 hms_rep
    obtain ⟨_, htup⟩ := muts_safety_counts_spec ms.toList 0 0 hms_rep132 ev187
    simp only [Nat.zero_add, Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩
    have hy243 := Ingress.binop_sub op258
    subst hy243
    have hv234 := Ingress.binop_mul op249
    have hmul0 :
        (((ms.toList.map mutUnsafeCount).sum : F)) *
          ((((ms.toList.map mutConstCount).sum : F)) - (((ms.toList.map mutUnsafeCount).sum : F))) = 0 :=
      Value.field.inj (hv234.symm.trans heq267)
    obtain ⟨m₀, hm₀, hl₀⟩ := hmem
    have hlt₀ := mutUnsafeCount_lt_of_memberHasLogic hl₀
    have hlt_sum : (ms.toList.map mutUnsafeCount).sum < (ms.toList.map mutConstCount).sum :=
      sum_mutUnsafeCount_lt_of_mem hm₀ hlt₀
    have hbound_sum : (ms.toList.map mutConstCount).sum < 8589934592 :=
      sum_mutConstCount_lt_bound hsz hexact_ld hcb
    rcases mul_sub_eq_zero_nat (Nat.le_of_lt hlt_sum) hbound_sum hmul0 with hu0 | hun
    · simp only [IxVM.Consistency.InLogic, hcb]
      exact (sum_mutUnsafeCount_eq_zero_iff ms.toList).mp hu0
    · omega

/-- A flag represented as the field `0` is `false`. -/
theorem repBoolField_zero_false {b : Bool}
    (h : Ingress.repBoolField b = .field 0) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd h (fun heq => one_ne_zero (Value.field.inj heq))

/-- **A converted definition on which `KernelCheck::is_unsafe_ci` answers `0` is one the reader
accepts.** -/
theorem safetyDecline_none_of_unsafe_ci_zero {d : Ixon.Definition}
    {tyPtr valPtr hint : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Core.W "KernelCheck::is_unsafe_ci"
      [Ingress.defnValShape d tyPtr valPtr hint] h (.field 0) h' cs) :
    Ix.Kernel.Reader.safetyDecline d = none := by
  cases hk : d.kind with
  | thm =>
    rw [Ix.Kernel.Reader.safetyDecline, hk]
    cases d.safety <;> decide
  | opaq =>
    simp only [Ingress.defnValShape, hk] at ev
    cases Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | Opaque _ _ _ _ _ _ _ hv he _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hu_eq⟩
      have hf := repBoolField_zero_false (hu_eq.trans he.symm)
      rw [Ix.Kernel.Reader.safetyDecline, hk]
      cases hs : d.safety with
      | safe => decide
      | unsaf => rw [hs] at hf; exact absurd hf (by decide)
      | part => decide
    | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
    | Thm _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv
  | defn =>
    simp only [Ingress.defnValShape, hk] at ev
    cases Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | Defn_Safe _ _ _ _ _ hv _ _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hs_eq, _⟩
      have hsafe : d.safety = .safe := by
        cases hds : d.safety with
        | safe => rfl
        | unsaf => rw [hds] at hs_eq; simp [Ingress.repDefSafetyVal] at hs_eq
        | part => rw [hds] at hs_eq; simp [Ingress.repDefSafetyVal] at hs_eq
      rw [Ix.Kernel.Reader.safetyDecline, hk, hsafe]
      decide
    | Defn_other _ _ _ _ _ _ _ _ he _ _ =>
      exact absurd he field_zero_ne_one
    | Axiom _ _ _ hv | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv

end IxVM.Refinement.Assembly
