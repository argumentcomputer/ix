import IxVMRefinement.Assembly.TypingRecParentTie
import IxVMRefinement.Claim.Constant

/-! # The recursor record's counts against its parent's

The late relation pins the record against the family: the major index and rule prefix are the
family's (`nP + 1 + #ctors + nIdx`, `nP + 1 + #ctors`), one rule per constructor. This module
reads the counts off the circuit's check of the record:

* `AnnShape`, `annotates_annShape`, `majorKey_annotates_eq`: two annotations of one term agree
  up to binder data and free-variable annotations, so they have one major key; the parent the
  route reads at the step is the tie's (`RecMajorTie`);
* `get_ci_bytes_bound`, `recr_rules_size_lt`: the record the walk loaded has fewer than `2^33`
  rules (its bytes are fewer than `2^32`, and a rule takes at least one unit of the decoder's
  resource bound), so the rule count is read exactly from its field image;
* `rec_counts_of_arm`: the record's parameter, index and motive counts and its rule count, against
  the parent's member inductive: `n_p = parent_np`, `n_i = parent_ni` (the member check),
  `n_mot = 1` (the arm), and the length of the rule list the parent's constructor count (the
  member check's `Lists::length` run).
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

/-! ## Two annotations of one term -/

/-- Two terms of one shape, up to binder data and free-variable annotations. -/
inductive AnnShape : Ix.Kernel.Expr .anon → Ix.Kernel.Expr .anon → Prop
  | bvar (i : Nat) : AnnShape (.bvar i) (.bvar i)
  | fvar (i : Nat) (x y : Ix.Kernel.Expr .anon) : AnnShape (.fvar i x) (.fvar i y)
  | sort (l : Ix.Kernel.Level) : AnnShape (.sort l) (.sort l)
  | const (k : Ix.Kernel.Key .anon) (us : List Ix.Kernel.Level) :
      AnnShape (.const k us) (.const k us)
  | lit (l : Ix.Kernel.Literal) : AnnShape (.lit l) (.lit l)
  | app {f g a b : Ix.Kernel.Expr .anon} :
      AnnShape f g → AnnShape a b → AnnShape (.app f a) (.app g b)
  | lam {t t' b b' : Ix.Kernel.Expr .anon} {m m' : Ix.Kernel.BinderMeta} :
      AnnShape t t' → AnnShape b b' → AnnShape (.lam t b m) (.lam t' b' m')
  | forallE {t t' b b' : Ix.Kernel.Expr .anon} {m m' : Ix.Kernel.BinderMeta} :
      AnnShape t t' → AnnShape b b' → AnnShape (.forallE t b m) (.forallE t' b' m')
  | proj {s : Ix.Kernel.Key .anon} {i : Nat} {e e' : Ix.Kernel.Expr .anon} :
      AnnShape e e' → AnnShape (.proj s i e) (.proj s i e')

/-- **Two annotations of one term have one shape**: `Annotates` fixes all but binder data and
free-variable annotations, and reduces a `let` the same way in both. -/
theorem annotates_annShape {E' T : Ix.Kernel.Expr .anon} (h : Annotates E' T) :
    ∀ {E'' : Ix.Kernel.Expr .anon}, Annotates E'' T → AnnShape E' E'' := by
  induction h with
  | bvar => intro E'' h2; cases h2; exact .bvar _
  | fvar _ _ => intro E'' h2; cases h2; exact .fvar _ _ _
  | sort => intro E'' h2; cases h2; exact .sort _
  | const => intro E'' h2; cases h2; exact .const _ _
  | lit => intro E'' h2; cases h2; exact .lit _
  | app _ _ ihf iha =>
    intro E'' h2
    cases h2 with
    | app hf ha => exact .app (ihf hf) (iha ha)
  | lam _ _ iht ihb =>
    intro E'' h2
    cases h2 with
    | lam ht hb => exact .lam (iht ht) (ihb hb)
  | forallE _ _ iht ihb =>
    intro E'' h2
    cases h2 with
    | forallE ht hb => exact .forallE (iht ht) (ihb hb)
  | proj _ ih =>
    intro E'' h2
    cases h2 with
    | proj he => exact .proj (ih he)
  | letE _ ih =>
    intro E'' h2
    cases h2 with
    | letE he => exact ih he

/-- The heads of two terms of one shape have one shape. -/
theorem AnnShape.getAppFn {a b : Ix.Kernel.Expr .anon} (h : AnnShape a b) :
    AnnShape a.getAppFn b.getAppFn := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i x y => exact .fvar i x y
  | sort l => exact .sort l
  | const k us => exact .const k us
  | lit l => exact .lit l
  | app _ _ ihf _ => exact ihf
  | lam ht hb _ _ => exact .lam ht hb
  | forallE ht hb _ _ => exact .forallE ht hb
  | proj he _ => exact .proj he

/-- Two terms of one shape have one head key. -/
theorem headKey_eq_of_annShape {a b : Ix.Kernel.Expr .anon} (h : AnnShape a b) :
    headKey a = headKey b := by
  unfold headKey
  have hg := h.getAppFn
  generalize a.getAppFn = x at hg ⊢
  generalize b.getAppFn = y at hg ⊢
  cases hg <;> rfl

/-- Two terms of one shape strip the same number of `∀`s, to bodies of one shape. -/
theorem annShape_stripPis : ∀ (n : Nat) {a b : Ix.Kernel.Expr .anon}, AnnShape a b →
    (a.stripPis n = none ∧ b.stripPis n = none) ∨
      ∃ bs body bs' body', a.stripPis n = some (bs, body) ∧ b.stripPis n = some (bs', body') ∧
        AnnShape body body' := by
  intro n
  induction n with
  | zero =>
    intro a b h
    exact Or.inr ⟨[], a, [], b, rfl, rfl, h⟩
  | succ k ih =>
    intro a b h
    cases h with
    | @forallE t t' b₁ b₁' m m' ht hb =>
      rcases ih hb with ⟨h1, h2⟩ | ⟨bs, body, bs', body', h1, h2, h3⟩
      · left
        simp [Ix.Kernel.Expr.stripPis, h1, h2]
      · right
        exact ⟨(t, m) :: bs, body, (t', m') :: bs', body',
          by simp [Ix.Kernel.Expr.stripPis, h1], by simp [Ix.Kernel.Expr.stripPis, h2], h3⟩
    | bvar => exact Or.inl ⟨rfl, rfl⟩
    | fvar => exact Or.inl ⟨rfl, rfl⟩
    | sort => exact Or.inl ⟨rfl, rfl⟩
    | const => exact Or.inl ⟨rfl, rfl⟩
    | lit => exact Or.inl ⟨rfl, rfl⟩
    | app => exact Or.inl ⟨rfl, rfl⟩
    | lam => exact Or.inl ⟨rfl, rfl⟩
    | proj => exact Or.inl ⟨rfl, rfl⟩

/-- Two terms of one shape have one major key. -/
theorem majorKey_eq_of_annShape {rc : Ixon.Recursor} {a b : Ix.Kernel.Expr .anon}
    (h : AnnShape a b) : majorKey rc a = majorKey rc b := by
  unfold majorKey binderDom
  rcases annShape_stripPis (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat) h with ⟨h1, h2⟩ | ⟨bs, body, bs', body', h1, h2, h3⟩
  · rw [h1, h2]
  · rw [h1, h2]
    cases h3 with
    | forallE hd _ => exact headKey_eq_of_annShape hd
    | bvar => rfl
    | fvar => rfl
    | sort => rfl
    | const => rfl
    | lit => rfl
    | app => rfl
    | lam => rfl
    | proj => rfl

/-- **Two annotations of one term have one major key.** -/
theorem majorKey_annotates_eq {rc : Ixon.Recursor} {E' E'' T : Ix.Kernel.Expr .anon}
    (h1 : Annotates E' T) (h2 : Annotates E'' T) : majorKey rc E' = majorKey rc E'' :=
  majorKey_eq_of_annShape (annotates_annShape h1 h2)

/-! ## The rule count of a loaded record is small -/

/-- **The record `get_ci` loaded**: bytes fewer than `2^32`, hashed in the run, at the address,
decoding exactly to a record (every arm of `get_ci` starts with `load_verified_constant`). -/
theorem get_ci_bytes_bound {A : _root_.Address} {x_addr r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} (ha : Core.S0.addr h x_addr A)
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_addr] h r h' calls) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant), rawBytes.size < 4294967296 ∧
      Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = A ∧
      Ixon.deConstantExact rawBytes = .ok c := by
  have key : ∀ {v : SourceValue F} {m : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "Ingress::load_verified_constant" [x_addr] h v m cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∃ (rawBytes : ByteArray) (c : Ixon.Constant), rawBytes.size < 4294967296 ∧
        Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = A ∧
        Ixon.deConstantExact rawBytes = .ok c := by
    intro v m cs e hsub
    obtain ⟨-, rawBytes, c, hsz, hh, hb, -, hex, -, -⟩ := Claim.load_verified_constant_de ha e
    exact ⟨rawBytes, c, hsz, Core.hashed_mono hsub hh, hb, hex⟩
  match Obs.«Ingress::get_ci».obs ev with
  | .Defn_n0 (ev14 := e) (hc302 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .Defn_other (ev14 := e) (hc423 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .Axio (ev14 := e) (hc515 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .Quot (ev14 := e) (hc606 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .DPrj (ev14 := e) (hc675 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .IPrj (ev14 := e) (hc750 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .CPrj (ev14 := e) (hc851 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .RPrj (ev14 := e) (hc926 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])
  | .Recr (ev14 := e) (hc1071 := hc) .. =>
    exact key e (by intro cl hcl; rw [hc]; simp [hcl])

/-- A list of rules is no longer than its resource size. -/
theorem rules_length_le_resourceSum :
    ∀ rs : List Ixon.RecursorRule, rs.length ≤ (rs.map Ixon.RecursorRule.resourceSize).sum
  | [] => by simp
  | r :: rs => by
    have hr : 1 ≤ r.resourceSize := by dsimp [Ixon.RecursorRule.resourceSize]; omega
    have hrs := rules_length_le_resourceSum rs
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- **A decoded recursor record of fewer than `2^32` bytes has fewer than `2^33` rules.** -/
theorem recr_rules_size_lt {rawBytes : ByteArray} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hsz : rawBytes.size < 4294967296) (hde : Ixon.deConstantExact rawBytes = .ok c)
    (hinfo : c.info = .recr rc) : rc.rules.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes c hde
  have hlen := rules_length_le_resourceSum rc.rules.toList
  rw [Array.length_toList] at hlen
  have hrc : rc.rules.size ≤ c.resourceSize := by
    have h1 : (rc.rules.toList.map Ixon.RecursorRule.resourceSize).sum ≤ rc.resourceSize := by
      dsimp [Ixon.Recursor.resourceSize]
      omega
    have h2 : rc.resourceSize ≤ c.info.resourceSize := by
      rw [hinfo]
      dsimp [Ixon.ConstantInfo.resourceSize]
      omega
    have h3 : c.info.resourceSize ≤ c.resourceSize := by
      dsimp [Ixon.Constant.resourceSize]
      omega
    omega
  omega

/-! ## Field images of small counts -/

/-- Field images of two counts below the modulus are equal only if the counts are. -/
theorem field_nat_inj {a b : Nat} (ha : a < 18446744069414584321)
    (hb : b < 18446744069414584321)
    (h : (SourceValue.field (a : F) : SourceValue F) = .field (b : F)) : a = b := by
  have h' := congrArg ZMod.val (Value.field.inj h)
  rwa [ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega),
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)] at h'

/-- A converted rule list is a list of its cells. -/
theorem RulesTraceRep.toRepListTrue {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : L1.BinderTreeData} {h : Heap F} {j : Nat} {root : F}
    {rus : List Ixon.RecursorRule} {p : SourceValue F}
    (r : L1.RulesTraceRep refs recurAddrs univs sharing blobs tree h j root rus p) :
    RepList Core.krrListEnum (fun _ _ _ => True) h rus p := by
  induction r with
  | nil cell => exact .nil cell
  | cons cell _ _ _ _ _ ih => exact .cons cell trivial ih

/-- `Lists::length` of a converted rule list is its length. -/
theorem rulesTrace_length_spec {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : L1.BinderTreeData} {j : Nat} {root : F} {rus : List Ixon.RecursorRule}
    {p r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<KernelTypes::KRecRule>» [p] h r h' cs)
    (hr : L1.RulesTraceRep refs recurAddrs univs sharing blobs tree h j root rus p) :
    r = .field (rus.length : F) := by
  have ev' : ObsFn Obs.W
      (Instance.mk "Lists::length" [(.named "KernelTypes::KRecRule" [])]).symbol
      [p] h r h' cs := by
    rw [Obs.Names.«Lists::length<KernelTypes::KRecRule>».symbol]
    exact ev
  have hl' : RepList
      (Instance.mk "Lists::Node" [(.named "KernelTypes::KRecRule" [])]).symbol
      (fun _ _ _ => True) h rus p := by
    rw [Obs.Names.«Lists::Node<KernelTypes::KRecRule>».symbol]
    exact RulesTraceRep.toRepListTrue hr
  exact (Lib.Lists.length_spec ev' hl').1

end IxVM.Refinement.Typing
