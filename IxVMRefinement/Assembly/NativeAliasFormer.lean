import IxVMRefinement.Assembly.NativeBlockReads
import IxVMRefinement.Assembly.NativeBlockFacts
import IxCK.Kernel.Model.Inductives.NativeAt

/-! # The former stage of a native block whose former is declared at a definition

The native block step's former stage (`formerStage_of_member`) and recognition
(`nativeParts_of_member`) hold where the reading of the former's type is a syntactic telescope of
the record's parameter and index counts ending in a sort (`FormerAtTele`). Otherwise the former
is declared at a definition that reaches its telescope only after unfolding (an alias former);
the circuit then types the head-normalized telescope (`KernelCheck::former_tele_typed`) and
asserts that the family has an index and that every constructor binder carries the zero-ness of
the family's sort (`former_decl_ok`'s second branch). This module is the second branch:

* `formerAt_cases`: the reading is a telescope of the counts (`FormerAtTele`), not a syntactic
  telescope into a sort at all (`FormerAtAlias`), or a syntactic telescope into a sort of another
  length (`FormerTeleOther`, which the circuit's `get_result_sort_level` refuses);
* recognition at the record's index count (`Ix.Kernel.Model.nativePartsAt?`):
  `nativePartsAt?_inv`, `nativePartsAt?_isSome`, `nativePartsAt_of_member`;
* IxCK's former stage at an alias former: `AliasTele` (the telescope constant checked from
  scratch, its shape, its definitional equality with the declared type), `aliasTele_of_tele`
  (inhabited by every former at its telescope), `sumIndRunJ_of_alias` (the stored former is the
  declared one, `FormerStoredJ`'s right branch), `formerStageAlias_of_member` (T6 at an alias
  former, over the named input `FormerAliasTele`);
* what the later stages read: `formerReadJ_of_zero` (`FormerReadJ`'s right branch) and
  `sumCtorsRunJ_retele` (the constructors' stage read at the telescope constant where its
  parameter binders are the declared former's).

Named input with no producer yet: `FormerAliasTele` (part E's evidence read at the prefix); see
its docstring.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (SumIndRunJ SumCtorsRunJ FormerReadJ ConstantValCheckJ Judgements
  ctorZeroOk)
open Ix.Kernel.Model (nativePartsAt? nativeRecStubAt rulesJ)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-! ## Recognition at a given index count -/

/-- `sumSplit` of constructors followed by a recursor with no rule. -/
theorem sumSplit_append_rec :
    ∀ (rest : List (ConstantInfo .anon)) (cvR : ConstantVal .anon) (mI rP : Nat),
      rest.all (fun | .ctorInfo .. => true | _ => false) = true →
      ∃ cs : List (ConstantVal .anon × Nat × Nat),
        Ix.Kernel.sumSplit (rest ++ [.recInfo cvR mI rP []]) = some (cs, cvR, mI, rP, []) ∧
        rest = cs.map (fun c => .ctorInfo c.1 c.2.1 c.2.2)
  | [], cvR, mI, rP, _ => ⟨[], rfl, rfl⟩
  | ci :: rest, cvR, mI, rP, hall => by
    cases ci with
    | ctorInfo cvC nP nF =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨cs, hsp, hrest⟩ := sumSplit_append_rec rest cvR mI rP hall.2
      refine ⟨(cvC, nP, nF) :: cs, ?_, by simp [hrest]⟩
      simp [List.cons_append, Ix.Kernel.sumSplit, hsp]
    | _ => simp at hall

/-- **What the recogniser at a given index count reads**: the block is the former and its
constructors, the parameter count is the given one, the eliminator is the small one, and at a
former that is not a syntactic telescope into a sort the index count is the given one. -/
theorem nativePartsAt?_inv {nPd nIdx : Nat} {block : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon} (h : nativePartsAt? nPd nIdx block = some p₀) :
    ∃ caps₀ : Ix.Kernel.IndCaps .anon,
      block = .indInfo p₀.cvT caps₀ :: p₀.ctors.map (fun c => .ctorInfo c.1 p₀.nP c.2) ∧
      p₀.nP = nPd ∧ p₀.large = false ∧
      Ix.Kernel.reservedBasisNames.contains p₀.cvT.name = false ∧
      (∀ c ∈ p₀.ctors, c.1.levelParams = p₀.cvT.levelParams ∧
        Ix.Kernel.reservedBasisNames.contains c.1.name = false) ∧
      ((∀ bs s, p₀.cvT.type.piBinders ≠ (bs, .sort s)) → p₀.nIdx = nIdx) := by
  cases block with
  | nil => simp [nativePartsAt?] at h
  | cons hd rest =>
    cases hd with
    | indInfo cvT caps₀ =>
      simp only [nativePartsAt?] at h
      split at h
      · next hall₀ =>
        have hall : (rest.all fun | .ctorInfo .. => true | _ => false) = true := by
          rw [List.all_eq_true] at hall₀ ⊢
          intro x hx
          have hx₀ := hall₀ x hx
          cases x <;> simp at hx₀ ⊢
        obtain ⟨hsh, _, _⟩ := Decl.nativeParts?_inv h
        obtain ⟨caps₁, rest₁, cs, mI, rP, rules, hblk, hsp, hcnt, hnP, hctors, _,
          hnbT, _, hcs, hctors_wf, _, _, hlarge_fn⟩ := Decl.nativeShape?_inv hsh
        simp only [List.cons.injEq, ConstantInfo.indInfo.injEq] at hblk
        obtain ⟨⟨rfl, rfl⟩, hrest₁⟩ := hblk
        let stubR : ConstantVal .anon :=
          { name := Ix.Kernel.auxKey p₀.cvT.name .recursor
            levelParams := p₀.cvT.levelParams
            type := .sort .zero }
        have hstub : nativeRecStubAt p₀.cvT nPd nIdx rest.length =
            .recInfo stubR (nPd + 1 + rest.length + nIdx) (nPd + 1 + rest.length) [] := rfl
        obtain ⟨cs₀, hsp₀, hrest_eq⟩ := sumSplit_append_rec rest stubR
          (nPd + 1 + rest.length + nIdx) (nPd + 1 + rest.length) hall
        have hlen₀ : cs₀.length = rest.length := by
          rw [hrest_eq]
          simp
        rw [hstub] at hrest₁
        rw [← hrest₁] at hsp
        rw [hsp₀] at hsp
        simp only [Option.some.injEq, Prod.mk.injEq] at hsp
        obtain ⟨rfl, hcvR_eq, rfl, rfl, rfl⟩ := hsp
        have hcvR_lps : p₀.cvR.levelParams = p₀.cvT.levelParams := by
          rw [← hcvR_eq]
        have hrest_map : rest = p₀.ctors.map (fun c => .ctorInfo c.1 p₀.nP c.2) := by
          rw [hrest_eq, hctors, List.map_map]
          apply List.map_congr_left
          intro c hc
          simp [(hcs c hc).1]
        have hlarge : p₀.large = false := by
          apply hlarge_fn
          intro elim heq
          rw [hcvR_lps] at heq
          have hlen := congrArg List.length heq
          simp at hlen
        refine ⟨caps₀, by rw [hrest_map], hnP, hlarge, hnbT, hctors_wf, fun halias => ?_⟩
        unfold Ix.Kernel.nativeCounts? at hcnt
        split at hcnt
        · next bs s₀ hpb => exact absurd hpb (halias bs s₀)
        · rw [hlen₀] at hcnt
          split at hcnt
          · exact nomatch hcnt
          · split at hcnt
            · simp only [Option.some.injEq, Prod.mk.injEq] at hcnt
              obtain ⟨-, h2⟩ := hcnt
              omega
            · exact nomatch hcnt
      · exact nomatch h
    | _ => simp [nativePartsAt?] at h

/-- **The recogniser at a given index count reads a former that is not a syntactic telescope
into a sort**, with its constructors, where the counts and level parameters agree and no name
is a reserved basis name. -/
theorem nativePartsAt?_isSome {nP nIdx : Nat} {cvT : ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon} {cs : List (ConstantInfo .anon)}
    (halias : ∀ bs s, cvT.type.piBinders ≠ (bs, .sort s))
    (hT : Ix.Kernel.reservedBasisNames.contains cvT.name = false)
    (hcs : ∀ c ∈ cs, ∃ cv nF, c = .ctorInfo cv nP nF ∧ cv.levelParams = cvT.levelParams ∧
      Ix.Kernel.reservedBasisNames.contains cv.name = false) :
    ∃ p₀, nativePartsAt? nP nIdx (.indInfo cvT caps :: cs) = some p₀ := by
  have hall : (cs.all fun | .ctorInfo .. => true | _ => false) = true := by
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨cv, nF, rfl, -, -⟩ := hcs c hc
    rfl
  obtain ⟨csT, hsp, hrest⟩ := sumSplit_append_rec cs
    ⟨Ix.Kernel.auxKey cvT.name .recursor, cvT.levelParams, .sort .zero⟩
    (nP + 1 + cs.length + nIdx) (nP + 1 + cs.length) hall
  have hlen : csT.length = cs.length := by
    rw [hrest]
    simp
  have hcnt : Ix.Kernel.nativeCounts? nP cvT csT (nP + 1 + cs.length + nIdx) (nP + 1 + cs.length)
      = some (nP, nIdx) := by
    unfold Ix.Kernel.nativeCounts?
    split
    · next bs s hpb => exact absurd hpb (halias bs s)
    · rw [hlen]
      split
      · next hc =>
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
        omega
      · split
        · simp only [Option.some.injEq, Prod.mk.injEq]
          exact ⟨trivial, by omega⟩
        · next hc =>
          simp only [beq_iff_eq] at hc
          omega
  simp only [nativePartsAt?]
  split
  case isFalse hneg =>
    exfalso
    apply hneg
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨cv, nF, rfl, -, -⟩ := hcs c hc
    rfl
  unfold Ix.Kernel.nativeParts?
  suffices h : ∃ q, Ix.Kernel.nativeShape? nP
      (.indInfo cvT caps :: (cs ++ [nativeRecStubAt cvT nP nIdx cs.length])) = some q by
    obtain ⟨q, hq⟩ := h
    exact ⟨_, by rw [hq]; rfl⟩
  simp only [Ix.Kernel.nativeShape?, nativeRecStubAt, hsp, hcnt]
  split
  · split <;> exact ⟨_, rfl⟩
  · rename_i hneg
    exfalso
    apply hneg
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨hT, Ix.Kernel.reservedBasisNames_contains_auxKey _ _⟩, ?_⟩
    intro c hc
    have hmem : ConstantInfo.ctorInfo c.1 c.2.1 c.2.2 ∈ cs := by
      rw [hrest]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    obtain ⟨cv, nF, e, hlps, hres⟩ := hcs _ hmem
    injection e with e1 e2 e3
    subst e1 e2
    exact ⟨⟨rfl, hlps⟩, hres⟩

/-! ## The case of the former -/

/-- **The former is declared at a definition**: the reading of its type is not a syntactic
telescope into a sort (at any length). -/
def FormerAtAlias (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ind : Ixon.Inductive) : Prop :=
  ∀ ty₀, (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
      ind.typ = .ok ty₀ →
    ∀ bs s, ty₀.piBinders ≠ (bs, .sort s)

/-- **The former is a syntactic telescope into a sort of another length** than the record's
parameter and index counts. The circuit refuses it: `get_result_sort_level` head-normalizes a
sort before a binder or a `∀` at the end, and the deterministic data head preserves both rigid constructors. -/
def FormerTeleOther (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ind : Ixon.Inductive) : Prop :=
  ∃ ty₀ bs s, (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
      ind.typ = .ok ty₀ ∧ ty₀.piBinders = (bs, .sort s) ∧
    bs.length ≠ ind.params.toNat + ind.indices.toNat

/-- **The three cases of the former's reading.** -/
theorem formerAt_cases (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ind : Ixon.Inductive) :
    FormerAtTele t E₀ B cb ind ∨ FormerAtAlias t E₀ B cb ind ∨ FormerTeleOther t E₀ B cb ind := by
  cases hr : (exprReader t (fun x => E₀.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ with
  | error e =>
    left
    intro ty₀ h
    rw [hr] at h
    cases h
  | ok ty₀ =>
    cases hpb : ty₀.piBinders with
    | mk bs r =>
      by_cases hs : ∃ s, r = .sort s
      · obtain ⟨s, rfl⟩ := hs
        by_cases hl : bs.length = ind.params.toNat + ind.indices.toNat
        · left
          intro ty₁ h
          rw [hr] at h
          obtain rfl := Except.ok.inj h
          refine ⟨bs, s, ?_⟩
          rw [← hl]
          exact Decl.stripPis_of_piBinders_sort _ hpb
        · right; right
          exact ⟨ty₀, bs, s, hr, hpb, hl⟩
      · right; left
        intro ty₁ h bs' s' he
        rw [hr] at h
        obtain rfl := Except.ok.inj h
        rw [hpb] at he
        injection he with _ hr'
        exact hs ⟨s', hr'⟩

section Recognise

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}

/-- **The declared block is recognised at the record's index count**, at a former declared at a
definition, with distinct constructor names; the recognised index count is the record's. -/
theorem nativePartsAt_of_member (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (halias : FormerAtAlias t E₀ B cb ind) {blk : List (ConstantInfo .anon)}
    (hblk : BlockReadings t E₀ B ind blk)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x)) :
    ∃ p₀, nativePartsAt? ind.params.toNat ind.indices.toNat blk = some p₀ ∧
      (p₀.ctors.map (·.1.name)).Nodup ∧ p₀.nIdx = ind.indices.toNat := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  obtain ⟨ty₀, caps, cs, rfl, hty, hlen, hcs⟩ := blockReads_shape ht hbound hS hrec hchk hblk
  have hal := halias ty₀ hty
  have hfreeF : Decl.KeyFree (keyOf t (memberAddr B 0 (.indc ind))) :=
    hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hfreeC : ∀ j, j < ind.ctors.size → Decl.KeyFree (keyOf t (ctorAddr B 0 j)) :=
    fun j hj => hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)
  have hlt : ∀ j c, cs[j]? = some c → j < ind.ctors.size := by
    intro j c hc
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨p₀, hp₀⟩ := nativePartsAt?_isSome (nIdx := ind.indices.toNat) (caps := caps) (cs := cs)
    (cvT := ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩) hal
    hfreeF.1 (by
      intro c hc
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨ct, tyj, -, -, hl, hp, -, rfl, -⟩ := hcs j c hj
      exact ⟨_, _, by rw [hp], by simp [hl], (hfreeC j (hlt j _ hj)).1⟩)
  obtain ⟨caps₀, hshape, -, -, -, -, hnIdx⟩ := nativePartsAt?_inv hp₀
  injection hshape with hhead hcs'
  injection hhead with hcv _
  refine ⟨p₀, hp₀, ?_, hnIdx (by rw [← hcv]; exact hal)⟩
  have hnames : p₀.ctors.map (·.1.name) = cs.map (·.name) := by
    rw [hcs', List.map_map]
    rfl
  rw [hnames]
  obtain ⟨-, -, -, -, hnc, -⟩ := ctorSlots_of_member hbound hS hrec hchk
  have hjb : ∀ {j}, j < ind.ctors.size → j < UInt64.size := fun hj => by
    show _ < 18446744073709551616
    omega
  refine nodup_names_of_index (f := fun j => keyOf t (ctorAddr B 0 j)) (fun j c hc => ?_)
    (fun j j' hj hj' e => ctorAddr_inj hrec hjb j j' (by omega) (by omega)
      (Core.keyOf_inj (a₁ := ctorAddr B 0 j) (a₂ := ctorAddr B 0 j') htwf e))
  obtain ⟨ct, tyj, -, -, -, -, -, rfl, -⟩ := hcs j c hc
  rfl

end Recognise

/-! ## IxCK's former stage at an alias former -/

/-- **The telescope of a former declared at a definition**, in IxCK's terms: a constant of the
declared former's name and level parameters checked from scratch at some type (`cvTa`), whose
type is a syntactic telescope of `nPI` binders ending in the sort `s`, and definitionally equal
to the checked declared former's type (`cvTa₀`). -/
def AliasTele (env : Ix.Kernel.Env .anon) (cvT cvTa₀ cvTa : ConstantVal .anon) (nPI : Nat)
    (s : Ix.Kernel.Level) : Prop :=
  (∃ ty, ConstantValCheckJ rulesJ env { cvT with type := ty } cvTa) ∧
  (∃ bs, cvTa.type.stripPis nPI = some (bs, .sort s)) ∧
  Ix.Kernel.Rules.DefEq env 0 cvTa₀.type cvTa.type

/-- **Inhabited at every former declared at its telescope**: the checked declared former is
its own telescope constant. -/
theorem aliasTele_of_tele {env : Ix.Kernel.Env .anon} {cvT cvTa₀ : ConstantVal .anon}
    {nPI : Nat} {bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)} {s : Ix.Kernel.Level}
    (hchk : ConstantValCheckJ rulesJ env cvT cvTa₀)
    (htele : cvTa₀.type.stripPis nPI = some (bs, .sort s)) :
    AliasTele env cvT cvTa₀ cvTa₀ nPI s :=
  ⟨⟨cvT.type, by cases cvT; exact hchk⟩, ⟨bs, htele⟩, .refl⟩

/-- **IxCK's former stage at a former declared at a definition**: the declared former checked
(`cvTa₀`) is stored, the telescope constant is the one the later stages read, and the record is
completed with the telescope's sort (`FormerStoredJ`'s right branch, at a family with an
index). -/
theorem sumIndRunJ_of_alias {env : Ix.Kernel.Env .anon} {p : Ix.Kernel.InductiveShape .anon}
    {cvTa₀ cvTa : ConstantVal .anon} {isRec : Bool} {s : Ix.Kernel.Level}
    (hchk : ConstantValCheckJ rulesJ env p.cvT cvTa₀)
    (htele : AliasTele env p.cvT cvTa₀ cvTa (p.nP + p.nIdx) s) (hn : p.nIdx ≠ 0) :
    SumIndRunJ rulesJ env p (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
      ⟨.indInfo cvTa₀ (Ix.Kernel.nativeCapsAt (p.withSort s) isRec) :: env.consts⟩ cvTa
      (p.withSort s) := by
  obtain ⟨⟨ty, hty⟩, ⟨bs, hst⟩, hdq⟩ := htele
  exact ⟨cvTa₀, s, bs, cvTa₀, hchk, Or.inr ⟨ty, hty⟩, hst, Or.inr ⟨rfl, hdq, hn⟩, rfl, rfl⟩

/-- **What the later stages read of an alias former**: every stored constructor's binders carry
the zero-ness of the family's sort (`FormerReadJ`'s right branch; the circuit's `ctor_zero_all`,
read by `Decl.former_decl_ok_spec`). -/
theorem formerReadJ_of_zero {env₁ : Ix.Kernel.Env .anon} {p : Ix.Kernel.NativeParts .anon}
    {cvTa : ConstantVal .anon} {ctorsA : List (ConstantVal .anon × Nat)}
    (hz : ∀ cA ∈ ctorsA, ctorZeroOk p.cvT.name (Ix.Kernel.Level.zeronessOf p.resSort) cA.1.type
      = true) :
    FormerReadJ env₁ p cvTa ctorsA :=
  Or.inr (List.all_eq_true.mpr hz)

/-- **The constructors' stage read at another telescope constant** whose first `nP` binders open
to the same free variables: the stage reads the telescope constant only through its parameter
binders' domains. -/
theorem sumCtorsRunJ_retele {J : Judgements .anon} {env₀ env : Ix.Kernel.Env .anon}
    {T : Ix.Kernel.Key .anon} {lps : List Ix.Kernel.LevelParam} {nP nIdx : Nat}
    {resSort : Ix.Kernel.Level} {isProp large : Bool} {cvTa₁ cvTa₂ : ConstantVal .anon}
    {cs ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List Ix.Kernel.Level)}
    (hsame : ∀ tfvs r₁, Ix.Kernel.openPisAtFvars nP cvTa₁.type 0 = some (tfvs, r₁) →
      ∃ r₂, Ix.Kernel.openPisAtFvars nP cvTa₂.type 0 = some (tfvs, r₂))
    (h : SumCtorsRunJ J env₀ env T lps nP nIdx resSort isProp large cvTa₁ cs ctorsA sortss) :
    SumCtorsRunJ J env₀ env T lps nP nIdx resSort isProp large cvTa₂ cs ctorsA sortss := by
  obtain ⟨hl1, hl2, hall⟩ := h
  refine ⟨hl1, hl2, fun j c cA hc hcA => ?_⟩
  obtain ⟨hnF, sorts, hs, hchk, hres, fvsP, crest, tfvs, trest, xFvs, idxArgs, hopC, hopT,
    hdoms, hopX, hidx, hx, he, hfs⟩ := hall j c cA hc hcA
  obtain ⟨trest₂, hopT₂⟩ := hsame tfvs trest hopT
  exact ⟨hnF, sorts, hs, hchk, hres, fvsP, crest, tfvs, trest₂, xFvs, idxArgs, hopC, hopT₂,
    hdoms, hopX, hidx, hx, he, hfs⟩

/-! ## The former stage at the prefix -/

/-- **Part E's evidence at the prefix, in IxCK's terms** (named input). For the reading `ty₀` of
the former's type and its canonical annotation `ty'`: a telescope constant (`AliasTele`) of the
record's parameter and index counts, whose parameter binders open as `ty'`'s.

Intended producer: the `Induct` arm's call `KernelCheck::former_tele_typed` at a former with
`former_is_tele = 0` — `former_tele_at`'s result (syntactic binders kept, so the parameters'
domains are `ty'`'s; ends in `Srt(ind_level)`), `validate_expr_well_scoped` and `k_ensure_sort` of
it at the prefix context (`Decl.constantValCheckJ_of_scoped`-style), and the definitional
equality, which needs either a determinism lemma for `KernelWhnf::whnf` (the two head-normalizing
walks, `get_result_sort_level`'s and `former_tele_at`'s, agree) or a circuit assertion
`k_is_def_eq(ty, tele)` read by `Decl.scoped_core_defeq` (see the lane notes). Inhabited at every
former declared at its telescope (`aliasTele_of_tele`). -/
def FormerAliasTele (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ind : Ixon.Inductive) (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ ty₀ ty' : Ix.Kernel.Expr .anon,
    (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read ind.typ
      = .ok ty₀ →
    LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((Ingress.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) ind.typ ty₀
      = some ty' →
    ∃ (cvTa : ConstantVal .anon) (s : Ix.Kernel.Level),
      AliasTele env ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ cvTa
        (ind.params.toNat + ind.indices.toNat) s ∧
      ∀ tfvs r₁, Ix.Kernel.openPisAtFvars ind.params.toNat ty' 0 = some (tfvs, r₁) →
        ∃ r₂, Ix.Kernel.openPisAtFvars ind.params.toNat cvTa.type 0 = some (tfvs, r₂)

section Stage

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}

/-- **The former's stage of IxCK at the prefix, at a former declared at a definition** (T6,
second branch): the recognised block's declared former is checked against the prefix as its
canonical annotation and stored, the telescope constant of part E is the one the later stages
read, and the record is completed with the telescope's sort, for either recursion flag. The
stored former's key is the key of its projection address. -/
theorem formerStageAlias_of_member {E : Ixon.Env} (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    {blk : List (ConstantInfo .anon)} (hblk : BlockReadings t E₀ B ind blk)
    {p₀ : Ix.Kernel.NativeParts .anon}
    (hp₀ : nativePartsAt? ind.params.toNat ind.indices.toNat blk = some p₀)
    (hnIdx : p₀.nIdx = ind.indices.toNat) (hn : ind.indices.toNat ≠ 0)
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t (some n) env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hfree : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B 0)))
    (htele : FormerAliasTele t E B cb ind env) :
    ∀ isRec : Bool, ∃ (cvS cvTa : ConstantVal .anon) (s : Ix.Kernel.Level),
      SumIndRunJ rulesJ env p₀.toInductiveShape
        (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
        ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec)
          :: env.consts⟩ cvTa (p₀.toInductiveShape.withSort s) ∧
      cvS.name = Core.keyOf t (Core.iprjAddr B 0) ∧ cvTa.name = cvS.name ∧
      cvTa.levelParams = cvS.levelParams := by
  intro isRec
  have hbound : Bounded calls := (hst.good env none).2
  obtain ⟨ty₀, caps, cs, rfl, hty, -, -⟩ := blockReads_shape ht hbound hS hrec hchk hblk
  obtain ⟨hlbb, hdef, hfv⟩ := former_scope hbound hS hrec hchk hty
  have hblockE : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  have hprojE : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
    (recordOf_eq_recordAt_of_decoded hst.decoded _).trans (hst.runRecord _ _ hrec.former)
  have htyE : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀ :=
    ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) hty
  obtain ⟨ty', hcT, -, hcheck, -⟩ := formerChecked_of_member ht hst hinv hblockE hrec.muts
    hprojE hchk htyE hlbb hdef hfv hstored hfresh hfree
  obtain ⟨caps₀, hshape, -, -, -, -, -⟩ := nativePartsAt?_inv hp₀
  injection hshape with hhead _
  injection hhead with hcv _
  have hcvT : p₀.toInductiveShape.cvT =
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩ := hcv.symm
  obtain ⟨cvTa, s, hAT, -⟩ := htele ty₀ ty' htyE hcT
  have hn₀ : p₀.toInductiveShape.nIdx ≠ 0 := by
    show p₀.nIdx ≠ 0
    rw [hnIdx]
    exact hn
  have hnP : p₀.toInductiveShape.nP + p₀.toInductiveShape.nIdx =
      ind.params.toNat + ind.indices.toNat := by
    obtain ⟨-, -, hnP, -⟩ := nativePartsAt?_inv hp₀
    show p₀.nP + p₀.nIdx = _
    rw [hnP, hnIdx]
  have hchk' : ConstantValCheckJ rulesJ env p₀.toInductiveShape.cvT
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ := by
    rw [hcvT]
    exact hcheck
  have hAT' : AliasTele env p₀.toInductiveShape.cvT
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ cvTa
      (p₀.toInductiveShape.nP + p₀.toInductiveShape.nIdx) s := by
    rw [hcvT, hnP]
    exact hAT
  obtain ⟨⟨tyT, htyT⟩, -, -⟩ := hAT
  refine ⟨⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, cvTa, s,
    sumIndRunJ_of_alias hchk' hAT' hn₀, rfl, htyT.name_eq, htyT.levelParams_eq⟩

end Stage

end IxVM.Refinement.Typing
