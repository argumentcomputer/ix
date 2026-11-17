import IxVMRefinement.Assembly.NativeBlockNewLoads
import IxVMRefinement.Assembly.TypingDefnBlock
import IxVMRefinement.Assembly.NativeBlockNamed

/-! # The new constants of a native block's install, read off the member check

`nativeInstallOut_of_member`: from the member check of a one-type native block (the inputs of
`ctorOuts_of_member_named`) and distinct names in the prefix, the constants the install puts in
front of the prefix (`new`), with

* IxC's install with the family named (`NativeNoRecFacts`, the telescope constant the stored
  former);
* `BlockInstall` (the new constants as the store reads them, `NativeBlockNewFacts.lean`);
* what `UnitStep` asks of `new`: distinct names, fresh in the prefix, a constant at the key of
  every constant address of the record that stores the address's reading (`StoredAs`), and every
  new constant at such a key or at a derived key;
* the constructors as the record names them, and the family's counts.

The stored constants are the canonical annotations of the readings, so `StoredAs` reads the
annotation off `canonAnn` (`canonAnn_annotates`). The record's counts are bounded by the member
check's load (`member_bounds`).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

universe u

/-! ## The canonical annotation annotates the reading -/

/-- A positional binder trace applied to an expression annotates it. -/
theorem applyBinderTrace_annotates (md : Core.KLevel → Ix.Kernel.BinderMeta) (e : Core.KExpr) :
    ∀ (levels : List Core.KLevel) (e' : Core.KExpr) (rest : List Core.KLevel),
      L1.applyBinderTrace md e levels = some (e', rest) → Annotates e' e := by
  induction e with
  | bvar i =>
    intro levels e' rest h
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, -⟩ := h
    subst h1
    exact .bvar
  | fvar i ty ih =>
    intro levels e' rest h
    cases hx : L1.applyBinderTrace md ty levels with
    | none => simp [L1.applyBinderTrace, hx] at h
    | some r =>
      obtain ⟨ty', rem⟩ := r
      simp only [L1.applyBinderTrace, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, -⟩ := h
      subst h1
      exact .fvar (ih _ _ _ hx)
  | sort l =>
    intro levels e' rest h
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, -⟩ := h
    subst h1
    exact .sort
  | const k us =>
    intro levels e' rest h
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, -⟩ := h
    subst h1
    exact .const
  | app f a ihf iha =>
    intro levels e' rest h
    cases h1 : L1.applyBinderTrace md f levels with
    | none => simp [L1.applyBinderTrace, h1] at h
    | some r1 =>
      obtain ⟨f', a1⟩ := r1
      cases h2 : L1.applyBinderTrace md a a1 with
      | none => simp [L1.applyBinderTrace, h1, h2] at h
      | some r2 =>
        obtain ⟨a', a2⟩ := r2
        simp only [L1.applyBinderTrace, h1, h2, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h3, -⟩ := h
        subst h3
        exact .app (ihf _ _ _ h1) (iha _ _ _ h2)
  | lam dom body m ihd ihb =>
    intro levels e' rest h
    cases levels with
    | nil => simp [L1.applyBinderTrace] at h
    | cons level remaining =>
      cases h1 : L1.applyBinderTrace md dom remaining with
      | none => simp [L1.applyBinderTrace, h1] at h
      | some r1 =>
        obtain ⟨d', a1⟩ := r1
        cases h2 : L1.applyBinderTrace md body a1 with
        | none => simp [L1.applyBinderTrace, h1, h2] at h
        | some r2 =>
          obtain ⟨b', a2⟩ := r2
          simp only [L1.applyBinderTrace, h1, h2, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h3, -⟩ := h
          subst h3
          exact .lam (ihd _ _ _ h1) (ihb _ _ _ h2)
  | forallE dom body m ihd ihb =>
    intro levels e' rest h
    cases levels with
    | nil => simp [L1.applyBinderTrace] at h
    | cons level remaining =>
      cases h1 : L1.applyBinderTrace md dom remaining with
      | none => simp [L1.applyBinderTrace, h1] at h
      | some r1 =>
        obtain ⟨d', a1⟩ := r1
        cases h2 : L1.applyBinderTrace md body a1 with
        | none => simp [L1.applyBinderTrace, h1, h2] at h
        | some r2 =>
          obtain ⟨b', a2⟩ := r2
          simp only [L1.applyBinderTrace, h1, h2, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h3, -⟩ := h
          subst h3
          exact .forallE (ihd _ _ _ h1) (ihb _ _ _ h2)
  | letE ty v b m ihty ihv ihb =>
    intro levels e' rest h
    cases h1 : L1.applyBinderTrace md ty levels with
    | none => simp [L1.applyBinderTrace, h1] at h
    | some r1 =>
      obtain ⟨ty', a1⟩ := r1
      cases h2 : L1.applyBinderTrace md v a1 with
      | none => simp [L1.applyBinderTrace, h1, h2] at h
      | some r2 =>
        obtain ⟨v', a2⟩ := r2
        cases h3 : L1.applyBinderTrace md b a2 with
        | none => simp [L1.applyBinderTrace, h1, h2, h3] at h
        | some r3 =>
          obtain ⟨b', a3⟩ := r3
          simp only [L1.applyBinderTrace, h1, h2, h3, Option.bind_eq_bind, Option.bind_some,
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h4, -⟩ := h
          subst h4
          exact .letE (L1.annotates_instantiate1Lift (ihb _ _ _ h3) (ihv _ _ _ h2) 0)
  | lit l =>
    intro levels e' rest h
    simp only [L1.applyBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, -⟩ := h
    subst h1
    exact .lit
  | proj s i inner ih =>
    intro levels e' rest h
    cases hx : L1.applyBinderTrace md inner levels with
    | none => simp [L1.applyBinderTrace, hx] at h
    | some r =>
      obtain ⟨inner', rem⟩ := r
      simp only [L1.applyBinderTrace, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, -⟩ := h
      subst h1
      exact .proj (ih _ _ _ hx)

/-- **The canonical annotation of a reading annotates it.** -/
theorem canonAnn_annotates {src : Ixon.Constant} {ps : List Ix.Kernel.LevelParam} {root : F}
    {e : Ixon.Expr} {E_rd E' : Ix.Kernel.Expr .anon}
    (h : LoadedReads.canonAnn src ps root e E_rd = some E') : Annotates E' E_rd := by
  unfold LoadedReads.canonAnn at h
  obtain ⟨plan, -, hb⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨E'', rest⟩, hb', hE⟩ := Option.map_eq_some_iff.mp hb
  subst hE
  exact applyBinderTrace_annotates _ _ _ _ _ hb'

/-! ## Names -/

/-- Constants with distinct names in two lists with no name in common have distinct names. -/
theorem nodup_names_append {l₁ l₂ : List (ConstantInfo .anon)}
    (h₁ : (l₁.map (·.name)).Nodup) (h₂ : (l₂.map (·.name)).Nodup)
    (hd : ∀ a ∈ l₁, ∀ b ∈ l₂, a.name ≠ b.name) : ((l₁ ++ l₂).map (·.name)).Nodup := by
  induction l₁ with
  | nil => simpa using h₂
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at h₁
    rw [List.cons_append, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h₁.2 (fun a ha b hb => hd a (List.mem_cons_of_mem _ ha) b hb)⟩
    intro hm
    rw [List.map_append, List.mem_append] at hm
    rcases hm with hm | hm
    · exact h₁.1 hm
    · obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      exact hd x List.mem_cons_self b hb he.symm

/-- A key the environment does not find is no stored constant's name. -/
theorem name_ne_of_find_none {env : Ix.Kernel.Env .anon} {k : Ix.Kernel.Key .anon}
    (h : env.find? k = none) : ∀ ci ∈ env.consts, ci.name ≠ k := by
  intro ci hci he
  have := List.find?_eq_none.mp h ci hci
  simp [he] at this

/-! ## The install with the family named, as constants put in front -/

/-- **The install's environment, with the family named**: the projection table (at a
structure-like block), the constructors in reverse and the former with the capability record
the former's stage computed, in front of the prefix. -/
theorem NativeNoRecFacts.named_env {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ p : Ix.Kernel.NativeParts .anon}
    {cvS cvT' : ConstantVal .anon} {ctorsA : List (ConstantVal .anon × Nat)}
    (h : NativeNoRecFacts env env₂ blk nP p₀ ⟨p, cvS, cvT', ctorsA⟩) :
    ∃ (isRec : Bool) (s : Ix.Kernel.Level) (kinds : List (List Ix.Kernel.RecFieldKind))
      (caps : IndCaps .anon) (tbls : List (ConstantInfo .anon)),
      p = (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds ∧
      caps = Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec ∧
      caps = Ix.Kernel.nativeCaps p ∧
      env₂ = ⟨(tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS caps])) ++ env.consts⟩ ∧
      (tbls = [] ∨ ∃ tbl : Ix.Kernel.ProjTable .anon, tbls = [.projInfo tbl] ∧
        tbl.structName = p.cvT.name) := by
  obtain ⟨-, -, isRec, cvS', cvTa, caps, p₁, p', ctorsA', sortss, kinds, tfvs, trest, isorts, hfam,
    hInd, hp, -, -, hcaps, -, -, -, -, hTbl⟩ := h
  injection hfam with h1 h2 h3 h4
  subst h1 h2 h3 h4
  obtain ⟨cvTa₀, s, bs, cvS'', -, -, -, -, hp₁, henvI⟩ := hInd
  have hcapsEq : caps = Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec := by
    injection henvI with hl
    injection hl with hhd
    injection hhd with _ hc'
    rw [hc', hp₁]
  have hcapsP : caps = Ix.Kernel.nativeCaps p := by
    rw [hcapsEq, hcaps, hp₁]
  have hpEq : p = (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds := by
    rw [hp, hp₁]
  have hc : (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩).consts =
      ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS caps]) ++ env.consts := by
    rw [Decl.consts_consSumCtors_eq]
    simp
  rcases checkNativeTable_shape hTbl with heq | ⟨tbl, heq, hsn⟩
  · refine ⟨isRec, s, kinds, caps, [], hpEq, hcapsEq, hcapsP, ?_, Or.inl rfl⟩
    rw [heq]
    exact congrArg Ix.Kernel.Env.mk (by rw [hc]; rfl)
  · refine ⟨isRec, s, kinds, caps, [.projInfo tbl], hpEq, hcapsEq, hcapsP, ?_,
      Or.inr ⟨tbl, rfl, hsn⟩⟩
    rw [heq, hc]
    rfl

/-! ## The record's counts are bounded -/

private theorem idx_zero' (B : _root_.Address) :
    (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := by
  show ((0 : Nat).toUInt64).toNat = 0
  decide

/-- **The member check's load bounds the record's counts.** -/
theorem member_bounds {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
    {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}
    (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n) :
    ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56 := by
  have hchkA := mutsMemberAt_checkedAt (mc := .indc ind) hbound hchk rfl
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    _, _, _, _, hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, _, hsub_chk⟩ :=
    Assembly.checkedAtFull_loadedL1 hbound ⟨n, hchkA⟩
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B 0 (.indc ind)) =
      some (memberProjection B 0 (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.former
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨-, -, v', hld', hraw⟩ := LoadedReads.loadedL1_record hS hsub_ld hhash hblake hL1 hrecP
  have hvv : v' = v := Except.ok.inj (hld'.symm.trans hld)
  subst hvv
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', -, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 _ lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB
  subst cb'
  have hms_eq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [idx_zero' B] at hms' raw
  have hind_eq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms'
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  obtain ⟨hlv, hnp, hni, hnc, -⟩ := raw
  have h256 : (2 : Nat) ^ 56 = 72057594037927936 := by norm_num
  rw [h256]
  exact ⟨hnp, hni, hnc⟩

end IxVM.Refinement.Typing
