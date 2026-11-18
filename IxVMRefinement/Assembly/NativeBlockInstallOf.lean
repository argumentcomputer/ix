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

/-! ## The install's new constants -/

/-- **What a native block's install puts in front of the prefix** (module docstring): IxC's
install with the family named, `BlockInstall`, and what `UnitStep` asks of the new constants. -/
structure NativeInstallOut (t : Ix.Kernel.RoleTable) (E₀ E : Ixon.Env) (n : Nat)
    (env : Ix.Kernel.Env .anon) (B : _root_.Address) (cb : Ixon.Constant)
    (ind : Ixon.Inductive) (blk : List (ConstantInfo .anon)) (p₀ : Ix.Kernel.NativeParts .anon)
    (new : List (ConstantInfo .anon)) (p : Ix.Kernel.NativeParts .anon)
    (ty' : Ix.Kernel.Expr .anon) (ctorsA : List (ConstantVal .anon × Nat))
    (caps : IndCaps .anon) : Prop where
  facts : NativeNoRecFacts env ⟨new ++ env.consts⟩ blk ind.params.toNat p₀
    ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩
  install : BlockInstall ⟨E, env, t, some n⟩ new B cb ind caps
  caps_eq : caps = Ix.Kernel.nativeCaps p
  nodup : (new.map (·.name)).Nodup
  fresh : ∀ ci ∈ new, env.find? ci.name = none
  reads : ∀ x, ConstAddrOf B cb x →
    ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀
  named : ∀ ci ∈ new, (∃ x, ConstAddrOf B cb x ∧ ci.name = keyOf t x) ∨
    ∃ k s, ci.name = .aux k s
  ctors : ∀ j < ind.ctors.size, ∃ (ct : Ixon.Constructor) (cty' : Ix.Kernel.Expr .anon),
    ind.ctors[j]? = some ct ∧ ct.lvls.toNat = ind.lvls.toNat ∧
    ct.params.toNat = ind.params.toNat ∧
    ctorsA[j]? = some (⟨Core.keyOf t (Core.cprjAddr B 0 j), List.range ct.lvls.toNat, cty'⟩,
      ct.fields.toNat)
  lenA : ctorsA.length = ind.ctors.size
  nP : p.nP = ind.params.toNat
  nIdx : p.nIdx = ind.indices.toNat
  nP₀ : p₀.nP = ind.params.toNat
  nIdx₀ : p₀.nIdx = ind.indices.toNat
  cvT : p.cvT = p₀.cvT
  cvT₀ : p₀.cvT.name = Core.keyOf t (Core.iprjAddr B 0) ∧
    p₀.cvT.levelParams = List.range ind.lvls.toNat
  ctorNames : p₀.ctors.map (·.1.name) = ctorsA.map (·.1.name)
  formerFind : (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
      (Core.keyOf t (Core.iprjAddr B 0)) =
    some (.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps)
  ctorFind : ∀ cA ∈ ctorsA, (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? cA.1.name =
    some (.ctorInfo cA.1 p.nP cA.2)
  tableName : ∀ tbl, ConstantInfo.projInfo tbl ∈ new →
    tbl.structName = Core.keyOf t (Core.iprjAddr B 0)

/-- **The table stage of a native block's install ran at sorts the classifier checked**: a
recursion flag and field sorts with `StageSortsChecked`, at which IxC's table stage, run after
the stage of that flag with the constructors stored, gives the environment of the install. With
`Guard.projGuardCert_of_checkNativeTable` this is what a certificate of the new projection table
is read from. -/
def InstallSortsChecked (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (n : Nat)
    (env : Ix.Kernel.Env .anon) (B : _root_.Address) (cvS : ConstantVal .anon)
    (p₀ : Ix.Kernel.NativeParts .anon) (new : List (ConstantInfo .anon))
    (p : Ix.Kernel.NativeParts .anon) (ctorsA : List (ConstantVal .anon × Nat)) : Prop :=
  ∃ (isRec : Bool) (sortss : List (List Ix.Kernel.Level)),
    StageSortsChecked calls t E n env B cvS p₀ ctorsA isRec sortss ∧
    Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss
      (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
        (p₀.toInductiveShape.withSort p₀.resSort) isRec) :: env.consts⟩) =
      .ok ⟨new ++ env.consts⟩

/-- **The new constants of a native block's install, read off the member check, with the sorts
of its table stage**: `nativeInstallOut_of_member`, and the table stage ran at sorts the
classifier checked (`InstallSortsChecked`, at the stored former). -/
theorem nativeInstallOut_of_member_checked {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {n : Nat} {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : L1.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env)
    (hndE : (env.consts.map (·.name)).Nodup) :
    ∃ (new : List (ConstantInfo .anon)) (p : Ix.Kernel.NativeParts .anon)
      (ty' : Ix.Kernel.Expr .anon) (ctorsA : List (ConstantVal .anon × Nat))
      (caps : IndCaps .anon),
      NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps ∧
      InstallSortsChecked calls t E n env B
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ p₀ new p ctorsA := by
  have hbound : Bounded calls := (hst.good env none).2
  have htwf : t.wf = true := hinv.tableWf
  obtain ⟨ty₀, ty', cvS, bsT, ctorsA, rawTypes, hty, hlbb, hdef, hcT, hcvT, hcvS, hnP₀, hnIdx₀,
    hlenP, hper, hT, hstT, hname, hlenA, hout, hun⟩ :=
    ctorOuts_of_member_named_checked ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP
      hkeys hfresh hfree hcov haux
  obtain ⟨p₀', hp₀', hnd₀⟩ := nativeParts_of_member ht hbound hS hrec hchk htele hblk hfree
  rw [hp₀] at hp₀'
  injection hp₀' with e
  subst e
  obtain ⟨env₂, p, hf, isRecQ, sortssQ, hQ, htabQ⟩ := nativeNoRecFacts_of_outs_named_with
    (Q := StageSortsChecked calls t E n env B cvS p₀ ctorsA) ht hS hst hrec hchk hblk hp₀ hnd₀
    hinv hfresh haux hT hstT hname hlenA hout hun
  subst hcvS
  obtain ⟨isRec, s, kinds, caps, tbls, hpEq, hcapsAt, hcapsP, henv₂, htbls⟩ := hf.named_env
  subst henv₂
  -- the family's counts and key
  have hpcvT : p.cvT = p₀.cvT := by rw [hpEq]; rfl
  have hpnP : p.nP = p₀.nP := by rw [hpEq]; rfl
  have hpnIdx : p.nIdx = p₀.nIdx := by rw [hpEq]; rfl
  have hlenA' : ctorsA.length = ind.ctors.size := hlenA.trans hlenP
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none :=
    hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hfreshC : ∀ j < ind.ctors.size, env.find? (keyOf t (ctorAddr B 0 j)) = none :=
    fun j hj => hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)
  have hbaseT : (Core.keyOf t (Core.iprjAddr B 0)).base = Core.keyOf t (Core.iprjAddr B 0) :=
    Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  have htbl : env.find? (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B 0))) = none :=
    haux.fresh_of_base_none (by
      show env.find? (Core.keyOf t (Core.iprjAddr B 0)).base = none
      rw [hbaseT]; exact hfreshT)
  have hTC : ∀ j < ind.ctors.size,
      keyOf t (ctorAddr B 0 j) ≠ Core.keyOf t (Core.iprjAddr B 0) := by
    intro j hj e
    have ha : ctorAddr B 0 j = memberAddr B 0 (.indc ind) := Core.keyOf_inj htwf e
    have h1 := hrec.ctors j hj
    rw [ha, hrec.former] at h1
    have hinfo := congrArg Ixon.Constant.info (Option.some.inj h1)
    simp [memberProjection, constructorProjection] at hinfo
  -- the constructors
  have hcOf : ∀ j < ind.ctors.size, ∃ c, p₀.ctors[j]? = some c := fun j hj =>
    ⟨p₀.ctors[j], List.getElem?_eq_getElem (by omega)⟩
  have hctorMem : ∀ cA ∈ ctorsA, ∃ j c, j < ind.ctors.size ∧ p₀.ctors[j]? = some c ∧
      ctorsA[j]? = some cA := by
    intro cA hcA
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hcA
    have hjlt : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
    have hjp : j < p₀.ctors.length := by omega
    exact ⟨j, p₀.ctors[j], by omega, List.getElem?_eq_getElem hjp, hj⟩
  have hnames : p₀.ctors.map (·.1.name) = ctorsA.map (·.1.name) := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_map, List.getElem?_map]
    cases hc : p₀.ctors[j]? with
    | none =>
      have h0 : ctorsA[j]? = none := by
        rw [List.getElem?_eq_none_iff] at hc ⊢
        omega
      rw [h0]
    | some c =>
      obtain ⟨ct, cty', -, -, -, -, -, -, -, -, -, -, -, hA⟩ := hper j c hc
      rw [hA]
      rfl
  -- every new constructor is a canonical constructor of the block
  have hrevMem : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse,
      ∃ j c cty', j < ind.ctors.size ∧ p₀.ctors[j]? = some c ∧
        ctorsA[j]? = some (⟨c.1.name, c.1.levelParams, cty'⟩, c.2) ∧
        ci = .ctorInfo ⟨c.1.name, c.1.levelParams, cty'⟩ p.nP c.2 := by
    intro ci hci
    obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hci)
    obtain ⟨j, c, hj, hc, hA⟩ := hctorMem cA hcA
    obtain ⟨ct, cty', -, -, -, -, -, -, -, -, -, -, -, hA'⟩ := hper j c hc
    rw [hA] at hA'
    injection hA' with hA'
    subst hA'
    exact ⟨j, c, cty', hj, hc, hA, rfl⟩
  have hrevName : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse,
      ∃ j < ind.ctors.size, ci.name = keyOf t (ctorAddr B 0 j) := by
    intro ci hci
    obtain ⟨j, c, cty', hj, hc, -, rfl⟩ := hrevMem ci hci
    obtain ⟨ct, cty'', -, -, -, -, hcn, -⟩ := hper j c hc
    exact ⟨j, hj, hcn⟩
  -- distinct names, fresh in the prefix
  have hndRev : ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse.map
      (·.name)).Nodup := by
    rw [List.map_reverse, List.nodup_reverse, List.map_map]
    have hf : ((·.name) ∘ fun c : ConstantVal .anon × Nat => ConstantInfo.ctorInfo c.1 p.nP c.2) =
        fun c => c.1.name := rfl
    rw [hf, ← hnames]
    exact hnd₀
  have hndL1 : (([ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0),
      List.range ind.lvls.toNat, ty'⟩ caps] ++ env.consts).map (·.name)).Nodup := by
    refine nodup_names_append (by simp) hndE ?_
    intro a ha b hb
    rw [List.mem_singleton.mp ha]
    exact (name_ne_of_find_none hfreshT b hb).symm
  have hndL2 : (((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      ([ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0),
      List.range ind.lvls.toNat, ty'⟩ caps] ++ env.consts)).map (·.name)).Nodup := by
    refine nodup_names_append hndRev hndL1 ?_
    intro a ha b hb
    obtain ⟨j, hj, hn⟩ := hrevName a ha
    rw [hn]
    rcases List.mem_append.mp hb with hb | hb
    · rw [List.mem_singleton.mp hb]
      exact hTC j hj
    · exact (name_ne_of_find_none (hfreshC j hj) b hb).symm
  have hndAll : (((tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        caps])) ++ env.consts).map (·.name)).Nodup := by
    rw [List.append_assoc, List.append_assoc]
    rcases htbls with rfl | ⟨tbl, rfl, hsn⟩
    · simpa using hndL2
    · refine nodup_names_append (by simp) hndL2 ?_
      intro a ha b hb
      rw [List.mem_singleton.mp ha]
      show Ix.Kernel.projTableName tbl.structName ≠ b.name
      rw [hsn, hpcvT, hcvT]
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨j, hj, hn⟩ := hrevName b hb
        rw [hn]
        exact (Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t _)).symm
      · rcases List.mem_append.mp hb with hb | hb
        · rw [List.mem_singleton.mp hb]
          exact (Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t _)).symm
        · exact (name_ne_of_find_none htbl b hb).symm
  have hfind : ∀ ci ∈ tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        caps]),
      (⟨(tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
          caps])) ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some ci :=
    fun ci hci => find_of_mem_nodup hndAll (List.mem_append_left _ hci)
  have hmemF : ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat,
      ty'⟩ caps ∈ tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        caps]) := by simp
  have hmemC : ∀ (j : Nat) (c : ConstantVal .anon × Nat) (cty' : Ix.Kernel.Expr .anon),
      p₀.ctors[j]? = some c →
      ctorsA[j]? = some (⟨c.1.name, c.1.levelParams, cty'⟩, c.2) →
      ConstantInfo.ctorInfo ⟨c.1.name, c.1.levelParams, cty'⟩ p.nP c.2 ∈
        tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
          caps]) := by
    intro j c cty' hc hA
    have h1 : ((⟨c.1.name, c.1.levelParams, cty'⟩, c.2) : ConstantVal .anon × Nat) ∈ ctorsA :=
      List.mem_of_getElem? hA
    have h2 : ConstantInfo.ctorInfo ⟨c.1.name, c.1.levelParams, cty'⟩ p.nP c.2 ∈
        ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2) :=
      List.mem_map.mpr ⟨_, h1, rfl⟩
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_reverse.mpr h2))
  -- the block's readings
  obtain ⟨fr, cs, hblkEq, hfrR, hlenC, hcsR⟩ := id hblk
  obtain ⟨caps₀, hshape, -, -, -, -, -, -⟩ := Decl.nativePartsNoRec?_inv hp₀
  rw [hshape] at hblkEq
  injection hblkEq with hfr hcs
  subst hfr hcs
  have hblockE : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  refine ⟨_, p, ty', ctorsA, caps, {
    facts := hf
    install := ?_
    caps_eq := hcapsP
    nodup := ?_
    fresh := ?_
    reads := ?_
    named := ?_
    ctors := ?_
    lenA := hlenA'
    nP := hpnP.trans hnP₀
    nIdx := hpnIdx.trans hnIdx₀
    nP₀ := hnP₀
    nIdx₀ := hnIdx₀
    cvT := hpcvT
    cvT₀ := by rw [hcvT]; exact ⟨rfl, rfl⟩
    ctorNames := hnames
    formerFind := hfind _ hmemF
    ctorFind := fun cA hcA => hfind (.ctorInfo cA.1 p.nP cA.2)
      (List.mem_append_right _ (List.mem_append_left _
        (List.mem_reverse.mpr (List.mem_map.mpr ⟨cA, hcA, rfl⟩))))
    tableName := ?_ }, isRecQ, sortssQ, hQ, htabQ⟩
  · -- the new constants as the store reads them
    obtain ⟨hp56, hi56, hc56⟩ := member_bounds hbound hS hrec hchk
    exact {
      check := ht
      decoded := hst.decoded
      held := hP
      block := hblockE
      muts := hrec.muts
      formerRec := (recordOf_eq_recordAt_of_decoded hst.decoded _).trans
        (hst.runRecord _ _ hrec.former)
      ctorRec := fun j hj => (recordOf_eq_recordAt_of_decoded hst.decoded _).trans
        (hst.runRecord _ _ (hrec.ctors j hj))
      bounds := ⟨hp56, hi56, hc56⟩
      used := usedRefsStored_append hstored _
      former := ⟨ty₀, ty', hty, hlbb, hdef, hcT, hfind _ hmemF⟩
      ctor := by
        intro j hj
        obtain ⟨c, hc⟩ := hcOf j hj
        obtain ⟨ct, cty', hct, hcidx, hcp, hcl, hcn, hclp, hc2, hrd, hclbb, hcdef, hcan, hA⟩ :=
          hper j c hc
        rw [ZMod.val_zero] at hcan
        refine ⟨ct, c.1.type, cty', hct, hcidx, hrd, hclbb, hcdef, hcan, ?_⟩
        have hf' := hfind _ (hmemC j c cty' hc hA)
        have hnP' : p.nP = ct.params.toNat := hpnP.trans (hnP₀.trans hcp.symm)
        rw [hcn, hclp, hc2] at hf'
        rw [← hnP']
        exact hf'
      newName := by
        intro ci hci
        rcases List.mem_append.mp hci with hci | hci
        · rcases htbls with rfl | ⟨tbl, rfl, -⟩
          · simp at hci
          · exact Or.inr (Or.inr ⟨tbl, List.mem_singleton.mp hci⟩)
        · rcases List.mem_append.mp hci with hci | hci
          · obtain ⟨j, hj, hn⟩ := hrevName ci hci
            exact Or.inr (Or.inl ⟨j, hj, hn⟩)
          · rw [List.mem_singleton.mp hci]
            exact Or.inl rfl
      newFind := hfind
      unit := by
        intro hi0 hsz hf0
        obtain ⟨c, hc1⟩ := List.length_eq_one_iff.mp (hlenP.trans hsz)
        have hc0 : p₀.ctors[0]? = some c := by rw [hc1]; rfl
        obtain ⟨ct, cty', hct, -, -, -, -, -, hc2, -⟩ := hper 0 c hc0
        have hcf : c.2 = 0 := hc2.trans (hf0 ct hct)
        have hcs1 : (p₀.toInductiveShape.withSort s).ctors = [c] := hc1
        rw [hcapsAt]
        unfold Ix.Kernel.nativeCapsAt
        rw [hcs1]
        have hidx : (p₀.toInductiveShape.withSort s).nIdx = 0 := hnIdx₀.trans hi0
        have hnp : (p₀.toInductiveShape.withSort s).nP = ind.params.toNat := hnP₀
        simp [hidx, hnp, hcf, hnIdx₀, hi0, hnP₀]
      free := (hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)).1 }
  · have h := hndAll
    rw [List.map_append] at h
    exact (List.nodup_append.mp h).1
  · intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · rcases htbls with rfl | ⟨tbl, rfl, hsn⟩
      · simp at hci
      · rw [List.mem_singleton.mp hci]
        show env.find? (Ix.Kernel.projTableName tbl.structName) = none
        rw [hsn, hpcvT, hcvT]
        exact htbl
    · rcases List.mem_append.mp hci with hci | hci
      · obtain ⟨j, hj, hn⟩ := hrevName ci hci
        rw [hn]
        exact hfreshC j hj
      · rw [List.mem_singleton.mp hci]
        exact hfreshT
  · intro x hx
    rcases hx with ⟨-, hs⟩ | ⟨ms', i, mi, hms', hmi, hx⟩
    · exact (standalone_not_block hs ⟨_, hrec.muts⟩).elim
    · rw [hrec.muts] at hms'
      have hmsEq : ms' = #[.indc ind] := (Ixon.ConstantInfo.muts.inj hms').symm
      subst hmsEq
      have hi : i = 0 := by
        have := (Array.getElem?_eq_some_iff.mp hmi).1
        simp at this
        omega
      subst hi
      have hmiEq : mi = .indc ind := by simpa using hmi.symm
      subst hmiEq
      rcases hx with rfl | ⟨ind', j, hind', hj, rfl⟩
      · refine ⟨_, hmemF, _, rfl, hfrR, ?_⟩
        unfold StoredAs
        refine ⟨?_, trivial⟩
        unfold ValStored
        rw [hcvT]
        exact ⟨rfl, rfl, canonAnn_annotates hcT⟩
      · injection hind' with hind'
        subst hind'
        obtain ⟨c, hc⟩ := hcOf j hj
        obtain ⟨ct, cty', hct, hcidx, hcp, hcl, hcn, hclp, hc2, hrd, hclbb, hcdef, hcan, hA⟩ :=
          hper j c hc
        have hcsj : (p₀.ctors.map (fun c => ConstantInfo.ctorInfo c.1 p₀.nP c.2))[j]? =
            some (.ctorInfo c.1 p₀.nP c.2) := by
          rw [List.getElem?_map, hc]
          rfl
        refine ⟨_, hmemC j c cty' hc hA, _, hcn, hcsR j _ hcsj, ?_⟩
        unfold StoredAs
        refine ⟨?_, hpnP, rfl⟩
        unfold ValStored
        exact ⟨rfl, rfl, canonAnn_annotates hcan⟩
  · intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · rcases htbls with rfl | ⟨tbl, rfl, -⟩
      · simp at hci
      · rw [List.mem_singleton.mp hci]
        exact Or.inr ⟨tbl.structName, .projTable, rfl⟩
    · rcases List.mem_append.mp hci with hci | hci
      · obtain ⟨j, hj, hn⟩ := hrevName ci hci
        exact Or.inl ⟨ctorAddr B 0 j,
          Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩, hn⟩
      · rw [List.mem_singleton.mp hci]
        exact Or.inl ⟨memberAddr B 0 (.indc ind),
          Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩, rfl⟩
  · intro j hj
    obtain ⟨c, hc⟩ := hcOf j hj
    obtain ⟨ct, cty', hct, hcidx, hcp, hcl, hcn, hclp, hc2, hrd, hclbb, hcdef, hcan, hA⟩ :=
      hper j c hc
    refine ⟨ct, cty', hct, hcl, hcp, ?_⟩
    rw [hA, hcn, hclp, hc2]
    rfl
  · intro tbl htm
    rcases List.mem_append.mp htm with h | h
    · rcases htbls with rfl | ⟨tbl', rfl, hsn⟩
      · simp at h
      · have e : tbl = tbl' := by
          have h' := List.mem_singleton.mp h
          injection h'
        rw [e, hsn, hpcvT, hcvT]
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨j, c, cty', -, -, -, he⟩ := hrevMem _ h
        exact nomatch he
      · exact nomatch List.mem_singleton.mp h

/-- **The new constants of a native block's install, read off the member check** (module
docstring). The inputs are those of `ctorOuts_of_member_named` and distinct names in the
prefix. -/
theorem nativeInstallOut_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {n : Nat} {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : L1.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env)
    (hndE : (env.consts.map (·.name)).Nodup) :
    ∃ (new : List (ConstantInfo .anon)) (p : Ix.Kernel.NativeParts .anon)
      (ty' : Ix.Kernel.Expr .anon) (ctorsA : List (ConstantVal .anon × Nat))
      (caps : IndCaps .anon),
      NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps := by
  obtain ⟨new, p, ty', ctorsA, caps, hO, -⟩ := nativeInstallOut_of_member_checked ht hS hst hrec
    hchk hnat htele hblk hp₀ hinv hstored hP hkeys hfresh hfree hcov haux hndE
  exact ⟨new, p, ty', ctorsA, caps, hO⟩

end IxVM.Refinement.Typing
