/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LocalOpening

/-!
# Substitution and let-type closing with local values

Registered values remain free in the kernel tree while their model indices
move below each syntactic binder. The actual memoized substitution and
singleton abstraction walkers preserve this reading. In particular, closing
an inferred let-body type and substituting the stored value preserves its
original reading and intern-table coherence. The residual abstraction is
derived from the body's reading, rather than supplied by the caller.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u
variable {β : Type u}

private theorem bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ intermediate, action = some intermediate ∧ next intermediate = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

private theorem depth_succ {depth : UInt64} (bound : depth.toNat + 1 < UInt64.size) :
    (depth + 1).toNat = depth.toNat + 1 := by
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt bound]

private theorem readLocalExpr?_let_parts {resolve : Address → Option (ConstRef β)}
    {values : LocalValues β} {name : Mode.anon.F Name} {domain value body : KExpr .anon}
    {nonDep : Bool} {info : ExprInfo .anon} {source : VExpr β} {depth : Nat}
    (reading : readLocalExpr? resolve values (.letE name domain value body nonDep info)
      depth = some source) :
    ∃ A v b, readLocalExpr? resolve values domain depth = some A ∧
      readLocalExpr? resolve values value depth = some v ∧
      readLocalExpr? resolve values body (depth + 1) = some b ∧ source = b.inst v := by
  rw [readLocalExpr?] at reading
  obtain ⟨A, domainReads, reading⟩ := bind_success reading
  obtain ⟨v, valueReads, reading⟩ := bind_success reading
  obtain ⟨b, bodyReads, reading⟩ := bind_success reading
  cases reading
  exact ⟨A, v, b, domainReads, valueReads, bodyReads, rfl⟩

/-- Lifting a term with no loose legacy variables shifts the reading of its
registered values beneath the new syntactic binders. -/
theorem readLocalExpr?_liftSpec
    {resolve : Address → Option (ConstRef β)} {values : LocalValues β}
    {term : KExpr .anon} {source : VExpr β} {depth shift : UInt64}
    (bound : depth.toNat + term.size < UInt64.size)
    (reading : readLocalExpr? resolve values term depth.toNat = some source) :
    readLocalExpr? resolve values (KExpr.liftSpec term shift depth)
      (depth.toNat + shift.toNat) = some (source.liftN shift.toNat depth.toNat) := by
  induction term generalizing source depth with
  | var index name info =>
      simp only [readLocalExpr?] at reading
      split at reading
      next inScope =>
        cases reading
        have below : ¬ index ≥ depth := by
          simp only [UInt64.le_iff_toNat_le]; omega
        simp [KExpr.liftSpec, below, readLocalExpr?, show index.toNat <
          depth.toNat + shift.toNat by omega, VExpr.liftN, liftVar, inScope]
      · contradiction
  | fvar id name info =>
      rw [readLocalExpr?] at reading
      obtain ⟨value, found, reading⟩ := Option.map_eq_some_iff.mp reading
      cases reading
      simp only [KExpr.liftSpec, readLocalExpr?, found, Option.map_some]
      congr 1
      exact (VExpr.liftN_combine (Nat.zero_le _) (by omega)).symm
  | sort _ _ | nat _ _ _ => cases reading; rfl
  | const id levels info =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      cases reading
      simp [KExpr.liftSpec, readLocalExpr?, resolved, VExpr.liftN]
  | str value _ _ =>
      rw [readString?_liftN reading]
      exact reading
  | letE name domain value body nonDep info hA hv hb =>
      obtain ⟨A, v, b, aReads, vReads, bReads, rfl⟩ := readLocalExpr?_let_parts reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyOut := hb (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next] using bReads)
      simp only [next] at bodyOut
      simp [KExpr.liftSpec, hA (by omega) aReads, hv (by omega) vReads,
        VExpr.liftN_inst_hi, show depth.toNat + shift.toNat + 1 =
          depth.toNat + 1 + shift.toNat by omega, bodyOut]
  | app fn arg info hf ha =>
      rw [readLocalExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := bind_success reading
      obtain ⟨a, aReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.liftSpec, hf (by omega) fReads, ha (by omega) aReads, VExpr.liftN]
  | lam name bi domain body info hd hb | all name bi domain body info hd hb =>
      rw [readLocalExpr?] at reading
      obtain ⟨A, domainReads, reading⟩ := bind_success reading
      obtain ⟨B, bodyReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyOut := hb (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next] using bodyReads)
      simp only [next] at bodyOut
      simp [KExpr.liftSpec, hd (by omega) domainReads, VExpr.liftN,
        show depth.toNat + shift.toNat + 1 = depth.toNat + 1 + shift.toNat by omega,
        bodyOut]
  | prj id index value info ih =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      obtain ⟨value, valueReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.liftSpec, resolved, ih (by omega) valueReads, VExpr.liftN]

/-- Removing one syntactic binder agrees with model substitution, including
arguments that contain registered values and their own nested binders. -/
theorem readLocalExpr?_substSpec
    {resolve : Address → Option (ConstRef β)} {values : LocalValues β}
    {body arg : KExpr .anon} {source argument : VExpr β} {depth : UInt64}
    (bound : depth.toNat + body.size + 1 < UInt64.size)
    (argBound : arg.size < UInt64.size)
    (bodyReads : readLocalExpr? resolve values body (depth.toNat + 1) = some source)
    (argReads : readLocalExpr? resolve values arg = some argument) :
    readLocalExpr? resolve values (KExpr.substSpec body arg depth) depth.toNat =
      some (source.inst argument depth.toNat) := by
  induction body generalizing source depth with
  | var index name info =>
      simp only [readLocalExpr?] at bodyReads
      split at bodyReads
      next inScope =>
        cases bodyReads
        by_cases equal : index = depth
        · subst index
          simp only [KExpr.substSpec, beq_self_eq_true, if_true, VExpr.inst, VExpr.instVar,
            Nat.lt_irrefl, if_false]
          simpa only [UInt64.toNat_zero, Nat.zero_add] using
            (readLocalExpr?_liftSpec (depth := 0) (shift := depth)
              (by simpa using argBound) argReads)
        · have smaller : index.toNat < depth.toNat := by
            have : index.toNat ≠ depth.toNat := fun h => equal (UInt64.toNat_inj.mp h)
            omega
          have below : ¬ index > depth := by
            simp only [UInt64.lt_iff_toNat_lt]; omega
          simp [KExpr.substSpec, equal, below, readLocalExpr?, smaller,
            VExpr.inst, VExpr.instVar]
      · contradiction
  | fvar id name info =>
      rw [readLocalExpr?] at bodyReads
      obtain ⟨value, found, bodyReads⟩ := Option.map_eq_some_iff.mp bodyReads
      cases bodyReads
      simp only [KExpr.substSpec, readLocalExpr?, found, Option.map_some]
      congr 1
      rw [← VExpr.liftN_combine (e := value.erase) (n₁ := depth.toNat) (n₂ := 1)
        (k₁ := 0) (k₂ := depth.toNat) (Nat.zero_le _) (by omega), VExpr.inst_liftN]
  | sort _ _ | nat _ _ _ => cases bodyReads; rfl
  | const id levels info =>
      rw [readLocalExpr?] at bodyReads
      obtain ⟨ref, resolved, bodyReads⟩ := bind_success bodyReads
      cases bodyReads
      simp [KExpr.substSpec, readLocalExpr?, resolved, VExpr.inst]
  | str value _ _ =>
      rw [readString?_inst bodyReads]
      exact bodyReads
  | letE name domain value body nonDep info hA hv hb =>
      obtain ⟨A, v, b, aReads, vReads, bReads, rfl⟩ := readLocalExpr?_let_parts bodyReads
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyOut := hb (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next] using bReads)
      simp only [next] at bodyOut
      simp [KExpr.substSpec, hA (by omega) aReads, hv (by omega) vReads,
        VExpr.inst0_inst_hi, bodyOut]
  | app fn value info hf ha =>
      rw [readLocalExpr?] at bodyReads
      obtain ⟨f, fReads, bodyReads⟩ := bind_success bodyReads
      obtain ⟨a, aReads, bodyReads⟩ := bind_success bodyReads
      cases bodyReads
      simp only [KExpr.size] at bound
      simp [KExpr.substSpec, hf (by omega) fReads, ha (by omega) aReads, VExpr.inst]
  | lam name bi domain body info hd hb | all name bi domain body info hd hb =>
      rw [readLocalExpr?] at bodyReads
      obtain ⟨A, domainReads, bodyReads⟩ := bind_success bodyReads
      obtain ⟨B, innerReads, reading⟩ := bind_success bodyReads
      cases reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyOut := hb (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next] using innerReads)
      simp only [next] at bodyOut
      simp [KExpr.substSpec, hd (by omega) domainReads, bodyOut, VExpr.inst]
  | prj id index value info ih =>
      rw [readLocalExpr?] at bodyReads
      obtain ⟨ref, resolved, bodyReads⟩ := bind_success bodyReads
      obtain ⟨value, valueReads, bodyReads⟩ := bind_success bodyReads
      cases bodyReads
      simp only [KExpr.size] at bound
      simp [KExpr.substSpec, resolved, ih (by omega) valueReads, VExpr.inst]

/-- The actual memoized, interned walker inherits the structural substitution
reading under finite collision freedom and bounds excluding index overflow. -/
theorem subst_readLocalExpr?
    {resolve : Address → Option (ConstRef β)} {values : LocalValues β}
    {body arg : KExpr .anon} {source argument : VExpr β} {table : InternTable .anon}
    (bodyConstructed : body.Constructed) (argConstructed : arg.Constructed)
    (bodyBound : body.size + 1 < UInt64.size) (argBound : arg.size < UInt64.size)
    (coherent : table.WF)
    (faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
      KExpr.SubstReach arg body 0 term)
    (bodyReads : readLocalExpr? resolve values body 1 = some source)
    (argReads : readLocalExpr? resolve values arg = some argument) :
    readLocalExpr? resolve values (subst body arg 0 table).1 = some (source.inst argument) ∧
      (subst body arg 0 table).2.WF := by
  obtain ⟨result, coherent, _⟩ := subst_spec faithful bodyConstructed argConstructed
    (by simpa using (show body.size < UInt64.size by omega)) argBound
    (fun _ h => Or.inr h) coherent (fun _ h => Or.inl h)
  refine ⟨?_, coherent⟩
  rw [result]
  exact readLocalExpr?_substSpec (depth := 0) (by simpa using bodyBound)
    argBound bodyReads argReads

private local instance : LawfulBEq FVarId where
  eq_of_beq := by
    intro left right equal
    cases left
    cases right
    congr 1
    exact eq_of_beq equal
  rfl {a} := by
    cases a with
    | mk x => show (x == x) = true; exact beq_self_eq_true x

@[simp] private theorem readLocalExpr?_mkVar (resolve : Address → Option (ConstRef β))
    (values : LocalValues β) (index : UInt64) (name : Mode.anon.F Name) (depth : Nat) :
    readLocalExpr? resolve values (KExpr.mkVar index name) depth =
      if index.toNat < depth then some (.bvar index.toNat) else none := rfl

theorem readLocalExpr?_abstractFVarsSpec
    {resolve : Address → Option (ConstRef β)} {values : LocalValues β}
    {body : KExpr .anon} {source : VExpr β} {depth : UInt64} {fresh : FVarId}
    (bound : depth.toNat + body.size + 1 < UInt64.size)
    (reading : readLocalExpr? resolve (values.pushBinder fresh) body depth.toNat = some source) :
    readLocalExpr? resolve values
      (KExpr.abstractFVarsSpec body ((∅ : Std.HashMap FVarId UInt64).insert fresh 0)
        1 depth) (depth.toNat + 1) = some source := by
  induction body generalizing source depth with
  | var index name info =>
      simp only [readLocalExpr?] at reading
      split at reading
      next inScope =>
        cases reading
        have before : ¬ index ≥ depth := by
          simp only [UInt64.le_iff_toNat_le]; omega
        simp [KExpr.abstractFVarsSpec, before, readLocalExpr?, show index.toNat <
          depth.toNat + 1 by omega]
      · contradiction
  | fvar id name info =>
      by_cases equal : id = fresh
      · subst id
        simp [readLocalExpr?, LocalValues.pushBinder, AExpr.erase, VExpr.liftN, liftVar] at reading
        cases reading
        simp [KExpr.abstractFVarsSpec]
      · simp only [readLocalExpr?, LocalValues.pushBinder, equal, if_false, Option.map_map] at reading
        obtain ⟨value, found, reading⟩ := Option.map_eq_some_iff.mp reading
        cases reading
        have combined : (value.erase.liftN 1).liftN depth.toNat =
            value.erase.liftN (depth.toNat + 1) := by
          rw [VExpr.liftN_combine (Nat.zero_le 0) (Nat.zero_le 1), Nat.add_comm]
        simp [KExpr.abstractFVarsSpec, Ne.symm equal,
          readLocalExpr?, found, AExpr.erase_liftN, combined]
  | sort _ _ | const _ _ _ | nat _ _ _ | str _ _ _ => exact reading
  | letE name domain value body nonDep info hA hv hb =>
      obtain ⟨A, v, b, aReads, vReads, bReads, rfl⟩ := readLocalExpr?_let_parts reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyOut := hb (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next] using bReads)
      simp only [next] at bodyOut
      simp [KExpr.abstractFVarsSpec, hA (by omega) aReads,
        hv (by omega) vReads, bodyOut]
  | app fn arg info hf ha =>
      rw [readLocalExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := bind_success reading
      obtain ⟨a, aReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.abstractFVarsSpec,
        hf (by omega) fReads, ha (by omega) aReads]
  | lam name bi domain body info hd hb | all name bi domain body info hd hb =>
      rw [readLocalExpr?] at reading
      obtain ⟨A, domainReads, reading⟩ := bind_success reading
      obtain ⟨B, bodyReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyBound : (depth + 1).toNat + body.size + 1 < UInt64.size := by
        rw [next]; omega
      have bodyReads' : readLocalExpr? resolve (values.pushBinder fresh) body (depth + 1).toNat =
          some B := by simpa only [next] using bodyReads
      have bodyOut : readLocalExpr? resolve values
          (KExpr.abstractFVarsSpec body ((∅ : Std.HashMap FVarId UInt64).insert fresh 0)
            1 (depth + 1)) (depth.toNat + 1 + 1) = some B := by
        simpa only [next] using hb bodyBound bodyReads'
      simp [KExpr.abstractFVarsSpec, hd (by omega) domainReads, bodyOut]
  | prj id index value info ih =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      obtain ⟨value, valueReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.abstractFVarsSpec, resolved,
        ih (by omega) valueReads]
theorem abstractFVars_readLocalExpr?
    {resolve : Address → Option (ConstRef β)} {values : LocalValues β}
    {body : KExpr .anon} {fresh : FVarId} {source : VExpr β}
    {table : InternTable .anon}
    (constructed : body.Constructed) (bound : body.size + 1 < UInt64.size)
    (coherent : table.WF)
    (faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
      KExpr.AbstractReach ((∅ : Std.HashMap FVarId UInt64).insert fresh 0) 1 body 0 term)
    (reading : readLocalExpr? resolve (values.pushBinder fresh) body = some source) :
    readLocalExpr? resolve values (abstractFVars body #[fresh] table).1 1 = some source ∧
      (abstractFVars body #[fresh] table).2.WF := by
  obtain ⟨result, coherent⟩ := abstractFVars_singleton_spec constructed (by omega)
    faithful coherent (fun _ => Or.inl) (fun _ => Or.inr)
  refine ⟨?_, coherent⟩
  rw [result]
  exact readLocalExpr?_abstractFVarsSpec (by simpa using bound) reading

theorem readLocalExpr?_readable {resolve : Address → Option (ConstRef β)}
    {values more : LocalValues β} {term : KExpr .anon} {depth : Nat} {source : VExpr β}
    (coverage : ∀ id value, values id = some value → ∃ value', more id = some value')
    (reading : readLocalExpr? resolve values term depth = some source) :
    ∃ source', readLocalExpr? resolve more term depth = some source' := by
  induction term generalizing source depth with
  | fvar id name info =>
      obtain ⟨value, found, _⟩ := Option.map_eq_some_iff.mp reading
      obtain ⟨value', found'⟩ := coverage _ _ found
      exact ⟨value'.erase.liftN depth, by simp [readLocalExpr?, found']⟩
  | var _ _ _ | sort _ _ | const _ _ _ | nat _ _ _ | str _ _ _ => exact ⟨source, reading⟩
  | app fn arg info hf ha | lam _ _ fn arg info hf ha | all _ _ fn arg info hf ha =>
      rw [readLocalExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := bind_success reading
      obtain ⟨a, aReads, _⟩ := bind_success reading
      obtain ⟨f', fReads'⟩ := hf fReads
      obtain ⟨a', aReads'⟩ := ha aReads
      simp [readLocalExpr?, fReads', aReads']
  | prj id index value info ih =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      obtain ⟨value, valueReads, _⟩ := bind_success reading
      obtain ⟨value', valueReads'⟩ := ih valueReads
      simp [readLocalExpr?, resolved, valueReads']
  | letE name domain value body nonDep info hA hv hb =>
      obtain ⟨A, v, b, aReads, vReads, bReads, _⟩ := readLocalExpr?_let_parts reading
      obtain ⟨A', aReads'⟩ := hA aReads
      obtain ⟨v', vReads'⟩ := hv vReads
      obtain ⟨b', bReads'⟩ := hb bReads
      simp [readLocalExpr?, aReads', vReads', bReads']

theorem readLocalExpr?_instantiateLocal {resolve : Address → Option (ConstRef β)}
    {values : LocalValues β} {fresh : FVarId} {value : AExpr β}
    {term : KExpr .anon} {depth : Nat} {source : VExpr β}
    (reading : readLocalExpr? resolve (values.pushBinder fresh) term depth = some source) :
    readLocalExpr? resolve (values.pushLet fresh value) term depth =
      some (source.inst value.erase depth) := by
  induction term generalizing source depth with
  | var index name info =>
      simp only [readLocalExpr?] at reading ⊢
      split at reading
      next bound =>
        cases reading
        simp [bound, VExpr.inst, VExpr.instVar]
      · contradiction
  | fvar id name info =>
      by_cases equal : id = fresh
      · subst id
        simp [readLocalExpr?, LocalValues.pushBinder, AExpr.erase, VExpr.liftN, liftVar] at reading
        cases reading
        simp [readLocalExpr?, LocalValues.pushLet, VExpr.inst, VExpr.instVar]
      · simp only [readLocalExpr?, LocalValues.pushBinder, equal, if_false, Option.map_map] at reading
        obtain ⟨previous, found, reading⟩ := Option.map_eq_some_iff.mp reading
        cases reading
        simp only [readLocalExpr?, LocalValues.pushLet, equal, if_false,
          found, Option.map_some, Function.comp_def, AExpr.erase_liftN]
        congr 1
        rw [VExpr.liftN_combine (Nat.zero_le 0) (Nat.zero_le 1), Nat.add_comm 1 depth,
          ← VExpr.liftN_combine (e := previous.erase) (n₁ := depth) (n₂ := 1)
            (k₁ := 0) (k₂ := depth) (Nat.zero_le _) (by omega), VExpr.inst_liftN]
  | sort _ _ | nat _ _ _ => cases reading; rfl
  | const id levels info =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      cases reading
      simp [readLocalExpr?, resolved, VExpr.inst]
  | str value name info =>
      rw [readString?_inst reading]
      exact reading
  | app fn arg info hf ha | lam _ _ fn arg info hf ha | all _ _ fn arg info hf ha =>
      rw [readLocalExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := bind_success reading
      obtain ⟨a, aReads, reading⟩ := bind_success reading
      cases reading
      simp [readLocalExpr?, hf fReads, ha aReads, VExpr.inst]
  | prj id index value info ih =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      obtain ⟨value, valueReads, reading⟩ := bind_success reading
      cases reading
      simp [readLocalExpr?, resolved, ih valueReads, VExpr.inst]
  | letE name domain value body nonDep info hA hv hb =>
      obtain ⟨A, v, b, aReads, vReads, bReads, rfl⟩ := readLocalExpr?_let_parts reading
      simp [readLocalExpr?, hA aReads, hv vReads, hb bReads, VExpr.inst0_inst_hi]

theorem readLocalExpr?_letResidual {resolve : Address → Option (ConstRef β)}
    {values : LocalValues β} {fresh : FVarId} {value : AExpr β}
    {term : KExpr .anon} {depth : Nat} {source : VExpr β}
    (reading : readLocalExpr? resolve (values.pushLet fresh value) term depth = some source) :
    ∃ residual, readLocalExpr? resolve (values.pushBinder fresh) term depth = some residual ∧
      source = residual.inst value.erase depth := by
  have coverage : ∀ id v, values.pushLet fresh value id = some v →
      ∃ v', values.pushBinder fresh id = some v' := by
    intro id v hit
    by_cases equal : id = fresh
    · subst id; simp [LocalValues.pushBinder]
    · simp only [LocalValues.pushLet, equal, if_false] at hit
      simp [LocalValues.pushBinder, equal, hit]
  obtain ⟨residual, readResidual⟩ := readLocalExpr?_readable coverage reading
  have instantiated := readLocalExpr?_instantiateLocal (value := value) readResidual
  exact ⟨residual, readResidual, Option.some.inj (reading.symm.trans instantiated)⟩

theorem _root_.Ix.Kernel.KExpr.abstractFVarsSpec_size
    (body : KExpr .anon) (pos : Std.HashMap FVarId UInt64)
    (count depth : UInt64) :
    (KExpr.abstractFVarsSpec body pos count depth).size = body.size := by
  open KExpr in
  induction body generalizing depth with
  | var index name info =>
      simp only [abstractFVarsSpec]
      split <;> rfl
  | fvar id name info =>
      simp only [abstractFVarsSpec]
      split <;> rfl
  | app fn arg info hf ha =>
      change (abstractFVarsSpec fn pos count depth).size +
        (abstractFVarsSpec arg pos count depth).size + 1 = _
      rw [hf, ha]; rfl
  | lam name bi domain body info hA hb | all name bi domain body info hA hb =>
      change (abstractFVarsSpec domain pos count depth).size +
        (abstractFVarsSpec body pos count (depth + 1)).size + 1 = _
      rw [hA, hb]; rfl
  | letE name domain value body nonDep info hA hv hb =>
      change (abstractFVarsSpec domain pos count depth).size +
        (abstractFVarsSpec value pos count depth).size +
        (abstractFVarsSpec body pos count (depth + 1)).size + 1 = _
      rw [hA, hv, hb]; rfl
  | prj id index value info ih =>
      change (abstractFVarsSpec value pos count depth).size + 1 = _
      rw [ih]; rfl
  | sort _ _ | const _ _ _ | nat _ _ _ | str _ _ _ => rfl

theorem closeLetType_readLocalExpr?
    {resolve : Address → Option (ConstRef β)} {values : LocalValues β}
    {body value : KExpr .anon} {fresh : FVarId} {e : AExpr β} {source : VExpr β}
    {table : InternTable .anon}
    (constructed : body.Constructed) (valueConstructed : value.Constructed)
    (bound : body.lbr.toNat + body.size + 1 < UInt64.size)
    (valueBound : value.size < UInt64.size) (coherent : table.WF)
    (abstractFaithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
      KExpr.AbstractReach ((∅ : Std.HashMap FVarId UInt64).insert fresh 0) 1 body 0 term)
    (substFaithful :
      let abstracted := abstractFVars body #[fresh] table
      KExpr.CollisionFree fun term => abstracted.2.ExprSupport term ∨
        KExpr.SubstReach value abstracted.1 0 term)
    (reading : readLocalExpr? resolve (values.pushLet fresh e) body = some source)
    (valueReads : readLocalExpr? resolve values value = some e.erase) :
    let abstracted := abstractFVars body #[fresh] table
    let result := subst abstracted.1 value 0 abstracted.2
    readLocalExpr? resolve values result.1 = some source ∧ result.2.WF := by
  obtain ⟨residual, residualReads, rfl⟩ := readLocalExpr?_letResidual reading
  have spec := (abstractFVars_singleton_spec constructed (by omega)
    abstractFaithful coherent (fun _ => Or.inl) (fun _ => Or.inr)).1
  have readClosed := abstractFVars_readLocalExpr? constructed (by omega)
    coherent abstractFaithful residualReads
  have closedConstructed : (abstractFVars body #[fresh] table).1.Constructed := by
    rw [spec]
    apply constructed.abstractFVarsSpec
    · intro id position found
      simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty] at found
      split at found
      · cases found; decide
      · contradiction
    · simpa using bound
  have closedBound : (abstractFVars body #[fresh] table).1.size + 1 < UInt64.size := by
    rw [spec, KExpr.abstractFVarsSpec_size]
    omega
  exact subst_readLocalExpr? closedConstructed valueConstructed closedBound
    valueBound readClosed.2 substFaithful readClosed.1 valueReads

end Ix.Kernel.Consistency
