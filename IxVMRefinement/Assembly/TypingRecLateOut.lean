import IxVMRefinement.Assembly.TypingRecLateStep
import IxVMRefinement.Assembly.TypingRecLateStored
import IxVMRefinement.StatementRel.LoadedReadsCanonRec

/-! # The late recursor step's output, from its parts

`RecLateOut t E₀ E A env fam` (the late relation with the recursor in front, the recursor at the
record's key, the record's reading, the recursor stored as read, and its reload) from:
* the reading of the record (`ty`, `rules`, their scoping), its canonical annotation (`tyC`,
  `rlsC`: `LoadedReads.canonAnn`/`canonRules`, which every load of the record represents);
* the conjuncts of `DeclNativeRecLateRunJ` at `pR := fam.recParts ⟨keyOf t A, ps, ty⟩ elim large
  (rules.map rhs)`: the pins, `NativeFamStored`, the elimination restriction, the field sorts,
  and `NativeRecJ` with the canonical recursor `⟨keyOf t A, ps, tyC⟩` and rules `rlsC.map rhs`;
* the K bit of the stored rule (`rec_k_stored_of_arm`'s form), the family's parameter count the
  record's, and `Reads t E₀ A` of the reading.

The stored recursor is `.recInfo ⟨keyOf t A, ps, tyC⟩ mI rP (sumRules …)`: `StoredAs` against the
reading by the annotations (`RuleStored rlsC rules`) and the pins; its reload is the canonical
constant's (`LoadedReads.reloadsAs_recr_cons`) moved to the stored rules
(`reloadsAs_recr_rules`: same field counts and right-hand sides, the K rule's bit from the
stored family).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal RecRule LevelParam)
open Ix.Kernel.Semantics (NativeFam NativeFamStored DeclNativeRecLateRunJ NativeRecJ FieldSortsJ)
open Ix.Kernel.Model (rulesJ)

/-! ## Lists -/

/-- Pointwise facts at every common index of two lists of one length are a `Forall₂`. -/
theorem forall₂_of_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ (j : Nat) (a : α) (b : β), l₁[j]? = some a → l₂[j]? = some b → R a b) →
      List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: as, b :: bs, hl, h =>
    .cons (h 0 a b rfl rfl)
      (forall₂_of_getElem? (by simpa using hl) (fun j a' b' ha hb => h (j + 1) a' b' ha hb))

/-- The canonical rules carry the record's K flag and parameter count, and the reading's
constructors and field counts. -/
theorem canonRules_fields {src : Ixon.Constant} {ps : List LevelParam} {kFlag : Bool}
    {cParams : Nat} :
    ∀ {root : F} {rus : List Ixon.RecursorRule} {rules rls : List (RecRule .anon)},
      LoadedReads.canonRules src ps kFlag cParams root rus rules = some rls →
      List.Forall₂ (fun rl r => r.k = kFlag ∧ r.ctorParams = cParams ∧ r.nfields = rl.nfields)
        rules rls
  | _, [], [], rls, h => by
    simp only [LoadedReads.canonRules, Option.some.injEq] at h
    subst h
    exact .nil
  | _, [], _ :: _, _, h => by simp [LoadedReads.canonRules] at h
  | _, _ :: _, [], _, h => by simp [LoadedReads.canonRules] at h
  | root, ru :: rus, rl :: rules, rls, h => by
    simp only [LoadedReads.canonRules] at h
    cases hA : LoadedReads.canonAnn src ps root ru.rhs rl.rhs with
    | none => rw [hA] at h; cases h
    | some rhs' =>
      rw [hA] at h
      cases hR : LoadedReads.canonRules src ps kFlag cParams (root + 1) rus rules with
      | none => rw [hR] at h; cases h
      | some rest =>
        rw [hR] at h
        simp at h
        subst h
        exact .cons ⟨rfl, rfl, rfl⟩ (canonRules_fields hR)

/-- The stored rules are stored as the read rules: same constructors and field counts (the
pins), right-hand sides annotating the reading's. -/
theorem sumRules_ruleStored {find? : Ix.Kernel.Key .anon → Option (ConstantInfo .anon)}
    {recName : Ix.Kernel.Key .anon} {nP mI rP : Nat} {recTy : Ix.Kernel.Expr .anon} :
    ∀ {ctorsA : List (ConstantVal .anon × Nat)} {rlsC rules : List (RecRule .anon)},
      List.Forall₂ (fun cA r => r.ctor = cA.1.name ∧ r.nfields = cA.2) ctorsA rules →
      List.Forall₂ RuleStored rlsC rules →
      List.Forall₂ RuleStored
        (Ix.Kernel.sumRules find? recName nP mI rP recTy ctorsA (rlsC.map (·.rhs))) rules
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hp hps, .cons hs hss => by
    simp only [List.map_cons, Ix.Kernel.sumRules]
    exact .cons ⟨by rw [Ix.Kernel.recRuleBits_ctor]; exact hp.1.symm, hp.2.symm,
      by rw [Ix.Kernel.recRuleBits_rhs]; exact hs.2.2⟩ (sumRules_ruleStored hps hss)

/-- The stored rules have the canonical rules' field counts and right-hand sides. -/
theorem sumRules_agree {find? : Ix.Kernel.Key .anon → Option (ConstantInfo .anon)}
    {recName : Ix.Kernel.Key .anon} {nP mI rP : Nat} {recTy : Ix.Kernel.Expr .anon} :
    ∀ {ctorsA : List (ConstantVal .anon × Nat)} {rlsC rules : List (RecRule .anon)},
      List.Forall₂ (fun cA r => r.ctor = cA.1.name ∧ r.nfields = cA.2) ctorsA rules →
      List.Forall₂ RuleStored rlsC rules →
      List.Forall₂ (fun rl rl' : RecRule .anon => rl'.nfields = rl.nfields ∧ rl'.rhs = rl.rhs)
        rlsC (Ix.Kernel.sumRules find? recName nP mI rP recTy ctorsA (rlsC.map (·.rhs)))
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hp hps, .cons hs hss => by
    simp only [List.map_cons, Ix.Kernel.sumRules]
    exact .cons ⟨hp.2.symm.trans hs.2.1.symm, rfl⟩ (sumRules_agree hps hss)

/-- The positions behind the elimination parameter are a permutation of the positions. -/
theorem recLps_perm (large : Bool) (k : Nat) :
    (Ix.Kernel.Reader.recLps large (List.range k)).Perm
      (List.range (Ix.Kernel.Reader.recLps large (List.range k)).length) := by
  cases large with
  | false =>
    show (List.range k).Perm (List.range (List.range k).length)
    simp only [List.length_range, List.Perm.refl]
  | true =>
    show ((List.range k).length :: List.range k).Perm
      (List.range ((List.range k).length :: List.range k).length)
    rw [List.length_cons, List.length_range, List.range_succ]
    exact (List.perm_append_singleton k (List.range k)).symm

/-! ## The output -/

/-- The single stored rule of a one-constructor family carries the stored K bit and the
family's parameter count. -/
theorem sumRules_single {find? : Ix.Kernel.Key .anon → Option (ConstantInfo .anon)}
    {recName : Ix.Kernel.Key .anon} {nP mI rP : Nat} {recTy : Ix.Kernel.Expr .anon}
    {cA : ConstantVal .anon × Nat} {rhss : List (Ix.Kernel.Expr .anon)} {rl' : RecRule .anon}
    (hS : Ix.Kernel.sumRules find? recName nP mI rP recTy [cA] rhss = [rl'])
    (hK : Ix.Kernel.recRuleKOf find? cA.1.name = true) :
    rl'.k = true ∧ rl'.ctorParams = nP := by
  cases rhss with
  | nil => simp [Ix.Kernel.sumRules] at hS
  | cons rhs rest =>
    simp only [Ix.Kernel.sumRules] at hS
    injection hS with h1 _
    rw [← h1]
    exact ⟨hK, rfl⟩

/-- A single canonical rule carries the record's K flag and parameter count. -/
theorem canonRules_single {src : Ixon.Constant} {ps : List LevelParam} {kFlag : Bool}
    {cParams : Nat} {root : F} {rus : List Ixon.RecursorRule} {rules : List (RecRule .anon)}
    {rl : RecRule .anon}
    (h : LoadedReads.canonRules src ps kFlag cParams root rus rules = some [rl]) :
    rl.k = kFlag ∧ rl.ctorParams = cParams := by
  have hf := canonRules_fields h
  obtain ⟨r, hr⟩ : ∃ r, rules = [r] := List.length_eq_one_iff.mp (by simpa using hf.length_eq)
  rw [hr] at hf
  obtain ⟨h1, h2, -⟩ := (List.forall₂_cons.mp hf).1
  exact ⟨h1, h2⟩

/-- **`RecLateOut` from its parts** (module docstring). -/
theorem rec_lateOut_of_parts {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {A : _root_.Address}
    {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hcE : recordOf E A = some c) (hinfo : c.info = .recr rc)
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → E.blobs.get? x = some b)
    (hstored : Decl.UsedRefsStored t env c)
    {k : Nat} {large : Bool} {elim : LevelParam}
    {ty tyC : Ix.Kernel.Expr .anon} {rules rlsC : List (RecRule .anon)}
    (hlen : (Ix.Kernel.Reader.recLps large (List.range k)).length = rc.lvls.toNat)
    (hty : (exprReader t (fun x => E₀.blobs.get? x) c
      (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps large (List.range k)))
      (soloSelf t A)).read rc.typ = .ok ty)
    (hty_lbb : ty.looseBVarsBounded 0 = true)
    (hty_def : ty.allLevelParamsDefined (Ix.Kernel.Reader.recLps large (List.range k)) = true)
    (hrd : List.Forall₂ (fun ru rl₀ => rl₀.nfields = ru.fields.toNat ∧
      (exprReader t (fun x => E₀.blobs.get? x) c
        (Ix.Kernel.Reader.recParam (Ix.Kernel.Reader.recLps large (List.range k)))
        (soloSelf t A)).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧
      rl₀.rhs.allLevelParamsDefined (Ix.Kernel.Reader.recLps large (List.range k)) = true)
      rc.rules.toList rules)
    (hcT : LoadedReads.canonAnn c (Ix.Kernel.Reader.recLps large (List.range k)) 0 rc.typ ty =
      some tyC)
    (hcR : LoadedReads.canonRules c (Ix.Kernel.Reader.recLps large (List.range k)) rc.k
      rc.params.toNat (0 + 1) rc.rules.toList rules = some rlsC)
    (hannT : Annotates tyC ty) (hrs : List.Forall₂ RuleStored rlsC rules)
    (hmI : rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat =
      (fam.recParts ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ elim large
        (rules.map (·.rhs))).majorIdx)
    (hrP : rc.params.toNat + rc.motives.toNat + rc.minors.toNat =
      (fam.recParts ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ elim large
        (rules.map (·.rhs))).rulePrefix)
    (hrlen : rules.length = fam.ctorsA.length)
    (hpins : ∀ (j : Nat) (r : RecRule .anon) (cA : ConstantVal .anon × Nat), rules[j]? = some r →
      fam.ctorsA[j]? = some cA → r.ctor = cA.1.name ∧ r.nfields = cA.2)
    (hfam : NativeFamStored env fam)
    (helim : large = true →
      (∀ φ : LevelParam → Nat, Ix.Kernel.Level.eval φ fam.p.resSort ≠ 0) ∨
        fam.ctorsA.length < 2)
    (hfs : large = true → fam.p.isProp = true →
      ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
        ∃ (fvsP : List (Ix.Kernel.Expr .anon)) (crest : Ix.Kernel.Expr .anon)
          (xFvs : List (Ix.Kernel.Expr .anon)) (xrest : Ix.Kernel.Expr .anon)
          (sorts : List Ix.Kernel.Level),
          Ix.Kernel.openPisAtFvars fam.p.nP cA.1.type 0 = some (fvsP, crest) ∧
          Ix.Kernel.openPisAtFvars cA.2 crest fam.p.nP = some (xFvs, xrest) ∧
          FieldSortsJ rulesJ env true true fam.p.resSort fam.p.nP xFvs
            (xrest.getAppArgs.drop fam.p.nP) cA.2 sorts)
    (hnatJ : NativeRecJ rulesJ env
      (fam.recParts ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ elim large
        (rules.map (·.rhs)))
      fam.cvTa fam.ctorsA ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), tyC⟩
      (rlsC.map (·.rhs)))
    (hK : rc.k = true → rc.rules.size = 1 ∧
      ∃ cA, fam.ctorsA = [cA] ∧ Ix.Kernel.recRuleKOf env.find? cA.1.name = true)
    (hnP : fam.p.nP = rc.params.toNat)
    (hreads : Reads t E₀ A (.recInfo ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules)) :
    RecLateOut t E₀ E A env fam := by
  have hpinsF : List.Forall₂ (fun cA r => r.ctor = cA.1.name ∧ r.nfields = cA.2) fam.ctorsA
      rules :=
    forall₂_of_getElem? hrlen.symm (fun j cA r hcA hr => hpins j r cA hr hcA)
  have hrun : DeclNativeRecLateRunJ rulesJ env fam
      ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules
      ⟨.recInfo ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), tyC⟩
        (fam.recParts ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ elim large
          (rules.map (·.rhs))).majorIdx
        (fam.recParts ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ elim large
          (rules.map (·.rhs))).rulePrefix
        (Ix.Kernel.sumRules env.find? (keyOf t A)
          (fam.recParts ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ elim large
            (rules.map (·.rhs))).nP
          (fam.recParts ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ elim large
            (rules.map (·.rhs))).majorIdx
          (fam.recParts ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ elim large
            (rules.map (·.rhs))).rulePrefix
          tyC fam.ctorsA (rlsC.map (·.rhs))) :: env.consts⟩ :=
    ⟨elim, large, _, _, _, rfl, hmI, hrP, hrlen, hpins, hfam, helim, hfs, hnatJ, rfl⟩
  -- the stored recursor, with the record's counts
  rw [← hmI, ← hrP] at hrun
  have hnPR : (fam.recParts ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), ty⟩ elim
      large (rules.map (·.rhs))).nP = rc.params.toNat := hnP
  rw [hnPR] at hrun
  -- the reload: the canonical constant's, moved to the stored rules
  have hcn := LoadedReads.canonRec_eq (key := keyOf t A) hcT hcR
  have hreC := LoadedReads.reloadsAs_recr_cons ht hcE hinfo hblobs hlen (recLps_perm large k)
    hty hty_lbb hty_def hrd (fun hk => (hK hk).1) hstored hcn
  have hkrule : ∀ rl rl', rlsC = [rl] →
      Ix.Kernel.sumRules env.find? (keyOf t A) rc.params.toNat
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) tyC fam.ctorsA
        (rlsC.map (·.rhs)) = [rl'] → rl.k = true →
      rl'.k = true ∧ rl'.ctorParams = rl.ctorParams := by
    intro rl rl' hC hS hk
    rw [hC] at hcR
    obtain ⟨hk1, hcp1⟩ := canonRules_single hcR
    rw [hk1] at hk
    obtain ⟨-, cA, hA, hKA⟩ := hK hk
    rw [hA] at hS
    obtain ⟨hk2, hcp2⟩ := sumRules_single hS hKA
    exact ⟨hk2, hcp2.trans hcp1.symm⟩
  have hre := reloadsAs_recr_rules (env₂ := ⟨.recInfo
      ⟨keyOf t A, Ix.Kernel.Reader.recLps large (List.range k), tyC⟩
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat)
      (Ix.Kernel.sumRules env.find? (keyOf t A) rc.params.toNat
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) tyC fam.ctorsA
        (rlsC.map (·.rhs))) :: env.consts⟩)
    hreC (find_isSome_cons_congr rfl) (sumRules_agree hpinsF hrs) hkrule
  exact ⟨_, _, _, rules, _, _, hrun, rfl, hreads,
    ⟨⟨rfl, rfl, hannT⟩, rfl, rfl, sumRules_ruleStored hpinsF hrs⟩, hre⟩

end IxVM.Refinement.Typing
