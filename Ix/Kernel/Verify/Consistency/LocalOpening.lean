/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LocalValues

/-!
# Opening binders with value-aware local readings

The production opening walker replaces a syntactic variable with an interned
fresh local. For a let, reading the result substitutes that local's stored
value. For a regular binder, reading preserves the body in the extended model
context. These facts cover every expression constructor, including nested
lets, projections and the canonical string expansion.

The operational theorems use the existing finite interning/walker support:
constructed source data, bounded machine indices and collision freedom on
exactly the table and reachable terms. They also preserve the local-context
invariant and the actual resulting intern table.
-/


namespace Ix.Kernel.Consistency
open Theory Theory.Model
universe u v
variable {β : Type u}

private theorem bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ value, action = some value ∧ next value = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

private theorem depth_succ {depth : UInt64} (bound : depth.toNat + 1 < UInt64.size) :
    (depth + 1).toNat = depth.toNat + 1 := by
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt bound]

private theorem inst_lift_above (source : VExpr β) (depth : Nat) :
    (source.liftN 1 (depth + 1)).inst (.bvar 0) depth = source := by
  induction source generalizing depth with
  | bvar index =>
      simp only [VExpr.liftN, VExpr.inst, liftVar, VExpr.instVar]
      split <;> split <;> (try split) <;>
        simp_all <;> omega
  | _ => simp_all [VExpr.liftN, VExpr.inst]

theorem readLocalExpr?_instantiateLetSpec
    {resolve : Address → Option (ConstRef β)} {values : LocalValues β}
    {body : KExpr .anon} {source : VExpr β} {value : AExpr β}
    {depth : UInt64} {fresh : FVarId}
    (absent : values fresh = none)
    (bound : depth.toNat + body.size + 1 < UInt64.size)
    (reading : readLocalExpr? resolve values body (depth.toNat + 1) = some source) :
    readLocalExpr? resolve (values.pushLet fresh value)
      (KExpr.instantiateRevSpec body #[KExpr.mkFVar fresh ()] depth) depth.toNat =
        some (source.inst value.erase depth.toNat) := by
  induction body generalizing source depth with
  | var index name info =>
      simp only [readLocalExpr?] at reading
      split at reading
      next inScope =>
        cases reading
        have next := depth_succ (depth := depth) (by simp only [KExpr.size] at bound; omega)
        by_cases equal : index = depth
        · subst index
          simp [KExpr.instantiateRevSpec, UInt64.lt_iff_toNat_lt, next,
            LocalValues.pushLet, VExpr.inst, VExpr.instVar]
        · have smaller : index.toNat < depth.toNat := by
            have : index.toNat ≠ depth.toNat := fun h => equal (UInt64.toNat_inj.mp h)
            omega
          have before : ¬ index ≥ depth := by simp only [UInt64.le_iff_toNat_le]; omega
          have beforeNext : ¬ index ≥ depth + 1 := by
            simp only [UInt64.le_iff_toNat_le, next]; omega
          simp [KExpr.instantiateRevSpec, before, beforeNext, readLocalExpr?, smaller,
            VExpr.inst, VExpr.instVar]
      · contradiction
  | fvar id name info =>
      obtain ⟨localValue, found, rfl⟩ := Option.map_eq_some_iff.mp reading
      have out := LocalValues.pushLet_extends absent value id localValue found
      simp only [KExpr.instantiateRevSpec, readLocalExpr?, out, Option.map_some]
      congr 1
      rw [← VExpr.liftN_combine (e := localValue.erase) (n₁ := depth.toNat) (n₂ := 1)
        (k₁ := 0) (k₂ := depth.toNat) (Nat.zero_le _) (by omega), VExpr.inst_liftN]
  | sort _ _ | nat _ _ _ => cases reading; rfl
  | const id levels info =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      cases reading
      simp [KExpr.instantiateRevSpec, readLocalExpr?, resolved, VExpr.inst]
  | str value name info =>
      rw [readString?_inst reading]
      exact reading
  | letE name domain value body nonDep info hA hv hb =>
      rw [readLocalExpr?] at reading
      obtain ⟨A, aReads, reading⟩ := bind_success reading
      obtain ⟨v, vReads, reading⟩ := bind_success reading
      obtain ⟨b, bReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyOut := hb (depth := depth + 1) (by rw [next]; omega)
        (by simpa only [next] using bReads)
      simp only [next] at bodyOut
      simp [KExpr.instantiateRevSpec, hA (by omega) aReads,
        hv (by omega) vReads, bodyOut, VExpr.inst0_inst_hi]
  | app fn arg info hf ha =>
      rw [readLocalExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := bind_success reading
      obtain ⟨a, aReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.instantiateRevSpec, VExpr.inst,
        hf (by omega) fReads, ha (by omega) aReads]
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
      simp [KExpr.instantiateRevSpec, VExpr.inst,
        hd (by omega) domainReads, bodyOut]
  | prj id index value info ih =>
      rw [readLocalExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      obtain ⟨value, valueReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.instantiateRevSpec, VExpr.inst, resolved,
        ih (by omega) valueReads]

theorem readLocalExpr?_instantiateBinderSpec
    {resolve : Address → Option (ConstRef β)} {values : LocalValues β}
    {body : KExpr .anon} {source : VExpr β} {depth : UInt64} {fresh : FVarId}
    (absent : values fresh = none)
    (bound : depth.toNat + body.size + 1 < UInt64.size)
    (reading : readLocalExpr? resolve values body (depth.toNat + 1) = some source) :
    readLocalExpr? resolve (values.pushBinder fresh)
      (KExpr.instantiateRevSpec body #[KExpr.mkFVar fresh ()] depth) depth.toNat =
        some source := by
  let lifted : LocalValues β := fun id => (values id).map (·.liftN 1)
  have liftReads := readLocalExpr?_lift (more := lifted) (by intros; simp_all [lifted]) reading
  have opened := readLocalExpr?_instantiateLetSpec (value := .bvar 0)
    (fresh := fresh) (by simp [lifted, absent]) bound liftReads
  have maps : lifted.pushLet fresh (.bvar 0) = values.pushBinder fresh := rfl
  rw [maps] at opened
  simpa only [AExpr.erase, inst_lift_above] using opened

private theorem BinderOpeningSupport.localWalk {before : TcState .anon}
    {body : KExpr .anon} (support : BinderOpeningSupport before body) :
    let fv := KExpr.mkFVar (m := .anon) ⟨before.env.nextFVarId⟩ ()
    let interned := before.env.intern.internExpr fv
    let walked := instantiateRev body #[fv] interned.2
    interned.1 = fv ∧ walked.1 = KExpr.instantiateRevSpec body #[fv] 0 ∧ walked.2.WF := by
  have keyFaithful : KExpr.KeyCollisionFree (fun term =>
      before.env.intern.ExprSupport term ∨ term = KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()) :=
    KExpr.keyCollisionFree_anon.mpr
    (support.faithful.mono fun term h => h.elim Or.inl (fun equal => .inr (.inl equal)))
  have interned : (before.env.intern.internExpr
      (KExpr.mkFVar ⟨before.env.nextFVarId⟩ ())).1 =
        KExpr.mkFVar ⟨before.env.nextFVarId⟩ () := by
    simpa only [KExpr.eraseMeta_anon] using
      before.env.intern.internExpr_eraseMeta support.coherent keyFaithful
  have walk := instantiateRev_spec (fvars := #[KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()])
    support.faithful support.constructed (by simpa using support.bound)
    (fun _ reached => .inr (.inr reached))
    (support.coherent.internExpr (KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()))
    (fun _ member => (InternTable.ExprSupport.of_internExpr member).elim
      Or.inl (fun equal => .inr (.inl equal)))
  exact ⟨interned, walk.1, walk.2.1⟩

theorem openLet_local_sound
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {values : LocalValues β} {context : Model.Context β}
    {type value body opened : KExpr .anon} {A e : AExpr β} {b : VExpr β}
    {fresh : FVarId} {before after : TcState .anon} {name : Mode.anon.F Name}
    (support : BinderOpeningSupport before body)
    (agreement : LocalContextValues.{u,v} resolve entries values before.lctx context)
    (below : values.Below before.env.nextFVarId)
    (typeReads : readLocalExpr? resolve values type = some A.erase)
    (valueReads : readLocalExpr? resolve values value = some e.erase)
    (bodyReads : readLocalExpr? resolve values body 1 = some b)
    (typed : TypingClaim.{u,v} entries context e A)
    (accepted : TcM.openLet name type value body before = .ok (opened, fresh) after) :
    fresh = ⟨before.env.nextFVarId⟩ ∧
      readLocalExpr? resolve (values.pushLet fresh e) opened = some (b.inst e.erase) ∧
      LocalContextValues.{u,v} resolve entries (values.pushLet fresh e) after.lctx context ∧
      (values.pushLet fresh e).Below after.env.nextFVarId ∧ after.env.intern.WF := by
  have nameUnit : name = () := Subsingleton.elim _ _
  subst name
  have absent := below.absent
  have walk := support.localWalk
  rw [openLet_eq] at accepted
  split at accepted
  next room =>
    simp only [walk.1] at accepted
    cases accepted
    refine ⟨rfl, ?_, agreement.pushLet absent typeReads valueReads typed,
      below.pushLet e room, walk.2.2⟩
    rw [walk.2.1]
    exact readLocalExpr?_instantiateLetSpec absent (by simpa using support.bound) bodyReads
  · contradiction

theorem openBinder_local_sound
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {values : LocalValues β} {context : Model.Context β}
    {type body opened : KExpr .anon} {A : AExpr β} {b : VExpr β}
    {fresh : FVarId} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    (support : BinderOpeningSupport before body)
    (agreement : LocalContextValues.{u,v} resolve entries values before.lctx context)
    (below : values.Below before.env.nextFVarId)
    (typeReads : readLocalExpr? resolve values type = some A.erase)
    (bodyReads : readLocalExpr? resolve values body 1 = some b)
    (accepted : TcM.openBinder name bi type body before = .ok (opened, fresh) after) :
    fresh = ⟨before.env.nextFVarId⟩ ∧
      readLocalExpr? resolve (values.pushBinder fresh) opened = some b ∧
      LocalContextValues.{u,v} resolve entries (values.pushBinder fresh)
        after.lctx (context.push A) ∧ (values.pushBinder fresh).Below after.env.nextFVarId ∧
      after.env.intern.WF := by
  have nameUnit : name = () := Subsingleton.elim _ _
  have biUnit : bi = () := Subsingleton.elim _ _
  subst name bi
  have absent := below.absent
  have walk := support.localWalk
  rw [openBinder_eq] at accepted
  split at accepted
  next room =>
    simp only [walk.1] at accepted
    cases accepted
    refine ⟨rfl, ?_, agreement.pushBinder absent typeReads, below.pushBinder room, walk.2.2⟩
    rw [walk.2.1]
    exact readLocalExpr?_instantiateBinderSpec absent (by simpa using support.bound) bodyReads
  · contradiction

end Ix.Kernel.Consistency
