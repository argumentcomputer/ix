/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Env
import Ix.Kernel.Const
import Ix.Kernel.Annotate
import Ix.Kernel.Inductive.Ordinary
import Ix.Kernel.Inductive.Structure
import Ix.Kernel.Inductive.Natural
import Ix.Kernel.Certified.Quotient.Install
import Ix.Kernel.Certified.Standard.Install
import Ix.Kernel.Certified.Basis.EqualityChecked

/-! # The declaration checker

The executable entry points of the kernel. `checkDecl` checks one declaration
against the environment; `checkDecls` folds it over a list in the supplied
order; `check` starts from the empty environment. Every accepting run has the
model constructed in `Ix.Kernel.Consistency`.

Outcomes are accept (`.ok`), reject (`Error.rejected`: the input is wrong),
and decline (`Error.declined`: the kernel does not support the input and says
why). Only accept carries the theorems.

Milestone K1 supports single-member blocks holding one safe definition,
theorem, or opaque: the declared type is annotated and checked to be a type,
the body is annotated and checked to have the declared type (a theorem's
type must be a proposition), and the constant is installed with its body. The
proof-carrying `checkDeclC` returns the environment together with model
extension, old-lookup preservation (`AdmissionClaim`), and the exact
installed type and body reading of the supplied block (`Block.Installed`). The public `checkDecl` erases
that evidence. -/

namespace Ix.Kernel

open Model Model.SetTheory Certified Certified.Ordinary Certified.Structure Inductive

universe u v

/-- Kernel configuration. -/
structure Config where
  /-- Fuel for reduction, inference, and conversion; exhaustion declines. -/
  fuel : Nat := 100000
  deriving Repr

/-- Non-accepting outcomes. -/
inductive Error where
  /-- The input is wrong. -/
  | rejected (reason : String)
  /-- The kernel does not support the input. -/
  | declined (reason : String)
  deriving Repr, DecidableEq

/-- Translate a bounded search failure without treating lack of evidence as
evidence that the input is wrong. The context locates a nested failure. -/
def Error.ofSearch (context : String) : SearchFailure → Error
  | .exhausted => .declined s!"{context}: out of fuel"
  | .unsupported reason => .declined s!"{context}: {reason}"
  | .unresolved reason => .declined s!"{context}: {reason}"
  | .malformed reason => .rejected s!"{context}: {reason}"
  | .noMatch => .declined s!"{context}: no applicable supported rule"

/-- The admitted eliminator of an equality family at member 0 of its block: the
installed entry with the equality eliminator interface over the family's
reflexivity constructor. Ixon stores a recursor as its own record, so its
reference is found, not assumed to follow the family; when none is found, the
paired fixture position is returned and the interface check reports the
mismatch. -/
def eqEliminator {β : Type u} [DecidableEq β] (env : Env β) : ConstRef β → Option (ConstRef β)
  | .member b 0 => some <| (env.findRef fun r =>
      decide (Basis.Equality.Interface env.toEnvironment (.member b 0) (.ctor b 0 0) r)).getD
        (.member b 1)
  | _ => none

/-- An input declaration: a block of constants at its address. -/
structure Decl (β : Type u) where
  address : β
  block : Block β

variable {β : Type u} [DecidableEq β]

/-- Attach the exact supplied block to an admission without another runtime
validation or a second copy of the environment. -/
private def acceptInstalled (env : Env β) (d : Decl β)
    (result : { env' : Env β // AdmissionClaim.{u,v} env env' })
    (source : d.block.Installed d.address result.val.toEnvironment) :
    Except Error { env' : Env β // AdmissionClaim.{u,v} env env' ∧
      d.block.Installed d.address env'.toEnvironment } :=
  .ok ⟨result.val, result.property, source⟩

/-- Install one checked definition. -/
private def installDefinition (env : Env β) (r : ConstRef β) (universes : Nat)
    (type body : AExpr β) (fresh : env.toEnvironment r = none)
    (hTs : type.Scope universes 0) (hBs : body.Scope universes 0)
    (hTr : type.ReferencesIn env.toEnvironment) (hBr : body.ReferencesIn env.toEnvironment)
    {level : VLevel} (hT : TypingClaim.{u,v} env.toEnvironment [] type (.sort level))
    (hB : TypingClaim.{u,v} env.toEnvironment [] body type) :
    { env' : Env β // AdmissionClaim.{u,v} env env' } :=
  let entry : ConstantEntry β := ⟨universes, type, some body, [], []⟩
  ⟨env.push r entry, ⟨fun V _ m => by
    obtain ⟨constants', hM', -⟩ := extend_definition (entry := entry) m.wf fresh rfl rfl rfl hBs hTr hBr
      hT hB m.constants m.realizes
    refine ⟨⟨constants', ?_, ?_⟩⟩
    · rw [Env.toEnvironment_push]; exact hM'
    · rw [Env.toEnvironment_push]
      exact m.wf.insert hTs (fun b hb => by cases hb; exact hBs) hTr
        (fun b hb => by cases hb; exact hBr) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ h => nomatch h) (fun _ h => nomatch h),
    env.preserves_push r entry fresh⟩⟩

/-- Replacing an installed entry's type by a formed type it converts to keeps
every model: only the type's validity and the constant's membership mention
the type, and conversion gives both types the same denotation. -/
noncomputable def Model.retype {V : Type v} [SetTheory V] {env : Env β} (m : Model V env)
    {r : ConstRef β} {entry : ConstantEntry β} (hr : env.toEnvironment r = some entry)
    {T : AExpr β} (hT : FormedClaim.{u,v} env.toEnvironment [] T)
    (hc : ConvClaim.{u,v} env.toEnvironment [] entry.type T)
    (hs : T.Scope entry.universes 0) (hrefs : T.ReferencesIn env.toEnvironment) :
    Model V (env.push r { entry with type := T }) where
  constants := m.constants
  realizes := by
    rw [Env.toEnvironment_push]
    have hM := m.realizes
    exact hM.insert {
      typeValid := fun levels _ valuation =>
        hT V m.constants hM levels valuation (Context.valid_nil m.constants levels valuation)
      member := fun levels hl valuation => by
        have hmem := hM.member r entry hr levels hl valuation
        rw [hc V m.constants hM levels valuation (Context.valid_nil m.constants levels valuation)
          (hM.typeValid r entry hr levels hl valuation)
          (hT V m.constants hM levels valuation (Context.valid_nil m.constants levels valuation))]
          at hmem
        exact hmem
      bodyValid := hM.bodyValid r entry hr
      bodyValue := hM.bodyValue r entry hr
      equationValue := hM.equationValue r entry hr
      factMeaning := hM.factMeaning r entry hr }
  wf := by
    rw [Env.toEnvironment_push]
    have hE := m.wf
    exact hE.insert hs (hE.bodyScope r entry hr) hrefs (hE.bodyReferences r entry hr)
      (hE.equationScope r entry hr) (hE.equationReferences r entry hr)
      (hE.factScope r entry hr) (hE.factReferences r entry hr)

omit [DecidableEq β] in
/-- A family's installed reading survives changes at any other reference. -/
theorem Const.Installed.mono_except {c : Const β} {source : β} {index : Nat}
    {before after : Environment β} {r : ConstRef β} (h : c.Installed source index before)
    (hmember : r ≠ .member source index) (hctor : ∀ j, r ≠ .ctor source index j)
    (preserves : ∀ q entry, q ≠ r → before q = some entry → after q = some entry) :
    c.Installed source index after := by
  refine ⟨?_, ?_⟩
  · obtain ⟨entry, he, hr⟩ := h.1
    exact ⟨entry, preserves _ _ (Ne.symm hmember) he, hr⟩
  · cases c <;> try trivial
    intro j ctor hc
    obtain ⟨entry, he, hr⟩ := h.2 j ctor hc
    exact ⟨entry, preserves _ _ (Ne.symm (hctor j)) he, hr⟩

/-- Whether a recursor reference is distinct from every reference of the
family at member 0 of `source`. -/
def recursorApart (source : β) : ConstRef β → Bool
  | .member b i => !(b == source && i == 0)
  | .ctor _ _ _ => false

theorem recursorApart_spec {source : β} {r : ConstRef β} (h : recursorApart source r = true) :
    r ≠ .member source 0 ∧ ∀ j, r ≠ .ctor source 0 j := by
  cases r with
  | member b i =>
    refine ⟨fun he => ?_, fun j he => by cases he⟩
    cases he
    simp [recursorApart] at h
  | ctor _ _ _ => simp [recursorApart] at h

/-- Install a read ordinary block: the generated family and recursor. -/
private def installReadingC (cfg : Config) (env : Env β) (source : β) (recursor : ConstRef β)
    (shape : Shape β) (mode : ElimMode) (k : Bool) : Except Error { env' : Env β //
      AdmissionClaim.{u,v} env env' ∧ (shape.source source).Installed source 0 env'.toEnvironment ∧
        ∃ entry, env'.toEnvironment recursor = some entry ∧
          (shape.recursorSource source mode k recursor).TypeBodyReads entry } :=
  let entries := env.toEnvironment
  if k && !decide shape.SupportsK then
    .error (.rejected "K-like reduction is declared for an inductive that does not support it")
  else
    match checkBlock.{u,v} cfg.fuel entries source shape mode recursor with
    | .ok ⟨hb⟩ =>
      if hnat : shape = Natural.shape then
        match Natural.check.{u,v} entries source (.recursor mode recursor) (hnat ▸ hb) with
        | some ⟨hn⟩ =>
          let installed := installNatural env source mode hn
          .ok ⟨installed.val, installed.property, by
            simpa only [hnat] using installNatural_members env source mode hn k⟩
        | none =>
          let installed := installOrdinary env source shape mode hb
          .ok ⟨installed.val, installed.property, installOrdinary_members env source shape mode hb k⟩
      else
      match readDescription.{u,v} cfg.fuel entries shape with
      | .ok description =>
        if hd : description.ordinary = shape then
          match Structure.check.{u,v} cfg.fuel entries description source (.recursor mode recursor) (hd ▸ hb) with
          | .ok ⟨hs⟩ =>
            let installed := installStructure env source description mode hs
            .ok ⟨installed.val, installed.property, by
              simpa only [← hd] using installStructure_members env source description mode hs k⟩
          | .error .exhausted => .error (Error.ofSearch "structure check" .exhausted)
          | .error _ =>
            let installed := installOrdinary env source shape mode hb
            .ok ⟨installed.val, installed.property, installOrdinary_members env source shape mode hb k⟩
        else
          let installed := installOrdinary env source shape mode hb
          .ok ⟨installed.val, installed.property, installOrdinary_members env source shape mode hb k⟩
      | .error .exhausted => .error (Error.ofSearch "structure description" .exhausted)
      | .error _ =>
        let installed := installOrdinary env source shape mode hb
        .ok ⟨installed.val, installed.property, installOrdinary_members env source shape mode hb k⟩
    | .error failure => .error (Error.ofSearch "inductive block" failure)

/-- Supplied recursor rules convert to the generated ones, pairwise. The
generated rules are the installed ones; this validates the supplied record. -/
private def rulesConvert (cfg : Config) (entries : Environment β) :
    List (RecRule β) → List (RecRule β) → Except Error Unit
  | [], [] => .ok ()
  | a :: as, b :: bs =>
    match annotate.{u,v} cfg.fuel entries [] a.rhs, annotate.{u,v} cfg.fuel entries [] b.rhs with
    | .ok a', .ok b' =>
      match isDefEq.{u,v} cfg.fuel entries [] a' b' with
      | .ok _ => rulesConvert cfg entries as bs
      | .error failure => .error (Error.ofSearch "supplied recursor rule conversion" failure)
    | .error failure, _ => .error (Error.ofSearch "supplied recursor rule" failure)
    | _, .error failure => .error (Error.ofSearch "generated recursor rule" failure)
  | _, _ => .error (.declined "the supplied recursor differs from the generated ordinary recursor")

/-- A supplied recursor that agrees with the generated one except for its type
and rule right-hand sides up to conversion, as when Lean's recursor drops the
`outParam`/`optParam`/`autoParam` annotations its family's parameters carry.
The generated block is installed; the recursor's entry is then shadowed with
the supplied type, which must be formed and convert to the generated type
(`Model.retype`). Its rules stay the generated ones. -/
private def retypedRecursorC (cfg : Config) (env : Env β) (source : β) (recursor : ConstRef β)
    (family rec : Const β) (shape : Shape β) (mode : ElimMode) (k : Bool)
    (hf : family = shape.source source) (fresh : env.toEnvironment recursor = none) :
    Except Error { env' : Env β //
      AdmissionClaim.{u,v} env env' ∧ family.Installed source 0 env'.toEnvironment ∧
        ∃ entry, env'.toEnvironment recursor = some entry ∧ rec.TypeBodyReads entry } :=
  match rec, hgen : shape.recursorSource source mode k recursor with
  | .recursor ru rp ri rm rn rt rr rk rs, .recursor gu gp gi gm gn _ gr gk gs =>
    if hu : ru = gu then
    if !(rp == gp && ri == gi && rm == gm && rn == gn && rk == gk && rs == gs &&
        rr.length == gr.length && (rr.zip gr).all fun (a, b) => a.nfields == b.nfields) then
      .error (.declined "the supplied recursor differs from the generated ordinary recursor")
    else if hapart : recursorApart source recursor = true then
      match installReadingC.{u,v} cfg env source recursor shape mode k with
      | .error e => .error e
      | .ok ⟨env', step, hfam, hgenReads⟩ =>
        let entries' := env'.toEnvironment
        match he : entries' recursor with
        | none => .error (.declined "the installed recursor is missing")
        | some entry =>
          match hT : annotate.{u,v} cfg.fuel entries' [] rt with
          | .error failure => .error (Error.ofSearch "supplied recursor type" failure)
          | .ok T =>
            if hs : T.Scope entry.universes 0 then
              if hrefs : T.ReferencesIn entries' then
                match inferA.{u,v} cfg.fuel entries' [] T with
                | .error failure => .error (Error.ofSearch "supplied recursor type" failure)
                | .ok ⟨_, hTyped⟩ =>
                  match isDefEq.{u,v} cfg.fuel entries' [] entry.type T with
                  | .error failure => .error (Error.ofSearch "supplied recursor type conversion" failure)
                  | .ok ⟨hc⟩ =>
                    match rulesConvert.{u,v} cfg entries' rr gr with
                    | .error e => .error e
                    | .ok () =>
                      let entry' : ConstantEntry β := { entry with type := T }
                      have hstep : StepClaim.{u,v} env (env'.push recursor entry') := fun V _ m => by
                        obtain ⟨m'⟩ := step.step V m
                        exact ⟨Model.retype m' he hTyped.formed hc hs hrefs⟩
                      have hpres : env.Preserves (env'.push recursor entry') := fun q e hq => by
                        rw [Env.toEnvironment_push]
                        have hne : q ≠ recursor := fresh_ne fresh hq
                        simp only [Environment.insert, hne, ite_false]
                        exact step.preserves q e hq
                      have hfam' : family.Installed source 0 (env'.push recursor entry').toEnvironment := by
                        rw [hf]
                        obtain ⟨hmember, hctor⟩ := recursorApart_spec hapart
                        refine hfam.mono_except hmember hctor fun q e hq hqe => ?_
                        rw [Env.toEnvironment_push]
                        simp only [Environment.insert, hq, ite_false]
                        exact hqe
                      have hlook : (env'.push recursor entry').toEnvironment recursor = some entry' := by
                        rw [Env.toEnvironment_push]
                        exact Environment.insert_same _ _ _
                      have hreads : (Const.recursor ru rp ri rm rn rt rr rk rs).TypeBodyReads entry' := by
                        obtain ⟨e, hl, hr⟩ := hgenReads
                        rw [hgen] at hr
                        have : e = entry := Option.some.inj (hl.symm.trans he)
                        subst this
                        obtain ⟨hun, -, hbody⟩ := hr
                        exact ⟨hun.trans hu.symm, annotate_erase hT, hbody⟩
                      .ok ⟨env'.push recursor entry', ⟨hstep, hpres⟩, hfam', entry', hlook, hreads⟩
              else .error (.rejected "the supplied recursor type references a constant that is not installed")
            else .error (.rejected "the supplied recursor type is not closed in its universe parameters and variables")
    else .error (.declined "the supplied recursor differs from the generated ordinary recursor")
    else .error (.declined "the supplied recursor differs from the generated ordinary recursor")
  | _, _ => .error (.declined "the supplied recursor differs from the generated ordinary recursor")

/-- The family and its recursor retain their original, independent references.
The reader only proposes a shape; acceptance compares both complete source
records with that shape before using its semantic construction. A supplied
recursor may differ from the generated one in its type and rules up to
conversion (`retypedRecursorC`). -/
def checkInductiveC (cfg : Config) (env : Env β) (source : β) (recursor : ConstRef β)
    (family rec : Const β) : Except Error { env' : Env β //
      AdmissionClaim.{u,v} env env' ∧ family.Installed source 0 env'.toEnvironment ∧
        ∃ entry, env'.toEnvironment recursor = some entry ∧ rec.TypeBodyReads entry } :=
  let entries := env.toEnvironment
  if hdup : (entries (.member source 0)).isSome || (entries recursor).isSome then
    .error (.rejected "duplicate inductive or recursor reference")
  else if !(family.refs ++ rec.refs).all (fun q => q.block == source || q == recursor || (entries q).isSome) then
    .error (.rejected "the declaration references a constant that is not installed")
  else
    match readBlock.{u,v} cfg.fuel entries source ⟨[family, rec]⟩ with
    | .error .noMatch => .error (.declined "the inductive and recursor are not in the ordinary shape class")
    | .error failure => .error (Error.ofSearch "inductive reading" failure)
    | .ok reading =>
      let shape := reading.shape
      let mode := reading.mode
      let k := reading.k
      if hf : family = shape.source source then
        if hr : rec = shape.recursorSource source mode k recursor then
          match installReadingC.{u,v} cfg env source recursor shape mode k with
          | .ok ⟨env', step, hfam, hrec⟩ => .ok ⟨env', step, hf ▸ hfam, hr ▸ hrec⟩
          | .error e => .error e
        else
          have fresh : entries recursor = none := by
            cases h : entries recursor with
            | none => rfl
            | some _ => simp [h] at hdup
          retypedRecursorC.{u,v} cfg env source recursor family rec shape mode k hf fresh
      else .error (.declined "the supplied inductive differs from the generated ordinary family")

/-- Check a supplied family and its constructors without an absent recursor.
The same Nat and structure fact checks apply to this smaller stage. -/
def checkFamilyC (cfg : Config) (env : Env β) (source : β) (family : Const β) :
    Except Error { env' : Env β // AdmissionClaim.{u,v} env env' ∧
      family.Installed source 0 env'.toEnvironment } := do
  let entries := env.toEnvironment
  if (entries (.member source 0)).isSome then
    throw (.rejected "duplicate inductive reference")
  if !family.refs.all (fun q => q.block == source || (entries q).isSome) then
    throw (.rejected "the declaration references a constant that is not installed")
  let shape ← (readFamily.{u,v} cfg.fuel entries source family).mapError
    (Error.ofSearch "inductive family reading")
  if hf : family = shape.source source then
    let ⟨hb⟩ ← ((Stage.family : Stage β).check.{u,v} cfg.fuel entries source shape).mapError
      (Error.ofSearch "inductive family")
    let fallback : Except Error { env' : Env β // AdmissionClaim.{u,v} env env' ∧
        family.Installed source 0 env'.toEnvironment } :=
      let installed := installFamily env source shape hb
      .ok ⟨installed.val, installed.property, by
        simpa only [hf] using installFamily_fidelity env source shape hb⟩
    if hnat : shape = Natural.shape then
      match Natural.check.{u,v} entries source .family (hnat ▸ hb) with
      | some ⟨hn⟩ =>
        let installed := installNaturalStage env source .family hn
        return ⟨installed.val, installed.property, by
          simpa only [hf, hnat] using installNaturalStage_family env source .family hn⟩
      | none => fallback
    else
      match readDescription.{u,v} cfg.fuel entries shape with
      | .ok description =>
        if hd : description.ordinary = shape then
          match Structure.check.{u,v} cfg.fuel entries description source .family (hd ▸ hb) with
          | .ok ⟨hs⟩ =>
            let installed := installStructureStage env source description .family hs
            return ⟨installed.val, installed.property, by
              simpa only [hf, ← hd] using installStructureStage_family env source description .family hs⟩
          | .error .exhausted => throw (Error.ofSearch "structure check" .exhausted)
          | .error _ => fallback
        else fallback
      | .error .exhausted => throw (Error.ofSearch "structure description" .exhausted)
      | .error _ => fallback
  else throw (.declined "the supplied inductive differs from the generated ordinary family")

/-- Check one declaration, returning model extension, preservation, and
the installed type and body reading with the environment. -/
def checkDeclC (cfg : Config) (env : Env β) (d : Decl β) :
    Except Error { env' : Env β // AdmissionClaim.{u,v} env env' ∧
      d.block.Installed d.address env'.toEnvironment } :=
  match hm : d.block.members with
  | [.defn universes kind type body .safe] =>
    let r : ConstRef β := .member d.address 0
    let entries := env.toEnvironment
    if fresh : entries r = none then
      if !(type.refs ++ body.refs).all (fun q => (entries q).isSome) then
        .error (.rejected "the declaration references a constant that is not installed")
      else
      match hTypeReading : annotate.{u,v} cfg.fuel entries [] type,
          hBodyReading : annotate.{u,v} cfg.fuel entries [] body with
      | .ok type', .ok body' =>
        if hTs : type'.Scope universes 0 then
          if hBs : body'.Scope universes 0 then
            if hTr : type'.ReferencesIn entries then
              if hBr : body'.ReferencesIn entries then
                match inferA.{u,v} cfg.fuel entries [] type' with
                | .ok ⟨S, hS⟩ =>
                  match sortOf (whnf.{u,v} cfg.fuel entries [] S) hS with
                  | .ok ⟨l, hT⟩ =>
                    if kind = .theorem && !levelIsZero l then
                      if zeroCondition l = .never then
                        .error (.rejected "the type of a theorem must be a proposition")
                      else
                        .error (.declined "the theorem's type was not established to be a proposition")
                    else
                      match inferA.{u,v} cfg.fuel entries [] body' with
                      | .ok ⟨B, hb⟩ =>
                        match isDefEq.{u,v} cfg.fuel entries [] B type' with
                        | .ok ⟨hc⟩ =>
                          acceptInstalled env d
                            (installDefinition env r universes type' body' fresh hTs hBs hTr hBr hT
                              (hb.convF hT.formed hc)) (by
                              have hblock : d.block = ⟨[.defn universes kind type body .safe]⟩ :=
                                congrArg Block.mk hm
                              rw [hblock]
                              exact Block.installed_singleton_push env d.address _ _
                                ⟨rfl, annotate_erase hTypeReading,
                                  congrArg some (annotate_erase hBodyReading)⟩ rfl)
                        | .error failure => .error (Error.ofSearch "body conversion" failure)
                      | .error failure => .error (Error.ofSearch "body" failure)
                  | .error failure => .error (Error.ofSearch "declared type" failure)
                | .error failure => .error (Error.ofSearch "declared type" failure)
              else .error (.rejected "the body references a constant that is not installed")
            else .error (.rejected "the declared type references a constant that is not installed")
          else .error (.rejected "the body is not closed in its universe parameters and variables")
        else .error (.rejected "the declared type is not closed in its universe parameters and variables")
      | .error a, .error b => .error (Error.ofSearch "annotation" (a.merge b))
      | .error failure, _ => .error (Error.ofSearch "declared type" failure)
      | _, .error failure => .error (Error.ofSearch "body" failure)
    else .error (.rejected "duplicate declaration address")
  | [.induct iu ip ii it ics .safe, .recursor ru rp ri rm rn rt rr rk .safe] => do
    let family := Const.induct iu ip ii it ics .safe
    let recDecl := Const.recursor ru rp ri rm rn rt rr rk .safe
    let ⟨env', step, hf, hr⟩ ←
      checkInductiveC.{u,v} cfg env d.address (.member d.address 1) family recDecl
    return ⟨env', step, by
      have hblock : d.block = ⟨[family, recDecl]⟩ := congrArg Block.mk hm
      rw [hblock]
      exact Block.installed_pair hf ⟨hr, trivial⟩⟩
  | [.induct iu ip ii it ics .safe] => do
    let family := Const.induct iu ip ii it ics .safe
    let ⟨env', step, hf⟩ ← checkFamilyC.{u,v} cfg env d.address family
    return ⟨env', step, by
      have hblock : d.block = ⟨[family]⟩ := congrArg Block.mk hm
      rw [hblock]
      exact Block.installed_singleton hf⟩
  | [.induct _ _ _ _ _ _, .recursor _ _ _ _ _ _ _ _ _] =>
    .error (.declined "unsafe inductive blocks are not supported")
  | [.defn _ _ _ _ _] => .error (.declined "unsafe and partial definitions are not supported")
  | [.quot kind uvars t] =>
    let self : ConstRef β := .member d.address 0
    let entries := env.toEnvironment
    if fresh : entries self = none then
      if !t.refs.all (fun q => (entries q).isSome) then
        .error (.rejected "the declaration references a constant that is not installed")
      else
      match kind, uvars, Quotient.occurrences t with
      | .type, 1, [] =>
        if hblock : d.block = ⟨[Quotient.Refs.source (⟨self, self, self, self, self⟩ : Quotient.Refs β) .type]⟩ then
          if hTs : (Quotient.typeType : AExpr β).Scope 1 0 then
            match checkSort.{u,v} cfg.fuel entries [] Quotient.typeType with
            | .ok ⟨_, ht⟩ => acceptInstalled env d (Quotient.installType env self fresh hTs ht) (by
                rw [hblock]
                exact Block.installed_singleton_push env d.address _ _ ⟨rfl, rfl, rfl⟩ rfl)
            | .error failure => .error (Error.ofSearch "quotient former type" failure)
          else .error (.rejected "the quotient former's type is not closed")
        else .error (.declined "the quotient former is not the primitive one")
      | .ctor, 1, [q] =>
        let refs : Quotient.Refs β := ⟨q, q, self, self, self⟩
        if hblock : d.block = ⟨[Quotient.Refs.source refs .ctor]⟩ then
          if hq : Quotient.HasFormer entries refs then
            if hTs : (Quotient.ctorType refs).Scope 1 0 then
              if hTr : (Quotient.ctorType refs).ReferencesIn entries then
                match checkSort.{u,v} cfg.fuel entries [] (Quotient.ctorType refs) with
                | .ok ⟨_, ht⟩ => acceptInstalled env d (Quotient.installCtor env refs fresh hTs hq hTr ht) (by
                    rw [hblock]
                    exact Block.installed_singleton_push env d.address _ _ ⟨rfl, rfl, rfl⟩ rfl)
                | .error failure => .error (Error.ofSearch "quotient constructor type" failure)
              else .error (.rejected "the quotient constructor references a constant that is not installed")
            else .error (.rejected "the quotient constructor's type is not closed")
          else .error (.rejected "the quotient constructor does not follow the admitted former")
        else .error (.declined "the quotient constructor is not the primitive one")
      | .lift, 2, [eq, q] =>
        let refs : Quotient.Refs β := ⟨eq, q, self, self, self⟩
        if hblock : d.block = ⟨[Quotient.Refs.source refs .lift]⟩ then
          if hq : Quotient.HasFormer entries refs then
            if hTs : (Quotient.liftType refs).Scope 2 0 then
              if hTr : (Quotient.liftType refs).ReferencesIn entries then
                match eqEliminator env eq with
                | some recursor =>
                  if hE : Quotient.EqInterface entries eq recursor then
                    match checkSort.{u,v} cfg.fuel entries [] (Quotient.liftType refs) with
                    | .ok ⟨_, ht⟩ => acceptInstalled env d
                        (Quotient.installLift env refs recursor fresh hTs hq hTr hE ht) (by
                          rw [hblock]
                          exact Block.installed_singleton_push env d.address _ _ ⟨rfl, rfl, rfl⟩ rfl)
                    | .error failure => .error (Error.ofSearch "quotient lift type" failure)
                  else .error (.declined "the quotient lift's equality is not the admitted one")
                | none => .error (.declined "the quotient lift's equality has no admitted eliminator")
              else .error (.rejected "the quotient lift references a constant that is not installed")
            else .error (.rejected "the quotient lift's type is not closed")
          else .error (.rejected "the quotient lift does not follow the admitted former")
        else .error (.declined "the quotient lift is not the primitive one")
      | .ind, 1, [q, c] =>
        let refs : Quotient.Refs β := ⟨q, q, c, self, self⟩
        if hblock : d.block = ⟨[Quotient.Refs.source refs .ind]⟩ then
          if hq : Quotient.HasFormer entries refs then
            if hc : Quotient.HasCtor entries refs then
              if hTs : (Quotient.indType refs).Scope 1 0 then
                if hTr : (Quotient.indType refs).ReferencesIn entries then
                  match checkSort.{u,v} cfg.fuel entries [] (Quotient.indType refs) with
                  | .ok ⟨_, ht⟩ => acceptInstalled env d (Quotient.installInd env refs fresh hTs hq hc hTr ht) (by
                      rw [hblock]
                      exact Block.installed_singleton_push env d.address _ _ ⟨rfl, rfl, rfl⟩ rfl)
                  | .error failure => .error (Error.ofSearch "quotient eliminator type" failure)
                else .error (.rejected "the quotient eliminator references a constant that is not installed")
              else .error (.rejected "the quotient eliminator's type is not closed")
            else .error (.rejected "the quotient eliminator does not follow the admitted constructor")
          else .error (.rejected "the quotient eliminator does not follow the admitted former")
        else .error (.declined "the quotient eliminator is not the primitive one")
      | _, _, _ => .error (.declined "the quotient declaration is not one of the primitive ones")
    else .error (.rejected "duplicate declaration address")
  | [.axiom 0 t .safe] =>
    let self : ConstRef β := .member d.address 0
    let entries := env.toEnvironment
    if fresh : entries self = none then
      if !t.refs.all (fun q => (entries q).isSome) then
        .error (.rejected "the declaration references a constant that is not installed")
      else
      match Standard.occurrences t with
      | [iff, eq] =>
        match Standard.propextSpec env eq iff with
        | some spec =>
          if hblock : d.block = ⟨[spec.source]⟩ then
            if hp : spec.Prerequisites entries then
              if hTs : spec.type.Scope spec.universes 0 then
                if hTr : spec.type.ReferencesIn entries then
                  match checkSort.{u,v} cfg.fuel entries [] spec.type with
                  | .ok ⟨level, ht⟩ => acceptInstalled env d
                      (Standard.install env self spec ⟨fresh, hp, hTs, hTr, ⟨level, ht⟩⟩) (by
                        rw [hblock]
                        exact Block.installed_singleton_push env d.address _ _ ⟨rfl, rfl, rfl⟩ rfl)
                  | .error failure => .error (Error.ofSearch "axiom type" failure)
                else .error (.rejected "the axiom references a constant that is not installed")
              else .error (.rejected "the axiom's type is not closed")
            else .error (.declined "the axiom's prerequisites are not the admitted interfaces")
          else .error (.declined "only the standard axioms and quotient soundness are supported")
        | none => .error (.declined "only the standard axioms and quotient soundness are supported")
      | _ => .error (.declined "only the standard axioms and quotient soundness are supported")
    else .error (.rejected "duplicate declaration address")
  | [.axiom 1 t .safe] =>
    let self : ConstRef β := .member d.address 0
    let entries := env.toEnvironment
    if fresh : entries self = none then
      if !t.refs.all (fun q => (entries q).isSome) then
        .error (.rejected "the declaration references a constant that is not installed")
      else
      match Quotient.occurrences t with
      | [eq, q, c] =>
        let refs : Quotient.Refs β := ⟨eq, q, c, self, self⟩
        if hblock : d.block = ⟨[Quotient.Refs.soundSource refs]⟩ then
          if hq : Quotient.HasFormer entries refs then
            if hc : Quotient.HasCtor entries refs then
              match eqEliminator env eq with
              | none => .error (.declined "the quotient soundness axiom's equality has no admitted eliminator")
              | some recursor =>
              if hE : Quotient.EqInterface entries eq recursor then
                if hTs : (Quotient.soundType refs).Scope 1 0 then
                  if hTr : (Quotient.soundType refs).ReferencesIn entries then
                    match checkSort.{u,v} cfg.fuel entries [] (Quotient.soundType refs) with
                    | .ok ⟨_, ht⟩ => acceptInstalled env d
                        (Quotient.installSound env refs self fresh hTs hq hc hE hTr ht) (by
                          rw [hblock]
                          exact Block.installed_singleton_push env d.address _ _ ⟨rfl, rfl, rfl⟩ rfl)
                    | .error failure => .error (Error.ofSearch "quotient soundness type" failure)
                  else .error (.rejected "the quotient soundness axiom references a constant that is not installed")
                else .error (.rejected "the quotient soundness axiom's type is not closed")
              else .error (.declined "the quotient soundness axiom's equality is not the admitted one")
            else .error (.rejected "the quotient soundness axiom does not follow the admitted constructor")
          else .error (.rejected "the quotient soundness axiom does not follow the admitted former")
        else .error (.declined "only the standard axioms and quotient soundness are supported")
      | [nonempty] =>
        match Standard.choiceSpec env nonempty with
        | some spec =>
          if hblock : d.block = ⟨[spec.source]⟩ then
            if hp : spec.Prerequisites entries then
              if hTs : spec.type.Scope spec.universes 0 then
                if hTr : spec.type.ReferencesIn entries then
                  match checkSort.{u,v} cfg.fuel entries [] spec.type with
                  | .ok ⟨level, ht⟩ => acceptInstalled env d
                      (Standard.install env self spec ⟨fresh, hp, hTs, hTr, ⟨level, ht⟩⟩) (by
                        rw [hblock]
                        exact Block.installed_singleton_push env d.address _ _ ⟨rfl, rfl, rfl⟩ rfl)
                  | .error failure => .error (Error.ofSearch "axiom type" failure)
                else .error (.rejected "the axiom references a constant that is not installed")
              else .error (.rejected "the axiom's type is not closed")
            else .error (.declined "the axiom's prerequisites are not the admitted interfaces")
          else .error (.declined "only the standard axioms and quotient soundness are supported")
        | none => .error (.declined "only the standard axioms and quotient soundness are supported")
      | _ => .error (.declined "only the standard axioms and quotient soundness are supported")
    else .error (.rejected "duplicate declaration address")
  | [.axiom _ _ _] => .error (.declined "only the standard axioms and quotient soundness are supported")
  | [_] => .error (.declined "only definitions, inductive blocks, quotient primitives, and the standard axioms are supported")
  | _ => .error (.declined "multi-member blocks are not supported")

/-- Check one declaration against the environment. -/
def checkDecl (cfg : Config) (env : Env β) (d : Decl β) : Except Error (Env β) :=
  (checkDeclC.{u,v} cfg env d).map Subtype.val

/-! ## Association of separate inductive and recursor records

Ixon stores an ordinary inductive family and its recursor in separate primary
records. Like `Ix.Tc` and the Rust kernel, association uses the recursor's
major premise. This reader handles the syntactic ordinary profile; it does
not reduce open telescope bodies in an empty context. Association is only
candidate discovery: `checkInductiveC` checks both complete records, all
metadata and rules, formation, and freshness before installing either. -/

/-- The ordinary recursor's major follows parameters, motives, minors, and
indices. Natural-number metadata cannot overflow while locating it. -/
def recursorMajor : Const β → Option (ConstRef β)
  | .recursor _ params indices motives minors type _ _ _ => do
    let (_, tail) ← Certified.Ordinary.splitN (params + motives + minors + indices) type
    let .forallE domain _ := tail | none
    let .const family _ := domain.appHead | none
    return family
  | _ => none

/-- A selected physical record and the remaining records. Proof fields ensure
that finding a candidate cannot silently discard another input record. -/
structure RecursorCandidate (decls : List (Decl β)) where
  declaration : Decl β
  constant : Const β
  rest : List (Decl β)
  singleton : declaration.block = ⟨[constant]⟩
  noConstructors : constant.ctorCount = 0
  covers : ∀ d ∈ decls, d = declaration ∨ d ∈ rest
  shorter : rest.length < decls.length

def findRecursor (family : ConstRef β) : (decls : List (Decl β)) → Option (RecursorCandidate decls)
  | [] => none
  | d :: ds =>
    let remaining : Unit → Option (RecursorCandidate (d :: ds)) := fun _ => do
      let candidate ← findRecursor family ds
      return {
        declaration := candidate.declaration
        constant := candidate.constant
        rest := d :: candidate.rest
        singleton := candidate.singleton
        noConstructors := candidate.noConstructors
        covers := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact .inr List.mem_cons_self
          · rcases candidate.covers q hq with same | member
            · exact .inl same
            · exact .inr (List.mem_cons_of_mem _ member)
        shorter := Nat.succ_lt_succ candidate.shorter }
    match hm : d.block.members with
    | [.recursor u p i mo mi type rules k safety] =>
      let constant := Const.recursor u p i mo mi type rules k safety
      if recursorMajor constant = some family then
        some {
          declaration := d
          constant
          rest := ds
          singleton := congrArg Block.mk hm
          noConstructors := rfl
          covers := fun q hq => List.mem_cons.mp hq
          shorter := Nat.lt_succ_self _ }
      else remaining ()
    | _ => remaining ()

/-- The proof-carrying fold, over physical declarations in the supplied order.
A singleton inductive family is admitted together with the first later
singleton recursor whose major premise names it (Ixon stores the two as
separate records); the ordinary paired layout remains supported by
`checkDeclC`. Every consumed declaration gets its installed type and body
reading (`Block.Installed`). -/
def checkDeclsC (cfg : Config) (env : Env β) :
    (decls : List (Decl β)) → Except Error { env' : Env β // AdmissionClaim.{u,v} env env' ∧
      ∀ d ∈ decls, d.block.Installed d.address env'.toEnvironment }
  | [] => .ok ⟨env, AdmissionClaim.refl env, by simp⟩
  | d :: ds =>
    match hm : d.block.members with
    | [.induct u p i type constructors safety] =>
      let family := Const.induct u p i type constructors safety
      match findRecursor (.member d.address 0) ds with
      | none => do
        let ⟨env₁, step₁, hd⟩ ← checkDeclC.{u,v} cfg env d
        let ⟨env₂, step₂, installed⟩ ← checkDeclsC cfg env₁ ds
        return ⟨env₂, step₁.trans step₂, by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hd.mono step₂.preserves
          · exact installed q hq⟩
      | some candidate => do
        let ⟨env₁, step₁, hf, hr⟩ ← checkInductiveC.{u,v} cfg env d.address
          (.member candidate.declaration.address 0) family candidate.constant
        let ⟨env₂, step₂, installed⟩ ← checkDeclsC cfg env₁ candidate.rest
        return ⟨env₂, step₁.trans step₂, by
          intro q hq
          rcases List.mem_cons.mp hq with same | hq
          · subst q
            have hblock : d.block = ⟨[family]⟩ := congrArg Block.mk hm
            rw [hblock]
            exact Block.installed_singleton (hf.mono step₂.preserves)
          · rcases candidate.covers q hq with rfl | hq
            · rw [candidate.singleton]
              obtain ⟨entry, found, reading⟩ := hr
              exact Block.installed_singleton ((Const.installed_of_lookup found reading
                candidate.noConstructors).mono step₂.preserves)
            · exact installed q hq⟩
    | _ => do
      let ⟨env₁, step₁, hd⟩ ← checkDeclC.{u,v} cfg env d
      let ⟨env₂, step₂, installed⟩ ← checkDeclsC cfg env₁ ds
      return ⟨env₂, step₁.trans step₂, by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hd.mono step₂.preserves
        · exact installed q hq⟩
  termination_by decls => decls.length
  decreasing_by
    · exact Nat.lt_succ_self _
    · exact Nat.lt_trans candidate.shorter (Nat.lt_succ_self _)
    · exact Nat.lt_succ_self _

/-- The closed fold: check declarations in the supplied order, each against the
environment the earlier ones built. -/
def checkDecls (cfg : Config) (env : Env β) (decls : List (Decl β)) : Except Error (Env β) :=
  (checkDeclsC.{u,v} cfg env decls).map Subtype.val

/-- The closed entry point: check declarations from the empty environment. -/
def check (cfg : Config) (decls : List (Decl β)) : Except Error (Env β) :=
  checkDecls.{u,v} cfg Env.empty decls

end Ix.Kernel
