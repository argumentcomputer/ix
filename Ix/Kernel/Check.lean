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
import Ix.Kernel.Arithmetic
import Ix.Kernel.Revalue
import Ix.Kernel.Inductive.Interleaved

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

universe u v w

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

/-- Claims established against the reduction view hold against the environment. -/
theorem TypingClaim.ofReductionView (env : Env β) {Γ : Context β} {e A : AExpr β}
    (h : TypingClaim.{u,v} env.reductionView Γ e A) : TypingClaim.{u,v} env.toEnvironment Γ e A :=
  fun V _ constants hM => h V constants (Env.realizes_reductionView env hM)

/-- The height of a definition's body: one more than the highest height among
the constants it mentions (a strategy hint for conversion). -/
def definitionHeight (entries : Environment β) (body : AExpr β) : Nat :=
  1 + body.references.foldl (fun h q =>
    match entries q with
    | some entry => max h (heightOf entry.facts)
    | none => h) 0

/-- Install one checked definition with its height; a theorem's or an opaque's
body (`hidden`) is installed but not unfolded by conversion. -/
private def installDefinition (env : Env β) (r : ConstRef β) (universes : Nat)
    (type body : AExpr β) (height : Nat) (hidden : Bool) (fresh : env.toEnvironment r = none)
    (hTs : type.Scope universes 0) (hBs : body.Scope universes 0)
    (hTr : type.ReferencesIn env.toEnvironment) (hBr : body.ReferencesIn env.toEnvironment)
    {level : VLevel} (hT : TypingClaim.{u,v} env.toEnvironment [] type (.sort level))
    (hB : TypingClaim.{u,v} env.toEnvironment [] body type) :
    { env' : Env β // AdmissionClaim.{u,v} env env' ∧
      env'.toEnvironment = (env.push r ⟨universes, type, some body, [], [.height height]⟩).toEnvironment } :=
  let entry : ConstantEntry β := ⟨universes, type, some body, [], [.height height]⟩
  ⟨env.pushWith hidden r entry, ⟨⟨fun V _ m => by
    obtain ⟨constants', hM', -⟩ := extend_definition (entry := entry) m.wf fresh rfl rfl
      (fun f hf => ⟨height, List.mem_singleton.mp hf⟩) hBs hTr hBr
      hT hB m.constants m.realizes
    refine ⟨⟨constants', ?_, ?_⟩⟩
    · rw [Env.toEnvironment_pushWith, Env.toEnvironment_push]; exact hM'
    · rw [Env.toEnvironment_pushWith, Env.toEnvironment_push]
      exact m.wf.insert hTs (fun b hb => by cases hb; exact hBs) hTr
        (fun b hb => by cases hb; exact hBr) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun f hf => by cases List.mem_singleton.mp hf; trivial)
        (fun f hf => by cases List.mem_singleton.mp hf; intro q hq; cases hq),
    fun q e hq => by
      rw [Env.toEnvironment_pushWith]
      exact env.preserves_push r entry fresh q e hq⟩,
    Env.toEnvironment_pushWith hidden env r entry⟩⟩

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

/-- Publishing a fact on an installed entry keeps every model whose assignment
meets the fact's meaning: nothing else about the entry changes. -/
noncomputable def Model.withFact {V : Type v} [SetTheory V] {env : Env β} (m : Model V env)
    {r : ConstRef β} {entry : ConstantEntry β} (hr : env.toEnvironment r = some entry)
    {fact : ConstantFact β} (hs : fact.Scope entry.universes)
    (hrefs : fact.ReferencesIn env.toEnvironment)
    (hmean : ∀ levels, levels.length = entry.universes → ∀ valuation,
      fact.Meaning m.constants r levels valuation) :
    Model V (env.push r { entry with facts := fact :: entry.facts }) where
  constants := m.constants
  realizes := by
    rw [Env.toEnvironment_push]
    have hM := m.realizes
    exact hM.insert {
      typeValid := hM.typeValid r entry hr
      member := hM.member r entry hr
      bodyValid := hM.bodyValid r entry hr
      bodyValue := hM.bodyValue r entry hr
      equationValue := hM.equationValue r entry hr
      factMeaning := fun f hf => by
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hmean
        · exact hM.factMeaning r entry hr f hf }
  wf := by
    rw [Env.toEnvironment_push]
    have hE := m.wf
    exact hE.insert (hE.typeScope r entry hr) (hE.bodyScope r entry hr)
      (hE.typeReferences r entry hr) (hE.bodyReferences r entry hr)
      (hE.equationScope r entry hr) (hE.equationReferences r entry hr)
      (fun f hf => by
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hs
        · exact hE.factScope r entry hr f hf)
      (fun f hf => by
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hrefs
        · exact hE.factReferences r entry hr f hf)

/-- Publish a checked arithmetic fact on a definition just installed at a
fresh reference, and record a numeric operation for later operations'
equations. -/
private def publishArithmetic (env env' : Env β) (r : ConstRef β) (entry : ConstantEntry β)
    (fresh : env.toEnvironment r = none) (admitted : AdmissionClaim.{u,v} env env')
    (hinst : env'.toEnvironment = (env.push r entry).toEnvironment) (hu : entry.universes = 0)
    (checked : Arithmetic.CheckedFact.{u,v} env'.reductionView r)
    (hrefs : checked.fact.ReferencesIn env'.toEnvironment) :
    { env'' : Env β // AdmissionClaim.{u,v} env env'' ∧
      env''.toEnvironment = (env.push r { entry with facts := checked.fact :: entry.facts }).toEnvironment } :=
  let entry' : ConstantEntry β := { entry with facts := checked.fact :: entry.facts }
  let natOps := match checked.fact with
    | .natOp op => (op, r) :: env'.natOps
    | _ => env'.natOps
  let env'' : Env β := { env'.push r entry' with natOps }
  have hr : env'.toEnvironment r = some entry := by
    rw [hinst, Env.toEnvironment_push]; simp [Environment.insert]
  have hview : env''.toEnvironment = (env.push r entry').toEnvironment := by
    show (env'.push r entry').toEnvironment = _
    rw [Env.toEnvironment_push, hinst, Env.toEnvironment_push, Env.toEnvironment_push]
    funext q
    simp only [Environment.insert]
    split <;> rfl
  ⟨env'', ⟨fun V _ m => by
      obtain ⟨m'⟩ := admitted.step V m
      have hmean : ∀ levels, levels.length = entry.universes → ∀ valuation,
          checked.fact.Meaning m'.constants r levels valuation := by
        intro levels hl valuation
        have hnil : levels = [] := List.eq_nil_of_length_eq_zero (hl.trans hu)
        subst hnil
        exact checked.claim V m'.constants (Env.realizes_reductionView env' m'.realizes) valuation
      let m'' := Model.withFact m' hr (hu ▸ checked.scope) hrefs hmean
      exact ⟨⟨m''.constants, m''.realizes, m''.wf⟩⟩,
    fun q e hq => by
      rw [hview, Env.toEnvironment_push]
      have hne : q ≠ r := fresh_ne fresh hq
      simp only [Environment.insert, hne, ite_false]
      exact hq⟩,
    hview⟩

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

/-! ## Ordinary fields after recursive fields (A2)

A family whose constructors interleave ordinary and recursive fields, with no
ordinary field depending on a recursive one, is admitted through its canonical
(ordinary-first) block: the canonical block is checked and installed as usual,
then the supplied constructors and recursor replace the canonical entries,
valued by closed wrapper terms over them (`Ix.Kernel.Revalue`). The supplied
types and rules are installed as supplied; every wrapper, rule and typing is
checked by inference and conversion first. -/

/-- Claims against the reduction view hold against the environment. -/
theorem ConvClaim.ofReductionView (env : Env β) {Γ : Context β} {a b : AExpr β}
    (h : ConvClaim.{u,v} env.reductionView Γ a b) : ConvClaim.{u,v} env.toEnvironment Γ a b :=
  fun V _ constants hM => h V constants (Env.realizes_reductionView env hM)

theorem FormedClaim.ofReductionView (env : Env β) {Γ : Context β} {e : AExpr β}
    (h : FormedClaim.{u,v} env.reductionView Γ e) : FormedClaim.{u,v} env.toEnvironment Γ e :=
  fun V _ constants hM => h V constants (Env.realizes_reductionView env hM)

/-- Establish `e : T` at the empty context: `T` is a type and `e`'s inferred
type converts to it. -/
private def checkClosedTyping (fuel : Nat) (entries : Environment β) (what : String)
    (e T : AExpr β) : Except Error (CheckedClaim.{u} (TypingClaim.{u,v} entries [] e T)) :=
  match inferA.{u,v} fuel entries [] T with
  | .error failure => .error (Error.ofSearch what failure)
  | .ok ⟨S, hS⟩ =>
    match sortOf (whnf.{u,v} fuel entries [] S) hS with
    | .error failure => .error (Error.ofSearch what failure)
    | .ok ⟨_, hT⟩ =>
      match inferA.{u,v} fuel entries [] e with
      | .error failure => .error (Error.ofSearch what failure)
      | .ok ⟨T', he⟩ =>
        match isDefEq.{u,v} fuel entries [] T' T with
        | .error failure => .error (Error.ofSearch what failure)
        | .ok ⟨hc⟩ => .ok ⟨he.convF hT.formed hc⟩

/-- Check a claim for every element of a list. -/
private def checkEach {α : Type w} {P : α → Prop} (check : (x : α) → Except Error (CheckedClaim.{u} (P x))) :
    (xs : List α) → Except Error (CheckedClaim.{u} (∀ x ∈ xs, P x))
  | [] => .ok ⟨by simp⟩
  | x :: xs => do
    let ⟨hx⟩ ← check x
    let ⟨hxs⟩ ← checkEach check xs
    return ⟨by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hxs y hy⟩

theorem Model.Revalued.Claims.ofReductionView (env : Env β) {σ : ConstRef β → Option (AExpr β)}
    {b : Revalued β} (h : Revalued.Claims.{u,v} env.reductionView σ b) :
    Revalued.Claims.{u,v} env.toEnvironment σ b where
  closed := h.closed
  body := h.body
  typed := TypingClaim.ofReductionView env h.typed
  equations := fun q hq =>
    let ⟨hc, hl, hr⟩ := h.equations q hq
    ⟨ConvClaim.ofReductionView env hc, FormedClaim.ofReductionView env hl,
      FormedClaim.ofReductionView env hr⟩
  facts := fun fact hf =>
    match h.facts fact hf with
    | .inl ha => .inl ha
    | .inr ⟨e, T, he, ht⟩ => .inr ⟨e, T, he, TypingClaim.ofReductionView env ht⟩

/-- What the kernel checks of one revalued entry, against the reduction view. -/
private def checkRevalued (fuel : Nat) (view : Environment β) (σ : ConstRef β → Option (AExpr β))
    (b : Revalued β) : Except Error (CheckedClaim.{u} (Revalued.Claims.{u,v} view σ b)) := do
  if hs : b.term.Scope b.entry.universes 0 then
    if hbody : b.entry.body = none then
      let what := if b.entry.equations.isEmpty then "interleaved: constructor wrapper"
        else "interleaved: recursor wrapper"
      let ⟨ht⟩ ← checkClosedTyping.{u,v} fuel view what b.term (b.entry.type.substConsts σ)
      let ⟨heq⟩ ← checkEach (P := fun q : ConstantEquation β =>
          ConvClaim.{u,v} view [] (q.lhs.substConsts σ) (q.rhs.substConsts σ) ∧
            FormedClaim.{u,v} view [] (q.lhs.substConsts σ) ∧ FormedClaim.{u,v} view [] (q.rhs.substConsts σ))
        (fun q => do
          let ⟨_, hl⟩ ← (inferA.{u,v} fuel view [] (q.lhs.substConsts σ)).mapError
            (Error.ofSearch "interleaved: rule")
          let ⟨_, hr⟩ ← (inferA.{u,v} fuel view [] (q.rhs.substConsts σ)).mapError
            (Error.ofSearch "interleaved: rule")
          let ⟨hc⟩ ← (isDefEq.{u,v} fuel view [] (q.lhs.substConsts σ) (q.rhs.substConsts σ)).mapError
            (Error.ofSearch "interleaved: rule conversion")
          return ⟨⟨hc, hl.formed, hr.formed⟩⟩) b.entry.equations
      let ⟨hf⟩ ← checkEach (P := fun fact : ConstantFact β => fact.Arity ∨
          ∃ e T, fact = .typed e T ∧ TypingClaim.{u,v} view [] (e.substConsts σ) (T.substConsts σ))
        (fun fact => match fact with
          | .typed e T => do
            let ⟨h⟩ ← checkClosedTyping.{u,v} fuel view "interleaved: rule type" (e.substConsts σ) (T.substConsts σ)
            return ⟨.inr ⟨e, T, rfl, h⟩⟩
          | fact => if h : fact.Arity then pure ⟨.inl h⟩
            else throw (.declined "interleaved: unexpected fact")) b.entry.facts
      return ⟨⟨hs, hbody, ht, heq, hf⟩⟩
    else throw (.declined "interleaved: a supplied entry has a body")
  else throw (.declined "interleaved: a wrapper is not closed")

/-- A revalued entry's scopes and references, decided. -/
private def checkFormed (after : Environment β) (b : Revalued β) :
    Except Error (CheckedClaim.{u} (Revalued.Formed after b)) :=
  if h : b.entry.type.Scope b.entry.universes 0 ∧ b.entry.type.ReferencesIn after ∧ b.entry.body = none ∧
      (∀ q ∈ b.entry.equations, q.lhs.Scope b.entry.universes 0 ∧ q.rhs.Scope b.entry.universes 0) ∧
      (∀ q ∈ b.entry.equations, q.lhs.ReferencesIn after ∧ q.rhs.ReferencesIn after) ∧
      (∀ fact ∈ b.entry.facts, fact.Scope b.entry.universes) ∧
      (∀ fact ∈ b.entry.facts, fact.ReferencesIn after) then
    .ok ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩⟩
  else .error (.rejected "interleaved: a supplied entry is not closed or mentions an uninstalled constant")

instance {c : Const β} {entry : ConstantEntry β} : Decidable (c.TypeBodyReads entry) := by
  unfold Const.TypeBodyReads; cases c <;> infer_instance

instance {c : Ctor β} {entry : ConstantEntry β} : Decidable (c.TypeReads entry) := by
  unfold Ctor.TypeReads; infer_instance

/-- Decide constructor `j`'s installed reading. -/
private def decideCtorReads (ctors : List (Ctor β)) (source : β) (entries : Environment β) (j : Nat) :
    Except Error (CheckedClaim.{u} (∀ ctor, ctors[j]? = some ctor →
      ∃ entry, entries (.ctor source 0 j) = some entry ∧ ctor.TypeReads entry)) :=
  match hcj : ctors[j]? with
  | none => .ok ⟨fun _ h => by cases h⟩
  | some ctor =>
    match entries (.ctor source 0 j) with
    | none => .error (.declined "interleaved: a constructor is not installed")
    | some e =>
      if ht : ctor.TypeReads e then
        .ok ⟨fun ctor' h => by cases h; exact ⟨e, rfl, ht⟩⟩
      else .error (.declined "interleaved: a constructor's installed type differs")

/-- Decide a family's installed reading. -/
private def decideFamilyInstalled (c : Const β) (source : β) (entries : Environment β) :
    Except Error (CheckedClaim.{u} (c.Installed source 0 entries)) :=
  match c with
  | .induct uvars _ _ type ctors _ =>
    match hf : entries (.member source 0) with
    | none => .error (.declined "interleaved: the family is not installed")
    | some fe =>
      if hr : fe.universes = uvars ∧ fe.type.erase = type ∧ fe.body = none then do
        let ⟨hc⟩ ← checkEach (decideCtorReads ctors source entries) (List.range ctors.length)
        return ⟨⟨⟨fe, hf, hr⟩, fun j ctor h =>
          hc j (List.mem_range.mpr (List.getElem?_eq_some_iff.mp h).1) ctor h⟩⟩
      else .error (.declined "interleaved: the family's installed type differs")
  | _ => .error (.declined "interleaved: not an inductive family")

/-- Decide a recursor's installed reading. -/
private def decideRecursorReads (rec : Const β) (recursor : ConstRef β) (entries : Environment β) :
    Except Error (CheckedClaim.{u} (∃ entry, entries recursor = some entry ∧ rec.TypeBodyReads entry)) :=
  match entries recursor with
  | none => .error (.declined "interleaved: the recursor is not installed")
  | some e =>
    if h : rec.TypeBodyReads e then .ok ⟨⟨e, rfl, h⟩⟩
    else .error (.declined "interleaved: the recursor's installed type differs")


theorem Model.Revalued.find_isSome {block : List (Revalued β)} {b : Revalued β} (hb : b ∈ block) :
    (Revalued.find block b.ref).isSome := by
  unfold Revalued.find
  exact List.find?_isSome.mpr ⟨b, hb, by simp⟩

omit [DecidableEq β] in
theorem Model.Environment.WF.references_installed {entries : Environment β} (hE : entries.WF)
    {q : ConstRef β} {entry : ConstantEntry β} (hq : entries q = some entry) :
    ∀ r ∈ entry.references, (entries r).isSome := by
  intro r hr
  simp only [ConstantEntry.references, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ((hr | hr) | ⟨law, hl, hr⟩) | ⟨fact, hf, hr⟩
  · exact hE.typeReferences q entry hq r hr
  · cases hb : entry.body with
    | none => simp [hb] at hr
    | some body =>
      simp only [hb, Option.map_some, Option.getD_some] at hr
      exact hE.bodyReferences q entry hq body hb r hr
  · rcases hr with hr | hr
    · exact (hE.equationReferences q entry hq law hl).1 r hr
    · exact (hE.equationReferences q entry hq law hl).2 r hr
  · exact hE.factReferences q entry hq fact hf r hr

/-- Admit a family whose constructors interleave ordinary and recursive fields
(see the section note). -/
private def checkInterleavedC (cfg : Config) (env : Env β) (source : β) (recursor : ConstRef β)
    (family rec : Const β) : Except Error { env' : Env β //
      AdmissionClaim.{u,v} env env' ∧ family.Installed source 0 env'.toEnvironment ∧
        ∃ entry, env'.toEnvironment recursor = some entry ∧ rec.TypeBodyReads entry } := do
  let entries := env.toEnvironment
  let reading ← (readInterleavedBlock.{u,v} cfg.fuel entries source ⟨[family, rec]⟩).mapError fun
    | .noMatch => .declined "the inductive and recursor are not in the ordinary shape class"
    | failure => Error.ofSearch "inductive reading" failure
  let shape := reading.reading.shape
  let mode := reading.reading.mode
  if reading.reading.k then throw (.declined "interleaved: K-like reduction is not supported")
  match family, rec with
  | .induct fu fnp fni _ ctors .safe, .recursor ru _ _ _ _ rtype rules _ .safe =>
    let ⟨hb⟩ ← (checkBlock.{u,v} cfg.fuel entries source shape mode recursor).mapError
      (Error.ofSearch "inductive block (interleaved)")
    let installed := installOrdinary env source shape mode hb
    let env' := installed.val
    let view := env'.reductionView
    -- The supplied types and rules, read over the canonical block.
    let ctorTypes ← ctors.mapM fun c =>
      (annotate.{u,v} cfg.fuel view [] c.type).mapError (Error.ofSearch "constructor type")
    -- The recursor's type and rules mention the declared constructors (and the
    -- rules the declared recursor): annotate them where those have their
    -- supplied types. Annotation only proposes binder data; every term is
    -- checked against the canonical block below.
    let declared := env'.pushList (ctorTypes.zipIdx.map fun (T, j) => (.ctor source 0 j, ⟨fu, T, none, [], []⟩))
    let recType ← (annotate.{u,v} cfg.fuel declared.reductionView [] rtype).mapError
      (Error.ofSearch "recursor type (interleaved)")
    let withRec := declared.push recursor ⟨ru, recType, none, [], []⟩
    let rhss ← rules.mapM fun r =>
      (annotate.{u,v} cfg.fuel withRec.reductionView [] r.rhs).mapError (Error.ofSearch "recursor rule (interleaved)")
    let nminors := ctors.length
    let some ctorTerms := ((ctorTypes.zip reading.positions).zipIdx.mapM fun ((T, pos), j) =>
        ctorWrapper source j fu fnp pos T)
      | throw (.declined "interleaved: a constructor wrapper could not be built")
    let info := (shape.constructors.zip reading.positions).map fun (c, pos) => (c.recursive.length, pos)
    let ctorBlock : List (Revalued β) :=
      (ctorTypes.zip ctorTerms).zipIdx.map fun ((T, W), j) => ⟨.ctor source 0 j, ⟨fu, T, none, [], []⟩, W⟩
    -- The wrapper's binders take the recursor type's domains over the canonical
    -- block: the declared constructors replaced by their wrappers.
    let some recTerm := recWrapper recursor ru fnp nminors fni (shape.recursorType source mode) info
        (recType.substConsts (Revalued.valuation ctorBlock))
      | throw (.declined "interleaved: the recursor wrapper could not be built")
    let some built := ((ctorTypes.zip (rules.zip rhss)).zipIdx.mapM fun ((T, (r, rhs)), j) =>
        declaredRule source recursor mode fu ru fnp nminors j recType T r.nfields rhs)
      | throw (.declined "interleaved: a rule could not be built")
    let recEntry : ConstantEntry β := ⟨ru, recType, none, built.map (·.1),
      shape.recursorFact source :: built.flatMap fun (law, ty) => [.typed law.lhs ty, .typed law.rhs ty]⟩
    let block : List (Revalued β) := ctorBlock ++ [⟨recursor, recEntry, recTerm⟩]
    let σ := Revalued.valuation block
    let ⟨hclaims⟩ ← checkEach (checkRevalued.{u,v} cfg.fuel view σ) block
    let after := Revalued.environment block env'.toEnvironment
    let ⟨hformed⟩ ← checkEach (checkFormed after) block
    -- The block's references are fresh before it and cover the canonical block.
    let famEnv := shape.familyEnvironment entries source
    if hfresh : ∀ b ∈ block, famEnv b.ref = none then
    if hrec : (Revalued.find block recursor).isSome then
    if hctors : ∀ i ∈ List.range shape.constructors.length, (Revalued.find block (.ctor source 0 i)).isSome then
      let env'' := env'.pushList (block.map fun b => (b.ref, b.entry))
      have henv'' : env''.toEnvironment = after := by
        funext q
        rw [Env.toEnvironment_pushList, List.find?_map]
        have hp : ((fun e : ConstRef β × ConstantEntry β => e.1 == q) ∘ fun b : Revalued β => (b.ref, b.entry)) =
            fun b => decide (b.ref = q) := by
          funext b; rfl
        rw [hp]
        simp only [after, Revalued.environment, Revalued.find]
        cases block.find? (fun b => decide (b.ref = q)) <;> rfl
      have henv' : env'.toEnvironment = shape.publishedEnvironment entries source mode recursor :=
        Shape.toEnvironment_installed env shape source mode recursor
      have hstep : StepClaim.{u,v} env env'' := fun V _ m => by
        obtain ⟨m'⟩ := installed.property.step V m
        have hE := m.wf
        have hfamWF : famEnv.WF := Shape.familyEnvironment_wf hb.shapeChecked hE
        have hkeep : ∀ q entry, env'.toEnvironment q = some entry → Revalued.find block q = none →
            ∀ r ∈ entry.references, Revalued.find block r = none := by
          intro q entry hq hn r hr
          -- `q` is outside the block, so its entry is the family stage's.
          have hq' : famEnv q = some entry := by
            rw [henv'] at hq
            have hqr : q ≠ recursor := fun h => by rw [h] at hn; simp [hn] at hrec
            have hctor : shape.constructorEntries source q = none := by
              cases he : shape.constructorEntries source q with
              | none => rfl
              | some e =>
                obtain ⟨i, ctor, rfl, hc, _⟩ := Shape.constructorEntries_some he
                have := hctors i (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hc).1)
                simp [hn] at this
            simpa [Shape.publishedEnvironment, Shape.constructorEnvironment, Environment.insert, hqr,
              Environment.overlay, hctor, famEnv] using hq
          have hinst := hfamWF.references_installed hq' r hr
          cases hfind : Revalued.find block r with
          | none => rfl
          | some b =>
            obtain ⟨hmem, hbr⟩ := Revalued.find_ref hfind
            have := hfresh b hmem
            rw [hbr] at this
            simp [this] at hinst
        have hc' := fun b hb => (hclaims b hb).ofReductionView env'
        refine ⟨⟨m'.constants.revalue σ, ?_, ?_⟩⟩
        · rw [henv'']; exact Revalued.realizes m'.wf m'.realizes hkeep hc'
        · rw [henv'']; exact Revalued.wf m'.wf hkeep hformed
      have hpres : env.Preserves env'' := fun q e hq => by
        have hq' := installed.property.preserves q e hq
        rw [henv'']
        simp only [after, Revalued.environment]
        cases hfind : Revalued.find block q with
        | none => simpa using hq'
        | some b =>
          obtain ⟨hmem, hbr⟩ := Revalued.find_ref hfind
          have hf := hfresh b hmem
          rw [hbr] at hf
          have : famEnv q = some e := by
            have hqf : q ≠ .member source 0 := by
              intro h
              have h0 : env.toEnvironment (.member source 0) = none :=
                hb.shapeChecked.fresh _ (List.mem_cons_self ..)
              rw [h, h0] at hq
              cases hq
            simp only [famEnv, Shape.familyEnvironment, Environment.insert, hqf, ↓reduceIte]
            exact hq
          simp [this] at hf
      let ⟨hfam⟩ ← decideFamilyInstalled family source env''.toEnvironment
      let ⟨hrecReads⟩ ← decideRecursorReads rec recursor env''.toEnvironment
      return ⟨env'', ⟨hstep, hpres⟩, hfam, hrecReads⟩
    else throw (.declined "interleaved: a canonical constructor is not in the block")
    else throw (.declined "interleaved: the recursor is not in the block")
    else throw (.rejected "interleaved: a block reference is not fresh")
  | _, _ => throw (.declined "the inductive and recursor are not in the ordinary shape class")

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
    | .error .noMatch =>
      -- Ordinary fields after recursive ones: the canonical block and wrappers.
      checkInterleavedC.{u,v} cfg env source recursor family rec
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
def checkDeclC (cfg : Config) (env : Env β) (d : Decl β) (height? : Option Nat := none) :
    Except Error { env' : Env β // AdmissionClaim.{u,v} env env' ∧
      d.block.Installed d.address env'.toEnvironment } :=
  match hm : d.block.members with
  | [.defn universes kind type body .safe] =>
    let r : ConstRef β := .member d.address 0
    let entries := env.toEnvironment
    -- Inference and conversion read the reduction view: theorem and opaque
    -- bodies are not unfolded (`TypingClaim.ofReductionView`).
    let view := env.reductionView
    if fresh : entries r = none then
      if !(type.refs ++ body.refs).all (fun q => (entries q).isSome) then
        .error (.rejected "the declaration references a constant that is not installed")
      else
      match hTypeReading : annotate.{u,v} cfg.fuel view [] type,
          hBodyReading : annotate.{u,v} cfg.fuel view [] body with
      | .ok type', .ok body' =>
        if hTs : type'.Scope universes 0 then
          if hBs : body'.Scope universes 0 then
            if hTr : type'.ReferencesIn entries then
              if hBr : body'.ReferencesIn entries then
                match inferA.{u,v} cfg.fuel view [] type' with
                | .ok ⟨S, hS⟩ =>
                  match sortOf (whnf.{u,v} cfg.fuel view [] S) hS with
                  | .ok ⟨l, hT⟩ =>
                    if kind = .theorem && !levelIsZero l then
                      if zeroCondition l = .never then
                        .error (.rejected "the type of a theorem must be a proposition")
                      else
                        .error (.declined "the theorem's type was not established to be a proposition")
                    else
                      match inferA.{u,v} cfg.fuel view [] body' with
                      | .ok ⟨B, hb⟩ =>
                        match isDefEq.{u,v} cfg.fuel view [] B type' with
                        | .ok ⟨hc⟩ =>
                          -- The supplied height (Lean's reducibility hint) or a computed one.
                          let height := height?.getD (definitionHeight entries body')
                          let installed := installDefinition env r universes type' body' height
                            (kind != .definition) fresh hTs hBs hTr hBr
                            (TypingClaim.ofReductionView env hT)
                            (TypingClaim.ofReductionView env (hb.convF hT.formed hc))
                          let entry : ConstantEntry β := ⟨universes, type', some body', [], [.height height]⟩
                          -- A definition computing a numeric operation publishes it.
                          let final : { env'' : Env β // AdmissionClaim.{u,v} env env'' ∧
                              ∃ facts, env''.toEnvironment =
                                (env.push r { entry with facts }).toEnvironment } :=
                            if hu : universes = 0 ∧ kind = .definition then
                              match Arithmetic.certify.{u,v} cfg.fuel env.natOps
                                  installed.val.reductionView r type' with
                              | some checked =>
                                if hrefs : checked.fact.ReferencesIn installed.val.toEnvironment then
                                  let published := publishArithmetic env installed.val r entry fresh
                                    installed.property.1 installed.property.2 hu.1 checked hrefs
                                  ⟨published.val, published.property.1, _, published.property.2⟩
                                else ⟨installed.val, installed.property.1, entry.facts, installed.property.2⟩
                              | none => ⟨installed.val, installed.property.1, entry.facts, installed.property.2⟩
                            else ⟨installed.val, installed.property.1, entry.facts, installed.property.2⟩
                          acceptInstalled env d ⟨final.val, final.property.1⟩ (by
                              have hblock : d.block = ⟨[.defn universes kind type body .safe]⟩ :=
                                congrArg Block.mk hm
                              rw [hblock]
                              show Block.Installed _ _ final.val.toEnvironment
                              obtain ⟨facts, hfinal⟩ := final.property.2
                              rw [hfinal]
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

/-- Check one declaration against the environment. `height?` is the definition's unfolding height, a
conversion hint (e.g. from Lean's reducibility hints); it affects only the
order of conversion steps. -/
def checkDecl (cfg : Config) (env : Env β) (d : Decl β) (height? : Option Nat := none) :
    Except Error (Env β) :=
  (checkDeclC.{u,v} cfg env d height?).map Subtype.val

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
