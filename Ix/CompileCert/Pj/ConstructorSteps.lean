import Ix.CompileCert.Pj.RecursiveIndices
import Ix.CompileCert.Pj.RecTeleSyntax
import IxC.Kernel.Verify.InferLemmas

/-! The actual minor conclusion's motive application. This intermediate
semantic bridge derives argument typing from the typed motive tuple and
the graded installed minor. The result-index count is an internal reader
obligation; this file does not add it to the promised final theorem.
Constructor-step/IH construction and the installed/source header adapter
remain separate required work. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- Select the actual dependent domain and member from a typed tuple.
Only the preceding arguments extend the valuation at this position. -/
theorem TeleTyped.domain_at {ρ : Nat → V} {ts : List Kernel.Expr} {xs : List V}
    (typed : TeleTyped cval env φ ρ ts xs) (i : Nat) (bound : i < xs.length) :
    ∃ A, Kernel.Denotes cval env φ (pushArguments ρ (xs.take i))
      (ts.getD i default) A ∧ xs[i] ∈ˢ A := by
  induction typed generalizing i with
  | nil => simp at bound
  | @cons ρ t ts x xs A domain member rest ih =>
    cases i with
    | zero =>
      refine ⟨A, ?_, ?_⟩
      · simpa only [List.take_zero, pushArguments, List.getD_cons_zero] using domain
      · simpa only [List.getElem_cons_zero] using member
    | succ i =>
      have inside : i < xs.length := Nat.lt_of_succ_lt_succ bound
      obtain ⟨B, reading, value⟩ := ih i inside
      refine ⟨B, ?_, ?_⟩
      · simpa only [List.take_succ_cons, pushArguments, List.getD_cons_succ] using reading
      · simpa only [List.getElem_cons_succ] using value

/-- A selected value in the actual motive-binder tuple inhabits the original
motive domain. Removing earlier motives uses the existing valuation-lift
theorem, retaining arbitrary parameter valuations and universe assignments. -/
theorem RecRd.motive_value_typed (R : RecRd) (ρ : Nat → V) (motives : List V)
    (typed : TeleTyped cval env φ ρ (R.motiveBinders.map Prod.fst) motives)
    (j : Nat) (bound : j < motives.length) :
    ∃ A, Kernel.Denotes cval env φ ρ
      ((R.motives.getD j default).type R.np) A ∧ motives[j] ∈ˢ A := by
  have length : motives.length = R.motives.length := by
    simpa only [RecRd.motiveBinders, List.length_map, List.length_mapIdx] using typed.length
  have sourceBound : j < R.motives.length := by omega
  have atIndex : (R.motiveBinders.map Prod.fst).getD j default =
      ((R.motives.getD j default).type R.np).liftLooseBVars j 0 := by
    simp only [RecRd.motiveBinders, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_mapIdx, List.getElem?_eq_getElem sourceBound,
      Option.map_some, Option.getD_some]
  have takeLength : (motives.take j).length = j := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  obtain ⟨A, domain, member⟩ := typed.domain_at j bound
  have lifted : Kernel.Denotes cval env φ (pushArguments ρ (motives.take j))
      (((R.motives.getD j default).type R.np).liftLooseBVars (motives.take j).length 0) A := by
    simpa only [atIndex, takeLength] using domain
  exact ⟨A, denotes_unlift (motives.take j).length _
    (valuationLift_prefix ρ (motives.take j)) lifted, member⟩

/-- The exact head and argument list already used by `MinorRd.concl`.
These abbreviations expose that application without changing its builder. -/
def MinorRd.conclusionHead (n : MinorRd) (nm : Nat) : Kernel.Expr :=
  .bvar (n.recFields.length + n.fields.length + (nm - 1 - n.motive))

def MinorRd.conclusionArguments (n : MinorRd) (np nm : Nat) : List Kernel.Expr :=
  n.resIdx.map (fun e => (e.liftLooseBVars nm n.fields.length).liftLooseBVars
    n.recFields.length 0) ++
  [Kernel.Expr.mkAppN (.const n.ctor n.ctorUs)
    (bvarsAt np (n.recFields.length + n.fields.length + nm) ++
      bvarsAt n.fields.length n.recFields.length)]

/-- Reconstruct each argument reading of the actual minor conclusion.
The original constructor-context indices are transported across the inserted
motives and IHs; the constructor receives the original parameter/field tuple. -/
theorem MinorRd.conclusion_spine (n : MinorRd) (np nm : Nat) (ρ : Nat → V)
    (params motives fields hypotheses indices : List V) (constructor : V)
    (paramLength : params.length = np)
    (motiveLength : motives.length = nm)
    (fieldLength : fields.length = n.fields.length)
    (hypothesisLength : hypotheses.length = n.recFields.length)
    (motiveBound : n.motive < motives.length)
    (indexRead : DenotesSpine cval env φ (pushArguments ρ (params ++ fields))
      n.resIdx indices)
    (constructorRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (.const n.ctor n.ctorUs) constructor) :
    Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (n.conclusionHead nm) motives[n.motive] ∧
    DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (n.conclusionArguments np nm)
      (indices ++ [(params ++ fields).foldl app constructor]) := by
  have position : (fields ++ hypotheses).length + (motives.length - 1 - n.motive) =
      n.recFields.length + n.fields.length + (nm - 1 - n.motive) := by
    simp only [List.length_append, motiveLength, fieldLength, hypothesisLength]
    omega
  have headRead := denotes_bvar_segment (cval := cval) (env := env) (φ := φ)
    ρ params motives (fields ++ hypotheses) n.motive motiveBound
  rw [position] at headRead
  have lifted := denotesSpine_lift
    (denotesSpine_lift indexRead (valuationLift_middle ρ params motives fields))
    (valuationLift_prefix (pushArguments ρ (params ++ motives ++ fields)) hypotheses)
  have indicesRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (n.resIdx.map (fun e =>
        (e.liftLooseBVars nm n.fields.length).liftLooseBVars n.recFields.length 0))
      indices := by
    simpa only [List.map_map, Function.comp_def, motiveLength, fieldLength,
      hypothesisLength, Ix.CompileCert.pushArguments_append] using lifted
  have paramsRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (bvarsAt np (n.recFields.length + n.fields.length + nm)) params := by
    have offset : n.recFields.length + n.fields.length + nm =
        (motives ++ fields ++ hypotheses).length := by
      simp only [List.length_append, motiveLength, fieldLength, hypothesisLength]
      omega
    rw [offset, ← paramLength]
    simpa only [List.append_assoc] using
      (denotesSpine_bvarsAt (cval := cval) (env := env) (φ := φ)
        ρ params (motives ++ fields ++ hypotheses))
  have fieldsRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses))
      (bvarsAt n.fields.length n.recFields.length) fields := by
    simpa only [fieldLength, hypothesisLength] using
      (denotesSpine_bvarsAt_middle (cval := cval) (env := env) (φ := φ)
        ρ (params ++ motives) fields hypotheses)
  refine ⟨?_, ?_⟩
  · simpa only [MinorRd.conclusionHead, List.append_assoc] using headRead
  · exact indicesRead.append (.cons
      (Ix.CompileCert.denotes_mkAppN constructorRead (paramsRead.append fieldsRead)) .nil)

/-- The actual graded minor conclusion applies its selected motive to a
tuple in that motive's original dependent telescope. The result-index count
is the finite block reader's internal saturation projection, not an inference
from the bare old Check or an added final induction premise. -/
theorem RecRd.minor_arguments_typed {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params motives fields hypotheses : List V)
    (paramsTyped : TeleTyped strong.public.cval env φ ρ (R.params.map Prod.fst) params)
    (motivesTyped : TeleTyped strong.public.cval env φ (pushArguments ρ params)
      (R.motiveBinders.map Prod.fst) motives)
    (n : MinorRd) (present : n ∈ R.minors)
    (fieldLength : fields.length = n.fields.length)
    (hypothesisLength : hypotheses.length = n.recFields.length)
    (indexCount : n.resIdx.length = (R.motives.getD n.motive default).idxs.length)
    (graded : Bridge.Graded strong.public.cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses)) (n.concl R.np R.nm)) :
    ∃ constructor indices,
      (∀ valuation, Kernel.Denotes strong.public.cval env φ valuation
        (.const n.ctor n.ctorUs) constructor) ∧
      DenotesSpine strong.public.cval env φ (pushArguments ρ (params ++ fields))
        n.resIdx indices ∧
      TeleTyped strong.public.cval env φ (pushArguments ρ params)
        (((R.motives.getD n.motive default).tele R.np).map Prod.fst)
        (indices ++ [(params ++ fields).foldl app constructor]) ∧
      Kernel.Denotes strong.public.cval env φ
        (pushArguments ρ (params ++ motives ++ fields ++ hypotheses)) (n.concl R.np R.nm)
        ((indices ++ [(params ++ fields).foldl app constructor]).foldl app (getElem motives n.motive (by
          have len : motives.length = R.nm := by
            simpa only [List.length_map, motiveBinders_length] using motivesTyped.length
          have own := (checked.2.2.2.2 n present).1
          simpa only [len] using own))) := by
  have paramLength : params.length = R.np := by
    simpa only [List.length_map, RecRd.np] using paramsTyped.length
  have motiveLength : motives.length = R.nm := by
    simpa only [List.length_map, motiveBinders_length] using motivesTyped.length
  have ncheck := checked.2.2.2.2 n present
  have sourceBound : n.motive < R.motives.length := ncheck.1
  have motiveBound : n.motive < motives.length := by simpa only [motiveLength] using ncheck.1
  have selectedPresent : R.motives.getD n.motive default ∈ R.motives := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem sourceBound, Option.getD_some]
    exact List.getElem_mem sourceBound
  obtain ⟨constructor, indices, constructorRead, indexRead, conclusionRead⟩ :=
    n.concl_read_of_graded R.np R.nm R.motives R.params ncheck.2.2.2.2.2
      strong φ ρ params motives fields hypotheses paramLength motiveLength
      fieldLength hypothesisLength motiveBound graded
  obtain ⟨A, motiveRead, motiveMember⟩ :=
    R.motive_value_typed (pushArguments ρ params) motives motivesTyped n.motive motiveBound
  obtain ⟨headRead, spine⟩ := n.conclusion_spine R.np R.nm ρ params motives fields hypotheses
    indices constructor paramLength motiveLength fieldLength hypothesisLength motiveBound
    indexRead (constructorRead _)
  have argumentLength : (n.conclusionArguments R.np R.nm).length =
      ((R.motives.getD n.motive default).tele R.np).length := by
    simp only [MinorRd.conclusionArguments, List.length_append, List.length_map,
      List.length_cons, List.length_nil, motive_tele_length, indexCount]
  have typed := typed_of_graded_spine
    ((R.motives.getD n.motive default).tele R.np)
    (RecRd.motive_graph checked selectedPresent)
    (f := n.conclusionHead R.nm) (args := n.conclusionArguments R.np R.nm)
    graded headRead motiveRead motiveMember spine argumentLength
  exact ⟨constructor, indices, constructorRead, indexRead, typed, conclusionRead⟩

end Ix.CompileCert.Pj

#print axioms Ix.CompileCert.Pj.TeleTyped.domain_at
#print axioms Ix.CompileCert.Pj.RecRd.motive_value_typed
#print axioms Ix.CompileCert.Pj.MinorRd.conclusion_spine
#print axioms Ix.CompileCert.Pj.RecRd.minor_arguments_typed

/-! A literal branch of the installed block-header adapter.

This file reads the actual `.indInfo` and `.ctorInfo` entries at the selected
universe instances. It retains their dependent telescope expressions and
annotations. Successful checks supply an INTERNAL minor-result saturation
lemma; their success is not a new premise of the promised compiler theorem.

REQUIRED, still open: a checked WHNF/conversion branch with same-model,
bidirectional dependent-telescope transport, and a proof that every block
produced from the original accepted-source domain reaches one of those
branches. The source proof must follow actual decomposeInductiveType,
buildMotiveType/buildMotiveTypeAux, buildMinorType, export and installation.
In particular, it must not identify the complete elimination family with
the original declaration members or replace specialized nested parameters
by the uniform prefix used in THIS branch. See README.md for exact targets.

No existing RecRd, Check, readRec, reader, model, domain or theorem is changed.
This excluded draft has not been elaborated or included in an audit. -/

namespace Ix.CompileCert.Pj.InstalledHeader

universe u

abbrev Telescope := List (Kernel.Expr × Kernel.BinderMeta)

/-- The exact instantiated member header, including all binder annotations.
The index count is obtained by peeling the stored type, not from a supplied
metadata count. This parser deliberately does not claim WHNF completeness. -/
structure Header where
  parameters : Telescope
  indices : Telescope
  sort : Kernel.Level
  deriving DecidableEq, Inhabited

def readSortTelescope : Kernel.Expr → Option (Telescope × Kernel.Level)
  | .sort s => some ([], s)
  | .forallE t body binderMeta =>
    (readSortTelescope body).map fun p => ((t, binderMeta) :: p.1, p.2)
  | _ => none

theorem readSortTelescope_sound (e : Kernel.Expr) :
    ∀ bs s, readSortTelescope e = some (bs, s) →
      e = piJoin bs (.sort s) := by
  induction e with
  | sort level =>
    intro bs s accepted
    simp only [readSortTelescope, Option.some.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    rfl
  | forallE domain body binderMeta _ ih =>
    intro bs s accepted
    cases parsed : readSortTelescope body with
    | none => simp only [readSortTelescope, parsed, Option.map_none, reduceCtorEq] at accepted
    | some p =>
      obtain ⟨tail, level⟩ := p
      simp only [readSortTelescope, parsed, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact congrArg (fun b => Kernel.Expr.forallE domain b binderMeta) (ih tail level parsed)
  | _ => intro bs s accepted; simp only [readSortTelescope, reduceCtorEq] at accepted

theorem readSortTelescope_piJoin (bs : Telescope) (s : Kernel.Level) :
    readSortTelescope (piJoin bs (.sort s)) = some (bs, s) := by
  induction bs with
  | nil => rfl
  | cons p bs ih =>
    obtain ⟨domain, binderMeta⟩ := p
    simp only [piJoin, readSortTelescope, ih, Option.map_some]

def readType (np : Nat) (e : Kernel.Expr) : Option Header :=
  match e.stripPis np with
  | none => none
  | some (parameters, body) =>
    match readSortTelescope body with
    | none => none
    | some (indices, sort) => some ⟨parameters, indices, sort⟩

theorem readType_sound {np : Nat} {e : Kernel.Expr} {h : Header}
    (accepted : readType np e = some h) :
    e = piJoin h.parameters (piJoin h.indices (.sort h.sort)) ∧
      h.parameters.length = np := by
  cases prefixRead : e.stripPis np with
  | none => simp only [readType, prefixRead, reduceCtorEq] at accepted
  | some p =>
    obtain ⟨parameters, body⟩ := p
    cases suffix : readSortTelescope body with
    | none => simp only [readType, prefixRead, suffix, reduceCtorEq] at accepted
    | some q =>
      obtain ⟨indices, sort⟩ := q
      simp only [readType, prefixRead, suffix, Option.some.injEq] at accepted
      cases accepted
      obtain ⟨typeEq, length⟩ := piJoin_of_stripPis np e parameters body prefixRead
      exact ⟨typeEq.trans (congrArg (piJoin parameters)
        (readSortTelescope_sound body indices sort suffix)), length⟩

theorem readType_piJoin (parameters indices : Telescope) (s : Kernel.Level) :
    readType parameters.length (piJoin parameters (piJoin indices (.sort s))) =
      some ⟨parameters, indices, s⟩ := by
  simp only [readType, stripPis_piJoin, readSortTelescope_piJoin]

/-- The actual environment lookup and the actual formal universe arity.
No source declaration or its universe arguments are reconstructed from a hash. -/
def read (env : Kernel.Env) (np : Nat) (m : MotiveRd) : Option Header :=
  match env.find? m.ind with
  | some (.indInfo cv _) =>
    if m.indUs.length = cv.levelParams.length then
      readType np (cv.type.instantiateLevelParams cv.levelParams m.indUs)
    else none
  | _ => none

theorem read_sound {env : Kernel.Env} {np : Nat} {m : MotiveRd} {h : Header}
    (accepted : read env np m = some h) :
    ∃ cv caps, env.find? m.ind = some (.indInfo cv caps) ∧
      m.indUs.length = cv.levelParams.length ∧
      cv.type.instantiateLevelParams cv.levelParams m.indUs =
        piJoin h.parameters (piJoin h.indices (.sort h.sort)) ∧
      h.parameters.length = np := by
  cases lookup : env.find? m.ind with
  | none => simp only [read, lookup, reduceCtorEq] at accepted
  | some ci =>
    cases ci <;> simp only [read, lookup, reduceCtorEq] at accepted
    case indInfo cv caps =>
      by_cases arity : m.indUs.length = cv.levelParams.length
      · have parsed : readType np
            (cv.type.instantiateLevelParams cv.levelParams m.indUs) = some h := by
          simpa only [arity, ↓reduceIte] using accepted
        exact ⟨cv, caps, rfl, arity, readType_sound parsed⟩
      · simp only [arity, ↓reduceIte, reduceCtorEq] at accepted

/-- Literal correspondence compares full domain expressions in their original
dependent contexts. Outer binder annotations are retained in both views;
annotations INSIDE each domain are part of the equality. -/
def matchMotive (env : Kernel.Env) (parameters : Telescope) (m : MotiveRd) :
    Option Header :=
  match read env parameters.length m with
  | none => none
  | some h =>
    if h.parameters.map Prod.fst = parameters.map Prod.fst ∧
        h.indices.map Prod.fst = m.idxs.map Prod.fst then some h else none

theorem matchMotive_sound {env : Kernel.Env} {parameters : Telescope}
    {m : MotiveRd} {h : Header} (accepted : matchMotive env parameters m = some h) :
    read env parameters.length m = some h ∧
      h.parameters.map Prod.fst = parameters.map Prod.fst ∧
      h.indices.map Prod.fst = m.idxs.map Prod.fst := by
  cases parsed : read env parameters.length m with
  | none => simp only [matchMotive, parsed, reduceCtorEq] at accepted
  | some header =>
    by_cases domains : header.parameters.map Prod.fst = parameters.map Prod.fst ∧
        header.indices.map Prod.fst = m.idxs.map Prod.fst
    · have eq : header = h := by
        simpa only [matchMotive, parsed, ite_eq_left domains, Option.some.injEq] using accepted
      subst header
      exact ⟨rfl, domains⟩
    · simp only [matchMotive, parsed, domains, ↓reduceIte, reduceCtorEq] at accepted

/-- The major telescope obtained from the actual installed member view. -/
def Header.majorTelescope (h : Header) (m : MotiveRd) : Telescope :=
  h.indices ++ [(Kernel.Expr.mkAppN (.const m.ind m.indUs)
    (bvarsAt h.parameters.length h.indices.length ++ bvarsAt h.indices.length 0), m.majMeta)]

theorem matchMotive_domains {env : Kernel.Env} {parameters : Telescope}
    {m : MotiveRd} {h : Header} (accepted : matchMotive env parameters m = some h) :
    (h.majorTelescope m).map Prod.fst = (m.tele parameters.length).map Prod.fst := by
  obtain ⟨_, params, indices⟩ := matchMotive_sound accepted
  have paramLength : h.parameters.length = parameters.length := by
    simpa only [List.length_map] using congrArg List.length params
  have indexLength : h.indices.length = m.idxs.length := by
    simpa only [List.length_map] using congrArg List.length indices
  simp only [Header.majorTelescope, MotiveRd.tele, MotiveRd.majTy,
    List.map_append, List.map_cons, List.map_nil, indices, paramLength, indexLength]

/-- Literal branch transport is an actual equality of the dependent domain
lists, so it works in both directions for arbitrary contexts and assignments. -/
theorem matchMotive_teleTyped_iff {V : Type u} [Kernel.SetTheory V]
    {cval : Kernel.Name → (Kernel.Name → Nat) → V}
    {env : Kernel.Env} {φ : Kernel.Name → Nat} {ρ : Nat → V} {arguments : List V}
    {parameters : Telescope} {m : MotiveRd} {h : Header}
    (accepted : matchMotive env parameters m = some h) :
    TeleTyped cval env φ ρ ((h.majorTelescope m).map Prod.fst) arguments ↔
      TeleTyped cval env φ ρ ((m.tele parameters.length).map Prod.fst) arguments := by
  rw [matchMotive_domains accepted]

def constructorBinders (parameters : Telescope) (motives : List MotiveRd)
    (n : MinorRd) : Telescope :=
  zipMetas (parameters.map Prod.fst) n.paramMetas ++ n.fieldTys parameters.length motives

def constructorResult (np : Nat) (motives : List MotiveRd) (n : MinorRd) : Kernel.Expr :=
  let m := motives.getD n.motive default
  Kernel.Expr.mkAppN (.const m.ind m.indUs) (bvarsAt np n.fields.length ++ n.resIdx)

theorem strip_constructorType (parameters : Telescope) (motives : List MotiveRd)
    (n : MinorRd) (metadata : n.paramMetas.length = parameters.length) :
    (n.ctorType parameters.length motives parameters).stripPis
        (parameters.length + n.fields.length) =
      some (constructorBinders parameters motives n,
        constructorResult parameters.length motives n) := by
  have length : (constructorBinders parameters motives n).length =
      parameters.length + n.fields.length := by
    simp only [constructorBinders, List.length_append,
      zipMetas_length (parameters.map Prod.fst) n.paramMetas
        (by simpa only [List.length_map] using metadata),
      List.length_map, fieldTys_length]
  have shape : n.ctorType parameters.length motives parameters =
      piJoin (constructorBinders parameters motives n)
        (constructorResult parameters.length motives n) := by
    rw [constructorBinders, piJoin_append]
    rfl
  rw [shape, ← length]
  exact stripPis_piJoin _ _

/-- Read the actual constructor residual using its OWN stored parameter and
field counts. The old CtorOk proof, not this function, connects those counts
and the entire original constructor type to the selected minor. -/
def readConstructorResidual (env : Kernel.Env) (n : MinorRd) : Option Kernel.Expr :=
  match env.find? n.ctor with
  | some (.ctorInfo cv np nf) =>
    if n.ctorUs.length = cv.levelParams.length then
      ((cv.type.instantiateLevelParams cv.levelParams n.ctorUs).stripPis (np + nf)).map Prod.snd
    else none
  | _ => none

theorem readConstructorResidual_of_CtorOk {env : Kernel.Env}
    (parameters : Telescope) (motives : List MotiveRd) (n : MinorRd)
    (checked : n.CtorOk env parameters.length motives parameters)
    (metadata : n.paramMetas.length = parameters.length) :
    readConstructorResidual env n = some (constructorResult parameters.length motives n) := by
  cases lookup : env.find? n.ctor with
  | none => simp only [MinorRd.CtorOk, lookup] at checked
  | some ci =>
    cases ci <;> simp only [MinorRd.CtorOk, lookup] at checked
    case ctorInfo cv np nf =>
      obtain ⟨npEq, nfEq, arity, typeEq⟩ := checked
      simp only [readConstructorResidual, lookup, ite_eq_left arity, typeEq, npEq, nfEq,
        strip_constructorType parameters motives n metadata, Option.map_some]

/-- Check ownership, exact parameter prefix, and complete application arity
of the actual constructor residual against the actual member header. This
does not infer arity from semantic grading or from a metadata count. -/
def checkMinorResult (env : Kernel.Env) (parameters : Telescope)
    (motives : List MotiveRd) (n : MinorRd) : Bool :=
  if n.motive < motives.length then
    let m := motives.getD n.motive default
    match matchMotive env parameters m, readConstructorResidual env n with
    | some h, some result =>
      decide (result.getAppFn = .const m.ind m.indUs ∧
        result.getAppArgs.take parameters.length = bvarsAt parameters.length n.fields.length ∧
        result.getAppArgs.length = parameters.length + h.indices.length)
    | _, _ => false
  else false

theorem checkMinorResult_index_count {env : Kernel.Env}
    (parameters : Telescope) (motives : List MotiveRd) (n : MinorRd)
    (checked : n.CtorOk env parameters.length motives parameters)
    (metadata : n.paramMetas.length = parameters.length)
    (accepted : checkMinorResult env parameters motives n = true) :
    n.motive < motives.length ∧
      n.resIdx.length = (motives.getD n.motive default).idxs.length := by
  have residual := readConstructorResidual_of_CtorOk parameters motives n checked metadata
  by_cases bound : n.motive < motives.length
  · cases header : matchMotive env parameters (motives.getD n.motive default) with
    | none => simp only [checkMinorResult, bound, ↓reduceIte, header, residual,
        Bool.false_eq_true] at accepted
    | some h =>
      have saturation := of_decide_eq_true (show decide
          ((constructorResult parameters.length motives n).getAppFn =
              .const (motives.getD n.motive default).ind (motives.getD n.motive default).indUs ∧
            (constructorResult parameters.length motives n).getAppArgs.take parameters.length =
              bvarsAt parameters.length n.fields.length ∧
            (constructorResult parameters.length motives n).getAppArgs.length =
              parameters.length + h.indices.length) = true by
        simpa only [checkMinorResult, bound, ↓reduceIte, header, residual] using accepted)
      have indexLength : h.indices.length = (motives.getD n.motive default).idxs.length := by
        simpa only [List.length_map] using
          congrArg List.length (matchMotive_sound header).2.2
      have totalLength : parameters.length + n.resIdx.length =
          parameters.length + h.indices.length := by
        simpa only [constructorResult, Kernel.Expr.getAppArgs_mkAppN,
          Kernel.Expr.getAppArgs, List.nil_append, List.length_append,
          bvarsAt, List.length_map, List.length_range] using saturation.2.2
      exact ⟨bound, (Nat.add_left_cancel totalLength).trans indexLength⟩
  · simp only [checkMinorResult, bound, ↓reduceIte, Bool.false_eq_true] at accepted

/-- The existing full Check supplies constructor reconstruction and metadata
lengths. Only the new actual-header branch supplies the missing saturation.
This is an internal reader lemma, not the final induction theorem. -/
theorem RecRd.minor_index_count_of_literal_header {env : Kernel.Env}
    {r : Kernel.Name} {R : Ix.CompileCert.Pj.RecRd} (checked : R.Check env r)
    (n : MinorRd) (present : n ∈ R.minors)
    (accepted : checkMinorResult env R.params R.motives n = true) :
    n.resIdx.length = (R.motives.getD n.motive default).idxs.length := by
  have minor := checked.2.2.2.2 n present
  exact (checkMinorResult_index_count R.params R.motives n minor.2.2.2.2.2
    minor.2.1 accepted).2

end Ix.CompileCert.Pj.InstalledHeader

#print axioms Ix.CompileCert.Pj.InstalledHeader.readSortTelescope_sound
#print axioms Ix.CompileCert.Pj.InstalledHeader.readSortTelescope_piJoin
#print axioms Ix.CompileCert.Pj.InstalledHeader.readType_sound
#print axioms Ix.CompileCert.Pj.InstalledHeader.readType_piJoin
#print axioms Ix.CompileCert.Pj.InstalledHeader.read_sound
#print axioms Ix.CompileCert.Pj.InstalledHeader.matchMotive_sound
#print axioms Ix.CompileCert.Pj.InstalledHeader.matchMotive_domains
#print axioms Ix.CompileCert.Pj.InstalledHeader.matchMotive_teleTyped_iff
#print axioms Ix.CompileCert.Pj.InstalledHeader.strip_constructorType
#print axioms Ix.CompileCert.Pj.InstalledHeader.readConstructorResidual_of_CtorOk
#print axioms Ix.CompileCert.Pj.InstalledHeader.checkMinorResult_index_count
#print axioms Ix.CompileCert.Pj.InstalledHeader.RecRd.minor_index_count_of_literal_header

/-! Excluded composition of two UNCOMPILED drafts. `MinorApplication.lean`
is the unchanged queued four-root dependency (SHA 051eb3cf...). This theorem
replaces that helper's free internal `indexCount` argument with the successful
literal installed-header check; it does NOT add reader success to the original
accepted-source endpoint or prove constructor-step/minor inhabitation. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

/-- Application typing obtained from the actual installed member/constructor
header branch. The accepted-source proof must establish this branch or the
still-required general WHNF branch; callers of the final theorem will not
receive a new index-count or literal-syntax obligation. -/
theorem RecRd.minor_arguments_typed_of_literal_header
    {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env} {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params motives fields hypotheses : List V)
    (paramsTyped : TeleTyped strong.public.cval env φ ρ (R.params.map Prod.fst) params)
    (motivesTyped : TeleTyped strong.public.cval env φ (pushArguments ρ params)
      (R.motiveBinders.map Prod.fst) motives)
    (n : MinorRd) (present : n ∈ R.minors)
    (fieldLength : fields.length = n.fields.length)
    (hypothesisLength : hypotheses.length = n.recFields.length)
    (header : InstalledHeader.checkMinorResult env R.params R.motives n = true)
    (graded : Bridge.Graded strong.public.cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses)) (n.concl R.np R.nm)) :
    ∃ constructor indices,
      (∀ valuation, Kernel.Denotes strong.public.cval env φ valuation
        (.const n.ctor n.ctorUs) constructor) ∧
      DenotesSpine strong.public.cval env φ (pushArguments ρ (params ++ fields))
        n.resIdx indices ∧
      TeleTyped strong.public.cval env φ (pushArguments ρ params)
        (((R.motives.getD n.motive default).tele R.np).map Prod.fst)
        (indices ++ [(params ++ fields).foldl app constructor]) ∧
      Kernel.Denotes strong.public.cval env φ
        (pushArguments ρ (params ++ motives ++ fields ++ hypotheses)) (n.concl R.np R.nm)
        ((indices ++ [(params ++ fields).foldl app constructor]).foldl app (getElem motives n.motive (by
          have len : motives.length = R.nm := by
            simpa only [List.length_map, motiveBinders_length] using motivesTyped.length
          have own := (checked.2.2.2.2 n present).1
          simpa only [len] using own))) := by
  exact R.minor_arguments_typed checked strong φ ρ params motives fields hypotheses
    paramsTyped motivesTyped n present fieldLength hypothesisLength
    (InstalledHeader.RecRd.minor_index_count_of_literal_header checked n present header) graded

end Ix.CompileCert.Pj

#print axioms Ix.CompileCert.Pj.RecRd.minor_arguments_typed_of_literal_header

