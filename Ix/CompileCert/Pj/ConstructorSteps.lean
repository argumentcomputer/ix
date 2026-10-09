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


/-! Internal semantic construction of the actual minor and IH telescopes.

This leaf depends on the exact accepted Pj17 V3 module. The original source
domain and final induction theorem are unchanged. The recursive saturation
condition and successful literal header branch below are INTERNAL obligations:
accepted-source/WHNF completeness and the original constructor-step adapter
must still discharge them. These statements do not claim that old Check alone
implies either condition. This fresh /tmp draft has not been elaborated. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- Reinsert precisely the two segments used by the actual IH builder.
The original dependent argument tuple is retained; no closedness or graph
regime condition is imposed on the recursive field's own telescope. -/
theorem MinorRd.ih_arguments_lift (n : MinorRd) (nm : Nat)
    (ys : List (Kernel.Expr × Kernel.BinderMeta)) (ρ : Nat → V)
    (params motives before after hypotheses arguments : List V)
    (motiveLength : motives.length = nm)
    (fieldLength : (before ++ after).length = n.fields.length)
    (typed : TeleTyped cval env φ (pushArguments ρ (params ++ before))
      (ys.map Prod.fst) arguments) :
    TeleTyped cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ after ++ hypotheses))
      ((liftTele (n.fields.length - before.length + hypotheses.length) 0
        (liftTele nm before.length ys)).map Prod.fst) arguments := by
  have shift : n.fields.length - before.length + hypotheses.length =
      (after ++ hypotheses).length := by
    simp only [List.length_append] at fieldLength ⊢
    omega
  have first := typed.lift (valuationLift_middle ρ params motives before)
  have second := first.lift
    (valuationLift_prefix (pushArguments ρ (params ++ motives ++ before))
      (after ++ hypotheses))
  simpa only [liftTele_types, shift, motiveLength,
    Ix.CompileCert.pushArguments_append] using second

/-- The head and arguments already present in `MinorRd.ihTy`. -/
def MinorRd.ihHead (n : MinorRd) (nm r ky j : Nat) : Kernel.Expr :=
  .bvar (ky + r + n.fields.length + (nm - 1 - j))

def MinorRd.ihArguments (n : MinorRd) (nm r a ky : Nat)
    (idx : List Kernel.Expr) : List Kernel.Expr :=
  idx.map (fun e => (e.liftLooseBVars nm (a + ky)).liftLooseBVars
    (n.fields.length - a + r) ky) ++
  [Kernel.Expr.mkAppN (.bvar (ky + r + (n.fields.length - 1 - a))) (bvarsAt ky 0)]

/-- Separate readings of the actual IH head and complete argument spine.
The selected field and motive retain their original values through every
context segment, including reflexive-field arguments and earlier IHs. -/
theorem MinorRd.ih_spine (n : MinorRd) (nm j : Nat)
    (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr)
    (ρ : Nat → V) (params motives before after hypotheses arguments indices : List V)
    (field : V)
    (motiveLength : motives.length = nm)
    (fieldLength : (before ++ [field] ++ after).length = n.fields.length)
    (argumentLength : arguments.length = ys.length)
    (motiveBound : j < motives.length)
    (indexRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ before ++ arguments)) idx indices) :
    Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (n.ihHead nm hypotheses.length ys.length j) motives[j] ∧
    DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (n.ihArguments nm hypotheses.length before.length ys.length idx)
      (indices ++ [arguments.foldl app field]) := by
  have motivePosition :
      (before ++ [field] ++ after ++ hypotheses ++ arguments).length +
        (motives.length - 1 - j) =
      ys.length + hypotheses.length + n.fields.length + (nm - 1 - j) := by
    simp only [List.length_append, List.length_cons, List.length_nil] at fieldLength ⊢
    omega
  have headRead := denotes_bvar_segment (cval := cval) (env := env) (φ := φ)
    ρ params motives (before ++ [field] ++ after ++ hypotheses ++ arguments) j motiveBound
  rw [motivePosition] at headRead
  have fieldPosition :
      (after ++ hypotheses ++ arguments).length + ([field].length - 1 - 0) =
      ys.length + hypotheses.length + (n.fields.length - 1 - before.length) := by
    simp only [List.length_append, List.length_cons, List.length_nil] at fieldLength ⊢
    omega
  have fieldRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (.bvar (ys.length + hypotheses.length + (n.fields.length - 1 - before.length)))
      field := by
    have reading := denotes_bvar_segment (cval := cval) (env := env) (φ := φ)
      ρ (params ++ motives ++ before) [field] (after ++ hypotheses ++ arguments) 0 (by simp)
    rw [fieldPosition] at reading
    simpa only [List.append_assoc, List.getElem_cons_zero] using reading
  have argumentsRead : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (bvarsAt ys.length 0) arguments := by
    simpa only [List.append_nil, List.length_nil, argumentLength] using
      (denotesSpine_bvarsAt_middle (cval := cval) (env := env) (φ := φ)
        ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses) arguments [])
  have indicesRead := n.ih_indices_lift nm ys.length idx ρ params motives before
    ([field] ++ after) hypotheses arguments indices motiveLength
    (by simpa only [List.append_assoc] using fieldLength) argumentLength indexRead
  have liftedIndices : DenotesSpine cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (idx.map (fun e => (e.liftLooseBVars nm (before.length + ys.length)).liftLooseBVars
        (n.fields.length - before.length + hypotheses.length) ys.length)) indices := by
    simpa only [List.append_assoc] using indicesRead
  refine ⟨?_, ?_⟩
  · simpa only [MinorRd.ihHead, List.append_assoc] using headRead
  · exact liftedIndices.append (.cons
      (Ix.CompileCert.denotes_mkAppN fieldRead argumentsRead) .nil)

/-- An actual inhabited IH supplies the original recursive indices and a
fully typed selected-motive application, for every ORIGINAL typed reflexive
argument tuple. The source/block adapter must establish `indexCount`; this
internal lemma does not infer it from old Check or change the final endpoint. -/
theorem RecRd.ih_arguments_typed {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (ρ : Nat → V)
    (params motives before after hypotheses arguments : List V) (field : V)
    (motivesTyped : TeleTyped cval env φ (pushArguments ρ params)
      (R.motiveBinders.map Prod.fst) motives)
    (n : MinorRd) (present : n ∈ R.minors)
    (j : Nat) (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr)
    (recursive : (before.length, j, ys, idx) ∈ n.recFields)
    (fieldLength : (before ++ [field] ++ after).length = n.fields.length)
    (indexCount : idx.length = (R.motives.getD j default).idxs.length)
    (graded : Bridge.Graded cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      (n.ihTy R.nm hypotheses.length before.length j ys idx))
    {T f : V}
    (typeRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      (n.ihTy R.nm hypotheses.length before.length j ys idx) T)
    (member : f ∈ˢ T)
    (typed : TeleTyped cval env φ (pushArguments ρ (params ++ before))
      (ys.map Prod.fst) arguments) :
    ∃ indices,
      DenotesSpine cval env φ (pushArguments ρ (params ++ before ++ arguments)) idx indices ∧
      TeleTyped cval env φ (pushArguments ρ params)
        (((R.motives.getD j default).tele R.np).map Prod.fst)
        (indices ++ [arguments.foldl app field]) ∧
      arguments.foldl app f ∈ˢ
        (indices ++ [arguments.foldl app field]).foldl app (getElem motives j (by
          have len : motives.length = R.nm := by
            simpa only [List.length_map, motiveBinders_length] using motivesTyped.length
          have own := (checked.2.2.2.2 n present).2.2.2.2.1 _ recursive
          simpa only [len] using own)) := by
  have motiveLength : motives.length = R.nm := by
    simpa only [List.length_map, motiveBinders_length] using motivesTyped.length
  have sourceBound : j < R.motives.length :=
    (checked.2.2.2.2 n present).2.2.2.2.1 _ recursive
  have motiveBound : j < motives.length := by
    simpa only [motiveLength, RecRd.nm] using sourceBound
  have selectedPresent : R.motives.getD j default ∈ R.motives := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem sourceBound, Option.getD_some]
    exact List.getElem_mem sourceBound
  have argumentLength : arguments.length = ys.length := by
    simpa only [List.length_map] using typed.length
  have lifted : TeleTyped cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      ((liftTele (n.fields.length - before.length + hypotheses.length) 0
        (liftTele R.nm before.length ys)).map Prod.fst) arguments := by
    simpa only [List.append_assoc] using
      n.ih_arguments_lift R.nm ys ρ params motives before ([field] ++ after)
        hypotheses arguments motiveLength
        (by simpa only [List.append_assoc] using fieldLength) typed
  obtain ⟨indices, indexRead, applied⟩ := n.ih_applied_exists R.nm j ys idx
    ρ params motives before after hypotheses arguments field motiveLength fieldLength
    motiveBound typeRead member lifted
  have bodyGraded := graded_piJoin (bs := liftTele
      (n.fields.length - before.length + hypotheses.length) 0
      (liftTele R.nm before.length ys))
    (by simpa only [MinorRd.ihTy] using graded) lifted
  have applicationGraded : Bridge.Graded cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses ++ arguments))
      (Kernel.Expr.mkAppN (n.ihHead R.nm hypotheses.length ys.length j)
        (n.ihArguments R.nm hypotheses.length before.length ys.length idx)) := by
    simpa only [MinorRd.ihHead, MinorRd.ihArguments,
      Ix.CompileCert.pushArguments_append] using bodyGraded
  obtain ⟨headRead, spine⟩ := n.ih_spine R.nm j ys idx ρ params motives before after
    hypotheses arguments indices field motiveLength fieldLength argumentLength motiveBound indexRead
  obtain ⟨A, motiveRead, motiveMember⟩ :=
    R.motive_value_typed (pushArguments ρ params) motives motivesTyped j motiveBound
  have argumentCount : (n.ihArguments R.nm hypotheses.length before.length ys.length idx).length =
      ((R.motives.getD j default).tele R.np).length := by
    simp only [MinorRd.ihArguments, List.length_append, List.length_map,
      List.length_cons, List.length_nil, motive_tele_length, indexCount]
  have tupleTyped := typed_of_graded_spine ((R.motives.getD j default).tele R.np)
    (RecRd.motive_graph checked selectedPresent) applicationGraded headRead motiveRead
    motiveMember spine argumentCount
  exact ⟨indices, indexRead, tupleTyped, applied⟩

/-- The interpreted actual IH proves the chosen predicate on the recursive
field application. This is a membership-to-predicate bridge, not an assumption
that the induction conclusion already holds. -/
theorem RecRd.ih_predicate {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (ρ : Nat → V)
    (params motives before after hypotheses arguments : List V) (field : V)
    (motivesTyped : TeleTyped cval env φ (pushArguments ρ params)
      (R.motiveBinders.map Prod.fst) motives)
    (predicate : Nat → List V → Prop)
    (chosen : ∀ j (bound : j < motives.length) values,
      TeleTyped cval env φ (pushArguments ρ params)
        (((R.motives.getD j default).tele R.np).map Prod.fst) values →
      values.foldl app motives[j] = truthVal (predicate j values))
    (n : MinorRd) (present : n ∈ R.minors)
    (j : Nat) (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr)
    (recursive : (before.length, j, ys, idx) ∈ n.recFields)
    (fieldLength : (before ++ [field] ++ after).length = n.fields.length)
    (indexCount : idx.length = (R.motives.getD j default).idxs.length)
    (graded : Bridge.Graded cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      (n.ihTy R.nm hypotheses.length before.length j ys idx))
    {T f : V}
    (typeRead : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ before ++ [field] ++ after ++ hypotheses))
      (n.ihTy R.nm hypotheses.length before.length j ys idx) T)
    (member : f ∈ˢ T)
    (typed : TeleTyped cval env φ (pushArguments ρ (params ++ before))
      (ys.map Prod.fst) arguments) :
    ∃ indices,
      DenotesSpine cval env φ (pushArguments ρ (params ++ before ++ arguments)) idx indices ∧
      TeleTyped cval env φ (pushArguments ρ params)
        (((R.motives.getD j default).tele R.np).map Prod.fst)
        (indices ++ [arguments.foldl app field]) ∧
      predicate j (indices ++ [arguments.foldl app field]) := by
  obtain ⟨indices, indexRead, tupleTyped, applied⟩ := R.ih_arguments_typed checked ρ
    params motives before after hypotheses arguments field motivesTyped n present j ys idx
    recursive fieldLength indexCount graded typeRead member typed
  refine ⟨indices, indexRead, tupleTyped, ?_⟩
  rw [chosen j _ _ tupleTyped] at applied
  exact of_mem_truthVal applied

/-- Grading of the actual selected telescope domain at its preceding typed
values. No grading of an unreachable prefix is requested from the caller. -/
theorem graded_piJoin_domain_at
    {bs : List (Kernel.Expr × Kernel.BinderMeta)} {b : Kernel.Expr}
    {ρ : Nat → V} {xs : List V}
    (graded : Bridge.Graded cval env φ ρ (piJoin bs b))
    (typed : TeleTyped cval env φ ρ (bs.map Prod.fst) xs)
    (i : Nat) (bound : i < xs.length) :
    Bridge.Graded cval env φ (pushArguments ρ (xs.take i))
      ((bs.map Prod.fst).getD i default) := by
  induction bs generalizing ρ xs i with
  | nil => cases typed; simp at bound
  | cons p bs ih =>
    obtain ⟨t, m⟩ := p
    cases xs with
    | nil => simp at bound
    | cons x xs =>
      obtain ⟨A, domain, member, rest⟩ := TeleTyped.cons_iff.mp typed
      obtain ⟨domainGraded, B, domainRead, bodyGraded, _⟩ := graded
      cases i with
      | zero =>
        simpa only [List.map_cons, List.getD_cons_zero, List.take_zero, pushArguments]
          using domainGraded
      | succ i =>
        have equal : A = B := Kernel.Denotes_functional domain domainRead
        have inside : i < xs.length := Nat.lt_of_succ_lt_succ bound
        have atTail := ih (bodyGraded x (equal ▸ member)) rest i inside
        simpa only [List.map_cons, List.getD_cons_succ, List.take_succ_cons, pushArguments]
          using atTail

/-- Select an actual IH inhabitant, its exact generated type and its grading
from the complete typed IH tuple. Its earlier-IH context is the actual prefix;
metadata length comes from the enclosing reader check. -/
theorem MinorRd.ih_value_typed (n : MinorRd) (nm : Nat) (ρ : Nat → V)
    (hypotheses : List V) {b : Kernel.Expr}
    (metaLength : n.ihMetas.length = n.recFields.length)
    (graded : Bridge.Graded cval env φ ρ (piJoin (zipMetas (n.ihTys nm) n.ihMetas) b))
    (typed : TeleTyped cval env φ ρ (n.ihTys nm) hypotheses)
    (i : Nat) (bound : i < hypotheses.length) :
    let entry := n.recFields.getD i default
    ∃ A,
      Kernel.Denotes cval env φ (pushArguments ρ (hypotheses.take i))
        (n.ihTy nm i entry.1 entry.2.1 entry.2.2.1 entry.2.2.2) A ∧
      hypotheses[i] ∈ˢ A ∧
      Bridge.Graded cval env φ (pushArguments ρ (hypotheses.take i))
        (n.ihTy nm i entry.1 entry.2.1 entry.2.2.1 entry.2.2.2) := by
  have length : hypotheses.length = n.recFields.length := by
    simpa only [ihTys_length] using typed.length
  have sourceBound : i < n.recFields.length := by omega
  have atIndex : (n.ihTys nm).getD i default =
      n.ihTy nm i (n.recFields.getD i default).1 (n.recFields.getD i default).2.1
        (n.recFields.getD i default).2.2.1 (n.recFields.getD i default).2.2.2 := by
    simp only [MinorRd.ihTys, List.getD_eq_getElem?_getD,
      List.getElem?_mapIdx, List.getElem?_eq_getElem sourceBound, Option.map_some,
      Option.getD_some]
  have domains : (zipMetas (n.ihTys nm) n.ihMetas).map Prod.fst = n.ihTys nm :=
    zipMetas_types _ _ (by simpa only [ihTys_length] using metaLength)
  have binderTyped : TeleTyped cval env φ ρ
      ((zipMetas (n.ihTys nm) n.ihMetas).map Prod.fst) hypotheses := by
    simpa only [domains] using typed
  obtain ⟨A, domain, member⟩ := typed.domain_at i bound
  have domainGraded := graded_piJoin_domain_at graded binderTyped i bound
  refine ⟨A, ?_, member, ?_⟩
  · simpa only [atIndex] using domain
  · simpa only [domains, atIndex] using domainGraded

end Ix.CompileCert.Pj

/-! Internal minor-inhabitation construction, using the accepted Pj17 result
and the actual reader telescopes. This is not the original induction endpoint:
the constructor-step adapter must discharge the explicit applied-step callback,
and accepted-source/WHNF completeness must discharge the header branch. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

/-- Construct a member of the actual minor type from its concrete applied
step. Both dependent telescope folds work in either binder regime. Original
constructor-field typing is recovered by removing only the motive insertion.

The callback consumes actual typed IH VALUES, not a postulated minor-function
inhabitant. The original constructor-step proof must convert those values into
its pointwise recursive premises (using the IH interpreter), then supply this
callback. Neither the callback nor the literal-header test is a new final
caller premise. This fresh excluded theorem is uncompiled. -/
theorem RecRd.minor_inhabited_of_applied_step
    {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env} {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params motives : List V)
    (paramsTyped : TeleTyped strong.public.cval env φ ρ (R.params.map Prod.fst) params)
    (motivesTyped : TeleTyped strong.public.cval env φ (pushArguments ρ params)
      (R.motiveBinders.map Prod.fst) motives)
    (predicate : Nat → List V → Prop)
    (chosen : ∀ j (bound : j < motives.length) values,
      TeleTyped strong.public.cval env φ (pushArguments ρ params)
        (((R.motives.getD j default).tele R.np).map Prod.fst) values →
      values.foldl app motives[j] = truthVal (predicate j values))
    (n : MinorRd) (present : n ∈ R.minors)
    (header : InstalledHeader.checkMinorResult env R.params R.motives n = true)
    (step : ∀ fields,
      TeleTyped strong.public.cval env φ (pushArguments ρ params)
        ((n.fieldTys R.np R.motives).map Prod.fst) fields →
      ∀ hypotheses,
        TeleTyped strong.public.cval env φ (pushArguments ρ (params ++ motives ++ fields))
          (n.ihTys R.nm) hypotheses →
        ∀ constructor indices,
          (∀ valuation, Kernel.Denotes strong.public.cval env φ valuation
            (.const n.ctor n.ctorUs) constructor) →
          DenotesSpine strong.public.cval env φ (pushArguments ρ (params ++ fields))
            n.resIdx indices →
          TeleTyped strong.public.cval env φ (pushArguments ρ params)
            (((R.motives.getD n.motive default).tele R.np).map Prod.fst)
            (indices ++ [(params ++ fields).foldl app constructor]) →
          predicate n.motive (indices ++ [(params ++ fields).foldl app constructor]))
    (graded : Bridge.Graded strong.public.cval env φ
      (pushArguments (pushArguments ρ params) motives)
      (n.type R.np R.nm R.motives))
    {A : V}
    (typeRead : Kernel.Denotes strong.public.cval env φ
      (pushArguments (pushArguments ρ params) motives)
      (n.type R.np R.nm R.motives) A) :
    ∃ x, x ∈ˢ A := by
  have ncheck := checked.2.2.2.2 n present
  have motiveLength : motives.length = R.nm := by
    simpa only [List.length_map, motiveBinders_length] using motivesTyped.length
  let fieldBinders := zipMetas ((n.fieldTys R.np R.motives).mapIdx
    (fun a p => p.1.liftLooseBVars R.nm a)) n.fieldMetas
  let hypothesisBinders := zipMetas (n.ihTys R.nm) n.ihMetas
  have hypothesisTypes : hypothesisBinders.map Prod.fst = n.ihTys R.nm := by
    exact zipMetas_types _ _ (by simpa only [ihTys_length] using ncheck.2.2.2.1)
  have outerRead : Kernel.Denotes strong.public.cval env φ
      (pushArguments (pushArguments ρ params) motives)
      (piJoin fieldBinders (piJoin hypothesisBinders (n.concl R.np R.nm))) A := typeRead
  have outerGraded : Bridge.Graded strong.public.cval env φ
      (pushArguments (pushArguments ρ params) motives)
      (piJoin fieldBinders (piJoin hypothesisBinders (n.concl R.np R.nm))) := graded
  apply tele_inhabited fieldBinders outerRead
  intro fields fieldρ fieldCount fieldInstalled
  obtain ⟨fieldTyped, fieldValuation, _⟩ :=
    installed_piJoin_iff.mp ⟨fieldInstalled, fieldCount⟩
  subst fieldρ
  have fieldsTyped := n.fields_unlift R.np R.nm R.motives
    (pushArguments ρ params) motives fields motiveLength ncheck.2.2.1 fieldTyped
  have fieldLength : fields.length = n.fields.length := by
    simpa only [List.length_map, fieldTys_length] using fieldsTyped.length
  obtain ⟨B, innerRead⟩ := fieldInstalled.read outerRead
  have innerGraded := graded_piJoin outerGraded fieldTyped
  refine ⟨B, innerRead, ?_⟩
  apply tele_inhabited hypothesisBinders innerRead
  intro hypotheses hypothesisρ hypothesisCount hypothesisInstalled
  obtain ⟨hypothesisTyped, hypothesisValuation, _⟩ :=
    installed_piJoin_iff.mp ⟨hypothesisInstalled, hypothesisCount⟩
  subst hypothesisρ
  have hypothesesTyped : TeleTyped strong.public.cval env φ
      (pushArguments ρ (params ++ motives ++ fields)) (n.ihTys R.nm) hypotheses := by
    simpa only [hypothesisTypes, Ix.CompileCert.pushArguments_append] using hypothesisTyped
  have hypothesisLength : hypotheses.length = n.recFields.length := by
    simpa only [ihTys_length] using hypothesesTyped.length
  have conclusionGraded : Bridge.Graded strong.public.cval env φ
      (pushArguments ρ (params ++ motives ++ fields ++ hypotheses)) (n.concl R.np R.nm) := by
    simpa only [Ix.CompileCert.pushArguments_append] using
      graded_piJoin innerGraded hypothesisTyped
  obtain ⟨constructor, indices, constructorRead, indexRead, tupleTyped, conclusionRead⟩ :=
    R.minor_arguments_typed_of_literal_header checked strong φ ρ
      params motives fields hypotheses paramsTyped motivesTyped n present
      fieldLength hypothesisLength header conclusionGraded
  have result := step fields fieldsTyped hypotheses hypothesesTyped
    constructor indices constructorRead indexRead tupleTyped
  refine ⟨(indices ++ [(params ++ fields).foldl app constructor]).foldl app
    (getElem motives n.motive (by simpa only [motiveLength] using ncheck.1)), ?_, pt, ?_⟩
  · simpa only [Ix.CompileCert.pushArguments_append] using conclusionRead
  · rw [chosen n.motive _ _ tupleTyped]
    exact pt_mem_truthVal result

end Ix.CompileCert.Pj

/-! Exact recursive-field positions of the existing reader.
No source/header premise is used in these list-projection statements. -/

namespace Ix.CompileCert.Pj

universe u

/-- Every recursive-field record comes from that exact original field
position. In particular, an out-of-range field cannot make recursive premises
vacuous by falling through a default lookup. -/
theorem MinorRd.recField_position (n : MinorRd) (a j : Nat)
    (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr)
    (present : (a, j, ys, idx) ∈ n.recFields) :
    ∃ bound : a < n.fields.length, n.fields[a].1 = .recur j ys idx := by
  obtain ⟨entry, inMap, selected⟩ := List.mem_filterMap.mp present
  obtain ⟨k, inside, position⟩ := List.mem_iff_getElem.mp inMap
  have sourceBound : k < n.fields.length := by
    simpa only [List.length_mapIdx] using inside
  have pair : (k, n.fields[k].1) = entry := by
    simpa only [List.getElem_mapIdx] using position
  rw [← pair] at selected
  cases field : n.fields[k].1 with
  | plain ty => simp only [field, reduceCtorEq] at selected
  | recur j' ys' idx' =>
    have same : (k, j', ys', idx') = (a, j, ys, idx) := by
      exact Option.some.inj (by simpa only [field] using selected)
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, rfl, rfl⟩ := same
    exact ⟨sourceBound, field⟩

/-- Every recursive constructor field is retained by the actual filter.
This is the reverse direction needed for complete recursive-premise coverage. -/
theorem MinorRd.recField_present (n : MinorRd) (a j : Nat)
    (ys : List (Kernel.Expr × Kernel.BinderMeta)) (idx : List Kernel.Expr)
    (bound : a < n.fields.length) (field : n.fields[a].1 = .recur j ys idx) :
    (a, j, ys, idx) ∈ n.recFields := by
  apply List.mem_filterMap.mpr
  refine ⟨(a, n.fields[a].1), ?_, ?_⟩
  · apply List.mem_iff_getElem.mpr
    refine ⟨a, ?_, ?_⟩
    · simpa only [List.length_mapIdx] using bound
    · simp only [List.getElem_mapIdx]
  · simp only [field]

/-- Exact prefix, selected value and suffix in the original list order. -/
theorem take_singleton_drop {α : Type u} (xs : List α) (i : Nat) (bound : i < xs.length) :
    xs.take i ++ [xs[i]] ++ xs.drop (i + 1) = xs := by
  induction xs generalizing i with
  | nil => simp at bound
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have inside : i < xs.length := Nat.lt_of_succ_lt_succ bound
      simpa only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons,
        List.cons_append] using congrArg (List.cons x) (ih i inside)

end Ix.CompileCert.Pj

/-! The original pointwise recursive premises, obtained from actual IH
inhabitants. Saturation is an internal accepted-source adapter obligation;
no final caller is asked to provide this fact. This draft is uncompiled. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

/-- Internal spelling of the report's pointwise recursive hypotheses.
Every actual recursive field is covered; its dependent argument tuple is
typed in the original parameter/earlier-field context. A valid getElem position
is supplied for each record rather than required from this property's caller. -/
def MinorStep.RecursivePremises {V : Type u} [Kernel.SetTheory V]
    (cval : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params fields : List V)
    (n : MinorRd) (predicate : Nat → List V → Prop) : Prop :=
  ∀ a j ys idx, (a, j, ys, idx) ∈ n.recFields →
    ∃ bound : a < fields.length, ∀ arguments,
      TeleTyped cval env φ (pushArguments ρ (params ++ fields.take a))
        (ys.map Prod.fst) arguments →
      ∃ indices,
        DenotesSpine cval env φ
          (pushArguments ρ (params ++ fields.take a ++ arguments)) idx indices ∧
        predicate j (indices ++ [arguments.foldl app fields[a]])

/-- Every actual typed IH value supplies the corresponding original recursive
premise. This derives all intermediate grading, value-prefix and field-position
facts from the existing minor and tuple, rather than taking those facts from
the final constructor-step caller. The explicit saturation map remains an
internal source/header obligation, not a new final assumption. -/
theorem RecRd.recursive_premises_of_ihs
    {V : Type u} [Kernel.SetTheory V]
    {cval : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {φ : Kernel.Name → Nat} {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (ρ : Nat → V) (params motives fields hypotheses : List V)
    (motivesTyped : TeleTyped cval env φ (pushArguments ρ params)
      (R.motiveBinders.map Prod.fst) motives)
    (predicate : Nat → List V → Prop)
    (chosen : ∀ j (bound : j < motives.length) values,
      TeleTyped cval env φ (pushArguments ρ params)
        (((R.motives.getD j default).tele R.np).map Prod.fst) values →
      values.foldl app motives[j] = truthVal (predicate j values))
    (n : MinorRd) (present : n ∈ R.minors)
    (saturated : ∀ a j ys idx, (a, j, ys, idx) ∈ n.recFields →
      idx.length = (R.motives.getD j default).idxs.length)
    (graded : Bridge.Graded cval env φ
      (pushArguments (pushArguments ρ params) motives) (n.type R.np R.nm R.motives))
    (fieldsTyped : TeleTyped cval env φ (pushArguments ρ params)
      ((n.fieldTys R.np R.motives).map Prod.fst) fields)
    (hypothesesTyped : TeleTyped cval env φ (pushArguments ρ (params ++ motives ++ fields))
      (n.ihTys R.nm) hypotheses) :
    MinorStep.RecursivePremises cval env φ ρ params fields n predicate := by
  have ncheck := checked.2.2.2.2 n present
  have motiveLength : motives.length = R.nm := by
    simpa only [List.length_map, motiveBinders_length] using motivesTyped.length
  have fieldLength : fields.length = n.fields.length := by
    simpa only [List.length_map, fieldTys_length] using fieldsTyped.length
  have hypothesisLength : hypotheses.length = n.recFields.length := by
    simpa only [ihTys_length] using hypothesesTyped.length
  have liftedFields := fieldsTyped.lift
    (valuationLift_prefix (pushArguments ρ params) motives)
  have actualFields : TeleTyped cval env φ (pushArguments (pushArguments ρ params) motives)
      ((zipMetas ((n.fieldTys R.np R.motives).mapIdx
        (fun a p => p.1.liftLooseBVars R.nm a)) n.fieldMetas).map Prod.fst) fields := by
    simpa only [n.fieldBinders_types R.np R.nm R.motives ncheck.2.2.1,
      motiveLength] using liftedFields
  have ihsGraded : Bridge.Graded cval env φ
      (pushArguments ρ (params ++ motives ++ fields))
      (piJoin (zipMetas (n.ihTys R.nm) n.ihMetas) (n.concl R.np R.nm)) := by
    simpa only [Ix.CompileCert.pushArguments_append] using
      graded_piJoin (by simpa only [MinorRd.type] using graded) actualFields
  intro a j ys idx recursive
  obtain ⟨fieldInside, _⟩ := n.recField_position a j ys idx recursive
  have bound : a < fields.length := by simpa only [fieldLength] using fieldInside
  refine ⟨bound, ?_⟩
  intro arguments argumentsTyped
  obtain ⟨i, sourceInside, atEntry⟩ := List.mem_iff_getElem.mp recursive
  have inside : i < hypotheses.length := by simpa only [hypothesisLength] using sourceInside
  have entry : n.recFields.getD i default = (a, j, ys, idx) := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem sourceInside,
      Option.getD_some] using atEntry
  have earlierFields : (fields.take a).length = a := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  have earlierHypotheses : (hypotheses.take i).length = i := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt inside)]
  have fieldParts := take_singleton_drop fields a bound
  have context :
      pushArguments ρ (params ++ motives ++ fields.take a ++ [fields[a]] ++
        fields.drop (a + 1) ++ hypotheses.take i) =
      pushArguments (pushArguments ρ (params ++ motives ++ fields)) (hypotheses.take i) := by
    rw [← Ix.CompileCert.pushArguments_append]
    apply congrArg (pushArguments ρ)
    simpa only [List.append_assoc] using
      congrArg (fun fs => params ++ motives ++ fs ++ hypotheses.take i) fieldParts
  obtain ⟨A, domain, member, domainGraded⟩ :=
    n.ih_value_typed R.nm (pushArguments ρ (params ++ motives ++ fields)) hypotheses
      ncheck.2.2.2.1 ihsGraded hypothesesTyped i inside
  have actualDomain : Kernel.Denotes cval env φ
      (pushArguments ρ (params ++ motives ++ fields.take a ++ [fields[a]] ++
        fields.drop (a + 1) ++ hypotheses.take i))
      (n.ihTy R.nm (hypotheses.take i).length (fields.take a).length j ys idx) A := by
    simpa only [context, earlierFields, earlierHypotheses, entry] using domain
  have actualGraded : Bridge.Graded cval env φ
      (pushArguments ρ (params ++ motives ++ fields.take a ++ [fields[a]] ++
        fields.drop (a + 1) ++ hypotheses.take i))
      (n.ihTy R.nm (hypotheses.take i).length (fields.take a).length j ys idx) := by
    simpa only [context, earlierFields, earlierHypotheses, entry] using domainGraded
  obtain ⟨indices, indexRead, _, property⟩ := R.ih_predicate checked ρ params motives
    (fields.take a) (fields.drop (a + 1)) (hypotheses.take i) arguments fields[a]
    motivesTyped predicate chosen n present j ys idx
    (by simpa only [earlierFields] using recursive)
    (by rw [fieldParts, fieldLength])
    (saturated a j ys idx recursive) actualGraded actualDomain member argumentsTyped
  exact ⟨indices, indexRead, property⟩

end Ix.CompileCert.Pj

/-! Conditional internal constructor-step assembly.

The steps below have the original semantic content: typed constructor fields
plus every pointwise recursive premise imply the selected constructor result.
The separate header/saturation conditions MUST come from the original accepted
source/block adapter. They are not proposed assumptions of the final theorem.
All-member frame/source assembly is separate from this one-rec-reader lemma. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments DenotesSpine)

universe u

/-- Internal spelling of the original semantic constructor step. Index and
constructor readings expose the report's result-index/model-value operations;
they do not assume any target predicate or a minor-function inhabitant. -/
def MinorStep.ConstructorStep {V : Type u} [Kernel.SetTheory V]
    (cval : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params : List V)
    (np : Nat) (sourceMotives : List MotiveRd) (n : MinorRd)
    (predicate : Nat → List V → Prop) : Prop :=
  ∀ fields,
    TeleTyped cval env φ (pushArguments ρ params)
      ((n.fieldTys np sourceMotives).map Prod.fst) fields →
    MinorStep.RecursivePremises cval env φ ρ params fields n predicate →
    ∀ constructor indices,
      (∀ valuation, Kernel.Denotes cval env φ valuation
        (.const n.ctor n.ctorUs) constructor) →
      DenotesSpine cval env φ (pushArguments ρ (params ++ fields)) n.resIdx indices →
      predicate n.motive (indices ++ [(params ++ fields).foldl app constructor])

/-- The original pointwise constructor step supplies the applied-step callback.
This discharges that semantic callback rather than exposing it as another
final assumption. Literal header and recursive saturation are still internal
source/WHNF obligations; the final caller does not receive them. -/
theorem RecRd.minor_inhabited_of_constructor_step
    {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env} {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params motives : List V)
    (paramsTyped : TeleTyped strong.public.cval env φ ρ (R.params.map Prod.fst) params)
    (motivesTyped : TeleTyped strong.public.cval env φ (pushArguments ρ params)
      (R.motiveBinders.map Prod.fst) motives)
    (predicate : Nat → List V → Prop)
    (chosen : ∀ j (bound : j < motives.length) values,
      TeleTyped strong.public.cval env φ (pushArguments ρ params)
        (((R.motives.getD j default).tele R.np).map Prod.fst) values →
      values.foldl app motives[j] = truthVal (predicate j values))
    (n : MinorRd) (present : n ∈ R.minors)
    (header : InstalledHeader.checkMinorResult env R.params R.motives n = true)
    (saturated : ∀ a j ys idx, (a, j, ys, idx) ∈ n.recFields →
      idx.length = (R.motives.getD j default).idxs.length)
    (step : MinorStep.ConstructorStep strong.public.cval env φ ρ params
      R.np R.motives n predicate)
    (graded : Bridge.Graded strong.public.cval env φ
      (pushArguments (pushArguments ρ params) motives) (n.type R.np R.nm R.motives))
    {A : V}
    (typeRead : Kernel.Denotes strong.public.cval env φ
      (pushArguments (pushArguments ρ params) motives) (n.type R.np R.nm R.motives) A) :
    ∃ x, x ∈ˢ A := by
  apply R.minor_inhabited_of_applied_step checked strong φ ρ params motives
    paramsTyped motivesTyped predicate chosen n present header
    (graded := graded) (typeRead := typeRead)
  intro fields fieldsTyped hypotheses hypothesesTyped constructor indices constructorRead indexRead _
  have premises := R.recursive_premises_of_ihs checked ρ params motives fields hypotheses
    motivesTyped predicate chosen n present saturated graded fieldsTyped hypothesesTyped
  exact step fields fieldsTyped premises constructor indices constructorRead indexRead

/-- Internal assembly for every typed major of this selected recursor. The
constructor steps cover every minor, including recursive, reflexive, mutual
and zero-field cases. No replacement universe assignment or element inversion
is assumed. This is NOT the final all-accepted-source/all-member endpoint:
the header and saturation inputs here must be eliminated by that adapter. -/
theorem RecRd.predicate_of_shape_checked_constructor_steps
    {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env} {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params : List V)
    (paramsTyped : TeleTyped strong.public.cval env φ ρ (R.params.map Prod.fst) params)
    (predicate : Nat → List V → Prop)
    (headers : ∀ n ∈ R.minors,
      InstalledHeader.checkMinorResult env R.params R.motives n = true)
    (saturation : ∀ n ∈ R.minors, ∀ a j ys idx, (a, j, ys, idx) ∈ n.recFields →
      idx.length = (R.motives.getD j default).idxs.length)
    (steps : ∀ n ∈ R.minors,
      MinorStep.ConstructorStep strong.public.cval env φ ρ params R.np R.motives n predicate)
    (arguments : List V)
    (typed : TeleTyped strong.public.cval env φ (pushArguments ρ params)
      ((R.majorMotive.tele R.np).map Prod.fst) arguments) :
    predicate R.major arguments := by
  apply RecRd.predicate_of_graded_minor_inhabitation checked strong φ ρ params
    paramsTyped predicate (arguments := arguments) (typed := typed)
  intro motives motivesTyped chosen n present graded A typeRead
  exact R.minor_inhabited_of_constructor_step checked strong φ ρ params motives
    paramsTyped motivesTyped predicate chosen n present (headers n present)
    (saturation n present) (steps n present) graded typeRead

end Ix.CompileCert.Pj

/-! Actual installed-constructor field projection for the literal-header
branch. The new checks are internal reader data checks, not added assumptions
of the original accepted-source induction theorem. Accepted-source completeness
and the general checked-WHNF branch remain required. Uncompiled draft. -/

namespace Ix.CompileCert.Pj

open Ix.CompileCert (pushArguments)

universe u

namespace InstalledHeader

/-- Read all actual installed field domains, using the constructor's own
stored parameter/field counts and the exact selected universe instance. -/
def readConstructorFields (env : Kernel.Env) (n : MinorRd) : Option Telescope :=
  match env.find? n.ctor with
  | some (.ctorInfo cv np nf) =>
    if n.ctorUs.length = cv.levelParams.length then
      ((cv.type.instantiateLevelParams cv.levelParams n.ctorUs).stripPis
        (np + nf)).map (fun result => result.1.drop np)
    else none
  | _ => none

/-- Existing CtorOk connects the complete actual field telescope, including
all dependent domains and binder metadata, to the existing minor data. -/
theorem readConstructorFields_of_CtorOk {env : Kernel.Env}
    (parameters : Telescope) (motives : List MotiveRd) (n : MinorRd)
    (checked : n.CtorOk env parameters.length motives parameters)
    (metadata : n.paramMetas.length = parameters.length) :
    readConstructorFields env n = some (n.fieldTys parameters.length motives) := by
  have parameterLength : (zipMetas (parameters.map Prod.fst) n.paramMetas).length =
      parameters.length := by
    simpa only [List.length_map] using
      zipMetas_length (parameters.map Prod.fst) n.paramMetas
        (by simpa only [List.length_map] using metadata)
  cases lookup : env.find? n.ctor with
  | none => simp only [MinorRd.CtorOk, lookup] at checked
  | some ci =>
    cases ci <;> simp only [MinorRd.CtorOk, lookup] at checked
    case ctorInfo cv np nf =>
      obtain ⟨npEq, nfEq, arity, typeEq⟩ := checked
      simp only [readConstructorFields, lookup, ite_eq_left arity, typeEq, npEq, nfEq,
        strip_constructorType parameters motives n metadata, Option.map_some,
        constructorBinders]
      exact congrArg some (List.drop_left' parameterLength)

/-- Select the actual constructor field, then strip precisely the recursive
field's own dependent argument binders. A missing field or prefix refuses. -/
def readFieldResidual (env : Kernel.Env) (n : MinorRd) (a depth : Nat) :
    Option Kernel.Expr :=
  match readConstructorFields env n with
  | none => none
  | some fields =>
    match fields[a]? with
    | none => none
    | some field => (field.1.stripPis depth).map Prod.snd

/-- The selected residual is projected from the actual installed constructor;
it is not synthesized from a caller-supplied index count or a cached hash. -/
theorem readFieldResidual_of_recField {env : Kernel.Env}
    (parameters : Telescope) (motives : List MotiveRd) (n : MinorRd)
    (checked : n.CtorOk env parameters.length motives parameters)
    (metadata : n.paramMetas.length = parameters.length)
    (a j : Nat) (ys : Telescope) (idx : List Kernel.Expr)
    (recursive : (a, j, ys, idx) ∈ n.recFields) :
    readFieldResidual env n a ys.length = some
      (Kernel.Expr.mkAppN (.const (motives.getD j default).ind (motives.getD j default).indUs)
        (bvarsAt parameters.length (a + ys.length) ++ idx)) := by
  obtain ⟨inside, field⟩ := n.recField_position a j ys idx recursive
  have atField : (n.fieldTys parameters.length motives)[a]? =
      some ((FieldRd.recur j ys idx).ty parameters.length motives a, n.fields[a].2) := by
    simp only [MinorRd.fieldTys, List.getElem?_mapIdx, List.getElem?_eq_getElem inside,
      Option.map_some, field]
  simp only [readFieldResidual, readConstructorFields_of_CtorOk parameters motives n checked metadata,
    atField, FieldRd.ty, stripPis_piJoin, Option.map_some]

/-- Validate the actual residual against the actual selected inductive
header: full head/universe instance, parameter prefix and complete arity. -/
def checkRecursiveField (env : Kernel.Env) (parameters : Telescope)
    (motives : List MotiveRd) (n : MinorRd) (a j depth : Nat) : Bool :=
  if j < motives.length then
    let m := motives.getD j default
    match matchMotive env parameters m, readFieldResidual env n a depth with
    | some h, some result =>
      decide (result.getAppFn = .const m.ind m.indUs ∧
        result.getAppArgs.take parameters.length = bvarsAt parameters.length (a + depth) ∧
        result.getAppArgs.length = parameters.length + h.indices.length)
    | _, _ => false
  else false

/-- The real header comparison supplies the missing recursive saturation.
All constructor-field and motive-header domains remain present in the two
readers and the existing CtorOk; no count is assumed as this lemma's result. -/
theorem checkRecursiveField_index_count {env : Kernel.Env}
    (parameters : Telescope) (motives : List MotiveRd) (n : MinorRd)
    (checked : n.CtorOk env parameters.length motives parameters)
    (metadata : n.paramMetas.length = parameters.length)
    (a j : Nat) (ys : Telescope) (idx : List Kernel.Expr)
    (recursive : (a, j, ys, idx) ∈ n.recFields)
    (accepted : checkRecursiveField env parameters motives n a j ys.length = true) :
    j < motives.length ∧ idx.length = (motives.getD j default).idxs.length := by
  have residual := readFieldResidual_of_recField parameters motives n checked metadata a j ys idx recursive
  by_cases bound : j < motives.length
  · cases header : matchMotive env parameters (motives.getD j default) with
    | none =>
      simp only [checkRecursiveField, ite_eq_left bound, header, residual,
        Bool.false_eq_true] at accepted
    | some h =>
      have saturation := of_decide_eq_true (show decide
          ((Kernel.Expr.mkAppN (.const (motives.getD j default).ind (motives.getD j default).indUs)
              (bvarsAt parameters.length (a + ys.length) ++ idx)).getAppFn =
                .const (motives.getD j default).ind (motives.getD j default).indUs ∧
            (Kernel.Expr.mkAppN (.const (motives.getD j default).ind (motives.getD j default).indUs)
              (bvarsAt parameters.length (a + ys.length) ++ idx)).getAppArgs.take parameters.length =
                bvarsAt parameters.length (a + ys.length) ∧
            (Kernel.Expr.mkAppN (.const (motives.getD j default).ind (motives.getD j default).indUs)
              (bvarsAt parameters.length (a + ys.length) ++ idx)).getAppArgs.length =
                parameters.length + h.indices.length) = true by
        simpa only [checkRecursiveField, ite_eq_left bound, header, residual] using accepted)
      have indexLength : h.indices.length = (motives.getD j default).idxs.length := by
        simpa only [List.length_map] using congrArg List.length (matchMotive_sound header).2.2
      have totalLength : parameters.length + idx.length = parameters.length + h.indices.length := by
        simpa only [Kernel.Expr.getAppArgs_mkAppN, Kernel.Expr.getAppArgs,
          List.nil_append, List.length_append, bvarsAt, List.length_map, List.length_range]
          using saturation.2.2
      exact ⟨bound, (Nat.add_left_cancel totalLength).trans indexLength⟩
  · simp only [checkRecursiveField, ite_eq_right bound, Bool.false_eq_true] at accepted

/-- The whole actual recursive-field inventory is checked, without a subset
or an assumed nonempty minor. A minor with no recursive fields is valid. -/
def checkRecursiveFields (env : Kernel.Env) (parameters : Telescope)
    (motives : List MotiveRd) (n : MinorRd) : Bool :=
  n.recFields.all fun (a, j, ys, _) => checkRecursiveField env parameters motives n a j ys.length

/-- Every record in the existing recursive-field inventory receives the
actual-header count conclusion. No selected field or IH is silently omitted. -/
theorem checkRecursiveFields_saturation {env : Kernel.Env}
    (parameters : Telescope) (motives : List MotiveRd) (n : MinorRd)
    (checked : n.CtorOk env parameters.length motives parameters)
    (metadata : n.paramMetas.length = parameters.length)
    (accepted : checkRecursiveFields env parameters motives n = true) :
    ∀ a j ys idx, (a, j, ys, idx) ∈ n.recFields →
      idx.length = (motives.getD j default).idxs.length := by
  intro a j ys idx recursive
  have every := List.all_eq_true.mp accepted
  have selected : checkRecursiveField env parameters motives n a j ys.length = true :=
    every (a, j, ys, idx) recursive
  exact (checkRecursiveField_index_count parameters motives n checked metadata
    a j ys idx recursive selected).2

end InstalledHeader

/-- Internal composition eliminates the free index-count input in favor of
the actual complete header checks. Accepted-source completeness and the
general WHNF branch must still discharge these checks; this is not a narrowed
replacement for the original final theorem. -/
theorem RecRd.predicate_of_literal_header_constructor_steps
    {V : Type u} [Kernel.SetTheory V] {env : Kernel.Env} {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params : List V)
    (paramsTyped : TeleTyped strong.public.cval env φ ρ (R.params.map Prod.fst) params)
    (predicate : Nat → List V → Prop)
    (headers : ∀ n ∈ R.minors,
      InstalledHeader.checkMinorResult env R.params R.motives n = true)
    (recursiveHeaders : ∀ n ∈ R.minors,
      InstalledHeader.checkRecursiveFields env R.params R.motives n = true)
    (steps : ∀ n ∈ R.minors,
      MinorStep.ConstructorStep strong.public.cval env φ ρ params R.np R.motives n predicate)
    (arguments : List V)
    (typed : TeleTyped strong.public.cval env φ (pushArguments ρ params)
      ((R.majorMotive.tele R.np).map Prod.fst) arguments) :
    predicate R.major arguments := by
  apply R.predicate_of_shape_checked_constructor_steps checked strong φ ρ params
    paramsTyped predicate headers (steps := steps) (arguments := arguments) (typed := typed)
  intro n present
  have minor := checked.2.2.2.2 n present
  exact InstalledHeader.checkRecursiveFields_saturation R.params R.motives n
    minor.2.2.2.2.2 minor.2.1 (recursiveHeaders n present)

end Ix.CompileCert.Pj

#print axioms Ix.CompileCert.Pj.MinorRd.ih_arguments_lift
#print axioms Ix.CompileCert.Pj.MinorRd.ih_spine
#print axioms Ix.CompileCert.Pj.RecRd.ih_arguments_typed
#print axioms Ix.CompileCert.Pj.RecRd.ih_predicate
#print axioms Ix.CompileCert.Pj.graded_piJoin_domain_at
#print axioms Ix.CompileCert.Pj.MinorRd.ih_value_typed
#print axioms Ix.CompileCert.Pj.RecRd.minor_inhabited_of_applied_step
#print axioms Ix.CompileCert.Pj.MinorRd.recField_position
#print axioms Ix.CompileCert.Pj.MinorRd.recField_present
#print axioms Ix.CompileCert.Pj.take_singleton_drop
#print axioms Ix.CompileCert.Pj.RecRd.recursive_premises_of_ihs
#print axioms Ix.CompileCert.Pj.RecRd.minor_inhabited_of_constructor_step
#print axioms Ix.CompileCert.Pj.RecRd.predicate_of_shape_checked_constructor_steps
#print axioms Ix.CompileCert.Pj.InstalledHeader.readConstructorFields_of_CtorOk
#print axioms Ix.CompileCert.Pj.InstalledHeader.readFieldResidual_of_recField
#print axioms Ix.CompileCert.Pj.InstalledHeader.checkRecursiveField_index_count
#print axioms Ix.CompileCert.Pj.InstalledHeader.checkRecursiveFields_saturation
#print axioms Ix.CompileCert.Pj.RecRd.predicate_of_literal_header_constructor_steps
