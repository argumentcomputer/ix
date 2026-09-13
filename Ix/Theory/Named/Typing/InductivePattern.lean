/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Typing.InductiveLemmas
import Ix.Theory.Named.Typing.Pattern

open Ix.Theory (VLevel)

/-! # Generated iota rules as patterns

Every iota rule generated for a certified mutual block
(`BlockGenerationChecked.rule`) is a closed defeq between lambda telescopes
whose left body is a `SimplePattern.iota` spine: the owning family's recursor
applied to the shared parameters, all motives, all minors, and the
constructor's result indices, with a constructor-headed major premise. This
module makes that connection exact and proves the generic pattern facts the
Church–Rosser `Params` interface demands of one certified block:

* `rulePattern` is the `SimplePattern` of one flattened constructor's rule,
  and `ruleLhsBody_matches` matches the exact generated left body against it
  at the rule's recursor levels.
* `IotaPat` is the block's pattern set, associating each rule's pattern with
  an RHS template (the registered right tower applied to the captured common
  arguments and fields) and a check list (parameter and result-index
  agreement between the recursor spine and the major premise).
* `pat_simple`, `pat_uniq`, `pat_app_l`, `pat_app_l_uniq`, and
  `pat_app_uniq` are exactly the `Params` obligations, specialized to
  `IotaPat`; their name-freshness inputs come from the certified block's
  `blockGeneratedNames` nodup bit, and the major-arity agreement between
  same-recursor rules comes from the analyzer's terminal `blockTarget?`
  arity equation.

The block supplies the `Params` facts. Pattern soundness (`pat_wf`) and the
block-local environment assembler are defined in `Typing/InductivePatternWF.lean`.
This module installs no open-environment `Params` instance. -/

namespace Ix.Theory.Named

open VExpr

namespace VExpr

@[simp] theorem bvarRevRange_length : ∀ (off m : Nat),
    (bvarRevRange off m).length = m
  | _, 0 => rfl
  | off, m+1 => by simp [bvarRevRange, bvarRevRange_length off m]

end VExpr

/-- Extending a `HeadConstN` spine by an application spine. -/
theorem HeadConstN.appN {c : Name} {ls : List VLevel} :
    ∀ (as : List VExpr) {n : Nat} {f : VExpr}, HeadConstN c ls n f →
      HeadConstN c ls (n + as.length) (VExpr.appN f as)
  | [], _, _, h => h
  | a :: as, n, f, h => by
    have := HeadConstN.appN as (h.app (a := a))
    show HeadConstN c ls (n + (as.length + 1)) (VExpr.appN (f.app a) as)
    rwa [(by omega : n + (as.length + 1) = n + 1 + as.length)]

namespace VInductDecl

/-! ## Positional facts about the checked pairings -/

theorem pairNormalizedFamilies_getElem? :
    ∀ (raws : List VInductiveType) (views : List CheckedFamilyData) (t : Nat)
      {family : NormalizedFamily},
      (pairNormalizedFamilies raws views)[t]? = some family →
      raws[t]? = some family.raw ∧ views[t]? = some family.view
  | raw :: raws, view :: views, 0, family => by
    intro h
    cases h
    exact ⟨rfl, rfl⟩
  | raw :: raws, view :: views, t+1, family => by
    intro h
    simpa using pairNormalizedFamilies_getElem? raws views t
      (by simpa [pairNormalizedFamilies] using h)
  | [], _, t, _ => by intro h; simp [pairNormalizedFamilies] at h
  | _ :: _, [], t, _ => by intro h; simp [pairNormalizedFamilies] at h

theorem pairNormalizedCtors_getElem? :
    ∀ (raws : List VConstVal) (views : List CheckedCtor) (t : Nat)
      {ctor : NormalizedCtor},
      (pairNormalizedCtors raws views)[t]? = some ctor →
      raws[t]? = some ctor.raw ∧ views[t]? = some ctor.view
  | raw :: raws, view :: views, 0, ctor => by
    intro h
    cases h
    exact ⟨rfl, rfl⟩
  | raw :: raws, view :: views, t+1, ctor => by
    intro h
    simpa using pairNormalizedCtors_getElem? raws views t
      (by simpa [pairNormalizedCtors] using h)
  | [], _, t, _ => by intro h; simp [pairNormalizedCtors] at h
  | _ :: _, [], t, _ => by intro h; simp [pairNormalizedCtors] at h

/-- The erased family-data spine reads back its exact member facts: ordinal
consecutiveness, the indexing family, the analyzer equations, and the
per-family acceptance bit. -/
theorem CheckedFamilies.data_getElem? {source : VInductDecl} {params : List VExpr} :
    ∀ {ord : Nat} {types : List VInductiveType}
      (fs : CheckedFamilies source params ord types) (t : Nat)
      {fd : CheckedFamilyData},
      fs.data[t]? = some fd →
      ∃ type, types[t]? = some type ∧ fd.ordinal = ord + t ∧ fd.value = type ∧
        fd.indices = ctorFields (VExpr.dropN source.nparams type.type) ∧
        fd.constructors = type.ctors.map (CheckedCtor.ofBlock source) ∧
        blockFamilyCore source params (ord + t) type = true
  | _, _, .nil, t, fd => by intro h; simp [CheckedFamilies.data] at h
  | ord, _, .cons head tail, 0, fd => by
    intro h
    cases h
    exact ⟨_, rfl, rfl, rfl, head.indices_eq, head.constructors_eq, head.accepted⟩
  | ord, _, .cons head tail, t+1, fd => by
    intro h
    obtain ⟨type, h1, h2, h3, h4, h5, h6⟩ :=
      CheckedFamilies.data_getElem? tail t (by simpa [CheckedFamilies.data] using h)
    exact ⟨type, by simpa using h1, by omega, h3, h4, h5,
      by rw [(by omega : ord + (t + 1) = ord + 1 + t)]; exact h6⟩

/-! ## Arity extraction from the analyzer's terminal target check -/

theorem blockTarget?_loop_length {U np j : Nat} {names : List Name}
    {head : VExpr} {args : List VExpr} :
    ∀ (headers : List FamilyHeader) (t : Nat) {target : Nat} {idxs : List VExpr},
      blockTarget?.loop U np j names head args t headers = some (target, idxs) →
      t ≤ target ∧ ∃ header, headers[target - t]? = some header ∧
        args.length = np + header.indices ∧ idxs = args.drop np
  | [], t, target, idxs => by intro h; simp [blockTarget?.loop] at h
  | header :: headers, t, target, idxs => by
    intro h
    rw [blockTarget?.loop] at h
    split at h
    · rename_i hcond
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact ⟨Nat.le_refl _, header, by simp, hcond.1.1.2, rfl⟩
    · obtain ⟨hle, header', h1, h2, h3⟩ :=
        blockTarget?_loop_length headers (t+1) h
      refine ⟨Nat.le_of_succ_le hle, header', ?_, h2, h3⟩
      rw [(by omega : target - t = (target - (t+1)) + 1)]
      simpa using h1

/-- A successful mutual target recognition pins the target's index arity to
its family header. -/
theorem blockTarget?_length {U np j : Nat} {headers : List FamilyHeader}
    {names : List Name} {B : VExpr} {target : Nat} {idxs : List VExpr}
    (h : blockTarget? U np j headers names B = some (target, idxs)) :
    ∃ header, headers[target]? = some header ∧
      (VExpr.appArgs B []).length = np + header.indices ∧
      idxs = (VExpr.appArgs B []).drop np := by
  rw [blockTarget?] at h
  obtain ⟨hle, header, h1, h2, h3⟩ := blockTarget?_loop_length headers 0 h
  exact ⟨header, by simpa using h1, h2, h3⟩

/-- The terminal of an accepted mutual constructor shape is a successful
`blockTarget?` recognition of the owner family, past all fields. -/
theorem blockStage3Ctor_result {U np : Nat} {headers : List FamilyHeader}
    {names : List Name} {owner : Nat} :
    ∀ (B : VExpr) (j : Nat), blockStage3Ctor U np headers names owner j B = true →
      ∃ idxs, blockTarget? U np (j + (ctorFields B).length) headers names
        (VExpr.resultOf B) = some (owner, idxs) := by
  intro B
  induction B with
    (intro j h
     simp only [blockStage3Ctor] at h
     try (split at h
          · rename_i target idxs heq
            refine ⟨idxs, ?_⟩
            simp only [ctorFields, List.length_nil, Nat.add_zero, VExpr.resultOf]
            rwa [(by simpa using h : target = owner)] at heq
          · cases h))
  | forallE A rest _ ihR =>
    rw [Bool.and_eq_true] at h
    obtain ⟨-, h2⟩ := h
    obtain ⟨idxs, hidx⟩ := ihR (j+1) h2
    refine ⟨idxs, ?_⟩
    simp only [ctorFields, List.length_cons, VExpr.resultOf]
    rwa [(by omega : j + ((ctorFields rest).length + 1) = j + 1 + (ctorFields rest).length)]

/-! ## Name transport across the normalization boundary -/

theorem sameCtorHeaders_names : ∀ {cs cs' : List VConstVal},
    sameCtorHeaders cs cs' = true → cs.map (·.name) = cs'.map (·.name)
  | [], [], _ => rfl
  | c :: cs, c' :: cs', h => by
    simp only [sameCtorHeaders, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, h.1.1, sameCtorHeaders_names h.2]
  | [], _ :: _, h => by simp [sameCtorHeaders] at h
  | _ :: _, [], h => by simp [sameCtorHeaders] at h

theorem sameTypeHeaders_names : ∀ {tys tys' : List VInductiveType},
    sameTypeHeaders tys tys' = true →
    tys.map (·.name) = tys'.map (·.name) ∧
      tys.flatMap (fun ty => ty.ctors.map (·.name)) =
        tys'.flatMap (fun ty => ty.ctors.map (·.name))
  | [], [], _ => ⟨rfl, rfl⟩
  | ty :: tys, ty' :: tys', h => by
    simp only [sameTypeHeaders, Bool.and_eq_true, beq_iff_eq] at h
    have ih := sameTypeHeaders_names h.2
    simp only [List.map_cons, List.flatMap_cons, h.1.1.1, ih.1, ih.2,
      sameCtorHeaders_names h.1.2, and_self]
  | [], _ :: _, h => by simp [sameTypeHeaders] at h
  | _ :: _, [], h => by simp [sameTypeHeaders] at h

/-- The reserved generated names are unchanged by normalization: they are
computed from family and constructor identities only. -/
theorem blockGeneratedNames_eq_of_sameTypeHeaders
    {tys tys' : List VInductiveType} (h : sameTypeHeaders tys tys' = true) :
    blockGeneratedNames tys = blockGeneratedNames tys' := by
  obtain ⟨h1, h2⟩ := sameTypeHeaders_names h
  have h3 : tys.map (fun ty => (.str ty.name "rec" : Name)) =
      tys'.map (fun ty => (.str ty.name "rec" : Name)) := by
    have := congrArg (List.map (fun n => (.str n "rec" : Name))) h1
    simpa [List.map_map, Function.comp_def] using this
  simp only [blockGeneratedNames, h1, h2, h3]

namespace BlockGenerationChecked

variable {source : VInductDecl} (gen : source.BlockGenerationChecked)

/-! ## Inventory facts from the certified block -/

include gen in
/-- The reserved generated names of the raw source are collision-free: the
analyzer certifies the view's inventory, and normalization retains every
identity. -/
theorem blockGeneratedNames_nodup :
    (blockGeneratedNames source.types).Nodup := by
  have hshape := gen.block.normalization.shape_eq
  simp only [normalizationShape, Bool.and_eq_true, beq_iff_eq] at hshape
  rw [blockGeneratedNames_eq_of_sameTypeHeaders hshape.2]
  have h := gen.block.checked.names_nodup
  rwa [gen.block.checked.names_eq] at h

/-! ## Named components of one generated iota rule -/

/-- Field count of one flattened constructor, as bound by its iota rule. -/
def ruleFieldCount (constructor : NormalizedBlockCtor) : Nat :=
  (constructor.ctor.fieldsR source.uvars source.nparams gen.elimination).length

/-- The result-index spine of one iota rule body, in the rule's binder
context. -/
def ruleIdx (constructor : NormalizedBlockCtor) : List VExpr :=
  constructor.ctor.resultIndicesR source.uvars gen.elimination |>.map
    fun e => e.liftN (gen.familyCount + gen.minorCount)
      (gen.ruleFieldCount constructor)

/-- The binder telescope shared by both towers of one iota rule. -/
def ruleBinders (constructor : NormalizedBlockCtor) : List VExpr :=
  gen.paramsTel ++ gen.motiveTypes ++ gen.minorTypes ++
    VExpr.liftTelN (gen.familyCount + gen.minorCount)
      (constructor.ctor.fieldsR source.uvars source.nparams gen.elimination) 0

/-- The constructor-headed major premise of one iota rule body. -/
def ruleCtorApp (constructor : NormalizedBlockCtor) : VExpr :=
  VExpr.appN (.const constructor.ctor.raw.name gen.sourceLevels)
    (VExpr.bvarRevRange
        (gen.ruleFieldCount constructor + (gen.familyCount + gen.minorCount))
        source.nparams ++
      VExpr.bvarRevRange 0 (gen.ruleFieldCount constructor))

/-- The exact left body of one generated iota rule: the owner's recursor
applied to the common arguments, the constructor's result indices, and the
constructor-headed major premise. -/
def ruleLhsBody (constructor : NormalizedBlockCtor) : VExpr :=
  VExpr.appN (gen.recBase (gen.ruleFieldCount constructor) constructor.owner)
    (gen.ruleIdx constructor ++ [gen.ruleCtorApp constructor])

/-- The generated rule's left side is exactly the shared binder telescope
over the `SimplePattern.iota` spine. -/
theorem rule_lhs (i : Nat) (constructor : NormalizedBlockCtor) :
    (gen.rule i constructor).lhs =
      VExpr.lamN (gen.ruleBinders constructor) (gen.ruleLhsBody constructor) := rfl

/-! ## The pattern of one generated iota rule -/

/-- The recursor constant owning one flattened constructor's iota rule. -/
def ruleRecName (constructor : NormalizedBlockCtor) : Name :=
  .str (gen.familyNameAt constructor.owner) "rec"

/-- Major-argument arity of one iota rule: shared parameters, all motives,
all minors, and the constructor's result indices. -/
def ruleMajorArity (constructor : NormalizedBlockCtor) : Nat :=
  source.nparams + gen.familyCount + gen.minorCount +
    (constructor.ctor.resultIndicesR source.uvars gen.elimination).length

/-- Argument arity of one iota rule's constructor-headed major premise. -/
def ruleArgArity (constructor : NormalizedBlockCtor) : Nat :=
  source.nparams + gen.ruleFieldCount constructor

/-- The `SimplePattern` of one generated iota rule. -/
@[reducible] def rulePattern (constructor : NormalizedBlockCtor) : SimplePattern :=
  .iota (gen.ruleRecName constructor) (gen.ruleMajorArity constructor)
    constructor.ctor.raw.name (gen.ruleArgArity constructor)

/-- The generated left body is matched by the rule's pattern, at exactly the
rule's recursor levels. -/
theorem ruleLhsBody_matches (constructor : NormalizedBlockCtor) :
    ∃ m2, ((gen.rulePattern constructor).toPattern).Matches
      (gen.ruleLhsBody constructor) gen.recLevels m2 := by
  rw [rulePattern, SimplePattern.toPattern_iota]
  have hleft : HeadConstN (gen.ruleRecName constructor) gen.recLevels
      (gen.ruleMajorArity constructor)
      (VExpr.appN (gen.recBase (gen.ruleFieldCount constructor) constructor.owner)
        (gen.ruleIdx constructor)) := by
    have h0 : HeadConstN (gen.ruleRecName constructor) gen.recLevels 0
        (.const (gen.ruleRecName constructor) gen.recLevels) := .const
    have h1 := (h0.appN (VExpr.bvarRevRange (gen.ruleFieldCount constructor)
      (source.nparams + gen.familyCount + gen.minorCount)))
    have h2 := h1.appN (as := gen.ruleIdx constructor)
    rw [VExpr.bvarRevRange_length] at h2
    have harity : 0 + (source.nparams + gen.familyCount + gen.minorCount) +
        (gen.ruleIdx constructor).length = gen.ruleMajorArity constructor := by
      simp only [ruleIdx, ruleMajorArity, List.length_map]; omega
    rwa [harity] at h2
  have hright : HeadConstN constructor.ctor.raw.name gen.sourceLevels
      (gen.ruleArgArity constructor) (gen.ruleCtorApp constructor) := by
    have h0 : HeadConstN constructor.ctor.raw.name gen.sourceLevels 0
        (.const constructor.ctor.raw.name gen.sourceLevels) := .const
    have h1 := h0.appN (as := VExpr.bvarRevRange
      (gen.ruleFieldCount constructor + (gen.familyCount + gen.minorCount))
      source.nparams ++ VExpr.bvarRevRange 0 (gen.ruleFieldCount constructor))
    rw [List.length_append, VExpr.bvarRevRange_length, VExpr.bvarRevRange_length] at h1
    have harity : 0 + (source.nparams + gen.ruleFieldCount constructor) =
        gen.ruleArgArity constructor := by simp only [ruleArgArity]; omega
    rwa [harity] at h1
  have hbody : gen.ruleLhsBody constructor =
      .app (VExpr.appN (gen.recBase (gen.ruleFieldCount constructor) constructor.owner)
          (gen.ruleIdx constructor))
        (gen.ruleCtorApp constructor) := by
    rw [ruleLhsBody, VExpr.appN_append]
    rfl
  rw [hbody]
  exact RecursorIotaPattern.matches_of hleft hright

/-! ## Positional anatomy of the flattened constructors -/

/-- The checked spine assigns family ordinals positionally. -/
theorem families_getElem?_ordinal {t : Nat} {family : NormalizedFamily}
    (h : gen.families[t]? = some family) : family.view.ordinal = t := by
  have h' : (pairNormalizedFamilies source.types
      gen.block.checked.families.data)[t]? = some family := h
  obtain ⟨-, hview⟩ := pairNormalizedFamilies_getElem? _ _ t h'
  obtain ⟨type, -, hord, -, -, -, -⟩ := CheckedFamilies.data_getElem? _ t hview
  simpa using hord

/-- Position `t` of the paired family list is the `t`-th source family. -/
theorem families_getElem?_raw {t : Nat} {family : NormalizedFamily}
    (h : gen.families[t]? = some family) : source.types[t]? = some family.raw :=
  (pairNormalizedFamilies_getElem? source.types
    gen.block.checked.families.data t h).1

/-- A family lookup names the owning recursor's family. -/
theorem familyNameAt_eq {t : Nat} {family : NormalizedFamily}
    (h : gen.families[t]? = some family) :
    gen.familyNameAt t = family.raw.name := by
  simp [familyNameAt, h]

/-- One flattened constructor decomposes into its owner family lookup and
its position inside that family's pairing. -/
theorem flatCtors_anatomy {constructor : NormalizedBlockCtor}
    (hc : constructor ∈ gen.flatCtors) :
    ∃ t family, gen.families[t]? = some family ∧
      constructor.owner = t ∧
      constructor.familyName = family.raw.name ∧
      constructor.familyIndices = family.view.indices ∧
      constructor.ctor ∈ family.ctorPairs := by
  have hc' : constructor ∈ gen.families.flatMap (·.blockCtors) := hc
  rw [List.mem_flatMap] at hc'
  obtain ⟨family, hfamily, hmem⟩ := hc'
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 hfamily
  simp only [NormalizedFamily.blockCtors, List.mem_map] at hmem
  obtain ⟨ctor, hctor, rfl⟩ := hmem
  exact ⟨t, family, ht, gen.families_getElem?_ordinal ht, rfl, rfl, hctor⟩

/-! ## The analyzer's arity equation for pattern majors -/

/-- Every flattened constructor's checked result-index spine has exactly its
owner family's index arity: the analyzer's terminal `blockTarget?` equation
transports through the checked spine. -/
theorem view_resultIndices_length {constructor : NormalizedBlockCtor}
    (hc : constructor ∈ gen.flatCtors) :
    constructor.ctor.view.resultIndices.length =
      constructor.familyIndices.length := by
  obtain ⟨t, family, ht, -, -, hindices, hmem⟩ := gen.flatCtors_anatomy hc
  have ht' : (pairNormalizedFamilies source.types
      gen.block.checked.families.data)[t]? = some family := ht
  obtain ⟨-, hview⟩ := pairNormalizedFamilies_getElem? _ _ t ht'
  obtain ⟨vtype, hvty, -, -, hvindices, hvctors, hvcore⟩ :=
    CheckedFamilies.data_getElem? _ t hview
  rw [Nat.zero_add] at hvcore
  obtain ⟨s, hs⟩ := List.mem_iff_getElem?.1 hmem
  have hs' : (pairNormalizedCtors family.raw.ctors
      family.view.constructors)[s]? = some constructor.ctor := hs
  obtain ⟨-, hviewCtor⟩ := pairNormalizedCtors_getElem? _ _ s hs'
  rw [hvctors, List.getElem?_map] at hviewCtor
  obtain ⟨c₀, hc₀, hview_eq⟩ : ∃ c₀, vtype.ctors[s]? = some c₀ ∧
      CheckedCtor.ofBlock _ c₀ = constructor.ctor.view := by
    cases h0 : vtype.ctors[s]? with
    | none => rw [h0] at hviewCtor; cases hviewCtor
    | some c₀ => rw [h0] at hviewCtor; exact ⟨c₀, rfl, by simpa using hviewCtor⟩
  simp only [blockFamilyCore, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hvcore
  have hstage := (hvcore.2 c₀ (List.mem_of_getElem? hc₀)).2
  obtain ⟨idxs, htarget⟩ := blockStage3Ctor_result _ 0 hstage
  obtain ⟨header, hheader, hlen, -⟩ := blockTarget?_length htarget
  rw [familyHeaders, List.getElem?_map, hvty, Option.map_some] at hheader
  have hri : constructor.ctor.view.resultIndices =
      (VExpr.appArgs (VExpr.resultOf (VExpr.dropN
        gen.block.normalization.view.nparams c₀.type)) []).drop
        gen.block.normalization.view.nparams := by
    rw [← hview_eq]; rfl
  rw [hri, hindices, hvindices, List.length_drop, hlen]
  cases hheader
  show gen.block.normalization.view.nparams +
      (ctorFields (VExpr.dropN gen.block.normalization.view.nparams
        vtype.type)).length -
      gen.block.normalization.view.nparams =
    (ctorFields (VExpr.dropN gen.block.normalization.view.nparams
      vtype.type)).length
  omega

/-- Pattern major arity through the owner family's index count. -/
theorem ruleMajorArity_eq {constructor : NormalizedBlockCtor}
    (hc : constructor ∈ gen.flatCtors) :
    gen.ruleMajorArity constructor =
      source.nparams + gen.familyCount + gen.minorCount +
        constructor.familyIndices.length := by
  simp only [ruleMajorArity, NormalizedCtor.resultIndicesR, List.length_map,
    gen.view_resultIndices_length hc]

/-! ## Name freshness of the generated inventory -/

include gen in
private theorem nodup_parts :
    (source.types.map (·.name)).Nodup ∧
      (source.types.flatMap fun ty => ty.ctors.map (·.name)).Nodup ∧
      ∀ a ∈ (source.types.flatMap fun ty => ty.ctors.map (·.name)),
        ∀ b ∈ source.types.map (fun ty => (.str ty.name "rec" : Name)), a ≠ b := by
  have h := gen.blockGeneratedNames_nodup
  rw [blockGeneratedNames, List.nodup_append] at h
  obtain ⟨hAB, -, hdisj⟩ := h
  rw [List.nodup_append] at hAB
  exact ⟨hAB.1, hAB.2.1, fun a ha b hb =>
    hdisj a (List.mem_append.2 (.inr ha)) b hb⟩

/-- Family positions are recoverable from raw family names. -/
theorem families_name_inj {t t' : Nat} {family family' : NormalizedFamily}
    (h : gen.families[t]? = some family) (h' : gen.families[t']? = some family')
    (hname : family.raw.name = family'.raw.name) : t = t' := by
  have h1 := gen.families_getElem?_raw h
  have h1' := gen.families_getElem?_raw h'
  have hm : (source.types.map (·.name))[t]? = some family.raw.name := by
    rw [List.getElem?_map, h1, Option.map_some]
  have hm' : (source.types.map (·.name))[t']? = some family.raw.name := by
    rw [List.getElem?_map, h1', Option.map_some, hname]
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hm
  exact (List.getElem?_inj hlt gen.nodup_parts.1).1 (hm.trans hm'.symm)

/-- Flattened positions are recoverable from raw constructor names. -/
theorem flatCtors_name_inj {i i' : Nat} {c c' : NormalizedBlockCtor}
    (h : gen.flatCtors[i]? = some c) (h' : gen.flatCtors[i']? = some c')
    (hname : c.ctor.raw.name = c'.ctor.raw.name) : i = i' ∧ c = c' := by
  have hnodup : ((source.blockConstructorConstants).map (·.name)).Nodup := by
    rw [VInductDecl.blockConstructorConstants, List.map_flatMap]
    exact gen.nodup_parts.2.1
  have hm : ((source.blockConstructorConstants).map (·.name))[i]? =
      some c.ctor.raw.name := by
    rw [List.getElem?_map, ← gen.flatCtors_map_raw, List.getElem?_map, h]
    rfl
  have hm' : ((source.blockConstructorConstants).map (·.name))[i']? =
      some c.ctor.raw.name := by
    rw [List.getElem?_map, ← gen.flatCtors_map_raw, List.getElem?_map, h',
      hname]
    rfl
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hm
  have hii : i = i' := (List.getElem?_inj hlt hnodup).1 (hm.trans hm'.symm)
  subst hii
  exact ⟨rfl, Option.some.inj (h.symm.trans h')⟩

/-- No family's recursor name collides with any flattened constructor's
name. -/
theorem recName_ne_ctorName {family : NormalizedFamily}
    (hfam : family ∈ gen.families) {constructor : NormalizedBlockCtor}
    (hc : constructor ∈ gen.flatCtors) :
    (.str family.raw.name "rec" : Name) ≠ constructor.ctor.raw.name := by
  have hmemC : constructor.ctor.raw.name ∈
      source.types.flatMap fun ty => ty.ctors.map (·.name) := by
    have h1 : constructor.ctor.raw ∈ source.blockConstructorConstants := by
      rw [← gen.flatCtors_map_raw]
      exact List.mem_map_of_mem hc
    rw [VInductDecl.blockConstructorConstants, List.mem_flatMap] at h1
    obtain ⟨ty, hty, hmem⟩ := h1
    rw [List.mem_flatMap]
    exact ⟨ty, hty, List.mem_map_of_mem hmem⟩
  have hmemR : (.str family.raw.name "rec" : Name) ∈
      source.types.map (fun ty => (.str ty.name "rec" : Name)) := by
    have h1 : family.raw ∈ source.types := by
      rw [← gen.families_map_raw]
      exact List.mem_map_of_mem hfam
    exact List.mem_map_of_mem h1
  intro heq
  exact gen.nodup_parts.2.2 _ hmemC _ hmemR heq.symm

/-- Two flattened constructors with the same owning recursor name share
their owner and their family's index telescope. -/
theorem ruleRecName_inj {c c' : NormalizedBlockCtor}
    (hc : c ∈ gen.flatCtors) (hc' : c' ∈ gen.flatCtors)
    (h : gen.ruleRecName c = gen.ruleRecName c') :
    c.owner = c'.owner ∧ c.familyIndices = c'.familyIndices := by
  obtain ⟨t, family, ht, ho, -, hi, -⟩ := gen.flatCtors_anatomy hc
  obtain ⟨t', family', ht', ho', -, hi', -⟩ := gen.flatCtors_anatomy hc'
  rw [ruleRecName, ruleRecName, ho, ho', gen.familyNameAt_eq ht,
    gen.familyNameAt_eq ht'] at h
  have hnames : family.raw.name = family'.raw.name := by
    injection h with h1 h2
  have ht2 : t = t' := gen.families_name_inj ht ht' hnames
  subst ht2
  cases Option.some.inj (ht.symm.trans ht')
  exact ⟨ho.trans ho'.symm, hi.trans hi'.symm⟩

/-- Rule distinctness: distinct flattened positions carry distinct
patterns. -/
theorem rulePattern_inj {i i' : Nat} {c c' : NormalizedBlockCtor}
    (h : gen.flatCtors[i]? = some c) (h' : gen.flatCtors[i']? = some c')
    (heq : gen.rulePattern c = gen.rulePattern c') : i = i' ∧ c = c' := by
  injection heq with h1 h2 h3 h4
  exact gen.flatCtors_name_inj h h' h3

/-! ## Rule payloads: RHS templates and agreement checks -/

/-- Closedness inputs for one certified block's rule payloads: the towers a
rule's RHS template and checks embed as fixed template constants. Concrete
fixtures discharge this bundle by `decide`; the pattern-soundness proof
derives it from the staged environment's rule well-formedness. -/
structure RuleClosure : Prop where
  rhs_closed : ∀ ⦃i : Nat⦄ ⦃constructor : NormalizedBlockCtor⦄,
    gen.flatCtors[i]? = some constructor →
      ((gen.rule i constructor).rhs).ClosedN 0
  idxTower_closed : ∀ ⦃constructor : NormalizedBlockCtor⦄,
    constructor ∈ gen.flatCtors → ∀ e ∈ gen.ruleIdx constructor,
      (VExpr.lamN (gen.ruleBinders constructor) e).ClosedN 0

/-- The template capture list shared by every payload tower: the recursor
side's parameters, motives, and minors, then the major premise's fields. -/
def captureArgs (constructor : NormalizedBlockCtor) :
    List (((gen.rulePattern constructor).toPattern).RHS) :=
  ((Pattern.varNPaths (.const (gen.ruleRecName constructor))
      (gen.ruleMajorArity constructor)).take
    (source.nparams + gen.familyCount + gen.minorCount)).map
      (fun path => .var (.inl path)) ++
  ((Pattern.varNPaths (.const constructor.ctor.raw.name)
      (gen.ruleArgArity constructor)).drop source.nparams).map
      (fun path => .var (.inr path))

/-- The RHS template of one rule: the registered right tower applied to the
captured common arguments and fields. -/
def ruleRHS (hcl : gen.RuleClosure) {i : Nat} {constructor : NormalizedBlockCtor}
    (h : gen.flatCtors[i]? = some constructor) :
    ((gen.rulePattern constructor).toPattern).RHS :=
  Pattern.RHS.appN (.fixed ((gen.rule i constructor).rhs) (hcl.rhs_closed h))
    (gen.captureArgs constructor)

/-- The check list of one rule: the major premise's parameters must agree
with the recursor side's parameters, and the recursor side's index arguments
must agree with the constructor's computed result indices (as fixed index
towers applied to the captures). -/
def ruleCheck (hcl : gen.RuleClosure) {constructor : NormalizedBlockCtor}
    (hc : constructor ∈ gen.flatCtors) :
    ((gen.rulePattern constructor).toPattern).Check :=
  let recPaths := Pattern.varNPaths (.const (gen.ruleRecName constructor))
    (gen.ruleMajorArity constructor)
  let ctorPaths := Pattern.varNPaths (.const constructor.ctor.raw.name)
    (gen.ruleArgArity constructor)
  let common := source.nparams + gen.familyCount + gen.minorCount
  let idxChecks :=
    ((gen.ruleIdx constructor).attach.zip (recPaths.drop common)).foldr
      (fun ep rest =>
        .defeq (.var (.inl ep.2))
          (Pattern.RHS.appN
            (.fixed (VExpr.lamN (gen.ruleBinders constructor) ep.1.1)
              (hcl.idxTower_closed hc ep.1.1 ep.1.2))
            (gen.captureArgs constructor)) rest)
      .true
  ((ctorPaths.take source.nparams).zip (recPaths.take source.nparams)).foldr
    (fun pr rest => .defeq (.var (.inr pr.1)) (.var (.inl pr.2)) rest)
    idxChecks

/-- Position `i` of the certified block's flattened constructor list. -/
abbrev ruleEntry (i : Nat) (constructor : NormalizedBlockCtor) : Prop :=
  gen.flatCtors[i]? = some constructor

/-- A decidable sufficient condition for `RuleClosure`, discharging concrete
fixtures by evaluation. -/
theorem RuleClosure.of_all
    (h1 : gen.flatCtors.zipIdx.all (fun ic =>
      decide (((gen.rule ic.2 ic.1).rhs).ClosedN 0)) = true)
    (h2 : gen.flatCtors.all (fun c => (gen.ruleIdx c).all fun e =>
      decide ((VExpr.lamN (gen.ruleBinders c) e).ClosedN 0)) = true) :
    gen.RuleClosure := by
  constructor
  · intro i constructor h
    have hmem : (constructor, i) ∈ gen.flatCtors.zipIdx := by
      apply List.mem_of_getElem? (i := i)
      rw [List.getElem?_zipIdx, h, Option.map_some, Nat.zero_add]
    exact of_decide_eq_true (List.all_eq_true.1 h1 _ hmem)
  · intro constructor hc e he
    exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h2 _ hc) _ he)

/-- The pattern set of one certified block: each flattened constructor's
rule pattern with its template and checks. -/
inductive IotaPat (hcl : gen.RuleClosure) :
    (p : Pattern) → p.RHS × p.Check → Prop where
  | mk {i : Nat} {constructor : NormalizedBlockCtor}
      (h : gen.ruleEntry i constructor) :
      IotaPat hcl ((gen.rulePattern constructor).toPattern)
        (gen.ruleRHS hcl h, gen.ruleCheck hcl (List.mem_of_getElem? h))

/-! ## The `Params` obligations for one certified block -/

/-- `Params.pat_simple` for the block's pattern set. -/
theorem IotaPat.pat_simple {hcl : gen.RuleClosure} {p : Pattern}
    {r : p.RHS × p.Check} (H : gen.IotaPat hcl p r) :
    ∃ sp : SimplePattern, p = sp.toPattern := by
  cases H with | mk h => exact ⟨_, rfl⟩

/-- Rule recovery: a pattern in the block's set determines its flattened
rule position and constructor. -/
theorem IotaPat.recover {hcl : gen.RuleClosure} {p : Pattern}
    {r : p.RHS × p.Check} (H : gen.IotaPat hcl p r) :
    ∃ (i : Nat) (constructor : NormalizedBlockCtor),
      gen.flatCtors[i]? = some constructor ∧
      p = (gen.rulePattern constructor).toPattern ∧
      ∀ (i' : Nat) (constructor' : NormalizedBlockCtor),
        gen.flatCtors[i']? = some constructor' →
        (gen.rulePattern constructor').toPattern = p →
        i' = i ∧ constructor' = constructor := by
  cases H with | @mk i constructor h =>
  refine ⟨i, constructor, h, rfl, ?_⟩
  intro i' constructor' h' heq
  have := RecursorIotaPattern.inj heq
  exact gen.flatCtors_name_inj h' h this.2.2.1

/-- `Params.pat_uniq` for the block's pattern set. -/
theorem IotaPat.pat_uniq {hcl : gen.RuleClosure} {p₁ p₂ p₃ p₄ : Pattern}
    {r : p₁.RHS × p₁.Check} {r' : p₂.RHS × p₂.Check}
    (H1 : gen.IotaPat hcl p₁ r) (H2 : gen.IotaPat hcl p₂ r')
    (H3 : Subpattern p₃ p₁) (H4 : p₂.inter p₃ = some p₄) :
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  cases H1 with | @mk i c h =>
  cases H2 with | @mk i' c' h' =>
  rcases RecursorIotaPattern.subpattern_inv H3 with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · obtain ⟨hR, hM, hC, hN, rfl⟩ := RecursorIotaPattern.inter_some H4
    obtain ⟨rfl, rfl⟩ := gen.flatCtors_name_inj h' h hC
    exact ⟨rfl, rfl, HEq.rfl⟩
  · obtain ⟨hb, hj'⟩ := RecursorIotaPattern.inter_varN_const_some H4
    obtain ⟨-, hIdx⟩ := gen.ruleRecName_inj (List.mem_of_getElem? h)
      (List.mem_of_getElem? h') hb
    have hM : gen.ruleMajorArity c' = gen.ruleMajorArity c := by
      rw [gen.ruleMajorArity_eq (List.mem_of_getElem? h'),
        gen.ruleMajorArity_eq (List.mem_of_getElem? h), hIdx]
    omega
  · obtain ⟨hb, -⟩ := RecursorIotaPattern.inter_varN_const_some H4
    obtain ⟨t', family', ht', ho', -, -, -⟩ :=
      gen.flatCtors_anatomy (List.mem_of_getElem? h')
    have hrec : gen.ruleRecName c' = (.str family'.raw.name "rec" : Name) := by
      rw [ruleRecName, ho', gen.familyNameAt_eq ht']
    refine absurd ?_ (gen.recName_ne_ctorName (List.mem_of_getElem? ht')
      (List.mem_of_getElem? h))
    rw [← hrec, hb]

/-- `Params.pat_app_l` for the block's pattern set. -/
theorem IotaPat.pat_app_l {hcl : gen.RuleClosure} {p : Pattern}
    {r : p.RHS × p.Check} {p₁ p₂ p₃ p₄ : Pattern}
    (H : gen.IotaPat hcl p r) (h : Subpattern (.app p₁ p₂) p) :
    ¬Subpattern (.app p₃ p₄) p₁ := by
  cases H with | @mk i c hi =>
  obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
  intro hsub
  obtain ⟨j', hj', heq'⟩ := hsub.varN_const_le
  cases j' <;> exact absurd heq' (by simp [Pattern.varN])

/-- `Params.pat_app_l_uniq` for the block's pattern set. -/
theorem IotaPat.pat_app_l_uniq {hcl : gen.RuleClosure} {p p' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check} {p₁ p₂ p₁' p₂' p₃ : Pattern}
    (H : gen.IotaPat hcl p r) (H' : gen.IotaPat hcl p' r')
    (h : Subpattern (.app p₁ p₂) p) (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  cases H with | @mk i c hi =>
  cases H' with | @mk i' c' hi' =>
  obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
  obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h'
  obtain ⟨j, hj, heq⟩ := h₃.varN_const_le
  cases j with
  | zero => exact absurd heq (by simp [Pattern.varN])
  | succ j'' =>
    rw [show Pattern.varN (.const (gen.ruleRecName c)) (j'' + 1) =
        .var (Pattern.varN (.const (gen.ruleRecName c)) j'') from rfl] at heq
    injection heq with heq'
    subst heq'
    by_cases hname : gen.ruleRecName c' = gen.ruleRecName c
    · obtain ⟨-, hIdx⟩ := gen.ruleRecName_inj (List.mem_of_getElem? hi')
        (List.mem_of_getElem? hi) hname
      have hM : gen.ruleMajorArity c' = gen.ruleMajorArity c := by
        rw [gen.ruleMajorArity_eq (List.mem_of_getElem? hi'),
          gen.ruleMajorArity_eq (List.mem_of_getElem? hi), hIdx]
      rw [hname]
      exact Pattern.varN_const_inter_of_ne_arity (by omega) _ _
    · exact Pattern.varN_const_inter_of_ne_name hname _ _

/-- `Params.pat_app_uniq` for the block's pattern set. -/
theorem IotaPat.pat_app_uniq {hcl : gen.RuleClosure} {p p' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    (H : gen.IotaPat hcl p r) (H' : gen.IotaPat hcl p' r')
    (h : Subpattern (.app p₁ p₂) p) (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern p₃ p₁) (h₃' : Subpattern p₃' p₂') : p₃.inter p₃' = none := by
  cases H with | @mk i c hi =>
  cases H' with | @mk i' c' hi' =>
  obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
  obtain ⟨-, rfl⟩ := RecursorIotaPattern.app_subpattern h'
  obtain ⟨j, hj, rfl⟩ := h₃.varN_const_le
  obtain ⟨j', hj', rfl⟩ := h₃'.varN_const_le
  refine Pattern.varN_const_inter_of_ne_name ?_ _ _
  obtain ⟨t, family, ht, ho, -, -, -⟩ :=
    gen.flatCtors_anatomy (List.mem_of_getElem? hi)
  have hrec : gen.ruleRecName c = (.str family.raw.name "rec" : Name) := by
    rw [ruleRecName, ho, gen.familyNameAt_eq ht]
  rw [hrec]
  exact gen.recName_ne_ctorName (List.mem_of_getElem? ht)
    (List.mem_of_getElem? hi')

/-! ## Axiom closures of the generic pattern facts -/

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockGenerationChecked.ruleLhsBody_matches [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockGenerationChecked.view_resultIndices_length [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockGenerationChecked.rulePattern_inj [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockGenerationChecked.IotaPat.pat_simple [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockGenerationChecked.IotaPat.recover [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockGenerationChecked.IotaPat.pat_uniq [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockGenerationChecked.IotaPat.pat_app_l [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockGenerationChecked.IotaPat.pat_app_l_uniq [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockGenerationChecked.IotaPat.pat_app_uniq [propext, Quot.sound]

end BlockGenerationChecked

end VInductDecl

end Ix.Theory.Named
