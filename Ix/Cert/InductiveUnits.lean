import Ix.Cert.InductiveBlocks
import Ix.Cert.RecursorReads
import Ix.Cert.SourceConversion
import Ix.Cert.LowerTransfer
import Ix.Cert.RecordReadings

/-! # Inductive blocks read as quotient Source's units renamed

An inductive group converts to a block every item of which is a function of its Lean
constant (`convertInductive_src`: `srcType`, `srcCtor`, `srcRec`), so quotient Source's block,
renamed, is too (`quotient_src`: `tgtType`, `tgtCtor`, `tgtRec`, recursors of inert rules in
canonical levels by `canonRec_eq`).

The reader reads a block compiled in Lean's order (`InductiveBlocks.readRecord_family`) and its
recursors from their own records (`RecursorReads.readRecursors_ok`). Given, at the closure's
context, every type's and constructor's key, header and a reading related to its Lean type
(`TypeFacts`, `CtorFacts`), and every recursor's index entry, record, key, header and readings
related to its Lean terms (`RecFacts`), the readings are quotient Source's renamed
(`related_renamed'`), and the record reads as the lowering of quotient Source's block renamed,
the recursors' motives aside, which only a nested block, whose motives lowering never reads,
may differ in (`inductive_reads`). With quotient Source's lowering of the group, that is the
unit's reading from every related state (`inductive_unit_reads`, through
`LowerTransfer.lowerInductive_transfer_motives`).

What the closure and the compile run supply stays a premise: the record and its layout, the
block shape and the recursor index, the keys, the related readings and headers, the index's
motives outside a nested block, good keys and quotient Source's lowering. -/

namespace Ix.Cert.InductiveUnits

open Ix.Kernel Ix.Kernel.Reader
open Ix.LeanIngress (FiberMap Numbering ingressKey ingressExpr canonLevelIn mapLevels LevelMemoInv mapLevelsGo
  mapLevelsGo_spec canonInfo canonExprM canonValM)
open Ix.Cert.SourceConversion (ownNum recNum motiveOf TypeRel CtorRel RuleRel RecRel convertInductive_exact)
open Ix.Cert.RecordReadings (sourceNames quotientHeader quotientHeader_eq forall₂_eq_map)

/-! ## Quotient Source's block, item by item -/

/-- A Lean term's conversion under a numbering (a placeholder where it does not convert). -/
def convOf (σ : Numbering) (e : Ix.Expr) : CExpr .source :=
  match ingressExpr σ.pos e with
  | .ok k => k
  | .error _ => .sort .zero

theorem convOf_eq {σ : Numbering} {e : Ix.Expr} {k : CExpr .source} (h : ingressExpr σ.pos e = .ok k) :
    convOf σ e = k := by
  simp [convOf, h]

/-- A type's item in the converted block. -/
def srcType (v : Ix.InductiveVal) : CVal .source × Nat × Nat :=
  (⟨ingressKey v.cnst.name, (ownNum v.cnst).params, convOf (ownNum v.cnst) v.cnst.type⟩, v.numParams, v.numIndices)

/-- A constructor's item in the converted block. -/
def srcCtor (c : Ix.ConstructorVal) : CVal .source × Nat × Nat :=
  (⟨ingressKey c.cnst.name, (ownNum c.cnst).params, convOf (ownNum c.cnst) c.cnst.type⟩, c.numParams, c.numFields)

/-- A recursor rule in the converted block. -/
def srcRule (σ : Numbering) (rule : Ix.RecursorRule) : RecRule .source :=
  ⟨ingressKey rule.ctor, rule.nfields, 0, .inert, convOf σ rule.rhs, false, false, false⟩

/-- A recursor's counts in the converted block. -/
def srcCounts (types : Array Ix.InductiveVal) (r : Ix.RecursorVal) : RecCounts :=
  ⟨r.numParams, r.numMotives, r.numMinors, r.numIndices, r.k, motiveOf types r⟩

/-- A recursor's item in the converted block. -/
def srcRec (types : Array Ix.InductiveVal) (first : Ix.InductiveVal) (r : Ix.RecursorVal) :
    CVal .source × RecCounts × List (RecRule .source) :=
  (⟨ingressKey r.cnst.name, (recNum first r).params, convOf (recNum first r) r.cnst.type⟩, srcCounts types r,
   r.rules.toList.map (srcRule (recNum first r)))

/-- The converted block of an inductive group. -/
def srcBlock (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal))
    (recs : Array Ix.RecursorVal) (first : Ix.InductiveVal) : BlockRead .source :=
  ⟨first.numParams, (types.toList.map srcType).toArray, ((ctors.toList.flatMap (·.toList)).map srcCtor).toArray,
   (ctors.toList.map fun cs => cs.toList.map (ingressKey ·.cnst.name)).toArray,
   (recs.toList.map (srcRec types first)).toArray⟩

theorem array_eq_of_toList {α : Type} {a : Array α} {l : List α} (h : a.toList = l) : a = l.toArray := by
  rw [← h, Array.toArray_toList]

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ a ∈ l, ∃ b ∈ m, R a b
  | [], [], .nil, _, ha => absurd ha List.not_mem_nil
  | _ :: _, b :: _, .cons hab rest, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨b', hb', hr⟩ := forall₂_mem_left rest a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', hr⟩

/-- **Quotient Source's conversion of an inductive group, as a function of its constants**,
with the conversion's checks: the types share the first's parameter count, and every
constructor's converted type has as many leading binders as it declares parameters and
fields. -/
theorem convertInductive_src {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {conv : Ix.LeanIngress.Converted}
    (ran : Ix.LeanIngress.convertInductive types ctors recs = .ok conv) :
    ∃ first, types[0]? = some first ∧ conv = .inductive (srcBlock types ctors recs first) ∧
      (∀ v ∈ types.toList, v.numParams = first.numParams) ∧
      ∀ c ∈ ctors.toList.flatMap (·.toList), first.numParams + c.numFields = piTeleLen (srcCtor c).1.type := by
  obtain ⟨first', hfirst', -, -, hparams, -⟩ :=
    Ix.CompileCert.SourceConstructorPositions.convertInductive_spec types ctors recs conv ran
  obtain ⟨first, rb, hfirst, rfl, hnp, ht, hc, hn, hr⟩ := convertInductive_exact ran
  have e : first = first' := Option.some.inj (hfirst.symm.trans hfirst')
  subst e
  have hC : ∀ c e, CtorRel first.numParams c e → e = srcCtor c := by
    rintro c ⟨⟨n, l, t⟩, p, i⟩ ⟨hname, hlps, htype, hp, hi, -⟩
    simp only at hname hlps htype hp hi
    rw [srcCtor, convOf_eq htype, hname, hlps, hp, hi]
  refine ⟨first, hfirst, ?_, hparams, ?_⟩
  · congr 1
    obtain ⟨nPd, T, C, N, Rs⟩ := rb
    simp only at hnp ht hc hn hr
    subst hnp
    have hT : T.toList = types.toList.map srcType := by
      refine forall₂_eq_map ?_ ht
      rintro v ⟨⟨n, l, t⟩, p, i⟩ ⟨hname, hlps, htype, hp, hi⟩
      simp only at hname hlps htype hp hi
      rw [srcType, convOf_eq htype, hname, hlps, hp, hi]
    have hR : Rs.toList = recs.toList.map (srcRec types first) := by
      refine forall₂_eq_map ?_ hr
      rintro r ⟨⟨n, l, t⟩, rc, rules⟩ ⟨hname, hlps, htype, hcounts, hrules⟩
      simp only at hname hlps htype hcounts hrules
      have hrules' : rules = r.rules.toList.map (srcRule (recNum first r)) := by
        refine forall₂_eq_map ?_ hrules
        rintro rule rr ⟨hrr, hrhs⟩
        rw [hrr, srcRule, ← convOf_eq hrhs]
      rw [srcRec, convOf_eq htype, hname, hlps, hcounts, hrules']
      rfl
    rw [array_eq_of_toList hT, array_eq_of_toList (forall₂_eq_map hC hc), array_eq_of_toList hn,
      array_eq_of_toList hR]
    rfl
  · intro c hc'
    obtain ⟨e, -, hrel⟩ := forall₂_mem_left hc c hc'
    rw [← hC c e hrel]
    exact hrel.2.2.2.2.2

theorem mapM_state {σ α β : Type} (g : α → StateM σ β) (h : α → β) (I : σ → Prop) :
    ∀ (l : List α), (∀ a ∈ l, ∀ s, I s → (g a s).1 = h a ∧ I (g a s).2) →
      ∀ s, I s → (l.mapM g s).1 = l.map h ∧ I (l.mapM g s).2
  | [], _, s, hs => ⟨rfl, hs⟩
  | a :: l, hg, s, hs => by
    obtain ⟨h1, h2⟩ := hg a List.mem_cons_self s hs
    obtain ⟨h3, h4⟩ := mapM_state g h I l (fun b hb => hg b (List.mem_cons_of_mem _ hb)) _ h2
    simp only [List.mapM_cons]
    show ((g a s).1 :: (l.mapM g (g a s).2).1) = _ ∧ I (l.mapM g (g a s).2).2
    rw [h1, h3]
    exact ⟨rfl, h4⟩

/-- **A recursor of inert rules in canonical levels**: its type's and its rules' right-hand
sides' levels, over its own level parameters. -/
theorem canonRec_eq (c : Ix.Kernel.ConstantVal .source) (rules : List (RecRule .source))
    (inert : ∀ r ∈ rules, r.fire = .inert) :
    canonInfo (.recInfo c 0 0 rules) = .recInfo { c with type := mapLevels (canonLevelIn c.levelParams) c.type } 0 0
      (rules.map fun r => { r with rhs := mapLevels (canonLevelIn c.levelParams) r.rhs }) := by
  unfold canonInfo canonInfo.go
  simp only []
  have h1 := mapLevelsGo_spec (f := canonLevelIn c.levelParams) c.type (memo := {})
    (by intro k v hk; simp at hk)
  dsimp only [StateT.run', StateT.run, bind, StateT.bind, pure, StateT.pure, Functor.map, canonValM, canonExprM]
  split
  rename_i a s heq
  have ha := congrArg Prod.fst heq
  rw [(mapM_state _ (fun r : RecRule .source => { r with rhs := mapLevels (canonLevelIn c.levelParams) r.rhs })
    (LevelMemoInv (canonLevelIn c.levelParams)) rules ?step _ h1.2).1] at ha
  · dsimp only at ha ⊢
    rw [← ha, h1.1]
  · intro r hr s hs
    have hf := inert r hr
    have h2 := mapLevelsGo_spec (f := canonLevelIn c.levelParams) r.rhs hs
    rw [hf]
    exact ⟨by rw [← h2.1]; rfl, h2.2⟩

variable (ρ : FiberMap) (f : Mode.Id .source → Mode.Id .anon)

/-- A type's item in quotient Source's block, renamed. -/
def tgtType (v : Ix.InductiveVal) : CVal .anon × Nat × Nat :=
  ((quotientHeader ρ (srcType v).1).mapKeys f, v.numParams, v.numIndices)

/-- A constructor's item in quotient Source's block, renamed. -/
def tgtCtor (c : Ix.ConstructorVal) : CVal .anon × Nat × Nat :=
  ((quotientHeader ρ (srcCtor c).1).mapKeys f, c.numParams, c.numFields)

/-- A recursor rule in quotient Source's block, renamed. -/
def tgtRule (σ : Numbering) (rule : Ix.RecursorRule) : RecRule .anon :=
  ⟨(Ix.LeanIngress.Key.subst ρ (ingressKey rule.ctor)).map f, rule.nfields, 0, .inert,
   (mapLevels (canonLevelIn σ.params) (Ix.LeanIngress.Expr.substKeys ρ (convOf σ rule.rhs))).mapKeys f,
   false, false, false⟩

/-- A recursor's item in quotient Source's block, renamed, at a motive. -/
def tgtRec (types : Array Ix.InductiveVal) (first : Ix.InductiveVal) (r : Ix.RecursorVal) (motive : Option Nat) :
    CVal .anon × RecCounts × List (RecRule .anon) :=
  ((quotientHeader ρ (srcRec types first r).1).mapKeys f, { srcCounts types r with motive },
   r.rules.toList.map (tgtRule ρ f (recNum first r)))

/-- Quotient Source's block of an inductive group, renamed, at the recursors' motives. -/
def tgtBlock (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal))
    (recs : Array Ix.RecursorVal) (first : Ix.InductiveVal) (motives : Ix.RecursorVal → Option Nat) :
    BlockRead .anon :=
  ⟨first.numParams, (types.toList.map (tgtType ρ f)).toArray,
   ((ctors.toList.flatMap (·.toList)).map (tgtCtor ρ f)).toArray,
   (ctors.toList.map fun cs => cs.toList.map fun c => (Ix.LeanIngress.Key.subst ρ (ingressKey c.cnst.name)).map f).toArray,
   (recs.toList.map fun r => tgtRec ρ f types first r (motives r)).toArray⟩

/-- **Quotient Source's block of an inductive group, renamed**, item by item. -/
theorem quotient_src (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal))
    (recs : Array Ix.RecursorVal) (first : Ix.InductiveVal) :
    (Ix.LeanIngress.BlockRead.canon (Ix.LeanIngress.BlockRead.substKeys ρ (srcBlock types ctors recs first))).mapKeys f =
      tgtBlock ρ f types ctors recs first (motiveOf types) := by
  simp only [Ix.LeanIngress.BlockRead.canon, Ix.LeanIngress.BlockRead.substKeys, srcBlock, tgtBlock,
    BlockRead.mapKeys, List.map_toArray, List.map_map, BlockRead.mk.injEq, true_and]
  refine ⟨rfl, rfl, by simp [Function.comp_def], ?_⟩
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply, srcRec, List.map_map]
  rw [canonRec_eq _ _ (fun rr hrr => by
    simp only [List.mem_map] at hrr
    obtain ⟨rule, -, rfl⟩ := hrr
    rfl)]
  simp only [tgtRec, List.map_map, quotientHeader_eq]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  refine List.map_congr_left fun rule _ => rfl

/-! ## Readings of Lean terms, renamed -/

/-- **A term related to a Lean term at quotient Source's names renamed is the term's
quotient Source conversion renamed**, at a numbering keeping the level parameters apart and
aligned with the reader's level parameters. -/
theorem related_renamed' {params : List Ix.Name} {σ : Ix.Name → LevelParam} {param : Nat → LevelParam}
    (inj : ∀ a ∈ params, ∀ b ∈ params, σ a = σ b → a = b)
    (aligned : ∀ i (h : i < params.length), param i = σ params[i]) {source : Ix.Expr} {target : CExpr .anon}
    (related : Ix.CompileCert.ExpressionState.Related (sourceNames ρ f)
      (Ix.CompileCert.UniversePipeline.LevelMeaning params σ param) source target) :
    ∃ converted, ingressExpr σ source = .ok converted ∧
      target = (mapLevels (canonLevelIn (params.map σ)) (Ix.LeanIngress.Expr.substKeys ρ converted)).mapKeys f := by
  obtain ⟨converted, hconv, hm⟩ := Ix.CompileCert.CanonLevelReading.related_ingress_canon inj aligned related
  refine ⟨converted, hconv, ?_⟩
  rw [RecordReadings.matches_eq (g := fun k => (Ix.LeanIngress.Key.subst ρ k).map f)
    (h := canonLevelIn (params.map σ)) (fun k k' ⟨n, hk, hn⟩ => by rw [hn, hk]) (fun l l' hl => hl.symm) hm,
    RecordReadings.mapKL_eq]

/-- A numbering of distinct level parameters numbers them by position, the first last when
large. -/
theorem pos_nodup_any {names : Array Ix.Name} (hnd : names.toList.Nodup) (large : Bool) {i : Nat}
    (hi : i < names.size) :
    (Numbering.mk names large).pos names[i] = if large then (if i = 0 then names.size - 1 else i - 1) else i := by
  rcases names with ⟨l⟩
  have h := RecordReadings.findIdx?_beqRaw_nodup hnd (i := i) (by simpa using hi)
  have h' : (List.toArray l).findIdx? (Ix.Name.beqRaw · (List.toArray l)[i]) = some i := by
    simpa [List.findIdx?_toArray] using h
  unfold Numbering.pos
  simp only [h']
  cases i <;> cases large <;> simp

/-- It keeps them apart. -/
theorem pos_inj_any {names : Array Ix.Name} (hnd : names.toList.Nodup) (large : Bool) :
    ∀ a ∈ names.toList, ∀ b ∈ names.toList,
      (Numbering.mk names large).pos a = (Numbering.mk names large).pos b → a = b := by
  intro a ha b hb he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  simp only [Array.getElem_toList] at he ⊢
  have hi' : i < names.size := by simpa using hi
  have hj' : j < names.size := by simpa using hj
  rw [pos_nodup_any hnd large hi', pos_nodup_any hnd large hj'] at he
  have : i = j := by
    cases large
    · simpa using he
    · simp only [↓reduceIte] at he
      have he' : (if i = 0 then names.size - 1 else i - 1 : Nat) = (if j = 0 then names.size - 1 else j - 1 : Nat) := he
      split at he' <;> split at he' <;> omega
  subst this
  rfl

/-- A level-parameter list read back at its own positions. -/
theorem recParam_aligned (σ : Ix.Name → LevelParam) (params : List Ix.Name) :
    ∀ i (h : i < params.length), recParam (params.map σ) i = σ params[i] := by
  intro i h
  simp [recParam, List.getD_eq_getElem?_getD, h]

theorem piTeleLen_tgt (g : Ix.Kernel.Level → Ix.Kernel.Level) (e : CExpr .source) :
    piTeleLen ((mapLevels g (Ix.LeanIngress.Expr.substKeys ρ e)).mapKeys f) = piTeleLen e := by
  induction e <;> simp_all [piTeleLen, mapLevels, Ix.LeanIngress.Expr.substKeys, Expr.mapKeys]

/-! ## What the reader reads of a block's items -/

open Ix.CompileCert.ExpressionState (Related)
open Ix.CompileCert.UniversePipeline (LevelMeaning)

/-- A Lean name's key in quotient Source, renamed. -/
abbrev srcKey (n : Ix.Name) : CName .anon := (Ix.LeanIngress.Key.subst ρ (ingressKey n)).map f

/-- **What the reader needs of constructor `j` of type `i`**: its position and safety, its
key, a reading of its type related to its Lean type, and its header. -/
structure CtorFacts (cx : Ctx .anon) (owner : Address) (mr : MemberReader .anon) (i j : Nat)
    (c : Ix.ConstructorVal) (ct : Ixon.Constructor) : Prop where
  cidx : ct.cidx.toNat = j
  safe : ct.isUnsafe = false
  key : cx.memberKey (.ctor owner i j) = .ok (srcKey ρ f c.cnst.name)
  type : ∃ type, mr.read ct.typ = .ok type ∧
    Related (sourceNames ρ f) (LevelMeaning c.cnst.levelParams.toList (ownNum c.cnst).pos id) c.cnst.type type
  lvls : ct.lvls.toNat = c.cnst.levelParams.size
  params : ct.params.toNat = c.numParams
  fields : ct.fields.toNat = c.numFields
  nodup : c.cnst.levelParams.toList.Nodup

/-- **What the reader needs of type `i`**: its key, a reading of its type related to its Lean
type, its safety and header, and its constructors'. -/
structure TypeFacts (cx : Ctx .anon) (owner : Address) (mr : MemberReader .anon) (i : Nat)
    (v : Ix.InductiveVal) (cs : Array Ix.ConstructorVal) (t : Ixon.Inductive) : Prop where
  key : cx.memberKey (.member owner i) = .ok (srcKey ρ f v.cnst.name)
  type : ∃ type, mr.read t.typ = .ok type ∧
    Related (sourceNames ρ f) (LevelMeaning v.cnst.levelParams.toList (ownNum v.cnst).pos id) v.cnst.type type
  safe : t.isUnsafe = false
  params : t.params.toNat = v.numParams
  lvls : t.lvls.toNat = v.cnst.levelParams.size
  indices : t.indices.toNat = v.numIndices
  nodup : v.cnst.levelParams.toList.Nodup
  nctors : t.ctors.size = cs.size
  ctors : ∀ j (hj : j < cs.size) (hj' : j < t.ctors.size), CtorFacts ρ f cx owner mr i j cs[j] t.ctors[j]

theorem tgtType_type (v : Ix.InductiveVal) : (tgtType ρ f v).1.type =
    (mapLevels (canonLevelIn (ownNum v.cnst).params)
      (Ix.LeanIngress.Expr.substKeys ρ (convOf (ownNum v.cnst) v.cnst.type))).mapKeys f := by
  simp only [tgtType, srcType, quotientHeader_eq]
  rfl

theorem tgtCtor_type (c : Ix.ConstructorVal) : (tgtCtor ρ f c).1.type =
    (mapLevels (canonLevelIn (ownNum c.cnst).params)
      (Ix.LeanIngress.Expr.substKeys ρ (convOf (ownNum c.cnst) c.cnst.type))).mapKeys f := by
  simp only [tgtCtor, srcCtor, quotientHeader_eq]
  rfl

/-- A reading related to a type's Lean type is quotient Source's, renamed. -/
theorem type_read {mr : MemberReader .anon} {v : Ix.InductiveVal} {typ : Ixon.Expr}
    (nodup : v.cnst.levelParams.toList.Nodup)
    (h : ∃ type, mr.read typ = .ok type ∧
      Related (sourceNames ρ f) (LevelMeaning v.cnst.levelParams.toList (ownNum v.cnst).pos id) v.cnst.type type) :
    mr.read typ = .ok (tgtType ρ f v).1.type := by
  obtain ⟨type, hread, hrel⟩ := h
  obtain ⟨conv, hconv, rfl⟩ :=
    related_renamed' ρ f (RecordReadings.pos_inj nodup) (RecordReadings.pos_aligned nodup) hrel
  rw [hread, tgtType_type, convOf_eq hconv]
  rfl

/-- A reading related to a constructor's Lean type is quotient Source's, renamed. -/
theorem ctor_read {mr : MemberReader .anon} {c : Ix.ConstructorVal} {typ : Ixon.Expr}
    (nodup : c.cnst.levelParams.toList.Nodup)
    (h : ∃ type, mr.read typ = .ok type ∧
      Related (sourceNames ρ f) (LevelMeaning c.cnst.levelParams.toList (ownNum c.cnst).pos id) c.cnst.type type) :
    mr.read typ = .ok (tgtCtor ρ f c).1.type := by
  obtain ⟨type, hread, hrel⟩ := h
  obtain ⟨conv, hconv, rfl⟩ :=
    related_renamed' ρ f (RecordReadings.pos_inj nodup) (RecordReadings.pos_aligned nodup) hrel
  rw [hread, tgtCtor_type, convOf_eq hconv]
  rfl

theorem type_item {cx : Ctx .anon} {owner : Address} {mr : MemberReader .anon} {i : Nat} {v : Ix.InductiveVal}
    {cs : Array Ix.ConstructorVal} {t : Ixon.Inductive} (h : TypeFacts ρ f cx owner mr i v cs t) :
    ((⟨srcKey ρ f v.cnst.name, List.range t.lvls.toNat, (tgtType ρ f v).1.type⟩ : CVal .anon),
      t.params.toNat, t.indices.toNat) = tgtType ρ f v := by
  rw [h.lvls, h.params, h.indices, ← RecordReadings.params_nodup h.nodup]
  simp only [tgtType, srcType, quotientHeader_eq]
  rfl

theorem ctor_item {cx : Ctx .anon} {owner : Address} {mr : MemberReader .anon} {i j : Nat}
    {c : Ix.ConstructorVal} {ct : Ixon.Constructor} (h : CtorFacts ρ f cx owner mr i j c ct) :
    ((⟨srcKey ρ f c.cnst.name, List.range ct.lvls.toNat, (tgtCtor ρ f c).1.type⟩ : CVal .anon),
      ct.params.toNat, ct.fields.toNat) = tgtCtor ρ f c := by
  rw [h.lvls, h.params, h.fields, ← RecordReadings.params_nodup h.nodup]
  simp only [tgtCtor, srcCtor, quotientHeader_eq]
  rfl

open Ix.Cert.InductiveBlocks (CtorFactsAt ctorReadsAt) in
/-- **A type's constructors read as quotient Source's, renamed**, from position `j`. -/
theorem ctorClass_go (cx : Ctx .anon) (owner : Address) (mr : MemberReader .anon) (nPd : Nat)
    (ctorKey : Nat → Nat → CName .anon) (i : Nat) :
    ∀ (tl : List Ixon.Constructor) (cl : List Ix.ConstructorVal) (j : Nat), tl.length = cl.length →
      (∀ k (hk : k < tl.length) (hk' : k < cl.length), CtorFacts ρ f cx owner mr i (j + k) cl[k] tl[k] ∧
        ctorKey i (j + k) = srcKey ρ f cl[k].cnst.name ∧
        nPd + cl[k].numFields = piTeleLen (srcCtor cl[k]).1.type) →
      CtorFactsAt cx owner mr nPd ctorKey i j tl (cl.map fun c => (tgtCtor ρ f c).1.type) ∧
        ctorReadsAt ctorKey i j tl (cl.map fun c => (tgtCtor ρ f c).1.type) = cl.map (tgtCtor ρ f)
  | [], [], _, _, _ => ⟨trivial, rfl⟩
  | ct :: tl, c :: cl, j, hlen, h => by
    obtain ⟨hf, hkey, hcheck⟩ := h 0 (by simp) (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hf hkey hcheck
    have ih := ctorClass_go cx owner mr nPd ctorKey i tl cl (j + 1) (by simpa using hlen) (fun k hk hk' => by
      have := h (k + 1) (by simpa using hk) (by simpa using hk')
      simp only [List.getElem_cons_succ] at this
      rw [show j + 1 + k = j + (k + 1) by omega]
      exact this)
    refine ⟨⟨hf.cidx, hf.safe, by rw [hkey]; exact hf.key, ctor_read ρ f hf.nodup hf.type, ?_, ih.1⟩, ?_⟩
    · rw [hf.fields, hcheck]
      show piTeleLen (srcCtor c).1.type = piTeleLen (tgtCtor ρ f c).1.type
      rw [tgtCtor_type, piTeleLen_tgt]
      rfl
    · simp only [List.map_cons, ctorReadsAt]
      rw [ih.2, hkey, ctor_item ρ f hf]
  | [], _ :: _, _, hlen, _ => absurd hlen (by simp)
  | _ :: _, [], _, hlen, _ => absurd hlen (by simp)

/-! ## Recursors -/

open Ix.Cert.RecursorReads (RecursorFacts recRead recReader ruleReads)

/-- **What the reader needs of a block's recursor**: its index entry, record, member, safety
and key; its level parameters as quotient Source numbers them; a reading of its type related
to its Lean type; its major inductive with a constructor per rule; every rule's constructor
key, field count and a reading of its right-hand side related to its Lean one; its counts;
and, outside a nested block, the motive its name gives. -/
structure RecFacts (cx : Ctx .anon) (blockLps : List LevelParam) (types : Array Ix.InductiveVal)
    (first : Ix.InductiveVal) (nested : Prop) (ref : ConstRef Address) (r : Ix.RecursorVal) : Prop where
  facts : ∃ entry rOwner j rc j', ∃ (rI : Ixon.Recursor) (major : Ixon.Inductive), ∃ mb mi,
    cx.index.recs[ref]? = some entry ∧ ref = .member rOwner j ∧ cx.store rOwner = some rc ∧
    (recursorMembers rc).find? (·.1 == j) = some (j', rI) ∧ rI.isUnsafe = false ∧
    cx.memberKey ref = .ok (srcKey ρ f r.cnst.name) ∧
    recLps entry.large blockLps = (recNum first r).params ∧
    (∃ type, (recReader cx rc rOwner (srcKey ρ f r.cnst.name) (recNum first r).params).read rI.typ = .ok type ∧
      Related (sourceNames ρ f) (LevelMeaning r.cnst.levelParams.toList (recNum first r).pos
        (recParam (recNum first r).params)) r.cnst.type type) ∧
    inductiveAt cx.store entry.major = some major ∧ major.ctors.size = rI.rules.size ∧
    entry.major = .member mb mi ∧ rI.rules.size = r.rules.size ∧
    (∀ k (hk : k < rI.rules.size) (hk' : k < r.rules.size),
      cx.memberKey (.ctor mb mi k) = .ok (srcKey ρ f r.rules[k].ctor) ∧
      rI.rules[k].fields.toNat = r.rules[k].nfields ∧
      ∃ rhs, (recReader cx rc rOwner (srcKey ρ f r.cnst.name) (recNum first r).params).read rI.rules[k].rhs =
          .ok rhs ∧
        Related (sourceNames ρ f) (LevelMeaning r.cnst.levelParams.toList (recNum first r).pos
          (recParam (recNum first r).params)) r.rules[k].rhs rhs) ∧
    rI.params.toNat = r.numParams ∧ rI.motives.toNat = r.numMotives ∧ rI.minors.toNat = r.numMinors ∧
    rI.indices.toNat = r.numIndices ∧ rI.k = r.k ∧ r.cnst.levelParams.toList.Nodup ∧
    (nested → some entry.motive = motiveOf types r)

/-- A reading related to a recursor's Lean term, at quotient Source's numbering of its level
parameters, is quotient Source's conversion renamed. -/
theorem rec_term_read {mr : MemberReader .anon} {first : Ix.InductiveVal} {r : Ix.RecursorVal}
    (nodup : r.cnst.levelParams.toList.Nodup) {source : Ix.Expr} {e : Ixon.Expr}
    (h : ∃ t, mr.read e = .ok t ∧ Related (sourceNames ρ f) (LevelMeaning r.cnst.levelParams.toList
      (recNum first r).pos (recParam (recNum first r).params)) source t) :
    mr.read e = .ok ((mapLevels (canonLevelIn (recNum first r).params)
      (Ix.LeanIngress.Expr.substKeys ρ (convOf (recNum first r) source))).mapKeys f) := by
  obtain ⟨t, hread, hrel⟩ := h
  obtain ⟨conv, hconv, rfl⟩ := related_renamed' ρ f (pos_inj_any nodup _)
    (recParam_aligned (recNum first r).pos r.cnst.levelParams.toList) hrel
  rw [hread, convOf_eq hconv]
  rfl

/-- The rule constructors' keys the reader reads. -/
def ruleKeyOf (r : Ix.RecursorVal) (k : Nat) : CName .anon :=
  ((r.rules[k]?).map fun rule => srcKey ρ f rule.ctor).getD (srcKey ρ f r.cnst.name)

/-- The rules' right-hand sides the reader reads. -/
def rhsOf (first : Ix.InductiveVal) (r : Ix.RecursorVal) (k : Nat) : CExpr .anon :=
  ((r.rules[k]?).map fun rule => (tgtRule ρ f (recNum first r) rule).rhs).getD (.sort .zero)

/-- **A recursor reads as quotient Source's, renamed**, at the index's motive. -/
theorem rec_facts {cx : Ctx .anon} {blockLps : List LevelParam} {types : Array Ix.InductiveVal}
    {first : Ix.InductiveVal} {nested : Prop} {ref : ConstRef Address} {r : Ix.RecursorVal}
    (h : RecFacts ρ f cx blockLps types first nested ref r) :
    ∃ m, RecursorFacts cx blockLps ref (tgtRec ρ f types first r (some m)) ∧
      (nested → some m = motiveOf types r) := by
  obtain ⟨entry, rOwner, j, rc, j', rI, major, mb, mi, hentry, href, hstore, hfind, hsafe, hkey, hlps, htype,
    hmajor, hmsize, hmb, hrsize, hrules, hp, hm, hn, hi, hk, nodup, hnested⟩ := h.facts
  refine ⟨entry.motive, ⟨entry, rOwner, j, rc, j', rI, srcKey ρ f r.cnst.name, _, major, mb, mi,
    ruleKeyOf ρ f r, rhsOf ρ f first r, hentry, href, hstore, hfind, hsafe, hkey,
    by rw [hlps]; exact rec_term_read ρ f nodup htype, hmajor, hmsize, hmb, ?_, ?_⟩, hnested⟩
  · intro x hx
    obtain ⟨rule, k⟩ := x
    have hx' := List.mem_zipIdx_iff_getElem?.mp hx
    simp only at hx'
    have hk1 : k < rI.rules.size := by
      have := (List.getElem?_eq_some_iff.mp hx').1
      simpa using this
    have hk2 : k < r.rules.size := hrsize ▸ hk1
    have hrule : rule = rI.rules[k] := by
      have := (List.getElem?_eq_some_iff.mp hx').2
      simpa using this.symm
    subst hrule
    obtain ⟨hck, -, hrhs⟩ := hrules k hk1 hk2
    refine ⟨?_, ?_⟩
    · simp only [ruleKeyOf, Array.getElem?_eq_getElem hk2, Option.map_some, Option.getD_some]
      exact hck
    · rw [hlps, rec_term_read ρ f nodup hrhs]
      simp only [rhsOf, Array.getElem?_eq_getElem hk2, Option.map_some, Option.getD_some, tgtRule]
  · rw [hlps]
    simp only [tgtRec, recRead, srcRec, quotientHeader_eq, srcCounts, hp, hm, hn, hi, hk]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [ruleReads]
    apply List.ext_getElem
    · simp [hrsize]
    · intro k h₁ h₂
      have hk1 : k < rI.rules.size := by simpa using h₂
      have hk2 : k < r.rules.size := hrsize ▸ hk1
      obtain ⟨-, hfields, -⟩ := hrules k hk1 hk2
      simp only [List.getElem_map, List.getElem_zipIdx, Array.getElem_toList, Nat.zero_add]
      simp only [ruleKeyOf, rhsOf, Array.getElem?_eq_getElem hk2, Option.map_some, Option.getD_some, hfields,
        tgtRule]

/-- A recursor item with its motive forgotten. -/
def eraseRec {md : Mode} (x : CVal md × RecCounts × List (RecRule md)) : CVal md × RecCounts × List (RecRule md) :=
  (x.1, { x.2.1 with motive := none }, x.2.2)

theorem tgtRec_erase (types : Array Ix.InductiveVal) (first : Ix.InductiveVal) (r : Ix.RecursorVal)
    (m m' : Option Nat) : eraseRec (tgtRec ρ f types first r m) = eraseRec (tgtRec ρ f types first r m') := rfl

/-- **A block's recursors read as quotient Source's, renamed**, at the index's motives. -/
theorem recs_facts {cx : Ctx .anon} {blockLps : List LevelParam} {types : Array Ix.InductiveVal}
    {first : Ix.InductiveVal} {nested : Prop} :
    ∀ {refs : List (ConstRef Address)} {rs : List Ix.RecursorVal},
      List.Forall₂ (RecFacts ρ f cx blockLps types first nested) refs rs →
      ∃ reads, List.Forall₂ (RecursorFacts cx blockLps) refs reads ∧
        reads.map eraseRec = (rs.map fun r => tgtRec ρ f types first r (motiveOf types r)).map eraseRec ∧
        (nested → reads = rs.map fun r => tgtRec ρ f types first r (motiveOf types r))
  | [], [], .nil => ⟨[], .nil, rfl, fun _ => rfl⟩
  | _ :: _, r :: _, .cons h rest => by
    obtain ⟨m, hm, hmot⟩ := rec_facts ρ f h
    obtain ⟨reads, hreads, herase, hnest⟩ := recs_facts rest
    refine ⟨_ :: reads, .cons hm hreads, ?_, fun hn => ?_⟩
    · simp only [List.map_cons, herase, tgtRec_erase ρ f types first r (some m) (motiveOf types r)]
    · simp only [List.map_cons, hnest hn, ← hmot hn]

/-- A list's `flatMap`, by position. -/
theorem flatMap_range {α β : Type} (F : α → List β) :
    ∀ l : List α, l.flatMap F = (List.range l.length).flatMap fun i => (l[i]?.map F).getD []
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_cons, List.flatMap_map,
      flatMap_range F l]
    rfl

/-! ## The block -/

open Ix.CompileCert.InductiveReading (blockSelf readRecursors)
open Ix.Cert.InductiveBlocks (CtorFactsAt ctorReadsAt typeReads ctorsReads indexed)
open Ix.Cert.CtxAgree (numNestedOf)
open Ix.Cert.LowerTransfer (eraseMotives)

/-- The block's member reader. -/
abbrev blockReader (cx : Ctx .anon) (owner : Address) (c : Ixon.Constant) (targets : List Ixon.Inductive) :
    MemberReader .anon :=
  MemberReader.mk' cx c id (blockSelf cx owner (targets.map Ixon.MutConst.indc).toArray)

theorem mem_indexed {targets : List Ixon.Inductive} {x : Nat × Ixon.Inductive} (hx : x ∈ indexed targets) :
    ∃ i, ∃ h : i < targets.length, x = (i, targets[i]) := by
  simp only [indexed, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, hi, by simp [hi]⟩

theorem flatMap_congr_mem {α β : Type} {F G : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, F a = G a) → l.flatMap F = l.flatMap G
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr_mem fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- The keys the reader reads the types under. -/
def keyAt (types : Array Ix.InductiveVal) (first : Ix.InductiveVal) (i : Nat) : CName .anon :=
  ((types[i]?).map fun v => srcKey ρ f v.cnst.name).getD (srcKey ρ f first.cnst.name)

/-- The types the reader reads. -/
def typeAt (types : Array Ix.InductiveVal) (i : Nat) : CExpr .anon :=
  ((types[i]?).map fun v => (tgtType ρ f v).1.type).getD (.sort .zero)

/-- The keys the reader reads the constructors under. -/
def ctorKeyAt (ctors : Array (Array Ix.ConstructorVal)) (first : Ix.InductiveVal) (i j : Nat) : CName .anon :=
  (((ctors[i]?).bind (·[j]?)).map fun c => srcKey ρ f c.cnst.name).getD (srcKey ρ f first.cnst.name)

/-- The constructors' types the reader reads. -/
def ctorTypesAt (ctors : Array (Array Ix.ConstructorVal)) (i : Nat) : List (CExpr .anon) :=
  ((ctors[i]?).map fun cs => cs.toList.map fun c => (tgtCtor ρ f c).1.type).getD []

theorem tgtCtor_name (c : Ix.ConstructorVal) : (tgtCtor ρ f c).1.name = srcKey ρ f c.cnst.name := by
  simp only [tgtCtor, srcCtor, quotientHeader_eq]
  rfl

/-- **An inductive block compiled in Lean's order reads as quotient Source's block, renamed**,
recursors' motives aside: the record reads as the lowering of a block equal to quotient
Source's renamed but for its recursors' motives, and equal to it outside a nested block. -/
theorem inductive_reads {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {conv : Ix.LeanIngress.Converted}
    (ran : Ix.LeanIngress.convertInductive types ctors recs = .ok conv) {first : Ix.InductiveVal}
    (hfirst : types[0]? = some first)
    (cx : Ctx .anon) (stA : State .anon) (owner : Address) (c : Ixon.Constant)
    (targets : List Ixon.Inductive) (hne : targets ≠ [])
    (info : c.info = .muts (targets.map Ixon.MutConst.indc).toArray) {shape : BlockShape}
    (hindexed : cx.index.blocks[owner]? = some shape) (order : shape.order = (List.range targets.length).toArray)
    (hsize : targets.length = types.size) (hcsize : ctors.size = types.size)
    (typeFacts : ∀ i (hi : i < types.size) (hi' : i < targets.length) (hc : i < ctors.size),
      TypeFacts ρ f cx owner (blockReader cx owner c targets) i types[i] ctors[i] targets[i])
    (recFacts : List.Forall₂ (RecFacts ρ f cx (List.range first.cnst.levelParams.size) types first
      (numNestedOf (srcBlock types ctors recs first) = 0)) shape.recs.toList recs.toList) :
    ∃ rbR, readRecord cx stA owner c = lowerInductive stA rbR ∧
      eraseMotives rbR = eraseMotives (tgtBlock ρ f types ctors recs first (motiveOf types)) ∧
      (numNestedOf (srcBlock types ctors recs first) ≠ 0 ∨ rbR = tgtBlock ρ f types ctors recs first (motiveOf types)) := by
  obtain ⟨first', hfirst', -, hparams, hchecks⟩ := convertInductive_src ran
  have e : first = first' := Option.some.inj (hfirst.symm.trans hfirst')
  subst e
  have tf : ∀ i (hi : i < targets.length), TypeFacts ρ f cx owner (blockReader cx owner c targets) i
      (types[i]'(hsize ▸ hi)) (ctors[i]'(hcsize ▸ hsize ▸ hi)) targets[i] :=
    fun i hi => typeFacts i (hsize ▸ hi) hi (hcsize ▸ hsize ▸ hi)
  -- each type's constructors
  have cls : ∀ i (hi : i < targets.length),
      CtorFactsAt cx owner (blockReader cx owner c targets) first.numParams (ctorKeyAt ρ f ctors first) i 0
          targets[i].ctors.toList (ctorTypesAt ρ f ctors i) ∧
        ctorReadsAt (ctorKeyAt ρ f ctors first) i 0 targets[i].ctors.toList (ctorTypesAt ρ f ctors i) =
          (ctors[i]'(hcsize ▸ hsize ▸ hi)).toList.map (tgtCtor ρ f) := by
    intro i hi
    have hci : i < ctors.size := hcsize ▸ hsize ▸ hi
    have htypes : ctorTypesAt ρ f ctors i = ctors[i].toList.map fun c => (tgtCtor ρ f c).1.type := by
      simp [ctorTypesAt, hci]
    rw [htypes]
    refine ctorClass_go ρ f cx owner _ first.numParams _ i _ _ 0 (by simpa using (tf i hi).nctors) ?_
    intro k hk hk'
    have hk1 : k < ctors[i].size := by simpa using hk'
    have hk2 : k < targets[i].ctors.size := by simpa using hk
    refine ⟨?_, ?_, ?_⟩
    · simpa using (tf i hi).ctors k hk1 hk2
    · simp [ctorKeyAt, hci, hk1]
    · refine hchecks _ (List.mem_flatMap.mpr ⟨ctors[i], Array.getElem_mem_toList hci, ?_⟩)
      simp
  -- the reader's facts
  have facts : ∀ x ∈ indexed targets,
      cx.memberKey (.member owner x.1) = .ok (keyAt ρ f types first x.1) ∧
      (blockReader cx owner c targets).read x.2.typ = .ok (typeAt ρ f types x.1) ∧
      x.2.isUnsafe = false ∧ x.2.params.toNat = first.numParams ∧
      CtorFactsAt cx owner (blockReader cx owner c targets) first.numParams (ctorKeyAt ρ f ctors first) x.1 0
        x.2.ctors.toList (ctorTypesAt ρ f ctors x.1) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_indexed hx
    have hti : i < types.size := hsize ▸ hi
    refine ⟨?_, ?_, (tf i hi).safe, ?_, (cls i hi).1⟩
    · simp only [keyAt, Array.getElem?_eq_getElem hti, Option.map_some, Option.getD_some]
      exact (tf i hi).key
    · simp only [typeAt, Array.getElem?_eq_getElem hti, Option.map_some, Option.getD_some]
      exact type_read ρ f (tf i hi).nodup (tf i hi).type
    · rw [(tf i hi).params]
      exact hparams _ (Array.getElem_mem_toList hti)
  have hfam := Ix.Cert.InductiveBlocks.readRecord_family cx stA owner c targets hne info hindexed order
    first.numParams (keyAt ρ f types first) (typeAt ρ f types) (ctorKeyAt ρ f ctors first) (ctorTypesAt ρ f ctors)
    facts
  -- the block's level parameters
  have hlps : (targets.head hne).lvls.toNat = first.cnst.levelParams.size := by
    have h0 : 0 < targets.length := List.length_pos_iff.mpr hne
    have hf0 : types[0]'(hsize ▸ h0) = first := by
      have := hfirst
      rw [Array.getElem?_eq_getElem (hsize ▸ h0)] at this
      exact Option.some.inj this
    rw [List.head_eq_getElem, (tf 0 h0).lvls, hf0]
  -- the recursors
  obtain ⟨reads, hR, herase, hnest⟩ := recs_facts ρ f recFacts
  have hrecs : readRecursors cx (List.range (targets.head hne).lvls.toNat) shape.recs = .ok reads.toArray := by
    unfold readRecursors
    rw [← Array.forIn_toList, hlps, Ix.Cert.RecursorReads.readRecursors_ok cx _ shape.recs.toList reads #[] hR]
    simp
  -- the block's items
  have htypes : typeReads (keyAt ρ f types first) (typeAt ρ f types) (indexed targets) =
      types.toList.map (tgtType ρ f) := by
    apply List.ext_getElem
    · simp [typeReads, indexed, hsize]
    · intro i h₁ h₂
      have hi : i < targets.length := by simpa [typeReads, indexed] using h₁
      have hti : i < types.size := hsize ▸ hi
      simp only [typeReads, indexed, List.getElem_map, List.getElem_range, Array.getElem_toList,
        getElem!_pos targets i hi]
      simp only [keyAt, typeAt, Array.getElem?_eq_getElem hti, Option.map_some, Option.getD_some]
      exact type_item ρ f (tf i hi)
  have hn : ctors.toList.length = targets.length := by simp [hcsize, hsize]
  have hctors : ctorsReads (ctorKeyAt ρ f ctors first) (ctorTypesAt ρ f ctors) (indexed targets) =
      (ctors.toList.flatMap (·.toList)).map (tgtCtor ρ f) := by
    rw [List.map_flatMap, flatMap_range, hn]
    simp only [ctorsReads, indexed, List.flatMap_map]
    refine flatMap_congr_mem fun i hi => ?_
    have hi' : i < targets.length := List.mem_range.mp hi
    rw [getElem!_pos targets i hi', (cls i hi').2]
    have hci : i < ctors.size := hcsize ▸ hsize ▸ hi'
    simp [Array.getElem?_eq_getElem hci]
  have hnames : ((indexed targets).map fun x =>
        (ctorReadsAt (ctorKeyAt ρ f ctors first) x.1 0 x.2.ctors.toList (ctorTypesAt ρ f ctors x.1)).map
          (·.1.name)) =
      ctors.toList.map fun cs => cs.toList.map fun c => srcKey ρ f c.cnst.name := by
    apply List.ext_getElem
    · simp [indexed, hn]
    · intro i h₁ h₂
      have hi : i < targets.length := by simpa [indexed] using h₁
      simp only [indexed, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply,
        getElem!_pos targets i hi, (cls i hi).2, Array.getElem_toList]
      refine List.map_congr_left fun c _ => ?_
      exact tgtCtor_name ρ f c
  have hread : readRecord cx stA owner c = lowerInductive stA ⟨first.numParams,
      (types.toList.map (tgtType ρ f)).toArray, ((ctors.toList.flatMap (·.toList)).map (tgtCtor ρ f)).toArray,
      (ctors.toList.map fun cs => cs.toList.map fun c => srcKey ρ f c.cnst.name).toArray, reads.toArray⟩ := by
    rw [hfam, hrecs, ← htypes, ← hctors, ← hnames]
    rfl
  refine ⟨_, hread, ?_, ?_⟩
  · simp only [eraseMotives, tgtBlock, List.map_toArray, BlockRead.mk.injEq, true_and]
    exact congrArg List.toArray herase
  · by_cases hnz : numNestedOf (srcBlock types ctors recs first) = 0
    · right
      rw [hnest hnz]
      rfl
    · exact .inl hnz

theorem numNested_tgt (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal))
    (recs : Array Ix.RecursorVal) (first : Ix.InductiveVal) (motives : Ix.RecursorVal → Option Nat) :
    numNestedOf (tgtBlock ρ f types ctors recs first motives) = numNestedOf (srcBlock types ctors recs first) := by
  simp only [numNestedOf, tgtBlock, srcBlock, List.getElem?_toArray, List.getElem?_map, List.size_toArray,
    List.length_map]
  cases recs.toList[0]? <;> rfl

/-! ## The units' readings -/

/-- **A compiled inductive block's record reads as quotient Source's unit renamed**, from every
state related to the unit's (the `reads` of `StreamUnits.Units.record`), given the reader's
facts of its types, constructors and recursors at the closure's context
(`TypeFacts`, `RecFacts`), quotient Source's lowering of the group, a good quotient block,
and good types and blocks in Source's state. -/
theorem inductive_unit_reads {P : KeyScope .source} (hP : P.Pre) (hf : InjOn f P)
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {conv : Ix.LeanIngress.Converted}
    (ran : Ix.LeanIngress.convertInductive types ctors recs = .ok conv) {first : Ix.InductiveVal}
    (hfirst : types[0]? = some first)
    (cx : Ctx .anon) (owner : Address) (c : Ixon.Constant)
    (targets : List Ixon.Inductive) (hne : targets ≠ [])
    (info : c.info = .muts (targets.map Ixon.MutConst.indc).toArray) {shape : BlockShape}
    (hindexed : cx.index.blocks[owner]? = some shape) (order : shape.order = (List.range targets.length).toArray)
    (hsize : targets.length = types.size) (hcsize : ctors.size = types.size)
    (typeFacts : ∀ i (hi : i < types.size) (hi' : i < targets.length) (hc : i < ctors.size),
      TypeFacts ρ f cx owner (blockReader cx owner c targets) i types[i] ctors[i] targets[i])
    (recFacts : List.Forall₂ (RecFacts ρ f cx (List.range first.cnst.levelParams.size) types first
      (numNestedOf (srcBlock types ctors recs first) = 0)) shape.recs.toList recs.toList)
    (good : ∀ rb, conv.quotient ρ = .inductive rb → rb.Good P)
    {stS : State .source}
    (typesGood : ∀ k : Key .source, k.Good P → ∀ p, stS.constTypes[k]? = some p → p.2.Good P)
    (blocksGood : ∀ k : Key .source, k.Good P → ∀ b, stS.indBlocks[k]? = some b → b.Good P)
    {rS : Read .source} (lowered : Ix.LeanIngress.lower stS (conv.quotient ρ) = .ok rS) :
    ∀ stA : State .anon, StreamRename.StateRen f P stS stA →
      ∃ rA, readRecord cx stA owner c = .ok rA ∧ StreamUnits.ReadRen f rS rA := by
  intro stA hst
  obtain ⟨first', hfirst', hconv, -, -⟩ := convertInductive_src ran
  have e : first = first' := Option.some.inj (hfirst.symm.trans hfirst')
  subst e
  have hq : conv.quotient ρ = .inductive (Ix.LeanIngress.BlockRead.canon
      (Ix.LeanIngress.BlockRead.substKeys ρ (srcBlock types ctors recs first))) := by
    rw [hconv]
    rfl
  have lowS : lowerInductive stS (Ix.LeanIngress.BlockRead.canon
      (Ix.LeanIngress.BlockRead.substKeys ρ (srcBlock types ctors recs first))) = .ok rS := by
    rw [hq] at lowered
    exact lowered
  obtain ⟨rbR, hread, herase, hor⟩ := inductive_reads ρ f ran hfirst cx stA owner c targets hne info hindexed
    order hsize hcsize typeFacts recFacts
  have hQ := quotient_src ρ f types ctors recs first
  have agree : CtxAgree.StateAgree f P stS stA :=
    ⟨hst.types, typesGood, fun k hk => by simp only [Std.HashMap.getD_eq_getD_getElem?, hst.heights k hk],
     hst.blocks, blocksGood⟩
  have hnest : numNestedOf (Ix.LeanIngress.BlockRead.canon
      (Ix.LeanIngress.BlockRead.substKeys ρ (srcBlock types ctors recs first))) =
        numNestedOf (srcBlock types ctors recs first) := by
    rw [← CtxAgree.numNestedOf_mapKeys (f := f), hQ, numNested_tgt]
  obtain ⟨rA, hA, ren⟩ := LowerTransfer.lowerInductive_transfer_motives hP hf agree (good _ hq) lowS
    (rb' := rbR) (by rw [hQ]; exact herase) (by rw [hnest, hQ]; exact hor)
  exact ⟨rA, hread.trans hA, ren⟩

/--
info: 'Ix.Cert.InductiveUnits.inductive_unit_reads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inductive_unit_reads

end Ix.Cert.InductiveUnits
