import Ix.CompileCert.RecursorEmission

/-! Source-related recursor payloads survive actual canonical sharing and
ordered type/rule write-back. The reader's family/constructor pairing is a
separate source-family obligation. -/

namespace Ix.CompileCert.RecursorSharing

open Ix Ix.CompileM
open Kernel.Reader

def rewrite (source : Ixon.Recursor) (type : Ixon.Expr) (rhss : List Ixon.Expr) : Ixon.Recursor :=
  { source with
    typ := type
    rules := (source.rules.toList.zip rhss).toArray.map fun (rule, rhs) => { rule with rhs } }

theorem roots (source : Ixon.Recursor) :
    constantInfoRootExprs (.recr source) = (source.typ :: source.rules.toList.map (·.rhs)).toArray := rfl

theorem writeback (source : Ixon.Recursor) (roots : Array Ixon.Expr) (info : Ixon.ConstantInfo)
    (size : roots.size = source.rules.size + 1)
    (ran : withRootExprs (.recr source) roots = .ok info) :
    ∃ type rhss, roots = (type :: rhss).toArray ∧ rhss.length = source.rules.size ∧
      info = .recr (rewrite source type rhss) := by
  rcases roots with ⟨values⟩
  cases values with
  | nil => simp at size
  | cons type rhss =>
    have count : rhss.length = source.rules.size := by simpa using size
    have actual : withRootExprs (.recr source) (type :: rhss).toArray =
        .ok (.recr (rewrite source type rhss)) := by
      simp only [withRootExprs, Sharing.Exact.withRoots]
      rw [ite_eq_right (by simp [Sharing.Exact.constantInfoRoots, Sharing.Exact.mutConstRoots, count])]
      simp [Sharing.Exact.withMutConstRoots, Sharing.Exact.takeRoot, ← count,
        Sharing.Verify.takeRoots_self, bind, Except.bind, pure, Except.pure, rewrite, Except.mapError]
    rw [actual] at ran
    exact ⟨type, rhss, rfl, count, (Except.ok.inj ran).symm⟩

structure RuleReading (before after : MemberReader) (source target : Ixon.RecursorRule) : Prop where
  fields : target.fields = source.fields
  rhs : after.read target.rhs = before.read source.rhs

structure Reading (before after : MemberReader) (source target : Ixon.Recursor) : Prop where
  k : target.k = source.k
  safety : target.isUnsafe = source.isUnsafe
  levels : target.lvls = source.lvls
  params : target.params = source.params
  indices : target.indices = source.indices
  motives : target.motives = source.motives
  minors : target.minors = source.minors
  type : after.read target.typ = before.read source.typ
  rules : List.Forall₂ (RuleReading before after) source.rules.toList target.rules.toList

theorem rules_read (before after : MemberReader) (source : List Ixon.RecursorRule)
    (rhss : List Ixon.Expr) (count : rhss.length = source.length)
    (readings : rhss.map after.read = source.map (fun rule => before.read rule.rhs)) :
    List.Forall₂ (RuleReading before after) source
      ((source.zip rhss).map fun (rule, rhs) => { rule with rhs }) := by
  induction source generalizing rhss with
  | nil =>
    have empty : rhss = [] := by simpa using count
    subst rhss
    exact .nil
  | cons rule rest ih =>
    cases rhss with
    | nil => simp at count
    | cons rhs rhss =>
      have counts : rhss.length = rest.length := by simpa using count
      have reads := List.cons.inj readings
      exact .cons ⟨rfl, reads.1⟩ (ih rhss counts reads.2)

theorem build_read (context : Ctx) (params : Nat → Kernel.Name) (self : Nat → Option Kernel.Name)
    (limits : Sharing.Exact.Limits) (source : Ixon.Recursor)
    (refs : Array Address) (univs : Array Ixon.Univ) (output : Ixon.Constant)
    (ran : buildConstantWithSharing limits (.recr source) refs univs = .ok output) :
    ∃ target, output.info = .recr target ∧
      Reading (MemberReader.mk' context { info := .recr source, sharing := #[], refs, univs } params self)
        (MemberReader.mk' context output params self) source target := by
  obtain ⟨shared, info, sharedRun, size, written, shape⟩ := Sharing.Verify.buildConstantWithSharing_eq_ok ran
  obtain ⟨type, rhss, rootsEq, count, header⟩ := writeback source shared.result.roots info
    (by simpa [roots] using size) written
  subst info
  subst output
  have meaning := Sharing.Verify.CanonicalMeaning.canonicalSharingTiered_meaning .tagN limits
    (constantInfoRootExprs (.recr source)) shared sharedRun
  rw [roots, rootsEq] at meaning
  have readings := SharingRead.meaning_read_before context
    { info := .recr source, sharing := #[], refs, univs }
    { info := .recr (rewrite source type rhss), sharing := shared.result.sharing, refs, univs }
    params self rfl rfl rfl (source.typ :: source.rules.toList.map (·.rhs)).toArray
    (type :: rhss).toArray meaning
  have lists := congrArg Array.toList readings
  simp only [Array.toList_map, List.map_cons, List.map_map] at lists
  have split := List.cons.inj lists
  refine ⟨rewrite source type rhss, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, split.1, ?_⟩
  change List.Forall₂ _ source.rules.toList
    ((source.rules.toList.zip rhss).toArray.map fun (rule, rhs) => { rule with rhs }).toList
  simp only [Array.toList_map]
  exact rules_read _ _ source.rules.toList rhss (by simpa using count) split.2

theorem rule_related (before after : MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name)
    (source : RecursorRule) (payload target : Ixon.RecursorRule)
    (reading : RuleReading before after payload target)
    (related : RecursorEmission.RuleRelated before names sourceParams params source payload) :
    RecursorEmission.RuleRelated after names sourceParams params source target := by
  obtain ⟨fields, rhs, meaning, read⟩ := related
  exact ⟨(congrArg UInt64.toNat reading.fields).trans fields, rhs, meaning, reading.rhs.trans read⟩

theorem rules_related (before after : MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name)
    (sources : List RecursorRule) (payloads targets : List Ixon.RecursorRule)
    (readings : List.Forall₂ (RuleReading before after) payloads targets)
    (related : List.Forall₂ (RecursorEmission.RuleRelated before names sourceParams params) sources payloads) :
    List.Forall₂ (RecursorEmission.RuleRelated after names sourceParams params) sources targets := by
  induction related generalizing targets with
  | nil => cases readings; exact .nil
  | cons head rest ih =>
    cases readings with
    | cons read reads => exact .cons (rule_related before after names sourceParams params _ _ _ read head) (ih _ reads)

theorem related (before after : MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name)
    (source : RecursorVal) (payload target : Ixon.Recursor)
    (reading : Reading before after payload target)
    (related : RecursorEmission.Related before names sourceParams params source payload) :
    RecursorEmission.Related after names sourceParams params source target := by
  obtain ⟨type, meaning, read⟩ := related.type
  exact ⟨reading.k.trans related.k, reading.safety.trans related.safety,
    (congrArg UInt64.toNat reading.levels).trans related.levels,
    (congrArg UInt64.toNat reading.params).trans related.parameters,
    (congrArg UInt64.toNat reading.indices).trans related.indices,
    (congrArg UInt64.toNat reading.motives).trans related.motives,
    (congrArg UInt64.toNat reading.minors).trans related.minors,
    ⟨type, meaning, reading.type.trans read⟩,
    rules_related before after names sourceParams params source.rules.toList
      payload.rules.toList target.rules.toList reading.rules related.rules⟩

theorem unshared_reading (context : Ctx) (base : Ixon.Constant) (params : Nat → Kernel.Name)
    (self : Nat → Option Kernel.Name) (state : BlockState) (ordinary : state.p3MetaMode = false)
    (payload : Ixon.Recursor) :
    Reading (ExpressionRead.blockReader context base params self state)
      (MemberReader.mk' (SharingRead.blobContext context state)
        { info := .recr payload, sharing := #[], refs := state.refs, univs := state.univs } params self)
      payload payload := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    SharingRead.unshared_read context base params self state ordinary _ _, ?_⟩
  suffices ∀ rules : List Ixon.RecursorRule, List.Forall₂ _ rules rules from this payload.rules.toList
  intro rules
  induction rules with
  | nil => exact .nil
  | cons rule rest ih =>
    exact .cons ⟨rfl, SharingRead.unshared_read context base params self state ordinary _ _⟩ ih

theorem build_payload (context : Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (state : BlockState) (ordinary : state.p3MetaMode = false)
    (source : RecursorVal) (payload : Ixon.Recursor)
    (meaning : RecursorEmission.Related
      (ExpressionRead.blockReader context base (paramOf params) self state) names sourceParams params source payload)
    (limits : Sharing.Exact.Limits) (output : Ixon.Constant)
    (ran : buildConstantWithSharing limits (.recr payload) state.refs state.univs = .ok output) :
    ∃ target, output.info = .recr target ∧
      RecursorEmission.Related
        (MemberReader.mk' (SharingRead.blobContext context state) output (paramOf params) self)
        names sourceParams params source target := by
  obtain ⟨target, info, reading⟩ := build_read (SharingRead.blobContext context state)
    (paramOf params) self limits payload state.refs state.univs output ran
  exact ⟨target, info, related _ _ names sourceParams params source payload target reading
    (related _ _ names sourceParams params source payload payload
      (unshared_reading context base (paramOf params) self state ordinary payload) meaning)⟩

end Ix.CompileCert.RecursorSharing
