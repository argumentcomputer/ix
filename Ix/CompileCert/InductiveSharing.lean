import Ix.CompileCert.InductiveEmission

/-! Canonical sharing and its actual root write-back preserve inductive and
constructor headers and anonymous type readings. No source metadata enters
the result relation. -/

namespace Ix.CompileCert.InductiveSharing

open Ix Ix.CompileM
open Kernel.Reader

def constructors (source : Ixon.Inductive) (types : List Ixon.Expr) : Array Ixon.Constructor :=
  (source.ctors.toList.zip types).toArray.map fun (ctor, type) => { ctor with typ := type }

def rewrite (source : Ixon.Inductive) (type : Ixon.Expr) (types : List Ixon.Expr) : Ixon.Inductive :=
  { source with typ := type, ctors := constructors source types }

theorem roots (source : Ixon.Inductive) :
    constantInfoRootExprs (.muts #[.indc source]) =
      (source.typ :: source.ctors.toList.map (·.typ)).toArray := by
  simp [constantInfoRootExprs, mutConstRootExprs]

theorem writeback (source : Ixon.Inductive) (roots : Array Ixon.Expr) (info : Ixon.ConstantInfo)
    (size : roots.size = source.ctors.size + 1)
    (ran : withRootExprs (.muts #[.indc source]) roots = .ok info) :
    ∃ type types, roots = (type :: types).toArray ∧ types.length = source.ctors.size ∧
      info = .muts #[.indc (rewrite source type types)] := by
  rcases roots with ⟨values⟩
  cases values with
  | nil => simp at size
  | cons type types =>
    have count : types.length = source.ctors.size := by simpa using size
    have actual : withRootExprs (.muts #[.indc source]) (type :: types).toArray =
        .ok (.muts #[.indc (rewrite source type types)]) := by
      simp only [withRootExprs, Sharing.Exact.withRoots]
      rw [ite_eq_right (by simp [Sharing.Exact.constantInfoRoots, Sharing.Exact.mutConstRoots, count])]
      rw [← Array.forIn_toList]
      simp [List.forIn_cons, List.forIn_nil, Sharing.Exact.withMutConstRoots,
        Sharing.Exact.takeRoot, ← count, Sharing.Verify.takeRoots_self,
        bind, Except.bind, pure, Except.pure, rewrite, constructors, Except.mapError]
    rw [actual] at ran
    exact ⟨type, types, rfl, count, (Except.ok.inj ran).symm⟩

structure ConstructorReading (before after : MemberReader) (source target : Ixon.Constructor) : Prop where
  safety : target.isUnsafe = source.isUnsafe
  levels : target.lvls = source.lvls
  index : target.cidx = source.cidx
  params : target.params = source.params
  fields : target.fields = source.fields
  type : after.read target.typ = before.read source.typ

structure Reading (before after : MemberReader) (source target : Ixon.Inductive) : Prop where
  safety : target.isUnsafe = source.isUnsafe
  levels : target.lvls = source.lvls
  params : target.params = source.params
  indices : target.indices = source.indices
  type : after.read target.typ = before.read source.typ
  constructors : List.Forall₂ (ConstructorReading before after) source.ctors.toList target.ctors.toList

theorem constructors_read (before after : MemberReader) (source : List Ixon.Constructor)
    (types : List Ixon.Expr) (count : types.length = source.length)
    (readings : types.map after.read = source.map (fun ctor => before.read ctor.typ)) :
    List.Forall₂ (ConstructorReading before after) source
      ((source.zip types).map fun (ctor, type) => { ctor with typ := type }) := by
  induction source generalizing types with
  | nil =>
    have empty : types = [] := by simpa using count
    subst types
    exact .nil
  | cons ctor rest ih =>
    cases types with
    | nil => simp at count
    | cons type types =>
      have counts : types.length = rest.length := by simpa using count
      have reads := List.cons.inj readings
      exact .cons ⟨rfl, rfl, rfl, rfl, rfl, reads.1⟩ (ih types counts reads.2)

theorem build_read (context : Ctx) (params : Nat → Kernel.Name) (self : Nat → Option Kernel.Name)
    (limits : Sharing.Exact.Limits) (source : Ixon.Inductive)
    (refs : Array Address) (univs : Array Ixon.Univ) (output : Ixon.Constant)
    (ran : buildConstantWithSharing limits (.muts #[.indc source]) refs univs = .ok output) :
    ∃ target, output.info = .muts #[.indc target] ∧
      Reading (MemberReader.mk' context { info := .muts #[.indc source], sharing := #[], refs, univs } params self)
        (MemberReader.mk' context output params self) source target := by
  obtain ⟨shared, info, sharedRun, size, written, shape⟩ := Sharing.Verify.buildConstantWithSharing_eq_ok ran
  rw [roots] at sharedRun size
  obtain ⟨type, types, rootsEq, count, header⟩ := writeback source shared.result.roots info
    (by simpa using size) written
  subst info
  subst output
  have meaning := Sharing.Verify.CanonicalMeaning.canonicalSharingTiered_meaning .tagN limits
    (constantInfoRootExprs (.muts #[.indc source])) shared (by rw [roots]; exact sharedRun)
  rw [roots] at meaning
  rw [rootsEq] at meaning
  have readings := SharingRead.meaning_read_before context
    { info := .muts #[.indc source], sharing := #[], refs, univs }
    { info := .muts #[.indc (rewrite source type types)], sharing := shared.result.sharing, refs, univs }
    params self rfl rfl rfl (source.typ :: source.ctors.toList.map (·.typ)).toArray
    (type :: types).toArray meaning
  have lists := congrArg Array.toList readings
  simp only [Array.toList_map, List.map_cons, List.map_map] at lists
  have split := List.cons.inj lists
  refine ⟨rewrite source type types, rfl, rfl, rfl, rfl, rfl, split.1, ?_⟩
  change List.Forall₂ _ source.ctors.toList
    ((source.ctors.toList.zip types).toArray.map fun (ctor, type) => { ctor with typ := type }).toList
  simp only [Array.toList_map]
  exact constructors_read _ _ source.ctors.toList types (by simpa using count) split.2

theorem constructor_related (before after : MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name)
    (source : ConstructorVal) (payload target : Ixon.Constructor)
    (reading : ConstructorReading before after payload target)
    (related : ConstructorEmission.Related before names sourceParams params source payload) :
    ConstructorEmission.Related after names sourceParams params source target := by
  obtain ⟨safety, levels, index, parameters, fields, type, meaning, read⟩ := related
  exact ⟨reading.safety.trans safety, (congrArg UInt64.toNat reading.levels).trans levels,
    (congrArg UInt64.toNat reading.index).trans index,
    (congrArg UInt64.toNat reading.params).trans parameters,
    (congrArg UInt64.toNat reading.fields).trans fields, type, meaning, reading.type.trans read⟩

theorem constructors_related (before after : MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name)
    (sources : List ConstructorVal) (payloads targets : List Ixon.Constructor)
    (readings : List.Forall₂ (ConstructorReading before after) payloads targets)
    (related : List.Forall₂ (ConstructorEmission.Related before names sourceParams params) sources payloads) :
    List.Forall₂ (ConstructorEmission.Related after names sourceParams params) sources targets := by
  induction related generalizing targets with
  | nil => cases readings; exact .nil
  | cons head rest ih =>
    cases readings with
    | cons read reads => exact .cons (constructor_related before after names sourceParams params _ _ _ read head) (ih _ reads)

theorem related (before after : MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name)
    (source : Ind) (payload target : Ixon.Inductive)
    (reading : Reading before after payload target)
    (related : InductiveEmission.Related before names sourceParams params source payload) :
    InductiveEmission.Related after names sourceParams params source target := by
  obtain ⟨safety, levels, parameters, indices, ⟨type, meaning, read⟩, ctors⟩ := related
  exact ⟨reading.safety.trans safety, (congrArg UInt64.toNat reading.levels).trans levels,
    (congrArg UInt64.toNat reading.params).trans parameters,
    (congrArg UInt64.toNat reading.indices).trans indices, ⟨type, meaning, reading.type.trans read⟩,
    constructors_related before after names sourceParams params source.ctors.toList
      payload.ctors.toList target.ctors.toList reading.constructors ctors⟩

theorem unshared_reading (context : Ctx) (base : Ixon.Constant) (params : Nat → Kernel.Name)
    (self : Nat → Option Kernel.Name) (state : BlockState) (ordinary : state.p3MetaMode = false)
    (payload : Ixon.Inductive) :
    Reading (ExpressionRead.blockReader context base params self state)
      (MemberReader.mk' (SharingRead.blobContext context state)
        { info := .muts #[.indc payload], sharing := #[], refs := state.refs, univs := state.univs } params self)
      payload payload := by
  refine ⟨rfl, rfl, rfl, rfl,
    SharingRead.unshared_read context base params self state ordinary _ _, ?_⟩
  suffices ∀ ctors : List Ixon.Constructor, List.Forall₂ _ ctors ctors from this payload.ctors.toList
  intro ctors
  induction ctors with
  | nil => exact .nil
  | cons ctor rest ih =>
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl,
      SharingRead.unshared_read context base params self state ordinary _ _⟩ ih

/-- The source-related payload supplied by the real compiler survives the
real sharing builder. Primary tables and local literal blobs are the ones
accumulated by payload compilation. -/
theorem build_payload (context : Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (state : BlockState) (ordinary : state.p3MetaMode = false)
    (source : Ind) (payload : Ixon.Inductive)
    (meaning : InductiveEmission.Related
      (ExpressionRead.blockReader context base (paramOf params) self state) names sourceParams params source payload)
    (limits : Sharing.Exact.Limits) (output : Ixon.Constant)
    (ran : buildConstantWithSharing limits (.muts #[.indc payload]) state.refs state.univs = .ok output) :
    ∃ target, output.info = .muts #[.indc target] ∧
      InductiveEmission.Related
        (MemberReader.mk' (SharingRead.blobContext context state) output (paramOf params) self)
        names sourceParams params source target := by
  obtain ⟨target, info, reading⟩ := build_read (SharingRead.blobContext context state)
    (paramOf params) self limits payload state.refs state.univs output ran
  exact ⟨target, info, related _ _ names sourceParams params source payload target reading
    (related _ _ names sourceParams params source payload payload
      (unshared_reading context base (paramOf params) self state ordinary payload) meaning)⟩

end Ix.CompileCert.InductiveSharing
