import Ix.Cert.Statement
import Ix.CompileCert.Loop

/-! # Each record's lowering (S1's units, reader side; (R1))

The S1 union is stated over units: one record's lowering, the modeller's
generated records then the record's own declaration, or a definition block's
declarations. IxC's decided units check closes each run of generated records
with an ungenerated declaration whose bases cover the run's
(`IxC/Kernel/Units.lean`). What the reader adds, per record:

* `stream_lowerings`: the stream `readRecords` decodes is its records'
  lowerings (`Read.decls`) concatenated, one per record, in order;
* `lowerDefinition_names`, `readDefinition_key`: a definition member's
  declaration declares exactly the member's key.

The inductive block's lowering (its `indDecl` declares the block's types',
constructors' and indexed recursors' keys), the per-record theorem and (R2)
(distinct records have disjoint member keys) follow. -/

namespace Ix.Cert.ReaderUnits

open Ix.Kernel (ConstRef Mode)
open Ix.Kernel.Reader

variable {md : Mode}

/-- A key the reader gives a member of the record at `owner`: of one of its
block's members or constructors, or of a recursor its block's shape indexes. -/
def MemberKeyOf (cx : Ctx md) (owner : Address) (k : CName md) : Prop :=
  ∃ ref : ConstRef Address,
    (ref.block = owner ∨ ∃ shape, cx.index.blocks[owner]? = some shape ∧ ref ∈ shape.recs) ∧
      cx.memberKey ref = .ok k

/-! ## The stream -/

/-- **The decoded stream is the records' lowerings, concatenated**: one
lowering per record, each what `readRecord` returned for it. -/
theorem stream_lowerings {cx : Ctx md} {st st' : State md} {records : List (Address × Ixon.Constant)}
    {out : Array (CDecl md)} (h : StreamRead cx st records st' out) :
    ∃ rs : List (Read md),
      List.Forall₂ (fun (x : Address × Ixon.Constant) r => ∃ st₀, readRecord cx st₀ x.1 x.2 = .ok r) records rs ∧
        out.toList = (rs.map fun r => r.decls.toList).flatten := by
  induction h with
  | nil => exact ⟨[], .nil, rfl⟩
  | @cons st _ a c r rest out read _ ih =>
    obtain ⟨rs, holds, flat⟩ := ih
    exact ⟨r :: rs, .cons ⟨st, read⟩ holds, by simp [flat]⟩

/-- `stream_lowerings` for an accepted `readRecords`. -/
theorem readRecords_lowerings {cx : Ctx md} {st st' : State md} {records : Array (Address × Ixon.Constant)}
    {out : Array (CDecl md)} (h : readRecords cx st records = .ok (st', out)) :
    ∃ rs : List (Read md),
      List.Forall₂ (fun (x : Address × Ixon.Constant) r => ∃ st₀, readRecord cx st₀ x.1 x.2 = .ok r)
        records.toList rs ∧
        out.toList = (rs.map fun r => r.decls.toList).flatten :=
  stream_lowerings (readRecords_spec h)

/-! ## Definition members -/

/-- **A lowered definition declares its header's name**, whatever its kind. -/
theorem lowerDefinition_names {hint : Option Ix.Kernel.ReducibilityHint} {st : State md}
    {heights : CName md → Nat} {cv : CVal md} {value : CExpr md} {kind : Ix.DefKind}
    {safety : Ix.DefinitionSafety} {decl : CDecl md} {rw : Bool}
    (h : lowerDefinition hint st heights cv value kind safety = .ok (decl, rw)) :
    decl.names = [cv.name] := by
  unfold lowerDefinition at h
  dsimp only at h
  split at h
  · simp [declined, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · cases kind <;> simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h <;> rfl

/-- **A definition member's declaration declares exactly the member's key.** -/
theorem readDefinition_key {cx : Ctx md} {st : State md} {heights : CName md → Nat}
    {ref : ConstRef Address} {lps : List Ix.Kernel.LevelParam} {mr : MemberReader md} {d : Ixon.Definition}
    {decl : CDecl md} {rw : Bool} (h : readDefinition cx st heights ref lps mr d = .ok (decl, rw)) :
    ∃ k, cx.memberKey ref = .ok k ∧ decl.names = [k] := by
  unfold readDefinition at h
  cases hk : cx.memberKey ref with
  | error e => simp [hk, bind, Except.bind] at h
  | ok k =>
    simp only [hk, bind, Except.bind] at h
    cases ht : mr.read d.typ with
    | error e => simp [ht] at h
    | ok t =>
      simp only [ht] at h
      cases hv : mr.read d.value with
      | error e => simp [hv] at h
      | ok v =>
        simp only [hv] at h
        exact ⟨k, rfl, lowerDefinition_names h⟩


/-! ## The inductive block's lowering -/

/-- An accepted branch of an `if` in `ReadM` is an accepted branch. -/
theorem ite_ok {α : Type} {c : Prop} [Decidable c] {x y : ReadM α} {r : α}
    (h : (if c then x else y) = .ok r) : x = .ok r ∨ y = .ok r := by
  by_cases hc : c
  · exact .inl (by simpa [hc] using h)
  · exact .inr (by simpa [hc] using h)

/-- **A lowered inductive block ends in its own declaration**: the modeller's
records (as many as `generated` says), then the block's `indDecl`, which
declares the block's types', constructors' and recursors' names, in that
order. -/
theorem lowerInductive_decls {st : State md} {rb : BlockRead md} {r : Read md}
    (h : lowerInductive st rb = .ok r) :
    ∃ gens d, r.decls.toList = gens ++ [d] ∧ r.generated = gens.length ∧
      d.names = rb.types.toList.map (·.1.name) ++ rb.ctors.toList.map (·.1.name) ++
        rb.recs.toList.map (·.1.name) := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  have names : ∀ (block : List (Ix.Kernel.ConstantInfo md)),
      block = types.toList.map (fun x => Ix.Kernel.ConstantInfo.indInfo x.1 {}) ++
        ctors.toList.map (fun x => Ix.Kernel.ConstantInfo.ctorInfo x.1 x.2.1 x.2.2) ++
        recs.toList.map (fun x => Ix.Kernel.ConstantInfo.recInfo x.1
          (x.2.1.params + x.2.1.motives + x.2.1.minors + x.2.1.indices)
          (x.2.1.params + x.2.1.motives + x.2.1.minors) x.2.2) →
      (Ix.Kernel.Declaration.indDecl block nPd).names =
        types.toList.map (·.1.name) ++ ctors.toList.map (·.1.name) ++ recs.toList.map (·.1.name) := by
    intro block hb
    subst hb
    simp only [Ix.Kernel.Declaration.names, List.map_append, List.map_map]
    rfl
  unfold lowerInductive at h
  simp only [ite_not, bne_iff_ne, ne_eq] at h
  split at h
  all_goals
    rcases ite_ok h with h | h
    all_goals first
      | (obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h)
      | skip
    all_goals
      rcases ite_ok h with h | h
      · split at h
        · simp [declined, throw, throwThe, MonadExceptOf.throw] at h
        · rename_i gen _
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨gen, _, by simp, rfl, names _ rfl⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨[], _, rfl, rfl, names _ rfl⟩

end Ix.Cert.ReaderUnits
