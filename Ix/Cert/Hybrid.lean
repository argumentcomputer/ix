import Ix.Cert.Schedule
import Ix.CompileCert.Canon.Ref
import Ix.Cert.Canon
import Ix.Cert.Statement

/-! # The hybrid environment compiles as the materialized one (CQP.4 b)

`Ix.Cert.compile` runs the driver `Ix.CompileM.compileEnvFold` over the
materialized environment (`{ consts := env.consts }`); the IO pipeline
(`Ix.CompileM.compileDecoratedConsts`) runs it over a hybrid one: the code
kinds materialized, theorem and opaque bodies canonicalized again on demand
through `fallback?` (`hybridEnv`). The driver and its validations read the
environment through `Ix.Environment.get?` only, apart from the order of the
inductive groups they check: the fold and the inductive-flag check run over
the lookup view `{ consts := {}, fallback? := some env.get? }`, and the
mixed-safety check reads members through `get?` (the compiler's
restatements, behaviour-identical). So:

* `validateInductiveFlags_eq`, `validateMutualSafety_eq`: the two
  validations agree on environments with the same lookups whose inductive
  groups agree in order (`groupOrder`);
* `groupOrder_eq`: the groups agree in order on environments with the same
  lookups whose stored inductives have the same first members: the
  validations take the first members as a set ordered by
  `Ix.nameCompareExact` (`groupHeads`, `mem_groupHeads`), each with its own
  `all` read through `get?`; `hybrid_heads`: so do the hybrid and the
  materialized environments when the code constants hold exactly the input's
  inductives;
* `compileEnvFold_lookups`: **two such environments compile alike** under
  every schedule (`width`, `dbg`, by `Ix.Cert.Schedule`); the result's `CompileEnv`
  holds the environment it was given (`restore`);
* `hybrid_lookups`: the IO pipeline's hybrid environment has the
  materialized environment's lookups where that environment is the input's
  canonicalization (`Ix.Cert.Canon.constS` under each name) and its
  materialized code constants are the materialized environment's. The
  fallback's half is `Ix.Cert.Canon.canonChunkCorrect` (C1): a constant
  canonicalized on demand is the specification's (`fallback_spec`);
* `pipeline_fold`: **the IO pipeline's fold equals `Ix.Cert.compile`'s**, on
  one condensation, under those premises.

**What stays a premise, and why:** the group order is no longer one (it was
`groupOrder`'s agreement until the validations' order became the first
members' set, 2026-10-19). The IO layer's own steps are tested, not proved:
that its loops build the hybrid environment's pieces as stated (`code`,
`canon`, and `inductives`: the code constants hold exactly the input's
inductives), that its streamed
canonicalization, graph, ground filter and condensation are
`Ix.Cert.groundSplit`'s and `blocksOf`'s (`cert-compile-parity-initstd`), and
that the blocks of one wave are independent (`compile-schedule-identity`'s
reference schedule). -/

namespace Ix.Cert.Hybrid

open Ix.CompileM

/-- The inductive groups the validations check, in their order
(`Ix.CompileM.orderedGroups`). -/
def groupOrder (env : Ix.Environment) : Array (Ix.Name × Array Ix.Name) :=
  orderedGroups env

theorem uniformSafety_eq {e₁ e₂ : Ix.Environment} (lookups : ∀ n, e₁.get? n = e₂.get? n) :
    uniformSafety e₁ = uniformSafety e₂ := by
  have get : Ix.Environment.get? e₁ = Ix.Environment.get? e₂ := funext lookups
  funext members
  unfold uniformSafety
  rw [get]

theorem mixedSafetyMessage_eq {e₁ e₂ : Ix.Environment} (lookups : ∀ n, e₁.get? n = e₂.get? n) :
    mixedSafetyMessage e₁ = mixedSafetyMessage e₂ := by
  have get : Ix.Environment.get? e₁ = Ix.Environment.get? e₂ := funext lookups
  funext members
  unfold mixedSafetyMessage
  rw [get]

/-! ## The validations' group order

`Ix.CompileM.orderedGroups` pairs each first member of an inductive group,
taken from a `Std.TreeSet` under `Ix.nameCompareExact`, with its own `all`
read through `get?` (`groupAll`). The set's order is its comparator's,
whatever the fold, so two environments with the same lookups whose stored
inductives have the same first members order their groups alike
(`groupOrder_eq`). -/

/-- `k` is the first member of an inductive stored in `consts`. -/
def HeadIn (consts : Std.HashMap Ix.Name Ix.ConstantInfo) (k : Ix.Name) : Prop :=
  ∃ p ∈ consts.toList, ∃ v, p.2 = .inductInfo v ∧ v.all[0]? = some k

/-- **The first members are the stored inductives'**, whatever the fold's order. -/
theorem mem_groupHeads (e : Ix.Environment) (k : Ix.Name) :
    k ∈ groupHeads e ↔ HeadIn e.consts k := by
  unfold groupHeads HeadIn
  rw [Std.HashMap.fold_eq_foldl_toList]
  generalize e.consts.toList = l
  rw [show (∃ p ∈ l, ∃ v, p.2 = .inductInfo v ∧ v.all[0]? = some k) ↔
      (k ∈ ({} : Std.TreeSet Ix.Name Ix.nameCompareExact) ∨
        ∃ p ∈ l, ∃ v, p.2 = .inductInfo v ∧ v.all[0]? = some k) by simp]
  generalize ({} : Std.TreeSet Ix.Name Ix.nameCompareExact) = t
  induction l generalizing t with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    obtain ⟨n, ci⟩ := p
    cases ci with
    | inductInfo v =>
      cases hv : v.all[0]? with
      | none => simp [hv]
      | some first =>
        simp only [hv, Std.TreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq, List.mem_cons,
          exists_eq_or_imp, ConstantInfo.inductInfo.injEq, exists_eq_left', Option.some.injEq]
        constructor
        · rintro ((h | h) | h) <;> simp_all
        · rintro (h | h | h) <;> simp_all
    | _ => simp

/-- **The group order is the first members' and the lookups'**: two environments
with the same lookups whose stored inductives have the same first members order
their groups alike. -/
theorem groupOrder_eq {e₁ e₂ : Ix.Environment} (lookups : ∀ n, e₁.get? n = e₂.get? n)
    (heads : ∀ k, HeadIn e₁.consts k ↔ HeadIn e₂.consts k) : groupOrder e₁ = groupOrder e₂ := by
  have get : Ix.Environment.get? e₁ = Ix.Environment.get? e₂ := funext lookups
  have sets : (groupHeads e₁).toArray = (groupHeads e₂).toArray :=
    Std.TreeSet.Equiv.toArray_eq (Std.TreeSet.Equiv.of_forall_mem_iff fun k => by
      rw [mem_groupHeads, mem_groupHeads, heads])
  unfold groupOrder orderedGroups groupAll
  rw [sets, get]

/-- **The mixed-safety validation agrees** on environments with the same
lookups whose inductive groups agree in order: it reads members through
`get?`. -/
theorem validateMutualSafety_eq {e₁ e₂ : Ix.Environment} (lookups : ∀ n, e₁.get? n = e₂.get? n)
    (groups : groupOrder e₁ = groupOrder e₂) (blocks : Ix.CondensedBlocks) :
    validateMutualSafety e₁ blocks = validateMutualSafety e₂ blocks := by
  have get : Ix.Environment.get? e₁ = Ix.Environment.get? e₂ := funext lookups
  unfold groupOrder at groups
  unfold validateMutualSafety
  rw [groups, get, uniformSafety_eq lookups, mixedSafetyMessage_eq lookups]

/-- **The inductive-flag validation agrees** on environments with the same
lookups whose inductive groups agree in order: it checks each group over
the lookup view. -/
theorem validateInductiveFlags_eq {e₁ e₂ : Ix.Environment} (lookups : ∀ n, e₁.get? n = e₂.get? n)
    (groups : groupOrder e₁ = groupOrder e₂) :
    validateInductiveFlags e₁ = validateInductiveFlags e₂ := by
  have get : Ix.Environment.get? e₁ = Ix.Environment.get? e₂ := funext lookups
  unfold groupOrder at groups
  unfold validateInductiveFlags
  rw [groups, get]

/-- The result's `CompileEnv`, given an environment again. -/
def restore (env : Ix.Environment) :
    Ixon.Env × Nat × CompileEnv → Ixon.Env × Nat × CompileEnv :=
  fun (ixe, bytes, cenv) => (ixe, bytes, { cenv with env })

/-- **Hybrid = materialized, generically**: two environments with the same
lookups, whose inductive groups agree in order, compile alike under every
schedule; the result's `CompileEnv` holds the environment it was given. -/
theorem compileEnvFold_lookups {e₁ e₂ : Ix.Environment} (lookups : ∀ n, e₁.get? n = e₂.get? n)
    (groups : groupOrder e₁ = groupOrder e₂)
    (blocks : Ix.CondensedBlocks) (dbg dbg' : Bool) (sharingLimits : Ix.Sharing.Exact.Limits)
    (width width' : Nat) :
    compileEnvFold e₁ blocks dbg sharingLimits width =
      restore e₁ <$> compileEnvFold e₂ blocks dbg' sharingLimits width' := by
  have get : Ix.Environment.get? e₁ = Ix.Environment.get? e₂ := funext lookups
  rw [Schedule.compileEnvFold_eq_seq, Schedule.compileEnvFold_eq_seq]
  unfold Schedule.compileEnvFoldSeq
  rw [validateInductiveFlags_eq lookups groups, validateMutualSafety_eq lookups groups, get]
  generalize missingBlockRefs? blocks = missing
  generalize validateInductiveFlags e₂ = flags
  generalize validateMutualSafety e₂ blocks = safety
  cases missing <;> cases flags <;> cases safety <;> try rfl
  all_goals
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    generalize Schedule.foldWavesSeq _ _ _ _ = r
    cases r
    · rfl
    · simp only
      generalize finalizeEnv _ = result
      cases result <;> rfl

/-! ## The IO pipeline's environment -/

/-- The IO pipeline's hybrid environment, as `compileDecoratedConsts` builds
it from its pieces: the materialized code constants, and every input
constant canonicalized again on demand. -/
def hybridEnv (codeConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
    (leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo)) : Ix.Environment :=
  { consts := codeConsts,
    fallback? := some fun n => (leanByIx.get? n).bind fun (ln, lci) =>
      ((Ix.CanonM.canonChunk #[(ln, lci)])[0]?).map (·.2) }

/-- **The fallback computes the specification** (C1): a constant
canonicalized on demand is `constS` of its Lean constant. -/
theorem fallback_spec (leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo)) (n : Ix.Name) :
    ((leanByIx.get? n).bind fun (ln, lci) => ((Ix.CanonM.canonChunk #[(ln, lci)])[0]?).map (·.2)) =
      (leanByIx.get? n).map fun p => Ix.Cert.Canon.constS p.2 := by
  cases leanByIx.get? n with
  | none => rfl
  | some p =>
    rcases p with ⟨ln, lci⟩
    have chunk := Ix.Cert.Canon.canonChunkCorrect #[(ln, lci)]
    simp [chunk]

/-- **The hybrid environment has the materialized one's lookups**, where the
materialized environment is the input's canonicalization (`canon`) and each
materialized code constant is the materialized environment's (`code`). -/
theorem hybrid_lookups (full : Ix.Environment) (codeConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
    (leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo))
    (canon : ∀ n, full.get? n = (leanByIx.get? n).map fun p => Ix.Cert.Canon.constS p.2)
    (code : ∀ n ci, codeConsts.get? n = some ci → full.get? n = some ci) :
    ∀ n, (hybridEnv codeConsts leanByIx).get? n = full.get? n := by
  intro n
  unfold hybridEnv Ix.Environment.get?
  cases materialized : codeConsts.get? n with
  | some ci => exact (code n ci materialized).symm
  | none =>
    simp only
    rw [fallback_spec, ← canon]
    rfl

/-- The hybrid environment's stored inductives, those of the materialized one,
have its first members. -/
theorem hybrid_heads {full : Ix.Environment} {codeConsts : Std.HashMap Ix.Name Ix.ConstantInfo}
    {leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo)}
    (inductives : ∀ n v, (n, Ix.ConstantInfo.inductInfo v) ∈ codeConsts.toList ↔
      (n, Ix.ConstantInfo.inductInfo v) ∈ full.consts.toList) (k : Ix.Name) :
    HeadIn (hybridEnv codeConsts leanByIx).consts k ↔ HeadIn full.consts k := by
  show HeadIn codeConsts k ↔ HeadIn full.consts k
  constructor
  · rintro ⟨⟨n, ci⟩, hm, v, rfl, hv⟩
    exact ⟨(n, .inductInfo v), (inductives n v).1 hm, v, rfl, hv⟩
  · rintro ⟨⟨n, ci⟩, hm, v, rfl, hv⟩
    exact ⟨(n, .inductInfo v), (inductives n v).2 hm, v, rfl, hv⟩

/-- **The IO pipeline's fold equals `Ix.Cert.compile`'s** (CQP.4 b): over
one condensation, the fold over the IO pipeline's hybrid environment, with
its `--workers` width and its options' trace, is the fold `Ix.Cert.compile`
runs over the materialized environment, its result's `CompileEnv` holding the
hybrid environment. Premises (the IO layer's loops, tested): the materialized
environment is the input's canonicalization, the materialized code constants
are its own, and they hold exactly its inductives (`inductives`). -/
theorem pipeline_fold (full : Ix.Environment) (codeConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
    (leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo))
    (canon : ∀ n, full.get? n = (leanByIx.get? n).map fun p => Ix.Cert.Canon.constS p.2)
    (code : ∀ n ci, codeConsts.get? n = some ci → full.get? n = some ci)
    (inductives : ∀ n v, (n, Ix.ConstantInfo.inductInfo v) ∈ codeConsts.toList ↔
      (n, Ix.ConstantInfo.inductInfo v) ∈ full.consts.toList)
    (blocks : Ix.CondensedBlocks) (dbg : Bool) (sharingLimits : Ix.Sharing.Exact.Limits) (width : Nat) :
    compileEnvFold (hybridEnv codeConsts leanByIx) blocks dbg sharingLimits width =
      restore (hybridEnv codeConsts leanByIx) <$>
        compileEnvFold full blocks false sharingLimits foldWaveTasks :=
  compileEnvFold_lookups (hybrid_lookups full codeConsts leanByIx canon code)
    (groupOrder_eq (hybrid_lookups full codeConsts leanByIx canon code) (hybrid_heads inductives))
    blocks dbg false sharingLimits width foldWaveTasks

end Ix.Cert.Hybrid
