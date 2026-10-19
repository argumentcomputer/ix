import Ix.Cert.Schedule
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
the lookup view `{ consts := {}, fallback? := some env.get? }`, the fold with
the source count `env.consts.size + unmaterialized`, and the mixed-safety
check reads members through `get?` (the compiler's restatements for CQP.4,
behaviour-identical). So:

* `validateInductiveFlags_eq`, `validateMutualSafety_eq`: the two
  validations agree on environments with the same lookups whose inductive
  groups agree in order (`groupOrder`);
* `compileEnvFold_lookups`: **two such environments, with the same source
  count, compile alike** under every schedule (`width`, `dbg`, by CQP.4 a);
  the result's `CompileEnv` holds the environment and count it was given
  (`restore`);
* `hybrid_lookups`: the IO pipeline's hybrid environment has the
  materialized environment's lookups where that environment is the input's
  canonicalization (`Ix.Cert.Canon.constS` under each name) and its
  materialized code constants are the materialized environment's. The
  fallback's half is `Ix.Cert.Canon.canonChunkCorrect` (C1): a constant
  canonicalized on demand is the specification's (`fallback_spec`);
* `pipeline_fold`: **the IO pipeline's fold equals `Ix.Cert.compile`'s**, on
  one condensation, under those premises;
* `sourceClaimOwned_fuel`, `pipeline_walk`: the restatement's bound on the
  source-claim walk (`Ix.AuxGen.sourceClaimOwned`) changes nothing: from any
  bound of at least the number of input names, the walk returns the same
  result, never its bound's error (a name is pushed at most once, only
  while present and unseen, so the walk ends within that many iterations);
  the restatement passes exactly that number.

**What stays a premise, and why:** the validations take their inductive
groups from `inductiveGroups`, an `env.consts.fold` that keeps the first
`all` met for each group and is then sorted by name hash. The hybrid map
holds every inductive the materialized one does, so the two orders agree
when a group's members agree on `all` and no two groups' first members share
a hash field; `groupOrder` states that agreement. The IO layer's own steps
are tested, not proved: that its loops build the hybrid environment's
pieces as stated (`code`, `canon`, `sizes`), that its streamed
canonicalization, graph, ground filter and condensation are
`Ix.Cert.groundSplit`'s and `blocksOf`'s (`cert-compile-parity-init`), and
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

/-- The result's `CompileEnv`, given an environment and a count again. -/
def restore (env : Ix.Environment) (unmaterialized : Nat) :
    Ixon.Env × Nat × CompileEnv → Ixon.Env × Nat × CompileEnv :=
  fun (ixe, bytes, cenv) => (ixe, bytes, { cenv with env, unmaterialized })

/-- **Hybrid = materialized, generically**: two environments with the same
lookups, whose inductive groups agree in order and whose source counts are
equal, compile alike under every schedule; the result's `CompileEnv` holds
the environment and count it was given. -/
theorem compileEnvFold_lookups {e₁ e₂ : Ix.Environment} (lookups : ∀ n, e₁.get? n = e₂.get? n)
    (groups : groupOrder e₁ = groupOrder e₂) {u₁ u₂ : Nat} (count : e₁.consts.size + u₁ = e₂.consts.size + u₂)
    (blocks : Ix.CondensedBlocks) (dbg dbg' : Bool) (sharingLimits : Ix.Sharing.Exact.Limits)
    (width width' : Nat) :
    compileEnvFold e₁ blocks dbg u₁ sharingLimits width =
      restore e₁ u₁ <$> compileEnvFold e₂ blocks dbg' u₂ sharingLimits width' := by
  have get : Ix.Environment.get? e₁ = Ix.Environment.get? e₂ := funext lookups
  rw [Schedule.compileEnvFold_eq_seq, Schedule.compileEnvFold_eq_seq]
  unfold Schedule.compileEnvFoldSeq Schedule.compileEnvFoldWithSourceSeq
  rw [validateInductiveFlags_eq lookups groups, validateMutualSafety_eq lookups groups, count, get]
  generalize missingBlockRefs? blocks = missing
  generalize validateInductiveFlags e₂ = flags
  generalize validateMutualSafety e₂ blocks = safety
  cases missing <;> cases flags <;> cases safety <;> try rfl
  all_goals
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    generalize Schedule.foldWavesSeq _ _ _ _ = r
    cases r <;> rfl

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

/-- **The IO pipeline's fold equals `Ix.Cert.compile`'s** (CQP.4 b): over
one condensation, the fold over the IO pipeline's hybrid environment, with
its count of unmaterialized constants, its `--workers` width and its
options' trace, is the fold `Ix.Cert.compile` runs over the materialized
environment, its result's `CompileEnv` holding the hybrid environment and
count. Premises: the materialized environment is the input's
canonicalization and holds exactly the input's names, the materialized code
constants are its own, and the two environments' inductive groups agree in
order. -/
theorem pipeline_fold (full : Ix.Environment) (codeConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
    (leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo))
    (canon : ∀ n, full.get? n = (leanByIx.get? n).map fun p => Ix.Cert.Canon.constS p.2)
    (code : ∀ n ci, codeConsts.get? n = some ci → full.get? n = some ci)
    (sizes : codeConsts.size ≤ leanByIx.size ∧ full.consts.size = leanByIx.size)
    (groups : groupOrder (hybridEnv codeConsts leanByIx) = groupOrder full)
    (blocks : Ix.CondensedBlocks) (dbg : Bool) (sharingLimits : Ix.Sharing.Exact.Limits) (width : Nat) :
    compileEnvFold (hybridEnv codeConsts leanByIx) blocks dbg (leanByIx.size - codeConsts.size) sharingLimits
        width =
      restore (hybridEnv codeConsts leanByIx) (leanByIx.size - codeConsts.size) <$>
        compileEnvFold full blocks false 0 sharingLimits foldWaveTasks :=
  compileEnvFold_lookups (hybrid_lookups full codeConsts leanByIx canon code) groups
    (by show codeConsts.size + (leanByIx.size - codeConsts.size) = full.consts.size + 0; omega)
    blocks dbg false sharingLimits width foldWaveTasks

/-! ## The source-claim walk's bound

The fold's restatement changed the IO pipeline's bound on the source-claim
walk (`Ix.AuxGen.sourceClaimOwned`, from `checkAuxSourceClaim`) from the
code constants plus the name-hash index's size to the number of input
constants. `sourceClaimOwned_fuel` is why that changes nothing: each
iteration either returns or pops a pending name, and a name is pushed at
most once, only while it is present and not yet seen; so with a list `L`
covering the present names (up to `Ix.Name`'s `==`, under lookups that
respect it), the walk returns within `L.length + 1` iterations, and every
bound of at least `L.length` gives the same result, which is never the
bound's error. -/

theorem filter_length_mono {α : Type} {p q : α → Bool} (h : ∀ x, q x = true → p x = true) :
    ∀ l : List α, (l.filter q).length ≤ (l.filter p).length := by
  intro l
  induction l with
  | nil => simp
  | cons y l ih =>
    simp only [List.filter_cons]
    cases hq : q y <;> cases hp : p y <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
    · exact ih
    · omega
    · exact absurd (h y hq) (by simp [hp])
    · omega

theorem filter_length_lt {α : Type} {p q : α → Bool} (h : ∀ x, q x = true → p x = true) :
    ∀ (l : List α) (x₀ : α), x₀ ∈ l → p x₀ = true → q x₀ = false → (l.filter q).length < (l.filter p).length := by
  intro l
  induction l with
  | nil => intro x₀ inside; cases inside
  | cons y l ih =>
    intro x₀ inside px qx
    have mono := filter_length_mono h l
    simp only [List.filter_cons]
    rcases List.mem_cons.mp inside with rfl | later
    · rw [px, qx]
      simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]
      omega
    · have strict := ih x₀ later px qx
      cases hq : q y <;> cases hp : p y <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      · exact strict
      · omega
      · exact absurd (h y hq) (by simp [hp])
      · omega

section Walk

variable (env : Ix.Environment) (L : List Ix.Name)

/-- The walk's measure: the present names in `L` not yet seen, plus the
pending names. -/
def measure (s : List Ix.Name × Std.HashSet Ix.Name) : Nat :=
  (L.filter fun x => (env.get? x).isSome && !s.2.contains x).length + s.1.length

/-- Pushing a present name not yet seen does not raise the measure, where
`L` covers the present names up to `==` and lookups respect `==`. -/
theorem measure_push (covers : ∀ n, (env.get? n).isSome = true → L.contains n = true)
    (invariant : ∀ a b, (a == b) = true → env.get? a = env.get? b) (pending : List Ix.Name)
    (seen : Std.HashSet Ix.Name) (r : Ix.Name) (fresh : (!seen.contains r && (env.get? r).isSome) = true) :
    measure env L (r :: pending, seen.insert r) ≤ measure env L (pending, seen) := by
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at fresh
  obtain ⟨x, inside, same⟩ := List.contains_iff_exists_mem_beq.mp (covers r fresh.2)
  have lookup : env.get? x = env.get? r := invariant x r (BEq.symm same)
  have seenSame : seen.contains x = seen.contains r := Std.HashSet.contains_congr (BEq.symm same)
  unfold measure
  have strict := filter_length_lt (l := L) (x₀ := x)
    (p := fun x => (env.get? x).isSome && !seen.contains x)
    (q := fun x => (env.get? x).isSome && !(seen.insert r).contains x)
    (by
      intro x hx
      simp only [Std.HashSet.contains_insert, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.or_eq_false_iff] at hx ⊢
      exact ⟨hx.1, hx.2.2⟩)
    inside (by simp [lookup, seenSame, fresh.1, fresh.2])
    (by simp [Std.HashSet.contains_insert, same])
  simp only [List.length_cons]
  omega

end Walk

theorem idBind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

/-- **A fuel loop whose step either exits or lowers a measure** exits, with
one value, from any two fuel lists longer than the measure. -/
theorem fuel_exit {σ ρ α : Type} (Φ : σ → Nat) (R : ρ → Prop)
    {body : α → Option ρ × σ → Id (ForInStep (Option ρ × σ))}
    (ignores : ∀ x y p, body x p = body y p)
    (step : ∀ x s, (∃ r t, body x (none, s) = .done (some r, t) ∧ R r) ∨
      (∃ s', body x (none, s) = .yield (none, s') ∧ Φ s' < Φ s))
    {l l' : List α} {s : σ} (long : Φ s < l.length) (long' : Φ s < l'.length) {o o' : Option ρ}
    (run : (forIn (m := Id) l (none, s) body).1 = o) (run' : (forIn (m := Id) l' (none, s) body).1 = o') :
    o = o' ∧ ∃ r, o = some r ∧ R r := by
  subst run run'
  induction l generalizing l' s with
  | nil => simp at long
  | cons x l ih =>
    cases l' with
    | nil => simp at long'
    | cons x' l' =>
      rw [List.forIn_cons, List.forIn_cons, ignores x' x]
      rcases step x s with ⟨r, t, exits, holds⟩ | ⟨s', yields, lower⟩
      · rw [exits]
        exact ⟨rfl, r, rfl, holds⟩
      · rw [yields]
        simp only [List.length_cons] at long long'
        exact ih (by omega) (by omega)

/-- A loop of steps that never raise a measure does not raise it. -/
theorem forIn_measure {σ α : Type} (Φ : σ → Nat) {body : α → σ → Id (ForInStep σ)}
    (step : ∀ x s, ∃ s', body x s = .yield s' ∧ Φ s' ≤ Φ s) :
    ∀ (l : List α) (s : σ), Φ (forIn (m := Id) l s body) ≤ Φ s := by
  intro l
  induction l with
  | nil => intro s; exact Nat.le_refl _
  | cons x l ih =>
    intro s
    rw [List.forIn_cons]
    obtain ⟨s', yields, lower⟩ := step x s
    rw [yields]
    exact Nat.le_trans (ih s') lower

set_option hygiene false in
/-- The walk's step obligations, on its inline step. -/
local macro "walk_step" : tactic => `(tactic| (
  intro x s
  rcases s with ⟨pending, seen⟩
  cases pending with
  | nil => exact .inl ⟨_, _, rfl, false, rfl⟩
  | cons n rest =>
    dsimp only
    by_cases own : owners.contains n = true
    · simp only [own, ↓reduceIte]
      exact .inl ⟨_, _, rfl, true, rfl⟩
    · simp only [own, Bool.false_eq_true, ↓reduceIte]
      cases found : env.get? n with
      | none =>
        refine .inr ⟨_, rfl, ?_⟩
        simp only [measure, List.length_cons]
        omega
      | some ci =>
        dsimp only
        by_cases hits : (Ix.AuxGen.auxSourceRefs ci).toList.any owners.contains = true
        · simp only [hits, ↓reduceIte]
          exact .inl ⟨_, _, rfl, true, rfl⟩
        · simp only [hits, Bool.false_eq_true, ↓reduceIte]
          refine .inr ⟨_, rfl, ?_⟩
          rw [Std.HashSet.forIn_eq_forIn_toList]
          refine Nat.lt_of_le_of_lt (forIn_measure (measure env L) ?_ _ _) ?_
          · intro r p
            by_cases fresh : (!p.2.contains r && (env.get? r).isSome) = true
            · simp only [fresh, ↓reduceIte]
              exact ⟨_, rfl, measure_push env L covers invariant p.1 p.2 r fresh⟩
            · simp only [fresh, Bool.false_eq_true, ↓reduceIte]
              exact ⟨_, rfl, Nat.le_refl _⟩
          · simp only [measure, List.length_cons]
            omega))

/-- **The source-claim walk's result does not depend on its bound**, from
the number of names of a list covering the present names on: with a bound of
at least `L.length` the walk returns within its iterations (never its
"exceeded" error), and any two such bounds give the same result. -/
theorem sourceClaimOwned_fuel (env : Ix.Environment) (L : List Ix.Name)
    (covers : ∀ n, (env.get? n).isSome = true → L.contains n = true)
    (invariant : ∀ a b, (a == b) = true → env.get? a = env.get? b) (owners : Std.HashSet Ix.Name) (name : Ix.Name)
    {k k' : Nat} (bound : L.length ≤ k) (bound' : L.length ≤ k') :
    Ix.AuxGen.sourceClaimOwned env owners name k = Ix.AuxGen.sourceClaimOwned env owners name k' ∧
      ∃ b, Ix.AuxGen.sourceClaimOwned env owners name k = .ok b := by
  unfold Ix.AuxGen.sourceClaimOwned
  simp only [Id.run]
  by_cases absent : (env.get? name).isNone = true
  · simp only [absent, ↓reduceIte]
    exact ⟨trivial, true, rfl⟩
  · simp only [absent, Bool.false_eq_true, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', idBind]
    have present : (env.get? name).isSome = true := by
      cases found : env.get? name <;> simp_all
    have start : measure env L ([name], (∅ : Std.HashSet Ix.Name).insert name) < L.length + 1 := by
      unfold measure
      obtain ⟨x, inside, same⟩ := List.contains_iff_exists_mem_beq.mp (covers name present)
      have strict := filter_length_lt (l := L) (x₀ := x) (p := fun _ => true)
        (q := fun x => (env.get? x).isSome && !((∅ : Std.HashSet Ix.Name).insert name).contains x)
        (by intros; rfl) inside rfl (by simp [Std.HashSet.contains_insert, same])
      rw [List.filter_eq_self.mpr (fun _ _ => rfl)] at strict
      simp only [List.length_cons, List.length_nil]
      omega
    have long : measure env L ([name], (∅ : Std.HashSet Ix.Name).insert name) <
        (List.range' 0 [:k + 1].size).length := by
      simp [Std.Legacy.Range.size]; omega
    have long' : measure env L ([name], (∅ : Std.HashSet Ix.Name).insert name) <
        (List.range' 0 [:k' + 1].size).length := by
      simp [Std.Legacy.Range.size]; omega
    split
    · rename_i r run
      split
      · rename_i r' run'
        have key := fuel_exit (measure env L) (fun r => ∃ b, r = .ok b) (fun _ _ _ => rfl) (by walk_step)
          long long' run run'
        obtain ⟨same, b, exited, holds⟩ := key
        cases same
        cases exited
        obtain ⟨b, rfl⟩ := holds
        exact ⟨rfl, b, rfl⟩
      · rename_i _ run'
        have key := fuel_exit (measure env L) (fun r => ∃ b, r = .ok b) (fun _ _ _ => rfl) (by walk_step)
          long long' run run'
        cases key.1
    · rename_i _ run
      have key := fuel_exit (measure env L) (fun r => ∃ b, r = .ok b) (fun _ _ _ => rfl) (by walk_step)
        long long run run
      obtain ⟨_, _, exited, _⟩ := key
      cases exited

/-- The walk reads its environment through `get?` only. -/
theorem sourceClaimOwned_lookups {e₁ e₂ : Ix.Environment} (lookups : ∀ n, e₁.get? n = e₂.get? n) :
    Ix.AuxGen.sourceClaimOwned e₁ = Ix.AuxGen.sourceClaimOwned e₂ := by
  have get : Ix.Environment.get? e₁ = Ix.Environment.get? e₂ := funext lookups
  funext owners name bound
  unfold Ix.AuxGen.sourceClaimOwned
  rw [get]

/-- The fold's lookup view of an environment has its lookups. -/
theorem view_get (env : Ix.Environment) (n : Ix.Name) :
    ({ consts := {}, fallback? := some env.get? } : Ix.Environment).get? n = env.get? n := by
  unfold Ix.Environment.get?
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]

/-- The hybrid environment's lookups respect `Ix.Name`'s `==`. -/
theorem hybrid_invariant (codeConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
    (leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo)) :
    ∀ a b, (a == b) = true → (hybridEnv codeConsts leanByIx).get? a = (hybridEnv codeConsts leanByIx).get? b := by
  intro a b same
  unfold hybridEnv Ix.Environment.get?
  simp only [Std.HashMap.get?_eq_getElem?]
  rw [Std.HashMap.getElem?_congr same, Std.HashMap.getElem?_congr (m := leanByIx) same]

/-- The hybrid environment's present names are `leanByIx`'s, when its code
constants are keyed among them. -/
theorem hybrid_covers (codeConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
    (leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo))
    (keys : ∀ n, codeConsts.contains n = true → leanByIx.contains n = true) :
    ∀ n, ((hybridEnv codeConsts leanByIx).get? n).isSome = true → leanByIx.keys.contains n = true := by
  intro n present
  rw [Std.HashMap.contains_keys]
  unfold hybridEnv Ix.Environment.get? at present
  simp only [Std.HashMap.get?_eq_getElem?] at present
  cases materialized : codeConsts[n]? with
  | some ci =>
    exact keys n (by rw [Std.HashMap.contains_eq_isSome_getElem?, materialized]; rfl)
  | none =>
    rw [materialized] at present
    rw [Std.HashMap.contains_eq_isSome_getElem?]
    cases found : leanByIx[n]? with
    | none => rw [found] at present; cases present
    | some _ => rfl

/-- **The restatement's bound on the source-claim walk changes nothing on
the IO pipeline**: the walk over the fold's lookup view of the hybrid
environment with any bound of at least `leanByIx.size` (the restatement
passes exactly that) gives the walk over the hybrid environment itself with
any other such bound (the bound before it, the code constants plus the
name-hash index, is `codeConsts.size + leanByIx.size`: both maps key the
input names by their hash fields), and it is never the bound's error. -/
theorem pipeline_walk (codeConsts : Std.HashMap Ix.Name Ix.ConstantInfo)
    (leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo))
    (keys : ∀ n, codeConsts.contains n = true → leanByIx.contains n = true)
    (owners : Std.HashSet Ix.Name) (name : Ix.Name) {k k' : Nat} (bound : leanByIx.size ≤ k)
    (bound' : leanByIx.size ≤ k') :
    Ix.AuxGen.sourceClaimOwned { consts := {}, fallback? := some (hybridEnv codeConsts leanByIx).get? } owners
        name k = Ix.AuxGen.sourceClaimOwned (hybridEnv codeConsts leanByIx) owners name k' ∧
      ∃ b, Ix.AuxGen.sourceClaimOwned (hybridEnv codeConsts leanByIx) owners name k' = .ok b := by
  rw [sourceClaimOwned_lookups (view_get (hybridEnv codeConsts leanByIx))]
  have walk := sourceClaimOwned_fuel (hybridEnv codeConsts leanByIx) leanByIx.keys
    (hybrid_covers codeConsts leanByIx keys) (hybrid_invariant codeConsts leanByIx) owners name
    (by rw [Std.HashMap.length_keys]; exact bound) (by rw [Std.HashMap.length_keys]; exact bound')
  refine ⟨walk.1, ?_⟩
  obtain ⟨b, ok⟩ := walk.2
  exact ⟨b, walk.1 ▸ ok⟩

end Ix.Cert.Hybrid
