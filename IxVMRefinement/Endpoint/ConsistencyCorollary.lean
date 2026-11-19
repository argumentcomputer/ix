import IxVMRefinement.Endpoint.ComposedResidual
import IxVMRefinement.StatementRel.ReadsMono
import IxC.Kernel.SetTheory.FiniteChain
import Ix.IxVM.Consistency.ReadsKeys
import Ix.IxVM.Consistency.Restrict
import Ix.Cert.CompileCorrectProof
import Ix.Cert.ReadingKeys
import IxC.Kernel.Audit.Axioms

/-!
# End-to-end consistency corollaries, anti-vacuity, and compiler composition

This module packages the unconditional zero-argument theorem
`IxVM.Refinement.Endpoint.circuitComposed : IxVM.Consistency.CircuitComposed`
into consumer-facing corollaries and verification checks:

1. **Circuit-level `no-False` and `SeedsInhabited` corollaries**:
   * `circuitComposed_selfHashed`, `circuitComposed_no_False`, and
     `circuitComposed_seeds_inhabited` lift `ComposedSpec.selfHashed`,
     `ComposedSpec.seeds_not_false`, and `ComposedSpec.seeds_inhabited` to the
     circuit level directly from `circuitComposed`, parametric in any
     `Ix.Kernel.SetTheory W`.
   * `circuitComposed_no_False_VSet` and `circuitComposed_seeds_inhabited_VSet`
     instantiate the `SetTheory` parameter concretely on the pure-Lean Aczel
     set universe `Ix.Kernel.VSet.{u}` (`IxC/Kernel/SetTheory/FiniteChain.lean`)
     under `Ix.Kernel.VSet.OmegaUniverses.{u}` (the exact set-theoretic
     assumption equivalent to Carneiro's `OmegaInaccessibles` in
     `Models/SetTheory/IxSetTheoryModel/Carneiro.lean`).  Every finite prefix
     `FiniteSetTheory n` of that axiom interface is unconditionally inhabited
     in Lean's universe hierarchy (`VSet.finiteSetTheory0` .. `VSet.finiteSetTheory4`).

2. **Kernel-checked conditional anti-vacuity lemmas**:
   * `emptyEnv_has_model` shows that `Ix.Kernel.Model` is non-vacuously
     inhabited on valid environments.
   * `no_model_of_proof_of_False` and `badEnvFalse_no_model` show that no
     `Ix.Kernel.Model` exists for any environment containing a constant of type
     `False`.
   * `no_model_of_alias_False` and `badEnvAliasFalse_no_model` show that no
     `Ix.Kernel.Model` exists for an environment containing a definition
     `P : Prop := False` together with a constant `t : P` (exercising both
     `Model.defn_value` and `Model.false_empty`, not merely syntactic absence
     of `False`).
   * `consistentReadOver_no_alias_False` lifts that refutation directly to the
     `ConsistentReadOver` conclusion of `CircuitComposed`.

3. **Thin `compileCorrect` ↔ `ReadsIn` composition adapter**:
   * `selfHashed_of_compileReport` combines `Ix.Cert.compileAuthentic` with an
     admitted binding to produce a `SelfHashed` reader view for `CircuitComposed`.
   * `readsIn_agree_of_compat` shows that any two agreeing `(store, blob)` pairs
     determine the same reading up to `SameReading` (`ReadsIn.mono` +
     `ReadsIn.functional`).
   * `noCollision_agrees_with_view` shows that in the collision-free branch of
     `ComposedSpec`, the binding run hashed the exact bytes of the view's role
     binding and admitted the exact same role table, every record and blob loaded
     by either run agrees byte-for-byte with the view on their overlap, and
     `ReadsIn` over `(storeOver E₀ R, blobOver E₀ R)` agrees with `Reads` over
     `V.env` up to `SameReading`.
   * `compileCorrect_circuitComposed_bridge` composes
     `Ix.Cert.ReaderStreamsTrace.compileCorrect` with
     `IxVM.Refinement.Endpoint.circuitComposed` over the compiled artifact's
     view.

## Remaining non-certified boundaries (TCB)

The formal theorems here cover the Lean-level Aiur circuit semantics
(`CircuitSound`), the IxVM program (`IxVM.source`), the Ixon reading (`ReadsIn`),
the kernel model (`Ix.Kernel.Model`), and the pure certified compiler
(`Ix.Cert.compileReport`).  The following remain outside the formal theorem:
* Rust lowering to Multi-STARK, STARK/FRI/LogUp cryptographic soundness,
  proof-compression circuits/keys, and the `aiur⟦⟧` DSL elaborators;
* exporter runtime obligations (`Depth.Certified`, `WellFormedActivation`,
  `cfg.bits ≤ 24`) and host `Claim.de`/Ixon codec parity with Rust;
* Rust BLAKE3 vs pure Lean `Address.blake3Pure` (`@[implemented_by]`);
* post-compile binder-data section attachment (`Ix.CompileM.compileCertified` /
  `RecordSections`), which produces sectioned records whose content addresses
  differ from bare `compileReport` records (when verified by `CircuitComposed`,
  the theorem applies directly to the sectioned view);
* existence of a full ω-chain of Grothendieck universes (`Ix.Kernel.SetTheory W`
  / `VSet.OmegaUniverses` / Mathlib `OmegaInaccessibles`), which is equivalent
  to Lean's own consistency strength.
-/

universe u v

namespace IxVM.Refinement.Endpoint

open IxVM.Consistency
open IxVM.Refinement (View Digest packDigest Hashed CircuitSound)
open Aiur.Generic.SourceSemantics (Call)
open Ix (Claim)
open Ix.Kernel (SetTheory VSet)

/-! ## 1. Concrete single-set-theory inhabitation and circuit-level `no-False` corollaries -/

open Ix.Kernel.SetTheory in
/-- **`SeedsInhabited` instantiated at one set theory `W`**: the claimed
environment has a model in `W`, and for each constant address a seed covers,
the stored constant `ci` is a pinned basis constant or `KeptIn`, and in every
model in `W`, at every level assignment, `ci`'s type denotes a set inhabited by
`ci`'s value. -/
def SeedsInhabitedIn (W : Type v) [SetTheory W] (calls : List (Call IxVM.F))
    (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (seeds : List Address) : Prop :=
  ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon), LoadedBy calls E₀ ∧
    Nonempty (Ix.Kernel.Model W (claimedEnv env)) ∧
    ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
      ∃ ci, env.find? (keyOf t a') = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (storeOver E₀ R) (blobOver E₀ R) a' ci) ∧
        ∀ (M : Ix.Kernel.Model W (claimedEnv env)) (φ : Ix.Kernel.LevelParam → Nat)
          (ρ : Ix.Kernel.BVarIdx → W),
          ∃ T, Ix.Kernel.Denotes M.cval (claimedEnv env) φ ρ ci.toConstantVal.type T ∧
            M.cval ci.name φ ∈ˢ T

/-- Specialize `SeedsInhabited` to a concrete set theory `W`. -/
theorem seedsInhabitedIn_of (W : Type v) [SetTheory W] {calls : List (Call IxVM.F)}
    {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {seeds : List Address}
    (h : SeedsInhabited.{v} calls t R seeds) : SeedsInhabitedIn W calls t R seeds := by
  obtain ⟨E₀, env, hload, hmodel, hseeds⟩ := h
  refine ⟨E₀, env, hload, hmodel W, fun a ha a' ha' => ?_⟩
  obtain ⟨ci, hfind, hprov, hinh⟩ := hseeds a ha a' ha'
  exact ⟨ci, hfind, hprov, fun M φ ρ => hinh W M φ ρ⟩

/-- **Circuit-level composed soundness over a `SelfHashed` view**: for any
accepted binding proof and accepted in-scope typing proof sharing the table
address `a`, either the runs exhibited a `GenuineCollision` against the view,
claims, and committed footprint, or the binding table admits and validates on
all 77 groups and `ConsistentReadOver` holds for the typing run's seeds. -/
theorem circuitComposed_selfHashed :
    CircuitSound fun callsB dB =>
      CircuitSound fun callsA dA =>
        ∀ (bytesB : ByteArray) (spec a : Address), Claim.de bytesB = .ok (.binding spec a) →
          packDigest (Address.blake3Pure bytesB) = dB →
          ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
            packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
            ∀ ctx, cA.context? = some ctx → ctx.binding = a →
              ∀ (V : View) (seeds : List Address), ClaimSeeds cA V seeds → SelfHashed V →
                GenuineCollision V (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
                  ComposedWith.{u} (fun t R envT => ConsistentReadOver.{u} callsA t R envT seeds)
                    callsB a := by
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposed.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hs hV
  exact hSpec.selfHashed deB dgB deA dgA hsc hctx hba hs hV

/-- **Circuit-level `no-False` corollary**, parametric in any `Ix.Kernel.SetTheory W`:
if the IxVM circuit accepts a `binding spec a` claim and an in-scope typing
claim under `a`, over any `SelfHashed` view of its seeds, then either the two
runs exhibited a `GenuineCollision` or the binding table is valid and the
claimed environment is consistent with no covered seed stored or declared with
type `False` (`SeedsNotFalse`). -/
theorem circuitComposed_no_False (W : Type u) [SetTheory W] :
    CircuitSound fun callsB dB =>
      CircuitSound fun callsA dA =>
        ∀ (bytesB : ByteArray) (spec a : Address), Claim.de bytesB = .ok (.binding spec a) →
          packDigest (Address.blake3Pure bytesB) = dB →
          ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
            packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
            ∀ ctx, cA.context? = some ctx → ctx.binding = a →
              ∀ (V : View) (seeds : List Address), ClaimSeeds cA V seeds → SelfHashed V →
                GenuineCollision V (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
                  ComposedWith.{u} (fun t R _ => SeedsNotFalse callsA t R seeds) callsB a := by
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposed_selfHashed.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hs hV
  exact (hSpec bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hs hV).imp_right
    (ComposedWith.imp fun _ _ _ hr => ConsistentReadOver.seeds_not_false W hr)

/-- **Circuit-level `SeedsInhabited` corollary**: for any accepted pair of
binding and typing claims over a `SelfHashed` view, either the runs exhibited a
`GenuineCollision` or every covered seed's stored type is inhabited in every
`SetTheory` model of the claimed environment. -/
theorem circuitComposed_seeds_inhabited :
    CircuitSound fun callsB dB =>
      CircuitSound fun callsA dA =>
        ∀ (bytesB : ByteArray) (spec a : Address), Claim.de bytesB = .ok (.binding spec a) →
          packDigest (Address.blake3Pure bytesB) = dB →
          ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
            packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
            ∀ ctx, cA.context? = some ctx → ctx.binding = a →
              ∀ (V : View) (seeds : List Address), ClaimSeeds cA V seeds → SelfHashed V →
                GenuineCollision V (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
                  ComposedWith.{u} (fun t R _ => SeedsInhabited.{u} callsA t R seeds) callsB a := by
  refine circuitSound_mono (fun callsB dB hA => ?_) circuitComposed_selfHashed.{u}
  refine circuitSound_mono (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hs hV
  exact (hSpec bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hs hV).imp_right
    (ComposedWith.imp fun _ _ _ hr => ConsistentReadOver.seeds_inhabited hr)

/-- **Concrete `VSet` (pure-Lean ZF-set) `no-False` corollary of `circuitComposed`**:
given an ω-chain of Grothendieck universes in `VSet.{u}` (`VSet.OmegaUniverses`),
no `SetTheory` parameter remains — accepted binding and typing proofs either
exhibit a `GenuineCollision` or establish `SeedsNotFalse`. -/
theorem circuitComposed_no_False_VSet (hΩ : VSet.OmegaUniverses.{u}) :
    CircuitSound fun callsB dB =>
      CircuitSound fun callsA dA =>
        ∀ (bytesB : ByteArray) (spec a : Address), Claim.de bytesB = .ok (.binding spec a) →
          packDigest (Address.blake3Pure bytesB) = dB →
          ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
            packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
            ∀ ctx, cA.context? = some ctx → ctx.binding = a →
              ∀ (V : View) (seeds : List Address), ClaimSeeds cA V seeds → SelfHashed V →
                GenuineCollision V (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
                  ComposedWith.{u + 1} (fun t R _ => SeedsNotFalse callsA t R seeds) callsB a :=
  @circuitComposed_no_False.{u + 1} VSet.{u} (VSet.setTheoryOfOmegaUniverses hΩ)

/-- **Concrete `VSet` `SeedsInhabited` corollary of `circuitComposed`**: given
`VSet.OmegaUniverses.{u}`, every covered seed's stored type is inhabited in
every `VSet.{u}` model of the claimed environment, and one exists. -/
theorem circuitComposed_seeds_inhabited_VSet (hΩ : VSet.OmegaUniverses.{u}) :
    CircuitSound fun callsB dB =>
      CircuitSound fun callsA dA =>
        ∀ (bytesB : ByteArray) (spec a : Address), Claim.de bytesB = .ok (.binding spec a) →
          packDigest (Address.blake3Pure bytesB) = dB →
          ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
            packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
            ∀ ctx, cA.context? = some ctx → ctx.binding = a →
              ∀ (V : View) (seeds : List Address), ClaimSeeds cA V seeds → SelfHashed V →
                GenuineCollision V (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
                  ComposedWith.{u + 1}
                    (fun t R _ => @SeedsInhabitedIn VSet.{u} (VSet.setTheoryOfOmegaUniverses hΩ)
                      callsA t R seeds)
                    callsB a := by
  refine @circuitSound_mono _ _ (fun callsB dB hA => ?_) (@circuitComposed_seeds_inhabited.{u + 1})
  refine @circuitSound_mono _ _ (fun callsA dA hSpec => ?_) hA
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hs hV
  exact (hSpec bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hs hV).imp_right
    (ComposedWith.imp fun _ _ _ hr =>
      @seedsInhabitedIn_of.{u + 1} VSet.{u} (VSet.setTheoryOfOmegaUniverses hΩ) _ _ _ _ hr)

/-! ## 2. Kernel-checked conditional anti-vacuity lemmas -/

/-- **Positive non-vacuity of `Ix.Kernel.Model`**: the empty environment has a
model in every `SetTheory V`.  Together with the refutations below, this shows
that `Nonempty (Ix.Kernel.Model V env)` is neither vacuously true nor vacuously
false. -/
theorem emptyEnv_has_model {md : Ix.Kernel.Mode} (V : Type u) [SetTheory V] :
    Nonempty (Ix.Kernel.Model V (⟨[]⟩ : Ix.Kernel.Env md)) := by
  refine ⟨{
    cval := fun _ _ => Ix.Kernel.SetTheory.empty
    mem := fun _ hc => nomatch hc
    false_empty := fun _ _ _ h => by cases h with | const hf _ => cases hf
    eq_equality := fun _ _ _ _ _ _ _ h => by cases h with | const hf _ => cases hf
    punit_unit := fun _ _ _ _ _ _ _ _ _ _ h => by cases h with | const hf _ => cases hf
    defn_value := fun _ _ _ hc => nomatch hc
    iota_rule := fun _ _ _ _ _ _ hf => nomatch hf
    unit_like := fun _ _ _ hf => nomatch hf
    proj_law := fun _ _ _ _ _ _ hf => nomatch hf
    proj_type := fun _ _ _ hf => by simp [Ix.Kernel.Env.findProj?, Ix.Kernel.Env.find?] at hf
    eta_fn := fun _ _ _ _ hf => nomatch hf
    lit_ops := ⟨(fun _ _ _ hf => nomatch hf), (fun _ _ _ _ _ _ hf => nomatch hf),
      (fun _ _ _ _ _ _ hf => nomatch hf)⟩
    nat_add := fun _ _ _ hf => nomatch hf
    graded := fun _ hc => nomatch hc
    cval_params := fun _ _ hf => nomatch hf
  }⟩

/-- **Anti-vacuity (direct `t : False`)**: no `Ix.Kernel.Model` exists in any
`SetTheory V` for an environment containing a constant of type `False`. -/
theorem no_model_of_proof_of_False {md : Ix.Kernel.Mode} (V : Type u) [SetTheory V]
    {env : Ix.Kernel.Env md} {ci : Ix.Kernel.ConstantInfo md}
    (hci : ci ∈ env.consts) (hty : ci.toConstantVal.type = .const Ix.Kernel.falseName []) :
    IsEmpty (Ix.Kernel.Model V env) :=
  ⟨fun M => M.consistent ci hci hty⟩

/-- **Anti-vacuity (aliased `P := False; t : P`)**: no `Ix.Kernel.Model` exists
in any `SetTheory V` for an environment that defines `P := False` (with zero
level parameters) and contains a constant `t : P`.  This exercises both
`Model.defn_value` (δ) and `Model.false_empty`, showing that semantic models
cannot satisfy a false alias by reinterpreting `P` as `True`. -/
theorem no_model_of_alias_False {md : Ix.Kernel.Mode} (V : Type u) [SetTheory V]
    {env : Ix.Kernel.Env md} {pName : Ix.Kernel.Key md} {cvP : Ix.Kernel.ConstantVal md}
    {hint : Ix.Kernel.ReducibilityHint} {ciT : Ix.Kernel.ConstantInfo md}
    (hfindP : env.find? pName = some (.defnInfo cvP (.const Ix.Kernel.falseName []) hint))
    (hlpsP : cvP.levelParams = [])
    (hciT : ciT ∈ env.consts) (htyT : ciT.toConstantVal.type = .const pName []) :
    IsEmpty (Ix.Kernel.Model V env) := by
  refine ⟨fun M => ?_⟩
  let φ : Ix.Kernel.LevelParam → Nat := fun _ => 0
  let ρ : Ix.Kernel.BVarIdx → V := fun _ => Ix.Kernel.SetTheory.empty
  obtain ⟨T, hDenT, hmem⟩ := M.mem ciT hciT φ ρ
  rw [htyT] at hDenT
  have hDenP : Ix.Kernel.Denotes M.cval env φ ρ (.const pName [])
      (M.cval pName (Ix.Kernel.Level.substFn φ cvP.levelParams [])) :=
    Ix.Kernel.Denotes.const hfindP (by simp [Ix.Kernel.ConstantInfo.toConstantVal, hlpsP])
  have hTeq : T = M.cval pName (Ix.Kernel.Level.substFn φ cvP.levelParams []) :=
    Ix.Kernel.Denotes_functional hDenT hDenP
  have hparams : M.cval pName (Ix.Kernel.Level.substFn φ cvP.levelParams []) = M.cval pName φ :=
    M.cval_params pName _ hfindP _ φ
      (fun p hp => by simp only [Ix.Kernel.ConstantInfo.toConstantVal, hlpsP] at hp; cases hp)
  have hmemP : Ix.Kernel.ConstantInfo.defnInfo cvP (.const Ix.Kernel.falseName []) hint ∈ env.consts :=
    List.mem_of_find?_eq_some hfindP
  have hnameP : cvP.name = pName := by
    have h := List.find?_some hfindP
    simpa [Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal] using h
  have hDenFalse : Ix.Kernel.Denotes M.cval env φ ρ (.const Ix.Kernel.falseName [])
      (M.cval cvP.name φ) :=
    M.defn_value cvP (.const Ix.Kernel.falseName []) hint hmemP φ ρ
  have hEmpty : M.cval cvP.name φ = Ix.Kernel.SetTheory.empty :=
    M.false_empty φ ρ (M.cval cvP.name φ) hDenFalse
  rw [hTeq, hparams, ← hnameP, hEmpty] at hmem
  exact Ix.Kernel.SetTheory.not_mem_empty _ hmem

/-- Concrete witness environment containing `False` and an axiom `t : False`. -/
def badEnvFalse : Ix.Kernel.Env .anon :=
  let tKey : Ix.Kernel.Key .anon := .id ⟨ByteArray.mk #[1]⟩
  ⟨[.axiomInfo ⟨tKey, [], .const Ix.Kernel.falseName []⟩,
    .indInfo ⟨Ix.Kernel.falseName, [], .sort .zero⟩ {}]⟩

/-- Concrete witness environment containing `False`, `def P : Prop := False`,
and `axiom t : P`. -/
def badEnvAliasFalse : Ix.Kernel.Env .anon :=
  let pKey : Ix.Kernel.Key .anon := .id ⟨ByteArray.mk #[2]⟩
  let tKey : Ix.Kernel.Key .anon := .id ⟨ByteArray.mk #[3]⟩
  ⟨[.axiomInfo ⟨tKey, [], .const pKey []⟩,
    .defnInfo ⟨pKey, [], .sort .zero⟩ (.const Ix.Kernel.falseName []) .abbrev,
    .indInfo ⟨Ix.Kernel.falseName, [], .sort .zero⟩ {}]⟩

/-- **Concrete anti-vacuity control 1**: `badEnvFalse` (`t : False`) has no model
in any `SetTheory V`. -/
theorem badEnvFalse_no_model (V : Type u) [SetTheory V] :
    IsEmpty (Ix.Kernel.Model V badEnvFalse) :=
  no_model_of_proof_of_False V (List.mem_cons_self ..) rfl

/-- **Concrete anti-vacuity control 2**: `badEnvAliasFalse` (`P := False; t : P`)
has no model in any `SetTheory V`. -/
theorem badEnvAliasFalse_no_model (V : Type u) [SetTheory V] :
    IsEmpty (Ix.Kernel.Model V badEnvAliasFalse) := by
  let pKey : Ix.Kernel.Key .anon := .id ⟨ByteArray.mk #[2]⟩
  have hfindP : badEnvAliasFalse.find? pKey =
      some (.defnInfo ⟨pKey, [], .sort .zero⟩ (.const Ix.Kernel.falseName []) .abbrev) := by
    simp only [badEnvAliasFalse, pKey, Ix.Kernel.Env.find?, List.find?,
      Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal]
    rfl
  exact no_model_of_alias_False V hfindP rfl (List.mem_cons_self ..) rfl

/-- **Anti-vacuity on `ConsistentReadOver`**: in any `SetTheory W`, no claimed
environment witnessed by `ConsistentReadOver` can contain both a non-auxiliary
definition `P := False` (zero level parameters) and any claimed constant `t : P`
(even though `P`'s type is `Sort 0`, not `False`). -/
theorem consistentReadOver_no_alias_False (W : Type u) [SetTheory W]
    {calls : List (Call IxVM.F)} {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {seeds : List Address}
    (h : ConsistentReadOver.{u} calls t R envT seeds) :
    ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon), LoadedBy calls E₀ ∧
      ∀ (aP : Address) (cvP : Ix.Kernel.ConstantVal .anon) (hint : Ix.Kernel.ReducibilityHint)
        (ciT : Ix.Kernel.ConstantInfo .anon),
        env.find? (keyOf t aP) = some (.defnInfo cvP (.const Ix.Kernel.falseName []) hint) →
        cvP.levelParams = [] →
        ciT ∈ (claimedEnv env).consts →
        ciT.toConstantVal.type = .const (keyOf t aP) [] →
        False := by
  obtain ⟨E₀, env, hload, -, -, -, -, hmodel⟩ := h
  refine ⟨E₀, env, hload, fun aP cvP hint ciT hfindP hlpsP hciT htyT => ?_⟩
  have hNotAux : ∀ k d, keyOf t aP ≠ .aux k d := by
    intro k d hk
    rcases keyOf_cases t aP with ⟨h1, -⟩ | ⟨r, -, h1⟩ <;> rw [h1] at hk <;> cases hk
  have hfindClaimed : (claimedEnv env).find? (keyOf t aP) =
      some (.defnInfo cvP (.const Ix.Kernel.falseName []) hint) := by
    rw [claimedEnv_find? (keptKey_of_not_aux hNotAux)]
    exact hfindP
  obtain ⟨M⟩ := hmodel W
  exact (no_model_of_alias_False W hfindClaimed hlpsP hciT htyT).false M

/-! ## 3. Thin `compileCorrect` ↔ `ReadsIn` / `CircuitComposed` composition adapter -/

/-- **A compiled artifact paired with an admitted role binding yields a `SelfHashed`
view**, bridging `Ix.Cert.compileAuthentic` to `ComposedSpec.selfHashed`. -/
theorem selfHashed_of_compileReport {env : Ix.Environment} {ixe : Ixon.Env}
    {failures : Ix.Cert.Failures} {binding : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} (trees : List Ix.AssumptionTree)
    (hcomp : Ix.Cert.compileReport env = .ok (ixe, failures))
    (hadmit : Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok t) :
    SelfHashed ⟨{ ixe with roleBinding := some ⟨binding.address, binding.bytes⟩ }, trees⟩ := by
  have hauth := Ix.Cert.compileAuthentic env ixe (Ix.Cert.compile_eq_ok.mpr ⟨failures, hcomp⟩)
  have hbind : Address.blake3Pure binding.bytes = binding.address := by
    have ha := ((Ix.Kernel.Admission.admitBinding_ok_iff Address.admissionHash binding t).mp hadmit).authentic
    simpa [Address.admissionHash_eq] using ha
  refine ⟨fun a lc hlc => (hauth.1 a lc hlc).symm,
    fun a bytes hbl => (hauth.2 a bytes hbl).symm,
    fun rb hrb => ?_⟩
  cases hrb
  exact hbind

/-- **`ReadsIn` agrees across any two compatible `(store, blob)` pairs** under
an admitted role table: if `store₁` and `store₂` agree on overlapping addresses
and `blob₁` and `blob₂` agree on overlapping addresses, then any two readings
of an address `a` agree up to `SameReading` (`ReadsIn.mono` + `ReadsIn.functional`). -/
theorem readsIn_agree_of_compat {t : Ix.Kernel.RoleTable}
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    {store₁ store₂ : Ix.Kernel.Reader.Store} {blob₁ blob₂ : Address → Option ByteArray}
    (hs : ∀ x c₁ c₂, store₁ x = some c₁ → store₂ x = some c₂ → c₁ = c₂)
    (hb : ∀ x b₁ b₂, blob₁ x = some b₁ → blob₂ x = some b₂ → b₁ = b₂)
    {a : Address} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : ReadsIn t store₁ blob₁ a ci₁) (h₂ : ReadsIn t store₂ blob₂ a ci₂) :
    SameReading ci₁ ci₂ := by
  let mergedStore : Ix.Kernel.Reader.Store := fun x => (store₁ x).orElse fun _ => store₂ x
  let mergedBlob : Address → Option ByteArray := fun x => (blob₁ x).orElse fun _ => blob₂ x
  have hs₁ : ∀ x c, store₁ x = some c → mergedStore x = some c := by
    intro x c hx; simp [mergedStore, hx]
  have hs₂ : ∀ x c, store₂ x = some c → mergedStore x = some c := by
    intro x c hx
    cases h1 : store₁ x with
    | none => simp [mergedStore, h1, hx]
    | some c₁ =>
      have heq := hs x c₁ c h1 hx
      simp [mergedStore, h1, heq]
  have hb₁ : ∀ x b, blob₁ x = some b → mergedBlob x = some b := by
    intro x b hx; simp [mergedBlob, hx]
  have hb₂ : ∀ x b, blob₂ x = some b → mergedBlob x = some b := by
    intro x b hx
    cases h1 : blob₁ x with
    | none => simp [mergedBlob, h1, hx]
    | some b₁ =>
      have heq := hb x b₁ b h1 hx
      simp [mergedBlob, h1, heq]
  exact ReadsIn.functional hroles (ReadsIn.mono hs₁ hb₁ h₁) (ReadsIn.mono hs₂ hb₂ h₂)

/-- **Collision-free agreement with a `SelfHashed` view**: when the combined
runs `callsA ++ callsB` exhibit no `GenuineCollision` against `V` (whose
`roleBinding` is `binding` at `a`, admitting as `t`):
1. the binding run's hashed table bytes `tb` equal `binding.bytes`, and its
   admitted table `t'` equals `t`;
2. `storeOver E₀ R` agrees with `recordOf V.env` on every overlapping address,
   and `blobOver E₀ R` agrees with `V.env.blobs.get?` on every overlapping address;
3. any `ReadsIn` witness over `(storeOver E₀ R, blobOver E₀ R)` agrees up to
   `SameReading` with any `Reads` witness over `V.env`. -/
theorem noCollision_agrees_with_view {V : View} {extra : List ByteArray}
    {callsA callsB : List (Call IxVM.F)} {E₀ R : Ixon.Env}
    {tb : ByteArray} {a : Address} {binding : Ix.Kernel.Admission.Binding}
    {t t' : Ix.Kernel.RoleTable}
    (hV : SelfHashed V)
    (hNoCol : ¬ GenuineCollision V extra (callsA ++ callsB))
    (hLoadA : LoadedBy callsA E₀) (hLoadB : LoadedBy callsB R)
    (hHashedTb : Hashed callsB tb)
    (hAdmitTb : Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t')
    (hViewBind : V.env.roleBinding = some ⟨binding.address, binding.bytes⟩)
    (hBindAddr : binding.address = a)
    (hAdmitBind : Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok t) :
    tb = binding.bytes ∧ t' = t ∧
      (∀ x c₁ c₂, storeOver E₀ R x = some c₁ → recordOf V.env x = some c₂ → c₁ = c₂) ∧
      (∀ x b₁ b₂, blobOver E₀ R x = some b₁ → V.env.blobs.get? x = some b₂ → b₁ = b₂) ∧
      (∀ x ci₁ ci₂, ReadsIn t (storeOver E₀ R) (blobOver E₀ R) x ci₁ → Reads t V.env x ci₂ →
        SameReading ci₁ ci₂) := by
  have hcA : ∀ c ∈ callsA, c ∈ callsA ++ callsB := fun c h => List.mem_append.mpr (Or.inl h)
  have hcB : ∀ c ∈ callsB, c ∈ callsA ++ callsB := fun c h => List.mem_append.mpr (Or.inr h)
  have hBytesEq : ∀ {held bytes : ByteArray},
      V.Preimage (Address.blake3Pure held) held →
      Hashed (callsA ++ callsB) bytes →
      Address.blake3Pure bytes = Address.blake3Pure held →
      bytes = held := by
    intro held bytes hpre hh heq
    exact Classical.byContradiction fun hne =>
      hNoCol (Or.inl ⟨held, bytes, Or.inl hpre, hh, hne, heq⟩)
  -- 1. Role binding bytes and table identity
  have hHashBind : Address.blake3Pure binding.bytes = a :=
    (hV.2.2 ⟨binding.address, binding.bytes⟩ hViewBind).trans hBindAddr
  have hHashTb : Address.blake3Pure tb = a := by
    have ha := ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ _).mp hAdmitTb).authentic
    simpa [Address.admissionHash_eq] using ha
  have hPreBind : V.Preimage (Address.blake3Pure binding.bytes) binding.bytes :=
    Or.inr (Or.inr (Or.inl ⟨⟨binding.address, binding.bytes⟩, hViewBind,
      (hV.2.2 ⟨binding.address, binding.bytes⟩ hViewBind).symm, rfl⟩))
  have hTbEq : tb = binding.bytes :=
    hBytesEq hPreBind (hashed_mono hcB hHashedTb) (hHashTb.trans hHashBind.symm)
  have hTableEq : t' = t := by
    have hbStruct : ({ address := a, bytes := tb } : Ix.Kernel.Admission.Binding) = binding := by
      cases binding with
      | mk addr bs =>
        simp only at hBindAddr hTbEq
        subst hBindAddr; subst hTbEq; rfl
    rw [hbStruct] at hAdmitTb
    rw [hAdmitBind] at hAdmitTb
    exact (Except.ok.inj hAdmitTb).symm
  -- 2. Record agreement for any environment loaded by `calls`
  have hRecAgree : ∀ {E : Ixon.Env}, LoadedBy (callsA ++ callsB) E →
      ∀ x c₁ c₂, recordOf E x = some c₁ → recordOf V.env x = some c₂ → c₁ = c₂ := by
    intro E hLoad x c₁ c₂ h1 h2
    unfold recordOf at h1 h2
    cases hE : E.consts.get? x with
    | none => rw [hE] at h1; cases h1
    | some lc₁ =>
      cases hVe : V.env.consts.get? x with
      | none => rw [hVe] at h2; cases h2
      | some lc₂ =>
        simp only [hE, Option.bind_some] at h1
        simp only [hVe, Option.bind_some] at h2
        have hHash1 := hLoad.1 x lc₁ hE
        have hHash2 := hV.1 x lc₂ hVe
        have hPre : V.Preimage (Address.blake3Pure lc₂.rawBytes) lc₂.rawBytes :=
          Or.inl ⟨lc₂, hHash2.symm ▸ hVe, rfl⟩
        have hRawEq : lc₁.rawBytes = lc₂.rawBytes :=
          hBytesEq hPre hHash1.1 (hHash1.2.trans hHash2.symm)
        rw [hRawEq] at h1
        exact Option.some.inj (h1.symm.trans h2)
  have hBlobAgreeEnv : ∀ {E : Ixon.Env}, LoadedBy (callsA ++ callsB) E →
      ∀ x b₁ b₂, E.blobs.get? x = some b₁ → V.env.blobs.get? x = some b₂ → b₁ = b₂ := by
    intro E hLoad x b₁ b₂ h1 h2
    have hHash1 := hLoad.2 x b₁ h1
    have hHash2 := hV.2.1 x b₂ h2
    have hPre : V.Preimage (Address.blake3Pure b₂) b₂ :=
      Or.inr (Or.inl (hHash2.symm ▸ h2))
    exact hBytesEq hPre hHash1.1 (hHash1.2.trans hHash2.symm)
  have hLoadA' : LoadedBy (callsA ++ callsB) E₀ :=
    ⟨fun a lc h => ⟨hashed_mono hcA (hLoadA.1 a lc h).1, (hLoadA.1 a lc h).2⟩,
     fun a b h => ⟨hashed_mono hcA (hLoadA.2 a b h).1, (hLoadA.2 a b h).2⟩⟩
  have hLoadB' : LoadedBy (callsA ++ callsB) R :=
    ⟨fun a lc h => ⟨hashed_mono hcB (hLoadB.1 a lc h).1, (hLoadB.1 a lc h).2⟩,
     fun a b h => ⟨hashed_mono hcB (hLoadB.2 a b h).1, (hLoadB.2 a b h).2⟩⟩
  have hStoreAgree : ∀ x c₁ c₂, storeOver E₀ R x = some c₁ → recordOf V.env x = some c₂ → c₁ = c₂ := by
    intro x c₁ c₂ h1 h2
    unfold storeOver at h1
    cases hE : recordOf E₀ x with
    | some c =>
      simp only [hE, Option.orElse_some, Option.some.injEq] at h1
      subst h1
      exact hRecAgree hLoadA' x c c₂ hE h2
    | none =>
      simp only [hE, Option.orElse_none] at h1
      exact hRecAgree hLoadB' x c₁ c₂ h1 h2
  have hBlobAgree : ∀ x b₁ b₂, blobOver E₀ R x = some b₁ → V.env.blobs.get? x = some b₂ → b₁ = b₂ := by
    intro x b₁ b₂ h1 h2
    unfold blobOver at h1
    cases hE : E₀.blobs.get? x with
    | some b =>
      simp only [hE, Option.orElse_some, Option.some.injEq] at h1
      subst h1
      exact hBlobAgreeEnv hLoadA' x b b₂ hE h2
    | none =>
      simp only [hE, Option.orElse_none] at h1
      exact hBlobAgreeEnv hLoadB' x b₁ b₂ h1 h2
  refine ⟨hTbEq, hTableEq, hStoreAgree, hBlobAgree, fun x ci₁ ci₂ hr₁ hr₂ => ?_⟩
  exact readsIn_agree_of_compat (roles_nodup_of_admitBinding hAdmitBind) hStoreAgree hBlobAgree hr₁ hr₂

/-- **End-to-end `compileCorrect` ↔ `CircuitComposed` composition bridge**:
given a Lean closure `sub` of `roots` in `env` compiled by `Ix.Cert.compileReport`
satisfying the `CompileCorrect` hypotheses (producing `Published ixe sub` and
`IxonCommutesCovering ixe sub t envQ` for `defaultBinding = .ok binding` and
`defaultTable = .ok t`), and given two accepted IxVM circuit proofs (one for
`binding` at `binding.address` and one for an in-scope typing claim `cA` whose
context binds `binding.address`, over the compiled artifact's view
`V = ⟨{ ixe with roleBinding := some binding }, trees⟩`):

Either the combined IxVM runs exhibited a `GenuineCollision` against `V`, the
claim bytes, and the committed images; **or**:
1. `Published ixe sub` and `IxonCommutesCovering ixe sub t envQ` hold from
   `Ix.Cert.ReaderStreamsTrace.compileCorrect`;
2. the IxVM binding run hashed the exact default binding bytes `binding.bytes`
   and admitted the exact same role table `t` (`defaultTable`), with a valid
   `TableShape` on all 77 groups;
3. `ConsistentReadOver callsA t R envT seeds` holds (so under any `SetTheory W`,
   `claimedEnv env` is consistent and `SeedsNotFalse` holds);
4. every `ReadsIn` witness over `(storeOver E₀ R, blobOver E₀ R)` agrees up to
   `SameReading` with `Reads t ixe` whenever `ixe` holds that record and its
   supporting block/blobs. -/
theorem compileCorrect_circuitComposed_bridge
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Ix.Cert.Failures} {t : Ix.Kernel.RoleTable}
    {envQ : Ix.Kernel.Env .source} {binding : Ix.Kernel.Admission.Binding}
    (htable : Ix.Kernel.Reader.defaultTable = .ok t)
    (hbind : Ix.Kernel.Admission.defaultBinding = .ok binding)
    (hsource : Ix.Cert.SourceAcceptsQ Ix.Cert.blocksOf env roots sub ixe t envQ)
    (hcomp : Ix.Cert.compileReport env = .ok (ixe, failures))
    (hnofail : Ix.Cert.NoFailure failures sub)
    (hpubRoles : Ix.Cert.PublishedRolesBound t ixe)
    (hpubAgree : Ix.Cert.PublishedAgree ixe)
    (hevAgrees : Ix.Cert.EvidenceCheck.EvidenceAgrees t ixe)
    (hroleEv : Ix.Cert.RoleClosure.RoleEvidenceChecks) :
    CircuitSound fun callsB dB =>
      CircuitSound fun callsA dA =>
        ∀ (bytesB : ByteArray) (spec : Address),
          Claim.de bytesB = .ok (.binding spec binding.address) →
          packDigest (Address.blake3Pure bytesB) = dB →
          ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
            packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
            ∀ ctx, cA.context? = some ctx → ctx.binding = binding.address →
              ∀ (trees : List Ix.AssumptionTree) (seeds : List Address),
                let V : View := ⟨{ ixe with roleBinding := some ⟨binding.address, binding.bytes⟩ }, trees⟩
                ClaimSeeds cA V seeds →
                  GenuineCollision V (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
                    (Ix.Cert.Published ixe sub ∧
                      Ix.Cert.IxonCommutesCovering.{u} ixe sub t envQ ∧
                      ∃ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon),
                        Hashed callsB binding.bytes ∧
                        Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok t ∧
                        AllBound t ∧ LoadedBy callsB R ∧
                        TableShape.{u} t (fun _ => True) R envT ∧
                        ConsistentReadOver.{u} callsA t R envT seeds ∧
                        (∀ E₀, LoadedBy callsA E₀ →
                          ∀ x ci₁ ci₂,
                            ReadsIn t (storeOver E₀ R) (blobOver E₀ R) x ci₁ →
                            Reads t ixe x ci₂ → SameReading ci₁ ci₂)) := by
  obtain ⟨hPub, hComm⟩ := Ix.Cert.ReaderStreamsTrace.compileCorrect.{u}
    env roots sub ixe failures t envQ htable hsource hcomp hnofail
    hpubRoles hpubAgree hevAgrees hroleEv
  have hAdmitBind : Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok t := by
    obtain ⟨b', hb', _, _, _, _, hacc, -⟩ := hComm
    rw [hbind] at hb'
    obtain rfl := Except.ok.inj hb'
    obtain ⟨-, tA, _, _, _, hadm, -⟩ := hacc
    have hteq : tA = t := Ix.Cert.ReadingKeys.admitBinding_default htable hbind hadm
    rwa [hteq] at hadm
  refine @circuitSound_mono _ _ (fun callsB dB hA => ?_) (@circuitComposed_selfHashed.{u})
  refine @circuitSound_mono _ _ (fun callsA dA hSpec => ?_) hA
  intro bytesB spec deB dgB bytesA cA deA dgA hsc ctx hctx hba trees seeds V hseeds
  have hV : SelfHashed V := selfHashed_of_compileReport trees hcomp hAdmitBind
  by_cases hCol : GenuineCollision V (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB)
  · exact Or.inl hCol
  · rcases hSpec bytesB spec binding.address deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds
        hseeds hV with hCol' | ⟨tb, t', R, envT, htb, hadm', hall, hloadB, hshape, hcons⟩
    · exact Or.inl hCol'
    · right
      obtain ⟨E₀_wit, _, hLoadA_wit, -⟩ := hcons
      obtain ⟨htbEq, htEq, -, -, -⟩ :=
        noCollision_agrees_with_view hV hCol hLoadA_wit hloadB htb hadm' rfl rfl hAdmitBind
      subst htbEq
      subst htEq
      refine ⟨hPub, hComm, R, envT, htb, hAdmitBind, hall, hloadB, hshape, hcons,
        fun E₀ hLoadA x ci₁ ci₂ hr₁ hr₂ => ?_⟩
      obtain ⟨-, -, -, -, hAgree⟩ :=
        noCollision_agrees_with_view hV hCol hLoadA hloadB htb hadm' rfl rfl hAdmitBind
      exact hAgree x ci₁ ci₂ hr₁ hr₂

end IxVM.Refinement.Endpoint

/-! ## 4. Kernel axiom guards on all exported theorems -/

#guard_module_axioms IxC.Kernel.SetTheory.FiniteChain

#guard_kernel_axioms Ix.Kernel.VSet.isTGUniverse_univSet [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.VSet.isTGUniverse_lift [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.VSet.finiteSetTheory0 [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.VSet.finiteSetTheory1 [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.VSet.finiteSetTheory2 [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.VSet.finiteSetTheory3 [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.VSet.finiteSetTheory4 [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.VSet.omegaUniverses_implies_setTheory [propext, Classical.choice, Quot.sound]

#guard_kernel_axioms IxVM.Refinement.Endpoint.seedsInhabitedIn_of [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitComposed_selfHashed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitComposed_no_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitComposed_seeds_inhabited [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitComposed_no_False_VSet [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.circuitComposed_seeds_inhabited_VSet [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.emptyEnv_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.no_model_of_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.no_model_of_alias_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.badEnvFalse_no_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.badEnvAliasFalse_no_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.consistentReadOver_no_alias_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.selfHashed_of_compileReport [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.readsIn_agree_of_compat [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.noCollision_agrees_with_view [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Endpoint.compileCorrect_circuitComposed_bridge [propext, Classical.choice, Quot.sound]
