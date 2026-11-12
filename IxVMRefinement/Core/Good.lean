import IxVMRefinement.Core.Ctx
import Ix.IxVM.Consistency.Statement

/-! # Good calls, the collision escape, and the loads

`Good c calls`: the calls hashed no collision with the records `c.E` (the escape of the
statement's `Core`, `View.HashedCollision { env := c.E } [] calls`), and they are **bounded**:
at most `2^39` distinct calls of each memoized callee in a valid ROM (the statement's `Bounded`,
which L0 provides). Every registry spec is conditional on `Good` of its own calls, and `Good`
passes to sub-derivations (`Good.sub`): a callee's calls are among its caller's.

`LoadFacts c`: the record loads the core makes read the environment: a load at an address the
table keys as `k` returns a constant representing `env`'s constant at `k`. This is the
L1 ↔ L7 interface: L1 (`Records`) says what a load returns in terms of the bytes it hashed;
L7 (with L5) says the environment stores, at each record's key, the constant those bytes read
as. The registry specs of `Ingress::get_ci`, `get_ci_cprj` and `get_ci_iprj` are discharged from
it. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

/-- **The calls are good**: no hashed collision with the records `c.E`, and bounded. -/
def Good (c : Ctx) (calls : List (Call F)) : Prop :=
  ¬ View.HashedCollision { env := c.E } [] calls ∧ IxVM.Consistency.Bounded calls

theorem hashed_mono {calls₁ calls₂ : List (Call F)} (hsub : ∀ x ∈ calls₁, x ∈ calls₂)
    {b : ByteArray} (h : Hashed calls₁ b) : Hashed calls₂ b := by
  obtain ⟨cl, hm, rest⟩ := h
  exact ⟨cl, hsub cl hm, rest⟩

theorem collision_mono {V : View} {calls₁ calls₂ : List (Call F)}
    (hsub : ∀ x ∈ calls₁, x ∈ calls₂) (h : V.HashedCollision [] calls₁) :
    V.HashedCollision [] calls₂ := by
  rcases h with ⟨x, held, bytes, hpre, hh, hne, hx⟩ | ⟨bytes, hpre, hx⟩
  · refine .inl ⟨x, held, bytes, ?_, hashed_mono hsub hh, hne, hx⟩
    rcases hpre with hp | hp | ⟨hh', hx'⟩
    · exact .inl hp
    · exact .inr (.inl hp)
    · exact .inr (.inr ⟨hashed_mono hsub hh', hx'⟩)
  · refine .inr ⟨bytes, ?_, hx⟩
    rcases hpre with hp | hp
    · exact .inl hp
    · exact .inr (hashed_mono hsub hp)

theorem bounded_sub {calls₁ calls₂ : List (Call F)} (hsub : ∀ x ∈ calls₁, x ∈ calls₂)
    (b : IxVM.Consistency.Bounded calls₂) : IxVM.Consistency.Bounded calls₁ :=
  let ⟨rom, hv, bound⟩ := b
  ⟨rom, hv, fun name hm =>
    let ⟨keys, hk, cover⟩ := bound name hm
    ⟨keys, hk, fun cl hcl => cover cl (hsub cl hcl)⟩⟩

/-- **Good passes to sub-derivations.** -/
theorem Good.sub {c : Ctx} {calls₁ calls₂ : List (Call F)} (g : Good c calls₂)
    (hsub : ∀ x ∈ calls₁, x ∈ calls₂) : Good c calls₁ :=
  ⟨fun h => g.1 (collision_mono hsub h), bounded_sub hsub g.2⟩

/-- **The record-load escape**: with no hashed collision, every byte string the run hashed to a
stored address is the records' data at that address. -/
theorem load_escape {E : Ixon.Env} {calls : List (Call F)} {x : _root_.Address}
    {lc : Ixon.LazyConstant} (hst : E.consts.get? x = some lc)
    (nc : ¬ View.HashedCollision { env := E } [] calls) :
    ∀ bytes, Hashed calls bytes → Address.blake3Pure bytes = x → bytes = lc.rawBytes := by
  intro bytes hh hx
  by_cases heq : bytes = lc.rawBytes
  · exact heq
  · exact absurd (.inl ⟨x, lc.rawBytes, bytes, .inl (.inl ⟨lc, hst, rfl⟩), hh, heq, hx⟩) nc

/-! ## The loads -/

/-- **The loads read the environment** (module docstring): every good derivation of
`Ingress::get_ci` at an address `a` returns a constant representing `env`'s constant at
`κ a`; and so do the projection loaders the core calls directly, `get_ci_cprj(block, i, j)` and
`get_ci_iprj(block, i)`, at the key of the projection record they stand for. -/
structure LoadFacts (c : Ctx) : Prop where
  getCI : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a addr →
      ∃ ci, c.env.find? (c.κ (ixAddr a)) = some ci ∧ CIPtrRep c.κ h' ptr ci
  getCprj : ∀ (bp ptr : SourceValue F) (i j : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h b bp →
      ∃ ci, c.env.find? (c.κ (cprjAddr (ixAddr b) i.val j.val)) = some ci ∧
        CIPtrRep c.κ h' ptr ci
  getIprj : ∀ (bp ptr : SourceValue F) (i : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h b bp →
      ∃ ci, c.env.find? (c.κ (iprjAddr (ixAddr b) i.val)) = some ci ∧ CIPtrRep c.κ h' ptr ci

/-! ## Specs -/

/-- **A spec**: a predicate on an observed derivation of a function (its arguments, the heap
before, the result, the heap after, its calls), relative to a context. Every function of the
registry has one (`Registry.lean`). -/
abbrev SpecFn : Type :=
  Ctx → List (SourceValue F) → Heap F → SourceValue F → Heap F → List (Call F) → Prop

/-- **The facts a step lemma may use about its context**: the environment invariant and the
loads. `S0.ctx` gives both. -/
structure CoreFacts (c : Ctx) : Prop where
  env : EnvFacts c
  loads : LoadFacts c

end IxVM.Refinement.Core
