import IxVMRefinement.Core.Good

/-! # The seams instance `S₀`: its components

The components of the one seams instance every layer states its results against
(`IxVM.Consistency.Seams`, `Ix/IxVM/Consistency/Statement.lean`):

* `S0.term E env g d k h v t` = `Tm g.κ d g.Γ h k t v` (`Rep.lean`);
* `S0.ctx E env g d h rc types`: `rc` reads a table `t` whose keying is `g.κ`, `types` is a
  segment of `g.Γ` ending at `d`, and the environment invariant (`EnvFacts`) and the loads
  (`LoadFacts`) hold of `⟨E, env, t⟩` (`Ctx.lean`, `Good.lean`);
* `S0.addr h v a`: `v` is a `Bytes::AddressRef` holding `a`;
* `S0.loaded`, `S0.Walked`, `S0.Checked`: first definitions (below).

**The ghost state.** A term's image depends on two things the current `Seams.term` and
`Seams.ctx` signatures do not carry: the keying of addresses (the table the run read) and the
types of the opened variables (the kernel's `fvar` carries its type; IxVM's `types` list holds
them). Both relations must agree on them, so they share a ghost argument `g : Ghost`, which
`Terms` and `Core` quantify over. Without it `Core`'s inference conjunct is unprovable for a
bound variable (its inferred type is the `fvar`'s annotation, which nothing would tie to
`types`). The statement change that adds the argument is proposed separately; every component
here is already stated with it. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

/-- **The ghost state the term and context seams share**: the keying of addresses and the types
of the opened variables. -/
structure Ghost where
  κ : _root_.Address → KKey
  Γ : Nat → KExpr

namespace S0

/-- (L3, L4) **The term seam.** -/
def term (_E : Ixon.Env) (_env : Ix.Kernel.Env .anon) (g : Ghost) (d k : Nat) (h : Heap F)
    (v : SourceValue F) (t : KExpr) : Prop :=
  Tm g.κ d g.Γ h k t v

/-- (L4) **The context seam**: the role context reads a table whose keying is the ghost's, the
context list is a segment of the ghost context, and the environment invariant and the loads
hold. -/
def ctx (E : Ixon.Env) (env : Ix.Kernel.Env .anon) (g : Ghost) (d : Nat) (h : Heap F)
    (rc types : SourceValue F) : Prop :=
  ∃ t : Ix.Kernel.RoleTable, g.κ = keyOf t ∧ RCRep t h rc ∧ TypesRep g.κ g.Γ h d types ∧
    EnvFacts ⟨E, env, t⟩ ∧ LoadFacts ⟨E, env, t⟩

/-- (L1, L6) **The address seam**: `v` is a `Bytes::AddressRef` holding `a`. -/
def addr (h : Heap F) (v : SourceValue F) (a : _root_.Address) : Prop :=
  ∃ a' : Bytes.Address, Bytes.RepAddressRef addrTy h a' v ∧ ixAddr a' = a

/-- (L1 → L4, L5) **The loaded-constant seam, first definition**: `ptr` points to a converted
constant of a record that `bytes` decode to (`Ixon.deConstant`), which represents (`CIRep`,
under `E₀`'s role table's keying) a constant the kernel's reading of the record stores.

*Provisional.* What "the reading stores" is (the reader's reading of the one record in the
records `E₀`, up to binder data) is fixed with the record-conversion and assembly packages;
nothing in the core reads `loaded` (the core reads `LoadFacts`). -/
def loaded (E₀ : Ixon.Env) (h : Heap F) (ptr : SourceValue F) (bytes : ByteArray) : Prop :=
  ∃ (c : Ixon.Constant) (t : Ix.Kernel.RoleTable) (ci : Ix.Kernel.ConstantInfo .anon),
    Ixon.deConstant bytes = .ok c ∧
    (∀ rb, E₀.roleBinding = some rb → Ix.Kernel.RoleTable.ofBytes rb.bytes = some t) ∧
    CIPtrRep (keyOf t) h ptr ci

/-- **The derivation contains an accepting check of the constant at `a`** under a role context
reading `t`: a call of `KernelCheck::check_const(rc, ci, addr)` on a loaded constant `ci` at the
address `a`. -/
def CheckedAt (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (a : _root_.Address) : Prop :=
  ∃ cl ∈ calls, cl.name = "KernelCheck::check_const" ∧
    ∃ rc v ap, cl.args = [rc, v, ap] ∧ RCRep t cl.heap rc ∧ addr cl.heap ap a

/-- (L6 → L7) **The walked closure, first definition**: a set `C` of addresses holding the seeds
and the table's bound constants, closed under references (a record's `refs`, a projection's
block), every one of whose records is stored in `E₀`, in Lean's logic, and checked by the
derivation (a block through each of its members' projection records, which the derivation
checks under their own addresses). -/
def Walked (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (seeds : List _root_.Address) : Prop :=
  ∃ C : _root_.Address → Prop,
    (∀ a ∈ seeds, C a) ∧
    (∀ r a, t.addressOf? r = some a → C a) ∧
    ∀ a, C a → ∃ c, Ix.Cert.recordAt E₀ a = some c ∧ IxVM.Consistency.InLogic c ∧
      (∀ r ∈ c.refs.toList, C r) ∧ C (Ix.Cert.ownerOf a c) ∧
      ((∃ ms, c.info = .muts ms) ∨ CheckedAt calls t a)

/-- (L7 → L5) **The derivation checked every constant a declaration installs, first
definition**: for records `E` and a table `t` whose environment facts and loads hold of `env`
and whose calls hashed no collision with `E`, every constant the declaration `d` installs is
stored as declared (`StoredAs`) by the image of a constant the derivation checked
(`KernelCheck::check_const` on a loaded constant representing it), at that constant's key. -/
def Checked (calls : List (Call F)) (env : Ix.Kernel.Env .anon)
    (d : Ix.Kernel.Declaration .anon) : Prop :=
  ∃ (E : Ixon.Env) (t : Ix.Kernel.RoleTable),
    EnvFacts ⟨E, env, t⟩ ∧ LoadFacts ⟨E, env, t⟩ ∧ Good ⟨E, env, t⟩ calls ∧
    ∀ ci₀ ∈ IxVM.Consistency.installs d,
      ∃ cl ∈ calls, cl.name = "KernelCheck::check_const" ∧
        ∃ rc v ap a ci, cl.args = [rc, v, ap] ∧ RCRep t cl.heap rc ∧ addr cl.heap ap a ∧
          keyOf t a = ci₀.name ∧ CIRep (keyOf t) cl.heap v ci ∧ IxVM.Consistency.StoredAs ci ci₀

/-! ## Heap monotonicity -/

theorem term_mono {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {g : Ghost} {d k : Nat}
    {h₁ h₂ : Heap F} {v : SourceValue F} {t : KExpr} (ext : Heap.Extends h₁ h₂)
    (r : term E env g d k h₁ v t) : term E env g d k h₂ v t :=
  Tm.mono ext r

theorem ctx_mono {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {g : Ghost} {d : Nat}
    {h₁ h₂ : Heap F} {rc types : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (r : ctx E env g d h₁ rc types) : ctx E env g d h₂ rc types :=
  let ⟨t, hκ, hrc, hty, hf, hl⟩ := r
  ⟨t, hκ, hrc.mono ext, hty.mono ext, hf, hl⟩

theorem addr_mono {h₁ h₂ : Heap F} {v : SourceValue F} {a : _root_.Address}
    (ext : Heap.Extends h₁ h₂) (r : addr h₁ v a) : addr h₂ v a :=
  let ⟨a', ha, he⟩ := r
  ⟨a', Bytes.repAddressRef_heapMono₂ addrTy ext ha, he⟩

theorem loaded_mono {E₀ : Ixon.Env} {h₁ h₂ : Heap F} {ptr : SourceValue F} {bytes : ByteArray}
    (ext : Heap.Extends h₁ h₂) (r : loaded E₀ h₁ ptr bytes) : loaded E₀ h₂ ptr bytes :=
  let ⟨c, t, ci, hd, ht, hr⟩ := r
  ⟨c, t, ci, hd, ht, hr.mono ext⟩

end S0

end IxVM.Refinement.Core
