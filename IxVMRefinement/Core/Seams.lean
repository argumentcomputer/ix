import IxVMRefinement.Core.Good

/-! # The seams instance `S₀`: its components

The components of the one seams instance every layer states its results against
(`IxVM.Consistency.Seams`, `Ix/IxVM/Consistency/Statement.lean`):

* `S0.term E env g d k h v t` = `Tm g.κ d g.Γ h k t v` (`Rep.lean`);
* `S0.ctx E env g d h rc types`: `rc` reads a table `t` whose keying is `g.κ`, `types` is a
  segment of `g.Γ` ending at `d`, and the environment invariant (`EnvFacts`) and the loads
  (`LoadFacts`) hold of `⟨E, env, t, lim⟩` (`Ctx.lean`, `Good.lean`);
* `S0.addr h v a`: `v` is a `Bytes::AddressRef` holding `a`;
* `S0.loaded`, `S0.Walked`, `S0.Checked`: first definitions (below).

**The ghost state.** A term's image depends on two things beyond the environment: the keying of
addresses (the table the run read) and the types of the opened variables (the kernel's `fvar`
carries its type; IxVM's `types` list holds them). The term and context relations agree on them
through the seams' shared ghost argument (`Seams.Ghost`), here `Ghost`, which `Terms` and `Core`
quantify over. `S₀` is the instance; `consistent_S₀` is `IxVM.consistent` at it. -/

universe u

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

/-- (L4) **The context seam**: the role context reads a table whose keying is the ghost's, at a
group limit, the context list is a segment of the ghost context, and the environment invariant
(for the roles in force under that limit) and the loads hold. -/
def ctx (E : Ixon.Env) (env : Ix.Kernel.Env .anon) (g : Ghost) (d : Nat) (h : Heap F)
    (rc types : SourceValue F) : Prop :=
  ∃ (t : Ix.Kernel.RoleTable) (lim : Option Nat), g.κ = keyOf t ∧ RCRep t lim h rc ∧
    TypesRep g.κ g.Γ h d types ∧ GhostScoped g.Γ d ∧ EnvFacts ⟨E, env, t, lim⟩ ∧
    LoadFacts ⟨E, env, t, lim⟩

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
    ∃ rc v ap lim, cl.args = [rc, v, ap] ∧ RCRep t lim cl.heap rc ∧ addr cl.heap ap a

/-- The reference-table indices an expression names as constants (`KernelClaim::const_idxs_expr`):
those of `ref` and `prj` nodes; literal indices name blobs and `share` nodes are read through the
sharing table. -/
def exprRefIdxs : Ixon.Expr → List Nat
  | .ref i _ => [i.toNat]
  | .prj i _ e => i.toNat :: exprRefIdxs e
  | .app f a => exprRefIdxs f ++ exprRefIdxs a
  | .lam t b => exprRefIdxs t ++ exprRefIdxs b
  | .all t b => exprRefIdxs t ++ exprRefIdxs b
  | .letE _ _ t v b => exprRefIdxs t ++ exprRefIdxs v ++ exprRefIdxs b
  | _ => []

/-- The reference-table indices a block member names (`KernelClaim::const_idxs_muts`). -/
def mutRefIdxs : Ixon.MutConst → List Nat
  | .defn d => exprRefIdxs d.typ ++ exprRefIdxs d.value
  | .indc i => exprRefIdxs i.typ ++ (i.ctors.toList.flatMap fun c => exprRefIdxs c.typ)
  | .recr r => exprRefIdxs r.typ ++ (r.rules.toList.flatMap fun rl => exprRefIdxs rl.rhs)

/-- **The reference-table indices a record uses** (`KernelClaim::const_idxs_of`): those of its
sharing table and of the expressions of its payload. -/
def usedRefIdxs (c : Ixon.Constant) : List Nat :=
  (c.sharing.toList.flatMap exprRefIdxs) ++
    match c.info with
    | .defn d => exprRefIdxs d.typ ++ exprRefIdxs d.value
    | .recr r => exprRefIdxs r.typ ++ (r.rules.toList.flatMap fun rl => exprRefIdxs rl.rhs)
    | .axio a => exprRefIdxs a.typ
    | .quot q => exprRefIdxs q.typ
    | .muts ms => ms.toList.flatMap mutRefIdxs
    | _ => []

/-- **An edge of the claim walk** (`KernelClaim::run_check_transitive`, `env_walk`): from a
projection record to its block, and from a record to a reference its expressions use. A
reference listed in the table and used nowhere is not followed (the reader never resolves it
either). -/
def WalkEdge (E₀ : Ixon.Env) (a b : _root_.Address) : Prop :=
  ∃ c, Ix.Cert.recordAt E₀ a = some c ∧
    ((Ix.Cert.ownerOf a c = b ∧ b ≠ a) ∨ ∃ i ∈ usedRefIdxs c, c.refs[i]? = some b)

/-- (L6 → L7) **The walked closure**: a set of addresses holding the seeds and the theorems the
table's evidence names, closed under the claim walk's edges and the reading's ground edges
(`Ix.Cert.GroundEdgeAt`: a `Nat` operation's ground roles, the literal-support roles), each
stored in `E₀`, in Lean's logic, and checked by the derivation (a block through its members'
projection records). The assembly reads the records of such a set (with the recursors it
draws): every reference a record of it uses lands in it, and a reference it lists without
using is never resolved. -/
def Walked (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (seeds : List _root_.Address) : Prop :=
  ∃ Wk : _root_.Address → Prop,
    (∀ a, (a ∈ seeds ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList) → Wk a) ∧
    (∀ a b, Wk a → (WalkEdge E₀ a b ∨ Ix.Cert.GroundEdgeAt t E₀ a b) → Wk b) ∧
    ∀ a, Wk a → ∃ c, Ix.Cert.recordAt E₀ a = some c ∧ IxVM.Consistency.InLogic c ∧
      ((∃ ms, c.info = .muts ms) ∨ CheckedAt calls t a)


/-- (L7 → L5) **The derivation checked every constant a declaration installs, first
definition**: for records `E` and a well-formed table `t` (the run's) whose loads read `env`
(`LoadFacts`) and whose calls are good, every constant the declaration `d` installs is stored as
declared (`StoredAs`) by the image of a constant the derivation checked
(`KernelCheck::check_const` on a loaded constant representing it), at that constant's key.

It carries what the assembly knows (the records, the table, the loads, the checks). The rest of
the environment invariant the core reads (`EnvFacts`: stored theorems typed, the role and
recursor facts) holds of the prefix by the declarations already checked, so it is the
declaration layer's to carry in its invariant (`Decls`) and to supply to `Core` at each step. -/
def Checked (calls : List (Call F)) (env : Ix.Kernel.Env .anon)
    (d : Ix.Kernel.Declaration .anon) : Prop :=
  ∃ (E : Ixon.Env) (t : Ix.Kernel.RoleTable),
    t.wf = true ∧ LoadFacts ⟨E, env, t, none⟩ ∧ Good ⟨E, env, t, none⟩ calls ∧
    ∀ ci₀ ∈ IxVM.Consistency.installs d,
      ∃ cl ∈ calls, cl.name = "KernelCheck::check_const" ∧
        ∃ rc v ap lim a ci, cl.args = [rc, v, ap] ∧ RCRep t lim cl.heap rc ∧ addr cl.heap ap a ∧
          keyOf t a = ci₀.name ∧ CIRep (keyOf t) cl.heap v ci ∧ IxVM.Consistency.StoredAs ci ci₀

/-! ## Heap monotonicity -/

theorem term_mono {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {g : Ghost} {d k : Nat}
    {h₁ h₂ : Heap F} {v : SourceValue F} {t : KExpr} (ext : Heap.Extends h₁ h₂)
    (r : term E env g d k h₁ v t) : term E env g d k h₂ v t :=
  Tm.mono ext r

theorem ctx_mono {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {g : Ghost} {d : Nat}
    {h₁ h₂ : Heap F} {rc types : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (r : ctx E env g d h₁ rc types) : ctx E env g d h₂ rc types := by
  obtain ⟨t, lim, hκ, hrc, hty, hs, hf, hl⟩ := r
  exact ⟨t, lim, hκ, hrc.mono ext, hty.mono ext, hs, hf, hl⟩

theorem addr_mono {h₁ h₂ : Heap F} {v : SourceValue F} {a : _root_.Address}
    (ext : Heap.Extends h₁ h₂) (r : addr h₁ v a) : addr h₂ v a := by
  obtain ⟨a', ha, he⟩ := r
  exact ⟨a', Bytes.repAddressRef_heapMono₂ addrTy ext ha, he⟩

theorem loaded_mono {E₀ : Ixon.Env} {h₁ h₂ : Heap F} {ptr : SourceValue F} {bytes : ByteArray}
    (ext : Heap.Extends h₁ h₂) (r : loaded E₀ h₁ ptr bytes) : loaded E₀ h₂ ptr bytes := by
  obtain ⟨c, t, ci, hd, ht, hr⟩ := r
  exact ⟨c, t, ci, hd, ht, hr.mono ext⟩

end S0

/-! ## The instance -/

/-- **The seams instance every layer states its results against.** -/
def S₀ : IxVM.Consistency.Seams where
  addr := S0.addr
  loaded := S0.loaded
  Ghost := Ghost
  term := S0.term
  ctx := S0.ctx
  Walked := S0.Walked
  Checked := S0.Checked

/-- **`IxVM.consistent` at `S₀`**: the eight obligations stated against the instance give the
concrete statement. -/
theorem consistent_S₀ (h0 : IxVM.Consistency.L0) (h1 : IxVM.Consistency.L1 S₀)
    (h2 : IxVM.Consistency.L2) (h3 : IxVM.Consistency.L3 S₀) (h4 : IxVM.Consistency.L4 S₀)
    (h5 : IxVM.Consistency.L5.{u} S₀) (h6 : IxVM.Consistency.L6 S₀)
    (h7 : IxVM.Consistency.L7.{u} S₀) : IxVM.Consistency.CircuitConsistent.{u} :=
  IxVM.consistent S₀ h0 h1 h2 h3 h4 h5 h6 h7

end IxVM.Refinement.Core
