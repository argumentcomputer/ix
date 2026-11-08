import Ix.Cert.Statement
import Ix.Claim
import Ix.AssumptionTree
import Ix.SpecDigest
import Ix.HostAdmission.Merkle
import Ix.Address.Pure

/-! # What a claim means, in IxC terms

Track B, Phase 2 (`plans/ixvm-certification-gap.md`): the meaning of the
claims `IxVM::verify_claim` accepts, stated over IxC's reference-level
acceptance `Ix.Cert.IxonAcceptsRef` (decision D3). Definitions only. The
statement over the IxVM program is in `Ix.IxVM.Refinement.Statement`.

## Views

A claim names addresses: constants, an assumption tree's root, a role
table's hash. What it says depends on what those addresses resolve to, so the
meaning is stated relative to a **view** (`View`): an Ixon environment (its
records, blobs and role table) and the assumption trees a reader holds.
`Ix.Claim.HoldsIn V c` is the claim's meaning in the view `V`.

* `Ix.Claim.Holds c` is decision D2's form: **some** authentic view makes the
  claim hold.
* The collision corollary (`IxVMClaimSpecIn`, in the statement module) is
  stated for **every** authentic view that covers the claim: the claim holds
  in it, or a second preimage of data the view holds exists.

Acceptance in a view (`AcceptsIn`) uses only the view's records and blobs,
except that it may supply recursor records the view lacks (`Draws`): IxC
declines an inductive block without its recursors
(`Ix.Kernel.Reader.readInductive`), IxVM reads only referenced records, and a
recursor is checked against its block, so supplying one adds no content.
Reducibility hints are free: they are not content addressed, and IxVM reads
them as unauthenticated advice.

## Per variant

* `check ctx a asm`: IxC accepts the closure of `a` (`TypingIn`).
* `checkEnv ctx root asm`: the tree at `root` has leaves, and IxC accepts the
  closure of all of them.
* `eval ctx input output asm`: the typing of `input`, and the output record
  is a safe definition. The value relation (`output`'s value is the normal
  form of `input`'s) is not stated yet; see the review note.
* `reveal comm info`: the record at `comm` has every field `info` reveals
  (`RevealLE`).
* `contains tree a`: `a` is a leaf of the tree at `tree`.
* `binding spec b`: the role table with hash `b` binds every role, and IxC
  accepts the closure of the bound constants and evidence theorems under it.
* `catalog`, `resource`: `False`. IxVM rejects both (no arm for variant 8;
  variant 9 asserts `0 = 1`), so `False` is the strongest true statement for
  the IxVM theorem. They have no IxC meaning here.

The typing claims (`check`, `checkEnv`, `eval`) carry, beside their context's
specification digest (which must be IxC's, `Ix.SpecDigest.specDigest`):

* **assumptions** `some r`: the typing is conditional. If IxC accepts each
  leaf of the tree at `r` in the view, it accepts the target.
* **an assumed binding** (validator 4, `bindingAssumed`): conditional on the
  `binding` claim for the context.
* **a literal class** (validator 5): `False`. IxVM refuses validator 5.
* **user axioms** (`axioms = some _`): **no statement** (the typing part is
  `ctx.axioms = none → …`). IxVM admits them (`KernelRoles::load_role_ctx`),
  but IxC has no reference-level fold that admits user axioms
  (`Ix.Kernel.Cached.AxiomPolicy.allowUser` exists only for the cached fold,
  at fixed fuel), so there is nothing in D3's terms to state. See the review
  note.
-/

namespace IxVM.Refinement

open Ix (Claim ClaimContext AssumptionTree RevealConstantInfo RevealMutConstInfo
  RevealConstructorInfo RevealRecursorRule)
open Ix.Kernel.Admission (Binding Limits)

/-! ## Assumption trees -/

/-- **An assumption tree's root**, as IxVM recomputes it
(`KernelClaim::parse_atree_body`): a leaf hashes as `BLAKE3(0x00 ‖ a)`, a
node as `BLAKE3(0x01 ‖ l ‖ r)`, padding is the zero address
(`Ix.HostAdmission.Merkle`, at pure BLAKE3). Total, unlike the host's
`Ix.AssumptionTree.root`. -/
def treeRoot : AssumptionTree → Address
  | .leaf a => Ix.HostAdmission.Merkle.leaf a
  | .padding => Ix.HostAdmission.Merkle.padding
  | .node l r => Ix.HostAdmission.Merkle.node (treeRoot l) (treeRoot r)

/-- An assumption tree's leaves, left to right; padding has none. -/
def treeLeaves : AssumptionTree → List Address
  | .leaf a => [a]
  | .padding => []
  | .node l r => treeLeaves l ++ treeLeaves r

/-- The byte strings an assumption tree's hashes are computed over, one per
leaf and node. -/
def treeImages : AssumptionTree → List ByteArray
  | .leaf a => [ByteArray.mk #[0] ++ a.hash]
  | .padding => []
  | .node l r =>
    (ByteArray.mk #[1] ++ (treeRoot l).hash ++ (treeRoot r).hash) :: (treeImages l ++ treeImages r)

/-! ## Views -/

/-- **A view**: what a reader of a claim holds. The environment's records,
blobs and role binding resolve the claim's addresses; `trees` are the
assumption trees it holds, found by root. -/
structure View where
  env : Ixon.Env
  trees : List AssumptionTree := []

/-- The view holds a tree with root `root` and leaves `leaves`. -/
def View.LeavesAt (V : View) (root : Address) (leaves : List Address) : Prop :=
  ∃ t ∈ V.trees, treeRoot t = root ∧ treeLeaves t = leaves

/-- The view holds a tree with root `root`. -/
def View.HoldsTree (V : View) (root : Address) : Prop :=
  ∃ leaves, V.LeavesAt root leaves

/-- The role table the view holds under the address `address`: its
environment's role binding, if that is the one. -/
def View.binding? (V : View) (address : Address) : Option Binding :=
  match V.env.roleBinding with
  | some rb => if rb.address = address then some { address := rb.address, bytes := rb.bytes } else none
  | none => none

/-- `a` is stored in the view. -/
def View.Stores (V : View) (a : Address) : Prop :=
  V.env.consts.contains a = true

/-- **An authentic view**: every record, blob and the role table are stored
under the pure BLAKE3 hash of their bytes. (A tree is authentic by
construction: its root is computed.) -/
def View.Authentic (V : View) : Prop :=
  (∀ a lc, V.env.consts.get? a = some lc → Address.blake3Pure lc.rawBytes = a) ∧
  (∀ a bytes, V.env.blobs.get? a = some bytes → Address.blake3Pure bytes = a) ∧
  (∀ rb, V.env.roleBinding = some rb → Address.blake3Pure rb.bytes = rb.address)

/-- `bytes` is data the view holds under the address `x`: a record, a blob,
the role table's section, or a tree's leaf or node image. -/
def View.Preimage (V : View) (x : Address) (bytes : ByteArray) : Prop :=
  (∃ lc, V.env.consts.get? x = some lc ∧ lc.rawBytes = bytes) ∨
  V.env.blobs.get? x = some bytes ∨
  (∃ rb, V.env.roleBinding = some rb ∧ rb.address = x ∧ rb.bytes = bytes) ∨
  (∃ t ∈ V.trees, bytes ∈ treeImages t ∧ Address.blake3Pure bytes = x)

/-- **A second preimage of the view's data** (or of `extra`, such as a
claim's bytes): another byte string with the same pure BLAKE3 hash as one the
view holds. Every statement here that allows a collision allows only this
kind, relative to data the reader holds; an unrelated collision always exists
(by counting) and would make such a disjunct trivial. -/
def View.Collision (V : View) (extra : List ByteArray) : Prop :=
  ∃ (x : Address) (held other : ByteArray),
    (V.Preimage x held ∨ (held ∈ extra ∧ Address.blake3Pure held = x)) ∧
      other ≠ held ∧ Address.blake3Pure other = x

/-! ## Acceptance in a view -/

/-- A record of recursors only: a recursor, or a block whose members are all
recursors. -/
def IsRecursorRecord (c : Ixon.Constant) : Prop :=
  match c.info with
  | .recr _ => True
  | .muts ms => ∀ m ∈ ms.toList, ∃ r, m = .recr r
  | _ => False

/-- **`E` draws from `E₀`**: every record of `E` is `E₀`'s record at its
address, or a recursor record at an address `E₀` does not store; every blob
of `E` is `E₀`'s. Hints, names and the role binding are unconstrained. -/
def Draws (E E₀ : Ixon.Env) : Prop :=
  (∀ a lc, E.consts.get? a = some lc →
    (∃ lc₀, E₀.consts.get? a = some lc₀ ∧ lc₀.rawBytes = lc.rawBytes) ∨
    (E₀.consts.contains a = false ∧ ∃ c, lc.get? = some c ∧ IsRecursorRecord c)) ∧
  (∀ a bytes, E.blobs.get? a = some bytes → E₀.blobs.get? a = some bytes)

/-- **IxC accepts the closure of the seeds `S` in the view `V`, under the
role table `b`**: an environment drawn from the view stores every seed, and
IxC's reference-level acceptance (`Ix.Cert.IxonAcceptsRef`, decision D3)
holds for the compiled closure of `S` in it, at some resource limits. -/
def AcceptsIn (V : View) (b : Binding) (S : Address → Prop) : Prop :=
  ∃ (E : Ixon.Env) (limits : Limits) (order : List Address) (envA : Ix.Kernel.Env .anon),
    Draws E V.env ∧ (∀ a, S a → E.consts.contains a = true) ∧
      Ix.Cert.IxonAcceptsRef b limits E S order envA

/-- **The seeds of a role table**: the constants it binds and the theorems
its evidence names. -/
def BindingSeeds (t : Ix.Kernel.RoleTable) (a : Address) : Prop :=
  (∃ r, t.addressOf? r = some a) ∨
    ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList

/-- **The `binding` claim in a view** (`binding spec b`, validator 3): `spec`
is IxC's specification digest; the view's role table with hash `b` is
admitted by IxC, binds every role, and IxC accepts the closure of its bound
constants and evidence theorems under it, which checks each bound constant
against its role's specification. -/
def BindingIn (V : View) (spec b : Address) : Prop :=
  Ix.SpecDigest.specDigest = .ok spec ∧
    ∃ bnd t, V.binding? b = some bnd ∧
      Ix.Kernel.Admission.admitBinding Address.admissionHash bnd = .ok t ∧
      (∀ r ∈ Ix.Kernel.Role.all, (t.addressOf? r).isSome = true) ∧
      AcceptsIn V bnd (BindingSeeds t)

/-- **Acceptance of `S` under the assumption tree `asm`**: unconditional for
`none`; for `some r`, the view holds a tree at `r`, and for every such tree,
if IxC accepts each of its leaves in the view, it accepts `S`. -/
def AssumingIn (V : View) (b : Binding) (S : Address → Prop) : Option Address → Prop
  | none => AcceptsIn V b S
  | some r => V.HoldsTree r ∧
      ∀ leaves, V.LeavesAt r leaves → (∀ a ∈ leaves, AcceptsIn V b (· = a)) → AcceptsIn V b S

/-- **The typing part of a typing claim**, about the seeds `S` with
assumptions `asm`, under the context `ctx`:

* `ctx.spec` is IxC's specification digest, and the context is not a
  literal class (IxVM refuses validator 5);
* with no user axioms (`ctx.axioms = none`; see the module docstring for why
  user axioms get no statement), and, if the context assumes its binding,
  given the `binding` claim for it: the view holds the role table with hash
  `ctx.binding`, and IxC accepts `S` under it, under the assumptions `asm`. -/
def TypingIn (V : View) (ctx : ClaimContext) (S : Address → Prop) (asm : Option Address) : Prop :=
  Ix.SpecDigest.specDigest = .ok ctx.spec ∧ ctx.literalClass = false ∧
    (ctx.axioms = none →
      (ctx.bindingAssumed = true → BindingIn V ctx.spec ctx.binding) →
      ∃ b, V.binding? ctx.binding = some b ∧ AssumingIn V b S asm)

/-- **An `eval` claim's output record**: the view stores a safe standalone
definition (kind `defn`, safety `safe`) at `output`. -/
def EvalOutputIn (V : View) (output : Address) : Prop :=
  ∃ c d, Ix.Cert.recordAt V.env output = some c ∧ c.info = .defn d ∧
    d.kind = .defn ∧ d.safety = .safe

/-! ## Reveal -/

/-- A revealed field: absent, or equal to the real one. -/
def OptEq {α : Type} (claimed : Option α) (real : α) : Prop :=
  ∀ x, claimed = some x → x = real

/-- The address a reveal names an expression by: pure BLAKE3 of its Ixon
serialization (`KernelClaim::expr_addr`; the host's `Ix.Commit.exprAddr`
hashes the same bytes). -/
def exprAddr (e : Ixon.Expr) : Address :=
  Address.blake3Pure (Ixon.runPut (Ixon.putExpr e))

/-- A recursor's rules as a reveal states them: every rule, at its position. -/
def revealRules (rules : Array Ixon.RecursorRule) : List RevealRecursorRule :=
  rules.toList.zipIdx.map fun (r, j) => ⟨j.toUInt64, r.fields, exprAddr r.rhs⟩

/-- Revealed constructor fields hold of `c`. -/
def RevealConstructorLE (info : RevealConstructorInfo) (c : Ixon.Constructor) : Prop :=
  OptEq info.isUnsafe c.isUnsafe ∧ OptEq info.lvls c.lvls ∧ OptEq info.cidx c.cidx ∧
    OptEq info.params c.params ∧ OptEq info.fields c.fields ∧ OptEq info.typ (exprAddr c.typ)

/-- Revealed definition fields hold of `d`. -/
def RevealDefnLE (kind : Option Ix.DefKind) (safety : Option Ix.DefinitionSafety)
    (lvls : Option UInt64) (typ value : Option Address) (d : Ixon.Definition) : Prop :=
  OptEq kind d.kind ∧ OptEq safety d.safety ∧ OptEq lvls d.lvls ∧
    OptEq typ (exprAddr d.typ) ∧ OptEq value (exprAddr d.value)

/-- Revealed recursor fields hold of `r`; revealed rules are all of them, in
order (`KernelClaim::check_recr_rules`). -/
def RevealRecrLE (k isUnsafe : Option Bool) (lvls params indices motives minors : Option UInt64)
    (typ : Option Address) (rules : Option (Array RevealRecursorRule)) (r : Ixon.Recursor) : Prop :=
  OptEq k r.k ∧ OptEq isUnsafe r.isUnsafe ∧ OptEq lvls r.lvls ∧ OptEq params r.params ∧
    OptEq indices r.indices ∧ OptEq motives r.motives ∧ OptEq minors r.minors ∧
    OptEq typ (exprAddr r.typ) ∧ OptEq (rules.map Array.toList) (revealRules r.rules)

/-- Revealed inductive fields hold of `i`; each revealed constructor entry
names a constructor by index (`KernelClaim::check_ctor_entries`). -/
def RevealIndcLE (isUnsafe : Option Bool) (lvls params indices : Option UInt64)
    (typ : Option Address) (ctors : Option (Array (UInt64 × RevealConstructorInfo)))
    (i : Ixon.Inductive) : Prop :=
  OptEq isUnsafe i.isUnsafe ∧ OptEq lvls i.lvls ∧ OptEq params i.params ∧
    OptEq indices i.indices ∧ OptEq typ (exprAddr i.typ) ∧
    ∀ cs, ctors = some cs → ∀ e ∈ cs.toList,
      ∃ c, i.ctors[e.1.toNat]? = some c ∧ RevealConstructorLE e.2 c

/-- Revealed fields of a block member hold of `m`, of the same kind. -/
def RevealMutLE : RevealMutConstInfo → Ixon.MutConst → Prop
  | .defn k s l t v, .defn d => RevealDefnLE k s l t v d
  | .indc u l p ix t cs, .indc i => RevealIndcLE u l p ix t cs i
  | .recr k u l p ix mo mi t rs, .recr r => RevealRecrLE k u l p ix mo mi t rs r
  | _, _ => False

/-- **Every field `info` reveals holds of the constant `ci`**, of the same
variant (`KernelClaim::run_reveal`); a block's revealed components name
members by index (`check_muts_components`). -/
def RevealLE : RevealConstantInfo → Ixon.ConstantInfo → Prop
  | .defn k s l t v, .defn d => RevealDefnLE k s l t v d
  | .recr k u l p ix mo mi t rs, .recr r => RevealRecrLE k u l p ix mo mi t rs r
  | .axio u l t, .axio a => OptEq u a.isUnsafe ∧ OptEq l a.lvls ∧ OptEq t (exprAddr a.typ)
  | .quot k l t, .quot q => OptEq k q.kind ∧ OptEq l q.lvls ∧ OptEq t (exprAddr q.typ)
  | .cPrj i c b, .cPrj p => OptEq i p.idx ∧ OptEq c p.cidx ∧ OptEq b p.block
  | .rPrj i b, .rPrj p => OptEq i p.idx ∧ OptEq b p.block
  | .iPrj i b, .iPrj p => OptEq i p.idx ∧ OptEq b p.block
  | .dPrj i b, .dPrj p => OptEq i p.idx ∧ OptEq b p.block
  | .muts cs, .muts ms => ∀ e ∈ cs.toList, ∃ m, ms[e.1.toNat]? = some m ∧ RevealMutLE e.2 m
  | _, _ => False

/-! ## Coverage -/

/-- **A closed view**: every reference of a stored record resolves to a
stored record or blob, a projection's block is stored, and the role table
the view holds has its bound constants and evidence theorems stored. -/
def View.Closed (V : View) : Prop :=
  (∀ a c, Ix.Cert.recordAt V.env a = some c →
    (∀ r ∈ c.refs.toList, V.env.consts.contains r = true ∨ V.env.blobs.contains r = true) ∧
      V.env.consts.contains (Ix.Cert.ownerOf a c) = true) ∧
  (∀ rb t, V.env.roleBinding = some rb → Ix.Kernel.RoleTable.ofBytes rb.bytes = some t →
    ∀ a, BindingSeeds t a → V.env.consts.contains a = true)

/-- What a view must hold for a typing claim: it is closed, it holds the
claim's role table, and it holds the assumption tree, if any. -/
def View.TypingCovers (V : View) (ctx : ClaimContext) (asm : Option Address) : Prop :=
  V.Closed ∧ (V.binding? ctx.binding).isSome = true ∧ ∀ r, asm = some r → V.HoldsTree r

end IxVM.Refinement

namespace Ix.Claim

open IxVM.Refinement

/-- **A claim's meaning in the view `V`**, in IxC terms (see the module
docstring for each variant). -/
def HoldsIn (V : View) : Claim → Prop
  | .eval ctx input output asm => TypingIn V ctx (· = input) asm ∧ EvalOutputIn V output
  | .check ctx a asm => TypingIn V ctx (· = a) asm
  | .checkEnv ctx root asm => V.HoldsTree root ∧
      ∀ leaves, V.LeavesAt root leaves → leaves ≠ [] ∧ TypingIn V ctx (· ∈ leaves) asm
  | .reveal comm info => ∃ c, Ix.Cert.recordAt V.env comm = some c ∧ RevealLE info c.info
  | .contains tree a => V.HoldsTree tree ∧ ∀ leaves, V.LeavesAt tree leaves → a ∈ leaves
  | .catalog _ => False
  | .resource _ _ => False
  | .binding spec b => BindingIn V spec b

/-- **What a view must hold for the claim** before the collision corollary
says anything about it: the addresses the claim names are stored, the trees
it names are held, and, for the typing and binding claims, the view is
closed and holds the role table. -/
def Covers (V : View) : Claim → Prop
  | .eval ctx input output asm => V.TypingCovers ctx asm ∧ V.Stores input ∧ V.Stores output
  | .check ctx a asm => V.TypingCovers ctx asm ∧ V.Stores a
  | .checkEnv ctx root asm => V.TypingCovers ctx asm ∧ V.HoldsTree root ∧
      ∀ leaves, V.LeavesAt root leaves → ∀ a ∈ leaves, V.Stores a
  | .reveal comm _ => V.Stores comm
  | .contains tree _ => V.HoldsTree tree
  | .binding _ b => V.Closed ∧ (V.binding? b).isSome = true
  | .catalog _ => True
  | .resource _ _ => True

/-- **Decision D2's form**: some authentic view makes the claim hold. For a
conditional claim this is weak: a view can be chosen in which a leaf is not
accepted. See the review note. -/
def Holds (c : Claim) : Prop :=
  ∃ V : View, V.Authentic ∧ c.HoldsIn V

end Ix.Claim
