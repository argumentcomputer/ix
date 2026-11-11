import Ix.Cert.AcceptsUnder
import IxC.Kernel.RoleEquations
import IxC.Kernel.Verify.Cached.NormalizeRef
import Ix.Claim
import Ix.AssumptionTree
import Ix.SpecDigest
import Ix.HostAdmission.Merkle
import Ix.Address.Pure

/-! # What a claim means, in IxC terms

Track B, Phase 2 (`plans/ixvm-certification-gap.md`): the meaning of the
claims `IxVM::verify_claim` accepts, stated over IxC's reference-level
acceptance (decision D3): `Ix.Cert.IxonAcceptsRef`, and for claims that name
user axioms its policy form `Ix.Cert.IxonAcceptsRefUnder .allowUser`.
Definitions only. The statement over the IxVM program is in
`Ix.IxVM.Refinement.Statement`.

## Views

A claim names addresses: constants, an assumption tree's root, a role
table's hash. What it says depends on what those addresses resolve to, so the
meaning is stated relative to a **view** (`View`): an Ixon environment (its
records, blobs and role table) and the assumption trees a reader holds.
`Ix.Claim.HoldsIn V c` is the claim's meaning in the view `V`. The main
statement is about every authentic view that covers the claim; there is no
existential form (decision D2 was revised; see the statement module).

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
* `eval ctx input output asm`: IxC accepts the closure of `input` and
  `output` together; the output record is a safe definition with the input's
  universe count and type; and at some fuel in the accepted environment their
  annotated values are definitionally equal (`Ix.Kernel.isDefEqCore` at
  `.verified`, `EvalValues`).
* `reveal comm info`: the record at `comm` has every field `info` reveals
  (`RevealLE`).
* `contains tree a`: `a` is a leaf of the tree at `tree`.
* `binding spec b`: the role table with hash `b` binds every role, and IxC
  accepts the closure of the bound constants and evidence theorems under it.
* `catalog`, `resource`: `False`. IxVM rejects both (no arm for variant 8;
  variant 9 asserts `0 = 1`), so `False` is the strongest true statement for
  the IxVM theorem.

The typing claims (`check`, `checkEnv`, `eval`) carry, beside their context's
specification digest (which must be IxC's, `Ix.SpecDigest.specDigest`):

* **user axioms** (`axioms = some r`): the view holds the tree at `r`; every
  leaf, used or not, is a stored safe axiom the role table does not bind
  (`UserAxiomLeavesIn`, as `KernelRoles::validate_user_axioms` checks);
  acceptance runs under `allowUser` over the seeds and every leaf, with every
  user axiom the accepted declarations install among the leaves
  (`AxiomScopeIn`), and it installs every leaf that is not also an assumption
  as a user axiom (`LeavesInstalled`: an assumed leaf stays conditional, like
  any assumption). With `axioms = none` it is the strict fold;
* **assumptions** `some r`: the typing is conditional. If IxC accepts each
  leaf of the tree at `r` in the view, separately, it accepts the target;
* **an assumed binding** (validator 4, `bindingAssumed`): conditional on the
  `binding` claim for the context;
* **a literal class** (validator 5): `False`. IxVM refuses validator 5.
-/

namespace IxVM.Refinement

open Ix (Claim ClaimContext AssumptionTree RevealConstantInfo RevealMutConstInfo
  RevealConstructorInfo RevealRecursorRule)
open Ix.Kernel.Admission (Binding Limits)
open Ix.Kernel.Cached (AxiomPolicy)

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
under the pure BLAKE3 hash of their bytes, and every record is the canonical
Ixon serialization of its decoded constant (`Ix.Cert.Stream.StoredCanonical`).
(A tree is authentic by construction: its root is computed.) -/
def View.Authentic (V : View) : Prop :=
  (∀ a lc, V.env.consts.get? a = some lc →
    Address.blake3Pure lc.rawBytes = a ∧
      ∃ c, lc.get? = some c ∧ c.wireWF ∧ Ixon.serConstant c = lc.rawBytes) ∧
  (∀ a bytes, V.env.blobs.get? a = some bytes → Address.blake3Pure bytes = a) ∧
  (∀ rb, V.env.roleBinding = some rb → Address.blake3Pure rb.bytes = rb.address)

/-- `bytes` is data the view holds under the address `x`: a record, a blob,
the role table's section, or a tree's leaf or node image. -/
def View.Preimage (V : View) (x : Address) (bytes : ByteArray) : Prop :=
  (∃ lc, V.env.consts.get? x = some lc ∧ lc.rawBytes = bytes) ∨
  V.env.blobs.get? x = some bytes ∨
  (∃ rb, V.env.roleBinding = some rb ∧ rb.address = x ∧ rb.bytes = bytes) ∨
  (∃ t ∈ V.trees, bytes ∈ treeImages t ∧ Address.blake3Pure bytes = x)

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

/-- **What a typing claim is checked under**: the role table, the axiom
policy, and the addresses user axioms may have (none under `strict`). -/
structure Scope where
  binding : Binding
  policy : AxiomPolicy
  axioms : Address → Prop

/-- The strict scope of a role table: no user axiom. -/
def Scope.strict (binding : Binding) : Scope := ⟨binding, .strict, fun _ => False⟩

/-- Every user axiom of `ds` is keyed by an address `allowed` admits. -/
def UserAxiomsWithin (allowed : Address → Prop) (ds : List (Ix.Kernel.Declaration .anon)) : Prop :=
  ∀ cv ∈ Ix.Kernel.userAxiomsOfDecls ds, ∃ a, allowed a ∧ cv.name = .id a

/-- A non-auxiliary theorem declaration as an `.opaque`-hinted definition
declaration, so the reference fold unfolds theorem bodies at delta and iota
majors as Lean 4.34.1 and IxVM do (`KernelWhnf::whnf_iota_major`,
`KernelDefEq::is_def_eq_delta`). -/
def thmToOpaqueDefn {md : Ix.Kernel.Mode} :
    Ix.Kernel.Declaration md → Ix.Kernel.Declaration md
  | .thmDecl cv value =>
    match cv.name with
    | .aux _ _ => .thmDecl cv value
    | _ => .defnDecl cv value .opaque
  | d => d

/-- Every theorem declaration in `ds` has a `Prop` (`Sort 0`) type in `envA`,
matching `Ix.Kernel.checkThmVal`'s proposition check before `thmToOpaqueDefn`
installs non-auxiliary theorems as `.opaque`-hinted definitions. -/
def TheoremsInProp {md : Ix.Kernel.Mode} (envA : Ix.Kernel.Env md)
    (ds : List (Ix.Kernel.Declaration md)) : Prop :=
  ∀ cv value, Ix.Kernel.Declaration.thmDecl cv value ∈ ds →
    ∃ F tA stype u,
      (Ix.Kernel.fueledOps .verified F).annotate envA 0 cv.type = .ok tA ∧
      (Ix.Kernel.fueledOps .verified F).inferType envA 0 tA = .ok stype ∧
      (Ix.Kernel.fueledOps .verified F).ensureSort envA 0 stype = .ok u ∧
      u.isZero = true

/-- **IxC accepts the closure of the seeds `S` in the view `V`, under the
scope `σ`, and `Q` holds of the run**: an environment drawn from the view
stores every seed, and IxC's reference-level acceptance under the scope's
policy (`Ix.Kernel.Cached.AcceptsRefUnder`, with non-auxiliary theorems
installed as `.opaque`-hinted definitions and `TheoremsInProp` so theorem
majors unfold as in Lean 4.34.1 and IxVM) holds for the compiled closure of `S`
under the admitted role table (`Ix.Cert.ClosureOrderAt`), at some resource
limits, with every user axiom in the scope. `Q` sees the role table, the
installed environment and the declarations; `AcceptsIn.acceptsRefUnder` and
`AcceptsIn.acceptsRef` recover `AcceptsRefUnder` and `AcceptsRef`. -/
def AcceptsIn (V : View) (σ : Scope) (S : Address → Prop)
    (Q : Binding → Ix.Kernel.Env .anon → List (Ix.Kernel.Declaration .anon) → Prop :=
      fun _ _ _ => True) : Prop :=
  ∃ (E : Ixon.Env) (limits : Limits) (order : List Address) (envA : Ix.Kernel.Env .anon),
    Draws E V.env ∧ (∀ a, S a → E.consts.contains a = true) ∧
    ∃ t pre ev ds, Ix.Kernel.Admission.admitBinding Address.admissionHash σ.binding = .ok t ∧
      Ix.Cert.ClosureOrderAt t E S order ∧
      Ix.Kernel.Admission.admitAxiomPolicy σ.policy t = .ok () ∧
      Ix.Kernel.Reader.preludeFor t = .ok pre ∧
      Ix.Kernel.Admission.prepareWith Address.admissionHash σ.binding pre limits
        (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E) = .ok (ev, ds) ∧
      Ix.Kernel.Cached.AcceptsRefUnder σ.policy .verified ev (ds.toList.map thmToOpaqueDefn) envA ∧
      TheoremsInProp envA ds.toList ∧
      UserAxiomsWithin σ.axioms ds.toList ∧ Q σ.binding envA ds.toList

/-- `AcceptsIn` gives `Ix.Kernel.Cached.AcceptsRefUnder` on the prepared
declarations (with `thmToOpaqueDefn`), together with `TheoremsInProp`,
`UserAxiomsWithin`, and `Q`. -/
theorem AcceptsIn.acceptsRefUnder {V : View} {σ : Scope} {S : Address → Prop}
    {Q : Binding → Ix.Kernel.Env .anon → List (Ix.Kernel.Declaration .anon) → Prop}
    (h : AcceptsIn V σ S Q) :
    ∃ ev ds envA,
      Ix.Kernel.Cached.AcceptsRefUnder σ.policy .verified ev (ds.map thmToOpaqueDefn) envA ∧
      TheoremsInProp envA ds ∧ UserAxiomsWithin σ.axioms ds ∧ Q σ.binding envA ds := by
  obtain ⟨_, _, _, envA, -, -, _, _, ev, ds, -, -, -, -, -, accepted, thms, within, q⟩ := h
  exact ⟨ev, ds.toList, envA, accepted, thms, within, q⟩

/-- Under a strict scope, `AcceptsIn` gives `Ix.Kernel.Cached.AcceptsRef` on the
prepared declarations (with `thmToOpaqueDefn`). -/
theorem AcceptsIn.acceptsRef {V : View} {b : Binding} {S : Address → Prop}
    {Q : Binding → Ix.Kernel.Env .anon → List (Ix.Kernel.Declaration .anon) → Prop}
    (h : AcceptsIn V (Scope.strict b) S Q) :
    ∃ ev ds envA,
      Ix.Kernel.Cached.AcceptsRef .verified ev (ds.map thmToOpaqueDefn) envA ∧
      TheoremsInProp envA ds ∧ Q b envA ds := by
  obtain ⟨ev, ds, envA, accepted, thms, -, q⟩ := h.acceptsRefUnder
  exact ⟨ev, ds, envA, Ix.Kernel.Cached.acceptsRefUnder_strict.mp accepted, thms, q⟩

/-- **Lean's compiler-trust roles**: the inert axioms `Lean.trustCompiler`,
`Lean.ofReduceBool` and `Lean.ofReduceNat`, and the opaques `Lean.reduceBool` and
`Lean.reduceNat` whose values use `Lean.trustCompiler`. The checker accepts no
declaration of the axioms and no constant using one, so a role table's check leaves
them out: none of them can enter an environment a claim certifies. -/
def compilerTrust : Ix.Kernel.Role → Bool
  | .trustCompiler | .reduceBool | .reduceNat | .ofReduceBool | .ofReduceNat => true
  | _ => false

/-- **The seeds of a role table**: the constants it binds, but for the
compiler-trust roles (`compilerTrust`), and the theorems its evidence names. -/
def BindingSeeds (t : Ix.Kernel.RoleTable) (a : Address) : Prop :=
  (∃ r, compilerTrust r = false ∧ t.addressOf? r = some a) ∨
    ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList

/-- **The role specifications the pure declaration fold does not check on its
own** (`IxC/Kernel/Roles.lean`, `IxC/Kernel/RoleEquations.lean`): no
declaration mismatches an install-checked anchor
(`Ix.Kernel.Declaration.anchorMismatch?`), and every role specified by
definition equations (`SpecKind.eqns`) passes `Ix.Kernel.eqnsCheck` at some
fuel in the installed environment. -/
def BindingSpecs (_ : Binding) (envA : Ix.Kernel.Env .anon)
    (ds : List (Ix.Kernel.Declaration .anon)) : Prop :=
  (∀ d ∈ ds, d.anchorMismatch? = none) ∧
    ∃ ev, ∀ r ∈ Ix.Kernel.Role.all, (r.spec (md := .anon)).kind = .eqns →
      ∃ F, Ix.Kernel.eqnsCheck (Ix.Kernel.fueledOps .verified F) envA r ev = .ok ()

/-- **The `binding` claim in a view** (`binding spec b`, validator 3): `spec`
is IxC's specification digest; the view's role table with hash `b` is
admitted by IxC, binds every role, and IxC's strict fold accepts the closure
of its bound constants (but for the compiler-trust roles) and evidence theorems
under it with `BindingSpecs`,
which checks each bound constant against its role's specification. -/
def BindingIn (V : View) (spec b : Address) : Prop :=
  Ix.SpecDigest.specDigest = .ok spec ∧
    ∃ bnd t, V.binding? b = some bnd ∧
      Ix.Kernel.Admission.admitBinding Address.admissionHash bnd = .ok t ∧
      (∀ r ∈ Ix.Kernel.Role.all, (t.addressOf? r).isSome = true) ∧
      AcceptsIn V (Scope.strict bnd) (BindingSeeds t) BindingSpecs

/-- **A role table the kernel admits, its bound constants checked**: the role
table `b` is admitted (`Ix.Kernel.Admission.admitBinding`: its hash, its canonical
decoding, `RoleTable.check`), and the strict fold accepts, under it and behind the
committed prelude (`preludeFor`, inside `AcceptsIn`), the closure of the constants it
binds and of its evidence theorems in the view's records (`BindingSeeds`), with the
role specifications the fold does not check on its own (`BindingSpecs`). This is
`BindingIn` without its claim's two extra conditions (the specification digest, and
every role bound). -/
def TableAdmitted (V : View) (b : Binding) : Prop :=
  ∃ t, Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t ∧
    AcceptsIn V (Scope.strict b) (BindingSeeds t) BindingSpecs

/-- **Every leaf of a claim's axioms tree is a user axiom record**, used or
not, as IxVM validates it (`KernelRoles::validate_user_axioms`): the view
stores a safe axiom record at it, and the role table `b` binds no role to it.
`LeavesInstalled` states, beside it, that IxC installs each leaf that is not an
assumption. -/
def UserAxiomLeavesIn (V : View) (b : Binding) (leaves : List Address) : Prop :=
  ∀ a ∈ leaves,
    (∃ c ax, Ix.Cert.recordAt V.env a = some c ∧ c.info = .axio ax ∧ ax.isUnsafe = false) ∧
      ∀ t, Ix.Kernel.RoleTable.ofBytes b.bytes = some t → ∀ r, t.addressOf? r ≠ some a

/-- **`a` is a leaf of the claim's assumption tree** in the view. -/
def AssumedIn (V : View) (asm : Option Address) (a : Address) : Prop :=
  ∃ r leaves, asm = some r ∧ V.LeavesAt r leaves ∧ a ∈ leaves

/-- **Every leaf is installed as a user axiom** in an accepting run, unless it is
assumed: for each leaf not `assumed`, the declarations IxC accepts install a user
axiom keyed by its address (IxVM type-checks every leaf of the axioms tree, used
or not, except a leaf that is also one of the claim's assumptions, which stays
conditional like any assumption). -/
def LeavesInstalled (leaves : List Address) (assumed : Address → Prop)
    (ds : List (Ix.Kernel.Declaration .anon)) : Prop :=
  ∀ a ∈ leaves, ¬ assumed a → ∃ cv ∈ Ix.Kernel.userAxiomsOfDecls ds, cv.name = .id a

/-- **The axiom scope of a typing claim** under the role table `b`: with no
user axioms, `k` at the strict policy and no leaves; with the axioms tree `r`,
the view holds a tree at `r`, and for every such tree, each of its leaves is a
user axiom record (`UserAxiomLeavesIn`) and `k` holds at `allowUser` and its
leaves. -/
def AxiomScopeIn (V : View) (b : Binding) :
    Option Address → (AxiomPolicy → List Address → Prop) → Prop
  | none, k => k .strict []
  | some r, k => V.HoldsTree r ∧ ∀ leaves, V.LeavesAt r leaves →
      UserAxiomLeavesIn V b leaves ∧ k .allowUser leaves

/-- **Acceptance of `S` under the assumption tree `asm`**: unconditional for
`none`; for `some r`, the view holds a tree at `r`, and for every such tree,
if IxC accepts each of its leaves separately in the view, it accepts `S`. -/
def AssumingIn (V : View) (σ : Scope) (S : Address → Prop)
    (Q : Binding → Ix.Kernel.Env .anon → List (Ix.Kernel.Declaration .anon) → Prop) :
    Option Address → Prop
  | none => AcceptsIn V σ S Q
  | some r => V.HoldsTree r ∧
      ∀ leaves, V.LeavesAt r leaves → (∀ a ∈ leaves, AcceptsIn V σ (· = a)) → AcceptsIn V σ S Q

/-- **The typing part of a typing claim**, about the seeds `S` with
assumptions `asm`, under the context `ctx`, with `Q` of the accepting run:

* `ctx.spec` is IxC's specification digest, and the context is not a
  literal class (IxVM refuses validator 5);
* the view holds the role table with hash `ctx.binding` and validates the
  context's axiom scope (`AxiomScopeIn`), and if the context assumes its
  binding, given the `binding` claim for it, IxC accepts `S` together with
  the axioms tree's leaves that are not assumptions under it, installing each
  of them as a user axiom (`LeavesInstalled`), under the assumptions `asm`. -/
def TypingIn (V : View) (ctx : ClaimContext) (S : Address → Prop) (asm : Option Address)
    (Q : Binding → Ix.Kernel.Env .anon → List (Ix.Kernel.Declaration .anon) → Prop :=
      fun _ _ _ => True) : Prop :=
  Ix.SpecDigest.specDigest = .ok ctx.spec ∧ ctx.literalClass = false ∧
    ∃ b, V.binding? ctx.binding = some b ∧
      AxiomScopeIn V b ctx.axioms fun policy leaves =>
        ((ctx.bindingAssumed = true → BindingIn V ctx.spec ctx.binding) →
          AssumingIn V ⟨b, policy, (· ∈ leaves)⟩ (fun a => S a ∨ (a ∈ leaves ∧ ¬ AssumedIn V asm a))
            (fun bnd envA ds => LeavesInstalled leaves (AssumedIn V asm) ds ∧ Q bnd envA ds) asm)

/-! ## Eval -/

/-- The type and value a declaration gives its constant: a definition's, a
theorem's, or an opaque's (whose value the fold checks and then discards). -/
def declValue? : Ix.Kernel.Declaration .anon →
    Option (Ix.Kernel.ConstantVal .anon × Ix.Kernel.Expr .anon)
  | .defnDecl cv value _ => some (cv, value)
  | .thmDecl cv value => some (cv, value)
  | .opaqueDecl cv value => some (cv, value)
  | _ => none

/-- **The kernel key of the record at `a`** under the role table `b`: the
address itself, or the role the table binds to it. -/
def AddressKey (b : Binding) (a : Address) (k : Ix.Kernel.Key .anon) : Prop :=
  k = .id a ∨ ∃ t r, Ix.Kernel.RoleTable.ofBytes b.bytes = some t ∧ t.addressOf? r = some a ∧ k = .role r

/-- **An `eval` claim's values, in the accepting run**: the declarations give
`input` a type and value and `output` a definition; the output has the input's
universe count and type, up to binder metadata; and at some fuel in the
installed environment their annotated values are definitionally equal
(`Ix.Kernel.annotateCore` and `Ix.Kernel.isDefEqCore` at `.verified`). -/
def EvalValues (input output : Address) (b : Binding) (envA : Ix.Kernel.Env .anon)
    (ds : List (Ix.Kernel.Declaration .anon)) : Prop :=
  ∃ (cvIn cvOut : Ix.Kernel.ConstantVal .anon) (vIn vOut : Ix.Kernel.Expr .anon)
    (hint : Ix.Kernel.ReducibilityHint),
    (∃ d ∈ ds, declValue? d = some (cvIn, vIn)) ∧ AddressKey b input cvIn.name ∧
    Ix.Kernel.Declaration.defnDecl cvOut vOut hint ∈ ds ∧ AddressKey b output cvOut.name ∧
    cvOut.levelParams.length = cvIn.levelParams.length ∧
    cvOut.type.eraseMeta = cvIn.type.eraseMeta ∧
    ∃ fuel vInA vOutA,
      Ix.Kernel.annotateCore .verified envA fuel 0 vIn = .ok vInA ∧
      Ix.Kernel.annotateCore .verified envA fuel 0 vOut = .ok vOutA ∧
      Ix.Kernel.isDefEqCore .verified envA fuel 0 vInA vOutA = .ok true

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

/-- A block member in the safe fragment: safe definitions, inductives,
constructors and recursors (`Ix.Kernel.Reader.safetyDecline`). -/
def SafeMutConst : Ixon.MutConst → Prop
  | .defn d => d.safety = .safe
  | .indc i => i.isUnsafe = false ∧ ∀ ctor ∈ i.ctors.toList, ctor.isUnsafe = false
  | .recr r => r.isUnsafe = false

/-- A constant record in the safe fragment (`Ix.Kernel.Reader.safetyDecline`,
`Ix.Kernel.checkDecl` at `.verified`). -/
def SafeConstant (c : Ixon.Constant) : Prop :=
  match c.info with
  | .defn d => d.safety = .safe
  | .recr r => r.isUnsafe = false
  | .axio a => a.isUnsafe = false
  | .muts ms => ∀ m ∈ ms.toList, SafeMutConst m
  | _ => True

/-- Whether `e` in `c`, after `n` leading `λ` binders (through `share`), has
body `.prj _ _ (.var 0)` (`Ix.Kernel.Reader.projRewrite`). -/
def IsProjFnAt (c : Ixon.Constant) : Nat → Ixon.Expr → Prop
  | 0, e =>
    ∃ i f v, Ix.Kernel.Reader.unshare c e = .prj i f v ∧
      Ix.Kernel.Reader.unshare c v = .var 0
  | n + 1, e =>
    ∃ ct t b, Ix.Kernel.Reader.unshare c e = .lam ct t b ∧ IsProjFnAt c n b

/-- Whether `e` has no `.recur` inside an application argument (`inArg = true`). -/
def noArgRecur (inArg : Bool) : Ixon.Expr → Bool
  | .recur _ _ => !inArg
  | .app fn arg => noArgRecur inArg fn && noArgRecur true arg
  | .lam _ ty body | .all _ _ ty body => noArgRecur inArg ty && noArgRecur inArg body
  | .letE _ ty val body => noArgRecur inArg ty && noArgRecur inArg val && noArgRecur inArg body
  | .prj _ _ val => noArgRecur inArg val
  | _ => true

/-- Whether reference `idx` of `c` resolves in `ixe` to a single, non-nested,
index-free one-constructor inductive block (`Ix.Kernel.nativeParts?` installs a
projection table for it). -/
def DirectProjTarget (ixe : Ixon.Env) (c : Ixon.Constant) (idx : UInt64) : Prop :=
  ∃ r cr cb ind ctor,
    c.refs[idx.toNat]? = some r ∧
    Ix.Cert.recordAt ixe r = some cr ∧
    Ix.Cert.recordAt ixe (Ix.Cert.ownerOf r cr) = some cb ∧
    cb.info = .muts #[.indc ind] ∧
    ind.indices = 0 ∧
    ind.ctors = #[ctor] ∧
    noArgRecur false (Ix.Kernel.Reader.unshare cb ctor.typ) = true

/-- Typed reference resolution and structure-projection target check for an
expression of `c` in `ixe`: `.ref` and `.prj` indices resolve to constant
records (and to `DirectProjTarget` when `directProj = true`), and `.nat` and
`.str` indices resolve to literal blobs. -/
def ExprRefsClosed (ixe : Ixon.Env) (c : Ixon.Constant) (directProj : Bool) :
    Ixon.Expr → Prop
  | .ref idx _ => ∃ r, c.refs[idx.toNat]? = some r ∧ ixe.consts.contains r = true
  | .prj idx _ val =>
    (∃ r, c.refs[idx.toNat]? = some r ∧ ixe.consts.contains r = true) ∧
      (directProj = true → DirectProjTarget ixe c idx) ∧
      ExprRefsClosed ixe c directProj val
  | .str idx | .nat idx => ∃ r, c.refs[idx.toNat]? = some r ∧ ixe.blobs.contains r = true
  | .app fn arg => ExprRefsClosed ixe c directProj fn ∧ ExprRefsClosed ixe c directProj arg
  | .lam _ ty body | .all _ _ ty body =>
    ExprRefsClosed ixe c directProj ty ∧ ExprRefsClosed ixe c directProj body
  | .letE _ ty val body =>
    ExprRefsClosed ixe c directProj ty ∧ ExprRefsClosed ixe c directProj val ∧
      ExprRefsClosed ixe c directProj body
  | _ => True

/-- Every expression of `c` is in the Lean contract fragment (`leanFragment`),
resolves its references by kind (`ExprRefsClosed`), and outside projection
functions (`IsProjFnAt`) projects only from direct structures. -/
def ConstantExprsClosed (ixe : Ixon.Env) (c : Ixon.Constant) : Prop :=
  (∀ e ∈ c.info.exprs ++ c.sharing.toList,
    e.leanFragment = true ∧ ExprRefsClosed ixe c false e) ∧
  ∀ e ∈ c.info.exprs,
    (¬ ∃ d n, c.info = .defn d ∧ e = d.value ∧ IsProjFnAt c n d.value) →
      ExprRefsClosed ixe c true (Ix.Kernel.Reader.unshare c e)

/-- Whether `envA` installs a constant at `.role r` whose universe parameters and
type (up to binder metadata) match `r`'s `.anchor` specification. -/
def AnchorPinned (envA : Ix.Kernel.Env .anon) (r : Ix.Kernel.Role) : Prop :=
  ∀ n ty, r.spec (md := .anon) = .anchor n ty →
    ∃ ci, envA.find? (.role r) = some ci ∧
      ci.toConstantVal.levelParams = List.range n ∧
      ci.toConstantVal.type.eraseMeta = ty.eraseMeta

/-- **A closed view**: every stored record is in the safe fragment
(`SafeConstant`) and the Lean contract fragment with well-typed reference kinds
and direct structure projections (`ConstantExprsClosed`), every reference of a
stored record resolves to a stored record or blob, a projection's block is
stored, and the role table the view holds is a valid role table admitted by IxC
(`RoleTable.check`, `preludeFor`, which pins the prelude roles) whose bound
constants and evidence theorems are stored and whose `.anchor` roles are
accepted by IxC with their pinned specification types (`AnchorPinned`) in the
view. Because `SafeConstant` restricts to the safe fragment, whole-environment
`checkEnv` claims whose leaves include `unsafe` or `partial` constants are
outside `Covers`. -/
def View.Closed (V : View) : Prop :=
  (∀ a c, Ix.Cert.recordAt V.env a = some c →
    SafeConstant c ∧ ConstantExprsClosed V.env c ∧
      (∀ r ∈ c.refs.toList, V.env.consts.contains r = true ∨ V.env.blobs.contains r = true) ∧
      V.env.consts.contains (Ix.Cert.ownerOf a c) = true) ∧
  (∀ rb, V.env.roleBinding = some rb →
    ∃ t, Ix.Kernel.RoleTable.ofBytes rb.bytes = some t ∧ t.check = .ok () ∧
      (∃ pre : Ix.Kernel.Reader.Prelude .anon, Ix.Kernel.Reader.preludeFor t = .ok pre) ∧
      (∀ a, BindingSeeds t a → V.env.consts.contains a = true) ∧
      ∀ r, (r.spec (md := .anon)).kind = .anchor → ∀ a, t.addressOf? r = some a →
        AcceptsIn V (Scope.strict ⟨rb.address, rb.bytes⟩) (· = a) fun _ envA _ =>
          AnchorPinned envA r)

/-- What a view must hold for a typing claim: it is closed, it holds the
claim's role table, the assumption tree, if any, and the axioms tree, if any,
with the role table admitted under `allowUser` and each axiom stored. -/
def View.TypingCovers (V : View) (ctx : ClaimContext) (asm : Option Address) : Prop :=
  V.Closed ∧ (V.binding? ctx.binding).isSome = true ∧ (∀ r, asm = some r → V.HoldsTree r) ∧
    ∀ r, ctx.axioms = some r →
      V.HoldsTree r ∧
        (∀ rb t, V.env.roleBinding = some rb → Ix.Kernel.RoleTable.ofBytes rb.bytes = some t →
          Ix.Kernel.Admission.admitAxiomPolicy .allowUser t = .ok ()) ∧
        ∀ leaves, V.LeavesAt r leaves → ∀ a ∈ leaves, V.Stores a

end IxVM.Refinement

namespace Ix.Claim

open IxVM.Refinement

/-- **A claim's meaning in the view `V`**, in IxC terms (see the module
docstring for each variant). -/
def HoldsIn (V : View) : Claim → Prop
  | .eval ctx input output asm =>
      TypingIn V ctx (fun a => a = input ∨ a = output) asm (EvalValues input output) ∧
        EvalOutputIn V output
  | .check ctx a asm => TypingIn V ctx (· = a) asm
  | .checkEnv ctx root asm => V.HoldsTree root ∧
      ∀ leaves, V.LeavesAt root leaves → leaves ≠ [] ∧ TypingIn V ctx (· ∈ leaves) asm
  | .reveal comm info => ∃ c, Ix.Cert.recordAt V.env comm = some c ∧ RevealLE info c.info
  | .contains tree a => V.HoldsTree tree ∧ ∀ leaves, V.LeavesAt tree leaves → a ∈ leaves
  | .catalog _ => False
  | .resource _ _ => False
  | .binding spec b => BindingIn V spec b

/-- **What a view must hold for the claim** before the main statement says
anything about it: the addresses the claim names are stored, the trees it
names are held, and, for the typing and binding claims, the view is closed
and holds the role table. -/
def Covers (V : View) : Claim → Prop
  | .eval ctx input output asm => V.TypingCovers ctx asm ∧ V.Stores input ∧ V.Stores output ∧
      ∀ c d, Ix.Cert.recordAt V.env output = some c → c.info = .defn d → ∀ n, ¬ IsProjFnAt c n d.value
  | .check ctx a asm => V.TypingCovers ctx asm ∧ V.Stores a
  | .checkEnv ctx root asm => V.TypingCovers ctx asm ∧ V.HoldsTree root ∧
      ∀ leaves, V.LeavesAt root leaves → ∀ a ∈ leaves, V.Stores a
  | .reveal comm _ => V.Stores comm
  | .contains tree _ => V.HoldsTree tree
  | .binding _ b => V.Closed ∧ (V.binding? b).isSome = true
  | .catalog _ => True
  | .resource _ _ => True

end Ix.Claim
