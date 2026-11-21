import IxVMRefinement.Core.Loaded
import IxC.Kernel.Rules.Rel
import IxC.Kernel.Rules.Transport
import IxC.Kernel.Rules.TransportKit
import IxC.Kernel.Ixon.RoleTable
import IxC.Kernel.Roles
import IxC.Kernel.RoleEquations
import Ix.IxVM.Refinement.Claim
import Ix.SpecDigest.Schedule
import IxC.Kernel.Model.Open.StoredFacts
import IxC.Kernel.BasisA
import IxC.Kernel.Model.StoreCompanions

/-! # The context seam: the role context, the context list, and the environment the core reads

The core's functions run under a role context `rc` (`KernelRoles::RoleCtx`) and a context list
`types` (`Lists::List<KExpr>`). They are related to the kernel side by:

* `Ctx`: the records `E` the kernel environment was read from (the collision escape is
  relative to them), the environment `env`, and the role table `t` the run read. The keying of
  addresses is the table's (`keyOf`): an address the table binds to a role `r` is `.role r`,
  any other address `a` is `.id a`, as the kernel reader keys records (`Reader.keyOfAddress`).
* `RCRep t lim h rc`: `rc` reads the table `t` at the group limit `lim` (`Ctx.inForce`: the
  roles of the groups below it). Every entry of its three maps (role → address,
  address → role, role → evidence) is `t`'s; a lookup that finds an entry is therefore sound.
  The search order is not constrained (nothing claims a failed lookup).
* `TypesRep κ Γ h d types`: `types` is a segment of the ghost context ending at depth `d`: its
  entry `i` (innermost first) is the type `Γ (d - 1 - i)` of the opened variable `d - 1 - i`,
  represented at the depth that variable was opened at (IxVM lifts it on lookup:
  `KernelInfer::types_lookup`). Trimming outer entries (`ctx_trim`) keeps a segment with the
  same top end.
* `EnvFacts c`: **the environment invariant the core reads** — the `Core` ↔ `Decls`/`Assembly` interface. Each
  field names the layer that must establish it.

| Field | What the core reads it for | Established by |
|---|---|---|
| `tableWf` | role keys are a function of addresses (no address bound twice) | Claim (the run admitted `t`), Assembly (`t` is `ReadIn`'s) |
| `storeClosed` | moving a derivation between depths (`Rules.Transport`), for the context-lowering rebases | Decls (every installed term is closed), Assembly |
| `thmTyped` | `Red.deltaThm`'s premises: a stored theorem's value, closed and typed at its own levels | Decls (each theorem's own check, carried along the fold by `Transport.weaken`) |
| `natLit`, `strLit`, `natOps`, `natAdd` | the native rules' stored-shape guards (`natLitSupported`, `strLitSupported`, `natOpStored`, `natAddTyOk`) | Decls (the constants of the roles in force installed as their specifications), Claim (a group is admitted before its roles are in force) |
| `eqStored` | `Red.eqProof`: `Eq` is stored when it is in force | Decls (roles in force installed as their specifications), Claim (group admission) |
| `recRules` | `Red.iota`'s rule lookup (the firing conjunct is `Ix.Kernel.Open.recRules_fire`): distinct keys, firing rules at stored constructors with their parameter counts, the `j`-th rule for the `j`-th constructor of the member the major's `iPrj` record names | Decls (recursor install), Assembly (keys from `ReadIn`) |
| `recPlain` | a plain rule's comparands are the major premise's domain | Decls (recursor install) |
| `recArity`, `ruleCtorArity`, `tableCtorArity`, `familyArity` | the stored telescopes the walks read have a binder for every argument (`CertsR.toCerts`): a recursor with a rule, a rule's or a projection table entry's constructor, a unit-like or η-capable family | Decls (the fold's invariants `EnvWF`, `RecCtorsStored`, `ProjOkT`; `Ix.Kernel.Open.StoredFacts`) |

The loads (`Ingress::get_ci` and the projection loaders) are related to `env` by `LoadFacts`
(`Good.lean`): the Ingress ↔ Assembly interface. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq Infer)

set_option linter.unusedVariables false

/-! ## The keying of the table the run read -/

/-- **The key of the constant at an address** under the role table `t`: the role `t` binds to
it, else the address itself (`Reader.keyOfAddress` on a table with no address bound twice). -/
def keyOf (t : Ix.Kernel.RoleTable) (a : _root_.Address) : KKey :=
  match t.bound.find? (·.2 == a) with
  | some (r, _) => .role r
  | none => .id a

/-- Every key of a role table's keying resolves: it is a role key or an input key. -/
instance (t : Ix.Kernel.RoleTable) (a : _root_.Address) : Resolved (keyOf t a) :=
  ⟨by unfold keyOf; split <;> exact nofun⟩

/-! ## The context -/

/-- **The context of a run of the core**: the records the environment was read from, the
environment, the role table the run read, and the role context's group limit (`lim`: the roles
of the groups before it are in force, `KernelRoles::role_of`; `none` for an assuming context,
under which every bound role is). -/
structure Ctx where
  E : Ixon.Env
  env : Ix.Kernel.Env .anon
  t : Ix.Kernel.RoleTable
  lim : Option Nat := none

/-- A core run selects the exact function, arguments, and input heap of its allowed calls, and
keys the terms it handles by `key`: the table's keying on the addresses the context knows
resolve, `unresolvedKey` on every other (`key_spec`). By default every address resolves and
`key` is the table's keying. A term is represented under `key` only when the keys of all its
constant and projection nodes resolve (`Tm.const`, `Tm.proj`), so the installed-lookup claims of
the loads can be conditional on resolution and still be read at every load the core makes.
The underlying context remains available to raw declaration and record traversal. -/
structure ScopedCtx extends Ctx where
  allowed : Call F → Prop
  key : _root_.Address → KKey := keyOf t
  key_spec : ∀ a, key a = keyOf t a ∨ key a = unresolvedKey := by intro a; exact Or.inl rfl

/-- Explicit compatibility with the historical unrestricted context. Actual declaration
origins supply their own selected-call predicate. -/
def ScopedCtx.unrestricted (c : Ctx) : ScopedCtx :=
  { toCtx := c, allowed := fun _ => True }

instance : Coe ScopedCtx Ctx := ⟨ScopedCtx.toCtx⟩

abbrev ScopedCtx.allowedTop (c : ScopedCtx) (fname : String)
    (args : List (SourceValue F)) (h : Heap F) : Prop :=
  c.allowed ⟨fname, args, h⟩

/-- The keying of addresses: the table's. -/
abbrev Ctx.κ (c : Ctx) : _root_.Address → KKey := keyOf c.t

/-- The keying of the terms a scoped run handles (`ScopedCtx.key`). -/
abbrev ScopedCtx.κ (c : ScopedCtx) : _root_.Address → KKey := c.key

/-- **A family is stored at member `i` of block `b`**: the inductive at the key of its projection
record, or one of its constructors. The evidence a run has in hand when it loads a member of the
block: it names the kind of the stored constant, so a constant of another kind at the same key
is no evidence. -/
def ScopedCtx.FamAt (c : ScopedCtx) (b : _root_.Address) (i : Nat) : Prop :=
  (∃ cv caps, c.env.find? (c.κ (iprjAddr b i)) = some (.indInfo cv caps)) ∨
    ∃ j cv nP nF, c.env.find? (c.κ (cprjAddr b i j)) = some (.ctorInfo cv nP nF)

/-- A resolved key of a scoped context is the table's. -/
theorem ScopedCtx.key_eq (c : ScopedCtx) {a : _root_.Address} (h : c.κ a ≠ unresolvedKey) :
    c.κ a = keyOf c.t a :=
  (c.key_spec a).resolve_right h

/-- A resolved address, as the instance the term seam reads. -/
theorem ScopedCtx.resolved (c : ScopedCtx) {a : _root_.Address} (h : c.κ a ≠ unresolvedKey) :
    Resolved (c.κ a) := ⟨h⟩

/-- **The context keys every address by the table**: no address is unresolved. The contexts of
the native fragments are of this kind; their loads are constrained by scope membership. -/
class ScopedCtx.TableKeyed (c : ScopedCtx) : Prop where
  key_eq : c.key = keyOf c.t

instance (c : Ctx) (allowed : Call F → Prop) :
    ScopedCtx.TableKeyed { toCtx := c, allowed := allowed } := ⟨rfl⟩

instance (c : Ctx) : (ScopedCtx.unrestricted c).TableKeyed := ⟨rfl⟩

/-- The keying of a table-keyed context is the table's. -/
theorem ScopedCtx.κ_eq (c : ScopedCtx) [h : c.TableKeyed] : c.κ = keyOf c.t := h.key_eq

/-- A table-keyed context with another scope is the plain context of its base and that scope. -/
theorem ScopedCtx.withAllowed_eq (c : ScopedCtx) [h : c.TableKeyed] (allowed : Call F → Prop) :
    ({ c with allowed := allowed } : ScopedCtx) = { toCtx := c.toCtx, allowed := allowed } := by
  obtain ⟨c₀, al, key, ks⟩ := c
  have hk : key = keyOf c₀.t := h.key_eq
  subst hk
  rfl

/-- Narrowing the scope of a table-keyed context keeps its keying. -/
theorem ScopedCtx.TableKeyed.withAllowed {c : ScopedCtx} (h : c.TableKeyed)
    (allowed : Call F → Prop) : ScopedCtx.TableKeyed { c with allowed := allowed } :=
  ⟨h.key_eq⟩

open Classical in
/-- **The keying that knows the addresses `res` resolve**: the table's on them, `unresolvedKey`
elsewhere. -/
noncomputable def resKey (t : Ix.Kernel.RoleTable) (res : _root_.Address → Prop)
    (a : _root_.Address) : KKey :=
  if res a then keyOf t a else unresolvedKey

theorem resKey_of_res {t : Ix.Kernel.RoleTable} {res : _root_.Address → Prop}
    {a : _root_.Address} (h : res a) : resKey t res a = keyOf t a := by
  simp [resKey, h]

theorem resKey_of_not_res {t : Ix.Kernel.RoleTable} {res : _root_.Address → Prop}
    {a : _root_.Address} (h : ¬ res a) : resKey t res a = unresolvedKey := by
  simp [resKey, h]

theorem res_of_resKey_ne {t : Ix.Kernel.RoleTable} {res : _root_.Address → Prop}
    {a : _root_.Address} (h : resKey t res a ≠ unresolvedKey) : res a := by
  by_contra hn
  exact h (resKey_of_not_res hn)

theorem resKey_spec (t : Ix.Kernel.RoleTable) (res : _root_.Address → Prop)
    (a : _root_.Address) : resKey t res a = keyOf t a ∨ resKey t res a = unresolvedKey := by
  by_cases h : res a
  · exact .inl (resKey_of_res h)
  · exact .inr (resKey_of_not_res h)

/-- **What a context over the prefix `pre` resolves**: an address whose key the context's
environment stores, and the marker of an address whose key `pre` stores. The second clause is
the projection permission (`ProjPermitted`): it is given at the addresses `pre` stores. -/
def Ctx.resolvesOver (c : Ctx) (pre : Ix.Kernel.Env .anon) (a : _root_.Address) : Prop :=
  (∃ ci, c.env.find? (keyOf c.t a) = some ci) ∨
    ∃ y, a = projMarker y ∧ ∃ ci, pre.find? (keyOf c.t y) = some ci

/-- **The context of a stage over a prefix**: the environment of `c` is the prefix `pre` with
the constants the stage has stored so far. The addresses that resolve are those whose key the
environment stores; a projection is permitted at the addresses `pre` stores, so not at a constant
the stage adds; no call is excluded. A term is represented under it only when every constant it
names is stored and every structure it projects at is one of the prefix. -/
noncomputable def Ctx.stagedOver (c : Ctx) (pre : Ix.Kernel.Env .anon) : ScopedCtx :=
  { toCtx := c, allowed := fun _ => True,
    key := resKey c.t (c.resolvesOver pre),
    key_spec := resKey_spec _ _ }

theorem Ctx.stagedOver_toCtx (c : Ctx) (pre : Ix.Kernel.Env .anon) :
    (c.stagedOver pre).toCtx = c := rfl

theorem Ctx.stagedOver_κ (c : Ctx) (pre : Ix.Kernel.Env .anon) :
    (c.stagedOver pre).κ = resKey c.t (c.resolvesOver pre) := rfl

/-- A key the environment of a stage stores resolves, as the table keys it. -/
theorem Ctx.stagedOver_key_of_find {c : Ctx} {pre : Ix.Kernel.Env .anon} {a : _root_.Address}
    {ci : Ix.Kernel.ConstantInfo .anon} (h : c.env.find? (keyOf c.t a) = some ci) :
    (c.stagedOver pre).κ a = keyOf c.t a := by
  rw [Ctx.stagedOver_κ]
  exact resKey_of_res (Or.inl ⟨ci, h⟩)

/-- An address a stage resolves, one a record can have, has its key stored. -/
theorem Ctx.stagedOver_key_ne {c : Ctx} {pre : Ix.Kernel.Env .anon} {a : _root_.Address}
    (h : (c.stagedOver pre).κ a ≠ unresolvedKey) (hm : ¬ IsProjMarker a) :
    ∃ ci, c.env.find? (keyOf c.t a) = some ci := by
  rw [Ctx.stagedOver_κ] at h
  rcases res_of_resKey_ne h with hs | ⟨y, hy, -⟩
  · exact hs
  · exact (hm ⟨y, hy⟩).elim

/-- **The context of a prefix**: the stage over the prefix that has stored nothing. The
addresses that resolve are those whose key the environment stores, a projection is permitted at
each of them, and no call is excluded. A term is represented under it only when every constant
it names is stored. -/
noncomputable def Ctx.stored (c : Ctx) : ScopedCtx := c.stagedOver c.env

theorem Ctx.stored_toCtx (c : Ctx) : c.stored.toCtx = c := rfl

theorem Ctx.stored_κ (c : Ctx) : c.stored.κ = resKey c.t (c.resolvesOver c.env) := rfl

/-- An address a prefix resolves, one a record can have, has its key stored. -/
theorem Ctx.stored_key_ne {c : Ctx} {a : _root_.Address}
    (h : c.stored.κ a ≠ unresolvedKey) (hm : ¬ IsProjMarker a) :
    ∃ ci, c.env.find? (keyOf c.t a) = some ci :=
  Ctx.stagedOver_key_ne (pre := c.env) h hm

theorem Ctx.stored_key_of_find {c : Ctx} {a : _root_.Address} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : c.env.find? (keyOf c.t a) = some ci) : c.stored.κ a = keyOf c.t a :=
  Ctx.stagedOver_key_of_find (pre := c.env) h

/-! ## Projection permission under the three keyings

`ProjPermitted` (`Rep.lean`) under the table's keying, under a prefix's and under a stage's. -/

/-- **Under the table's keying a projection is permitted at every address**, by instance: every
key resolves. -/
theorem projPermitted_keyOf (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    ProjPermitted (keyOf t) a := inferInstance

/-- A table-keyed context permits a projection at every address. -/
theorem ScopedCtx.projPermitted_of_tableKeyed (c : ScopedCtx) [h : c.TableKeyed]
    (a : _root_.Address) : ProjPermitted c.κ a := by
  rw [ScopedCtx.κ_eq c]
  exact inferInstance

/-- **The keying of a stage permits a projection at an address the prefix stores.** -/
theorem Ctx.stagedOver_projPermitted_of_find {c : Ctx} {pre : Ix.Kernel.Env .anon}
    {a : _root_.Address} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : pre.find? (keyOf c.t a) = some ci) : ProjPermitted (c.stagedOver pre).κ a := by
  have e : (c.stagedOver pre).κ (projMarker a) = keyOf c.t (projMarker a) := by
    rw [Ctx.stagedOver_κ]
    exact resKey_of_res (Or.inr ⟨a, rfl, ci, h⟩)
  exact ⟨by rw [e]; exact Resolved.ne⟩

/-- **Where the keying of a stage permits a projection**: at an address the prefix stores, or
at one whose marker has a stored key. -/
theorem Ctx.stagedOver_projPermitted_iff {c : Ctx} {pre : Ix.Kernel.Env .anon}
    {a : _root_.Address} :
    ProjPermitted (c.stagedOver pre).κ a ↔
      (∃ ci, pre.find? (keyOf c.t a) = some ci) ∨
        ∃ ci, c.env.find? (keyOf c.t (projMarker a)) = some ci := by
  constructor
  · intro h
    have h' : resKey c.t (c.resolvesOver pre) (projMarker a) ≠ unresolvedKey := h.ne
    rcases res_of_resKey_ne h' with hs | ⟨y, hy, hpre⟩
    · exact Or.inr hs
    · rw [projMarker_injective hy]
      exact Or.inl hpre
  · intro h
    rcases h with ⟨ci, hci⟩ | ⟨ci, hci⟩
    · exact Ctx.stagedOver_projPermitted_of_find hci
    · have e : (c.stagedOver pre).κ (projMarker a) = keyOf c.t (projMarker a) :=
        Ctx.stagedOver_key_of_find hci
      exact ⟨by rw [e]; exact Resolved.ne⟩

/-- **The keying of a stage permits no projection at an address the prefix does not store**
and whose marker has no stored key: so not at a constant the stage adds. -/
theorem Ctx.stagedOver_not_projPermitted {c : Ctx} {pre : Ix.Kernel.Env .anon}
    {a : _root_.Address} (hpre : pre.find? (keyOf c.t a) = none)
    (hm : c.env.find? (keyOf c.t (projMarker a)) = none) :
    ¬ ProjPermitted (c.stagedOver pre).κ a := by
  intro h
  rcases Ctx.stagedOver_projPermitted_iff.mp h with ⟨ci, hci⟩ | ⟨ci, hci⟩
  · rw [hpre] at hci
    cases hci
  · rw [hm] at hci
    cases hci

/-- **The keying of a prefix permits a projection at a stored address.** -/
theorem Ctx.stored_projPermitted_of_find {c : Ctx} {a : _root_.Address}
    {ci : Ix.Kernel.ConstantInfo .anon} (h : c.env.find? (keyOf c.t a) = some ci) :
    ProjPermitted c.stored.κ a :=
  Ctx.stagedOver_projPermitted_of_find (pre := c.env) h

/-- **The keying of a prefix permits a projection exactly at the stored addresses**, for an
address whose marker has no stored key. -/
theorem Ctx.stored_projPermitted_iff {c : Ctx} {a : _root_.Address}
    (hm : c.env.find? (keyOf c.t (projMarker a)) = none) :
    ProjPermitted c.stored.κ a ↔ ∃ ci, c.env.find? (keyOf c.t a) = some ci := by
  constructor
  · intro h
    rcases (Ctx.stagedOver_projPermitted_iff (pre := c.env)).mp h with hs | ⟨ci, hci⟩
    · exact hs
    · rw [hm] at hci
      cases hci
  · intro h
    obtain ⟨ci, hci⟩ := h
    exact Ctx.stored_projPermitted_of_find hci

/-! ## The role context -/

abbrev rcEnum : String := "KernelRoles::RoleCtxNode"
abbrev rtEnum : String := "KernelRoles::RoleTableNode"
abbrev roleAddrMapEnum : String := Obs.Names.«KernelRoles::RoleMap<&[Field; 32]>»
abbrev roleEvMapEnum : String :=
  Obs.Names.«KernelRoles::RoleMap<&Lists::Node<KernelRoles::RoleEvidence>>»
abbrev addrMapEnum : String := Obs.Names.«RBTreeMap::RBTreeMap<Field>»
abbrev evEnum : String := "KernelRoles::RoleEvidence"
abbrev evListEnum : String := Obs.Names.«Lists::Node<KernelRoles::RoleEvidence>»

/-- **Every entry of a role map satisfies `P`** (`KernelRoles::RoleMap<V>`: a search tree held
by value, `Node(color, key, value, &left, &right)`). Only the entries are constrained: a lookup
that finds a key returns a value its entry satisfies, all the soundness of a lookup reads. -/
inductive RoleMapAll (en : String) (P : Heap F → F → SourceValue F → Prop) (h : Heap F) :
    SourceValue F → Prop where
  | nil : RoleMapAll en P h (.construct en "Nil" [])
  | node {c key : F} {v lp rp lv rv : SourceValue F}
      (hP : P h key v) (hl : loadValue h lp = .ok lv) (hr : loadValue h rp = .ok rv)
      (rl : RoleMapAll en P h lv) (rr : RoleMapAll en P h rv) :
      RoleMapAll en P h (.construct en "Node" [.field c, .field key, v, lp, rp])

/-- **Every entry of an address-keyed map satisfies `P`** (`RBTreeMap::RBTreeMap<V>`, held by
value, `Node(color, &key, value, &left, &right)`), as `RoleMapAll`. -/
inductive AddrMapAll (en : String) (P : Heap F → Bytes.Address → SourceValue F → Prop)
    (h : Heap F) : SourceValue F → Prop where
  | nil : AddrMapAll en P h (.construct en "Nil" [])
  | node {c : F} {kp v lp rp lv rv : SourceValue F} {a : Bytes.Address}
      (hk : Bytes.RepAddressRef addrTy h a kp) (hP : P h a v)
      (hl : loadValue h lp = .ok lv) (hr : loadValue h rp = .ok rv)
      (rl : AddrMapAll en P h lv) (rr : AddrMapAll en P h rv) :
      AddrMapAll en P h (.construct en "Node" [.field c, kp, v, lp, rp])

/-- A role's number in IxVM: its index in `Role.all` (the binding section's role byte). -/
abbrev roleNum (r : Ix.Kernel.Role) : F := (r.idx : F)

/-- An entry of the role → address map: `t` binds the role to the address. -/
def BoundEntry (t : Ix.Kernel.RoleTable) (h : Heap F) (key : F) (v : SourceValue F) : Prop :=
  ∃ (r : Ix.Kernel.Role) (a : Bytes.Address), key = roleNum r ∧
    Bytes.RepAddressRef addrTy h a v ∧ t.addressOf? r = some (ixAddr a)

/-- An entry of the address → role map: the role's number plus one, and `t` binds it there. -/
def IndexEntry (t : Ix.Kernel.RoleTable) (h : Heap F) (a : Bytes.Address) (v : SourceValue F) :
    Prop :=
  ∃ r : Ix.Kernel.Role, v = .field (roleNum r + 1) ∧ t.addressOf? r = some (ixAddr a)

/-- One evidence entry (`KernelRoles::RoleEvidence`). -/
def EvRep (h : Heap F) (e : Ix.Kernel.Evidence _root_.Address) (v : SourceValue F) : Prop :=
  (e = .defeq ∧ v = .construct evEnum "Defeq" []) ∨
    ∃ (a : Bytes.Address) (p : SourceValue F), e = .proof (ixAddr a) ∧
      v = .construct evEnum "Proof" [p] ∧ Bytes.RepAddressRef addrTy h a p

/-- An entry of the role → evidence map: the table's evidence of the role, one for one. -/
def EvidenceEntry (t : Ix.Kernel.RoleTable) (h : Heap F) (key : F) (v : SourceValue F) : Prop :=
  ∃ (r : Ix.Kernel.Role) (es : Array (Ix.Kernel.Evidence _root_.Address)),
    key = roleNum r ∧ (r, es) ∈ t.evidence.toList ∧ RepList evListEnum EvRep h es.toList v

/-- **The role table `t`** (`KernelRoles::RoleTable`): every entry of its maps is `t`'s. -/
def TableRep (t : Ix.Kernel.RoleTable) (h : Heap F) (tbl : SourceValue F) : Prop :=
  ∃ bp byRole byAddr ev, loadValue h tbl = .ok (.construct rtEnum "Mk" [bp, byRole, byAddr, ev]) ∧
    RoleMapAll roleAddrMapEnum (BoundEntry t) h byRole ∧
    AddrMapAll addrMapEnum (IndexEntry t) h byAddr ∧
    RoleMapAll roleEvMapEnum (EvidenceEntry t) h ev

/-- **The role context `rc` reads the table `t` at the group limit `lim`**
(`KernelRoles::RoleCtx`: a validating context `Mk(table, group limit, axioms)`, whose limit is
`lim` and below `2^32`, or an assuming one `Assumed(table, axioms)`, at `lim = none`). The
limit decides which roles are in force (`Ctx.inForce`). -/
def RCRep (t : Ix.Kernel.RoleTable) (lim : Option Nat) (h : Heap F) (rc : SourceValue F) : Prop :=
  ∃ tbl ax node, loadValue h rc = .ok node ∧
    ((∃ n : Nat, lim = some n ∧ n < 4294967296 ∧
        node = .construct rcEnum "Mk" [tbl, .field (n : F), ax]) ∨
      (lim = none ∧ node = .construct rcEnum "Assumed" [tbl, ax])) ∧
    TableRep t h tbl

/-! ## The context list -/

/-- **The context list is a segment of the ghost context** ending at depth `d` (module
docstring). -/
inductive TypesRep (κ : _root_.Address → KKey) (Γ : Nat → KExpr) (h : Heap F) :
    Nat → SourceValue F → Prop where
  | nil {d addr : Nat} (cell : h[addr]? = some (.construct kexprListEnum "Nil" [])) :
      TypesRep κ Γ h d (.ptr (.enum kexprListEnum) addr)
  | cons {d addr : Nat} {tp rest : SourceValue F}
      (cell : h[addr]? = some (.construct kexprListEnum "Cons" [tp, rest]))
      (rt : Tm κ d Γ h 0 (Γ d) tp) (rr : TypesRep κ Γ h d rest) :
      TypesRep κ Γ h (d + 1) (.ptr (.enum kexprListEnum) addr)

/-- **The ghost context is scoped**: the type of the opened variable `j` mentions only the
variables opened before it (`Expr.wscopedB j`). Opening a binder with a represented domain keeps
it. With it, a term represented at depth `d` is scoped at `d`, which moving a derivation to
another depth (`Rules.Transport`: `DefEq.lift`, `Infer.lift`, `Red.lift`) requires. -/
def GhostScoped (Γ : Nat → KExpr) (d : Nat) : Prop := ∀ j, j < d → (Γ j).wscopedB j = true

/-! ## The environment the core reads -/

/-- The domain of the `n`-th binder of a `∀`-telescope (its loose bound variables are the
binders before it). -/
def piDomAt : Nat → KExpr → Option KExpr
  | 0, .forallE ty _ _ => some ty
  | n + 1, .forallE _ b _ => piDomAt n b
  | _, _ => none

/-- **A role equation's statement** (`Ix.Kernel.Equation.statement`), the `i`-th of the role's
specification, for a definition's equations (`Spec.eqns`). The operations' certificates
(`Spec.ops`) are checked by the fold's own procedure and carry no statement here. -/
def roleStatement (r : Ix.Kernel.Role) (i : Nat) : Option KExpr :=
  match (Ix.Kernel.Role.spec (md := .anon)) r with
  | .eqns _ _ eqs => (eqs[i]?).map Ix.Kernel.Equation.statement
  | _ => none

/-- The table binds the role. -/
abbrev Ctx.binds (c : Ctx) (r : Ix.Kernel.Role) : Prop := (c.t.addressOf? r).isSome

/-- **The role is in force**: the table binds it and its group (`Ix.SpecDigest.groupOf`, the
validation schedule the circuit's `role_group` renders) is below the context's limit. A role
lookup of the circuit succeeds only for a role in force; during the validation of a group the
roles of that group and later ones are bound but not in force (nor installed). -/
def Ctx.inForce (c : Ctx) (r : Ix.Kernel.Role) : Prop :=
  c.binds r ∧ ∀ n, c.lim = some n → Ix.SpecDigest.groupOf r < n

abbrev ScopedCtx.binds (c : ScopedCtx) (r : Ix.Kernel.Role) : Prop := (c.t.addressOf? r).isSome

abbrev ScopedCtx.inForce (c : ScopedCtx) (r : Ix.Kernel.Role) : Prop :=
  c.binds r ∧ ∀ n, c.lim = some n → Ix.SpecDigest.groupOf r < n

/-- **A recursor key is non-K at its record in `E`**: the key is an unroled address `.id a`
whose exact record in `E` is a recursor projection into a block in `E` with `rc.k = false`.
Such a recursor never loads with `kf = .field 1` (`recHead_of_getCI`), so K-rescue never fires
at it. -/
def RecNotKAt (E : Ixon.Env) (k : KKey) : Prop :=
  ∃ (a : _root_.Address) (lc0 lcb : Ixon.LazyConstant) (c0 cb : Ixon.Constant)
      (p : Ixon.RecursorProj) (rs : Array Ixon.MutConst) (rc : Ixon.Recursor),
    k = .id a ∧
    E.consts.get? a = some lc0 ∧ Ixon.deConstantExact lc0.rawBytes = .ok c0 ∧ c0.info = .rPrj p ∧
    E.consts.get? p.block = some lcb ∧ Ixon.deConstantExact lcb.rawBytes = .ok cb ∧
      cb.info = .muts rs ∧ rs[p.idx.toNat]? = some (.recr rc) ∧ rc.k = false

/-- **Either a recursor's rules' constructors build its major inductive, or the recursor is
non-K at its record in `E`** (`RecNotKAt`). Native and basis recursors satisfy the left arm
(which K-rescue reads); modeled family recursors are non-K and unroled, satisfying the right
arm. -/
def RuleCtorHeadFact (E : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ k cv mI rP rls,
    env.find? k = some (.recInfo cv mI rP rls) →
    (∀ rl cvj nP nF T us, rl ∈ rls →
      env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
      (piDomAt mI cv.type).map (·.getAppFn) = some (.const T us) →
      ∃ tus, (Ix.Kernel.Expr.piResult cvj.type).getAppFn = .const T tus) ∨
    RecNotKAt E k

/-- The canonical kernel expression for a signed integer: `Int.ofNat n` or `Int.negSucc n`
at a `Nat` literal. -/
def intLitExpr : Int → KExpr
  | .ofNat n => .app (.const (.role .intOfNat) []) (.lit (.natVal n))
  | .negSucc n => .app (.const (.role .intNegSucc) []) (.lit (.natVal n))

/-- **Certified primitive reductions from validated equation groups (`g ≥ 46`)**: once any
equation-specified role is in force (only after group 76 raises the limit past 46), the
constructor anchors are stored and each accelerated equation-specified operation reduces
literal arguments to its certified result at every depth. -/
structure PrimEqnEnv (env : Ix.Kernel.Env .anon) : Prop where
  intOfNatStored : ∃ ci, env.find? (.role .intOfNat) = some ci
  intNegSuccStored : ∃ ci, env.find? (.role .intNegSucc) = some ci
  intOpStored : ∀ r : Ix.Kernel.Role,
    r ∈ [.intNeg, .intNatAbs, .intAdd, .intSub, .intMul, .intEdiv, .intEmod, .intPow, .intBmod, .intBdiv] →
    ∃ ci, env.find? (.role r) = some ci
  intNeg : ∀ d (x : Int),
    Red env d (.app (.const (.role .intNeg) []) (intLitExpr x)) (intLitExpr (-x))
  intNatAbs : ∀ d (x : Int),
    Red env d (.app (.const (.role .intNatAbs) []) (intLitExpr x)) (.lit (.natVal x.natAbs))
  intAdd : ∀ d (x y : Int),
    Red env d (.app (.app (.const (.role .intAdd) []) (intLitExpr x)) (intLitExpr y))
      (intLitExpr (x + y))
  intSub : ∀ d (x y : Int),
    Red env d (.app (.app (.const (.role .intSub) []) (intLitExpr x)) (intLitExpr y))
      (intLitExpr (x - y))
  intMul : ∀ d (x y : Int),
    Red env d (.app (.app (.const (.role .intMul) []) (intLitExpr x)) (intLitExpr y))
      (intLitExpr (x * y))
  intEdiv : ∀ d (x y : Int),
    Red env d (.app (.app (.const (.role .intEdiv) []) (intLitExpr x)) (intLitExpr y))
      (intLitExpr (x.ediv y))
  intEmod : ∀ d (x y : Int),
    Red env d (.app (.app (.const (.role .intEmod) []) (intLitExpr x)) (intLitExpr y))
      (intLitExpr (x.emod y))
  intPow : ∀ d (x : Int) (n : Nat), n ≤ 2 ^ 24 →
    Red env d (.app (.app (.const (.role .intPow) []) (intLitExpr x)) (.lit (.natVal n)))
      (intLitExpr (x ^ n))
  intBmod : ∀ d (x : Int) (m : Nat),
    Red env d (.app (.app (.const (.role .intBmod) []) (intLitExpr x)) (.lit (.natVal m)))
      (intLitExpr (x.bmod m))
  intBdiv : ∀ d (x : Int) (m : Nat),
    Red env d (.app (.app (.const (.role .intBdiv) []) (intLitExpr x)) (.lit (.natVal m)))
      (intLitExpr (x.bdiv m))
  strOpStored : ∀ r : Ix.Kernel.Role,
    r ∈ [.stringUtf8ByteSize, .stringBack, .stringToByteArray, .stringDecEq, .stringAppend,
      .charUtf8Size] →
    ∃ ci, env.find? (.role r) = some ci
  charOfNatStored : ∃ ci, env.find? (.role .charOfNat) = some ci
  byteArrayEmptyStored : ∃ ci, env.find? (.role .byteArrayEmpty) = some ci
  stringStored : ∃ ci, env.find? (.role .string) = some ci
  eqStored : ∃ ci, env.find? (.role .eq) = some ci
  eqReflStored : ∃ ci, env.find? (.role .eqRefl) = some ci
  decidableIsTrueStored : ∃ ci, env.find? (.role .decidableIsTrue) = some ci
  charUtf8Size : ∀ d (c : Char),
    Red env d
      (.app (.const (.role .charUtf8Size) []) (.app (.const (.role .charOfNat) []) (.lit (.natVal c.toNat))))
      (.lit (.natVal c.utf8Size))
  strUtf8ByteSize : ∀ d (s : String),
    Red env d (.app (.const (.role .stringUtf8ByteSize) []) (.lit (.strVal s)))
      (.lit (.natVal s.utf8ByteSize))
  strBack : ∀ d (s : String),
    Red env d (.app (.const (.role .stringBack) []) (.lit (.strVal s)))
      (.app (.const (.role .charOfNat) []) (.lit (.natVal (s.toList.getLastD 'A').toNat)))
  strToByteArrayEmpty : ∀ d,
    Red env d (.app (.const (.role .stringToByteArray) []) (.lit (.strVal "")))
      (.const (.role .byteArrayEmpty) [])
  strDecEqRefl : ∀ d (s : String),
    Red env d (.app (.app (.const (.role .stringDecEq) []) (.lit (.strVal s))) (.lit (.strVal s)))
      (.app (.app (.const (.role .decidableIsTrue) [])
        (.app (.app (.app (.const (.role .eq) [.succ .zero]) (.const (.role .string) []))
          (.lit (.strVal s))) (.lit (.strVal s))))
        (.app (.app (.const (.role .eqRefl) [.succ .zero]) (.const (.role .string) []))
          (.lit (.strVal s))))
  strAppend : ∀ d (s₁ s₂ : String),
    Red env d (.app (.app (.const (.role .stringAppend) []) (.lit (.strVal s₁))) (.lit (.strVal s₂)))
      (.lit (.strVal (s₁ ++ s₂)))
  bitVecOpStored : ∀ r : Ix.Kernel.Role, r ∈ [.bitVecToNat, .bitVecUlt] →
    ∃ ci, env.find? (.role r) = some ci
  bitVecOfNatStored : ∃ ci, env.find? (.role .bitVecOfNat) = some ci
  bitVecToNat : ∀ d (w n : Nat), w ≤ 2 ^ 24 →
    Red env d
      (.app (.app (.const (.role .bitVecToNat) []) (.lit (.natVal w)))
        (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n))))
      (.lit (.natVal (n % 2 ^ w)))
  bitVecUlt : ∀ d (w n₁ n₂ : Nat), w ≤ 2 ^ 24 →
    Red env d
      (.app (.app (.app (.const (.role .bitVecUlt) []) (.lit (.natVal w)))
        (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n₁))))
        (.app (.app (.const (.role .bitVecOfNat) []) (.lit (.natVal w))) (.lit (.natVal n₂))))
      (.const (if n₁ % 2 ^ w < n₂ % 2 ^ w then Ix.Kernel.boolTrueName else Ix.Kernel.boolFalseName) [])

theorem PrimEqnEnv.weaken {env env' : Ix.Kernel.Env .anon} (h : PrimEqnEnv env)
    (hext : Ix.Kernel.EnvExt env env') : PrimEqnEnv env' where
  intOfNatStored := let ⟨ci, hci⟩ := h.intOfNatStored; ⟨ci, hext.find hci⟩
  intNegSuccStored := let ⟨ci, hci⟩ := h.intNegSuccStored; ⟨ci, hext.find hci⟩
  intOpStored := fun r hr => let ⟨ci, hci⟩ := h.intOpStored r hr; ⟨ci, hext.find hci⟩
  intNeg := fun d x => Ix.Kernel.Rules.Red.weaken hext (h.intNeg d x)
  intNatAbs := fun d x => Ix.Kernel.Rules.Red.weaken hext (h.intNatAbs d x)
  intAdd := fun d x y => Ix.Kernel.Rules.Red.weaken hext (h.intAdd d x y)
  intSub := fun d x y => Ix.Kernel.Rules.Red.weaken hext (h.intSub d x y)
  intMul := fun d x y => Ix.Kernel.Rules.Red.weaken hext (h.intMul d x y)
  intEdiv := fun d x y => Ix.Kernel.Rules.Red.weaken hext (h.intEdiv d x y)
  intEmod := fun d x y => Ix.Kernel.Rules.Red.weaken hext (h.intEmod d x y)
  intPow := fun d x n hn => Ix.Kernel.Rules.Red.weaken hext (h.intPow d x n hn)
  intBmod := fun d x m => Ix.Kernel.Rules.Red.weaken hext (h.intBmod d x m)
  intBdiv := fun d x m => Ix.Kernel.Rules.Red.weaken hext (h.intBdiv d x m)
  strOpStored := fun r hr => let ⟨ci, hci⟩ := h.strOpStored r hr; ⟨ci, hext.find hci⟩
  charOfNatStored := let ⟨ci, hci⟩ := h.charOfNatStored; ⟨ci, hext.find hci⟩
  byteArrayEmptyStored := let ⟨ci, hci⟩ := h.byteArrayEmptyStored; ⟨ci, hext.find hci⟩
  stringStored := let ⟨ci, hci⟩ := h.stringStored; ⟨ci, hext.find hci⟩
  eqStored := let ⟨ci, hci⟩ := h.eqStored; ⟨ci, hext.find hci⟩
  eqReflStored := let ⟨ci, hci⟩ := h.eqReflStored; ⟨ci, hext.find hci⟩
  decidableIsTrueStored := let ⟨ci, hci⟩ := h.decidableIsTrueStored; ⟨ci, hext.find hci⟩
  charUtf8Size := fun d c => Ix.Kernel.Rules.Red.weaken hext (h.charUtf8Size d c)
  strUtf8ByteSize := fun d s => Ix.Kernel.Rules.Red.weaken hext (h.strUtf8ByteSize d s)
  strBack := fun d s => Ix.Kernel.Rules.Red.weaken hext (h.strBack d s)
  strToByteArrayEmpty := fun d => Ix.Kernel.Rules.Red.weaken hext (h.strToByteArrayEmpty d)
  strDecEqRefl := fun d s => Ix.Kernel.Rules.Red.weaken hext (h.strDecEqRefl d s)
  strAppend := fun d s₁ s₂ => Ix.Kernel.Rules.Red.weaken hext (h.strAppend d s₁ s₂)
  bitVecOpStored := fun r hr => let ⟨ci, hci⟩ := h.bitVecOpStored r hr; ⟨ci, hext.find hci⟩
  bitVecOfNatStored := let ⟨ci, hci⟩ := h.bitVecOfNatStored; ⟨ci, hext.find hci⟩
  bitVecToNat := fun d w n hw => Ix.Kernel.Rules.Red.weaken hext (h.bitVecToNat d w n hw)
  bitVecUlt := fun d w n₁ n₂ hw => Ix.Kernel.Rules.Red.weaken hext (h.bitVecUlt d w n₁ n₂ hw)

/-- **The environment invariant the core reads** (module docstring's table, with the layer that
establishes each field). -/
structure EnvFacts (c : Ctx) : Prop where
  /-- (Claim, Assembly) The table is well formed: no address bound to two roles (`RoleTable.check`). -/
  tableWf : c.t.wf = true
  /-- (Decls, Assembly) Every stored term the rules read is closed (`Ix.Kernel.StoreClosed`: stored types,
  definition values, rule right-hand sides, projection bodies have no opened variable), as moving
  a derivation to another depth requires. -/
  storeClosed : Ix.Kernel.StoreClosed c.env
  /-- (Decls) `Red.deltaThm`: every stored theorem's value is closed, typed at the theorem's own
  levels in the empty context, against its type, which is a proposition at every assignment. -/
  thmTyped : ∀ n cv value, c.env.find? n = some (.thmInfo cv value) →
    value.hasFvar = false ∧ value.looseBVarsBounded 0 = true ∧
    ∃ vt s u, Infer c.env .full 0 value vt ∧ DefEq c.env 0 vt cv.type ∧
      Infer c.env .full 0 cv.type s ∧ Red c.env 0 s (.sort u) ∧
      ∀ φ, Ix.Kernel.Level.eval φ u = 0
  /-- (Decls, Claim) The `Nat` literal support, when `Nat`, `Nat.zero`, `Nat.succ` are in force. -/
  natLit : c.inForce .nat → c.inForce .natZero → c.inForce .natSucc →
    Ix.Kernel.natLitSupported c.env = true
  /-- (Decls, Claim) The `String` literal support, when `String` is in force (the default table and an
  admitted one bind its literal support with it, `LiteralSupportBound`, in earlier groups). -/
  strLit : c.inForce .string → Ix.Kernel.strLitSupported c.env = true
  /-- (Decls, Claim) Every native `Nat` operation (`Nat.pred` and binary ops) in force is a stored
  definition (`natOpStored`). -/
  natOps : ∀ r, c.inForce r → (.role r : KKey) ∈ Ix.Kernel.natPredName :: Ix.Kernel.Rules.natBinOpNames →
    Ix.Kernel.natOpStored c.env (.role r) = true
  /-- (Decls, Claim) `Nat.add`, in force, has the shape the offset rules read (`natAddTyOk`). -/
  natAdd : c.inForce .natAdd → Ix.Kernel.Rules.natAddTyOk (c.env.find? Ix.Kernel.natAddName) = true
  /-- (Decls, Claim) `Red.eqProof`: `Eq` is stored when it is in force. -/
  eqStored : c.inForce .eq → ∃ ci, c.env.find? Ix.Kernel.eqName = some ci
  /-- (Claim) Certified primitive reductions for equation-specified roles (`g ≥ 46`), once any
  equation-specified role is in force. -/
  primEqn : (∃ r, 46 ≤ Ix.SpecDigest.groupOf r ∧ c.inForce r) → PrimEqnEnv c.env
  /-- (Decls, Assembly) `Red.iota`'s rule lookup: the rules of a stored recursor have distinct constructor
  keys; each fires (`.plain` or `.nested`, never `.inert`) at a stored constructor with the rule's
  parameter count; and when the head of the major premise's domain is the key of an address whose
  record in `c.E` is the inductive projection `ip`, the `j`-th rule is for the `j`-th constructor
  of that member, keyed by its projection record (the pair is read off the record, so a
  mismatch with the pair IxVM hashed is a hashed collision, which `Good` excludes). -/
  recRules : ∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) →
    (rls.map (·.ctor)).Nodup ∧
    (∀ rl ∈ rls, rl.fire ≠ .inert ∧
      ∃ cvj nF, c.env.find? rl.ctor = some (.ctorInfo cvj rl.ctorParams nF)) ∧
    ∀ (p : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj) (us : List KLevel),
      (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
      Ix.Cert.recordAt c.E p = some cm → cm.info = .iPrj ip →
      ∀ j rl, rls[j]? = some rl → rl.ctor = c.κ (cprjAddr ip.block ip.idx.toNat j)
  /-- (Decls) A plain rule's comparands (`recFireComparands`) are the major premise's domain: its
  head is the inductive at the constructor's level parameters, its first `nP` arguments are
  the recursor's leading bound variables (the canonical shape `Expr.recRulePlain` tests), and
  its remaining arguments are the index binders' (the trailing `mI - rP` bound variables, which
  `Red.iota` compares against the major's indices). -/
  recPlain : ∀ k cv mI rP rls rl cvj nP nF, c.env.find? k = some (.recInfo cv mI rP rls) →
    rl ∈ rls → rl.fire = .plain → c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
    ∃ D T, piDomAt mI cv.type = some D ∧
      D.getAppFn = .const T (cvj.levelParams.map .param) ∧
      D.getAppArgs.take nP = (List.range nP).map (fun i => .bvar (mI - 1 - i)) ∧
      D.getAppArgs.drop nP = (List.range (mI - rP)).map fun i => .bvar (mI - rP - 1 - i)
  /-- (Decls) **The store invariant** of the declaration layer's fold (`EnvWF`, `RecCtorsStored`,
  `ProjOkT`; `IxC/Kernel/Model/StoreFold.lean`, `storeFoldRoutes`): nested rules' major-domain
  shape, the stored types' level parameters defined, the projection tables' head data. The
  arity fields below and `recRules`' firing conjunct follow from it
  (`storedFacts_of_invariants`). -/
  store : Ix.Kernel.Open.StoreInv c.env
  /-- (Assembly) **The major inductive of a stored recursor with a rule has a record**: the key heading
  the major premise's domain is that of an address the records `c.E` hold (the reader reads a
  recursor only with its block's records). -/
  recMajorRecord : ∀ k cv mI rP rls (p : _root_.Address) us,
    c.env.find? k = some (.recInfo cv mI rP rls) → rls ≠ [] →
    (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
    ∃ cm, Ix.Cert.recordAt c.E p = some cm
  /-- (Decls) **A rule's constructor builds the recursor's major inductive, or the recursor is
  non-K at its record in `c.E`** (`RuleCtorHeadFact`). -/
  ruleCtorHead : RuleCtorHeadFact c.E c.env
  /-- (Decls, Claim) **The quotient roles in force store the pinned basis**: the annotated basis
  constants (`Ix.Kernel.BasisKind.declsA .quotK`: `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`,
  `Quot.sound`) are stored at their keys once `Quot` is in force (its group admitted, the basis
  installed by the basis route). -/
  quotBasis : c.inForce .quot → ∀ ci ∈ Ix.Kernel.BasisKind.declsA (md := .anon) .quotK,
    c.env.find? ci.name = some ci
  /-- (Decls) **An η-capable stored family has a projection table entry at each of its `etaFields`
  slots**: `Ix.Kernel.Model.EtaTowers` (`IxC/Kernel/Model/StoreCompanions.lean`), which
  `etaTowers_declsRunJ` keeps along every accepted declaration. -/
  etaTowers : Ix.Kernel.Model.EtaTowers c.env
  /-- (Decls) **The type of a full application of an η-constructor**: its io-inferred type reduces to
  the structure at the same levels applied to the parameters (the stored constructor's type is
  the telescope of the parameters and fields ending in the structure at the constructor's level
  parameters applied to the parameter variables), at parameters with no loose bound variable (at a
  loose one it is false, `Decl.etaType_open_false`). From the stored constructor's shape and an
  inversion of io `Infer` along the spine (`Decl.etaType_of_closed_stored`). -/
  etaType : ∀ (T kc : KKey) (cvT cvc : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (nP nF : Nat),
    c.env.find? T = some (.indInfo cvT caps) → caps.eta = true → caps.etaCtor = some kc →
    c.env.find? kc = some (.ctorInfo cvc nP nF) →
    ∀ (d : Nat) (us : List KLevel) (Ss : List KExpr) (ta : KExpr), Ss.length = nP + nF →
      (∀ s ∈ Ss.take nP, s.looseBVarsBounded 0 = true) →
      Infer c.env .io d (Ix.Kernel.Expr.mkAppN (.const kc us) Ss) ta →
      Red c.env d ta (Ix.Kernel.Expr.mkAppN (.const T us) (Ss.take nP))
  /-- (Decls) **A one-rule recursor's η bit is the install's** (`recRuleBits`): `rl.eta` is
  `recRuleEtaOf` (the constructor is the η constructor of a stored η-capable inductive at its
  level parameters, and the recursor is no projection function). -/
  recEta : ∀ k cv mI rP rl, c.env.find? k = some (.recInfo cv mI rP [rl]) →
    rl.eta = Ix.Kernel.recRuleEtaOf c.env.find? k rl.ctor
  /-- (Decls) **An η-capable family's sort datum is its sort's zero-ness**: `caps.sortZ` is the
  zero-ness of the stored type's sort after its `etaParams` parameters (`nativeCapsAt` sets
  `sortZ := zeronessOf p.resSort`, `nativeCaps_sortZ`), so `capsNeverZero` at the use's levels is
  the never-zero test IxVM makes on that sort. -/
  etaSort : ∀ T cvT caps, c.env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    ∃ bs l, cvT.type.stripPis caps.etaParams = some (bs, .sort l) ∧
      caps.sortZ = Ix.Kernel.Level.zeronessOf l
  /-- (Decls) **An η-capable family's η-constructor builds that family**: the head of the
  constructor type's result is `T`. -/
  etaCtorHead : ∀ (T kc : KKey) (cvT : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (nP nF : Nat),
    c.env.find? T = some (.indInfo cvT caps) → caps.eta = true → caps.etaCtor = some kc →
    ∀ cvc, c.env.find? kc = some (.ctorInfo cvc nP nF) →
      ∃ tus, (Ix.Kernel.Expr.piResult cvc.type).getAppFn = .const T tus
  /-- (Decls) **A stored recursor with a rule has a binder for each argument up to the major
  premise** (the walk `Red.iota` reads, `CertsR.toCerts`; a recursor with no rule never fires).
  `Ix.Kernel.Open.recArity_of`. A projection function is such a recursor, so this is also the
  arity premise of `EtaProjCerts.cons`. -/
  recArity : ∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) → ∀ rl ∈ rls,
    (cv.type.stripPis (mI + 1)).isSome = true
  /-- (Decls) **A rule's constructor has a binder for each parameter and field**, at the rule's
  counts (the walks of `Red.iota`, `Red.rescueK`, `Red.rescueEta` over a constructor's
  arguments). `Ix.Kernel.Open.ruleCtor_arity`. -/
  ruleCtorArity : ∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) → ∀ rl ∈ rls,
    ∀ cvj nP nF, c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
      nP = rl.ctorParams ∧ nF = rl.nfields ∧ (cvj.type.stripPis (nP + nF)).isSome = true
  /-- (Decls) **The constructor of a stored projection table's entry has a binder for each parameter
  and field**, at the entry's counts (`Red.proj`). `Ix.Kernel.Open.tableCtor_arity`. -/
  tableCtorArity : ∀ sn i entry, c.env.findProj? sn i = some entry →
    ∀ cvC nP nF, c.env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
      nP = entry.numParams ∧ nF = entry.numFields ∧ (cvC.type.stripPis (nP + nF)).isSome = true
  /-- (Decls) **A unit-like or η-capable family has a binder for each parameter its flag counts**
  (the walks of the unit-like and η rescues over the family's arguments).
  `Ix.Kernel.Open.storedArities_of`'s first half (`EnvWF.indCaps`). -/
  familyArity : ∀ T cvT caps, c.env.find? T = some (.indInfo cvT caps) →
    (caps.unitlike = true → (cvT.type.stripPis caps.unitParams).isSome = true) ∧
      (caps.eta = true → (cvT.type.stripPis caps.etaParams).isSome = true)

/-! ## Heap monotonicity -/

theorem RoleMapAll.mono {en : String} {P : Heap F → F → SourceValue F → Prop}
    (hP : ∀ h₁ h₂ k v, Heap.Extends h₁ h₂ → P h₁ k v → P h₂ k v) {h₁ h₂ : Heap F}
    {v : SourceValue F} (ext : Heap.Extends h₁ h₂) (r : RoleMapAll en P h₁ v) :
    RoleMapAll en P h₂ v := by
  induction r with
  | nil => exact .nil
  | node hp hl hr _ _ ihl ihr => exact .node (hP _ _ _ _ ext hp) (ext.loadValue_eq hl) (ext.loadValue_eq hr) ihl ihr

theorem AddrMapAll.mono {en : String} {P : Heap F → Bytes.Address → SourceValue F → Prop}
    (hP : ∀ h₁ h₂ k v, Heap.Extends h₁ h₂ → P h₁ k v → P h₂ k v) {h₁ h₂ : Heap F}
    {v : SourceValue F} (ext : Heap.Extends h₁ h₂) (r : AddrMapAll en P h₁ v) :
    AddrMapAll en P h₂ v := by
  induction r with
  | nil => exact .nil
  | node hk hp hl hr _ _ ihl ihr =>
    exact .node (Bytes.repAddressRef_heapMono₂ addrTy ext hk) (hP _ _ _ _ ext hp) (ext.loadValue_eq hl)
      (ext.loadValue_eq hr) ihl ihr

theorem evRep_heapMono₂ : HeapMono₂ EvRep := by
  intro h₁ h₂ e v ext r
  rcases r with h0 | ⟨a, p, he, hv, ha⟩
  · exact .inl h0
  · exact .inr ⟨a, p, he, hv, Bytes.repAddressRef_heapMono₂ addrTy ext ha⟩

theorem TableRep.mono {t : Ix.Kernel.RoleTable} {h₁ h₂ : Heap F} {tbl : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : TableRep t h₁ tbl) : TableRep t h₂ tbl := by
  obtain ⟨bp, byRole, byAddr, ev, hl, h1, h2, h3⟩ := r
  refine ⟨bp, byRole, byAddr, ev, ext.loadValue_eq hl, ?_, ?_, ?_⟩
  · refine RoleMapAll.mono ?_ ext h1
    intro _ _ _ _ ext' hb
    obtain ⟨r, a, hk, ha, hb⟩ := hb
    exact ⟨r, a, hk, Bytes.repAddressRef_heapMono₂ addrTy ext' ha, hb⟩
  · exact AddrMapAll.mono (fun _ _ _ _ _ hx => hx) ext h2
  · refine RoleMapAll.mono ?_ ext h3
    intro _ _ _ _ ext' he
    obtain ⟨r, es, hk, hm, hl'⟩ := he
    exact ⟨r, es, hk, hm, repList_heapMono₂ evListEnum evRep_heapMono₂ ext' hl'⟩

theorem RCRep.mono {t : Ix.Kernel.RoleTable} {lim : Option Nat} {h₁ h₂ : Heap F}
    {rc : SourceValue F} (ext : Heap.Extends h₁ h₂) (r : RCRep t lim h₁ rc) :
    RCRep t lim h₂ rc := by
  obtain ⟨tbl, ax, node, hl, hn, ht⟩ := r
  exact ⟨tbl, ax, node, ext.loadValue_eq hl, hn, ht.mono ext⟩

theorem TypesRep.mono {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h₁ h₂ : Heap F} {d : Nat}
    {types : SourceValue F} (ext : Heap.Extends h₁ h₂) (r : TypesRep κ Γ h₁ d types) :
    TypesRep κ Γ h₂ d types := by
  induction r with
  | nil cell => exact .nil (ext.getElem?_eq cell)
  | cons cell rt _ ih => exact .cons (ext.getElem?_eq cell) (Tm.mono ext rt) ih

end IxVM.Refinement.Core
