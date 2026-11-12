import IxVMRefinement.Core.Loaded
import IxC.Kernel.Rules.Rel
import IxC.Kernel.Ixon.RoleTable
import IxC.Kernel.Roles
import IxC.Kernel.RoleEquations
import Ix.IxVM.Refinement.Claim

/-! # The context seam: the role context, the context list, and the environment the core reads

The core's functions run under a role context `rc` (`KernelRoles::RoleCtx`) and a context list
`types` (`Lists::List<KExpr>`). They are related to the kernel side by:

* `Ctx`: the records `E` the kernel environment was read from (the collision escape is
  relative to them), the environment `env`, and the role table `t` the run read. The keying of
  addresses is the table's (`keyOf`): an address the table binds to a role `r` is `.role r`,
  any other address `a` is `.id a`, as the kernel reader keys records (`Reader.keyOfAddress`).
* `RCRep t h rc`: `rc` reads the table `t`. Every entry of its three maps (role → address,
  address → role, role → evidence) is `t`'s; a lookup that finds an entry is therefore sound.
  The search order is not constrained (nothing claims a failed lookup).
* `TypesRep κ Γ h d types`: `types` is a segment of the ghost context ending at depth `d`: its
  entry `i` (innermost first) is the type `Γ (d - 1 - i)` of the opened variable `d - 1 - i`,
  represented at the depth that variable was opened at (IxVM lifts it on lookup:
  `KernelInfer::types_lookup`). Trimming outer entries (`ctx_trim`) keeps a segment with the
  same top end.
* `EnvFacts c`: **the environment invariant the core reads** — the L4 ↔ L5/L7 interface. Each
  field names the layer that must establish it.

| Field | What the core reads it for | Established by |
|---|---|---|
| `tableWf` | role keys are a function of addresses (no address bound twice) | L6 (the run admitted `t`), L7 (`t` is `ReadIn`'s) |
| `thmTyped` | `Red.deltaThm`'s premises: a stored theorem's value, closed and typed at its own levels | L5 (each theorem's own check, carried along the fold by `Transport.weaken`) |
| `natLit`, `strLit`, `natOps`, `natAdd` | the native rules' stored-shape guards (`natLitSupported`, `strLitSupported`, `natOpStored`, `natAddTyOk`) | L5 (role constants installed as their specifications), L6 (the table binds them) |
| `eqStored`, `evidence` | `Red.eqProof`: `Eq` is stored; each evidence theorem the table names is stored at its key, its type definitionally equal to the role equation's statement | L5 (evidence theorems checked like any theorem), L6 (the table's evidence matches its roles) |
| `recRules` | `Red.iota`'s rule lookup: a stored recursor's `j`-th rule is for the `j`-th constructor of its major inductive, keyed by that constructor's projection record | L5 (recursor install), L7 (keys from `ReadIn`) |

The loads (`Ingress::get_ci` and the projection loaders) are related to `env` by `LoadFacts`
(`Good.lean`): the L1 ↔ L7 interface. -/

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

/-! ## The context -/

/-- **The context of a run of the core**: the records the environment was read from, the
environment, and the role table the run read. -/
structure Ctx where
  E : Ixon.Env
  env : Ix.Kernel.Env .anon
  t : Ix.Kernel.RoleTable

/-- The keying of addresses: the table's. -/
abbrev Ctx.κ (c : Ctx) : _root_.Address → KKey := keyOf c.t

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

/-- **The role context `rc` reads the table `t`** (`KernelRoles::RoleCtx`: a validating context
`Mk(table, group limit, axioms)` or an assuming one `Assumed(table, axioms)`). The group limit
only restricts which roles are in force (`KernelRoles::role_of`), so it is not constrained. -/
def RCRep (t : Ix.Kernel.RoleTable) (h : Heap F) (rc : SourceValue F) : Prop :=
  ∃ tbl ax node, loadValue h rc = .ok node ∧
    ((∃ lim : F, node = .construct rcEnum "Mk" [tbl, .field lim, ax]) ∨
      node = .construct rcEnum "Assumed" [tbl, ax]) ∧
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

/-- **The environment invariant the core reads** (module docstring's table, with the layer that
establishes each field). -/
structure EnvFacts (c : Ctx) : Prop where
  /-- (L6, L7) The table is well formed: no address bound to two roles (`RoleTable.check`). -/
  tableWf : c.t.wf = true
  /-- (L5) `Red.deltaThm`: every stored theorem's value is closed, typed at the theorem's own
  levels in the empty context, against its type, which is a proposition at every assignment. -/
  thmTyped : ∀ n cv value, c.env.find? n = some (.thmInfo cv value) →
    value.hasFvar = false ∧ value.looseBVarsBounded 0 = true ∧
    ∃ vt s u, Infer c.env .full 0 value vt ∧ DefEq c.env 0 vt cv.type ∧
      Infer c.env .full 0 cv.type s ∧ Red c.env 0 s (.sort u) ∧
      ∀ φ, Ix.Kernel.Level.eval φ u = 0
  /-- (L5, L6) The `Nat` literal support, when the table binds `Nat`, `Nat.zero`, `Nat.succ`. -/
  natLit : c.binds .nat → c.binds .natZero → c.binds .natSucc →
    Ix.Kernel.natLitSupported c.env = true
  /-- (L5, L6) The `String` literal support, when the table binds its roles. -/
  strLit : c.binds .nat → c.binds .natZero → c.binds .natSucc → c.binds .string →
    c.binds .stringOfList → c.binds .char → c.binds .charOfNat → c.binds .list →
    c.binds .listNil → c.binds .listCons → Ix.Kernel.strLitSupported c.env = true
  /-- (L5, L6) Every bound binary `Nat` operation is a stored definition (`natOpStored`). -/
  natOps : ∀ r, c.binds r → (.role r : KKey) ∈ Ix.Kernel.Rules.natBinOpNames →
    Ix.Kernel.natOpStored c.env (.role r) = true
  /-- (L5, L6) The bound `Nat.add` has the shape the offset rules read (`natAddTyOk`). -/
  natAdd : c.binds .natAdd → Ix.Kernel.Rules.natAddTyOk (c.env.find? Ix.Kernel.natAddName) = true
  /-- (L5, L6) `Red.eqProof`: `Eq` is stored when the table binds it. -/
  eqStored : c.binds .eq → ∃ ci, c.env.find? Ix.Kernel.eqName = some ci
  /-- (L5, L6) `Red.eqProof`: each evidence theorem the table names for a definition's equation
  is a stored theorem at its key, whose type is definitionally equal to the equation's
  statement at the theorem's levels. -/
  evidence : ∀ r es i a, (r, es) ∈ c.t.evidence.toList → es[i]? = some (.proof a) →
    ∀ stmt, roleStatement r i = some stmt →
      ∃ cv v, c.env.find? (c.κ a) = some (.thmInfo cv v) ∧ DefEq c.env 0 cv.type stmt
  /-- (L5, L7) `Red.iota`'s rule lookup: the `j`-th rule of a stored recursor is for the `j`-th
  constructor of its major inductive (member `i` of block `b`: the head of the major premise's
  type is that member's key), keyed by the constructor's projection record. -/
  recRules : ∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) →
    ∃ (b : _root_.Address) (i : Nat) (us : List KLevel),
      (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ (iprjAddr b i)) us) ∧
      ∀ j rl, rls[j]? = some rl → rl.ctor = c.κ (cprjAddr b i j)

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
  · exact RoleMapAll.mono (fun _ _ _ _ ext' ⟨r, a, hk, ha, hb⟩ =>
      ⟨r, a, hk, Bytes.repAddressRef_heapMono₂ addrTy ext' ha, hb⟩) ext h1
  · exact AddrMapAll.mono (fun _ _ _ _ _ hx => hx) ext h2
  · exact RoleMapAll.mono (fun _ _ _ _ ext' ⟨r, es, hk, hm, hl'⟩ =>
      ⟨r, es, hk, hm, repList_heapMono₂ evListEnum evRep_heapMono₂ ext' hl'⟩) ext h3

theorem RCRep.mono {t : Ix.Kernel.RoleTable} {h₁ h₂ : Heap F} {rc : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RCRep t h₁ rc) : RCRep t h₂ rc := by
  obtain ⟨tbl, ax, node, hl, hn, ht⟩ := r
  exact ⟨tbl, ax, node, ext.loadValue_eq hl, hn, ht.mono ext⟩

theorem TypesRep.mono {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h₁ h₂ : Heap F} {d : Nat}
    {types : SourceValue F} (ext : Heap.Extends h₁ h₂) (r : TypesRep κ Γ h₁ d types) :
    TypesRep κ Γ h₂ d types := by
  induction r with
  | nil cell => exact .nil (ext.getElem?_eq cell)
  | cons cell rt _ ih => exact .cons (ext.getElem?_eq cell) (Tm.mono ext rt) ih

end IxVM.Refinement.Core
