import Ix.IxVM.Consistency.StatementRel
import Ix.SpecDigest.Schedule

/-! # Consistency against a valid role table

The form of the consistency statement whose premise on the role table is semantic: the
table is *valid*, witnessed by an authentic store of records and an environment made of
those records' readings that has a model. No run of a checker, installer or stream reader
appears in the premise or the conclusion.

## The headline: two runs

`ComposedSpec callsA callsB dA dB` is the public statement, about a typing run and a
`binding` run of the circuit together. For an accepted `binding spec a` claim and an accepted
`check` or `checkEnv` claim in scope whose context names the table address `a`: the two runs
together hashed a collision, or

* the table bytes the binding run hashed at `a` admit as a table `t` (`admitBinding`), and
  `t` binds every role (`AllBound`) and binds the prelude roles at the committed records
  (`PreludePinned`);
* an environment `envT` witnesses `t`'s validity over records the binding run loaded
  (`TableShape`): it is made of those records' readings, contains the kernel's pinned basis
  blocks whole, recursors included, stores `And` and `Bool` as the committed prelude records
  declare them, keeps the constant of every role a model reads and of the two standard
  axioms, and has a model;
* the typing claim's environment extends `envT` by constants that store what the typing
  run's own records declare, covers the seeds, and has a model (`ConsistentReadOver`).

`binding_discharge` proves it from the two halves. At the circuit level the statement is
`CircuitComposed`: `ComposedSpec` of the calls of every accepted proof of `dB` and every
accepted proof of `dA` (`CircuitSound`, nested); `circuitComposed_of_halves` derives it from
the halves. It is about one circuit source: a `binding` proof for one source and a typing
proof for another are not covered, because the halves share `Facts`.

## The two halves, and what is internal

* `BindingSpecOn Facts`: what a `binding` derivation establishes: the table bytes it hashed
  admit, every role is bound, and a `TableWitness` on every group over records it loaded.
* `TypingSpecOn Facts`: what a typing derivation establishes against a `TableWitness` on
  every group: `ConsistentReadOver`.

`TableWitness` is `TableShape`, whose fields are all stated with public definitions, plus
`facts : Facts t G R env`. `Facts` is a parameter standing for what the proof of the typing
half continues from: the invariant its declaration steps preserve and the stored shapes the
checker's native rules read at role keys. Neither is expressible here. `CircuitConsistentOn`
is therefore existential in `Facts`, and it is not the statement to read: a consumer cannot
build a `TableWitness`. `binding_discharge` eliminates `Facts`.

`TableShape` and `TableWitness` are indexed by a set of validation groups, closed under what
its groups need. The public statements use the set of all groups; validity on the 77 groups
is validity on all (`TableShape.of_all_groups`). The index is for the proof of the binding
half, which adds one group at a time (`GroupStep`: from the groups below `g` to those and
`g`). Every group-indexed clause is empty at the empty set, so a witness there says nothing
about the table.

## What each kind of accepted claim gives

* A `binding` claim alone: the public shape of the table's validity (`BindingShapeSpec`,
  `circuitBindingShape_of_halves`).
* A typing claim that validates its table (validator 3), with no `binding` proof: nothing
  under this statement. Its own validations are lazy and do not establish validity.
* A typing claim that assumes its table (validator 4), alone: nothing.
* Either typing claim, together with an accepted `binding` claim for the same table address:
  `ComposedSpec`.

## What a verifier of the two proofs checks, and the view

Both proofs verify for this circuit; the verifier holds the claim bytes behind both digests;
the binding claim's bytes decode to `binding spec a`; the typing claim's bytes decode to a
`check` or `checkEnv` claim that names no user axioms, assumes no leaves, is not a literal
class, and whose context's `binding` is `a`; and, for `checkEnv`, a view holding the tree of
seeds. The verifier need not hold the table bytes: that they admit is concluded. The
specification digests and the validator are not compared: the statement is about one circuit
source, which asserts its own digest.

The collision alternative is relative to the view. With an empty view (possible for `check`)
the conclusion is about the bytes the runs hashed: the record at a seed's address is the one
a run hashed there, and the table is the one the binding run hashed at `a`. A consumer who
wants the conclusion to be about a record, blob or table they hold puts it in the view,
stored under its own hash (the table as the view's `roleBinding`): a run that hashed other
bytes at that address then hashed a collision with the view. Over a view stored under its
own hashes the alternative is a BLAKE3 collision one side of which a run hashed, or a
preimage of the zero address a run hashed or the view holds (`ComposedSpec.selfHashed`).

## Corollaries

`ComposedSpec.seeds_not_false` and `ComposedSpec.seeds_inhabited`: no covered seed's stored
type is `False`, and every covered seed's stored type is inhabited in every model of the
claimed environment. Both follow from the model clause and are relative to the existence of
a `SetTheory`: the first takes one, the second speaks of every model in every one.

## What the circuit must do for the halves to hold

* compare the address bound to each of the 26 prelude roles with the committed one
  (`PreludePinned`); shape validation alone does not, since a re-encoding of a committed
  record validates at another address;
* reject an evidence entry for a role that has no equations (`admitBinding`: with every role
  bound it is the one condition of `Ix.Kernel.RoleTable.check` that the parse of the wire
  format, the per-role evidence counts and kinds, and the validation of each role do not
  cover);
* walk and check, in a `binding` run, the record of each of the fourteen anchors whose
  constant the witness keeps: the ten shape anchors (`kept`) and `Bool.rec`, `And`,
  `And.intro`, `And.rec` (`preludeKept`);
* compare the types of the ten shape anchors structurally, admit an operation that a checked
  constant references, and validate an operation on its value (for `Facts`: the shapes and
  equations the native rules rely on);
* refuse a recursor with a `let` in its first motive's type or its major premise's domain
  (`Reads` at a recursor; see the `Reads` documentation).

## What the statements do not cover

Truth in a standard model. The claimed environment is satisfiable; a model constrains a type
only through the constants stored with it. A type whose recursor is not in the environment is
an arbitrary set with its constructors' values, and a structure whose projection table is not
in the environment has projections with no law. Nothing requires either to be present beyond
the pinned basis blocks, `And` and `Bool`.

Claims with user axioms, assumed leaves, a literal class, `eval`. That the role addresses are
a given toolchain's constants.
-/

universe u

namespace IxVM.Consistency

open IxVM.Refinement
open Aiur.Generic.SourceSemantics (Call)
open Ix (Claim)
open Ix.Kernel.Admission (Binding)

/-! ## Groups, the prelude pin, and the roles whose constants a valid table keeps -/

/-- The roles of validation group `g` (none past the last group). -/
def roleGroup (g : Nat) : List Ix.Kernel.Role :=
  (Ix.SpecDigest.groups[g]?).getD []

/-- The roles group `g` needs outside itself. -/
def groupNeeded (g : Nat) : List Ix.Kernel.Role :=
  Ix.SpecDigest.groupNeeds (roleGroup g)

/-- There are 77 validation groups. -/
theorem groups_length : Ix.SpecDigest.groups.length = 77 := rfl

/-- Past the last group there are no roles: a clause over the roles of a group says nothing
there. -/
theorem roleGroup_eq_nil {g : Nat} (h : Ix.SpecDigest.groups.length ≤ g) : roleGroup g = [] :=
  (congrArg (fun o : Option (List Ix.Kernel.Role) => o.getD [])
    (List.getElem?_eq_none h)).trans rfl

set_option maxRecDepth 8192 in
/-- **Every role lies in its own group**, so a clause over the roles of every group is a
clause over every role. -/
theorem role_mem_roleGroup (r : Ix.Kernel.Role) : r ∈ roleGroup (Ix.SpecDigest.groupOf r) := by
  cases r <;> decide +kernel

/-- Every role's group is one of the 77. -/
theorem groupOf_lt (r : Ix.Kernel.Role) :
    Ix.SpecDigest.groupOf r < Ix.SpecDigest.groups.length := by
  rcases Nat.lt_or_ge (Ix.SpecDigest.groupOf r) Ix.SpecDigest.groups.length with h | h
  · exact h
  · have hm := role_mem_roleGroup r
    rw [roleGroup_eq_nil h] at hm
    cases hm

/-- **The prelude roles** (`Ix.Kernel.preludeShape`): the members of the `Eq`, `Nat`, `PUnit`,
`Empty` and `False` blocks, the quotient package, `And` and `Bool`. -/
def preludeRoles : List Ix.Kernel.Role :=
  Ix.Kernel.preludeShape.flatMap id

/-- There are 26 prelude roles. -/
theorem preludeRoles_length : preludeRoles.length = 26 := rfl

/-- **The prelude is pinned**: `t` binds every prelude role where the committed default
table, as it admits, binds it: at the committed prelude records. A property of the table
and committed data alone. -/
def PreludePinned (t : Ix.Kernel.RoleTable) : Prop :=
  ∃ (b₀ : Binding) (t₀ : Ix.Kernel.RoleTable), Ix.Kernel.Admission.defaultBinding = .ok b₀ ∧
    Ix.Kernel.Admission.admitBinding Address.admissionHash b₀ = .ok t₀ ∧
    ∀ r ∈ preludeRoles, t.addressOf? r = t₀.addressOf? r

/-- The table binds every role. -/
def AllBound (t : Ix.Kernel.RoleTable) : Prop :=
  ∀ r : Ix.Kernel.Role, (t.addressOf? r).isSome = true

/-- A role of the quotient package. -/
def quotRole : Ix.Kernel.Role → Bool
  | .quot | .quotMk | .quotLift | .quotInd | .quotSound => true
  | _ => false

/-- A role whose bound record the circuit walks when it validates the role: a block member
outside the quotient package, an operation, or a definition specified by equations. -/
def walkedRole (r : Ix.Kernel.Role) : Bool :=
  match r.spec (md := .anon) with
  | .block .. => !quotRole r
  | .ops .. | .eqns .. => true
  | _ => false

/-- The anchors whose stored types the kernel's literal and `Bool` rules read. -/
def shapeAnchors : List Ix.Kernel.Role :=
  [.string, .stringOfList, .list, .listNil, .listCons, .char, .charOfNat,
   .bool, .boolTrue, .boolFalse]

/-- **A role whose constant a model reads**: a walked role or a shape anchor. -/
def modelRead (r : Ix.Kernel.Role) : Prop :=
  walkedRole r = true ∨ r ∈ shapeAnchors

/-- The standard axioms that are records of their own (`Quot.sound` is a slot of the pinned
quotient package). A run that assumes its table accepts the record at their addresses
without comparing its type. -/
def standardAxioms : List Ix.Kernel.Role := [.propext, .choice]

/-- **A role whose constant a valid table's environment keeps as its record declares it**
(or as the kernel's pin): a role whose constant a model reads, or a standard axiom. -/
def keptRole (r : Ix.Kernel.Role) : Prop :=
  modelRead r ∨ r ∈ standardAxioms

/-- **The roles at which an axiom record may stand**: the three standard axioms. -/
def axiomRoles : List Ix.Kernel.Role := [.propext, .choice, .quotSound]

/-! ## The witness -/

/-- Every record and blob of `R` is stored under the pure BLAKE3 hash of its bytes. -/
def EnvSelfHashed (R : Ixon.Env) : Prop :=
  (∀ a lc, R.consts.get? a = some lc → Address.blake3Pure lc.rawBytes = a) ∧
  (∀ a bytes, R.blobs.get? a = some bytes → Address.blake3Pure bytes = a)

/-- **`R` is closed under what its records use**: the block of a projection record, and the
record at every constant reference a record uses (`usedRefIdxs`), are records of `R`; and
for every block of `R`, the projection record of each member and of each constructor of an
inductive member is the record of `R` at its address. A run that checks a block hashes
every one of those projection records to compute the member's address. -/
def UsedClosed (R : Ixon.Env) : Prop :=
  (∀ a c, recordOf R a = some c →
    (recordOf R (Ix.Cert.ownerOf a c)).isSome = true ∧
    ∀ i ∈ usedRefIdxs c, ∀ x, c.refs[i]? = some x → (recordOf R x).isSome = true) ∧
  ∀ (B : Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst), recordOf R B = some c →
    c.info = .muts ms → ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m →
      recordOf R (memberAddr B i m) = some (memberProjection B i m) ∧
      ∀ (ind : Ixon.Inductive), m = .indc ind → ∀ (j : Nat), j < ind.ctors.size →
        recordOf R (ctorAddr B i j) = some (constructorProjection B i j)

/-- The committed prelude records, by address: the rows of the committed file whose address
and bytes parse. -/
def committedRows : List (Address × ByteArray) :=
  Ix.Kernel.Reader.RoleData.prelude.toList.filterMap fun row =>
    (Ix.Kernel.Reader.addressOfHex row.1).bind fun a =>
      (bytesOfHex row.2).map fun bytes => (a, bytes)

/-- **`R` agrees with the committed prelude**: at the address of a committed prelude record,
`R` holds that record's bytes or nothing. -/
def AgreesCommitted (R : Ixon.Env) : Prop :=
  ∀ p ∈ committedRows, ∀ lc, R.consts.get? p.1 = some lc → lc.rawBytes = p.2

/-- A pinned basis constant: one of the constants the kernel installs for a basis block. -/
def PinnedBasis (ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ∃ kind : Ix.Kernel.BasisKind, ci ∈ (kind.declsA : List (Ix.Kernel.ConstantInfo .anon))

/-- **`ci` stores what the record at `a` declares**, over a store of records and blobs: the
record declares some `ci₀` (`ReadsIn`) and `ci` is `ci₀` stored (`StoredAs`). An axiom record
is kept only at an address the role table binds a standard axiom's role to (`axiomRoles`). -/
def KeptIn (t : Ix.Kernel.RoleTable) (store : Ix.Kernel.Reader.Store)
    (blob : Address → Option ByteArray) (a : Address) (ci : Ix.Kernel.ConstantInfo .anon) :
    Prop :=
  (∀ c ax, store a = some c → c.info = .axio ax → ∃ r ∈ axiomRoles, keyOf t a = .role r) ∧
    ∃ ci₀, ReadsIn t store blob a ci₀ ∧ StoredAs ci ci₀

/-- A form of the storage clause that no environment with a definition satisfies: it asks
for every reading of every address to be stored. A definition record has one reading for
each reducibility hint, and `StoredAs` compares hints (`storedEveryReading_false`). Kept to
record why `ReadingOf.stored` quantifies over addresses. -/
def StoredEveryReading (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop :=
  ∀ a ci₀, Reads t R a ci₀ →
    ∃ ci, env.find? ci₀.name = some ci ∧ (StoredAs ci ci₀ ∨ PinnedBasis ci)

/-- **Storing every reading is contradictory at a definition**: two readings of one address
that differ in their hint cannot both be stored at one key, unless the key holds a pin. -/
theorem storedEveryReading_false {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {a : Address} {cv : Ix.Kernel.ConstantVal .anon}
    {v : Ix.Kernel.Expr .anon} {hint hint' : Ix.Kernel.ReducibilityHint}
    (hs : StoredEveryReading t R env) (h₁ : Reads t R a (.defnInfo cv v hint))
    (h₂ : Reads t R a (.defnInfo cv v hint')) (hne : hint ≠ hint')
    (hpin : ∀ ci, env.find? cv.name = some ci → ¬ PinnedBasis ci) : False := by
  obtain ⟨ci, hf0, hst⟩ := hs a _ h₁
  obtain ⟨ci', hf0', hst'⟩ := hs a _ h₂
  have hf : env.find? cv.name = some ci := hf0
  have hf' : env.find? cv.name = some ci' := hf0'
  have hcc : ci' = ci := Option.some.inj (hf'.symm.trans hf)
  rw [hcc] at hst'
  rcases hst with hst | hp
  · rcases hst' with hst' | hp'
    · have hm := hst.2
      have hm' := hst'.2
      cases ci with
      | defnInfo _ _ hs' =>
        have e : hs' = hint := hm.2
        have e' : hs' = hint' := hm'.2
        exact hne (e.symm.trans e')
      | axiomInfo _ => exact False.elim hm
      | thmInfo _ _ => exact False.elim hm
      | indInfo _ _ => exact False.elim hm
      | ctorInfo _ _ _ => exact False.elim hm
      | recInfo _ _ _ _ => exact False.elim hm
      | projInfo _ => exact False.elim hm
    · exact hpin ci hf hp'
  · exact hpin ci hf hp

/-- **`env` is made of the readings of `R`'s records**: its names are distinct; every
constant of its claimed sub-environment is a projection table, a pinned basis constant, or
stores what a record of `R` declares; and at the key of every address of `R` that declares
a constant, `env` stores a pin or one reading of that address. -/
structure ReadingOf (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop where
  nodup : (env.consts.map (·.name)).Nodup
  provenance : ∀ ci ∈ (claimedEnv env).consts,
    (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
      ∃ a, KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci
  stored : ∀ a, (∃ ci₀, Reads t R a ci₀) →
    ∃ ci, env.find? (keyOf t a) = some ci ∧
      (PinnedBasis ci ∨ ∃ ci₀, Reads t R a ci₀ ∧ StoredAs ci ci₀)

/-- **The public part of a table's validity on the groups `G`**, with store `R` and
environment `env`.

* `G` is closed under what its groups need, and `t` binds every role of a group of `G`;
* `t` pins the prelude and binds a string literal's whole support;
* `R` is authentic, closed under used references and block members, and agrees with the
  committed prelude records;
* `R` holds no record and no blob at the zero address (`zeroFree`). A run that hashed a
  preimage of the zero address hashed a collision in the sense of the statements, so a
  `binding` run can establish this of the records it loaded; and the proof of the typing
  half needs the store it reads from to be free of one;
* `env` is made of the readings of `R`'s records (`ReadingOf`) and has a model in every set
  theory;
* at every role of `G` that a model reads, and at the two standard axioms, `env` stores a
  pinned basis constant or what the record of `R` at the role's address declares (`kept`).
  So the record is in `R`, it reads, and its literals' blobs are in `R`. The standard axioms
  are among these roles because a run that assumes its table accepts the record at their
  addresses without comparing its type: the witness fixes what that record declares;
* `env` contains every pinned basis block whole, recursors included (`pins`): the ten
  prelude declarations the kernel pins (`Eq`, `Nat`, `PUnit`, `Empty`, `False`, the quotient
  package);
* at every prelude role of `G`, `env` stores a pinned basis constant or what the record at
  the role's address declares (`preludeKept`). The address is the committed one
  (`PreludePinned`) and the record the committed one (`AgreesCommitted`), so the other two
  prelude declarations, `And` and `Bool`, are stored as their committed records declare
  them, recursors included.

Why the pin is by whole blocks and by address. A model constrains an inductive type only
through the constants stored with it, so an environment holding the `False` type without
its recursor, or beside a constructor, would say little or be unsatisfiable. With `pins`
and distinct names, the constant at the key of `False` is the kernel's, and so is its
recursor. With `AgreesCommitted`, a store that holds another block at the committed
`False` address, with a constructor, is not a witness's store; a run that hashes such a
block at that address hashes a collision with the committed images, which every statement
here compares with (`committedFootprint`). -/
structure TableShape (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env)
    (env : Ix.Kernel.Env .anon) : Prop where
  needsClosed : ∀ g, G g → ∀ r ∈ groupNeeded g, G (Ix.SpecDigest.groupOf r)
  bound : ∀ g, G g → ∀ r ∈ roleGroup g, (t.addressOf? r).isSome = true
  prelude : PreludePinned t
  literals : LiteralSupportBound t
  hashed : EnvSelfHashed R
  usedClosed : UsedClosed R
  committed : AgreesCommitted R
  zeroFree : R.consts.get? Ix.HostAdmission.Merkle.padding = none ∧
    R.blobs.get? Ix.HostAdmission.Merkle.padding = none
  kept : ∀ g r a, G g → r ∈ roleGroup g → keptRole r → t.addressOf? r = some a →
    ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci ∧
      (PinnedBasis ci ∨ KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci)
  reading : ReadingOf t R env
  pins : ∀ (kind : Ix.Kernel.BasisKind),
    ∀ ci ∈ (kind.declsA : List (Ix.Kernel.ConstantInfo .anon)), ci ∈ env.consts
  preludeKept : ∀ g r a, G g → r ∈ roleGroup g → r ∈ preludeRoles → t.addressOf? r = some a →
    ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci ∧
      (PinnedBasis ci ∨ KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci)
  model : ∀ (W : Type u) [Ix.Kernel.SetTheory W], Nonempty (Ix.Kernel.Model W (claimedEnv env))

/-- **The table `t` is valid on the groups `G`, witnessed by `R` and `env`**: the public
part (`TableShape`), and `Facts t G R env`, what the typing statement's proof continues from
(see the module docstring). -/
structure TableWitness
    (Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop where
  shape : TableShape.{u} t G R env
  facts : Facts t G R env

/-! ### The group index -/

/-- **Validity on the 77 groups is validity on every group**: past the last group a group
has no roles. -/
theorem TableShape.of_all_groups {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {env : Ix.Kernel.Env .anon}
    (h : TableShape.{u} t (fun g => g < Ix.SpecDigest.groups.length) R env) :
    TableShape.{u} t (fun _ => True) R env := by
  have hlt : ∀ (g : Nat) (r : Ix.Kernel.Role), r ∈ roleGroup g →
      g < Ix.SpecDigest.groups.length := by
    intro g r hr
    rcases Nat.lt_or_ge g Ix.SpecDigest.groups.length with hl | hge
    · exact hl
    · rw [roleGroup_eq_nil hge] at hr
      cases hr
  exact {
    needsClosed := fun _ _ _ _ => trivial
    bound := fun g _ r hr => h.bound g (hlt g r hr) r hr
    prelude := h.prelude
    literals := h.literals
    hashed := h.hashed
    usedClosed := h.usedClosed
    committed := h.committed
    zeroFree := h.zeroFree
    kept := fun g r a _ hr hk ha => h.kept g r a (hlt g r hr) hr hk ha
    reading := h.reading
    pins := h.pins
    preludeKept := fun g r a _ hr hp ha => h.preludeKept g r a (hlt g r hr) hr hp ha
    model := h.model }

/-- `TableShape.of_all_groups` for a witness, given that `Facts` on the 77 groups is `Facts`
on every group. -/
theorem TableWitness.of_all_groups
    {Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hF : Facts t (fun g => g < Ix.SpecDigest.groups.length) R env → Facts t (fun _ => True) R env)
    (h : TableWitness.{u} Facts t (fun g => g < Ix.SpecDigest.groups.length) R env) :
    TableWitness.{u} Facts t (fun _ => True) R env :=
  ⟨h.shape.of_all_groups, hF h.facts⟩

/-- **The step the proof of the binding half iterates** (a statement; nothing here proves
it). `Admits t g R R'` stands for what the run establishes when it admits group `g` of `t`,
its loaded records growing from `R` to `R'`. From a witness on the groups below `g`, the
step gives a witness on those groups and `g`, over the grown store and an environment that
extends the earlier one. The set is fixed as "below `g`, or `g`": the step cannot be
discharged with a witness on the empty set, where every group-indexed clause is empty.
Iterated from `g = 0` it reaches the 77 groups, and `TableWitness.of_all_groups` every group. -/
def GroupStep
    (Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (Admits : Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env → Prop) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env) (env : Ix.Kernel.Env .anon),
    g < Ix.SpecDigest.groups.length → AllBound t →
    TableWitness.{u} Facts t (fun k => k < g) R env → Admits t g R R' →
      ∃ env' : Ix.Kernel.Env .anon, (∀ ci ∈ env.consts, ci ∈ env'.consts) ∧
        TableWitness.{u} Facts t (fun k => k < g ∨ k = g) R' env'

/-! ## The conclusion: the witness's environment, extended -/

/-- The records the run loaded, and behind them the witness's. -/
def storeOver (E₀ R : Ixon.Env) : Ix.Kernel.Reader.Store :=
  fun a => (recordOf E₀ a).orElse fun _ => recordOf R a

/-- The blobs the run loaded, and behind them the witness's. -/
def blobOver (E₀ R : Ixon.Env) : Address → Option ByteArray :=
  fun a => (E₀.blobs.get? a).orElse fun _ => R.blobs.get? a

/-- **The consistency conclusion against a valid table**, with witness store `R` and
environment `envT`. There are records `E₀` the run loaded (`LoadedBy`) and an environment
`env` such that

* `env`'s names are distinct, and `env` contains every constant of `envT`;
* every constant of the claimed sub-environment is a projection table, a pinned basis
  constant, or stores what an authentic record declares (`KeptIn`), the record being one the
  run hashed or one of the witness's store;
* every constant address a seed covers (`SeedConstant`) is stored at its key, as a pinned
  basis constant or as what its own record declares;
* the claimed sub-environment has a model in every set theory. -/
def ConsistentReadOver (calls : List (Call IxVM.F)) (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
    (envT : Ix.Kernel.Env .anon) (seeds : List Address) : Prop :=
  ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon),
    LoadedBy calls E₀ ∧
    (env.consts.map (·.name)).Nodup ∧
    (∀ ci ∈ envT.consts, ci ∈ env.consts) ∧
    (∀ ci ∈ (claimedEnv env).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
        ∃ a, KeptIn t (storeOver E₀ R) (blobOver E₀ R) a ci) ∧
    (∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
      ∃ ci, env.find? (keyOf t a') = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (storeOver E₀ R) (blobOver E₀ R) a' ci)) ∧
    ∀ (W : Type u) [Ix.Kernel.SetTheory W], Nonempty (Ix.Kernel.Model W (claimedEnv env))

/-- **The committed images every statement here compares with**: the committed records and
blobs, and the projection records reconstructed from the committed records. The prelude pin
is by address, so a byte string a run hashes at a pinned address that differs from the
committed one is a collision with these. -/
def committedFootprint : List ByteArray :=
  committedImages ++ committedProjImages

/-- **A collision the run hashed one side of**, with the view's data or `extra`
(`View.HashedCollision`), or with a record or blob of the store `R`: a byte string the run
hashed that differs from what `R` holds at its hash. -/
def CollisionWith (V : View) (extra : List ByteArray) (R : Ixon.Env)
    (calls : List (Call IxVM.F)) : Prop :=
  V.HashedCollision extra calls ∨
  ∃ (x : Address) (held bytes : ByteArray),
    ((∃ lc, R.consts.get? x = some lc ∧ lc.rawBytes = held) ∨ R.blobs.get? x = some held) ∧
    Hashed calls bytes ∧ bytes ≠ held ∧ Address.blake3Pure bytes = x

/-! ## The statements -/

/-- **The typing claims covered**: `check` and `checkEnv` that name no user axioms, assume
no leaves and are not a literal class, whether they validate their role table or assume it. -/
def InScopeTyping : Claim → Prop
  | .check ctx _ asm => ctx.axioms = none ∧ asm = none ∧ ctx.literalClass = false
  | .checkEnv ctx _ asm => ctx.axioms = none ∧ asm = none ∧ ctx.literalClass = false
  | _ => False

/-- **What a typing derivation establishes against a valid table** (one half; see the module
docstring): for every claim byte string whose digest packs to `d` and decodes to a typing
claim in scope, every reader's view of its seeds, every byte string that admits as a table
`t` at the address the claim's context names, and every witness that `t` is valid on every
group: the run hashed a collision (with the claim's bytes, the table's, the committed images,
the view's data or the witness's store), or `ConsistentReadOver`. -/
def TypingSpecOn
    (Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (calls : List (Call IxVM.F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (c : Claim), Claim.de bytes = .ok c →
    packDigest (Address.blake3Pure bytes) = d → InScopeTyping c →
      ∀ (V : View) (seeds : List Address), ClaimSeeds c V seeds →
        ∀ ctx, c.context? = some ctx → ∀ (tb : ByteArray) (t : Ix.Kernel.RoleTable),
          Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨ctx.binding, tb⟩ = .ok t →
          ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon),
            TableWitness.{u} Facts t (fun _ => True) R envT →
              CollisionWith V (bytes :: tb :: committedFootprint) R calls ∨
                ConsistentReadOver.{u} calls t R envT seeds

/-- **What a `binding` derivation establishes** (the other half): for every claim byte string
whose digest packs to `d` and decodes to `binding spec a`, and every view: the run hashed a
collision (with the claim's bytes, the committed images or the view's data), or it hashed
table bytes that admit as a table `t` at `a`, `t` binds every role, and `t` is valid on
every group, witnessed over records the run loaded. -/
def BindingSpecOn
    (Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (calls : List (Call IxVM.F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (spec a : Address), Claim.de bytes = .ok (.binding spec a) →
    packDigest (Address.blake3Pure bytes) = d → ∀ V : View,
      V.HashedCollision (bytes :: committedFootprint) calls ∨
        ∃ (tb : ByteArray) (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
          (env : Ix.Kernel.Env .anon),
          Hashed calls tb ∧
          Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t ∧
          AllBound t ∧ LoadedBy calls R ∧ TableWitness.{u} Facts t (fun _ => True) R env

/-- The two halves hold of the deployed circuit, for some `Facts`. Internal: the statement
to read is `ComposedSpec`, which `binding_discharge` derives from the halves. -/
def CircuitConsistentOn : Prop :=
  ∃ Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop,
    CircuitSound (BindingSpecOn.{u} Facts) ∧ CircuitSound (TypingSpecOn.{u} Facts)

/-- **What a typing derivation and a `binding` derivation establish together** (the public
statement; see the module docstring). For a `binding spec a` claim behind `dB` and a typing
claim in scope behind `dA` whose context names the table address `a`, and every reader's view
of the seeds: the two runs hashed a collision (with either claim's bytes, the committed
images or the view's data), or the binding run hashed table bytes that admit as a table `t`
at `a` binding every role, `t`'s validity on every group is witnessed by an environment
`envT` over records the binding run loaded (`TableShape`: prelude pinned, pinned basis
blocks whole, a model), and the typing run's environment extends `envT`, covers the seeds
and has a model (`ConsistentReadOver`). -/
def ComposedSpec (callsA callsB : List (Call IxVM.F)) (dA dB : Digest) : Prop :=
  ∀ (bytesB : ByteArray) (spec a : Address), Claim.de bytesB = .ok (.binding spec a) →
    packDigest (Address.blake3Pure bytesB) = dB →
    ∀ (bytesA : ByteArray) (cA : Claim), Claim.de bytesA = .ok cA →
      packDigest (Address.blake3Pure bytesA) = dA → InScopeTyping cA →
      ∀ ctx, cA.context? = some ctx → ctx.binding = a →
        ∀ (V : View) (seeds : List Address), ClaimSeeds cA V seeds →
          V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
            ∃ (tb : ByteArray) (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
              (envT : Ix.Kernel.Env .anon),
              Hashed callsB tb ∧
              Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t ∧
              AllBound t ∧ LoadedBy callsB R ∧ TableShape.{u} t (fun _ => True) R envT ∧
              ConsistentReadOver.{u} callsA t R envT seeds

/-! ## Composition -/

/-- What a longer list of calls hashed includes what a part of it hashed. -/
theorem hashed_mono {calls calls' : List (Call IxVM.F)} (hc : ∀ c ∈ calls, c ∈ calls')
    {bytes : ByteArray} (h : Hashed calls bytes) : Hashed calls' bytes := by
  unfold Hashed at h ⊢
  obtain ⟨c, hmem, rest⟩ := h
  exact ⟨c, hc c hmem, rest⟩

/-- The collision alternative is monotone: in the calls, and in the byte strings compared,
where a byte string may also become one the calls hashed. -/
theorem hashedCollision_mono {V : View} {extra extra' : List ByteArray}
    {calls calls' : List (Call IxVM.F)} (he : ∀ x ∈ extra, x ∈ extra' ∨ Hashed calls' x)
    (hc : ∀ c ∈ calls, c ∈ calls') (h : V.HashedCollision extra calls) :
    V.HashedCollision extra' calls' := by
  unfold View.HashedCollision at h ⊢
  rcases h with ⟨x, held, bytes, hheld, hh, hne, hx⟩ | ⟨bytes, hb, hp⟩
  · refine Or.inl ⟨x, held, bytes, ?_, hashed_mono hc hh, hne, hx⟩
    rcases hheld with hpre | ⟨hmem, hx'⟩ | ⟨hh', hx'⟩
    · exact Or.inl hpre
    · rcases he held hmem with h1 | h2
      · exact Or.inr (Or.inl ⟨h1, hx'⟩)
      · exact Or.inr (Or.inr ⟨h2, hx'⟩)
    · exact Or.inr (Or.inr ⟨hashed_mono hc hh', hx'⟩)
  · refine Or.inr ⟨bytes, ?_, hp⟩
    rcases hb with hpre | hh
    · exact Or.inl hpre
    · exact Or.inr (hashed_mono hc hh)

/-- **A binding run discharges a typing run's premise**: the two halves give the composed
statement, for any `Facts`. -/
theorem binding_discharge
    {Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {callsA callsB : List (Call IxVM.F)} {dA dB : Digest}
    (hB : BindingSpecOn.{u} Facts callsB dB) (hA : TypingSpecOn.{u} Facts callsA dA) :
    ComposedSpec.{u} callsA callsB dA dB := by
  unfold ComposedSpec
  intro bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hs
  have hcA : ∀ c ∈ callsA, c ∈ callsA ++ callsB := fun c h => List.mem_append.mpr (Or.inl h)
  have hcB : ∀ c ∈ callsB, c ∈ callsA ++ callsB := fun c h => List.mem_append.mpr (Or.inr h)
  rcases hB bytesB spec a deB dgB V with hcol | ⟨tb, t, R, envT, htb, ht, hall, hload, hw⟩
  · refine Or.inl (hashedCollision_mono (fun x h => ?_) hcB hcol)
    exact Or.inl (List.mem_cons_of_mem _ h)
  · have ht' : Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨ctx.binding, tb⟩ =
        .ok t := by
      rw [hba]
      exact ht
    have heA : ∀ x ∈ bytesA :: tb :: committedFootprint,
        x ∈ bytesA :: bytesB :: committedFootprint ∨ Hashed (callsA ++ callsB) x := by
      intro x h
      rcases List.mem_cons.mp h with h1 | h
      · exact Or.inl (List.mem_cons.mpr (Or.inl h1))
      · rcases List.mem_cons.mp h with h2 | h3
        · refine Or.inr ?_
          rw [h2]
          exact hashed_mono hcB htb
        · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h3))
    rcases hA bytesA cA deA dgA hsc V seeds hs ctx hctx tb t ht' R envT hw with hcol | hok
    · rcases hcol with hcol | ⟨x, held, bytes, hheld, hh, hne, hx⟩
      · exact Or.inl (hashedCollision_mono heA hcA hcol)
      · obtain ⟨hrec, hblob⟩ := hload
        have hR : Hashed callsB held ∧ Address.blake3Pure held = x := by
          rcases hheld with ⟨lc, hl, hlc⟩ | hbl
          · rw [← hlc]
            exact hrec x lc hl
          · exact hblob x held hbl
        refine Or.inl ?_
        unfold View.HashedCollision
        exact Or.inl ⟨x, held, bytes, Or.inr (Or.inr ⟨hashed_mono hcB hR.1, hR.2⟩),
          hashed_mono hcA hh, hne, hx⟩
    · exact Or.inr ⟨tb, t, R, envT, htb, ht, hall, hload, hw.shape, hok⟩

/-! ## The circuit-level statements -/

/-- `CircuitSound` is monotone in what it concludes of a run. -/
theorem circuitSound_mono {P Q : List (Call IxVM.F) → Digest → Prop}
    (hPQ : ∀ calls d, P calls d → Q calls d) (h : CircuitSound P) : CircuitSound Q := by
  unfold CircuitSound at h ⊢
  intro _ _ compiled physical _ cert bits plan wf _ valid len d _ _ _ signed _ erased notin _
    rowsLen memo decodes decoded
  obtain ⟨value, heap, calls, hobs, hrom, hp⟩ :=
    h compiled physical cert bits plan wf valid len d signed erased notin rowsLen memo decodes
      decoded
  exact ⟨value, heap, calls, hobs, hrom, hPQ calls d hp⟩

/-- **What a `binding` derivation establishes, in public terms**: `BindingSpecOn` with the
public part of the witness (`TableShape`) in place of the witness. What an accepted `binding`
claim gives with no typing claim beside it. -/
def BindingShapeSpec (calls : List (Call IxVM.F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (spec a : Address), Claim.de bytes = .ok (.binding spec a) →
    packDigest (Address.blake3Pure bytes) = d → ∀ V : View,
      V.HashedCollision (bytes :: committedFootprint) calls ∨
        ∃ (tb : ByteArray) (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
          (env : Ix.Kernel.Env .anon),
          Hashed calls tb ∧
          Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t ∧
          AllBound t ∧ LoadedBy calls R ∧ TableShape.{u} t (fun _ => True) R env

/-- The binding half gives its public form, for any `Facts`. -/
theorem BindingSpecOn.shape
    {Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {calls : List (Call IxVM.F)} {d : Digest} (h : BindingSpecOn.{u} Facts calls d) :
    BindingShapeSpec.{u} calls d := by
  unfold BindingShapeSpec
  intro bytes spec a hde hd V
  rcases h bytes spec a hde hd V with hcol | ⟨tb, t, R, env, h1, h2, h3, h4, hw⟩
  · exact Or.inl hcol
  · exact Or.inr ⟨tb, t, R, env, h1, h2, h3, h4, hw.shape⟩

/-- **The two-run statement of the circuit** (the public circuit-level statement): for every
accepted proof of a digest `dB` and every accepted proof of a digest `dA`, `ComposedSpec` of
the calls of observed derivations of the two (`CircuitSound`, nested: of the first run, that
of the second run the composed statement holds). One circuit source: both proofs are of it. -/
def CircuitComposed : Prop :=
  CircuitSound fun callsB dB =>
    CircuitSound fun callsA dA => ComposedSpec.{u} callsA callsB dA dB

/-- **The two-run statement follows from the two halves.** -/
theorem circuitComposed_of_halves (h : CircuitConsistentOn.{u}) : CircuitComposed.{u} := by
  obtain ⟨Facts, hB, hA⟩ := h
  unfold CircuitComposed
  refine circuitSound_mono (P := BindingSpecOn.{u} Facts) ?_ hB
  intro callsB dB hb
  show CircuitSound fun callsA dA => ComposedSpec.{u} callsA callsB dA dB
  exact circuitSound_mono (P := TypingSpecOn.{u} Facts)
    (fun _ _ ha => binding_discharge hb ha) hA

/-- **What an accepted `binding` proof alone gives**: the public shape of its table's
validity. -/
theorem circuitBindingShape_of_halves (h : CircuitConsistentOn.{u}) :
    CircuitSound BindingShapeSpec.{u} := by
  obtain ⟨Facts, hB, -⟩ := h
  exact circuitSound_mono (P := BindingSpecOn.{u} Facts) (fun _ _ hb => BindingSpecOn.shape hb)
    hB

/-! ## Corollaries -/

/-- **No covered seed is stored with type `False`**: the claimed environment is consistent,
and every constant address a seed covers is stored at its key with a type other than `False`;
where the constant stores what its record declares, the declared type is not `False` either.
Syntactic: it speaks of the role key of `False` only. `SeedsInhabited` is the semantic form. -/
def SeedsNotFalse (calls : List (Call IxVM.F)) (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
    (seeds : List Address) : Prop :=
  ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon), LoadedBy calls E₀ ∧
    Ix.Kernel.Consistent (claimedEnv env) ∧
    ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
      ∃ ci, env.find? (keyOf t a') = some ci ∧
        ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] ∧
        (PinnedBasis ci ∨
          ∃ ci₀, ReadsIn t (storeOver E₀ R) (blobOver E₀ R) a' ci₀ ∧ StoredAs ci ci₀ ∧
            ci₀.toConstantVal.type ≠ .const Ix.Kernel.falseName [])

/-- **No claimed constant has type `False`**, against a valid table. Relative to the
existence of a set theory `W`: the claimed environment has a model in it. -/
theorem ConsistentReadOver.seeds_not_false (W : Type u) [Ix.Kernel.SetTheory W]
    {calls : List (Call IxVM.F)} {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {seeds : List Address}
    (h : ConsistentReadOver.{u} calls t R envT seeds) : SeedsNotFalse calls t R seeds := by
  unfold SeedsNotFalse
  obtain ⟨E₀, env, hload, -, -, -, hseeds, hmodel⟩ := h
  have hcons : Ix.Kernel.Consistent (claimedEnv env) :=
    Ix.Kernel.consistent_of_model W (hmodel W)
  refine ⟨E₀, env, hload, hcons, fun a ha a' ha' => ?_⟩
  obtain ⟨ci, hfind, hprov⟩ := hseeds a ha a' ha'
  have hci : ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] :=
    fun hf => hcons ci (seed_claimed hfind).1 hf
  refine ⟨ci, hfind, hci, ?_⟩
  rcases hprov with hp | ⟨-, ci₀, hr, hst⟩
  · exact Or.inl hp
  · refine Or.inr ⟨ci₀, hr, hst, fun hf => ?_⟩
    have hann := hst.1.2.2
    rw [hf] at hann
    exact hci hann.const_inv

open Ix.Kernel.SetTheory in
/-- **Every covered seed's stored type is inhabited in every model of the claimed
environment**, so none is refutable there. For each constant address a seed covers, the
constant `ci` stored at its key is a pin or stores what its record declares, and in every
model, at every level assignment, `ci`'s type denotes a set and `ci`'s value is a member of
it. Where `ci` stores what its record declares, that type is an annotation of the declared
one.

Not covered: that the type holds in a standard model (see the module docstring); the
declared type of a seed that is a pinned basis constant, of which only the pin is stored. -/
def SeedsInhabited (calls : List (Call IxVM.F)) (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
    (seeds : List Address) : Prop :=
  ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon), LoadedBy calls E₀ ∧
    (∀ (W : Type u) [Ix.Kernel.SetTheory W],
      Nonempty (Ix.Kernel.Model W (claimedEnv env))) ∧
    ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
      ∃ ci, env.find? (keyOf t a') = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (storeOver E₀ R) (blobOver E₀ R) a' ci) ∧
        ∀ (W : Type u) [Ix.Kernel.SetTheory W] (M : Ix.Kernel.Model W (claimedEnv env))
          (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → W),
          ∃ T, Ix.Kernel.Denotes M.cval (claimedEnv env) φ ρ ci.toConstantVal.type T ∧
            M.cval ci.name φ ∈ˢ T

/-- **Every seed's stored type is inhabited in every model of the claimed environment**
(`Ix.Kernel.Model.mem`). -/
theorem ConsistentReadOver.seeds_inhabited {calls : List (Call IxVM.F)}
    {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {seeds : List Address} (h : ConsistentReadOver.{u} calls t R envT seeds) :
    SeedsInhabited.{u} calls t R seeds := by
  unfold SeedsInhabited
  obtain ⟨E₀, env, hload, -, -, -, hseeds, hmodel⟩ := h
  refine ⟨E₀, env, hload, hmodel, fun a ha a' ha' => ?_⟩
  obtain ⟨ci, hfind, hprov⟩ := hseeds a ha a' ha'
  exact ⟨ci, hfind, hprov, fun W _ M φ ρ => M.mem ci (seed_claimed hfind).1 φ ρ⟩

/-! ### Of the composed statement -/

/-- **The composed conclusion, with `P` of the table, the binding run's store and the
witness's environment**: the binding run hashed table bytes that admit at `a` as a table
binding every role, valid on every group over records the run loaded, and `P` holds.
`ComposedSpec` concludes it with `ConsistentReadOver` for `P`. -/
def ComposedWith (P : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (callsB : List (Call IxVM.F)) (a : Address) : Prop :=
  ∃ (tb : ByteArray) (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon),
    Hashed callsB tb ∧
    Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t ∧
    AllBound t ∧ LoadedBy callsB R ∧ TableShape.{u} t (fun _ => True) R envT ∧ P t R envT

theorem ComposedWith.imp {P Q : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    (hPQ : ∀ t R envT, P t R envT → Q t R envT) {callsB : List (Call IxVM.F)} {a : Address}
    (h : ComposedWith.{u} P callsB a) : ComposedWith.{u} Q callsB a := by
  obtain ⟨tb, t, R, envT, h1, h2, h3, h4, h5, hp⟩ := h
  unfold ComposedWith
  exact ⟨tb, t, R, envT, h1, h2, h3, h4, h5, hPQ t R envT hp⟩

section Composed

variable {callsA callsB : List (Call IxVM.F)} {dA dB : Digest} {bytesB : ByteArray}
  {spec a : Address} {bytesA : ByteArray} {cA : Claim} {ctx : Ix.ClaimContext} {V : View}
  {seeds : List Address}

/-- `ComposedSpec` at a `binding` claim, a typing claim under its table and a view. -/
theorem ComposedSpec.apply (h : ComposedSpec.{u} callsA callsB dA dB)
    (deB : Claim.de bytesB = .ok (.binding spec a))
    (dgB : packDigest (Address.blake3Pure bytesB) = dB) (deA : Claim.de bytesA = .ok cA)
    (dgA : packDigest (Address.blake3Pure bytesA) = dA) (hsc : InScopeTyping cA)
    (hctx : cA.context? = some ctx) (hba : ctx.binding = a) (hs : ClaimSeeds cA V seeds) :
    V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
      ComposedWith.{u} (fun t R envT => ConsistentReadOver.{u} callsA t R envT seeds)
        callsB a :=
  h bytesB spec a deB dgB bytesA cA deA dgA hsc ctx hctx hba V seeds hs

/-- **The composed statement over a view stored under its own hashes**: a BLAKE3 collision
one side of which a run hashed (or a preimage of the zero address a run hashed or the view
holds), or the composed conclusion. -/
theorem ComposedSpec.selfHashed (h : ComposedSpec.{u} callsA callsB dA dB)
    (deB : Claim.de bytesB = .ok (.binding spec a))
    (dgB : packDigest (Address.blake3Pure bytesB) = dB) (deA : Claim.de bytesA = .ok cA)
    (dgA : packDigest (Address.blake3Pure bytesA) = dA) (hsc : InScopeTyping cA)
    (hctx : cA.context? = some ctx) (hba : ctx.binding = a) (hs : ClaimSeeds cA V seeds)
    (hV : SelfHashed V) :
    GenuineCollision V (callsA ++ callsB) ∨
      ComposedWith.{u} (fun t R envT => ConsistentReadOver.{u} callsA t R envT seeds)
        callsB a :=
  (h.apply deB dgB deA dgA hsc hctx hba hs).elim
    (fun hcol => Or.inl (hashedCollision_genuine hV hcol)) Or.inr

/-- **No covered seed is stored with type `False`**, of the composed statement. Relative to
the existence of a set theory `W`. -/
theorem ComposedSpec.seeds_not_false (W : Type u) [Ix.Kernel.SetTheory W]
    (h : ComposedSpec.{u} callsA callsB dA dB)
    (deB : Claim.de bytesB = .ok (.binding spec a))
    (dgB : packDigest (Address.blake3Pure bytesB) = dB) (deA : Claim.de bytesA = .ok cA)
    (dgA : packDigest (Address.blake3Pure bytesA) = dA) (hsc : InScopeTyping cA)
    (hctx : cA.context? = some ctx) (hba : ctx.binding = a) (hs : ClaimSeeds cA V seeds) :
    V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
      ComposedWith.{u} (fun t R _ => SeedsNotFalse callsA t R seeds) callsB a :=
  (h.apply deB dgB deA dgA hsc hctx hba hs).elim Or.inl fun hok =>
    Or.inr (ComposedWith.imp
      (P := fun t R envT => ConsistentReadOver.{u} callsA t R envT seeds)
      (Q := fun t R _ => SeedsNotFalse callsA t R seeds)
      (fun _ _ _ hr => ConsistentReadOver.seeds_not_false W hr) hok)

/-- **Every covered seed's stored type is inhabited in every model of the claimed
environment**, of the composed statement. -/
theorem ComposedSpec.seeds_inhabited (h : ComposedSpec.{u} callsA callsB dA dB)
    (deB : Claim.de bytesB = .ok (.binding spec a))
    (dgB : packDigest (Address.blake3Pure bytesB) = dB) (deA : Claim.de bytesA = .ok cA)
    (dgA : packDigest (Address.blake3Pure bytesA) = dA) (hsc : InScopeTyping cA)
    (hctx : cA.context? = some ctx) (hba : ctx.binding = a) (hs : ClaimSeeds cA V seeds) :
    V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
      ComposedWith.{u} (fun t R _ => SeedsInhabited.{u} callsA t R seeds) callsB a :=
  (h.apply deB dgB deA dgA hsc hctx hba hs).elim Or.inl fun hok =>
    Or.inr (ComposedWith.imp
      (P := fun t R envT => ConsistentReadOver.{u} callsA t R envT seeds)
      (Q := fun t R _ => SeedsInhabited.{u} callsA t R seeds)
      (fun _ _ _ hr => ConsistentReadOver.seeds_inhabited hr) hok)

end Composed

end IxVM.Consistency
