import Ix.IxVM.Consistency.StatementRel
import Ix.SpecDigest.Schedule

/-! # Consistency against a valid role table

The form of the consistency statement whose premise on the role table is semantic: the
table is *valid*, witnessed by an authentic store of records and an environment made of
those records' readings that has a model. No run of a checker, installer or stream reader
appears in the premise or the conclusion.

* `TableWitness Facts t G R env`: the table `t` is valid on the groups `G`, witnessed by the
  record store `R` and the environment `env`.
* `TypingSpecOn Facts`: what a `check` or `checkEnv` derivation establishes against a valid
  table, whether the claim validates its table or assumes it: the claimed environment
  *extends the witness's environment* by constants that store what the run's own records
  declare, and has a model (`ConsistentReadOver`).
* `BindingSpecOn Facts`: what a `binding` derivation establishes: a witness of the table's
  validity on every group, over records the run hashed.
* `binding_discharge`: the two compose. A typing run and a binding run for the same table
  bytes give the conclusion with no premise on the table beyond its admission as a table.

## What is public and what is not

Every field of `TableWitness` but one is stated with public definitions: the validation
schedule's groups (`Ix.SpecDigest`), the committed default table (for the basis pin), `Reads`
and `StoredAs`, and the kernel's `Model`. The exception is `facts : Facts t G env`. `Facts` is
a parameter standing for what the proof of the typing statement continues from: the invariant
its declaration steps preserve, and the stored shapes the checker's native rules read at role
keys. Neither is expressible here: the first is chosen by the declaration layer's proof, the
second is an interface of the core's proof. The public statement is therefore existential in
it (`CircuitConsistentOn`): some `Facts` makes both `BindingSpecOn` and `TypingSpecOn` hold of
the circuit. `binding_discharge` eliminates it. If the declaration layer's invariant turns out
to be the kernel's own fold invariant, `Facts` can be replaced by that and the hinge becomes
public outright.

## What a verifier of two proofs checks

Given an accepted typing claim and an accepted `binding` claim, `binding_discharge` applies
when the typing claim's context names the binding claim's table address
(`BindingAt cA b`, `b.address` the address in the binding claim). Both runs are runs of this
circuit, which asserts its own specification digest, so the two claims' digests agree for
accepted runs; a verifier that accepts proofs under more than one circuit must also compare
the claims' `spec` fields. The typing claim must name no user axioms and assume no leaves
(`InScopeTyping`). A typing claim that assumes its table (validator 4) says nothing alone.
-/

universe u

namespace IxVM.Consistency

open IxVM.Refinement
open Aiur.Generic.SourceSemantics (Call)
open Ix (Claim)
open Ix.Kernel.Admission (Binding)

/-! ## Groups and the roles a valid table's store holds -/

/-- The roles of validation group `g` (none past the last group). -/
def roleGroup (g : Nat) : List Ix.Kernel.Role :=
  Ix.SpecDigest.groups.getD g []

/-- The roles group `g` needs outside itself. -/
def groupNeeded (g : Nat) : List Ix.Kernel.Role :=
  Ix.SpecDigest.groupNeeds (roleGroup g)

/-- **The basis roles**: the members of the blocks the kernel models by hand (`Eq`, `Nat`,
`PUnit`, `Empty`, `False`) and the quotient package. -/
def basisRoles : List Ix.Kernel.Role :=
  [.eq, .eqRefl, .eqRec, .nat, .natZero, .natSucc, .natRec, .punit, .punitUnit, .punitRec,
   .empty, .emptyRec, .false, .falseRec, .quot, .quotMk, .quotLift, .quotInd, .quotSound]

/-- **The basis is pinned**: where `t` binds a basis role, it binds it to the address the
committed default table binds it to, the address of the committed basis record. A property of
the table and committed data alone. -/
def BasisPinned (t : Ix.Kernel.RoleTable) : Prop :=
  ∃ t₀, Ix.Kernel.Reader.defaultTable = .ok t₀ ∧
    ∀ r ∈ basisRoles, ∀ a, t.addressOf? r = some a → t₀.addressOf? r = some a

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

/-- **A role whose constant a model reads**, so that a valid table's store holds its record. -/
def modelRead (r : Ix.Kernel.Role) : Prop :=
  walkedRole r = true ∨ r ∈ shapeAnchors

/-! ## The witness -/

/-- Every record and blob of `R` is stored under the pure BLAKE3 hash of its bytes. -/
def EnvSelfHashed (R : Ixon.Env) : Prop :=
  (∀ a lc, R.consts.get? a = some lc → Address.blake3Pure lc.rawBytes = a) ∧
  (∀ a bytes, R.blobs.get? a = some bytes → Address.blake3Pure bytes = a)

/-- **`R` is closed under what its records use**: the block of a projection record, and the
record at every constant reference a record uses (`usedRefIdxs`), are records of `R`. -/
def UsedClosed (R : Ixon.Env) : Prop :=
  ∀ a c, recordOf R a = some c →
    (recordOf R (Ix.Cert.ownerOf a c)).isSome = true ∧
    ∀ i ∈ usedRefIdxs c, ∀ x, c.refs[i]? = some x → (recordOf R x).isSome = true

/-- A pinned basis constant: one of the constants the kernel installs for a basis block. -/
def PinnedBasis (ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ∃ kind : Ix.Kernel.BasisKind, ci ∈ (kind.declsA : List (Ix.Kernel.ConstantInfo .anon))

/-- **`ci` stores what the record at `a` declares**, over a store of records and blobs: the
record declares some `ci₀` (`ReadsIn`) and `ci` is `ci₀` stored (`StoredAs`). An axiom record
is kept only at an address the role table binds a role to. -/
def KeptIn (t : Ix.Kernel.RoleTable) (store : Ix.Kernel.Reader.Store)
    (blob : Address → Option ByteArray) (a : Address) (ci : Ix.Kernel.ConstantInfo .anon) :
    Prop :=
  (∀ c ax, store a = some c → c.info = .axio ax → ∃ r, keyOf t a = .role r) ∧
    ∃ ci₀, ReadsIn t store blob a ci₀ ∧ StoredAs ci ci₀

/-- **`env` is made of the readings of `R`'s records**: its names are distinct; every
constant of its claimed sub-environment is a projection table, a pinned basis constant, or
stores what a record of `R` declares; and what each record of `R` declares is stored at its
key (or, for a basis record, its pin is). -/
structure ReadingOf (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop where
  nodup : (env.consts.map (·.name)).Nodup
  provenance : ∀ ci ∈ (claimedEnv env).consts,
    (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
      ∃ a, KeptIn t (recordOf R) (fun x => R.blobs.get? x) a ci
  stored : ∀ a ci₀, Reads t R a ci₀ →
    ∃ ci, env.find? ci₀.name = some ci ∧ (StoredAs ci ci₀ ∨ PinnedBasis ci)

/-- **The table `t` is valid on the groups `G`, witnessed by the store `R` and the
environment `env`.**

* `G` is closed under what its groups need, and `t` binds every role of a group of `G`;
* `t` pins the basis and binds a string literal's whole support;
* `R` is authentic and closed under used references, and holds the record of every role of
  `G` that a model reads;
* `env` is made of the readings of `R`'s records (`ReadingOf`) and has a model in every set
  theory;
* `Facts t G env`: what the typing statement's proof continues from (see the module
  docstring). -/
structure TableWitness (Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ix.Kernel.Env .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop where
  needsClosed : ∀ g, G g → ∀ r ∈ groupNeeded g, G (Ix.SpecDigest.groupOf r)
  bound : ∀ g, G g → ∀ r ∈ roleGroup g, (t.addressOf? r).isSome = true
  basis : BasisPinned t
  literals : LiteralSupportBound t
  hashed : EnvSelfHashed R
  usedClosed : UsedClosed R
  roles : ∀ g r a, G g → r ∈ roleGroup g → modelRead r → t.addressOf? r = some a →
    (recordOf R a).isSome = true
  reading : ReadingOf t R env
  model : ∀ (W : Type u) [Ix.Kernel.SetTheory W], Nonempty (Ix.Kernel.Model W (claimedEnv env))
  facts : Facts t G env

/-- **The table `t` is valid on the groups `G`**: some store and environment witness it. -/
def TableValidOn (Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ix.Kernel.Env .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) : Prop :=
  ∃ (R : Ixon.Env) (env : Ix.Kernel.Env .anon), TableWitness.{u} Facts t G R env

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

/-- **The typing claims covered**: `check` and `checkEnv` that name no user axioms and assume
no leaves, whether they validate their role table or assume it. -/
def InScopeTyping : Claim → Prop
  | .check ctx _ asm => ctx.axioms = none ∧ asm = none
  | .checkEnv ctx _ asm => ctx.axioms = none ∧ asm = none
  | _ => False

/-- A claim in `InScope` is in `InScopeTyping`. -/
theorem InScope.typing {c : Claim} (h : InScope c) : InScopeTyping c := by
  cases c with
  | check ctx a asm => exact ⟨h.2.1, h.2.2⟩
  | checkEnv ctx root asm => exact ⟨h.2.1, h.2.2⟩
  | _ => exact h

/-- **What a typing derivation establishes against a valid table**: for every claim byte
string whose digest packs to `d` and decodes to a typing claim in scope, every reader's view
of its seeds, every role table at the claim's address that admits as a table, and every
witness that the table is valid on groups holding every role it binds: the run hashed a
collision (with the claim's bytes, the table's, the view's data, the projection records
reconstructed from the view's blocks, or the witness's store), or `ConsistentReadOver`. -/
def TypingSpecOn (Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ix.Kernel.Env .anon → Prop)
    (calls : List (Call IxVM.F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (c : Claim), Claim.de bytes = .ok c →
    packDigest (Address.blake3Pure bytes) = d → InScopeTyping c →
      ∀ (V : View) (seeds : List Address) (b : Binding), ClaimSeeds c V seeds →
        BindingAt c b → ∀ t : Ix.Kernel.RoleTable,
          Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t →
          ∀ (G : Nat → Prop) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon),
            TableWitness.{u} Facts t G R envT →
            (∀ r a, t.addressOf? r = some a → G (Ix.SpecDigest.groupOf r)) →
              CollisionWith V (bytes :: b.bytes :: derivedProjImages V) R calls ∨
                ConsistentReadOver.{u} calls t R envT seeds

/-- **What a `binding` derivation establishes**: for every claim byte string whose digest
packs to `d` and decodes to `binding spec a`, every view and every role table at `a` that
admits as a table: the run hashed a collision (with the claim's bytes, the table's, the
view's data or the committed images), or the table is valid on every group, witnessed over
records the run loaded. -/
def BindingSpecOn (Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ix.Kernel.Env .anon → Prop)
    (calls : List (Call IxVM.F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (spec a : Address), Claim.de bytes = .ok (.binding spec a) →
    packDigest (Address.blake3Pure bytes) = d →
      ∀ (V : View) (b : Binding), b.address = a → ∀ t : Ix.Kernel.RoleTable,
        Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t →
          V.HashedCollision (bytes :: b.bytes :: committedImages) calls ∨
            ∃ (R : Ixon.Env) (env : Ix.Kernel.Env .anon),
              LoadedBy calls R ∧ TableWitness.{u} Facts t (fun _ => True) R env

/-- **The deployed IxVM circuit proves role tables valid and typing claims consistent
against valid tables**: for some `Facts`, a `binding` derivation gives a table's validity
(`BindingSpecOn`) and a typing derivation gives `ConsistentReadOver` against it
(`TypingSpecOn`). -/
def CircuitConsistentOn : Prop :=
  ∃ Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ix.Kernel.Env .anon → Prop,
    CircuitSound (BindingSpecOn.{u} Facts) ∧ CircuitSound (TypingSpecOn.{u} Facts)

/-! ## Composition -/

/-- What a longer list of calls hashed includes what a part of it hashed. -/
theorem hashed_mono {calls calls' : List (Call IxVM.F)} (hc : ∀ c ∈ calls, c ∈ calls')
    {bytes : ByteArray} (h : Hashed calls bytes) : Hashed calls' bytes := by
  unfold Hashed at h ⊢
  obtain ⟨c, hmem, rest⟩ := h
  exact ⟨c, hc c hmem, rest⟩

/-- The collision alternative is monotone in the byte strings compared and in the calls. -/
theorem hashedCollision_mono {V : View} {extra extra' : List ByteArray}
    {calls calls' : List (Call IxVM.F)} (he : ∀ x ∈ extra, x ∈ extra')
    (hc : ∀ c ∈ calls, c ∈ calls') (h : V.HashedCollision extra calls) :
    V.HashedCollision extra' calls' := by
  unfold View.HashedCollision at h ⊢
  rcases h with ⟨x, held, bytes, hheld, hh, hne, hx⟩ | ⟨bytes, hb, hp⟩
  · refine Or.inl ⟨x, held, bytes, ?_, hashed_mono hc hh, hne, hx⟩
    rcases hheld with hpre | ⟨hmem, hx'⟩ | ⟨hh', hx'⟩
    · exact Or.inl hpre
    · exact Or.inr (Or.inl ⟨he held hmem, hx'⟩)
    · exact Or.inr (Or.inr ⟨hashed_mono hc hh', hx'⟩)
  · refine Or.inr ⟨bytes, ?_, hp⟩
    rcases hb with hpre | hh
    · exact Or.inl hpre
    · exact Or.inr (hashed_mono hc hh)

/-- **A binding run discharges a typing run's premise.** Given what a `binding` derivation
establishes (`BindingSpecOn`) and what a typing derivation establishes (`TypingSpecOn`), for
a typing claim in scope whose context names the table of the `binding` claim: the two runs
together hashed a collision, or the typing claim's environment extends an environment that
witnesses the table's validity over records the binding run loaded, and has a model. The
table is constrained only by its admission as a table. -/
theorem binding_discharge
    {Facts : Ix.Kernel.RoleTable → (Nat → Prop) → Ix.Kernel.Env .anon → Prop}
    {callsA callsB : List (Call IxVM.F)} {dA dB : Digest}
    (hB : BindingSpecOn.{u} Facts callsB dB) (hA : TypingSpecOn.{u} Facts callsA dA)
    {bytesB : ByteArray} {spec a : Address} (deB : Claim.de bytesB = .ok (.binding spec a))
    (dgB : packDigest (Address.blake3Pure bytesB) = dB)
    {bytesA : ByteArray} {cA : Claim} (deA : Claim.de bytesA = .ok cA)
    (dgA : packDigest (Address.blake3Pure bytesA) = dA) (hsc : InScopeTyping cA)
    {V : View} {seeds : List Address} {b : Binding} (hs : ClaimSeeds cA V seeds)
    (hb : BindingAt cA b) (hba : b.address = a) {t : Ix.Kernel.RoleTable}
    (ht : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t) :
    V.HashedCollision
        ((bytesA :: bytesB :: b.bytes :: committedImages) ++ derivedProjImages V)
        (callsA ++ callsB) ∨
      ∃ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon),
        LoadedBy callsB R ∧ ConsistentReadOver.{u} callsA t R envT seeds := by
  have hcA : ∀ c ∈ callsA, c ∈ callsA ++ callsB := fun c h => List.mem_append.mpr (Or.inl h)
  have hcB : ∀ c ∈ callsB, c ∈ callsA ++ callsB := fun c h => List.mem_append.mpr (Or.inr h)
  have heB : ∀ x ∈ bytesB :: b.bytes :: committedImages,
      x ∈ (bytesA :: bytesB :: b.bytes :: committedImages) ++ derivedProjImages V :=
    fun x h => List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ h))
  have heA : ∀ x ∈ bytesA :: b.bytes :: derivedProjImages V,
      x ∈ (bytesA :: bytesB :: b.bytes :: committedImages) ++ derivedProjImages V := by
    intro x h
    rcases List.mem_cons.mp h with h1 | h
    · exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inl h1)))
    · rcases List.mem_cons.mp h with h2 | h3
      · exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl h2)))))
      · exact List.mem_append.mpr (Or.inr h3)
  rcases hB bytesB spec a deB dgB V b hba t ht with hcol | ⟨R, envT, hload, hw⟩
  · exact Or.inl (hashedCollision_mono heB hcB hcol)
  · rcases hA bytesA cA deA dgA hsc V seeds b hs hb t ht (fun _ => True) R envT hw
        (fun _ _ _ => trivial) with hcol | hok
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
    · exact Or.inr ⟨R, envT, hload, hok⟩

/-! ## The corollary: no claimed constant has type `False` -/

/-- **No claimed constant has type `False`**, against a valid table, in every set theory.
The claimed environment is consistent, and every constant address a seed covers is stored at
its key with a type other than `False`; where the constant stores what its record declares,
the declared type is not `False` either. -/
theorem ConsistentReadOver.seeds_not_false (W : Type u) [Ix.Kernel.SetTheory W]
    {calls : List (Call IxVM.F)} {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {seeds : List Address}
    (h : ConsistentReadOver.{u} calls t R envT seeds) :
    ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon), LoadedBy calls E₀ ∧
      Ix.Kernel.Consistent (claimedEnv env) ∧
      ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
        ∃ ci, env.find? (keyOf t a') = some ci ∧
          ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] ∧
          (PinnedBasis ci ∨
            ∃ ci₀, ReadsIn t (storeOver E₀ R) (blobOver E₀ R) a' ci₀ ∧ StoredAs ci ci₀ ∧
              ci₀.toConstantVal.type ≠ .const Ix.Kernel.falseName []) := by
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

end IxVM.Consistency
