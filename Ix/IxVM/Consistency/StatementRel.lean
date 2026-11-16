import Ix.IxVM.Consistency.Statement

/-! # The consistency statement, with a per-record reading in its conclusion

A candidate for the public statement, beside `Ix.IxVM.Consistency.Statement`, whose
definitions it reuses (`InScope`, `ClaimSeeds`, `LoadedBy`, `Annotates`, `StoredAs`,
`installs`, `claimedEnv`, the collision footprint, `CircuitSound`). Only the conclusion
changes.

## What changes

`ConsistentRead` asks for a successful run of the kernel's whole-stream reader over a record
stream that the statement leaves existential. The conclusions here ask instead that every
constant of the claimed environment be accounted for one by one, as what a single record
declares (`Reads`), the record being bytes the run hashed. No record stream, order or
declaration list appears. Three forms are stated; they share `Reads`.

* **Against a valid role table** (`Ix.IxVM.Consistency.TableValid`: `TableWitness`,
  `TypingSpecOn`, `BindingSpecOn`, `binding_discharge`). The premise is semantic validity of
  the table: an authentic store of records, an environment of their readings with a model,
  and no run of any checker. The claimed environment extends that environment by what the
  run's own records declare. A `binding` claim is to produce the premise.
* **Without a premise on the table's constants** (`ConsistentReadP`, `ConsistencySpecP`,
  `CircuitConsistentP`). The premise on the role table is its admission as a table
  (`Ix.Kernel.Admission.admitBinding`: its hash, canonical decoding and well-formedness) and
  `LiteralSupportBound`, both properties of the table's bytes. Every constant of the claimed
  environment is a projection table or keeps what a record declares: its stored form
  (`StoredAs`), or the kernel's pinned basis constant that the declared constant matches
  (`PinnedAs`). A role-bound constant is a record like any other. No run of the kernel's
  checker, installer or stream reader is in the premise or the conclusion; the kernel's
  library supplies the model (`Ix.Kernel.Model`), expression decoding and the pinned basis.
  This form asks the run itself to validate every role its environment relies on. It holds
  only of a circuit that does: one that validates a role when a native rule first uses it
  leaves the `False` role, a stored string literal's support and a merely referenced
  operation unvalidated, and this form is then false.
* **Over an admission witness** (`ConsistentReadRel`, `ConsistencySpecRel`,
  `CircuitConsistentRel`). The premise holds a run of the kernel over the role table's
  closure (`ReaderAdmissionWitness`), and the statement is for every witness. The claimed
  environment keeps that run's checked environment, and every other constant stores what a
  record declares.

What the reading means for Lean is a separate matter from consistency: that on records the
certified compiler produced, `Reads` agrees with what the kernel's reader reads. `Reads` is a
function of the table, the store and the address (`ReadsIn.functional`), and the kernel
reader's output satisfies it (proved over the reader, outside this module).

## `Reads`

`Reads t E a ci₀`: the record that `E` holds at the constant address `a` declares the
constant `ci₀` under the role table `t`. A constant address is the address of a standalone
record (definition, theorem, opaque, axiom, quotient, recursor) or of the projection record
of a block member or constructor. The record is the *exact decoding of the stored bytes*
(`recordOf`), not the store's decoded cache.

* **Keys** (`keyOf`): the constant at address `x` has the key of the role the table binds
  to `x`, otherwise the address key `x`. This is a function of the table and the address
  alone. A reference to `x` inside a record reads as that key.
* **Expressions** are converted by the kernel reader's own function
  (`Ix.Kernel.Reader.MemberReader.read`), in the context `readCtx`, whose key of an address
  is `keyOf` (`readCtx_keyAt`, in `Ix.IxVM.Consistency.ReadsKeys`) and whose literal blobs
  are the store's. Sharing, literal decoding and universe tables are the reader's.
* **Block members.** Member `i` of the block at `B` has the constant address `memberAddr B i`
  (the BLAKE3 address of its projection record), and constructor `j` of an inductive member
  has `ctorAddr B i j`. `Reads` at such an address requires the store to hold the projection
  record there, with empty tables, and the block at `B`. A `recur k` inside a block's
  expressions is the key of member `k`'s address; inside a standalone definition or recursor
  `recur 0` is the record's own key.
* **Level parameters** are positional: `0, …, n - 1`. A recursor with one level more than
  the inductive of its first motive (a large eliminator) has `n :: [0, …, n - 1]`, where `n`
  is that inductive's level count (`Ix.Kernel.Reader.recLps`).
* **Recursors.** The family and the major premise are read off the recursor's type as plain
  syntax (`familyKey`, `majorKey`): the first `params` binders, then the first motive, whose
  last binder's domain is headed by an inductive's key; and after
  `params + motives + minors + indices` binders the major premise, whose domain is headed by
  an inductive's key. No `let` is reduced and no definition unfolded: a recursor whose type
  has another shape has no reading. Rule `k` names constructor `k` of the major premise's
  inductive, with the record's field count and right-hand side; the rule count is that
  inductive's constructor count.
* **Safety.** Only records in Lean's logic are read (`InLogic`, of the record or its block).
* **What `Reads` leaves open**: a definition's reducibility hint and an inductive type's
  capability record. `Reads` is otherwise a function of the table, the store and the address
  (`ReadsIn.functional`).
* **Not reproduced.** The reader's projection rewrite (`Ix.Kernel.Reader.projRewrite`), which
  replaces a definition's value depending on the reader's state: `Reads` declares the
  record's own value. And the kernel's substitution of its pinned basis blocks
  (`Ix.Kernel.basisPinHit`), which compares a whole block: a member of such a block reads as
  the record declares it. Every table the admission accepts binds the pinned roles at the
  committed prelude records, so the pinned constants are constants of the admitted
  environment. A quotient record declares the kernel's pinned quotient constant of its kind,
  when it matches that pin (`QuotReads`).
-/

universe u

namespace IxVM.Consistency

open IxVM.Refinement
open Aiur.Generic.SourceSemantics (Call)
open Ix (Claim)
open Ix.Kernel.Admission (Binding)

/-! ## Keys -/

/-- **The key of the constant at an address** under the role table `t`: the role `t` binds
to it, otherwise the address itself. -/
def keyOf (t : Ix.Kernel.RoleTable) (a : Address) : Ix.Kernel.Key .anon :=
  match t.bound.find? (·.2 == a) with
  | some (r, _) => .role r
  | none => .id a

/-- A key is the address key of an address no role is bound to, or the key of a role bound
to the address. -/
theorem keyOf_cases (t : Ix.Kernel.RoleTable) (a : Address) :
    (keyOf t a = .id a ∧ ∀ r, (r, a) ∉ t.bound.toList) ∨
      ∃ r, (r, a) ∈ t.bound.toList ∧ keyOf t a = .role r := by
  unfold keyOf
  cases h : t.bound.find? (·.2 == a) with
  | none =>
    refine Or.inl ⟨rfl, fun r hr => ?_⟩
    have hall := Array.find?_eq_none.mp h
    exact hall (r, a) (Array.mem_toList_iff.mp hr) (beq_self_eq_true a)
  | some p =>
    obtain ⟨r, a'⟩ := p
    have hp : ((r, a').2 == a) = true :=
      Array.find?_some (p := fun x : Ix.Kernel.Role × Address => x.2 == a) h
    have ha : a' = a := beq_iff_eq.mp hp
    subst ha
    exact Or.inr ⟨r, Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some h), rfl⟩

private theorem snd_eq_of_nodup_fst {α β : Type} {l : List (α × β)}
    (hn : (l.map (·.1)).Nodup) {x : α} {y y' : β} (h : (x, y) ∈ l) (h' : (x, y') ∈ l) :
    y = y' := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons p l ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with e | h1
    · rcases List.mem_cons.mp h' with e' | h2
      · exact (Prod.mk.inj (e.trans e'.symm)).2
      · exact (hn.1 (List.mem_map.mpr ⟨(x, y'), h2, by rw [← e]⟩)).elim
    · rcases List.mem_cons.mp h' with e' | h2
      · exact (hn.1 (List.mem_map.mpr ⟨(x, y), h1, by rw [← e']⟩)).elim
      · exact ih hn.2 h1 h2

/-- **Keys identify addresses**, under a table that binds no role twice (every admitted
table: `Ix.Kernel.RoleTable.check`). -/
theorem keyOf_inj {t : Ix.Kernel.RoleTable} (hroles : (t.bound.toList.map (·.1)).Nodup)
    {a a' : Address} (h : keyOf t a = keyOf t a') : a = a' := by
  rcases keyOf_cases t a with ⟨ha, -⟩ | ⟨r, hr, ha⟩ <;>
    rcases keyOf_cases t a' with ⟨ha', -⟩ | ⟨r', hr', ha'⟩ <;> rw [ha, ha'] at h
  · exact Ix.Kernel.Key.id.inj h
  · cases h
  · cases h
  · injection h with hrr
    rw [← hrr] at hr'
    exact snd_eq_of_nodup_fst hroles hr hr'

/-! ## Stores and constant addresses -/

/-- **The record `E` holds at `a`**: the exact decoding of the bytes stored there. The
store's decoded cache is not consulted. -/
def recordOf (E : Ixon.Env) (a : Address) : Option Ixon.Constant :=
  (E.consts.get? a).bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption

/-- **The constant address of member `i` of the block at `B`**: the BLAKE3 address of its
projection record (`memberProjection`). -/
def memberAddr (B : Address) (i : Nat) (m : Ixon.MutConst) : Address :=
  Address.blake3Pure (Ixon.serConstant (memberProjection B i m))

/-- **The constant address of constructor `j` of inductive member `i` of the block at `B`**:
the BLAKE3 address of its projection record (`constructorProjection`). -/
def ctorAddr (B : Address) (i j : Nat) : Address :=
  Address.blake3Pure (Ixon.serConstant (constructorProjection B i j))

/-! ## The reading context -/

/-- A singleton record. In a store that holds it at every address, every address resolves
to itself. -/
def keyRecord : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[], #[]⟩

/-- **The context expressions are read in**: the kernel reader's context whose key of an
address is `keyOf t` (`readCtx_keyAt`: in the store that resolves every address to itself,
the reader keys an address by the role the table binds to it, otherwise by the address) and
whose literal blobs are `blob`. It has no recursor index, hints or precomputed keys; the
expression reader uses none. -/
def readCtx (t : Ix.Kernel.RoleTable) (blob : Address → Option ByteArray) :
    Ix.Kernel.Reader.Ctx .anon :=
  { store := fun _ => some keyRecord
    blob := blob
    roles := Ix.Kernel.Reader.bindingsOf (fun _ => some keyRecord) t
    index := {} }

/-- **The kernel's expression reader over the record `src`** (its sharing, reference and
universe tables), with universe variable `i` read as the level parameter `param i` and
`recur k` as `self k`. -/
def exprReader (t : Ix.Kernel.RoleTable) (blob : Address → Option ByteArray)
    (src : Ixon.Constant) (param : Nat → Ix.Kernel.LevelParam)
    (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))) :
    Ix.Kernel.Reader.MemberReader .anon :=
  Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src param self

/-- `recur` in a standalone record at `a`: `recur 0` is the record's own key. -/
def soloSelf (t : Ix.Kernel.RoleTable) (a : Address) :
    Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) :=
  fun k => if k == 0 then some (pure (keyOf t a)) else none

/-- `recur` in the block at `B` with members `ms`: `recur k` is the key of member `k`'s
constant address. -/
def blockSelf (t : Ix.Kernel.RoleTable) (B : Address) (ms : Array Ixon.MutConst) :
    Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) :=
  fun k => (ms[k]?).map fun m => pure (keyOf t (memberAddr B k m))

/-! ## What each kind of record declares -/

/-- **A definition record's constant, by its kind**: a definition with any reducibility
hint, a theorem, or for an opaque an axiom of its type (the kernel keeps no value of an
opaque: `installs`). -/
def DefnShape (kind : Ix.DefKind) (cv : Ix.Kernel.ConstantVal .anon)
    (value : Ix.Kernel.Expr .anon) (ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  match kind with
  | .defn => ∃ hint, ci₀ = .defnInfo cv value hint
  | .thm => ci₀ = .thmInfo cv value
  | .opaq => ci₀ = .axiomInfo cv

/-- **What a definition payload declares** under the key `name`: its level parameters by
position, and the readings of its type and of its value (an opaque's value must read too). -/
def DefnReads (mr : Ix.Kernel.Reader.MemberReader .anon) (name : Ix.Kernel.Key .anon)
    (d : Ixon.Definition) (ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ∃ ty value, mr.read d.typ = .ok ty ∧ mr.read d.value = .ok value ∧
    DefnShape d.kind ⟨name, List.range d.lvls.toNat, ty⟩ value ci₀

/-- **What an axiom record declares**: an axiom of the reading of its type. A record at the
key of an inert role declares nothing (`inertKey`: the kernel installs nothing for `sorryAx`
and declines Lean's compiler-trust axioms). The record at the key of `Quot.sound` reads as
any axiom does; the kernel keeps the pinned form of that axiom (`PinnedAs`), as a slot of
its quotient package. -/
def AxiomReads (mr : Ix.Kernel.Reader.MemberReader .anon) (name : Ix.Kernel.Key .anon)
    (ax : Ixon.Axiom) (ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  inertKey name = false ∧
    ∃ ty, mr.read ax.typ = .ok ty ∧ ci₀ = .axiomInfo ⟨name, List.range ax.lvls.toNat, ty⟩

/-- The kernel's quotient kind of a quotient record. -/
def quotSlot : Ix.QuotKind → Ix.Kernel.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

/-- **What a quotient record declares**: the kernel's pinned quotient constant of the
record's kind, when the record's reading matches that pin (`Ix.Kernel.quotPinHit`, the
kernel's own test). The kernel installs the pinned package and never the record's reading. -/
def QuotReads (mr : Ix.Kernel.Reader.MemberReader .anon) (name : Ix.Kernel.Key .anon)
    (q : Ixon.Quotient) (ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ∃ ty, mr.read q.typ = .ok ty ∧
    Ix.Kernel.quotPinHit (quotSlot q.kind)
      (⟨name, List.range q.lvls.toNat, ty⟩ : Ix.Kernel.ConstantVal .anon) = true ∧
    (Ix.Kernel.BasisKind.quotK.declsA : List (Ix.Kernel.ConstantInfo .anon))[
      (quotSlot q.kind).slot]? = some ci₀

/-- **What an inductive member declares**: an inductive type with the reading of its type,
and any capability record (the kernel computes it; `StoredAs` does not compare it). -/
def IndReads (mr : Ix.Kernel.Reader.MemberReader .anon) (name : Ix.Kernel.Key .anon)
    (ind : Ixon.Inductive) (ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ∃ ty caps, mr.read ind.typ = .ok ty ∧
    ci₀ = .indInfo ⟨name, List.range ind.lvls.toNat, ty⟩ caps

/-- **What a constructor declares**: a constructor with the reading of its type and the
record's parameter and field counts. -/
def CtorReads (mr : Ix.Kernel.Reader.MemberReader .anon) (name : Ix.Kernel.Key .anon)
    (ct : Ixon.Constructor) (ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ∃ ty, mr.read ct.typ = .ok ty ∧
    ci₀ = .ctorInfo ⟨name, List.range ct.lvls.toNat, ty⟩ ct.params.toNat ct.fields.toNat

/-- **`c`, the record at `a`, is the projection record of member `i` (`m`) of the block at
`B`**: the store holds the block `cb` with members `ms` at `B`, in Lean's logic; `c` is the
member's projection record with empty tables, and `a` is its address. -/
def MemberAt (store : Ix.Kernel.Reader.Store) (a : Address) (c : Ixon.Constant) (B : Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (i : Nat) (m : Ixon.MutConst) : Prop :=
  store B = some cb ∧ cb.info = .muts ms ∧ ms[i]? = some m ∧
    c = memberProjection B i m ∧ a = memberAddr B i m ∧ InLogic cb

/-! ### Recursors -/

/-- The domain of the last binder of a `∀`-telescope. -/
def lastBinderDom : Ix.Kernel.Expr .anon → Option (Ix.Kernel.Expr .anon)
  | .forallE d b _ =>
    match b with
    | .forallE _ _ _ => lastBinderDom b
    | _ => some d
  | _ => none

/-- The key of the constant at the head of an application spine. -/
def headKey (e : Ix.Kernel.Expr .anon) : Option (Ix.Kernel.Key .anon) :=
  match e.getAppFn with
  | .const k _ => some k
  | _ => none

/-- The domain of binder `n` (from `0`) of a type that begins with `n + 1` literal `∀`s. -/
def binderDom (n : Nat) (ty : Ix.Kernel.Expr .anon) : Option (Ix.Kernel.Expr .anon) :=
  match ty.stripPis n with
  | some (_, .forallE d _ _) => some d
  | _ => none

/-- **The key heading a recursor's family**: its type begins with `params` literal `∀`s and
then the first motive, a literal `∀`-telescope whose last binder's domain (the motive's
major premise) is an application headed by a constant. That constant's key. -/
def familyKey (rc : Ixon.Recursor) (ty : Ix.Kernel.Expr .anon) : Option (Ix.Kernel.Key .anon) :=
  (binderDom rc.params.toNat ty).bind fun motive => (lastBinderDom motive).bind headKey

/-- **The key heading a recursor's major premise**: its type begins with
`params + motives + minors + indices` literal `∀`s and then the major premise, whose domain is
an application headed by a constant. That constant's key. -/
def majorKey (rc : Ixon.Recursor) (ty : Ix.Kernel.Expr .anon) : Option (Ix.Kernel.Key .anon) :=
  (binderDom (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) ty).bind
    headKey

/-- **`k` is the key of an inductive type the store holds**: of member `i` (`ind`) of the
block at `B`, whose projection record the store holds at the address `k` is the key of. -/
def IndKeyAt (t : Ix.Kernel.RoleTable) (store : Ix.Kernel.Reader.Store) (k : Ix.Kernel.Key .anon)
    (B : Address) (i : Nat) (ind : Ixon.Inductive) : Prop :=
  ∃ a c p cb ms, k = keyOf t a ∧ store a = some c ∧ c.info = .iPrj p ∧ B = p.block ∧
    i = p.idx.toNat ∧ MemberAt store a c B cb ms i (.indc ind)

/-- **One rule as declared**: rule `ru.2` names constructor `ru.2` of member `im` of the
block at `Bm`, with the record's field count and the reading of its right-hand side. The
other fields are the reader's placeholders (the kernel computes them at install, and
`RuleStored` does not compare them). -/
def RuleReads (t : Ix.Kernel.RoleTable) (mr : Ix.Kernel.Reader.MemberReader .anon) (Bm : Address)
    (im : Nat) (ru : Ixon.RecursorRule × Nat) (rl : Ix.Kernel.RecRule .anon) : Prop :=
  ∃ rhs, mr.read ru.1.rhs = .ok rhs ∧
    rl = Ix.Kernel.RecRule.mk (keyOf t (ctorAddr Bm im ru.2)) ru.1.fields.toNat 0 .inert rhs
      false false false

/-- **What a recursor payload declares** under the key `name`, read from the record `src`
with `recur` as `self`.

Its type is first read with positional level parameters (`tyP`), to find the inductive `ind`
whose key heads its family (`familyKey`) and the inductive `indM` whose key heads its major
premise (`majorKey`); level parameter names do not affect either. Its level parameters `ps`
are `ind`'s, behind one more for a large eliminator. The constant has the reading `ty` of
the type under `ps`, the major premise's position, the rule prefix's length, and one rule for
each constructor of `indM`, in order. -/
def RecReads (t : Ix.Kernel.RoleTable) (store : Ix.Kernel.Reader.Store)
    (blob : Address → Option ByteArray) (src : Ixon.Constant)
    (self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)))
    (name : Ix.Kernel.Key .anon) (rc : Ixon.Recursor) (ci₀ : Ix.Kernel.ConstantInfo .anon) :
    Prop :=
  ∃ (tyP ty : Ix.Kernel.Expr .anon) (kF kM : Ix.Kernel.Key .anon) (B Bm : Address) (i im : Nat)
    (ind indM : Ixon.Inductive) (ps : List Ix.Kernel.LevelParam)
    (rules : List (Ix.Kernel.RecRule .anon)),
    (exprReader t blob src id self).read rc.typ = .ok tyP ∧
    familyKey rc tyP = some kF ∧ IndKeyAt t store kF B i ind ∧
    majorKey rc tyP = some kM ∧ IndKeyAt t store kM Bm im indM ∧
    ps = Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
      (List.range ind.lvls.toNat) ∧
    (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read rc.typ = .ok ty ∧
    rc.rules.size = indM.ctors.size ∧
    List.Forall₂
      (RuleReads t (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self) Bm im)
      rc.rules.toList.zipIdx rules ∧
    ci₀ = .recInfo ⟨name, ps, ty⟩
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules

/-! ## `Reads` -/

/-- **What the record `c` at the constant address `a` declares**, by the record's kind. A
block record is not a constant: its members are read at their own addresses. -/
def ReadsRecord (t : Ix.Kernel.RoleTable) (store : Ix.Kernel.Reader.Store)
    (blob : Address → Option ByteArray) (a : Address) (c : Ixon.Constant)
    (ci₀ : Ix.Kernel.ConstantInfo .anon) : Ixon.ConstantInfo → Prop
  | .defn d =>
    InLogic c ∧ DefnReads (exprReader t blob c id (soloSelf t a)) (keyOf t a) d ci₀
  | .axio ax =>
    InLogic c ∧ AxiomReads (exprReader t blob c id (fun _ => none)) (keyOf t a) ax ci₀
  | .quot q => QuotReads (exprReader t blob c id (fun _ => none)) (keyOf t a) q ci₀
  | .recr rc => InLogic c ∧ RecReads t store blob c (soloSelf t a) (keyOf t a) rc ci₀
  | .dPrj p =>
    ∃ cb ms d, MemberAt store a c p.block cb ms p.idx.toNat (.defn d) ∧
      DefnReads (exprReader t blob cb id (blockSelf t p.block ms)) (keyOf t a) d ci₀
  | .iPrj p =>
    ∃ cb ms ind, MemberAt store a c p.block cb ms p.idx.toNat (.indc ind) ∧
      IndReads (exprReader t blob cb id (blockSelf t p.block ms)) (keyOf t a) ind ci₀
  | .cPrj p =>
    ∃ cb ms ind ct, store p.block = some cb ∧ cb.info = .muts ms ∧
      ms[p.idx.toNat]? = some (.indc ind) ∧ ind.ctors[p.cidx.toNat]? = some ct ∧
      ct.cidx.toNat = p.cidx.toNat ∧ c = constructorProjection p.block p.idx.toNat p.cidx.toNat ∧
      a = ctorAddr p.block p.idx.toNat p.cidx.toNat ∧ InLogic cb ∧
      CtorReads (exprReader t blob cb id (blockSelf t p.block ms)) (keyOf t a) ct ci₀
  | .rPrj p =>
    ∃ cb ms rc, MemberAt store a c p.block cb ms p.idx.toNat (.recr rc) ∧
      RecReads t store blob cb (blockSelf t p.block ms) (keyOf t a) rc ci₀
  | .muts _ => False

/-- **`Reads` over a store of records and blobs**: the record `store` holds at the constant
address `a` declares `ci₀` under the role table `t`, reading blocks from `store` and literal
blobs from `blob`. -/
def ReadsIn (t : Ix.Kernel.RoleTable) (store : Ix.Kernel.Reader.Store)
    (blob : Address → Option ByteArray) (a : Address) (ci₀ : Ix.Kernel.ConstantInfo .anon) :
    Prop :=
  ∃ c, store a = some c ∧ ReadsRecord t store blob a c ci₀ c.info

/-- **The record at the constant address `a` in `E` declares the constant `ci₀`** under the
role table `t`: `ReadsIn` over the exact decodings of `E`'s stored bytes (`recordOf`) and
`E`'s blobs. -/
def Reads (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (a : Address)
    (ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ReadsIn t (recordOf E) (fun x => E.blobs.get? x) a ci₀

/-! ## `Reads` is a function, up to hint and capability record -/

/-- **Two declared constants agree up to what `Reads` leaves open**: they are equal, or the
same definition under two reducibility hints, or the same inductive type under two capability
records. -/
def SameReading (ci ci' : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ci = ci' ∨
  (∃ cv v h h', ci = .defnInfo cv v h ∧ ci' = .defnInfo cv v h') ∨
  (∃ cv caps caps', ci = .indInfo cv caps ∧ ci' = .indInfo cv caps')

theorem DefnShape.same {kind : Ix.DefKind} {cv : Ix.Kernel.ConstantVal .anon}
    {value : Ix.Kernel.Expr .anon} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : DefnShape kind cv value ci₁) (h₂ : DefnShape kind cv value ci₂) :
    SameReading ci₁ ci₂ := by
  cases kind with
  | defn =>
    obtain ⟨hint₁, e₁⟩ := h₁
    obtain ⟨hint₂, e₂⟩ := h₂
    exact Or.inr (Or.inl ⟨cv, value, hint₁, hint₂, e₁, e₂⟩)
  | thm =>
    have e₁ : ci₁ = .thmInfo cv value := h₁
    have e₂ : ci₂ = .thmInfo cv value := h₂
    exact Or.inl (e₁.trans e₂.symm)
  | opaq =>
    have e₁ : ci₁ = .axiomInfo cv := h₁
    have e₂ : ci₂ = .axiomInfo cv := h₂
    exact Or.inl (e₁.trans e₂.symm)

private theorem ok_inj {ε α : Type} {x : Except ε α} {a b : α} (h₁ : x = .ok a) (h₂ : x = .ok b) :
    a = b := by
  rw [h₁] at h₂
  exact Except.ok.inj h₂

private theorem some_inj {α : Type} {x : Option α} {a b : α} (h₁ : x = some a) (h₂ : x = some b) :
    a = b := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem DefnReads.same {mr : Ix.Kernel.Reader.MemberReader .anon} {name : Ix.Kernel.Key .anon}
    {d : Ixon.Definition} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : DefnReads mr name d ci₁) (h₂ : DefnReads mr name d ci₂) : SameReading ci₁ ci₂ := by
  obtain ⟨ty₁, v₁, ht₁, hv₁, s₁⟩ := h₁
  obtain ⟨ty₂, v₂, ht₂, hv₂, s₂⟩ := h₂
  obtain rfl := ok_inj ht₁ ht₂
  obtain rfl := ok_inj hv₁ hv₂
  exact s₁.same s₂

theorem AxiomReads.same {mr : Ix.Kernel.Reader.MemberReader .anon} {name : Ix.Kernel.Key .anon}
    {ax : Ixon.Axiom} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : AxiomReads mr name ax ci₁) (h₂ : AxiomReads mr name ax ci₂) : ci₁ = ci₂ := by
  obtain ⟨-, ty₁, ht₁, e₁⟩ := h₁
  obtain ⟨-, ty₂, ht₂, e₂⟩ := h₂
  obtain rfl := ok_inj ht₁ ht₂
  exact e₁.trans e₂.symm

theorem QuotReads.same {mr : Ix.Kernel.Reader.MemberReader .anon} {name : Ix.Kernel.Key .anon}
    {q : Ixon.Quotient} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : QuotReads mr name q ci₁) (h₂ : QuotReads mr name q ci₂) : ci₁ = ci₂ := by
  obtain ⟨_, -, -, e₁⟩ := h₁
  obtain ⟨_, -, -, e₂⟩ := h₂
  exact some_inj e₁ e₂

theorem IndReads.same {mr : Ix.Kernel.Reader.MemberReader .anon} {name : Ix.Kernel.Key .anon}
    {ind : Ixon.Inductive} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : IndReads mr name ind ci₁) (h₂ : IndReads mr name ind ci₂) : SameReading ci₁ ci₂ := by
  obtain ⟨ty₁, caps₁, ht₁, e₁⟩ := h₁
  obtain ⟨ty₂, caps₂, ht₂, e₂⟩ := h₂
  obtain rfl := ok_inj ht₁ ht₂
  exact Or.inr (Or.inr ⟨_, caps₁, caps₂, e₁, e₂⟩)

theorem CtorReads.same {mr : Ix.Kernel.Reader.MemberReader .anon} {name : Ix.Kernel.Key .anon}
    {ct : Ixon.Constructor} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : CtorReads mr name ct ci₁) (h₂ : CtorReads mr name ct ci₂) : ci₁ = ci₂ := by
  obtain ⟨ty₁, ht₁, e₁⟩ := h₁
  obtain ⟨ty₂, ht₂, e₂⟩ := h₂
  obtain rfl := ok_inj ht₁ ht₂
  exact e₁.trans e₂.symm

/-- The store determines the block, its members and the member a projection record names. -/
theorem MemberAt.unique {store : Ix.Kernel.Reader.Store} {a : Address} {c : Ixon.Constant}
    {B : Address} {cb cb' : Ixon.Constant} {ms ms' : Array Ixon.MutConst} {i : Nat}
    {m m' : Ixon.MutConst} (h : MemberAt store a c B cb ms i m)
    (h' : MemberAt store a c B cb' ms' i m') : cb' = cb ∧ ms' = ms ∧ m' = m := by
  obtain ⟨hs, hi, hm, -⟩ := h
  obtain ⟨hs', hi', hm', -⟩ := h'
  obtain rfl := some_inj hs hs'
  rw [hi] at hi'
  obtain rfl := Ixon.ConstantInfo.muts.inj hi'
  exact ⟨rfl, rfl, some_inj hm' hm⟩

/-- A key names at most one inductive type of the store. -/
theorem IndKeyAt.unique {t : Ix.Kernel.RoleTable} (hroles : (t.bound.toList.map (·.1)).Nodup)
    {store : Ix.Kernel.Reader.Store} {k : Ix.Kernel.Key .anon} {B B' : Address} {i i' : Nat}
    {ind ind' : Ixon.Inductive} (h : IndKeyAt t store k B i ind)
    (h' : IndKeyAt t store k B' i' ind') : B' = B ∧ i' = i ∧ ind' = ind := by
  obtain ⟨a, c, p, cb, ms, hk, hs, hi, hB, hidx, hm⟩ := h
  obtain ⟨a', c', p', cb', ms', hk', hs', hi', hB', hidx', hm'⟩ := h'
  obtain rfl : a = a' := keyOf_inj hroles (hk.symm.trans hk')
  obtain rfl := some_inj hs hs'
  rw [hi] at hi'
  obtain rfl := Ixon.ConstantInfo.iPrj.inj hi'
  have hBB : B' = B := hB'.trans hB.symm
  have hii : i' = i := hidx'.trans hidx.symm
  subst hBB
  subst hii
  obtain ⟨-, -, hmm⟩ := MemberAt.unique hm hm'
  exact ⟨rfl, rfl, Ixon.MutConst.indc.inj hmm⟩

private theorem forall₂_unique {α β : Type} {R : α → β → Prop}
    (hR : ∀ a b b', R a b → R a b' → b = b') {l : List α} {m m' : List β}
    (h : List.Forall₂ R l m) (h' : List.Forall₂ R l m') : m = m' := by
  induction h generalizing m' with
  | nil => cases h'; rfl
  | cons hab _ ih =>
    cases h' with
    | cons hab' t' => rw [hR _ _ _ hab hab', ih t']

theorem RuleReads.unique {t : Ix.Kernel.RoleTable} {mr : Ix.Kernel.Reader.MemberReader .anon}
    {Bm : Address} {im : Nat} {ru : Ixon.RecursorRule × Nat} {rl rl' : Ix.Kernel.RecRule .anon}
    (h : RuleReads t mr Bm im ru rl) (h' : RuleReads t mr Bm im ru rl') : rl = rl' := by
  obtain ⟨rhs, hr, e⟩ := h
  obtain ⟨rhs', hr', e'⟩ := h'
  obtain rfl := ok_inj hr hr'
  exact e.trans e'.symm

theorem RecReads.same {t : Ix.Kernel.RoleTable} (hroles : (t.bound.toList.map (·.1)).Nodup)
    {store : Ix.Kernel.Reader.Store} {blob : Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {name : Ix.Kernel.Key .anon} {rc : Ixon.Recursor} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : RecReads t store blob src self name rc ci₁)
    (h₂ : RecReads t store blob src self name rc ci₂) : ci₁ = ci₂ := by
  obtain ⟨tyP₁, ty₁, kF₁, kM₁, B₁, Bm₁, i₁, im₁, ind₁, indM₁, ps₁, rules₁,
    hP₁, hF₁, hIF₁, hM₁, hIM₁, hps₁, hty₁, -, hr₁, e₁⟩ := h₁
  obtain ⟨tyP₂, ty₂, kF₂, kM₂, B₂, Bm₂, i₂, im₂, ind₂, indM₂, ps₂, rules₂,
    hP₂, hF₂, hIF₂, hM₂, hIM₂, hps₂, hty₂, -, hr₂, e₂⟩ := h₂
  obtain rfl := ok_inj hP₁ hP₂
  obtain rfl := some_inj hF₁ hF₂
  obtain rfl := some_inj hM₁ hM₂
  obtain ⟨rfl, rfl, rfl⟩ := IndKeyAt.unique hroles hIF₁ hIF₂
  obtain ⟨rfl, rfl, rfl⟩ := IndKeyAt.unique hroles hIM₁ hIM₂
  obtain rfl : ps₁ = ps₂ := hps₁.trans hps₂.symm
  obtain rfl := ok_inj hty₁ hty₂
  obtain rfl := forall₂_unique (R := RuleReads _ _ _ _)
    (fun _ _ _ h h' => RuleReads.unique h h') hr₁ hr₂
  exact e₁.trans e₂.symm

/-- **`Reads` is a function of the table, the store and the address**, up to a definition's
reducibility hint and an inductive type's capability record: two readings of one address
agree (`SameReading`). The table binds no role twice (every admitted table). -/
theorem ReadsIn.functional {t : Ix.Kernel.RoleTable}
    (hroles : (t.bound.toList.map (·.1)).Nodup) {store : Ix.Kernel.Reader.Store}
    {blob : Address → Option ByteArray} {a : Address} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : ReadsIn t store blob a ci₁) (h₂ : ReadsIn t store blob a ci₂) :
    SameReading ci₁ ci₂ := by
  obtain ⟨c, hc, h₁⟩ := h₁
  obtain ⟨c', hc', h₂⟩ := h₂
  obtain rfl := some_inj hc hc'
  generalize c.info = info at h₁ h₂
  cases info with
  | defn d =>
    obtain ⟨-, r₁⟩ := h₁
    obtain ⟨-, r₂⟩ := h₂
    exact r₁.same r₂
  | axio ax =>
    obtain ⟨-, r₁⟩ := h₁
    obtain ⟨-, r₂⟩ := h₂
    exact Or.inl (r₁.same r₂)
  | quot q => exact Or.inl (QuotReads.same h₁ h₂)
  | recr rc =>
    obtain ⟨-, r₁⟩ := h₁
    obtain ⟨-, r₂⟩ := h₂
    exact Or.inl (RecReads.same hroles r₁ r₂)
  | dPrj p =>
    obtain ⟨cb₁, ms₁, d₁, hm₁, r₁⟩ := h₁
    obtain ⟨cb₂, ms₂, d₂, hm₂, r₂⟩ := h₂
    obtain ⟨rfl, rfl, hmm⟩ := MemberAt.unique hm₁ hm₂
    obtain rfl := Ixon.MutConst.defn.inj hmm
    exact r₁.same r₂
  | iPrj p =>
    obtain ⟨cb₁, ms₁, ind₁, hm₁, r₁⟩ := h₁
    obtain ⟨cb₂, ms₂, ind₂, hm₂, r₂⟩ := h₂
    obtain ⟨rfl, rfl, hmm⟩ := MemberAt.unique hm₁ hm₂
    obtain rfl := Ixon.MutConst.indc.inj hmm
    exact r₁.same r₂
  | cPrj p =>
    obtain ⟨cb₁, ms₁, ind₁, ct₁, hs₁, hi₁, hm₁, hct₁, -, -, -, -, r₁⟩ := h₁
    obtain ⟨cb₂, ms₂, ind₂, ct₂, hs₂, hi₂, hm₂, hct₂, -, -, -, -, r₂⟩ := h₂
    obtain rfl := some_inj hs₁ hs₂
    rw [hi₁] at hi₂
    obtain rfl := Ixon.ConstantInfo.muts.inj hi₂
    obtain rfl := Ixon.MutConst.indc.inj (some_inj hm₁ hm₂)
    obtain rfl := some_inj hct₁ hct₂
    exact Or.inl (r₁.same r₂)
  | rPrj p =>
    obtain ⟨cb₁, ms₁, rc₁, hm₁, r₁⟩ := h₁
    obtain ⟨cb₂, ms₂, rc₂, hm₂, r₂⟩ := h₂
    obtain ⟨rfl, rfl, hmm⟩ := MemberAt.unique hm₁ hm₂
    obtain rfl := Ixon.MutConst.recr.inj hmm
    exact Or.inl (RecReads.same hroles r₁ r₂)
  | muts ms => exact False.elim h₁

/-- `ReadsIn.functional` over an environment. -/
theorem Reads.functional {t : Ix.Kernel.RoleTable} (hroles : (t.bound.toList.map (·.1)).Nodup)
    {E : Ixon.Env} {a : Address} {ci₁ ci₂ : Ix.Kernel.ConstantInfo .anon}
    (h₁ : Reads t E a ci₁) (h₂ : Reads t E a ci₂) : SameReading ci₁ ci₂ :=
  ReadsIn.functional hroles h₁ h₂

/-- Every reading in an environment is of a record whose bytes the environment stores: the
record is their exact decoding. -/
theorem Reads.stored {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {a : Address}
    {ci₀ : Ix.Kernel.ConstantInfo .anon} (h : Reads t E a ci₀) :
    ∃ lc c, E.consts.get? a = some lc ∧ Ixon.deConstantExact lc.rawBytes = .ok c := by
  obtain ⟨c, hc, -⟩ := h
  unfold recordOf at hc
  cases hl : E.consts.get? a with
  | none =>
    rw [hl] at hc
    simp at hc
  | some lc =>
    rw [hl] at hc
    have hc' : (Ixon.deConstantExact lc.rawBytes).toOption = some c := hc
    refine ⟨lc, c, rfl, ?_⟩
    cases hd : Ixon.deConstantExact lc.rawBytes with
    | error e =>
      rw [hd] at hc'
      simp [Except.toOption] at hc'
    | ok c' =>
      rw [hd] at hc'
      exact congrArg Except.ok (Option.some.inj hc')

/-! ## The admitted prefix -/

/-- **The declarations the admission's fold ran over**: the witness's reading of the role
table's closure, behind the prelude. -/
def prefixDecls {V : View} {b : Binding} (w : ReaderAdmissionWitness V b) :
    List (Ix.Kernel.Declaration .anon) :=
  (Ix.Kernel.Frontend.preparePrelude w.prelude.ix w.fullDecls).toList

/-- **`name` is declared as a theorem by `ds`**, at a key the kernel does not derive. The
admission's fold checks such a theorem as an opaque-hinted definition (`thmToOpaqueDefn`). -/
def DeclaredTheorem (ds : List (Ix.Kernel.Declaration .anon)) (name : Ix.Kernel.Key .anon) :
    Prop :=
  ∃ cv value, Ix.Kernel.Declaration.thmDecl cv value ∈ ds ∧ cv.name = name ∧
    ∀ k d, name ≠ .aux k d

/-- **The form the claimed environment keeps a checked constant `ci'` in**: a declared
theorem, which the admission's fold stores as an opaque-hinted definition, is kept as the
theorem with that signature and value; every other constant is kept as it is. -/
def PrefixForm (ds : List (Ix.Kernel.Declaration .anon))
    (ci' ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  (∃ cv value, ci' = .defnInfo cv value .opaque ∧ DeclaredTheorem ds cv.name ∧
    ci = .thmInfo cv value) ∨
  (ci = ci' ∧ ¬ ∃ cv value, ci' = .defnInfo cv value .opaque ∧ DeclaredTheorem ds cv.name)

/-- **A constant of the admitted prefix**: a constant of the witness's checked environment,
in the form the claimed environment keeps it (`PrefixForm`). -/
def PrefixConstant {V : View} {b : Binding} (w : ReaderAdmissionWitness V b)
    (ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ∃ ci' ∈ w.checkedEnv.consts, PrefixForm (prefixDecls w) ci' ci

/-! ## Seeds and axiom records -/

/-- `E` holds an axiom record at `a`. -/
def IsAxiomRecord (E : Ixon.Env) (a : Address) : Prop :=
  ∃ c ax, recordOf E a = some c ∧ c.info = .axio ax

/-- **The constant addresses a seed covers**: the seed itself, when it is no block record; for
a block record, every member's address and every constructor's address. -/
def SeedConstant (E₀ : Ixon.Env) (a a' : Address) : Prop :=
  (a' = a ∧ ∀ c ms, recordOf E₀ a = some c → c.info ≠ .muts ms) ∨
  ∃ c ms i m, recordOf E₀ a = some c ∧ c.info = .muts ms ∧ ms[i]? = some m ∧
    (a' = memberAddr a i m ∨
      ∃ ind j, m = .indc ind ∧ j < ind.ctors.size ∧ a' = ctorAddr a i j)

/-- The role table `b` is at the address the claim names. -/
def BindingAt (c : Claim) (b : Binding) : Prop :=
  ∃ ctx, c.context? = some ctx ∧ b.address = ctx.binding

/-- A claimed constant at the key of a constant address is not a model-family constant, and
its key is not derived. -/
theorem seed_claimed {t : Ix.Kernel.RoleTable} {a' : Address}
    {env : Ix.Kernel.Env .anon} {ci : Ix.Kernel.ConstantInfo .anon}
    (hfind : env.find? (keyOf t a') = some ci) :
    ci ∈ (claimedEnv env).consts ∧ ∀ k d, ci.name ≠ .aux k d := by
  have hmem0 : ci ∈ env.consts := List.mem_of_find?_eq_some hfind
  have hname : ci.name = keyOf t a' := by
    have := List.find?_some hfind
    simpa using this
  have hna : ∀ k d, ci.name ≠ .aux k d := by
    intro k d hk'
    rw [hname] at hk'
    rcases keyOf_cases t a' with ⟨hk, -⟩ | ⟨r, -, hk⟩ <;> rw [hk] at hk' <;> cases hk'
  have hnaux : isModelAux ci = false := by
    unfold isModelAux
    rw [hname]
    rcases keyOf_cases t a' with ⟨hk, -⟩ | ⟨r, -, hk⟩ <;> rw [hk]
  exact ⟨List.mem_filter.mpr ⟨hmem0, by simp [hnaux]⟩, hna⟩

/-! ## The conclusion without an admission premise -/

/-- **`ci` is the kernel's pinned basis constant for the declared constant `ci₀`**: `ci₀`
has the canonical form (`Ix.Kernel.ConstantInfo.canon`: level parameters renamed by position,
capabilities dropped) of the raw pin at slot `j` of a basis block (`Eq`, `Nat`, `PUnit`,
`Empty`, `False`, the quotient package), and `ci` is that slot's annotated pin, the constant
the kernel's model of the basis is proved about. This is the kernel's own comparison of a
block with a pin (`Ix.Kernel.basisPinHit`), member by member. -/
def PinnedAs (ci ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ∃ (kind : Ix.Kernel.BasisKind) (j : Nat) (raw : Ix.Kernel.ConstantInfo .anon),
    (kind.decls : List (Ix.Kernel.ConstantInfo .anon))[j]? = some raw ∧
    Ix.Kernel.ConstantInfo.canon ci₀ = Ix.Kernel.ConstantInfo.canon raw ∧
    (kind.declsA : List (Ix.Kernel.ConstantInfo .anon))[j]? = some ci

/-- **`ci` keeps what the record at `a` declares**: the record declares some `ci₀` (`Reads`),
and `ci` is `ci₀` stored (`StoredAs`) or the pinned basis constant `ci₀` matches (`PinnedAs`).
An axiom record is kept only at an address the role table binds a role to: the claims in
scope name no user axioms. -/
def KeepsRecord (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (a : Address)
    (ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  (IsAxiomRecord E₀ a → ∃ r, keyOf t a = .role r) ∧
    ∃ ci₀, Reads t E₀ a ci₀ ∧ (StoredAs ci ci₀ ∨ PinnedAs ci ci₀)

/-- **The consistency conclusion, per record, with no admission premise**, under the role
table `t`. There are records `E₀` the run loaded (`LoadedBy`: every record and blob is a byte
string the run hashed, under its BLAKE3 address) and an environment `env` such that

* `env`'s names are distinct;
* every constant of the claimed sub-environment (`claimedEnv`) is a projection table or keeps
  what a record of `E₀` declares (`KeepsRecord`);
* every constant address a seed covers (`SeedConstant`: the seed, or every member and
  constructor of a block seed) is kept at its key, as what its own record declares;
* the claimed sub-environment has a model in every set theory. -/
def ConsistentReadP (calls : List (Call IxVM.F)) (t : Ix.Kernel.RoleTable)
    (seeds : List Address) : Prop :=
  ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon),
    LoadedBy calls E₀ ∧
    (env.consts.map (·.name)).Nodup ∧
    (∀ ci ∈ (claimedEnv env).consts, (∃ tbl, ci = .projInfo tbl) ∨ ∃ a, KeepsRecord t E₀ a ci) ∧
    (∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
      ∃ ci, env.find? (keyOf t a') = some ci ∧ KeepsRecord t E₀ a' ci) ∧
    ∀ (W : Type u) [Ix.Kernel.SetTheory W], Nonempty (Ix.Kernel.Model W (claimedEnv env))

/-- **What a verify_claim derivation establishes, with no admission premise**: for every
claim byte string whose digest packs to `d` and decodes to an in-scope claim, every reader's
view of its seeds and every role table at the claim's address that admits as a table
(`admitBinding`) and binds a string literal's whole support (`LiteralSupportBound`), the run
hashed a collision (with the claim's bytes, the table's, the view's data or the projection
records reconstructed from the view's blocks), or `ConsistentReadP`. -/
def ConsistencySpecP (calls : List (Call IxVM.F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (c : Claim), Claim.de bytes = .ok c →
    packDigest (Address.blake3Pure bytes) = d → InScope c →
      ∀ (V : View) (seeds : List Address) (b : Binding), ClaimSeeds c V seeds →
        BindingAt c b → ∀ t : Ix.Kernel.RoleTable,
          Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t →
          LiteralSupportBound t →
            V.HashedCollision (bytes :: b.bytes :: derivedProjImages V) calls ∨
              ConsistentReadP.{u} calls t seeds

/-- **The deployed IxVM circuit accepts only claims whose claimed environment has a model**,
each claimed constant kept as its own record declares it, with no premise beyond the role
table's admission as a table: `CircuitSound` of `ConsistencySpecP`. -/
def CircuitConsistentP : Prop := CircuitSound ConsistencySpecP.{u}

/-- **No claimed constant has type `False`**, in every set theory, with no admission
premise. The claimed environment is consistent, and every constant address a seed covers (the
seed, or each member and constructor of a block seed) is kept at its key with a type other
than `False`, as what its own record declares; where the constant is stored rather than
pinned, the declared type is not `False` either. -/
theorem ConsistentReadP.seeds_not_false (W : Type u) [Ix.Kernel.SetTheory W]
    {calls : List (Call IxVM.F)} {t : Ix.Kernel.RoleTable} {seeds : List Address}
    (h : ConsistentReadP.{u} calls t seeds) :
    ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon), LoadedBy calls E₀ ∧
      Ix.Kernel.Consistent (claimedEnv env) ∧
      ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
        ∃ ci ci₀, env.find? (keyOf t a') = some ci ∧ Reads t E₀ a' ci₀ ∧
          ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] ∧
          ((StoredAs ci ci₀ ∧ ci₀.toConstantVal.type ≠ .const Ix.Kernel.falseName []) ∨
            PinnedAs ci ci₀) := by
  obtain ⟨E₀, env, hload, -, -, hseeds, hmodel⟩ := h
  have hcons : Ix.Kernel.Consistent (claimedEnv env) :=
    Ix.Kernel.consistent_of_model W (hmodel W)
  refine ⟨E₀, env, hload, hcons, fun a ha a' ha' => ?_⟩
  obtain ⟨ci, hfind, -, ci₀, hr, hkeep⟩ := hseeds a ha a' ha'
  have hci : ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] :=
    fun hf => hcons ci (seed_claimed hfind).1 hf
  refine ⟨ci, ci₀, hfind, hr, hci, ?_⟩
  rcases hkeep with hst | hpin
  · refine Or.inl ⟨hst, fun hf => ?_⟩
    have hann := hst.1.2.2
    rw [hf] at hann
    exact hci hann.const_inv
  · exact Or.inr hpin

/-- The corollary for every derivation the statement covers. -/
theorem ConsistencySpecP.no_false (W : Type u) [Ix.Kernel.SetTheory W]
    {calls : List (Call IxVM.F)} {d : Digest} (h : ConsistencySpecP.{u} calls d)
    {bytes : ByteArray} {c : Claim} (hde : Claim.de bytes = .ok c)
    (hd : packDigest (Address.blake3Pure bytes) = d) (hc : InScope c)
    {V : View} {seeds : List Address} {b : Binding} (hs : ClaimSeeds c V seeds)
    (hb : BindingAt c b) {t : Ix.Kernel.RoleTable}
    (ht : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hl : LiteralSupportBound t) :
    V.HashedCollision (bytes :: b.bytes :: derivedProjImages V) calls ∨
      ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon), LoadedBy calls E₀ ∧
        Ix.Kernel.Consistent (claimedEnv env) ∧
        ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
          ∃ ci ci₀, env.find? (keyOf t a') = some ci ∧ Reads t E₀ a' ci₀ ∧
            ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] ∧
            ((StoredAs ci ci₀ ∧ ci₀.toConstantVal.type ≠ .const Ix.Kernel.falseName []) ∨
              PinnedAs ci ci₀) :=
  (h bytes c hde hd hc V seeds b hs hb t ht hl).elim Or.inl
    fun hr => Or.inr (ConsistentReadP.seeds_not_false W hr)

/-! ## The conclusion over an admission witness -/

/-- **`ci` stores what the record at `a` declares**: the record is no axiom record, it
declares some `ci₀` (`Reads`), and `ci` is `ci₀` stored (`StoredAs`). Over an admission
witness an axiom enters the claimed environment only through the admitted prefix. -/
def StoresRecord (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (a : Address)
    (ci : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ¬ IsAxiomRecord E₀ a ∧ ∃ ci₀, Reads t E₀ a ci₀ ∧ StoredAs ci ci₀

/-- **The consistency conclusion, per record**, for the admission witness `w` of the role
table. There are records `E₀` the run loaded (`LoadedBy`: every record and blob is a byte
string the run hashed, under its BLAKE3 address) and an environment `env` such that

* `env`'s names are distinct;
* `env` keeps every constant of the witness's checked environment (`PrefixForm`);
* every constant of the claimed sub-environment (`claimedEnv`) is a projection table, a
  constant of the admitted prefix (`PrefixConstant`), or stores what a record of `E₀` that is
  no axiom record declares (`StoresRecord`);
* every constant address a seed covers (`SeedConstant`: the seed, or every member and
  constructor of a block seed) is stored at its key, as a constant of the admitted prefix or
  as what its own record declares;
* the claimed sub-environment has a model in every set theory. -/
def ConsistentReadRel (V : View) (calls : List (Call IxVM.F)) (b : Binding)
    (w : ReaderAdmissionWitness V b) (seeds : List Address) : Prop :=
  ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon),
    LoadedBy calls E₀ ∧
    (env.consts.map (·.name)).Nodup ∧
    (∀ ci' ∈ w.checkedEnv.consts, ∃ ci ∈ env.consts, PrefixForm (prefixDecls w) ci' ci) ∧
    (∀ ci ∈ (claimedEnv env).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PrefixConstant w ci ∨ ∃ a, StoresRecord w.table E₀ a ci) ∧
    (∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
      ∃ ci, env.find? (keyOf w.table a') = some ci ∧
        (PrefixConstant w ci ∨ StoresRecord w.table E₀ a' ci)) ∧
    ∀ (W : Type u) [Ix.Kernel.SetTheory W], Nonempty (Ix.Kernel.Model W (claimedEnv env))

/-- `ReaderTable` is a table at the claim's address with an admission witness. -/
theorem readerTable_iff {c : Claim} {V : View} {b : Binding} :
    ReaderTable c V b ↔ BindingAt c b ∧ Nonempty (ReaderAdmissionWitness V b) :=
  Iff.rfl

/-- **What a verify_claim derivation establishes**: for every claim byte string whose digest
packs to `d` and decodes to an in-scope claim, every reader's view of its seeds, every role
table at the claim's address and every admission witness of that table in the view, the run
hashed a collision (with the claim's bytes, the table's, the view's data or the committed
and reconstructed projection images, `readerImages V`), or `ConsistentReadRel` for that
witness. -/
def ConsistencySpecRel (calls : List (Call IxVM.F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (c : Claim), Claim.de bytes = .ok c →
    packDigest (Address.blake3Pure bytes) = d → InScope c →
      ∀ (V : View) (seeds : List Address) (b : Binding), ClaimSeeds c V seeds →
        BindingAt c b → ∀ w : ReaderAdmissionWitness V b,
          V.HashedCollision (bytes :: b.bytes :: readerImages V) calls ∨
            ConsistentReadRel.{u} V calls b w seeds

/-- **The deployed IxVM circuit accepts only claims whose claimed environment has a model**,
each claimed constant stored as its own record declares it: `CircuitSound` of
`ConsistencySpecRel`. -/
def CircuitConsistentRel : Prop := CircuitSound ConsistencySpecRel.{u}

/-! ### The corollary over an admission witness: no claimed constant has type `False` -/

/-- **No claimed constant has type `False`**, in every set theory. The claimed environment is
consistent (`Ix.Kernel.Consistent`), and every constant address a seed covers (the seed, or
each member and constructor of a block seed) is stored at its key with a type other than
`False`; when the constant is not one of the admitted prefix, the type its own record
declares is not `False` either. -/
theorem ConsistentReadRel.seeds_not_false (W : Type u) [Ix.Kernel.SetTheory W]
    {V : View} {calls : List (Call IxVM.F)} {b : Binding} {w : ReaderAdmissionWitness V b}
    {seeds : List Address} (h : ConsistentReadRel.{u} V calls b w seeds) :
    ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon), LoadedBy calls E₀ ∧
      Ix.Kernel.Consistent (claimedEnv env) ∧
      ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
        ∃ ci, env.find? (keyOf w.table a') = some ci ∧
          ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] ∧
          (PrefixConstant w ci ∨
            (¬ IsAxiomRecord E₀ a' ∧ ∃ ci₀, Reads w.table E₀ a' ci₀ ∧ StoredAs ci ci₀ ∧
              ci₀.toConstantVal.type ≠ .const Ix.Kernel.falseName [])) := by
  obtain ⟨E₀, env, hload, -, -, -, hseeds, hmodel⟩ := h
  have hcons : Ix.Kernel.Consistent (claimedEnv env) :=
    Ix.Kernel.consistent_of_model W (hmodel W)
  refine ⟨E₀, env, hload, hcons, fun a ha a' ha' => ?_⟩
  obtain ⟨ci, hfind, hprov⟩ := hseeds a ha a' ha'
  have hci : ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] :=
    fun hf => hcons ci (seed_claimed hfind).1 hf
  refine ⟨ci, hfind, hci, ?_⟩
  rcases hprov with hp | ⟨hax, ci₀, hr, hst⟩
  · exact Or.inl hp
  · refine Or.inr ⟨hax, ci₀, hr, hst, fun hf => ?_⟩
    have hann := hst.1.2.2
    rw [hf] at hann
    exact hci hann.const_inv

/-- The corollary for every derivation the statement covers. -/
theorem ConsistencySpecRel.no_false (W : Type u) [Ix.Kernel.SetTheory W]
    {calls : List (Call IxVM.F)} {d : Digest} (h : ConsistencySpecRel.{u} calls d)
    {bytes : ByteArray} {c : Claim} (hde : Claim.de bytes = .ok c)
    (hd : packDigest (Address.blake3Pure bytes) = d) (hc : InScope c)
    {V : View} {seeds : List Address} {b : Binding} (hs : ClaimSeeds c V seeds)
    (hb : BindingAt c b) (w : ReaderAdmissionWitness V b) :
    V.HashedCollision (bytes :: b.bytes :: readerImages V) calls ∨
      ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon), LoadedBy calls E₀ ∧
        Ix.Kernel.Consistent (claimedEnv env) ∧
        ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
          ∃ ci, env.find? (keyOf w.table a') = some ci ∧
            ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] ∧
            (PrefixConstant w ci ∨
              (¬ IsAxiomRecord E₀ a' ∧ ∃ ci₀, Reads w.table E₀ a' ci₀ ∧ StoredAs ci ci₀ ∧
                ci₀.toConstantVal.type ≠ .const Ix.Kernel.falseName [])) :=
  (h bytes c hde hd hc V seeds b hs hb w).elim Or.inl
    fun hr => Or.inr (ConsistentReadRel.seeds_not_false W hr)

/-! ## The admitted prefix, stored as declared

An admission whose checked environment stores what its declarations declare gives every seed,
in the prefix or not, as a declared constant stored. Whether a table's admission has this
property is a fact about that admission, decided by running it. -/

/-- **The checked environment stores the admitted declarations as declared**: every constant
of it at a key the kernel does not derive, in the form the claimed environment keeps it, is
the stored form (`StoredAs`) of a constant one of the admitted declarations installs
(`installs`). -/
def PrefixStoredAsDeclared {V : View} {b : Binding} (w : ReaderAdmissionWitness V b) : Prop :=
  ∀ ci' ∈ w.checkedEnv.consts, ∀ ci, PrefixForm (prefixDecls w) ci' ci →
    (∀ k d, ci.name ≠ .aux k d) →
    ∃ d ∈ prefixDecls w, ∃ ci₀ ∈ installs d, StoredAs ci ci₀

/-- **Under an admission that stores its declarations as declared, every seed is a declared
constant, stored**: each constant address a seed covers is stored at its key as a constant
`ci₀` that an admitted declaration installs or that its own record declares, and neither the
declared nor the stored type is `False`. -/
theorem ConsistentReadRel.seeds_declared (W : Type u) [Ix.Kernel.SetTheory W]
    {V : View} {calls : List (Call IxVM.F)} {b : Binding} {w : ReaderAdmissionWitness V b}
    {seeds : List Address} (h : ConsistentReadRel.{u} V calls b w seeds)
    (hw : PrefixStoredAsDeclared w) :
    ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon), LoadedBy calls E₀ ∧
      Ix.Kernel.Consistent (claimedEnv env) ∧
      ∀ a ∈ seeds, ∀ a', SeedConstant E₀ a a' →
        ∃ ci ci₀, env.find? (keyOf w.table a') = some ci ∧ StoredAs ci ci₀ ∧
          ((∃ d ∈ prefixDecls w, ci₀ ∈ installs d) ∨
            (¬ IsAxiomRecord E₀ a' ∧ Reads w.table E₀ a' ci₀)) ∧
          ci₀.toConstantVal.type ≠ .const Ix.Kernel.falseName [] ∧
          ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] := by
  obtain ⟨E₀, env, hload, -, -, -, hseeds, hmodel⟩ := h
  have hcons : Ix.Kernel.Consistent (claimedEnv env) :=
    Ix.Kernel.consistent_of_model W (hmodel W)
  refine ⟨E₀, env, hload, hcons, fun a ha a' ha' => ?_⟩
  obtain ⟨ci, hfind, hprov⟩ := hseeds a ha a' ha'
  obtain ⟨hmem, hna⟩ := seed_claimed hfind
  have hci : ci.toConstantVal.type ≠ .const Ix.Kernel.falseName [] :=
    fun hf => hcons ci hmem hf
  have hdecl : ∀ ci₀, StoredAs ci ci₀ →
      ci₀.toConstantVal.type ≠ .const Ix.Kernel.falseName [] := by
    intro ci₀ hst hf
    have hann := hst.1.2.2
    rw [hf] at hann
    exact hci hann.const_inv
  rcases hprov with ⟨ci', hci', hform⟩ | ⟨hax, ci₀, hr, hst⟩
  · obtain ⟨d, hd, ci₀, hci₀, hst⟩ := hw ci' hci' ci hform hna
    exact ⟨ci, ci₀, hfind, hst, Or.inl ⟨d, hd, hci₀⟩, hdecl ci₀ hst, hci⟩
  · exact ⟨ci, ci₀, hfind, hst, Or.inr ⟨hax, hr⟩, hdecl ci₀ hst, hci⟩

/-! ## The collision alternative over a view stored under its own hashes -/

/-- **A view stored under its own hashes**: every record, blob and the role table are stored
under the pure BLAKE3 hash of their bytes. Weaker than `View.Authentic`, which also asks for
canonical records. -/
def SelfHashed (V : View) : Prop :=
  (∀ a lc, V.env.consts.get? a = some lc → Address.blake3Pure lc.rawBytes = a) ∧
  (∀ a bytes, V.env.blobs.get? a = some bytes → Address.blake3Pure bytes = a) ∧
  (∀ rb, V.env.roleBinding = some rb → Address.blake3Pure rb.bytes = rb.address)

/-- An authentic view is stored under its own hashes. -/
theorem selfHashed_of_authentic {V : View} (h : V.Authentic) : SelfHashed V := by
  obtain ⟨hrec, hblob, hrole⟩ := h
  exact And.intro (fun a lc hl => (hrec a lc hl).1) (And.intro hblob hrole)

/-- **A BLAKE3 collision the run hashed one side of**: a byte string the run hashed and a
different byte string with the same pure BLAKE3 hash; or a preimage of the zero address. -/
def GenuineCollision (calls : List (Call IxVM.F)) : Prop :=
  (∃ held bytes : ByteArray, Hashed calls bytes ∧ bytes ≠ held ∧
    Address.blake3Pure bytes = Address.blake3Pure held) ∨
  ∃ bytes : ByteArray, Address.blake3Pure bytes = Ix.HostAdmission.Merkle.padding

/-- **Over a view stored under its own hashes, the collision alternative is a collision**:
`View.HashedCollision` counts a byte string the view holds at an address as a preimage of
that address whatever its hash; when the view's data is stored under its own hashes, the
alternative exhibits two different byte strings with one BLAKE3 hash, one of them hashed by
the run, or a preimage of the zero address. -/
theorem hashedCollision_genuine {V : View} (hV : SelfHashed V) {extra : List ByteArray}
    {calls : List (Call IxVM.F)} (h : V.HashedCollision extra calls) : GenuineCollision calls := by
  obtain ⟨hrec, hblob, hrole⟩ := hV
  unfold GenuineCollision
  rcases h with ⟨x, held, bytes, hheld, hh, hne, hx⟩ | ⟨bytes, -, hp⟩
  · have hx' : Address.blake3Pure held = x := by
      rcases hheld with hpre | ⟨-, hx'⟩ | ⟨-, hx'⟩
      · rcases hpre with ⟨lc, hl, hlc⟩ | hb | ⟨rb, hr, hra, hrb⟩ | ⟨_, -, -, hx'⟩
        · rw [← hlc]
          exact hrec x lc hl
        · exact hblob x held hb
        · rw [← hra, ← hrb]
          exact hrole rb hr
        · exact hx'
      · exact hx'
      · exact hx'
    exact Or.inl ⟨held, bytes, hh, hne, hx.trans hx'.symm⟩
  · exact Or.inr ⟨bytes, hp⟩

/-- **The statement over a view stored under its own hashes**: a collision the run hashed
one side of, or `ConsistentReadRel`. -/
theorem ConsistencySpecRel.selfHashed {calls : List (Call IxVM.F)} {d : Digest}
    (h : ConsistencySpecRel.{u} calls d) {bytes : ByteArray} {c : Claim}
    (hde : Claim.de bytes = .ok c) (hd : packDigest (Address.blake3Pure bytes) = d)
    (hc : InScope c) {V : View} {seeds : List Address} {b : Binding}
    (hs : ClaimSeeds c V seeds) (hb : BindingAt c b) (w : ReaderAdmissionWitness V b)
    (hV : SelfHashed V) :
    GenuineCollision calls ∨ ConsistentReadRel.{u} V calls b w seeds :=
  (h bytes c hde hd hc V seeds b hs hb w).elim
    (fun hcol => Or.inl (hashedCollision_genuine hV hcol)) Or.inr

/-- **The statement with no admission premise, over a view stored under its own hashes**: a
collision the run hashed one side of, or `ConsistentReadP`. -/
theorem ConsistencySpecP.selfHashed {calls : List (Call IxVM.F)} {d : Digest}
    (h : ConsistencySpecP.{u} calls d) {bytes : ByteArray} {c : Claim}
    (hde : Claim.de bytes = .ok c) (hd : packDigest (Address.blake3Pure bytes) = d)
    (hc : InScope c) {V : View} {seeds : List Address} {b : Binding}
    (hs : ClaimSeeds c V seeds) (hb : BindingAt c b) {t : Ix.Kernel.RoleTable}
    (ht : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hl : LiteralSupportBound t) (hV : SelfHashed V) :
    GenuineCollision calls ∨ ConsistentReadP.{u} calls t seeds :=
  (h bytes c hde hd hc V seeds b hs hb t ht hl).elim
    (fun hcol => Or.inl (hashedCollision_genuine hV hcol)) Or.inr

end IxVM.Consistency
