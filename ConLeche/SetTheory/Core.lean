module

@[expose] public section

/-!
# The axiomatic core: ZF⁻ plus an ω-chain of Grothendieck universes

The `SetTheory` class below is the *entire* axiomatic interface of the
consistency proof; every operator and law the model construction uses
(`ConLeche/SetTheory/Basic.lean`) is *derived* from it in
`ConLeche/SetTheory/Derive/*`, never assumed.

The set-theoretic axioms are **extensionality, pairing, union, power
set, regularity, the replacement scheme, and an ω-chain of
Grothendieck universes** `univChain 0 ∈ univChain 1 ∈ …` —
universehood stated as the matrix of Tarski's Axiom A (A. Tarski,
*Über unerreichbare Kardinalzahlen*, Fund. Math. 30 (1938), 68–89)
strengthened with a transitivity clause, i.e. as Grothendieck
universes (SGA 4, Exp. I, Appendix).  Infinity and choice are
derivable and therefore absent.

This calibrates the axiomatic strength to exactly what the checker
consumes — the ω-indexed tower `univ 0, univ 1, univ 2, …` — and to
the known consistency strength of Lean itself: ZFC plus a strictly
increasing ω-sequence of inaccessible cardinals — the
`OmegaInaccessibles` hypothesis
`∃ κ : ℕ → Cardinal, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible`
of Mario Carneiro, *The Type Theory of Lean*, master's thesis,
Carnegie Mellon University, 2019, §1.2.  Under that hypothesis the intended
model takes `univChain n := V_{κ n}`.  This is strictly weaker than
full Tarski–Grothendieck set theory (Tarski's Axiom A places a
universe above *every* set, a proper class of inaccessibles; cf. the
Mizar axiomatics, A. Trybulec, *Tarski Grothendieck Set Theory*,
Formalized Mathematics 1(1), 1990).

Deliberate deviations from a first-order presentation:

* **Replacement** is a Lean-level scheme: the image operator takes an
  arbitrary function `V → V`.  This is the usual strengthening when the
  ambient logic can quantify over class functions; `V_κ` for `κ`
  inaccessible still satisfies it.
* **Choice is not a field.**  A first-order axiomatization must assert
  choice; here the ambient logic is Lean with `Classical.choice`, and
  every set-level form of choice over `V` (the global selector
  `schoice`, and the Jech-form choice-function statement, *Set Theory*,
  §5) is a *theorem* — replacement applied to a classically chosen
  selector.  See `ConLeche/SetTheory/Derive/Choice.lean`.  Asserting it
  here would add redundant axiomatic content; global choice is supplied
  by the meta-logic, not by this class.
* **No `nonempty` field.**  First-order logic's nonempty domain is
  implied: `univChain` already exhibits elements of `V`.

Everything else — the empty set, separation, ordered pairs, infinity,
function graphs, the universe tower, quotients — is constructed in
`ConLeche/SetTheory/Derive/*`.
-/

namespace ConLeche

universe u

/-- `y` and `u` are equinumerous: some (meta-level) function restricts to
a bijection from the members of `y` onto the members of `u`.  This is the
notion Tarski's Axiom A is stated with; using a Lean-level function keeps
ordered pairs out of the core (a first-order presentation instead
describes set-level bijections by formulas).  For the intended models this is
equivalent: a set-level bijection yields a meta-level one by choice, and
the axiom's disjunction is only ever *used* by refuting this side via a
diagonal argument (`Derive/Universe.lean`). -/
def Equinumerous {V : Type u} (mem : V → V → Prop) (y u : V) : Prop :=
  ∃ f : V → V,
    (∀ z, mem z y → mem (f z) u) ∧
    (∀ z z', mem z y → mem z' y → f z = f z' → z = z') ∧
    (∀ w, mem w u → ∃ z, mem z y ∧ f z = w)

/-- The matrix of Tarski's Axiom A (Tarski 1938), strengthened with the
transitivity clause: `u` is a Grothendieck universe (SGA 4, Exp. I,
Appendix).  The four clauses, in order:

1. *transitivity*: members of members are members — the clause that
   distinguishes a Grothendieck universe from a bare Tarski one, and
   what makes the empty set fall out of regularity;
2. *subsets of members are members*;
3. *power sets stay inside*: some member contains all subsets of a
   member (with clause 2 this makes `power y` itself a member);
4. *inaccessibility*: a subset of `u` is equinumerous with `u` or a
   member.  Dropping the equinumerosity disjunct is **inconsistent**
   (`u ⊆ u` would force `u ∈ u`, against regularity). -/
def IsTGUniverse {V : Type u} (mem : V → V → Prop) (u : V) : Prop :=
  (∀ y z, mem y u → mem z y → mem z u) ∧
  (∀ y z, mem y u → (∀ w, mem w z → mem w y) → mem z u) ∧
  (∀ y, mem y u → ∃ p, mem p u ∧ ∀ z, (∀ w, mem w z → mem w y) → mem z p) ∧
  (∀ y, (∀ w, mem w y → mem w u) → Equinumerous mem y u ∨ mem y u)

/-- A model of set theory of exactly the strength the checker needs:
membership, the six ZF⁻ axioms (extensionality, pairing, union, power
set, regularity, Lean-level replacement), and an ω-chain of
Grothendieck universes.  Infinity is derivable; choice is inherited
from the meta-logic (`Classical.choice`); see the module docstring. -/
class SetTheory (V : Type u) where
  /-- Set membership. -/
  Mem : V → V → Prop
  /-- Extensionality: sets with the same members are equal. -/
  ext : ∀ {x y : V}, (∀ z, Mem z x ↔ Mem z y) → x = y
  /-- Pairing: the unordered pair. -/
  upair : V → V → V
  /-- Characterization of the unordered pair. -/
  mem_upair : ∀ {z a b : V}, Mem z (upair a b) ↔ z = a ∨ z = b
  /-- Union: the union of the members. -/
  sUnion : V → V
  /-- Characterization of the union. -/
  mem_sUnion : ∀ {z x : V}, Mem z (sUnion x) ↔ ∃ y, Mem y x ∧ Mem z y
  /-- Power set. -/
  power : V → V
  /-- Characterization of the power set: members are the subsets. -/
  mem_power : ∀ {z x : V}, Mem z (power x) ↔ ∀ w, Mem w z → Mem w x
  /-- Regularity: every nonempty set has an `∈`-minimal member. -/
  regularity : ∀ x : V, (∃ y, Mem y x) → ∃ y, Mem y x ∧ ¬ ∃ z, Mem z y ∧ Mem z x
  /-- Replacement, as a Lean-level scheme: the image of a set under an
  arbitrary function `V → V`. -/
  image : (V → V) → V → V
  /-- Characterization of the replacement image. -/
  mem_image : ∀ {f : V → V} {a z : V}, Mem z (image f a) ↔ ∃ w, Mem w a ∧ z = f w
  /-- An ω-chain of Grothendieck universes: the sets interpreting the
  universe tower (Carneiro's ω-many inaccessibles, op. cit.;
  intended model `V_{κ n}`). -/
  univChain : Nat → V
  /-- The chain increases strictly: each universe is a member of the
  next. -/
  univChain_mem : ∀ n : Nat, Mem (univChain n) (univChain (n + 1))
  /-- Each chain member is a Grothendieck universe (Tarski's Axiom A
  matrix with transitivity, `IsTGUniverse`). -/
  univChain_tg : ∀ n : Nat, IsTGUniverse Mem (univChain n)

namespace SetTheory

@[inherit_doc] scoped infix:50 " ∈ˢ " => Mem

variable {V : Type u} [SetTheory V]

/-- Subset, from membership. -/
protected def Subset (x y : V) : Prop := ∀ z, z ∈ˢ x → z ∈ˢ y

@[inherit_doc] scoped infix:50 " ⊆ˢ " => SetTheory.Subset

theorem Subset.refl (x : V) : x ⊆ˢ x := fun _ hz => hz

theorem Subset.trans {x y z : V} (h₁ : x ⊆ˢ y) (h₂ : y ⊆ˢ z) : x ⊆ˢ z :=
  fun w hw => h₂ w (h₁ w hw)

theorem Subset.antisymm {x y : V} (h₁ : x ⊆ˢ y) (h₂ : y ⊆ˢ x) : x = y :=
  ext fun z => ⟨h₁ z, h₂ z⟩

theorem mem_power_iff_subset {z x : V} : z ∈ˢ power x ↔ z ⊆ˢ x := mem_power

end SetTheory

end ConLeche
