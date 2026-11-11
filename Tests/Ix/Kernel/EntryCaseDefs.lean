import Tests.Ix.Kernel.TutorialMeta

/-! # Lean sources of the certified entry's host cases

Ordinary Lean declarations that `kernel-entry-cases`
(`Tests.Ix.Kernel.EntryCases`) loads from this module's `.olean`, compiles
with Ix's compiler and submits, as canonical record bytes, to the certified
entry `Ix.Kernel.Admission.checkBytes`. Lean's kernel checked every
declaration here except the ones installed unchecked
(`TutorialMeta.bad_thm`, `bad_decl`), the inputs of the wrong type:
`levelWrong`, `falseThm` (its value is `True.intro`) and the false ι and
constructor equations at the nested blocks (`nb4IotaFalse`, `ra1IotaFalse`,
`bd2CtorFalse`, ...). `BD1` and `BD2` are declared through Lean's kernel.
-/

open Tests.Ix.Kernel.TutorialMeta

namespace Tests.Ix.Kernel.EntryCaseDefs

universe u

/-! ## Accepted -/

/-- A definition. -/
def twice {α : Sort u} (f : α → α) (a : α) : α := f (f a)

/-- A theorem, by δ through `twice` and `id`. -/
theorem twiceId {α : Sort u} (a : α) : twice id a = a := rfl

/-- An inductive with its recursor, and an ι-reduction through it. -/
inductive Color where
  | red
  | green
  | blue

noncomputable def Color.next (c : Color) : Color :=
  Color.rec (motive := fun _ => Color) .green .blue .red c

theorem Color.nextRed : Color.red.next = .green := rfl

/-- A structure, its projection function, and a projection reduction. -/
structure Point where
  x : Nat
  y : Nat

theorem Point.xMk : (Point.mk Nat.zero (Nat.succ Nat.zero)).x = Nat.zero := rfl

/-- The quotient's lift reduction. -/
theorem quotLiftMk (r : Nat → Nat → Prop) (f : Nat → Nat) (h : ∀ a b, r a b → f a = f b)
    (a : Nat) : Quot.lift f h (Quot.mk r a) = f a := rfl

/-- A `Nat` literal against its constructors. -/
theorem natLit : (2 : Nat) = Nat.succ (Nat.succ Nat.zero) := rfl

/-- A pinned `Nat` operation on literals. -/
theorem natAdd : (2 : Nat) + 3 = 5 := rfl

/-- A `String` literal against its `String.ofList` expansion. -/
theorem strLit : "ab" = String.ofList [Char.ofNat 97, Char.ofNat 98] := rfl

/-- A nested inductive (through `List`). -/
inductive Tree where
  | node : List Tree → Tree

/-- A container that is itself nested (through `List`). -/
inductive LNode (α : Type) where
  | node : List (LNode α) → LNode α
  | leaf : α → LNode α

/-- A block nested through a container that is itself nested. Ix's compiler
orders `LTree.rec`'s auxiliary motives canonically, as
`[List (LNode LTree), LNode LTree]`: the container family's instance before
its head, an order in which the in-process modeller must still emit each
`pack_i` once. -/
inductive LTree where
  | node : LNode LTree → LTree

/-- The shape of `Lean.Elab.InfoTree`: nested through a structure whose field
is nested through `Array` (`PersistentArray` → `PersistentArrayNode`). Its
auxiliary motives are compiled as `[Array ITree, Array (PNode ITree), PArr
ITree, List (PNode ITree), List ITree, PNode ITree]`, as `InfoTree`'s are. -/
inductive PNode (α : Type) where
  | node : Array (PNode α) → PNode α
  | leaf : Array α → PNode α

structure PArr (α : Type) where
  root : PNode α
  tail : Array α
  size : Nat

inductive ITree where
  | context : Nat → ITree → ITree
  | node : Nat → PArr ITree → ITree
  | hole : Nat → ITree

-- A mutual inductive block: terms and their argument lists.
mutual
inductive Tm where
  | var : Nat → Tm
  | app : Nat → Args → Tm
inductive Args where
  | nil : Args
  | cons : Tm → Args → Args
end

-- Definitions by structural recursion over the mutual block (through
-- `Tm.brecOn` and `Args.brecOn`), and a reduction through them.
mutual
def Tm.size : Tm → Nat
  | .var _ => 1
  | .app _ as => as.size + 1
def Args.size : Args → Nat
  | .nil => 0
  | .cons t as => t.size + as.size
end

theorem Tm.sizeApp : (Tm.app 0 (.cons (.var 0) .nil)).size = 2 := rfl

-- A block both mutual and nested: argument lists through `List`.
mutual
inductive MTm where
  | var : Nat → MTm
  | app : Nat → List MArg → MTm
inductive MArg where
  | pos : MTm → MArg
  | named : Nat → MTm → MArg
end

/-- Nested blocks whose index domain mentions a parameter: the nested
occurrences' index arguments (`a₀`, `[]`) mention the parameters too. -/
inductive NB (α : Type) (a₀ : α) : α → Type where
  | base : NB α a₀ a₀
  | mk : List (NB α a₀ a₀) → NB α a₀ a₀

inductive NB4 (α : Type) : List α → Type where
  | nil : NB4 α []
  | mk : List (NB4 α []) → NB4 α []

/-- A value by `NB4`'s recursors (both motives), and its ι reduction. -/
noncomputable def nb4Val (t : NB4 Nat []) : Nat :=
  NB4.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ => Nat) 0 (fun _ ih => ih + 1) 0
    (fun _ _ ih1 ih2 => ih1 + ih2 + 1) t

theorem nb4Iota : nb4Val (NB4.mk [NB4.nil]) = 2 := rfl

/-- Nested blocks with a reflexive field into a member: in a constructor of
the block (`RA1`), and in a container pinned at a function into the block
(`RA3`: the container's own field, `Option.some`'s, is reflexive). -/
inductive RA1 where
  | leaf : RA1
  | mk : (Nat → RA1) → List RA1 → RA1

inductive RA3 where
  | leaf : RA3
  | mk : Option (Nat → RA3) → RA3

/-- Values by the blocks' recursors, and ι reductions through the
reflexive fields' hypotheses. -/
noncomputable def ra1Val (t : RA1) : Nat :=
  RA1.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) 1 (fun _ _ ihf ihl => ihf 0 + ihl + 1) 0
    (fun _ _ ih1 ih2 => ih1 + ih2) t

theorem ra1Iota : ra1Val (RA1.mk (fun _ => RA1.leaf) [RA1.leaf]) = 3 := rfl

noncomputable def ra3Val (t : RA3) : Nat :=
  RA3.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) 1 (fun _ ih => ih + 1) 0
    (fun _ ih => ih 0 + 5) t

theorem ra3Iota : ra3Val (RA3.mk (some fun _ => RA3.leaf)) = 7 := rfl

/-- Nested blocks with a recursive occurrence behind a definition (`Id' T`,
which Lean's kernel reads after whnf): in a constructor of the block (`BD1`)
and in a container's (`BD2`, through `List (Id' BD2)`). Declared through
Lean's kernel: the elaborator's `SizeOf` generation fails on them. -/
def Id' (α : Type) : Type := α

open Lean in
run_cmd Elab.Command.liftCoreM do
  let ns := `Tests.Ix.Kernel.EntryCaseDefs
  let idT (t : Expr) := mkApp (mkConst (ns ++ `Id')) t
  let list (t : Expr) := mkApp (mkConst ``List [levelZero]) t
  let bd1 := mkConst (ns ++ `BD1)
  addDecl (.inductDecl [] 0 [⟨ns ++ `BD1, mkSort levelOne,
    [⟨ns ++ `BD1.leaf, bd1⟩,
     ⟨ns ++ `BD1.mk, mkForall `a .default (idT bd1) (mkForall `b .default (list bd1) bd1)⟩]⟩] false)
  let bd2 := mkConst (ns ++ `BD2)
  addDecl (.inductDecl [] 0 [⟨ns ++ `BD2, mkSort levelOne,
    [⟨ns ++ `BD2.leaf, bd2⟩, ⟨ns ++ `BD2.mk, mkForall `a .default (list (idT bd2)) bd2⟩]⟩] false)

/-- Values by the blocks' recursors, and ι reductions through the
hypotheses of the fields behind `Id'`. -/
noncomputable def bd1Val (t : BD1) : Nat :=
  BD1.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) 1 (fun _ _ iha ihb => iha + ihb + 1) 0
    (fun _ _ ih1 ih2 => ih1 + ih2) t

theorem bd1Iota : bd1Val (BD1.mk BD1.leaf [BD1.leaf]) = 3 := rfl

noncomputable def bd2Val (t : BD2) : Nat :=
  BD2.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) 1 (fun _ ih => ih + 1) 0
    (fun _ _ ih1 ih2 => ih1 + ih2) t

theorem bd2Iota : bd2Val (BD2.mk [BD2.leaf]) = 2 := rfl

/-- The face of a `partial` definition: an opaque constant whose value is an
inhabitant of its type. The recursive body is the `partial` companion
`loop._unsafe_rec`. -/
partial def loop (n : Nat) : Nat := loop (n + 1)

/- A mutual `partial` block of three (the typing tier): Lean adds the
companions `ping._unsafe_rec`, `pong._unsafe_rec` and `pang._unsafe_rec` as one
partial `mutualDefnDecl`. The bodies differ, so that the compiler keeps
three members (alpha-equivalent members collapse into one). -/
mutual
partial def ping (n : Nat) : Nat := pong (n + 1)
partial def pong (n : Nat) : Nat := pang (n + 2)
partial def pang (n : Nat) : Nat := ping (n + 3)
end

/- `badFalse : False := badFalse`, a partial definition of `False`, which
Lean's kernel accepts in partial mode (the elaborator would want `Inhabited
False`, so it is added directly). The typing tier types it with itself
opaque; the logical environment never holds it. -/
open Lean in
run_meta do
  let n := `Tests.Ix.Kernel.EntryCaseDefs.badFalse
  addDecl (.mutualDefnDecl [
    { name := n, levelParams := [], type := mkConst ``False, value := mkConst n,
      hints := .opaque, safety := .partial, all := [n] }])

/- `deltaT : Sort 2 → Sort 2 := fun x => x` and `deltaUse : deltaT (Sort 1) :=
Sort 0`, partial: Lean's kernel accepts `deltaUse` by unfolding `deltaT`
(`is_delta` unfolds partial definitions); the typing tier keeps `deltaT`
opaque, so it declines `deltaUse`. -/
open Lean in
run_meta do
  let T := `Tests.Ix.Kernel.EntryCaseDefs.deltaT
  let U := `Tests.Ix.Kernel.EntryCaseDefs.deltaUse
  let s2 := mkSort (.succ .one)
  addDecl (.mutualDefnDecl [
    { name := T, levelParams := [], type := .forallE `x s2 s2 .default,
      value := .lam `x s2 (.bvar 0) .default, hints := .opaque, safety := .partial, all := [T] }])
  addDecl (.mutualDefnDecl [
    { name := U, levelParams := [], type := mkApp (mkConst T) (mkSort .one),
      value := mkSort .zero, hints := .opaque, safety := .partial, all := [U] }])

/- The unsafe stage of the typing tier: an unsafe definition, an unsafe
opaque (Lean checks it in safe mode), an unsafe axiom of `False` and an
unsafe definition of `False` by it. The tier types all four; the logical
environment never holds them. -/
unsafe def unsafeSucc (n : Nat) : Nat := n + 1
unsafe opaque unsafeOpq : Nat
unsafe axiom unsafeAx : False
-- a definition of a proposition on purpose: Lean has no unsafe theorems
set_option linter.defProp false in
unsafe def unsafeFalse : False := unsafeAx

/-- An equation between elements of a `Subtype` of a type in
`Sort (imax (u+2) (imax (v+1) v))`, the shape of `RatFunc.liftOn_def` (an
`irreducible_def` unfolding lemma). Lean elaborates `Subtype.{W}` and
`Eq.{max 1 W}`; Ix's compiler stores each level as its canonical form,
`Subtype.{imax (max (u+2) (v+1)) v}` and `Eq.{max (v+1) (imax (u+2) v)}`.
The `Subtype`'s type `Sort (max (imax (max (u+2) (v+1)) v) 1)` is the
`Eq`'s domain at every valuation, which nanoda's level comparison (the
official kernel's) does not establish; the kernel's comparison decides that
case by Géran's sublevels (`IxC/Kernel/LevelGeran.lean`).
-/
theorem levelCanon.{w, x} {a b : {_f : (K : Type w) → (P : Sort x) → P // True}} (h : a = b) :
    a = b := h

/-! ## Refused -/

/-- An axiom other than the pinned standard ones. -/
axiom someAxiom (n : Nat) : n = n

-- `∀ (α : Sort w) (a : α), @Eq.{w+1} α a a`, by `Eq.refl.{w+1}`: an
-- equation at the wrong universe level, installed in Lean unchecked. No
-- valuation of `w` makes it well typed: a reject by the complete level
-- comparison, not a decline.
bad_decl .thmDecl {
  name := `Tests.Ix.Kernel.EntryCaseDefs.levelWrong
  levelParams := [`w]
  type := .forallE `α (.sort (.param `w))
    (.forallE `a (.bvar 0) (Lean.mkApp3 (.const ``Eq [.succ (.param `w)]) (.bvar 1) (.bvar 0) (.bvar 0))
      .default) .default
  value := .lam `α (.sort (.param `w))
    (.lam `a (.bvar 0) (Lean.mkApp2 (.const ``Eq.refl [.succ (.param `w)]) (.bvar 1) (.bvar 0)) .default)
    .default }

-- A theorem of `False`, installed in Lean unchecked.
bad_thm falseThm : False := unchecked True.intro

-- A false ι equation and a false constructor equation at `NB4`, installed in
-- Lean unchecked: the modeled route's recursor and constructors must not
-- equate them.
bad_thm nb4IotaFalse : nb4Val (NB4.mk [NB4.nil]) = 3 := unchecked (Eq.refl (nb4Val (NB4.mk [NB4.nil])))

bad_thm nb4CtorFalse : NB4.nil (α := Nat) = NB4.mk [] := unchecked (Eq.refl (NB4.nil (α := Nat)))

-- False ι equations through the reflexive fields of `RA1` and `RA3`, and a
-- false constructor equation at `RA3`, installed in Lean unchecked.
bad_thm ra1IotaFalse : ra1Val (RA1.mk (fun _ => RA1.leaf) [RA1.leaf]) = 4 :=
  unchecked (Eq.refl (ra1Val (RA1.mk (fun _ => RA1.leaf) [RA1.leaf])))

bad_thm ra3IotaFalse : ra3Val (RA3.mk (some fun _ => RA3.leaf)) = 6 :=
  unchecked (Eq.refl (ra3Val (RA3.mk (some fun _ => RA3.leaf))))

bad_thm ra3CtorFalse : RA3.mk none = RA3.leaf := unchecked (Eq.refl (RA3.mk none))

-- A false ι equation through `BD1`'s field behind `Id'`, and a false
-- constructor equation at `BD2`, installed in Lean unchecked.
bad_thm bd1IotaFalse : bd1Val (BD1.mk BD1.leaf [BD1.leaf]) = 4 :=
  unchecked (Eq.refl (bd1Val (BD1.mk BD1.leaf [BD1.leaf])))

bad_thm bd2CtorFalse : BD2.mk [] = BD2.leaf := unchecked (Eq.refl (BD2.mk []))

end Tests.Ix.Kernel.EntryCaseDefs
