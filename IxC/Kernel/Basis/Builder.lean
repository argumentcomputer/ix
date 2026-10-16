module

public import IxC.Kernel.Basis.Names

@[expose] public section

/-!
# A tiny builder for the hand-written raw pins

The pinned basis blocks, the standard-axiom prerequisite families and
the compiler-trust pins are all *raw* `ConstantInfo`s: exactly what an
export carries for them, which is exactly the toolchain's own
`Init.Prelude` declaration — binder names and infos
are not part of an `Expr` (task #205; `piI`/`lmI` mark where the
signature says `{…}`, for the reader), the `pw` datum at the parse
placeholder `.never` — and every install-computed recursor-rule
field at its parse placeholder (`ctorParams := 0`, `fire := .inert`).

Written out with `Ix.Kernel.Expr`'s constructors and `Name.str` chains,
one such declaration is a single unreadable line.  The helpers below —
`pi`/`piI`/`piA`, `lm`/`lmI`, `bv`, `cnst`, `srt`, `ap2`…`ap4` — are a
one-to-one, non-abbreviating renaming of those constructors at the
*raw* binder annotations, so a reader can line the pin up against
`Init.Prelude` binder by binder and index by index.  They introduce no
new notion: every one of them is a `def` whose body is a single `Expr`
constructor application.

The annotated forms are NOT written here: they are computed from these
raw pins by the checker's own annotation pass at elaboration time
(`#annotate_basis`, `IxC/Kernel/BasisGen.lean`).
-/

namespace Ix.Kernel

/-! The raw-pin builder: `Expr` constructors under the raw binder
annotations.  Opened by the pin modules (`IxC/Kernel/Basis/*`,
`IxC/Kernel/StdAxioms.lean`, `IxC/Kernel/TrustAxioms.lean`). -/

namespace BasisDSL

/-- Universe parameter `0` (the exporter's `u`) — every basis block's
first one. -/
def uN : LevelParam := 0

/-- The universe parameter `uN`, as a level. -/
def u : Level := .param uN

/-- Universe parameter `1` (the exporter's `v`, `Quot.lift`'s target
sort). -/
def vN : LevelParam := 1

/-- The universe parameter `vN`, as a level. -/
def v : Level := .param vN

/-- Universe parameter `1` — a recursor's elimination parameter
after its block's one parameter `uN` (the exporter's `u_1`). -/
def u1N : LevelParam := 1

/-- The universe parameter `u1N`, as a level. -/
def u1 : Level := .param u1N

/-- A bound variable, by de Bruijn index. -/
def bv (i : Nat) : Expr md := .bvar i

/-- `Sort u`. -/
def srt (u : Level) : Expr md := .sort u

/-- `Prop` = `Sort 0`. -/
def prop : Expr md := .sort .zero

/-- `Type` = `Sort 1`. -/
def type1 : Expr md := .sort (.succ .zero)

/-- A constant, at the given universe arguments. -/
def cnst (n : Key md) (us : List Level := []) : Expr md := .const n us

/-! **Binder names and binder infos are for the reader only** (tasks
#203/#205).  `Expr` carries neither (task #205: the official kernel's
equality and hash ignore both, so the fields were dropped outright), so
`pi "a"`/`piI "α"`/`lm`/`lmI` take the `Init.Prelude` spelling purely
so a reader can line the pin up binder by binder; `piI`/`lmI` mark
where the signature says `{…}`.  All five build the same node shape. -/

/-- `∀ (x : ty), body` — an explicit binder (`x` documents the
`Init.Prelude` spelling). -/
def pi (_x : String) (ty body : Expr md) : Expr md :=
  .forallE ty body { pw := .never }

/-- `∀ {x : ty}, body` — an implicit binder in `Init.Prelude` (the
same node as `pi`; the braces are for the reader). -/
def piI (_x : String) (ty body : Expr md) : Expr md :=
  .forallE ty body { pw := .never }

/-- `∀ (_ : ty), body` — an anonymous explicit binder (`ty → body`). -/
def piA (ty body : Expr md) : Expr md :=
  .forallE ty body { pw := .never }

/-- `fun (x : ty) => body` — an explicit binder (name for the reader). -/
def lm (_x : String) (ty body : Expr md) : Expr md :=
  .lam ty body { pw := .never }

/-- `fun {x : ty} => body` — an implicit binder in `Init.Prelude` (the
same node as `lm`). -/
def lmI (_x : String) (ty body : Expr md) : Expr md :=
  .lam ty body { pw := .never }

/-- Binary application. -/
def ap2 (f a b : Expr md) : Expr md := .app (.app f a) b

/-- Ternary application. -/
def ap3 (f a b c : Expr md) : Expr md := .app (.app (.app f a) b) c

/-- Quaternary application. -/
def ap4 (f a b c d : Expr md) : Expr md := .app (.app (.app (.app f a) b) c) d

/-- A raw iota rule: the install-computed fields (`ctorParams`,
`fire`, `k`, `eta`, `paramsBlind`) at their parse placeholders, which
is what the exporter emits and what `#annotate_basis` recomputes. -/
def rule (ctor : Key md) (nfields : Nat) (rhs : Expr md) : RecRule md :=
  ⟨ctor, nfields, 0, .inert, rhs, false, false, false⟩

end BasisDSL

end Ix.Kernel
