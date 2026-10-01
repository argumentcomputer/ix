module

public import ConLeche.Kernel.Basis.Names

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

Written out with `ConLeche.Expr`'s constructors and `Name.str` chains,
one such declaration is a single unreadable line.  The helpers below —
`pi`/`piI`/`piA`, `lm`/`lmI`, `bv`, `cnst`, `srt`, `ap2`…`ap4` — are a
one-to-one, non-abbreviating renaming of those constructors at the
*raw* binder annotations, so a reader can line the pin up against
`Init.Prelude` binder by binder and index by index.  They introduce no
new notion: every one of them is a `def` whose body is a single `Expr`
constructor application.

The annotated forms are NOT written here: they are computed from these
raw pins by the checker's own annotation pass at elaboration time
(`#annotate_basis`, `ConLeche/Kernel/BasisGen.lean`).
-/

namespace ConLeche

/-! The raw-pin builder: `Expr` constructors under the raw binder
annotations.  Opened by the pin modules (`ConLeche/Kernel/Basis/*`,
`ConLeche/Kernel/StdAxioms.lean`, `ConLeche/Kernel/TrustAxioms.lean`). -/

namespace BasisDSL

/-- A top-level (single-component) name: `bn "Eq"` is `Eq`. -/
def bn (s : String) : Name := .str .anonymous s

/-- The universe parameter `u` — every basis block's first one. -/
def uN : Name := bn "u"

/-- The universe parameter `u`, as a level. -/
def u : Level := .param uN

/-- The universe parameter `v` (`Quot.lift`'s target sort). -/
def vN : Name := bn "v"

/-- The universe parameter `v`, as a level. -/
def v : Level := .param vN

/-- The universe parameter `u_1` — the motive sort the exporter names
for a recursor whose type former already spends `u`. -/
def u1N : Name := bn "u_1"

/-- The universe parameter `u_1`, as a level. -/
def u1 : Level := .param u1N

/-- A bound variable, by de Bruijn index. -/
def bv (i : Nat) : Expr := .bvar i

/-- `Sort u`. -/
def srt (u : Level) : Expr := .sort u

/-- `Prop` = `Sort 0`. -/
def prop : Expr := .sort .zero

/-- `Type` = `Sort 1`. -/
def type1 : Expr := .sort (.succ .zero)

/-- A constant, at the given universe arguments. -/
def cnst (n : Name) (us : List Level := []) : Expr := .const n us

/-! **Binder names and binder infos are for the reader only** (tasks
#203/#205).  `Expr` carries neither (task #205: the official kernel's
equality and hash ignore both, so the fields were dropped outright), so
`pi "a"`/`piI "α"`/`lm`/`lmI` take the `Init.Prelude` spelling purely
so a reader can line the pin up binder by binder; `piI`/`lmI` mark
where the signature says `{…}`.  All five build the same node shape. -/

/-- `∀ (x : ty), body` — an explicit binder (`x` documents the
`Init.Prelude` spelling). -/
def pi (_x : String) (ty body : Expr) : Expr :=
  .forallE ty body ⟨.never⟩

/-- `∀ {x : ty}, body` — an implicit binder in `Init.Prelude` (the
same node as `pi`; the braces are for the reader). -/
def piI (_x : String) (ty body : Expr) : Expr :=
  .forallE ty body ⟨.never⟩

/-- `∀ (_ : ty), body` — an anonymous explicit binder (`ty → body`). -/
def piA (ty body : Expr) : Expr :=
  .forallE ty body ⟨.never⟩

/-- `fun (x : ty) => body` — an explicit binder (name for the reader). -/
def lm (_x : String) (ty body : Expr) : Expr :=
  .lam ty body ⟨.never⟩

/-- `fun {x : ty} => body` — an implicit binder in `Init.Prelude` (the
same node as `lm`). -/
def lmI (_x : String) (ty body : Expr) : Expr :=
  .lam ty body ⟨.never⟩

/-- Binary application. -/
def ap2 (f a b : Expr) : Expr := .app (.app f a) b

/-- Ternary application. -/
def ap3 (f a b c : Expr) : Expr := .app (.app (.app f a) b) c

/-- Quaternary application. -/
def ap4 (f a b c d : Expr) : Expr := .app (.app (.app (.app f a) b) c) d

/-- A raw iota rule: the install-computed fields (`ctorParams`,
`fire`, `k`, `eta`, `paramsBlind`) at their parse placeholders, which
is what the exporter emits and what `#annotate_basis` recomputes. -/
def rule (ctor : Name) (nfields : Nat) (rhs : Expr) : RecRule :=
  ⟨ctor, nfields, 0, .inert, rhs, false, false, false⟩

end BasisDSL

end ConLeche
