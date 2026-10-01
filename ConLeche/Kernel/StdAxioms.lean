module

public import ConLeche.Kernel.BasisA
public meta import ConLeche.Kernel.BasisA
import ConLeche.Kernel.BasisGen

@[expose] public section

/-!
# Recognized standard axioms and their prerequisite shapes

A stream may use the standard axioms `propext` and `Classical.choice`.
Both are true in the set-theoretic model — `propext` by extensionality
of propositions (derived through the stored `Iff` recursor),
`Classical.choice` by global choice (through the stored `Nonempty`
recursor) — so the checker accepts exactly these two axioms, after
pinning their types and the *shapes of the inductives they quantify
over* to the toolchain's.  Raw pins below, hand-written through the builder
in `ConLeche/Kernel/Basis/Builder.lean`; the annotated forms — what the
checker's own annotation produces for them, in dependency order — are
computed from them at elaboration time by `#annotate_basis` /
`#annotate_pins` (`ConLeche/Kernel/BasisGen.lean`).

**Binder annotations (tasks #142, #203, #205).**  A pin carries no
binder name and no binder info — `Expr` has neither field (task #205),
so `propext`'s `{a b : Prop}` and `Classical.choice`'s `{α}` are
`pi`/`piI` for the reader only.  The comparison `ConstantVal.matchesPin`
is exact up to the `pw` datum (`erasePw`); `Expr.ErasedEq` — the
model's "same denotation" relation, up to `fvar` type annotations —
bridges a hit.
-/

namespace ConLeche

open Name (anonymous)
open BasisDSL

/-- The name `propext`. -/
def propextName : Name := anonymous |>.str "propext"

/-- The name `Classical.choice`. -/
def choiceName : Name := (anonymous |>.str "Classical") |>.str "choice"

/-- The name `Iff`. -/
def iffName : Name := anonymous |>.str "Iff"

/-- The name `Iff.intro`. -/
def iffIntroName : Name := iffName |>.str "intro"

/-- The name `Iff.rec`. -/
def iffRecName : Name := iffName |>.str "rec"

/-- The name `Nonempty`. -/
def nonemptyName : Name := anonymous |>.str "Nonempty"

/-- The name `Nonempty.intro`. -/
def nonemptyIntroName : Name := nonemptyName |>.str "intro"

/-- The name `Nonempty.rec`. -/
def nonemptyRecName : Name := nonemptyName |>.str "rec"

/-- Shape comparison for the standard pins: exact name, level
parameters and counts, type up to the `pw` datum.

**Guidance for anyone adding a pin.**  Two properties of a pin decide
how expensive it is for a *consumer* of the pin (the checker's own
soundness proofs, and the type-theory bridge of task #119):

* **Pin the level when the artifact only ever needs one.**  A pin that
  quantifies a level is more general, and that generality is paid for
  by every consumer: it must supply a level assignment and carry it
  through each application.  Measured instance —
  `Nonempty.rec`'s motive sort is pinned to `Prop` while
  `Iff.rec.{u_1,u}` quantifies its, and the bridge's `Iff` elimination
  needed a bespoke assignment driving `u_1` to `0` where the
  `Nonempty` one needed nothing at all.  *A pin that fixes a level is
  easier to consume than a pin that quantifies one, even when the
  quantified pin is more general.*
* **What this comparison forgives is what the interpretation ignores.**
  `matchesPin` accepts a stored type equal to the pin *up to binder
  names*, and neither the set model's `interpExpr` nor the bridge's
  `denote` reads a binder name — a binder is opened with a variable
  whose meaning is its de Bruijn index.  That alignment is why a
  `matchesPin` hit is usable at all: a consumer may compute on the
  *pin* rather than on whatever spelling the input stream sent.
  Preserve it — a pin comparison must never forgive something the
  interpretation reads.

**Task #161 P5, the `pw` exception (and why it is not a violation of
the rule above).**  The comparison is also up to the binder
*prop-ness datum*: the pins carry the generated (true) datum, while
the compared side carries whatever the mode produced — the pass's
written datum at `--verified`, the parse placeholder `.never` at
`--trusted`, where nothing reads annotations at all.  Forgiving it
here is safe *because the consumer computes on the pin*: the pin's
datum is the generated one, so a consumer never sees a placeholder;
and at `--verified` the compared side's datum is independently
validated against the checker's own inference at the front door
(a genuinely wrong datum declines there, not here).  Left unforgiven,
`--trusted` — which writes nothing — would stop matching every
annotated pin, i.e. an annotation-only deviation would change a
verdict, exactly what the binder-info paragraph above forbids. -/
def Expr.erasePw : Expr → Expr
  | .bvar i => .bvar i
  | .fvar i ty => .fvar i ty.erasePw
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app f.erasePw a.erasePw
  | .lam ty b _ => .lam ty.erasePw b.erasePw ⟨.never⟩
  | .forallE ty b _ => .forallE ty.erasePw b.erasePw ⟨.never⟩
  | .letE ty v b => .letE ty.erasePw v.erasePw b.erasePw
  | .lit l => .lit l
  | .proj s i e => .proj s i e.erasePw

def ConstantVal.matchesPin (cv pin : ConstantVal) : Bool :=
  cv.name = pin.name && cv.levelParams = pin.levelParams &&
    cv.type.erasePw == pin.type.erasePw

/-! ### The lockstep comparison (task #226)

`matchesPin` above is the SPECIFICATION, and every proof about a pin
hit consumes it (`Verify/StdAxiomPin.lean`, `Verify/OfReducePin.lean`,
`Verify/ReducePinInv.lean`, `Model/DivMod.lean`).  What it says to do
— build `erasePw` of BOTH sides, then compare — is `O(tree)` on the
side that comes from the stream: `Expr.erasePw` rebuilds every node,
so a DAG-shared type unfolds.  `tests/e2e/tower_axiom_pin.ndjson`
(a `propext` whose type carries a depth-60 shared tower over a
standardly-shaped stored `Iff`) exhausts memory on it.

`Expr.erasePwEq` decides the same question by descending **both**
terms together and stopping at the first disagreement.  Wherever the
two agree they have the pin's shape, so the walk is bounded by the
PIN's tree size — a few dozen nodes — however large the stream side
is; and where they disagree it stops there.  `matchesPinFast` is
swapped in for `matchesPin` by `@[csimp]` below, so the executed
comparison is the lockstep one and the specification every proof reads
is unchanged: same verdict on every input, only the work changes. -/

/-- `a.erasePw = b.erasePw`, decided in lockstep
(`erasePwEq_eq`). -/
def Expr.erasePwEq : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i t, .fvar j t' => i == j && t.erasePwEq t'
  | .sort u, .sort v => u == v
  | .const n us, .const n' us' => n == n' && us == us'
  | .app f a, .app f' a' => f.erasePwEq f' && a.erasePwEq a'
  | .lam t b _, .lam t' b' _ => t.erasePwEq t' && b.erasePwEq b'
  | .forallE t b _, .forallE t' b' _ => t.erasePwEq t' && b.erasePwEq b'
  | .letE t v b, .letE t' v' b' =>
      t.erasePwEq t' && v.erasePwEq v' && b.erasePwEq b'
  | .lit l, .lit l' => l == l'
  | .proj s i e, .proj s' i' e' => s == s' && i == i' && e.erasePwEq e'
  | _, _ => false

/-- **The agreement**, propositional half: the lockstep descent holds
exactly when the two erased forms are equal.  `erasePw` preserves
every node's constructor and its non-recursive fields (it only resets
the binder `pw` datum), so two erased terms are equal iff the
originals agree constructor by constructor down to their leaves —
which is what the descent tests. -/
theorem Expr.erasePwEq_iff :
    ∀ a b : Expr, a.erasePwEq b = true ↔ a.erasePw = b.erasePw := by
  intro a
  induction a with
  | bvar i => intro b; cases b <;> simp [Expr.erasePwEq, Expr.erasePw]
  | fvar i t ih =>
    intro b; cases b <;> simp [Expr.erasePwEq, Expr.erasePw, Bool.and_eq_true, ih]
  | sort u => intro b; cases b <;> simp [Expr.erasePwEq, Expr.erasePw]
  | const n us => intro b; cases b <;> simp [Expr.erasePwEq, Expr.erasePw]
  | app f a ihf iha =>
    intro b; cases b <;>
      simp [Expr.erasePwEq, Expr.erasePw, Bool.and_eq_true, ihf, iha]
  | lam t b m iht ihb =>
    intro c; cases c <;>
      simp [Expr.erasePwEq, Expr.erasePw, Bool.and_eq_true, iht, ihb]
  | forallE t b m iht ihb =>
    intro c; cases c <;>
      simp [Expr.erasePwEq, Expr.erasePw, Bool.and_eq_true, iht, ihb]
  | letE t v b iht ihv ihb =>
    intro c; cases c <;>
      simp [Expr.erasePwEq, Expr.erasePw, Bool.and_eq_true, iht, ihv, ihb, and_assoc]
  | lit l => intro b; cases b <;> simp [Expr.erasePwEq, Expr.erasePw]
  | proj s i e ih =>
    intro b; cases b <;>
      simp [Expr.erasePwEq, Expr.erasePw, Bool.and_eq_true, ih, and_assoc]

/-- **The agreement**: the lockstep comparison returns exactly what
`matchesPin`'s equation test returns, on every pair of terms. -/
theorem Expr.erasePwEq_eq (a b : Expr) :
    a.erasePwEq b = (a.erasePw == b.erasePw) := by
  cases hb : (a.erasePw == b.erasePw) with
  | true => exact (Expr.erasePwEq_iff a b).2 (eq_of_beq hb)
  | false =>
    refine Bool.eq_false_iff.2 fun h => ?_
    exact absurd ((Expr.erasePwEq_iff a b).1 h) (by simpa using hb)

/-- `matchesPin` at the lockstep comparison (`@[csimp]` below): the
executed shape test. -/
def ConstantVal.matchesPinFast (cv pin : ConstantVal) : Bool :=
  cv.name = pin.name && cv.levelParams = pin.levelParams &&
    cv.type.erasePwEq pin.type

@[csimp] theorem ConstantVal.matchesPin_eq_matchesPinFast :
    @ConstantVal.matchesPin = @ConstantVal.matchesPinFast := by
  funext cv pin
  simp [ConstantVal.matchesPin, ConstantVal.matchesPinFast, Expr.erasePwEq_eq]

/-- `Iff (a b : Prop) : Prop`. -/
def iffRaw : ConstantInfo :=
  .indInfo ⟨iffName, [], pi "a" prop <| pi "b" prop prop⟩ {}

/-- `Iff.intro (a b : Prop) (mp : a → b) (mpr : b → a) : Iff a b`. -/
def iffIntroRaw : ConstantInfo :=
  .ctorInfo ⟨iffIntroName, [],
    pi "a" prop <|
    pi "b" prop <|
    pi "mp" (piA (bv 1) (bv 1)) <|
    pi "mpr" (piA (bv 1) (bv 3)) <|
    ap2 (cnst iffName) (bv 3) (bv 2)⟩
    2 2

/-- `Iff.rec`'s minor premise, in the `a`/`b`/`motive` binder context:
`∀ (mp : a → b) (mpr : b → a), motive (Iff.intro a b mp mpr)`. -/
def iffRecIntro : Expr :=
  pi "mp" (pi "right" (bv 2) (bv 2)) <|
  pi "mpr" (piA (bv 2) (bv 4)) <|
  .app (bv 2) (ap4 (cnst iffIntroName) (bv 4) (bv 3) (bv 1) (bv 0))

/-- `Iff.rec.{u} (a b : Prop) (motive : Iff a b → Sort u)
(intro : ∀ mp mpr, motive (Iff.intro a b mp mpr)) (t : Iff a b) :
motive t`. -/
def iffRecRaw : ConstantInfo :=
  .recInfo ⟨iffRecName, [uN],
    pi "a" prop <|
    pi "b" prop <|
    pi "motive" (pi "t" (ap2 (cnst iffName) (bv 1) (bv 0)) (srt u)) <|
    pi "intro" iffRecIntro <|
    pi "t" (ap2 (cnst iffName) (bv 3) (bv 2)) (.app (bv 2) (bv 0))⟩
    4 4 []

/-- The raw `Iff` family, as an export carries it (dependency
order). -/
def iffFamily : List ConstantInfo := [iffRaw, iffIntroRaw, iffRecRaw]

/-- The raw `propext` declaration:
`propext (a b : Prop) : Iff a b → Eq.{1} Prop a b`. -/
def propextRaw : ConstantVal :=
  ⟨propextName, [],
    pi "a" prop <|
    pi "b" prop <|
    piA (ap2 (cnst iffName) (bv 1) (bv 0)) <|
    ap3 (cnst eqName [.succ .zero]) prop (bv 2) (bv 1)⟩

/-- `Nonempty.{u} (α : Sort u) : Prop`. -/
def nonemptyRaw : ConstantInfo :=
  .indInfo ⟨nonemptyName, [uN], pi "α" (srt u) prop⟩ {}

/-- `Nonempty.intro.{u} (α : Sort u) (val : α) : Nonempty α`. -/
def nonemptyIntroRaw : ConstantInfo :=
  .ctorInfo ⟨nonemptyIntroName, [uN],
    pi "α" (srt u) <|
    pi "val" (bv 0) <|
    .app (cnst nonemptyName [u]) (bv 1)⟩
    1 1

/-- `Nonempty.rec.{u} (α : Sort u) (motive : Nonempty α → Prop)
(intro : ∀ val, motive (Nonempty.intro α val)) (t : Nonempty α) :
motive t`.  The motive sort is pinned to `Prop` (see the guidance
above). -/
def nonemptyRecRaw : ConstantInfo :=
  .recInfo ⟨nonemptyRecName, [uN],
    pi "α" (srt u) <|
    pi "motive" (pi "t" (.app (cnst nonemptyName [u]) (bv 0)) prop) <|
    pi "intro"
      (pi "val" (bv 1) <|
        .app (bv 1) (ap2 (cnst nonemptyIntroName [u]) (bv 2) (bv 0))) <|
    pi "t" (.app (cnst nonemptyName [u]) (bv 2)) (.app (bv 2) (bv 0))⟩
    3 3 []

/-- The raw `Nonempty` family. -/
def nonemptyFamily : List ConstantInfo :=
  [nonemptyRaw, nonemptyIntroRaw, nonemptyRecRaw]

/-- The raw `Classical.choice` declaration:
`Classical.choice.{u} (α : Sort u) : Nonempty α → α`. -/
def choiceRaw : ConstantVal :=
  ⟨choiceName, [uN],
    pi "α" (srt u) <|
    piA (.app (cnst nonemptyName [u]) (bv 0)) (bv 1)⟩

/-! ## The annotated pins

Computed from the raw pins above by the checker's own annotation pass
while this module elaborates (`#annotate_basis`,
`ConLeche/Kernel/BasisGen.lean`), in the same dependency order the
prerequisite families would be installed in — over the pinned `Eq`
basis, which `propext`'s conclusion mentions. -/

#annotate_basis over [eqA]
  | iffA := iffRaw
  | iffIntroA := iffIntroRaw
  | iffRecA := iffRecRaw
  | nonemptyA := nonemptyRaw
  | nonemptyIntroA := nonemptyIntroRaw
  | nonemptyRecA := nonemptyRecRaw

#annotate_pins over
    [nonemptyRecA, nonemptyIntroA, nonemptyA, iffRecA, iffIntroA, iffA, eqA]
  | propextA := propextRaw
  | choiceA := choiceRaw


/-- Is this checked axiom one of the two recognized standard axioms,
over standardly-shaped stored `Iff` / `Nonempty` families (and the
pinned `Eq` basis)?  A pure predicate so the checker's `axiomDecl`
arm stays a single conditional.

**Why all three of the family's constants are pinned, not just the
type.**  The verification has to *realize* the axiom, and the two
spellings differ: the checker's `propext` takes `Iff a b`, while the
declarative layer's takes the two implications separately
(`ConLeche/Term/Const.lean`).  Bridging them needs the implications
extracted from the `Iff` — and **nothing in the layer turns an
inhabitant of an opaque family into its fields except that family's own
recursor**, since a modeled inductive is opaque to the interpretation
by design.  So `Iff.rec` (resp. `Nonempty.rec`) has to be pinned
alongside the type, and `Iff.intro` (resp. `Nonempty.intro`) with it,
because the recursor's minor premise is stated at the constructor.
Only the recursors' *types* are used — never their reduction rules
(the retired declarative lane's `StdAxiomKey.lean` and its record,
both deleted — see DESIGN.md's task #209 section — for why that
distinction carries a scheduling consequence).  The
pins predate that argument; it is recorded here because it is the
reason they are right. -/
def stdAxiomOk (env : Env) (cvA : ConstantVal) : Bool :=
  if cvA.name = propextName then
    decide (env.find? eqName = some eqA) &&
    (match env.find? iffName with
     | some (.indInfo cvI _) => ConstantVal.matchesPin cvI iffA.toConstantVal
     | _ => false) &&
    (match env.find? iffIntroName with
     | some (.ctorInfo cvIi 2 2) =>
       ConstantVal.matchesPin cvIi iffIntroA.toConstantVal
     | _ => false) &&
    (match env.find? iffRecName with
     | some (.recInfo cvIr 4 4 _) =>
       ConstantVal.matchesPin cvIr iffRecA.toConstantVal
     | _ => false) &&
    ConstantVal.matchesPin cvA propextA
  else if cvA.name = choiceName then
    (match env.find? nonemptyName with
     | some (.indInfo cvN _) =>
       ConstantVal.matchesPin cvN nonemptyA.toConstantVal
     | _ => false) &&
    (match env.find? nonemptyIntroName with
     | some (.ctorInfo cvNi 1 1) =>
       ConstantVal.matchesPin cvNi nonemptyIntroA.toConstantVal
     | _ => false) &&
    (match env.find? nonemptyRecName with
     | some (.recInfo cvNr 3 3 _) =>
       ConstantVal.matchesPin cvNr nonemptyRecA.toConstantVal
     | _ => false) &&
    ConstantVal.matchesPin cvA choiceA
  else false

end ConLeche
