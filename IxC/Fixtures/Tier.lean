import IxC.Kernel.Tier.Check
import IxC.Kernel.Cached.Installed

/-! # The typing tier on hand-built declarations

The tier fold (`Ix.Kernel.Tier.checkTierC`) on Source-mode declarations over
the empty logical environment, with nothing but sorts, so that every verdict
is the tier's own:

* typed: a self-recursive partial definition; a mutual partial block of
  three; `bad : ∀ p : Prop, p := fun p => bad p`, a "proof" of every
  proposition, typed with itself opaque, and never a constant of the logical
  environment: a safe declaration that names it is refused there (the fence);
* declined: a partial definition that types only by unfolding another
  (`useT : T (Sort 1) := Sort 0`, which Lean's kernel accepts by δ and the
  tier, keeping `T` opaque, does not); a value that names a constant the tier
  has not installed (an unsafe one, in Lean's lattice); an empty block, a key
  declared twice, members that disagree on their universe parameters, a role
  key; and an unsafe block (the unsafe stage is not built).

The Ixon and Source entries' cases are host-compiled: `kernel-entry-cases`
(`checkBytesTiered`) and `kernel-source-ingress --fixture`
(`checkSourceTiered`). -/

open Ix.Kernel Ix.Kernel.Tier

namespace Tests.Ix.Kernel.TierFixtures

abbrev E := Expr .source

def key (s : String) : Key .source := .id (.str .anonymous s)
def const (s : String) : E := .const (key s) []
/-- The level `n`. -/
def lvl : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (lvl n)
/-- `Sort n`. -/
def ty (n : Nat) : E := .sort (lvl n)
def bm : BinderMeta := { pw := .never }
def arrow (a b : E) : E := .forallE a b bm
def lam (a b : E) : E := .lam a b bm
def cv (s : String) (t : E) (lps : List LevelParam := []) : ConstantVal .source := ⟨key s, lps, t⟩

/-- The tier constants' names, newest first, if the fold accepts `ds` over the
empty environment. -/
def typedNames (ds : List (TierDecl .source)) : Option (List String) :=
  match checkTierC (mkFEnv Env.empty) ds with
  | .ok (_, ts) => some (ts.map fun c => toString c.cv.name)
  | .error _ => none

/-- Whether the fold declines `ds` at position `i`, with a message `msg`
accepts. -/
def declinedAt (ds : List (TierDecl .source)) (i : Nat) (msg : String → Bool := fun _ => true) : Bool :=
  match checkTierC (mkFEnv Env.empty) ds with
  | .ok _ => false
  | .error (e, j) => i == j && msg (toString e)

/-! ## Typed -/

/-- `loop : Sort 1 → Sort 1 := fun x => loop x`. -/
def loopD : TierDecl .source :=
  .defs .part [(cv "loop" (arrow (ty 1) (ty 1)), lam (ty 1) (.app (const "loop") (.bvar 0)))]

#guard typedNames [loopD] == some ["loop"]

/-- A mutual block of three, each calling the next. -/
def mutD : TierDecl .source :=
  .defs .part [
    (cv "a" (arrow (ty 1) (ty 1)), lam (ty 1) (.app (const "b") (.bvar 0))),
    (cv "b" (arrow (ty 1) (ty 1)), lam (ty 1) (.app (const "c") (.bvar 0))),
    (cv "c" (arrow (ty 1) (ty 1)), lam (ty 1) (.app (const "a") (.bvar 0)))]

#guard typedNames [mutD] == some ["c", "b", "a"]

/-- `bad : ∀ p : Prop, p := fun p => bad p`. -/
def badD : TierDecl .source :=
  .defs .part [(cv "bad" (.forallE (ty 0) (.bvar 0) bm), lam (ty 0) (.app (const "bad") (.bvar 0)))]

#guard typedNames [loopD, badD] == some ["bad", "loop"]

/- The fence: the logical fold refuses a safe declaration that names `bad`,
which the logical environment never holds. -/
#guard match Cached.checkDecls .verified [] #[.defnDecl (cv "useBad" (.forallE (ty 0) (.bvar 0) bm))
    (const "bad") .opaque] with
  | .ok _ => false
  | .error (e, _) => ((toString e).splitOn "unknown constant").length > 1

/-! ## Declined -/

/-- `T : Sort 2 → Sort 2 := fun x => x` and `useT : T (Sort 1) := Sort 0`:
typed only by unfolding `T`, which the tier keeps opaque. -/
def tD : TierDecl .source :=
  .defs .part [(cv "T" (arrow (ty 2) (ty 2)), lam (ty 2) (.bvar 0))]
def useTD : TierDecl .source :=
  .defs .part [(cv "useT" (.app (const "T") (ty 1)), ty 0)]

#guard typedNames [tD] == some ["T"]
#guard declinedAt [tD, useTD] 1 (· == "invalid: type mismatch in definition useT")

/- A value that names a constant the tier has not installed. -/
#guard declinedAt [.defs .part [(cv "p" (ty 1), const "unsafeThing")]] 0

/- The block's shape. -/
#guard declinedAt [.defs .part []] 0
#guard declinedAt [.defs .part [(cv "d" (ty 1), ty 0), (cv "d" (ty 1), ty 0)]] 0
#guard declinedAt [.defs .part [(cv "e" (ty 1), ty 0), (cv "f" (ty 1) [0], ty 0)]] 0
#guard declinedAt [.defs .part [(⟨.role .nat, [], ty 1⟩, ty 0)]] 0

/- The unsafe stage is not built. -/
#guard declinedAt [loopD, .defs .unsaf [(cv "u" (ty 1), ty 0)]] 1
  (·.endsWith "the unsafe stage is not implemented")

end Tests.Ix.Kernel.TierFixtures
