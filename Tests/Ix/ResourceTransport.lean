module

public import Ix.Resource.Admit
public import Tests.Ix.Resource

/-!
# Contracts cannot be changed by transporting along an unchecked equality

The kernel's conversion compares binder input contracts but not the result
contracts of `∀`s, so it accepts `rfl : ((~ x : Nat) → ~ Nat) = ((~ x : Nat) →
Nat)`. A transport such as `cast` along that equality would turn a local result
into an unrestricted one. The resource checker therefore checks, with contracts,
every proof it relies on: a marked theorem's proof (`checkTheorem`) and every
term in an erased position (`conform`). The exception is a proof of an equation
between values of a literal type, stated with the kernel's `Eq`
(`dataEquation`): it holds with contracts exactly when it holds without, and it
is not inspected.

Each case below is a small program: the shared declarations of `base`, then the
case's own declarations, admitted with the default policy. The laundering cases
assert the refusal and where it happens; the controls assert the error the same
program gets without the transport; the legitimate uses must stay accepted.
-/

public section

namespace Tests.ResourceTransport

open Ixon Ix.Resource
open Tests.Resource (b arr lam v errorCode)

abbrev E := Ixon.Expr

def ref (i : Nat) : E := .ref i.toUInt64 #[]

def natTy : E := ref 0
def eq (α a c : E) : E := .app (.app (.app (ref 1) α) a) c
def refl (α a : E) : E := .app (.app (ref 2) α) a
def cast (α β h x : E) : E := .app (.app (.app (.app (ref 3) α) β) h) x
def trans (α a c d h₁ h₂ : E) : E :=
  .app (.app (.app (.app (.app (.app (ref 4) α) a) c) d) h₁) h₂
def zero : E := .nat 0

/-- `(~ x : Nat)`, `(! x : Nat)`, `(0 h : …)`. -/
def localIn : BinderContract := ⟨.many, .localShared⟩
def uniqueIn : BinderContract := ⟨.many, .unique⟩
def erasedIn : BinderContract := ⟨.erased, .shared⟩

/-- `(~ x : Nat) → ~ Nat` and `(~ x : Nat) → Nat`. -/
def localArrow : E := .all localIn .localShared natTy natTy
def escapingArrow : E := .all localIn .shared natTy natTy
/-- `Nat → Nat` and `Nat → ! Nat`. -/
def sharedArrow : E := arr (b .many) .shared natTy natTy
def uniqueArrow : E := arr (b .many) .unique natTy natTy
/-- `(! acc : Nat) → ! (Nat → ! Nat)` and the same with a shared outer result. -/
def oneShotArrow : E := .all uniqueIn .unique natTy uniqueArrow
def reusableArrow : E := .all uniqueIn .shared natTy uniqueArrow

/-- `0 Nat`, `1 Eq`, `2 Eq.refl`, `3 cast`, `4 Eq.trans`, `5 localId`, `6 share`,
`7 oneShot`, `8 both`. `cast` and `Eq.trans` are contract-free interfaces, as in
Lean's library: no profile entry is needed for them. -/
def base : Array Declaration := #[
  { type := .sort 1, kind := .typeConstructor },
  { type := arr (b .many) .shared (.sort 1) (arr (b .many) .shared (v 0)
      (arr (b .many) .shared (v 1) (.sort 0))), kind := .typeConstructor },
  { type := arr (b .many) .shared (.sort 1) (arr (b .many) .shared (v 0) (eq (v 1) (v 0) (v 0))),
    kind := .constructor },
  { type := arr (b .many) .shared (.sort 1) (arr (b .many) .shared (.sort 1)
      (arr (b .many) .shared (eq (.sort 1) (v 1) (v 0)) (arr (b .many) .shared (v 2) (v 2)))),
    kind := .assumption },
  { type := arr (b .many) .shared (.sort 1) (arr (b .many) .shared (v 0)
      (arr (b .many) .shared (v 1) (arr (b .many) .shared (v 2)
        (arr (b .many) .shared (eq (v 3) (v 2) (v 1))
          (arr (b .many) .shared (eq (v 4) (v 2) (v 1)) (eq (v 5) (v 4) (v 2))))))),
    kind := .assumption },
  { type := localArrow, body := some (.lam localIn natTy (v 0)) },
  { type := sharedArrow, body := some (lam (b .many) (v 0)) },
  { type := oneShotArrow, body := some (.lam uniqueIn natTy (lam (b .many) (v 1))) },
  { type := .all uniqueIn .unique natTy (.all uniqueIn .unique natTy natTy),
    body := some (.lam uniqueIn natTy (.lam uniqueIn natTy (v 1))) }
]

def theoremOf (type proof : E) : Declaration := { type, body := some proof, kind := .theorem }
def definitionOf (type body : E) : Declaration := { type, body := some body }

/-- `fun (~ x) => (cast α β h localId) x` at type `(~ x : Nat) → Nat`. -/
def escapeVia (α β h : E) : Declaration :=
  definitionOf escapingArrow (.lam localIn natTy (.app (cast α β h (ref 5)) (v 0)))

inductive Expect where
  | accepted
  /-- Refused at this declaration (an index into the case's program) with this error. -/
  | refused (declaration : Nat) (code : String)

structure Case where
  name : String
  extra : Array Declaration
  expect : Expect
  fields : Array Field := #[]
  groups : Array (Array Nat) := #[]

/-- The first declaration after `base`. -/
def n : Nat := base.size

/-- Declaration `n`: `add : Nat → Nat → Nat`, an ordinary interface. Two
literals stand for `1` and `2`. -/
def addDecl : Declaration :=
  { type := arr (b .many) .shared natTy (arr (b .many) .shared natTy natTy), kind := .assumption }
def one : E := .nat 1
def two : E := .nat 2
/-- `localId (add 1 1) = 2`. -/
def onePlusOne : E := eq natTy (.app (ref 5) (.app (.app (ref n) one) one)) two
/-- Declaration `n + 1`: `fun (0 h : localId (add 1 1) = 2) => 0`. -/
def needsProof : Declaration :=
  definitionOf (.all erasedIn .shared onePlusOne natTy) (.lam erasedIn onePlusOne zero)

def cases : Array Case := #[
  -- local result → unrestricted (`esc`)
  ⟨"theorem equating a local and an unrestricted result",
    #[theoremOf (eq (.sort 1) localArrow escapingArrow) (refl (.sort 1) localArrow),
      escapeVia localArrow escapingArrow (ref n)],
    .refused n "type", #[], #[]⟩,
  ⟨"control: the escape without the transport",
    #[definitionOf escapingArrow (.lam localIn natTy (.app (ref 5) (v 0)))],
    .refused n "unrestricted", #[], #[]⟩,
  ⟨"control: the same equality as a definition",
    #[definitionOf (eq (.sort 1) localArrow escapingArrow) (refl (.sort 1) localArrow),
      escapeVia localArrow escapingArrow (ref n)],
    .refused n "type", #[], #[]⟩,
  -- shared result → unique (`alias`)
  ⟨"theorem equating a shared and a unique result",
    #[theoremOf (eq (.sort 1) sharedArrow uniqueArrow) (refl (.sort 1) sharedArrow),
      definitionOf uniqueArrow (lam (b .many) (.app (cast sharedArrow uniqueArrow (ref n) (ref 6)) (v 0)))],
    .refused n "type", #[], #[]⟩,
  ⟨"control: a shared value returned as unique",
    #[definitionOf uniqueArrow (lam (b .many) (.app (ref 6) (v 0)))],
    .refused n "ownership", #[], #[]⟩,
  -- one-shot closure over a unique owner → reusable (`twoOwners`)
  ⟨"theorem making a one-shot closure reusable",
    #[theoremOf (eq (.sort 1) oneShotArrow reusableArrow) (refl (.sort 1) oneShotArrow),
      definitionOf (.all uniqueIn .unique natTy natTy) (.lam uniqueIn natTy
        (.letE { nonDep := false } uniqueArrow
          (.app (cast oneShotArrow reusableArrow (ref n) (ref 7)) (v 0))
          (.app (.app (ref 8) (.app (v 0) zero)) (.app (v 0) zero))))],
    .refused n "type", #[], #[]⟩,
  ⟨"control: the one-shot closure invoked twice",
    #[definitionOf (.all uniqueIn .unique natTy natTy) (.lam uniqueIn natTy
        (.letE { nonDep := false } uniqueArrow (.app (ref 7) (v 0))
          (.app (.app (ref 8) (.app (v 0) zero)) (.app (v 0) zero))))],
    .refused n "capture", #[], #[]⟩,
  -- the statement names definitions whose bodies carry the contracts
  ⟨"theorem equating definitions of the two arrow types",
    #[definitionOf (.sort 1) localArrow, definitionOf (.sort 1) escapingArrow,
      theoremOf (eq (.sort 1) (ref n) (ref (n + 1))) (refl (.sort 1) (ref n)),
      escapeVia (ref n) (ref (n + 1)) (ref (n + 2))],
    .refused (n + 2) "type", #[], #[]⟩,
  -- the bad step sits in an erased argument of a sound theorem
  ⟨"erased proof argument with a contract-changing step",
    #[theoremOf (arr (b .many) .shared (.sort 1) (arr (b .many) .shared (.sort 1)
          (.all erasedIn .shared (eq (.sort 1) (v 1) (v 0)) (eq (.sort 1) (v 2) (v 1)))))
        (lam (b .many) (lam (b .many) (.lam erasedIn (eq (.sort 1) (v 1) (v 0)) (v 0)) (.sort 1)) (.sort 1)),
      escapeVia localArrow escapingArrow
        (.app (.app (.app (ref n) localArrow) escapingArrow)
          (trans (.sort 1) localArrow localArrow escapingArrow
            (refl (.sort 1) localArrow) (refl (.sort 1) localArrow)))],
    .refused (n + 1) "type", #[], #[]⟩,
  -- the equality is a field of a proposition-valued structure
  ⟨"theorem building a structure whose field equates the arrow types",
    #[{ type := .sort 0, kind := .typeConstructor },
      { type := arr (b .many) .shared (eq (.sort 1) localArrow escapingArrow) (ref n),
        kind := .constructor },
      theoremOf (ref n) (.app (ref (n + 1)) (refl (.sort 1) localArrow)),
      escapeVia localArrow escapingArrow (.prj n.toUInt64 0 (ref (n + 2)))],
    .refused (n + 2) "type",
    #[{ typeRef := n.toUInt64, index := 0, type := eq (.sort 1) localArrow escapingArrow,
        contract := .shared }],
    #[#[n, n + 1]]⟩,
  ⟨"control: an axiom equating the arrow types needs a profile entry",
    #[{ type := eq (.sort 1) localArrow escapingArrow, kind := .assumption },
      escapeVia localArrow escapingArrow (ref n)],
    .refused n "unsupported", #[], #[]⟩,
  -- legitimate uses
  ⟨"theorem between equal arrow types, used by a transport",
    #[theoremOf (eq (.sort 1) localArrow localArrow) (refl (.sort 1) localArrow),
      definitionOf localArrow (.lam localIn natTy (.app (cast localArrow localArrow (ref n) (ref 5)) (v 0)))],
    .accepted, #[], #[]⟩,
  ⟨"equation theorem of an annotated function",
    #[theoremOf (arr (b .many) .shared natTy (eq natTy (.app (ref 5) (v 0)) (v 0)))
        (lam (b .many) (refl natTy (v 0)))],
    .accepted, #[], #[]⟩,
  -- An equation between `Nat` values is not inspected: its proof may need a
  -- reduction the checker lacks (here literal arithmetic, `localId (1 + 1) = 2`).
  ⟨"equation between Nat values whose proof needs literal reduction",
    #[addDecl, theoremOf onePlusOne (refl natTy two)],
    .accepted, #[], #[]⟩,
  ⟨"erased proof of an equation between Nat values",
    #[addDecl, needsProof, definitionOf natTy (.app (ref (n + 1)) (refl natTy two))],
    .accepted, #[], #[]⟩,
  -- Only the kernel's `Eq` is exempt: an inductive of the same shape could
  -- carry a contract-changing equality in its constructor.
  ⟨"theorem of an Eq-shaped inductive whose constructor equates the arrow types",
    #[{ type := (base[1]!).type, kind := .typeConstructor },
      { type := arr (b .many) .shared (.sort 1) (arr (b .many) .shared (v 0)
          (arr (b .many) .shared (eq (.sort 1) localArrow escapingArrow)
            (.app (.app (.app (ref n) (v 2)) (v 1)) (v 1)))),
        kind := .constructor },
      theoremOf (.app (.app (.app (ref n) natTy) zero) zero)
        (.app (.app (.app (ref (n + 1)) natTy) zero) (refl (.sort 1) localArrow))],
    .refused (n + 2) "type", #[], #[#[n, n + 1]]⟩
]

/-- Controls run without naming the kernel's `Eq`: the proofs above are then
checked, and refused. -/
def withoutEquality : Array Case := #[
  ⟨"control: the equation theorem checked",
    #[addDecl, theoremOf onePlusOne (refl natTy two)],
    .refused (n + 1) "type", #[], #[]⟩,
  ⟨"control: the erased proof checked",
    #[addDecl, needsProof, definitionOf natTy (.app (ref (n + 1)) (refl natTy two))],
    .refused (n + 2) "type", #[], #[]⟩
]

def run : IO UInt32 := do
  let mut failed := 0
  let all := cases.map (·, true) ++ withoutEquality.map (·, false)
  for (c, equality) in all do
    -- Declaration `1` is the kernel's `Eq`, as the address adapter records it.
    let program : Program := {
      declarations := base ++ c.extra, fields := c.fields, groups := c.groups
      natType := some natTy, equality := if equality then some 1 else none }
    let outcome := match admitProgram program with
      | .ok () => "accepted"
      | .error ⟨some i, e⟩ => s!"refused at {i}: {errorCode e}"
      | .error ⟨none, e⟩ => s!"refused: {errorCode e}"
    let expected := match c.expect with
      | .accepted => "accepted"
      | .refused i code => s!"refused at {i}: {code}"
    let ok := outcome == expected
    unless ok do failed := failed + 1
    IO.println s!"  {c.name}: {outcome}{if ok then "" else s!"  (expected {expected})"}"
  if failed == 0 then
    IO.println s!"resource-transport: {all.size} programs admitted or refused as expected"
    return 0
  IO.eprintln s!"resource-transport: {failed} of {all.size} programs differ"
  return 1

end Tests.ResourceTransport

end
