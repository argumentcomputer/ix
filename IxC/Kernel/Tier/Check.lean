module

public import IxC.Kernel.Tier.Basic
public import IxC.Kernel.Cached.Installed

@[expose] public section

/-!
# The typing tier: the fold

`checkTierC fe ds` checks the tier declarations `ds` in order against the
index `fe` of the logical environment (the logical fold's accept), at
`.verified`. It is built from the logical fold's own cached functions and
changes none of them:

* **A partial block** `defs .part ms`, as Lean's `add_mutual` adds it
  (`environment.cpp:225-269`):
  1. **its shape** (`blockShape`): non-empty, distinct keys, the same level
     parameters for every member, and no member under a role key or a
     generated key;
  2. **its headers at `fe`**, where no member is visible: `annotConstantValC`
     on each (the duplicate, reserved-name and scope guards, the key fresh at
     `fe`, the annotation, resolution at `fe`), each from a fresh memo state;
  3. **the install**: every header pushed as `axiomInfo`, never unfolded;
  4. **its values at the extension**: `annotValC` (the value annotated with
     the block visible, resolution at the extension), then `checkPending`'s
     inference and conversion against the header (the type's sort, the
     value's type against the declared one), each from a fresh memo state.
* **Staging is Lean's lattice by visibility.** A partial block sees the
  logical environment and the partial constants before it and in it: never
  an unsafe constant, which is not installed (partial mode's "no unsafe"
  rule, `type_checker.cpp:110-113`, by construction). The unsafe stage is
  not built: an unsafe block declines.

Every failure is tagged with the declaration's position in `ds`. A tier
failure is a decline whatever its constructor: IxC cannot tell an ill-typed
declaration from one that types only by unfolding a tier definition, which
the tier refuses (`Ix.Kernel.Tier`). The theorem is `checkTierC_typed`
(`IxC/Kernel/Verify/Tier.lean`).
-/

namespace Ix.Kernel.Tier

open Ix.Kernel Ix.Kernel.Cached

/-- **A definition block's shape** (Lean's `add_mutual`,
`environment.cpp:229-249`, and the tier's own key rule): non-empty, distinct
keys, the same level parameters for every member, every key an input key
(never a role key nor a generated one). -/
def blockShape (ms : List (ConstantVal md × Expr md)) : Except (CheckError md) Unit := do
  let some (cv₀, _) := ms.head? | throw (.notImplemented "tier: an empty definition block")
  unless decide (ms.map (·.1.name)).Nodup do
    throw (.notImplemented msg!"tier: a definition block declares a key twice ({cv₀.name})")
  for (cv, _) in ms do
    unless cv.levelParams == cv₀.levelParams do
      throw (.notImplemented
        msg!"tier: the members of a definition block disagree on their universe parameters ({cv.name})")
    match cv.name with
    | .id _ => pure ()
    | k => throw (.notImplemented msg!"tier: a role key or a generated key ({k})")

/-- **A block's headers**, each checked at `fe`, where no member is visible,
from a fresh memo state (`annotConstantValC`). -/
def headersC (fe : FEnv md) : List (ConstantVal md × Expr md) → Except (CheckError md) (List (ConstantVal md))
  | [] => .ok []
  | (cv, _) :: ms =>
    match annotConstantValC .verified fe cv {} with
    | .error e => .error e
    | .ok ((cvA, _), _) =>
      match headersC fe ms with
      | .error e => .error e
      | .ok hs => .ok (cvA :: hs)

/-- `fe` with the headers pushed as `axiomInfo`, in order (the last one
newest). -/
def pushHeaders (fe : FEnv md) : List (ConstantVal md) → FEnv md
  | [] => fe
  | cvA :: hs => pushHeaders (fe.push (.axiomInfo cvA)) hs

/-- **A member's value** at `fe` (its block installed): annotated
(`annotValC`), then typed against its header (`checkPending`: the header's
sort, the value's type, the conversion), each from a fresh memo state. -/
def valueC (fe : FEnv md) (cvA : ConstantVal md) (v : Expr md) : Except (CheckError md) Unit :=
  match annotValC .verified fe cvA v {} with
  | .error e => .error e
  | .ok (jv, _) =>
    match checkPending .verified fe ⟨⟨.defn, cvA, jv⟩, 0, fe.visibleBelow⟩ {} with
    | .error e => .error e
    | .ok _ => .ok ()

/-- Every member's value against its header, in order. -/
def valuesC (fe : FEnv md) : List (ConstantVal md) → List (ConstantVal md × Expr md) →
    Except (CheckError md) Unit
  | cvA :: hs, (_, v) :: ms =>
    match valueC fe cvA v with
    | .error e => .error e
    | .ok () => valuesC fe hs ms
  | _, _ => .ok ()

/-- A block's constants, newest first, from its headers in order. -/
def blockConsts (s : Safety) (hs : List (ConstantVal md)) : List (TierConst md) :=
  (hs.map fun cv => ⟨cv, s⟩).reverse

/-- **One tier declaration** at `fe`: the extended index, and the
declaration's constants, newest first. -/
def checkDeclC (fe : FEnv md) : TierDecl md → Except (CheckError md) (FEnv md × List (TierConst md))
  | .defs .unsaf _ => .error (.notImplemented "tier: the unsafe stage is not implemented")
  | .defs .part ms =>
    match blockShape ms with
    | .error e => .error e
    | .ok () =>
      match headersC fe ms with
      | .error e => .error e
      | .ok hs =>
        let fe' := pushHeaders fe hs
        match valuesC fe' hs ms with
        | .error e => .error e
        | .ok () => .ok (fe', blockConsts .part hs)

/-- The fold from an accumulator: the index, the constants so far (newest
first), the position. -/
def checkTierFrom (fe : FEnv md) (acc : List (TierConst md)) (i : Nat) :
    List (TierDecl md) → Except (CheckError md × Nat) (FEnv md × List (TierConst md))
  | [] => .ok (fe, acc)
  | d :: ds =>
    match checkDeclC fe d with
    | .ok (fe', ts) => checkTierFrom fe' (ts ++ acc) (i + 1) ds
    | .error e => .error (e, i)

/-- **The tier fold**: every declaration in order, each at the index the
ones before it extended; a failure is tagged with its position. The result
is the extended index and the tier constants, newest first. -/
def checkTierC (fe : FEnv md) (ds : List (TierDecl md)) :
    Except (CheckError md × Nat) (FEnv md × List (TierConst md)) :=
  checkTierFrom fe [] 0 ds

end Ix.Kernel.Tier
