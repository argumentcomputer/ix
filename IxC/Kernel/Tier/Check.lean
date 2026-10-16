module

public import IxC.Kernel.Tier.Basic
public import IxC.Kernel.Cached.Installed

@[expose] public section

/-!
# The typing tier: the fold

`checkTierC fe ds` checks the tier declarations `ds`, staged, against the
index `fe` of the logical environment (the logical fold's accept), at
`.verified`. It is built from the logical fold's own cached functions and
changes none of them:

* **A definition block** `defs s ms`, partial or unsafe, as Lean's
  `add_mutual` adds it (`environment.cpp:225-269`; an unsafe singleton is
  added before its body as well, `:163-178`):
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
* **An unsafe opaque** `unsafeOpaque cv v`, as Lean's `add_opaque` checks one,
  in safe mode (`environment.cpp:211-223`): its header and its value at the
  **logical view** `fe₀`, the index before any tier constant, so it can name
  none; its key fresh at the full index too; then pushed.
* **An unsafe axiom** `unsafeAxiom cv`, as `add_axiom` checks one in unsafe
  mode (`environment.cpp:152-158`): its header at the full index, its type a
  sort there (`checkPending`'s first half); then pushed. Never through
  `checkDeclStepC`, which declines a non-standard axiom.
* **Staging is Lean's lattice by visibility** (`staged`): every partial
  block in input order, then every unsafe opaque, then every unsafe block
  and axiom in input order. A partial block sees the logical environment and
  the partial constants before it and in it: never an unsafe constant, which
  is not installed yet (partial mode's "no unsafe" rule,
  `type_checker.cpp:110-113`, by construction); an unsafe opaque sees no tier
  constant; unsafe code sees every tier constant before it, and its own block
  (`type_checker.cpp:110`).

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

/-- **A definition block** `defs s ms` at `fe`: its shape, its headers at
`fe`, the install, its values at the extension. -/
def blockC (fe : FEnv md) (s : Safety) (ms : List (ConstantVal md × Expr md)) :
    Except (CheckError md) (FEnv md × List (TierConst md)) :=
  match blockShape ms with
  | .error e => .error e
  | .ok () =>
    match headersC fe ms with
    | .error e => .error e
    | .ok hs =>
      let fe' := pushHeaders fe hs
      match valuesC fe' hs ms with
      | .error e => .error e
      | .ok () => .ok (fe', blockConsts s hs)

/-- **An unsafe opaque**, in Lean's safe mode: its header and its value at the
logical view `fe₀` (no tier constant visible), its key fresh at `fe`, then
pushed onto `fe`. -/
def opaqueC (fe₀ fe : FEnv md) (cv : ConstantVal md) (v : Expr md) :
    Except (CheckError md) (FEnv md × List (TierConst md)) :=
  match annotConstantValC .verified fe₀ cv {} with
  | .error e => .error e
  | .ok ((cvA, _), _) =>
    if (fe.find? cvA.name).isSome then .error (.invalid msg!"duplicate declaration {cvA.name}")
    else
      match valueC fe₀ cvA v with
      | .error e => .error e
      | .ok () => .ok (fe.push (.axiomInfo cvA), blockConsts .unsaf [cvA])

/-- **A header's type is a sort** at `fe`: `checkPending`'s first half (the
type's inference, then `ensureSort`), from a fresh memo state. -/
def sortC (fe : FEnv md) (cvA : ConstantVal md) : Except (CheckError md) Unit :=
  match (do
      let jsty ← (coreKnotI .verified fe checkFuel).infer 0 cvA.type
      let _ ← opSIxC .verified fe 0 jsty
      pure () : (CheckCM md) Unit) {} with
  | .error e => .error e
  | .ok _ => .ok ()

/-- **An unsafe axiom**, in Lean's unsafe mode: its header at `fe` (every tier
constant before it visible), its type a sort there, then pushed. -/
def axiomC (fe : FEnv md) (cv : ConstantVal md) :
    Except (CheckError md) (FEnv md × List (TierConst md)) :=
  match annotConstantValC .verified fe cv {} with
  | .error e => .error e
  | .ok ((cvA, _), _) =>
    match sortC fe cvA with
    | .error e => .error e
    | .ok () => .ok (fe.push (.axiomInfo cvA), blockConsts .unsaf [cvA])

/-- **One tier declaration** at `fe`, with `fe₀` the logical view (the index
before any tier constant): the extended index, and the declaration's
constants, newest first. -/
def checkDeclC (fe₀ fe : FEnv md) : TierDecl md → Except (CheckError md) (FEnv md × List (TierConst md))
  | .defs s ms => blockC fe s ms
  | .unsafeOpaque cv v => opaqueC fe₀ fe cv v
  | .unsafeAxiom cv => axiomC fe cv

/-- A tier declaration's stage in Lean's lattice: a partial block (0), an
unsafe opaque (1), an unsafe block or axiom (2). -/
def TierDecl.stage : TierDecl md → Nat
  | .defs .part _ => 0
  | .unsafeOpaque .. => 1
  | .defs .unsaf _ | .unsafeAxiom _ => 2

/-- The declarations with their positions, from position `i`. -/
def indexed : Nat → List (TierDecl md) → List (Nat × TierDecl md)
  | _, [] => []
  | i, d :: ds => (i, d) :: indexed (i + 1) ds

/-- **The staged order**: the declarations with their positions, every
partial block in input order, then every unsafe opaque, then every unsafe
block and axiom in input order. -/
def staged (ds : List (TierDecl md)) : List (Nat × TierDecl md) :=
  let xs := indexed 0 ds
  xs.filter (·.2.stage == 0) ++ (xs.filter (·.2.stage == 1) ++ xs.filter (·.2.stage == 2))

/-- The fold from an accumulator, over positioned declarations: the logical
view, the index, the constants so far (newest first). -/
def checkTierFrom (fe₀ fe : FEnv md) (acc : List (TierConst md)) :
    List (Nat × TierDecl md) → Except (CheckError md × Nat) (FEnv md × List (TierConst md))
  | [] => .ok (fe, acc)
  | (i, d) :: ds =>
    match checkDeclC fe₀ fe d with
    | .ok (fe', ts) => checkTierFrom fe₀ fe' (ts ++ acc) ds
    | .error e => .error (e, i)

/-- **The tier fold**: the declarations staged (`staged`), each at the index
the ones before it extended, from the logical index `fe`, which is also the
logical view; a failure is tagged with its position in `ds`. The result is
the extended index and the tier constants, newest first. -/
def checkTierC (fe : FEnv md) (ds : List (TierDecl md)) :
    Except (CheckError md × Nat) (FEnv md × List (TierConst md)) :=
  checkTierFrom fe fe [] (staged ds)

end Ix.Kernel.Tier
