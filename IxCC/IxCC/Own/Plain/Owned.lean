import IxCC.Own.Plain.Check
import IxCC.Own.Plain.PrimSig
import IxCC.Rt.Rc.Classes

/-! # The ownership checker (heap stage 2)

A static judgement over today's `Own.Plain.Code`: any body map it accepts refines the source and
reclaims (`Own.Plain.Proof.Owned`), whatever placement of `inc`/`dec` it carries. Certificate
admission (`Certificate.admit`) and the `Cfg.Rc` admission check call it; the canonical map, the
only one `checkPlainMap` accepts, is among those it accepts (`checkPlainMap_checkOwned`).

A path's context `Ctx` says, for each variable in scope, one of:
* **immediate** (`imm`): its value is a literal, `□` or a field-less constructor; it needs no
  token, and `inc`, `dec` and consuming uses of it are free (they are no-ops at run time);
* **owned** (`own x = n`): the path holds `n` tokens for it; `n = 0` is dead (unusable);
* **borrowed** (`brw x = e`): a projection's result not yet incremented, usable (read, projected,
  incremented) only while no release has happened since it was bound (`epoch = e`).

Rules: `inc x 1` adds a token (a borrowed variable becomes owned with one); `dec x` takes one and
is a release; a consuming use (a constructor field, a call or tail-call argument, `x := y`, a
returned or jumped value) takes one token per occurrence; a read (`case`, `proj`, `prim`) needs
the variable available and takes nothing; a non-tail call is a release (the callee may free);
a primitive is checked under its ownership signature (`primStep` over a `PrimSig`): the consumed
arguments are taken, the read ones must still be held, the arguments it marks `imm` are immediates
afterwards (it succeeded, so they are literals), and the result is an immediate, owned or
borrowed as the signature says. Every primitive of today has the signature `PrimSig.scalar`
(`lamSig`), under which that step is `bindCtx`'s (`primStep_conservative`). At `ret`, `tcall`
and `jmp` the consumed tokens must be all the
path holds (`total = 0`), a jump also consuming one token of each variable the target join
captures; a `trap` may leak (a trap ends the whole run). A join body starts with one token for
each captured variable that is not an immediate and each parameter, the immediates of its
declaration, and nothing borrowed. Branches of a `case` are checked from the same context; Own
has no merge point (a branch ends in a terminal), so no context is ever joined.

Cost: one pass over the candidate, each map operation a `NatMap` walk; a jump costs its target's
captured list, so the worst case is quadratic in the body (`docs/data-and-roots-design.md`, "The
ownership checker"). -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Fir (Var JoinId FunId Arg Rhs)

/-- Structural emptiness test for `Src.NatMap`. -/
def mapIsEmpty {α : Type} : Src.NatMap α → Bool
  | .leaf => true
  | .node none z o => mapIsEmpty z && mapIsEmpty o
  | .node (some _) _ _ => false

/-- Structural intersection of two `Src.NatSet`s. -/
def interSet : Src.NatSet → Src.NatSet → Src.NatSet
  | .leaf, _ => .leaf
  | _, .leaf => .leaf
  | .node va za oa, .node vb zb ob =>
    .node (if va.isSome && vb.isSome then some () else none) (interSet za zb) (interSet oa ob)

/-- A 0-arity constructor `c` agrees with `ctors` (cannot collide with a positive-arity key). -/
def ctor0Valid (ctors : List Lam.CtorInfo) (c : Fir.CtorInfo) : Bool :=
  match Fir.CtorInfo.ofKey ctors c.key with
  | some info => info.arity == 0
  | none => true

/-- One path's ownership context. `total` is the sum of `own` (kept so that terminals cost O(1)).
`pbrw` holds caller-backed function-lifetime borrowed variables (parameters marked `@borrowed`
and variables projected or copied from them); unlike epoch-scoped `brw`, `pbrw` survives releases
and calls for the lifetime of the activation.
`ctorOf` records known constructor keys from enclosing `case` arms; `projOf` records projections
`(parent, key, idx)`; `uniq` tracks statically guaranteed unique owned variables (`tokens = 1`);
`rset` tracks live reset slots `slot ↦ (sizeClass, guaranteedUnique)`. -/
structure Ctx where
  imm : Src.NatSet := .leaf
  own : Src.NatMap Nat := .leaf
  brw : Src.NatMap Nat := .leaf
  pbrw : Src.NatSet := .leaf
  ctorOf : Src.NatMap Key.CtorKey := .leaf
  projOf : Src.NatMap (Var × Key.CtorKey × Nat) := .leaf
  uniq : Src.NatSet := .leaf
  rset : Src.NatMap (Nat × Bool) := .leaf
  epoch : Nat := 0
  total : Nat := 0
  deriving Inhabited

namespace Ctx

def isImm (Γ : Ctx) (x : Var) : Bool := Γ.imm.contains x
def isPbrw (Γ : Ctx) (x : Var) : Bool := Γ.pbrw.contains x
def isUniq (Γ : Ctx) (x : Var) : Bool := Γ.uniq.contains x
def tokens (Γ : Ctx) (x : Var) : Nat := Γ.own.getD x 0
def borrowed (Γ : Ctx) (x : Var) : Bool := Γ.brw.get? x == some Γ.epoch
def avail (Γ : Ctx) (x : Var) : Bool :=
  Γ.isImm x || decide (0 < Γ.tokens x) || Γ.borrowed x || Γ.isPbrw x
def known (Γ : Ctx) (x : Var) : Bool :=
  Γ.imm.contains x || Γ.own.contains x || Γ.brw.contains x || Γ.pbrw.contains x
def borrowable (Γ : Ctx) (x : Var) : Bool :=
  Γ.isImm x || Γ.isPbrw x || decide (0 < Γ.tokens x)

def addOwn (Γ : Ctx) (x : Var) (n : Nat) : Ctx :=
  { Γ with own := Γ.own.insert x (Γ.tokens x + n), total := Γ.total + n }

def addUniqOwn (Γ : Ctx) (x : Var) : Ctx :=
  { Γ.addOwn x 1 with uniq := Γ.uniq.insert x }

/-- `x` is now known to be an immediate: its tokens (if any) are vacuous and dropped. -/
def setImm (Γ : Ctx) (x : Var) : Ctx :=
  { Γ with imm := Γ.imm.insert x, own := Γ.own.erase x, brw := Γ.brw.erase x,
           uniq := Γ.uniq.erase x, total := Γ.total - Γ.tokens x }

/-- `x` is a table-valid immediate (literal, erased, prim/bool, or valid 0-arity ctor),
safe to pass to `@unique` parameters and return from `@unique` functions. -/
def setImmUniq (Γ : Ctx) (x : Var) : Ctx :=
  { Γ.setImm x with uniq := Γ.uniq.insert x }

def setBorrow (Γ : Ctx) (x : Var) : Ctx := { Γ with brw := Γ.brw.insert x Γ.epoch }

def setPbrw (Γ : Ctx) (x : Var) : Ctx := { Γ with pbrw := Γ.pbrw.insert x }

def setCtor (Γ : Ctx) (x : Var) (key : Key.CtorKey) : Ctx :=
  { Γ with ctorOf := Γ.ctorOf.insert x key }

def setProj (Γ : Ctx) (x y : Var) (key : Key.CtorKey) (idx : Nat) : Ctx :=
  { Γ with projOf := Γ.projOf.insert x (y, key, idx) }

def clearUniq (Γ : Ctx) (x : Var) : Ctx :=
  { Γ with uniq := Γ.uniq.erase x }

/-- A release (`dec`, a non-tail call): every epoch-borrowed variable dies (`pbrw` survives). -/
def release (Γ : Ctx) : Ctx := { Γ with epoch := Γ.epoch + 1 }

/-- Consume one token of `x`; an immediate is free. Clears static uniqueness of `x`. -/
def take (Γ : Ctx) (x : Var) : Except String Ctx :=
  if Γ.isImm x then .ok Γ else
  match Γ.own.get? x with
  | some (n + 1) =>
    .ok { Γ with own := Γ.own.insert x n, uniq := Γ.uniq.erase x, total := Γ.total - 1 }
  | _ =>
    if Γ.isPbrw x then .error s!"v{x} is a borrowed parameter and consumed without an increment"
    else if Γ.borrowed x then .error s!"v{x} is borrowed and consumed without an increment"
    else if Γ.brw.contains x then
      .error s!"v{x} was borrowed (never incremented) and is consumed after a release ended the borrow"
    else .error s!"v{x} consumed with no token left"

def takeArg (Γ : Ctx) : Arg → Except String Ctx
  | .var x => Γ.take x
  | _ => .ok Γ

def takeArgs : Ctx → List Arg → Except String Ctx
  | Γ, [] => .ok Γ
  | Γ, a :: as => do takeArgs (← Γ.takeArg a) as

/-- Consume tokens for non-borrowed (`false`) argument positions only. -/
def takeOwnedArgs : Ctx → List Bool → List Arg → Except String Ctx
  | Γ, _, [] => .ok Γ
  | Γ, true :: bs, _ :: as => takeOwnedArgs Γ bs as
  | Γ, false :: bs, a :: as => do takeOwnedArgs (← Γ.takeArg a) bs as
  | Γ, [], a :: as => do takeOwnedArgs (← Γ.takeArg a) [] as

/-- Consume tokens for non-borrowed (`false`) argument positions, verifying `@unique` positions
hold a statically unique value (`isUniq`) at the moment they are consumed. -/
def takeOwnedUniqueArgs : Ctx → List Bool → List Bool → List Arg → Except String Ctx
  | Γ, _, _, [] => .ok Γ
  | Γ, true :: bs, _ :: us, _ :: as => takeOwnedUniqueArgs Γ bs us as
  | Γ, true :: bs, [], _ :: as => takeOwnedUniqueArgs Γ bs [] as
  | Γ, false :: bs, true :: us, a :: as => do
    match a with
    | .var x =>
      unless Γ.isUniq x do
        throw s!"v{x} passed to @unique parameter is not statically unique"
      takeOwnedUniqueArgs (← Γ.take x) bs us as
    | _ => takeOwnedUniqueArgs Γ bs us as
  | Γ, false :: bs, false :: us, a :: as => do
    takeOwnedUniqueArgs (← Γ.takeArg a) bs us as
  | Γ, false :: bs, [], a :: as => do
    takeOwnedUniqueArgs (← Γ.takeArg a) bs [] as
  | Γ, [], true :: us, a :: as => do
    match a with
    | .var x =>
      unless Γ.isUniq x do
        throw s!"v{x} passed to @unique parameter is not statically unique"
      takeOwnedUniqueArgs (← Γ.take x) [] us as
    | _ => takeOwnedUniqueArgs Γ [] us as
  | Γ, [], false :: us, a :: as => do
    takeOwnedUniqueArgs (← Γ.takeArg a) [] us as
  | Γ, [], [], a :: as => do
    takeOwnedUniqueArgs (← Γ.takeArg a) [] [] as

/-- Clear static uniqueness on any non-immediate variable passed in a borrowed (`true`) call position
(a callee may increment and return a copy of a borrowed argument). -/
def clearBorrowedUniq : Ctx → List Bool → List Arg → Ctx
  | Γ, _, [] => Γ
  | Γ, true :: bs, .var x :: as =>
    clearBorrowedUniq (if Γ.isImm x then Γ else Γ.clearUniq x) bs as
  | Γ, _ :: bs, _ :: as => clearBorrowedUniq Γ bs as
  | Γ, [], _ => Γ

/-- Check that every borrowed (`true`) argument of a non-tail call is caller-backed or still owned
in `Γ` (checked *after* `takeOwnedArgs` so an owned+borrowed alias cannot cause use-after-free). -/
def checkCallBorrowed (Γ : Ctx) : List Bool → List Arg → Except String Unit
  | _, [] => .ok ()
  | true :: bs, .var x :: as => do
    unless Γ.borrowable x do
      throw s!"v{x} passed as borrowed call argument without caller ownership or borrow"
    Γ.checkCallBorrowed bs as
  | true :: bs, _ :: as => Γ.checkCallBorrowed bs as
  | false :: bs, _ :: as => Γ.checkCallBorrowed bs as
  | [], _ => .ok ()

/-- Check that every borrowed (`true`) argument of a tail call is caller-backed (`isImm || isPbrw`),
since local owned tokens are gone when the callee runs. -/
def checkTailBorrowed (Γ : Ctx) : List Bool → List Arg → Except String Unit
  | _, [] => .ok ()
  | true :: bs, .var x :: as => do
    unless Γ.isImm x || Γ.isPbrw x do
      throw s!"v{x} passed as borrowed tail-call argument is not caller-backed"
    Γ.checkTailBorrowed bs as
  | true :: bs, _ :: as => Γ.checkTailBorrowed bs as
  | false :: bs, _ :: as => Γ.checkTailBorrowed bs as
  | [], _ => .ok ()

def takeVars : Ctx → List Var → Except String Ctx
  | Γ, [] => .ok Γ
  | Γ, x :: xs => do takeVars (← Γ.take x) xs

def need (Γ : Ctx) (x : Var) (what : String) : Except String Unit :=
  if Γ.avail x then .ok ()
  else if Γ.brw.contains x then .error s!"v{x} {what} after a release ended its borrow"
  else .error s!"v{x} {what} but neither owned, borrowed nor immediate"

def needArgs (Γ : Ctx) : List Arg → Except String Unit
  | [] => .ok ()
  | .var x :: as => do Γ.need x "read by a primitive"; Γ.needArgs as
  | _ :: as => Γ.needArgs as

/-- Every variable captured by join `j` is available at its declaration. -/
def needCaptured (Γ : Ctx) (j : JoinId) : List Var → Except String Unit
  | [] => .ok ()
  | c :: cs => do Γ.need c s!"captured by join j{j}"; Γ.needCaptured j cs

/-- Argument positions marked immediate by `imms` (a primitive's signature) become valid immediates. -/
def immArgs : Ctx → List Bool → List Arg → Ctx
  | Γ, true :: ms, .var x :: as => immArgs (Γ.setImmUniq x) ms as
  | Γ, _ :: ms, _ :: as => immArgs Γ ms as
  | Γ, _, _ => Γ

end Ctx

/-- **A primitive's signature: which arguments are immediates by construction once it has
returned.** Every primitive today (`Lam.Prim`: the `Nat` primitives and stage W1's fixed-width words, whose
words are tagged immediates as a `Nat` is) takes only tagged immediates: Own's
`primResult` is stuck unless `natArgs` reads every argument as `.lit (.nat n)` (and Fir's
evaluation likewise), so after a successful primitive each argument's value is `ImmVal` — the
lemma the proof uses (from `natArgs`, not from a typing fact). A primitive that takes a boxed
word or any heap value (stage W2's raw or boxed words) must mark that position `false`: there it
is only a read, its tokens stay, and it must still be released. -/
def primImmArgs (op : Lam.Prim) (arity : Nat) : List Bool :=
  match op with
  | .natAdd | .natSub | .natMul | .natDiv | .natMod | .natPow | .natGcd | .natBeq | .natBle
  | .natLand | .natLor | .natXor | .natShl | .natShr | .natPred | .natBlt => List.replicate arity true
  | .word .. => List.replicate arity true
  -- Placeholder (lane prims-core): sound only while Own's `primResult` is stuck on `.arr`, so this
  -- mask is never read on a successful run. Array arguments are heap values, not immediates:
  -- lane own-sigs replaces this arm by the primitive's signature (`PrimSig`).
  | .arr .. => List.replicate arity true

namespace Ctx

/-- `inc x n`: only unit increments (the native fragment's); an epoch-borrowed variable becomes
owned, while a caller-backed `pbrw` variable mints an owned token and stays `pbrw`.
Clears static uniqueness of `x`. -/
def inc (Γ : Ctx) (x : Var) (n : Nat) : Except String Ctx :=
  if n != 1 then .error s!"inc v{x} {n}: only unit increments are admitted" else
  if Γ.isImm x then .ok Γ
  else if 0 < Γ.tokens x then .ok ((Γ.clearUniq x).addOwn x 1)
  else if Γ.isPbrw x then .ok ((Γ.clearUniq x).addOwn x 1)
  else if Γ.borrowed x then .ok ({ Γ with brw := Γ.brw.erase x, uniq := Γ.uniq.erase x }.addOwn x 1)
  else if Γ.brw.contains x then .error s!"inc v{x}: a release ended its borrow"
  else .error s!"inc v{x}: v{x} is dead"

def dec (Γ : Ctx) (x : Var) : Except String Ctx :=
  match Γ.take x with
  | .ok Γ' => .ok Γ'.release
  | .error e => .error s!"dec: {e}"

/-- Check and promote the projected fields of a `reset` from `x` (`ctor.key`) into owned tokens. -/
def promoteResetFields (Γ0 : Ctx) (x : Var) (key : Key.CtorKey) :
    Nat → List (Option Var) → Ctx → Except String Ctx
  | _, [], Γ => .ok Γ
  | j, none :: rest, Γ => promoteResetFields Γ0 x key (j + 1) rest Γ
  | j, some v :: rest, Γ => do
    if v == x then throw s!"reset v{x}: field {j} aliases scrutinee"
    unless Γ0.projOf.get? v == some (x, key, j) do
      throw s!"reset v{x}: v{v} is not a projection of field {j} of v{x}"
    unless Γ0.avail v do
      throw s!"reset v{x}: projected field v{v} is not available"
    let Γ' :=
      if Γ.isImm v then Γ
      else ({ Γ with brw := Γ.brw.erase v, uniq := Γ.uniq.erase v }.addOwn v 1)
    promoteResetFields Γ0 x key (j + 1) rest Γ'

/-- Valid heap constructor layout for `reset`/`reuse` (scanned shared dynamic cell). -/
def validReuseCtor (c : Fir.CtorInfo) : Option Nat :=
  if decide (0 < c.arity) && decide (c.arity ≤ 61) && decide (c.nscalar = 0) &&
      decide (c.fieldKinds.length = c.nobj) && c.fieldKinds.all (· == .shared) then
    let lay := Rt.Rc.CellLayout.ofFields c.arity c.tag
    if lay.ok then lay.cls? else none
  else none

/-- Check `.reset s x ctor fields uniq`: consumes one token of `x`, promotes every `some v`
projected field to an owned token, advances the borrow epoch, and opens reset slot `s`. -/
def reset (Γ : Ctx) (ctors : List Lam.CtorInfo) (s : Nat) (x : Var) (ctor : Fir.CtorInfo)
    (fields : List (Option Var)) (uniq : Bool) (known : Lam.Known := {}) : Except String Ctx := do
  unless Fir.CtorInfo.ofKey ctors ctor.key == some ctor do
    throw s!"reset s{s}: constructor does not match program constructor table"
  if known.natZero == some ctor.key || known.natSucc == some ctor.key then
    throw s!"reset s{s}: cannot reset Nat constructor"
  let some cls := validReuseCtor ctor | throw s!"reset s{s}: invalid constructor layout"
  if Γ.rset.contains s then throw s!"reset s{s}: slot already live"
  unless Γ.ctorOf.get? x == some ctor.key do
    throw s!"reset s{s}: v{x} is not known to have constructor tag"
  unless fields.length == ctor.arity do
    throw s!"reset s{s}: field list length {fields.length} != arity {ctor.arity}"
  if Γ.isImm x then throw s!"reset s{s}: cannot reset immediate v{x}"
  if uniq && !Γ.isUniq x then
    throw s!"reset s{s}: static unique reset on non-unique v{x}"
  let Γ₁ ← Γ.take x
  let Γ₂ ← promoteResetFields Γ x ctor.key 0 fields Γ₁
  return { Γ₂.release with rset := Γ₂.rset.insert s (cls, uniq) }

/-- Check `.reuse x s ctor args uniq`: consumes slot `s` (matching size class and static
uniqueness flag) and `args`, binds fresh statically unique `x`. -/
def reuse (Γ : Ctx) (ctors : List Lam.CtorInfo) (x : Var) (s : Nat) (ctor : Fir.CtorInfo)
    (args : List Arg) (uniq : Bool) (known : Lam.Known := {}) : Except String Ctx := do
  if Γ.known x then throw s!"v{x} rebound"
  unless Fir.CtorInfo.ofKey ctors ctor.key == some ctor do
    throw s!"reuse v{x}: constructor does not match program constructor table"
  if known.natZero == some ctor.key || known.natSucc == some ctor.key then
    throw s!"reuse v{x}: cannot reuse for Nat constructor"
  let some cls := validReuseCtor ctor | throw s!"reuse v{x}: invalid constructor layout"
  unless args.length == ctor.arity do
    throw s!"reuse v{x}: argument count {args.length} != arity {ctor.arity}"
  let some (slotCls, slotUniq) := Γ.rset.get? s | throw s!"reuse v{x}: slot s{s} is not live"
  unless slotCls == cls do
    throw s!"reuse v{x}: class mismatch (slot class {slotCls}, ctor class {cls})"
  if uniq && !slotUniq then
    throw s!"reuse v{x}: static unique reuse on non-unique slot s{s}"
  let Γ₁ := { Γ with rset := Γ.rset.erase s }
  let Γ₂ ← Γ₁.takeArgs args
  return Γ₂.addUniqOwn x

/-- Check `.dropSlot s`: consumes and releases unused reset slot `s`. -/
def dropSlot (Γ : Ctx) (s : Nat) : Except String Ctx := do
  unless Γ.rset.contains s do throw s!"dropSlot s{s}: slot is not live"
  return { Γ.release with rset := Γ.rset.erase s }

/-- The variables a join body holds tokens for: its captured variables that are not immediates
of the declaration, then its parameters. -/
def entered (Γ : Ctx) (captured params : List Var) : List Var :=
  captured.filter (fun c => !Γ.isImm c) ++ params

/-- The context a join body starts from (inheriting `imm`, valid immediate `uniq`, and caller-backed `pbrw`). -/
def enter (Γ : Ctx) (captured params : List Var) : Ctx :=
  let owned := Γ.entered captured params
  { imm := Γ.imm, pbrw := Γ.pbrw, uniq := interSet Γ.imm Γ.uniq,
    own := Src.NatMap.ofList (owned.map (·, 1)), total := owned.length }

def entry (params : List Var) : Ctx :=
  { own := Src.NatMap.ofList (params.map (·, 1)), total := params.length }

/-- Owned parameters selected by borrow mask `bs` (`false` = owned, missing = owned). -/
def entryOwned : List Var → List Bool → List Var
  | [], _ => []
  | p :: ps, false :: bs => p :: entryOwned ps bs
  | _ :: ps, true :: bs => entryOwned ps bs
  | ps, [] => ps

/-- Borrowed parameters selected by borrow mask `bs` (`true` = `@borrowed`). -/
def entryBorrowed : List Var → List Bool → List Var
  | [], _ => []
  | p :: ps, true :: bs => p :: entryBorrowed ps bs
  | _ :: ps, false :: bs => entryBorrowed ps bs
  | _, [] => []

/-- Unique parameters selected by `(borrows, uniqs)`: owned and marked `@unique`. -/
def entryUnique : List Var → List Bool → List Bool → List Var
  | [], _, _ => []
  | _ :: ps, true :: bs, _ :: us => entryUnique ps bs us
  | _ :: ps, true :: bs, [] => entryUnique ps bs []
  | p :: ps, false :: bs, true :: us => p :: entryUnique ps bs us
  | _ :: ps, false :: bs, false :: us => entryUnique ps bs us
  | _ :: ps, false :: bs, [] => entryUnique ps bs []
  | p :: ps, [], true :: us => p :: entryUnique ps [] us
  | _ :: ps, [], false :: us => entryUnique ps [] us
  | _, [], [] => []

/-- Function entry context with borrow mask `borrows` and optional uniqueness mask `uniqs`.
Specializes definitionally to `entry` when `borrows = []` and `uniqs = []`. -/
def entryWith (params : List Var) (borrows : List Bool) (uniqs : List Bool := []) : Ctx :=
  let owned := entryOwned params borrows
  let borrowed := entryBorrowed params borrows
  let unique := entryUnique params borrows uniqs
  { own := Src.NatMap.ofList (owned.map (·, 1))
    pbrw := Src.NatMap.ofList (borrowed.map (·, ()))
    uniq := Src.NatMap.ofList (unique.map (·, ()))
    total := owned.length }

/-- At a terminal: every token and reset slot the path holds has been consumed. -/
def closed (Γ : Ctx) (what : String) : Except String Unit :=
  if Γ.total == 0 && mapIsEmpty Γ.rset then .ok ()
  else if Γ.total != 0 then
    .error s!"{what}: {Γ.total} token(s) still held (a missing dec): {(Γ.own.toList.filter (·.2 > 0)).map (·.1)}"
  else
    .error s!"{what}: reset slot(s) still live (missing reuse or dropSlot)"

end Ctx

/-- No variable twice (linear in the list, with a set of those seen). -/
def nodupFrom (seen : Src.NatSet) : List Var → Bool
  | [] => true
  | x :: xs => !seen.contains x && nodupFrom (seen.insert x) xs

def nodupVars (xs : List Var) : Bool := nodupFrom .leaf xs

def bindCtx (Γ : Ctx) (x : Var) (r : Rhs) (borrows : BorrowSigs := .leaf)
    (uniqs : UniqSigs := .leaf) (ctors : List Lam.CtorInfo := []) : Except String Ctx :=
  match r with
  | .arg (.var y) =>
    if Γ.isImm y then .ok (if Γ.isUniq y then Γ.setImmUniq x else Γ.setImm x)
    else if Γ.tokens y == 0 && Γ.isPbrw y then .ok (Γ.setPbrw x)
    else do
      let wasUniq := Γ.isUniq y && Γ.tokens y == 1
      let Γ₁ ← Γ.take y
      return if wasUniq then Γ₁.addUniqOwn x else Γ₁.addOwn x 1
  | .arg _ => .ok (Γ.setImmUniq x)
  | .ctor c args =>
    if c.arity == 0 then .ok (if ctor0Valid ctors c then Γ.setImmUniq x else Γ.setImm x)
    else do return (← Γ.takeArgs args).addUniqOwn x
  | .call f args => do
    let bs := borrows.getD f []
    let (us, retU) := uniqs.getD f ([], false)
    let Γ₁ ← Γ.takeOwnedUniqueArgs bs us args
    Γ₁.checkCallBorrowed bs args
    let Γ₂ := (Γ₁.clearBorrowedUniq bs args).release
    return if retU then Γ₂.addUniqOwn x else Γ₂.addOwn x 1
  | .proj y key idx => do
    Γ.need y "projected"
    let Γ' := if Γ.isImm y then Γ.setImmUniq x else if Γ.isPbrw y then Γ.setPbrw x else Γ.setBorrow x
    return Γ'.setProj x y key idx
  | .prim op args => do
    Γ.needArgs args
    return (Ctx.immArgs Γ (primImmArgs op args.length) args).setImmUniq x

/-! ## A primitive under its ownership signature

`primStep` is the checker's step at `x := op args` for a signature (`PrimSig.lean`). `bindCtx`'s
primitive case above is the rule it replaces (every argument and the result an immediate,
`primImmArgs`): `checkCode` no longer runs it, and it stays as the reference the new step is
proved equal to on today's primitives (`primStep_conservative`), which the canonical producer's
acceptance proof and the `Cfg.Rc` bridge still read through `checkCode_bind`. -/

/-- Take the consumed arguments, left to right. -/
def takeConsumed : Ctx → List ArgUse → List Arg → Except String Ctx
  | Γ, .consume :: us, .var x :: as => do takeConsumed (← Γ.take x) us as
  | Γ, _ :: us, _ :: as => takeConsumed Γ us as
  | Γ, _, _ => .ok Γ

/-- After the consumed arguments are taken, every read argument is still held (owned, a
caller-backed borrow or an immediate): an argument both consumed and read needs two tokens, so a
primitive never mutates in place an array it also reads. Checked after the takes, as a call's
borrowed arguments are (`Ctx.checkCallBorrowed`). -/
def checkRead (Γ : Ctx) : List ArgUse → List Arg → Except String Unit
  | .consume :: us, _ :: as => checkRead Γ us as
  | _ :: us, .var x :: as =>
    if Γ.borrowable x || Γ.borrowed x then checkRead Γ us as
    else .error s!"v{x} read by a primitive that consumed its last token"
  | _ :: us, _ :: as => checkRead Γ us as
  | _, _ => .ok ()

/-- The arguments a signature marks immediate become immediates (`Ctx.immArgs` over the
signature's uses: `markImm_eq_immArgs`). -/
def markImm : Ctx → List ArgUse → List Arg → Ctx
  | Γ, .imm :: us, .var x :: as => markImm (Γ.setImmUniq x) us as
  | Γ, _ :: us, _ :: as => markImm Γ us as
  | Γ, _, _ => Γ

/-- **`x := prim args` under signature `sig`**: every argument available; the consumed ones
taken; the read ones still held; a release if the primitive may free; then the result bound as
the signature says. With `PrimSig.scalar` this is `bindCtx`'s primitive case
(`primStep_conservative`). -/
def primStep (Γ : Ctx) (sig : PrimSig) (x : Var) (args : List Arg) : Except String Ctx := do
  Γ.needArgs args
  let Γ₁ ← takeConsumed Γ sig.args args
  checkRead Γ₁ sig.args args
  let Γ₂ := markImm Γ₁ sig.args args
  let Γ₃ := if sig.release then Γ₂.release else Γ₂
  match sig.result with
  | .imm => pure (Γ₃.setImmUniq x)
  | .fresh true => pure (Γ₃.addUniqOwn x)
  | .fresh false => pure (Γ₃.addOwn x 1)
  | .borrowed _ => pure (Γ₃.setBorrow x)

/-- **The checker's step at `x := r`**: a primitive under its ownership signature (`primStep`
with `lamSig`), every other right-hand side by `bindCtx`. It is `bindCtx` on every right-hand
side of today (`bindStep_eq_bindCtx`). -/
def bindStep (Γ : Ctx) (x : Var) (r : Rhs) (borrows : BorrowSigs := .leaf)
    (uniqs : UniqSigs := .leaf) (ctors : List Lam.CtorInfo := []) : Except String Ctx :=
  match r with
  | .prim op args => primStep Γ (lamSig op args.length) x args
  | r => bindCtx Γ x r borrows uniqs ctors

/-- Join-capture context: join id to the variables whose tokens a jump hands to the body. -/
abbrev JCtx := Src.NatMap (List Var)

mutual
def checkCode (Δ : JCtx) (Γ : Ctx) (c : Code) (borrows : BorrowSigs := .leaf)
    (uniqs : UniqSigs := .leaf) (retUniq : Bool := false)
    (ctors : List Lam.CtorInfo := []) (known : Lam.Known := {}) : Except String Unit :=
  match c with
  | .act (.inc x n) k => do checkCode Δ (← Γ.inc x n) k borrows uniqs retUniq ctors known
  | .act (.dec x) k => do checkCode Δ (← Γ.dec x) k borrows uniqs retUniq ctors known
  | .bind x r k => do
    if Γ.known x then throw s!"v{x} rebound"
    checkCode Δ (← bindStep Γ x r borrows uniqs ctors) k borrows uniqs retUniq ctors known
  | .reset s x ctor fields uniq k => do
    checkCode Δ (← Γ.reset ctors s x ctor fields uniq known) k borrows uniqs retUniq ctors known
  | .reuse x s ctor args uniq k => do
    checkCode Δ (← Γ.reuse ctors x s ctor args uniq known) k borrows uniqs retUniq ctors known
  | .dropSlot s k => do
    checkCode Δ (← Γ.dropSlot s) k borrows uniqs retUniq ctors known
  | .jp j ps captured rec body k => do
    unless nodupVars captured do throw s!"join j{j}: repeated captured variable"
    Γ.needCaptured j captured
    checkCode (if rec then Δ.insert j captured else Δ) (Γ.enter captured ps) body borrows uniqs retUniq ctors known
    checkCode (Δ.insert j captured) Γ k borrows uniqs retUniq ctors known
  | .jmp j args => do
    let some captured := Δ.get? j | throw s!"jump to unknown join j{j}"
    let Γ ← Γ.takeArgs args
    let Γ ← Γ.takeVars captured
    Γ.closed s!"jump to j{j}"
  | .case x alts dflt => do
    Γ.need x "scrutinised"
    checkAlts Δ Γ x alts borrows uniqs retUniq ctors known
    checkOpt Δ Γ dflt borrows uniqs retUniq ctors known
  | .ret a => do
    if retUniq then
      match a with
      | .var y =>
        unless Γ.isUniq y do
          throw s!"return v{y}: not statically unique for @unique return"
      | _ => pure ()
    (← Γ.takeArg a).closed "return"
  | .tcall f args => do
    let bs := borrows.getD f []
    let (us, calleeRetU) := uniqs.getD f ([], false)
    if retUniq && !calleeRetU then
      throw s!"tail call of f{f}: callee does not guarantee @unique return"
    let Γ₁ ← Γ.takeOwnedUniqueArgs bs us args
    Γ₁.checkTailBorrowed bs args
    Γ₁.closed s!"tail call of f{f}"
  | .trap => .ok ()
def checkAlts (Δ : JCtx) (Γ : Ctx) (x : Var) (alts : List Alt) (borrows : BorrowSigs := .leaf)
    (uniqs : UniqSigs := .leaf) (retUniq : Bool := false)
    (ctors : List Lam.CtorInfo := []) (known : Lam.Known := {}) : Except String Unit :=
  match alts with
  | [] => .ok ()
  | .mk key body :: rest => do
    checkCode Δ (Γ.setCtor x key) body borrows uniqs retUniq ctors known
    checkAlts Δ Γ x rest borrows uniqs retUniq ctors known
def checkOpt (Δ : JCtx) (Γ : Ctx) (dflt : Option Code) (borrows : BorrowSigs := .leaf)
    (uniqs : UniqSigs := .leaf) (retUniq : Bool := false)
    (ctors : List Lam.CtorInfo := []) (known : Lam.Known := {}) : Except String Unit :=
  match dflt with
  | none => .ok ()
  | some c => checkCode Δ Γ c borrows uniqs retUniq ctors known
end

-- The candidate erases to the source (`eraseCode c = s`), decided without building `eraseCode`.
mutual
def erases : Code → Fir.Code → Bool
  | .act _ k, s => erases k s
  | .bind x r k, .bind x' r' k' => decide (x = x') && decide (r = r') && erases k k'
  | .reset _ _ _ _ _ k, s => erases k s
  | .reuse x _ c args _ k, .bind x' (.ctor c' args') k' =>
    decide (x = x') && decide (c = c') && decide (args = args') && erases k k'
  | .dropSlot _ k, s => erases k s
  | .jp j ps _ rec b k, .jp j' ps' rec' b' k' =>
    decide (j = j') && decide (ps = ps') && decide (rec = rec') && erases b b' && erases k k'
  | .jmp j args, .jmp j' args' => decide (j = j') && decide (args = args')
  | .case x alts d, .case x' alts' d' => decide (x = x') && erasesAlts alts alts' && erasesOpt d d'
  | .ret a, .ret a' => decide (a = a')
  | .tcall f args, .tcall f' args' => decide (f = f') && decide (args = args')
  | .trap, .trap => true
  | _, _ => false
def erasesAlts : List Alt → List Fir.Alt → Bool
  | [], [] => true
  | .mk key b :: rest, .mk key' b' :: rest' => decide (key = key') && erases b b' && erasesAlts rest rest'
  | _, _ => false
def erasesOpt : Option Code → Option Fir.Code → Bool
  | none, none => true
  | some c, some s => erases c s
  | _, _ => false
end

def sameShape : Src.NatMap Fir.Fun → Src.NatMap Code → Bool
  | .leaf, .leaf => true
  | .node v z o, .node v' z' o' => v.isSome == v'.isSome && sameShape z z' && sameShape o o'
  | _, _ => false

/-- Validate per-function borrow masks: exported entry points own all parameters (external ABI),
and every declared mask matches its function's parameter arity. -/
def borrowsValid (F : Fir.Program) (borrows : BorrowSigs) : Bool :=
  F.exports.all (fun f => (borrows.getD f []).all (!·)) &&
  (List.range F.size).all fun f =>
    match F.fun? f, borrows.get? f with
    | some fd, some bs => bs.length == fd.params.length
    | _, none => true
    | none, some _ => false

/-- Validate per-function uniqueness signatures: exported entry points never assume `@unique`
parameters (external ABI), every declared mask matches arity, and no parameter is both
`@borrowed` and `@unique`. -/
def uniqsValid (F : Fir.Program) (borrows : BorrowSigs) (uniqs : UniqSigs) : Bool :=
  F.exports.all (fun f => ((uniqs.getD f ([], false)).1).all (!·)) &&
  (List.range F.size).all fun f =>
    match F.fun? f, uniqs.get? f with
    | some fd, some (us, _) =>
      let bs := borrows.getD f []
      us.length == fd.params.length &&
        (us.zip bs).all fun (u, b) => !(u && b)
    | _, none => true
    | none, some _ => false

def checkBodyE (fd : Fir.Fun) (body : Code) (borrows : BorrowSigs := .leaf)
    (selfBorrows : List Bool := []) (uniqs : UniqSigs := .leaf)
    (selfUniq : List Bool × Bool := ([], false))
    (ctors : List Lam.CtorInfo := []) (known : Lam.Known := {}) : Except String Unit := do
  unless erases body fd.body do throw "ownership code does not erase to the Fir body"
  checkCode .leaf (Ctx.entryWith (fd.params.map (·.1)) selfBorrows selfUniq.1) body borrows
    uniqs selfUniq.2 ctors known

/-- The listed functions' candidates, with the reason for the first refusal. -/
def checkFuns (F : Fir.Program) (candidate : Src.NatMap Code) (fs : List FunId)
    (borrows : BorrowSigs := .leaf) (uniqs : UniqSigs := .leaf) : Except String Unit :=
  match fs with
  | [] => .ok ()
  | f :: fs =>
    match F.fun? f, candidate.get? f with
    | some fd, some body =>
      match checkBodyE fd body borrows (borrows.getD f []) uniqs (uniqs.getD f ([], false)) F.ctors F.known with
      | .ok () => checkFuns F candidate fs borrows uniqs
      | .error e => .error s!"f{f}: {e}"
    | _, _ => .error s!"f{f}: missing"

/-- Every numbered function's candidate, with the reason for the first refusal. -/
def checkMapE (F : Fir.Program) (candidate : Src.NatMap Code)
    (borrows : BorrowSigs := .leaf) (uniqs : UniqSigs := .leaf) : Except String Unit := do
  unless sameShape F.funs candidate do throw "candidate and source function maps differ in shape"
  checkFuns F candidate (List.range F.size) borrows uniqs

/-- **The ownership checker.** Same source domain as `checkPlainMap` (written contracts
`.many`/shared only); `checkContractOwned` takes `checkContractPlainMap`'s. -/
def checkOwned (F : Fir.Program) (candidate : Src.NatMap Code)
    (borrows : BorrowSigs := .leaf) (uniqs : UniqSigs := .leaf) : Bool :=
  programDomain F && checkBoolPins F && borrowsValid F borrows && uniqsValid F borrows uniqs &&
    (checkMapE F candidate borrows uniqs).isOk

def checkContractOwned (F : Fir.Program) (candidate : Src.NatMap Code)
    (borrows : BorrowSigs := .leaf) (uniqs : UniqSigs := .leaf) : Bool :=
  contractProgramDomain F && checkBoolPins F && borrowsValid F borrows && uniqsValid F borrows uniqs &&
    (checkMapE F candidate borrows uniqs).isOk

end IxCC.Own.Plain
