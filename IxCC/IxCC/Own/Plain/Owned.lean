import IxCC.Own.Plain.Check

/-! # The ownership checker (heap stage 2)

A static judgement over today's `Own.Plain.Code`: any body map it accepts refines the source and
reclaims (`Own.Plain.Proof.Owned`), whatever placement of `inc`/`dec` it carries. Nothing in
production calls it yet; the recheck still admits only the canonical map (`checkPlainMap`), which
this checker also accepts (`checkPlainMap_checkOwned`).

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
after a primitive, the arguments its signature marks (`primImmArgs`) are immediates (it
succeeded, so they are literals). At `ret`, `tcall` and `jmp` the consumed tokens must be all the
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

/-- One path's ownership context. `total` is the sum of `own` (kept so that terminals cost O(1)). -/
structure Ctx where
  imm : Src.NatSet := .leaf
  own : Src.NatMap Nat := .leaf
  brw : Src.NatMap Nat := .leaf
  epoch : Nat := 0
  total : Nat := 0
  deriving Inhabited

namespace Ctx

def isImm (Γ : Ctx) (x : Var) : Bool := Γ.imm.contains x
def tokens (Γ : Ctx) (x : Var) : Nat := Γ.own.getD x 0
def borrowed (Γ : Ctx) (x : Var) : Bool := Γ.brw.get? x == some Γ.epoch
def avail (Γ : Ctx) (x : Var) : Bool := Γ.isImm x || decide (0 < Γ.tokens x) || Γ.borrowed x
def known (Γ : Ctx) (x : Var) : Bool := Γ.imm.contains x || Γ.own.contains x || Γ.brw.contains x

def addOwn (Γ : Ctx) (x : Var) (n : Nat) : Ctx :=
  { Γ with own := Γ.own.insert x (Γ.tokens x + n), total := Γ.total + n }

/-- `x` is now known to be an immediate: its tokens (if any) are vacuous and dropped. -/
def setImm (Γ : Ctx) (x : Var) : Ctx :=
  { Γ with imm := Γ.imm.insert x, own := Γ.own.erase x, brw := Γ.brw.erase x,
           total := Γ.total - Γ.tokens x }

def setBorrow (Γ : Ctx) (x : Var) : Ctx := { Γ with brw := Γ.brw.insert x Γ.epoch }

/-- A release (`dec`, a non-tail call): every borrowed variable dies. -/
def release (Γ : Ctx) : Ctx := { Γ with epoch := Γ.epoch + 1 }

/-- Consume one token of `x`; an immediate is free. -/
def take (Γ : Ctx) (x : Var) : Except String Ctx :=
  if Γ.isImm x then .ok Γ else
  match Γ.own.get? x with
  | some (n + 1) => .ok { Γ with own := Γ.own.insert x n, total := Γ.total - 1 }
  | _ =>
    if Γ.borrowed x then .error s!"v{x} is borrowed and consumed without an increment"
    else if Γ.brw.contains x then
      .error s!"v{x} was borrowed (never incremented) and is consumed after a release ended the borrow"
    else .error s!"v{x} consumed with no token left"

def takeArg (Γ : Ctx) : Arg → Except String Ctx
  | .var x => Γ.take x
  | _ => .ok Γ

def takeArgs : Ctx → List Arg → Except String Ctx
  | Γ, [] => .ok Γ
  | Γ, a :: as => do takeArgs (← Γ.takeArg a) as

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

/-- Argument positions marked immediate by `imms` (a primitive's signature) become immediates. -/
def immArgs : Ctx → List Bool → List Arg → Ctx
  | Γ, true :: ms, .var x :: as => immArgs (Γ.setImm x) ms as
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

namespace Ctx

/-- `inc x n`: only unit increments (the native fragment's); a borrowed variable becomes owned. -/
def inc (Γ : Ctx) (x : Var) (n : Nat) : Except String Ctx :=
  if n != 1 then .error s!"inc v{x} {n}: only unit increments are admitted" else
  if Γ.isImm x then .ok Γ
  else if 0 < Γ.tokens x then .ok (Γ.addOwn x 1)
  else if Γ.borrowed x then .ok ({ Γ with brw := Γ.brw.erase x }.addOwn x 1)
  else if Γ.brw.contains x then .error s!"inc v{x}: a release ended its borrow"
  else .error s!"inc v{x}: v{x} is dead"

def dec (Γ : Ctx) (x : Var) : Except String Ctx :=
  match Γ.take x with
  | .ok Γ' => .ok Γ'.release
  | .error e => .error s!"dec: {e}"

/-- The variables a join body holds tokens for: its captured variables that are not immediates
of the declaration, then its parameters. -/
def entered (Γ : Ctx) (captured params : List Var) : List Var :=
  captured.filter (fun c => !Γ.isImm c) ++ params

/-- The context a join body starts from. -/
def enter (Γ : Ctx) (captured params : List Var) : Ctx :=
  let owned := Γ.entered captured params
  { imm := Γ.imm, own := Src.NatMap.ofList (owned.map (·, 1)), total := owned.length }

def entry (params : List Var) : Ctx :=
  { own := Src.NatMap.ofList (params.map (·, 1)), total := params.length }

/-- At a terminal: every token the path holds has been consumed. -/
def closed (Γ : Ctx) (what : String) : Except String Unit :=
  if Γ.total == 0 then .ok ()
  else .error s!"{what}: {Γ.total} token(s) still held (a missing dec): {(Γ.own.toList.filter (·.2 > 0)).map (·.1)}"

end Ctx

/-- No variable twice (linear in the list, with a set of those seen). -/
def nodupFrom (seen : Src.NatSet) : List Var → Bool
  | [] => true
  | x :: xs => !seen.contains x && nodupFrom (seen.insert x) xs

def nodupVars (xs : List Var) : Bool := nodupFrom .leaf xs

def bindCtx (Γ : Ctx) (x : Var) : Rhs → Except String Ctx
  | .arg (.var y) => do
    let Γ' ← Γ.take y
    return if Γ.isImm y then Γ'.setImm x else Γ'.addOwn x 1
  | .arg _ => .ok (Γ.setImm x)
  | .ctor c args =>
    if c.arity == 0 then .ok (Γ.setImm x) else do return (← Γ.takeArgs args).addOwn x 1
  | .call _ args => do return (← Γ.takeArgs args).release.addOwn x 1
  | .proj y _ _ => do
    Γ.need y "projected"
    return if Γ.isImm y then Γ.setImm x else Γ.setBorrow x
  | .prim op args => do
    Γ.needArgs args
    return (Ctx.immArgs Γ (primImmArgs op args.length) args).setImm x

/-- Join-capture context: join id to the variables whose tokens a jump hands to the body. -/
abbrev JCtx := Src.NatMap (List Var)

mutual
def checkCode (Δ : JCtx) (Γ : Ctx) : Code → Except String Unit
  | .act (.inc x n) k => do checkCode Δ (← Γ.inc x n) k
  | .act (.dec x) k => do checkCode Δ (← Γ.dec x) k
  | .bind x r k => do
    if Γ.known x then throw s!"v{x} rebound"
    checkCode Δ (← bindCtx Γ x r) k
  | .jp j ps captured rec body k => do
    unless nodupVars captured do throw s!"join j{j}: repeated captured variable"
    Γ.needCaptured j captured
    checkCode (if rec then Δ.insert j captured else Δ) (Γ.enter captured ps) body
    checkCode (Δ.insert j captured) Γ k
  | .jmp j args => do
    let some captured := Δ.get? j | throw s!"jump to unknown join j{j}"
    let Γ ← Γ.takeArgs args
    let Γ ← Γ.takeVars captured
    Γ.closed s!"jump to j{j}"
  | .case x alts dflt => do
    Γ.need x "scrutinised"
    checkAlts Δ Γ alts
    checkOpt Δ Γ dflt
  | .ret a => do (← Γ.takeArg a).closed "return"
  | .tcall f args => do (← Γ.takeArgs args).closed s!"tail call of f{f}"
  | .trap => .ok ()
def checkAlts (Δ : JCtx) (Γ : Ctx) : List Alt → Except String Unit
  | [] => .ok ()
  | .mk _ body :: rest => do checkCode Δ Γ body; checkAlts Δ Γ rest
def checkOpt (Δ : JCtx) (Γ : Ctx) : Option Code → Except String Unit
  | none => .ok ()
  | some c => checkCode Δ Γ c
end

-- The candidate erases to the source (`eraseCode c = s`), decided without building `eraseCode`.
mutual
def erases : Code → Fir.Code → Bool
  | .act _ k, s => erases k s
  | .bind x r k, .bind x' r' k' => decide (x = x') && decide (r = r') && erases k k'
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

def checkBodyE (fd : Fir.Fun) (body : Code) : Except String Unit := do
  unless erases body fd.body do throw "ownership code does not erase to the Fir body"
  checkCode .leaf (Ctx.entry (fd.params.map (·.1))) body

/-- The listed functions' candidates, with the reason for the first refusal. -/
def checkFuns (F : Fir.Program) (candidate : Src.NatMap Code) : List FunId → Except String Unit
  | [] => .ok ()
  | f :: fs =>
    match F.fun? f, candidate.get? f with
    | some fd, some body =>
      match checkBodyE fd body with
      | .ok () => checkFuns F candidate fs
      | .error e => .error s!"f{f}: {e}"
    | _, _ => .error s!"f{f}: missing"

/-- Every numbered function's candidate, with the reason for the first refusal. -/
def checkMapE (F : Fir.Program) (candidate : Src.NatMap Code) : Except String Unit := do
  unless sameShape F.funs candidate do throw "candidate and source function maps differ in shape"
  checkFuns F candidate (List.range F.size)

/-- **The ownership checker.** Same source domain as `checkPlainMap` (written contracts
`.many`/shared only); `checkContractOwned` takes `checkContractPlainMap`'s. -/
def checkOwned (F : Fir.Program) (candidate : Src.NatMap Code) : Bool :=
  programDomain F && checkBoolPins F && (checkMapE F candidate).isOk

def checkContractOwned (F : Fir.Program) (candidate : Src.NatMap Code) : Bool :=
  contractProgramDomain F && checkBoolPins F && (checkMapE F candidate).isOk

end IxCC.Own.Plain
