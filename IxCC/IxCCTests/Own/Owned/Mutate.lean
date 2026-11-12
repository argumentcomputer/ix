import IxCC.Own.Plain.Owned

/-! # The ownership checker's suite: negative controls

Each control edits one site of an accepted ownership body, chosen with the checker's own context
at that site so that the edit is a real error (the variable is not an immediate and holds exactly
the tokens the error needs), and expects a refusal for the stated reason:
* `doubleDec`: a `dec x` repeated where `x` holds one token;
* `missingDec`: a `dec x` inside a `case` alternative deleted (a leak on that branch);
* `useAfterDec`: a `dec x` inserted before a use (read or consuming) of `x` holding one token;
* `borrowedConsumed`: the `inc x` after `x := proj y` deleted;
* `missingIncCtor`: an `inc x` before a constructor taking `x` deleted;
* `movedIntoCall`: an `inc x` before a call taking `x` deleted (`x` moved into the call, then used). -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned

open IxCC IxCC.Own.Plain
open IxCC.Fir (Var JoinId FunId Arg Rhs)

inductive Kind where
  | doubleDec | missingDec | useAfterDec | borrowedConsumed | missingIncCtor | movedIntoCall
  deriving BEq, Repr, Inhabited

def Kind.all : List Kind :=
  [.doubleDec, .missingDec, .useAfterDec, .borrowedConsumed, .missingIncCtor, .movedIntoCall]

def Kind.name : Kind → String
  | .doubleDec => "double-dec" | .missingDec => "missing-dec-on-branch"
  | .useAfterDec => "use-after-last-dec" | .borrowedConsumed => "borrowed-consumed"
  | .missingIncCtor => "missing-inc-before-2nd-use" | .movedIntoCall => "moved-into-call-then-used"

/-- Whether a refusal message is the stated reason for this kind. -/
def Kind.expected (k : Kind) (e : String) : Bool :=
  let has (s : String) := (e.splitOn s).length > 1
  let gone := has "no token left" || has "neither owned" || has "is dead"
  match k with
  | .doubleDec => has "dec: v" && has "no token left"
  | .missingDec => has "still held"
  | .useAfterDec => gone
  | .borrowedConsumed => has "borrow"
  | .missingIncCtor | .movedIntoCall => gone

structure MS where
  next : Nat := 0
  done : Bool := false

def hit (target : Nat) : StateM MS Bool := do
  let s ← get
  if s.done then return false
  set { s with next := s.next + 1, done := s.next == target }
  return s.next == target

/-- The first non-action node, for an `inc` that feeds it. -/
def headNode : Code → Code
  | .act _ k => headNode k
  | c => c

def single (Γ : Ctx) (x : Var) : Bool := !Γ.isImm x && Γ.tokens x == 1 && !Γ.borrowed x

def firstSingle (Γ : Ctx) (xs : List Var) : Option Var := xs.find? (single Γ)

def rhsUses : Rhs → List Var
  | .arg a => argVars [a]
  | .ctor _ args | .call _ args | .prim _ args => argVars args
  | .proj y _ _ => [y]

def terminalMut (kind : Kind) (target : Nat) (Γ : Ctx) (xs : List Var) (c : Code) :
    StateM MS Code := do
  if kind == .useAfterDec then
    if let some y := firstSingle Γ xs then
      if ← hit target then return .act (.dec y) c
  return c

mutual
def mutCode (kind : Kind) (target : Nat) (Δ : JCtx) (Γ : Ctx) (inBranch : Bool) :
    Code → StateM MS Code
  | .act (.inc x n) k => do
    let feeds := match kind, headNode k with
      | .missingIncCtor, .bind _ (.ctor c args) _ => c.arity > 0 && (argVars args).contains x
      | .movedIntoCall, .bind _ (.call _ args) _ => (argVars args).contains x
      | _, _ => false
    if feeds && !Γ.isImm x then
      if ← hit target then return k
    match Γ.inc x n with
    | .ok Γ' => return .act (.inc x n) (← mutCode kind target Δ Γ' inBranch k)
    | .error _ => return .act (.inc x n) k
  | .act (.dec x) k => do
    if kind == .doubleDec && single Γ x then
      if ← hit target then return .act (.dec x) (.act (.dec x) k)
    if kind == .missingDec && inBranch && !Γ.isImm x then
      if ← hit target then return k
    match Γ.dec x with
    | .ok Γ' => return .act (.dec x) (← mutCode kind target Δ Γ' inBranch k)
    | .error _ => return .act (.dec x) k
  | .bind x r k => do
    if kind == .useAfterDec then
      if let some y := firstSingle Γ (rhsUses r) then
        if ← hit target then return .act (.dec y) (.bind x r k)
    if kind == .borrowedConsumed then
      if let .proj y _ _ := r then
        if let .act (.inc x' 1) k2 := k then
          if x' == x && !Γ.isImm y then
            if ← hit target then return .bind x r k2
    match bindCtx Γ x r with
    | .ok Γ' => return .bind x r (← mutCode kind target Δ Γ' inBranch k)
    | .error _ => return .bind x r k
  | .jp j ps captured rec body k => do
    let body' ← mutCode kind target (if rec then Δ.insert j captured else Δ)
      (Γ.enter captured ps) false body
    let k' ← mutCode kind target (Δ.insert j captured) Γ inBranch k
    return .jp j ps captured rec body' k'
  | .case x alts d => do
    if kind == .useAfterDec && single Γ x then
      if ← hit target then return .act (.dec x) (.case x alts d)
    return .case x (← mutAlts kind target Δ Γ alts) (← mutOpt kind target Δ Γ d)
  | .ret a => terminalMut kind target Γ (argVars [a]) (.ret a)
  | .tcall f args => terminalMut kind target Γ (argVars args) (.tcall f args)
  | .jmp j args => terminalMut kind target Γ (argVars args) (.jmp j args)
  | .trap => return .trap
def mutAlts (kind : Kind) (target : Nat) (Δ : JCtx) (Γ : Ctx) : List Alt → StateM MS (List Alt)
  | [] => return []
  | .mk key b :: rest => do
    let b' ← mutCode kind target Δ Γ true b
    return .mk key b' :: (← mutAlts kind target Δ Γ rest)
def mutOpt (kind : Kind) (target : Nat) (Δ : JCtx) (Γ : Ctx) : Option Code → StateM MS (Option Code)
  | none => return none
  | some c => return some (← mutCode kind target Δ Γ true c)
end

/-- The mutant at eligible site `target` of a function body, if there is one. -/
def mutant (kind : Kind) (target : Nat) (params : List Var) (body : Code) : Option Code :=
  let (c, s) := (mutCode kind target .leaf (Ctx.entry params) false body).run {}
  if s.done then some c else none

end IxCCTests.Own.Owned
