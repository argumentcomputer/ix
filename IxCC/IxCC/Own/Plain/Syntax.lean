import IxCC.Fir.Syntax

/-! Conservative plain-RC producer. Erasure retains Fir's computation, while
action prefixes make ownership transfers explicit. Plain.Check binds untrusted
bodies to this producer; semantic refinement is in Plain.Proof.Candidate. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Fir (Var JoinId FunId Arg Rhs)

inductive Action where
  | inc (x : Var) (n : Nat)
  | dec (x : Var)
  deriving DecidableEq, Repr

mutual
inductive Code where
  | act (a : Action) (k : Code)
  | bind (x : Var) (r : Rhs) (k : Code)
  | jp (j : JoinId) (params captured : List Var) (rec : Bool) (body k : Code)
  | jmp (j : JoinId) (args : List Arg)
  | case (x : Var) (alts : List Alt) (dflt : Option Code)
  | ret (a : Arg)
  | tcall (f : FunId) (args : List Arg)
  | trap
inductive Alt where
  | mk (key : Key.CtorKey) (body : Code)
end

deriving instance Repr for Code, Alt

def actionPrefix : List Action → Code → Code
  | [], k => k
  | a :: as, k => .act a (actionPrefix as k)

/-- Duplicate each variable occurrence separately. -/
def copies : List Arg → List Action
  | [] => []
  | .var x :: as => .inc x 1 :: copies as
  | _ :: as => copies as

/-- Retain captured variables by identity, never by aliased heap value. -/
def drops (captured : List Var) : List Var → List Action
  | [] => []
  | x :: xs => if captured.contains x then drops captured xs else .dec x :: drops captured xs

def isImmArg (imm : List Var) : Arg → Bool
  | .var x => imm.contains x
  | _ => true

def isImmRhs (imm : List Var) : Rhs → Bool
  | .prim .. => true
  | .ctor c _ => c.arity == 0
  | .arg a => isImmArg imm a
  | .proj y _ _ => imm.contains y
  | .call .. => false

def argVars : List Arg → List Var
  | [] => []
  | .var x :: as => x :: argVars as
  | _ :: as => argVars as

def nextImm (imm : List Var) (x : Var) (r : Rhs) : List Var :=
  match r with
  | .prim _ args => imm ++ argVars args ++ [x]
  | _ => if isImmRhs imm r then imm ++ [x] else imm

def heapArgs (imm : List Var) : List Arg → List Arg
  | [] => []
  | a :: as => if isImmArg imm a then heapArgs imm as else a :: heapArgs imm as

/-- Duplicate variable occurrences only when already retained (`seen`), moving
the first occurrence of each non-captured variable argument. -/
def moveCopies (seen : List Var) : List Arg → List Action
  | [] => []
  | .var x :: as =>
    if seen.contains x then .inc x 1 :: moveCopies seen as
    else moveCopies (x :: seen) as
  | _ :: as => moveCopies seen as

def transferActions (imm captured live : List Var) (args : List Arg) : List Action :=
  moveCopies (captured ++ imm) (heapArgs imm args) ++
    drops ((captured ++ imm) ++ argVars (heapArgs imm args)) live

def transfer (live imm captured : List Var) (args : List Arg) (k : Code) : Code :=
  actionPrefix (transferActions imm captured live args) k

abbrev Joins := List (JoinId × List Var)

mutual
def lowerCode (live : List Var) (joins : Joins) (c : Fir.Code) (imm : List Var := []) : Code :=
  match c with
  | .bind x r k =>
    let next := lowerCode (live ++ [x]) joins k (nextImm imm x r)
    match r with
    | .arg a => actionPrefix (copies (heapArgs imm [a])) (.bind x r next)
    | .ctor _ args | .call _ args => actionPrefix (copies (heapArgs imm args)) (.bind x r next)
    | .proj y _ _ =>
      if imm.contains y then .bind x r next
      else .bind x r (.act (.inc x 1) next)
    | .prim .. => .bind x r next
  | .jp j ps rec body k =>
    .jp j ps live rec
      (lowerCode (live ++ ps) (if rec then (j, live) :: joins else joins) body)
      (lowerCode live ((j, live) :: joins) k imm)
  | .jmp j args => transfer live imm ((joins.lookup j).getD []) args (.jmp j args)
  | .case x alts dflt => .case x (lowerAlts live joins alts imm) (lowerOpt live joins dflt imm)
  | .ret a => transfer live imm [] [a] (.ret a)
  | .tcall f args => transfer live imm [] args (.tcall f args)
  | .trap => transfer live imm [] [] .trap

def lowerAlts (live : List Var) (joins : Joins) (alts : List Fir.Alt) (imm : List Var := []) : List Alt :=
  match alts with
  | [] => []
  | .mk key body :: rest => .mk key (lowerCode live joins body imm) :: lowerAlts live joins rest imm

def lowerOpt (live : List Var) (joins : Joins) (dflt : Option Fir.Code) (imm : List Var := []) : Option Code :=
  match dflt with
  | none => none
  | some c => some (lowerCode live joins c imm)
end

/-! Missing join labels use an empty capture list only to keep this structural
helper total. They remain invalid Fir and must be rejected by the eventual
checked entry point, which binds this helper to Fir.lower's scopedness proof.
Do not expose lowerCode alone as a certified source-admission interface. -/

mutual
def eraseCode : Code → Fir.Code
  | .act _ k => eraseCode k
  | .bind x r k => .bind x r (eraseCode k)
  | .jp j ps _ rec body k => .jp j ps rec (eraseCode body) (eraseCode k)
  | .jmp j args => .jmp j args
  | .case x alts dflt => .case x (eraseAlts alts) (eraseOpt dflt)
  | .ret a => .ret a
  | .tcall f args => .tcall f args
  | .trap => .trap

def eraseAlts : List Alt → List Fir.Alt
  | [] => []
  | .mk key body :: alts => .mk key (eraseCode body) :: eraseAlts alts

def eraseOpt : Option Code → Option Fir.Code
  | none => none
  | some c => some (eraseCode c)
end

theorem erase_prefix (as : List Action) (k : Code) : eraseCode (actionPrefix as k) = eraseCode k := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa [actionPrefix, eraseCode] using ih

theorem erase_transfer (live imm captured : List Var) (args : List Arg) (k : Code) :
    eraseCode (transfer live imm captured args k) = eraseCode k := erase_prefix ..

mutual
theorem erase_lowerCode (live : List Var) (joins : Joins) :
    ∀ c (imm : List Var), eraseCode (lowerCode live joins c imm) = c
  | .bind x r k, imm => by
    cases r with
    | proj y _ _ =>
      dsimp only [lowerCode]
      cases imm.contains y <;> simp [eraseCode, erase_lowerCode]
    | _ => simp [lowerCode, erase_prefix, eraseCode, erase_lowerCode]
  | .jp j ps rec body k, imm => by
    simp [lowerCode, eraseCode, erase_lowerCode]
  | .jmp j args, imm => by simp [lowerCode, erase_transfer, eraseCode]
  | .case x alts dflt, imm => by simp [lowerCode, eraseCode, erase_lowerAlts, erase_lowerOpt]
  | .ret a, imm => by simp [lowerCode, erase_transfer, eraseCode]
  | .tcall f args, imm => by simp [lowerCode, erase_transfer, eraseCode]
  | .trap, imm => by simp [lowerCode, erase_transfer, eraseCode]

theorem erase_lowerAlts (live : List Var) (joins : Joins) :
    ∀ alts (imm : List Var), eraseAlts (lowerAlts live joins alts imm) = alts
  | [], _ => rfl
  | .mk key body :: alts, imm => by simp [lowerAlts, eraseAlts, erase_lowerCode, erase_lowerAlts]

theorem erase_lowerOpt (live : List Var) (joins : Joins) :
    ∀ dflt (imm : List Var), eraseOpt (lowerOpt live joins dflt imm) = dflt
  | none, _ => rfl
  | some c, imm => by simp [lowerOpt, eraseOpt, erase_lowerCode]
end


end IxCC.Own.Plain
