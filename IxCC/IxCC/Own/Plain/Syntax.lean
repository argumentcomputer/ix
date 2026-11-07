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

def transfer (live captured : List Var) (args : List Arg) (k : Code) : Code :=
  actionPrefix (copies args ++ drops captured live) k

abbrev Joins := List (JoinId × List Var)

mutual
def lowerCode (live : List Var) (joins : Joins) : Fir.Code → Code
  | .bind x r k =>
    let next := lowerCode (live ++ [x]) joins k
    match r with
    | .arg a => actionPrefix (copies [a]) (.bind x r next)
    | .ctor _ args | .call _ args => actionPrefix (copies args) (.bind x r next)
    | .proj .. => .bind x r (.act (.inc x 1) next)
    | .prim .. => .bind x r next
  | .jp j ps rec body k =>
    .jp j ps live rec
      (lowerCode (live ++ ps) (if rec then (j, live) :: joins else joins) body)
      (lowerCode live ((j, live) :: joins) k)
  | .jmp j args => transfer live ((joins.lookup j).getD []) args (.jmp j args)
  | .case x alts dflt => .case x (lowerAlts live joins alts) (lowerOpt live joins dflt)
  | .ret a => transfer live [] [a] (.ret a)
  | .tcall f args => transfer live [] args (.tcall f args)
  | .trap => actionPrefix (drops [] live) .trap

def lowerAlts (live : List Var) (joins : Joins) : List Fir.Alt → List Alt
  | [] => []
  | .mk key body :: alts => .mk key (lowerCode live joins body) :: lowerAlts live joins alts

def lowerOpt (live : List Var) (joins : Joins) : Option Fir.Code → Option Code
  | none => none
  | some c => some (lowerCode live joins c)
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

theorem erase_transfer (live captured : List Var) (args : List Arg) (k : Code) :
    eraseCode (transfer live captured args k) = eraseCode k := erase_prefix ..

mutual
theorem erase_lowerCode (live : List Var) (joins : Joins) :
    ∀ c, eraseCode (lowerCode live joins c) = c
  | .bind x r k => by
    cases r <;> simp [lowerCode, erase_prefix, eraseCode, erase_lowerCode]
  | .jp j ps rec body k => by
    simp [lowerCode, eraseCode, erase_lowerCode]
  | .jmp j args => by simp [lowerCode, erase_transfer, eraseCode]
  | .case x alts dflt => by simp [lowerCode, eraseCode, erase_lowerAlts, erase_lowerOpt]
  | .ret a => by simp [lowerCode, erase_transfer, eraseCode]
  | .tcall f args => by simp [lowerCode, erase_transfer, eraseCode]
  | .trap => by simp [lowerCode, erase_prefix, eraseCode]

theorem erase_lowerAlts (live : List Var) (joins : Joins) :
    ∀ alts, eraseAlts (lowerAlts live joins alts) = alts
  | [] => rfl
  | .mk key body :: alts => by simp [lowerAlts, eraseAlts, erase_lowerCode, erase_lowerAlts]

theorem erase_lowerOpt (live : List Var) (joins : Joins) :
    ∀ dflt, eraseOpt (lowerOpt live joins dflt) = dflt
  | none => rfl
  | some c => by simp [lowerOpt, eraseOpt, erase_lowerCode]
end


end IxCC.Own.Plain
