/-
  Ix.Theory.Eval: Fueled specification-level NbE evaluator.

  eval_s and apply_s take a Nat fuel parameter and return Option SVal.
  Total by structural recursion on fuel.
  Mirrors Ix.Kernel2.Infer (eval, applyValThunk) but strict, pure, no ST.
-/
import Ix.Theory.Value

namespace Ix.Theory

variable {L : Type}

mutual
/-- Evaluate an expression in a closure environment.
    Environment is a list with the most recent binding at the head (index 0 = bvar 0).
    This matches the implementation's Array-based env but with :: instead of push. -/
def eval_s (fuel : Nat) (e : SExpr L) (env : List (SVal L)) : Option (SVal L) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar idx => env[idx]?
    | .sort u => some (.sort u)
    | .const id levels => some (.neutral (.const id levels) [])
    | .app fn arg =>
      do let fv ← eval_s fuel fn env
         let av ← eval_s fuel arg env
         apply_s fuel fv av
    | .lam dom body =>
      do let dv ← eval_s fuel dom env
         some (.lam dv body env)
    | .forallE dom body =>
      do let dv ← eval_s fuel dom env
         some (.pi dv body env)
    | .letE _ty val body =>
      do let vv ← eval_s fuel val env
         eval_s fuel body (vv :: env)
    | .lit n => some (.lit n)
    | .proj _t _i _s => none -- proj stuck in specification (no iota reduction)

/-- Apply a value to an argument. Beta for lambdas, accumulate for neutrals. -/
def apply_s (fuel : Nat) (fn arg : SVal L) : Option (SVal L) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match fn with
    | .lam _dom body env => eval_s fuel body (arg :: env)
    | .neutral hd spine => some (.neutral hd (spine ++ [arg]))
    | _ => none -- stuck
end

-- BEq for sanity checks (can't derive for mutual inductives)
mutual
def SVal.beq [BEq L] : SVal L → SVal L → Bool
  | .lam d1 b1 e1, .lam d2 b2 e2 => d1.beq d2 && b1 == b2 && beqSValList e1 e2
  | .pi d1 b1 e1, .pi d2 b2 e2 => d1.beq d2 && b1 == b2 && beqSValList e1 e2
  | .sort u1, .sort u2 => u1 == u2
  | .neutral h1 s1, .neutral h2 s2 => h1.beq h2 && beqSValList s1 s2
  | .lit n1, .lit n2 => n1 == n2
  | _, _ => false

def SHead.beq [BEq L] : SHead L → SHead L → Bool
  | .fvar l1, .fvar l2 => l1 == l2
  | .const i1 ls1, .const i2 ls2 => i1 == i2 && ls1 == ls2
  | _, _ => false

def beqSValList [BEq L] : List (SVal L) → List (SVal L) → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && beqSValList as bs
  | _, _ => false
end

instance [BEq L] : BEq (SVal L) := ⟨SVal.beq⟩
instance [BEq L] : BEq (SHead L) := ⟨SHead.beq⟩

-- Sanity checks (using L := Nat)
#guard eval_s 10 (.lit 42 : SExpr Nat) [] == some (.lit 42)
#guard eval_s 10 (.app (.lam (.sort 0) (.bvar 0)) (.lit 5) : SExpr Nat) [] == some (.lit 5)
#guard eval_s 20
    (.app (.app (.lam (.sort 0) (.lam (.sort 0) (.bvar 1))) (.lit 1)) (.lit 2) : SExpr Nat)
    [] == some (.lit 1)
#guard eval_s 10 (.letE (.sort 0) (.lit 5) (.bvar 0) : SExpr Nat) [] == some (.lit 5)
#guard eval_s 10 (.const 42 [] : SExpr Nat) [] == some (.neutral (.const 42 []) [])
#guard eval_s 10 (.app (.const 42 []) (.lit 1) : SExpr Nat) [] ==
    some (.neutral (.const 42 []) [.lit 1])

end Ix.Theory
