import IxCC.Own.Plain.Program

/-! # Heap stage 2, step 0: maps built to be expensive for the checker (probe)

Synthetic Fir programs of one function, with the canonical producer's map (the shape an adversary
would choose: every live variable captured by every join, so a certificate of size O(V + K)
makes the checker take one captured token per variable per jump):
* `wideCase V B`: V parameters live across one `case` of B branches (each returns the first);
* `joinFan V K`: a join capturing V variables, jumped to from K branches;
* `deepJoins D V`: D nested joins, each capturing V variables and jumping to the enclosing one;
* `chain V M`: M `inc`/`dec` pairs on one variable before the return (a long certificate). -/

set_option autoImplicit false

namespace IxCCTests.Own.Stage2.Hostile

open IxCC IxCC.Own.Plain
open IxCC.Fir (Var Arg)

def mkProg (params : List Var) (body : Fir.Code) (vars : Nat) : Fir.Program :=
  let fd : Fir.Fun := { (default : Fir.Fun) with params := params.map (·, .tobj), body, vars }
  { funs := Src.NatMap.ofList [(0, fd)], size := 1, exports := [0], ctors := [], known := {} }

def alts (n : Nat) (body : Nat → Fir.Code) : List Fir.Alt :=
  (List.range n).map fun i => .mk default (body i)

def wideCase (V B : Nat) : Fir.Program :=
  mkProg (List.range V) (.case 0 (alts B fun _ => .ret (.var 0)) none) V

def joinFan (V K : Nat) : Fir.Program :=
  mkProg (List.range V)
    (.jp 0 [V] false (.ret (.var V)) (.case 0 (alts K fun _ => .jmp 0 [.lit (.nat 0)]) none)) (V + 1)

def deepJoins (D V : Nat) : Fir.Program :=
  let rec nest : Nat → Fir.Code
    | 0 => .jmp (D - 1) []
    | i + 1 => let j := D - 1 - i
      .jp j [] false (if j == 0 then .ret (.var 0) else .jmp (j - 1) []) (nest i)
  mkProg (List.range V) (nest D) V

/-- The canonical map with `M` extra `inc 0`/`dec 0` pairs at the head of the body. -/
def chain (V M : Nat) : Fir.Program × Src.NatMap Code :=
  let F := wideCase V 1
  let pad : List Action := (List.range M).flatMap fun _ => [.inc 0 1, .dec 0]
  (F, (Program.canonical F).bodies.map (actionPrefix pad))

end IxCCTests.Own.Stage2.Hostile
