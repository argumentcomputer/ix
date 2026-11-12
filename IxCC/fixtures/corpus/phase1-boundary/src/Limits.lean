/-!
The constructor-count limits of Phase 1 cells (phase 1 plan, MT.3; 04 §3) as
Lean sources reach them; the field-count limit is in `Fields254.lean` and
`Fields255.lean`. A header holds a constructor tag of at most `0x7EFF`;
`Rt.lower` declines anything larger (`rt.layout`). From a Lean source, IxCC's
expression-depth budget (256, a `share` node a leaf), on the records a root
reaches, comes first:

* an inductive of 125 constructors (124 field-less, the last with a field)
  is read; one of 126 is declined at ingress (`decode`: its `casesOn`, which
  the root's `match` reaches, is 2n + 5 = 257 deep), so tags above 124 are
  not reached (nor the header's full `u16` tag, nor `0x7EFF`);
* before that, the four-arm `match` with a wildcard of `tags…` keeps its
  alternatives as closures (`fir: fir.closures`) on an inductive of 17 or
  more constructors; 16 compile.

Each fixture is the closure of one root, so a decline of one does not hide
the others. The values go through `keep…`, a recursion on a runtime count,
so the cells survive the middle end.
-/

namespace Limits

inductive T16 where
  | c0
  | c1
  | c2
  | c3
  | c4
  | c5
  | c6
  | c7
  | c8
  | c9
  | c10
  | c11
  | c12
  | c13
  | c14
  | c15 (m : Nat)

def mkT16 (n : Nat) : T16 :=
  if n == 0 then .c0 else if n == 1 then .c14 else .c15 n

def keepT16 : Nat → T16 → T16
  | 0, t => t
  | k + 1, t => keepT16 k t

/-- 0 for `c0`, 14 for `c14`, `m + 15` for `c15 m`. -/
def tags16 (n k : Nat) : Nat :=
  match keepT16 k (mkT16 n) with
  | .c0 => 0
  | .c14 => 14
  | .c15 m => m + 15
  | _ => 1

inductive T17 where
  | c0
  | c1
  | c2
  | c3
  | c4
  | c5
  | c6
  | c7
  | c8
  | c9
  | c10
  | c11
  | c12
  | c13
  | c14
  | c15
  | c16 (m : Nat)

def mkT17 (n : Nat) : T17 :=
  if n == 0 then .c0 else if n == 1 then .c15 else .c16 n

def keepT17 : Nat → T17 → T17
  | 0, t => t
  | k + 1, t => keepT17 k t

/-- 0 for `c0`, 15 for `c15`, `m + 16` for `c16 m`. -/
def tags17 (n k : Nat) : Nat :=
  match keepT17 k (mkT17 n) with
  | .c0 => 0
  | .c15 => 15
  | .c16 m => m + 16
  | _ => 1

inductive T125 where
  | c0
  | c1
  | c2
  | c3
  | c4
  | c5
  | c6
  | c7
  | c8
  | c9
  | c10
  | c11
  | c12
  | c13
  | c14
  | c15
  | c16
  | c17
  | c18
  | c19
  | c20
  | c21
  | c22
  | c23
  | c24
  | c25
  | c26
  | c27
  | c28
  | c29
  | c30
  | c31
  | c32
  | c33
  | c34
  | c35
  | c36
  | c37
  | c38
  | c39
  | c40
  | c41
  | c42
  | c43
  | c44
  | c45
  | c46
  | c47
  | c48
  | c49
  | c50
  | c51
  | c52
  | c53
  | c54
  | c55
  | c56
  | c57
  | c58
  | c59
  | c60
  | c61
  | c62
  | c63
  | c64
  | c65
  | c66
  | c67
  | c68
  | c69
  | c70
  | c71
  | c72
  | c73
  | c74
  | c75
  | c76
  | c77
  | c78
  | c79
  | c80
  | c81
  | c82
  | c83
  | c84
  | c85
  | c86
  | c87
  | c88
  | c89
  | c90
  | c91
  | c92
  | c93
  | c94
  | c95
  | c96
  | c97
  | c98
  | c99
  | c100
  | c101
  | c102
  | c103
  | c104
  | c105
  | c106
  | c107
  | c108
  | c109
  | c110
  | c111
  | c112
  | c113
  | c114
  | c115
  | c116
  | c117
  | c118
  | c119
  | c120
  | c121
  | c122
  | c123
  | c124 (m : Nat)

def mkT125 (n : Nat) : T125 :=
  if n == 0 then .c0 else if n == 1 then .c123 else .c124 n

def keepT125 : Nat → T125 → T125
  | 0, t => t
  | k + 1, t => keepT125 k t

/-- 0 for `c0`, 123 for `c123`, `m + 124` for `c124 m`. -/
def tags125 (n k : Nat) : Nat :=
  match keepT125 k (mkT125 n) with
  | .c0 => 0
  | .c123 => 123
  | .c124 m => m + 124
  | _ => 1

inductive T126 where
  | c0
  | c1
  | c2
  | c3
  | c4
  | c5
  | c6
  | c7
  | c8
  | c9
  | c10
  | c11
  | c12
  | c13
  | c14
  | c15
  | c16
  | c17
  | c18
  | c19
  | c20
  | c21
  | c22
  | c23
  | c24
  | c25
  | c26
  | c27
  | c28
  | c29
  | c30
  | c31
  | c32
  | c33
  | c34
  | c35
  | c36
  | c37
  | c38
  | c39
  | c40
  | c41
  | c42
  | c43
  | c44
  | c45
  | c46
  | c47
  | c48
  | c49
  | c50
  | c51
  | c52
  | c53
  | c54
  | c55
  | c56
  | c57
  | c58
  | c59
  | c60
  | c61
  | c62
  | c63
  | c64
  | c65
  | c66
  | c67
  | c68
  | c69
  | c70
  | c71
  | c72
  | c73
  | c74
  | c75
  | c76
  | c77
  | c78
  | c79
  | c80
  | c81
  | c82
  | c83
  | c84
  | c85
  | c86
  | c87
  | c88
  | c89
  | c90
  | c91
  | c92
  | c93
  | c94
  | c95
  | c96
  | c97
  | c98
  | c99
  | c100
  | c101
  | c102
  | c103
  | c104
  | c105
  | c106
  | c107
  | c108
  | c109
  | c110
  | c111
  | c112
  | c113
  | c114
  | c115
  | c116
  | c117
  | c118
  | c119
  | c120
  | c121
  | c122
  | c123
  | c124
  | c125 (m : Nat)

def mkT126 (n : Nat) : T126 :=
  if n == 0 then .c0 else if n == 1 then .c124 else .c125 n

def keepT126 : Nat → T126 → T126
  | 0, t => t
  | k + 1, t => keepT126 k t

/-- 0 for `c0`, 124 for `c124`, `m + 125` for `c125 m`. -/
def tags126 (n k : Nat) : Nat :=
  match keepT126 k (mkT126 n) with
  | .c0 => 0
  | .c124 => 124
  | .c125 m => m + 125
  | _ => 1

end Limits

/-- The oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "Limits.tags16", [x, y] => toString (Limits.tags16 x y)
        | "Limits.tags17", [x, y] => toString (Limits.tags17 x y)
        | "Limits.tags125", [x, y] => toString (Limits.tags125 x y)
        | "Limits.tags126", [x, y] => toString (Limits.tags126 x y)
        | _, _ => s!"unknown root {root} {args}"
