import IxC.Kernel.Roles
import IxC.Kernel.Ixon.RoleTable

/-! # The specification set, frozen

The checker's specification set (`Ix.Kernel.Role.spec`, `Role.block`,
`Role.deps`, `specVersion`; `IxC/Kernel/Roles.lean`) changes only on purpose:
this audit prints every role's specification kind, level count, equation
count and evidence kinds, its block and its dependencies, and the version.
The terms themselves are frozen by their digest, which the root library
computes and freezes (`Ix.SpecDigest`, `Ix/SpecDigest.lean`): the kernel
admits no hasher. A change to either output is a change to the specification
set, and bumps `specVersion` and the digest together.

Re-frozen at version 2 (2026-10-20, `ALPHA-COLLAPSE.md` §8.2, owner's
approval): the five compiler-trust roles (`Lean.trustCompiler`,
`Lean.reduceBool`, `Lean.reduceNat`, `Lean.ofReduceBool`, `Lean.ofReduceNat`,
formerly 59–63) and the `identity` kind are gone.

Version 3 makes `Iff`, `Nonempty` and their constructors and recursors
(23–28) blocks and gives the inert `sorryAx` (58) its type over `Bool` (4).
Native definitions and their anchors occupy roles 59–102; their equations
use `eqns`. Each line also records `Role.usedImplicitly`. -/

namespace Ix.Kernel.Audit

open Ix.Kernel

/-- One role's line: kind, levels or equations, evidence kinds (`d` for
`defeq`, `p` for proof, `e` for either), block and dependencies, and `implicit`
for a role the checker uses implicitly. -/
def roleLine (r : Role) : String :=
  let shape := match (r.spec (md := .anon)) with
    | .block decls => s!"block {decls.length}"
    | .anchor levels _ => s!"anchor {levels}"
    | .ops _ eqs => s!"ops {eqs.length}"
    | .axiom levels _ => s!"axiom {levels}{if r == Role.sorryAx then " inert" else ""}"
    | .eqns levels _ eqs => s!"eqns {levels} {eqs.length}"
  let ev := String.ofList ((r.spec (md := .anon)).evidenceAllowed.map fun
    | some true => 'd'
    | some false => 'p'
    | none => 'e')
  let names (rs : List Role) := ",".intercalate (rs.map fun s => s!"{s.idx}")
  s!"{r.idx} {r.leanName}: {shape}{if ev.isEmpty then "" else " " ++ ev} block [{names r.block}] \
    deps [{names r.deps}]{if r.usedImplicitly then " implicit" else ""}"

end Ix.Kernel.Audit

/-- info: 3 -/
#guard_msgs in #eval Ix.Kernel.specVersion

/--
info: 0 Nat: block 4 block [0,1,2,3] deps [] implicit
1 Nat.zero: block 4 block [0,1,2,3] deps [] implicit
2 Nat.succ: block 4 block [0,1,2,3] deps [] implicit
3 Nat.rec: block 4 block [0,1,2,3] deps []
4 Bool: anchor 0 block [4,5,6,7] deps []
5 Bool.false: anchor 0 block [4,5,6,7] deps []
6 Bool.true: anchor 0 block [4,5,6,7] deps []
7 Bool.rec: anchor 1 block [4,5,6,7] deps []
8 Eq: block 3 block [8,9,10] deps []
9 Eq.refl: block 3 block [8,9,10] deps []
10 Eq.rec: block 3 block [8,9,10] deps []
11 PUnit: block 3 block [11,12,13] deps []
12 PUnit.unit: block 3 block [11,12,13] deps []
13 PUnit.rec: block 3 block [11,12,13] deps []
14 Empty: block 2 block [14,15] deps []
15 Empty.rec: block 2 block [14,15] deps []
16 False: block 2 block [16,17] deps []
17 False.rec: block 2 block [16,17] deps []
18 True: anchor 0 block [18,19] deps []
19 True.intro: anchor 0 block [18,19] deps []
20 And: anchor 0 block [20,21,22] deps []
21 And.intro: anchor 0 block [20,21,22] deps []
22 And.rec: anchor 1 block [20,21,22] deps []
23 Iff: anchor 0 block [23,24,25] deps []
24 Iff.intro: anchor 0 block [23,24,25] deps []
25 Iff.rec: anchor 1 block [23,24,25] deps []
26 Nonempty: anchor 1 block [26,27,28] deps []
27 Nonempty.intro: anchor 1 block [26,27,28] deps []
28 Nonempty.rec: anchor 1 block [26,27,28] deps []
29 List: anchor 1 block [29,30,31] deps [] implicit
30 List.nil: anchor 1 block [29,30,31] deps [] implicit
31 List.cons: anchor 1 block [29,30,31] deps [] implicit
32 Quot: block 5 block [32,33,34,35,36] deps [8]
33 Quot.mk: block 5 block [32,33,34,35,36] deps [8]
34 Quot.lift: block 5 block [32,33,34,35,36] deps [8]
35 Quot.ind: block 5 block [32,33,34,35,36] deps [8]
36 Quot.sound: block 5 block [32,33,34,35,36] deps [8]
37 String: anchor 0 block [37] deps [] implicit
38 String.ofList: anchor 0 block [38] deps [29,39,37] implicit
39 Char: anchor 0 block [39] deps [] implicit
40 Char.ofNat: anchor 0 block [40] deps [0,39] implicit
41 Nat.pred: ops 2 dd block [41] deps [0]
42 Nat.add: ops 2 dd block [42] deps [0]
43 Nat.sub: ops 2 dd block [43] deps [0,41]
44 Nat.mul: ops 2 dd block [44] deps [0,42]
45 Nat.pow: ops 2 dd block [45] deps [0,42,44]
46 Nat.beq: ops 4 dddd block [46] deps [0,4]
47 Nat.ble: ops 3 ddd block [47] deps [0,4]
48 Nat.div: ops 3 ppp block [48] deps [0,41,43,47,4,8]
49 Nat.mod: ops 3 ppp block [49] deps [0,41,43,47,4,8]
50 Nat.gcd: ops 2 pp block [50] deps [0,47,49,4,8]
51 Nat.land: ops 2 pp block [51] deps [0,42,44,47,48,49,4,8]
52 Nat.lor: ops 2 pp block [52] deps [0,42,43,44,47,48,49,4,8]
53 Nat.xor: ops 2 pp block [53] deps [0,42,44,47,48,49,4,8]
54 Nat.shiftLeft: ops 2 pp block [54] deps [0,43,44,47,4,8]
55 Nat.shiftRight: ops 2 pp block [55] deps [0,43,47,48,4,8]
56 propext: axiom 0 block [56] deps [23,8] implicit
57 Classical.choice: axiom 1 block [57] deps [26] implicit
58 sorryAx: axiom 1 inert block [58] deps []
59 Decidable: anchor 0 block [59,60,61] deps []
60 Decidable.isTrue: anchor 0 block [59,60,61] deps []
61 Decidable.isFalse: anchor 0 block [59,60,61] deps [62]
62 Not: anchor 0 block [62] deps []
63 of_decide_eq_true: anchor 0 block [63] deps [59,65,4,8]
64 of_decide_eq_false: anchor 0 block [64] deps [59,65,62,4,8]
65 Decidable.decide: eqns 0 3 eep block [65] deps [59,62,4,8]
66 Nat.le: anchor 0 block [66] deps [0]
67 Nat.decEq: eqns 0 1 e block [67] deps [0,4,8,59,65,46]
68 Nat.decLe: eqns 0 1 e block [68] deps [0,4,8,59,65,66,47]
69 Nat.decLt: eqns 0 1 e block [69] deps [0,8,59,66,68]
70 Int: anchor 0 block [70,71,72] deps []
71 Int.ofNat: anchor 0 block [70,71,72] deps [0]
72 Int.negSucc: anchor 0 block [70,71,72] deps [0]
73 Int.negOfNat: eqns 0 2 ee block [73] deps [0,70,8]
74 Int.subNatNat: eqns 0 2 pp block [74] deps [0,70,4,8,41,43,47]
75 Int.neg: eqns 0 2 ee block [75] deps [0,70,8,73]
76 Int.add: eqns 0 4 eeee block [76] deps [0,70,8,42,74]
77 Int.sub: eqns 0 1 e block [77] deps [70,8,76,75]
78 Int.mul: eqns 0 4 eeee block [78] deps [0,70,8,44,73]
79 Int.natAbs: eqns 0 2 ee block [79] deps [0,70,8]
80 Int.ediv: eqns 0 5 eeeee block [80] deps [0,70,8,48,75]
81 Int.emod: eqns 0 4 eeee block [81] deps [0,70,8,49,74]
82 Int.pow: eqns 0 3 epp block [82] deps [0,70,4,8,45,49,46,75]
83 BitVec: anchor 0 block [83,84] deps [0]
84 BitVec.ofNat: anchor 0 block [83,84] deps [0]
85 BitVec.toNat: eqns 0 1 e block [85] deps [0,8,83,49,45]
86 BitVec.ult: eqns 0 1 e block [86] deps [0,4,8,83,49,45,47]
87 String.decEq: eqns 0 1 e block [87] deps [37,4,8,59,65]
88 ByteArray: anchor 0 block [88,89] deps []
89 ByteArray.empty: anchor 0 block [88,89] deps []
90 String.toByteArray: eqns 0 1 e block [90] deps [37,29,39,38,8,88]
91 List.append: eqns 1 2 ee block [91] deps [29,8]
92 String.append: eqns 0 1 e block [92] deps [37,29,39,38,8,91]
93 ite: eqns 1 2 ee block [93] deps [59,62,8]
94 Int.le: anchor 0 block [94] deps [70]
95 Int.decEq: eqns 0 4 eeee block [95] deps [0,70,4,8,59,65,46]
96 Int.decLe: eqns 0 4 eeee block [96] deps [0,70,4,8,59,65,94,47]
97 Int.decLt: eqns 0 1 e block [97] deps [0,70,8,59,94,76,96]
98 Int.bmod: eqns 0 1 e block [98] deps [0,70,8,93,94,76,77,80,81,97]
99 Int.bdiv: eqns 0 1 e block [99] deps [0,70,8,93,94,76,80,81,97,67]
100 Char.utf8Size: eqns 0 5 ppppp block [100] deps [0,39,40,4,8,44,47]
101 String.utf8ByteSize: eqns 0 2 ee block [101] deps [0,37,29,39,38,8,42,100]
102 String.back: eqns 0 3 eee block [102] deps [0,37,29,39,40,38,8,44]
-/
#guard_msgs in #eval IO.println ("\n".intercalate (Ix.Kernel.Role.all.map Ix.Kernel.Audit.roleLine))
