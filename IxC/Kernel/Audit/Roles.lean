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
set, and bumps `specVersion` and the digest together. -/

namespace Ix.Kernel.Audit

open Ix.Kernel

/-- One role's line: kind, levels or equations, evidence kinds (`d` for
`defeq`, `p` for proof), block and dependencies. -/
def roleLine (r : Role) : String :=
  let shape := match (r.spec (md := .anon)) with
    | .block decls => s!"block {decls.length}"
    | .anchor levels _ => s!"anchor {levels}"
    | .ops _ eqs => s!"ops {eqs.length}"
    | .axiom levels type => s!"axiom {levels}{if type.isNone then " inert" else ""}"
    | .identity _ => "identity"
  let ev := String.ofList ((r.spec (md := .anon)).evidenceKinds.map fun b => if b then 'd' else 'p')
  let names (rs : List Role) := ",".intercalate (rs.map fun s => s!"{s.idx}")
  s!"{r.idx} {r.leanName}: {shape}{if ev.isEmpty then "" else " " ++ ev} block [{names r.block}] \
    deps [{names r.deps}]"

end Ix.Kernel.Audit

/-- info: 1 -/
#guard_msgs in #eval Ix.Kernel.specVersion

/--
info: 0 Nat: block 4 block [0,1,2,3] deps []
1 Nat.zero: block 4 block [0,1,2,3] deps []
2 Nat.succ: block 4 block [0,1,2,3] deps []
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
29 List: anchor 1 block [29,30,31] deps []
30 List.nil: anchor 1 block [29,30,31] deps []
31 List.cons: anchor 1 block [29,30,31] deps []
32 Quot: block 5 block [32,33,34,35,36] deps [8]
33 Quot.mk: block 5 block [32,33,34,35,36] deps [8]
34 Quot.lift: block 5 block [32,33,34,35,36] deps [8]
35 Quot.ind: block 5 block [32,33,34,35,36] deps [8]
36 Quot.sound: block 5 block [32,33,34,35,36] deps [8]
37 String: anchor 0 block [37] deps []
38 String.ofList: anchor 0 block [38] deps [29,39,37]
39 Char: anchor 0 block [39] deps []
40 Char.ofNat: anchor 0 block [40] deps [0,39]
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
56 propext: axiom 0 block [56] deps [23,8]
57 Classical.choice: axiom 1 block [57] deps [26]
58 sorryAx: axiom 1 inert block [58] deps []
59 Lean.trustCompiler: axiom 0 block [59] deps [18]
60 Lean.reduceBool: identity block [60] deps [4]
61 Lean.reduceNat: identity block [61] deps [0]
62 Lean.ofReduceBool: axiom 0 block [62] deps [60,4,8]
63 Lean.ofReduceNat: axiom 0 block [63] deps [61,0,8]
-/
#guard_msgs in #eval IO.println ("\n".intercalate (Ix.Kernel.Role.all.map Ix.Kernel.Audit.roleLine))
