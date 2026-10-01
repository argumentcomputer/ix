/-!
The layout limits of Phase 1 cells (phase 1 plan, MT.3; 04 §3) as Lean
sources reach them. A header holds a scanned-field count of at most 254 and
a constructor tag of at most `0x7EFF`; `Rt.lower` declines anything larger
(`rt.layout`). From a Lean source, the Ixon v3 decoder's expression depth
budget (256) comes first:

* a structure of 254 `Nat` fields decodes, is allocated and read back;
  one of 255 fields is declined at ingress (`decode`: a constant of its
  closure is deeper than 256), so `rt.layout` is not reached;
* an inductive of 125 constructors (124 field-less, the last with a field)
  decodes; one of 126 is declined at ingress, so tags above 124 are not
  reached (nor the header's full `u16` tag, nor `0x7EFF`);
* before that, the four-arm `match` with a wildcard of `tags…` keeps its
  alternatives as closures (`fir: fir.closures`) on an inductive of 17 or
  more constructors; 16 compile.

Each fixture is the closure of one root, so a decline of one does not hide
the others. The values go through `keep…`, a recursion on a runtime count,
so the cells survive the middle end; the constructor arguments are the
variable in the first four positions and literals after them, which keeps
`mk…` within the depth budget.
-/

namespace Limits

structure Big254 where
  f0 : Nat
  f1 : Nat
  f2 : Nat
  f3 : Nat
  f4 : Nat
  f5 : Nat
  f6 : Nat
  f7 : Nat
  f8 : Nat
  f9 : Nat
  f10 : Nat
  f11 : Nat
  f12 : Nat
  f13 : Nat
  f14 : Nat
  f15 : Nat
  f16 : Nat
  f17 : Nat
  f18 : Nat
  f19 : Nat
  f20 : Nat
  f21 : Nat
  f22 : Nat
  f23 : Nat
  f24 : Nat
  f25 : Nat
  f26 : Nat
  f27 : Nat
  f28 : Nat
  f29 : Nat
  f30 : Nat
  f31 : Nat
  f32 : Nat
  f33 : Nat
  f34 : Nat
  f35 : Nat
  f36 : Nat
  f37 : Nat
  f38 : Nat
  f39 : Nat
  f40 : Nat
  f41 : Nat
  f42 : Nat
  f43 : Nat
  f44 : Nat
  f45 : Nat
  f46 : Nat
  f47 : Nat
  f48 : Nat
  f49 : Nat
  f50 : Nat
  f51 : Nat
  f52 : Nat
  f53 : Nat
  f54 : Nat
  f55 : Nat
  f56 : Nat
  f57 : Nat
  f58 : Nat
  f59 : Nat
  f60 : Nat
  f61 : Nat
  f62 : Nat
  f63 : Nat
  f64 : Nat
  f65 : Nat
  f66 : Nat
  f67 : Nat
  f68 : Nat
  f69 : Nat
  f70 : Nat
  f71 : Nat
  f72 : Nat
  f73 : Nat
  f74 : Nat
  f75 : Nat
  f76 : Nat
  f77 : Nat
  f78 : Nat
  f79 : Nat
  f80 : Nat
  f81 : Nat
  f82 : Nat
  f83 : Nat
  f84 : Nat
  f85 : Nat
  f86 : Nat
  f87 : Nat
  f88 : Nat
  f89 : Nat
  f90 : Nat
  f91 : Nat
  f92 : Nat
  f93 : Nat
  f94 : Nat
  f95 : Nat
  f96 : Nat
  f97 : Nat
  f98 : Nat
  f99 : Nat
  f100 : Nat
  f101 : Nat
  f102 : Nat
  f103 : Nat
  f104 : Nat
  f105 : Nat
  f106 : Nat
  f107 : Nat
  f108 : Nat
  f109 : Nat
  f110 : Nat
  f111 : Nat
  f112 : Nat
  f113 : Nat
  f114 : Nat
  f115 : Nat
  f116 : Nat
  f117 : Nat
  f118 : Nat
  f119 : Nat
  f120 : Nat
  f121 : Nat
  f122 : Nat
  f123 : Nat
  f124 : Nat
  f125 : Nat
  f126 : Nat
  f127 : Nat
  f128 : Nat
  f129 : Nat
  f130 : Nat
  f131 : Nat
  f132 : Nat
  f133 : Nat
  f134 : Nat
  f135 : Nat
  f136 : Nat
  f137 : Nat
  f138 : Nat
  f139 : Nat
  f140 : Nat
  f141 : Nat
  f142 : Nat
  f143 : Nat
  f144 : Nat
  f145 : Nat
  f146 : Nat
  f147 : Nat
  f148 : Nat
  f149 : Nat
  f150 : Nat
  f151 : Nat
  f152 : Nat
  f153 : Nat
  f154 : Nat
  f155 : Nat
  f156 : Nat
  f157 : Nat
  f158 : Nat
  f159 : Nat
  f160 : Nat
  f161 : Nat
  f162 : Nat
  f163 : Nat
  f164 : Nat
  f165 : Nat
  f166 : Nat
  f167 : Nat
  f168 : Nat
  f169 : Nat
  f170 : Nat
  f171 : Nat
  f172 : Nat
  f173 : Nat
  f174 : Nat
  f175 : Nat
  f176 : Nat
  f177 : Nat
  f178 : Nat
  f179 : Nat
  f180 : Nat
  f181 : Nat
  f182 : Nat
  f183 : Nat
  f184 : Nat
  f185 : Nat
  f186 : Nat
  f187 : Nat
  f188 : Nat
  f189 : Nat
  f190 : Nat
  f191 : Nat
  f192 : Nat
  f193 : Nat
  f194 : Nat
  f195 : Nat
  f196 : Nat
  f197 : Nat
  f198 : Nat
  f199 : Nat
  f200 : Nat
  f201 : Nat
  f202 : Nat
  f203 : Nat
  f204 : Nat
  f205 : Nat
  f206 : Nat
  f207 : Nat
  f208 : Nat
  f209 : Nat
  f210 : Nat
  f211 : Nat
  f212 : Nat
  f213 : Nat
  f214 : Nat
  f215 : Nat
  f216 : Nat
  f217 : Nat
  f218 : Nat
  f219 : Nat
  f220 : Nat
  f221 : Nat
  f222 : Nat
  f223 : Nat
  f224 : Nat
  f225 : Nat
  f226 : Nat
  f227 : Nat
  f228 : Nat
  f229 : Nat
  f230 : Nat
  f231 : Nat
  f232 : Nat
  f233 : Nat
  f234 : Nat
  f235 : Nat
  f236 : Nat
  f237 : Nat
  f238 : Nat
  f239 : Nat
  f240 : Nat
  f241 : Nat
  f242 : Nat
  f243 : Nat
  f244 : Nat
  f245 : Nat
  f246 : Nat
  f247 : Nat
  f248 : Nat
  f249 : Nat
  f250 : Nat
  f251 : Nat
  f252 : Nat
  f253 : Nat

def mk254 (n : Nat) : Big254 :=
  ⟨n, n, n, n, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
   112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
   128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143,
   144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
   160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175,
   176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191,
   192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207,
   208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
   224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239,
   240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253⟩

def keep254 : Nat → Big254 → Big254
  | 0, b => b
  | k + 1, b => keep254 k b

/-- `n + 253`: the first field plus the last. -/
def fields254 (n k : Nat) : Nat :=
  let b := keep254 k (mk254 n)
  b.f0 + b.f253

structure Big255 where
  f0 : Nat
  f1 : Nat
  f2 : Nat
  f3 : Nat
  f4 : Nat
  f5 : Nat
  f6 : Nat
  f7 : Nat
  f8 : Nat
  f9 : Nat
  f10 : Nat
  f11 : Nat
  f12 : Nat
  f13 : Nat
  f14 : Nat
  f15 : Nat
  f16 : Nat
  f17 : Nat
  f18 : Nat
  f19 : Nat
  f20 : Nat
  f21 : Nat
  f22 : Nat
  f23 : Nat
  f24 : Nat
  f25 : Nat
  f26 : Nat
  f27 : Nat
  f28 : Nat
  f29 : Nat
  f30 : Nat
  f31 : Nat
  f32 : Nat
  f33 : Nat
  f34 : Nat
  f35 : Nat
  f36 : Nat
  f37 : Nat
  f38 : Nat
  f39 : Nat
  f40 : Nat
  f41 : Nat
  f42 : Nat
  f43 : Nat
  f44 : Nat
  f45 : Nat
  f46 : Nat
  f47 : Nat
  f48 : Nat
  f49 : Nat
  f50 : Nat
  f51 : Nat
  f52 : Nat
  f53 : Nat
  f54 : Nat
  f55 : Nat
  f56 : Nat
  f57 : Nat
  f58 : Nat
  f59 : Nat
  f60 : Nat
  f61 : Nat
  f62 : Nat
  f63 : Nat
  f64 : Nat
  f65 : Nat
  f66 : Nat
  f67 : Nat
  f68 : Nat
  f69 : Nat
  f70 : Nat
  f71 : Nat
  f72 : Nat
  f73 : Nat
  f74 : Nat
  f75 : Nat
  f76 : Nat
  f77 : Nat
  f78 : Nat
  f79 : Nat
  f80 : Nat
  f81 : Nat
  f82 : Nat
  f83 : Nat
  f84 : Nat
  f85 : Nat
  f86 : Nat
  f87 : Nat
  f88 : Nat
  f89 : Nat
  f90 : Nat
  f91 : Nat
  f92 : Nat
  f93 : Nat
  f94 : Nat
  f95 : Nat
  f96 : Nat
  f97 : Nat
  f98 : Nat
  f99 : Nat
  f100 : Nat
  f101 : Nat
  f102 : Nat
  f103 : Nat
  f104 : Nat
  f105 : Nat
  f106 : Nat
  f107 : Nat
  f108 : Nat
  f109 : Nat
  f110 : Nat
  f111 : Nat
  f112 : Nat
  f113 : Nat
  f114 : Nat
  f115 : Nat
  f116 : Nat
  f117 : Nat
  f118 : Nat
  f119 : Nat
  f120 : Nat
  f121 : Nat
  f122 : Nat
  f123 : Nat
  f124 : Nat
  f125 : Nat
  f126 : Nat
  f127 : Nat
  f128 : Nat
  f129 : Nat
  f130 : Nat
  f131 : Nat
  f132 : Nat
  f133 : Nat
  f134 : Nat
  f135 : Nat
  f136 : Nat
  f137 : Nat
  f138 : Nat
  f139 : Nat
  f140 : Nat
  f141 : Nat
  f142 : Nat
  f143 : Nat
  f144 : Nat
  f145 : Nat
  f146 : Nat
  f147 : Nat
  f148 : Nat
  f149 : Nat
  f150 : Nat
  f151 : Nat
  f152 : Nat
  f153 : Nat
  f154 : Nat
  f155 : Nat
  f156 : Nat
  f157 : Nat
  f158 : Nat
  f159 : Nat
  f160 : Nat
  f161 : Nat
  f162 : Nat
  f163 : Nat
  f164 : Nat
  f165 : Nat
  f166 : Nat
  f167 : Nat
  f168 : Nat
  f169 : Nat
  f170 : Nat
  f171 : Nat
  f172 : Nat
  f173 : Nat
  f174 : Nat
  f175 : Nat
  f176 : Nat
  f177 : Nat
  f178 : Nat
  f179 : Nat
  f180 : Nat
  f181 : Nat
  f182 : Nat
  f183 : Nat
  f184 : Nat
  f185 : Nat
  f186 : Nat
  f187 : Nat
  f188 : Nat
  f189 : Nat
  f190 : Nat
  f191 : Nat
  f192 : Nat
  f193 : Nat
  f194 : Nat
  f195 : Nat
  f196 : Nat
  f197 : Nat
  f198 : Nat
  f199 : Nat
  f200 : Nat
  f201 : Nat
  f202 : Nat
  f203 : Nat
  f204 : Nat
  f205 : Nat
  f206 : Nat
  f207 : Nat
  f208 : Nat
  f209 : Nat
  f210 : Nat
  f211 : Nat
  f212 : Nat
  f213 : Nat
  f214 : Nat
  f215 : Nat
  f216 : Nat
  f217 : Nat
  f218 : Nat
  f219 : Nat
  f220 : Nat
  f221 : Nat
  f222 : Nat
  f223 : Nat
  f224 : Nat
  f225 : Nat
  f226 : Nat
  f227 : Nat
  f228 : Nat
  f229 : Nat
  f230 : Nat
  f231 : Nat
  f232 : Nat
  f233 : Nat
  f234 : Nat
  f235 : Nat
  f236 : Nat
  f237 : Nat
  f238 : Nat
  f239 : Nat
  f240 : Nat
  f241 : Nat
  f242 : Nat
  f243 : Nat
  f244 : Nat
  f245 : Nat
  f246 : Nat
  f247 : Nat
  f248 : Nat
  f249 : Nat
  f250 : Nat
  f251 : Nat
  f252 : Nat
  f253 : Nat
  f254 : Nat

def mk255 (n : Nat) : Big255 :=
  ⟨n, n, n, n, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
   112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
   128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143,
   144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
   160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175,
   176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191,
   192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207,
   208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
   224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239,
   240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254⟩

def keep255 : Nat → Big255 → Big255
  | 0, b => b
  | k + 1, b => keep255 k b

/-- `n + 254`: the first field plus the last. -/
def fields255 (n k : Nat) : Nat :=
  let b := keep255 k (mk255 n)
  b.f0 + b.f254
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
        | "Limits.fields254", [x, y] => toString (Limits.fields254 x y)
        | "Limits.fields255", [x, y] => toString (Limits.fields255 x y)
        | "Limits.tags16", [x, y] => toString (Limits.tags16 x y)
        | "Limits.tags17", [x, y] => toString (Limits.tags17 x y)
        | "Limits.tags125", [x, y] => toString (Limits.tags125 x y)
        | "Limits.tags126", [x, y] => toString (Limits.tags126 x y)
        | _, _ => s!"unknown root {root} {args}"
