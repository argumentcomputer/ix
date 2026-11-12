/-!
The widest cell a header counts, from source (the `phase1-boundary` family;
its README has the measurements): a structure of 254 `Nat` fields, allocated,
kept through a recursion on a runtime count and read back. The closure ix
selects holds the structure's whole logical unit, whose `noConfusionType`,
`noConfusion`, `rec`, `casesOn` and `sizeOf` lemmas are past IxCC's
expression-depth budget (256, a `share` node a leaf); the root reaches none of
them, only the block (255 deep) and `mk254` (256), so ingress does not read
them. The constructor arguments are the variable in the first four positions
and literals after them, which keeps `mk254` within the budget.

`genInjectivity` is off: Lean then does not generate `mk.inj` and `mk.injEq`,
which `ix compile` took about 12 minutes to compile at this width (each of the
corpus tool's two compiles of the fixture; 2.5 seconds without them). The
fixture needs neither, and the records above remain over the budget and
unreached. In a file of its own, as is `Fields255.lean`.
-/

set_option genInjectivity false

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
        | _, _ => s!"unknown root {root} {args}"
