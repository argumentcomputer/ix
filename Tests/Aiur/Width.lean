module

public import LSpec
public import Ix.Aiur
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.IxVM.U64.Goldilocks
public import Ix.IxVM.U64.Small
public import Ix.IxVM.Width.Goldilocks
public import Ix.IxVM.Width.KoalaBear
public import Ix.IxVM.Toplevel

/-!
The field-width profiles (`Ix/IxVM/Width/`). The KoalaBear forms are byte
logic, so they compute identical results under the Goldilocks interpreter
for in-range values — parity against the Goldilocks forms — and their
narrow bounds reject by failed assert, which the interpreter also
exercises faithfully. The heavyweight gate at the end: the full kernel
toplevel over the KoalaBear profile compiles, and every compiled constant
fits KoalaBear's modulus (`checkConstants`), the Phase-A' audit that no
Goldilocks-sized literal remains outside the profiles.
-/

public section

open LSpec Aiur

namespace AiurTests.Width

/-- KoalaBear's modulus: 2³¹ − 2²⁴ + 1. -/
def koalaBearSize : Nat := 2130706433

/-- `canon_ord_cmp_g`/`canon_ord_then`, verbatim from the kernel — merged so
`kernelWidthKoalaBear`'s address chunks resolve without pulling the kernel. -/
def canonHelpers : Source.Toplevel := ⟦
  fn canon_ord_cmp_g(a: G, b: G) -> G {
    match a - b {
      0 => 1,
      _ =>
        match u32_lt(a, b) {
          1 => 0,
          0 => 2,
        },
    }
  }

  fn canon_ord_then(a: G, b: G) -> G {
    match a {
      1 => b,
      _ => a,
    }
  }
⟧

/-- Entrypoints exercising the core profile ops; identical under both
profiles for in-range values. -/
def coreTests : Source.Toplevel := ⟦
  pub fn t_lt(a: G, b: G) -> G { u32_lt(a, b) }

  pub fn t_add() -> G {
    let [s0, s1, s2, s3] = u32_add([255u8, 255u8, 255u8, 255u8], [1u8, 0u8, 0u8, 0u8]);
    assert_eq!(to_field(s0) + to_field(s1) + to_field(s2) + to_field(s3), 0,
      "wrapping add");
    let [t0, t1, t2, t3] = u32_add3([250u8, 0u8, 0u8, 0u8], [10u8, 0u8, 0u8, 0u8], [5u8, 0u8, 0u8, 0u8]);
    assert_eq!(to_field(t0), 9, "add3 low byte");
    assert_eq!(to_field(t1), 1, "add3 carry byte");
    assert_eq!(to_field(t2) + to_field(t3), 0, "add3 high bytes");
    1
  }

  pub fn t_pack_low() -> G {
    let h = [[1u8, 2u8, 3u8, 4u8], [0u8, 0u8, 0u8, 0u8], [0u8, 0u8, 0u8, 0u8], [0u8, 0u8, 0u8, 0u8],
             [0u8, 0u8, 0u8, 0u8], [0u8, 0u8, 0u8, 0u8], [0u8, 0u8, 0u8, 0u8], [0u8, 0u8, 0u8, 0u8]];
    let p = b3_pack(h);
    p[0]
  }
⟧

/-- Kernel-extra entrypoints (KoalaBear forms with `canonHelpers`). -/
def kernelTests : Source.Toplevel := ⟦
  pub fn t_idx_max() -> G { .IDX_MAX }

  pub fn t_split(x: G) -> G {
    let [b0, b1, b2, b3] = u32_split(x);
    to_field(b0) + 1000 * to_field(b1) + 1000000 * to_field(b2)
      + 1000000000 * to_field(b3)
  }

  pub fn t_chunk() -> G {
    -- big-endian: first byte decides
    let gt = canon_addr_chunk(1, 0, 0, 0, 0, 255, 255, 255);
    let eq = canon_addr_chunk(9, 8, 7, 6, 9, 8, 7, 6);
    let lt = canon_addr_chunk(3, 3, 3, 3, 3, 3, 3, 4);
    gt * 100 + eq * 10 + lt
  }
⟧

def build (mods : List Source.Toplevel) : Except String CompiledToplevel := do
  let merged := mods.foldlM
    (fun (acc : Source.Toplevel) (m : Source.Toplevel) => acc.merge m) IxVM.core
  let t ← merged.mapError fun (e : Global) => s!"merge failed at `{e.toName}`"
  t.compile

def run (c : CompiledToplevel) (name : Lean.Name) (input : Array Aiur.G) : Option Aiur.G := do
  let idx ← c.getFuncIdx name
  match c.bytecode.execute idx input default with
  | .error _ => none
  | .ok (output, _, _) => output[0]?

def g := Aiur.G.ofNat

def tests : TestSeq :=
  let gold := build [IxVM.byteStream, IxVM.widthGoldilocks, coreTests]
  let kb := build [IxVM.byteStream, IxVM.widthKoalaBear, coreTests]
  let kbKernel := build
    [IxVM.byteStream, IxVM.widthKoalaBear, IxVM.kernelWidthKoalaBear,
     canonHelpers, kernelTests]
  match gold, kb, kbKernel with
  | .error e, _, _ => test s!"goldilocks core builds: {e}" false
  | _, .error e, _ => test s!"koalabear core builds: {e}" false
  | _, _, .error e => test s!"koalabear kernel extras build: {e}" false
  | .ok gold, .ok kb, .ok kbKernel =>
    -- parity vectors: (a, b) pairs inside the 24-bit space, edges included
    let pairs : List (Nat × Nat) :=
      [(0, 0), (0, 1), (1, 0), (5, 5), (255, 256), (256, 255),
       (65535, 65536), (16777214, 16777215), (16777215, 16777214), (12345, 12345)]
    let parity := pairs.all fun (a, b) =>
      let l := run gold `t_lt #[g a, g b]
      l == run kb `t_lt #[g a, g b] && l == some (g (if a < b then 1 else 0))
    test "u32_lt parity (goldilocks = koalabear = spec) on 24-bit vectors" parity ++
    test "u32_lt rejects an index at 2^24 (koalabear)"
      (run kb `t_lt #[g 16777216, g 0] == none) ++
    test "u32_lt accepts 2^24 on goldilocks" (run gold `t_lt #[g 16777216, g 0] == some (g 0)) ++
    test "wrapping adds agree with spec (goldilocks)" (run gold `t_add #[] == some (g 1)) ++
    test "wrapping adds agree with spec (koalabear)" (run kb `t_add #[] == some (g 1)) ++
    test "b3_pack low element: 4-byte packing (goldilocks)"
      (run gold `t_pack_low #[] == some (g 67305985)) ++
    test "b3_pack low element: 2-byte packing (koalabear)"
      (run kb `t_pack_low #[] == some (g 513)) ++
    test "IDX_MAX is 2^24 - 1" (run kbKernel `t_idx_max #[] == some (g 16777215)) ++
    test "u32_split roundtrips p - 1"
      (run kbKernel `t_split #[g (koalaBearSize - 1)] == some (g (127 * 1000000000))) ++
    test "u32_split roundtrips 2^24" (run kbKernel `t_split #[g 16777216] == some (g 1000000000)) ++
    test "u32_split rejects p (checked canonicality)"
      (run kbKernel `t_split #[g koalaBearSize] == none) ++
    test "u32_split rejects p + 5" (run kbKernel `t_split #[g (koalaBearSize + 5)] == none) ++
    test "canon_addr_chunk orders big-endian bytes"
      (run kbKernel `t_chunk #[] == some (g 210)) ++
    -- The heavyweight gate: the full kernel over the KoalaBear profile
    -- compiles, and every compiled constant fits KoalaBear's modulus.
    (match (do
        let profile ← IxVM.koalaBearProfile.mapError
          fun (e : Global) => s!"profile merge: `{e.toName}`"
        let full ← (IxVM.ixVMFullOver profile).mapError
          fun (e : Global) => s!"kernel merge: `{e.toName}`"
        let compiled ← full.compile
        compiled.bytecode.checkConstants koalaBearSize
        : Except String Unit) with
     | .ok _ => test "ixVM over the KoalaBear profile compiles; constants fit p" true
     | .error e => test s!"ixVM over the KoalaBear profile: {e}" false)

end AiurTests.Width
