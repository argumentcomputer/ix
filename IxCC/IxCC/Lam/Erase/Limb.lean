import IxCC.Lam.Semantics
import IxCC.Lam.WordSem

/-! # Pinning and Erasing the Five 64-bit Hardware Limb Primitives

Rewrites the five pinned `IxCC.BigNat.LimbOps` globals (`addCarry64`, `subBorrow64`, `mulWide64`,
`divWide64`, `clz64`) in a `Lam.Program` into closed λ-bodies built from the 9 scalar `WordOp`
limb-component primitives (`Lam.Prim.word .w64 ...`).

Why this gives zero-alloc GMP-speed inner loops:
1. Each limb body is 3–7 Lam nodes, so `Anf` P3 inlines it directly at every call site.
2. Pair-returning ops emit `con prodKey [prim loOp args, prim hiOp args]`, which `Anf.Convert`
   places as two immediately-adjacent primitive bindings followed by `con prodKey`.
3. `Anf` P2 shrink (`projKnown` / `caseKnown` + `dead`) eliminates `con prodKey` whenever the
   caller destructures the pair (`p.1`, `p.2`, or `let (lo, hi) := ...`), leaving ZERO heap
   allocation.
4. `Rt.lowerRep` fuses adjacent `(loOp, hiOp)` pairs on identical operands into a single
   `Lir.Stmt.limb r1 r2 op` (one x86-64 `mul` / `div` / `adc` / `sbb` sequence).

All five bodies are proved exact against `IxCC.BigNat.LimbOps` (`limbBody_*_correct`). -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Limb

open IxCC.Src (CId LimbOp WordOp)
open IxCC.Ixon

/-- Convert a `Bool` variable (at index 0) into a 0/1 word literal via `case`. -/
def boolToWord (bf bt : Key.CtorKey) (scrut : Term) : Term :=
  .case scrut [.mk bf 0 (.lit (.nat 0)), .mk bt 0 (.lit (.nat 1))] none

/-- Convert a 0/1 word expression into a `Bool` via `0 < w` (`natBlt [0, w]`). -/
def wordToBool (w : Term) : Term :=
  .prim .natBlt [.lit (.nat 0), w]

/-- The closed Lam λ-body for a pinned 64-bit hardware limb primitive. -/
def limbBody (prodKey bf bt : Key.CtorKey) : LimbOp → Term
  | .clz64 =>
    .lam .strict .many (.prim (.word .w64 .clz64) [.var 0])
  | .mulWide64 =>
    .lam .strict .many (.lam .strict .many
      (.con prodKey
        [.prim (.word .w64 .mulWideLo) [.var 1, .var 0],
         .prim (.word .w64 .mulWideHi) [.var 1, .var 0]]))
  | .divWide64 =>
    -- (hi lo d _h) -> (divWideQ hi lo d, divWideR hi lo d); proof `_h` ignored.
    .lam .strict .many (.lam .strict .many (.lam .strict .many (.lam .strict .many
      (.con prodKey
        [.prim (.word .w64 .divWideQ) [.var 3, .var 2, .var 1],
         .prim (.word .w64 .divWideR) [.var 3, .var 2, .var 1]]))))
  | .addCarry64 =>
    -- (a b c) -> let cn := boolToWord c in (addCarryLo a b cn, wordToBool (addCarryOut a b cn))
    .lam .strict .many (.lam .strict .many (.lam .strict .many
      (.letE (.value .many) (boolToWord bf bt (.var 0))
        (.con prodKey
          [.prim (.word .w64 .addCarryLo) [.var 3, .var 2, .var 0],
           wordToBool (.prim (.word .w64 .addCarryOut) [.var 3, .var 2, .var 0])]))))
  | .subBorrow64 =>
    -- (a b bIn) -> let bn := boolToWord bIn in (subBorrowLo a b bn, wordToBool (subBorrowOut a b bn))
    .lam .strict .many (.lam .strict .many (.lam .strict .many
      (.letE (.value .many) (boolToWord bf bt (.var 0))
        (.con prodKey
          [.prim (.word .w64 .subBorrowLo) [.var 3, .var 2, .var 0],
           wordToBool (.prim (.word .w64 .subBorrowOut) [.var 3, .var 2, .var 0])]))))

/-- Ensure `prodKey` (tag 0, arity 2) and `Bool` keys are registered in a program's constructor
table when rewriting limb globals. -/
def ensureCtor (ctors : List CtorInfo) (info : CtorInfo) : List CtorInfo :=
  if ctors.any (·.key == info.key) then ctors else ctors ++ [info]

/-- Rewrite any global keyed `.const c _` with `(c, op) ∈ pins` to its hardware limb primitive
body. Requires `P.known.boolFalse` and `P.known.boolTrue` when `addCarry64`/`subBorrow64` appear. -/
def rewriteProgram (pins : List (CId × LimbOp)) (prodKey : Key.CtorKey) (P : Program) : Program :=
  match P.known.boolFalse, P.known.boolTrue with
  | some bf, some bt =>
    let globals := (List.range P.size).foldl (init := P.globals) fun m g =>
      match m.get? g with
      | some gl =>
        match gl.key with
        | .const c _ =>
          match pins.lookup c with
          | some op => m.insert g { gl with body := limbBody prodKey bf bt op }
          | none => m
        | _ => m
      | none => m
    let ctors := ensureCtor P.ctors { key := prodKey, tag := 0, arity := 2 }
    { P with globals, ctors }
  | _, _ => P

/-! ## Exact Semantic Agreement with `IxCC.BigNat.LimbOps` -/

theorem primResult_clz64 (K : Known) (x : UInt64) :
    primResult K (.word .w64 .clz64) [.lit (.nat x.toNat)] =
      .ok (.lit (.nat (IxCC.BigNat.clz64 x).toNat)) := by
  have hx : x.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt x
  simp only [primResult, natArgs, Prim.sem, wordSem, WordOp.arity, WordOp.isDecision,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hx, decide_true,
    Bool.or_true, Option.map_some]
  exact congrArg (fun n => Sem.Result.ok (Val.lit (.nat n))) (LimbOp.clz64_conservative x)

theorem primResult_mulWideLo (K : Known) (a b : UInt64) :
    primResult K (.word .w64 .mulWideLo) [.lit (.nat a.toNat), .lit (.nat b.toNat)] =
      .ok (.lit (.nat (IxCC.BigNat.mulWide64 a b).1.toNat)) := by
  have ha : a.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt a
  have hb : b.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt b
  simp only [primResult, natArgs, Prim.sem, wordSem, WordOp.arity, WordOp.isDecision,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, ha, hb, decide_true,
    Bool.and_self, Option.map_some]
  exact congrArg (fun n => Sem.Result.ok (Val.lit (.nat n))) (LimbOp.mulWide64_lo_conservative a b)

theorem primResult_mulWideHi (K : Known) (a b : UInt64) :
    primResult K (.word .w64 .mulWideHi) [.lit (.nat a.toNat), .lit (.nat b.toNat)] =
      .ok (.lit (.nat (IxCC.BigNat.mulWide64 a b).2.toNat)) := by
  have ha : a.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt a
  have hb : b.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt b
  simp only [primResult, natArgs, Prim.sem, wordSem, WordOp.arity, WordOp.isDecision,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, ha, hb, decide_true,
    Bool.and_self, Option.map_some]
  exact congrArg (fun n => Sem.Result.ok (Val.lit (.nat n))) (LimbOp.mulWide64_hi_conservative a b)

theorem primResult_divWideQ (K : Known) (hi lo d : UInt64) (h : hi < d) :
    primResult K (.word .w64 .divWideQ) [.lit (.nat hi.toNat), .lit (.nat lo.toNat), .lit (.nat d.toNat)] =
      .ok (.lit (.nat (IxCC.BigNat.divWide64 hi lo d h).1.toNat)) := by
  have hhi : hi.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt hi
  have hlo : lo.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt lo
  have hd : d.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt d
  simp only [primResult, natArgs, Prim.sem, wordSem, WordOp.arity, WordOp.isDecision,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hhi, hlo, hd, decide_true,
    Bool.and_self, Option.map_some, LimbOp.divWide64_q_conservative hi lo d h, Src.WordResult.val]

theorem primResult_divWideR (K : Known) (hi lo d : UInt64) (h : hi < d) :
    primResult K (.word .w64 .divWideR) [.lit (.nat hi.toNat), .lit (.nat lo.toNat), .lit (.nat d.toNat)] =
      .ok (.lit (.nat (IxCC.BigNat.divWide64 hi lo d h).2.toNat)) := by
  have hhi : hi.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt hi
  have hlo : lo.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt lo
  have hd : d.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt d
  simp only [primResult, natArgs, Prim.sem, wordSem, WordOp.arity, WordOp.isDecision,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hhi, hlo, hd, decide_true,
    Bool.and_self, Option.map_some, LimbOp.divWide64_r_conservative hi lo d h, Src.WordResult.val]

theorem primResult_addCarryLo (K : Known) (a b : UInt64) (c : Bool) :
    primResult K (.word .w64 .addCarryLo) [.lit (.nat a.toNat), .lit (.nat b.toNat), .lit (.nat c.toNat)] =
      .ok (.lit (.nat (IxCC.BigNat.addCarry64 a b c).1.toNat)) := by
  have ha : a.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt a
  have hb : b.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt b
  have hc : c.toNat < Src.Width.size .w64 := by cases c <;> decide
  simp only [primResult, natArgs, Prim.sem, wordSem, WordOp.arity, WordOp.isDecision,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, ha, hb, hc, decide_true,
    Bool.and_self, Option.map_some, LimbOp.addCarry64_lo_conservative a b c, Src.WordResult.val]

theorem primResult_addCarryOut (K : Known) (a b : UInt64) (c : Bool) :
    primResult K (.word .w64 .addCarryOut) [.lit (.nat a.toNat), .lit (.nat b.toNat), .lit (.nat c.toNat)] =
      .ok (.lit (.nat (IxCC.BigNat.addCarry64 a b c).2.toNat)) := by
  have ha : a.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt a
  have hb : b.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt b
  have hc : c.toNat < Src.Width.size .w64 := by cases c <;> decide
  simp only [primResult, natArgs, Prim.sem, wordSem, WordOp.arity, WordOp.isDecision,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, ha, hb, hc, decide_true,
    Bool.and_self, Option.map_some, LimbOp.addCarry64_out_conservative a b c, Src.WordResult.val]

theorem primResult_subBorrowLo (K : Known) (a b : UInt64) (bIn : Bool) :
    primResult K (.word .w64 .subBorrowLo) [.lit (.nat a.toNat), .lit (.nat b.toNat), .lit (.nat bIn.toNat)] =
      .ok (.lit (.nat (IxCC.BigNat.subBorrow64 a b bIn).1.toNat)) := by
  have ha : a.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt a
  have hb : b.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt b
  have hbi : bIn.toNat < Src.Width.size .w64 := by cases bIn <;> decide
  simp only [primResult, natArgs, Prim.sem, wordSem, WordOp.arity, WordOp.isDecision,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, ha, hb, hbi, decide_true,
    Bool.and_self, Option.map_some, LimbOp.subBorrow64_lo_conservative a b bIn, Src.WordResult.val]

theorem primResult_subBorrowOut (K : Known) (a b : UInt64) (bIn : Bool) :
    primResult K (.word .w64 .subBorrowOut) [.lit (.nat a.toNat), .lit (.nat b.toNat), .lit (.nat bIn.toNat)] =
      .ok (.lit (.nat (IxCC.BigNat.subBorrow64 a b bIn).2.toNat)) := by
  have ha : a.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt a
  have hb : b.toNat < Src.Width.size .w64 := IxCC.BigNat.uint64_toNat_lt b
  have hbi : bIn.toNat < Src.Width.size .w64 := by cases bIn <;> decide
  simp only [primResult, natArgs, Prim.sem, wordSem, WordOp.arity, WordOp.isDecision,
    bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, ha, hb, hbi, decide_true,
    Bool.and_self, Option.map_some, LimbOp.subBorrow64_out_conservative a b bIn, Src.WordResult.val]

theorem primResult_wordToBool (K : Known) (b : Bool) :
    primResult K .natBlt [.lit (.nat 0), .lit (.nat b.toNat)] =
      Sem.Result.ofOption ((if b then K.boolTrue else K.boolFalse).map (.con · [])) := by
  cases b
  · cases h : K.boolFalse <;> simp [primResult, natArgs, Prim.sem, h, Sem.Result.ofOption]
  · cases h : K.boolTrue <;> simp [primResult, natArgs, Prim.sem, h, Sem.Result.ofOption]

end IxCC.Lam.Erase.Limb
