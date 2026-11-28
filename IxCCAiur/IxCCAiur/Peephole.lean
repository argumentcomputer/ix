import IxCCAiur.Lower
import IxCCAiur.Gadgets
import Aiur.Generic.LawfulBEq
import Aiur.Library.U32.Correctness
import Aiur.Library.U32.Goldilocks

/-! # Certified `UInt32` Algebraic Peephole Fusion (`IxCCAiur.Peephole`)

Algebraic peephole rewriter over Formal Aiur `Aiur.Generic.Expr Nat` (supporting
both nested expressions and the ANF `let`-chains emitted by `TypedLower.lean`),
together with exact `isPlainExpr` preservation and operational `EvalExpr`
soundness proofs over `UInt32` contracts.

## Rewrites

Two-phase bottom-up pass (`rewriteExpr := lowerByteShifts [] ∘ fuseExpr []`):

1. **Phase 1 — Algebraic fusion (`fuseExpr`)**:
   * Ternary addition (`UInt32::add3`):
     - `UInt32::add (UInt32::add a b) c` → `UInt32::add3 a b c`
     - `UInt32::add a (UInt32::add b c)` → `UInt32::add3 a b c`
     (both nested and ANF `let`-chains, including tail position).
   * Byte-aligned constant rotations (`UInt32::rotr16`, `UInt32::rotr8`):
     - `UInt32::or (u32_shr x 16) (u32_shl x 16)` → `UInt32::rotr16 x`
     - `UInt32::or (u32_shr x 8) (u32_shl x 24)` → `UInt32::rotr8 x`
     (in either operand order, both nested and ANF `let`-chains).
   * Fused XOR-rotations (`UInt32::xor_rotr12`, `UInt32::xor_rotr7`):
     - `UInt32::or (u32_shr (UInt32::xor a b) 12) (u32_shl (UInt32::xor a b) 20)` → `UInt32::xor_rotr12 a b`
     - `UInt32::or (u32_shr (UInt32::xor a b) 7) (u32_shl (UInt32::xor a b) 25)` → `UInt32::xor_rotr7 a b`
     (in either operand order, both nested and 3- and 4-step ANF `let`-chains).
   * Constant `UInt32` propagation (`u32_of_field`, `UInt32::from_field`,
     `UInt32::from_fields`, and `UInt32::sub` of constants such as `32 - c` from
     `rotr32`) into shift counts, dropping newly-dead pure constant bindings.

2. **Phase 2 — Constant byte-shuffle lowering (`lowerByteShifts`)**:
   Runs *after* rotation fusion so `rotr8`/`rotr16` always fuse first:
   * `u32_shr x 0` / `u32_shl x 0` → `x`
   * `u32_shr x k` / `u32_shl x k` for `k % 32 ∈ {8, 16, 24}` → inline byte
     permutation `UInt32::from_bytes [...]` with a checked zero byte obtained via
     `UInt8::from_fields(0, 0)` (keeping every emitted expression strictly plain
     with `isPlainExpr = true` and reusing the already-linked `pair_inputs` table).

## Soundness Guarantees

* `isPlainExpr_rewriteExpr`: exact Boolean equality
  `isPlainExpr (rewriteExpr e) = isPlainExpr e`.
* Pure `Nat` bitwise/byte-packing identities for `add3`, `rotr8`, `rotr16`,
  `xor_rotr7`, `xor_rotr12`, and byte shifts by `0, 8, 16, 24`.
* `U32Contracts`: operational contracts over `Aiur.Generic.SourceSemantics.EvalFn`
  (plus library-body proofs connecting `Aiur.Library.U32` bodies to `U32Contracts`).
* `EvalExpr` soundness theorems for `add3` (left & right), `rotr16`, `rotr8`,
  `xor_rotr12`, `xor_rotr7`, `byteShrE`, and `byteShlE`.

Zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`, zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.Peephole

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Lower
  (Expr Pat Fn callE vE litE letE qualified isPlainExpr isPlainList isPlainArms)
open IxCC.AiurBackend.Gadgets

/-! ## Pattern Binding, Free-Variable, and Purity Helpers -/

/-- Local-variable constant environment mapping `UInt32`-typed Aiur locals to their
known value modulo `2^32`. -/
abbrev ConstEnv := List (String × Nat)

def envRemove (names : List String) (env : ConstEnv) : ConstEnv :=
  env.filter fun p => !(names.contains p.1)

mutual

/-- All variable names bound by a pattern. -/
def patBoundNames : Pat → List String
  | .bind n => [n]
  | .literal _ | .wildcard | .global _ _ => []
  | .load p | .repeat p _ => patBoundNames p
  | .orElse l r _ => patBoundNames l ++ patBoundNames r
  | .tuple ps | .array ps | .record _ ps | .construct _ _ ps | .constructAs _ _ _ ps =>
    patBoundNamesList ps

def patBoundNamesList : List Pat → List String
  | [] => []
  | p :: ps => patBoundNames p ++ patBoundNamesList ps

end

mutual

/-- Conservative check whether local variable `nm` occurs free in `e`. -/
def occursFree (nm : String) : Expr → Bool
  | .var n => n == nm
  | .literal _ | .global _ _ => false
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs =>
    occursFreeList nm xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x | .control _ x =>
    occursFree nm x
  | .binary _ l r => occursFree nm l || occursFree nm r
  | .letValue p v b =>
    occursFree nm v || (!(patBoundNames p).contains nm && occursFree nm b)
  | .matchValue s arms =>
    occursFree nm s || occursFreeArms nm arms

def occursFreeList (nm : String) : List Expr → Bool
  | [] => false
  | x :: xs => occursFree nm x || occursFreeList nm xs

def occursFreeArms (nm : String) : List (Pat × Expr) → Bool
  | [] => false
  | (p, b) :: rest =>
    (!(patBoundNames p).contains nm && occursFree nm b) || occursFreeArms nm rest

end

/-- Whether `nm` is a known heap-pure `UInt32` / `UInt8` call (never executes `.store`). -/
def isPureU32Callee (nm : String) : Bool :=
  nm == "UInt32::add" || nm == "UInt32::add3" || nm == "UInt32::sub" ||
  nm == "UInt32::xor" || nm == "UInt32::and" || nm == "UInt32::or" ||
  nm == "UInt32::rotr8" || nm == "UInt32::rotr16" ||
  nm == "UInt32::xor_rotr7" || nm == "UInt32::xor_rotr12" ||
  nm == "UInt32::from_bytes" || nm == "UInt32::to_bytes" ||
  nm == "UInt32::from_field" || nm == "UInt32::from_fields" ||
  nm == "UInt32::compact" || nm == "UInt8::from_fields" || nm == "UInt8::to_field" ||
  nm == "u32_of_field" || nm == "Prog::u32_of_field" ||
  nm == "u32_shr" || nm == "Prog::u32_shr" ||
  nm == "u32_shl" || nm == "Prog::u32_shl" ||
  nm == "u32_mul" || nm == "Prog::u32_mul"

mutual

/-- Conservative heap-purity check: guarantees evaluating `e` never allocates on the
heap (contains no `.store` and only calls known heap-pure word operations). -/
def isHeapPure : Expr → Bool
  | .literal _ | .var _ => true
  | .tuple xs | .array xs => isHeapPureList xs
  | .index x _ | .project x _ | .neg x => isHeapPure x
  | .binary _ l r => isHeapPure l && isHeapPure r
  | .call nm (some []) xs => isPureU32Callee nm && isHeapPureList xs
  | _ => false

def isHeapPureList : List Expr → Bool
  | [] => true
  | x :: xs => isHeapPure x && isHeapPureList xs

end

/-- Pure atomic `UInt32` expression that can be safely evaluated earlier without
changing trap or allocation order (variables and constant `UInt32` literals). -/
def isPureU32Atom : Expr → Bool
  | .var _ | .literal _ => true
  | .call nm (some []) [.literal _] =>
    nm == "u32_of_field" || nm == "Prog::u32_of_field" || nm == "UInt32::from_field"
  | _ => false

/-! ## Constant `UInt32` Recognition & Structural Matchers -/

def isShrName (nm : String) : Bool :=
  nm == "u32_shr" || nm == "Prog::u32_shr"

def isShlName (nm : String) : Bool :=
  nm == "u32_shl" || nm == "Prog::u32_shl"

def isU32OfFieldName (nm : String) : Bool :=
  nm == "u32_of_field" || nm == "Prog::u32_of_field" || nm == "UInt32::from_field"

/-- Extract a statically known `UInt32` constant (modulo `2^32`) from an Aiur
expression under constant environment `env`. Recognizes literals, bound constant
locals, `u32_of_field`/`UInt32::from_field` on literals, `UInt32::from_fields` on
4 byte literals, and `UInt32::sub` of two constants (such as `32 - c` in `rotr32`). -/
def extractU32Const? (env : ConstEnv) : Expr → Option Nat
  | .literal k => some (k % U32.base)
  | .var nm => env.lookup nm
  | .call nm (some []) [.literal k] =>
    if isU32OfFieldName nm then some (k % U32.base) else none
  | .call "UInt32::from_fields" (some []) [.array [.literal b0, .literal b1, .literal b2, .literal b3]] =>
    if b0 < 256 && b1 < 256 && b2 < 256 && b3 < 256 then
      some (U32.pack b0 b1 b2 b3)
    else none
  | .call "UInt32::sub" (some []) [a, b] =>
    match extractU32Const? env a, extractU32Const? env b with
    | some va, some vb => some ((U32.base + va - vb) % U32.base)
    | _, _ => none
  | _ => none

theorem isPlainExpr_of_extractU32Const? {env : ConstEnv} {e : Expr} {k : Nat}
    (h : extractU32Const? env e = some k) : isPlainExpr e = true := by
  unfold extractU32Const? at h
  split at h
  · rfl
  · rfl
  · rfl
  · rfl
  · next a b =>
    cases ha : extractU32Const? env a with
    | none => simp [ha] at h
    | some va =>
      cases hb : extractU32Const? env b with
      | none => simp [ha, hb] at h
      | some vb =>
        have hpa := isPlainExpr_of_extractU32Const? ha
        have hpb := isPlainExpr_of_extractU32Const? hb
        simp [isPlainExpr, isPlainList, hpa, hpb]
  · cases h
termination_by sizeOf e

/-- Match `UInt32::add(a, b)`. -/
def matchAdd : Expr → Option (Expr × Expr)
  | .call "UInt32::add" (some []) [a, b] => some (a, b)
  | _ => none

/-- Match `UInt32::xor(a, b)`. -/
def matchXor : Expr → Option (Expr × Expr)
  | .call "UInt32::xor" (some []) [a, b] => some (a, b)
  | _ => none

/-- Match `UInt32::or(a, b)`. -/
def matchOr : Expr → Option (Expr × Expr)
  | .call "UInt32::or" (some []) [a, b] => some (a, b)
  | _ => none

/-- Match a constant-count shift `u32_shr(x, c)` (`isRight = true`) or
`u32_shl(x, c)` (`isRight = false`), returning `(isRight, x, k % 32)`. -/
def matchShiftConst (env : ConstEnv) : Expr → Option (Bool × Expr × Nat)
  | .call nm (some []) [x, c] =>
    if isShrName nm then
      (extractU32Const? env c).map fun k => (true, x, k % 32)
    else if isShlName nm then
      (extractU32Const? env c).map fun k => (false, x, k % 32)
    else none
  | _ => none

/-- Match a pair `(e1, e2)` of complementary constant shifts of the same heap-pure
operand `x` (one `u32_shr`, one `u32_shl`, in either order), returning
`(x, kShr, kShl)` with `kShr, kShl < 32`. -/
def matchRotPair (env : ConstEnv) (e1 e2 : Expr) : Option (Expr × Nat × Nat) :=
  match matchShiftConst env e1, matchShiftConst env e2 with
  | some (true, x1, kShr), some (false, x2, kShl) =>
    if x1 == x2 && isHeapPure x1 then some (x1, kShr, kShl) else none
  | some (false, x1, kShl), some (true, x2, kShr) =>
    if x1 == x2 && isHeapPure x1 then some (x1, kShr, kShl) else none
  | _, _ => none

theorem matchAdd_plain {e a b : Expr} (h : matchAdd e = some (a, b)) :
    isPlainExpr e = (isPlainExpr a && isPlainExpr b) := by
  unfold matchAdd at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [isPlainExpr, isPlainList]
  · cases h

theorem matchXor_plain {e a b : Expr} (h : matchXor e = some (a, b)) :
    isPlainExpr e = (isPlainExpr a && isPlainExpr b) := by
  unfold matchXor at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [isPlainExpr, isPlainList]
  · cases h

theorem matchOr_plain {e a b : Expr} (h : matchOr e = some (a, b)) :
    isPlainExpr e = (isPlainExpr a && isPlainExpr b) := by
  unfold matchOr at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [isPlainExpr, isPlainList]
  · cases h

theorem matchShiftConst_plain {env : ConstEnv} {e x : Expr} {d : Bool} {k : Nat}
    (h : matchShiftConst env e = some (d, x, k)) :
    isPlainExpr e = isPlainExpr x := by
  unfold matchShiftConst at h
  split at h
  · next nm a c =>
    split at h
    · cases hc : extractU32Const? env c with
      | none => simp [hc] at h
      | some kv =>
        rw [hc] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        have hpc := isPlainExpr_of_extractU32Const? hc
        simp [isPlainExpr, isPlainList, hpc]
    · split at h
      · cases hc : extractU32Const? env c with
        | none => simp [hc] at h
        | some kv =>
          rw [hc] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl, _⟩ := h
          have hpc := isPlainExpr_of_extractU32Const? hc
          simp [isPlainExpr, isPlainList, hpc]
      · cases h
  · cases h

theorem matchRotPair_plain {env : ConstEnv} {e1 e2 x : Expr} {k1 k2 : Nat}
    (h : matchRotPair env e1 e2 = some (x, k1, k2)) :
    (isPlainExpr e1 && isPlainExpr e2) = isPlainExpr x := by
  unfold matchRotPair at h
  split at h
  · next x1 kShr x2 kShl h1 h2 =>
    have hp1 := matchShiftConst_plain h1
    have hp2 := matchShiftConst_plain h2
    split at h
    · next hcond =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rw [hp1, hp2, ← hcond.1, Bool.and_self]
    · cases h
  · next x1 kShl x2 kShr h1 h2 =>
    have hp1 := matchShiftConst_plain h1
    have hp2 := matchShiftConst_plain h2
    split at h
    · next hcond =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rw [hp1, hp2, ← hcond.1, Bool.and_self]
    · cases h
  · cases h

/-! ## Phase 1: Algebraic Fusion (`add3`, `rotr8`, `rotr16`, `xor_rotr7`, `xor_rotr12`) -/

def rotrFnOf? : Nat → Nat → Option String
  | 16, 16 => some "UInt32::rotr16"
  | 8, 24 => some "UInt32::rotr8"
  | _, _ => none

def xorRotrFnOf? : Nat → Nat → Option String
  | 12, 20 => some "UInt32::xor_rotr12"
  | 7, 25 => some "UInt32::xor_rotr7"
  | _, _ => none

/-- Whether `(o1, o2)` is `{vE a, vE b}` in either order. -/
def isVarPair (a b : String) (o1 o2 : Expr) : Bool :=
  (o1 == vE a && o2 == vE b) || (o1 == vE b && o2 == vE a)

theorem isPlainExpr_of_isVarPair {a b : String} {o1 o2 : Expr}
    (h : isVarPair a b o1 o2 = true) :
    isPlainExpr o1 = true ∧ isPlainExpr o2 = true := by
  simp only [isVarPair, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- Local non-recursive fusion step on a `.call name types args` whose arguments
have already been fused bottom-up. -/
def tryFuseCall (env : ConstEnv) (name : String) (types : Option (List Lower.Ty))
    (args : List Expr) : Option Expr :=
  match types, args with
  | some [], [a, b] =>
    if name == "UInt32::add" then
      match matchAdd a with
      | some (x, y) => some (callE "UInt32::add3" [x, y, b])
      | none =>
        match matchAdd b with
        | some (y, z) => some (callE "UInt32::add3" [a, y, z])
        | none => none
    else if name == "UInt32::or" then
      match matchRotPair env a b with
      | some (x, kShr, kShl) =>
        match rotrFnOf? kShr kShl with
        | some rotName => some (callE rotName [x])
        | none =>
          match xorRotrFnOf? kShr kShl, matchXor x with
          | some xfn, some (u, v) => some (callE xfn [u, v])
          | _, _ => none
      | none => none
    else if isShrName name || isShlName name then
      -- Inline constant shift-count locals (`let c = u32_of_field(k); u32_shr(x, c)`)
      -- so dead constant bindings can be dropped and ANF rotations become adjacent.
      match b with
      | .var nm =>
        match env.lookup nm with
        | some k => some (callE name [a, callE "u32_of_field" [litE (k % 32)]])
        | none => none
      | _ => none
    else none
  | _, _ => none

theorem tryFuseCall_plain {env : ConstEnv} {name : String} {types : Option (List Lower.Ty)}
    {args : List Expr} {e' : Expr} (h : tryFuseCall env name types args = some e') :
    isPlainExpr e' = isPlainList args := by
  unfold tryFuseCall at h
  split at h
  · next a b =>
    split at h
    · cases ha : matchAdd a with
      | some p =>
        rw [ha] at h; dsimp only at h
        rcases p with ⟨x, y⟩
        simp only [Option.some.injEq] at h
        subst h
        have hpa := matchAdd_plain ha
        simp [callE, isPlainExpr, isPlainList, hpa, Bool.and_assoc]
      | none =>
        rw [ha] at h; dsimp only at h
        cases hb : matchAdd b with
        | none => simp [hb] at h
        | some p =>
          rw [hb] at h; dsimp only at h
          rcases p with ⟨y, z⟩
          simp only [Option.some.injEq] at h
          subst h
          have hpb := matchAdd_plain hb
          simp [callE, isPlainExpr, isPlainList, hpb]
    · split at h
      · cases hr : matchRotPair env a b with
        | none => simp [hr] at h
        | some t =>
          rcases t with ⟨x, kShr, kShl⟩
          rw [hr] at h; dsimp only at h
          have hpr := matchRotPair_plain hr
          cases hrot : rotrFnOf? kShr kShl with
          | some rotName =>
            rw [hrot] at h; dsimp only at h
            simp only [Option.some.injEq] at h
            subst h
            simp [callE, isPlainExpr, isPlainList, hpr]
          | none =>
            rw [hrot] at h; dsimp only at h
            cases hxrot : xorRotrFnOf? kShr kShl with
            | none => simp [hxrot] at h
            | some xfn =>
              cases hxor : matchXor x with
              | none => simp [hxrot, hxor] at h
              | some p =>
                rcases p with ⟨u, v⟩
                rw [hxrot, hxor] at h; dsimp only at h
                simp only [Option.some.injEq] at h
                subst h
                have hpx := matchXor_plain hxor
                simp [callE, isPlainExpr, isPlainList, ← hpx, ← hpr]
      · split at h
        · cases b with
          | var nm =>
            dsimp only at h
            cases hl : env.lookup nm with
            | none => simp [hl] at h
            | some k =>
              rw [hl] at h; dsimp only at h
              simp only [Option.some.injEq] at h
              subst h
              simp [callE, litE, isPlainExpr, isPlainList]
          | _ => cases h
        · cases h
  · cases h

/-! ### Modular ANF `let`-Chain Fusion Helpers -/

/-- (1) Drop a newly-dead pure constant `UInt32` binding. -/
def tryDropDeadConst (env : ConstEnv) (nm : String) (val body : Expr) : Option Expr :=
  match extractU32Const? env val with
  | some _ => if !occursFree nm body then some body else none
  | none => none

/-- (2) ANF 2-step & tail `UInt32::add3` fusion (left- and right-nested). -/
def tryFuseLetAdd3 (nm : String) (val body : Expr) : Option Expr :=
  match matchAdd val with
  | none => none
  | some (a, b) =>
    match body with
    | .letValue (.bind y) rhs rest =>
      match matchAdd rhs with
      | some (p, q) =>
        if p == vE nm && !occursFree nm q && (nm == y || !occursFree nm rest) then
          some (letE y (callE "UInt32::add3" [a, b, q]) rest)
        else if q == vE nm && !occursFree nm p && isPureU32Atom p &&
            (nm == y || !occursFree nm rest) then
          some (letE y (callE "UInt32::add3" [p, a, b]) rest)
        else none
      | none => none
    | _ =>
      match matchAdd body with
      | some (p, q) =>
        if p == vE nm && !occursFree nm q then
          some (callE "UInt32::add3" [a, b, q])
        else if q == vE nm && !occursFree nm p && isPureU32Atom p then
          some (callE "UInt32::add3" [p, a, b])
        else none
      | none => none

/-- (3) ANF 3-step & tail `UInt32::rotr16` / `UInt32::rotr8` fusion. -/
def tryFuseLetRotr (env : ConstEnv) (nm : String) (val body : Expr) : Option Expr :=
  match matchShiftConst env val with
  | none => none
  | some (d1, x1, k1) =>
    if !isHeapPure x1 then none
    else
      match body with
      | .letValue (.bind s2) val2 body2 =>
        if s2 == nm then none
        else
          match matchShiftConst env val2 with
          | none => none
          | some (d2, x2, k2) =>
            if d1 == d2 || !(x1 == x2) || occursFree nm x2 then none
            else
              let kShr := if d1 then k1 else k2
              let kShl := if d1 then k2 else k1
              match rotrFnOf? kShr kShl with
              | none => none
              | some rotName =>
                match body2 with
                | .letValue (.bind y) rhs rest =>
                  match matchOr rhs with
                  | some (o1, o2) =>
                    if isVarPair nm s2 o1 o2 &&
                        (nm == y || !occursFree nm rest) &&
                        (s2 == y || !occursFree s2 rest) then
                      some (letE y (callE rotName [x1]) rest)
                    else none
                  | none => none
                | _ =>
                  match matchOr body2 with
                  | some (o1, o2) =>
                    if isVarPair nm s2 o1 o2 then some (callE rotName [x1]) else none
                  | none => none
      | _ => none

/-- (4a) ANF 4-step & tail `UInt32::xor_rotr12` / `UInt32::xor_rotr7` fusion. -/
def tryFuseLetXorRotr4 (env : ConstEnv) (nm : String) (val body : Expr) : Option Expr :=
  match matchXor val, body with
  | some (a, b), .letValue (.bind s1) val1 (.letValue (.bind s2) val2 body2) =>
    if s1 == nm || s2 == nm || s1 == s2 then none
    else
      match matchShiftConst env val1, matchShiftConst env val2 with
      | some (d1, x1, k1), some (d2, x2, k2) =>
        if d1 == d2 || !(x1 == vE nm) || !(x2 == vE nm) then none
        else
          let kShr := if d1 then k1 else k2
          let kShl := if d1 then k2 else k1
          match xorRotrFnOf? kShr kShl with
          | none => none
          | some xfn =>
            match body2 with
            | .letValue (.bind y) rhs rest =>
              match matchOr rhs with
              | some (o1, o2) =>
                if isVarPair s1 s2 o1 o2 &&
                    (nm == y || !occursFree nm rest) &&
                    (s1 == y || !occursFree s1 rest) &&
                    (s2 == y || !occursFree s2 rest) then
                  some (letE y (callE xfn [a, b]) rest)
                else none
              | none => none
            | _ =>
              match matchOr body2 with
              | some (o1, o2) =>
                if isVarPair s1 s2 o1 o2 then some (callE xfn [a, b]) else none
              | none => none
      | _, _ => none
  | _, _ => none

/-- (4b) Half-nested `let w = xor(a, b); [let y =] or(sh1(w, k1), sh2(w, k2))` fusion. -/
def tryFuseLetXorRotrHalf (env : ConstEnv) (nm : String) (val body : Expr) : Option Expr :=
  match matchXor val with
  | none => none
  | some (a, b) =>
    match body with
    | .letValue (.bind y) rhs rest =>
      match matchOr rhs with
      | some (e1, e2) =>
        match matchRotPair env e1 e2 with
        | some (x, kShr, kShl) =>
          if !(x == vE nm) || !(nm == y || !occursFree nm rest) then none
          else
            match xorRotrFnOf? kShr kShl with
            | some xfn => some (letE y (callE xfn [a, b]) rest)
            | none => none
        | none => none
      | none => none
    | _ =>
      match matchOr body with
      | some (e1, e2) =>
        match matchRotPair env e1 e2 with
        | some (x, kShr, kShl) =>
          if !(x == vE nm) then none
          else
            match xorRotrFnOf? kShr kShl with
            | some xfn => some (callE xfn [a, b])
            | none => none
        | none => none
      | none => none

/-- Combined ANF `let`-chain fusion step for `.letValue (.bind nm) val body`. -/
def tryFuseLet (env : ConstEnv) (nm : String) (val body : Expr) : Option Expr :=
  match tryDropDeadConst env nm val body with
  | some e => some e
  | none =>
    match tryFuseLetAdd3 nm val body with
    | some e => some e
    | none =>
      match tryFuseLetRotr env nm val body with
      | some e => some e
      | none =>
        match tryFuseLetXorRotr4 env nm val body with
        | some e => some e
        | none => tryFuseLetXorRotrHalf env nm val body

private theorem tryDropDeadConst_plain {env : ConstEnv} {nm : String} {val body e' : Expr}
    (h : tryDropDeadConst env nm val body = some e') :
    isPlainExpr e' = (isPlainExpr val && isPlainExpr body) := by
  unfold tryDropDeadConst at h
  cases hc : extractU32Const? env val with
  | none => simp [hc] at h
  | some _ =>
    rw [hc] at h; dsimp only at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rw [isPlainExpr_of_extractU32Const? hc, Bool.true_and]
    · cases h

private theorem tryFuseLetAdd3_plain {nm : String} {val body e' : Expr}
    (h : tryFuseLetAdd3 nm val body = some e') :
    isPlainExpr e' = (isPlainExpr val && isPlainExpr body) := by
  unfold tryFuseLetAdd3 at h
  cases ha : matchAdd val with
  | none => simp [ha] at h
  | some pab =>
    rcases pab with ⟨a, b⟩
    rw [ha] at h; dsimp only at h
    have hpa := matchAdd_plain ha
    split at h
    · next y rhs rest =>
      cases hr : matchAdd rhs with
      | none => simp [hr] at h
      | some pq =>
        rcases pq with ⟨p, q⟩
        rw [hr] at h; dsimp only at h
        have hpr := matchAdd_plain hr
        split at h
        · next hcond =>
          simp only [Option.some.injEq] at h; subst h
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          have hp : isPlainExpr p = true := by rw [hcond.1.1]; rfl
          simp [letE, callE, isPlainExpr, isPlainList, hpa, hpr, hp, Bool.and_assoc]
        · split at h
          · next hcond =>
            simp only [Option.some.injEq] at h; subst h
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            have hq : isPlainExpr q = true := by rw [hcond.1.1.1]; rfl
            simp only [letE, callE, isPlainExpr, isPlainList, hpa, hpr, hq,
              Bool.and_true]
            cases isPlainExpr a <;> cases isPlainExpr b <;>
              cases isPlainExpr p <;> cases isPlainExpr rest <;> rfl
          · cases h
    · cases hr : matchAdd body with
      | none => simp [hr] at h
      | some pq =>
        rcases pq with ⟨p, q⟩
        rw [hr] at h; dsimp only at h
        have hpr := matchAdd_plain hr
        split at h
        · next hcond =>
          simp only [Option.some.injEq] at h; subst h
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          have hp : isPlainExpr p = true := by rw [hcond.1]; rfl
          simp [callE, isPlainExpr, isPlainList, hpa, hpr, hp, Bool.and_assoc]
        · split at h
          · next hcond =>
            simp only [Option.some.injEq] at h; subst h
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            have hq : isPlainExpr q = true := by rw [hcond.1.1]; rfl
            simp only [callE, isPlainExpr, isPlainList, hpa, hpr, hq,
              Bool.and_true]
            cases isPlainExpr a <;> cases isPlainExpr b <;> cases isPlainExpr p <;> rfl
          · cases h

private theorem tryFuseLetRotr_plain {env : ConstEnv} {nm : String} {val body e' : Expr}
    (h : tryFuseLetRotr env nm val body = some e') :
    isPlainExpr e' = (isPlainExpr val && isPlainExpr body) := by
  unfold tryFuseLetRotr at h
  cases hs1 : matchShiftConst env val with
  | none => simp [hs1] at h
  | some sh1 =>
    rcases sh1 with ⟨d1, x1, k1⟩
    rw [hs1] at h; dsimp only at h
    have hps1 := matchShiftConst_plain hs1
    split at h
    · cases h
    · split at h
      · next s2 val2 body2 =>
        split at h
        · cases h
        · cases hs2 : matchShiftConst env val2 with
          | none => simp [hs2] at h
          | some sh2 =>
            rcases sh2 with ⟨d2, x2, k2⟩
            rw [hs2] at h; dsimp only at h
            have hps2 := matchShiftConst_plain hs2
            split at h
            · cases h
            · next hne =>
              have hxEq : x1 = x2 := by
                by_contra hneq
                apply hne
                simp [beq_false_of_ne hneq]
              cases hrot : rotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
              | none => simp [hrot] at h
              | some rotName =>
                rw [hrot] at h; dsimp only at h
                split at h
                · next y rhs rest =>
                  cases hor : matchOr rhs with
                  | none => simp [hor] at h
                  | some po =>
                    rcases po with ⟨o1, o2⟩
                    rw [hor] at h; dsimp only at h
                    have hpor := matchOr_plain hor
                    split at h
                    · next hcond =>
                      simp only [Option.some.injEq] at h; subst h
                      simp only [Bool.and_eq_true] at hcond
                      obtain ⟨ho1, ho2⟩ := isPlainExpr_of_isVarPair hcond.1.1
                      simp [letE, callE, isPlainExpr, isPlainList, hps1, hps2, hpor,
                        ho1, ho2, ← hxEq]
                    · cases h
                · cases hor : matchOr body2 with
                  | none => simp [hor] at h
                  | some po =>
                    rcases po with ⟨o1, o2⟩
                    rw [hor] at h; dsimp only at h
                    have hpor := matchOr_plain hor
                    split at h
                    · next hcond =>
                      simp only [Option.some.injEq] at h; subst h
                      obtain ⟨ho1, ho2⟩ := isPlainExpr_of_isVarPair hcond
                      simp [callE, isPlainExpr, isPlainList, hps1, hps2, hpor,
                        ho1, ho2, ← hxEq]
                    · cases h
      · cases h

private theorem tryFuseLetXorRotr4_plain {env : ConstEnv} {nm : String} {val body e' : Expr}
    (h : tryFuseLetXorRotr4 env nm val body = some e') :
    isPlainExpr e' = (isPlainExpr val && isPlainExpr body) := by
  unfold tryFuseLetXorRotr4 at h
  split at h
  · next a b s1 val1 s2 val2 body2 hx =>
    have hpx := matchXor_plain hx
    split at h
    · cases h
    · split at h
      · next d1 x1 k1 d2 x2 k2 hs1 hs2 =>
        have hps1 := matchShiftConst_plain hs1
        have hps2 := matchShiftConst_plain hs2
        split at h
        · cases h
        · next hne =>
          have hx1 : x1 = vE nm := by
            by_contra hneq; apply hne; simp [beq_false_of_ne hneq]
          have hx2 : x2 = vE nm := by
            by_contra hneq; apply hne; simp [beq_false_of_ne hneq]
          have hpx1 : isPlainExpr x1 = true := by rw [hx1]; rfl
          have hpx2 : isPlainExpr x2 = true := by rw [hx2]; rfl
          dsimp only at h
          cases hxr : xorRotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
          | none => simp [hxr] at h
          | some xfn =>
            rw [hxr] at h; dsimp only at h
            split at h
            · next y rhs rest =>
              cases hor : matchOr rhs with
              | none => simp [hor] at h
              | some po =>
                rcases po with ⟨o1, o2⟩
                rw [hor] at h; dsimp only at h
                have hpor := matchOr_plain hor
                split at h
                · next hcond =>
                  simp only [Option.some.injEq] at h; subst h
                  simp only [Bool.and_eq_true] at hcond
                  obtain ⟨ho1, ho2⟩ := isPlainExpr_of_isVarPair hcond.1.1.1
                  simp [letE, callE, isPlainExpr, isPlainList, hpx,
                    hps1, hps2, hpx1, hpx2, hpor, ho1, ho2, Bool.and_assoc]
                · cases h
            · cases hor : matchOr body2 with
              | none => simp [hor] at h
              | some po =>
                rcases po with ⟨o1, o2⟩
                rw [hor] at h; dsimp only at h
                have hpor := matchOr_plain hor
                split at h
                · next hcond =>
                  simp only [Option.some.injEq] at h; subst h
                  obtain ⟨ho1, ho2⟩ := isPlainExpr_of_isVarPair hcond
                  simp [callE, isPlainExpr, isPlainList, hpx,
                    hps1, hps2, hpx1, hpx2, hpor, ho1, ho2]
                · cases h
      · cases h
  · cases h

private theorem tryFuseLetXorRotrHalf_plain {env : ConstEnv} {nm : String} {val body e' : Expr}
    (h : tryFuseLetXorRotrHalf env nm val body = some e') :
    isPlainExpr e' = (isPlainExpr val && isPlainExpr body) := by
  unfold tryFuseLetXorRotrHalf at h
  cases hx : matchXor val with
  | none => simp [hx] at h
  | some pab =>
    rcases pab with ⟨a, b⟩
    rw [hx] at h; dsimp only at h
    have hpx := matchXor_plain hx
    split at h
    · next y rhs rest =>
      cases hor : matchOr rhs with
      | none => simp [hor] at h
      | some po =>
        rcases po with ⟨e1, e2⟩
        rw [hor] at h; dsimp only at h
        have hpor := matchOr_plain hor
        cases hrp : matchRotPair env e1 e2 with
        | none => simp [hrp] at h
        | some tr =>
          rcases tr with ⟨x, kShr, kShl⟩
          rw [hrp] at h; dsimp only at h
          have hprp := matchRotPair_plain hrp
          split at h
          · cases h
          · next hne =>
            have hxv : x = vE nm := by
              by_contra hneq; apply hne; simp [beq_false_of_ne hneq]
            have hpxv : isPlainExpr x = true := by rw [hxv]; rfl
            cases hxr : xorRotrFnOf? kShr kShl with
            | none => simp [hxr] at h
            | some xfn =>
              rw [hxr] at h; dsimp only at h
              simp only [Option.some.injEq] at h; subst h
              simp [letE, callE, isPlainExpr, isPlainList, hpx, hpor, hprp, hpxv, Bool.and_assoc]
    · cases hor : matchOr body with
      | none => simp [hor] at h
      | some po =>
        rcases po with ⟨e1, e2⟩
        rw [hor] at h; dsimp only at h
        have hpor := matchOr_plain hor
        cases hrp : matchRotPair env e1 e2 with
        | none => simp [hrp] at h
        | some tr =>
          rcases tr with ⟨x, kShr, kShl⟩
          rw [hrp] at h; dsimp only at h
          have hprp := matchRotPair_plain hrp
          split at h
          · cases h
          · next hne =>
            have hxv : x = vE nm := by
              by_contra hneq; apply hne; simp [beq_false_of_ne hneq]
            have hpxv : isPlainExpr x = true := by rw [hxv]; rfl
            cases hxr : xorRotrFnOf? kShr kShl with
            | none => simp [hxr] at h
            | some xfn =>
              rw [hxr] at h; dsimp only at h
              simp only [Option.some.injEq] at h; subst h
              simp [callE, isPlainExpr, isPlainList, hpx, hpor, hprp, hpxv]

theorem tryFuseLet_plain {env : ConstEnv} {nm : String} {val body e' : Expr}
    (h : tryFuseLet env nm val body = some e') :
    isPlainExpr e' = (isPlainExpr val && isPlainExpr body) := by
  unfold tryFuseLet at h
  cases h1 : tryDropDeadConst env nm val body with
  | some e =>
    rw [h1] at h; simp only [Option.some.injEq] at h; subst h
    exact tryDropDeadConst_plain h1
  | none =>
    rw [h1] at h
    cases h2 : tryFuseLetAdd3 nm val body with
    | some e =>
      rw [h2] at h; simp only [Option.some.injEq] at h; subst h
      exact tryFuseLetAdd3_plain h2
    | none =>
      rw [h2] at h
      cases h3 : tryFuseLetRotr env nm val body with
      | some e =>
        rw [h3] at h; simp only [Option.some.injEq] at h; subst h
        exact tryFuseLetRotr_plain h3
      | none =>
        rw [h3] at h
        cases h4 : tryFuseLetXorRotr4 env nm val body with
        | some e =>
          rw [h4] at h; simp only [Option.some.injEq] at h; subst h
          exact tryFuseLetXorRotr4_plain h4
        | none =>
          rw [h4] at h
          exact tryFuseLetXorRotrHalf_plain h

mutual

/-- Phase 1 bottom-up algebraic fusion over `Aiur.Generic.Expr Nat`. -/
def fuseExpr (env : ConstEnv) : Expr → Expr
  | .literal x => .literal x
  | .var n => .var n
  | .global n t => .global n t
  | .tuple xs => .tuple (fuseList env xs)
  | .array xs => .array (fuseList env xs)
  | .repeat x n => .repeat (fuseExpr env x) n
  | .index x i => .index (fuseExpr env x) i
  | .slice x s e => .slice (fuseExpr env x) s e
  | .construct n ts c xs => .construct n ts c (fuseList env xs)
  | .constructAs ps t c xs => .constructAs ps t c (fuseList env xs)
  | .record h xs => .record h (fuseList env xs)
  | .member x f => .member (fuseExpr env x) f
  | .update ps xs => .update ps (fuseList env xs)
  | .builtin op xs => .builtin op (fuseList env xs)
  | .project x i => .project (fuseExpr env x) i
  | .store x => .store (fuseExpr env x)
  | .load x => .load (fuseExpr env x)
  | .hint t k ch => .hint t (fuseExpr env k) ch
  | .neg x => .neg (fuseExpr env x)
  | .binary op l r => .binary op (fuseExpr env l) (fuseExpr env r)
  | .control k b => .control k (fuseExpr env b)
  | .call n ts xs =>
    let xs' := fuseList env xs
    (tryFuseCall env n ts xs').getD (.call n ts xs')
  | .letValue p v b =>
    let v' := fuseExpr env v
    match p with
    | .bind nm =>
      let env' :=
        match extractU32Const? env v' with
        | some k => (nm, k) :: envRemove [nm] env
        | none => envRemove [nm] env
      let b' := fuseExpr env' b
      (tryFuseLet env nm v' b').getD (.letValue (.bind nm) v' b')
    | _ =>
      let env' := envRemove (patBoundNames p) env
      .letValue p v' (fuseExpr env' b)
  | .matchValue s arms =>
    .matchValue (fuseExpr env s) (fuseArms env arms)

def fuseList (env : ConstEnv) : List Expr → List Expr
  | [] => []
  | x :: xs => fuseExpr env x :: fuseList env xs

def fuseArms (env : ConstEnv) : List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, b) :: rest => (p, fuseExpr (envRemove (patBoundNames p) env) b) :: fuseArms env rest

end

mutual

theorem isPlainExpr_fuseExpr (env : ConstEnv) :
    ∀ (e : Expr), isPlainExpr (fuseExpr env e) = isPlainExpr e
  | .literal _ | .var _ | .global .. => rfl
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => by
    simp [fuseExpr, isPlainExpr, isPlainExpr_fuseExpr env x]
  | .control .. => by simp [fuseExpr, isPlainExpr]
  | .binary _ l r => by
    simp [fuseExpr, isPlainExpr, isPlainExpr_fuseExpr env l, isPlainExpr_fuseExpr env r]
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => by
    simp [fuseExpr, isPlainExpr, isPlainList_fuseList env xs]
  | .call n ts xs => by
    simp only [fuseExpr]
    cases hf : tryFuseCall env n ts (fuseList env xs) with
    | none => simp [isPlainExpr, isPlainList_fuseList env xs]
    | some e' =>
      simp only [Option.getD_some]
      rw [tryFuseCall_plain hf, isPlainList_fuseList env xs]
      rfl
  | .letValue p v b => by
    cases p with
    | bind nm =>
      simp only [fuseExpr]
      set env' : ConstEnv :=
        match extractU32Const? env (fuseExpr env v) with
        | some k => (nm, k) :: envRemove [nm] env
        | none => envRemove [nm] env
      cases hf : tryFuseLet env nm (fuseExpr env v) (fuseExpr env' b) with
      | none =>
        simp [isPlainExpr, isPlainExpr_fuseExpr env v, isPlainExpr_fuseExpr env' b]
      | some e' =>
        simp only [Option.getD_some]
        rw [tryFuseLet_plain hf, isPlainExpr_fuseExpr env v, isPlainExpr_fuseExpr env' b]
        rfl
    | literal _ | wildcard | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      simp [fuseExpr, isPlainExpr, isPlainExpr_fuseExpr env v,
        isPlainExpr_fuseExpr (envRemove (patBoundNames _) env) b]
  | .matchValue s arms => by
    simp [fuseExpr, isPlainExpr, isPlainExpr_fuseExpr env s, isPlainArms_fuseArms env arms]

theorem isPlainList_fuseList (env : ConstEnv) :
    ∀ (xs : List Expr), isPlainList (fuseList env xs) = isPlainList xs
  | [] => rfl
  | x :: xs => by simp [fuseList, isPlainList, isPlainExpr_fuseExpr env x, isPlainList_fuseList env xs]

theorem isPlainArms_fuseArms (env : ConstEnv) :
    ∀ (arms : List (Pat × Expr)), isPlainArms (fuseArms env arms) = isPlainArms arms
  | [] => rfl
  | (p, b) :: rest => by
    simp [fuseArms, isPlainArms, isPlainExpr_fuseExpr (envRemove (patBoundNames p) env) b,
      isPlainArms_fuseArms env rest]

end

/-! ## Phase 2: Constant Byte-Shuffle Shifts (`k ∈ {0, 8, 16, 24}`) -/

/-- Build an inline checked-byte permutation of `x : UInt32::U32` using a checked
zero byte obtained from `UInt8::from_fields(0, 0)`. Because `x` is evaluated
before binding `__peep_b` and `__peep_z` and the body references only those two
fresh locals, no outer binding can ever be captured; and because no `.global` is
used, `isPlainExpr` is strictly preserved (`= isPlainExpr x`). -/
def byteShuffleE (x : Expr) (slots : List (Option Nat)) : Expr :=
  let bName := "__peep_b"
  let zName := "__peep_z"
  let byteAt : Option Nat → Expr
    | some idx => .index (vE bName) idx
    | none => vE zName
  letE bName (callE "UInt32::to_bytes" [x]) <|
  .letValue (.tuple [.bind zName, .wildcard]) (callE "UInt8::from_fields" [litE 0, litE 0]) <|
  callE "UInt32::from_bytes" [.array (slots.map byteAt)]

/-- Zero-cost byte-shuffle right shift for `k ∈ {0, 8, 16, 24}`. -/
def byteShrE (k : Nat) (x : Expr) : Option Expr :=
  match k % 32 with
  | 0 => some x
  | 8 => some (byteShuffleE x [some 1, some 2, some 3, none])
  | 16 => some (byteShuffleE x [some 2, some 3, none, none])
  | 24 => some (byteShuffleE x [some 3, none, none, none])
  | _ => none

/-- Zero-cost byte-shuffle left shift for `k ∈ {0, 8, 16, 24}`. -/
def byteShlE (k : Nat) (x : Expr) : Option Expr :=
  match k % 32 with
  | 0 => some x
  | 8 => some (byteShuffleE x [none, some 0, some 1, some 2])
  | 16 => some (byteShuffleE x [none, none, some 0, some 1])
  | 24 => some (byteShuffleE x [none, none, none, some 0])
  | _ => none

theorem isPlainExpr_byteShuffleE (x : Expr) (slots : List (Option Nat)) :
    isPlainExpr (byteShuffleE x slots) = isPlainExpr x := by
  have hslots : ∀ l : List (Option Nat),
      isPlainList (l.map fun
        | some idx => .index (vE "__peep_b") idx
        | none => vE "__peep_z") = true := by
    intro l
    induction l with
    | nil => rfl
    | cons o tl ih =>
      cases o <;> simp [isPlainList, isPlainExpr, ih] <;> rfl
  simp [byteShuffleE, letE, callE, litE, isPlainExpr, isPlainList, hslots]

theorem byteShrE_plain {k : Nat} {x e' : Expr} (h : byteShrE k x = some e') :
    isPlainExpr e' = isPlainExpr x := by
  unfold byteShrE at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp only [Option.some.injEq] at h; subst h; exact isPlainExpr_byteShuffleE x _
  · simp only [Option.some.injEq] at h; subst h; exact isPlainExpr_byteShuffleE x _
  · simp only [Option.some.injEq] at h; subst h; exact isPlainExpr_byteShuffleE x _
  · cases h

theorem byteShlE_plain {k : Nat} {x e' : Expr} (h : byteShlE k x = some e') :
    isPlainExpr e' = isPlainExpr x := by
  unfold byteShlE at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp only [Option.some.injEq] at h; subst h; exact isPlainExpr_byteShuffleE x _
  · simp only [Option.some.injEq] at h; subst h; exact isPlainExpr_byteShuffleE x _
  · simp only [Option.some.injEq] at h; subst h; exact isPlainExpr_byteShuffleE x _
  · cases h

def tryLowerByteShift (env : ConstEnv) (name : String) (types : Option (List Lower.Ty))
    (args : List Expr) : Option Expr :=
  match types, args with
  | some [], [x, c] =>
    if isShrName name then
      (extractU32Const? env c).bind fun k => byteShrE k x
    else if isShlName name then
      (extractU32Const? env c).bind fun k => byteShlE k x
    else none
  | _, _ => none

theorem tryLowerByteShift_plain {env : ConstEnv} {name : String}
    {types : Option (List Lower.Ty)} {args : List Expr} {e' : Expr}
    (h : tryLowerByteShift env name types args = some e') :
    isPlainExpr e' = isPlainList args := by
  unfold tryLowerByteShift at h
  split at h
  · next x c =>
    split at h
    · cases hc : extractU32Const? env c with
      | none => simp [hc] at h
      | some k =>
        rw [hc] at h
        simp only [Option.bind_some] at h
        rw [byteShrE_plain h, isPlainList, isPlainList, isPlainList,
          isPlainExpr_of_extractU32Const? hc, Bool.and_true, Bool.and_true]
    · split at h
      · cases hc : extractU32Const? env c with
        | none => simp [hc] at h
        | some k =>
          rw [hc] at h
          simp only [Option.bind_some] at h
          rw [byteShlE_plain h, isPlainList, isPlainList, isPlainList,
            isPlainExpr_of_extractU32Const? hc, Bool.and_true, Bool.and_true]
      · cases h
  · cases h

mutual

/-- Phase 2 bottom-up lowering of constant `u32_shr`/`u32_shl` by `{0, 8, 16, 24}`
to inline byte shuffles. -/
def lowerByteShifts (env : ConstEnv) : Expr → Expr
  | .literal x => .literal x
  | .var n => .var n
  | .global n t => .global n t
  | .tuple xs => .tuple (lowerByteShiftsList env xs)
  | .array xs => .array (lowerByteShiftsList env xs)
  | .repeat x n => .repeat (lowerByteShifts env x) n
  | .index x i => .index (lowerByteShifts env x) i
  | .slice x s e => .slice (lowerByteShifts env x) s e
  | .construct n ts c xs => .construct n ts c (lowerByteShiftsList env xs)
  | .constructAs ps t c xs => .constructAs ps t c (lowerByteShiftsList env xs)
  | .record h xs => .record h (lowerByteShiftsList env xs)
  | .member x f => .member (lowerByteShifts env x) f
  | .update ps xs => .update ps (lowerByteShiftsList env xs)
  | .builtin op xs => .builtin op (lowerByteShiftsList env xs)
  | .project x i => .project (lowerByteShifts env x) i
  | .store x => .store (lowerByteShifts env x)
  | .load x => .load (lowerByteShifts env x)
  | .hint t k ch => .hint t (lowerByteShifts env k) ch
  | .neg x => .neg (lowerByteShifts env x)
  | .binary op l r => .binary op (lowerByteShifts env l) (lowerByteShifts env r)
  | .control k b => .control k (lowerByteShifts env b)
  | .call n ts xs =>
    let xs' := lowerByteShiftsList env xs
    (tryLowerByteShift env n ts xs').getD (.call n ts xs')
  | .letValue p v b =>
    let v' := lowerByteShifts env v
    match p with
    | .bind nm =>
      let env' :=
        match extractU32Const? env v' with
        | some k => (nm, k) :: envRemove [nm] env
        | none => envRemove [nm] env
      .letValue (.bind nm) v' (lowerByteShifts env' b)
    | _ =>
      .letValue p v' (lowerByteShifts (envRemove (patBoundNames p) env) b)
  | .matchValue s arms =>
    .matchValue (lowerByteShifts env s) (lowerByteShiftsArms env arms)

def lowerByteShiftsList (env : ConstEnv) : List Expr → List Expr
  | [] => []
  | x :: xs => lowerByteShifts env x :: lowerByteShiftsList env xs

def lowerByteShiftsArms (env : ConstEnv) : List (Pat × Expr) → List (Pat × Expr)
  | [] => []
  | (p, b) :: rest =>
    (p, lowerByteShifts (envRemove (patBoundNames p) env) b) :: lowerByteShiftsArms env rest

end

mutual

theorem isPlainExpr_lowerByteShifts (env : ConstEnv) :
    ∀ (e : Expr), isPlainExpr (lowerByteShifts env e) = isPlainExpr e
  | .literal _ | .var _ | .global .. => rfl
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => by
    simp [lowerByteShifts, isPlainExpr, isPlainExpr_lowerByteShifts env x]
  | .control .. => by simp [lowerByteShifts, isPlainExpr]
  | .binary _ l r => by
    simp [lowerByteShifts, isPlainExpr,
      isPlainExpr_lowerByteShifts env l, isPlainExpr_lowerByteShifts env r]
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => by
    simp [lowerByteShifts, isPlainExpr, isPlainList_lowerByteShifts env xs]
  | .call n ts xs => by
    simp only [lowerByteShifts]
    cases hf : tryLowerByteShift env n ts (lowerByteShiftsList env xs) with
    | none => simp [isPlainExpr, isPlainList_lowerByteShifts env xs]
    | some e' =>
      simp only [Option.getD_some]
      rw [tryLowerByteShift_plain hf, isPlainList_lowerByteShifts env xs]
      rfl
  | .letValue p v b => by
    cases p with
    | bind nm =>
      simp only [lowerByteShifts]
      set env' : ConstEnv :=
        match extractU32Const? env (lowerByteShifts env v) with
        | some k => (nm, k) :: envRemove [nm] env
        | none => envRemove [nm] env
      simp [isPlainExpr, isPlainExpr_lowerByteShifts env v, isPlainExpr_lowerByteShifts env' b]
    | literal _ | wildcard | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      simp [lowerByteShifts, isPlainExpr, isPlainExpr_lowerByteShifts env v,
        isPlainExpr_lowerByteShifts (envRemove (patBoundNames _) env) b]
  | .matchValue s arms => by
    simp [lowerByteShifts, isPlainExpr, isPlainExpr_lowerByteShifts env s,
      isPlainArms_lowerByteShifts env arms]

theorem isPlainList_lowerByteShifts (env : ConstEnv) :
    ∀ (xs : List Expr), isPlainList (lowerByteShiftsList env xs) = isPlainList xs
  | [] => rfl
  | x :: xs => by
    simp [lowerByteShiftsList, isPlainList,
      isPlainExpr_lowerByteShifts env x, isPlainList_lowerByteShifts env xs]

theorem isPlainArms_lowerByteShifts (env : ConstEnv) :
    ∀ (arms : List (Pat × Expr)), isPlainArms (lowerByteShiftsArms env arms) = isPlainArms arms
  | [] => rfl
  | (p, b) :: rest => by
    simp [lowerByteShiftsArms, isPlainArms,
      isPlainExpr_lowerByteShifts (envRemove (patBoundNames p) env) b,
      isPlainArms_lowerByteShifts env rest]

end

/-! ## Public Rewriter Entrypoints & Plainness Theorem -/

/-- Complete two-phase `UInt32` algebraic peephole rewriter over `Aiur.Generic.Expr Nat`. -/
def rewriteExpr (e : Expr) : Expr :=
  lowerByteShifts [] (fuseExpr [] e)

/-- Apply `rewriteExpr` to a lowered Formal Aiur function body. -/
def rewriteFn (f : Fn) : Fn :=
  { f with body := rewriteExpr f.body }

/-- Apply `rewriteFn` to every function in a lowered Formal Aiur program. -/
def rewriteProgram (prog : Aiur.Generic.Program Nat) : Aiur.Generic.Program Nat :=
  { prog with functions := prog.functions.map rewriteFn }

/-- **Exact plainness preservation**: `rewriteExpr` preserves `isPlainExpr` for
every expression `e` (both `true` and `false`!). -/
theorem isPlainExpr_rewriteExpr (e : Expr) : isPlainExpr (rewriteExpr e) = isPlainExpr e := by
  rw [rewriteExpr, isPlainExpr_lowerByteShifts, isPlainExpr_fuseExpr]

/-- Diagnostics summary counting fused `UInt32` primitives in a rewritten expression. -/
structure FusedCounts where
  add3 : Nat := 0
  rotr8 : Nat := 0
  rotr16 : Nat := 0
  xorRotr7 : Nat := 0
  xorRotr12 : Nat := 0
  fromBytes : Nat := 0
  remainingShr : Nat := 0
  remainingShl : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def FusedCounts.merge (a b : FusedCounts) : FusedCounts :=
  { add3 := a.add3 + b.add3
    rotr8 := a.rotr8 + b.rotr8
    rotr16 := a.rotr16 + b.rotr16
    xorRotr7 := a.xorRotr7 + b.xorRotr7
    xorRotr12 := a.xorRotr12 + b.xorRotr12
    fromBytes := a.fromBytes + b.fromBytes
    remainingShr := a.remainingShr + b.remainingShr
    remainingShl := a.remainingShl + b.remainingShl }

mutual

/-- Count fused `UInt32` calls and remaining general `u32_shr`/`u32_shl` calls in `e`. -/
def countFused : Expr → FusedCounts
  | .literal _ | .var _ | .global .. => {}
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => countFusedList xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x | .control _ x => countFused x
  | .binary _ l r => (countFused l).merge (countFused r)
  | .letValue _ v b => (countFused v).merge (countFused b)
  | .matchValue s arms => (countFused s).merge (countFusedArms arms)
  | .call nm _ xs =>
    let base : FusedCounts :=
      if nm == "UInt32::add3" then { add3 := 1 }
      else if nm == "UInt32::rotr8" then { rotr8 := 1 }
      else if nm == "UInt32::rotr16" then { rotr16 := 1 }
      else if nm == "UInt32::xor_rotr7" then { xorRotr7 := 1 }
      else if nm == "UInt32::xor_rotr12" then { xorRotr12 := 1 }
      else if nm == "UInt32::from_bytes" then { fromBytes := 1 }
      else if isShrName nm then { remainingShr := 1 }
      else if isShlName nm then { remainingShl := 1 }
      else {}
    base.merge (countFusedList xs)

def countFusedList : List Expr → FusedCounts
  | [] => {}
  | x :: xs => (countFused x).merge (countFusedList xs)

def countFusedArms : List (Pat × Expr) → FusedCounts
  | [] => {}
  | (_, b) :: rest => (countFused b).merge (countFusedArms rest)

end

/-! ## Pure `Nat` Bitwise & Byte-Packing Identities for `UInt32` -/

def rotr8Nat (x : Nat) : Nat := (x >>> 8) ||| ((x <<< 24) % U32.base)
def rotr16Nat (x : Nat) : Nat := (x >>> 16) ||| ((x <<< 16) % U32.base)
def rotr12Nat (x : Nat) : Nat := (x >>> 12) ||| ((x <<< 20) % U32.base)
def rotr7Nat (x : Nat) : Nat := (x >>> 7) ||| ((x <<< 25) % U32.base)

theorem add3_left_nat (a b c : Nat) :
    ((a + b) % U32.base + c) % U32.base = (a + b + c) % U32.base := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem add3_right_nat (a b c : Nat) :
    (a + (b + c) % U32.base) % U32.base = (a + b + c) % U32.base := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]

/-- Helper: bit `i` of `a + b * 2^m` splits cleanly at `m` whenever `a < 2^m`. -/
theorem testBit_add_mul_two_pow {a b m : Nat} (ha : a < 2 ^ m) (i : Nat) :
    (a + b * 2 ^ m).testBit i = if i < m then a.testBit i else b.testBit (i - m) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  by_cases hi : i < m
  · simp only [hi, ↓reduceIte]
    have hsplit : m = i + (m - i) := by omega
    have hpow : 2 ^ m = 2 ^ i * 2 ^ (m - i) := by rw [← Nat.pow_add, ← hsplit]
    have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
    have hdiv : (a + b * 2 ^ m) / 2 ^ i = a / 2 ^ i + b * 2 ^ (m - i) := by
      rw [hpow, show b * (2 ^ i * 2 ^ (m - i)) = (b * 2 ^ (m - i)) * 2 ^ i by ring]
      exact Nat.add_mul_div_right a (b * 2 ^ (m - i)) hpos
    rw [hdiv]
    have h2dvd : 2 ^ (m - i) = 2 * 2 ^ (m - i - 1) := by
      have hmi : m - i = (m - i - 1) + 1 := by omega
      conv_lhs => rw [hmi]
      rw [Nat.pow_succ, Nat.mul_comm]
    have hmod : (a / 2 ^ i + b * 2 ^ (m - i)) % 2 = (a / 2 ^ i) % 2 := by
      rw [h2dvd, show b * (2 * 2 ^ (m - i - 1)) = (b * 2 ^ (m - i - 1)) * 2 by ring,
        Nat.add_mul_mod_self_right]
    simp [hmod]
  · simp only [hi, ↓reduceIte]
    have hsplit : i = m + (i - m) := by omega
    have hpow : 2 ^ i = 2 ^ m * 2 ^ (i - m) := by rw [← Nat.pow_add, ← hsplit]
    have hdiv1 : (a + b * 2 ^ m) / 2 ^ m = b := by
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [hpow, ← Nat.div_div_eq_div_mul, hdiv1]

/-- Disjoint bit ranges combine identically under bitwise OR and addition. -/
theorem lor_eq_add_mul_two_pow {a b m : Nat} (ha : a < 2 ^ m) :
    a ||| (b * 2 ^ m) = a + b * 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_add_mul_two_pow ha]
  have hbm : (b * 2 ^ m).testBit i = if i < m then false else b.testBit (i - m) := by
    simpa using testBit_add_mul_two_pow (a := 0) (b := b) (m := m) (Nat.two_pow_pos m) i
  rw [hbm]
  by_cases hi : i < m
  · simp [hi]
  · simp only [hi, ↓reduceIte]
    have hlt : a < 2 ^ i := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
    have ha0 : a.testBit i = false := Nat.testBit_lt_two_pow hlt
    simp [ha0]

/-- Bitwise XOR distributes across disjoint bit ranges separated at `2^m`. -/
theorem xor_add_mul_two_pow {a b c d m : Nat} (ha : a < 2 ^ m) (hc : c < 2 ^ m) :
    Nat.xor (a + b * 2 ^ m) (c + d * 2 ^ m) = Nat.xor a c + Nat.xor b d * 2 ^ m := by
  have hxlt : Nat.xor a c < 2 ^ m := Nat.xor_lt_two_pow ha hc
  apply Nat.eq_of_testBit_eq
  intro i
  change ((a + b * 2 ^ m) ^^^ (c + d * 2 ^ m)).testBit i = _
  rw [Nat.testBit_xor, testBit_add_mul_two_pow ha, testBit_add_mul_two_pow hc,
    testBit_add_mul_two_pow hxlt]
  by_cases hi : i < m
  · simp only [hi, ↓reduceIte]
    exact (Nat.testBit_xor a c i).symm
  · simp only [hi, ↓reduceIte]
    exact (Nat.testBit_xor b d (i - m)).symm

theorem xor_pack {a0 a1 a2 a3 b0 b1 b2 b3 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (_ha3 : a3 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (_hb3 : b3 < 256) :
    Nat.xor (U32.pack a0 a1 a2 a3) (U32.pack b0 b1 b2 b3) =
      U32.pack (Nat.xor a0 b0) (Nat.xor a1 b1) (Nat.xor a2 b2) (Nat.xor a3 b3) := by
  have step : ∀ {x0 y0 x1 y1 : Nat}, x0 < 256 → y0 < 256 →
      Nat.xor (x0 + 256 * x1) (y0 + 256 * y1) = Nat.xor x0 y0 + 256 * Nat.xor x1 y1 := by
    intro x0 y0 x1 y1 hx0 hy0
    have h := xor_add_mul_two_pow (a := x0) (b := x1) (c := y0) (d := y1) (m := 8) hx0 hy0
    simpa [Nat.mul_comm] using h
  have hrw : ∀ x0 x1 x2 x3 : Nat,
      U32.pack x0 x1 x2 x3 = x0 + 256 * (x1 + 256 * (x2 + 256 * x3)) := by
    intro x0 x1 x2 x3; unfold U32.pack; ring
  rw [hrw a0 a1 a2 a3, hrw b0 b1 b2 b3, hrw,
    step ha0 hb0, step ha1 hb1, step ha2 hb2]

theorem shr8_pack {b0 b1 b2 b3 : Nat} (h0 : b0 < 256) (_h1 : b1 < 256)
    (_h2 : b2 < 256) (_h3 : b3 < 256) :
    U32.pack b0 b1 b2 b3 >>> 8 = U32.pack b1 b2 b3 0 := by
  rw [Nat.shiftRight_eq_div_pow]; unfold U32.pack; omega

theorem shr16_pack {b0 b1 b2 b3 : Nat} (h0 : b0 < 256) (h1 : b1 < 256)
    (_h2 : b2 < 256) (_h3 : b3 < 256) :
    U32.pack b0 b1 b2 b3 >>> 16 = U32.pack b2 b3 0 0 := by
  rw [Nat.shiftRight_eq_div_pow]; unfold U32.pack; omega

theorem shr24_pack {b0 b1 b2 b3 : Nat} (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (_h3 : b3 < 256) :
    U32.pack b0 b1 b2 b3 >>> 24 = U32.pack b3 0 0 0 := by
  rw [Nat.shiftRight_eq_div_pow]; unfold U32.pack; omega

theorem shl8_pack {b0 b1 b2 b3 : Nat} (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (_h3 : b3 < 256) :
    (U32.pack b0 b1 b2 b3 <<< 8) % U32.base = U32.pack 0 b0 b1 b2 := by
  rw [Nat.shiftLeft_eq]; unfold U32.pack U32.base; omega

theorem shl16_pack {b0 b1 b2 b3 : Nat} (h0 : b0 < 256) (h1 : b1 < 256)
    (_h2 : b2 < 256) (_h3 : b3 < 256) :
    (U32.pack b0 b1 b2 b3 <<< 16) % U32.base = U32.pack 0 0 b0 b1 := by
  rw [Nat.shiftLeft_eq]; unfold U32.pack U32.base; omega

theorem shl24_pack {b0 b1 b2 b3 : Nat} (h0 : b0 < 256) (_h1 : b1 < 256)
    (_h2 : b2 < 256) (_h3 : b3 < 256) :
    (U32.pack b0 b1 b2 b3 <<< 24) % U32.base = U32.pack 0 0 0 b0 := by
  rw [Nat.shiftLeft_eq]; unfold U32.pack U32.base; omega

theorem rotr8_pack {b0 b1 b2 b3 : Nat} (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (h3 : b3 < 256) :
    rotr8Nat (U32.pack b0 b1 b2 b3) = U32.pack b1 b2 b3 b0 := by
  unfold rotr8Nat
  rw [shr8_pack h0 h1 h2 h3, shl24_pack h0 h1 h2 h3]
  have ha : U32.pack b1 b2 b3 0 < 2 ^ 24 := by unfold U32.pack; omega
  have hb : U32.pack 0 0 0 b0 = b0 * 2 ^ 24 := by unfold U32.pack; ring
  rw [hb, lor_eq_add_mul_two_pow ha]
  unfold U32.pack; ring

theorem rotr16_pack {b0 b1 b2 b3 : Nat} (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (h3 : b3 < 256) :
    rotr16Nat (U32.pack b0 b1 b2 b3) = U32.pack b2 b3 b0 b1 := by
  unfold rotr16Nat
  rw [shr16_pack h0 h1 h2 h3, shl16_pack h0 h1 h2 h3]
  have ha : U32.pack b2 b3 0 0 < 2 ^ 16 := by unfold U32.pack; omega
  have hb : U32.pack 0 0 b0 b1 = (b0 + 256 * b1) * 2 ^ 16 := by unfold U32.pack; ring
  rw [hb, lor_eq_add_mul_two_pow ha]
  unfold U32.pack; ring

theorem rotr12_pack {x0 x1 x2 x3 : Nat} (h0 : x0 < 256) (h1 : x1 < 256)
    (h2 : x2 < 256) (h3 : x3 < 256) :
    rotr12Nat (U32.pack x0 x1 x2 x3) =
      U32.pack
        (x1 / 16 + (x2 % 16) * 16)
        (x2 / 16 + (x3 % 16) * 16)
        (x3 / 16 + (x0 % 16) * 16)
        (x0 / 16 + (x1 % 16) * 16) := by
  unfold rotr12Nat
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  set x := U32.pack x0 x1 x2 x3
  have hx : x < U32.base := U32.pack_lt h0 h1 h2 h3
  have ha : x / 2 ^ 12 < 2 ^ 20 := by unfold U32.base at hx; omega
  have hshl : (x * 2 ^ 20) % U32.base = (x % 2 ^ 12) * 2 ^ 20 := by
    unfold U32.base; omega
  rw [hshl, lor_eq_add_mul_two_pow ha]
  unfold x U32.pack
  omega

theorem rotr7_pack {x0 x1 x2 x3 : Nat} (h0 : x0 < 256) (h1 : x1 < 256)
    (h2 : x2 < 256) (h3 : x3 < 256) :
    rotr7Nat (U32.pack x0 x1 x2 x3) =
      U32.pack
        (x0 / 128 + (x1 % 128) * 2)
        (x1 / 128 + (x2 % 128) * 2)
        (x2 / 128 + (x3 % 128) * 2)
        (x3 / 128 + (x0 % 128) * 2) := by
  unfold rotr7Nat
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  set x := U32.pack x0 x1 x2 x3
  have hx : x < U32.base := U32.pack_lt h0 h1 h2 h3
  have ha : x / 2 ^ 7 < 2 ^ 25 := by unfold U32.base at hx; omega
  have hshl : (x * 2 ^ 25) % U32.base = (x % 2 ^ 7) * 2 ^ 25 := by
    unfold U32.base; omega
  rw [hshl, lor_eq_add_mul_two_pow ha]
  unfold x U32.pack
  omega

theorem xor_rotr12_pack {a0 a1 a2 a3 b0 b1 b2 b3 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256) :
    let x0 := Nat.xor a0 b0
    let x1 := Nat.xor a1 b1
    let x2 := Nat.xor a2 b2
    let x3 := Nat.xor a3 b3
    rotr12Nat (Nat.xor (U32.pack a0 a1 a2 a3) (U32.pack b0 b1 b2 b3)) =
      U32.pack
        (x1 / 16 + (x2 % 16) * 16)
        (x2 / 16 + (x3 % 16) * 16)
        (x3 / 16 + (x0 % 16) * 16)
        (x0 / 16 + (x1 % 16) * 16) := by
  dsimp only
  rw [xor_pack ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  exact rotr12_pack
    (U8Facts.xor_lt_256 ha0 hb0) (U8Facts.xor_lt_256 ha1 hb1)
    (U8Facts.xor_lt_256 ha2 hb2) (U8Facts.xor_lt_256 ha3 hb3)

theorem xor_rotr7_pack {a0 a1 a2 a3 b0 b1 b2 b3 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256) :
    let x0 := Nat.xor a0 b0
    let x1 := Nat.xor a1 b1
    let x2 := Nat.xor a2 b2
    let x3 := Nat.xor a3 b3
    rotr7Nat (Nat.xor (U32.pack a0 a1 a2 a3) (U32.pack b0 b1 b2 b3)) =
      U32.pack
        (x0 / 128 + (x1 % 128) * 2)
        (x1 / 128 + (x2 % 128) * 2)
        (x2 / 128 + (x3 % 128) * 2)
        (x3 / 128 + (x0 % 128) * 2) := by
  dsimp only
  rw [xor_pack ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  exact rotr7_pack
    (U8Facts.xor_lt_256 ha0 hb0) (U8Facts.xor_lt_256 ha1 hb1)
    (U8Facts.xor_lt_256 ha2 hb2) (U8Facts.xor_lt_256 ha3 hb3)

/-! ## Operational `UInt32` Contracts & `EvalExpr` Soundness Lemmas -/

section Soundness

variable {F : Type} [Field F] [DecidableEq F]

/-- Checked 32-bit word value: 4 little-endian byte fields `< 256` packing to `n`. -/
def isU32Val (n : Nat) (v : SourceValue F) : Prop :=
  ∃ b0 b1 b2 b3 : Nat,
    b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
    n = U32.pack b0 b1 b2 b3 ∧
    v = .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]

omit [DecidableEq F] in
theorem isU32Val_lt {n : Nat} {v : SourceValue F} (h : isU32Val n v) : n < U32.base := by
  obtain ⟨_, _, _, _, h0, h1, h2, h3, rfl, _⟩ := h
  exact U32.pack_lt h0 h1 h2 h3

omit [DecidableEq F] in
theorem isU32Val_unique (comp : U32.Compatible F) {n m : Nat} {v : SourceValue F}
    (hn : isU32Val n v) (hm : isU32Val m v) : n = m := by
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3, rfl, rfl⟩ := hn
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, hv⟩ := hm
  simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq, and_true] at hv
  have injByte : ∀ {x y : Nat}, x < 256 → y < 256 → (x : F) = (y : F) → x = y := by
    intro x y hx hy heq
    exact comp (by unfold U32.base; change x < 3 * 4294967296; omega)
      (by unfold U32.base; change y < 3 * 4294967296; omega) heq
  rw [injByte ha0 hb0 hv.1, injByte ha1 hb1 hv.2.1,
    injByte ha2 hb2 hv.2.2.1, injByte ha3 hb3 hv.2.2.2]

omit [DecidableEq F] in
theorem isU32Val_val_unique {n : Nat} {v1 v2 : SourceValue F}
    (h1 : isU32Val n v1) (h2 : isU32Val n v2) : v1 = v2 := by
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3, rfl, rfl⟩ := h1
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hpack, rfl⟩ := h2
  unfold U32.pack at hpack
  have e0 : a0 = b0 := by omega
  have e1 : a1 = b1 := by omega
  have e2 : a2 = b2 := by omega
  have e3 : a3 = b3 := by omega
  subst e0; subst e1; subst e2; subst e3; rfl

/-- Operational contracts over `Aiur.Generic.SourceSemantics.EvalFn` for the
`Aiur.Library.U32` primitives and lowered `u32_shr`/`u32_shl` helpers. -/
structure U32Contracts (world : World F) : Prop where
  add : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
    EvalFn world "UInt32::add" [wa, wb] h r h' →
    isU32Val ((a + b) % U32.base) r ∧ h' = h
  add3 : ∀ a b c wa wb wc h r h', isU32Val a wa → isU32Val b wb → isU32Val c wc →
    EvalFn world "UInt32::add3" [wa, wb, wc] h r h' →
    isU32Val ((a + b + c) % U32.base) r ∧ h' = h
  xor : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
    EvalFn world "UInt32::xor" [wa, wb] h r h' →
    isU32Val (Nat.xor a b) r ∧ h' = h
  or : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
    EvalFn world "UInt32::or" [wa, wb] h r h' →
    isU32Val (a ||| b) r ∧ h' = h
  rotr8 : ∀ a wa h r h', isU32Val a wa →
    EvalFn world "UInt32::rotr8" [wa] h r h' →
    isU32Val (rotr8Nat a) r ∧ h' = h
  rotr16 : ∀ a wa h r h', isU32Val a wa →
    EvalFn world "UInt32::rotr16" [wa] h r h' →
    isU32Val (rotr16Nat a) r ∧ h' = h
  xor_rotr7 : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
    EvalFn world "UInt32::xor_rotr7" [wa, wb] h r h' →
    isU32Val (rotr7Nat (Nat.xor a b)) r ∧ h' = h
  xor_rotr12 : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
    EvalFn world "UInt32::xor_rotr12" [wa, wb] h r h' →
    isU32Val (rotr12Nat (Nat.xor a b)) r ∧ h' = h
  to_bytes : ∀ a wa h r h', isU32Val a wa →
    EvalFn world "UInt32::to_bytes" [wa] h r h' →
    r = wa ∧ h' = h
  from_bytes : ∀ a wa h r h', isU32Val a wa →
    EvalFn world "UInt32::from_bytes" [wa] h r h' →
    r = wa ∧ h' = h
  u8_from_fields : ∀ v1 v2 h r h',
    EvalFn world "UInt8::from_fields" [v1, v2] h r h' →
    h' = h ∧ ∃ a b : Nat, a < 256 ∧ b < 256 ∧
      v1 = .field (a : F) ∧ v2 = .field (b : F) ∧ r = .tuple [v1, v2]
  shr : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
    EvalFn world (qualified "u32_shr") [wa, wb] h r h' →
    isU32Val (a >>> (b % 32)) r ∧ h' = h
  shl : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
    EvalFn world (qualified "u32_shl") [wa, wb] h r h' →
    isU32Val ((a <<< (b % 32)) % U32.base) r ∧ h' = h

private theorem evalExpr_call3_inv {world : World F} {locals : Environment F Nat}
    {name : String} {a b c : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.call name (some []) [a, b, c]) h r h') :
    ∃ va vb vc h1 h2 hm,
      EvalExpr world [] locals a h va h1 ∧
      EvalExpr world [] locals b h1 vb h2 ∧
      EvalExpr world [] locals c h2 vc hm ∧
      EvalFn world name [va, vb, vc] hm r h' := by
  obtain ⟨vs, hm, hargs, hcal⟩ := evalExpr_call_inv ev
  cases hargs with
  | cons ha ht1 =>
    cases ht1 with
    | cons hb ht2 =>
      cases ht2 with
      | cons hc ht3 =>
        cases ht3
        exact ⟨_, _, _, _, _, _, ha, hb, hc, hcal⟩

private theorem evalExpr_array4_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e0 e1 e2 e3 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.array [e0, e1, e2, e3]) h r h') :
    ∃ v0 v1 v2 v3 h1 h2 h3,
      EvalExpr world types locals e0 h v0 h1 ∧
      EvalExpr world types locals e1 h1 v1 h2 ∧
      EvalExpr world types locals e2 h2 v2 h3 ∧
      EvalExpr world types locals e3 h3 v3 h' ∧
      r = .tuple [v0, v1, v2, v3] := by
  cases ev with
  | array hargs =>
    cases hargs with | cons h0 t0 =>
    cases t0 with | cons h1 t1 =>
    cases t1 with | cons h2 t2 =>
    cases t2 with | cons h3 t3 =>
    cases t3
    exact ⟨_, _, _, _, _, _, _, h0, h1, h2, h3, rfl⟩

/-! ### `EvalExpr` Soundness of Every Fused `UInt32` Peephole -/

/-- **Soundness of left-nested `add3` fusion**:
`UInt32::add3(a, b, c)` evaluates to the exact same `UInt32` value as
`UInt32::add(UInt32::add(a, b), c)`. -/
theorem evalExpr_add3_left_sound {world : World F} (C : U32Contracts world)
    {locals : Environment F Nat} {ea eb ec : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F} {na nb nc : Nat}
    (ev : EvalExpr world [] locals (.call "UInt32::add3" (some []) [ea, eb, ec]) h r h')
    (ha : ∀ v h1, EvalExpr world [] locals ea h v h1 → isU32Val na v ∧ h1 = h)
    (hb : ∀ v h1, EvalExpr world [] locals eb h v h1 → isU32Val nb v ∧ h1 = h)
    (hc : ∀ v h1, EvalExpr world [] locals ec h v h1 → isU32Val nc v ∧ h1 = h) :
    isU32Val (((na + nb) % U32.base + nc) % U32.base) r ∧ h' = h := by
  obtain ⟨va, vb, vc, h1, h2, hm, eva, evb, evc, hfn⟩ := evalExpr_call3_inv ev
  obtain ⟨hva, rfl⟩ := ha va h1 eva
  obtain ⟨hvb, rfl⟩ := hb vb h2 evb
  obtain ⟨hvc, rfl⟩ := hc vc hm evc
  obtain ⟨hr, rfl⟩ := C.add3 na nb nc va vb vc _ r h' hva hvb hvc hfn
  rw [add3_left_nat]
  exact ⟨hr, rfl⟩

/-- **Soundness of right-nested `add3` fusion**:
`UInt32::add3(a, b, c)` evaluates to the exact same `UInt32` value as
`UInt32::add(a, UInt32::add(b, c))`. -/
theorem evalExpr_add3_right_sound {world : World F} (C : U32Contracts world)
    {locals : Environment F Nat} {ea eb ec : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F} {na nb nc : Nat}
    (ev : EvalExpr world [] locals (.call "UInt32::add3" (some []) [ea, eb, ec]) h r h')
    (ha : ∀ v h1, EvalExpr world [] locals ea h v h1 → isU32Val na v ∧ h1 = h)
    (hb : ∀ v h1, EvalExpr world [] locals eb h v h1 → isU32Val nb v ∧ h1 = h)
    (hc : ∀ v h1, EvalExpr world [] locals ec h v h1 → isU32Val nc v ∧ h1 = h) :
    isU32Val ((na + (nb + nc) % U32.base) % U32.base) r ∧ h' = h := by
  obtain ⟨va, vb, vc, h1, h2, hm, eva, evb, evc, hfn⟩ := evalExpr_call3_inv ev
  obtain ⟨hva, rfl⟩ := ha va h1 eva
  obtain ⟨hvb, rfl⟩ := hb vb h2 evb
  obtain ⟨hvc, rfl⟩ := hc vc hm evc
  obtain ⟨hr, rfl⟩ := C.add3 na nb nc va vb vc _ r h' hva hvb hvc hfn
  rw [add3_right_nat]
  exact ⟨hr, rfl⟩

/-- **Soundness of `rotr16` fusion**:
`UInt32::rotr16(x)` evaluates to `(nx >>> 16) ||| ((nx <<< 16) % 2^32)`, matching
`UInt32::or(u32_shr(x, 16), u32_shl(x, 16))`. -/
theorem evalExpr_rotr16_sound {world : World F} (C : U32Contracts world)
    {locals : Environment F Nat} {ex : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F} {nx : Nat}
    (ev : EvalExpr world [] locals (.call "UInt32::rotr16" (some []) [ex]) h r h')
    (hx : ∀ v h1, EvalExpr world [] locals ex h v h1 → isU32Val nx v ∧ h1 = h) :
    isU32Val ((nx >>> 16) ||| ((nx <<< 16) % U32.base)) r ∧ h' = h := by
  obtain ⟨vx, hm, evx, hfn⟩ := evalExpr_call1_inv ev
  obtain ⟨hvx, rfl⟩ := hx vx hm evx
  exact C.rotr16 nx vx _ r h' hvx hfn

/-- **Soundness of `rotr8` fusion**:
`UInt32::rotr8(x)` evaluates to `(nx >>> 8) ||| ((nx <<< 24) % 2^32)`, matching
`UInt32::or(u32_shr(x, 8), u32_shl(x, 24))`. -/
theorem evalExpr_rotr8_sound {world : World F} (C : U32Contracts world)
    {locals : Environment F Nat} {ex : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F} {nx : Nat}
    (ev : EvalExpr world [] locals (.call "UInt32::rotr8" (some []) [ex]) h r h')
    (hx : ∀ v h1, EvalExpr world [] locals ex h v h1 → isU32Val nx v ∧ h1 = h) :
    isU32Val ((nx >>> 8) ||| ((nx <<< 24) % U32.base)) r ∧ h' = h := by
  obtain ⟨vx, hm, evx, hfn⟩ := evalExpr_call1_inv ev
  obtain ⟨hvx, rfl⟩ := hx vx hm evx
  exact C.rotr8 nx vx _ r h' hvx hfn

/-- **Soundness of `xor_rotr12` fusion**:
`UInt32::xor_rotr12(a, b)` evaluates to
`((na ^^^ nb) >>> 12) ||| (((na ^^^ nb) <<< 20) % 2^32)`, matching
`UInt32::or(u32_shr(UInt32::xor(a, b), 12), u32_shl(UInt32::xor(a, b), 20))`. -/
theorem evalExpr_xor_rotr12_sound {world : World F} (C : U32Contracts world)
    {locals : Environment F Nat} {ea eb : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F} {na nb : Nat}
    (ev : EvalExpr world [] locals (.call "UInt32::xor_rotr12" (some []) [ea, eb]) h r h')
    (ha : ∀ v h1, EvalExpr world [] locals ea h v h1 → isU32Val na v ∧ h1 = h)
    (hb : ∀ v h1, EvalExpr world [] locals eb h v h1 → isU32Val nb v ∧ h1 = h) :
    isU32Val ((Nat.xor na nb >>> 12) ||| ((Nat.xor na nb <<< 20) % U32.base)) r ∧ h' = h := by
  obtain ⟨va, vb, h1, hm, eva, evb, hfn⟩ := evalExpr_call2_inv ev
  obtain ⟨hva, rfl⟩ := ha va h1 eva
  obtain ⟨hvb, rfl⟩ := hb vb hm evb
  exact C.xor_rotr12 na nb va vb _ r h' hva hvb hfn

/-- **Soundness of `xor_rotr7` fusion**:
`UInt32::xor_rotr7(a, b)` evaluates to
`((na ^^^ nb) >>> 7) ||| (((na ^^^ nb) <<< 25) % 2^32)`, matching
`UInt32::or(u32_shr(UInt32::xor(a, b), 7), u32_shl(UInt32::xor(a, b), 25))`. -/
theorem evalExpr_xor_rotr7_sound {world : World F} (C : U32Contracts world)
    {locals : Environment F Nat} {ea eb : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F} {na nb : Nat}
    (ev : EvalExpr world [] locals (.call "UInt32::xor_rotr7" (some []) [ea, eb]) h r h')
    (ha : ∀ v h1, EvalExpr world [] locals ea h v h1 → isU32Val na v ∧ h1 = h)
    (hb : ∀ v h1, EvalExpr world [] locals eb h v h1 → isU32Val nb v ∧ h1 = h) :
    isU32Val ((Nat.xor na nb >>> 7) ||| ((Nat.xor na nb <<< 25) % U32.base)) r ∧ h' = h := by
  obtain ⟨va, vb, h1, hm, eva, evb, hfn⟩ := evalExpr_call2_inv ev
  obtain ⟨hva, rfl⟩ := ha va h1 eva
  obtain ⟨hvb, rfl⟩ := hb vb hm evb
  exact C.xor_rotr7 na nb va vb _ r h' hva hvb hfn

private def pickByte (b0 b1 b2 b3 : Nat) : Option Nat → Nat
  | some 0 => b0
  | some 1 => b1
  | some 2 => b2
  | some 3 => b3
  | _ => 0

/-- Helper inverting a 4-slot `byteShuffleE` expression specialized to field `F`. -/
private theorem evalExpr_byteShuffleE_inv {world : World F} (C : U32Contracts world)
    (comp : U32.Compatible F) {locals : Environment F Nat} {ex : Aiur.Generic.Expr F}
    {s0 s1 s2 s3 : Option Nat} {h h' : Heap F} {r : SourceValue F} {nx : Nat}
    (hx : ∀ v h1, EvalExpr world [] locals ex h v h1 → isU32Val nx v ∧ h1 = h)
    (ev : EvalExpr world [] locals
      (.letValue (.bind "__peep_b") (.call "UInt32::to_bytes" (some []) [ex])
        (.letValue (.tuple [.bind "__peep_z", .wildcard])
          (.call "UInt8::from_fields" (some []) [.literal (0 : F), .literal (0 : F)])
          (.call "UInt32::from_bytes" (some [])
            [.array [
              match s0 with | some idx => .index (.var "__peep_b") idx | none => .var "__peep_z",
              match s1 with | some idx => .index (.var "__peep_b") idx | none => .var "__peep_z",
              match s2 with | some idx => .index (.var "__peep_b") idx | none => .var "__peep_z",
              match s3 with | some idx => .index (.var "__peep_b") idx | none => .var "__peep_z"]])))
      h r h') :
    ∃ b0 b1 b2 b3 : Nat,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      nx = U32.pack b0 b1 b2 b3 ∧
      (s0.all (· < 4) = true → s1.all (· < 4) = true → s2.all (· < 4) = true → s3.all (· < 4) = true →
        isU32Val (U32.pack (pickByte b0 b1 b2 b3 s0) (pickByte b0 b1 b2 b3 s1)
          (pickByte b0 b1 b2 b3 s2) (pickByte b0 b1 b2 b3 s3)) r ∧ h' = h) := by
  obtain ⟨vb, h1, evTb, evRest1⟩ := evalExpr_let_bind_inv ev
  obtain ⟨vx, h0', evx, hfnTb⟩ := evalExpr_call1_inv evTb
  obtain ⟨hvx, rfl⟩ := hx vx h0' evx
  obtain ⟨rfl, rfl⟩ := C.to_bytes nx vx _ vb h1 hvx hfnTb
  obtain ⟨vz, vw, h2, evZ, evRest2⟩ := evalExpr_let_tuple2_wild_inv evRest1
  obtain ⟨v0, v1, hz1, hz2, evL0, evL1, hfnZ⟩ := evalExpr_call2_inv evZ
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evL0
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evL1
  obtain ⟨rfl, a0, a1, _ha0, _ha1, hfa0, _hfa1, htupZ⟩ := C.u8_from_fields _ _ _ _ _ hfnZ
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupZ
  obtain ⟨rfl, _⟩ := htupZ
  have ha0Zero : a0 = 0 := by
    have heq : ((0 : Nat) : F) = (a0 : F) := by simpa [Value.field.injEq] using hfa0
    exact (comp (by unfold U32.base; change 0 < 3 * 4294967296; omega)
      (by unfold U32.base; change a0 < 3 * 4294967296; omega) heq).symm
  subst ha0Zero
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hnx, rfl⟩ := hvx
  obtain ⟨varr, h3, evArr, hfnFb⟩ := evalExpr_call1_inv evRest2
  obtain ⟨w0, w1, w2, w3, ha1, ha2, ha3, ev0, ev1, ev2, ev3, rfl⟩ := evalExpr_array4_inv evArr
  refine ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hnx, ?_⟩
  intro hs0 hs1 hs2 hs3
  have evalSlot : ∀ (s : Option Nat) (hf : Heap F) (w : SourceValue F) (hf' : Heap F),
      EvalExpr world []
        (("__peep_z", Value.field (0 : F)) ::
          ("__peep_b", Value.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]) ::
          locals)
        (match s with | some idx => .index (.var "__peep_b") idx | none => .var "__peep_z")
        hf w hf' →
      s.all (· < 4) = true →
      w = .field ((pickByte b0 b1 b2 b3 s : Nat) : F) ∧ hf' = hf := by
    intro s hf w hf' evs hi
    cases s with
    | none =>
      obtain ⟨hlook, rfl⟩ := evalExpr_var_inv evs
      simp at hlook
      exact ⟨by simpa [pickByte, Nat.cast_zero] using hlook.symm, rfl⟩
    | some idx =>
      obtain ⟨vv, evv, hproj⟩ := evalExpr_index_inv evs
      obtain ⟨hlook, rfl⟩ := evalExpr_var_inv evv
      simp at hlook
      subst hlook
      simp only [Option.all_some, decide_eq_true_eq] at hi
      rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3) with rfl | rfl | rfl | rfl <;>
        · simp [Aiur.projectValue] at hproj
          exact ⟨by simpa [pickByte] using hproj.symm, rfl⟩
  obtain ⟨rfl, rfl⟩ := evalSlot s0 _ w0 ha1 ev0 hs0
  obtain ⟨rfl, rfl⟩ := evalSlot s1 _ w1 ha2 ev1 hs1
  obtain ⟨rfl, rfl⟩ := evalSlot s2 _ w2 ha3 ev2 hs2
  obtain ⟨rfl, rfl⟩ := evalSlot s3 _ w3 h3 ev3 hs3
  have pickLt : ∀ (s : Option Nat), pickByte b0 b1 b2 b3 s < 256 := by
    intro s
    cases s with
    | none => simp [pickByte]
    | some idx => rcases idx with _ | _ | _ | _ | _ <;> simp [pickByte] <;> omega
  have hU32Arr : isU32Val
      (U32.pack (pickByte b0 b1 b2 b3 s0) (pickByte b0 b1 b2 b3 s1)
        (pickByte b0 b1 b2 b3 s2) (pickByte b0 b1 b2 b3 s3))
      (.tuple [
        .field ((pickByte b0 b1 b2 b3 s0 : Nat) : F),
        .field ((pickByte b0 b1 b2 b3 s1 : Nat) : F),
        .field ((pickByte b0 b1 b2 b3 s2 : Nat) : F),
        .field ((pickByte b0 b1 b2 b3 s3 : Nat) : F)]) :=
    ⟨_, _, _, _, pickLt s0, pickLt s1, pickLt s2, pickLt s3, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := C.from_bytes _ _ _ _ _ hU32Arr hfnFb
  exact ⟨hU32Arr, rfl⟩

/-- **Soundness of constant byte-shuffle right shifts** (`k ∈ {0, 8, 16, 24}`):
evaluating `byteShrE k x` (mapped into field `F`) yields `isU32Val (nx >>> (k % 32)) r`
with unchanged heap. -/
theorem evalExpr_byteShr_sound {world : World F} (C : U32Contracts world)
    (comp : U32.Compatible F) {locals : Environment F Nat} {x e' : Expr} {k : Nat}
    {h h' : Heap F} {r : SourceValue F} {nx : Nat}
    (hshr : byteShrE k x = some e')
    (hx : ∀ v h1, EvalExpr world [] locals (x.map Nat.cast) h v h1 → isU32Val nx v ∧ h1 = h)
    (ev : EvalExpr world [] locals (e'.map Nat.cast) h r h') :
    isU32Val (nx >>> (k % 32)) r ∧ h' = h := by
  unfold byteShrE at hshr
  split at hshr
  · next h0 =>
    simp only [Option.some.injEq] at hshr; subst hshr
    rw [h0, Nat.shiftRight_zero]
    exact hx r h' ev
  · next h8 =>
    simp only [Option.some.injEq] at hshr; subst hshr
    rw [h8]
    simp only [byteShuffleE, letE, callE, litE, vE, List.map, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Nat.cast_zero] at ev
    obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, hres⟩ :=
      evalExpr_byteShuffleE_inv C comp (s0 := some 1) (s1 := some 2) (s2 := some 3) (s3 := none) hx ev
    obtain ⟨hu, rfl⟩ := hres rfl rfl rfl rfl
    rw [shr8_pack hb0 hb1 hb2 hb3]
    exact ⟨hu, rfl⟩
  · next h16 =>
    simp only [Option.some.injEq] at hshr; subst hshr
    rw [h16]
    simp only [byteShuffleE, letE, callE, litE, vE, List.map, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Nat.cast_zero] at ev
    obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, hres⟩ :=
      evalExpr_byteShuffleE_inv C comp (s0 := some 2) (s1 := some 3) (s2 := none) (s3 := none) hx ev
    obtain ⟨hu, rfl⟩ := hres rfl rfl rfl rfl
    rw [shr16_pack hb0 hb1 hb2 hb3]
    exact ⟨hu, rfl⟩
  · next h24 =>
    simp only [Option.some.injEq] at hshr; subst hshr
    rw [h24]
    simp only [byteShuffleE, letE, callE, litE, vE, List.map, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Nat.cast_zero] at ev
    obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, hres⟩ :=
      evalExpr_byteShuffleE_inv C comp (s0 := some 3) (s1 := none) (s2 := none) (s3 := none) hx ev
    obtain ⟨hu, rfl⟩ := hres rfl rfl rfl rfl
    rw [shr24_pack hb0 hb1 hb2 hb3]
    exact ⟨hu, rfl⟩
  · cases hshr

/-- **Soundness of constant byte-shuffle left shifts** (`k ∈ {0, 8, 16, 24}`):
evaluating `byteShlE k x` (mapped into field `F`) yields
`isU32Val ((nx <<< (k % 32)) % 2^32) r` with unchanged heap. -/
theorem evalExpr_byteShl_sound {world : World F} (C : U32Contracts world)
    (comp : U32.Compatible F) {locals : Environment F Nat} {x e' : Expr} {k : Nat}
    {h h' : Heap F} {r : SourceValue F} {nx : Nat}
    (hshl : byteShlE k x = some e')
    (hx : ∀ v h1, EvalExpr world [] locals (x.map Nat.cast) h v h1 → isU32Val nx v ∧ h1 = h)
    (ev : EvalExpr world [] locals (e'.map Nat.cast) h r h') :
    isU32Val ((nx <<< (k % 32)) % U32.base) r ∧ h' = h := by
  unfold byteShlE at hshl
  split at hshl
  · next h0 =>
    simp only [Option.some.injEq] at hshl; subst hshl
    obtain ⟨hu, rfl⟩ := hx r h' ev
    rw [h0, Nat.shiftLeft_zero, Nat.mod_eq_of_lt (isU32Val_lt hu)]
    exact ⟨hu, rfl⟩
  · next h8 =>
    simp only [Option.some.injEq] at hshl; subst hshl
    rw [h8]
    simp only [byteShuffleE, letE, callE, litE, vE, List.map, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Nat.cast_zero] at ev
    obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, hres⟩ :=
      evalExpr_byteShuffleE_inv C comp (s0 := none) (s1 := some 0) (s2 := some 1) (s3 := some 2) hx ev
    obtain ⟨hu, rfl⟩ := hres rfl rfl rfl rfl
    rw [shl8_pack hb0 hb1 hb2 hb3]
    exact ⟨hu, rfl⟩
  · next h16 =>
    simp only [Option.some.injEq] at hshl; subst hshl
    rw [h16]
    simp only [byteShuffleE, letE, callE, litE, vE, List.map, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Nat.cast_zero] at ev
    obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, hres⟩ :=
      evalExpr_byteShuffleE_inv C comp (s0 := none) (s1 := none) (s2 := some 0) (s3 := some 1) hx ev
    obtain ⟨hu, rfl⟩ := hres rfl rfl rfl rfl
    rw [shl16_pack hb0 hb1 hb2 hb3]
    exact ⟨hu, rfl⟩
  · next h24 =>
    simp only [Option.some.injEq] at hshl; subst hshl
    rw [h24]
    simp only [byteShuffleE, letE, callE, litE, vE, List.map, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Nat.cast_zero] at ev
    obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, hres⟩ :=
      evalExpr_byteShuffleE_inv C comp (s0 := none) (s1 := none) (s2 := none) (s3 := some 0) hx ev
    obtain ⟨hu, rfl⟩ := hres rfl rfl rfl rfl
    rw [shl24_pack hb0 hb1 hb2 hb3]
    exact ⟨hu, rfl⟩
  · cases hshl

/-! ### Library Body Bridge Theorems (`Aiur.Library.U32` → `U32Contracts`) -/

/-- Exact body of `UInt32::rotr8(a)` from `Aiur.Library.U32`. -/
def u32Rotr8Body : Aiur.Generic.Expr F :=
  .array [.index (.var "a") 1, .index (.var "a") 2, .index (.var "a") 3, .index (.var "a") 0]

/-- Exact body of `UInt32::rotr16(a)` from `Aiur.Library.U32`. -/
def u32Rotr16Body : Aiur.Generic.Expr F :=
  .array [.index (.var "a") 2, .index (.var "a") 3, .index (.var "a") 0, .index (.var "a") 1]

/-- Exact body of `UInt32::xor_rotr7(a, b)` from `Aiur.Library.U32`. -/
def u32XorRotr7Body : Aiur.Generic.Expr F :=
  .letValue (.bind "p0") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 0, .index (.var "b") 0]) <|
  .letValue (.bind "p1") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 1, .index (.var "b") 1]) <|
  .letValue (.bind "p2") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 2, .index (.var "b") 2]) <|
  .letValue (.bind "p3") (.call "UInt8::xor_split7" (some []) [.index (.var "a") 3, .index (.var "b") 3]) <|
  .array [
    .call "UInt8::join7" (some []) [.var "p0", .var "p1"],
    .call "UInt8::join7" (some []) [.var "p1", .var "p2"],
    .call "UInt8::join7" (some []) [.var "p2", .var "p3"],
    .call "UInt8::join7" (some []) [.var "p3", .var "p0"]]

/-- Exact body of `UInt32::xor_rotr12(a, b)` from `Aiur.Library.U32`. -/
def u32XorRotr12Body : Aiur.Generic.Expr F :=
  .letValue (.bind "p0") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 0, .index (.var "b") 0]) <|
  .letValue (.bind "p1") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 1, .index (.var "b") 1]) <|
  .letValue (.bind "p2") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 2, .index (.var "b") 2]) <|
  .letValue (.bind "p3") (.call "UInt8::xor_split4" (some []) [.index (.var "a") 3, .index (.var "b") 3]) <|
  .array [
    .call "UInt8::join4" (some []) [.var "p1", .var "p2"],
    .call "UInt8::join4" (some []) [.var "p2", .var "p3"],
    .call "UInt8::join4" (some []) [.var "p3", .var "p0"],
    .call "UInt8::join4" (some []) [.var "p0", .var "p1"]]

/-- `UInt32::rotr8` library body satisfies its `U32Contracts.rotr8` contract. -/
theorem u32Rotr8_contract_of_body {world : World F}
    (hfn : WorldHasFn world "UInt32::rotr8" ["a"] u32Rotr8Body)
    {a : Nat} {wa : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    (ha : isU32Val a wa) (ev : EvalFn world "UInt32::rotr8" [wa] h r h') :
    isU32Val (rotr8Nat a) r ∧ h' = h := by
  obtain ⟨_, evBody⟩ := evalFn_plain_inv hfn rfl ev
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ := ha
  obtain ⟨v0, v1, v2, v3, h1, h2, h3, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv evBody
  obtain ⟨u0, eu0, hp0⟩ := evalExpr_index_inv e0
  obtain ⟨hl0, rfl⟩ := evalExpr_var_inv eu0
  simp at hl0; subst hl0; simp [Aiur.projectValue] at hp0; subst hp0
  obtain ⟨u1, eu1, hp1⟩ := evalExpr_index_inv e1
  obtain ⟨hl1, rfl⟩ := evalExpr_var_inv eu1
  simp at hl1; subst hl1; simp [Aiur.projectValue] at hp1; subst hp1
  obtain ⟨u2, eu2, hp2⟩ := evalExpr_index_inv e2
  obtain ⟨hl2, rfl⟩ := evalExpr_var_inv eu2
  simp at hl2; subst hl2; simp [Aiur.projectValue] at hp2; subst hp2
  obtain ⟨u3, eu3, hp3⟩ := evalExpr_index_inv e3
  obtain ⟨hl3, rfl⟩ := evalExpr_var_inv eu3
  simp at hl3; subst hl3; simp [Aiur.projectValue] at hp3; subst hp3
  rw [rotr8_pack hb0 hb1 hb2 hb3]
  exact ⟨⟨b1, b2, b3, b0, hb1, hb2, hb3, hb0, rfl, rfl⟩, rfl⟩

/-- `UInt32::rotr16` library body satisfies its `U32Contracts.rotr16` contract. -/
theorem u32Rotr16_contract_of_body {world : World F}
    (hfn : WorldHasFn world "UInt32::rotr16" ["a"] u32Rotr16Body)
    {a : Nat} {wa : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    (ha : isU32Val a wa) (ev : EvalFn world "UInt32::rotr16" [wa] h r h') :
    isU32Val (rotr16Nat a) r ∧ h' = h := by
  obtain ⟨_, evBody⟩ := evalFn_plain_inv hfn rfl ev
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ := ha
  obtain ⟨v0, v1, v2, v3, h1, h2, h3, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv evBody
  obtain ⟨u0, eu0, hp0⟩ := evalExpr_index_inv e0
  obtain ⟨hl0, rfl⟩ := evalExpr_var_inv eu0
  simp at hl0; subst hl0; simp [Aiur.projectValue] at hp0; subst hp0
  obtain ⟨u1, eu1, hp1⟩ := evalExpr_index_inv e1
  obtain ⟨hl1, rfl⟩ := evalExpr_var_inv eu1
  simp at hl1; subst hl1; simp [Aiur.projectValue] at hp1; subst hp1
  obtain ⟨u2, eu2, hp2⟩ := evalExpr_index_inv e2
  obtain ⟨hl2, rfl⟩ := evalExpr_var_inv eu2
  simp at hl2; subst hl2; simp [Aiur.projectValue] at hp2; subst hp2
  obtain ⟨u3, eu3, hp3⟩ := evalExpr_index_inv e3
  obtain ⟨hl3, rfl⟩ := evalExpr_var_inv eu3
  simp at hl3; subst hl3; simp [Aiur.projectValue] at hp3; subst hp3
  rw [rotr16_pack hb0 hb1 hb2 hb3]
  exact ⟨⟨b2, b3, b0, b1, hb2, hb3, hb0, hb1, rfl, rfl⟩, rfl⟩

private theorem evalExpr_call_var2_inv {world : World F} {locals : Environment F Nat}
    {name x y : String} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.call name (some []) [.var x, .var y]) h r h') :
    ∃ vx vy,
      locals.find? (·.1 == x) = some (x, vx) ∧
      locals.find? (·.1 == y) = some (y, vy) ∧
      EvalFn world name [vx, vy] h r h' := by
  obtain ⟨vx, vy, h1, h2, evx, evy, hfn⟩ := evalExpr_call2_inv ev
  obtain ⟨hlx, rfl⟩ := evalExpr_var_inv evx
  obtain ⟨hly, rfl⟩ := evalExpr_var_inv evy
  exact ⟨vx, vy, hlx, hly, hfn⟩

/-- `UInt32::xor_rotr7` library body satisfies `U32Contracts.xor_rotr7` given the
byte-split/join contracts of `UInt8::xor_split7` and `UInt8::join7`. -/
theorem u32XorRotr7_contract_of_body {world : World F}
    (hfn : WorldHasFn world "UInt32::xor_rotr7" ["a", "b"] u32XorRotr7Body)
    (hSplit7 : ∀ (a b : Nat) h r h', a < 256 → b < 256 →
      EvalFn world "UInt8::xor_split7" [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ r = .tuple [.field ((Nat.xor a b / 128 : Nat) : F),
                            .field (((Nat.xor a b % 128) * 2 : Nat) : F)])
    (hJoin7 : ∀ (x y : Nat) h r h', x < 256 → y < 256 →
      EvalFn world "UInt8::join7"
        [.tuple [.field ((x / 128 : Nat) : F), .field (((x % 128) * 2 : Nat) : F)],
         .tuple [.field ((y / 128 : Nat) : F), .field (((y % 128) * 2 : Nat) : F)]] h r h' →
      h' = h ∧ r = .field ((x / 128 + (y % 128) * 2 : Nat) : F))
    {a b : Nat} {wa wb : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    (ha : isU32Val a wa) (hb : isU32Val b wb)
    (ev : EvalFn world "UInt32::xor_rotr7" [wa, wb] h r h') :
    isU32Val (rotr7Nat (Nat.xor a b)) r ∧ h' = h := by
  obtain ⟨_, evBody⟩ := evalFn_plain_inv hfn rfl ev
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3, rfl, rfl⟩ := ha
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ := hb
  obtain ⟨p0, h1, evp0, evRest1⟩ := evalExpr_let_bind_inv evBody
  obtain ⟨va0, vb0, h0a, h0b, eva0, evb0, hfn0⟩ := evalExpr_call2_inv evp0
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv eva0; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv evb0; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨rfl, rfl⟩ := hSplit7 a0 b0 _ p0 h1 ha0 hb0 hfn0
  obtain ⟨p1, h2, evp1, evRest2⟩ := evalExpr_let_bind_inv evRest1
  obtain ⟨va1, vb1, h1a, h1b, eva1, evb1, hfn1⟩ := evalExpr_call2_inv evp1
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv eva1; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv evb1; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨rfl, rfl⟩ := hSplit7 a1 b1 _ p1 h2 ha1 hb1 hfn1
  obtain ⟨p2, h3, evp2, evRest3⟩ := evalExpr_let_bind_inv evRest2
  obtain ⟨va2, vb2, h2a, h2b, eva2, evb2, hfn2⟩ := evalExpr_call2_inv evp2
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv eva2; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv evb2; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨rfl, rfl⟩ := hSplit7 a2 b2 _ p2 h3 ha2 hb2 hfn2
  obtain ⟨p3, h4, evp3, evRest4⟩ := evalExpr_let_bind_inv evRest3
  obtain ⟨va3, vb3, h3a, h3b, eva3, evb3, hfn3⟩ := evalExpr_call2_inv evp3
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv eva3; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv evb3; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨rfl, rfl⟩ := hSplit7 a3 b3 _ p3 h4 ha3 hb3 hfn3
  obtain ⟨w0, w1, w2, w3, hj1, hj2, hj3, evj0, evj1, evj2, evj3, rfl⟩ := evalExpr_array4_inv evRest4
  have hx0 := U8Facts.xor_lt_256 ha0 hb0
  have hx1 := U8Facts.xor_lt_256 ha1 hb1
  have hx2 := U8Facts.xor_lt_256 ha2 hb2
  have hx3 := U8Facts.xor_lt_256 ha3 hb3
  obtain ⟨q0, q1, hl0, hl1, hf0⟩ := evalExpr_call_var2_inv evj0
  simp at hl0 hl1; subst hl0; subst hl1
  obtain ⟨rfl, rfl⟩ := hJoin7 _ _ _ w0 hj1 hx0 hx1 (by simpa using hf0)
  obtain ⟨q0, q1, hl0, hl1, hf1⟩ := evalExpr_call_var2_inv evj1
  simp at hl0 hl1; subst hl0; subst hl1
  obtain ⟨rfl, rfl⟩ := hJoin7 _ _ _ w1 hj2 hx1 hx2 (by simpa using hf1)
  obtain ⟨q0, q1, hl0, hl1, hf2⟩ := evalExpr_call_var2_inv evj2
  simp at hl0 hl1; subst hl0; subst hl1
  obtain ⟨rfl, rfl⟩ := hJoin7 _ _ _ w2 hj3 hx2 hx3 (by simpa using hf2)
  obtain ⟨q0, q1, hl0, hl1, hf3⟩ := evalExpr_call_var2_inv evj3
  simp at hl0 hl1; subst hl0; subst hl1
  obtain ⟨rfl, rfl⟩ := hJoin7 _ _ _ w3 h' hx3 hx0 (by simpa using hf3)
  rw [xor_rotr7_pack ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  exact ⟨⟨_, _, _, _,
    U32.joined_seven_bits_lt hx0 hx1, U32.joined_seven_bits_lt hx1 hx2,
    U32.joined_seven_bits_lt hx2 hx3, U32.joined_seven_bits_lt hx3 hx0, rfl, rfl⟩, rfl⟩

/-- `UInt32::xor_rotr12` library body satisfies `U32Contracts.xor_rotr12` given
the byte-split/join contracts of `UInt8::xor_split4` and `UInt8::join4`. -/
theorem u32XorRotr12_contract_of_body {world : World F}
    (hfn : WorldHasFn world "UInt32::xor_rotr12" ["a", "b"] u32XorRotr12Body)
    (hSplit4 : ∀ (a b : Nat) h r h', a < 256 → b < 256 →
      EvalFn world "UInt8::xor_split4" [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ r = .tuple [.field ((Nat.xor a b / 16 : Nat) : F),
                            .field (((Nat.xor a b % 16) * 16 : Nat) : F)])
    (hJoin4 : ∀ (x y : Nat) h r h', x < 256 → y < 256 →
      EvalFn world "UInt8::join4"
        [.tuple [.field ((x / 16 : Nat) : F), .field (((x % 16) * 16 : Nat) : F)],
         .tuple [.field ((y / 16 : Nat) : F), .field (((y % 16) * 16 : Nat) : F)]] h r h' →
      h' = h ∧ r = .field ((x / 16 + (y % 16) * 16 : Nat) : F))
    {a b : Nat} {wa wb : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    (ha : isU32Val a wa) (hb : isU32Val b wb)
    (ev : EvalFn world "UInt32::xor_rotr12" [wa, wb] h r h') :
    isU32Val (rotr12Nat (Nat.xor a b)) r ∧ h' = h := by
  obtain ⟨_, evBody⟩ := evalFn_plain_inv hfn rfl ev
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3, rfl, rfl⟩ := ha
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ := hb
  obtain ⟨p0, h1, evp0, evRest1⟩ := evalExpr_let_bind_inv evBody
  obtain ⟨va0, vb0, h0a, h0b, eva0, evb0, hfn0⟩ := evalExpr_call2_inv evp0
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv eva0; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv evb0; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨rfl, rfl⟩ := hSplit4 a0 b0 _ p0 h1 ha0 hb0 hfn0
  obtain ⟨p1, h2, evp1, evRest2⟩ := evalExpr_let_bind_inv evRest1
  obtain ⟨va1, vb1, h1a, h1b, eva1, evb1, hfn1⟩ := evalExpr_call2_inv evp1
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv eva1; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv evb1; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨rfl, rfl⟩ := hSplit4 a1 b1 _ p1 h2 ha1 hb1 hfn1
  obtain ⟨p2, h3, evp2, evRest3⟩ := evalExpr_let_bind_inv evRest2
  obtain ⟨va2, vb2, h2a, h2b, eva2, evb2, hfn2⟩ := evalExpr_call2_inv evp2
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv eva2; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv evb2; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨rfl, rfl⟩ := hSplit4 a2 b2 _ p2 h3 ha2 hb2 hfn2
  obtain ⟨p3, h4, evp3, evRest4⟩ := evalExpr_let_bind_inv evRest3
  obtain ⟨va3, vb3, h3a, h3b, eva3, evb3, hfn3⟩ := evalExpr_call2_inv evp3
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv eva3; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨u, eu, hpu⟩ := evalExpr_index_inv evb3; obtain ⟨hl, rfl⟩ := evalExpr_var_inv eu
  simp at hl; subst hl; simp [Aiur.projectValue] at hpu; subst hpu
  obtain ⟨rfl, rfl⟩ := hSplit4 a3 b3 _ p3 h4 ha3 hb3 hfn3
  obtain ⟨w0, w1, w2, w3, hj1, hj2, hj3, evj0, evj1, evj2, evj3, rfl⟩ := evalExpr_array4_inv evRest4
  have hx0 := U8Facts.xor_lt_256 ha0 hb0
  have hx1 := U8Facts.xor_lt_256 ha1 hb1
  have hx2 := U8Facts.xor_lt_256 ha2 hb2
  have hx3 := U8Facts.xor_lt_256 ha3 hb3
  obtain ⟨q0, q1, hl0, hl1, hf0⟩ := evalExpr_call_var2_inv evj0
  simp at hl0 hl1; subst hl0; subst hl1
  obtain ⟨rfl, rfl⟩ := hJoin4 _ _ _ w0 hj1 hx1 hx2 (by simpa using hf0)
  obtain ⟨q0, q1, hl0, hl1, hf1⟩ := evalExpr_call_var2_inv evj1
  simp at hl0 hl1; subst hl0; subst hl1
  obtain ⟨rfl, rfl⟩ := hJoin4 _ _ _ w1 hj2 hx2 hx3 (by simpa using hf1)
  obtain ⟨q0, q1, hl0, hl1, hf2⟩ := evalExpr_call_var2_inv evj2
  simp at hl0 hl1; subst hl0; subst hl1
  obtain ⟨rfl, rfl⟩ := hJoin4 _ _ _ w2 hj3 hx3 hx0 (by simpa using hf2)
  obtain ⟨q0, q1, hl0, hl1, hf3⟩ := evalExpr_call_var2_inv evj3
  simp at hl0 hl1; subst hl0; subst hl1
  obtain ⟨rfl, rfl⟩ := hJoin4 _ _ _ w3 h' hx0 hx1 (by simpa using hf3)
  rw [xor_rotr12_pack ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  exact ⟨⟨_, _, _, _,
    U32.joined_nibbles_lt hx1 hx2, U32.joined_nibbles_lt hx2 hx3,
    U32.joined_nibbles_lt hx3 hx0, U32.joined_nibbles_lt hx0 hx1, rfl, rfl⟩, rfl⟩

omit [DecidableEq F] in
/-- `UInt32::add3` algebraic soundness bridge: any checked result word satisfying
the cubic carry constraint of `Aiur.Library.U32.add3` equals `(a + b + c) % 2^32`. -/
theorem u32Add3_check_sound (comp : U32.Compatible F) {a b c res : Nat}
    {wa wb wc wr : SourceValue F}
    (ha : isU32Val a wa) (hb : isU32Val b wb) (hc : isU32Val c wc) (hr : isU32Val res wr)
    (hcarry :
      let carry := ((a : F) + (b : F) + (c : F) - (res : F)) / (U32.base : F)
      carry * (carry - 1) * (carry - 2) = 0) :
    isU32Val ((a + b + c) % U32.base) wr := by
  have heq : res = (a + b + c) % U32.base :=
    (U32.add3_words_check_iff comp (isU32Val_lt ha) (isU32Val_lt hb)
      (isU32Val_lt hc) (isU32Val_lt hr)).1 hcarry
  simpa [heq] using hr

end Soundness

/-! ## Compile-Time Sanity Guards (Blake3 `g` & Block Packing Patterns) -/

section Guards

private def u32Lit (k : Nat) : Expr := callE "u32_of_field" [litE k]

-- Nested `add3` (left and right)
#guard rewriteExpr (callE "UInt32::add" [callE "UInt32::add" [vE "a", vE "b"], vE "c"]) ==
  callE "UInt32::add3" [vE "a", vE "b", vE "c"]
#guard rewriteExpr (callE "UInt32::add" [vE "a", callE "UInt32::add" [vE "b", vE "c"]]) ==
  callE "UInt32::add3" [vE "a", vE "b", vE "c"]

-- Nested `rotr16`, `rotr8`, `xor_rotr12`, `xor_rotr7`
#guard rewriteExpr
  (callE "UInt32::or" [callE "u32_shr" [vE "x", u32Lit 16], callE "u32_shl" [vE "x", u32Lit 16]]) ==
  callE "UInt32::rotr16" [vE "x"]
#guard rewriteExpr
  (callE "UInt32::or" [callE "u32_shr" [vE "x", u32Lit 8], callE "u32_shl" [vE "x", u32Lit 24]]) ==
  callE "UInt32::rotr8" [vE "x"]
#guard rewriteExpr
  (callE "UInt32::or"
    [callE "u32_shr" [callE "UInt32::xor" [vE "a", vE "b"], u32Lit 12],
     callE "u32_shl" [callE "UInt32::xor" [vE "a", vE "b"], u32Lit 20]]) ==
  callE "UInt32::xor_rotr12" [vE "a", vE "b"]
#guard rewriteExpr
  (callE "UInt32::or"
    [callE "u32_shr" [callE "UInt32::xor" [vE "a", vE "b"], u32Lit 7],
     callE "u32_shl" [callE "UInt32::xor" [vE "a", vE "b"], u32Lit 25]]) ==
  callE "UInt32::xor_rotr7" [vE "a", vE "b"]

-- ANF `let`-chain mirroring `TypedLower` output on Blake3 `g`:
-- `va = va + vb + mx; vd = rotr32 (vd ^^^ va) 16; vc = vc + vd; vb = rotr32 (vb ^^^ vc) 12; ...`
private def blake3GAnfSample : Expr :=
  letE "t0" (callE "UInt32::add" [vE "va", vE "vb"]) <|
  letE "va1" (callE "UInt32::add" [vE "t0", vE "mx"]) <|
  letE "x1" (callE "UInt32::xor" [vE "vd", vE "va1"]) <|
  letE "s1" (callE "u32_shr" [vE "x1", u32Lit 16]) <|
  letE "s2" (callE "u32_shl" [vE "x1", u32Lit 16]) <|
  letE "vd1" (callE "UInt32::or" [vE "s1", vE "s2"]) <|
  letE "vc1" (callE "UInt32::add" [vE "vc", vE "vd1"]) <|
  letE "x2" (callE "UInt32::xor" [vE "vb", vE "vc1"]) <|
  letE "c32" (u32Lit 32) <|
  letE "c12" (u32Lit 12) <|
  letE "c20" (callE "UInt32::sub" [vE "c32", vE "c12"]) <|
  letE "s3" (callE "u32_shr" [vE "x2", vE "c12"]) <|
  letE "s4" (callE "u32_shl" [vE "x2", vE "c20"]) <|
  letE "vb1" (callE "UInt32::or" [vE "s3", vE "s4"]) <|
  letE "t1" (callE "UInt32::add" [vE "va1", vE "vb1"]) <|
  letE "va2" (callE "UInt32::add" [vE "t1", vE "my"]) <|
  letE "x3" (callE "UInt32::xor" [vE "vd1", vE "va2"]) <|
  letE "s5" (callE "u32_shr" [vE "x3", u32Lit 8]) <|
  letE "s6" (callE "u32_shl" [vE "x3", u32Lit 24]) <|
  letE "vd2" (callE "UInt32::or" [vE "s5", vE "s6"]) <|
  letE "vc2" (callE "UInt32::add" [vE "vc1", vE "vd2"]) <|
  letE "x4" (callE "UInt32::xor" [vE "vb1", vE "vc2"]) <|
  letE "s7" (callE "u32_shr" [vE "x4", u32Lit 7]) <|
  letE "s8" (callE "u32_shl" [vE "x4", u32Lit 25]) <|
  letE "vb2" (callE "UInt32::or" [vE "s7", vE "s8"]) <|
  .tuple [vE "va2", vE "vb2", vE "vc2", vE "vd2"]

#guard countFused (rewriteExpr blake3GAnfSample) ==
  { add3 := 2, rotr8 := 1, rotr16 := 1, xorRotr7 := 1, xorRotr12 := 1,
    fromBytes := 0, remainingShr := 0, remainingShl := 0 }

-- Constant byte shifts (`0`, `8`, `16`, `24`)
#guard rewriteExpr (callE "u32_shr" [vE "w", u32Lit 0]) == vE "w"
#guard rewriteExpr (callE "u32_shl" [vE "w", u32Lit 0]) == vE "w"
#guard (countFused (rewriteExpr (callE "u32_shr" [vE "w", u32Lit 8]))).fromBytes == 1
#guard (countFused (rewriteExpr (callE "u32_shr" [vE "w", u32Lit 8]))).remainingShr == 0
#guard (countFused (rewriteExpr (callE "u32_shl" [vE "w", u32Lit 24]))).fromBytes == 1
#guard (countFused (rewriteExpr (callE "u32_shl" [vE "w", u32Lit 24]))).remainingShl == 0

end Guards

end IxCC.AiurBackend.Peephole
