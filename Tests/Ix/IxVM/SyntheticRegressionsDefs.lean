/-! # Lean fixtures for synthetic and corpus-driven IxVM / IxCK regression tests

Elaborated Lean 4 declarations exercised by `ixvm-synthetic-regressions`
(`Tests.Ix.IxVM.SyntheticRegressions`):
- large multi-container (`MultiContDoc`) and 8-member mutual+nested (`AstMod`..`AstType`)
  modeled AST families;
- nested-in-mutual (`NestedInMut`), nested-in-nested (`NestedInNested`), 3-type
  mutual+nested (`TriM1`..`TriM3`), and universe-polymorphic kitchen-sink (`KS1Clean`/`KS2Clean`);
- parameterized dependent alias former (`AliasParamDep`), `Nat.pow` at the `2^24` boundary,
  and 4-byte UTF-8 `String.ofList` parity;
- `autoParam` / modeled-type extraction leaves and Lean 4.34 `native_decide` + custom-axiom
  classification fixtures.
-/

namespace SynReg

universe u

/-! ## 1. Multi-container nested AST (5 distinct container recursors) -/

inductive MultiContDoc where
  | text (s : String) : MultiContDoc
  | seq (xs : List MultiContDoc) : MultiContDoc
  | arr (xs : Array MultiContDoc) : MultiContDoc
  | opt (x : Option MultiContDoc) : MultiContDoc
  | pair (p : Prod MultiContDoc MultiContDoc) : MultiContDoc
  | choice (c : Sum MultiContDoc MultiContDoc) : MultiContDoc

theorem multiContDocIota :
    MultiContDoc.rec
      (motive_1 := fun _ => Nat)
      (motive_2 := fun _ => Nat)
      (motive_3 := fun _ => Nat)
      (motive_4 := fun _ => Nat)
      (motive_5 := fun _ => Nat)
      (motive_6 := fun _ => Nat)
      (fun _ => 1)
      (fun _ r => r + 1)
      (fun _ r => r + 2)
      (fun _ r => r + 3)
      (fun _ r => r + 4)
      (fun _ r => r + 5)
      0
      (fun _ _ r1 r2 => r1 + r2)
      (fun _ r => r)
      0
      (fun _ r => r)
      (fun _ _ r1 r2 => r1 + r2)
      (fun _ r => r)
      (fun _ r => r)
      (MultiContDoc.text "hi") = 1 := rfl

/-! ## 2. Large 8-member mutual + nested AST (HaskellSpec / SubVerso shape) -/

mutual
inductive AstMod where
  | mkMod (name : String) (decls : List AstDecl) : AstMod

inductive AstDecl where
  | valDecl (b : AstBind) : AstDecl
  | tyDecl (t : AstType) (alts : Array AstAlt) : AstDecl

inductive AstBind where
  | bind (p : AstPat) (rhs : AstExpr) (ann : Option AstType) : AstBind

inductive AstPat where
  | pVar (n : Nat) : AstPat
  | pLit (l : AstLit) : AstPat
  | pTuple (ps : List AstPat) (tag : optParam Nat 0) : AstPat

inductive AstExpr where
  | eLit (l : AstLit) : AstExpr
  | eApp (f : AstExpr) (args : Array AstExpr) : AstExpr
  | eLet (bs : List AstBind) (body : AstExpr) : AstExpr
  | eCase (scrut : AstExpr) (alts : List AstAlt) (prec : Nat := by exact 1) : AstExpr
  | ePair (p : Prod AstExpr AstExpr) : AstExpr

inductive AstAlt where
  | alt (p : AstPat) (rhs : AstExpr) (guard : Option AstExpr) : AstAlt

inductive AstLit where
  | lNat (n : Nat) : AstLit
  | lStr (s : String) : AstLit

inductive AstType where
  | tBase (n : Nat) : AstType
  | tFun (dom : AstType) (cod : AstType) : AstType
  | tApp (args : List AstType) : AstType
end

theorem astExprIota :
    AstExpr.rec
      (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
      (motive_3 := fun _ => Nat) (motive_4 := fun _ => Nat)
      (motive_5 := fun _ => Nat) (motive_6 := fun _ => Nat)
      (motive_7 := fun _ => Nat) (motive_8 := fun _ => Nat)
      (motive_9 := fun _ => Nat) (motive_10 := fun _ => Nat)
      (motive_11 := fun _ => Nat) (motive_12 := fun _ => Nat)
      (motive_13 := fun _ => Nat) (motive_14 := fun _ => Nat)
      (motive_15 := fun _ => Nat) (motive_16 := fun _ => Nat)
      (motive_17 := fun _ => Nat) (motive_18 := fun _ => Nat)
      (motive_19 := fun _ => Nat)
      (fun _ _ r => r)
      (fun _ r => r)
      (fun _ _ r1 r2 => r1 + r2)
      (fun _ _ _ r1 r2 r3 => r1 + r2 + r3)
      (fun n => n)
      (fun _ r => r)
      (fun _ k r => k + r)
      (fun _ r => r)
      (fun _ _ r1 r2 => r1 + r2)
      (fun _ _ r1 r2 => r1 + r2)
      (fun _ _ p r1 r2 => p + r1 + r2)
      (fun _ r => r)
      (fun _ _ _ r1 r2 r3 => r1 + r2 + r3)
      (fun n => n + 10)
      (fun _ => 20)
      (fun n => n)
      (fun _ _ r1 r2 => r1 + r2)
      (fun _ r => r)
      -- motive_9: List AstDecl
      0 (fun _ _ r1 r2 => r1 + r2)
      -- motive_10: Array AstAlt
      (fun _ r => r)
      -- motive_11: Option AstType
      0 (fun _ r => r)
      -- motive_12: List AstPat
      0 (fun _ _ r1 r2 => r1 + r2)
      -- motive_13: Array AstExpr
      (fun _ r => r)
      -- motive_14: List AstBind
      0 (fun _ _ r1 r2 => r1 + r2)
      -- motive_15: List AstAlt
      0 (fun _ _ r1 r2 => r1 + r2)
      -- motive_16: Prod AstExpr AstExpr
      (fun _ _ r1 r2 => r1 + r2)
      -- motive_17: Option AstExpr
      0 (fun _ r => r)
      -- motive_18: List AstType
      0 (fun _ _ r1 r2 => r1 + r2)
      -- motive_19: List AstExpr
      0 (fun _ _ r1 r2 => r1 + r2)
      (AstExpr.eLit (AstLit.lNat 5)) = 15 := rfl

/-! ## 3. Mutual-inside-nested and nested-inside-nested -/

mutual
inductive MutContA (α : Type) where
  | leafA (a : α) : MutContA α
  | stepA (b : MutContB α) : MutContA α
inductive MutContB (α : Type) where
  | leafB : MutContB α
  | stepB (a : MutContA α) : MutContB α
end

inductive NestedInMut where
  | base : NestedInMut
  | mk (x : MutContA NestedInMut) : NestedInMut

theorem nestedInMutIota :
    NestedInMut.rec
      (motive_1 := fun _ => Nat)
      (motive_2 := fun _ => Nat)
      (motive_3 := fun _ => Nat)
      7
      (fun _ r => r + 1)
      (fun _ r => r)
      (fun _ r => r)
      0
      (fun _ r => r)
      NestedInMut.base = 7 := rfl

inductive RoseCont (α : Type) where
  | rnode (a : α) (cs : List (RoseCont α)) : RoseCont α

inductive NestedInNested where
  | nil : NestedInNested
  | cons (r : RoseCont NestedInNested) : NestedInNested

theorem nestedInNestedIota :
    NestedInNested.rec
      (motive_1 := fun _ => Nat)
      (motive_2 := fun _ => Nat)
      (motive_3 := fun _ => Nat)
      9
      (fun _ r => r + 1)
      (fun _ _ r1 r2 => r1 + r2)
      0
      (fun _ _ r1 r2 => r1 + r2)
      NestedInNested.nil = 9 := rfl

/-! ## 4. 3-type mutual+nested + full orthogonal kitchen sink -/

mutual
inductive TriM1 where
  | leaf1 (n : optParam Nat 2) : TriM1
  | list1 (xs : List TriM2) (tag : Nat := by exact 1) : TriM1
inductive TriM2 where
  | arr2 (ys : Array TriM3) : TriM2
  | back2 (x : TriM1) : TriM2
inductive TriM3 where
  | opt3 (o : Option TriM1) : TriM3
end

theorem triM1Iota :
    TriM1.rec
      (motive_1 := fun _ => Nat)
      (motive_2 := fun _ => Nat)
      (motive_3 := fun _ => Nat)
      (motive_4 := fun _ => Nat)
      (motive_5 := fun _ => Nat)
      (motive_6 := fun _ => Nat)
      (motive_7 := fun _ => Nat)
      (fun n => n)
      (fun _ t r => t + r)
      (fun _ r => r)
      (fun _ r => r)
      (fun _ r => r)
      0 (fun _ _ r1 r2 => r1 + r2)
      (fun _ r => r)
      0 (fun _ r => r)
      0 (fun _ _ r1 r2 => r1 + r2)
      (TriM1.leaf1 11) = 11 := rfl

structure PolyTag (α : Type u) : Type u where
  tag : α
  idx : Nat

mutual
inductive KS1Clean (α : Type u) (t : PolyTag α) : Nat → Type u where
  | base (x : let A := α; A) (k : optParam Nat 3) : KS1Clean α t (t.idx + 2 * 3)
  | step (xs : List (Prod α (KS2Clean α t)))
         (n : Nat := by exact 1) : KS1Clean α t (t.idx + 6)
inductive KS2Clean (α : Type u) (t : PolyTag α) : Type u where
  | leaf (y : α) : KS2Clean α t
  | wrap (o : Option (KS1Clean α t (t.idx + 6))) : KS2Clean α t
end

theorem kitchenSinkCleanThm (α : Type u) (r : α → α → Prop)
    (f : α → Nat) (hf : ∀ a b, r a b → f a = f b) (a : α) :
    let tg : PolyTag α := ⟨a, 10⟩
    let q : Quot r := Quot.mk r a
    let _ : Sort (imax u (max u 1)) = Sort (max u 1) := rfl
    KS1Clean.rec
      (motive_1 := fun _ _ => Nat) (motive_2 := fun _ => Nat)
      (motive_3 := fun _ => Nat) (motive_4 := fun _ => Nat) (motive_5 := fun _ => Nat)
      (fun x k => k + Quot.lift f hf q + (PolyTag.mk x tg.idx).idx)
      (fun _ n r => n + r) (fun _ => 0) (fun _ r => r)
      0 (fun _ _ u1 u2 => u1 + u2) 0 (fun _ r => r) (fun _ _ r => r)
      (KS1Clean.base (t := tg) a 4) = 4 + f a + 10 := rfl

/-! ## 5. Alias former, Nat.pow cap, 4-byte UTF-8, and boundary controls -/

def FamAlias (α : Type u) : Type (u + 1) := α → Type u

inductive AliasParamDep (α : Type u) : FamAlias α where
  | mk (x : α) : AliasParamDep α x

theorem aliasParamDepThm (α : Type u) (x : α) :
    @AliasParamDep.rec α (fun _ _ => Nat) (fun _ => 42) x (AliasParamDep.mk x) = 42 := rfl

set_option exponentiation.threshold 20000000 in
theorem natPowAtCap : Nat.pow 1 16777216 = 1 := rfl

theorem strUtf8LitEqOfList : "λ🚀" = String.ofList ['λ', '🚀'] := rfl

inductive TwoProp : Prop where
  | left : TwoProp
  | right : TwoProp

/-! ## 6. Extraction & native_decide inert-classification fixtures -/

/-- Touches `autoParam` → `Lean.Syntax` without naming `Lean.Syntax.rec` or `Array.rec`. -/
def autoParamLeaf (n : Nat := by exact 7) : Nat := n + 1

/-- Touches the 8-member mutual+nested `AstExpr` without naming any recursors. -/
def usesAstType (_ : AstExpr) : Nat := 0

/-- Lean 4.34 `native_decide` theorem emitting `_native.native_decide.ax_*`. -/
theorem nativeDecideProof : Nat.ble 3 5 = true := by native_decide

/-- Downstream theorem depending on `nativeDecideProof`. -/
theorem nativeDecideDownstream : Nat.ble 3 5 = true := nativeDecideProof

/-- Explicit custom user axiom control (must remain in `ClaimContext.userAxioms`). -/
axiom customUserAx : Prop

theorem usesCustomUserAx : customUserAx → customUserAx := id

end SynReg
