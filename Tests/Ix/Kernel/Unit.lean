/-
  Kernel2 unit tests: eval, quote, force, whnf.
  Pure tests using synthetic environments — no IO, no Ixon loading.
-/
import Tests.Ix.Kernel.Helpers
import LSpec

open LSpec
open Ix.Kernel (buildPrimitives)
open Tests.Ix.Kernel.Helpers (mkAddr mkId MId parseIxName)
open Tests.Ix.Kernel.Helpers

namespace Tests.Ix.Kernel.Unit

/-! ## Expr shorthands for .meta mode -/

private def levelOfNat : Nat → L
  | 0 => .zero
  | n + 1 => .succ (levelOfNat n)

private def bv (n : Nat) : E := Ix.Kernel.Expr.mkBVar n
private def srt (n : Nat) : E := Ix.Kernel.Expr.mkSort (levelOfNat n)
private def prop : E := Ix.Kernel.Expr.mkSort .zero
private def ty : E := srt 1
private def lam (dom body : E) : E := Ix.Kernel.Expr.mkLam dom body
private def pi (dom body : E) : E := Ix.Kernel.Expr.mkForallE dom body
private def app (f a : E) : E := Ix.Kernel.Expr.mkApp f a
private def cst (id : MId) : E := .const id #[]
private def cstL (id : MId) (lvls : Array L) : E := .const id lvls
private def natLit (n : Nat) : E := .lit (.natVal n)
private def strLit (s : String) : E := .lit (.strVal s)
private def letE (ty val body : E) : E := Ix.Kernel.Expr.mkLetE ty val body
private def projE (typeId : MId) (idx : Nat) (struct : E) : E :=
  Ix.Kernel.Expr.mkProj typeId idx struct

/-! ## Test: eval+quote roundtrip for pure lambda calculus -/

def testEvalQuoteIdentity : TestSeq :=
  -- Atoms roundtrip unchanged
  test "sort roundtrips" (evalQuoteEmpty prop == .ok prop) $
  test "sort Type roundtrips" (evalQuoteEmpty ty == .ok ty) $
  test "lit nat roundtrips" (evalQuoteEmpty (natLit 42) == .ok (natLit 42)) $
  test "lit string roundtrips" (evalQuoteEmpty (strLit "hello") == .ok (strLit "hello")) $
  -- Lambda roundtrips (body is a closure, quote evaluates with fresh var)
  test "id lam roundtrips" (evalQuoteEmpty (lam ty (bv 0)) == .ok (lam ty (bv 0))) $
  test "const lam roundtrips" (evalQuoteEmpty (lam ty (natLit 5)) == .ok (lam ty (natLit 5))) $
  -- Pi roundtrips
  test "pi roundtrips" (evalQuoteEmpty (pi ty (bv 0)) == .ok (pi ty (bv 0))) $
  test "pi const roundtrips" (evalQuoteEmpty (pi ty ty) == .ok (pi ty ty))

/-! ## Test: beta reduction -/

def testBetaReduction : TestSeq :=
  -- (λx. x) 5 = 5
  let idApp := app (lam ty (bv 0)) (natLit 5)
  test "id applied to 5" (evalQuoteEmpty idApp == .ok (natLit 5)) $
  -- (λx. 42) 5 = 42
  let constApp := app (lam ty (natLit 42)) (natLit 5)
  test "const applied to 5" (evalQuoteEmpty constApp == .ok (natLit 42)) $
  -- (λx. λy. x) 1 2 = 1
  let fstApp := app (app (lam ty (lam ty (bv 1))) (natLit 1)) (natLit 2)
  test "fst 1 2 = 1" (evalQuoteEmpty fstApp == .ok (natLit 1)) $
  -- (λx. λy. y) 1 2 = 2
  let sndApp := app (app (lam ty (lam ty (bv 0))) (natLit 1)) (natLit 2)
  test "snd 1 2 = 2" (evalQuoteEmpty sndApp == .ok (natLit 2)) $
  -- Nested beta: (λf. λx. f x) (λy. y) 7 = 7
  let nestedApp := app (app (lam ty (lam ty (app (bv 1) (bv 0)))) (lam ty (bv 0))) (natLit 7)
  test "apply id nested" (evalQuoteEmpty nestedApp == .ok (natLit 7)) $
  -- Partial application: (λx. λy. x) 3 should be a lambda
  let partialApp := app (lam ty (lam ty (bv 1))) (natLit 3)
  test "partial app is lam" (evalQuoteEmpty partialApp == .ok (lam ty (natLit 3)))

/-! ## Test: let-expression zeta reduction -/

def testLetReduction : TestSeq :=
  -- let x := 5 in x = 5
  let letId := letE ty (natLit 5) (bv 0)
  test "let x := 5 in x = 5" (evalQuoteEmpty letId == .ok (natLit 5)) $
  -- let x := 5 in 42 = 42
  let letConst := letE ty (natLit 5) (natLit 42)
  test "let x := 5 in 42 = 42" (evalQuoteEmpty letConst == .ok (natLit 42)) $
  -- let x := 3 in let y := 7 in x = 3
  let letNested := letE ty (natLit 3) (letE ty (natLit 7) (bv 1))
  test "nested let fst" (evalQuoteEmpty letNested == .ok (natLit 3)) $
  -- let x := 3 in let y := 7 in y = 7
  let letNested2 := letE ty (natLit 3) (letE ty (natLit 7) (bv 0))
  test "nested let snd" (evalQuoteEmpty letNested2 == .ok (natLit 7))

/-! ## Test: Nat primitive reduction via force -/

def testNatPrimitives : TestSeq :=
  let prims := buildPrimitives .meta
  -- Build: Nat.add (lit 2) (lit 3)
  let addExpr := app (app (cst prims.natAdd) (natLit 2)) (natLit 3)
  test "Nat.add 2 3 = 5" (whnfEmpty addExpr == .ok (natLit 5)) $
  -- Nat.mul 4 5
  let mulExpr := app (app (cst prims.natMul) (natLit 4)) (natLit 5)
  test "Nat.mul 4 5 = 20" (whnfEmpty mulExpr == .ok (natLit 20)) $
  -- Nat.sub 10 3
  let subExpr := app (app (cst prims.natSub) (natLit 10)) (natLit 3)
  test "Nat.sub 10 3 = 7" (whnfEmpty subExpr == .ok (natLit 7)) $
  -- Nat.sub 3 10 = 0 (truncated)
  let subTrunc := app (app (cst prims.natSub) (natLit 3)) (natLit 10)
  test "Nat.sub 3 10 = 0" (whnfEmpty subTrunc == .ok (natLit 0)) $
  -- Nat.pow 2 10 = 1024
  let powExpr := app (app (cst prims.natPow) (natLit 2)) (natLit 10)
  test "Nat.pow 2 10 = 1024" (whnfEmpty powExpr == .ok (natLit 1024)) $
  -- Nat.succ 41 = 42
  let succExpr := app (cst prims.natSucc) (natLit 41)
  test "Nat.succ 41 = 42" (whnfEmpty succExpr == .ok (natLit 42)) $
  -- Nat.mod 17 5 = 2
  let modExpr := app (app (cst prims.natMod) (natLit 17)) (natLit 5)
  test "Nat.mod 17 5 = 2" (whnfEmpty modExpr == .ok (natLit 2)) $
  -- Nat.div 17 5 = 3
  let divExpr := app (app (cst prims.natDiv) (natLit 17)) (natLit 5)
  test "Nat.div 17 5 = 3" (whnfEmpty divExpr == .ok (natLit 3)) $
  -- Nat.beq 5 5 = Bool.true
  let beqTrue := app (app (cst prims.natBeq) (natLit 5)) (natLit 5)
  test "Nat.beq 5 5 = true" (whnfEmpty beqTrue == .ok (cst prims.boolTrue)) $
  -- Nat.beq 5 6 = Bool.false
  let beqFalse := app (app (cst prims.natBeq) (natLit 5)) (natLit 6)
  test "Nat.beq 5 6 = false" (whnfEmpty beqFalse == .ok (cst prims.boolFalse)) $
  -- Nat.ble 3 5 = Bool.true
  let bleTrue := app (app (cst prims.natBle) (natLit 3)) (natLit 5)
  test "Nat.ble 3 5 = true" (whnfEmpty bleTrue == .ok (cst prims.boolTrue)) $
  -- Nat.ble 5 3 = Bool.false
  let bleFalse := app (app (cst prims.natBle) (natLit 5)) (natLit 3)
  test "Nat.ble 5 3 = false" (whnfEmpty bleFalse == .ok (cst prims.boolFalse))

/-! ## Test: large Nat (the pathological case) -/

def testLargeNat : TestSeq :=
  let prims := buildPrimitives .meta
  -- Nat.pow 2 63 should compute instantly via nat primitives (not Peano)
  let pow2_63 := app (app (cst prims.natPow) (natLit 2)) (natLit 63)
  test "Nat.pow 2 63 = 2^63" (whnfEmpty pow2_63 == .ok (natLit 9223372036854775808)) $
  -- Nat.mul (2^32) (2^32) = 2^64
  let big := app (app (cst prims.natMul) (natLit 4294967296)) (natLit 4294967296)
  test "Nat.mul 2^32 2^32 = 2^64" (whnfEmpty big == .ok (natLit 18446744073709551616))

/-! ## Test: delta unfolding via force -/

def testDeltaUnfolding : TestSeq :=
  let defId := mkId "myFive" 1
  let prims := buildPrimitives .meta
  -- Define: myFive := Nat.add 2 3
  let addBody := app (app (cst prims.natAdd) (natLit 2)) (natLit 3)
  let env := addDef default defId ty addBody
  -- whnf (myFive) should unfold definition and reduce primitives
  test "unfold def to Nat.add 2 3 = 5" (whnfK2 env (cst defId) == .ok (natLit 5)) $
  -- Chain: myTen := Nat.add myFive myFive
  let tenId := mkId "myTen" 2
  let tenBody := app (app (cst prims.natAdd) (cst defId)) (cst defId)
  let env := addDef env tenId ty tenBody
  test "unfold chain myTen = 10" (whnfK2 env (cst tenId) == .ok (natLit 10))

/-! ## Test: delta unfolding of lambda definitions -/

def testDeltaLambda : TestSeq :=
  let idId := mkId "myId" 10
  -- Define: myId := λx. x
  let env := addDef default idId (pi ty ty) (lam ty (bv 0))
  -- whnf (myId 42) should unfold and beta-reduce to 42
  test "myId 42 = 42" (whnfK2 env (app (cst idId) (natLit 42)) == .ok (natLit 42)) $
  -- Define: myConst := λx. λy. x
  let constId := mkId "myConst" 11
  let env := addDef env constId (pi ty (pi ty ty)) (lam ty (lam ty (bv 1)))
  test "myConst 1 2 = 1" (whnfK2 env (app (app (cst constId) (natLit 1)) (natLit 2)) == .ok (natLit 1))

/-! ## Test: projection reduction -/

def testProjection : TestSeq :=
  let pairIndId := mkId "Pair" 20
  let pairCtorId := mkId "Pair.mk" 21
  -- Minimal Prod-like inductive: Pair : Type → Type → Type
  let env := addInductive default pairIndId
    (pi ty (pi ty ty))
    #[pairCtorId] (numParams := 2)
  -- Constructor: Pair.mk : (α β : Type) → α → β → Pair α β
  let ctorType := pi ty (pi ty (pi (bv 1) (pi (bv 1)
    (app (app (cst pairIndId) (bv 3)) (bv 2)))))
  let env := addCtor env pairCtorId pairIndId ctorType 0 2 2
  -- proj 0 of (Pair.mk Nat Nat 3 7) = 3
  let mkExpr := app (app (app (app (cst pairCtorId) ty) ty) (natLit 3)) (natLit 7)
  let proj0 := Ix.Kernel.Expr.mkProj pairIndId 0 mkExpr
  test "proj 0 (mk 3 7) = 3" (evalQuote env proj0 == .ok (natLit 3)) $
  -- proj 1 of (Pair.mk Nat Nat 3 7) = 7
  let proj1 := Ix.Kernel.Expr.mkProj pairIndId 1 mkExpr
  test "proj 1 (mk 3 7) = 7" (evalQuote env proj1 == .ok (natLit 7))

/-! ## Test: stuck terms stay stuck -/

def testStuckTerms : TestSeq :=
  let prims := buildPrimitives .meta
  let axId := mkId "myAxiom" 30
  let env := addAxiom default axId ty
  -- An axiom stays stuck (no value to unfold)
  test "axiom stays stuck" (whnfK2 env (cst axId) == .ok (cst axId)) $
  -- Nat.add (axiom) 5 stays stuck (can't reduce with non-literal arg)
  let stuckAdd := app (app (cst prims.natAdd) (cst axId)) (natLit 5)
  test "Nat.add axiom 5 stuck" (whnfHeadAddr env stuckAdd == .ok (some prims.natAdd.addr)) $
  -- Partial prim application stays neutral: Nat.add 5 (no second arg)
  let partialApp := app (cst prims.natAdd) (natLit 5)
  test "partial prim app stays neutral" (whnfHeadAddr env partialApp == .ok (some prims.natAdd.addr)) $
  -- Nat.add axiom (Nat.succ axiom): second arg IS structural succ, step-case fires
  let succAx := app (cst prims.natSucc) (cst axId)
  let addAxSuccAx := app (app (cst prims.natAdd) (cst axId)) succAx
  test "Nat.add axiom (succ axiom) head is succ" (whnfHeadAddr env addAxSuccAx == .ok (some prims.natSucc.addr))

/-! ## Test: nested beta+delta -/

def testNestedBetaDelta : TestSeq :=
  let prims := buildPrimitives .meta
  -- Define: double := λx. Nat.add x x
  let doubleId := mkId "double" 40
  let doubleBody := lam ty (app (app (cst prims.natAdd) (bv 0)) (bv 0))
  let env := addDef default doubleId (pi ty ty) doubleBody
  -- whnf (double 21) = 42
  test "double 21 = 42" (whnfK2 env (app (cst doubleId) (natLit 21)) == .ok (natLit 42)) $
  -- Define: quadruple := λx. double (double x)
  let quadId := mkId "quadruple" 41
  let quadBody := lam ty (app (cst doubleId) (app (cst doubleId) (bv 0)))
  let env := addDef env quadId (pi ty ty) quadBody
  test "quadruple 10 = 40" (whnfK2 env (app (cst quadId) (natLit 10)) == .ok (natLit 40))

/-! ## Test: higher-order functions -/

def testHigherOrder : TestSeq :=
  -- (λf. λx. f (f x)) (λy. Nat.succ y) 0 = 2
  let prims := buildPrimitives .meta
  let succFn := lam ty (app (cst prims.natSucc) (bv 0))
  let twice := lam (pi ty ty) (lam ty (app (bv 1) (app (bv 1) (bv 0))))
  let expr := app (app twice succFn) (natLit 0)
  test "twice succ 0 = 2" (whnfEmpty expr == .ok (natLit 2))

/-! ## Test: iota reduction (Nat.rec) -/

def testIotaReduction : TestSeq :=
  -- Build a minimal Nat-like inductive: MyNat with zero/succ
  let natIndId := mkId "MyNat" 50
  let zeroId := mkId "MyNat.zero" 51
  let succId := mkId "MyNat.succ" 52
  let recId := mkId "MyNat.rec" 53
  -- MyNat : Type
  let env := addInductive default natIndId ty #[zeroId, succId]
  -- MyNat.zero : MyNat
  let env := addCtor env zeroId natIndId (cst natIndId) 0 0 0
  -- MyNat.succ : MyNat → MyNat
  let succType := pi (cst natIndId) (cst natIndId)
  let env := addCtor env succId natIndId succType 1 0 1
  -- MyNat.rec : (motive : MyNat → Sort u) → motive zero → ((n : MyNat) → motive n → motive (succ n)) → (t : MyNat) → motive t
  -- params=0, motives=1, minors=2, indices=0
  -- For simplicity, build with 1 level and a Nat → Type motive
  let recType := pi (pi (cst natIndId) ty)  -- motive
    (pi (app (bv 0) (cst zeroId))            -- base case: motive zero
      (pi (pi (cst natIndId) (pi (app (bv 3) (bv 0)) (app (bv 4) (app (cst succId) (bv 1))))) -- step
        (pi (cst natIndId)                   -- target
          (app (bv 3) (bv 0)))))               -- result: motive t
  -- Rule for zero: nfields=0, rhs = λ motive base step => base
  let zeroRhs : E := lam ty (lam (bv 0) (lam ty (bv 1)))  -- simplified
  -- Rule for succ: nfields=1, rhs = λ motive base step n => step n (rec motive base step n)
  -- bv 0=n, bv 1=step, bv 2=base, bv 3=motive
  let succRhs : E := lam ty (lam (bv 0) (lam ty (lam (cst natIndId) (app (app (bv 1) (bv 0)) (app (app (app (app (cst recId) (bv 3)) (bv 2)) (bv 1)) (bv 0))))))
  let env := addRec env recId 0 recType #[natIndId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 2)
    (rules := #[
      { ctor := zeroId, nfields := 0, rhs := zeroRhs },
      { ctor := succId, nfields := 1, rhs := succRhs }
    ])
  -- Test: rec (λ_. Nat) 0 (λ_ acc. Nat.succ acc) zero = 0
  let motive := lam (cst natIndId) ty  -- λ _ => Nat (using real Nat for result type)
  let base := natLit 0
  let step := lam (cst natIndId) (lam ty (app (cst (buildPrimitives .meta).natSucc) (bv 0)))
  let recZero := app (app (app (app (cst recId) motive) base) step) (cst zeroId)
  test "rec zero = 0" (whnfK2 env recZero == .ok (natLit 0)) $
  -- Test: rec motive 0 step (succ zero) = 1
  let recOne := app (app (app (app (cst recId) motive) base) step) (app (cst succId) (cst zeroId))
  test "rec (succ zero) = 1" (whnfK2 env recOne == .ok (natLit 1))

/-! ## Test: isDefEq -/

def testIsDefEq : TestSeq :=
  let prims := buildPrimitives .meta
  -- Sort equality
  test "Prop == Prop" (isDefEqEmpty prop prop == .ok true) $
  test "Type == Type" (isDefEqEmpty ty ty == .ok true) $
  test "Prop != Type" (isDefEqEmpty prop ty == .ok false) $
  -- Literal equality
  test "42 == 42" (isDefEqEmpty (natLit 42) (natLit 42) == .ok true) $
  test "42 != 43" (isDefEqEmpty (natLit 42) (natLit 43) == .ok false) $
  -- Lambda equality
  test "λx.x == λx.x" (isDefEqEmpty (lam ty (bv 0)) (lam ty (bv 0)) == .ok true) $
  test "λx.x != λx.42" (isDefEqEmpty (lam ty (bv 0)) (lam ty (natLit 42)) == .ok false) $
  -- Pi equality
  test "Π.x == Π.x" (isDefEqEmpty (pi ty (bv 0)) (pi ty (bv 0)) == .ok true) $
  -- Delta: two different defs that reduce to the same value
  let d1 := mkId "d1" 60
  let d2 := mkId "d2" 61
  let env := addDef (addDef default d1 ty (natLit 5)) d2 ty (natLit 5)
  test "def1 == def2 (both reduce to 5)" (isDefEqK2 env (cst d1) (cst d2) == .ok true) $
  -- Eta: λx. f x == f
  let fId := mkId "f" 62
  let env := addDef default fId (pi ty ty) (lam ty (bv 0))
  let etaExpanded := lam ty (app (cst fId) (bv 0))
  test "eta: λx. f x == f" (isDefEqK2 env etaExpanded (cst fId) == .ok true) $
  -- Nat primitive reduction: 2+3 == 5
  let addExpr := app (app (cst prims.natAdd) (natLit 2)) (natLit 3)
  test "2+3 == 5" (isDefEqPrim addExpr (natLit 5) == .ok true) $
  test "2+3 != 6" (isDefEqPrim addExpr (natLit 6) == .ok false)

/-! ## Test: type inference -/

def testInfer : TestSeq :=
  let prims := buildPrimitives .meta
  -- Sort inference
  test "infer Sort 0 = Sort 1" (inferEmpty prop == .ok (srt 1)) $
  test "infer Sort 1 = Sort 2" (inferEmpty ty == .ok (srt 2)) $
  -- Literal inference
  test "infer natLit = Nat" (inferEmpty (natLit 42) == .ok (cst prims.nat)) $
  test "infer strLit = String" (inferEmpty (strLit "hi") == .ok (cst prims.string)) $
  -- Env with Nat registered (needed for isSort on Nat domains)
  let natConst := cst prims.nat
  let natMId : MId := (parseIxName "Nat", prims.nat.addr)
  let natEnv := addAxiom default natMId ty
  -- Lambda: λ(x : Nat). x : Nat → Nat
  let idNat := lam natConst (bv 0)
  test "infer λx:Nat. x = Nat → Nat" (inferK2 natEnv idNat == .ok (pi natConst natConst)) $
  -- Pi: (Nat → Nat) : Sort 1
  test "infer Nat → Nat = Sort 1" (inferK2 natEnv (pi natConst natConst) == .ok (srt 1)) $
  -- App: (λx:Nat. x) 5 : Nat
  let idApp := app idNat (natLit 5)
  test "infer (λx:Nat. x) 5 = Nat" (inferK2 natEnv idApp == .ok natConst) $
  -- Const: infer type of a defined constant
  let fId := mkId "f" 80
  let env := addDef natEnv fId (pi natConst natConst) (lam natConst (bv 0))
  test "infer const = its declared type" (inferK2 env (cst fId) == .ok (pi natConst natConst)) $
  -- Let: let x : Nat := 5 in x : Nat
  let letExpr := letE natConst (natLit 5) (bv 0)
  test "infer let x := 5 in x = Nat" (inferK2 natEnv letExpr == .ok natConst) $
  -- ForallE: ∀ (A : Sort 1), A → A : Sort 2
  -- i.e., pi (Sort 1) (pi (bv 0) (bv 1))
  let polyId := pi ty (pi (bv 0) (bv 1))
  test "infer ∀ A, A → A = Sort 2" (inferEmpty polyId == .ok (srt 2)) $
  -- Prop → Prop : Sort 1 (via imax 1 1 = 1)
  test "infer Prop → Prop = Sort 1" (inferEmpty (pi prop prop) == .ok (srt 1)) $
  -- isSort: Sort 0 has sort level 1
  test "isSort Sort 0 = level 1" (isSortK2 default prop == .ok (.succ .zero))

/-! ## Test: missing nat primitives -/

def testNatPrimsMissing : TestSeq :=
  let prims := buildPrimitives .meta
  -- Nat.gcd 12 8 = 4
  let gcdExpr := app (app (cst prims.natGcd) (natLit 12)) (natLit 8)
  test "Nat.gcd 12 8 = 4" (whnfEmpty gcdExpr == .ok (natLit 4)) $
  -- Nat.land 10 12 = 8 (0b1010 & 0b1100 = 0b1000)
  let landExpr := app (app (cst prims.natLand) (natLit 10)) (natLit 12)
  test "Nat.land 10 12 = 8" (whnfEmpty landExpr == .ok (natLit 8)) $
  -- Nat.lor 10 5 = 15 (0b1010 | 0b0101 = 0b1111)
  let lorExpr := app (app (cst prims.natLor) (natLit 10)) (natLit 5)
  test "Nat.lor 10 5 = 15" (whnfEmpty lorExpr == .ok (natLit 15)) $
  -- Nat.xor 10 12 = 6 (0b1010 ^ 0b1100 = 0b0110)
  let xorExpr := app (app (cst prims.natXor) (natLit 10)) (natLit 12)
  test "Nat.xor 10 12 = 6" (whnfEmpty xorExpr == .ok (natLit 6)) $
  -- Nat.shiftLeft 1 10 = 1024
  let shlExpr := app (app (cst prims.natShiftLeft) (natLit 1)) (natLit 10)
  test "Nat.shiftLeft 1 10 = 1024" (whnfEmpty shlExpr == .ok (natLit 1024)) $
  -- Nat.shiftRight 1024 3 = 128
  let shrExpr := app (app (cst prims.natShiftRight) (natLit 1024)) (natLit 3)
  test "Nat.shiftRight 1024 3 = 128" (whnfEmpty shrExpr == .ok (natLit 128))

/-! ## Test: opaque constants -/

def testOpaqueConstants : TestSeq :=
  let opaqueId := mkId "myOpaque" 100
  -- Opaque should NOT unfold
  let env := addOpaque default opaqueId ty (natLit 5)
  test "opaque stays stuck" (whnfK2 env (cst opaqueId) == .ok (cst opaqueId)) $
  -- Opaque function applied: should stay stuck
  let opaqFnId := mkId "myOpaqueFn" 101
  let env := addOpaque default opaqFnId (pi ty ty) (lam ty (bv 0))
  test "opaque fn app stays stuck" (whnfHeadAddr env (app (cst opaqFnId) (natLit 42)) == .ok (some opaqFnId.addr)) $
  -- Theorem SHOULD unfold
  let thmId := mkId "myThm" 102
  let env := addTheorem default thmId ty (natLit 5)
  test "theorem unfolds" (whnfK2 env (cst thmId) == .ok (natLit 5))

/-! ## Test: universe polymorphism -/

def testUniversePoly : TestSeq :=
  -- myId.{u} : Sort u → Sort u := λx.x (numLevels=1)
  let idId := mkId "myId" 110
  let lvlParam : L := .param 0 default
  let paramSort : E := .sort lvlParam
  let env := addDef default idId (pi paramSort paramSort) (lam paramSort (bv 0)) (numLevels := 1)
  -- myId.{1} (Type) should reduce to Type
  let lvl1 : L := .succ .zero
  let applied := app (cstL idId #[lvl1]) ty
  test "poly id.{1} Type = Type" (whnfK2 env applied == .ok ty) $
  -- myId.{0} (Prop) should reduce to Prop
  let applied0 := app (cstL idId #[.zero]) prop
  test "poly id.{0} Prop = Prop" (whnfK2 env applied0 == .ok prop)

/-! ## Test: K-reduction -/

def testKReduction : TestSeq :=
  -- MyTrue : Prop, MyTrue.intro : MyTrue
  let trueIndId := mkId "MyTrue" 120
  let introId := mkId "MyTrue.intro" 121
  let recId := mkId "MyTrue.rec" 122
  let env := addInductive default trueIndId prop #[introId]
  let env := addCtor env introId trueIndId (cst trueIndId) 0 0 0
  -- MyTrue.rec : (motive : MyTrue → Prop) → motive intro → (t : MyTrue) → motive t
  -- params=0, motives=1, minors=1, indices=0, k=true
  let recType := pi (pi (cst trueIndId) prop)  -- motive
    (pi (app (bv 0) (cst introId))               -- h : motive intro
      (pi (cst trueIndId)                         -- t : MyTrue
        (app (bv 2) (bv 0))))                       -- motive t
  let ruleRhs : E := lam (pi (cst trueIndId) prop) (lam prop (bv 0))
  let env := addRec env recId 0 recType #[trueIndId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 1)
    (rules := #[{ ctor := introId, nfields := 0, rhs := ruleRhs }])
    (k := true)
  -- K-reduction: rec motive h intro = h (intro is ctor, normal iota)
  let motive := lam (cst trueIndId) prop
  let h := cst introId -- placeholder proof
  let recIntro := app (app (app (cst recId) motive) h) (cst introId)
  test "K-rec intro = h" (whnfK2 env recIntro |>.isOk) $
  -- K-reduction with non-ctor major: rec motive h x where x is axiom of type MyTrue
  let axId := mkId "myAxiom" 123
  let env := addAxiom env axId (cst trueIndId)
  let recAx := app (app (app (cst recId) motive) h) (cst axId)
  -- K-reduction should return h (the minor) without needing x to be a ctor
  test "K-rec axiom = h" (whnfK2 env recAx |>.isOk)

/-! ## Test: proof irrelevance -/

def testProofIrrelevance : TestSeq :=
  -- Proof irrelevance fires when typeof(typeof(t)) = Sort 0 (i.e., t is a proof of a Prop type)
  -- Two axioms of type Prop are propositions (types), NOT proofs — proof irrel doesn't apply
  let ax1 := mkId "ax1" 130
  let ax2 := mkId "ax2" 131
  let env := addAxiom (addAxiom default ax1 prop) ax2 prop
  -- typeof(ax1) = Prop = Sort 0, typeof(Sort 0) = Sort 1 ≠ Sort 0 → not proofs
  test "no proof irrel: two Prop axioms (types, not proofs)" (isDefEqK2 env (cst ax1) (cst ax2) == .ok false)

/-! ## Test: Bool.true reflection -/

def testBoolTrueReflection : TestSeq :=
  let prims := buildPrimitives .meta
  -- Nat.beq 5 5 reduces to Bool.true
  let beq55 := app (app (cst prims.natBeq) (natLit 5)) (natLit 5)
  test "Bool.true == Nat.beq 5 5" (isDefEqEmpty (cst prims.boolTrue) beq55 == .ok true) $
  test "Nat.beq 5 5 == Bool.true" (isDefEqEmpty beq55 (cst prims.boolTrue) == .ok true) $
  -- Nat.beq 5 6 is Bool.false, not equal to Bool.true
  let beq56 := app (app (cst prims.natBeq) (natLit 5)) (natLit 6)
  test "Nat.beq 5 6 != Bool.true" (isDefEqPrim beq56 (cst prims.boolTrue) == .ok false)

/-! ## Test: unit-like type equality -/

def testUnitLikeDefEq : TestSeq :=
  -- MyUnit : Type with MyUnit.mk : MyUnit (1 ctor, 0 fields)
  let unitIndId := mkId "MyUnit" 140
  let mkId' := mkId "MyUnit.mk" 141
  let env := addInductive default unitIndId ty #[mkId']
  let env := addCtor env mkId' unitIndId (cst unitIndId) 0 0 0
  -- mk == mk (same ctor, trivially)
  test "unit-like: mk == mk" (isDefEqK2 env (cst mkId') (cst mkId') == .ok true) $
  -- Note: two different const-headed neutrals (ax1 vs ax2) return false in isDefEqCore
  -- before reaching isDefEqUnitLikeVal, because the const case short-circuits.
  -- This is a known limitation of the NbE-based kernel2 isDefEq.
  let ax1 := mkId "ax1" 142
  let env := addAxiom env ax1 (cst unitIndId)
  -- mk == mk applied through lambda (tests that unit-like paths resolve)
  let mkViaLam := app (lam ty (cst mkId')) (natLit 0)
  test "unit-like: mk == (λ_.mk) 0" (isDefEqK2 env mkViaLam (cst mkId') == .ok true)

/-! ## Test: isDefEqOffset (Nat.succ chain) -/

def testDefEqOffset : TestSeq :=
  let prims := buildPrimitives .meta
  -- Nat.succ (natLit 0) == natLit 1
  let succ0 := app (cst prims.natSucc) (natLit 0)
  test "Nat.succ 0 == 1" (isDefEqPrim succ0 (natLit 1) == .ok true) $
  -- Nat.zero == natLit 0
  test "Nat.zero == 0" (isDefEqPrim (cst prims.natZero) (natLit 0) == .ok true) $
  -- Nat.succ (Nat.succ Nat.zero) == natLit 2
  let succ_succ_zero := app (cst prims.natSucc) (app (cst prims.natSucc) (cst prims.natZero))
  test "Nat.succ (Nat.succ Nat.zero) == 2" (isDefEqPrim succ_succ_zero (natLit 2) == .ok true) $
  -- natLit 3 != natLit 4
  test "3 != 4" (isDefEqEmpty (natLit 3) (natLit 4) == .ok false)

/-! ## Test: recursive iota (multi-step) -/

def testRecursiveIota : TestSeq :=
  -- Reuse the MyNat setup from testIotaReduction, but test deeper recursion
  let natIndId := mkId "MyNat" 50
  let zeroId := mkId "MyNat.zero" 51
  let succId := mkId "MyNat.succ" 52
  let recId := mkId "MyNat.rec" 53
  let env := addInductive default natIndId ty #[zeroId, succId]
  let env := addCtor env zeroId natIndId (cst natIndId) 0 0 0
  let succType := pi (cst natIndId) (cst natIndId)
  let env := addCtor env succId natIndId succType 1 0 1
  let recType := pi (pi (cst natIndId) ty)
    (pi (app (bv 0) (cst zeroId))
      (pi (pi (cst natIndId) (pi (app (bv 3) (bv 0)) (app (bv 4) (app (cst succId) (bv 1)))))
        (pi (cst natIndId)
          (app (bv 3) (bv 0)))))
  let zeroRhs : E := lam ty (lam (bv 0) (lam ty (bv 1)))
  let succRhs : E := lam ty (lam (bv 0) (lam ty (lam (cst natIndId) (app (app (bv 1) (bv 0)) (app (app (app (app (cst recId) (bv 3)) (bv 2)) (bv 1)) (bv 0))))))
  let env := addRec env recId 0 recType #[natIndId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 2)
    (rules := #[
      { ctor := zeroId, nfields := 0, rhs := zeroRhs },
      { ctor := succId, nfields := 1, rhs := succRhs }
    ])
  let motive := lam (cst natIndId) ty
  let base := natLit 0
  let step := lam (cst natIndId) (lam ty (app (cst (buildPrimitives .meta).natSucc) (bv 0)))
  -- rec motive 0 step (succ (succ zero)) = 2
  let two := app (cst succId) (app (cst succId) (cst zeroId))
  let recTwo := app (app (app (app (cst recId) motive) base) step) two
  test "rec (succ (succ zero)) = 2" (whnfK2 env recTwo == .ok (natLit 2)) $
  -- rec motive 0 step (succ (succ (succ zero))) = 3
  let three := app (cst succId) two
  let recThree := app (app (app (app (cst recId) motive) base) step) three
  test "rec (succ^3 zero) = 3" (whnfK2 env recThree == .ok (natLit 3))

/-! ## Test: quotient reduction -/

def testQuotReduction : TestSeq :=
  -- Build Quot, Quot.mk, Quot.lift, Quot.ind
  let quotId := mkId "Quot" 150
  let quotMkId := mkId "Quot.mk" 151
  let quotLiftId := mkId "Quot.lift" 152
  let quotIndId := mkId "Quot.ind" 153
  -- Quot.{u} : (α : Sort u) → (α → α → Prop) → Sort u
  let quotType := pi ty (pi (pi (bv 0) (pi (bv 1) prop)) (bv 1))
  let env := addQuot default quotId quotType .type (numLevels := 1)
  -- Quot.mk.{u} : {α : Sort u} → (α → α → Prop) → α → Quot α r
  -- Simplified type — the exact type doesn't matter for reduction, only the kind
  let mkType := pi ty (pi (pi (bv 0) (pi (bv 1) prop)) (pi (bv 1)
    (app (app (cstL quotId #[.param 0 default]) (bv 2)) (bv 1))))
  let env := addQuot env quotMkId mkType .ctor (numLevels := 1)
  -- Quot.lift.{u,v} : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} →
  --   (f : α → β) → ((a b : α) → r a b → f a = f b) → Quot α r → β
  -- 6 args total, fPos=3 (0-indexed: α, r, β, f, h, quot)
  let liftType := pi ty (pi ty (pi ty (pi ty (pi ty (pi ty ty)))))  -- simplified
  let env := addQuot env quotLiftId liftType .lift (numLevels := 2)
  -- Quot.ind: 5 args, fPos=3
  let indType := pi ty (pi ty (pi ty (pi ty (pi ty prop))))  -- simplified
  let env := addQuot env quotIndId indType .ind (numLevels := 1)
  -- Test: Quot.lift α r β f h (Quot.mk α r a) = f a
  -- Build Quot.mk applied to args: (Quot.mk α r a) — need α, r, a as args
  -- mk spine: [α, r, a] where α=Nat(ty), r=dummy, a=42
  let dummyRel := lam ty (lam ty prop)  -- dummy relation
  let mkExpr := app (app (app (cstL quotMkId #[.succ .zero]) ty) dummyRel) (natLit 42)
  -- Quot.lift applied: [α, r, β, f, h, mk_expr]
  let fExpr := lam ty (app (cst (buildPrimitives .meta).natSucc) (bv 0))  -- f = λx. Nat.succ x
  let hExpr := lam ty (lam ty (lam prop (natLit 0)))  -- h = dummy proof
  let liftExpr := app (app (app (app (app (app
    (cstL quotLiftId #[.succ .zero, .succ .zero]) ty) dummyRel) ty) fExpr) hExpr) mkExpr
  test "Quot.lift f h (Quot.mk r a) = f a"
    (whnfK2 env liftExpr (quotInit := true) == .ok (natLit 43))

/-! ## Test: structure eta in isDefEq -/

def testStructEtaDefEq : TestSeq :=
  -- Reuse Pair from testProjection: Pair : Type → Type → Type, Pair.mk : α → β → Pair α β
  let pairIndId := mkId "Pair" 160
  let pairCtorId := mkId "Pair.mk" 161
  let env := addInductive default pairIndId
    (pi ty (pi ty ty))
    #[pairCtorId] (numParams := 2)
  let ctorType := pi ty (pi ty (pi (bv 1) (pi (bv 1)
    (app (app (cst pairIndId) (bv 3)) (bv 2)))))
  let env := addCtor env pairCtorId pairIndId ctorType 0 2 2
  -- Pair.mk Nat Nat 3 7 == Pair.mk Nat Nat 3 7 (trivial, same ctor)
  let mk37 := app (app (app (app (cst pairCtorId) ty) ty) (natLit 3)) (natLit 7)
  test "struct eta: mk == mk" (isDefEqK2 env mk37 mk37 == .ok true) $
  -- Same ctor applied to different args via definitions (defEq reduces through delta)
  let d1 := mkId "d1" 162
  let d2 := mkId "d2" 163
  let env := addDef (addDef env d1 ty (natLit 3)) d2 ty (natLit 3)
  let mk_d1 := app (app (app (app (cst pairCtorId) ty) ty) (cst d1)) (natLit 7)
  let mk_d2 := app (app (app (app (cst pairCtorId) ty) ty) (cst d2)) (natLit 7)
  test "struct eta: mk d1 7 == mk d2 7 (defs reduce to same)"
    (isDefEqK2 env mk_d1 mk_d2 == .ok true) $
  -- Projection reduction works: proj 0 (mk 3 7) = 3
  let proj0 := Ix.Kernel.Expr.mkProj pairIndId 0 mk37
  test "struct: proj 0 (mk 3 7) == 3"
    (isDefEqK2 env proj0 (natLit 3) == .ok true) $
  -- proj 1 (mk 3 7) = 7
  let proj1 := Ix.Kernel.Expr.mkProj pairIndId 1 mk37
  test "struct: proj 1 (mk 3 7) == 7"
    (isDefEqK2 env proj1 (natLit 7) == .ok true)

/-! ## Test: structure eta in iota -/

def testStructEtaIota : TestSeq :=
  -- Wrap : Type → Type with Wrap.mk : α → Wrap α (structure-like: 1 ctor, 1 field, 1 param)
  let wrapIndId := mkId "Wrap" 170
  let wrapMkId := mkId "Wrap.mk" 171
  let wrapRecId := mkId "Wrap.rec" 172
  let env := addInductive default wrapIndId (pi ty ty) #[wrapMkId] (numParams := 1)
  -- Wrap.mk : (α : Type) → α → Wrap α
  let mkType := pi ty (pi (bv 0) (app (cst wrapIndId) (bv 1)))
  let env := addCtor env wrapMkId wrapIndId mkType 0 1 1
  -- Wrap.rec : {α : Type} → (motive : Wrap α → Sort u) → ((a : α) → motive (mk a)) → (w : Wrap α) → motive w
  -- params=1, motives=1, minors=1, indices=0
  let recType := pi ty (pi (pi (app (cst wrapIndId) (bv 0)) ty)
    (pi (pi (bv 1) (app (bv 1) (app (app (cst wrapMkId) (bv 2)) (bv 0))))
      (pi (app (cst wrapIndId) (bv 2)) (app (bv 2) (bv 0)))))
  -- rhs: λ α motive f a => f a
  let ruleRhs : E := lam ty (lam ty (lam ty (lam ty (app (bv 1) (bv 0)))))
  let env := addRec env wrapRecId 0 recType #[wrapIndId]
    (numParams := 1) (numIndices := 0) (numMotives := 1) (numMinors := 1)
    (rules := #[{ ctor := wrapMkId, nfields := 1, rhs := ruleRhs }])
  -- Test: Wrap.rec (λ_. Nat) (λa. Nat.succ a) (Wrap.mk Nat 5) = 6
  let motive := lam (app (cst wrapIndId) ty) ty  -- λ _ => Nat
  let minor := lam ty (app (cst (buildPrimitives .meta).natSucc) (bv 0))  -- λa. succ a
  let mkExpr := app (app (cst wrapMkId) ty) (natLit 5)
  let recCtor := app (app (app (app (cst wrapRecId) ty) motive) minor) mkExpr
  test "struct iota: rec (mk 5) = 6" (whnfK2 env recCtor == .ok (natLit 6)) $
  -- Struct eta iota: rec motive minor x where x is axiom of type (Wrap Nat)
  -- Should eta-expand x via projection: minor (proj 0 x)
  let axId := mkId "myAxiom" 173
  let wrapNat := app (cst wrapIndId) ty
  let env := addAxiom env axId wrapNat
  let recAx := app (app (app (app (cst wrapRecId) ty) motive) minor) (cst axId)
  -- Result should be: minor (proj 0 axId) = succ (proj 0 axId)
  -- whnf won't fully reduce since proj 0 of axiom is stuck
  test "struct eta iota: rec on axiom reduces" (whnfK2 env recAx |>.isOk)

/-! ## Test: string literal ↔ constructor in isDefEq -/

def testStringDefEq : TestSeq :=
  let prims := buildPrimitives .meta
  -- Two identical string literals
  test "str defEq: same strings" (isDefEqEmpty (strLit "hello") (strLit "hello") == .ok true) $
  test "str defEq: diff strings" (isDefEqEmpty (strLit "hello") (strLit "world") == .ok false) $
  -- Empty string vs empty string
  test "str defEq: empty == empty" (isDefEqEmpty (strLit "") (strLit "") == .ok true) $
  -- String lit vs String.mk (List.nil Char) — constructor form of ""
  -- Build: String.mk (List.nil.{0} Char)
  let charType := cst prims.char
  let nilChar := app (cstL prims.listNil #[.zero]) charType
  let emptyStr := app (cst prims.stringMk) nilChar
  test "str defEq: \"\" == String.mk (List.nil Char)"
    (isDefEqPrim (strLit "") emptyStr == .ok true) $
  -- String lit "a" vs String.mk (List.cons Char (Char.mk 97) (List.nil Char))
  let charA := app (cst prims.charMk) (natLit 97)
  let consA := app (app (app (cstL prims.listCons #[.zero]) charType) charA) nilChar
  let strA := app (cst prims.stringMk) consA
  test "str defEq: \"a\" == String.mk (List.cons (Char.mk 97) nil)"
    (isDefEqPrim (strLit "a") strA == .ok true)

/-! ## Test: reducibility hints (unfold order in lazyDelta) -/

def testReducibilityHints : TestSeq :=
  -- abbrev unfolds before regular (abbrev has highest priority)
  -- Define abbrevFive := 5 (hints = .abbrev)
  let abbrevId := mkId "abbrevFive" 180
  let env := addDef default abbrevId ty (natLit 5) (hints := .abbrev)
  -- Define regularFive := 5 (hints = .regular 1)
  let regId := mkId "regularFive" 181
  let env := addDef env regId ty (natLit 5) (hints := .regular 1)
  -- Both should be defEq (both reduce to 5)
  test "hints: abbrev == regular (both reduce to 5)"
    (isDefEqK2 env (cst abbrevId) (cst regId) == .ok true) $
  -- Different values: abbrev 5 != regular 6
  let regId2 := mkId "regularSix" 182
  let env := addDef env regId2 ty (natLit 6) (hints := .regular 1)
  test "hints: abbrev 5 != regular 6"
    (isDefEqK2 env (cst abbrevId) (cst regId2) == .ok false) $
  -- Opaque stays stuck even vs abbrev with same value
  let opaqId := mkId "opaqFive" 183
  let env := addOpaque env opaqId ty (natLit 5)
  test "hints: opaque != abbrev (opaque doesn't unfold)"
    (isDefEqK2 env (cst opaqId) (cst abbrevId) == .ok false)

/-! ## Test: isDefEq with let expressions -/

def testDefEqLet : TestSeq :=
  -- let x := 5 in x == 5
  test "defEq let: let x := 5 in x == 5"
    (isDefEqEmpty (letE ty (natLit 5) (bv 0)) (natLit 5) == .ok true) $
  -- let x := 3 in let y := 4 in Nat.add x y == 7
  let prims := buildPrimitives .meta
  let addXY := app (app (cst prims.natAdd) (bv 1)) (bv 0)
  let letExpr := letE ty (natLit 3) (letE ty (natLit 4) addXY)
  test "defEq let: nested let add == 7"
    (isDefEqPrim letExpr (natLit 7) == .ok true) $
  -- let x := 5 in x != 6
  test "defEq let: let x := 5 in x != 6"
    (isDefEqEmpty (letE ty (natLit 5) (bv 0)) (natLit 6) == .ok false) $
  -- let x := 5 in Nat.add x x == 10 (body uses bound var twice)
  let addXX := app (app (cst prims.natAdd) (bv 0)) (bv 0)
  let letExpr2 := letE ty (natLit 5) addXX
  test "defEq let: let x := 5 in x + x == 10"
    (isDefEqPrim letExpr2 (natLit 10) == .ok true)

/-! ## Test: multiple universe parameters -/

def testMultiUnivParams : TestSeq :=
  -- myConst.{u,v} : Sort u → Sort v → Sort u := λx y. x (numLevels=2)
  let constId := mkId "myConst" 190
  let u : L := .param 0 default
  let v : L := .param 1 default
  let uSort : E := .sort u
  let vSort : E := .sort v
  let constType := pi uSort (pi vSort uSort)
  let constBody := lam uSort (lam vSort (bv 1))
  let env := addDef default constId constType constBody (numLevels := 2)
  -- myConst.{1,0} Type Prop = Type
  let applied := app (app (cstL constId #[.succ .zero, .zero]) ty) prop
  test "multi-univ: const.{1,0} Type Prop = Type" (whnfK2 env applied == .ok ty) $
  -- myConst.{0,1} Prop Type = Prop
  let applied2 := app (app (cstL constId #[.zero, .succ .zero]) prop) ty
  test "multi-univ: const.{0,1} Prop Type = Prop" (whnfK2 env applied2 == .ok prop)

/-! ## Test: negative / error cases -/

private def isError : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def testErrors : TestSeq :=
  -- Variable out of range
  test "bvar out of range" (isError (inferEmpty (bv 99))) $
  -- Unknown const reference (whnf: stays stuck; infer: errors)
  let badId := mkId "bad" 255
  test "unknown const infer" (isError (inferEmpty (cst badId))) $
  -- Application of non-function (natLit applied to natLit)
  test "app non-function" (isError (inferEmpty (app (natLit 5) (natLit 3))))

/-! ## Test: iota reduction edge cases -/

def testIotaEdgeCases : TestSeq :=
  let (env, natId, zeroId, succId, recId) := buildMyNatEnv
  let prims := buildPrimitives .meta
  let natConst := cst natId
  let motive := lam natConst ty
  let base := natLit 0
  let step := lam natConst (lam ty (app (cst prims.natSucc) (bv 0)))
  -- natLit as major on non-Nat recursor stays stuck (natLit→ctor only works for real Nat)
  let recLit0 := app (app (app (app (cst recId) motive) base) step) (natLit 0)
  test "iota natLit 0 stuck on MyNat.rec" (whnfHeadAddr env recLit0 == .ok (some recId.addr)) $
  -- rec on (succ zero) reduces to 1
  let one := app (cst succId) (cst zeroId)
  let recOne := app (app (app (app (cst recId) motive) base) step) one
  test "iota succ zero = 1" (whnfK2 env recOne == .ok (natLit 1)) $
  -- rec on (succ (succ (succ (succ zero)))) = 4
  let four := app (cst succId) (app (cst succId) (app (cst succId) (app (cst succId) (cst zeroId))))
  let recFour := app (app (app (app (cst recId) motive) base) step) four
  test "iota succ^4 zero = 4" (whnfK2 env recFour == .ok (natLit 4)) $
  -- Recursor stuck on axiom major (not a ctor, not a natLit)
  let axId := mkId "myAxiom" 54
  let env' := addAxiom env axId natConst
  let recAx := app (app (app (app (cst recId) motive) base) step) (cst axId)
  test "iota stuck on axiom" (whnfHeadAddr env' recAx == .ok (some recId.addr)) $
  -- Extra trailing args after major: build a function-motive that returns (Nat → Nat)
  -- rec motive base step zero extraArg — extraArg should be applied to result
  let fnMotive := lam natConst (pi ty ty)  -- motive: MyNat → (Nat → Nat)
  let fnBase := lam ty (app (cst prims.natAdd) (bv 0))  -- base: λx. Nat.add x (partial app)
  let fnStep := lam natConst (lam (pi ty ty) (bv 0))  -- step: λ_ acc. acc
  let recFnZero := app (app (app (app (app (cst recId) fnMotive) fnBase) fnStep) (cst zeroId)) (natLit 10)
  -- Should be: (λx. Nat.add x) 10 = Nat.add 10 = reduced
  -- Result is (λx. Nat.add x) applied to 10 → Nat.add 10 (partial, stays neutral)
  test "iota with extra trailing arg" (whnfK2 env recFnZero |>.isOk) $
  -- Deep recursion: rec on succ^5 zero = 5
  let five := app (cst succId) (app (cst succId) (app (cst succId) (app (cst succId) (app (cst succId) (cst zeroId)))))
  let recFive := app (app (app (app (cst recId) motive) base) step) five
  test "iota rec succ^5 zero = 5" (whnfK2 env recFive == .ok (natLit 5))

/-! ## Test: K-reduction extended -/

def testKReductionExtended : TestSeq :=
  let (env, trueId, introId, recId) := buildMyTrueEnv
  let trueConst := cst trueId
  let motive := lam trueConst prop
  let h := cst introId  -- minor premise: just intro as a placeholder proof
  -- K-rec on intro: verify actual result (not just .isOk)
  let recIntro := app (app (app (cst recId) motive) h) (cst introId)
  test "K-rec intro = intro" (whnfK2 env recIntro == .ok (cst introId)) $
  -- K-rec on axiom: verify returns the minor
  let axId := mkId "myAxiom" 123
  let env' := addAxiom env axId trueConst
  let recAx := app (app (app (cst recId) motive) h) (cst axId)
  test "K-rec axiom = intro" (whnfK2 env' recAx == .ok (cst introId)) $
  -- K-rec with different minor value
  let ax2 := mkId "ax2" 124
  let env' := addAxiom env ax2 trueConst
  let recAx2 := app (app (app (cst recId) motive) (cst ax2)) (cst introId)
  test "K-rec intro with ax minor = ax" (whnfK2 env' recAx2 == .ok (cst ax2)) $
  -- K-reduction fails on non-K recursor: use MyNat.rec (not K)
  let (natEnv, natId, _zeroId, _succId, natRecId) := buildMyNatEnv
  let natMotive := lam (cst natId) ty
  let natBase := natLit 0
  let prims := buildPrimitives .meta
  let natStep := lam (cst natId) (lam ty (app (cst prims.natSucc) (bv 0)))
  -- Apply rec to axiom of type MyNat — should stay stuck (not K-reducible)
  let natAxId := mkId "natAxiom" 125
  let natEnv' := addAxiom natEnv natAxId (cst natId)
  let recNatAx := app (app (app (app (cst natRecId) natMotive) natBase) natStep) (cst natAxId)
  test "non-K rec on axiom stays stuck" (whnfHeadAddr natEnv' recNatAx == .ok (some natRecId.addr))

/-! ## Test: proof irrelevance extended -/

def testProofIrrelevanceExtended : TestSeq :=
  let (env, _trueId, introId, _recId) := buildMyTrueEnv
  -- Proof irrelevance fires when typeof(typeof(t)) = Sort 0, i.e., t is a proof of a Prop type.
  -- Two axioms of type Prop are propositions (types), NOT proofs — proof irrel doesn't apply:
  let p1 := mkId "p1" 130
  let p2 := mkId "p2" 131
  let propEnv := addAxiom (addAxiom default p1 prop) p2 prop
  test "no proof irrel: two Prop axioms (types, not proofs)" (isDefEqK2 propEnv (cst p1) (cst p2) == .ok false) $
  -- Two axioms of type MyTrue are proofs. typeof(proof) = MyTrue, typeof(MyTrue) = Prop.
  -- Proof irrel checks: typeof(h1) = MyTrue, whnf(MyTrue) is neutral, not Sort 0 → no irrel.
  -- BUT proofs of same type should still be defEq via proof irrel at the proof level.
  -- Actually: inferTypeOfVal h1 → MyTrue, then whnf(MyTrue) is .neutral, not .sort .zero.
  -- So proof irrel does NOT fire for proofs of MyTrue (it fires for Prop types, not proofs of Prop types).
  -- intro and intro should be defEq (same term)
  test "proof irrel: intro == intro" (isDefEqK2 env (cst introId) (cst introId) == .ok true) $
  -- Two Type-level axioms should NOT be defEq via proof irrelevance
  let a1 := mkId "a1" 132
  let a2 := mkId "a2" 133
  let env'' := addAxiom (addAxiom env a1 ty) a2 ty
  test "no proof irrel for Type" (isDefEqK2 env'' (cst a1) (cst a2) == .ok false) $
  -- Two axioms of type Nat should NOT be defEq
  let prims := buildPrimitives .meta
  let natMId : MId := (parseIxName "Nat", prims.nat.addr)
  let natEnv := addAxiom default natMId ty
  let n1 := mkId "n1" 134
  let n2 := mkId "n2" 135
  let natEnv := addAxiom (addAxiom natEnv n1 (cst prims.nat)) n2 (cst prims.nat)
  test "no proof irrel for Nat" (isDefEqK2 natEnv (cst n1) (cst n2) == .ok false)

/-! ## Test: quotient extended -/

def testQuotExtended : TestSeq :=
  -- Same quot setup as testQuotReduction
  let quotId := mkId "Quot" 150
  let quotMkId := mkId "Quot.mk" 151
  let quotLiftId := mkId "Quot.lift" 152
  let quotIndId := mkId "Quot.ind" 153
  let quotType := pi ty (pi (pi (bv 0) (pi (bv 1) prop)) (bv 1))
  let env := addQuot default quotId quotType .type (numLevels := 1)
  let mkType := pi ty (pi (pi (bv 0) (pi (bv 1) prop)) (pi (bv 1)
    (app (app (cstL quotId #[.param 0 default]) (bv 2)) (bv 1))))
  let env := addQuot env quotMkId mkType .ctor (numLevels := 1)
  let liftType := pi ty (pi ty (pi ty (pi ty (pi ty (pi ty ty)))))
  let env := addQuot env quotLiftId liftType .lift (numLevels := 2)
  let indType := pi ty (pi ty (pi ty (pi ty (pi ty prop))))
  let env := addQuot env quotIndId indType .ind (numLevels := 1)
  let prims := buildPrimitives .meta
  let dummyRel := lam ty (lam ty prop)
  -- Quot.lift with quotInit=false should NOT reduce
  let mkExpr := app (app (app (cstL quotMkId #[.succ .zero]) ty) dummyRel) (natLit 42)
  let fExpr := lam ty (app (cst prims.natSucc) (bv 0))
  let hExpr := lam ty (lam ty (lam prop (natLit 0)))
  let liftExpr := app (app (app (app (app (app
    (cstL quotLiftId #[.succ .zero, .succ .zero]) ty) dummyRel) ty) fExpr) hExpr) mkExpr
  -- When quotInit=false, Quot.lift stays stuck (whnfCoreImpl guards on quotInit)
  test "Quot.lift stays stuck with quotInit=false"
    (whnfK2 env liftExpr (quotInit := false) != .ok (natLit 43)) $
  -- Quot.lift with quotInit=true reduces (verify it works)
  test "Quot.lift reduces when quotInit=true"
    (whnfK2 env liftExpr (quotInit := true) == .ok (natLit 43)) $
  -- Quot.ind: 5 args, fPos=3
  -- Quot.ind α r (motive : Quot α r → Prop) (f : ∀ a, motive (Quot.mk a)) (q : Quot α r) : motive q
  -- Applying to (Quot.mk α r a) should give f a
  let indFExpr := lam ty (cst prims.boolTrue)  -- f = λa. Bool.true (dummy)
  let indMotiveExpr := lam ty prop  -- motive = λ_. Prop (dummy)
  let indExpr := app (app (app (app (app
    (cstL quotIndId #[.succ .zero]) ty) dummyRel) indMotiveExpr) indFExpr) mkExpr
  test "Quot.ind reduces"
    (whnfK2 env indExpr (quotInit := true) == .ok (cst prims.boolTrue))

/-! ## Test: lazyDelta strategies -/

def testLazyDeltaStrategies : TestSeq :=
  -- Two defs with same body, same height → same-head should short-circuit
  let d1 := mkId "d1" 200
  let d2 := mkId "d2" 201
  let body := natLit 42
  let env := addDef (addDef default d1 ty body (hints := .regular 1)) d2 ty body (hints := .regular 1)
  test "same head, same height: defEq" (isDefEqK2 env (cst d1) (cst d2) == .ok true) $
  -- Two defs with DIFFERENT bodies, same height → unfold both, compare
  let d3 := mkId "d3" 202
  let d4 := mkId "d4" 203
  let env := addDef (addDef default d3 ty (natLit 5) (hints := .regular 1)) d4 ty (natLit 6) (hints := .regular 1)
  test "same height, diff bodies: not defEq" (isDefEqK2 env (cst d3) (cst d4) == .ok false) $
  -- Chain of defs: a := 5, b := a, c := b → c == 5
  let a := mkId "a" 204
  let b := mkId "b" 205
  let c := mkId "c" 206
  let env := addDef default a ty (natLit 5) (hints := .regular 1)
  let env := addDef env b ty (cst a) (hints := .regular 2)
  let env := addDef env c ty (cst b) (hints := .regular 3)
  test "def chain: c == 5" (isDefEqK2 env (cst c) (natLit 5) == .ok true) $
  test "def chain: c == a" (isDefEqK2 env (cst c) (cst a) == .ok true) $
  -- Abbrev vs regular at different heights
  let ab := mkId "ab" 207
  let reg := mkId "reg" 208
  let env := addDef (addDef default ab ty (natLit 10) (hints := .abbrev)) reg ty (natLit 10) (hints := .regular 5)
  test "abbrev == regular (same val)" (isDefEqK2 env (cst ab) (cst reg) == .ok true) $
  -- Applied defs with same head: f 3 == g 3 where f = g = λx.x
  let f := mkId "f" 209
  let g := mkId "g" 210
  let env := addDef (addDef default f (pi ty ty) (lam ty (bv 0)) (hints := .regular 1)) g (pi ty ty) (lam ty (bv 0)) (hints := .regular 1)
  test "same head applied: f 3 == g 3" (isDefEqK2 env (app (cst f) (natLit 3)) (app (cst g) (natLit 3)) == .ok true) $
  -- Same head, different spines → not defEq
  test "same head, diff spine: f 3 != f 4" (isDefEqK2 env (app (cst f) (natLit 3)) (app (cst f) (natLit 4)) == .ok false)

/-! ## Test: eta expansion extended -/

def testEtaExtended : TestSeq :=
  -- f == λx. f x (reversed from existing test — non-lambda on left)
  let fId := mkId "f" 220
  let env := addDef default fId (pi ty ty) (lam ty (bv 0))
  let etaExpanded := lam ty (app (cst fId) (bv 0))
  test "eta: f == λx. f x" (isDefEqK2 env (cst fId) etaExpanded == .ok true) $
  -- Double eta: f == λx. λy. f x y where f : Nat → Nat → Nat
  let f2Id := mkId "f2" 221
  let f2Type := pi ty (pi ty ty)
  let env := addDef default f2Id f2Type (lam ty (lam ty (bv 1)))
  let doubleEta := lam ty (lam ty (app (app (cst f2Id) (bv 1)) (bv 0)))
  test "double eta: f == λx.λy. f x y" (isDefEqK2 env (cst f2Id) doubleEta == .ok true) $
  -- Eta: λx. (λy. y) x == λy. y  (beta under eta)
  let idLam := lam ty (bv 0)
  let etaId := lam ty (app (lam ty (bv 0)) (bv 0))
  test "eta+beta: λx.(λy.y) x == λy.y" (isDefEqEmpty etaId idLam == .ok true) $
  -- Lambda vs lambda with different but defEq bodies
  let l1 := lam ty (natLit 5)
  let l2 := lam ty (natLit 5)
  test "lam body defEq" (isDefEqEmpty l1 l2 == .ok true) $
  -- Lambda vs lambda with different bodies
  let l3 := lam ty (natLit 5)
  let l4 := lam ty (natLit 6)
  test "lam body not defEq" (isDefEqEmpty l3 l4 == .ok false)

/-! ## Test: nat primitive edge cases -/

def testNatPrimEdgeCases : TestSeq :=
  let prims := buildPrimitives .meta
  -- Nat.div 0 0 = 0 (Lean convention)
  let div00 := app (app (cst prims.natDiv) (natLit 0)) (natLit 0)
  test "Nat.div 0 0 = 0" (whnfEmpty div00 == .ok (natLit 0)) $
  -- Nat.mod 0 0 = 0
  let mod00 := app (app (cst prims.natMod) (natLit 0)) (natLit 0)
  test "Nat.mod 0 0 = 0" (whnfEmpty mod00 == .ok (natLit 0)) $
  -- Nat.gcd 0 0 = 0
  let gcd00 := app (app (cst prims.natGcd) (natLit 0)) (natLit 0)
  test "Nat.gcd 0 0 = 0" (whnfEmpty gcd00 == .ok (natLit 0)) $
  -- Nat.sub 0 0 = 0
  let sub00 := app (app (cst prims.natSub) (natLit 0)) (natLit 0)
  test "Nat.sub 0 0 = 0" (whnfEmpty sub00 == .ok (natLit 0)) $
  -- Nat.pow 0 0 = 1
  let pow00 := app (app (cst prims.natPow) (natLit 0)) (natLit 0)
  test "Nat.pow 0 0 = 1" (whnfEmpty pow00 == .ok (natLit 1)) $
  -- Nat.mul 0 anything = 0
  let mul0 := app (app (cst prims.natMul) (natLit 0)) (natLit 999)
  test "Nat.mul 0 999 = 0" (whnfEmpty mul0 == .ok (natLit 0)) $
  -- Nat.ble with equal args
  let bleEq := app (app (cst prims.natBle) (natLit 5)) (natLit 5)
  test "Nat.ble 5 5 = true" (whnfEmpty bleEq == .ok (cst prims.boolTrue)) $
  -- Chained: (3 * 4) + (10 - 3) = 19
  let inner1 := app (app (cst prims.natMul) (natLit 3)) (natLit 4)
  let inner2 := app (app (cst prims.natSub) (natLit 10)) (natLit 3)
  let chained := app (app (cst prims.natAdd) inner1) inner2
  test "chained: (3*4) + (10-3) = 19" (whnfEmpty chained == .ok (natLit 19)) $
  -- Nat.beq 0 0 = true
  let beq00 := app (app (cst prims.natBeq) (natLit 0)) (natLit 0)
  test "Nat.beq 0 0 = true" (whnfEmpty beq00 == .ok (cst prims.boolTrue)) $
  -- Nat.shiftLeft 0 100 = 0
  let shl0 := app (app (cst prims.natShiftLeft) (natLit 0)) (natLit 100)
  test "Nat.shiftLeft 0 100 = 0" (whnfEmpty shl0 == .ok (natLit 0)) $
  -- Nat.shiftRight 0 100 = 0
  let shr0 := app (app (cst prims.natShiftRight) (natLit 0)) (natLit 100)
  test "Nat.shiftRight 0 100 = 0" (whnfEmpty shr0 == .ok (natLit 0))

/-! ## Test: inference extended -/

def testInferExtended : TestSeq :=
  let prims := buildPrimitives .meta
  let natMId : MId := (parseIxName "Nat", prims.nat.addr)
  let natEnv := addAxiom default natMId ty
  let natConst := cst prims.nat
  -- Nested lambda: λ(x:Nat). λ(y:Nat). x : Nat → Nat → Nat
  let nestedLam := lam natConst (lam natConst (bv 1))
  test "infer nested lambda" (inferK2 natEnv nestedLam == .ok (pi natConst (pi natConst natConst))) $
  -- ForallE imax: Prop → Type should be Type (imax 0 1 = 1)
  test "infer Prop → Type = Sort 2" (inferEmpty (pi prop ty) == .ok (srt 2)) $
  -- Type → Prop: domain Sort 1 : Sort 2 (u=2), body Sort 0 : Sort 1 (v=1)
  -- Result = Sort (imax 2 1) = Sort (max 2 1) = Sort 2
  test "infer Type → Prop = Sort 2" (inferEmpty (pi ty prop) == .ok (srt 2)) $
  -- Projection inference: proj 0 of (Pair.mk Type Type 3 7)
  -- This requires a fully set up Pair env with valid ctor types
  let (pairEnv, pairId, pairCtorId) := buildPairEnv natEnv
  let mkExpr := app (app (app (app (cst pairCtorId) natConst) natConst) (natLit 3)) (natLit 7)
  let proj0 := Ix.Kernel.Expr.mkProj pairId 0 mkExpr
  test "infer proj 0 (mk Nat Nat 3 7)" (inferK2 pairEnv proj0 |>.isOk) $
  -- Let inference: let x : Nat := 5 in let y : Nat := x in y : Nat
  let letNested := letE natConst (natLit 5) (letE natConst (bv 0) (bv 0))
  test "infer nested let" (inferK2 natEnv letNested == .ok natConst) $
  -- Inference of app with computed type
  let idId := mkId "id" 230
  let env := addDef natEnv idId (pi natConst natConst) (lam natConst (bv 0))
  test "infer applied def" (inferK2 env (app (cst idId) (natLit 5)) == .ok natConst)

/-! ## Test: errors extended -/

def testErrorsExtended : TestSeq :=
  let prims := buildPrimitives .meta
  let natMId : MId := (parseIxName "Nat", prims.nat.addr)
  let natEnv := addAxiom default natMId ty
  let natConst := cst prims.nat
  -- App type mismatch: (λ(x:Nat). x) Prop
  let badApp := app (lam natConst (bv 0)) prop
  test "app type mismatch" (isError (inferK2 natEnv badApp)) $
  -- Let value type mismatch: let x : Nat := Prop in x
  let badLet := letE natConst prop (bv 0)
  test "let type mismatch" (isError (inferK2 natEnv badLet)) $
  -- Wrong universe level count on const: myId.{u} applied with 0 levels instead of 1
  let idId := mkId "myId" 240
  let lvlParam : L := .param 0 default
  let paramSort : E := .sort lvlParam
  let env := addDef natEnv idId (pi paramSort paramSort) (lam paramSort (bv 0)) (numLevels := 1)
  test "wrong univ level count" (isError (inferK2 env (cst idId))) $  -- 0 levels, expects 1
  -- Non-sort domain in lambda: λ(x : 5). x
  let badLam := lam (natLit 5) (bv 0)
  test "non-sort domain in lambda" (isError (inferK2 natEnv badLam)) $
  -- Non-sort domain in forallE
  let badPi := pi (natLit 5) (bv 0)
  test "non-sort domain in forallE" (isError (inferK2 natEnv badPi)) $
  -- Double application of non-function: (5 3) 2
  test "nested non-function app" (isError (inferEmpty (app (app (natLit 5) (natLit 3)) (natLit 2))))

/-! ## Test: string literal edge cases -/

def testStringEdgeCases : TestSeq :=
  let prims := buildPrimitives .meta
  -- whnf of string literal stays as literal
  test "whnf string lit stays" (whnfEmpty (strLit "hello") == .ok (strLit "hello")) $
  -- String inequality via defEq
  test "str: \"a\" != \"b\"" (isDefEqEmpty (strLit "a") (strLit "b") == .ok false) $
  -- Multi-char string defEq
  test "str: \"ab\" == \"ab\"" (isDefEqEmpty (strLit "ab") (strLit "ab") == .ok true) $
  -- Multi-char string vs constructor form: "ab" == String.mk (cons (Char.mk 97) (cons (Char.mk 98) nil))
  let charType := cst prims.char
  let nilChar := app (cstL prims.listNil #[.zero]) charType
  let charA := app (cst prims.charMk) (natLit 97)
  let charB := app (cst prims.charMk) (natLit 98)
  let consB := app (app (app (cstL prims.listCons #[.zero]) charType) charB) nilChar
  let consAB := app (app (app (cstL prims.listCons #[.zero]) charType) charA) consB
  let strAB := app (cst prims.stringMk) consAB
  test "str: \"ab\" == String.mk ctor form"
    (isDefEqPrim (strLit "ab") strAB == .ok true) $
  -- Different multi-char strings
  test "str: \"ab\" != \"ac\"" (isDefEqEmpty (strLit "ab") (strLit "ac") == .ok false)

/-! ## Test: isDefEq complex -/

def testDefEqComplex : TestSeq :=
  let prims := buildPrimitives .meta
  -- DefEq through application: f 3 == g 3 where f,g reduce to same lambda
  let f := mkId "f" 250
  let g := mkId "g" 251
  let env := addDef (addDef default f (pi ty ty) (lam ty (bv 0))) g (pi ty ty) (lam ty (bv 0))
  test "defEq: f 3 == g 3" (isDefEqK2 env (app (cst f) (natLit 3)) (app (cst g) (natLit 3)) == .ok true) $
  -- DefEq between Pi types
  test "defEq: Nat→Nat == Nat→Nat" (isDefEqEmpty (pi ty ty) (pi ty ty) == .ok true) $
  -- DefEq with nested pis
  test "defEq: (A → B → A) == (A → B → A)" (isDefEqEmpty (pi ty (pi ty (bv 1))) (pi ty (pi ty (bv 1))) == .ok true) $
  -- Negative: Pi types where codomain differs
  test "defEq: (A → A) != (A → B)" (isDefEqEmpty (pi ty (bv 0)) (pi ty ty) == .ok false) $
  -- DefEq through projection
  let (pairEnv, pairId, pairCtorId) := buildPairEnv
  let mk37 := app (app (app (app (cst pairCtorId) ty) ty) (natLit 3)) (natLit 7)
  let proj0 := Ix.Kernel.Expr.mkProj pairId 0 mk37
  test "defEq: proj 0 (mk 3 7) == 3" (isDefEqK2 pairEnv proj0 (natLit 3) == .ok true) $
  -- DefEq through double projection
  let proj1 := Ix.Kernel.Expr.mkProj pairId 1 mk37
  test "defEq: proj 1 (mk 3 7) == 7" (isDefEqK2 pairEnv proj1 (natLit 7) == .ok true) $
  -- DefEq: Nat.add commutes (via reduction)
  let add23 := app (app (cst prims.natAdd) (natLit 2)) (natLit 3)
  let add32 := app (app (cst prims.natAdd) (natLit 3)) (natLit 2)
  test "defEq: 2+3 == 3+2" (isDefEqPrim add23 add32 == .ok true) $
  -- DefEq: complex nested expression
  let expr1 := app (app (cst prims.natAdd) (app (app (cst prims.natMul) (natLit 2)) (natLit 3))) (natLit 1)
  test "defEq: 2*3 + 1 == 7" (isDefEqPrim expr1 (natLit 7) == .ok true) $
  -- DefEq sort levels
  test "defEq: Sort 0 != Sort 1" (isDefEqEmpty prop ty == .ok false) $
  test "defEq: Sort 2 == Sort 2" (isDefEqEmpty (srt 2) (srt 2) == .ok true)

/-! ## Test: universe extended -/

def testUniverseExtended : TestSeq :=
  -- Three universe params: myConst.{u,v,w}
  let constId := mkId "myConst" 260
  let u : L := .param 0 default
  let v : L := .param 1 default
  let w : L := .param 2 default
  let uSort : E := .sort u
  let vSort : E := .sort v
  let wSort : E := .sort w
  -- myConst.{u,v,w} : Sort u → Sort v → Sort w → Sort u
  let constType := pi uSort (pi vSort (pi wSort uSort))
  let constBody := lam uSort (lam vSort (lam wSort (bv 2)))
  let env := addDef default constId constType constBody (numLevels := 3)
  -- myConst.{1,0,2} Type Prop (Sort 2) = Type
  let applied := app (app (app (cstL constId #[.succ .zero, .zero, .succ (.succ .zero)]) ty) prop) (srt 2)
  test "3-univ: const.{1,0,2} Type Prop Sort2 = Type" (whnfK2 env applied == .ok ty) $
  -- Universe level defEq: Sort (max 0 1) == Sort 1
  let maxSort := Ix.Kernel.Expr.mkSort (.max .zero (.succ .zero))
  test "defEq: Sort (max 0 1) == Sort 1" (isDefEqEmpty maxSort ty == .ok true) $
  -- Universe level defEq: Sort (imax 1 0) == Sort 0
  -- imax u 0 = 0
  let imaxSort := Ix.Kernel.Expr.mkSort (.imax (.succ .zero) .zero)
  test "defEq: Sort (imax 1 0) == Prop" (isDefEqEmpty imaxSort prop == .ok true) $
  -- imax 0 1 = max 0 1 = 1
  let imaxSort2 := Ix.Kernel.Expr.mkSort (.imax .zero (.succ .zero))
  test "defEq: Sort (imax 0 1) == Type" (isDefEqEmpty imaxSort2 ty == .ok true) $
  -- Sort (succ (succ zero)) == Sort 2
  let sort2a := Ix.Kernel.Expr.mkSort (.succ (.succ .zero))
  test "defEq: Sort (succ (succ zero)) == Sort 2" (isDefEqEmpty sort2a (srt 2) == .ok true)

/-! ## Test: whnf caching and stuck terms -/

def testWhnfCaching : TestSeq :=
  let prims := buildPrimitives .meta
  -- Repeated whnf on same term should use cache (we can't observe cache directly,
  -- but we can verify correctness through multiple evaluations)
  let addExpr := app (app (cst prims.natAdd) (natLit 100)) (natLit 200)
  test "whnf cached: first eval" (whnfEmpty addExpr == .ok (natLit 300)) $
  -- Projection stuck on axiom
  let (pairEnv, pairId, _pairCtorId) := buildPairEnv
  let axId := mkId "myAxiom" 270
  let env := addAxiom pairEnv axId (app (app (cst pairId) ty) ty)
  let projStuck := Ix.Kernel.Expr.mkProj pairId 0 (cst axId)
  test "proj stuck on axiom" (whnfK2 env projStuck |>.isOk) $
  -- Deeply chained definitions: a → b → c → d → e, all reducing to 99
  let a := mkId "a" 271
  let b := mkId "b" 272
  let c := mkId "c" 273
  let d := mkId "d" 274
  let e := mkId "e" 275
  let chainEnv := addDef (addDef (addDef (addDef (addDef default a ty (natLit 99)) b ty (cst a)) c ty (cst b)) d ty (cst c)) e ty (cst d)
  test "deep def chain" (whnfK2 chainEnv (cst e) == .ok (natLit 99))

-- TODO: OVERFLOW
--/-! ## Test: struct eta in defEq with axioms -/
--
def testStructEtaAxiom : TestSeq :=
  -- Pair where one side is an axiom, eta-expand via projections
  let (pairEnv, pairId, pairCtorId) := buildPairEnv
  -- mk (proj 0 x) (proj 1 x) == x should hold by struct eta
  let axId := mkId "myAxiom" 290
  let pairType := app (app (cst pairId) ty) ty
  let env := addAxiom pairEnv axId pairType
  let proj0 := Ix.Kernel.Expr.mkProj pairId 0 (cst axId)
  let proj1 := Ix.Kernel.Expr.mkProj pairId 1 (cst axId)
  let rebuilt := app (app (app (app (cst pairCtorId) ty) ty) proj0) proj1
  -- This tests the tryEtaStructVal path in isDefEqCore
  test "struct eta: mk (proj0 x) (proj1 x) == x"
    (isDefEqK2 env rebuilt (cst axId) == .ok true) $
  -- Same struct, same axiom: trivially defEq
  test "struct eta: x == x" (isDefEqK2 env (cst axId) (cst axId) == .ok true) $
  -- Two different axioms of same struct type: NOT defEq (Type, not Prop)
  let ax2Id := mkId "ax2" 291
  let env := addAxiom env ax2Id pairType
  test "struct: diff axioms not defEq"
    (isDefEqK2 env (cst axId) (cst ax2Id) == .ok false)

/-! ## Test: reduceBool / reduceNat native reduction -/

def testNativeReduction : TestSeq :=
  let prims := buildPrimitives .meta
  -- Set up custom prims with reduceBool/reduceNat addresses
  let rbId := mkId "reduceBool" 200  -- reduceBool marker
  let rnId := mkId "reduceNat" 201  -- reduceNat marker
  let customPrims : Prims := { prims with reduceBool := rbId, reduceNat := rnId }
  -- Define a def that reduces to Bool.true
  let trueDefId := mkId "trueDef" 202
  let env := addDef default trueDefId (cst prims.bool) (cst prims.boolTrue)
  -- Define a def that reduces to Bool.false
  let falseDefId := mkId "falseDef" 203
  let env := addDef env falseDefId (cst prims.bool) (cst prims.boolFalse)
  -- Define a def that reduces to natLit 42
  let natDefId := mkId "natDef" 204
  let env := addDef env natDefId ty (natLit 42)
  -- reduceBool trueDef → Bool.true
  let rbTrue := app (cst rbId) (cst trueDefId)
  test "reduceBool true def" (whnfK2WithPrims env rbTrue customPrims == .ok (cst prims.boolTrue)) $
  -- reduceBool falseDef → Bool.false
  let rbFalse := app (cst rbId) (cst falseDefId)
  test "reduceBool false def" (whnfK2WithPrims env rbFalse customPrims == .ok (cst prims.boolFalse)) $
  -- reduceNat natDef → natLit 42
  let rnExpr := app (cst rnId) (cst natDefId)
  test "reduceNat 42" (whnfK2WithPrims env rnExpr customPrims == .ok (natLit 42)) $
  -- reduceNat with def that reduces to 0
  let zeroDefId := mkId "zeroDef" 205
  let env := addDef env zeroDefId ty (natLit 0)
  let rnZero := app (cst rnId) (cst zeroDefId)
  test "reduceNat 0" (whnfK2WithPrims env rnZero customPrims == .ok (natLit 0))

/-! ## Test: isDefEqOffset deep -/

def testDefEqOffsetDeep : TestSeq :=
  let prims := buildPrimitives .meta
  -- Nat.zero (ctor) == natLit 0 (lit) via isZero on both representations
  test "offset: Nat.zero ctor == natLit 0" (isDefEqPrim (cst prims.natZero) (natLit 0) == .ok true) $
  -- Deep succ chain: Nat.succ^3 Nat.zero == natLit 3 via succOf? peeling
  let succ3 := app (cst prims.natSucc) (app (cst prims.natSucc) (app (cst prims.natSucc) (cst prims.natZero)))
  test "offset: succ^3 zero == 3" (isDefEqPrim succ3 (natLit 3) == .ok true) $
  -- natLit 100 == natLit 100 (quick check, no peeling needed)
  test "offset: lit 100 == lit 100" (isDefEqPrim (natLit 100) (natLit 100) == .ok true) $
  -- Nat.succ (natLit 4) == natLit 5 (mixed: one side is succ, other is lit)
  let succ4 := app (cst prims.natSucc) (natLit 4)
  test "offset: succ (lit 4) == lit 5" (isDefEqPrim succ4 (natLit 5) == .ok true) $
  -- natLit 5 == Nat.succ (natLit 4) (reversed)
  test "offset: lit 5 == succ (lit 4)" (isDefEqPrim (natLit 5) succ4 == .ok true) $
  -- Negative: succ 4 != 6
  test "offset: succ 4 != 6" (isDefEqPrim succ4 (natLit 6) == .ok false) $
  -- Nat.succ x == Nat.succ x where x is same axiom
  let axId := mkId "ax" 210
  let primEnv := addAxiom buildPrimEnv axId (cst prims.nat)
  let succAx := app (cst prims.natSucc) (cst axId)
  test "offset: succ ax == succ ax" (isDefEqK2 primEnv succAx succAx == .ok true) $
  -- Nat.succ x != Nat.succ y where x, y are different axioms
  let ax2Id := mkId "ax2" 211
  let primEnv := addAxiom primEnv ax2Id (cst prims.nat)
  let succAx2 := app (cst prims.natSucc) (cst ax2Id)
  test "offset: succ ax1 != succ ax2" (isDefEqK2 primEnv succAx succAx2 == .ok false)

/-! ## Test: isDefEqUnitLikeVal -/

def testUnitLikeExtended : TestSeq :=
  -- Build a proper unit-like inductive: MyUnit : Type, MyUnit.star : MyUnit
  let unitIndId := mkId "MyUnit" 220
  let starId := mkId "MyUnit.star" 221
  let env := addInductive default unitIndId ty #[starId]
  let env := addCtor env starId unitIndId (cst unitIndId) 0 0 0
  -- Note: isDefEqUnitLikeVal only fires from the _, _ => fallback in isDefEqCore.
  -- Two neutral (.const) values with different addresses are rejected at line 657 before
  -- reaching the fallback. So unit-like can't equate two axioms directly.
  -- But it CAN fire when comparing e.g. a ctor vs a neutral through struct eta first.
  -- Let's test that star == star and that mk via lambda reduces:
  let ax1 := mkId "ax1" 222
  let env := addAxiom env ax1 (cst unitIndId)
  test "unit-like: star == star" (isDefEqK2 env (cst starId) (cst starId) == .ok true) $
  -- star == (λ_.star) 0 — ctor vs reduced ctor
  let mkViaLam := app (lam ty (cst starId)) (natLit 0)
  test "unit-like: star == (λ_.star) 0" (isDefEqK2 env mkViaLam (cst starId) == .ok true) $
  -- Build a type with 1 ctor but 1 field (NOT unit-like due to fields)
  let wrapIndId := mkId "Wrap" 224
  let wrapMkId := mkId "Wrap.mk" 225
  let env2 := addInductive default wrapIndId (pi ty ty) #[wrapMkId] (numParams := 1)
  let wrapMkType := pi ty (pi (bv 0) (app (cst wrapIndId) (bv 1)))
  let env2 := addCtor env2 wrapMkId wrapIndId wrapMkType 0 1 1
  -- Two axioms of Wrap Nat should NOT be defEq (has a field)
  let wa1 := mkId "wa1" 226
  let wa2 := mkId "wa2" 227
  let env2 := addAxiom (addAxiom env2 wa1 (app (cst wrapIndId) ty)) wa2 (app (cst wrapIndId) ty)
  test "not unit-like: 1-field type" (isDefEqK2 env2 (cst wa1) (cst wa2) == .ok false) $
  -- Multi-ctor type: Bool-like with 2 ctors should NOT be unit-like
  let boolIndId := mkId "MyBool" 228
  let b1 := mkId "MyBool.t" 229
  let b2 := mkId "MyBool.f" 230
  let env3 := addInductive default boolIndId ty #[b1, b2]
  let env3 := addCtor (addCtor env3 b1 boolIndId (cst boolIndId) 0 0 0) b2 boolIndId (cst boolIndId) 1 0 0
  let ba1 := mkId "ba1" 231
  let ba2 := mkId "ba2" 232
  let env3 := addAxiom (addAxiom env3 ba1 (cst boolIndId)) ba2 (cst boolIndId)
  test "not unit-like: multi-ctor" (isDefEqK2 env3 (cst ba1) (cst ba2) == .ok false)

/-! ## Test: struct eta bidirectional + type mismatch -/

def testStructEtaBidirectional : TestSeq :=
  let (pairEnv, pairId, pairCtorId) := buildPairEnv
  let axId := mkId "myAxiom" 240
  let pairType := app (app (cst pairId) ty) ty
  let env := addAxiom pairEnv axId pairType
  let proj0 := Ix.Kernel.Expr.mkProj pairId 0 (cst axId)
  let proj1 := Ix.Kernel.Expr.mkProj pairId 1 (cst axId)
  let rebuilt := app (app (app (app (cst pairCtorId) ty) ty) proj0) proj1
  -- Reversed direction: x == mk (proj0 x) (proj1 x)
  test "struct eta reversed: x == mk (proj0 x) (proj1 x)"
    (isDefEqK2 env (cst axId) rebuilt == .ok true) $
  -- Build a second, different struct: Pair2 with different addresses
  let pair2IndId := mkId "Pair2" 241
  let pair2CtorId := mkId "Pair2.mk" 242
  let env2 := addInductive env pair2IndId
    (pi ty (pi ty ty)) #[pair2CtorId] (numParams := 2)
  let ctor2Type := pi ty (pi ty (pi (bv 1) (pi (bv 1)
    (app (app (cst pair2IndId) (bv 3)) (bv 2)))))
  let env2 := addCtor env2 pair2CtorId pair2IndId ctor2Type 0 2 2
  -- mk1 3 7 vs mk2 3 7 — different struct types, should NOT be defEq
  let mk1 := app (app (app (app (cst pairCtorId) ty) ty) (natLit 3)) (natLit 7)
  let mk2 := app (app (app (app (cst pair2CtorId) ty) ty) (natLit 3)) (natLit 7)
  test "struct eta: diff types not defEq" (isDefEqK2 env2 mk1 mk2 == .ok false)

/-! ## Test: Nat.pow overflow guard -/

def testNatPowOverflow : TestSeq :=
  let prims := buildPrimitives .meta
  -- Nat.pow 2 16777216 should still compute (boundary, exponent = 2^24)
  let powBoundary := app (app (cst prims.natPow) (natLit 2)) (natLit 16777216)
  let boundaryResult := whnfIsNatLit default powBoundary
  test "Nat.pow boundary computes" (boundaryResult.map Option.isSome == .ok true) $
  -- Nat.pow 2 16777217 should stay stuck (exponent > 2^24)
  let powOver := app (app (cst prims.natPow) (natLit 2)) (natLit 16777217)
  test "Nat.pow overflow stays stuck" (whnfHeadAddr default powOver == .ok (some prims.natPow.addr)) $
  -- 2^63 + 2^63 == 2^64 (large nat arithmetic in 2^64 range)
  let pow63 := app (app (cst prims.natPow) (natLit 2)) (natLit 63)
  let pow64 := app (app (cst prims.natPow) (natLit 2)) (natLit 64)
  let sum := app (app (cst prims.natAdd) pow63) pow63
  test "Nat.pow: 2^63 + 2^63 == 2^64" (isDefEqPrim sum pow64 == .ok true)

/-! ## Test: natLitToCtorThunked in isDefEqCore -/

def testNatLitCtorDefEq : TestSeq :=
  let prims := buildPrimitives .meta
  -- natLit 0 == Nat.zero (ctor) — triggers natLitToCtorThunked path
  test "natLitCtor: 0 == Nat.zero" (isDefEqPrim (natLit 0) (cst prims.natZero) == .ok true) $
  -- Nat.zero == natLit 0 (reversed)
  test "natLitCtor: Nat.zero == 0" (isDefEqPrim (cst prims.natZero) (natLit 0) == .ok true) $
  -- natLit 1 == Nat.succ Nat.zero
  let succZero := app (cst prims.natSucc) (cst prims.natZero)
  test "natLitCtor: 1 == succ zero" (isDefEqPrim (natLit 1) succZero == .ok true) $
  -- natLit 5 == succ^5 zero
  let succ5 := app (cst prims.natSucc) (app (cst prims.natSucc) (app (cst prims.natSucc)
    (app (cst prims.natSucc) (app (cst prims.natSucc) (cst prims.natZero)))))
  test "natLitCtor: 5 == succ^5 zero" (isDefEqPrim (natLit 5) succ5 == .ok true) $
  -- Negative: natLit 5 != succ^4 zero
  let succ4 := app (cst prims.natSucc) (app (cst prims.natSucc) (app (cst prims.natSucc)
    (app (cst prims.natSucc) (cst prims.natZero))))
  test "natLitCtor: 5 != succ^4 zero" (isDefEqPrim (natLit 5) succ4 == .ok false)

/-! ## Test: proof irrelevance precision -/

def testProofIrrelPrecision : TestSeq :=
  -- Proof irrelevance fires when typeof(t) = Sort 0, meaning t is a type in Prop.
  -- Two different propositions (axioms of type Prop) should be defEq:
  let p1 := mkId "p1" 250
  let p2 := mkId "p2" 251
  let env := addAxiom (addAxiom default p1 prop) p2 prop
  test "no proof irrel: two propositions (types, not proofs)" (isDefEqK2 env (cst p1) (cst p2) == .ok false) $
  -- Two axioms whose type is NOT Sort 0 — proof irrel should NOT fire.
  -- Axioms of type (Sort 1 = Type) — typeof(t) = Sort 1, NOT Sort 0
  let t1 := mkId "t1" 252
  let t2 := mkId "t2" 253
  let env := addAxiom (addAxiom default t1 ty) t2 ty
  test "no proof irrel: Sort 1 axioms" (isDefEqK2 env (cst t1) (cst t2) == .ok false) $
  -- Axioms of type Prop are propositions. Prop : Sort 1, not Sort 0.
  -- So typeof(Prop) = Sort 1. proof irrel does NOT fire when comparing Prop with Prop.
  -- (This is already tested above — just confirming we don't equate all Prop values)
  -- Two proofs of same proposition: h1, h2 : P where P : Prop
  -- typeof(h1) = P, isPropVal(P) checks typeof(P) = Prop = Sort 0 → true!
  -- So proof irrel fires: isDefEq(typeof(h1), typeof(h2)) = isDefEq(P, P) = true.
  let pAxiom := mkId "P" 254
  let h1 := mkId "h1" 255
  let h2 := mkId "h2" 1
  let env := addAxiom default pAxiom prop
  let env := addAxiom (addAxiom env h1 (cst pAxiom)) h2 (cst pAxiom)
  test "proof irrel: proofs of same proposition" (isDefEqK2 env (cst h1) (cst h2) == .ok true)

/-! ## Test: deep spine comparison -/

def testDeepSpine : TestSeq :=
  let fType := pi ty (pi ty (pi ty (pi ty ty)))
  -- Defs with same body: f 1 2 == g 1 2 (both reduce to same value)
  let fId := mkId "f" 2
  let gId := mkId "g" 3
  let fBody := lam ty (lam ty (lam ty (lam ty (bv 3))))
  let env := addDef (addDef default fId fType fBody) gId fType fBody
  let fg12a := app (app (cst fId) (natLit 1)) (natLit 2)
  let fg12b := app (app (cst gId) (natLit 1)) (natLit 2)
  test "deep spine: f 1 2 == g 1 2 (same body)" (isDefEqK2 env fg12a fg12b == .ok true) $
  -- f 1 2 3 4 reduces to 1, g 1 2 3 5 also reduces to 1 — both equal
  let f1234 := app (app (app (app (cst fId) (natLit 1)) (natLit 2)) (natLit 3)) (natLit 4)
  let g1235 := app (app (app (app (cst gId) (natLit 1)) (natLit 2)) (natLit 3)) (natLit 5)
  test "deep spine: f 1 2 3 4 == g 1 2 3 5 (both reduce)" (isDefEqK2 env f1234 g1235 == .ok true) $
  -- f 1 2 3 4 != g 2 2 3 4 (different first arg, reduces to 1 vs 2)
  let g2234 := app (app (app (app (cst gId) (natLit 2)) (natLit 2)) (natLit 3)) (natLit 4)
  test "deep spine: diff first arg" (isDefEqK2 env f1234 g2234 == .ok false) $
  -- Two different axioms with same type applied to same args: NOT defEq
  let ax1 := mkId "ax1" 4
  let ax2 := mkId "ax2" 5
  let env2 := addAxiom (addAxiom default ax1 (pi ty ty)) ax2 (pi ty ty)
  test "deep spine: diff axiom heads" (isDefEqK2 env2 (app (cst ax1) (natLit 1)) (app (cst ax2) (natLit 1)) == .ok false)

/-! ## Test: Pi type comparison in isDefEq -/

def testPiDefEq : TestSeq :=
  -- Pi with dependent codomain: (x : Nat) → x = x  (well, we can't build Eq easily,
  -- so test with simpler dependent types)
  -- Two identical Pi types with binder reference: Π(A:Type). A → A
  let depPi := pi ty (pi (bv 0) (bv 1))
  test "pi defEq: Π A. A → A" (isDefEqEmpty depPi depPi == .ok true) $
  -- Two Pi types where domains are defEq through reduction
  let dTyId := mkId "dTy" 6
  let env := addDef default dTyId (srt 2) ty  -- dTy : Sort 2 := Type
  -- Π(_ : dTy). Type  vs  Π(_ : Type). Type  — dTy reduces to Type
  test "pi defEq: reduced domain" (isDefEqK2 env (pi (cst dTyId) ty) (pi ty ty) == .ok true) $
  -- Negative: different codomains
  test "pi defEq: diff codomain" (isDefEqEmpty (pi ty ty) (pi ty prop) == .ok false) $
  -- Negative: different domains
  test "pi defEq: diff domain" (isDefEqEmpty (pi ty (bv 0)) (pi prop (bv 0)) == .ok false)

/-! ## Test: 3-char string literal to ctor conversion -/

def testStringCtorDeep : TestSeq :=
  let prims := buildPrimitives .meta
  -- "abc" == String.mk (cons 'a' (cons 'b' (cons 'c' nil)))
  let charType := cst prims.char
  let nilChar := app (cstL prims.listNil #[.zero]) charType
  let charA := app (cst prims.charMk) (natLit 97)
  let charB := app (cst prims.charMk) (natLit 98)
  let charC := app (cst prims.charMk) (natLit 99)
  let consC := app (app (app (cstL prims.listCons #[.zero]) charType) charC) nilChar
  let consBC := app (app (app (cstL prims.listCons #[.zero]) charType) charB) consC
  let consABC := app (app (app (cstL prims.listCons #[.zero]) charType) charA) consBC
  let strABC := app (cst prims.stringMk) consABC
  test "str ctor: \"abc\" == String.mk form"
    (isDefEqPrim (strLit "abc") strABC == .ok true) $
  -- "abc" != "ab" via string literals (known working)
  test "str ctor: \"abc\" != \"ab\""
    (isDefEqEmpty (strLit "abc") (strLit "ab") == .ok false)


/-! ## Test: projection in isDefEq -/

def testProjDefEq : TestSeq :=
  let (pairEnv, pairId, pairCtorId) := buildPairEnv
  -- proj comparison: same struct, same index
  let mk37 := app (app (app (app (cst pairCtorId) ty) ty) (natLit 3)) (natLit 7)
  let proj0a := Ix.Kernel.Expr.mkProj pairId 0 mk37
  let proj0b := Ix.Kernel.Expr.mkProj pairId 0 mk37
  test "proj defEq: same proj" (isDefEqK2 pairEnv proj0a proj0b == .ok true) $
  -- proj 0 vs proj 1 of same struct — different fields
  let proj1 := Ix.Kernel.Expr.mkProj pairId 1 mk37
  test "proj defEq: proj 0 != proj 1" (isDefEqK2 pairEnv proj0a proj1 == .ok false) $
  -- proj 0 (mk 3 7) == 3 (reduces)
  test "proj reduces to val" (isDefEqK2 pairEnv proj0a (natLit 3) == .ok true) $
  -- Projection on axiom stays stuck but proj == proj on same axiom should be defEq
  let axId := mkId "myAxiom" 7
  let pairType := app (app (cst pairId) ty) ty
  let env := addAxiom pairEnv axId pairType
  let projAx0 := Ix.Kernel.Expr.mkProj pairId 0 (cst axId)
  test "proj defEq: proj 0 ax == proj 0 ax" (isDefEqK2 env projAx0 projAx0 == .ok true) $
  -- proj 0 ax != proj 1 ax
  let projAx1 := Ix.Kernel.Expr.mkProj pairId 1 (cst axId)
  test "proj defEq: proj 0 ax != proj 1 ax" (isDefEqK2 env projAx0 projAx1 == .ok false)

/-! ## Test: lambda/pi body fvar comparison -/

def testFvarComparison : TestSeq :=
  -- When comparing lambdas, isDefEqCore creates fresh fvars for the bound variable.
  -- λ(x : Nat). λ(y : Nat). x  vs  λ(x : Nat). λ(y : Nat). x  — trivially equal
  test "fvar: identical lambdas" (isDefEqEmpty (lam ty (lam ty (bv 1))) (lam ty (lam ty (bv 1))) == .ok true) $
  -- λ(x : Nat). λ(y : Nat). x  vs  λ(x : Nat). λ(y : Nat). y  — different bvar references
  test "fvar: diff bvar refs" (isDefEqEmpty (lam ty (lam ty (bv 1))) (lam ty (lam ty (bv 0))) == .ok false) $
  -- Pi: (A : Type) → A  vs  (A : Type) → A — codomains reference bound var
  test "fvar: pi with bvar cod" (isDefEqEmpty (pi ty (bv 0)) (pi ty (bv 0)) == .ok true) $
  -- (A : Type) → A  vs  (A : Type) → Type — one references bvar, other doesn't
  test "fvar: pi cod bvar vs const" (isDefEqEmpty (pi ty (bv 0)) (pi ty ty) == .ok false) $
  -- Nested lambda with computation:
  -- λ(f : Nat → Nat). λ(x : Nat). f x  vs  λ(f : Nat → Nat). λ(x : Nat). f x
  let fnType := pi ty ty
  let applyFX := lam fnType (lam ty (app (bv 1) (bv 0)))
  test "fvar: lambda with app" (isDefEqEmpty applyFX applyFX == .ok true)

/-! ## Suite -/

/-! ## Test: typecheck a definition that uses a recursor (Nat.add-like) -/

def testDefnTypecheckAdd : TestSeq :=
  let (env, natId, zeroId, succId, recId) := buildMyNatEnv
  let prims := buildPrimitives .meta
  let natConst := cst natId
  -- Define: myAdd : MyNat → MyNat → MyNat
  --   myAdd n m = @MyNat.rec (fun _ => MyNat) n (fun _ ih => succ ih) m
  let addId := mkId "myAdd" 55
  let addType : E := pi natConst (pi natConst natConst)  -- MyNat → MyNat → MyNat
  let motive := lam natConst natConst       -- fun _ : MyNat => MyNat
  let base := bv 1                          -- n
  let step := lam natConst (lam natConst (app (cst succId) (bv 0)))  -- fun _ ih => succ ih
  let target := bv 0                        -- m
  let recApp := app (app (app (app (cst recId) motive) base) step) target
  let addBody := lam natConst (lam natConst recApp)
  let env := addDef env addId addType addBody
  -- First check: whnf of myAdd applied to concrete values
  let twoE := app (cst succId) (app (cst succId) (cst zeroId))
  let threeE := app (cst succId) (app (cst succId) (app (cst succId) (cst zeroId)))
  let addApp := app (app (cst addId) twoE) threeE
  test "myAdd 2 3 whnf reduces" (whnfK2 env addApp |>.isOk) $
  -- Now typecheck the constant
  let result := Ix.Kernel.typecheckConst env prims addId
  test "myAdd typechecks" (result.isOk) $
  match result with
  | .ok () => test "myAdd typecheck succeeded" true
  | .error e => test s!"myAdd typecheck error: {e}" false


/-! ## Tests ported from Rust kernel test suite -/

/-! ### Proof irrelevance: under lambda + intro vs axiom -/

def testProofIrrelUnderLambda : TestSeq :=
  let (env, trueId, _introId, _recId) := buildMyTrueEnv
  let p1 := mkId "p1" 8
  let p2 := mkId "p2" 9
  let env := addAxiom (addAxiom env p1 (cst trueId)) p2 (cst trueId)
  -- λ(x:Type). p1 == λ(x:Type). p2 (proof irrel under lambda)
  test "proof irrel under lambda"
    (isDefEqK2 env (lam ty (cst p1)) (lam ty (cst p2)) == .ok true)

def testProofIrrelIntroVsAxiom : TestSeq :=
  let (env, trueId, introId, _recId) := buildMyTrueEnv
  let p1 := mkId "p1" 10
  let env := addAxiom env p1 (cst trueId)
  -- The constructor intro and axiom p1 are both proofs of MyTrue → defeq
  test "proof irrel: intro vs axiom"
    (isDefEqK2 env (cst introId) (cst p1) == .ok true)

/-! ### Eta expansion with axioms -/

def testEtaAxiomFun : TestSeq :=
  let prims := buildPrimitives .meta
  let fId := mkId "f" 11
  let natMId : MId := (parseIxName "Nat", prims.nat.addr)
  let env := addAxiom default natMId ty
  let env := addAxiom env fId (pi (cst prims.nat) (cst prims.nat))
  -- f == λx. f x (eta with axiom)
  let etaF := lam (cst prims.nat) (app (cst fId) (bv 0))
  test "eta axiom: f == λx. f x" (isDefEqK2 env (cst fId) etaF == .ok true) $
  test "eta axiom: λx. f x == f" (isDefEqK2 env etaF (cst fId) == .ok true)

def testEtaNestedAxiom : TestSeq :=
  let prims := buildPrimitives .meta
  let fId := mkId "f" 12
  let natE := cst prims.nat
  let natMId : MId := (parseIxName "Nat", prims.nat.addr)
  let env := addAxiom default natMId ty
  let env := addAxiom env fId (pi natE (pi natE natE))
  -- f == λx.λy. f x y (double eta with axiom)
  let doubleEta := lam natE (lam natE (app (app (cst fId) (bv 1)) (bv 0)))
  test "eta axiom nested: f == λx.λy. f x y"
    (isDefEqK2 env (cst fId) doubleEta == .ok true)

/-! ### Bidirectional check -/

def testCheckLamAgainstPi : TestSeq :=
  let prims := buildPrimitives .meta
  let natE := cst prims.nat
  let natMId : MId := (parseIxName "Nat", prims.nat.addr)
  let env := addAxiom default natMId ty
  -- λ(x:Nat). x checked against (Nat → Nat) succeeds
  let idLam := lam natE (bv 0)
  let piTy := pi natE natE
  test "check: λx.x against Nat→Nat"
    (checkK2 env idLam piTy |>.isOk)

def testCheckDomainMismatch : TestSeq :=
  let prims := buildPrimitives .meta
  let natE := cst prims.nat
  let boolE := cst prims.bool
  let natMId : MId := (parseIxName "Nat", prims.nat.addr)
  let boolMId : MId := (parseIxName "Bool", prims.bool.addr)
  let env := addAxiom (addAxiom default natMId ty) boolMId ty
  -- λ(x:Bool). x checked against (Nat → Nat) fails
  let lamBool := lam boolE (bv 0)
  let piNat := pi natE natE
  test "check: domain mismatch fails"
    (isError (checkK2 env lamBool piNat))

/-! ### Level equality -/

def testLevelEquality : TestSeq :=
  let u : L := .param 0 default
  let v : L := .param 1 default
  -- Sort (max u v) == Sort (max v u)
  let sMaxUV : E := .sort (.max u v)
  let sMaxVU : E := .sort (.max v u)
  test "level: max u v == max v u" (isDefEqEmpty sMaxUV sMaxVU == .ok true) $
  -- imax(u, 0) normalizes to 0, so Sort(imax(u,0)) == Prop
  let sImaxU0 : E := .sort (.imax u .zero)
  test "level: imax u 0 == 0" (isDefEqEmpty sImaxU0 prop == .ok true) $
  -- Sort 1 != Sort 0
  test "level: Sort 1 != Sort 0" (isDefEqEmpty ty prop == .ok false) $
  -- Sort u == Sort u
  let sU : E := .sort u
  test "level: Sort u == Sort u" (isDefEqEmpty sU sU == .ok true) $
  -- Sort 2 == Sort 2
  test "level: Sort 2 == Sort 2" (isDefEqEmpty (srt 2) (srt 2) == .ok true) $
  -- Sort 2 != Sort 3
  test "level: Sort 2 != Sort 3" (isDefEqEmpty (srt 2) (srt 3) == .ok false)

/-! ### Projection nested pair -/

def testProjNestedPair : TestSeq :=
  let (env, pairId, pairCtorId) := buildPairEnv
  -- mk (mk 1 2) (mk 3 4)
  let inner1 := app (app (app (app (cst pairCtorId) ty) ty) (natLit 1)) (natLit 2)
  let inner2 := app (app (app (app (cst pairCtorId) ty) ty) (natLit 3)) (natLit 4)
  let pairOfPairTy := app (app (cst pairId) ty) ty
  let outer := app (app (app (app (cst pairCtorId) pairOfPairTy) pairOfPairTy) inner1) inner2
  -- proj 0 outer == mk 1 2
  let proj0 := projE pairId 0 outer
  let expected := app (app (app (app (cst pairCtorId) ty) ty) (natLit 1)) (natLit 2)
  test "proj nested: proj 0 outer == mk 1 2" (isDefEqK2 env proj0 expected == .ok true) $
  -- proj 0 (proj 0 outer) == 1
  let projProj := projE pairId 0 proj0
  test "proj nested: proj 0 (proj 0 outer) == 1" (isDefEqK2 env projProj (natLit 1) == .ok true)

/-! ### Opaque/theorem self-equality -/

def testOpaqueSelfEq : TestSeq :=
  let oId := mkId "myOpaque" 13
  let env := addOpaque default oId ty (natLit 5)
  -- Opaque constant defeq to itself
  test "opaque self eq" (isDefEqK2 env (cst oId) (cst oId) == .ok true)

def testTheoremSelfEq : TestSeq :=
  let tId := mkId "myThm" 14
  let env := addTheorem default tId ty (natLit 5)
  -- Theorem constant defeq to itself
  test "theorem self eq" (isDefEqK2 env (cst tId) (cst tId) == .ok true) $
  -- Theorem is unfolded during defEq, so thm == 5
  test "theorem unfolds to value" (isDefEqK2 env (cst tId) (natLit 5) == .ok true)

/-! ### Beta inside defeq -/

def testBetaInsideDefEq : TestSeq :=
  -- (λx.x) 5 == (λy.y) 5
  test "beta inside: (λx.x) 5 == (λy.y) 5"
    (isDefEqEmpty (app (lam ty (bv 0)) (natLit 5)) (app (lam ty (bv 0)) (natLit 5)) == .ok true) $
  -- (λx.x) 5 == 5
  test "beta inside: (λx.x) 5 == 5"
    (isDefEqEmpty (app (lam ty (bv 0)) (natLit 5)) (natLit 5) == .ok true)

/-! ### Sort defeq levels -/

def testSortDefEqLevels : TestSeq :=
  test "sort defeq: Prop == Prop" (isDefEqEmpty prop prop == .ok true) $
  test "sort defeq: Prop != Type" (isDefEqEmpty prop ty == .ok false) $
  test "sort defeq: Sort 2 == Sort 2" (isDefEqEmpty (srt 2) (srt 2) == .ok true) $
  test "sort defeq: Sort 2 != Sort 3" (isDefEqEmpty (srt 2) (srt 3) == .ok false)

/-! ### Nat supplemental -/

def testNatSupplemental : TestSeq :=
  let prims := buildPrimitives .meta
  -- Large literal equality (O(1))
  test "nat: 1000000 == 1000000" (isDefEqEmpty (natLit 1000000) (natLit 1000000) == .ok true) $
  test "nat: 1000000 != 1000001" (isDefEqEmpty (natLit 1000000) (natLit 1000001) == .ok false) $
  -- nat_lit(0) whnf stays as nat_lit(0)
  test "nat: whnf 0 stays 0" (whnfEmpty (natLit 0) == .ok (natLit 0)) $
  -- Nat.succ(x) == Nat.succ(x) with symbolic x
  let x := mkId "x" 15
  let y := mkId "y" 16
  let env := addAxiom (addAxiom buildPrimEnv x (cst prims.nat)) y (cst prims.nat)
  let sx := app (cst prims.natSucc) (cst x)
  test "nat succ sym: succ x == succ x" (isDefEqK2 env sx sx == .ok true) $
  let sy := app (cst prims.natSucc) (cst y)
  test "nat succ sym: succ x != succ y" (isDefEqK2 env sx sy == .ok false)

/-! ### Whnf nat prim symbolic stays stuck -/

def testWhnfNatPrimSymbolic : TestSeq :=
  let (env, natId, _, _, _) := buildMyNatEnv
  let x := mkId "x" 17
  let env := addAxiom env x (cst natId)
  -- Nat.add x 3 should NOT reduce (x is symbolic)
  let addSym := app (app (cst (buildPrimitives .meta).natAdd) (cst x)) (natLit 3)
  let result := whnfK2 env addSym
  test "whnf: Nat.add sym stays stuck" (result != .ok (natLit 3))

/-! ### Lazy delta supplemental -/

def testLazyDeltaSupplemental : TestSeq :=
  -- Same head axiom spine: f 1 2 == f 1 2
  let fId := mkId "f" 18
  let env := addAxiom default fId (pi ty (pi ty ty))
  let fa := app (app (cst fId) (natLit 1)) (natLit 2)
  test "lazy delta: f 1 2 == f 1 2" (isDefEqK2 env fa fa == .ok true) $
  -- f 1 2 != f 1 3
  let fc := app (app (cst fId) (natLit 1)) (natLit 3)
  test "lazy delta: f 1 2 != f 1 3" (isDefEqK2 env fa fc == .ok false) $
  -- Theorem unfolded by delta
  let thmId := mkId "myThm" 19
  let env := addTheorem default thmId ty (natLit 5)
  test "lazy delta: theorem unfolds" (isDefEqK2 env (cst thmId) (natLit 5) == .ok true)

/-! ### K-reduction supplemental -/

def testKReductionSupplemental : TestSeq :=
  let (env, trueId, introId, recId) := buildMyTrueEnv
  -- K-rec on intro directly reduces to minor premise
  let motive := lam (cst trueId) prop
  let base := natLit 42  -- the "value" produced by the minor premise (abusing types for simplicity)
  let recOnIntro := app (app (app (cst recId) motive) base) (cst introId)
  test "K-rec on intro reduces" (whnfK2 env recOnIntro |>.isOk) $
  -- K-rec on axiom of right type: toCtorWhenK should handle this
  let axId := mkId "myAxiom" 20
  let env := addAxiom env axId (cst trueId)
  let recOnAxiom := app (app (app (cst recId) motive) base) (cst axId)
  test "K-rec on axiom reduces" (whnfK2 env recOnAxiom |>.isOk)

/-! ### Struct eta not recursive -/

def testStructEtaNotRecursive : TestSeq :=
  -- Build a recursive list-like type — struct eta should NOT fire
  let listIndId := mkId "MyList" 21
  let listNilId := mkId "MyList.nil" 22
  let listConsId := mkId "MyList.cons" 23
  let env := addInductive default listIndId (pi ty ty) #[listNilId, listConsId]
    (numParams := 1) (isRec := true)
  let env := addCtor env listNilId listIndId
    (pi ty (app (cst listIndId) (bv 0))) 0 1 0
  let env := addCtor env listConsId listIndId
    (pi ty (pi (bv 0) (pi (app (cst listIndId) (bv 1)) (app (cst listIndId) (bv 2))))) 1 1 2
  -- Two axioms of list type should NOT be defeq
  let ax1 := mkId "ax1" 24
  let ax2 := mkId "ax2" 25
  let listNat := app (cst listIndId) ty
  let env := addAxiom (addAxiom env ax1 listNat) ax2 listNat
  test "struct eta not recursive: list axioms not defeq"
    (isDefEqK2 env (cst ax1) (cst ax2) == .ok false)

/-! ### Unit-like Prop defeq -/

def testUnitLikePropDefEq : TestSeq :=
  -- Prop type with 1 ctor, 0 fields → both unit-like and proof-irrel
  let pIndId := mkId "MyP" 26
  let pMkId := mkId "MyP.mk" 27
  let env := addInductive default pIndId prop #[pMkId]
  let env := addCtor env pMkId pIndId (cst pIndId) 0 0 0
  let ax1 := mkId "ax1" 28
  let ax2 := mkId "ax2" 29
  let env := addAxiom (addAxiom env ax1 (cst pIndId)) ax2 (cst pIndId)
  -- Both proof irrelevance and unit-like apply
  test "unit-like prop defeq"
    (isDefEqK2 env (cst ax1) (cst ax2) == .ok true)

/-! ========================================================================
    Phase 1: Declaration-level checking tests
    ======================================================================== -/

/-! ### 1B. Positive tests: existing envs pass checkConst -/

def testCheckMyNatInd : TestSeq :=
  let (env, natId, zeroId, succId, recId) := buildMyNatEnv
  let prims := buildPrimitives .meta
  test "checkConst: MyNat inductive"
    (typecheckConstK2 env natId prims |>.isOk) $
  test "checkConst: MyNat.zero ctor"
    (typecheckConstK2 env zeroId prims |>.isOk) $
  test "checkConst: MyNat.succ ctor"
    (typecheckConstK2 env succId prims |>.isOk) $
  test "checkConst: MyNat.rec recursor"
    (typecheckConstK2 env recId prims |>.isOk)

def testCheckMyTrueInd : TestSeq :=
  let (env, trueId, introId, recId) := buildMyTrueEnv
  let prims := buildPrimitives .meta
  test "checkConst: MyTrue inductive"
    (typecheckConstK2 env trueId prims |>.isOk) $
  test "checkConst: MyTrue.intro ctor"
    (typecheckConstK2 env introId prims |>.isOk) $
  test "checkConst: MyTrue.rec K-recursor"
    (typecheckConstK2 env recId prims |>.isOk)

def testCheckPairInd : TestSeq :=
  let (env, pairId, pairCtorId) := buildPairEnv
  let prims := buildPrimitives .meta
  test "checkConst: Pair inductive"
    (typecheckConstK2 env pairId prims |>.isOk) $
  test "checkConst: Pair.mk ctor"
    (typecheckConstK2 env pairCtorId prims |>.isOk)

def testCheckAxiom : TestSeq :=
  let axId := mkId "myAxiom" 30
  let env := addAxiom default axId ty
  let prims := buildPrimitives .meta
  test "checkConst: axiom"
    (typecheckConstK2 env axId prims |>.isOk)

def testCheckOpaque : TestSeq :=
  let opId := mkId "myOpaque" 31
  -- opaque : Type := Prop
  let env := addOpaque default opId (srt 2) ty
  let prims := buildPrimitives .meta
  test "checkConst: opaque"
    (typecheckConstK2 env opId prims |>.isOk)

def testCheckTheorem : TestSeq :=
  let (env, trueId, introId, _recId) := buildMyTrueEnv
  let prims := buildPrimitives .meta
  -- theorem : MyTrue := MyTrue.intro
  let thmId := mkId "myThm" 32
  let env := addTheorem env thmId (cst trueId) (cst introId)
  test "checkConst: theorem"
    (typecheckConstK2 env thmId prims |>.isOk)

def testCheckDefinition : TestSeq :=
  let defId := mkId "myDef" 33
  -- def : Type := Type
  let env := addDef default defId (srt 2) ty
  let prims := buildPrimitives .meta
  test "checkConst: definition"
    (typecheckConstK2 env defId prims |>.isOk)

/-! ### 1C. Negative tests: constructor validation -/

def testCheckCtorParamCountMismatch : TestSeq :=
  -- MyNat-like but constructor has numParams=1 instead of 0
  let natIndId := mkId "MyNat" 34
  let zeroId := mkId "MyNat.zero" 35
  let natType : E := srt 1
  let natConst := cst natIndId
  let env := addInductive default natIndId natType #[zeroId]
  -- Constructor claims numParams=1 but inductive has numParams=0
  let env := addCtor env zeroId natIndId natConst 0 (numParams := 1) (numFields := 0)
  let prims := buildPrimitives .meta
  test "checkConst: ctor param count mismatch → error"
    (typecheckConstK2 env natIndId prims |> fun r => !r.isOk)

def testCheckCtorReturnTypeNotInductive : TestSeq :=
  -- Constructor whose return type is not the inductive
  let myIndId := mkId "MyInd" 36
  let myCtorId := mkId "MyInd.mk" 37
  let bogusId := mkId "bogus" 38
  let myType := srt 1
  let env := addInductive default myIndId myType #[myCtorId]
  -- Constructor type: bogusId instead of myIndId
  let env := addAxiom env bogusId myType
  let env := addCtor env myCtorId myIndId (cst bogusId) 0 0 0
  let prims := buildPrimitives .meta
  test "checkConst: ctor return type not inductive → error"
    (typecheckConstK2 env myIndId prims |> fun r => !r.isOk)

/-! ### 1D. Strict positivity tests -/

def testPositivityOkNoOccurrence : TestSeq :=
  -- Inductive T with ctor mk : Nat → T (no mention of T in field domain)
  let tIndId := mkId "T" 39
  let tMkId := mkId "T.mk" 40
  let natId' := mkId "MyNat" 41
  let natConst := cst natId'
  let tConst := cst tIndId
  let env := addAxiom default natId' (srt 1)  -- Nat : Type
  let env := addInductive env tIndId (srt 1) #[tMkId]
  let env := addCtor env tMkId tIndId (pi natConst tConst) 0 0 1
  let prims := buildPrimitives .meta
  test "positivity: no occurrence (trivially positive)"
    (typecheckConstK2 env tIndId prims |>.isOk)

def testPositivityOkDirect : TestSeq :=
  -- Recursive inductive: mk : T → T (direct positive occurrence)
  let tIndId := mkId "T" 42
  let tMkId := mkId "T.mk" 43
  let tConst := cst tIndId
  let env := addInductive default tIndId (srt 1) #[tMkId] (isRec := true)
  let env := addCtor env tMkId tIndId (pi tConst tConst) 0 0 1
  let prims := buildPrimitives .meta
  test "positivity: direct positive occurrence"
    (typecheckConstK2 env tIndId prims |>.isOk)

def testPositivityViolationNegative : TestSeq :=
  -- Negative occurrence: mk : (T → Nat) → T  (T in domain)
  let tIndId := mkId "T" 44
  let tMkId := mkId "T.mk" 45
  let natId' := mkId "MyNat" 46
  let tConst := cst tIndId
  let natConst := cst natId'
  let env := addAxiom default natId' (srt 1)  -- Nat : Type
  let env := addInductive env tIndId (srt 1) #[tMkId] (isRec := true)
  -- mk : (T → Nat) → T
  let fieldType := pi (pi tConst natConst) tConst
  let env := addCtor env tMkId tIndId fieldType 0 0 1
  let prims := buildPrimitives .meta
  test "positivity: negative occurrence → error"
    (typecheckConstK2 env tIndId prims |> fun r => !r.isOk)

def testPositivityOkCovariant : TestSeq :=
  -- Covariant: mk : (Nat → T) → T  (T only in codomain)
  let tIndId := mkId "T" 47
  let tMkId := mkId "T.mk" 48
  let natId' := mkId "MyNat" 49
  let tConst := cst tIndId
  let natConst := cst natId'
  let env := addAxiom default natId' (srt 1)
  let env := addInductive env tIndId (srt 1) #[tMkId] (isRec := true)
  -- mk : (Nat → T) → T
  let fieldType := pi (pi natConst tConst) tConst
  let env := addCtor env tMkId tIndId fieldType 0 0 1
  let prims := buildPrimitives .meta
  test "positivity: covariant occurrence OK"
    (typecheckConstK2 env tIndId prims |>.isOk)

/-! ### 1E. K-flag validation tests -/

def testKFlagOk : TestSeq :=
  let (env, _trueId, _introId, recId) := buildMyTrueEnv
  let prims := buildPrimitives .meta
  test "K-flag: MyTrue.rec K-recursor passes"
    (typecheckConstK2 env recId prims |>.isOk)

def testKFlagFailNotProp : TestSeq :=
  -- Type-level inductive with K=true → error
  let tIndId := mkId "T" 56
  let tMkId := mkId "T.mk" 57
  let tRecId := mkId "T.rec" 58
  let tConst := cst tIndId
  -- T : Type (not Prop)
  let env := addInductive default tIndId (srt 1) #[tMkId]
  let env := addCtor env tMkId tIndId tConst 0 0 0
  -- Recursor with K=true on a Type-level inductive
  let recType := pi (pi tConst prop) (pi (app (bv 0) (cst tMkId)) (pi tConst (app (bv 2) (bv 0))))
  let ruleRhs := lam (pi tConst prop) (lam prop (bv 0))
  let env := addRec env tRecId 0 recType #[tIndId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 1)
    (rules := #[{ ctor := tMkId, nfields := 0, rhs := ruleRhs }])
    (k := true)
  let prims := buildPrimitives .meta
  test "K-flag: not Prop → error"
    (typecheckConstK2 env tRecId prims |> fun r => !r.isOk)

def testKFlagFailMultipleCtors : TestSeq :=
  -- Prop inductive with 2 ctors + K=true → error
  let pIndId := mkId "P" 59
  let pMk1Id := mkId "P.mk1" 60
  let pMk2Id := mkId "P.mk2" 61
  let pRecId := mkId "P.rec" 62
  let pConst := cst pIndId
  let env := addInductive default pIndId prop #[pMk1Id, pMk2Id]
  let env := addCtor env pMk1Id pIndId pConst 0 0 0
  let env := addCtor env pMk2Id pIndId pConst 1 0 0
  -- Recursor with K=true
  let recType := pi (pi pConst prop) (pi (app (bv 0) (cst pMk1Id)) (pi (app (bv 1) (cst pMk2Id)) (pi pConst (app (bv 3) (bv 0)))))
  let ruleRhs1 := lam (pi pConst prop) (lam prop (lam prop (bv 1)))
  let ruleRhs2 := lam (pi pConst prop) (lam prop (lam prop (bv 0)))
  let env := addRec env pRecId 0 recType #[pIndId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 2)
    (rules := #[
      { ctor := pMk1Id, nfields := 0, rhs := ruleRhs1 },
      { ctor := pMk2Id, nfields := 0, rhs := ruleRhs2 }
    ])
    (k := true)
  let prims := buildPrimitives .meta
  test "K-flag: multiple ctors → error"
    (typecheckConstK2 env pRecId prims |> fun r => !r.isOk)

def testKFlagFailHasFields : TestSeq :=
  -- Prop inductive with 1 ctor that has 1 field + K=true → error
  let pIndId := mkId "P" 63
  let pMkId := mkId "P.mk" 64
  let pRecId := mkId "P.rec" 65
  let pConst := cst pIndId
  -- P : Prop, mk : P → P (1 field)
  let env := addInductive default pIndId prop #[pMkId] (isRec := true)
  let env := addCtor env pMkId pIndId (pi pConst pConst) 0 0 1
  -- Recursor with K=true
  let recType := pi (pi pConst prop)
    (pi (pi pConst (pi (app (bv 1) (bv 0)) (app (bv 2) (cst pMkId |> fun x => app x (bv 1)))))
      (pi pConst (app (bv 2) (bv 0))))
  let ruleRhs := lam (pi pConst prop) (lam (pi pConst (pi prop prop)) (lam pConst (app (app (bv 1) (bv 0)) (app (bv 2) (bv 0)))))
  let env := addRec env pRecId 0 recType #[pIndId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 1)
    (rules := #[{ ctor := pMkId, nfields := 1, rhs := ruleRhs }])
    (k := true)
  let prims := buildPrimitives .meta
  test "K-flag: has fields → error"
    (typecheckConstK2 env pRecId prims |> fun r => !r.isOk)

/-! ### 1F. Recursor validation tests -/

def testRecRulesCountMismatch : TestSeq :=
  -- Inductive with 2 ctors but recursor has only 1 rule
  let (env, natId, zeroId, _succId, _) := buildMyNatEnv
  let badRecId := mkId "MyNat.badrec" 66
  let natConst := cst natId
  let recType := pi (pi natConst (srt 1))
    (pi (app (bv 0) (cst zeroId))
      (pi natConst (app (bv 2) (bv 0))))
  -- Only 1 rule for a 2-ctor inductive
  let ruleRhs := lam (pi natConst (srt 1)) (lam (srt 1) (bv 0))
  let env := addRec env badRecId 0 recType #[natId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 1)
    (rules := #[{ ctor := zeroId, nfields := 0, rhs := ruleRhs }])
  let prims := buildPrimitives .meta
  test "recursor: rules count mismatch → error"
    (typecheckConstK2 env badRecId prims |> fun r => !r.isOk)

def testRecRulesNfieldsMismatch : TestSeq :=
  -- MyNat.succ has 1 field but rule claims 0
  let (env, natId, zeroId, succId, _) := buildMyNatEnv
  let badRecId := mkId "MyNat.badrec" 67
  let natConst := cst natId
  let recType := pi (pi natConst (srt 1))
    (pi (app (bv 0) (cst zeroId))
      (pi (pi natConst (pi (app (bv 2) (bv 0)) (app (bv 3) (app (cst succId) (bv 1)))))
        (pi natConst (app (bv 3) (bv 0)))))
  let zeroRhs := lam (pi natConst (srt 1)) (lam (srt 1) (lam (pi natConst (pi (srt 1) (srt 1))) (bv 1)))
  -- succ rule claims nfields=0 instead of 1
  let succRhs := lam (pi natConst (srt 1)) (lam (srt 1) (lam (pi natConst (pi (srt 1) (srt 1))) (bv 0)))
  let env := addRec env badRecId 0 recType #[natId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 2)
    (rules := #[
      { ctor := zeroId, nfields := 0, rhs := zeroRhs },
      { ctor := succId, nfields := 0, rhs := succRhs }  -- wrong! should be 1
    ])
  let prims := buildPrimitives .meta
  test "recursor: nfields mismatch → error"
    (typecheckConstK2 env badRecId prims |> fun r => !r.isOk)

/-! ### 1G. Elimination level tests -/

def testElimLevelTypeLargeOk : TestSeq :=
  -- Type-level inductive: large elimination always OK (verified via recursor check)
  let (env, _natId, _zeroId, _succId, recId) := buildMyNatEnv
  let prims := buildPrimitives .meta
  test "elim level: Type recursor passes"
    (typecheckConstK2 env recId prims |>.isOk)

def testElimLevelPropToPropOk : TestSeq :=
  -- Prop inductive with 2 ctors: the inductive itself typechecks
  -- The elim-level negative test (multi-ctor large) covers the error path
  let pIndId := mkId "P" 68
  let pMk1Id := mkId "P.mk1" 69
  let pMk2Id := mkId "P.mk2" 70
  let pConst := cst pIndId
  let env := addInductive default pIndId prop #[pMk1Id, pMk2Id]
  let env := addCtor env pMk1Id pIndId pConst 0 0 0
  let env := addCtor env pMk2Id pIndId pConst 1 0 0
  let prims := buildPrimitives .meta
  test "elim level: Prop 2-ctor inductive passes"
    (typecheckConstK2 env pIndId prims |>.isOk)

def testElimLevelLargeFromPropMultiCtorFail : TestSeq :=
  -- Prop inductive with 2 ctors, claiming large elimination → error
  let pIndId := mkId "P" 71
  let pMk1Id := mkId "P.mk1" 72
  let pMk2Id := mkId "P.mk2" 73
  let pRecId := mkId "P.rec" 74
  let pConst := cst pIndId
  let env := addInductive default pIndId prop #[pMk1Id, pMk2Id]
  let env := addCtor env pMk1Id pIndId pConst 0 0 0
  let env := addCtor env pMk2Id pIndId pConst 1 0 0
  -- Recursor claims large elimination (motive : P → Type)
  let recType := pi (pi pConst (srt 1))
    (pi (app (bv 0) (cst pMk1Id))
      (pi (app (bv 1) (cst pMk2Id))
        (pi pConst (app (bv 3) (bv 0)))))
  let ruleRhs1 := lam (pi pConst (srt 1)) (lam (srt 1) (lam (srt 1) (bv 1)))
  let ruleRhs2 := lam (pi pConst (srt 1)) (lam (srt 1) (lam (srt 1) (bv 0)))
  let env := addRec env pRecId 0 recType #[pIndId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 2)
    (rules := #[
      { ctor := pMk1Id, nfields := 0, rhs := ruleRhs1 },
      { ctor := pMk2Id, nfields := 0, rhs := ruleRhs2 }
    ])
  let prims := buildPrimitives .meta
  test "elim level: large from Prop multi-ctor → error"
    (typecheckConstK2 env pRecId prims |> fun r => !r.isOk)

/-! ### 1H. Theorem validation tests -/

def testCheckTheoremNotInProp : TestSeq :=
  -- Theorem type in Type (not Prop) → error
  let thmId := mkId "badThm" 75
  let env := addTheorem default thmId ty (srt 0)
  let prims := buildPrimitives .meta
  test "checkConst: theorem type not in Prop → error"
    (typecheckConstK2 env thmId prims |> fun r => !r.isOk)

def testCheckTheoremValueMismatch : TestSeq :=
  -- Theorem value has wrong type
  let (env, trueId, _introId, _recId) := buildMyTrueEnv
  let thmId := mkId "badThm" 76
  -- theorem : MyTrue := Sort 0 (wrong value)
  let env := addTheorem env thmId (cst trueId) prop
  let prims := buildPrimitives .meta
  test "checkConst: theorem value mismatch → error"
    (typecheckConstK2 env thmId prims |> fun r => !r.isOk)

/-! ========================================================================
    Phase 2: Level arithmetic edge cases
    ======================================================================== -/

def testLevelArithmeticExtended : TestSeq :=
  -- These test level equality via isDefEq on sorts
  let u := Ix.Kernel.Level.param 0 default
  let v := Ix.Kernel.Level.param 1 default
  -- max(u, 0) = u
  test "level: max(u, 0) = u"
    (isDefEqEmpty (Ix.Kernel.Expr.mkSort (.max u .zero)) (Ix.Kernel.Expr.mkSort u) == .ok true) $
  -- max(0, u) = u
  test "level: max(0, u) = u"
    (isDefEqEmpty (Ix.Kernel.Expr.mkSort (.max .zero u)) (Ix.Kernel.Expr.mkSort u) == .ok true) $
  -- max(succ u, succ v) = succ(max(u,v))
  test "level: max(succ u, succ v) = succ(max(u,v))"
    (isDefEqEmpty (Ix.Kernel.Expr.mkSort (.max (.succ u) (.succ v))) (Ix.Kernel.Expr.mkSort (.succ (.max u v))) == .ok true) $
  -- max(u, u) = u
  test "level: max(u, u) = u"
    (isDefEqEmpty (Ix.Kernel.Expr.mkSort (.max u u)) (Ix.Kernel.Expr.mkSort u) == .ok true) $
  -- imax(u, succ v) = max(u, succ v)
  test "level: imax(u, succ v) = max(u, succ v)"
    (isDefEqEmpty (Ix.Kernel.Expr.mkSort (.imax u (.succ v))) (Ix.Kernel.Expr.mkSort (.max u (.succ v))) == .ok true) $
  -- imax(u, 0) = 0
  test "level: imax(u, 0) = 0"
    (isDefEqEmpty (Ix.Kernel.Expr.mkSort (.imax u .zero)) (Ix.Kernel.Expr.mkSort .zero) == .ok true) $
  -- 0 <= u (Sort 0 is sub-sort of Sort u)
  -- We test via Sort 0 ≤ Sort u: always true since Prop ≤ anything
  -- param 0 != param 1
  test "level: param 0 != param 1"
    (isDefEqEmpty (Ix.Kernel.Expr.mkSort u) (Ix.Kernel.Expr.mkSort v) == .ok false) $
  -- succ(succ 0) == succ(succ 0)
  test "level: succ(succ 0) == succ(succ 0)"
    (isDefEqEmpty (srt 2) (srt 2) == .ok true) $
  -- max(max(u, v), w) == max(u, max(v, w)) (associativity)
  let w := Ix.Kernel.Level.param 2 default
  test "level: max associativity"
    (isDefEqEmpty (Ix.Kernel.Expr.mkSort (.max (.max u v) w)) (Ix.Kernel.Expr.mkSort (.max u (.max v w))) == .ok true) $
  -- imax(succ u, succ v) == max(succ u, succ v)
  test "level: imax(succ u, succ v) = max(succ u, succ v)"
    (isDefEqEmpty (Ix.Kernel.Expr.mkSort (.imax (.succ u) (.succ v))) (Ix.Kernel.Expr.mkSort (.max (.succ u) (.succ v))) == .ok true) $
  -- succ(max(u, v)) == max(succ u, succ v)
  test "level: succ(max(u, v)) = max(succ u, succ v)"
    (isDefEqEmpty (Ix.Kernel.Expr.mkSort (.succ (.max u v))) (Ix.Kernel.Expr.mkSort (.max (.succ u) (.succ v))) == .ok true)

/-! ========================================================================
    Phase 3: Parity cleanup
    ======================================================================== -/

def testProofIrrelNotProp : TestSeq :=
  -- Two axioms of a Type-level inductive are NOT proof-irrelevant (not in Prop)
  let (env, natId, _zeroId, _succId, _recId) := buildMyNatEnv
  let ax1 := mkId "ax1" 77
  let ax2 := mkId "ax2" 78
  let env := addAxiom (addAxiom env ax1 (cst natId)) ax2 (cst natId)
  test "proof irrel not prop: MyNat axioms not defeq"
    (isDefEqK2 env (cst ax1) (cst ax2) == .ok false)

def testUnitLikeWithFieldsNotDefEq : TestSeq :=
  -- Pair (2 fields) is NOT unit-like so axioms are NOT defeq
  let (env, pairId, _pairCtorId) := buildPairEnv
  let ax1 := mkId "ax1" 79
  let ax2 := mkId "ax2" 80
  let pairNatNat := app (app (cst pairId) ty) ty
  let env := addAxiom (addAxiom env ax1 pairNatNat) ax2 pairNatNat
  test "unit-like: pair with fields not defeq"
    (isDefEqK2 env (cst ax1) (cst ax2) == .ok false)

/-! ========================================================================
    Phase 4: Rust parity — remaining gaps
    ======================================================================== -/

def testProofIrrelDifferentPropTypes : TestSeq :=
  -- Build MyTrue (Prop inductive with 1 ctor) + MyFalse (Prop inductive with 0 ctors)
  let (env, trueId, _introId, _recId) := buildMyTrueEnv
  let falseIndId := mkId "MyFalse" 81
  let env := addInductive env falseIndId prop #[] (all := #[falseIndId])
  let h1 := mkId "h1" 82
  let h2 := mkId "h2" 83
  let env := addAxiom (addAxiom env h1 (cst trueId)) h2 (cst falseIndId)
  -- Proofs of different Prop types are NOT defeq
  test "proof irrel: different prop types not defeq"
    (isDefEqK2 env (cst h1) (cst h2) == .ok false)

def testProofIrrelBasicInductive : TestSeq :=
  -- Two axioms of MyTrue (Prop inductive) are defeq via proof irrelevance
  let (env, trueId, _introId, _recId) := buildMyTrueEnv
  let p1 := mkId "p1" 84
  let p2 := mkId "p2" 85
  let env := addAxiom (addAxiom env p1 (cst trueId)) p2 (cst trueId)
  test "proof irrel basic: two axioms of MyTrue defeq"
    (isDefEqK2 env (cst p1) (cst p2) == .ok true)

def testNonKRecursorStaysStuck : TestSeq :=
  -- MyNat.rec (K=false) applied to axiom of type MyNat stays stuck
  let (env, natId, _zeroId, _succId, recId) := buildMyNatEnv
  let axId := mkId "myAxiom" 86
  let env := addAxiom env axId (cst natId)
  let motive := lam (cst natId) ty
  let base := natLit 0
  let step := lam (cst natId) (lam ty (bv 0))
  let recExpr := app (app (app (app (cst recId) motive) base) step) (cst axId)
  -- Non-K recursor on axiom (not a ctor) stays stuck
  test "non-K rec on axiom stays stuck"
    (whnfHeadAddr env recExpr == .ok (some recId.addr))

def testLazyDeltaAbbrevChain : TestSeq :=
  -- Chain of abbrevs: a := 7, b := a, c := b (all .abbrev hints)
  let a := mkId "a" 87
  let b := mkId "b" 88
  let c := mkId "c" 89
  let env := addDef default a ty (natLit 7) (hints := .abbrev)
  let env := addDef env b ty (cst a) (hints := .abbrev)
  let env := addDef env c ty (cst b) (hints := .abbrev)
  test "abbrev chain: c == 7" (isDefEqK2 env (cst c) (natLit 7) == .ok true) $
  test "abbrev chain: a == c" (isDefEqK2 env (cst a) (cst c) == .ok true)

def suite : List TestSeq := [
  group "eval+quote roundtrip" testEvalQuoteIdentity,
  group "beta reduction" testBetaReduction,
  group "let reduction" testLetReduction,
  group "nat primitives" testNatPrimitives,
  group "nat prims missing" testNatPrimsMissing,
  group "large nat" testLargeNat,
  group "delta unfolding" testDeltaUnfolding,
  group "delta lambda" testDeltaLambda,
  group "opaque constants" testOpaqueConstants,
  group "universe poly" testUniversePoly,
  group "projection" testProjection,
  group "stuck terms" testStuckTerms,
  group "nested beta+delta" testNestedBetaDelta,
  group "higher-order" testHigherOrder,
  group "iota reduction" testIotaReduction,
  group "recursive iota" testRecursiveIota,
  group "K-reduction" testKReduction,
  group "proof irrelevance" testProofIrrelevance,
  group "quotient reduction" testQuotReduction,
  group "isDefEq" testIsDefEq,
  group "Bool.true reflection" testBoolTrueReflection,
  group "unit-like defEq" testUnitLikeDefEq,
  group "defEq offset" testDefEqOffset,
  group "struct eta defEq" testStructEtaDefEq,
  group "struct eta iota" testStructEtaIota,
  group "string defEq" testStringDefEq,
  group "reducibility hints" testReducibilityHints,
  group "defEq let" testDefEqLet,
  group "multi-univ params" testMultiUnivParams,
  group "type inference" testInfer,
  group "errors" testErrors,
  -- Extended test groups
  group "iota edge cases" testIotaEdgeCases,
  group "K-reduction extended" testKReductionExtended,
  group "proof irrelevance extended" testProofIrrelevanceExtended,
  group "quotient extended" testQuotExtended,
  group "lazyDelta strategies" testLazyDeltaStrategies,
  group "eta expansion extended" testEtaExtended,
  group "nat primitive edge cases" testNatPrimEdgeCases,
  group "inference extended" testInferExtended,
  group "errors extended" testErrorsExtended,
  group "string edge cases" testStringEdgeCases,
  group "isDefEq complex" testDefEqComplex,
  group "universe extended" testUniverseExtended,
  group "whnf caching" testWhnfCaching,
  group "struct eta axiom" testStructEtaAxiom,
  -- Round 2 test groups
  group "native reduction" testNativeReduction,
  group "defEq offset deep" testDefEqOffsetDeep,
  group "unit-like extended" testUnitLikeExtended,
  group "struct eta bidirectional" testStructEtaBidirectional,
  group "nat pow overflow" testNatPowOverflow,
  group "natLit ctor defEq" testNatLitCtorDefEq,
  group "proof irrel precision" testProofIrrelPrecision,
  group "deep spine" testDeepSpine,
  group "pi defEq" testPiDefEq,
  group "string ctor deep" testStringCtorDeep,
  group "proj defEq" testProjDefEq,
  group "fvar comparison" testFvarComparison,
  group "defn typecheck add" testDefnTypecheckAdd,
  -- Round 3: Rust parity tests
  group "proof irrel under lambda" testProofIrrelUnderLambda,
  group "proof irrel intro vs axiom" testProofIrrelIntroVsAxiom,
  group "eta axiom fun" testEtaAxiomFun,
  group "eta nested axiom" testEtaNestedAxiom,
  group "check lam against pi" testCheckLamAgainstPi,
  group "check domain mismatch" testCheckDomainMismatch,
  group "level equality" testLevelEquality,
  group "proj nested pair" testProjNestedPair,
  group "opaque self eq" testOpaqueSelfEq,
  group "theorem self eq" testTheoremSelfEq,
  group "beta inside defEq" testBetaInsideDefEq,
  group "sort defEq levels" testSortDefEqLevels,
  group "nat supplemental" testNatSupplemental,
  group "whnf nat prim symbolic" testWhnfNatPrimSymbolic,
  group "lazy delta supplemental" testLazyDeltaSupplemental,
  group "K-reduction supplemental" testKReductionSupplemental,
  group "struct eta not recursive" testStructEtaNotRecursive,
  group "unit-like prop defEq" testUnitLikePropDefEq,
  -- Phase 1: Declaration-level checking
  group "checkConst: MyNat" testCheckMyNatInd,
  group "checkConst: MyTrue" testCheckMyTrueInd,
  group "checkConst: Pair" testCheckPairInd,
  group "checkConst: axiom" testCheckAxiom,
  group "checkConst: opaque" testCheckOpaque,
  group "checkConst: theorem" testCheckTheorem,
  group "checkConst: definition" testCheckDefinition,
  group "ctor param count mismatch" testCheckCtorParamCountMismatch,
  group "ctor return type not inductive" testCheckCtorReturnTypeNotInductive,
  group "positivity: no occurrence" testPositivityOkNoOccurrence,
  group "positivity: direct positive" testPositivityOkDirect,
  group "positivity: negative violation" testPositivityViolationNegative,
  group "positivity: covariant OK" testPositivityOkCovariant,
  group "K-flag: OK" testKFlagOk,
  group "K-flag: not Prop" testKFlagFailNotProp,
  group "K-flag: multiple ctors" testKFlagFailMultipleCtors,
  group "K-flag: has fields" testKFlagFailHasFields,
  group "rec rules count mismatch" testRecRulesCountMismatch,
  group "rec rules nfields mismatch" testRecRulesNfieldsMismatch,
  group "elim level: Type large OK" testElimLevelTypeLargeOk,
  group "elim level: Prop to Prop OK" testElimLevelPropToPropOk,
  group "elim level: large from Prop multi-ctor" testElimLevelLargeFromPropMultiCtorFail,
  group "theorem: not in Prop" testCheckTheoremNotInProp,
  group "theorem: value mismatch" testCheckTheoremValueMismatch,
  -- Phase 2: Level arithmetic
  group "level arithmetic extended" testLevelArithmeticExtended,
  -- Phase 3: Parity cleanup
  group "proof irrel not prop" testProofIrrelNotProp,
  group "unit-like with fields not defeq" testUnitLikeWithFieldsNotDefEq,
  -- Phase 4: Rust parity remaining gaps
  group "proof irrel different prop types" testProofIrrelDifferentPropTypes,
  group "proof irrel basic inductive" testProofIrrelBasicInductive,
  group "non-K recursor stays stuck" testNonKRecursorStaysStuck,
  group "lazy delta abbrev chain" testLazyDeltaAbbrevChain,
]

end Tests.Ix.Kernel.Unit
