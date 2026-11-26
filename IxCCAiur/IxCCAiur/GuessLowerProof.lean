import IxCCAiur.GuessLower
import IxCCAiur.TypedBackward
import IxCC.Src.EvalG
import IxCC.Fir.Proof.Mono

/-! # Certified Backward Soundness for Tier-2 `guess` Lowering (`IxCCAiur.GuessLowerProof`)

Proves end-to-end backward `EvalFn` soundness for `IxCCAiur.GuessLower`, with zero
TCB expansion:

1. **Soundness of `foldOversizedNatCmp` (`evalRhs_foldOversizedNatCmpRhs`)**:
   Every rewritten oversized-literal comparison (`x < M`, `x ≤ M`, `M < x`, `M ≤ x`,
   `x == M`, `M == x` for `< 2^56` operands and `M ≥ 2^56`) evaluates identically to
   the original `Fir.evalRhs`.
2. **Heap independence of shape-checkable `TVR` (`TVR_heap_indep_of_shapeCheckable`)**:
   For every `isShapeCheckableRep` return representation (`.irr`, `.nat b`, `.w8`,
   `.w16`, `.w32`, `.w64`, `.enum ind`, acyclic pointer-free `.data d`), `TVR` is
   invariant under arbitrary heap changes.
3. **`U4` canonical bounds soundness (`shapeCheckExpr_sound`, `fromRawExpr_sound`)**:
   Any `EvalExpr` derivation of `shapeCheckExpr` (or `fromRawExpr` for `.w32`/`.w64`)
   on raw, untrusted `hint` output `yVal` unconditionally guarantees
   `∃ v, TVR P cert feat h r v yVal` with `h' = h`.
4. **Generic backward `EvalFn` inversion (`eval_guessWrapper_inv`)**:
   Any `EvalFn` derivation of a `GuessLower`-rewritten `fName` (with `hint` returning
   ANY arbitrary `Constant F`) implies BOTH:
   * `∃ v, TVR P cert feat h' g.retRep v r` (`U4` canonicality & bounds), AND
   * `∃ hKey okVal, EvalFn world (qualified g.cName) (args ++ [r]) hKey okVal h' ∧
       BoolTrueVal g.boolCheck okVal` (the checker accepted `(args, r)` with `Bool.true`).
5. **Composition with verified `guess` soundness & `SrcG` (`RunG`)**:
   * `guess_backward_denotation`: composes `eval_guessWrapper_inv` with checker backward
     soundness and the verified `guess` uniqueness theorem (`∀ xs y, c xs y = true → y = f xs`)
     to recover exact denotation `y = f xs`.
   * `guess_backward_runG`: composes directly with `IxCC.Src.RunG.guess` to produce a
     `SrcG` derivation `RunG src ls g.fCId xs (toSrcVal yVal)`.

Zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`, zero `bv_decide`,
strictly `[propext, Classical.choice, Quot.sound]`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.GuessLowerProof

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.Fir (Program Fun FunId Var Arg Rhs Code Alt CtorInfo Env evalArgs evalRhs boolVal primResult)
open IxCC.Key
open IxCC.Lam (Lit Prim)
open IxCC.Shape (Shape DataDecl)
open IxCC.Fir.Shape (ShapeCert FunShapes)
open IxCC.AiurBackend.Lower
  (Ty Expr Pat Fn natLimit natDigits localName localName_inj moduleName qualified objQName
   funName ctorNameOf pC callE vE litE letE seqE matchE assertion trapE
   qualifyName qualifyTy qualifyPat qualifyExpr qualifyPatF qualifyExprF
   isPlainExpr isPlainExpr_qualifyExprF ctorEntry?_sound)
open IxCC.AiurBackend.Gadgets
  (WorldHasFn evalFn_plain_inv evalExpr_var_inv evalExpr_literal_inv
   evalExpr_let_bind_inv evalExpr_let_wildcard_inv evalExpr_call_inv
   evalExpr_call1_inv evalExpr_call2_inv evalExpr_assertEq_inv
   evalExpr_hint_inv evalExpr_construct0_inv isU64Val)
open IxCC.AiurBackend.Peephole (isU32Val)
open IxCC.AiurBackend.TypedRep
open IxCC.AiurBackend.TypedLower
open IxCC.AiurBackend.TypedGadgets
  (FieldCompatible64 ByteCheckSpec U32Contracts
   eval_check_u8 eval_check_u16 eval_check_u24 eval_check_u56
   eval_sub_borrow_56 evalExpr_let_wild_tuple2_inv
   qualifyName_check_u8 qualifyName_check_u16 qualifyName_check_u24
   qualifyName_check_u56 qualifyName_sub_borrow_56 qualifyName_u32_from_fields)
open IxCC.AiurBackend.TypedBackward (TVR TVRDataFields qualifyName_enumName qualifyName_dataName)
open IxCC.AiurBackend.GuessLower

/-! ## Section 1: Soundness of `foldOversizedNatCmp` -/

section FoldOversizedNatCmp

private theorem boolCtorInfo?_spec {P : Program} {b : Bool} {cInfo : CtorInfo}
    (h : boolCtorInfo? P b = some cInfo) :
    boolVal P b = some (.ctor cInfo []) ∧ cInfo.arity = 0 := by
  unfold boolCtorInfo? at h
  cases b with
  | true =>
    simp only [↓reduceIte, bind, Option.bind] at h
    cases hk : P.known.boolTrue with
    | none => simp [hk] at h
    | some k =>
      simp only [hk] at h
      cases hi : P.ctorInfo? k with
      | none => simp [hi] at h
      | some info =>
        simp only [hi] at h
        split at h
        · rename_i har
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨by simp [boolVal, hk, hi], beq_iff_eq.mp har⟩
        · cases h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind] at h
    cases hk : P.known.boolFalse with
    | none => simp [hk] at h
    | some k =>
      simp only [hk] at h
      cases hi : P.ctorInfo? k with
      | none => simp [hi] at h
      | some info =>
        simp only [hi] at h
        split at h
        · rename_i har
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨by simp [boolVal, hk, hi], beq_iff_eq.mp har⟩
        · cases h

private theorem smallNatArg_eval {fsh : FunShapes} {ρ : Env} {a : Arg}
    (hEnv : ∀ x, isSmallNatShape (fsh.var x) = true →
      ∃ n : Nat, n < natLimit ∧ ρ.get? x = some (.lit (.nat n)))
    (hSmall : isSmallNatArg fsh a = true) :
    ∃ n : Nat, n < natLimit ∧ a.eval ρ = some (.lit (.nat n)) := by
  cases a with
  | lit l =>
    cases l with
    | nat n =>
      simp only [isSmallNatArg, decide_eq_true_eq] at hSmall
      exact ⟨n, hSmall, rfl⟩
    | str _ => simp [isSmallNatArg] at hSmall
  | var x =>
    simp only [isSmallNatArg] at hSmall
    obtain ⟨n, hlt, hget⟩ := hEnv x hSmall
    exact ⟨n, hlt, hget⟩
  | erased => simp [isSmallNatArg] at hSmall

/-- Exact `Fir.evalRhs` soundness of `foldOversizedNatCmpRhs`: whenever every
`< natLimit`-shaped variable in `ρ` holds a `Nat` `< natLimit`, rewriting oversized
constant comparisons (`M ≥ natLimit`) preserves `Fir.evalRhs` identically. -/
theorem evalRhs_foldOversizedNatCmpRhs {P : Program} {fsh : FunShapes} {ρ : Env} {r : Rhs}
    (hEnv : ∀ x, isSmallNatShape (fsh.var x) = true →
      ∃ n : Nat, n < natLimit ∧ ρ.get? x = some (.lit (.nat n))) :
    evalRhs P ρ (foldOversizedNatCmpRhs P fsh r) = evalRhs P ρ r := by
  cases r with
  | arg _ | ctor _ _ | proj _ _ _ | call _ _ => rfl
  | prim op as =>
    rcases as with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · rfl
    · rfl
    · unfold foldOversizedNatCmpRhs
      dsimp only
      have hAux : ∀ (foldOpt : Option Bool),
          (match op, a, b with
           | .natBlt, x, .lit (.nat m) =>
             if natLimit ≤ m && isSmallNatArg fsh x then some true else none
           | .natBle, x, .lit (.nat m) =>
             if natLimit ≤ m && isSmallNatArg fsh x then some true else none
           | .natBlt, .lit (.nat m), x =>
             if natLimit ≤ m && isSmallNatArg fsh x then some false else none
           | .natBle, .lit (.nat m), x =>
             if natLimit ≤ m && isSmallNatArg fsh x then some false else none
           | .natBeq, x, .lit (.nat m) =>
             if natLimit ≤ m && isSmallNatArg fsh x then some false else none
           | .natBeq, .lit (.nat m), x =>
             if natLimit ≤ m && isSmallNatArg fsh x then some false else none
           | _, _, _ => none) = foldOpt →
          evalRhs P ρ
            (match foldOpt.bind (boolCtorInfo? P) with
             | some cInfo => .ctor cInfo []
             | none => .prim op [a, b]) = evalRhs P ρ (.prim op [a, b]) := by
        intro foldOpt hFold
        cases foldOpt with
        | none => rfl
        | some bval =>
          simp only [Option.bind_some]
          cases hci : boolCtorInfo? P bval with
          | none => rfl
          | some cInfo =>
            obtain ⟨hbv, har⟩ := boolCtorInfo?_spec hci
            have hGoal : evalRhs P ρ (.ctor cInfo []) = .ok (.ctor cInfo []) := by
              simp [evalRhs, evalArgs, har]
            rw [hGoal]
            split at hFold
            · rename_i x m
              split at hFold
              · rename_i hc
                simp only [Option.some.injEq] at hFold; subst hFold
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                obtain ⟨n, hn, hx⟩ := smallNatArg_eval hEnv hc.2
                have hcmp : decide (n < m) = true := decide_eq_true (by omega)
                have hlit : (Arg.lit (.nat m)).eval ρ = some (.lit (.nat m)) := rfl
                simp [evalRhs, evalArgs, hx, hlit, primResult, Fir.natArgs,
                  IxCC.Lam.Prim.sem, hcmp, hbv, IxCC.Sem.Result.ofOption]
              · cases hFold
            · rename_i x m
              split at hFold
              · rename_i hc
                simp only [Option.some.injEq] at hFold; subst hFold
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                obtain ⟨n, hn, hx⟩ := smallNatArg_eval hEnv hc.2
                have hcmp : decide (n ≤ m) = true := decide_eq_true (by omega)
                have hlit : (Arg.lit (.nat m)).eval ρ = some (.lit (.nat m)) := rfl
                simp [evalRhs, evalArgs, hx, hlit, primResult, Fir.natArgs,
                  IxCC.Lam.Prim.sem, IxCC.Lam.Prim.sem.srcOp, IxCC.Src.PrimOp.eval2,
                  hcmp, hbv, IxCC.Sem.Result.ofOption]
              · cases hFold
            · rename_i m x
              split at hFold
              · rename_i hc
                simp only [Option.some.injEq] at hFold; subst hFold
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                obtain ⟨n, hn, hx⟩ := smallNatArg_eval hEnv hc.2
                have hcmp : decide (m < n) = false := decide_eq_false (by omega)
                have hlit : (Arg.lit (.nat m)).eval ρ = some (.lit (.nat m)) := rfl
                simp [evalRhs, evalArgs, hx, hlit, primResult, Fir.natArgs,
                  IxCC.Lam.Prim.sem, hcmp, hbv, IxCC.Sem.Result.ofOption]
              · cases hFold
            · rename_i m x
              split at hFold
              · rename_i hc
                simp only [Option.some.injEq] at hFold; subst hFold
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                obtain ⟨n, hn, hx⟩ := smallNatArg_eval hEnv hc.2
                have hcmp : decide (m ≤ n) = false := decide_eq_false (by omega)
                have hlit : (Arg.lit (.nat m)).eval ρ = some (.lit (.nat m)) := rfl
                simp [evalRhs, evalArgs, hx, hlit, primResult, Fir.natArgs,
                  IxCC.Lam.Prim.sem, IxCC.Lam.Prim.sem.srcOp, IxCC.Src.PrimOp.eval2,
                  hcmp, hbv, IxCC.Sem.Result.ofOption]
              · cases hFold
            · rename_i x m
              split at hFold
              · rename_i hc
                simp only [Option.some.injEq] at hFold; subst hFold
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                obtain ⟨n, hn, hx⟩ := smallNatArg_eval hEnv hc.2
                have hcmp : (n == m) = false := beq_false_of_ne (by omega)
                have hlit : (Arg.lit (.nat m)).eval ρ = some (.lit (.nat m)) := rfl
                simp [evalRhs, evalArgs, hx, hlit, primResult, Fir.natArgs,
                  IxCC.Lam.Prim.sem, IxCC.Lam.Prim.sem.srcOp, IxCC.Src.PrimOp.eval2,
                  hcmp, hbv, IxCC.Sem.Result.ofOption]
              · cases hFold
            · rename_i m x
              split at hFold
              · rename_i hc
                simp only [Option.some.injEq] at hFold; subst hFold
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                obtain ⟨n, hn, hx⟩ := smallNatArg_eval hEnv hc.2
                have hcmp : (m == n) = false := beq_false_of_ne (by omega)
                have hlit : (Arg.lit (.nat m)).eval ρ = some (.lit (.nat m)) := rfl
                simp [evalRhs, evalArgs, hx, hlit, primResult, Fir.natArgs,
                  IxCC.Lam.Prim.sem, IxCC.Lam.Prim.sem.srcOp, IxCC.Src.PrimOp.eval2,
                  hcmp, hbv, IxCC.Sem.Result.ofOption]
              · cases hFold
            · cases hFold
      exact hAux _ rfl
    · rfl

private theorem litNatArgs?_eval {ρ : Env} :
    ∀ {as : List Arg} {vs : List Fir.Val},
      litNatArgs? as = some vs → evalArgs ρ as = some vs
  | [], _, h => by
    simp only [litNatArgs?, Option.some.injEq] at h
    subst h; rfl
  | .lit (.nat n) :: rest, _, h => by
    simp only [litNatArgs?] at h
    cases hr : litNatArgs? rest with
    | none => simp [hr] at h
    | some vs' =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst h
      simp [evalArgs, Arg.eval, litNatArgs?_eval hr]
  | .lit (.str _) :: _, _, h => by simp [litNatArgs?] at h
  | .var _ :: _, _, h => by simp [litNatArgs?] at h
  | .erased :: _, _, h => by simp [litNatArgs?] at h

private theorem arg_eval_congr {ρ₁ ρ₂ : Env} {x : Var} {a : Arg}
    (hEq : ∀ v, v ≠ x → ρ₁.get? v = ρ₂.get? v) (hNo : argReadsVar x a = false) :
    a.eval ρ₁ = a.eval ρ₂ := by
  cases a with
  | var v =>
    simp only [argReadsVar, beq_eq_false_iff_ne] at hNo
    exact hEq v hNo
  | lit _ | erased => rfl

private theorem evalArgs_congr {ρ₁ ρ₂ : Env} {x : Var} :
    ∀ {as : List Arg},
      (∀ v, v ≠ x → ρ₁.get? v = ρ₂.get? v) →
      as.any (argReadsVar x) = false →
      evalArgs ρ₁ as = evalArgs ρ₂ as
  | [], _, _ => rfl
  | a :: as, hEq, hNo => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hNo
    simp only [evalArgs, arg_eval_congr hEq hNo.1, evalArgs_congr hEq hNo.2]

private theorem evalRhs_congr {P : Program} {ρ₁ ρ₂ : Env} {x : Var} {r : Rhs}
    (hEq : ∀ v, v ≠ x → ρ₁.get? v = ρ₂.get? v) (hNo : rhsReadsVar x r = false) :
    evalRhs P ρ₁ r = evalRhs P ρ₂ r := by
  cases r with
  | arg a => simp only [evalRhs, arg_eval_congr hEq hNo]
  | ctor c as => simp only [evalRhs, evalArgs_congr hEq hNo]
  | prim op as => simp only [evalRhs, evalArgs_congr hEq hNo]
  | proj v c i =>
    simp only [rhsReadsVar, beq_eq_false_iff_ne] at hNo
    simp only [evalRhs, hEq v hNo]
  | call _ _ => rfl

private theorem env_congr_insert {ρ₁ ρ₂ : Env} {x y : Var} {v : Fir.Val}
    (hEq : ∀ u, u ≠ x → ρ₁.get? u = ρ₂.get? u) :
    ∀ u, u ≠ x → (ρ₁.insert y v).get? u = (ρ₂.insert y v).get? u := by
  intro u hne
  by_cases huy : u = y
  · subst huy; simp [IxCC.Src.NatMap.get?_insert_self]
  · rw [IxCC.Src.NatMap.get?_insert_ne _ _ huy, IxCC.Src.NatMap.get?_insert_ne _ _ huy, hEq u hne]

private theorem env_congr_bindAll {x : Var} :
    ∀ {ps : List Var} {vs : List Fir.Val} {ρ₁ ρ₂ : Env},
      (∀ u, u ≠ x → ρ₁.get? u = ρ₂.get? u) →
      ∀ u, u ≠ x → (Fir.bindAll ρ₁ ps vs).get? u = (Fir.bindAll ρ₂ ps vs).get? u
  | [], _, _, _, hEq => hEq
  | _ :: _, [], _, _, hEq => hEq
  | p :: _, v :: _, ρ₁, ρ₂, hEq =>
    env_congr_bindAll (ρ₁ := ρ₁.insert p v) (ρ₂ := ρ₂.insert p v) (env_congr_insert hEq)

private inductive JRel (x : Var) : List Fir.JEntry → List Fir.JEntry → Prop where
  | same (J : List Fir.JEntry) : JRel x J J
  | cons {e₁ e₂ : Fir.JEntry} {J₁ J₂ : List Fir.JEntry}
      (hid : e₁.id = e₂.id) (hch : e₁.charged = e₂.charged)
      (hps : e₁.params = e₂.params) (hbd : e₁.body = e₂.body)
      (hrec : e₁.isRec = e₂.isRec)
      (henv : ∀ u, u ≠ x → e₁.env.get? u = e₂.env.get? u)
      (hno : codeReadsVar x e₁.body = false)
      (hrest : JRel x J₁ J₂) :
      JRel x (e₁ :: J₁) (e₂ :: J₂)

private theorem jrel_lookupJ {x : Var} (j : Fir.JoinId) :
    ∀ {J₁ J₂ : List Fir.JEntry}, JRel x J₁ J₂ →
      (Fir.lookupJ j J₁ = none ∧ Fir.lookupJ j J₂ = none) ∨
      (∃ e r, Fir.lookupJ j J₁ = some (e, r) ∧ Fir.lookupJ j J₂ = some (e, r)) ∨
      (∃ e₁ r₁ e₂ r₂,
        Fir.lookupJ j J₁ = some (e₁, r₁) ∧ Fir.lookupJ j J₂ = some (e₂, r₂) ∧
        e₁.id = e₂.id ∧ e₁.charged = e₂.charged ∧ e₁.params = e₂.params ∧
        e₁.body = e₂.body ∧ e₁.isRec = e₂.isRec ∧
        (∀ u, u ≠ x → e₁.env.get? u = e₂.env.get? u) ∧
        codeReadsVar x e₁.body = false ∧
        JRel x (e₁.after r₁) (e₂.after r₂))
  | _, _, .same J => by
    cases hl : Fir.lookupJ j J with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some p => exact Or.inr (Or.inl ⟨p.1, p.2, rfl, rfl⟩)
  | _, _, .cons hid hch hps hbd hrec henv hno hrest => by
    simp only [Fir.lookupJ, hid]
    split
    · refine Or.inr (Or.inr ⟨_, _, _, _, rfl, rfl, hid, hch, hps, hbd, hrec, henv, hno, ?_⟩)
      unfold Fir.JEntry.after
      rw [hrec]
      split
      · exact .cons hid rfl hps hbd rfl henv hno hrest
      · exact hrest
    · exact jrel_lookupJ j hrest

private theorem eval_congr_unused_aux (P : Program) (x : Var) :
    ∀ (k n : Nat),
      (∀ (ρ₁ ρ₂ : Env) (J₁ J₂ : List Fir.JEntry) (c : Code),
        c.size + Fir.jweight J₁ ≤ n →
        JRel x J₁ J₂ →
        (∀ u, u ≠ x → ρ₁.get? u = ρ₂.get? u) →
        codeReadsVar x c = false →
        Fir.eval P k ρ₁ J₁ c = Fir.eval P k ρ₂ J₂ c) ∧
      (∀ (ρ₁ ρ₂ : Env) (J₁ J₂ : List Fir.JEntry) (key : CtorKey) (alts : List Alt) (d : Option Code),
        Code.altsSize alts + Code.optSize d + Fir.jweight J₁ + 1 ≤ n →
        JRel x J₁ J₂ →
        (∀ u, u ≠ x → ρ₁.get? u = ρ₂.get? u) →
        altsReadsVar x alts = false →
        optReadsVar x d = false →
        Fir.evalAlts P k ρ₁ J₁ key alts d = Fir.evalAlts P k ρ₂ J₂ key alts d) := by
  intro k
  induction k with
  | zero =>
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ _ _ _ c hle => ?_, fun _ _ _ _ _ _ _ hle => by omega⟩
      have := Code.size_pos c; omega
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · intro ρ₁ ρ₂ J₁ J₂ c hle hJ hEq hNo
        cases c with
        | bind y r k' =>
          simp only [codeReadsVar, Bool.or_eq_false_iff] at hNo
          have hsz : k'.size + Fir.jweight J₁ ≤ n := by simp only [Code.size] at hle; omega
          cases r with
          | call f as =>
            rw [Fir.eval.eq_def, Fir.eval.eq_def]; dsimp only
            rw [evalArgs_congr hEq hNo.1]
            cases evalArgs ρ₂ as with
            | none => rfl
            | some vs =>
              dsimp only
              cases Fir.evalCall P 0 f vs with
              | ok v => exact ih.1 _ _ J₁ J₂ k' hsz hJ (env_congr_insert (y := y) (v := v) hEq) hNo.2
              | timeout | resource _ | trap | stuck => rfl
          | arg _ | ctor _ _ | proj _ _ _ | prim _ _ =>
            rw [Fir.eval.eq_def, Fir.eval.eq_def]; dsimp only
            rw [evalRhs_congr hEq hNo.1]
            cases evalRhs P ρ₂ _ with
            | ok v => exact ih.1 _ _ J₁ J₂ k' hsz hJ (env_congr_insert (y := y) (v := v) hEq) hNo.2
            | timeout | resource _ | trap | stuck => rfl
        | jp j ps isRec b k' =>
          simp only [codeReadsVar, Bool.or_eq_false_iff] at hNo
          rw [Fir.eval.eq_def, Fir.eval.eq_def]; dsimp only
          have hsz : k'.size + Fir.jweight ({ id := j, charged := false, env := ρ₁, params := ps, body := b, isRec } :: J₁) ≤ n := by
            simp only [Code.size, Fir.jweight, Fir.JEntry.weight, Bool.false_eq_true, ↓reduceIte] at hle ⊢
            omega
          exact ih.1 ρ₁ ρ₂ _ _ k' hsz (.cons rfl rfl rfl rfl rfl hEq hNo.1 hJ) hEq hNo.2
        | jmp j as =>
          simp only [codeReadsVar] at hNo
          rw [Fir.eval.eq_def, Fir.eval.eq_def]; dsimp only
          rw [evalArgs_congr hEq hNo]
          rcases jrel_lookupJ j hJ with ⟨hl1, hl2⟩ | ⟨e, r, hl1, hl2⟩ |
              ⟨e₁, r₁, e₂, r₂, hl1, hl2, _, hch, hps, hbd, _, henv, hbdNo, hJ'⟩
          · rw [hl1, hl2]
          · rw [hl1, hl2]
          · rw [hl1, hl2]
            cases evalArgs ρ₂ as with
            | none => rfl
            | some vs =>
              dsimp only
              rw [hps, hch]
              split
              · split
                · rfl
                · rename_i hnc
                  have hw := Fir.lookupJ_weight j hl1
                  have hsz : e₁.body.size + Fir.jweight (e₁.after r₁) ≤ n := by
                    rw [Fir.JEntry.jweight_after]
                    simp only [Fir.JEntry.weight, hch, hnc, Bool.false_eq_true, ↓reduceIte] at hw
                    simp only [Code.size] at hle; omega
                  rw [← hps, ← hbd]
                  exact ih.1 _ _ _ _ e₁.body hsz hJ' (env_congr_bindAll henv) hbdNo
              · rfl
        | case v alts d =>
          simp only [codeReadsVar, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hNo
          rw [Fir.eval.eq_def, Fir.eval.eq_def]; dsimp only
          rw [hEq v hNo.1.1]
          cases ρ₂.get? v with
          | none => rfl
          | some val =>
            dsimp only
            cases val.asCtor P.known with
            | none => rfl
            | some p =>
              dsimp only
              have hsz : Code.altsSize alts + Code.optSize d + Fir.jweight J₁ + 1 ≤ n := by
                simp only [Code.size] at hle; omega
              exact ih.2 ρ₁ ρ₂ J₁ J₂ p.1 alts d hsz hJ hEq hNo.1.2 hNo.2
        | ret a =>
          simp only [codeReadsVar] at hNo
          rw [Fir.eval.eq_def, Fir.eval.eq_def]; simp only [arg_eval_congr hEq hNo]
        | tcall f as =>
          simp only [codeReadsVar] at hNo
          rw [Fir.eval.eq_def, Fir.eval.eq_def]; simp only [evalArgs_congr hEq hNo]
        | trap => rw [Fir.eval.eq_def, Fir.eval.eq_def]
      · intro ρ₁ ρ₂ J₁ J₂ key alts d hle hJ hEq hAlts hOpt
        cases alts with
        | nil =>
          rw [Fir.evalAlts.eq_def, Fir.evalAlts.eq_def]
          cases d with
          | none => rfl
          | some c =>
            simp only [optReadsVar] at hOpt
            have hsz : c.size + Fir.jweight J₁ ≤ n := by
              simp only [Code.altsSize, Code.optSize] at hle; omega
            exact ih.1 ρ₁ ρ₂ J₁ J₂ c hsz hJ hEq hOpt
        | cons alt rest =>
          cases alt with
          | mk key' body =>
            simp only [altsReadsVar, Bool.or_eq_false_iff] at hAlts
            rw [Fir.evalAlts.eq_def, Fir.evalAlts.eq_def]; dsimp only
            split
            · have hsz : body.size + Fir.jweight J₁ ≤ n := by
                simp only [Code.altsSize] at hle; omega
              exact ih.1 ρ₁ ρ₂ J₁ J₂ body hsz hJ hEq hAlts.1
            · have hsz : Code.altsSize rest + Code.optSize d + Fir.jweight J₁ + 1 ≤ n := by
                have := Code.size_pos body
                simp only [Code.altsSize] at hle; omega
              exact ih.2 ρ₁ ρ₂ J₁ J₂ key rest d hsz hJ hEq hAlts.2 hOpt
  | succ k ihk =>
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ _ _ _ c hle => ?_, fun _ _ _ _ _ _ _ hle => by omega⟩
      have := Code.size_pos c; omega
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · intro ρ₁ ρ₂ J₁ J₂ c hle hJ hEq hNo
        cases c with
        | bind y r k' =>
          simp only [codeReadsVar, Bool.or_eq_false_iff] at hNo
          have hsz : k'.size + Fir.jweight J₁ ≤ n := by simp only [Code.size] at hle; omega
          cases r with
          | call f as =>
            rw [Fir.eval.eq_def, Fir.eval.eq_def]; dsimp only
            rw [evalArgs_congr hEq hNo.1]
            cases evalArgs ρ₂ as with
            | none => rfl
            | some vs =>
              dsimp only
              cases Fir.evalCall P (k + 1) f vs with
              | ok v => exact ih.1 _ _ J₁ J₂ k' hsz hJ (env_congr_insert (y := y) (v := v) hEq) hNo.2
              | timeout | resource _ | trap | stuck => rfl
          | arg _ | ctor _ _ | proj _ _ _ | prim _ _ =>
            rw [Fir.eval.eq_def, Fir.eval.eq_def]; dsimp only
            rw [evalRhs_congr hEq hNo.1]
            cases evalRhs P ρ₂ _ with
            | ok v => exact ih.1 _ _ J₁ J₂ k' hsz hJ (env_congr_insert (y := y) (v := v) hEq) hNo.2
            | timeout | resource _ | trap | stuck => rfl
        | jp j ps isRec b k' =>
          simp only [codeReadsVar, Bool.or_eq_false_iff] at hNo
          rw [Fir.eval.eq_def, Fir.eval.eq_def]; dsimp only
          have hsz : k'.size + Fir.jweight ({ id := j, charged := false, env := ρ₁, params := ps, body := b, isRec } :: J₁) ≤ n := by
            simp only [Code.size, Fir.jweight, Fir.JEntry.weight, Bool.false_eq_true, ↓reduceIte] at hle ⊢
            omega
          exact ih.1 ρ₁ ρ₂ _ _ k' hsz (.cons rfl rfl rfl rfl rfl hEq hNo.1 hJ) hEq hNo.2
        | jmp j as =>
          simp only [codeReadsVar] at hNo
          rw [Fir.eval.eq_def, Fir.eval.eq_def]; dsimp only
          rw [evalArgs_congr hEq hNo]
          rcases jrel_lookupJ j hJ with ⟨hl1, hl2⟩ | ⟨e, r, hl1, hl2⟩ |
              ⟨e₁, r₁, e₂, r₂, hl1, hl2, _, hch, hps, hbd, _, henv, hbdNo, hJ'⟩
          · rw [hl1, hl2]
          · rw [hl1, hl2]
          · rw [hl1, hl2]
            cases evalArgs ρ₂ as with
            | none => rfl
            | some vs =>
              dsimp only
              rw [hps, hch]
              split
              · split
                · rw [← hps, ← hbd]
                  exact (ihk (e₁.body.size + Fir.jweight (e₁.after r₁))).1
                    _ _ _ _ e₁.body (Nat.le_refl _) hJ' (env_congr_bindAll henv) hbdNo
                · rename_i hnc
                  have hw := Fir.lookupJ_weight j hl1
                  have hsz : e₁.body.size + Fir.jweight (e₁.after r₁) ≤ n := by
                    rw [Fir.JEntry.jweight_after]
                    simp only [Fir.JEntry.weight, hch, hnc, Bool.false_eq_true, ↓reduceIte] at hw
                    simp only [Code.size] at hle; omega
                  rw [← hps, ← hbd]
                  exact ih.1 _ _ _ _ e₁.body hsz hJ' (env_congr_bindAll henv) hbdNo
              · rfl
        | case v alts d =>
          simp only [codeReadsVar, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hNo
          rw [Fir.eval.eq_def, Fir.eval.eq_def]; dsimp only
          rw [hEq v hNo.1.1]
          cases ρ₂.get? v with
          | none => rfl
          | some val =>
            dsimp only
            cases val.asCtor P.known with
            | none => rfl
            | some p =>
              dsimp only
              have hsz : Code.altsSize alts + Code.optSize d + Fir.jweight J₁ + 1 ≤ n := by
                simp only [Code.size] at hle; omega
              exact ih.2 ρ₁ ρ₂ J₁ J₂ p.1 alts d hsz hJ hEq hNo.1.2 hNo.2
        | ret a =>
          simp only [codeReadsVar] at hNo
          rw [Fir.eval.eq_def, Fir.eval.eq_def]; simp only [arg_eval_congr hEq hNo]
        | tcall f as =>
          simp only [codeReadsVar] at hNo
          rw [Fir.eval.eq_def, Fir.eval.eq_def]; simp only [evalArgs_congr hEq hNo]
        | trap => rw [Fir.eval.eq_def, Fir.eval.eq_def]
      · intro ρ₁ ρ₂ J₁ J₂ key alts d hle hJ hEq hAlts hOpt
        cases alts with
        | nil =>
          rw [Fir.evalAlts.eq_def, Fir.evalAlts.eq_def]
          cases d with
          | none => rfl
          | some c =>
            simp only [optReadsVar] at hOpt
            have hsz : c.size + Fir.jweight J₁ ≤ n := by
              simp only [Code.altsSize, Code.optSize] at hle; omega
            exact ih.1 ρ₁ ρ₂ J₁ J₂ c hsz hJ hEq hOpt
        | cons alt rest =>
          cases alt with
          | mk key' body =>
            simp only [altsReadsVar, Bool.or_eq_false_iff] at hAlts
            rw [Fir.evalAlts.eq_def, Fir.evalAlts.eq_def]; dsimp only
            split
            · have hsz : body.size + Fir.jweight J₁ ≤ n := by
                simp only [Code.altsSize] at hle; omega
              exact ih.1 ρ₁ ρ₂ J₁ J₂ body hsz hJ hEq hAlts.1
            · have hsz : Code.altsSize rest + Code.optSize d + Fir.jweight J₁ + 1 ≤ n := by
                have := Code.size_pos body
                simp only [Code.altsSize] at hle; omega
              exact ih.2 ρ₁ ρ₂ J₁ J₂ key rest d hsz hJ hEq hAlts.2 hOpt

private theorem eval_congr_unused {P : Program} {k : Nat} {x : Var}
    {ρ₁ ρ₂ : Env} {J : List Fir.JEntry} {c : Code}
    (hEq : ∀ u, u ≠ x → ρ₁.get? u = ρ₂.get? u)
    (hNo : codeReadsVar x c = false) :
    Fir.eval P k ρ₁ J c = Fir.eval P k ρ₂ J c :=
  (eval_congr_unused_aux P x k (c.size + Fir.jweight J)).1
    ρ₁ ρ₂ J J c (Nat.le_refl _) (.same J) hEq hNo

/-- Exact `Fir.eval` soundness of `foldOversizedCallStep?`: whenever a closed literal-argument
call evaluates to a `Nat` constant `m ≥ natLimit` within `closedCallFuel`, replacing the call
plus its immediately following oversized comparison by the folded `Bool` constructor preserves
`Fir.eval` identically for every clock `k ≥ closedCallFuel`. -/
theorem eval_foldOversizedCallStep {P : Program} {fsh : FunShapes}
    {x y : Var} {g : FunId} {as : List Arg} {op : Prim} {a b : Arg} {k' : Code}
    {cInfo : CtorInfo} {k : Nat} {ρ : Env} {J : List Fir.JEntry}
    (hStep : foldOversizedCallStep? P fsh x g as y op a b k' = some cInfo)
    (hClock : closedCallFuel ≤ k)
    (hEnv : ∀ v, v ≠ x → isSmallNatShape (fsh.var v) = true →
      ∃ n : Nat, n < natLimit ∧ ρ.get? v = some (.lit (.nat n))) :
    Fir.eval P k ρ J (.bind x (.call g as) (.bind y (.prim op [a, b]) k')) =
    Fir.eval P k ρ J (.bind y (.ctor cInfo []) k') := by
  unfold foldOversizedCallStep? at hStep
  simp only [guard, bind, Option.bind_eq_some_iff, pure, failure,
    Option.ite_none_right_eq_some, Bool.and_eq_true, bne_iff_ne,
    Bool.not_eq_true'] at hStep
  obtain ⟨_, ⟨⟨hxy, hNoRead⟩, _⟩, vs, hLit, hCallRest⟩ := hStep
  cases hCall : Fir.evalCall P closedCallFuel g vs with
  | ok val =>
    rw [hCall] at hCallRest
    cases val with
    | lit l =>
      cases l with
      | nat m =>
        dsimp only at hCallRest
        simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some] at hCallRest
        obtain ⟨_, ⟨hm, _⟩, hFold⟩ := hCallRest
        set substX : Arg → Arg := fun arg => if arg == .var x then Arg.lit (.nat m) else arg
        cases hFoldEq : foldOversizedNatCmpRhs P fsh (.prim op [substX a, substX b]) with
        | ctor ci args =>
          rw [hFoldEq] at hFold
          cases args with
          | nil =>
            simp only [Option.some.injEq] at hFold
            subst hFold
            have hCallK : Fir.evalCall P k g vs = .ok (.lit (.nat m)) := by
              have hMono := IxCC.Fir.evalCall_mono P g vs hClock
              dsimp only at hMono
              rw [hCall] at hMono
              exact hMono (by simp)
            set ρ' : Env := ρ.insert x (.lit (.nat m))
            have hSubstEq : ∀ arg : Arg, (substX arg).eval ρ' = arg.eval ρ' := by
              intro arg
              dsimp only [substX]
              split
              · rename_i hax
                have hax' : arg = .var x := beq_iff_eq.mp hax
                subst hax'
                simp [Arg.eval, ρ', IxCC.Src.NatMap.get?_insert_self]
              · rfl
            have hPrimEq :
                evalRhs P ρ' (.prim op [a, b]) =
                evalRhs P ρ' (.prim op [substX a, substX b]) := by
              simp [evalRhs, evalArgs, hSubstEq]
            have hNoX : ∀ arg : Arg, substX arg ≠ .var x := by
              intro arg; dsimp only [substX]
              split
              · intro h; cases h
              · rename_i hne; intro h; exact hne (beq_iff_eq.mpr h)
            have hFoldEval : evalRhs P ρ' (.prim op [substX a, substX b]) =
                evalRhs P ρ' (.ctor ci []) := by
              let fsh' : FunShapes := { fsh with vars := fsh.vars.insert x .any }
              have hSmallEq : ∀ arg : Arg, arg ≠ .var x →
                  isSmallNatArg fsh' arg = isSmallNatArg fsh arg := by
                intro arg hne
                cases arg with
                | lit l => cases l <;> rfl
                | erased => rfl
                | var z =>
                  have hzx : z ≠ x := fun h => hne (congrArg Arg.var h)
                  simp only [isSmallNatArg, fsh', IxCC.Fir.Shape.FunShapes.var, IxCC.Src.NatMap.getD]
                  rw [IxCC.Src.NatMap.get?_insert_ne _ _ hzx]
              have hEnv' : ∀ v, isSmallNatShape (fsh'.var v) = true →
                  ∃ n : Nat, n < natLimit ∧ ρ'.get? v = some (.lit (.nat n)) := by
                intro v hv
                by_cases hvx : v = x
                · subst hvx
                  simp only [fsh', IxCC.Fir.Shape.FunShapes.var, IxCC.Src.NatMap.getD,
                    IxCC.Src.NatMap.get?_insert_self, Option.getD_some, isSmallNatShape] at hv
                  cases hv
                · simp only [fsh', IxCC.Fir.Shape.FunShapes.var, IxCC.Src.NatMap.getD] at hv
                  rw [IxCC.Src.NatMap.get?_insert_ne _ _ hvx] at hv
                  obtain ⟨n, hn, hget⟩ := hEnv v hvx hv
                  exact ⟨n, hn, by rw [IxCC.Src.NatMap.get?_insert_ne _ _ hvx, hget]⟩
              have hRhsEq : foldOversizedNatCmpRhs P fsh' (.prim op [substX a, substX b]) =
                  foldOversizedNatCmpRhs P fsh (.prim op [substX a, substX b]) := by
                have ha' := hSmallEq (substX a) (hNoX a)
                have hb' := hSmallEq (substX b) (hNoX b)
                unfold foldOversizedNatCmpRhs
                dsimp only
                congr 1
                congr 1
                split
                · rw [ha']
                · rw [ha']
                · rw [hb']
                · rw [hb']
                · rw [ha']
                · rw [hb']
                · rfl
              have hSound := evalRhs_foldOversizedNatCmpRhs (P := P) (fsh := fsh') (ρ := ρ')
                (r := .prim op [substX a, substX b]) hEnv'
              rw [hRhsEq, hFoldEq] at hSound
              exact hSound.symm
            have hCtorOk : evalRhs P ρ' (.ctor ci []) = evalRhs P ρ (.ctor ci []) := rfl
            rw [Fir.eval.eq_def]
            dsimp only
            rw [litNatArgs?_eval hLit]
            dsimp only
            rw [hCallK]
            dsimp only
            rw [Fir.eval.eq_def]
            dsimp only
            rw [hPrimEq, hFoldEval, hCtorOk]
            conv_rhs => rw [Fir.eval.eq_def]
            dsimp only
            cases hC : evalRhs P ρ (.ctor ci []) with
            | ok v =>
              dsimp only
              apply eval_congr_unused _ hNoRead
              intro u hux
              by_cases huy : u = y
              · subst huy; simp [IxCC.Src.NatMap.get?_insert_self]
              · rw [IxCC.Src.NatMap.get?_insert_ne _ _ huy,
                  IxCC.Src.NatMap.get?_insert_ne _ _ huy,
                  IxCC.Src.NatMap.get?_insert_ne _ _ hux]
            | timeout | resource _ | trap | stuck => rfl
          | cons _ _ => cases hFold
        | arg _ | proj _ _ _ | prim _ _ | call _ _ => rw [hFoldEq] at hFold; cases hFold
      | str _ => cases hCallRest
    | ctor _ _ | erased => cases hCallRest
  | timeout | resource _ | trap | stuck => rw [hCall] at hCallRest; cases hCallRest

end FoldOversizedNatCmp

/-! ## Section 2: Qualification & Pattern-Matching Helpers -/

section Helpers

variable {F : Type} [Field F] [DecidableEq F]

@[simp] theorem qualifyName_u64_from_fields :
    qualifyName "UInt64::from_fields" = "UInt64::from_fields" := rfl

private theorem evalExpr_var_eq {world : World F} {locals : Environment F Nat}
    {nm : String} {v r : SourceValue F} {h h' : Heap F}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals (.var nm) h r h') :
    r = v ∧ h' = h := by
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv ev
  rw [hlook, Option.some.injEq, Prod.mk.injEq] at hl
  exact ⟨hl.2.symm, rfl⟩

private theorem evalExpr_let_tuple0_inv {world : World F} {locals : Environment F Nat}
    {e b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.letValue (.tuple []) e b) h r h') :
    ∃ hm, EvalExpr world [] locals e h (.tuple []) hm ∧ EvalExpr world [] locals b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    rename_i inp _ bindings
    cases inp with
    | tuple vs =>
      cases vs with
      | nil =>
        simp only [World.matchPattern, matchPatternWith, matchListWith,
          List.length_nil, bne_self_eq_false, List.attach_nil,
          pure, Except.pure, bind, Except.bind, Bool.false_eq_true, ↓reduceIte,
          Except.ok.injEq, Option.some.injEq] at hm
        subst hm
        exact ⟨_, hv, hb⟩
      | cons _ _ => simp [World.matchPattern, matchPatternWith] at hm
    | field _ | ptr _ _ | construct _ _ _ => simp [World.matchPattern, matchPatternWith] at hm

omit [Field F] in
private theorem selectArm_mem {world : World F} {types : Types} {heap : Heap F}
    {v : SourceValue F} {arms : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
    {bindings : Environment F Nat} {body : Aiur.Generic.Expr F}
    (h : SourceSemantics.selectArm world types heap v arms = .ok (some (bindings, body))) :
    ∃ pat, (pat, body) ∈ arms ∧ world.matchPattern types heap pat v = .ok (some bindings) := by
  induction arms with
  | nil => simp [SourceSemantics.selectArm, pure, Except.pure] at h
  | cons hd tl ih =>
    rcases hd with ⟨p, b⟩
    simp only [SourceSemantics.selectArm, bind, Except.bind] at h
    cases hm : world.matchPattern types heap p v with
    | error e => simp [hm] at h
    | ok res =>
      simp only [hm] at h
      cases res with
      | some bs =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨p, List.mem_cons_self, hm⟩
      | none =>
        obtain ⟨pat, hmem, hmp⟩ := ih h
        exact ⟨pat, List.mem_cons_of_mem _ hmem, hmp⟩

omit [Field F] in
private theorem matchListWith_binds_gen {world : World F} {heap : Heap F}
    {S : List (Aiur.Generic.Pattern F)} :
    ∀ {nms : List String} (ps : List { p // p ∈ S })
      {ws : List (SourceValue F)} {bindings : Environment F Nat},
      ps.map Subtype.val = nms.map Aiur.Generic.Pattern.bind →
      matchListWith
        (fun pat val => matchPatternWith world.constant world.constDepth [] heap pat.val val)
        ps ws = .ok (some bindings) →
      ws.length = nms.length ∧ bindings = nms.zip ws
  | [], [], [], bindings, _, h => by
    simp [matchListWith, pure, Except.pure] at h
    exact ⟨rfl, by simpa using h.symm⟩
  | [], [], _ :: _, _, _, h => by simp [matchListWith, pure, Except.pure] at h
  | [], _ :: _, _, _, hmap, _ => by simp at hmap
  | _ :: _, [], _, _, hmap, _ => by simp at hmap
  | _ :: _, _ :: _, [], _, _, h => by simp [matchListWith, pure, Except.pure] at h
  | nm :: nms, p :: ps, w :: ws, bindings, hmap, h => by
    simp only [List.map_cons, List.cons.injEq] at hmap
    obtain ⟨hpVal, hpsVal⟩ := hmap
    simp only [matchListWith, hpVal, matchPatternWith, bind, Except.bind, pure, Except.pure] at h
    cases hr : matchListWith
        (fun pat val => matchPatternWith world.constant world.constDepth [] heap pat.val val)
        ps ws with
    | error e => simp [hr] at h
    | ok res =>
      simp only [hr] at h
      cases res with
      | none => simp at h
      | some rest =>
        simp only [Except.ok.injEq, Option.some.injEq] at h
        obtain ⟨hlen, hrest⟩ := matchListWith_binds_gen ps hpsVal hr
        refine ⟨congrArg Nat.succ hlen, ?_⟩
        rw [← h, hrest]
        rfl

omit [Field F] in
private theorem matchListWith_binds {world : World F} {heap : Heap F}
    {nms : List String} {ws : List (SourceValue F)} {bindings : Environment F Nat}
    (h : matchListWith
      (fun pat val => matchPatternWith world.constant world.constDepth [] heap pat.val val)
      (nms.map Aiur.Generic.Pattern.bind).attach ws = .ok (some bindings)) :
    ws.length = nms.length ∧ bindings = nms.zip ws := by
  have hval : (nms.map (Aiur.Generic.Pattern.bind (α := F))).attach.map Subtype.val =
      nms.map Aiur.Generic.Pattern.bind := by
    simpa using (List.attach_map_val (l := nms.map (Aiur.Generic.Pattern.bind (α := F))) (f := id))
  exact matchListWith_binds_gen (nms.map Aiur.Generic.Pattern.bind).attach hval h

omit [Field F] [DecidableEq F] in
private theorem find?_zip_append {nm : String} :
    ∀ {nms : List String} {ws : List (SourceValue F)} {rest : Environment F Nat}
      {i : Nat} {v : SourceValue F},
      nms.Nodup →
      nms.length = ws.length →
      nms[i]? = some nm →
      ws[i]? = some v →
      (nms.zip ws ++ rest).find? (·.1 == nm) = some (nm, v)
  | [], _, _, _, _, _, _, hnm, _ => by simp at hnm
  | a :: nms, [], _, _, _, _, hlen, _, _ => by simp at hlen
  | a :: nms, w :: ws, rest, 0, v, _, _, hnm, hw => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hnm hw
    subst hnm hw
    simp
  | a :: nms, w :: ws, rest, i + 1, v, hnd, hlen, hnm, hw => by
    simp only [List.getElem?_cons_succ] at hnm hw
    simp only [List.nodup_cons] at hnd
    have hmem : nm ∈ nms := List.mem_of_getElem? hnm
    have hne : a ≠ nm := fun heq => hnd.1 (heq ▸ hmem)
    have hbeq : (a == nm) = false := beq_false_of_ne hne
    simp only [List.zip_cons_cons, List.cons_append, List.find?_cons, hbeq]
    exact find?_zip_append hnd.2 (Nat.succ.inj hlen) hnm hw

omit [Field F] [DecidableEq F] in
private theorem find?_zip_exact {nm : String} {nms : List String} {ws : List (SourceValue F)}
    {i : Nat} {v : SourceValue F}
    (hnd : nms.Nodup) (hlen : nms.length = ws.length)
    (hnm : nms[i]? = some nm) (hw : ws[i]? = some v) :
    (nms.zip ws).find? (·.1 == nm) = some (nm, v) := by
  simpa using find?_zip_append (rest := []) hnd hlen hnm hw

private theorem fieldName_inj (pfx : String) {i j : Nat}
    (h : pfx ++ "_" ++ String.ofList (natDigits i) =
         pfx ++ "_" ++ String.ofList (natDigits j)) : i = j := by
  have h1 := congrArg String.toList h
  simp only [String.toList_append, String.toList_ofList] at h1
  have h2 : natDigits i = natDigits j := List.append_cancel_left h1
  apply localName_inj
  unfold localName
  rw [h2]

private theorem nodup_fieldNames {α : Type*} (pfx : String) (fl : List α) :
    (fl.zipIdx.map fun (_, fi) => pfx ++ "_" ++ String.ofList (natDigits fi)).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at hij
  exact Fin.ext (fieldName_inj pfx hij)

private theorem evalExpr_seqUnitList_inv {world : World F} {locals : Environment F Nat} :
    ∀ {es : List Expr} {h h' : Heap F} {r : SourceValue F},
      EvalExpr world [] locals (qualifyExprF F (seqUnitList es)) h r h' →
      (∀ e ∈ es, ∀ h0 h1 v,
        EvalExpr world [] locals (qualifyExprF F e) h0 v h1 → h1 = h0) →
      h' = h ∧ ∀ e ∈ es, ∃ v, EvalExpr world [] locals (qualifyExprF F e) h v h
  | [], h, h', r, ev, _ => by
    simp only [seqUnitList, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map] at ev
    cases ev with
    | tuple hargs =>
      cases hargs
      exact ⟨rfl, fun _ hm => by cases hm⟩
  | [e], h, h', r, ev, hpres => by
    have hh := hpres e List.mem_cons_self h h' r ev
    subst hh
    exact ⟨rfl, fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨r, ev⟩⟩
  | e1 :: e2 :: rest, h, h', r, ev, hpres => by
    simp only [seqUnitList, seqE, qualifyExprF, qualifyExpr, qualifyPat,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map] at ev
    obtain ⟨v1, hm, ev1, evRest⟩ := evalExpr_let_wildcard_inv ev
    have hh1 := hpres e1 List.mem_cons_self h hm v1 ev1
    subst hh1
    obtain ⟨hh2, hall⟩ := evalExpr_seqUnitList_inv evRest
      (fun x hx => hpres x (List.mem_cons_of_mem _ hx))
    subst hh2
    refine ⟨rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨v1, ev1⟩
    · exact hall x hx'

private theorem evalArgs_varList_inv {world : World F} {locals : Environment F Nat} :
    ∀ {nms : List String} {expected : List (SourceValue F)} {h h' : Heap F}
      {vs : List (SourceValue F)},
      nms.length = expected.length →
      (∀ (i : Nat) nm v, nms[i]? = some nm → expected[i]? = some v →
        locals.find? (·.1 == nm) = some (nm, v)) →
      EvalArgs world [] locals
        ((nms.map vE).map (qualifyExprF F)) h vs h' →
      vs = expected ∧ h' = h
  | [], [], _, _, _, _, _, ev => by cases ev; exact ⟨rfl, rfl⟩
  | [], _ :: _, _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _, _ => by simp at hlen
  | nm :: nms, v :: vs', h, h', res, hlen, hlook, ev => by
    simp only [List.map_cons, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with
    | cons hhd htl =>
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (hlook 0 nm v rfl rfl) hhd
      obtain ⟨rfl, rfl⟩ := evalArgs_varList_inv (Nat.succ.inj hlen)
        (fun i nm' v' h1 h2 => hlook (i + 1) nm' v' h1 h2) htl
      exact ⟨rfl, rfl⟩

end Helpers

/-! ## Section 3: Heap Independence of Shape-Checkable `TVR` -/

section HeapIndep

variable {F : Type} [Field F]

mutual

/-- Every `isShapeCheckableRep` return representation is pointer-free, so its `TVR`
relation is completely independent of the heap! -/
theorem TVR_heap_indep_of_shapeCheckable {P : Program} {cert : ShapeCert} {feat : Features} :
    ∀ {fuel : Nat} {r : Rep} {h1 h2 : Heap F} {v : Fir.Val} {w : SourceValue F},
      isShapeCheckableRep P cert feat fuel r = true →
      TVR P cert feat h1 r v w →
      TVR P cert feat h2 r v w
  | _, .irr, _, _, _, _, _, .irr => .irr
  | _, .nat _, _, _, _, _, _, .nat hs => .nat hs
  | _, .w8, _, _, _, _, _, .w8 hs => .w8 hs
  | _, .w16, _, _, _, _, _, .w16 hs => .w16 hs
  | _, .w32, _, _, _, _, _, .w32 hw => .w32 hw
  | _, .w64, _, _, _, _, _, .w64 hw => .w64 hw
  | _, .enum _, _, _, _, _, _, .enumVal he hm hi hk ha => .enumVal he hm hi hk ha
  | 0, .data _, _, _, _, _, hsc, _ => by cases hsc
  | fuel + 1, .data d, _, _, _, _, hsc, .dataVal hd hc hi hk ha hfl hfs => by
    simp only [isShapeCheckableRep, hd, Bool.and_eq_true] at hsc
    obtain ⟨_, hAll⟩ := hsc
    rw [List.all_eq_true] at hAll
    have hflOk := List.all_eq_true.mp (hAll _ hc)
    refine .dataVal hd hc hi hk ha hfl (TVRDataFields_heap_indep_of_shapeCheckable fuel ?_ hfs)
    intro sh hsh
    have hshOk := hflOk sh hsh
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hshOk
    exact ⟨hshOk.1.1, hshOk.2⟩
  | _, .obj, _, _, _, _, hsc, _ => by
    unfold isShapeCheckableRep at hsc
    cases hsc

theorem TVRDataFields_heap_indep_of_shapeCheckable {P : Program} {cert : ShapeCert}
    {feat : Features} (fuel : Nat) :
    ∀ {d : Nat} {fl : List Shape} {vs : List Fir.Val} {ws : List (SourceValue F)}
      {h1 h2 : Heap F},
      (∀ sh ∈ fl, dataFieldNeedsPtr P cert feat d (repOf P cert feat sh) = false ∧
        isShapeCheckableRep P cert feat fuel (repOf P cert feat sh) = true) →
      TVRDataFields P cert feat h1 d fl vs ws →
      TVRDataFields P cert feat h2 d fl vs ws
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, hAll, .consInline hnp hdRel tlRel =>
    let h0 := hAll _ List.mem_cons_self
    .consInline hnp
      (TVR_heap_indep_of_shapeCheckable h0.2 hdRel)
      (TVRDataFields_heap_indep_of_shapeCheckable fuel
        (fun sh hsh => hAll sh (List.mem_cons_of_mem _ hsh)) tlRel)
  | _, _, _, _, _, _, hAll, .consPtr hp _ _ _ => by
    have h0 := hAll _ List.mem_cons_self
    rw [hp] at h0
    cases h0.1

end

end HeapIndep

/-! ## Section 4: `U4` Shape-Check Contract Bundle & Soundness (`shapeCheckExpr_sound`) -/

section ShapeCheckSound

variable {F : Type} [Field F] [DecidableEq F]

/-- Operational contracts of the range-check and word-constructor helpers invoked by
`GuessLower`'s `U4` canonicality checks. Discharged directly from `TypedGadgets`! -/
structure ShapeCheckSpecs (world : World F) : Prop where
  fc : FieldCompatible64 F
  check_u8 : ∀ v h r h',
    EvalFn world (qualified "check_u8") [v] h r h' →
    r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < 2 ^ 8 ∧ v = .field (n : F)
  check_u16 : ∀ v h r h',
    EvalFn world (qualified "check_u16") [v] h r h' →
    r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < 2 ^ 16 ∧ v = .field (n : F)
  check_u24 : ∀ v h r h',
    EvalFn world (qualified "check_u24") [v] h r h' →
    r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < 2 ^ 24 ∧ v = .field (n : F)
  check_u56 : ∀ v h r h',
    EvalFn world (qualified "check_u56") [v] h r h' →
    r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < natLimit ∧ v = .field (n : F)
  sub_borrow_56 : ∀ x y h r h', x < natLimit → y < natLimit →
    EvalFn world (qualified "sub_borrow_56") [.field (x : F), .field (y : F)] h r h' →
    h' = h ∧ r = .tuple [.field ((x - y : Nat) : F), .field (if y ≤ x then (1 : F) else 0)]
  u32_from_fields : ∀ raw h r h',
    EvalFn world "UInt32::from_fields" [raw] h r h' →
    h' = h ∧ ∃ n : Nat, isU32Val n r
  u64_from_fields : ∀ raw h r h',
    EvalFn world "UInt64::from_fields" [raw] h r h' →
    h' = h ∧ ∃ n : Nat, isU64Val n r

/-- Discharge `ShapeCheckSpecs` directly from `TypedGadgets` `WorldHasFn` hypotheses! -/
theorem ShapeCheckSpecs.of_world {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F) (hbc : ByteCheckSpec world usePair)
    (hu8 : WorldHasFn world (qualified "check_u8") ["x"]
      (qualifyExprF F (checkU8Fn usePair).body))
    (hu16 : WorldHasFn world (qualified "check_u16") ["x"]
      (qualifyExprF F (checkU16Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hu32 : ∀ raw h r h', EvalFn world "UInt32::from_fields" [raw] h r h' →
      h' = h ∧ ∃ n : Nat, isU32Val n r)
    (hu64 : ∀ raw h r h', EvalFn world "UInt64::from_fields" [raw] h r h' →
      h' = h ∧ ∃ n : Nat, isU64Val n r) :
    ShapeCheckSpecs world where
  fc := fc
  check_u8 := fun _ _ _ _ ev => eval_check_u8 hbc hu8 ev
  check_u16 := fun _ _ _ _ ev => eval_check_u16 hbc hu16 ev
  check_u24 := fun _ _ _ _ ev => eval_check_u24 hbc hu24 ev
  check_u56 := fun _ _ _ _ ev => eval_check_u56 hbc hu56 ev
  sub_borrow_56 := fun _ _ _ _ _ hx hy ev => eval_sub_borrow_56 fc hbc hsub hx hy ev
  u32_from_fields := hu32
  u64_from_fields := hu64

/-- **Soundness of `fromRawExpr`** for `.w32` and `.w64`: raw advice passed through
`UInt32::from_fields` / `UInt64::from_fields` satisfies `TVR` and preserves the heap. -/
theorem fromRawExpr_sound {world : World F} {P : Program} {cert : ShapeCert} {feat : Features}
    (specs : ShapeCheckSpecs world) {locals : Environment F Nat}
    {rawNm : String} {rawVal yVal : SourceValue F} {h h' : Heap F}
    (hlook : locals.find? (·.1 == rawNm) = some (rawNm, rawVal))
    {r : Rep} (hword : r = .w32 ∨ r = .w64)
    (ev : EvalExpr world [] locals (qualifyExprF F (fromRawExpr r (vE rawNm))) h yVal h') :
    h' = h ∧ ∃ v : Fir.Val, TVR P cert feat h r v yVal := by
  rcases hword with rfl | rfl
  · simp only [fromRawExpr, callE, vE, qualifyExprF, qualifyExpr, qualifyName_u32_from_fields,
      Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
    obtain ⟨vr, _, evr, hcal⟩ := evalExpr_call1_inv ev
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evr
    obtain ⟨rfl, n, hn⟩ := specs.u32_from_fields _ _ _ _ hcal
    exact ⟨rfl, .lit (.nat n), .w32 hn⟩
  · simp only [fromRawExpr, callE, vE, qualifyExprF, qualifyExpr, qualifyName_u64_from_fields,
      Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
    obtain ⟨vr, _, evr, hcal⟩ := evalExpr_call1_inv ev
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evr
    obtain ⟨rfl, n, hn⟩ := specs.u64_from_fields _ _ _ _ hcal
    exact ⟨rfl, .lit (.nat n), .w64 hn⟩

/-- **Heap-preservation of `shapeCheckExpr`** on all shape-checkable non-word representations. -/
theorem shapeCheckExpr_heap {world : World F} {P : Program} {cert : ShapeCert} {feat : Features}
    (specs : ShapeCheckSpecs world) :
    ∀ (fuel : Nat) (pfx : String) (r : Rep) (yNm : String)
      (locals : Environment F Nat) (h h' : Heap F) (out : SourceValue F),
      isShapeCheckableRep P cert feat fuel r = true →
      EvalExpr world [] locals (qualifyExprF F (shapeCheckExpr P cert feat fuel pfx r yNm).1) h out h' →
      h' = h
  | _, _, .irr, _, _, _, _, _, _, ev => by
    simp only [shapeCheckExpr, vE, qualifyExprF, qualifyExpr, qualifyPat,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
    obtain ⟨hm, evv, evu⟩ := evalExpr_let_tuple0_inv ev
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evv
    cases evu with | tuple hargs => cases hargs; rfl
  | _, _, .nat b, _, _, _, _, _, hsc, ev => by
    unfold shapeCheckExpr at ev
    dsimp only at ev
    split at ev
    · simp only [callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u56,
        Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
      obtain ⟨_, _, evv, hcal⟩ := evalExpr_call1_inv ev
      obtain ⟨_, rfl⟩ := evalExpr_var_inv evv
      exact (specs.check_u56 _ _ _ _ hcal).2.1
    · split at ev
      · simp only [callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u8,
          Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
        obtain ⟨_, _, evv, hcal⟩ := evalExpr_call1_inv ev
        obtain ⟨_, rfl⟩ := evalExpr_var_inv evv
        exact (specs.check_u8 _ _ _ _ hcal).2.1
      · split at ev
        · simp only [callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u16,
            Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
          obtain ⟨_, _, evv, hcal⟩ := evalExpr_call1_inv ev
          obtain ⟨_, rfl⟩ := evalExpr_var_inv evv
          exact (specs.check_u16 _ _ _ _ hcal).2.1
        · split at ev
          · simp only [callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u24,
              Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
            obtain ⟨_, _, evv, hcal⟩ := evalExpr_call1_inv ev
            obtain ⟨_, rfl⟩ := evalExpr_var_inv evv
            exact (specs.check_u24 _ _ _ _ hcal).2.1
          · rename_i hne56 _ _ _
            simp only [seqE, callE, vE, litE, qualifyExprF, qualifyExpr, qualifyPat,
              qualifyName_check_u56, qualifyName_sub_borrow_56,
              Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
            obtain ⟨_, _, evChk, k1⟩ := evalExpr_let_wildcard_inv ev
            obtain ⟨vy, _, evy, hc56⟩ := evalExpr_call1_inv evChk
            obtain ⟨hlook, rfl⟩ := evalExpr_var_inv evy
            obtain ⟨_, rfl, n, hnLt, rfl⟩ := specs.check_u56 _ _ _ _ hc56
            obtain ⟨_, vge, _, evSub, k2⟩ := evalExpr_let_wild_tuple2_inv k1
            obtain ⟨vy', vb', _, _, evy', evb', hsub⟩ := evalExpr_call2_inv evSub
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evy'
            obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evb'
            have hbLt : min b natLimit < natLimit := by
              have hle := Nat.min_le_right b natLimit
              have hne : min b natLimit ≠ natLimit := by simpa using hne56
              omega
            obtain ⟨rfl, _⟩ := specs.sub_borrow_56 n (min b natLimit) _ _ _ hnLt hbLt hsub
            obtain ⟨_, _, _, evge, ev0, _, _⟩ := evalExpr_assertEq_inv k2
            obtain ⟨_, rfl⟩ := evalExpr_var_inv evge
            obtain ⟨_, rfl⟩ := evalExpr_literal_inv ev0
            rfl
  | _, _, .w8, _, _, _, _, _, _, ev => by
    simp only [shapeCheckExpr, callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u8,
      Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
    obtain ⟨_, _, evv, hcal⟩ := evalExpr_call1_inv ev
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evv
    exact (specs.check_u8 _ _ _ _ hcal).2.1
  | _, _, .w16, _, _, _, _, _, _, ev => by
    simp only [shapeCheckExpr, callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u16,
      Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
    obtain ⟨_, _, evv, hcal⟩ := evalExpr_call1_inv ev
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evv
    exact (specs.check_u16 _ _ _ _ hcal).2.1
  | _, _, .w32, _, _, _, _, _, _, ev => by
    simp only [shapeCheckExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map] at ev
    cases ev with | tuple hargs => cases hargs; rfl
  | _, _, .w64, _, _, _, _, _, _, ev => by
    simp only [shapeCheckExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map] at ev
    cases ev with | tuple hargs => cases hargs; rfl
  | _, _, .enum ind, yNm, locals, h, h', out, hsc, ev => by
    unfold shapeCheckExpr at ev
    simp only [isShapeCheckableRep, validEnum] at hsc
    cases he : cert.enum? ind with
    | none => simp [he] at hsc
    | some ks =>
      simp only [he] at ev
      split at ev
      · simp only [trapE, seqE, litE, qualifyExprF, qualifyExpr, qualifyPat,
          Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
          Nat.cast_zero, Nat.cast_one] at ev
        obtain ⟨_, _, hass, _⟩ := evalExpr_let_wildcard_inv ev
        obtain ⟨_, _, _, e0, e1, h01, _⟩ := evalExpr_assertEq_inv hass
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e0
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e1
        exact False.elim (zero_ne_one (Value.field.inj h01))
      · simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
        cases ev with
        | matchValue evs hsel hbr =>
          obtain ⟨_, hh⟩ := evalExpr_var_inv evs
          subst hh
          obtain ⟨pat, hmem, _⟩ := selectArm_mem hsel
          rw [List.mem_map] at hmem
          obtain ⟨⟨p1, b1⟩, hmem1, hEqArm1⟩ := hmem
          rw [List.mem_map] at hmem1
          obtain ⟨⟨p0, b0⟩, hmem0, hEqArm0⟩ := hmem1
          rw [List.mem_filterMap] at hmem0
          obtain ⟨k, _, hMap⟩ := hmem0
          cases hce : Lower.ctorEntry? P k with
          | none => simp [hce] at hMap
          | some ce =>
            simp only [hce, Option.map_some, Option.some.injEq] at hMap
            obtain ⟨_, hb0⟩ := Prod.mk.inj hMap
            obtain ⟨_, hb1⟩ := Prod.mk.inj hEqArm0
            obtain ⟨_, hbody⟩ := Prod.mk.inj hEqArm1
            subst hb0 hb1 hbody
            simp only [qualifyExpr, Aiur.Generic.Expr.map, List.map] at hbr
            cases hbr with | tuple hargs => cases hargs; rfl
  | 0, _, .data _, _, _, _, _, _, hsc, _ => by simp [isShapeCheckableRep] at hsc
  | fuel + 1, pfx, .data d, yNm, locals, h, h', out, hsc, ev => by
    unfold shapeCheckExpr at ev
    simp only [isShapeCheckableRep] at hsc
    cases hd : cert.data? d with
    | none => simp [hd] at hsc
    | some D =>
      simp only [hd, Bool.and_eq_true, List.all_eq_true] at hsc
      simp only [hd] at ev
      split at ev
      · simp only [trapE, seqE, litE, qualifyExprF, qualifyExpr, qualifyPat,
          Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
          Nat.cast_zero, Nat.cast_one] at ev
        obtain ⟨_, _, hass, _⟩ := evalExpr_let_wildcard_inv ev
        obtain ⟨_, _, _, e0, e1, h01, _⟩ := evalExpr_assertEq_inv hass
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e0
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e1
        exact False.elim (zero_ne_one (Value.field.inj h01))
      · simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
        cases ev with
        | matchValue evs hsel hbr =>
          obtain ⟨_, hh⟩ := evalExpr_var_inv evs
          subst hh
          obtain ⟨pat, hmem, _⟩ := selectArm_mem hsel
          rw [List.mem_map] at hmem
          obtain ⟨⟨p1, b1⟩, hmem1, hEqArm1⟩ := hmem
          rw [List.mem_map] at hmem1
          obtain ⟨⟨p0, b0⟩, hmem0, hEqArm0⟩ := hmem1
          rw [List.mem_map] at hmem0
          obtain ⟨⟨arm0, _⟩, harm0, hEq0⟩ := hmem0
          rw [List.mem_filterMap] at harm0
          obtain ⟨⟨k, fl⟩, hkMem, hMap⟩ := harm0
          cases hce : Lower.ctorEntry? P k with
          | none => simp [hce] at hMap
          | some ce =>
            rcases ce with ⟨idx, e⟩
            simp only [hce, Option.map_some, Option.some.injEq] at hMap
            obtain ⟨hArmEq, _⟩ := Prod.mk.inj hMap
            obtain ⟨_, hb1⟩ := Prod.mk.inj hEqArm0
            obtain ⟨_, hbody⟩ := Prod.mk.inj hEqArm1
            subst hEq0 hb1 hbody
            rw [← hArmEq] at hbr
            change EvalExpr world [] _ (qualifyExprF F (seqUnitList _)) _ out h' at hbr
            refine (evalExpr_seqUnitList_inv hbr ?_).1
            intro fe hfe h0 h1 v evFe
            rw [List.mem_map] at hfe
            obtain ⟨⟨fnm, fe', fd'⟩, hmem1, rfl⟩ := hfe
            rw [List.mem_map] at hmem1
            obtain ⟨⟨sh, fi⟩, hshMem, hEqFe⟩ := hmem1
            have hfeEq : fe' = (shapeCheckExpr P cert feat fuel
                (pfx ++ "_" ++ String.ofList (natDigits fi))
                (repOf P cert feat sh)
                (pfx ++ "_" ++ String.ofList (natDigits fi))).1 := by
              have := congrArg (fun p => p.2.1) hEqFe
              simpa using this.symm
            rw [hfeEq] at evFe
            have hshInFl : sh ∈ fl := by
              have hzi := List.mem_zipIdx hshMem
              have hlt : fi < fl.length := by simpa using hzi.2.1
              have heq : sh = fl[fi] := by simpa using hzi.2.2
              rw [heq]; exact List.getElem_mem hlt
            have hshOk := hsc.2 (k, fl) hkMem sh hshInFl
            exact shapeCheckExpr_heap specs fuel _ _ _ _ _ _ _ hshOk.2 evFe
  | _, _, .obj, _, _, _, _, _, hsc, _ => by simp [isShapeCheckableRep] at hsc

/-- **U4 Canonical Shape-Check Soundness (`shapeCheckExpr_sound`)**:
Any `EvalExpr` derivation of `shapeCheckExpr` on a shape-checkable non-word
representation `r` proves `h' = h` and `∃ v, TVR P cert feat h r v yVal`,
regardless of what arbitrary raw constant the host `hint` returned! -/
theorem shapeCheckExpr_sound {world : World F} {P : Program} {cert : ShapeCert} {feat : Features}
    (specs : ShapeCheckSpecs world) :
    ∀ (fuel : Nat) (pfx : String) (r : Rep) (yNm : String)
      (locals : Environment F Nat) (yVal out : SourceValue F) (h h' : Heap F),
      isShapeCheckableRep P cert feat fuel r = true →
      r ≠ .w32 → r ≠ .w64 →
      locals.find? (·.1 == yNm) = some (yNm, yVal) →
      EvalExpr world [] locals (qualifyExprF F (shapeCheckExpr P cert feat fuel pfx r yNm).1) h out h' →
      h' = h ∧ ∃ v : Fir.Val, TVR P cert feat h r v yVal
  | _, _, .irr, yNm, locals, yVal, out, h, h', _, _, _, hlook, ev => by
    simp only [shapeCheckExpr, vE, qualifyExprF, qualifyExpr, qualifyPat,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
    obtain ⟨hm, evv, evu⟩ := evalExpr_let_tuple0_inv ev
    obtain ⟨hyEq, rfl⟩ := evalExpr_var_eq hlook evv
    cases evu with
    | tuple hargs =>
      cases hargs
      exact ⟨rfl, .erased, hyEq ▸ .irr⟩
  | _, _, .nat b, yNm, locals, yVal, out, h, h', hsc, _, _, hlook, ev => by
    unfold shapeCheckExpr at ev
    dsimp only at ev
    split at ev
    · rename_i heq56
      have hbound : min b natLimit = natLimit := beq_iff_eq.mp heq56
      simp only [callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u56,
        Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
      obtain ⟨vy, _, evy, hcal⟩ := evalExpr_call1_inv ev
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evy
      obtain ⟨_, rfl, n, hnLt, rfl⟩ := specs.check_u56 _ _ _ _ hcal
      exact ⟨rfl, .lit (.nat n), .nat (by rw [hbound]; exact hnLt)⟩
    · split at ev
      · rename_i heq8
        have hbound : min b natLimit = 256 := beq_iff_eq.mp heq8
        simp only [callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u8,
          Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
        obtain ⟨vy, _, evy, hcal⟩ := evalExpr_call1_inv ev
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evy
        obtain ⟨_, rfl, n, hnLt, rfl⟩ := specs.check_u8 _ _ _ _ hcal
        exact ⟨rfl, .lit (.nat n), .nat (by rw [hbound]; exact hnLt)⟩
      · split at ev
        · rename_i heq16
          have hbound : min b natLimit = 65536 := beq_iff_eq.mp heq16
          simp only [callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u16,
            Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
          obtain ⟨vy, _, evy, hcal⟩ := evalExpr_call1_inv ev
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evy
          obtain ⟨_, rfl, n, hnLt, rfl⟩ := specs.check_u16 _ _ _ _ hcal
          exact ⟨rfl, .lit (.nat n), .nat (by rw [hbound]; exact hnLt)⟩
        · split at ev
          · rename_i heq24
            have hbound : min b natLimit = 16777216 := beq_iff_eq.mp heq24
            simp only [callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u24,
              Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
            obtain ⟨vy, _, evy, hcal⟩ := evalExpr_call1_inv ev
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evy
            obtain ⟨_, rfl, n, hnLt, rfl⟩ := specs.check_u24 _ _ _ _ hcal
            exact ⟨rfl, .lit (.nat n), .nat (by rw [hbound]; exact hnLt)⟩
          · rename_i hne56 _ _ _
            simp only [seqE, callE, vE, litE, qualifyExprF, qualifyExpr, qualifyPat,
              qualifyName_check_u56, qualifyName_sub_borrow_56,
              Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
              Nat.cast_zero] at ev
            obtain ⟨_, _, evChk, k1⟩ := evalExpr_let_wildcard_inv ev
            obtain ⟨vy, _, evy, hc56⟩ := evalExpr_call1_inv evChk
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evy
            obtain ⟨_, rfl, n, hnLt, rfl⟩ := specs.check_u56 _ _ _ _ hc56
            obtain ⟨_, vge, _, evSub, k2⟩ := evalExpr_let_wild_tuple2_inv k1
            obtain ⟨vy', vb', _, _, evy', evb', hsub⟩ := evalExpr_call2_inv evSub
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evy'
            obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evb'
            have hbLt : min b natLimit < natLimit := by
              have hle := Nat.min_le_right b natLimit
              have hne : min b natLimit ≠ natLimit := by simpa using hne56
              omega
            obtain ⟨rfl, hsubEq⟩ := specs.sub_borrow_56 n (min b natLimit) _ _ _ hnLt hbLt hsub
            simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hsubEq
            obtain ⟨_, rfl⟩ := hsubEq
            obtain ⟨v1, v2, _, evge, ev0, hEq0, _⟩ := evalExpr_assertEq_inv k2
            obtain ⟨hv1, rfl⟩ := evalExpr_var_eq
              (v := .field (if min b natLimit ≤ n then (1 : F) else 0)) rfl evge
            obtain ⟨hv2, rfl⟩ := evalExpr_literal_inv ev0
            rw [hv1, hv2] at hEq0
            have hnLtB : n < min b natLimit := by
              by_contra hge
              have hle : min b natLimit ≤ n := by omega
              simp only [hle, ↓reduceIte] at hEq0
              exact one_ne_zero (Value.field.inj hEq0)
            exact ⟨rfl, .lit (.nat n), .nat hnLtB⟩
  | _, _, .w8, yNm, locals, yVal, out, h, h', _, _, _, hlook, ev => by
    simp only [shapeCheckExpr, callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u8,
      Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
    obtain ⟨vy, _, evy, hcal⟩ := evalExpr_call1_inv ev
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evy
    obtain ⟨_, rfl, n, hnLt, rfl⟩ := specs.check_u8 _ _ _ _ hcal
    exact ⟨rfl, .lit (.nat n), .w8 hnLt⟩
  | _, _, .w16, yNm, locals, yVal, out, h, h', _, _, _, hlook, ev => by
    simp only [shapeCheckExpr, callE, vE, qualifyExprF, qualifyExpr, qualifyName_check_u16,
      Option.map_some, Aiur.Generic.Expr.map, List.map] at ev
    obtain ⟨vy, _, evy, hcal⟩ := evalExpr_call1_inv ev
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evy
    obtain ⟨_, rfl, n, hnLt, rfl⟩ := specs.check_u16 _ _ _ _ hcal
    exact ⟨rfl, .lit (.nat n), .w16 hnLt⟩
  | _, _, .w32, _, _, _, _, _, _, _, hne32, _, _, _ => False.elim (hne32 rfl)
  | _, _, .w64, _, _, _, _, _, _, _, _, hne64, _, _ => False.elim (hne64 rfl)
  | _, _, .enum ind, yNm, locals, yVal, out, h, h', hsc, _, _, hlook, ev => by
    unfold shapeCheckExpr at ev
    simp only [isShapeCheckableRep, validEnum] at hsc
    cases he : cert.enum? ind with
    | none => simp [he] at hsc
    | some ks =>
      simp only [he, Bool.and_eq_true, List.all_eq_true] at hsc
      simp only [he] at ev
      split at ev
      · simp only [trapE, seqE, litE, qualifyExprF, qualifyExpr, qualifyPat,
          Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
          Nat.cast_zero, Nat.cast_one] at ev
        obtain ⟨_, _, hass, _⟩ := evalExpr_let_wildcard_inv ev
        obtain ⟨_, _, _, e0, e1, h01, _⟩ := evalExpr_assertEq_inv hass
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e0
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e1
        exact False.elim (zero_ne_one (Value.field.inj h01))
      · simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
        cases ev with
        | matchValue evs hsel hbr =>
          obtain ⟨hyEq, hhEq⟩ := evalExpr_var_eq hlook evs
          subst hhEq
          rw [hyEq] at hsel
          obtain ⟨pat, hmem, hmp⟩ := selectArm_mem hsel
          rw [List.mem_map] at hmem
          obtain ⟨⟨p1, b1⟩, hmem1, hEqArm1⟩ := hmem
          rw [List.mem_map] at hmem1
          obtain ⟨⟨p0, b0⟩, hmem0, hEqArm0⟩ := hmem1
          rw [List.mem_filterMap] at hmem0
          obtain ⟨k, hkMem, hMap⟩ := hmem0
          cases hce : Lower.ctorEntry? P k with
          | none => simp [hce] at hMap
          | some ce =>
            rcases ce with ⟨idx, entry⟩
            simp only [hce, Option.map_some, Option.some.injEq] at hMap
            obtain ⟨hget, hkeyEq⟩ := ctorEntry?_sound hce
            have har0 : entry.arity = 0 := by
              have hka := hsc.2 k hkMem
              simp only [hce, beq_iff_eq] at hka
              exact hka
            obtain ⟨hp0, hb0⟩ := Prod.mk.inj hMap
            obtain ⟨hp1, hb1⟩ := Prod.mk.inj hEqArm0
            obtain ⟨hpat, hbody⟩ := Prod.mk.inj hEqArm1
            subst hp0 hb0 hp1 hb1 hpat hbody
            simp only [qualifyExpr, Aiur.Generic.Expr.map, List.map] at hbr
            cases hbr with
            | tuple hargs =>
              cases hargs
              simp only [qualifyPat, qualifyTy, qualifyName_enumName, Aiur.Generic.Pattern.map,
                List.map] at hmp
              cases yVal with
              | construct en ctor args =>
                simp only [World.matchPattern, matchPatternWith, constructorName,
                  Aiur.Generic.Ty.subst, Aiur.Generic.Ty.toCore, List.length_nil] at hmp
                split at hmp
                · simp [pure, Except.pure] at hmp
                · rename_i hok
                  simp only [Bool.or_eq_true, bne_iff_ne, not_or, Decidable.not_not] at hok
                  obtain ⟨⟨rfl, rfl⟩, hlen0⟩ := hok
                  have hargsNil : args = [] := List.eq_nil_of_length_eq_zero hlen0.symm
                  subst hargsNil
                  let cInfo : CtorInfo :=
                    { key := k, tag := entry.tag, nobj := 0, nscalar := 0, fieldKinds := [] }
                  refine ⟨rfl, .ctor cInfo [], ?_⟩
                  simpa [cInfo, hkeyEq, Aiur.Generic.Instance.symbol] using
                    TVR.enumVal he hkMem hget hkeyEq har0
              | field _ | ptr _ _ | tuple _ =>
                simp [World.matchPattern, matchPatternWith, pure, Except.pure] at hmp
  | 0, _, .data _, _, _, _, _, _, _, hsc, _, _, _, _ => by simp [isShapeCheckableRep] at hsc
  | fuel + 1, pfx, .data d, yNm, locals, yVal, out, h, h', hsc, _, _, hlook, ev => by
    unfold shapeCheckExpr at ev
    simp only [isShapeCheckableRep, validData] at hsc
    cases hd : cert.data? d with
    | none => simp [hd] at hsc
    | some D =>
      simp only [hd, Bool.and_eq_true, List.all_eq_true] at hsc
      simp only [hd] at ev
      split at ev
      · simp only [trapE, seqE, litE, qualifyExprF, qualifyExpr, qualifyPat,
          Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
          Nat.cast_zero, Nat.cast_one] at ev
        obtain ⟨_, _, hass, _⟩ := evalExpr_let_wildcard_inv ev
        obtain ⟨_, _, _, e0, e1, h01, _⟩ := evalExpr_assertEq_inv hass
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e0
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e1
        exact False.elim (zero_ne_one (Value.field.inj h01))
      · simp only [matchE, vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
        cases ev with
        | matchValue evs hsel hbr =>
          obtain ⟨hyEq, hhEq⟩ := evalExpr_var_eq hlook evs
          subst hhEq
          rw [hyEq] at hsel
          obtain ⟨pat, hmem, hmp⟩ := selectArm_mem hsel
          rw [List.mem_map] at hmem
          obtain ⟨⟨p1, b1⟩, hmem1, hEqArm1⟩ := hmem
          rw [List.mem_map] at hmem1
          obtain ⟨⟨p0, b0⟩, hmem0, hEqArm0⟩ := hmem1
          rw [List.mem_map] at hmem0
          obtain ⟨⟨arm0, _⟩, harm0, hEq0⟩ := hmem0
          rw [List.mem_filterMap] at harm0
          obtain ⟨⟨k, fl⟩, hkMem, hMap⟩ := harm0
          cases hce : Lower.ctorEntry? P k with
          | none => simp [hce] at hMap
          | some ce =>
            rcases ce with ⟨idx, entry⟩
            simp only [hce, Option.map_some, Option.some.injEq] at hMap
            obtain ⟨hget, hkeyEq⟩ := ctorEntry?_sound hce
            have harEq : entry.arity = fl.length := by
              have hka := hsc.1.2 (k, fl) hkMem
              simp only [hce, beq_iff_eq] at hka
              exact hka
            let fieldChecks : List (String × Expr × Demand) :=
              fl.zipIdx.map fun (sh, fi) =>
                let fnm := pfx ++ "_" ++ String.ofList (natDigits fi)
                let fr := repOf P cert feat sh
                let (fe, fd) := shapeCheckExpr P cert feat fuel fnm fr fnm
                (fnm, fe, fd)
            let fnms : List String := fieldChecks.map Prod.fst
            let fexprs : List Expr := fieldChecks.map fun (_, fe, _) => fe
            obtain ⟨hArmEq, _⟩ := Prod.mk.inj hMap
            obtain ⟨hp1, hb1⟩ := Prod.mk.inj hEqArm0
            obtain ⟨hpat, hbody⟩ := Prod.mk.inj hEqArm1
            subst hEq0 hp1 hb1 hpat hbody
            rw [← hArmEq] at hmp hbr
            have hpatEq :
                (qualifyPat (.construct (.named (dataName d) []) (ctorNameOf idx entry.key)
                  (fieldChecks.map fun (fnm, _, _) => .bind fnm))).map Nat.cast =
                (.construct (.named (dataQName d) []) (ctorNameOf idx entry.key)
                  (fnms.map .bind) : Aiur.Generic.Pattern F) := by
              simp [fnms, qualifyPat, qualifyTy, qualifyName_dataName,
                Aiur.Generic.Pattern.map, List.map_map]
            rw [hpatEq] at hmp
            cases yVal with
            | construct en ctor ws =>
              simp only [World.matchPattern, matchPatternWith, constructorName,
                Aiur.Generic.Ty.subst, Aiur.Generic.Ty.toCore, List.length_map] at hmp
              split at hmp
              · simp [pure, Except.pure] at hmp
              · rename_i hok
                simp only [Bool.or_eq_true, bne_iff_ne, not_or, Decidable.not_not] at hok
                obtain ⟨⟨rfl, rfl⟩, hlenWs⟩ := hok
                obtain ⟨hwsLen, hbindEq⟩ := matchListWith_binds hmp
                rw [hbindEq] at hbr
                change EvalExpr world [] (fnms.zip ws ++ locals)
                  (qualifyExprF F (seqUnitList fexprs)) _ out h' at hbr
                have hbr' := hbr
                have hFieldPres : ∀ fe ∈ fexprs, ∀ h0 h1 v,
                    EvalExpr world [] (fnms.zip ws ++ locals) (qualifyExprF F fe) h0 v h1 →
                    h1 = h0 := by
                  intro fe hfe h0 h1 v evFe
                  rw [List.mem_map] at hfe
                  obtain ⟨⟨fnm, fe', fd'⟩, hmem1, rfl⟩ := hfe
                  rw [List.mem_map] at hmem1
                  obtain ⟨⟨sh, fi⟩, hshMem, hEqFe⟩ := hmem1
                  have hfeEq : fe' = (shapeCheckExpr P cert feat fuel
                      (pfx ++ "_" ++ String.ofList (natDigits fi))
                      (repOf P cert feat sh)
                      (pfx ++ "_" ++ String.ofList (natDigits fi))).1 := by
                    have := congrArg (fun p => p.2.1) hEqFe
                    simpa using this.symm
                  rw [hfeEq] at evFe
                  have hshInFl : sh ∈ fl := by
                    have hzi := List.mem_zipIdx hshMem
                    have hlt : fi < fl.length := by simpa using hzi.2.1
                    have heq : sh = fl[fi] := by simpa using hzi.2.2
                    rw [heq]; exact List.getElem_mem hlt
                  have hshOk := hsc.2 (k, fl) hkMem sh hshInFl
                  exact shapeCheckExpr_heap specs fuel _ _ _ _ _ _ _ hshOk.2 evFe
                obtain ⟨rfl, hallEv⟩ := evalExpr_seqUnitList_inv hbr' hFieldPres
                have hfnmsEq : fnms = fl.zipIdx.map fun (_, fi) =>
                    pfx ++ "_" ++ String.ofList (natDigits fi) := by
                  simp [fnms, fieldChecks, List.map_map]
                have hfnmsNd : fnms.Nodup := by
                  rw [hfnmsEq]; exact nodup_fieldNames pfx fl
                have hfnmsLen : fnms.length = fl.length := by
                  simp [fnms, fieldChecks]
                have hwsFlLen : ws.length = fl.length := hwsLen.trans hfnmsLen
                have hBuild :
                    ∀ (k0 : Nat) (flSub : List Shape) (wsSub : List (SourceValue F))
                      (hlen : flSub.length = wsSub.length),
                      (∀ j, (hj : j < flSub.length) →
                        fl[k0 + j]? = some flSub[j] ∧ ws[k0 + j]? = some (wsSub[j]'(hlen ▸ hj))) →
                      ∃ vsSub : List Fir.Val,
                        vsSub.length = flSub.length ∧
                        TVRDataFields P cert feat h' d flSub vsSub wsSub := by
                  intro k0 flSub
                  induction flSub generalizing k0 with
                  | nil =>
                    intro wsSub hlen _
                    cases wsSub with
                    | nil => exact ⟨[], rfl, .nil⟩
                    | cons _ _ => simp at hlen
                  | cons sh rest ih =>
                    intro wsSub hlen hsub
                    cases wsSub with
                    | nil => simp at hlen
                    | cons w wRest =>
                      have h0 := hsub 0 (by simp)
                      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
                      have hshInFl : sh ∈ fl := List.mem_of_getElem? h0.1
                      have hshOk := hsc.2 (k, fl) hkMem sh hshInFl
                      have hk0Lt : k0 < fl.length := by
                        by_contra hge
                        have hnone : fl[k0]? = none := List.getElem?_eq_none (by omega)
                        rw [hnone] at h0; cases h0.1
                      let nm0 := pfx ++ "_" ++ String.ofList (natDigits k0)
                      have hnmGet : fnms[k0]? = some nm0 := by
                        rw [hfnmsEq, List.getElem?_map, List.getElem?_zipIdx]
                        simp [h0.1, nm0]
                      have hfeMem : (shapeCheckExpr P cert feat fuel nm0
                          (repOf P cert feat sh) nm0).1 ∈ fexprs := by
                        have hzMem : (sh, k0) ∈ fl.zipIdx := by
                          rw [List.mem_iff_getElem?]
                          exact ⟨k0, by rw [List.getElem?_zipIdx]; simp [h0.1]⟩
                        rw [List.mem_map]
                        refine ⟨(nm0, (shapeCheckExpr P cert feat fuel nm0 (repOf P cert feat sh) nm0).1,
                          (shapeCheckExpr P cert feat fuel nm0 (repOf P cert feat sh) nm0).2), ?_, rfl⟩
                        rw [List.mem_map]
                        exact ⟨(sh, k0), hzMem, rfl⟩
                      obtain ⟨vOut, ev0⟩ := hallEv _ hfeMem
                      have hlook0 : (fnms.zip ws ++ locals).find? (·.1 == nm0) = some (nm0, w) :=
                        find?_zip_append hfnmsNd hwsLen.symm hnmGet h0.2
                      have hne32 : repOf P cert feat sh ≠ .w32 := by
                        intro heq; rw [heq] at hshOk; simp [isNonOpaqueRep] at hshOk
                      have hne64 : repOf P cert feat sh ≠ .w64 := by
                        intro heq; rw [heq] at hshOk; simp [isNonOpaqueRep] at hshOk
                      obtain ⟨_, vHead, htvrHead⟩ :=
                        shapeCheckExpr_sound specs fuel nm0 (repOf P cert feat sh) nm0
                          (fnms.zip ws ++ locals) w vOut h' h' hshOk.2 hne32 hne64 hlook0 ev0
                      obtain ⟨vsRest, hvsRestLen, htvrRest⟩ :=
                        ih (k0 + 1) wRest (Nat.succ.inj hlen) fun j hj => by
                          have hj' := hsub (j + 1) (Nat.succ_lt_succ hj)
                          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj'
                      have hnoPtr : dataFieldNeedsPtr P cert feat d (repOf P cert feat sh) = false := by
                        simpa using hshOk.1.1
                      exact ⟨vHead :: vsRest, congrArg Nat.succ hvsRestLen,
                        .consInline hnoPtr htvrHead htvrRest⟩
                obtain ⟨vs, hvsLen, htvrFields⟩ :=
                  hBuild 0 fl ws hwsFlLen.symm fun j hj => by
                    have hjWs : j < ws.length := hwsFlLen.symm ▸ hj
                    simp [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjWs]
                let cInfo : CtorInfo :=
                  { key := k, tag := entry.tag, nobj := fl.length, nscalar := 0,
                    fieldKinds := List.replicate fl.length .shared }
                refine ⟨rfl, .ctor cInfo vs, ?_⟩
                simpa [cInfo, hkeyEq, Aiur.Generic.Instance.symbol] using
                  TVR.dataVal hd hkMem hget hkeyEq (hvsLen.trans harEq.symm) harEq.symm htvrFields
            | field _ | ptr _ _ | tuple _ =>
              simp [World.matchPattern, matchPatternWith, pure, Except.pure] at hmp
  | _, _, .obj, _, _, _, _, _, _, hsc, _, _, _, _ => by simp [isShapeCheckableRep] at hsc

end ShapeCheckSound

/-! ## Section 5: Generic Backward `EvalFn` Soundness for `GuessLower` (`eval_guessWrapper_inv`) -/

section GuessWrapperBackward

variable {F : Type} [Field F] [DecidableEq F]

/-- Semantic meaning of the checker's accepted `Bool.true` result value. -/
def BoolTrueVal : BoolCheckKind → SourceValue F → Prop
  | .enumTrue ind ctorNm, v => v = .construct (enumQName ind) ctorNm []
  | .objTrue ctorNm, v => v = .construct objQName ctorNm []

omit [Field F] [DecidableEq F] in
private theorem find?_cons_of_ne {locals : Environment F Nat} {a b : String} {va vb : SourceValue F}
    (hne : a ≠ b) (h : locals.find? (·.1 == b) = some (b, vb)) :
    ((a, va) :: locals).find? (·.1 == b) = some (b, vb) := by
  have hbeq : (a == b) = false := beq_false_of_ne hne
  simp only [List.find?_cons, hbeq]
  exact h

private theorem eval_checkTail_inv {world : World F} {locals : Environment F Nat}
    {g : ResolvedGuess} {args : List (SourceValue F)} {yVal r : SourceValue F} {h h' : Heap F}
    (hLen : args.length = g.paramNames.length)
    (hLookParams : ∀ (i : Nat) nm v, g.paramNames[i]? = some nm → args[i]? = some v →
      locals.find? (·.1 == nm) = some (nm, v))
    (hLookY : locals.find? (·.1 == "g_y") = some ("g_y", yVal))
    (hcQual : qualifyName g.cName = qualified g.cName)
    (ev : EvalExpr world [] locals
      (qualifyExprF F
        (letE "g_ok" (callE g.cName (g.paramNames.map vE ++ [vE "g_y"]))
          (match g.boolCheck with
           | .enumTrue ind ctorNm =>
             seqE (.builtin (.assertEq (assertion "guess: checker returned false"))
                    [vE "g_ok", .construct (enumName ind) (some []) ctorNm []])
               (vE "g_y")
           | .objTrue ctorNm =>
             matchE (vE "g_ok")
               [(pC ctorNm [], vE "g_y"),
                (.wildcard, seqE (.builtin (.assertEq (assertion "guess: checker returned false"))
                  [litE 0, litE 1]) (vE "g_y"))]))) h r h') :
    r = yVal ∧
    ∃ okVal : SourceValue F,
      EvalFn world (qualified g.cName) (args ++ [yVal]) h okVal h' ∧
      BoolTrueVal g.boolCheck okVal := by
  simp only [letE, callE, qualifyExprF, qualifyExpr, qualifyPat, hcQual,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map,
    List.map_append, List.map_cons, List.map_nil] at ev
  obtain ⟨vok, hm, evCall, evAfter⟩ := evalExpr_let_bind_inv ev
  obtain ⟨callArgs, hArgsEnd, evArgs, hCal⟩ := evalExpr_call_inv evCall
  have hArgsEq : callArgs = args ++ [yVal] ∧ hArgsEnd = h := by
    have hAll : ∀ (i : Nat) nm v, (g.paramNames ++ ["g_y"])[i]? = some nm →
        (args ++ [yVal])[i]? = some v → locals.find? (·.1 == nm) = some (nm, v) := by
      intro i nm v h1 h2
      by_cases hi : i < g.paramNames.length
      · have hiA : i < args.length := hLen.symm ▸ hi
        rw [List.getElem?_append_left hi] at h1
        rw [List.getElem?_append_left hiA] at h2
        exact hLookParams i nm v h1 h2
      · have hi0 : i - g.paramNames.length = 0 := by
          rw [List.getElem?_append_right (by omega)] at h1
          cases hsub : i - g.paramNames.length with
          | zero => rfl
          | succ m => simp [hsub] at h1
        rw [List.getElem?_append_right (by omega), hi0] at h1
        rw [List.getElem?_append_right (by omega), hLen, hi0] at h2
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
        subst h1 h2
        exact hLookY
    have hLenBoth : (g.paramNames ++ ["g_y"]).length = (args ++ [yVal]).length := by
      simp [hLen]
    have evArgs' : EvalArgs world [] locals
        (((g.paramNames ++ ["g_y"]).map vE).map (qualifyExprF F)) h callArgs hArgsEnd := by
      simpa only [List.map_append, List.map_cons, List.map_nil, List.map_map,
        Function.comp_def, qualifyExprF] using evArgs
    exact evalArgs_varList_inv hLenBoth hAll evArgs'
  obtain ⟨rfl, rfl⟩ := hArgsEq
  have hLookY' : (("g_ok", vok) :: locals).find? (·.1 == "g_y") = some ("g_y", yVal) :=
    find?_cons_of_ne (by decide) hLookY
  cases hbk : g.boolCheck with
  | enumTrue ind ctorNm =>
    simp only [hbk, seqE, vE, qualifyExpr, qualifyPat, qualifyName_enumName,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at evAfter
    obtain ⟨_, _, evAss, evRet⟩ := evalExpr_let_wildcard_inv evAfter
    obtain ⟨vl, vr, _, evl, evr, hEqBool, _⟩ := evalExpr_assertEq_inv evAss
    obtain ⟨hvl, rfl⟩ := evalExpr_var_eq (v := vok) rfl evl
    obtain ⟨hvr, rfl⟩ := evalExpr_construct0_inv evr
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hLookY' evRet
    exact ⟨rfl, _, hCal, by unfold BoolTrueVal; rw [← hvl, hEqBool, hvr]⟩
  | objTrue ctorNm =>
    simp only [hbk, matchE, pC, seqE, vE, litE, qualifyExpr, qualifyPat,
      qualifyTy, Lower.objTy, Lower.qualifyName_obj,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
      Nat.cast_zero, Nat.cast_one] at evAfter
    cases evAfter with
    | matchValue evs hsel hbr =>
      obtain ⟨hvok, rfl⟩ := evalExpr_var_eq (v := vok) rfl evs
      rw [hvok] at hsel
      obtain ⟨pat, hmem, hmp⟩ := selectArm_mem hsel
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · cases vok with
        | construct en ctor ws =>
          simp only [World.matchPattern, matchPatternWith, constructorName,
            Aiur.Generic.Ty.subst, Aiur.Generic.Ty.toCore, List.length_nil] at hmp
          split at hmp
          · simp [pure, Except.pure] at hmp
          · rename_i hok
            simp only [Bool.or_eq_true, bne_iff_ne, not_or, Decidable.not_not] at hok
            obtain ⟨⟨rfl, rfl⟩, hlen0⟩ := hok
            have hwsNil : ws = [] := List.eq_nil_of_length_eq_zero hlen0.symm
            subst hwsNil
            simp only [List.attach_nil, matchListWith, pure, Except.pure, bind, Except.bind,
              Except.ok.injEq, Option.some.injEq] at hmp
            subst hmp
            obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hLookY' hbr
            exact ⟨rfl, _, hCal, rfl⟩
        | field _ | ptr _ _ | tuple _ =>
          simp [World.matchPattern, matchPatternWith, pure, Except.pure] at hmp
      · simp only [World.matchPattern, matchPatternWith, pure, Except.pure,
          Except.ok.injEq, Option.some.injEq] at hmp
        subst hmp
        obtain ⟨_, _, hass, _⟩ := evalExpr_let_wildcard_inv hbr
        obtain ⟨_, _, _, e0, e1, h01, _⟩ := evalExpr_assertEq_inv hass
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e0
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e1
        exact False.elim (zero_ne_one (Value.field.inj h01))

/-- **Generic Backward `EvalFn` Soundness Theorem for `GuessLower` (`eval_guessWrapper_inv`)**:
For ANY `EvalFn` derivation of a `GuessLower`-rewritten guess subject `g.fName`
(with `hint` returning ANY arbitrary constant from an untrusted host!), BOTH:
1. **U4 Canonicality & Shape Bounds**: `∃ v : Fir.Val, TVR P cert feat h' g.retRep v r`, AND
2. **Checker Acceptance**: `∃ hKey okVal, EvalFn world (qualified g.cName) (args ++ [r]) hKey okVal h' ∧
     BoolTrueVal g.boolCheck okVal`. -/
theorem eval_guessWrapper_inv {world : World F} {P : Program} {cert : ShapeCert} {feat : Features}
    (specs : ShapeCheckSpecs world) (g : ResolvedGuess)
    (hShapeOk : isShapeCheckableRep P cert feat (cert.datas.length + 2) g.retRep = true)
    (hNd : g.paramNames.Nodup)
    (hNoG : "g_y" ∉ g.paramNames ∧ "g_raw" ∉ g.paramNames)
    (hcQual : qualifyName g.cName = qualified g.cName)
    (hFn : WorldHasFn world (qualified g.fName) g.paramNames
      (qualifyExprF F (guessWrapperBody P cert feat g).1))
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn world (qualified g.fName) args h r h') :
    (∃ v : Fir.Val, TVR P cert feat h' g.retRep v r) ∧
    (∃ hKey okVal,
      EvalFn world (qualified g.cName) (args ++ [r]) hKey okVal h' ∧
      BoolTrueVal g.boolCheck okVal) := by
  obtain ⟨hLen, body⟩ := evalFn_plain_inv hFn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_guessWrapperBody P cert feat g) ev
  have hBaseParams : ∀ (i : Nat) nm v, g.paramNames[i]? = some nm → args[i]? = some v →
      (g.paramNames.zip args).find? (·.1 == nm) = some (nm, v) :=
    fun i nm v h1 h2 => find?_zip_exact hNd hLen.symm h1 h2
  have hNeGY : ∀ nm, nm ∈ g.paramNames → "g_y" ≠ nm := fun nm hmem heq => hNoG.1 (heq ▸ hmem)
  have hNeGRaw : ∀ nm, nm ∈ g.paramNames → "g_raw" ≠ nm := fun nm hmem heq => hNoG.2 (heq ▸ hmem)
  unfold guessWrapperBody at body
  cases hret : g.retRep with
  | w32 =>
    simp only [hret] at body
    rw [letE, qualifyExprF, qualifyExpr, qualifyPat,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map] at body
    obtain ⟨vRaw, hKey, _, k1⟩ := evalExpr_let_bind_inv body
    rw [letE, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map] at k1
    obtain ⟨vY, hFrom, evFrom, k2⟩ := evalExpr_let_bind_inv k1
    obtain ⟨hhEq, vFir, htvrY⟩ :=
      fromRawExpr_sound (P := P) (cert := cert) (feat := feat) specs
        (rawVal := vRaw) rfl (Or.inl rfl) evFrom
    subst hhEq
    have hLookP : ∀ (i : Nat) nm v, g.paramNames[i]? = some nm → args[i]? = some v →
        (("g_y", vY) :: ("g_raw", vRaw) :: g.paramNames.zip args).find? (·.1 == nm) = some (nm, v) := by
      intro i nm v h1 h2
      have hmem := List.mem_of_getElem? h1
      exact find?_cons_of_ne (hNeGY nm hmem)
        (find?_cons_of_ne (hNeGRaw nm hmem) (hBaseParams i nm v h1 h2))
    obtain ⟨rfl, okVal, hChkCal, hBoolOk⟩ :=
      eval_checkTail_inv (yVal := vY) hLen hLookP rfl hcQual k2
    refine ⟨⟨vFir, ?_⟩, ⟨_, okVal, hChkCal, hBoolOk⟩⟩
    exact TVR_heap_indep_of_shapeCheckable (hret ▸ hShapeOk) htvrY
  | w64 =>
    simp only [hret] at body
    rw [letE, qualifyExprF, qualifyExpr, qualifyPat,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map] at body
    obtain ⟨vRaw, hKey, _, k1⟩ := evalExpr_let_bind_inv body
    rw [letE, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map] at k1
    obtain ⟨vY, hFrom, evFrom, k2⟩ := evalExpr_let_bind_inv k1
    obtain ⟨hhEq, vFir, htvrY⟩ :=
      fromRawExpr_sound (P := P) (cert := cert) (feat := feat) specs
        (rawVal := vRaw) rfl (Or.inr rfl) evFrom
    subst hhEq
    have hLookP : ∀ (i : Nat) nm v, g.paramNames[i]? = some nm → args[i]? = some v →
        (("g_y", vY) :: ("g_raw", vRaw) :: g.paramNames.zip args).find? (·.1 == nm) = some (nm, v) := by
      intro i nm v h1 h2
      have hmem := List.mem_of_getElem? h1
      exact find?_cons_of_ne (hNeGY nm hmem)
        (find?_cons_of_ne (hNeGRaw nm hmem) (hBaseParams i nm v h1 h2))
    obtain ⟨rfl, okVal, hChkCal, hBoolOk⟩ :=
      eval_checkTail_inv (yVal := vY) hLen hLookP rfl hcQual k2
    refine ⟨⟨vFir, ?_⟩, ⟨_, okVal, hChkCal, hBoolOk⟩⟩
    exact TVR_heap_indep_of_shapeCheckable (hret ▸ hShapeOk) htvrY
  | irr | nat _ | w8 | w16 | «enum» _ | data _ | obj =>
    simp only [hret] at body
    rw [hret] at hShapeOk
    rw [letE, qualifyExprF, qualifyExpr, qualifyPat,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map] at body
    obtain ⟨vY, hKey, _, k1⟩ := evalExpr_let_bind_inv body
    rw [seqE, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map] at k1
    obtain ⟨vChk, hChk, evChk, k2⟩ := evalExpr_let_wildcard_inv k1
    have hne32 : g.retRep ≠ .w32 := by rw [hret]; intro h; cases h
    have hne64 : g.retRep ≠ .w64 := by rw [hret]; intro h; cases h
    have evChk' : EvalExpr world [] (("g_y", vY) :: g.paramNames.zip args)
        (qualifyExprF F (shapeCheckExpr P cert feat (cert.datas.length + 2) "g_f" g.retRep "g_y").1)
        hKey vChk hChk := by
      rw [hret]; exact evChk
    obtain ⟨hhEq, vFir, htvrY⟩ :=
      shapeCheckExpr_sound specs (cert.datas.length + 2) "g_f" g.retRep "g_y"
        (("g_y", vY) :: g.paramNames.zip args) vY vChk hKey hChk
        (by rw [hret]; exact hShapeOk) hne32 hne64 rfl evChk'
    subst hhEq
    have hLookP : ∀ (i : Nat) nm v, g.paramNames[i]? = some nm → args[i]? = some v →
        (("g_y", vY) :: g.paramNames.zip args).find? (·.1 == nm) = some (nm, v) := by
      intro i nm v h1 h2
      have hmem := List.mem_of_getElem? h1
      exact find?_cons_of_ne (hNeGY nm hmem) (hBaseParams i nm v h1 h2)
    obtain ⟨rfl, okVal, hChkCal, hBoolOk⟩ :=
      eval_checkTail_inv (yVal := vY) hLen hLookP rfl hcQual k2
    refine ⟨⟨vFir, ?_⟩, ⟨_, okVal, hChkCal, hBoolOk⟩⟩
    exact TVR_heap_indep_of_shapeCheckable hShapeOk (hret ▸ htvrY)

end GuessWrapperBackward

/-! ## Section 6: Composition with Verified `guess` Soundness & `SrcG` (`RunG`) -/

section Composition

variable {F : Type} [Field F] [DecidableEq F]

/-- **End-to-End Denotational Composition (`guess_backward_denotation`)**:
Composes `eval_guessWrapper_inv` with:
1. Backward soundness of the checker `g.cName` in `world`, and
2. The kernel-verified `guess` uniqueness theorem (`∀ xs y, checkerSem xs y = true → y = fSem xs`),
proving that ANY `EvalFn` derivation in the guess-lowered program yields a canonical
`TVR`-valid witness `yVal` satisfying `yVal = fSem xs` (zero TCB expansion)! -/
theorem guess_backward_denotation
    {α β : Type*}
    {world : World F} {P : Program} {cert : ShapeCert} {feat : Features}
    (specs : ShapeCheckSpecs world) (g : ResolvedGuess)
    (hShapeOk : isShapeCheckableRep P cert feat (cert.datas.length + 2) g.retRep = true)
    (hNd : g.paramNames.Nodup)
    (hNoG : "g_y" ∉ g.paramNames ∧ "g_raw" ∉ g.paramNames)
    (hcQual : qualifyName g.cName = qualified g.cName)
    (hFn : WorldHasFn world (qualified g.fName) g.paramNames
      (qualifyExprF F (guessWrapperBody P cert feat g).1))
    {ArgRel : α → List (SourceValue F) → Prop}
    {RetOfFir : Fir.Val → β}
    {fSem : α → β} {checkerSem : α → β → Bool}
    (hCheckerBackward :
      ∀ {xs args y h0 ok h1 yFir},
        ArgRel xs args →
        TVR P cert feat h1 g.retRep yFir y →
        EvalFn world (qualified g.cName) (args ++ [y]) h0 ok h1 →
        BoolTrueVal g.boolCheck ok →
        checkerSem xs (RetOfFir yFir) = true)
    (hGuessSound : ∀ xs y, checkerSem xs y = true → y = fSem xs)
    {xs : α} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hArgs : ArgRel xs args)
    (ev : EvalFn world (qualified g.fName) args h r h') :
    ∃ yFir : Fir.Val,
      TVR P cert feat h' g.retRep yFir r ∧ RetOfFir yFir = fSem xs := by
  obtain ⟨⟨yFir, htvr⟩, ⟨hKey, okVal, hChkCal, hBoolOk⟩⟩ :=
    eval_guessWrapper_inv specs g hShapeOk hNd hNoG hcQual hFn ev
  have hChkTrue : checkerSem xs (RetOfFir yFir) = true :=
    hCheckerBackward hArgs htvr hChkCal hBoolOk
  exact ⟨yFir, htvr, hGuessSound xs (RetOfFir yFir) hChkTrue⟩

/-- **Direct Backward Simulation into `IxCC.Src.RunG` (`SrcG`)**:
Given a validated `guess` entry in `src.table.guess` and backward simulation of the
checker `g.cName` into `Src.RunG src ls g.cCId`, any `EvalFn` derivation of the
guess-lowered subject `g.fName` simulates directly backward to `Src.RunG src ls g.fCId`
via `Src.RunG.guess`! -/
theorem guess_backward_runG
    {world : World F} {src : IxCC.Src.Program} {P : Program} {cert : ShapeCert} {feat : Features}
    (specs : ShapeCheckSpecs world) (g : ResolvedGuess)
    {entry : IxCC.Src.GuessEntry} {boolTrueC : IxCC.Src.CId}
    (hEntry : src.table.guessOf g.fCId = some entry)
    (hCheckerId : entry.checker = g.cCId)
    (hBoolTrue : src.known.boolTrue = some boolTrueC)
    (hShapeOk : isShapeCheckableRep P cert feat (cert.datas.length + 2) g.retRep = true)
    (hNd : g.paramNames.Nodup)
    (hNoG : "g_y" ∉ g.paramNames ∧ "g_raw" ∉ g.paramNames)
    (hcQual : qualifyName g.cName = qualified g.cName)
    (hFn : WorldHasFn world (qualified g.fName) g.paramNames
      (qualifyExprF F (guessWrapperBody P cert feat g).1))
    {ls : IxCC.Src.Levels} {xs : List IxCC.Src.Value} {toSrcVal : Fir.Val → IxCC.Src.Value}
    (hXsLen : xs.length = entry.arity)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hCheckerRunG :
      ∀ {y h0 ok h1 yFir},
        TVR P cert feat h1 g.retRep yFir y →
        EvalFn world (qualified g.cName) (args ++ [y]) h0 ok h1 →
        BoolTrueVal g.boolCheck ok →
        IxCC.Src.RunG src ls g.cCId (xs ++ [toSrcVal yFir]) (.con boolTrueC [] [] []))
    (ev : EvalFn world (qualified g.fName) args h r h') :
    ∃ yFir : Fir.Val,
      TVR P cert feat h' g.retRep yFir r ∧
      IxCC.Src.RunG src ls g.fCId xs (toSrcVal yFir) := by
  obtain ⟨⟨yFir, htvr⟩, ⟨hKey, okVal, hChkCal, hBoolOk⟩⟩ :=
    eval_guessWrapper_inv specs g hShapeOk hNd hNoG hcQual hFn ev
  have hChkG := hCheckerRunG htvr hChkCal hBoolOk
  rw [← hCheckerId] at hChkG
  exact ⟨yFir, htvr, .guess hEntry hXsLen hBoolTrue hChkG⟩

end Composition

/-! ## Section 7: Axiom Audit (`#print axioms`) -/

/-- info: 'IxCC.AiurBackend.GuessLowerProof.evalRhs_foldOversizedNatCmpRhs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalRhs_foldOversizedNatCmpRhs

/-- info: 'IxCC.AiurBackend.GuessLowerProof.eval_foldOversizedCallStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_foldOversizedCallStep

/-- info: 'IxCC.AiurBackend.GuessLowerProof.shapeCheckExpr_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shapeCheckExpr_sound

/-- info: 'IxCC.AiurBackend.GuessLowerProof.eval_guessWrapper_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_guessWrapper_inv

/-- info: 'IxCC.AiurBackend.GuessLowerProof.guess_backward_denotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guess_backward_denotation

/-- info: 'IxCC.AiurBackend.GuessLowerProof.guess_backward_runG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guess_backward_runG

end IxCC.AiurBackend.GuessLowerProof
