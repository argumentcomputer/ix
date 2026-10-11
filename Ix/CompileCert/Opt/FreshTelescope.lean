import Ix.CompileCert.Opt.FreshOpeningSupport

/-!
Finite fresh opening and closing, and the exact erased reconstruction performed
by the actual `mkLambda`.
All raw expressions, initial supplies and preferred allocation names are admitted.
The lookup table is the structural NameTable, including its last-write semantics.
This file makes no claim about the O11a instance callback or final faithfulness.
-/

namespace Ix.CompileCert.Opt.FreshTelescope

open Ix (Name Expr)
open Ix.AuxGen (FreshFVars LocalDecl instantiate1At batchAbstractNames mkLambda)
open Ix.Compile.Canon (NameTable keyName)
open Ix.CompileCert.Conv
open Ix.CompileCert.Opt.FreshFVarsProof

/-- Requests retain the actual prefix, preferred index and opening depth. -/
abbrev OpenRequest := String × Nat × Nat

/-- A finite composition of the actual allocator and actual opening helper.
Protection is done once by the producer theorem below, not at every step. -/
def openRequests : List OpenRequest → FreshFVars → Expr →
    List (Name × Nat) × FreshFVars × Expr
  | [], supply, body => ([], supply, body)
  | (pfx, index, depth) :: rest, supply, body =>
      let chosen := supply.fresh pfx index
      let tail := openRequests rest chosen.2 (instantiate1At body chosen.1.2 depth)
      ((chosen.1.1, depth) :: tail.1, tail.2.1, tail.2.2)

/-- Close the last opening first. Depths are recorded by the producer. -/
def closeRequests : List (Name × Nat) → Tm → Tm
  | [], body => body
  | (name, depth) :: rest, body =>
      babs (singletonTable name).get? 1 depth (closeRequests rest body)

theorem openRequests_grows (requests : List OpenRequest) (supply : FreshFVars)
    (body : Expr) :
    ∀ key, key ∈ supply.used → key ∈ (openRequests requests supply body).2.1.used := by
  induction requests generalizing supply body with
  | nil => exact fun _ member => member
  | cons request rest ih =>
      rcases request with ⟨pfx, index, depth⟩
      intro key member
      exact ih _ _ key (fresh_grows supply pfx index key member)

theorem openRequests_protects (requests : List OpenRequest) (supply : FreshFVars)
    (body : Expr) (covered : Protects supply body) :
    Protects (openRequests requests supply body).2.1
      (openRequests requests supply body).2.2 := by
  induction requests generalizing supply body with
  | nil => exact covered
  | cons request rest ih =>
      rcases request with ⟨pfx, index, depth⟩
      exact ih _ _ (fresh_open_protects_of supply body pfx index depth covered)

/-- Internal compositional form; the public producer supplies `covered`. -/
theorem openRequests_close_of_protected (requests : List OpenRequest)
    (supply : FreshFVars) (body : Expr) (covered : Protects supply body) :
    closeRequests (openRequests requests supply body).1
      (er (openRequests requests supply body).2.2) = er body := by
  induction requests generalizing supply body with
  | nil => rfl
  | cons request rest ih =>
      rcases request with ⟨pfx, index, depth⟩
      change babs (singletonTable (supply.fresh pfx index).1.1).get? 1 depth
        (closeRequests
          (openRequests rest (supply.fresh pfx index).2
            (instantiate1At body (supply.fresh pfx index).1.2 depth)).1
          (er (openRequests rest (supply.fresh pfx index).2
            (instantiate1At body (supply.fresh pfx index).1.2 depth)).2.2)) = er body
      rw [ih _ _ (fresh_open_protects_of supply body pfx index depth covered)]
      rw [fresh_pair_expr, er_instantiate1At, er_mkFVar]
      apply close_open_fresh
      intro occurs
      exact fresh_not_mem supply pfx index (covered _ ((tmOccurs_er _ body).1 occurs))

/-- Arbitrarily many openings are closed exactly on erased terms, including
open inputs and repeated/colliding preferred names. No freshness premise. -/
theorem protected_openRequests_close (requests : List OpenRequest)
    (supply : FreshFVars) (body : Expr) :
    let answer := openRequests requests (supply.protectExpr body) body
    closeRequests answer.1 (er answer.2.2) = er body ∧
      Protects answer.2.1 answer.2.2 ∧
      ∀ key, key ∈ supply.used → key ∈ answer.2.1.used := by
  dsimp only
  refine ⟨openRequests_close_of_protected requests _ body
    (protectExpr_protects supply body),
    openRequests_protects requests _ body (protectExpr_protects supply body), ?_⟩
  intro key member
  exact openRequests_grows requests _ body key (protectExpr_grows supply body key member)

/-- Every allocation in the returned history remains reserved at the end. -/
theorem openRequests_reserved (requests : List OpenRequest) (supply : FreshFVars)
    (body : Expr) (entry : Name × Nat)
    (member : entry ∈ (openRequests requests supply body).1) :
    keyName entry.1 ∈ (openRequests requests supply body).2.1.used := by
  induction requests generalizing supply body with
  | nil => cases member
  | cons request rest ih =>
      rcases request with ⟨pfx, index, depth⟩
      rcases List.mem_cons.1 member with equal | later
      · subst entry
        exact openRequests_grows rest _ _ _ (fresh_reserved supply pfx index)
      · exact ih _ _ later

/-- The actual first pass of `mkBinderChain`: outermost declarations are
inserted first, and duplicate structural names retain the final index. -/
def declarationTable (decls : Array LocalDecl) : NameTable Nat :=
  forIn (m := Id) decls.zipIdx {} fun (decl, index) table =>
    pure (.yield (table.insert decl.fvarName index))

/-- Independent erased reconstruction. The body has every declaration in
scope; the domain at index j has exactly the first j declarations in scope.
The reverse source loop builds an outermost-first lambda chain. -/
def erasedLambda (body : Tm) (decls : Array LocalDecl) : Tm :=
  if decls.size == 0 then body else
    let table := declarationTable decls
    forIn (m := Id) decls.zipIdx.reverse (babs table.get? decls.size 0 body)
      fun (decl, index) result =>
        pure (.yield (.lam (babs table.get? index 0 (er decl.domain)) result))

private theorem er_forIn {α : Type} (raw : α → Expr → Expr)
    (erased : α → Tm → Tm)
    (step : ∀ value body, er (raw value body) = erased value (er body)) :
    ∀ (values : List α) (body : Expr),
      er (forIn (m := Id) values body (fun value current => pure (.yield (raw value current)))) =
        forIn (m := Id) values (er body)
          (fun value current => pure (.yield (erased value current)))
  | [], _ => rfl
  | value :: rest, body => by
      rw [List.forIn_cons, List.forIn_cons]
      change er (forIn (m := Id) rest (raw value body)
        (fun item current => pure (.yield (raw item current)))) =
        forIn (m := Id) rest (erased value (er body))
          (fun item current => pure (.yield (erased item current)))
      rw [er_forIn raw erased step rest (raw value body), step]

/-- Exact connection to the actual runtime reconstruction, on arbitrary
raw bodies and declaration arrays, including duplicate names. -/
theorem er_mkLambda (body : Expr) (decls : Array LocalDecl) :
    er (mkLambda body decls) = erasedLambda (er body) decls := by
  unfold mkLambda Ix.AuxGen.mkBinderChain erasedLambda
  simp only [Id.run]
  split
  · rfl
  · change er (forIn (m := Id) decls.zipIdx.reverse
        (batchAbstractNames body (declarationTable decls) decls.size 0)
        (fun (decl, index) result => pure (.yield
          (Expr.mkLam decl.binderName
            (batchAbstractNames decl.domain (declarationTable decls) index 0) result decl.info)))) =
      forIn (m := Id) decls.zipIdx.reverse
        (babs (declarationTable decls).get? decls.size 0 (er body))
        (fun (decl, index) result => pure (.yield
          (.lam (babs (declarationTable decls).get? index 0 (er decl.domain)) result)))
    rw [← Array.forIn_toList, ← Array.forIn_toList]
    have loop := er_forIn (α := LocalDecl × Nat)
      (fun (decl, index) result => Expr.mkLam decl.binderName
        (batchAbstractNames decl.domain (declarationTable decls) index 0) result decl.info)
      (fun (decl, index) result => Tm.lam
        (babs (declarationTable decls).get? index 0 (er decl.domain)) result)
      (by
        rintro ⟨decl, index⟩ current
        rw [er_mkLam, er_batchAbstractNames])
      decls.zipIdx.reverse.toList
      (batchAbstractNames body (declarationTable decls) decls.size 0)
    rw [er_batchAbstractNames] at loop
    exact loop

theorem mkLambda_er_congr (decls : Array LocalDecl) (left right : Expr)
    (same : er left = er right) : er (mkLambda left decls) = er (mkLambda right decls) := by
  rw [er_mkLambda, er_mkLambda, same]

/-- Singleton reconstruction uses the same structural table as the opening
roundtrip. Its domain is outside its own binder. -/
theorem mkLambda_singleton (body : Expr) (decl : LocalDecl) :
    mkLambda body #[decl] = Expr.mkLam decl.binderName decl.domain
      (batchAbstractNames body (singletonTable decl.fvarName) 1 0) decl.info := by
  simp [mkLambda, Ix.AuxGen.mkBinderChain, singletonTable, Ix.AuxGen.batchAbstractNames]
  congr 1
  cases decl.domain <;> rfl

/-- Iterated one-binder closing, in original declaration order. -/
def closeDecls : List LocalDecl → Expr → Expr
  | [], body => body
  | decl :: rest, body => mkLambda (closeDecls rest body) #[decl]

theorem closeDecls_append (first last : List LocalDecl) (body : Expr) :
    closeDecls (first ++ last) body = closeDecls first (closeDecls last body) := by
  induction first with
  | nil => rfl
  | cons decl rest ih =>
      exact congrArg (fun value => mkLambda value #[decl]) ih

theorem closeDecls_er_congr (decls : List LocalDecl) (left right : Expr)
    (same : er left = er right) : er (closeDecls decls left) = er (closeDecls decls right) := by
  induction decls with
  | nil => exact same
  | cons decl rest ih => exact mkLambda_er_congr #[decl] _ _ ih

/-- The current protected lambda supplies freshness for both the body's
opening and its singleton reconstruction; its dependent domain is retained. -/
theorem fresh_lambda_close (supply : FreshFVars) (name : Name)
    (domain body : Expr) (info : Lean.BinderInfo) (hash : Address)
    (pfx : String) (index : Nat)
    (covered : Protects supply (.lam name domain body info hash)) :
    er (mkLambda (Ix.AuxGen.instantiate1 body (supply.fresh pfx index).1.2)
      #[{ fvarName := (supply.fresh pfx index).1.1,
          binderName := name, domain := domain, info := info }]) =
      er (.lam name domain body info hash) := by
  rw [mkLambda_singleton, er_mkLam, fresh_pair_expr]
  have roundtrip := close_instantiate1At_fvar_of_fresh body
    (supply.fresh pfx index).1.1 0 (by
      intro occurs
      exact fresh_not_mem supply pfx index (covered _ (.inr occurs)))
  change Tm.lam (er domain)
    (er (batchAbstractNames (instantiate1At body
      (Expr.mkFVar (supply.fresh pfx index).1.1) 0)
      (singletonTable (supply.fresh pfx index).1.1) 1 0)) = Tm.lam (er domain) (er body)
  rw [roundtrip]

end Ix.CompileCert.Opt.FreshTelescope
