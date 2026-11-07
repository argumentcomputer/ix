import Aiur.Inlining.Scope
import Aiur.Generic.Equality
import Aiur.Generic.LoweringTypeFacts

namespace Aiur.Inlining
open Generic

/-- A finite explanation of circuit-only expansion. Its two interpretations
are ordinary core expressions; no new source evaluation rule is introduced. -/
inductive Tree (F : Type) where
  | literal (value : F)
  | var (name : String)
  | tuple (items : List (Tree F))
  | construct (name ctor : String) (items : List (Tree F))
  | project (child : Tree F) (index : Nat)
  | letValue (pattern : Aiur.Pattern F) (value body : Tree F)
  | store (child : Tree F)
  | load (child : Tree F)
  | hint (type : Aiur.Ty) (key : Tree F) (channel : String := "")
  | neg (child : Tree F)
  | binary (op : BinOp) (left right : Tree F)
  | assertEq (assertion : Assertion) (left right : Tree F)
  | call (name : String) (args : List (Tree F))
  | expand (callee : Aiur.Function F) (args : List (Tree F)) (body : Tree F)
  | matchValue (value : Tree F) (arms : List (Aiur.Pattern F × Tree F))

def Tree.source : Tree F → Aiur.Expr F
  | .literal x => .literal x
  | .var n => .var n
  | .tuple xs => .tuple (xs.map Tree.source)
  | .construct n c xs => .construct n c (xs.map Tree.source)
  | .project x i => .project x.source i
  | .letValue p x b => .letValue p x.source b.source
  | .store x => .store x.source
  | .load x => .load x.source
  | .hint t x channel => .hint t x.source channel
  | .neg x => .neg x.source
  | .binary op x y => .binary op x.source y.source
  | .assertEq op x y => .assertEq op x.source y.source
  | .call n xs => .call n (xs.map Tree.source)
  | .expand f xs _ => .call f.name (xs.map Tree.source)
  | .matchValue x arms => .matchValue x.source (arms.map fun a => (a.1,a.2.source))
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def Tree.target : Tree F → Aiur.Expr F
  | .literal x => .literal x
  | .var n => .var n
  | .tuple xs => .tuple (xs.map Tree.target)
  | .construct n c xs => .construct n c (xs.map Tree.target)
  | .project x i => .project x.target i
  | .letValue p x b => .letValue p x.target b.target
  | .store x => .store x.target
  | .load x => .load x.target
  | .hint t x channel => .hint t x.target channel
  | .neg x => .neg x.target
  | .binary op x y => .binary op x.target y.target
  | .assertEq op x y => .assertEq op x.target y.target
  | .call n xs => .call n (xs.map Tree.target)
  | .expand f xs b => .letValue (.tuple (f.params.map fun p => .bind p.1))
      (.tuple (xs.map Tree.target)) b.target
  | .matchValue x arms => .matchValue x.target (arms.map fun a => (a.1,a.2.target))
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

/-- Purely syntactic expansion certificate. In particular, ordinary calls can
never name a mandatory-inline function. -/
def Tree.Safe (p : Aiur.Program F) (inlineNames : List String) : Tree F → Prop
  | .literal _ | .var _ => True
  | .tuple xs | .construct _ _ xs => ∀ x ∈ xs, x.Safe p inlineNames
  | .project x _ | .store x | .load x | .hint _ x channel | .neg x => x.Safe p inlineNames
  | .binary _ x y | .assertEq _ x y | .letValue _ x y => x.Safe p inlineNames ∧ y.Safe p inlineNames
  | .call n xs => n ∉ inlineNames ∧ ∀ x ∈ xs, x.Safe p inlineNames
  | .expand f xs b =>
      p.findFunction? f.name = some f ∧ f.name ∈ inlineNames ∧ b.source = f.body ∧
      hasScope (f.params.map Prod.fst) b.target = true ∧ b.Safe p inlineNames ∧
      ∀ x ∈ xs, x.Safe p inlineNames
  | .matchValue x arms => x.Safe p inlineNames ∧ ∀ a ∈ arms, a.2.Safe p inlineNames
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def Tree.safe [DecidableEq F] (p : Aiur.Program F) (names : List String) : Tree F → Bool
  | .literal _ | .var _ => true
  | .tuple xs | .construct _ _ xs => (xs.map (Tree.safe p names)).all id
  | .project x _ | .store x | .load x | .hint _ x channel | .neg x => x.safe p names
  | .binary _ x y | .assertEq _ x y | .letValue _ x y => x.safe p names && y.safe p names
  | .call n xs => decide (n ∉ names) && (xs.map (Tree.safe p names)).all id
  | .expand f xs b => decide (p.findFunction? f.name = some f) && decide (f.name ∈ names) &&
      decide (b.source = f.body) && hasScope (f.params.map Prod.fst) b.target &&
      b.safe p names && (xs.map (Tree.safe p names)).all id
  | .matchValue x arms => x.safe p names && (arms.map fun a => a.2.safe p names).all id
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

theorem Tree.safe_iff [DecidableEq F] (p : Aiur.Program F) (names : List String) (t : Tree F) :
    t.safe p names = true ↔ t.Safe p names := by
  have sub (x : Tree F) (smaller : sizeOf x < sizeOf t) :
      x.safe p names = true ↔ x.Safe p names := Tree.safe_iff p names x
  have items (xs : List (Tree F)) (small : ∀ x ∈ xs, sizeOf x < sizeOf t) :
      (xs.map (Tree.safe p names)).all id = true ↔ ∀ x ∈ xs, x.Safe p names := by
    simp only [List.all_map,List.all_eq_true,Function.comp_def,id_eq]
    exact forall_congr' fun x => forall_congr' fun hx => sub x (small x hx)
  cases t with
  | literal | var => simp [Tree.safe,Tree.Safe]
  | tuple xs | construct _ _ xs =>
      simp only [Tree.safe,Tree.Safe]
      exact items xs (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
  | project x _ | store x | load x | hint _ x channel | neg x =>
      simp only [Tree.safe,Tree.Safe]
      exact sub x (by simp_wf; try omega)
  | binary _ x y | assertEq _ x y | letValue _ x y =>
      simp only [Tree.safe,Tree.Safe,Bool.and_eq_true]
      exact and_congr (sub x (by simp_wf; omega)) (sub y (by simp_wf; omega))
  | call n xs =>
      simp only [Tree.safe,Tree.Safe,Bool.and_eq_true,decide_eq_true_eq]
      exact and_congr Iff.rfl (items xs (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))
  | expand f xs b =>
      simp only [Tree.safe,Tree.Safe,Bool.and_eq_true,decide_eq_true_eq,and_assoc]
      rw [sub b (by simp_wf; omega), items xs (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
  | matchValue x arms =>
      simp only [Tree.safe,Tree.Safe,Bool.and_eq_true]
      apply and_congr (sub x (by simp_wf; omega))
      simp only [List.all_map,List.all_eq_true,Function.comp_def,id_eq]
      exact forall_congr' fun a => forall_congr' fun ha =>
        sub a.2 (by simp_wf; have := List.sizeOf_lt_of_mem ha; cases a; simp_all only [Prod.mk.sizeOf_spec]; omega)
termination_by sizeOf t
decreasing_by exact smaller

instance [DecidableEq F] (p : Aiur.Program F) (names : List String) (t : Tree F) : Decidable (t.Safe p names) :=
  decidable_of_iff (t.safe p names = true) (Tree.safe_iff p names t)

/-- Record enough static types to reflect an erased call's parameter checks.
All tests concern finite syntax; no semantic property is decided here. -/
def Tree.checkTypes (q : Aiur.Program F) (locals : List (String × Aiur.Ty)) (tree : Tree F) : Option Aiur.Ty := do
  let type ← (inferType q "$inline" locals tree.target).toOption
  let checks : Option Unit := match tree with
    | .literal _ | .var _ => some ()
    | .tuple xs | .construct _ _ xs | .call _ xs => (xs.mapM (Tree.checkTypes q locals)).map fun _ => ()
    | .project x _ | .store x | .load x | .hint _ x channel | .neg x => (x.checkTypes q locals).map fun _ => ()
    | .binary _ x y | .assertEq _ x y => do
        let _ ← x.checkTypes q locals
        let _ ← y.checkTypes q locals
        some ()
    | .letValue p x b => do
        let type ← x.checkTypes q locals
        let bs ← (checkPattern q.enums "$inline" p type).toOption
        let _ ← b.checkTypes q (bs ++ locals)
        some ()
    | .expand f xs b => do
        let types ← xs.mapM (Tree.checkTypes q locals)
        if types ≠ f.params.map Prod.snd then none else do
          let _ ← b.checkTypes q f.params
          some ()
    | .matchValue x arms => do
        let type ← x.checkTypes q locals
        let _ ← arms.mapM fun (a : Aiur.Pattern F × Tree F) => do
          let bs ← (checkPattern q.enums "$inline" a.1 type).toOption
          a.2.checkTypes q (bs ++ locals)
        some ()
  checks.map (fun _ => type)
termination_by sizeOf tree
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def expand (p : Aiur.Program F) (names : List String) (depth : Nat) (expr : Aiur.Expr F) : Except String (Tree F) := do
  match expr with
  | .literal x => return .literal x
  | .var n => return .var n
  | .tuple xs => return .tuple (← xs.mapM (expand p names depth))
  | .construct n c xs => return .construct n c (← xs.mapM (expand p names depth))
  | .project x i => return .project (← expand p names depth x) i
  | .store x => return .store (← expand p names depth x)
  | .load x => return .load (← expand p names depth x)
  | .hint t x channel => return .hint t (← expand p names depth x) channel
  | .neg x => return .neg (← expand p names depth x)
  | .binary op x y => return .binary op (← expand p names depth x) (← expand p names depth y)
  | .assertEq op x y => return .assertEq op (← expand p names depth x) (← expand p names depth y)
  | .letValue pat x b => return .letValue pat (← expand p names depth x) (← expand p names depth b)
  | .matchValue x arms =>
      let value ← expand p names depth x
      let branches ← arms.mapM fun a => return (a.1, ← expand p names depth a.2)
      return .matchValue value branches
  | .call n xs =>
      let args ← xs.mapM (expand p names depth)
      if !names.contains n then return .call n args
      let some callee := p.findFunction? n | throw s!"unknown inline function '{n}'"
      match depth with
      | 0 => throw s!"inline cycle through '{n}'"
      | depth + 1 => return .expand callee args (← expand p names depth callee.body)
termination_by (depth, sizeOf expr)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

end Aiur.Inlining
