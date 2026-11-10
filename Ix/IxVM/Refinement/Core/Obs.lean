import Ix.IxVM.Refinement.Mirror
import Aiur.HeapMono

/-! # Observed derivations: inversion and the induction on size

Spike S3 (`plans/ixvm-no-false-plan.md` 8.4, 8.7). The core of IxVM is proved
sound against the kernel's rules by **one induction on derivation size over all
functions at once**. A derivation is an observed one (`ObsFn`, with its call
list), because the collision escape of the statement is read off the calls; its
size is the length of the call list. A callee's call list is a strict infix of
its caller's (`ObsExpr.call` adds the callee's own entry), so the statement for
the callees "at smaller size" is the statement for every observed derivation
with fewer calls (`ObsFn.strong_induction`).

This module is generic (nothing about IxVM): the inversion lemmas for observed
expressions, one per node (the observed twins of `Mirror.lean`'s
`EvalExpr.*_inv`), the arm selection (`selectArm_mem`), and the induction
principle. -/

namespace Aiur.Generic.SourceSemantics

variable {F : Type} [Field F] [DecidableEq F] {world : World F} {types : Types}
  {locals : Environment F Nat} {before after : Heap F} {result : SourceValue F}
  {calls : List (Call F)}

/-! ## Inversion at the head of an observed expression -/

theorem ObsExpr.literal_inv {x : F}
    (h : ObsExpr world types locals (.literal x) before result after calls) :
    result = .field x ∧ after = before ∧ calls = [] := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem ObsExpr.var_inv {name : String}
    (h : ObsExpr world types locals (.var name) before result after calls) :
    locals.find? (·.1 == name) = some (name, result) ∧ after = before ∧ calls = [] := by
  cases h with | var lookup => exact ⟨lookup, rfl, rfl⟩

theorem ObsExpr.load_inv {e : Expr F}
    (h : ObsExpr world types locals (.load e) before result after calls) :
    ∃ input, ObsExpr world types locals e before input after calls ∧
      loadValue after input = .ok result := by
  cases h with | load pointer loaded => exact ⟨_, pointer, loaded⟩

theorem ObsExpr.store_inv {e : Expr F}
    (h : ObsExpr world types locals (.store e) before result after calls) :
    ∃ input middle, ObsExpr world types locals e before input middle calls ∧
      result = .ptr input.type middle.length ∧ after = middle ++ [input] := by
  cases h with | store value => exact ⟨_, _, value, rfl, rfl⟩

theorem ObsExpr.construct_inv {name : String} {args : Option (List Ty)} {ctor : String}
    {es : List (Expr F)}
    (h : ObsExpr world types locals (.construct name args ctor es) before result after calls) :
    ∃ values, ObsArgs world types locals es before values after calls ∧
      result = .construct (instanceName types name args) ctor values := by
  cases h with | construct items => exact ⟨_, items, rfl⟩

theorem ObsExpr.tuple_inv {es : List (Expr F)}
    (h : ObsExpr world types locals (.tuple es) before result after calls) :
    ∃ values, ObsArgs world types locals es before values after calls ∧
      result = .tuple values := by
  cases h with | tuple items => exact ⟨_, items, rfl⟩

theorem ObsExpr.letValue_inv {pat : Pattern F} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue pat e rest) before result after calls) :
    ∃ input middle bindings calls₁ calls₂,
      ObsExpr world types locals e before input middle calls₁ ∧
      world.matchPattern types middle pat input = .ok (some bindings) ∧
      ObsExpr world types (bindings ++ locals) rest middle result after calls₂ ∧
      calls = calls₁ ++ calls₂ := by
  cases h with
  | letValue value matched body => exact ⟨_, _, _, _, _, value, matched, body, rfl⟩

theorem ObsExpr.matchValue_inv {e : Expr F} {arms : List (Pattern F × Expr F)}
    (h : ObsExpr world types locals (.matchValue e arms) before result after calls) :
    ∃ input middle bindings body calls₁ calls₂,
      ObsExpr world types locals e before input middle calls₁ ∧
      selectArm world types middle input arms = .ok (some (bindings, body)) ∧
      ObsExpr world types (bindings ++ locals) body middle result after calls₂ ∧
      calls = calls₁ ++ calls₂ := by
  cases h with
  | matchValue value selected branch =>
    exact ⟨_, _, _, _, _, _, value, selected, branch, rfl⟩

theorem ObsExpr.binary_inv {op : BinOp} {lhs rhs : Expr F}
    (h : ObsExpr world types locals (.binary op lhs rhs) before result after calls) :
    ∃ x y middle calls₁ calls₂, ObsExpr world types locals lhs before x middle calls₁ ∧
      ObsExpr world types locals rhs middle y after calls₂ ∧ evalBinOp op x y = .ok result ∧
      calls = calls₁ ++ calls₂ := by
  cases h with
  | binary left right operation => exact ⟨_, _, _, _, _, left, right, operation, rfl⟩

theorem ObsExpr.builtin_inv {op : Builtin} {es : List (Expr F)}
    (h : ObsExpr world types locals (.builtin op es) before result after calls) :
    ∃ values, ObsArgs world types locals es before values after calls ∧
      op.apply values = .ok result := by
  cases h with | builtin items applied => exact ⟨_, items, applied⟩

theorem ObsArgs.nil_inv {values : List (SourceValue F)}
    (h : ObsArgs world types locals [] before values after calls) :
    values = [] ∧ after = before ∧ calls = [] := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem ObsArgs.cons_inv {e : Expr F} {es : List (Expr F)} {values : List (SourceValue F)}
    (h : ObsArgs world types locals (e :: es) before values after calls) :
    ∃ v vs middle calls₁ calls₂, values = v :: vs ∧
      ObsExpr world types locals e before v middle calls₁ ∧
      ObsArgs world types locals es middle vs after calls₂ ∧ calls = calls₁ ++ calls₂ := by
  cases h with | cons head tail => exact ⟨_, _, _, _, _, rfl, head, tail, rfl⟩

/-! ## Arm selection -/

omit [Field F] in
/-- **The selected arm is an arm whose pattern matched**, with the bindings the
match produced. (Which matching arm is selected is not needed when every arm's
result is sound on its own.) -/
theorem selectArm_mem {arms : List (Pattern F × Expr F)} {input : SourceValue F}
    {heap : Heap F} {bindings : Environment F Nat} {body : Expr F}
    (selected : selectArm world types heap input arms = .ok (some (bindings, body))) :
    ∃ pat, (pat, body) ∈ arms ∧ world.matchPattern types heap pat input = .ok (some bindings) := by
  induction arms with
  | nil => simp [SourceSemantics.selectArm] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pat, expr⟩
      cases matched : world.matchPattern types heap pat input with
      | error e => simp [SourceSemantics.selectArm, matched, bind, Except.bind] at selected
      | ok bs => cases bs with
        | none =>
            obtain ⟨p, hp, hm⟩ := ih (by
              simpa [SourceSemantics.selectArm, matched, bind, Except.bind] using selected)
            exact ⟨p, by simp [hp], hm⟩
        | some bs =>
            have same : bs = bindings ∧ expr = body := by
              simpa [SourceSemantics.selectArm, matched, bind, Except.bind, pure, Except.pure]
                using selected
            obtain ⟨rfl, rfl⟩ := same
            exact ⟨pat, by simp, matched⟩

/-! ## The induction on size -/

/-- **Strong induction on the size of observed derivations**, the length of
their call lists, for every function at once: if every observed derivation
satisfies `P` whenever all observed derivations with strictly fewer calls do,
then every observed derivation satisfies `P`. -/
theorem ObsFn.strong_induction
    (P : String → List (SourceValue F) → Heap F → SourceValue F → Heap F → List (Call F) → Prop)
    (step : ∀ n args b v a cs, ObsFn world n args b v a cs →
      (∀ n' args' b' v' a' cs', cs'.length < cs.length → ObsFn world n' args' b' v' a' cs' →
        P n' args' b' v' a' cs') →
      P n args b v a cs) :
    ∀ n args b v a cs, ObsFn world n args b v a cs → P n args b v a cs := by
  have key : ∀ N n args b v a cs, cs.length ≤ N → ObsFn world n args b v a cs →
      P n args b v a cs := by
    intro N
    induction N with
    | zero =>
        intro n args b v a cs hle ev
        exact step _ _ _ _ _ _ ev (fun _ _ _ _ _ cs' hlt _ => absurd hlt (by omega))
    | succ N ih =>
        intro n args b v a cs hle ev
        exact step _ _ _ _ _ _ ev (fun n' args' b' v' a' cs' hlt ev' =>
          ih n' args' b' v' a' cs' (by omega) ev')
  exact fun n args b v a cs ev => key _ n args b v a cs (Nat.le_refl _) ev

/-! ## The heap only grows -/

theorem ObsExpr.heap_extends {expr : Expr F}
    (evaluated : ObsExpr world types locals expr before result after calls) :
    Heap.Extends before after := by
  induction evaluated using ObsExpr.rec
    (motive_2 := fun _ _ _ before _ after _ _ => Heap.Extends before after)
    (motive_3 := fun _ _ before _ after _ _ => Heap.Extends before after)
    (motive_4 := fun _ _ _ before _ _ after _ _ => Heap.Extends before after)
    (motive_5 := fun _ _ _ before _ _ after _ _ => Heap.Extends before after) with
  | literal | var | nil =>
      exact Heap.Extends.refl _
  | block _ ih
  | blockExit _ ih
  | global _ _ _ ih
  | tuple _ ih
  | array _ ih
  | «repeat» _ ih
  | index _ _ ih
  | slice _ _ ih
  | builtin _ _ ih
  | update _ _ ih
  | record _ ih
  | member _ _ ih
  | construct _ ih
  | constructAs _ ih
  | project _ _ ih
  | load _ _ ih
  | hint _ _ ih
  | neg _ _ ih
  | intro _ _ ih
  | returned _ _ ih
  | exit _ ih
  | exitPayload _ ih
  | fromBlock _ _ ih
  | fromGlobal _ _ _ ih
  | fromTuple _ ih
  | fromArray _ ih
  | fromRepeat _ ih
  | fromIndex _ ih
  | fromSlice _ ih
  | fromBuiltin _ ih
  | fromUpdate _ ih
  | fromRecord _ ih
  | fromMember _ ih
  | fromConstruct _ ih
  | fromConstructAs _ ih
  | fromProject _ ih
  | fromLetValue _ ih
  | fromStore _ ih
  | fromLoad _ ih
  | fromHint _ ih
  | fromNeg _ ih
  | binaryLeft _ ih
  | fromCall _ ih
  | fromMatchValue _ ih
  | head _ ih =>
      exact ih
  | letValue _ _ _ ih₁ ih₂
  | binary _ _ _ ih₁ ih₂
  | call _ _ ih₁ ih₂
  | matchValue _ _ _ ih₁ ih₂
  | cons _ _ ih₁ ih₂
  | letBody _ _ _ ih₁ ih₂
  | binaryRight _ _ ih₁ ih₂
  | matchBody _ _ _ ih₁ ih₂
  | tail _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | store _ ih =>
      exact ih.trans (Heap.Extends.snoc _ _)

theorem ObsArgs.heap_extends {exprs : List (Expr F)} {values : List (SourceValue F)}
    (evaluated : ObsArgs world types locals exprs before values after calls) :
    Heap.Extends before after :=
  (ObsExpr.tuple evaluated).heap_extends

theorem ObsFn.heap_extends {name : String} {args : List (SourceValue F)}
    (evaluated : ObsFn world name args before result after calls) :
    Heap.Extends before after :=
  evaluated.erase.heap_extends

end Aiur.Generic.SourceSemantics
