import Aiur.Generic.ControlNoExit
import Aiur.Generic.ConstScopeFacts
import Aiur.Generic.LookupFacts
import Aiur.Generic.NativeCompleteness

/-! # A deterministic reading of the source semantics

`Generic.SourceSemantics.EvalFn` is a relation: a hint takes any value of its
type, at every evaluation. `execFn` is a function that reads the same rules,
taking the hints' values from a stream (`HintStream`, consumed in evaluation
order) and bounding call and const depth by fuel. It has no rule for
`control` (named blocks and exits), which the checked IxVM program does not
use.

**`EvalFn.exec`** (completeness): in a world whose function bodies use no
`control`, every derivation is an `execFn` run, for some hint stream and every
large enough fuel. So a property of every derivation follows from a
property of every run: refinement proofs reason about a function, by
computing, instead of inverting a derivation node by node. The mirror of a
function is its run (`execFn world fuel name`). -/

namespace Aiur.Generic.SourceSemantics

variable {F : Type} [Field F] [DecidableEq F]

/-- **Hint answers**, consumed in evaluation order. -/
abbrev HintStream (F : Type) := List (Constant F)

mutual
  /-- An expression's run: its value, the heap after it, and the hints left. -/
  def execExpr (world : World F) (fuel : Nat) (types : Types) (locals : Environment F Nat) :
      Expr F → Heap F → HintStream F → Option (SourceValue F × Heap F × HintStream F)
    | .control _ _, _, _ => none
    | .literal x, h, hs => some (.field x, h, hs)
    | .var n, h, hs => (locals.find? (·.1 == n)).map fun p => (p.2, h, hs)
    | .global n (some t), h, hs =>
      match fuel with
      | 0 => none
      | fuel + 1 =>
        match world.constant n (t.subst types) with
        | .ok pat =>
          match Consts.toExpr pat with
          | .ok body => execExpr world fuel [] [] body h hs
          | .error _ => none
        | .error _ => none
    | .global _ none, _, _ => none
    | .tuple es, h, hs =>
      (execArgs world fuel types locals es h hs).map fun (vs, h, hs) => (.tuple vs, h, hs)
    | .array es, h, hs =>
      (execArgs world fuel types locals es h hs).map fun (vs, h, hs) => (.tuple vs, h, hs)
    | .repeat e n, h, hs =>
      (execExpr world fuel types locals e h hs).map fun (v, h, hs) =>
        (.tuple (List.replicate n v), h, hs)
    | .index e i, h, hs =>
      (execExpr world fuel types locals e h hs).bind fun (v, h, hs) =>
        (projectValue v i).toOption.map fun r => (r, h, hs)
    | .slice e a b, h, hs =>
      (execExpr world fuel types locals e h hs).bind fun (v, h, hs) =>
        (sliceValue v a b).toOption.map fun r => (r, h, hs)
    | .builtin op es, h, hs =>
      (execArgs world fuel types locals es h hs).bind fun (vs, h, hs) =>
        (op.apply vs).toOption.map fun r => (r, h, hs)
    | .update paths es, h, hs =>
      (execArgs world fuel types locals es h hs).bind fun (vs, h, hs) =>
        (Update.value types paths vs).toOption.map fun r => (r, h, hs)
    | .record head es, h, hs =>
      (execArgs world fuel types locals es h hs).map fun (vs, h, hs) =>
        (.construct (constructorName types head.type) structConstructor
          (head.order vs (.tuple [])), h, hs)
    | .member e field, h, hs =>
      (execExpr world fuel types locals e h hs).bind fun (v, h, hs) =>
        (memberValue types field v).toOption.map fun r => (r, h, hs)
    | .construct name args ctor es, h, hs =>
      (execArgs world fuel types locals es h hs).map fun (vs, h, hs) =>
        (.construct (instanceName types name args) ctor vs, h, hs)
    | .constructAs _ t ctor es, h, hs =>
      (execArgs world fuel types locals es h hs).map fun (vs, h, hs) =>
        (.construct (constructorName types t) ctor vs, h, hs)
    | .project e i, h, hs =>
      (execExpr world fuel types locals e h hs).bind fun (v, h, hs) =>
        (projectValue v i).toOption.map fun r => (r, h, hs)
    | .letValue pat e rest, h, hs =>
      (execExpr world fuel types locals e h hs).bind fun (v, h, hs) =>
        match world.matchPattern types h pat v with
        | .ok (some bs) => execExpr world fuel types (bs ++ locals) rest h hs
        | _ => none
    | .store e, h, hs =>
      (execExpr world fuel types locals e h hs).map fun (v, h, hs) =>
        (.ptr v.type h.length, h ++ [v], hs)
    | .load e, h, hs =>
      (execExpr world fuel types locals e h hs).bind fun (v, h, hs) =>
        (loadValue h v).toOption.map fun r => (r, h, hs)
    | .hint t key _, h, hs =>
      (execExpr world fuel types locals key h hs).bind fun (_, h, hs) =>
        match hs with
        | c :: hs => if world.typed (t.subst types).toCore c then some (c.toValue, h, hs) else none
        | [] => none
    | .neg e, h, hs =>
      (execExpr world fuel types locals e h hs).bind fun (v, h, hs) =>
        (evalNeg v).toOption.map fun r => (r, h, hs)
    | .binary op l r, h, hs =>
      (execExpr world fuel types locals l h hs).bind fun (x, h, hs) =>
        (execExpr world fuel types locals r h hs).bind fun (y, h, hs) =>
          (evalBinOp op x y).toOption.map fun v => (v, h, hs)
    | .call name targs es, h, hs =>
      (execArgs world fuel types locals es h hs).bind fun (vs, h, hs) =>
        execFn world fuel (instanceName types name targs) vs h hs
    | .matchValue e arms, h, hs =>
      (execExpr world fuel types locals e h hs).bind fun (v, h, hs) =>
        execArms world fuel types locals v arms h hs
  termination_by e _ _ => (fuel, sizeOf e + 1)

  /-- Arguments, left to right. -/
  def execArgs (world : World F) (fuel : Nat) (types : Types) (locals : Environment F Nat) :
      List (Expr F) → Heap F → HintStream F → Option (List (SourceValue F) × Heap F × HintStream F)
    | [], h, hs => some ([], h, hs)
    | e :: es, h, hs =>
      (execExpr world fuel types locals e h hs).bind fun (v, h, hs) =>
        (execArgs world fuel types locals es h hs).map fun (vs, h, hs) => (v :: vs, h, hs)
  termination_by es _ _ => (fuel, sizeOf es + 1)

  /-- The first arm whose pattern matches, as `selectArm` selects it. -/
  def execArms (world : World F) (fuel : Nat) (types : Types) (locals : Environment F Nat)
      (value : SourceValue F) :
      List (Pattern F × Expr F) → Heap F → HintStream F → Option (SourceValue F × Heap F × HintStream F)
    | [], _, _ => none
    | (pat, body) :: arms, h, hs =>
      match world.matchPattern types h pat value with
      | .ok (some bs) => execExpr world fuel types (bs ++ locals) body h hs
      | .ok none => execArms world fuel types locals value arms h hs
      | .error _ => none
  termination_by arms _ _ => (fuel, sizeOf arms + 1)

  /-- **A call's run**: one unit of fuel per call. -/
  def execFn (world : World F) :
      Nat → String → List (SourceValue F) → Heap F → HintStream F →
        Option (SourceValue F × Heap F × HintStream F)
    | 0, _, _, _, _ => none
    | fuel + 1, name, args, h, hs =>
      match world.prepare name args with
      | .ok (types, locals, body) => execExpr world fuel types locals body h hs
      | .error _ => none
  termination_by fuel _ _ _ _ => (fuel, 0)
end

/-! ## Completeness -/

/-- **No `control` in any body the world prepares.** -/
def ControlFree (world : World F) : Prop :=
  ∀ n args types locals body, world.prepare n args = .ok (types, locals, body) →
    ControlLower.hasControl body = false

omit [Field F] in
/-- **A checked source whose function bodies use no `control` has a
`ControlFree` world**: every body `s.world.prepare` returns is either a
function's body or a map row's constant expression. -/
theorem _root_.Aiur.Generic.Source.controlFree (s : Source F)
    (h : s.program.functions.all (fun f => !ControlLower.hasControl f.body) = true) :
    ControlFree s.world := by
  intro name args types locals body prepared
  cases hfn : s.program.sourceFunction? name with
  | some fn =>
    obtain ⟨-, -, rfl⟩ := Source.world_prepare_of_sourceFunction hfn prepared
    obtain ⟨f, hf, hbody⟩ := Program.sourceFunction?_body_mem hfn
    rw [hbody]
    rw [List.all_eq_true] at h
    simpa using h f hf
  | none =>
    simp only [Source.world, sourceWorld, hfn, bind, Except.bind, pure, Except.pure] at prepared
    cases hmap : lookupMap s.tables name args with
    | error e => simp [hmap] at prepared
    | ok row =>
      simp only [hmap, Except.ok.injEq, Prod.mk.injEq] at prepared
      rw [← prepared.2.2]
      exact (constantExpr_closed row).noControl

section
variable {world : World F}

theorem execArms_of_selectArm {types : Types} {locals : Environment F Nat} {heap : Heap F}
    {value : SourceValue F} {bs : Environment F Nat} {body : Expr F} {k : Nat}
    {hs : HintStream F} :
    ∀ {arms : List (Pattern F × Expr F)},
      selectArm world types heap value arms = .ok (some (bs, body)) →
      execArms world k types locals value arms heap hs =
        execExpr world k types (bs ++ locals) body heap hs
  | [], selected => by simp [selectArm] at selected
  | (pat, e) :: arms, selected => by
    cases m : world.matchPattern types heap pat value with
    | error err => simp [selectArm, m, bind, Except.bind] at selected
    | ok r =>
      cases r with
      | none =>
        simp only [selectArm, m, bind, Except.bind] at selected
        rw [execArms, m]
        exact execArms_of_selectArm selected
      | some bs' =>
        simp only [selectArm, m, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          Option.some.injEq, Prod.mk.injEq] at selected
        obtain ⟨rfl, rfl⟩ := selected
        rw [execArms, m]

theorem hint_step {types : Types} {locals : Environment F Nat} {key : Expr F} {t : Ty}
    {channel : String} {before after : Heap F} {input : SourceValue F} {value : Constant F}
    {hs : HintStream F} {k0 : Nat}
    (run : ∀ k ≥ k0, ∀ rest, execExpr world k types locals key before (hs ++ rest) =
      some (input, after, rest))
    (typed : world.typed (t.subst types).toCore value = true) :
    ∃ (hs' : HintStream F) (k0' : Nat), ∀ k ≥ k0', ∀ rest,
      execExpr world k types locals (.hint t key channel) before (hs' ++ rest) =
        some (value.toValue, after, rest) := by
  refine ⟨hs ++ [value], k0, fun k hk rest => ?_⟩
  rw [execExpr, List.append_assoc, run k hk ([value] ++ rest)]
  simp [typed]

/-- **Every derivation is a run** of a body without `control`, for some hint
stream and every large enough fuel. -/
theorem EvalExpr.exec (free : ControlFree world) {types : Types} {locals : Environment F Nat}
    {expr : Expr F} {before after : Heap F} {result : SourceValue F}
    (ev : EvalExpr world types locals expr before result after) :
    ControlLower.hasControl expr = false →
      ∃ (hs : HintStream F) (k0 : Nat), ∀ k ≥ k0, ∀ rest,
        execExpr world k types locals expr before (hs ++ rest) = some (result, after, rest) := by
  induction ev using EvalExpr.rec
    (motive_2 := fun ts ls es b vs a _ => (∀ e ∈ es, ControlLower.hasControl e = false) →
      ∃ (hs : HintStream F) (k0 : Nat), ∀ k ≥ k0, ∀ rest,
        execArgs world k ts ls es b (hs ++ rest) = some (vs, a, rest))
    (motive_3 := fun n xs b v a _ =>
      ∃ (hs : HintStream F) (k0 : Nat), ∀ k ≥ k0, ∀ rest,
        execFn world k n xs b (hs ++ rest) = some (v, a, rest))
    (motive_4 := fun _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True) with
  | block _ _ => intro h; simp [ControlLower.hasControl] at h
  | blockExit _ _ => intro h; simp [ControlLower.hasControl] at h
  | literal => intro _; exact ⟨[], 0, fun k _ rest => by simp [execExpr]⟩
  | var lookup => intro _; exact ⟨[], 0, fun k _ rest => by simp [execExpr, lookup]⟩
  | global lookup interpreted _ ih =>
    intro _
    obtain ⟨hs, k0, run⟩ := ih (Consts.toExpr_closed _ interpreted).noControl
    refine ⟨hs, k0 + 1, fun k hk rest => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [execExpr, lookup, interpreted]
    exact run k' (by omega) rest
  | tuple _ ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa [ControlLower.hasControl, List.any_eq_false] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest]⟩
  | array _ ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa [ControlLower.hasControl, List.any_eq_false] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest]⟩
  | «repeat» _ ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa only [ControlLower.hasControl] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest]⟩
  | index _ op ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa only [ControlLower.hasControl] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest, op, Except.toOption]⟩
  | slice _ op ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa only [ControlLower.hasControl] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest, op, Except.toOption]⟩
  | builtin _ op ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa [ControlLower.hasControl, List.any_eq_false] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest, op, Except.toOption]⟩
  | update _ op ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa [ControlLower.hasControl, List.any_eq_false] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest, op, Except.toOption]⟩
  | record _ ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa [ControlLower.hasControl, List.any_eq_false] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest]⟩
  | member _ op ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa only [ControlLower.hasControl] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest, op, Except.toOption]⟩
  | construct _ ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa [ControlLower.hasControl, List.any_eq_false] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest]⟩
  | constructAs _ ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa [ControlLower.hasControl, List.any_eq_false] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest]⟩
  | project _ op ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa only [ControlLower.hasControl] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest, op, Except.toOption]⟩
  | letValue _ matched _ ih1 ih2 =>
    intro h
    simp only [ControlLower.hasControl, Bool.or_eq_false_iff] at h
    obtain ⟨hs1, k1, run1⟩ := ih1 h.1
    obtain ⟨hs2, k2, run2⟩ := ih2 h.2
    refine ⟨hs1 ++ hs2, k1 + k2, fun k hk rest => ?_⟩
    rw [execExpr, List.append_assoc, run1 k (by omega) (hs2 ++ rest)]
    simp only [Option.bind_some, matched]
    exact run2 k (by omega) rest
  | store _ ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa only [ControlLower.hasControl] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest]⟩
  | load _ loaded ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa only [ControlLower.hasControl] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest, loaded, Except.toOption]⟩
  | hint _ typed ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa only [ControlLower.hasControl] using h)
    exact hint_step run typed
  | neg _ op ih =>
    intro h
    obtain ⟨hs, k0, run⟩ := ih (by simpa only [ControlLower.hasControl] using h)
    exact ⟨hs, k0, fun k hk rest => by simp [execExpr, run k hk rest, op, Except.toOption]⟩
  | binary _ _ op ih1 ih2 =>
    intro h
    simp only [ControlLower.hasControl, Bool.or_eq_false_iff] at h
    obtain ⟨hs1, k1, run1⟩ := ih1 h.1
    obtain ⟨hs2, k2, run2⟩ := ih2 h.2
    refine ⟨hs1 ++ hs2, k1 + k2, fun k hk rest => ?_⟩
    rw [execExpr, List.append_assoc, run1 k (by omega) (hs2 ++ rest)]
    simp [run2 k (by omega) rest, op, Except.toOption]
  | call _ _ ih1 ih2 =>
    intro h
    obtain ⟨hs1, k1, run1⟩ := ih1 (by simpa [ControlLower.hasControl, List.any_eq_false] using h)
    obtain ⟨hs2, k2, run2⟩ := ih2
    refine ⟨hs1 ++ hs2, k1 + k2, fun k hk rest => ?_⟩
    rw [execExpr, List.append_assoc, run1 k (by omega) (hs2 ++ rest)]
    simp only [Option.bind_some]
    exact run2 k (by omega) rest
  | matchValue _ selected _ ih1 ih2 =>
    intro h
    simp only [ControlLower.hasControl, Bool.or_eq_false_iff, List.any_map, List.any_eq_false,
      Function.comp_def, id_eq] at h
    obtain ⟨hs1, k1, run1⟩ := ih1 h.1
    obtain ⟨pat, member⟩ := selected_member selected
    obtain ⟨hs2, k2, run2⟩ := ih2 (by simpa using h.2 _ member)
    refine ⟨hs1 ++ hs2, k1 + k2, fun k hk rest => ?_⟩
    rw [execExpr, List.append_assoc, run1 k (by omega) (hs2 ++ rest)]
    simp only [Option.bind_some]
    rw [execArms_of_selectArm selected]
    exact run2 k (by omega) rest
  | nil => exact ⟨[], 0, fun k _ rest => by simp [execArgs]⟩
  | cons _ _ ih1 ih2 =>
    rename_i h
    obtain ⟨hs1, k1, run1⟩ := ih1 (h _ (by simp))
    obtain ⟨hs2, k2, run2⟩ := ih2 (fun e he => h e (by simp [he]))
    refine ⟨hs1 ++ hs2, k1 + k2, fun k hk rest => ?_⟩
    rw [execArgs, List.append_assoc, run1 k (by omega) (hs2 ++ rest)]
    simp [run2 k (by omega) rest]
  | intro prepared _ ih =>
    obtain ⟨hs, k0, run⟩ := ih (free _ _ _ _ _ prepared)
    refine ⟨hs, k0 + 1, fun k hk rest => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [execFn, prepared]
    exact run k' (by omega) rest
  | returned prepared body _ =>
    exact (OpenSource.EvalExit.hasControl (OpenSource.exit_of_closed body)
      (free _ _ _ _ _ prepared)).elim
  | _ => trivial

/-- **Every call derivation is a run**, for some hint stream and every large
enough fuel. -/
theorem EvalFn.exec (free : ControlFree world) {name : String} {args : List (SourceValue F)}
    {before after : Heap F} {result : SourceValue F}
    (ev : EvalFn world name args before result after) :
    ∃ (hs : HintStream F) (k0 : Nat), ∀ k ≥ k0, ∀ rest,
      execFn world k name args before (hs ++ rest) = some (result, after, rest) := by
  cases ev with
  | intro prepared body =>
    obtain ⟨hs, k0, run⟩ := body.exec free (free _ _ _ _ _ prepared)
    refine ⟨hs, k0 + 1, fun k hk rest => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [execFn, prepared]
    exact run k' (by omega) rest
  | returned prepared body =>
    exact (OpenSource.EvalExit.hasControl (OpenSource.exit_of_closed body)
      (free _ _ _ _ _ prepared)).elim

/-- **Any two expression runs that consume the same hint stream produce the same
value and heap.** -/
theorem execExpr_unique_of_runs {types : Types} {locals : Environment F Nat}
    {expr : Expr F} {before after₁ after₂ : Heap F}
    {result₁ result₂ : SourceValue F} {hs : HintStream F} {k₁ k₂ : Nat}
    (run₁ : ∀ k ≥ k₁, ∀ rest,
      execExpr world k types locals expr before (hs ++ rest) = some (result₁, after₁, rest))
    (run₂ : ∀ k ≥ k₂, ∀ rest,
      execExpr world k types locals expr before (hs ++ rest) = some (result₂, after₂, rest)) :
    result₁ = result₂ ∧ after₁ = after₂ := by
  have h := run₁ (max k₁ k₂) (Nat.le_max_left k₁ k₂) []
  rw [run₂ (max k₁ k₂) (Nat.le_max_right k₁ k₂) []] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.1.symm⟩

/-- **Any two call runs that consume the same hint stream produce the same value
and heap.** -/
theorem execFn_unique_of_runs {name : String} {args : List (SourceValue F)}
    {before after₁ after₂ : Heap F} {result₁ result₂ : SourceValue F}
    {hs : HintStream F} {k₁ k₂ : Nat}
    (run₁ : ∀ k ≥ k₁, ∀ rest,
      execFn world k name args before (hs ++ rest) = some (result₁, after₁, rest))
    (run₂ : ∀ k ≥ k₂, ∀ rest,
      execFn world k name args before (hs ++ rest) = some (result₂, after₂, rest)) :
    result₁ = result₂ ∧ after₁ = after₂ := by
  have h := run₁ (max k₁ k₂) (Nat.le_max_left k₁ k₂) []
  rw [run₂ (max k₁ k₂) (Nat.le_max_right k₁ k₂) []] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.1.symm⟩

end

end Aiur.Generic.SourceSemantics
