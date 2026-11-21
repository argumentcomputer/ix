import Aiur.Generic.ControlEnvironment

namespace Aiur.Generic.OpenSource
open SourceSemantics

abbrev Post (F : Type) := SourceValue F → Heap F → Prop
abbrev ExitPost (F : Type) := ExitTarget → SourceValue F → Heap F → Prop

def Exec [Field F] [DecidableEq F] (world : World F) (calls : CallRelation F)
    (types : Types) (locals : Environment F Nat) (expr : Expr F)
    (normal : Post F) (abrupt : ExitPost F) (before : Heap F) : Prop :=
  (∃ value after, EvalExpr world calls types locals expr before value after ∧ normal value after) ∨
  ∃ target value after, EvalExit world calls types locals expr before target value after ∧ abrupt target value after

def ExecArgs [Field F] [DecidableEq F] (world : World F) (calls : CallRelation F)
    (types : Types) (locals : Environment F Nat) (exprs : List (Expr F))
    (normal : List (SourceValue F) → Heap F → Prop) (abrupt : ExitPost F) (before : Heap F) : Prop :=
  (∃ values after, EvalArgs world calls types locals exprs before values after ∧ normal values after) ∨
  ∃ target value after, EvalArgsExit world calls types locals exprs before target value after ∧ abrupt target value after

variable [Field F] [DecidableEq F] {world : World F} {calls : CallRelation F}
variable {types : Types} {locals : Environment F Nat} {normal : Post F} {abrupt : ExitPost F}

theorem Exec.congr (normalEq : ∀ v h, normal v h ↔ normal' v h)
    (abruptEq : ∀ t v h, abrupt t v h ↔ abrupt' t v h) :
    Exec world calls types locals expr normal abrupt heap ↔
      Exec world calls types locals expr normal' abrupt' heap := by
  simp only [Exec, normalEq, abruptEq]

theorem ExecArgs.congr (normalEq : ∀ vs h, next vs h ↔ next' vs h)
    (abruptEq : ∀ t v h, abrupt t v h ↔ abrupt' t v h) :
    ExecArgs world calls types locals exprs next abrupt heap ↔
      ExecArgs world calls types locals exprs next' abrupt' heap := by
  simp only [ExecArgs, normalEq, abruptEq]

theorem EvalArgs.length (ev : EvalArgs world calls types locals exprs before values after) :
    values.length = exprs.length := by
  induction exprs generalizing values before with
  | nil => cases ev; rfl
  | cons expr exprs ih =>
      cases ev with
      | cons head tail => simpa using congrArg Nat.succ (ih tail)

theorem ExecArgs.congr_length (normalEq : ∀ vs h, vs.length = exprs.length → (next vs h ↔ next' vs h))
    (abruptEq : ∀ t v h, abrupt t v h ↔ abrupt' t v h) :
    ExecArgs world calls types locals exprs next abrupt heap ↔
      ExecArgs world calls types locals exprs next' abrupt' heap := by
  constructor <;> rintro (⟨vs, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
  · exact .inl ⟨vs, h, ev, (normalEq vs h ev.length).mp post⟩
  · exact .inr ⟨t, v, h, ev, (abruptEq t v h).mp post⟩
  · exact .inl ⟨vs, h, ev, (normalEq vs h ev.length).mpr post⟩
  · exact .inr ⟨t, v, h, ev, (abruptEq t v h).mpr post⟩

theorem exec_literal : Exec world calls types locals (.literal x) normal abrupt heap ↔ normal (.field x) heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩) <;> cases ev
    exact post
  · intro h; exact .inl ⟨_, _, .literal, h⟩

theorem exec_var : Exec world calls types locals (.var name) normal abrupt heap ↔
    ∃ value, locals.find? (·.1 == name) = some (name, value) ∧ normal value heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩) <;> cases ev
    exact ⟨_, ‹_›, post⟩
  · rintro ⟨v, lookup, post⟩; exact .inl ⟨_, _, .var lookup, post⟩

theorem exec_exit : Exec world calls types locals (.control (.exit target) expr) normal abrupt heap ↔
    Exec world calls types locals expr (abrupt target) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev
    · cases ev with
      | exit ev => exact .inl ⟨_, _, ev, post⟩
      | exitPayload ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inr ⟨_, _, _, .exit ev, post⟩
    · exact .inr ⟨_, _, _, .exitPayload ev, post⟩

theorem exec_block : Exec world calls types locals (.control (.block label) expr) normal abrupt heap ↔
    Exec world calls types locals expr normal
      (fun target v h => if target = .block label then normal v h else abrupt target v h) heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with
      | block ev => exact .inl ⟨_, _, ev, post⟩
      | blockExit ev => exact .inr ⟨_, _, _, ev, by simpa using post⟩
    · cases ev with
      | fromBlock ne ev => exact .inr ⟨_, _, _, ev, by simpa only [if_neg ne] using post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .block ev, post⟩
    · split at post
      · rename_i same; subst t; exact .inl ⟨_, _, .blockExit ev, post⟩
      · exact .inr ⟨_, _, _, .fromBlock ‹_› ev, post⟩

theorem execArgs_nil : ExecArgs world calls types locals [] next abrupt heap ↔ next [] heap := by
  constructor
  · rintro (⟨vs, h, ev, post⟩ | ⟨t, v, h, ev, post⟩) <;> cases ev
    exact post
  · intro h; exact .inl ⟨_, _, .nil, h⟩

theorem execArgs_cons : ExecArgs world calls types locals (expr :: exprs) next abrupt heap ↔
    Exec world calls types locals expr
      (fun v h => ExecArgs world calls types locals exprs (fun vs a => next (v :: vs) a) abrupt h) abrupt heap := by
  constructor
  · rintro (⟨vs, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with
      | cons head tail => exact .inl ⟨_, _, head, .inl ⟨_, _, tail, post⟩⟩
    · cases ev with
      | head ev => exact .inr ⟨_, _, _, ev, post⟩
      | tail head tail => exact .inl ⟨_, _, head, .inr ⟨_, _, _, tail, post⟩⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨vs, a, tail, post⟩ | ⟨t, v, a, tail, post⟩
      · exact .inl ⟨_, _, .cons ev tail, post⟩
      · exact .inr ⟨_, _, _, .tail ev tail, post⟩
    · exact .inr ⟨_, _, _, .head ev, post⟩

theorem exec_repeat : Exec world calls types locals (.repeat expr n) normal abrupt heap ↔
    Exec world calls types locals expr (fun v h => normal (.tuple (List.replicate n v)) h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | «repeat» value => exact .inl ⟨_, _, value, post⟩
    · cases ev with | fromRepeat ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .repeat ev, post⟩
    · exact .inr ⟨_, _, _, .fromRepeat ev, post⟩

theorem exec_store : Exec world calls types locals (.store expr) normal abrupt heap ↔
    Exec world calls types locals expr (fun v h => normal (.ptr v.type h.length) (h ++ [v])) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | store value => exact .inl ⟨_, _, value, post⟩
    · cases ev with | fromStore ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .store ev, post⟩
    · exact .inr ⟨_, _, _, .fromStore ev, post⟩

theorem exec_index : Exec world calls types locals (.index expr i) normal abrupt heap ↔
    Exec world calls types locals expr (fun v h => ∃ result, projectValue v i = .ok result ∧ normal result h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | index value operation => exact .inl ⟨_, _, value, _, operation, post⟩
    · cases ev with | fromIndex ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨result, operation, post⟩
      exact .inl ⟨_, _, .index ev operation, post⟩
    · exact .inr ⟨_, _, _, .fromIndex ev, post⟩

theorem exec_project : Exec world calls types locals (.project expr i) normal abrupt heap ↔
    Exec world calls types locals expr (fun v h => ∃ result, projectValue v i = .ok result ∧ normal result h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | project value operation => exact .inl ⟨_, _, value, _, operation, post⟩
    · cases ev with | fromProject ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨result, operation, post⟩
      exact .inl ⟨_, _, .project ev operation, post⟩
    · exact .inr ⟨_, _, _, .fromProject ev, post⟩

theorem exec_member : Exec world calls types locals (.member expr field) normal abrupt heap ↔
    Exec world calls types locals expr (fun v h => ∃ result, memberValue types field v = .ok result ∧ normal result h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | member value operation => exact .inl ⟨_, _, value, _, operation, post⟩
    · cases ev with | fromMember ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨result, operation, post⟩
      exact .inl ⟨_, _, .member ev operation, post⟩
    · exact .inr ⟨_, _, _, .fromMember ev, post⟩

theorem exec_slice : Exec world calls types locals (.slice expr start stop) normal abrupt heap ↔
    Exec world calls types locals expr (fun v h => ∃ result, sliceValue v start stop = .ok result ∧ normal result h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | slice value operation => exact .inl ⟨_, _, value, _, operation, post⟩
    · cases ev with | fromSlice ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨result, operation, post⟩
      exact .inl ⟨_, _, .slice ev operation, post⟩
    · exact .inr ⟨_, _, _, .fromSlice ev, post⟩

theorem exec_load : Exec world calls types locals (.load expr) normal abrupt heap ↔
    Exec world calls types locals expr (fun v h => ∃ result, loadValue h v = .ok result ∧ normal result h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | load value operation => exact .inl ⟨_, _, value, _, operation, post⟩
    · cases ev with | fromLoad ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨result, operation, post⟩
      exact .inl ⟨_, _, .load ev operation, post⟩
    · exact .inr ⟨_, _, _, .fromLoad ev, post⟩

theorem exec_neg : Exec world calls types locals (.neg expr) normal abrupt heap ↔
    Exec world calls types locals expr (fun v h => ∃ result, evalNeg v = .ok result ∧ normal result h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | neg value operation => exact .inl ⟨_, _, value, _, operation, post⟩
    · cases ev with | fromNeg ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨result, operation, post⟩
      exact .inl ⟨_, _, .neg ev operation, post⟩
    · exact .inr ⟨_, _, _, .fromNeg ev, post⟩

theorem exec_hint : Exec world calls types locals (.hint type expr channel) normal abrupt heap ↔
    Exec world calls types locals expr (fun v h => ∃ value : Constant F, world.typed (type.subst types).toCore value = true ∧ normal value.toValue h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | hint value operation => exact .inl ⟨_, _, value, _, operation, post⟩
    · cases ev with | fromHint ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨result, operation, post⟩
      exact .inl ⟨_, _, .hint ev operation, post⟩
    · exact .inr ⟨_, _, _, .fromHint ev, post⟩

theorem exec_tuple : Exec world calls types locals (.tuple exprs) normal abrupt heap ↔
    ExecArgs world calls types locals exprs (fun vs h => normal (.tuple vs) h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | tuple ev => exact .inl ⟨_, _, ev, post⟩
    · cases ev with | fromTuple ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨vs, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .tuple ev, post⟩
    · exact .inr ⟨_, _, _, .fromTuple ev, post⟩

theorem exec_array : Exec world calls types locals (.array exprs) normal abrupt heap ↔
    ExecArgs world calls types locals exprs (fun vs h => normal (.tuple vs) h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | array ev => exact .inl ⟨_, _, ev, post⟩
    · cases ev with | fromArray ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨vs, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .array ev, post⟩
    · exact .inr ⟨_, _, _, .fromArray ev, post⟩

theorem exec_construct : Exec world calls types locals (.construct name typeArgs ctor exprs) normal abrupt heap ↔
    ExecArgs world calls types locals exprs (fun vs h => normal (.construct (instanceName types name typeArgs) ctor vs) h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | construct ev => exact .inl ⟨_, _, ev, post⟩
    · cases ev with | fromConstruct ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨vs, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .construct ev, post⟩
    · exact .inr ⟨_, _, _, .fromConstruct ev, post⟩

theorem exec_constructAs : Exec world calls types locals (.constructAs params type ctor exprs) normal abrupt heap ↔
    ExecArgs world calls types locals exprs (fun vs h => normal (.construct (constructorName types type) ctor vs) h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | constructAs ev => exact .inl ⟨_, _, ev, post⟩
    · cases ev with | fromConstructAs ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨vs, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .constructAs ev, post⟩
    · exact .inr ⟨_, _, _, .fromConstructAs ev, post⟩

theorem exec_builtin : Exec world calls types locals (.builtin paths exprs) normal abrupt heap ↔
    ExecArgs world calls types locals exprs
      (fun values h => ∃ result, paths.apply values = .ok result ∧ normal result h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | builtin args op => exact .inl ⟨_, _, args, _, op, post⟩
    · cases ev with | fromBuiltin args => exact .inr ⟨_, _, _, args, post⟩
  · rintro (⟨vs, h, ev, result, op, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .builtin ev op, post⟩
    · exact .inr ⟨_, _, _, .fromBuiltin ev, post⟩

theorem exec_update : Exec world calls types locals (.update paths exprs) normal abrupt heap ↔
    ExecArgs world calls types locals exprs
      (fun values h => ∃ result, Update.value types paths values = .ok result ∧ normal result h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | update args op => exact .inl ⟨_, _, args, _, op, post⟩
    · cases ev with | fromUpdate args => exact .inr ⟨_, _, _, args, post⟩
  · rintro (⟨vs, h, ev, result, op, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .update ev op, post⟩
    · exact .inr ⟨_, _, _, .fromUpdate ev, post⟩

theorem exec_record : Exec world calls types locals (.record head exprs) normal abrupt heap ↔
    ExecArgs world calls types locals exprs (fun vs h => normal (.construct (constructorName types head.type) structConstructor (head.order vs (.tuple []))) h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | record ev => exact .inl ⟨_, _, ev, post⟩
    · cases ev with | fromRecord ev => exact .inr ⟨_, _, _, ev, post⟩
  · rintro (⟨vs, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .record ev, post⟩
    · exact .inr ⟨_, _, _, .fromRecord ev, post⟩

theorem exec_call : Exec world calls types locals (.call name typeArgs exprs) normal abrupt heap ↔
    ExecArgs world calls types locals exprs
      (fun vs h => ∃ v a, calls (instanceName types name typeArgs) vs h v a ∧ normal v a) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | call args callee => exact .inl ⟨_, _, args, _, _, callee, post⟩
    · cases ev with | fromCall args => exact .inr ⟨_, _, _, args, post⟩
  · rintro (⟨vs, h, ev, v, a, callee, post⟩ | ⟨t, v, h, ev, post⟩)
    · exact .inl ⟨_, _, .call ev callee, post⟩
    · exact .inr ⟨_, _, _, .fromCall ev, post⟩

theorem exec_binary : Exec world calls types locals (.binary op lhs rhs) normal abrupt heap ↔
    Exec world calls types locals lhs (fun x h =>
      Exec world calls types locals rhs (fun y a => ∃ result, evalBinOp op x y = .ok result ∧ normal result a)
        abrupt h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | binary left right operation => exact .inl ⟨_, _, left, .inl ⟨_, _, right, _, operation, post⟩⟩
    · cases ev with
      | binaryLeft ev => exact .inr ⟨_, _, _, ev, post⟩
      | binaryRight left right => exact .inl ⟨_, _, left, .inr ⟨_, _, _, right, post⟩⟩
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨y, a, right, result, operation, post⟩ | ⟨t, v, a, right, post⟩
      · exact .inl ⟨_, _, .binary ev right operation, post⟩
      · exact .inr ⟨_, _, _, .binaryRight ev right, post⟩
    · exact .inr ⟨_, _, _, .binaryLeft ev, post⟩

theorem exec_let : Exec world calls types locals (.letValue pat value body) normal abrupt heap ↔
    Exec world calls types locals value (fun v h => ∃ bindings,
      world.matchPattern types h pat v = .ok (some bindings) ∧
        Exec world calls types (bindings ++ locals) body normal abrupt h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | letValue value matched body => exact .inl ⟨_, _, value, _, matched, .inl ⟨_, _, body, post⟩⟩
    · cases ev with
      | fromLetValue ev => exact .inr ⟨_, _, _, ev, post⟩
      | letBody value matched body => exact .inl ⟨_, _, value, _, matched, .inr ⟨_, _, _, body, post⟩⟩
  · rintro (⟨v, h, ev, bindings, matched, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨v, a, body, post⟩ | ⟨t, v, a, body, post⟩
      · exact .inl ⟨_, _, .letValue ev matched body, post⟩
      · exact .inr ⟨_, _, _, .letBody ev matched body, post⟩
    · exact .inr ⟨_, _, _, .fromLetValue ev, post⟩

theorem exec_match : Exec world calls types locals (.matchValue value arms) normal abrupt heap ↔
    Exec world calls types locals value (fun v h => ∃ bindings body,
      SourceSemantics.selectArm world types h v arms = .ok (some (bindings, body)) ∧
        Exec world calls types (bindings ++ locals) body normal abrupt h) abrupt heap := by
  constructor
  · rintro (⟨v, h, ev, post⟩ | ⟨t, v, h, ev, post⟩)
    · cases ev with | matchValue value selected body => exact .inl ⟨_, _, value, _, _, selected, .inl ⟨_, _, body, post⟩⟩
    · cases ev with
      | fromMatchValue ev => exact .inr ⟨_, _, _, ev, post⟩
      | matchBody value selected body => exact .inl ⟨_, _, value, _, _, selected, .inr ⟨_, _, _, body, post⟩⟩
  · rintro (⟨v, h, ev, bindings, body, selected, post⟩ | ⟨t, v, h, ev, post⟩)
    · rcases post with ⟨v, a, body, post⟩ | ⟨t, v, a, body, post⟩
      · exact .inl ⟨_, _, .matchValue ev selected body, post⟩
      · exact .inr ⟨_, _, _, .matchBody ev selected body, post⟩
    · exact .inr ⟨_, _, _, .fromMatchValue ev, post⟩

end Aiur.Generic.OpenSource
