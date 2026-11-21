import Aiur.WireMemory
import Aiur.Memory.Representation
import Aiur.Semantics.WithCalls

namespace Aiur

/-- Pointers have finite provenance through cells whose contents have the same
property. The rest of the ROM may contain malformed or unreachable cells. -/
inductive ROM.Provenance (rom : ROM F) : Value F → Prop where
  | field : rom.Provenance (.field value)
  | tuple (items : ∀ value ∈ values, rom.Provenance value) :
      rom.Provenance (.tuple values)
  | construct (items : ∀ value ∈ values, rom.Provenance value) :
      rom.Provenance (.construct name ctor values)
  | ptr (cell : (address, stored) ∈ rom.entries) (contents : rom.Provenance stored) :
      rom.Provenance (.ptr stored.type address)

/-- A raw ROM cannot assign two encodings to one typed address. -/
theorem WireROM.functional {rom : WireROM F} (valid : rom.Valid)
    {address : F} {left right : WireValue F}
    (first : (address, left) ∈ rom.entries) (second : (address, right) ∈ rom.entries)
    (typed : left.type = right.type) : left = right :=
  valid _ first _ second rfl typed

variable {F : Type} {rom : ROM F}

theorem ROM.Provenance.of_pointerFree (value : Value F)
    (free : value.pointerFree = true) : rom.Provenance value := by
  cases value with
  | field => exact .field
  | ptr => simp [Value.pointerFree] at free
  | tuple values | construct name ctor values =>
      have items : ∀ value ∈ values, value.pointerFree = true := by
        simpa [Value.pointerFree] using free
      first | apply ROM.Provenance.tuple | apply ROM.Provenance.construct
      exact fun value member => .of_pointerFree value (items value member)
termination_by sizeOf value

@[simp] theorem ROM.Provenance.tuple_iff {values : List (Value F)} :
    rom.Provenance (.tuple values) ↔ ∀ value ∈ values, rom.Provenance value := by
  constructor
  · intro trusted; cases trusted; assumption
  · exact .tuple

@[simp] theorem ROM.Provenance.construct_iff {name ctor : String} {values : List (Value F)} :
    rom.Provenance (.construct name ctor values) ↔ ∀ value ∈ values, rom.Provenance value := by
  constructor
  · intro trusted; cases trusted; assumption
  · exact .construct

theorem ROM.Provenance.load {target : Ty} {address : F} {value : Value F}
    (trusted : rom.Provenance (.ptr target address)) (valid : rom.Valid)
    (cell : (address, value) ∈ rom.entries) (typed : value.type = target) : rom.Provenance value := by
  cases trusted with
  | ptr stored contents =>
      have same := ROM.functional valid stored cell typed.symm
      simpa only [same] using contents

/-- Once an address has store provenance, a raw load's existing ROM lookup
already guarantees that its payload decodes. No independent enum validation is
required at the load. -/
theorem WireROM.load_of_provenance [NatCast F] [Zero F] [DecidableEq F]
    {decls : Declarations} {wireRom : WireROM F} (valid : wireRom.Valid)
    {target : Ty} {address : F} {wire : WireValue F}
    (trusted : (wireRom.decode decls).Provenance (.ptr target address))
    (cell : (address, wire) ∈ wireRom.entries) (typed : wire.type = target) :
    ∃ value, wire.decode decls = some value ∧ value.type = target ∧
      (wireRom.decode decls).Provenance value := by
  cases trusted with
  | ptr storedCell contents =>
      obtain ⟨encoded, original, decoded⟩ := WireROM.mem_decode.mp storedCell
      have same := WireROM.functional valid original cell ((WireValue.decode_spec decoded).1.symm.trans typed.symm)
      exact ⟨_, same ▸ decoded, rfl, contents⟩

/-- Provenance is required only for the values available to the expression. -/
def Environment.Provenance (rom : ROM F) (locals : Environment F) : Prop :=
  ∀ binding ∈ locals, rom.Provenance binding.2

@[simp] theorem Environment.provenance_append {left right : Environment F} :
    (left ++ right).Provenance rom ↔ left.Provenance rom ∧ right.Provenance rom := by
  simp [Provenance, or_imp, forall_and]

theorem Environment.Provenance.lookup {locals : Environment F} {name : String} {value : Value F}
    (trusted : locals.Provenance rom)
    (found : locals.find? (·.1 == name) = some (name, value)) : rom.Provenance value :=
  trusted _ (List.mem_of_find?_eq_some found)

theorem ROM.Provenance.project {input result : Value F} {index : Nat}
    (trusted : rom.Provenance input) (projected : projectValue input index = .ok result) :
    rom.Provenance result := by
  cases trusted with
  | field | ptr | construct => cases projected
  | tuple items =>
      simp only [projectValue] at projected
      split at projected
      · cases projected
        exact items _ (List.mem_of_getElem? ‹_›)
      · cases projected

mutual
  theorem Pattern.bindings_provenance [DecidableEq F]
      {pattern : Pattern F} {value : Value F} {locals : Environment F}
      (trusted : rom.Provenance value) (matched : pattern.bindings value = some locals) :
      locals.Provenance rom := by
    cases pattern with
    | wildcard =>
        simp only [Pattern.bindings, Option.some.injEq] at matched
        subst locals
        simp [Environment.Provenance]
    | bind name =>
        simp only [Pattern.bindings, Option.some.injEq] at matched
        subst locals
        simpa [Environment.Provenance] using trusted
    | literal literal =>
        cases value with
        | tuple | ptr | construct => simp [Pattern.bindings] at matched
        | field x =>
            simp only [Pattern.bindings] at matched
            split at matched
            · cases matched; simp [Environment.Provenance]
            · cases matched
    | tuple patterns =>
        cases value with
        | field | ptr | construct => simp [Pattern.bindings] at matched
        | tuple values =>
            simp only [Pattern.bindings] at matched
            exact Pattern.bindingsList_provenance (ROM.Provenance.tuple_iff.mp trusted) matched
    | construct name ctor patterns =>
        cases value with
        | field | tuple | ptr => simp [Pattern.bindings] at matched
        | construct actual constructor values =>
            simp only [Pattern.bindings] at matched
            split at matched
            · exact Pattern.bindingsList_provenance (ROM.Provenance.construct_iff.mp trusted) matched
            · cases matched
  termination_by sizeOf pattern

  theorem Pattern.bindingsList_provenance [DecidableEq F]
      {patterns : List (Pattern F)} {values : List (Value F)} {locals : Environment F}
      (trusted : ∀ value ∈ values, rom.Provenance value)
      (matched : Pattern.bindingsList patterns values = some locals) : locals.Provenance rom := by
    cases patterns with
    | nil => cases values <;> simp_all [Pattern.bindingsList, Environment.Provenance]
    | cons pattern patterns =>
        cases values with
        | nil => simp [Pattern.bindingsList] at matched
        | cons value values =>
            simp only [Pattern.bindingsList] at matched
            obtain ⟨head, headRun, rest⟩ := Option.bind_eq_some_iff.mp matched
            obtain ⟨tail, tailRun, finished⟩ := Option.bind_eq_some_iff.mp rest
            simp only [Option.pure_def, Option.some.injEq] at finished
            subst locals
            exact Environment.provenance_append.mpr
              ⟨Pattern.bindings_provenance (trusted _ (by simp)) headRun,
                Pattern.bindingsList_provenance (fun v h => trusted v (by simp [h])) tailRun⟩
  termination_by sizeOf patterns
end

theorem selectArm_provenance [DecidableEq F]
    {value : Value F} {arms : List (Pattern F × Expr F)} {locals : Environment F} {body : Expr F}
    (trusted : rom.Provenance value) (selected : selectArm value arms = some (locals, body)) :
    locals.Provenance rom := by
  induction arms with
  | nil => simp [selectArm] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pattern, branch⟩
      cases matched : pattern.bindings value with
      | none => exact ih (by simpa [selectArm, matched] using selected)
      | some bindings =>
          simp [selectArm, matched] at selected
          rcases selected with ⟨rfl, rfl⟩
          exact Pattern.bindings_provenance trusted matched

theorem ROM.Provenance.neg [Field F] {input result : Value F}
    (operation : evalNeg input = .ok result) : rom.Provenance result := by
  cases input with
  | field => cases operation; exact .field
  | tuple | construct | ptr => cases operation

theorem ROM.Provenance.binary [Field F] [DecidableEq F]
    {left right result : Value F} {op : BinOp}
    (operation : evalBinOp op left right = .ok result) : rom.Provenance result := by
  cases left with
  | tuple | construct | ptr => cases operation
  | field =>
      cases right with
      | tuple | construct | ptr => cases operation
      | field =>
          cases op with
          | add | sub | mul => cases operation; exact .field
          | div =>
              simp only [evalBinOp] at operation
              split at operation
              · cases operation
              · cases operation; exact .field

theorem ROM.Provenance.assertEq [DecidableEq F]
    {left right result : Value F} {message : Assertion}
    (operation : evalAssertEq message left right = .ok result) : rom.Provenance result := by
  obtain ⟨_, _, rfl⟩ := evalAssertEq_ok.mp operation
  exact .tuple (by simp)

/-- Evaluation propagates pointer provenance. Calls need only preserve it when
their arguments have provenance; the theorem imposes no condition on unrelated
rows or calls with fabricated pointer arguments. -/
theorem ROMEvalExprWith.provenance [Field F] [DecidableEq F]
    {decls : Declarations} {calls : CallRelation F}
    {locals : Environment F} {expr : Expr F} {result : Value F}
    (evaluated : ROMEvalExprWith decls rom calls locals expr result)
    (valid : rom.Valid)
    (callProvenance : ∀ name args result, calls name args result →
      (∀ value ∈ args, rom.Provenance value) → rom.Provenance result)
    (trusted : locals.Provenance rom) : rom.Provenance result := by
  revert trusted
  induction evaluated using ROMEvalExprWith.rec
    (motive_2 := fun locals _ values _ =>
      locals.Provenance rom → ∀ value ∈ values, rom.Provenance value) with
  | literal => intro _; exact .field
  | var found => intro env; exact env.lookup found
  | tuple _ ih => intro env; exact .tuple (ih env)
  | construct _ ih => intro env; exact .construct (ih env)
  | project _ projected ih => intro env; exact (ih env).project projected
  | letValue _ matched _ valueIH bodyIH =>
      intro env
      exact bodyIH (Environment.provenance_append.mpr
        ⟨Pattern.bindings_provenance (valueIH env) matched, env⟩)
  | store _ cell ih => intro env; exact .ptr cell (ih env)
  | load _ cell typed ih => intro env; exact (ih env).load valid cell typed
  | @hint locals expr input type channel _ constant typed ih =>
      intro _
      exact .of_pointerFree _ (Constant.toValue_pointerFree constant)
  | neg _ operation _ => intro _; exact .neg operation
  | assertEq _ _ operation _ _ => intro _; exact .assertEq operation
  | binary _ _ operation _ _ => intro _; exact .binary operation
  | call _ callee ih => intro env; exact callProvenance _ _ _ callee (ih env)
  | matchValue _ selected _ valueIH bodyIH =>
      intro env
      exact bodyIH (Environment.provenance_append.mpr
        ⟨selectArm_provenance (valueIH env) selected, env⟩)
  | nil => simp_all
  | cons _ _ headIH tailIH =>
      rename_i env value member
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH env
      · exact tailIH env value member

theorem ROMEvalArgsWith.provenance [Field F] [DecidableEq F]
    {decls : Declarations} {calls : CallRelation F}
    {locals : Environment F} {exprs : List (Expr F)} {values : List (Value F)}
    (evaluated : ROMEvalArgsWith decls rom calls locals exprs values)
    (valid : rom.Valid)
    (callProvenance : ∀ name args result, calls name args result →
      (∀ value ∈ args, rom.Provenance value) → rom.Provenance result)
    (trusted : locals.Provenance rom) : ∀ value ∈ values, rom.Provenance value :=
  ROM.Provenance.tuple_iff.mp
    ((ROMEvalExprWith.tuple evaluated).provenance valid callProvenance trusted)

theorem prepareCall_provenance [DecidableEq F]
    {program : Program F} {name : String} {args : List (Value F)}
    {locals : Environment F} {expr : Expr F}
    (prepared : prepareCall program name args = .ok (locals, expr))
    (trusted : ∀ value ∈ args, rom.Provenance value) : locals.Provenance rom := by
  rcases prepareCall_spec prepared with function | table
  · obtain ⟨fn, _, _, _, rfl, _⟩ := function
    exact fun binding member => trusted binding.2 (List.of_mem_zip member).2
  · obtain ⟨constant, _, _, rfl, _⟩ := table
    simp [Environment.Provenance]

/-- Actual function evaluation also preserves provenance, including through
mutual recursion. Finiteness comes from its derivation, not a totality premise. -/
theorem ROMEvalExpr.provenance [Field F] [DecidableEq F]
    {program : Program F} {locals : Environment F} {expr : Expr F} {result : Value F}
    (evaluated : ROMEvalExpr rom program locals expr result)
    (valid : rom.Valid) (trusted : locals.Provenance rom) : rom.Provenance result := by
  revert trusted
  induction evaluated using ROMEvalExpr.rec
    (motive_2 := fun locals _ values _ =>
      locals.Provenance rom → ∀ value ∈ values, rom.Provenance value)
    (motive_3 := fun _ args result _ =>
      (∀ value ∈ args, rom.Provenance value) → rom.Provenance result) with
  | literal => intro _; exact .field
  | var found => intro env; exact env.lookup found
  | tuple _ ih => intro env; exact .tuple (ih env)
  | construct _ ih => intro env; exact .construct (ih env)
  | project _ projected ih => intro env; exact (ih env).project projected
  | letValue _ matched _ valueIH bodyIH =>
      intro env
      exact bodyIH (Environment.provenance_append.mpr
        ⟨Pattern.bindings_provenance (valueIH env) matched, env⟩)
  | store _ cell ih => intro env; exact .ptr cell (ih env)
  | load _ cell typed ih => intro env; exact (ih env).load valid cell typed
  | @hint locals expr input type channel _ constant typed ih =>
      intro _
      exact .of_pointerFree _ (Constant.toValue_pointerFree constant)
  | neg _ operation _ => intro _; exact .neg operation
  | assertEq _ _ operation _ _ => intro _; exact .assertEq operation
  | binary _ _ operation _ _ => intro _; exact .binary operation
  | call _ _ argsIH calleeIH => intro env; exact calleeIH (argsIH env)
  | matchValue _ selected _ valueIH bodyIH =>
      intro env
      exact bodyIH (Environment.provenance_append.mpr
        ⟨selectArm_provenance (valueIH env) selected, env⟩)
  | nil => simp_all
  | cons _ _ headIH tailIH =>
      rename_i env value member
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH env
      · exact tailIH env value member
  | intro prepared _ bodyIH =>
      rename_i argsTrusted
      exact bodyIH (prepareCall_provenance prepared argsTrusted)

theorem ROMEvalCall.provenance [Field F] [DecidableEq F]
    {program : Program F} {name : String} {args : List (Value F)} {result : Value F}
    (evaluated : ROMEvalCall rom program name args result)
    (valid : rom.Valid) (trusted : ∀ value ∈ args, rom.Provenance value) :
    rom.Provenance result := by
  cases evaluated with
  | intro prepared body =>
      exact body.provenance valid (prepareCall_provenance prepared trusted)

end Aiur
