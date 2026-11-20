import IxAICore

/-!
# Normal-form literals

An Ix `Eval` claim says that an input definition normalizes to an output definition, compared
structurally without reducing the output. The output must therefore be written exactly as the
kernel's normal form: constructor applications with explicit type arguments, raw `Nat` literals,
and `Int` values as `Int.ofNat`/`Int.negSucc` of literals. `NormalForm` renders values that way.
-/

namespace IxAI

open IxAICore

class NormalForm (α : Type) where
  /-- The Lean type, as source. -/
  typeName : String
  /-- The value in kernel normal form, as source. -/
  render : α → String

instance : NormalForm Nat := ⟨"Nat", fun n => s!"(nat_lit {n})"⟩

instance : NormalForm Int :=
  ⟨"Int", fun i => match i with
    | .ofNat n => s!"(Int.ofNat (nat_lit {n}))"
    | .negSucc n => s!"(Int.negSucc (nat_lit {n}))"⟩

instance : NormalForm Bool := ⟨"Bool", fun b => if b then "Bool.true" else "Bool.false"⟩

instance : NormalForm String := ⟨"String", fun s => s!"{repr s}"⟩

instance {α : Type} [NormalForm α] : NormalForm (List α) :=
  ⟨s!"(List {NormalForm.typeName α})", fun xs =>
    let t := NormalForm.typeName α
    xs.foldr (fun x acc => s!"(@List.cons {t} {NormalForm.render x} {acc})") s!"(@List.nil {t})"⟩

instance : NormalForm Fx := ⟨"IxAICore.Fx", fun x => s!"(IxAICore.Fx.mk {NormalForm.render x.raw})"⟩

instance : NormalForm Model :=
  ⟨"IxAICore.Model", fun m =>
    s!"(IxAICore.Model.mk {NormalForm.render m.w1} {NormalForm.render m.b1} " ++
      s!"{NormalForm.render m.w2} {NormalForm.render m.b2})"⟩

instance : NormalForm QuestionCard :=
  ⟨"IxAICore.QuestionCard", fun q =>
    s!"(IxAICore.QuestionCard.mk {NormalForm.render q.name} {NormalForm.render q.correct} " ++
      s!"{NormalForm.render q.total} {NormalForm.render q.brierRaw} {NormalForm.render q.calibrationRaw})"⟩

instance : NormalForm Card :=
  ⟨"IxAICore.Card", fun c => s!"(IxAICore.Card.mk {NormalForm.render c.questions})"⟩

instance : NormalForm Triage.Action :=
  ⟨"IxAICore.Triage.Action", fun
    | .publish => "IxAICore.Triage.Action.publish"
    | .refuted => "IxAICore.Triage.Action.refuted"
    | .defer => "IxAICore.Triage.Action.defer"⟩

def formulaSource : Formula → String
  | .atom n => s!"(IxAICore.Formula.atom {n})"
  | .top => "IxAICore.Formula.top"
  | .imp a b => s!"(IxAICore.Formula.imp {formulaSource a} {formulaSource b})"
  | .and a b => s!"(IxAICore.Formula.and {formulaSource a} {formulaSource b})"

def configSource (c : Config) : String :=
  s!"\{ seed := {c.seed}, hidden := {c.hidden}, lrRaw := {c.lrRaw}, epochs := {c.epochs}, " ++
    s!"batch := {c.batch}, trainSize := {c.trainSize}, testSize := {c.testSize} }"

instance {α β : Type} [NormalForm α] [NormalForm β] : NormalForm (α × β) :=
  ⟨s!"({NormalForm.typeName α} × {NormalForm.typeName β})", fun (a, b) =>
    s!"(@Prod.mk {NormalForm.typeName α} {NormalForm.typeName β} {NormalForm.render a} {NormalForm.render b})"⟩

/-- `def name : T := value` in normal form. -/
def literalDef {α : Type} [NormalForm α] (name : String) (x : α) : String :=
  s!"def {name} : {NormalForm.typeName α} :=\n  {NormalForm.render x}\n"

end IxAI
