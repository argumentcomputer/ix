/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Operations

/-!
# Untrusted certificate suggestions

This bounded producer handles dependent functions with syntactic product
heads, conservative universe simplification, and conversion certificates.
Its output is ordinary data.
Only the certified validator can turn a suggestion into acceptance. Failure
to find a certificate is a decline and says nothing about untypability.
-/

namespace Ix.Theory.Certificate

open Model Certified

universe u
variable {β : Type u} [DecidableEq β]

/-- Untrusted search hints. The public builder derives these from the fixed
profile; the semantic validator independently checks every resulting fact. -/
class Hints (β : Type u) where
  natural : Option (ConstRef β)

instance (priority := low) : Hints β := ⟨none⟩

variable [Hints β]

def annotations : AExpr β → AnnotationTree
  | .bvar _ | .sort _ | .const .. | .natLit _ => .leaf
  | .app f a => .app (annotations f) (annotations a)
  | .lam p A b => .lam p.toRaw (annotations A) (annotations b)
  | .forallE p A B => .forallE p.toRaw (annotations A) (annotations B)
  | .proj _ _ e => .proj (annotations e)

structure Suggestion (β : Type u) where
  expression : AExpr β
  type : AExpr β
  witness : TypingWitness β

/-- A limited conversion search. The validator independently rechecks every
level equality and the type of the expected type. -/
def cast? (n : Nat) (suggestion : Suggestion β) (type : AExpr β) : Option (TypingWitness β) :=
  if suggestion.type = type then some suggestion.witness
  else
    match suggestion.type, type with
    | .sort l, .sort l' =>
      if LevelEq.check n l l' then
        some (.conv suggestion.type (.succ l') suggestion.witness .sort .sort)
      else none
    | _, _ => none

def headConstant? : AExpr β → Option (ConstRef β × List VLevel)
  | .const r levels => some (r, levels)
  | .app f _ => headConstant? f
  | _ => none

def applicationArgs : AExpr β → List (AExpr β) → List (AExpr β)
  | .app f a, args => applicationArgs f (a :: args)
  | _, args => args

def lambdaBody : AExpr β → Nat × AExpr β
  | .lam _ _ body => let (n, result) := lambdaBody body; (n + 1, result)
  | e => (0, e)

/-- Collect possible arguments of a closed equation telescope. This search
does not certify matching: the fully instantiated endpoint is compared below
and every application/beta step is subsequently checked by the validator. -/
def matchEquationArgs? : AExpr β → AExpr β → List (Option (AExpr β)) → Option (List (Option (AExpr β)))
  | .bvar i, actual, slots => do
    let slot ← slots[i]?
    match slot with
    | none => some (slots.set i (some actual))
    | some previous => if previous = actual then some slots else none
  | .app f x, .app g y, slots => do
    let slots ← matchEquationArgs? f g slots
    matchEquationArgs? x y slots
  | .const r ls, .const q ms, slots => if r = q ∧ ls = ms then some slots else none
  | .sort l, .sort m, slots => if l = m then some slots else none
  | .proj r i major, .proj q j actual, slots =>
    if r = q ∧ i = j then matchEquationArgs? major actual slots else none
  | .lam .., .lam .., slots | .forallE .., .forallE .., slots => some slots
  | _, _, _ => none

def instantiateLambdas? : AExpr β → List (AExpr β) → Option (AExpr β)
  | e, [] => some e
  | .lam _ _ body, arg :: rest => instantiateLambdas? (body.inst arg) rest
  | _, _ => none

def equationArguments? (pattern actual : AExpr β) : Option (List (AExpr β)) := do
  let (count, body) := lambdaBody pattern
  let slots ← matchEquationArgs? body actual (List.replicate count none)
  let args ← slots.reverse.mapM id
  let instantiated ← instantiateLambdas? pattern args
  if instantiated = actual then some args else none

/-- Suggest the same equation with a different final major proof. The full
application prefix must still match exactly. A subsequent typed conversion
must justify replacing that proof; this matcher alone grants no equation. -/
def equationProofArguments? (pattern actual : AExpr β) : Option (List (AExpr β)) := do
  let (count, body) := lambdaBody pattern
  let .app rulePrefix _ := body | none
  let .app actualPrefix _ := actual | none
  let slots ← matchEquationArgs? rulePrefix actualPrefix (List.replicate count none)
  let args ← slots.reverse.mapM id
  let .app instantiatedPrefix _ ← instantiateLambdas? pattern args | none
  if instantiatedPrefix = actualPrefix then some args else none

mutual
def inferSource? (fuel n : Nat) (entries : Environment β) (Γ : Context β) :
    VExpr β → Option (Suggestion β) :=
  match fuel with
  | 0 => fun _ => none
  | fuel + 1 => fun source =>
    match source with
    | .bvar i => do
      let A ← Γ[i]?
      return ⟨.bvar i, A, .bvar⟩
    | .sort l =>
      if l.WF n then some ⟨.sort l, .sort (.succ l), .sort⟩ else none
    | .const r ls => do
      let entry ← entries r
      if ls.length = entry.universes ∧ ∀ l ∈ ls, l.WF n then
        return ⟨.const r ls, entry.type.instL ls, .const⟩
      else none
    | .forallE A B => do
      let a ← inferSource? fuel n entries Γ A
      let a ← normalizeType? fuel n entries Γ a
      let .sort lA := a.type | none
      let b ← inferSource? fuel n entries (Γ.push a.expression) B
      let b ← normalizeType? fuel n entries (Γ.push a.expression) b
      let .sort lB := b.type | none
      return ⟨.forallE (zeroCondition lB) a.expression b.expression, .sort (.imax lA lB),
        .forallE lA lB a.witness b.witness⟩
    | .lam A body => do
      let a ← inferSource? fuel n entries Γ A
      let a ← normalizeType? fuel n entries Γ a
      let .sort lA := a.type | none
      let b ← inferSource? fuel n entries (Γ.push a.expression) body
      let b ← normalizeType? fuel n entries (Γ.push a.expression) b
      let B ← inferAnnotated? fuel n entries (Γ.push a.expression) b.type
      let B ← normalizeType? fuel n entries (Γ.push a.expression) B
      let .sort lB := B.type | none
      return ⟨.lam (zeroCondition lB) a.expression b.expression,
        .forallE (zeroCondition lB) a.expression b.type,
        .lam lA lB b.type a.witness B.witness b.witness⟩
    | .app f arg => do
      let fn ← inferSource? fuel n entries Γ f
      let fn ← normalizeType? fuel n entries Γ fn
      let .forallE p A B := fn.type | none
      let a ← inferSource? fuel n entries Γ arg
      let aw ← castWith? fuel n entries Γ a A
      return ⟨.app fn.expression a.expression, B.inst a.expression,
        .app p A B fn.witness aw⟩
    | .proj ref index major => do
      let major ← inferSource? fuel n entries Γ major
      let typed ← normalizeType? fuel n entries Γ major
      let (owner, ls) ← headConstant? typed.type
      if owner != ref then none else do
        let entry ← entries ref
        if ls.length != entry.universes then none else
          entry.facts.zipIdx.findSome? fun (fact, factIndex) => do
            let .typed expression type := fact | none
            let (_, .proj family field _) := lambdaBody expression | none
            if family != ref || field != index then none else do
              let result ← applyFact? fuel n entries Γ
                ⟨expression.instL ls, type.instL ls, .fact ref factIndex ls⟩
                (applicationArgs typed.type [] ++ [major.expression])
              if result.expression = .proj ref index major.expression then some result else none
    | .natLit value => do
      let ref ← Hints.natural (β := β)
      let entry ← entries ref
      if entry.universes != 0 then none else
        entry.facts.zipIdx.findSome? fun (fact, i) => match fact with
          | .natural _ _ => some ⟨.natLit value, .const ref [], .natLit ref i⟩
          | _ => none

/-- Instantiate an admitted closed typing fact using checked beta results.
The result retains the actual source projection rather than a replacement
term with a merely convertible type. -/
def applyFact? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (fact : Suggestion β) (args : List (AExpr β)) : Option (Suggestion β) :=
  match fuel with
  | 0 => none
  | fuel + 1 => match args with
    | [] => some fact
    | arg :: rest => do
      let .lam p D body := fact.expression | none
      let .forallE q A B := fact.type | none
      if p != q || D != A then none else do
        let a ← inferAnnotated? fuel n entries Γ arg
        let aw ← castWith? fuel n entries Γ a D
        applyFact? fuel n entries Γ ⟨body.inst arg, B.inst arg,
          .betaResult p D body arg B fact.witness aw⟩ rest

def inferAnnotated? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (e : AExpr β) : Option (Suggestion β) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let result ← inferSource? fuel n entries Γ e.erase
    if result.expression = e then some result else none

/-- Build a conversion certificate rather than normalizing away source
syntax. The semantic validator checks the target's sort independently. -/
def castWith? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (suggestion : Suggestion β) (type : AExpr β) : Option (TypingWitness β) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match cast? n suggestion type with
    | some witness => some witness
    | none => do
      let target ← inferAnnotated? fuel n entries Γ type
      let target ← normalizeType? fuel n entries Γ target
      let .sort l := target.type | none
      let witness ← conversion? fuel n entries Γ suggestion.type type
      return .conv suggestion.type l suggestion.witness target.witness witness

def beta? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (e : AExpr β) : Option (AExpr β × ConversionWitness β) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let .app (.lam p D body) arg := e | none
    let fn ← inferAnnotated? fuel n entries Γ (.lam p D body)
    let a ← inferAnnotated? fuel n entries Γ arg
    let aw ← castWith? fuel n entries Γ a D
    return (body.inst arg, .beta fn.type fn.witness aw)

def eta? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (a b : AExpr β) : Option (ConversionWitness β) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let .lam p D body := a | none
    let fn ← inferAnnotated? fuel n entries Γ b
    let fn ← normalizeType? fuel n entries Γ fn
    let .forallE q D' B := fn.type | none
    if p = q ∧ D = D' ∧ body = .app (b.liftN 1) (.bvar 0) then
      return .eta B fn.witness
    else none

/-- A checked beta/delta step may occur in the function of an application. -/
def headStep? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (e : AExpr β) : Option (AExpr β × ConversionWitness β) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let delta := fun (_ : Unit) => do
      let .const r ls := e | none
      let entry ← entries r
      if ls.length != entry.universes then none else do
        let body ← entry.body
        return (body.instL ls, .delta)
    let app := fun (_ : Unit) => do
      let .app f x := e | none
      let (f', w) ← headStep? fuel n entries Γ f <|> equationStep? fuel n entries Γ f
      return (.app f' x, .app w .refl)
    let argument := fun (_ : Unit) => do
      let .app f x := e | none
      let (x', w) ← headStep? fuel n entries Γ x <|> equationStep? fuel n entries Γ x
      return (.app f x', .app .refl w)
    let projection := fun (_ : Unit) => do
      let .proj r i x := e | none
      let (x', w) ← headStep? fuel n entries Γ x <|> equationStep? fuel n entries Γ x
      return (.proj r i x', .proj w)
    let literal := fun (_ : Unit) => do
      let .natLit value := e | none
      let ref ← Hints.natural (β := β)
      let entry ← entries ref
      if entry.universes != 0 then none else
        entry.facts.zipIdx.findSome? fun (fact, i) => match fact with
          | .natural zero succ => some
            ((match value with | 0 => .const zero [] | n + 1 => .app (.const succ []) (.natLit n)), .natLiteral ref i)
          | _ => none
    beta? fuel n entries Γ e <|> delta () <|> app () <|> argument () <|> projection () <|> literal ()

def equationStep? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (e : AExpr β) : Option (AExpr β × ConversionWitness β) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (ref, levels) : ConstRef β × List VLevel ← match e with
      | .proj ref _ major => do
        let typed ← inferAnnotated? fuel n entries Γ major
        let typed ← normalizeType? fuel n entries Γ typed
        let (owner, levels) ← headConstant? typed.type
        if owner = ref then some (ref, levels) else none
      | _ => do
        let (ref, levels) ← headConstant? e
        let owner : ConstRef β := match ref with | .ctor source member _ => .member source member | _ => ref
        some (owner, levels)
    let entry ← entries ref
    if levels.length != entry.universes then none else
      entry.equations.zipIdx.findSome? fun (law, i) => do
        let lhs := law.lhs.instL levels
        let rhs := law.rhs.instL levels
        let args ← equationArguments? lhs e <|> (do
          let (_, .app _ constructor) := lambdaBody lhs | none
          let (.ctor .., _) ← headConstant? constructor | none
          let .app fn major := e | none
          let expanded ← etaMajor? fuel n entries Γ major
          equationArguments? lhs (.app fn expanded)) <|> (do
          let .app _ major := e | none
          let typed ← inferAnnotated? fuel n entries Γ major
          let type ← inferAnnotated? fuel n entries Γ typed.type
          let _ ← cast? n type (.sort .zero)
          equationProofArguments? lhs e)
        let lhsApplied := args.foldl AExpr.app lhs
        let rhsApplied := args.foldl AExpr.app rhs
        let beta ← conversion? fuel n entries Γ lhsApplied e
        let equation := args.foldl (fun w _ => ConversionWitness.app w .refl) (.equation ref i levels)
        return (rhsApplied, .trans lhsApplied (.symm beta) equation)

/-- A stuck eliminator may use an existing structure's checked eta equation
to expose its constructor. This only suggests arguments: `equationStep?`
still constructs and checks conversion of the complete original application
to the chosen rule's complete instantiated left side. Model companions with
no eta equation cannot acquire this behavior from the search. -/
def etaMajor? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (major : AExpr β) : Option (AExpr β) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let typed ← inferAnnotated? fuel n entries Γ major
    let typed ← normalizeType? fuel n entries Γ typed
    let (family, levels) ← headConstant? typed.type
    let entry ← entries family
    if levels.length != entry.universes then none else
      entry.equations.findSome? fun law => do
        let arguments := applicationArgs typed.type [] ++ [major]
        let rhs ← instantiateLambdas? (law.rhs.instL levels) arguments
        if rhs != major then none else do
          let lhs ← instantiateLambdas? (law.lhs.instL levels) arguments
          if lhs = major then none else some lhs

/-- Reduction of an inferred type is accompanied by a conversion witness
and a fresh formation witness for the resulting type. -/
def normalizeType? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (suggestion : Suggestion β) : Option (Suggestion β) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match suggestion.type with
    | .sort _ | .forallE .. => some suggestion
    | _ =>
      match headStep? fuel n entries Γ suggestion.type <|> equationStep? fuel n entries Γ suggestion.type with
      | none => some suggestion
      | some (type, conversion) => do
        let formed ← inferAnnotated? fuel n entries Γ type
        let formed ← normalizeType? fuel n entries Γ formed
        let .sort level := formed.type | none
        normalizeType? fuel n entries Γ
          ⟨suggestion.expression, type, .conv suggestion.type level suggestion.witness formed.witness conversion⟩

def conversion? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (a b : AExpr β) : Option (ConversionWitness β) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if a = b then some .refl
    else
      -- Once a checked reduction is available, follow it without exploring
      -- alternate reduction orders again after fuel exhaustion.
      match headStep? fuel n entries Γ a with
      | some (a', w) => do return .trans a' w (← conversion? fuel n entries Γ a' b)
      | none => match headStep? fuel n entries Γ b with
      | some (b', w) => do return .trans b' (← conversion? fuel n entries Γ a b') (.symm w)
      | none =>
      let congruence := fun (_ : Unit) =>
        match a, b with
        | .sort l, .sort l' => if LevelEq.check n l l' then some .sort else none
        | .app f x, .app g y => do
          return .app (← conversion? fuel n entries Γ f g) (← conversion? fuel n entries Γ x y)
        | .proj r i x, .proj q j y =>
          if r = q ∧ i = j then (.proj ·) <$> conversion? fuel n entries Γ x y else none
        | .lam p D body, .lam q D' body' => do
          if p != q then none else do
            let domain ← inferAnnotated? fuel n entries Γ D
            let .sort l := domain.type | none
            return .lam l domain.witness (← conversion? fuel n entries Γ D D')
              (← conversion? fuel n entries (Γ.push D) body body')
        | .forallE p D B, .forallE q D' B' => do
          if p != q then none else do
            let domain ← inferAnnotated? fuel n entries Γ D
            let .sort l := domain.type | none
            return .forallE l domain.witness (← conversion? fuel n entries Γ D D')
              (← conversion? fuel n entries (Γ.push D) B B')
        | _, _ => none
      let proofIrrel := fun (_ : Unit) => do
        let left ← inferAnnotated? fuel n entries Γ a
        let type ← inferAnnotated? fuel n entries Γ left.type
        let typeWitness ← cast? n type (.sort .zero)
        let right ← inferAnnotated? fuel n entries Γ b
        let rightWitness ← castWith? fuel n entries Γ right left.type
        return .proofIrrel left.type typeWitness left.witness rightWitness
      eta? fuel n entries Γ a b <|>
        ((.symm ·) <$> eta? fuel n entries Γ b a) <|> congruence () <|>
        (match equationStep? fuel n entries Γ a with
        | some (a', w) => do return .trans a' w (← conversion? fuel n entries Γ a' b)
        | none => match equationStep? fuel n entries Γ b with
        | some (b', w) => do return .trans b' (← conversion? fuel n entries Γ a b') (.symm w)
        | none => proofIrrel ())
end

def inferenceWitness? (fuel n : Nat) (entries : Environment β) (Γ : Context β)
    (source : VExpr β) : Option (InferenceWitness β) := do
  let suggestion ← inferSource? fuel n entries Γ source
  return ⟨annotations suggestion.expression, suggestion.type, suggestion.witness⟩

end Ix.Theory.Certificate
