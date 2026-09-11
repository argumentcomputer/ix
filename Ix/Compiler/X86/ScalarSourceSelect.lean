import Ix.Compiler.X86.ScalarSourceSim

namespace Ix.Compiler.X86.Scalar.Source
open Ix.Compiler.Ixon (Address)

def findDeclaration (declarations : List (Address × IxIR0.Decl)) (wanted : IxIR0.Decl) : Option Address :=
  (declarations.find? (fun pair => pair.2 == wanted)).map (·.1)

/-- Primitive names are discovered from complete evaluator bodies. A name,
hash, or extern declaration alone never enables native arithmetic. -/
def discover (declarations : List (Address × IxIR0.Decl)) : Option Primitives := do
  let ctx : IxIR0.Ctx := { env := IxIR0.Env.ofList declarations }
  for (alias, declaration) in declarations do
    if let .defn .shared (.ref recursor) := declaration then
      for (successor, declaration) in declarations do
        if declaration == .ctor 1 1 then
          let arithmetic : NatSchema := { successor, recursor, alias }
          if IxIR0.NatArithmetic.Matches ctx arithmetic then
            if let some addition := findDeclaration declarations (.defn .shared (IxIR0.NatArithmetic.body arithmetic)) then
              if let some predecessor := findDeclaration declarations (.defn .shared (IxIR0.NatArithmetic.predBody arithmetic)) then
                if let some subtraction := findDeclaration declarations (.defn .shared (IxIR0.NatArithmetic.subBody arithmetic predecessor)) then
                  if let some caseRecursor := findDeclaration declarations (.recursor 2 true IxIR0.NatArithmetic.caseRules) then
                    if let some caseAlias := findDeclaration declarations (.defn .shared (.ref caseRecursor)) then
                      let primitives : Primitives := { arithmetic, addition, predecessor, subtraction, caseRecursor, caseAlias }
                      if primitives.Matches ctx then return primitives
  none

def lowerAtom (bindings : Array Binding) : IxIR0.Expr → Except String Atom
  | .var index =>
      match bindings.findIdx? (· == .var index) with
      | some localIndex => .ok (.var localIndex)
      | none => .error "scalar source variable is outside the admitted bindings"
  | .lit (.nat number) | .app (.lam .many (.lit (.nat number))) .erased =>
      match ExactNat.encode number with
      | some word => .ok (.constant word)
      | none => .error "scalar source literal does not fit an exact 64-bit Nat"
  | _ => .error "scalar source operand must be a bound Nat or a Nat literal"

def functionParts : IxIR0.Expr → Except String (Nat × IxIR0.Expr)
  | .lam .many (.lam .many body) =>
      match body with
      | .lam _ _ => .error "scalar source function has more than two parameters"
      | _ => .ok (2, body)
  | .lam .many body =>
      match body with
      | .lam _ _ => .error "scalar source parameter uses are unsupported"
      | _ => .ok (1, body)
  | .lam _ _ => .error "scalar source parameter uses are unsupported"
  | body => .ok (0, body)

abbrev Functions := Array (Address × Function)

mutual
  def lowerFunction (ctx : IxIR0.Ctx) (primitives : Primitives) :
      Nat → Functions → Address → Except String (Functions × Nat)
    | 0, _, _ => .error "scalar source call graph exceeds the depth limit or is recursive"
    | fuel + 1, functions, address => do
        if let some index := functions.findIdx? (·.1 == address) then return (functions, index)
        let some (.defn .shared body) := ctx.env address | throw "scalar source callee must be a shared definition"
        let (parameters, body) ← functionParts body
        let (functions, body) ← lowerExpression ctx primitives fuel functions (Source.parameters parameters) body
        if functions.size >= maxFunctions then throw "scalar source has too many functions"
        return (functions.push (address, { parameters, body }), functions.size)

  def lowerExpression (ctx : IxIR0.Ctx) (primitives : Primitives) :
      Nat → Functions → Array Binding → IxIR0.Expr → Except String (Functions × Expr)
    | 0, _, _, _ => .error "scalar source expression exceeds the depth limit"
    | fuel + 1, functions, bindings, expr => do
        match expr with
        | .letE .many value body =>
            let (functions, value) ← lowerExpression ctx primitives fuel functions bindings value
            let (functions, body) ← lowerExpression ctx primitives fuel functions (push bindings) body
            return (functions, .letE value body)
        | .app (.app (.app (.ref address) (.lam .many zero)) (.lam .many successor)) scrutinee =>
            if address != primitives.caseAlias then throw "scalar source branch must use the checked Nat case recursor"
            let scrutinee ← lowerAtom bindings scrutinee
            let (functions, zero) ← lowerExpression ctx primitives fuel functions (lift bindings) zero
            let (functions, successor) ← lowerExpression ctx primitives fuel functions (lift bindings) successor
            return (functions, .branch scrutinee zero successor)
        | .app (.app (.ref address) left) right =>
            let left ← lowerAtom bindings left
            let right ← lowerAtom bindings right
            if address == primitives.addition then return (functions, .add left right)
            if address == primitives.subtraction then return (functions, .sub left right)
            let (functions, callee) ← lowerFunction ctx primitives fuel functions address
            return (functions, .call callee #[left, right])
        | .app (.ref address) argument =>
            let argument ← lowerAtom bindings argument
            let (functions, callee) ← lowerFunction ctx primitives fuel functions address
            return (functions, .call callee #[argument])
        | .ref address =>
            let (functions, callee) ← lowerFunction ctx primitives fuel functions address
            return (functions, .call callee #[])
        | _ => return (functions, .atom (← lowerAtom bindings expr))
end

def programMatches (ctx : IxIR0.Ctx) (primitives : Primitives) (entries : Array Address) (program : Program) : Bool :=
  entries.size == program.functions.size &&
    (entries.zip program.functions).all (fun (address, function) =>
      ctx.env address == some (.defn .shared (functionBody primitives entries function)))

theorem programMatches_sound {ctx : IxIR0.Ctx} {primitives : Primitives} {entries : Array Address} {program : Program}
    (primitiveMatches : primitives.Matches ctx) (accepted : programMatches ctx primitives entries program = true) :
    ProgramMatches ctx primitives entries program := by
  simp only [programMatches, Bool.and_eq_true, beq_iff_eq] at accepted
  refine ⟨primitiveMatches, accepted.1, ?_⟩
  intro index function found
  obtain ⟨bound, equal⟩ := Array.getElem?_eq_some_iff.mp found
  have entryBound : index < entries.size := by rw [accepted.1]; exact bound
  have selected := Array.all_eq_true.mp accepted.2 index (by simp [Array.size_zip, accepted.1, bound])
  simp only [Array.getElem_zip, equal, beq_iff_eq] at selected
  exact ⟨entries[index], Array.getElem?_eq_getElem entryBound, selected⟩

structure Selected (declarations : List (Address × IxIR0.Decl)) (root : Address) where
  primitives : Primitives
  entries : Array Address
  scalar : Checked
  matched : ProgramMatches { env := IxIR0.Env.ofList declarations } primitives entries scalar.program
  rootFound : entries[scalar.program.entry]? = some root
  entryFunction : Function
  functionFound : scalar.program.functions[scalar.program.entry]? = some entryFunction
  binary : entryFunction.parameters = 2

/-- The first source ABI exports two runtime Nats. Internal helpers may
have zero, one, or two parameters. Selection does no per-input evaluation. -/
def select (declarations : List (Address × IxIR0.Decl)) (root : Address) : Except String (Selected declarations root) := do
  let some primitives := discover declarations | throw "scalar source primitive bodies are missing or unsupported"
  let ctx : IxIR0.Ctx := { env := IxIR0.Env.ofList declarations }
  let (functions, entry) ← lowerFunction ctx primitives 128 #[] root
  let entries := functions.map (·.1)
  let some scalar := Scalar.check { functions := functions.map (·.2), entry }
    | throw "scalar source graph exceeds its arity, scope, call-order, or size limits"
  if primitiveMatches : primitives.Matches ctx then
    if accepted : programMatches ctx primitives entries scalar.program = true then
      if rootFound : entries[scalar.program.entry]? = some root then
        match functionFound : scalar.program.functions[scalar.program.entry]? with
        | none => throw "scalar source entry is missing"
        | some entryFunction =>
            if binary : entryFunction.parameters = 2 then
              return {
                primitives, entries, scalar, matched := programMatches_sound primitiveMatches accepted
                rootFound, entryFunction, functionFound, binary }
            else throw "scalar source entry must accept two runtime Nats"
      else throw "scalar source entry does not match the selected root"
    else throw "scalar source reconstruction certificate failed"
  else throw "scalar source primitive certificate failed"

end Ix.Compiler.X86.Scalar.Source
