import Aiur.Generic.PatternLowering
import Aiur.Generic.ArrayLowering
import Aiur.Typecheck

namespace Aiur.Generic

def arguments (params : List String) (types : List Ty) : Except String (List (String × Ty)) := do
  if params.length != types.length then
    throw s!"expected {params.length} type arguments, got {types.length}"
  return params.zip types

def resolveEnum (p : Program α) (key : Instance) : Except String Aiur.EnumDecl := do
  let some decl := p.findEnum? key.name | throw s!"unknown enum '{key.name}'"
  let env ← arguments decl.typeParams key.types
  return {
    name := key.symbol
    constructors := decl.constructors.map fun ctor =>
      { name := ctor.name, fields := ctor.fields.map (fun t => (t.subst env).toCore) }
  }

namespace StructLowering

def nominalName (types : List (String × Ty)) (type : Ty) : String :=
  match (type.subst types).toCore with | .enum name => name | _ => "$invalid"

/-- Evaluate initializers once in written order, then arrange their values in
  declaration order. The temporary's scope contains only generated syntax. -/
def record (types : List (String × Ty)) (head : RecordHead) (items : List (Aiur.Expr α)) : Aiur.Expr α :=
  .letValue (.bind "$record") (.tuple items)
    (.construct (nominalName types head.type) structConstructor
      (head.order ((List.range items.length).map fun i => .project (.var "$record") i) (.tuple [])))

def fieldPatterns : Nat → Nat → List (Aiur.Pattern α)
  | 0, _ => []
  | n + 1, 0 => .bind "$member" :: List.replicate n .wildcard
  | n + 1, i + 1 => .wildcard :: fieldPatterns n i

def fieldPattern (field : FieldRef) : Aiur.Pattern α :=
  .construct (nominalName [] (field.owner.getD (.named "$invalid" []))) structConstructor
    (fieldPatterns field.arity field.index)

def member (types : List (String × Ty)) (value : Aiur.Expr α) (field : FieldRef) : Aiur.Expr α :=
  .letValue (fieldPattern (field.subst types)) value (.var "$member")

end StructLowering

namespace UpdateLowering

def shape (types : List (String × Ty)) (step : UpdateStep) : Aiur.Pattern α :=
  match step.owner with
  | none => .tuple (List.replicate step.width .wildcard)
  | some type => .construct (StructLowering.nominalName types type) structConstructor
      (List.replicate step.width .wildcard)

def product (types : List (String × Ty)) (step : UpdateStep) (items : List (Aiur.Expr α)) : Aiur.Expr α :=
  match step.owner with
  | none => .tuple items
  | some type => .construct (StructLowering.nominalName types type) structConstructor items

def component (types : List (String × Ty)) (step : UpdateStep) (index : Nat) : Aiur.Expr α :=
  match step.owner with
  | none => .project (.var "$withBase") index
  | some type => StructLowering.member types (.var "$withBase")
      { name := "", owner := some type, index, arity := step.width }

/-- Only generated code occurs inside these fixed temporary scopes. -/
def path (types : List (String × Ty)) : UpdatePath → Aiur.Expr α → Aiur.Expr α
  | [], input => .letValue .wildcard input (.var "$withNew")
  | step :: rest, input =>
      .letValue (.bind "$withBase") input
        (.letValue (shape types step) (.var "$withBase")
          (product types step ((List.range step.width).map fun i =>
            if i == step.position then path types rest (component types step i)
            else component types step i)))

def sequence (types : List (String × Ty)) : List UpdatePath → Nat → Aiur.Expr α
  | [], _ => .var "$withCurrent"
  | target :: targets, index =>
      .letValue (.bind "$withNew") (.project (.var "$withInputs") index)
        (.letValue (.bind "$withCurrent") (path types target (.var "$withCurrent"))
          (sequence types targets (index + 1)))

def expression (types : List (String × Ty)) (paths : List UpdatePath) (operands : List (Aiur.Expr α)) : Aiur.Expr α :=
  .letValue (.bind "$withInputs") (.tuple operands)
    (.letValue (.tuple (List.replicate (paths.length + 1) .wildcard)) (.var "$withInputs")
      (.letValue (.bind "$withCurrent") (.project (.var "$withInputs") 0)
        (sequence types paths 1)))

end UpdateLowering

namespace BuiltinLowering

/-- Only generated syntax occurs inside these temporary scopes. -/
def expression (op : Builtin) (operands : List (Aiur.Expr α)) : Aiur.Expr α :=
  match op with
  | .assertEq message => .letValue (.tuple [.bind "$assertLeft", .bind "$assertRight"]) (.tuple operands)
      (.assertEq message (.var "$assertLeft") (.var "$assertRight"))
  | .ascribe _ => .letValue (.tuple [.bind "$annotation"]) (.tuple operands) (.var "$annotation")
  | .debug _ => .letValue .wildcard (.tuple operands) (.tuple [])

end BuiltinLowering

/-- Inference has filled in every call/constructor's type arguments before
circuit lowering. Source evaluation uses the original body with a type
environment and never calls this translation. -/
def Expr.lower (env : List (String × Ty)) : Expr α → Aiur.Expr α
  | .literal x => .literal x
  | .var n => .var n
  | .global n _ => .var ("$const:" ++ n)
  | .control _ _ => .var "$unloweredControl"
  | .tuple xs | .array xs => .tuple (xs.map (Expr.lower env))
  | .repeat x n => ArrayLowering.repeatValue (x.lower env) n
  | .index x i => .project (x.lower env) i
  | .slice x start (some stop) => ArrayLowering.sliceValue (x.lower env) start stop
  | .slice _ _ none => .var "$unelaboratedSlice"
  | .construct n ts c xs =>
      .construct (Instance.symbol ⟨n, (ts.getD []).map (Ty.subst env)⟩) c (xs.map (Expr.lower env))
  | .constructAs _ t c xs =>
      let name := match (t.subst env).toCore with | .enum n => n | _ => "$invalid"
      .construct name c (xs.map (Expr.lower env))
  | .builtin op xs => BuiltinLowering.expression op (xs.map (Expr.lower env))
  | .update paths xs => UpdateLowering.expression env paths (xs.map (Expr.lower env))
  | .record head xs => StructLowering.record env head (xs.map (Expr.lower env))
  | .member x field => StructLowering.member env (x.lower env) field
  | .project x i => .project (x.lower env) i
  | .letValue p x b => PatternLowering.lowerLet env p (x.lower env) (b.lower env)
  | .store x => .store (x.lower env)
  | .load x => .load (x.lower env)
  | .hint t k channel => .hint (t.subst env).toCore (k.lower env) channel
  | .neg x => .neg (x.lower env)
  | .binary op x y => .binary op (x.lower env) (y.lower env)
  | .call n ts xs =>
      .call (Instance.symbol ⟨n, (ts.getD []).map (Ty.subst env)⟩) (xs.map (Expr.lower env))
  | .matchValue x arms =>
      PatternLowering.lowerMatch env (x.lower env) (arms.map fun arm => (arm.1, arm.2.lower env))
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def resolveFunction (p : Program α) (key : Instance) : Except String (Aiur.Function α) := do
  let some fn := p.findFunction? key.name | throw s!"unknown function '{key.name}'"
  let env ← arguments fn.typeParams key.types
  return {
    name := key.symbol
    params := fn.params.map fun (n, t) => (n, (t.subst env).toCore)
    result := (fn.result.subst env).toCore
    body := fn.body.lower env
  }

/-- Lookup in the compiler language, decoding the canonical instance name and
lowering its body. Source execution uses `Program.sourceFunction?` instead. -/
def Program.function? (p : Program α) (name : String) : Option (Aiur.Function α) :=
  (Instance.ofSymbol name >>= resolveFunction p).toOption

def Program.enum? (p : Program α) (name : String) : Option Aiur.EnumDecl :=
  (Instance.ofSymbol name >>= resolveEnum p).toOption

def coreTypeNames : Aiur.Ty → List String
  | .field => []
  | .tuple ts => ts.flatMap coreTypeNames
  | .ptr t => coreTypeNames t
  | .enum n => [n]
termination_by t => sizeOf t

def corePatternNames : Aiur.Pattern α → List String
  | .literal _ | .wildcard | .bind _ => []
  | .tuple ps => ps.flatMap corePatternNames
  | .construct n _ ps => n :: ps.flatMap corePatternNames
termination_by p => sizeOf p

/-- Syntactic dependencies include inactive arms; specialization is independent
of a particular execution or a hint provider. -/
def coreCalls : Aiur.Expr α → List String
  | .literal _ | .var _ => []
  | .tuple xs | .construct _ _ xs => xs.flatMap coreCalls
  | .call n xs => n :: xs.flatMap coreCalls
  | .project x _ | .store x | .load x | .hint _ x channel | .neg x => coreCalls x
  | .letValue _ x b | .binary _ x b | .assertEq _ x b => coreCalls x ++ coreCalls b
  | .matchValue x arms => coreCalls x ++ arms.flatMap (fun a => coreCalls a.2)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

def coreExprNames : Aiur.Expr α → List String
  | .literal _ | .var _ => []
  | .tuple xs | .call _ xs => xs.flatMap coreExprNames
  | .construct n _ xs => n :: xs.flatMap coreExprNames
  | .project x _ | .store x | .load x | .neg x => coreExprNames x
  | .hint t x channel => coreTypeNames t ++ coreExprNames x
  | .letValue p x b => corePatternNames p ++ coreExprNames x ++ coreExprNames b
  | .binary _ x b | .assertEq _ x b => coreExprNames x ++ coreExprNames b
  | .matchValue x arms => coreExprNames x ++ arms.flatMap (fun a => corePatternNames a.1 ++ coreExprNames a.2)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

/-- Finite type closure stops at identical instances. Different instances of
the same enum are essential for nested containers. A depth and type-size bound
rejects endlessly expanding families; the core checker rejects inline cycles. -/
def collectEnums (p : Program α) (rigid : List String) :
    Nat → List Instance → List String → Except String Aiur.Declarations
  | 0, _, _ => .error "enum instance limit exceeded"
  | fuel + 1, path, names => do
      let mut result := []
      for name in names.eraseDups do
        if name.startsWith "$param:" then
          if !(rigid.contains (name.drop 7).toString) then throw "unresolved type parameter"
          result := result ++ [{ name, constructors := [{ name := "$opaque", fields := [] }] }]
        else
          let key ← Instance.ofSymbol name
          if (key.types.map Ty.nodes).sum > 4096 then throw "enum instance type-size limit exceeded"
          if !path.contains key then
            let decl ← resolveEnum p key
            result := result ++ [decl] ++ (← collectEnums p rigid fuel (key :: path)
              (decl.constructors.flatMap fun ctor => ctor.fields.flatMap coreTypeNames))
      return result.foldl (fun acc d => if acc.any (·.name == d.name) then acc else acc ++ [d]) []

end Aiur.Generic
