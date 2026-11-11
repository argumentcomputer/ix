import Aiur.Modules.AST
import Mathlib.Data.List.Forall2

namespace Aiur.Modules

abbrev Bindings := List (String × Ref)

/- The static meaning of application and aliases. This relation has no fuel,
cache or elaborator in its definition. Canonical instances always name a body,
and aliases introduce no new identity. -/
mutual
inductive Denotes (p : Program α) : Bindings → Ref → Ref → Prop where
  | parameter (found : bindings.lookup name = some value) :
      Denotes p bindings (.mk name []) value
  | definitions (found : p.findModule? name = some decl)
      (body : decl.body = .definitions definitions)
      (arguments : DenotesMany p bindings args actual)
      (arity : decl.parameters.length = actual.length) :
      Denotes p bindings (.mk name args) (.mk name actual)
  | alias (found : p.findModule? name = some decl)
      (body : decl.body = .alias target)
      (arguments : DenotesMany p bindings args actual)
      (arity : decl.parameters.length = actual.length)
      (applied : Denotes p ((decl.parameters.map Prod.fst).zip actual) target result) :
      Denotes p bindings (.mk name args) result

inductive DenotesMany (p : Program α) : Bindings → List Ref → List Ref → Prop where
  | nil : DenotesMany p bindings [] []
  | cons : Denotes p bindings a b → DenotesMany p bindings as bs →
      DenotesMany p bindings (a :: as) (b :: bs)
end

structure Resolution (p : Program α) (bindings : Bindings) (ref : Ref) where
  value : Ref
  valid : Denotes p bindings ref value

structure Resolutions (p : Program α) (bindings : Bindings) (refs : List Ref) where
  values : List Ref
  valid : DenotesMany p bindings refs values

mutual
  /-- Bounded implementation of declarative resolution. Bounds only reject
  programs; every successful result carries its independent derivation. -/
  def resolve (p : Program α) (bindings : Bindings) :
      (fuel : Nat) → (ref : Ref) → Except String (Resolution p bindings ref)
    | 0, _ => .error "module expansion depth exceeded (possible cyclic alias)"
    | fuel + 1, .mk name args => do
        if h : args = [] then
          match found : bindings.lookup name with
          | some value => return ⟨value, by subst args; exact .parameter found⟩
          | none => pure ()
        else if (bindings.lookup name).isSome then
          throw s!"module parameter '{name}' cannot be applied"
        match found : p.findModule? name with
        | none => throw s!"unknown module '{name}'"
        | some decl =>
          let actual ← resolveMany p bindings fuel args
          if arity : decl.parameters.length = actual.values.length then
            match body : decl.body with
            | .definitions definitions =>
                return ⟨.mk name actual.values, .definitions found body actual.valid arity⟩
            | .alias target =>
                let result ← resolve p ((decl.parameters.map Prod.fst).zip actual.values) fuel target
                return ⟨result.value, .alias found body actual.valid arity result.valid⟩
          else throw s!"module '{name}' expects {decl.parameters.length} arguments"
  termination_by fuel _ => (fuel, 0)

  def resolveMany (p : Program α) (bindings : Bindings) (fuel : Nat) :
      (refs : List Ref) → Except String (Resolutions p bindings refs)
    | [] => return ⟨[], .nil⟩
    | ref :: refs => do
        let head ← resolve p bindings fuel ref
        let tail ← resolveMany p bindings fuel refs
        return ⟨head.value :: tail.values, .cons head.valid tail.valid⟩
  termination_by refs => (fuel, refs.length + 1)
end

/-- Rootless paths in expressions retain their spelling until module resolution.
Splitting respects nested applications such as `F::<G::<M>>::f`. -/
def splitPath (path : String) : List String := Id.run do
  let chars := path.toList
  let mut depth := 0
  let mut current := []
  let mut parts := []
  let mut i := 0
  while i < chars.length do
    let c := chars[i]!
    if c == ':' && chars[i + 1]? == some ':' && depth == 0 && chars[i + 2]? != some '<' then
      if !current.isEmpty then parts := parts ++ [String.ofList current]
      current := []
      i := i + 2
    else
      if c == '<' then depth := depth + 1
      if c == '>' then depth := depth - 1
      current := current ++ [c]
      i := i + 1
  if !current.isEmpty then parts := parts ++ [String.ofList current]
  return parts

private def splitArgs (chars : List Char) : List String := Id.run do
  let mut depth := 0
  let mut current := []
  let mut parts := []
  for c in chars do
    if c == ',' && depth == 0 then
      parts := parts ++ [String.ofList current]
      current := []
    else
      if c == '<' then depth := depth + 1
      if c == '>' then depth := depth - 1
      current := current ++ [c]
  return parts ++ [String.ofList current]

def parseRef : Nat → String → Except String Ref
  | 0, _ => .error "module path depth exceeded"
  | fuel + 1, text => do
      let text := text.trimAscii.toString
      let parts := text.splitOn "::<"
      let name := parts.head!
      if name.isEmpty then throw "empty module name"
      if parts.length == 1 then return .mk name []
      if !text.endsWith ">" then throw "unterminated module application"
      let args := ((text.drop (name.length + 3)).toString.dropEnd 1).toString
      let refs ← (splitArgs args.toList).mapM (parseRef fuel)
      return .mk name refs

end Aiur.Modules
