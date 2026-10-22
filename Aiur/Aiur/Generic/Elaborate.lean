import Aiur.Generic.Consts

namespace Aiur.Generic

def checkType (p : Program α) (params : List String) : Ty → Except String Unit
  | .field => pure ()
  | .ptr t => checkType p params t
  | .array t n => do checkArrayLength n; checkType p params t
  | .tuple ts => do
      for t in ts do checkType p params t
  | .param n => if params.contains n then pure () else throw s!"unbound type parameter '{n}'"
  | .named n ts => do
      let some decl := p.findEnum? n | throw s!"unknown type '{n}'"
      let _ ← arguments decl.typeParams ts
      for t in ts do checkType p params t
termination_by t => sizeOf t

/-- Preserve the source rule that recursive type cycles cross a pointer, even
when a zero-length array would erase the cycle from the concrete layout. -/
def checkInlineType (p : Program α) : Nat → List Instance → Ty → Except String Unit
  | 0, _, _ => throw "inline type check depth exceeded"
  | fuel + 1, path, t => match t with
    | .field | .param _ | .ptr _ => pure ()
    | .array t _ => checkInlineType p fuel path t
    | .tuple ts => ts.forM (checkInlineType p fuel path)
    | .named n ts => do
        let key := Instance.mk n ts
        if path.contains key then throw s!"inline recursive type '{n}' requires a pointer"
        if (ts.map Ty.nodes).sum > 4096 then throw "enum instance type-size limit exceeded"
        let some decl := p.findEnum? n | throw s!"unknown enum '{n}'"
        let env ← arguments decl.typeParams ts
        for ctor in decl.constructors do
          for t in ctor.fields do checkInlineType p fuel (key :: path) (t.subst env)

/-- Inspect source types before zero-length arrays erase their element layout.
All constructor payloads are checked, independently of inhabited values. -/
def checkPointerFree (p : Program α) (context : String) : Nat → List Instance → Ty → Except String Unit
  | 0, _, _ => throw "pointer-free type check depth exceeded"
  | fuel + 1, seen, t => match t with
    | .field => pure ()
    | .ptr _ => throw s!"pointer type is not allowed in {context}"
    | .param _ => throw s!"{context} requires a concrete pointer-free type"
    | .array t _ => checkPointerFree p context fuel seen t
    | .tuple ts => ts.forM (checkPointerFree p context fuel seen)
    | .named n ts => do
        let key := Instance.mk n ts
        if seen.contains key then return
        let some decl := p.findEnum? n | throw s!"unknown enum '{n}'"
        let env ← arguments decl.typeParams ts
        for ctor in decl.constructors do
          for t in ctor.fields do checkPointerFree p context fuel (key :: seen) (t.subst env)

private structure Inference where
  next : Nat := 0
  solutions : List (String × Ty) := []
  exits : List (ExitTarget × Ty) := []
  /-- A jump has no ordinary value. Its otherwise unconstrained result slot
  may default to unit without making generic value inference permissive. -/
  dead : List String := []
  /-- Static interface checking may supply const types without their values.
  Ordinary source checking always leaves this empty. -/
  interfaceConsts : List (String × Ty) := []

private abbrev Infer := StateT Inference (Except String)

private def fresh : Infer Ty := do
  let state ← get
  set { state with next := state.next + 1 }
  return .param s!"$infer{state.next}"

private def normalize (s : Inference) (t : Ty) : Ty :=
  (List.range (s.next + 1)).foldl (fun t _ => t.subst s.solutions) t

private def zonk (t : Ty) : Infer Ty := return normalize (← get) t

private def finishType (s : Inference) (t : Ty) : Except String Ty := do
  let defaults := s.dead.flatMap fun name =>
    match normalize s (.param name) with
    | .param n => if n.startsWith "$infer" then [(n, Ty.tuple [])] else []
    | _ => []
  let t := (normalize s t).subst defaults
  if t.parameters.any (·.startsWith "$infer") then
    throw "cannot infer type arguments; add explicit ::<...> arguments or a result type"
  return t

private def bindMeta (name : String) (t : Ty) : Infer Unit := do
  if t.parameters.contains name then throw "infinite type in type argument inference"
  modify fun s => { s with solutions := (name, t) :: s.solutions }

private def unify : Nat → Ty → Ty → Infer Unit
  | 0, _, _ => throw "type inference depth limit exceeded"
  | fuel + 1, a, b => do
      let a ← zonk a
      let b ← zonk b
      if a == b then return
      match a, b with
      | .param n, t =>
          if n.startsWith "$infer" then bindMeta n t
          else match t with
            | .param m =>
                if m.startsWith "$infer" then bindMeta m a
                else throw s!"type mismatch: {repr a} and {repr b}"
            | _ => throw s!"type mismatch: {repr a} and {repr b}"
      | t, .param n =>
          if n.startsWith "$infer" then bindMeta n t
          else throw s!"type mismatch: {repr a} and {repr b}"
      | .ptr a, .ptr b => unify fuel a b
      | .array a n, .array b m =>
          if n != m then throw s!"array length mismatch: {n} and {m}"
          unify fuel a b
      | .tuple xs, .tuple ys | .named _ xs, .named _ ys =>
          match a, b with
          | .named n _, .named m _ => if n != m then throw s!"different nominal types '{n}' and '{m}'"
          | _, _ => pure ()
          if xs.length != ys.length then throw "type argument or tuple arity mismatch"
          for (x, y) in xs.zip ys do unify fuel x y
      | _, _ => throw s!"type mismatch: {repr a} and {repr b}"

private def agree (a b : Ty) : Infer Unit := unify 1024 a b

private def typeArgs (p : Program α) (rigid params : List String) (supplied : Option (List Ty)) : Infer (List Ty) := do
  match supplied with
  | some ts =>
      let _ ← liftM (arguments params ts)
      liftM (ts.forM (checkType p rigid))
      return ts
  | none => params.mapM fun _ => fresh

private def ctorFields (p : Program α) (name ctor : String) (ts : List Ty) : Except String (List Ty) := do
  let some decl := p.findEnum? name | throw s!"unknown enum '{name}'"
  let env ← arguments decl.typeParams ts
  let some c := decl.constructors.find? (·.name == ctor) | throw s!"unknown constructor '{name}::{ctor}'"
  return c.fields.map (Ty.subst env)

private def instantiateTemplate (p : Program α) (rigid params : List String) (target : Ty) : Infer Ty := do
  liftM (checkParams params)
  liftM (checkType p (params ++ rigid) target)
  let ts ← params.mapM fun _ => fresh
  return target.subst (params.zip ts)

private def inferRecordHead (p : Program α) (rigid : List String)
    (head : RecordHead) (count : Nat) (expected : Option Ty) : Infer (RecordHead × List Ty) := do
  let type : Ty ← if head.params.isEmpty then do
      let .named name supplied := head.type | throw "struct construction requires a nominal struct type"
      let some decl := p.findStruct? name | throw s!"unknown struct '{name}'"
      pure (Ty.named name (← typeArgs p rigid decl.typeParams (if supplied.isEmpty then none else some supplied)))
    else instantiateTemplate p rigid head.params head.type
  if let some expected := expected then agree type expected
  let .named name types ← zonk type | throw "expected a known struct type"
  let some decl := p.findStruct? name | throw s!"unknown struct '{name}'"
  let env ← liftM (arguments decl.typeParams types)
  if head.fields.length != count then throw "struct field/value count mismatch"
  if let some field := findDuplicate head.fields [] then throw s!"duplicate struct field '{field}'"
  let fieldTypes ← head.fields.mapM fun field => do
    let some type := decl.fields.lookup field | throw s!"unknown field '{field}' in struct '{name}'"
    pure (type.subst env)
  if !head.rest then
    for (field, _) in decl.fields do
      if !head.fields.contains field then throw s!"missing field '{field}' in struct '{name}'"
  let slots := decl.fields.map fun (field, _) => head.fields.findIdx? (· == field)
  return ({ head with type := .named name types, params := [], slots := some slots }, fieldTypes)

private def inferPattern (p : Program α) (rigid : List String) : Nat → Pattern α → Ty → Infer (Pattern α × List (String × Ty))
  | 0, _, _ => throw "pattern depth limit exceeded"
  | fuel + 1, pat, expected => do
      match pat with
      | .record head ps =>
          let (head, types) ← inferRecordHead p rigid head ps.length (some expected)
          let pairs ← (ps.zip types).mapM fun (pat, type) => inferPattern p rigid fuel pat type
          return (.record head (pairs.map Prod.fst), (head.order (pairs.map Prod.snd) []).flatten)
      | .literal x => agree .field expected; return (.literal x, [])
      | .wildcard => return (.wildcard, [])
      | .bind n => return (.bind n, [(n, expected)])
      | .global n annotation =>
          if let some t := annotation then agree t expected
          if let some t := (← get).interfaceConsts.lookup n then
            agree t expected
            return (.global n (some expected), [])
          let body ← liftM (Consts.lookup p.consts n)
          let (_, bindings) ← inferPattern p rigid fuel body expected
          if !bindings.isEmpty then throw s!"const '::{n}' contains a binder"
          return (.global n (some expected), [])
      | .orElse left right _ =>
          let (left, leftBindings) ← inferPattern p rigid fuel left expected
          let (right, rightBindings) ← inferPattern p rigid fuel right expected
          for bindings in [leftBindings, rightBindings] do
            if let some n := findDuplicate (bindings.map Prod.fst) [] then
              throw s!"duplicate pattern binding '{n}'"
          if leftBindings.length != rightBindings.length then
            throw "or-pattern alternatives must bind the same names"
          for (name, type) in leftBindings do
            let some other := rightBindings.lookup name |
              throw s!"or-pattern alternative does not bind '{name}'"
            agree type other
          let names := leftBindings.map Prod.fst
          let rightOrder := names.map fun name => rightBindings.findIdx (·.1 == name)
          return (.orElse left right ⟨names, rightOrder⟩, leftBindings)
      | .load pat =>
          let target ← fresh
          agree (.ptr target) expected
          let (pat, bindings) ← inferPattern p rigid fuel pat target
          return (.load pat, bindings)
      | .tuple ps =>
          let ts ← ps.mapM fun _ => fresh
          agree (.tuple ts) expected
          let pairs ← (ps.zip ts).mapM fun (pat, t) => inferPattern p rigid fuel pat t
          return (.tuple (pairs.map Prod.fst), pairs.flatMap Prod.snd)
      | .array ps =>
          liftM (checkArrayLength ps.length)
          let t ← fresh
          agree (.array t ps.length) expected
          let pairs ← ps.mapM fun pat => inferPattern p rigid fuel pat t
          return (.array (pairs.map Prod.fst), pairs.flatMap Prod.snd)
      | .repeat pat n =>
          liftM (checkArrayLength n)
          let t ← fresh
          agree (.array t n) expected
          let (pat, bindings) ← inferPattern p rigid fuel pat t
          return (.repeat pat n, (List.replicate n bindings).flatten)
      | .construct (.named n supplied) ctor ps =>
          let some decl := p.findEnum? n | throw s!"unknown enum '{n}'"
          let ts ← typeArgs p rigid decl.typeParams (if supplied.isEmpty then none else some supplied)
          agree (.named n ts) expected
          let fields ← liftM (ctorFields p n ctor ts)
          if ps.length != fields.length then throw s!"wrong arity for constructor '{n}::{ctor}'"
          let pairs ← (ps.zip fields).mapM fun (pat, t) => inferPattern p rigid fuel pat t
          return (.construct (.named n ts) ctor (pairs.map Prod.fst), pairs.flatMap Prod.snd)
      | .construct _ _ _ => throw "constructor pattern requires a nominal enum type"
      | .constructAs params target ctor ps =>
          let target ← instantiateTemplate p rigid params target
          agree target expected
          let .named n ts ← zonk target | throw "constructor pattern requires a known nominal enum type"
          let fields ← liftM (ctorFields p n ctor ts)
          if ps.length != fields.length then throw s!"wrong arity for constructor '{n}::{ctor}'"
          let pairs ← (ps.zip fields).mapM fun (pat, t) => inferPattern p rigid fuel pat t
          return (.construct (.named n ts) ctor (pairs.map Prod.fst), pairs.flatMap Prod.snd)

private def pattern (p : Program α) (rigid : List String) (pat : Pattern α) (t : Ty) : Infer (Pattern α × List (String × Ty)) := do
  let (pat, bindings) ← inferPattern p rigid 1024 pat t
  if let some n := findDuplicate (bindings.map Prod.fst) [] then throw s!"duplicate pattern binding '{n}'"
  return (pat, bindings)

private def inferUpdatePath (p : Program α) : Ty → UpdatePath → Infer (Ty × UpdatePath)
  | type, [] => pure (type, [])
  | type, step :: rest => do
      let type ← zonk type
      let (target, step) ← match step, type with
        | .member field, .named name types => do
            let some decl := p.findStruct? name | throw "update field requires a struct"
            let some index := decl.fields.findIdx? (fun pair => pair.1 == field.name) |
              throw s!"unknown update field '{field.name}' in struct '{name}'"
            let some target := decl.fields.lookup field.name | throw "unknown update field"
            let env ← liftM (arguments decl.typeParams types)
            pure (target.subst env, UpdateStep.member { field with owner := some type, index, arity := decl.fields.length })
        | .project index _, .tuple fields => do
            let some target := fields[index]? | throw "tuple update index out of bounds"
            pure (target, UpdateStep.project index fields.length)
        | .index index _, .array element length => do
            if index >= length then throw "array update index out of bounds"
            pure (element, UpdateStep.index index length)
        | _, .ptr _ => throw "update paths cannot follow pointers; load the value explicitly"
        | .member _, _ => throw "update field requires a struct"
        | .project _ _, _ => throw "tuple update requires a tuple"
        | .index _ _, _ => throw "array update requires an array"
      let (result, rest) ← inferUpdatePath p target rest
      return (result, step :: rest)

private def updateOverlap : UpdatePath → UpdatePath → Bool
  | [], _ | _, [] => true
  | a :: as, b :: bs => a.position == b.position && updateOverlap as bs

private def infer (p : Program α) (rigid : List String) :
    Nat → List (String × Ty) → Expr α → Option Ty → Infer (Ty × Expr α)
  | 0, _, _, _ => throw "expression depth limit exceeded"
  | fuel + 1, locals, e, expected => do
      let (t, e) ← match e with
      | .control (.block label) body => do
          liftM (checkIdentifier label)
          let target ← match expected with | some t => pure t | none => fresh
          let previous := (← get).exits
          modify fun s => { s with exits := (.block label, target) :: previous }
          let (_, body) ← infer p rigid fuel locals body (some target)
          modify fun s => { s with exits := previous }
          pure (target, .control (.block label) body)
      | .control (.exit target) value => do
          let some result := (← get).exits.lookup target |
            throw (match target with
              | .function => "return outside a function"
              | .block label => s!"unknown enclosing block label '{label}'")
          let (_, value) ← infer p rigid fuel locals value (some result)
          let t ← match expected with
            | some t => pure t
            | none => fresh
          modify fun s => { s with dead := t.parameters ++ s.dead }
          pure (t, .control (.exit target) value)
      | .builtin op operands => do
          match op with
          | .ascribe type =>
              liftM (checkType p rigid type)
              let [value] := operands | throw "type annotations take one expression"
              if let some expected := expected then agree type expected
              let (_, value) ← infer p rigid fuel locals value (some type)
              pure (type, .builtin (.ascribe type) [value])
          | .assertEq message =>
              let [left, right] := operands | throw "assert_eq! takes two operands"
              let (type, left) ← infer p rigid fuel locals left none
              let (_, right) ← infer p rigid fuel locals right (some type)
              let type ← zonk type
              liftM (checkPointerFree p "assert_eq!" 1024 [] type)
              pure (.tuple [], .builtin (.assertEq message) [left, right])
          | .debug message =>
              let pairs ← operands.mapM fun value => infer p rigid fuel locals value none
              pure (.tuple [], .builtin (.debug message) (pairs.map Prod.snd))
      | .update paths operands => do
          let base :: replacements := operands | throw "update requires a base value"
          if paths.length != replacements.length then throw "update path/replacement count mismatch"
          let (type, base) ← infer p rigid fuel locals base expected
          let mut checkedPaths := []
          let mut checkedValues := []
          for (path, replacement) in paths.zip replacements do
            if path.isEmpty then throw "update paths cannot be empty"
            let (target, path) ← inferUpdatePath p type path
            if checkedPaths.any (updateOverlap path) then throw "duplicate or overlapping update targets"
            let (_, replacement) ← infer p rigid fuel locals replacement (some target)
            checkedPaths := checkedPaths ++ [path]
            checkedValues := checkedValues ++ [replacement]
          pure (type, .update checkedPaths (base :: checkedValues))
      | .record head xs => do
          if head.rest then throw "struct values must specify every field"
          let (head, types) ← inferRecordHead p rigid head xs.length expected
          let pairs ← (xs.zip types).mapM fun (expr, type) => infer p rigid fuel locals expr (some type)
          pure (head.type, .record head (pairs.map Prod.snd))
      | .member value field => do
          let (type, value) ← infer p rigid fuel locals value none
          let .named name types ← zonk type | throw "named field access requires a struct"
          let some decl := p.findStruct? name | throw "named field access requires a struct"
          let some index := decl.fields.findIdx? (fun pair => pair.1 == field.name) |
            throw s!"unknown field '{field.name}' in struct '{name}'"
          let some type := decl.fields.lookup field.name | throw "unknown struct field"
          let env ← liftM (arguments decl.typeParams types)
          pure (type.subst env, .member value
            { field with owner := some (.named name types), index, arity := decl.fields.length })
      | .literal x => pure (.field, .literal x)
      | .var n =>
          match locals.lookup n with
          | some t => pure (t, .var n)
          | none => infer p rigid fuel [] (.global n) expected
      | .global n annotation => do
          let t ← match expected with | some t => pure t | none => fresh
          if let some a := annotation then agree a t
          if let some declared := (← get).interfaceConsts.lookup n then agree declared t
          else
            let body ← liftM (Consts.lookup p.consts n)
            let (_, bindings) ← inferPattern p rigid fuel body t
            if !bindings.isEmpty then throw s!"const '::{n}' contains a binder"
          pure (t, .global n (some t))
      | .tuple xs => do
          let ts ← xs.mapM fun _ => fresh
          if let some expected := expected then agree (.tuple ts) expected
          let pairs ← (xs.zip ts).mapM fun (x, t) => infer p rigid fuel locals x (some t)
          pure (.tuple ts, .tuple (pairs.map Prod.snd))
      | .array xs => do
          liftM (checkArrayLength xs.length)
          let t ← fresh
          if let some expected := expected then agree (.array t xs.length) expected
          let pairs ← xs.mapM fun x => infer p rigid fuel locals x (some t)
          pure (.array t xs.length, .array (pairs.map Prod.snd))
      | .repeat x n => do
          liftM (checkArrayLength n)
          let t ← fresh
          if let some expected := expected then agree (.array t n) expected
          let (_, x) ← infer p rigid fuel locals x (some t)
          pure (.array t n, .repeat x n)
      | .index x i => do
          let (t, x) ← infer p rigid fuel locals x none
          let .array t n ← zonk t | throw "indexing requires a known array type"
          if i >= n then throw s!"array index {i} out of bounds for length {n}"
          pure (t, .index x i)
      | .slice x start stop => do
          let (t, x) ← infer p rigid fuel locals x none
          let .array t n ← zonk t | throw "slicing requires a known array type"
          let stop := stop.getD n
          if start > stop || stop > n then throw s!"array slice {start}..{stop} out of bounds for length {n}"
          pure (.array t (stop - start), .slice x start (some stop))
      | .construct n supplied ctor xs => do
          let some decl := p.findEnum? n | throw s!"unknown enum '{n}'"
          let ts ← typeArgs p rigid decl.typeParams supplied
          if let some expected := expected then agree (.named n ts) expected
          let fields ← liftM (ctorFields p n ctor ts)
          if xs.length != fields.length then throw s!"wrong arity for constructor '{n}::{ctor}'"
          let pairs ← (xs.zip fields).mapM fun (x, t) => infer p rigid fuel locals x (some t)
          pure (.named n ts, .construct n (some ts) ctor (pairs.map Prod.snd))
      | .constructAs params target ctor xs => do
          let target ← instantiateTemplate p rigid params target
          if let some expected := expected then agree target expected
          let .named n ts ← zonk target | throw "constructor requires a known nominal enum type"
          let fields ← liftM (ctorFields p n ctor ts)
          if xs.length != fields.length then throw s!"wrong arity for constructor '{n}::{ctor}'"
          let pairs ← (xs.zip fields).mapM fun (x, t) => infer p rigid fuel locals x (some t)
          pure (.named n ts, .construct n (some ts) ctor (pairs.map Prod.snd))
      | .project x i => do
          let (t, x) ← infer p rigid fuel locals x none
          let .tuple ts ← zonk t | throw "projection requires a known tuple type"
          let some t := ts[i]? | throw s!"tuple index {i} out of bounds"
          pure (t, .project x i)
      | .letValue pat x b => do
          let (t, x) ← infer p rigid fuel locals x none
          let (pat, bs) ← pattern p rigid pat t
          let (t, b) ← infer p rigid fuel (bs ++ locals) b expected
          pure (t, .letValue pat x b)
      | .store x => do
          let target ← fresh
          if let some expected := expected then agree (.ptr target) expected
          let (_, x) ← infer p rigid fuel locals x (some target)
          pure (.ptr target, .store x)
      | .load x => do
          let target ← fresh
          let (_, x) ← infer p rigid fuel locals x (some (.ptr target))
          pure (target, .load x)
      | .hint t k channel => do
          if !t.concrete then throw "hint result types must be concrete, including in generic functions"
          liftM (checkType p [] t)
          liftM (checkPointerFree p "hint result" 1024 [] t)
          let decls ← liftM (collectEnums p [] 1024 [] (coreTypeNames t.toCore))
          let _ ← liftM ((checkHintType decls "generic function" t.toCore).mapError toString)
          let (_, k) ← infer p rigid fuel locals k none
          pure (t, .hint t k channel)
      | .neg x => do
          let (_, x) ← infer p rigid fuel locals x (some .field)
          pure (.field, .neg x)
      | .binary op x y => do
          let (_, x) ← infer p rigid fuel locals x (some .field)
          let (_, y) ← infer p rigid fuel locals y (some .field)
          pure (.field, .binary op x y)
      | .call n supplied xs => do
          let (params, inputs, result) ← match p.findFunction? n with
            | some fn => pure (fn.typeParams, fn.params.map Prod.snd, fn.result)
            | none => match p.maps.find? (·.name == n) with
              | some m => pure ([], m.params.map Prod.snd, m.result)
              | none => throw s!"unknown function or map '{n}'"
          let ts ← typeArgs p rigid params supplied
          let env := params.zip ts
          let result := result.subst env
          if let some expected := expected then agree result expected
          if xs.length != inputs.length then throw s!"wrong argument count for '{n}'"
          let pairs ← (xs.zip inputs).mapM fun (x, t) => infer p rigid fuel locals x (some (t.subst env))
          pure (result, .call n (some ts) (pairs.map Prod.snd))
      | .matchValue x arms => do
          if arms.isEmpty then throw "empty match"
          let (t, x) ← infer p rigid fuel locals x none
          let result ← match expected with | some t => pure t | none => fresh
          let arms ← arms.mapM fun (pat, b) => do
            let (pat, bs) ← pattern p rigid pat t
            let (_, b) ← infer p rigid fuel (bs ++ locals) b (some result)
            return (pat, b)
          pure (result, .matchValue x arms)
      if let some expected := expected then agree t expected
      return (t, e)

private def finishPattern (s : Inference) : Pattern α → Except String (Pattern α)
  | .literal x => pure (.literal x)
  | .wildcard => pure .wildcard
  | .bind n => pure (.bind n)
  | .global n t => return .global n (← t.mapM (finishType s))
  | .record head ps => return .record { head with type := ← finishType s head.type } (← ps.mapM (finishPattern s))
  | .orElse left right names => return .orElse (← finishPattern s left) (← finishPattern s right) names
  | .load p => return .load (← finishPattern s p)
  | .tuple ps => return .tuple (← ps.mapM (finishPattern s))
  | .array ps => return .array (← ps.mapM (finishPattern s))
  | .repeat p n => return .repeat (← finishPattern s p) n
  | .construct t c ps => return .construct (← finishType s t) c (← ps.mapM (finishPattern s))
  | .constructAs _ _ _ _ => throw "unelaborated constructor pattern template"
termination_by p => sizeOf p

private def finishExpr (s : Inference) : Expr α → Except String (Expr α)
  | .control kind body => return .control kind (← finishExpr s body)
  | .literal x => pure (.literal x)
  | .var n => pure (.var n)
  | .global n t => return .global n (← t.mapM (finishType s))
  | .tuple xs => return .tuple (← xs.mapM (finishExpr s))
  | .array xs => return .array (← xs.mapM (finishExpr s))
  | .repeat x n => return .repeat (← finishExpr s x) n
  | .index x i => return .index (← finishExpr s x) i
  | .slice x start stop => return .slice (← finishExpr s x) start stop
  | .construct n ts c xs => return .construct n (some (← (ts.getD []).mapM (finishType s))) c (← xs.mapM (finishExpr s))
  | .constructAs _ _ _ _ => throw "unelaborated constructor template"
  | .builtin op xs => return .builtin (← op.mapTypesM (finishType s)) (← xs.mapM (finishExpr s))
  | .update paths xs => do
      let paths ← paths.mapM fun path => path.mapM fun step => match step with
        | .member field => return .member { field with owner := ← field.owner.mapM (finishType s) }
        | step => pure step
      return .update paths (← xs.mapM (finishExpr s))
  | .record head xs => return .record { head with type := ← finishType s head.type } (← xs.mapM (finishExpr s))
  | .member x field => return .member (← finishExpr s x) { field with owner := ← field.owner.mapM (finishType s) }
  | .project x i => return .project (← finishExpr s x) i
  | .letValue p x b => return .letValue (← finishPattern s p) (← finishExpr s x) (← finishExpr s b)
  | .store x => return .store (← finishExpr s x)
  | .load x => return .load (← finishExpr s x)
  | .hint t k channel => return .hint (← finishType s t) (← finishExpr s k) channel
  | .neg x => return .neg (← finishExpr s x)
  | .binary op x y => return .binary op (← finishExpr s x) (← finishExpr s y)
  | .call n ts xs => return .call n (some (← (ts.getD []).mapM (finishType s))) (← xs.mapM (finishExpr s))
  | .matchValue x arms =>
      return .matchValue (← finishExpr s x)
        (← arms.mapM fun arm => return (← finishPattern s arm.1, ← finishExpr s arm.2))
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; try simp_all only [Prod.mk.sizeOf_spec]
  all_goals first | omega | cases ‹Pattern α × Expr α›; simp_all only [Prod.mk.sizeOf_spec]; omega

def elaborateExpr (p : Program α) (rigid : List String) (locals : List (String × Ty))
    (e : Expr α) (expected : Ty) (inFunction : Bool := false)
    (interfaceConsts : List (String × Ty) := []) : Except String (Expr α) := do
  let ((_, e), state) ← infer p rigid 4096 locals e (some expected)
    { exits := if inFunction then [(.function, expected)] else [], interfaceConsts }
  finishExpr state e

/-- Infer a module's exported constant type using only dependency interfaces.
The pattern is checked directly, without inventing values for abstract types. -/
def inferInterfaceConst (p : Program α) (body : Pattern α)
    (expected : Option Ty) (interfaceConsts : List (String × Ty))
    (requireConcrete : Bool := true) : Except String Ty := do
  let (type, state) ← (do
    let type ← match expected with | some type => pure type | none => fresh
    let (_, bindings) ← inferPattern p [] 4096 body type
    if !bindings.isEmpty then throw "const body contains binders"
    zonk type : Infer Ty).run { interfaceConsts }
  let type ← (zonk type).run' state
  if requireConcrete && !type.concrete then throw "ambiguous exported const type; add a type annotation"
  return type

/-- Check one const body at its use type, retaining any nested references.
This supplies type information for context-dependent constructors such as
`Option::None`; it never inlines a referenced const. -/
def elaborateConst (p : Program α) (name : String) (expected : Ty) : Except String (Pattern α) := do
  let body ← Consts.lookup p.consts name
  let ((body, _), state) ← inferPattern p expected.parameters 4096 body expected {}
  finishPattern state body

/-- Syntactic call dependencies retain every branch, including redundant ones.
Consts cannot contain calls, so a reference introduces no function dependency. -/
def sourceCalls (types : List (String × Ty)) : Expr α → List Instance
  | .call name supplied args =>
      ⟨name, (supplied.getD []).map (Ty.subst types)⟩ :: args.flatMap (sourceCalls types)
  | .builtin _ xs | .update _ xs | .record _ xs | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs => xs.flatMap (sourceCalls types)
  | .member x _ | .control _ x | .project x _ | .index x _ | .slice x _ _ | .repeat x _ | .store x | .load x | .hint _ x channel | .neg x => sourceCalls types x
  | .letValue _ x b | .binary _ x b => sourceCalls types x ++ sourceCalls types b
  | .matchValue x arms => sourceCalls types x ++ arms.flatMap (fun a => sourceCalls types a.2)
  | _ => []
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

/-- Whole-program conservative specialization admissibility. Ordinary recursion
closes a path; a change of recursive type arguments is rejected even in an
unused function. This is independent of termination of value evaluation. -/
def checkGenericCycles (p : Program α) : Except String Unit := do
  let rec visit : Nat → List Instance → Instance → Except String Unit
    | 0, _, _ => throw "generic dependency depth exceeded"
    | fuel + 1, path, key => do
        let some fn := p.findFunction? key.name | return
        if let some ancestor := path.find? (·.name == key.name) then
          if ancestor != key then
            throw s!"recursive call to '{key.name}' changes type arguments"
          return
        let types ← arguments fn.typeParams key.types
        (sourceCalls types fn.body).forM (visit fuel (key :: path))
  -- Only a generic function can be revisited with different type arguments.
  -- Every such function is checked from its own symbolic root, including paths
  -- through ordinary functions. Starting again at every ordinary function adds
  -- no check, but enumerates exponentially many paths in large recursive code.
  (p.functions.filter (fun fn => !fn.typeParams.isEmpty)).forM fun fn =>
    visit (p.functions.length + 1) [] ⟨fn.name, fn.typeParams.map Ty.param⟩

/-- Only edges between mandatory-inline functions participate in this check.
An ordinary function call stops expansion, including on a recursive path. -/
def checkInlineCycles (p : Program α) : Except String Unit := do
  let rec visit : Nat → List String → String → Except String Unit
    | 0, _, _ => throw "inline dependency depth exceeded"
    | fuel + 1, path, name => do
        let some fn := p.findFunction? name | return
        if !fn.isInline then return
        if path.contains name then throw s!"inline cycle through '{name}'"
        for callee in sourceCalls [] fn.body do
          visit fuel (name :: path) callee.name
  for fn in p.functions do visit (p.functions.length + 1) [] fn.name

/-- Check source expressions and infer their type metadata. Const references
remain references; only type information is normalized. -/
def elaborate (p : Program α) : Except String (Program α) := do
  Consts.checkAcyclic p
  let aliases := p.aliases
  let p ← expandAliases p
  if let some n := findDuplicate (p.functions.map (·.name) ++ p.maps.map (·.name)) [] then
    throw s!"duplicate function/map '{n}'"
  if let some n := findDuplicate (p.enums.map (·.name)) [] then throw s!"duplicate enum '{n}'"
  for d in p.structs do
    checkIdentifier d.name
    if d.name == "Field" then throw "Field is a reserved type name"
    checkParams d.typeParams
    if let some field := findDuplicate (d.fields.map Prod.fst) [] then throw s!"duplicate struct field '{field}'"
    for (name, type) in d.fields do
      checkIdentifier name
      checkType p d.typeParams type
    checkInlineType p 1024 [] (.named d.name (d.typeParams.map Ty.param))
    let name := (Instance.mk d.name (d.typeParams.map Ty.param)).symbol
    let decls ← collectEnums p d.typeParams 1024 [] [name]
    (checkDeclarations decls).mapError toString
  for d in p.enums do
    checkIdentifier d.name
    if d.name == "Field" then throw "Field is a reserved type name"
    checkParams d.typeParams
    if d.constructors.isEmpty then throw s!"empty enum '{d.name}'"
    if let some n := findDuplicate (d.constructors.map (·.name)) [] then throw s!"duplicate constructor '{n}'"
    for c in d.constructors do
      checkIdentifier c.name
      c.fields.forM (checkType p d.typeParams)
    let name := (Instance.mk d.name (d.typeParams.map Ty.param)).symbol
    checkInlineType p 1024 [] (.named d.name (d.typeParams.map Ty.param))
    let decls ← collectEnums p d.typeParams 1024 [] [name]
    (checkDeclarations decls).mapError toString
  for d in p.consts do
    -- Templates need not fix omitted constructor type arguments before a use
    -- supplies context, but every template must admit a consistent type.
    let _ ← (do
      let target ← fresh
      let _ ← inferPattern p [] 1024 d.value target
      pure () : Infer Unit).run {}
  let functions ← p.functions.mapM fun fn => do
    checkIdentifier fn.name
    checkParams fn.typeParams
    if let some n := findDuplicate (fn.params.map Prod.fst) [] then throw s!"duplicate parameter '{n}'"
    (fn.params.map Prod.snd ++ [fn.result]).forM (checkType p fn.typeParams)
    let body ← elaborateExpr p fn.typeParams fn.params fn.body fn.result true
    return { fn with body }
  let tables ← p.tables.mapM fun t => do
    checkType p [] t.rowType
    checkPointerFree p s!"table '{t.name}'" 1024 [] t.rowType
    let rows ← t.rows.mapM fun row => elaborateExpr p [] [] row t.rowType
    return { t with rows }
  for m in p.maps do
    checkIdentifier m.name
    (m.params.map Prod.snd ++ [m.result]).forM (checkType p [])
    (m.params.map Prod.snd ++ [m.result]).forM (checkPointerFree p s!"map '{m.name}'" 1024 [])
    let some input := p.tables.find? (·.name == m.input) | throw s!"unknown table '{m.input}'"
    let some output := p.tables.find? (·.name == m.output) | throw s!"unknown table '{m.output}'"
    if input.rowType != .tuple (m.params.map Prod.snd) then throw s!"input table type mismatch for map '{m.name}'"
    if output.rowType != m.result then throw s!"output table type mismatch for map '{m.name}'"
  let checked := { p with functions, tables, aliases }
  checkGenericCycles checked
  checkInlineCycles checked
  return checked

/-- Compiler preparation may inline consts after the source semantics boundary.
The source checker above does not use this transformation. -/
def prepareTemplates (p : Program α) : Except String (Program α) := do
  let p ← elaborate (← expandConsts p)
  return { p with aliases := [], consts := [] }

/-- Resolve pattern conditions for diagnostics and compiler preparation. The
original match arms remain unchanged. -/
def inspectPattern (p : Program α) : Nat → Pattern α → Except String (Pattern α)
  | 0, _ => throw "pattern inspection depth exceeded"
  | fuel + 1, pat => match pat with
    | .global name (some type) => do inspectPattern p fuel (← elaborateConst p name type)
    | .global name none => throw s!"missing type information for const '::{name}'"
    | .record head ps => return .record head (← ps.mapM (inspectPattern p fuel))
    | .orElse left right names => return .orElse (← inspectPattern p fuel left) (← inspectPattern p fuel right) names
    | .load pat => return .load (← inspectPattern p fuel pat)
    | .tuple ps => return .tuple (← ps.mapM (inspectPattern p fuel))
    | .array ps => return .array (← ps.mapM (inspectPattern p fuel))
    | .repeat pat n => return .repeat (← inspectPattern p fuel pat) n
    | .construct t c ps => return .construct t c (← ps.mapM (inspectPattern p fuel))
    | .constructAs ts t c ps => return .constructAs ts t c (← ps.mapM (inspectPattern p fuel))
    | _ => pure pat

end Aiur.Generic
