import Aiur.Modules.Rewrite

namespace Aiur.Modules

def memberNames (p : Generic.Program α) : List String :=
  p.functions.map (·.name) ++ p.nominals.map (·.name) ++ p.aliases.map (·.name) ++
    p.consts.map (·.name) ++ p.tables.map (·.name) ++ p.maps.map (·.name)

def Signature.names (s : Signature) :=
  s.types.map (·.name) ++ s.consts.map Prod.fst ++ s.functions.map (·.name) ++ s.tables.map Prod.fst

def Signature.exposes (s : Signature) (access : Access) (name : String) : Bool :=
  match access with
  | .type => s.types.any (·.name == name)
  | .constructor => (s.types.find? (·.name == name)).any (·.definition.isSome)
  | .constant => s.consts.any (·.1 == name)
  | .callable => s.functions.any (·.name == name)
  | .table => s.tables.any (·.1 == name)

def hasMember (p : Generic.Program α) (access : Access) (name : String) : Bool :=
  match access with
  | .type | .constructor => (p.nominals.map (·.name) ++ p.aliases.map (·.name)).contains name
  | .constant => p.consts.any (·.name == name)
  | .callable => p.functions.any (·.name == name) || p.maps.any (·.name == name)
  | .table => p.tables.any (·.name == name)

def simpleIdentifier (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun c => c.isAlphanum || c == '_') &&
    !(name.toList.head!.isDigit) && name != "Field"

def validate (p : Program α) : Except String Unit := do
  let names := p.modules.map (·.name) ++ p.signatures.map (·.name)
  if let some n := findDuplicate names [] then throw s!"duplicate module/signature '{n}'"
  for n in names do
    unless simpleIdentifier n do throw s!"invalid module/signature name '{n}'"
  for s in p.signatures do
    if let some n := findDuplicate s.names [] then throw s!"duplicate signature member '{n}'"
    for n in s.names do unless simpleIdentifier n do throw s!"invalid signature member '{n}'"
    for t in s.types do
      if t.isOpaque && t.definition.isSome then
        throw s!"opaque signature member '{s.name}::{t.name}' cannot expose a representation"
  for m in p.modules do
    if let some n := findDuplicate (m.parameters.map Prod.fst) [] then throw s!"duplicate module parameter '{n}'"
    for (n, sig) in m.parameters do
      unless simpleIdentifier n do throw s!"invalid module parameter '{n}'"
      if names.contains n then throw s!"module parameter '{n}' shadows a global module/signature"
      if (p.findSignature? sig).isNone then throw s!"unknown signature '{sig}'"
    if let some sig := m.signature then
      if (p.findSignature? sig).isNone then throw s!"unknown signature '{sig}'"
    if let .definitions d := m.body then
      if let some n := findDuplicate (memberNames d.program) [] then throw s!"duplicate member '{m.name}::{n}'"
      for n in memberNames d.program do
        unless simpleIdentifier n do throw s!"invalid module member '{n}'"
      if let some n := findDuplicate d.opaqueTypes [] then throw s!"duplicate opaque declaration '{n}'"
      for n in d.opaqueTypes do
        unless hasMember d.program .type n do throw s!"unknown opaque type '{m.name}::{n}'"

structure Item (α : Type) where
  key : Ref
  canonical : Ref
  decl : Module α
  bindings : Bindings
  target : Option Ref := none
  qualified : Option (Generic.Program α) := none
  constTypes : List (String × Generic.Ty) := []
  parameterPatterns : List (String × List (Generic.Pattern α)) := []
  deriving Inhabited

structure World (α : Type) where
  items : List (Item α) := []
  requirements : List (Ref × String) := []
  deriving Inhabited

abbrev Build (α : Type) := StateT (World α) (Except String)

def World.find? (w : World α) (key : Ref) := w.items.find? (·.key == key)

/-- Preserve an alias's interface for checking, but normalize argument identity
before memoizing an application. Contract obligations remember the supplied view. -/
def ensure (p : Program α) : Nat → Bindings → Ref → Build α Ref
  | 0, _, _ => throw "module expansion depth exceeded (possible cyclic alias)"
  | fuel + 1, bindings, ref => do
      if ref.args.isEmpty then
        if let some bound := bindings.lookup ref.name then return bound
      else if (bindings.lookup ref.name).isSome then throw "module parameters cannot be applied"
      let some decl := p.findModule? ref.name | throw s!"unknown module '{ref.name}'"
      if decl.parameters.length != ref.args.length then
        throw s!"module '{ref.name}' expects {decl.parameters.length} arguments"
      let actual ← ref.args.mapM (ensure p fuel bindings)
      for ((_, signature), argument) in decl.parameters.zip actual do
        modify fun w => { w with requirements := (argument, signature) :: w.requirements }
      let canonicalArgs ← actual.mapM fun arg => do return (← liftM (resolve p [] 128 arg)).value
      let key := Ref.mk ref.name canonicalArgs
      if ((← get).find? key).isSome then return key
      if (← get).items.length >= 512 then throw "module instance limit exceeded (512)"
      let canonical := (← liftM (resolve p [] 128 key)).value
      let bound := (decl.parameters.map Prod.fst).zip canonicalArgs
      let target ← match decl.body with
        | .definitions _ => pure none
        | .alias target => some <$> ensure p fuel bound target
      modify fun w => { w with items := w.items ++ [⟨key, canonical, decl, bound, target, none, [], []⟩] }
      return key

def getItem (key : Ref) : Build α (Item α) := do
  let some item := (← get).find? key | throw s!"missing module instance '{key.symbol}'"
  return item

/-- Access is checked against the supplied alias/interface before following it.
Inside a module its implementation members remain available. -/
def accessible (p : Program α) : Nat → Ref → Ref → Access → String → Build α Unit
  | 0, _, _, _, _ => throw "module alias depth exceeded"
  | fuel + 1, owner, target, access, name => do
      let item ← getItem target
      if owner != target then
        if let some sig := item.decl.signature then
          let some signature := p.findSignature? sig | throw s!"unknown signature '{sig}'"
          unless signature.exposes access name do throw s!"'{target.symbol}::{name}' is not exposed by signature '{sig}'"
          return
      match item.decl.body with
      | .definitions d =>
          unless hasMember d.program access name do throw s!"unknown {repr access} '{target.symbol}::{name}'"
          if owner != target && access == .constructor && d.opaqueTypes.contains name then
            throw s!"cannot access the representation of opaque type '{target.symbol}::{name}'"
      | .alias _ =>
          let some next := item.target | throw "missing alias target"
          accessible p fuel owner next access name

def locate (p : Program α) (owner : Ref) (bindings : Bindings) (path : String) : Build α (Ref × String) := do
  match splitPath path with
  | [name] => return (owner, name)
  | [head, name] =>
      let ref ← liftM (parseRef 128 head)
      if (p.findModule? ref.name).isNone && (bindings.lookup ref.name).isNone then
        throw s!"unknown module '{ref.name}'"
      return (← ensure p 128 bindings ref, name)
  | _ => throw s!"expected a module-qualified member, got '{path}'"

def qualify (p : Program α) (owner : Ref) (bindings : Bindings) (access : Access) (path : String) : Build α String := do
  let (target, name) ← locate p owner bindings path
  accessible p 128 owner target access name
  return rename target.symbol name

def qualifySignature (p : Program α) (item : Item α) (sig : Signature) : Build α Signature := do
  let q := qualify p item.key item.bindings
  -- Signature-local names are requirements, and need not occur in a malformed
  -- implementation. Their existence is checked by conformance, separately.
  let tyName := fun path =>
    match splitPath path with
    | [name] => pure (rename item.key.symbol name)
    | _ => q .type path
  let types ← sig.types.mapM fun t => do
    return { t with name := rename item.key.symbol t.name, definition := ← t.definition.mapM (retype tyName) }
  let consts ← sig.consts.mapM fun (n,t) => return (rename item.key.symbol n, ← retype tyName t)
  let tables ← sig.tables.mapM fun (n,t) => return (rename item.key.symbol n, ← retype tyName t)
  let functions ← sig.functions.mapM fun f => do
    return { f with
      name := rename item.key.symbol f.name
      params := ← f.params.mapM fun (n,t) => return (n, ← retype tyName t)
      result := ← retype tyName f.result }
  return { sig with types, consts, tables, functions }

def finish (p : Program α) : Nat → Build α Unit
  | 0 => throw "module dependency expansion limit exceeded"
  | fuel + 1 => do
      let some item := (← get).items.find? (fun i => i.qualified.isNone) | return
      -- Mark before walking dependencies: cross-module function recursion is legal.
      modify fun w => { w with items := w.items.map fun i =>
        if i.key == item.key then { i with qualified := some { functions := [] } } else i }
      if let .definitions d := item.decl.body then
        let q := qualify p item.key item.bindings
        let qualified ← rewrite item.key.symbol q d.program
        let constTypes ← d.constTypes.mapM fun (n,t) => return (rename item.key.symbol n, ← retype (q .type) t)
        let parameterPatterns ← d.parameterPatterns.mapM fun (n,ps) => do
          return (rename item.key.symbol n, ← ps.mapM (repattern q))
        modify fun w => { w with items := w.items.map fun i =>
          if i.key == item.key then { i with qualified := some qualified, constTypes, parameterPatterns } else i }
      if let some sig := item.decl.signature then
        let some signature := p.findSignature? sig | throw s!"unknown signature '{sig}'"
        let _ ← qualifySignature p item signature
      finish p fuel

def collect (p : Program α) (entries : List String) (seeds : List Ref := []) : Except String (World α × List (String × String)) := do
  let (selected, world) ← (do
    for seed in seeds do let _ ← ensure p 128 [] seed; pure ()
    for m in p.modules do
      if m.parameters.isEmpty then let _ ← ensure p 128 [] (.mk m.name []); pure ()
    if let some name := findDuplicate entries [] then throw s!"duplicate entrypoint '{name}'"
    let selected ← entries.mapM fun path => do
      let [head, name] := splitPath path | throw "entrypoints must be module-qualified"
      let target ← ensure p 128 [] (← liftM (parseRef 128 head))
      accessible p 128 (.mk "" []) target .callable name
      let item ← getItem target
      return (path, rename item.canonical.symbol name)
    finish p 1024
    return selected : Build α (List (String × String))).run {}
  return (world, selected)

end Aiur.Modules
