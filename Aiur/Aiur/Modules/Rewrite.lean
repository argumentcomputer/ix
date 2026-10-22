import Aiur.Modules.Resolution
import Aiur.Generic.Elaborate

namespace Aiur.Modules

inductive Access where
  | type | constructor | constant | callable | table
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Rebinding changes global names, never evaluation structure or local binders.
The callback is also used for visibility checks and dependency discovery. -/
def retype [Monad m] [LawfulMonad m] (name : String → m String) : Generic.Ty → m Generic.Ty
  | .field => pure .field
  | .param p => pure (.param p)
  | .ptr t => return .ptr (← retype name t)
  | .array t n => return .array (← retype name t) n
  | .tuple ts => return .tuple (← ts.attach.mapM (fun t => retype name t.val))
  | .named n ts => return .named (← name n) (← ts.attach.mapM (fun t => retype name t.val))
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem t.property; omega

/-- Constructibility concerns the outer type. An abstract type is still a
valid type argument to an exposed tuple/record/enum constructor. -/
def reConstructorType [Monad m] [LawfulMonad m] (name : Access → String → m String) : Generic.Ty → m Generic.Ty
  | .named n ts => return .named (← name .constructor n) (← ts.mapM (retype (name .type)))
  | t => retype (name .type) t

def rehead [Monad m] [LawfulMonad m] (name : Access → String → m String) (h : Generic.RecordHead) := do
  let t ← reConstructorType name h.type
  return { h with type := t }

def repattern [Monad m] [LawfulMonad m] (name : Access → String → m String) : Generic.Pattern α → m (Generic.Pattern α)
  | .literal x => pure (.literal x)
  | .wildcard => pure .wildcard
  | .bind n => pure (.bind n)
  | .global n t => return .global (← name .constant n) (← t.mapM (retype (name .type)))
  | .load p => return .load (← repattern name p)
  | .orElse p q bs => return .orElse (← repattern name p) (← repattern name q) bs
  | .tuple ps => return .tuple (← ps.attach.mapM (fun p => repattern name p.val))
  | .array ps => return .array (← ps.attach.mapM (fun p => repattern name p.val))
  | .repeat p n => return .repeat (← repattern name p) n
  | .record h ps => return .record (← rehead name h) (← ps.attach.mapM (fun p => repattern name p.val))
  | .construct t c ps => return .construct (← reConstructorType name t) c (← ps.attach.mapM (fun p => repattern name p.val))
  | .constructAs params t c ps =>
      return .constructAs params (← reConstructorType name t) c (← ps.attach.mapM (fun p => repattern name p.val))
termination_by p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem p.property; omega

def refield [Monad m] [LawfulMonad m] (name : Access → String → m String) (f : Generic.FieldRef) := do
  return { f with owner := ← f.owner.mapM (retype (name .type)) }

def restep [Monad m] [LawfulMonad m] (name : Access → String → m String) : Generic.UpdateStep → m Generic.UpdateStep
  | .member f => return .member (← refield name f)
  | .index i n => pure (.index i n)
  | .project i n => pure (.project i n)

def reexpr [Monad m] [LawfulMonad m] [MonadExceptOf String m] (name : Access → String → m String)
    (locals : List String) : Generic.Expr α → m (Generic.Expr α)
  | .literal x => pure (.literal x)
  | .var n => if locals.contains n then pure (.var n) else return .global (← name .constant n)
  | .global n t => return .global (← name .constant n) (← t.mapM (retype (name .type)))
  | .tuple xs => return .tuple (← xs.attach.mapM (fun x => reexpr name locals x.val))
  | .array xs => return .array (← xs.attach.mapM (fun x => reexpr name locals x.val))
  | .repeat x n => return .repeat (← reexpr name locals x) n
  | .index x n => return .index (← reexpr name locals x) n
  | .slice x a b => return .slice (← reexpr name locals x) a b
  | .construct n ts c xs =>
      return .construct (← name .constructor n)
        (← ts.mapM (List.mapM (retype (name .type)))) c (← xs.attach.mapM (fun x => reexpr name locals x.val))
  | .constructAs ps t c xs =>
      return .constructAs ps (← reConstructorType name t) c
        (← xs.attach.mapM (fun x => reexpr name locals x.val))
  | .record h xs => return .record (← rehead name h) (← xs.attach.mapM (fun x => reexpr name locals x.val))
  | .member x f => return .member (← reexpr name locals x) (← refield name f)
  | .update ps xs => return .update (← ps.mapM (List.mapM (restep name))) (← xs.attach.mapM (fun x => reexpr name locals x.val))
  | .builtin op xs => return .builtin (← op.mapTypesM (retype (name .type))) (← xs.attach.mapM (fun x => reexpr name locals x.val))
  | .project x n => return .project (← reexpr name locals x) n
  | .letValue p x b =>
      return .letValue (← repattern name p) (← reexpr name locals x)
        (← reexpr name (p.bindingNames ++ locals) b)
  | .store x => return .store (← reexpr name locals x)
  | .load x => return .load (← reexpr name locals x)
  | .hint t x channel => return .hint (← retype (name .type) t) (← reexpr name locals x) channel
  | .neg x => return .neg (← reexpr name locals x)
  | .binary op x y => return .binary op (← reexpr name locals x) (← reexpr name locals y)
  | .call n ts xs => do
      if locals.contains n then throw s!"local '{n}' is not callable; qualify the global function"
      return .call (← name .callable n) (← ts.mapM (List.mapM (retype (name .type))))
        (← xs.attach.mapM (fun x => reexpr name locals x.val))
  | .matchValue x arms =>
      return .matchValue (← reexpr name locals x)
        (← arms.attach.mapM fun arm => return (← repattern name arm.val.1, ← reexpr name (arm.val.1.bindingNames ++ locals) arm.val.2))
  | .control c x => return .control c (← reexpr name locals x)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem x.property; omega
    | have h := List.sizeOf_lt_of_mem arm.property
      rcases arm with ⟨⟨p,b⟩,mem⟩
      simp_all only [Prod.mk.sizeOf_spec]
      omega

def rename (owner name : String) := owner ++ "::" ++ name

def rewrite [Monad m] [LawfulMonad m] [MonadExceptOf String m] (owner : String)
    (name : Access → String → m String) (p : Generic.Program α) : m (Generic.Program α) := do
  let functions ← p.functions.mapM fun f => do
    return { f with
      name := rename owner f.name
      params := ← f.params.mapM fun (n,t) => return (n, ← retype (name .type) t)
      result := ← retype (name .type) f.result
      body := ← reexpr name (f.params.map Prod.fst) f.body }
  let enums ← p.enums.mapM fun d => do
    return { d with
      name := rename owner d.name
      constructors := ← d.constructors.mapM fun c => do
        return { c with fields := ← c.fields.mapM (retype (name .type)) } }
  let structs ← p.structs.mapM fun d => do
    return { d with
      name := rename owner d.name
      fields := ← d.fields.mapM fun (n,t) => return (n, ← retype (name .type) t) }
  let aliases ← p.aliases.mapM fun d => do
    return { d with
      name := rename owner d.name, target := ← retype (name .type) d.target }
  let consts ← p.consts.mapM fun d => do
    return { d with
      name := rename owner d.name, value := ← repattern name d.value }
  let tables ← p.tables.mapM fun d => do
    return { d with
      name := rename owner d.name, rowType := ← retype (name .type) d.rowType
      rows := ← d.rows.mapM (reexpr name []) }
  let maps ← p.maps.mapM fun d => do
    return { d with
      name := rename owner d.name
      params := ← d.params.mapM fun (n,t) => return (n, ← retype (name .type) t)
      result := ← retype (name .type) d.result
      input := ← name .table d.input, output := ← name .table d.output }
  return { functions, enums, structs, aliases, consts, tables, maps }

def append (p q : Generic.Program α) : Generic.Program α := {
  functions := p.functions ++ q.functions, enums := p.enums ++ q.enums
  structs := p.structs ++ q.structs, aliases := p.aliases ++ q.aliases
  consts := p.consts ++ q.consts, tables := p.tables ++ q.tables, maps := p.maps ++ q.maps }

end Aiur.Modules
