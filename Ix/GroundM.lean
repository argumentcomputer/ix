import Lean
import Ix.Common

namespace Ix

structure GroundEnv where
  env : Lean.Environment
  univCtx: List Lean.Name
  bindCtx: List Lean.Name
  current: Lean.Name

def GroundEnv.init (env: Lean.Environment): GroundEnv := ⟨env, {}, {}, default⟩

inductive GroundError where
| level (x : Lean.Level) (ctx: List Lean.Name)
| ref (x : Lean.Name)
| mvar (x : Lean.Expr)
| var (x : Lean.Expr) (ctx: List Lean.Name)
| indc (i: Lean.InductiveVal) (c: Option Lean.ConstantInfo)
deriving Inhabited, Repr, BEq, Hashable

structure GroundState where
  exprRefs: Map Lean.Expr (Set Lean.Name)
  outRefs : Map Lean.Name (Set Lean.Name)
  inRefs: Map Lean.Name (Set Lean.Name)
  ungrounded: Map Lean.Name GroundError
  exprCache : Map (List Lean.Name × List Lean.Name × Lean.Expr) (Set Lean.Name)
  univCache : Set (List Lean.Name × Lean.Level)

def GroundState.init : GroundState := ⟨{}, {}, {}, {}, {}, {}⟩

abbrev GroundM := ReaderT GroundEnv <| ExceptT GroundError <|  StateT GroundState IO

def GroundM.withCurrent (name: Lean.Name) : GroundM α -> GroundM α :=
  withReader $ fun c => { c with current := name }

-- add binding name to local context
def GroundM.withBinder (name: Lean.Name) : GroundM α -> GroundM α :=
  withReader $ fun c => { c with bindCtx := name :: c.bindCtx }

-- add levels to local context
def GroundM.withLevels (lvls : List Lean.Name) : GroundM α -> GroundM α :=
  withReader $ fun c => { c with univCtx := lvls }

def groundLevel (lvl: Lean.Level) : GroundM Unit := do
  let ctx := (<- read).univCtx
  match (<- get).univCache.contains (ctx, lvl) with
  | true => pure ()
  | false => do
    let _ <- go lvl
    modify fun stt => { stt with
      univCache := stt.univCache.insert (ctx, lvl)
    }
  where
    go : Lean.Level -> GroundM Unit
    | .zero => pure ()
    | .succ x => groundLevel x
    | .max x y => groundLevel x *> groundLevel y
    | .imax x y => groundLevel x *> groundLevel y
    | .param n => do
      let lvls := (<- read).univCtx
      match lvls.idxOf? n with
      | some _ => pure ()
      | none   => throw <| .level (.param n) lvls
    | l@(.mvar ..) => do throw <| .level l (<- read).univCtx

def addRef (current out: Lean.Name) : GroundM Unit := do
  modify fun stt => { stt with 
    outRefs := stt.outRefs.alter current fun x => match x with
      | .some rs => .some (rs.insert out)
      | .none => .some {out}
    inRefs := stt.inRefs.alter out fun x => match x with
      | .some rs => .some (rs.insert current)
      | .none => .some {current}
  }

def groundExpr (expr: Lean.Expr) : GroundM (Set Lean.Name) := do
  let key := ((<- read).univCtx, (<- read).bindCtx, expr)
  match (<- get).exprCache.find? key with
  | some x => pure x
  | none => do
    let refs <- go expr
    modifyGet fun stt => (refs, { stt with
      exprCache := stt.exprCache.insert key refs
    })
  where
    go : Lean.Expr -> GroundM (Set Lean.Name)
    | .mdata _ x => groundExpr x
    | .bvar idx => do
      let ctx := (<- read).bindCtx
      match ctx[idx]? with
      | .some _ => pure {}
      | .none => throw <| .var (.bvar idx) ctx
    | .sort lvl => groundLevel lvl *> pure {}
    | .const name lvls => do
      lvls.forM groundLevel
      match (<- read).env.constants.find? name with
      | .some _ => pure {name}
      | .none =>
        if name == .mkSimple "_obj"
        || name == .mkSimple "_neutral"
        || name == .mkSimple "_unreachable"
        then pure <| {name}
        else throw <| .ref name
    | .app f a => .union <$> groundExpr f <*> groundExpr a
    | .lam n t b _ => .union <$> groundExpr t <*> .withBinder n (groundExpr b)
    | .forallE n t b _ => .union <$> groundExpr t <*> .withBinder n (groundExpr b)
    | .letE n t v b _ => do
      let t' <- groundExpr t
      let v' <- groundExpr v
      let b' <- .withBinder n (groundExpr b)
      pure (.union t' (.union v' b'))
    | .proj typeName _ s => do
      let s' <- groundExpr s
      match (<- read).env.constants.find? typeName with
      | .some _ => addRef (<- read).current typeName *> pure s'
      | .none => throw (.ref typeName)
    | .lit _ => pure {}
    | x@(.mvar _) => throw <| .mvar x
    | x@(.fvar _) => do throw <| .var x (<- read).bindCtx

def groundConst: Lean.ConstantInfo -> GroundM (Set Lean.Name)
| .axiomInfo val => .withLevels val.levelParams <| groundExpr val.type
| .defnInfo val => .withLevels val.levelParams <|
  .union <$> groundExpr val.type <*> groundExpr val.value
| .thmInfo val => .withLevels val.levelParams <|
  .union <$> groundExpr val.type <*> groundExpr val.value
| .opaqueInfo val => .withLevels val.levelParams <|
  .union <$> groundExpr val.type <*> groundExpr val.value
| .quotInfo val => .withLevels val.levelParams <| groundExpr val.type
| .inductInfo val => .withLevels val.levelParams <| do
  let env := (<- read).env.constants
  let mut ctors := {}
  for ctor in val.ctors do
    let crefs <- match env.find? ctor with
    | .some (.ctorInfo ctorVal) => 
      .withLevels ctorVal.levelParams <| groundExpr ctorVal.type
    | c => throw <| .indc val c
    ctors := ctors.union crefs
  let type <- groundExpr val.type
  return .union ctors type
| .ctorInfo val => .withLevels val.levelParams <| groundExpr val.type
| .recInfo val => .withLevels val.levelParams <| do
  let t <- groundExpr val.type
  let rs <- val.rules.foldrM (fun r s => .union s <$> groundExpr r.rhs) {}
  return .union t rs

def groundEnv: GroundM Unit := do
  let mut stack := #[]
  for (n, c) in (<- read).env.constants do
    let refs <- observing (groundConst c)
    match refs with
    | .error e => do
      stack := stack.push n
      modify fun stt => { stt with
        ungrounded := stt.ungrounded.insert n e
        outRefs := stt.outRefs.alter n fun x => match x with
          | .some rs => .some rs
          | .none => .some {}
        inRefs := stt.inRefs.alter n fun x => match x with
          | .some rs => .some rs
          | .none => .some {}
      }
    | .ok refs => refs.toList.forM (fun r => addRef n r)
  while !stack.isEmpty do
    let name := stack.back!
    --dbg_trace s!"groundEnv stack {name}"
    stack := stack.pop
    let inRefs := match ((<- get).inRefs.get? name) with
    | .some x => x
    | .none => {}
    for ref in inRefs do
      --dbg_trace s!"groundEnv STACK {name} {ref}"
      match (<- get).ungrounded.get? ref with
      | .some _ => continue
      | .none => do
        stack := stack.push ref
        modify fun stt => { stt with
          ungrounded := stt.ungrounded.insert ref (.ref name)
        }

def GroundM.run (env: Lean.Environment) (g: GroundM α)
  : IO (Except GroundError α × GroundState)
  := (StateT.run (ExceptT.run (ReaderT.run g (GroundEnv.init env))) GroundState.init)

def GroundM.env (env: Lean.Environment) : IO GroundState := do
  let (_, stt) <- (GroundM.run env groundEnv)
  return stt

end Ix
