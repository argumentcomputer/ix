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

inductive Grounding where
| grounded
| ungrounded (xs: Set GroundError)
deriving Inhabited, Repr

def Grounding.add : Grounding -> Grounding -> Grounding
| .grounded, .grounded => .grounded
| .grounded, x => x
| x, .grounded => x
| .ungrounded xs, .ungrounded ys => .ungrounded (.union xs ys)

structure GroundState where
  exprRefs: Map Lean.Expr (Set Lean.Name)
  outRefs : Map Lean.Name (Set Lean.Name)
  inRefs: Map Lean.Name (Set Lean.Name)
  ungrounded: Map Lean.Name Grounding
  constCache : Map Lean.Name Grounding
  exprCache : Map (List Lean.Name × List Lean.Name × Lean.Expr) Grounding
  univCache : Map (List Lean.Name × Lean.Level) Grounding

def GroundState.init : GroundState := ⟨{}, {}, {}, {}, {}, {}, {}⟩

abbrev GroundM := ReaderT GroundEnv <| StateT GroundState IO

def GroundM.withCurrent (name: Lean.Name) : GroundM α -> GroundM α :=
  withReader $ fun c => { c with current := name }

-- add binding name to local context
def GroundM.withBinder (name: Lean.Name) : GroundM α -> GroundM α :=
  withReader $ fun c => { c with bindCtx := name :: c.bindCtx }

-- add levels to local context
def GroundM.withLevels (lvls : List Lean.Name) : GroundM α -> GroundM α :=
  withReader $ fun c => { c with univCtx := lvls }

def groundLevel (lvl: Lean.Level) : GroundM Grounding := do
  let ctx := (<- read).univCtx
  match (<- get).univCache.find? (ctx, lvl) with
  | some l => pure l
  | none => do
    let grounding <- go lvl
    modifyGet fun stt => (grounding, { stt with
      univCache := stt.univCache.insert (ctx, lvl) grounding
    })
  where
    go : Lean.Level -> GroundM Grounding
    | .zero => pure .grounded
    | .succ x => groundLevel x
    | .max x y => .add <$> groundLevel x <*> groundLevel y
    | .imax x y => .add <$> groundLevel x <*> groundLevel y
    | .param n => do
      let lvls := (<- read).univCtx
      match lvls.idxOf? n with
      | some _ => pure .grounded
      | none   => pure <| .ungrounded {.level (.param n) lvls}
    | l@(.mvar ..) => do pure <| .ungrounded {.level l (<- read).univCtx}

def addRef (current out: Lean.Name) : GroundM Unit := do
  modify fun stt => { stt with 
    outRefs := stt.outRefs.alter current fun x => match x with
      | .some rs => .some (rs.insert out)
      | .none => .some {out}
    inRefs := stt.inRefs.alter out fun x => match x with
      | .some rs => .some (rs.insert current)
      | .none => .some {current}
  }

mutual
def groundExpr (expr: Lean.Expr) : GroundM Grounding := do
  let key := ((<- read).univCtx, (<- read).bindCtx, expr)
  match (<- get).exprCache.find? key with
  | some l => pure l
  | none => do
    let grounding <- go expr
    modifyGet fun stt => (grounding, { stt with
      exprCache := stt.exprCache.insert key grounding
    })
  where
    go : Lean.Expr -> GroundM Grounding
    | .mdata _ x => groundExpr x
    | .bvar idx => do
      let ctx := (<- read).bindCtx
      match ctx[idx]? with
      | .some _ => pure .grounded
      | .none => pure <| .ungrounded {.var (.bvar idx) ctx}
    | .sort lvl => groundLevel lvl
    | .const name lvls => do
      let ls <- lvls.foldrM (fun l g => .add g <$> groundLevel l) .grounded
      match (<- read).env.constants.find? name with
      | .some _ => addRef (<- read).current name *> pure ls
      | .none =>
        if name == .mkSimple "_obj"
        || name == .mkSimple "_neutral"
        || name == .mkSimple "_unreachable"
        then pure <| .grounded
        else pure <| .add ls (.ungrounded {.ref name})
    | .app f a => .add <$> groundExpr f <*> groundExpr a
    | .lam n t b _ => .add <$> groundExpr t <*> .withBinder n (groundExpr b)
    | .forallE n t b _ => .add <$> groundExpr t <*> .withBinder n (groundExpr b)
    | .letE n t v b _ => do
      let t' <- groundExpr t
      let v' <- groundExpr v
      let b' <- .withBinder n (groundExpr b)
      pure (.add t' (.add v' b'))
    | .proj typeName _ s => do
      let s' <- groundExpr s
      match (<- read).env.constants.find? typeName with
      | .some _ => addRef (<- read).current typeName *> pure s'
      | .none => pure <| .add s' (.ungrounded {.ref typeName})
    | .lit _ => pure .grounded
    | x@(.mvar _) => pure <| .ungrounded {.mvar x}
    | x@(.fvar _) => do pure <| .ungrounded {.var x (<- read).bindCtx}

def groundConst (const: Lean.ConstantInfo) : GroundM Grounding := do
  match (<- get).constCache.find? const.name with
  | some g => pure g
  | none => do
    let grounding <- .withCurrent const.name <| go const
    modifyGet fun stt => (grounding, { stt with
      constCache := stt.constCache.insert const.name grounding
    })
  where
    go : Lean.ConstantInfo -> GroundM Grounding
    | .axiomInfo val => .withLevels val.levelParams <| groundExpr val.type
    | .defnInfo val => .withLevels val.levelParams <|
      .add <$> groundExpr val.type <*> groundExpr val.value
    | .thmInfo val => .withLevels val.levelParams <|
      .add <$> groundExpr val.type <*> groundExpr val.value
    | .opaqueInfo val => .withLevels val.levelParams <|
      .add <$> groundExpr val.type <*> groundExpr val.value
    | .quotInfo val => .withLevels val.levelParams <| groundExpr val.type
    | .inductInfo val => .withLevels val.levelParams <| do
      let env := (<- read).env.constants
      let mut ctors := .grounded
      for ctor in val.ctors do
        let g <- match env.find? ctor with
        | .some (.ctorInfo ctorVal) => .withLevels ctorVal.levelParams <| do
          addRef val.name ctor *> groundExpr ctorVal.type
        | c => pure <| .ungrounded {.indc val c}
        ctors := .add ctors g
      let type <- groundExpr val.type
      return .add ctors type
    | .ctorInfo val => .withLevels val.levelParams <| groundExpr val.type
    | .recInfo val => .withLevels val.levelParams <| do
      let t <- groundExpr val.type
      let rs <- val.rules.foldrM (fun r s => .add s <$> groundExpr r.rhs) .grounded
      return .add t rs
end

def groundEnv: GroundM Unit := do
  let mut stack := #[]
  for (n, c) in (<- read).env.constants do
    --dbg_trace s!"groundEnv {n}"
    modify fun stt => { stt with
      outRefs := stt.outRefs.alter n fun x => match x with
      | .none => .some {}
      | x => x
      inRefs := stt.inRefs.alter n fun x => match x with
      | .none => .some {}
      | x => x
    }
    match (<- groundConst c) with
    | .grounded => continue
    | u@(.ungrounded _) => 
      dbg_trace s!"groundEnv UNGROUNDED {n} {repr u}"
      stack := stack.push n
      modify fun stt => { stt with
        ungrounded := stt.ungrounded.insert n u
      }
  while !stack.isEmpty do
    let name := stack.back!
    --dbg_trace s!"groundEnv stack {name}"
    stack := stack.pop
    let inRefs := match ((<- get).inRefs.get? name) with
    | .some x => x
    | .none => {}
    for ref in inRefs do
      dbg_trace s!"groundEnv STACK {name} {ref}"
      match (<- get).ungrounded.get? ref with
      | .some u =>
        modify fun stt => { stt with
          ungrounded := stt.ungrounded.insert ref (.add (.ungrounded {.ref name}) u)
        }
      | .none => do
        stack := stack.push ref
        modify fun stt => { stt with
          ungrounded := stt.ungrounded.insert ref (.ungrounded {.ref name})
        }

def GroundM.run (env: Lean.Environment) (g: GroundM α): IO (α × GroundState)
  := (StateT.run (ReaderT.run g (.init env)) GroundState.init)

def GroundM.env (env: Lean.Environment) : IO GroundState := do
  let (_, stt) <- (GroundM.run env groundEnv)
  return stt

end Ix
