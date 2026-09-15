module

public import Ix.Kernel.Ingress

/-!
# Source-only conversion predictions

A conversion recipe records the finite interning operations performed by the
bounded production converters. Its prediction returns each proposed node
directly, keeping source resolution, sharing caches, universe normalization,
and errors independent of the checker's mutable intern tables.

The correspondence with production execution and the finite collision
conditions needed to use a prediction are proved in the consistency library.
This optional interface does not change production loading or admission.
-/

public section
@[expose] section

namespace Ix.Kernel

/-- An explicit description of a terminating conversion's intern effects. -/
inductive ConversionRecipe (α : Type) where
  | done (value : α)
  | fail (error : IngressErr)
  | internE (candidate : KExpr .anon) (next : KExpr .anon → ConversionRecipe α)
  | internU (candidate : KUniv .anon) (next : KUniv .anon → ConversionRecipe α)

namespace ConversionRecipe

def bind (recipe : ConversionRecipe α) (next : α → ConversionRecipe β) : ConversionRecipe β :=
  match recipe with
  | .done value => next value
  | .fail error => .fail error
  | .internE candidate rest => .internE candidate (fun value => bind (rest value) next)
  | .internU candidate rest => .internU candidate (fun value => bind (rest value) next)

instance : Monad ConversionRecipe where
  pure := .done
  bind := bind

def catchError (recipe : ConversionRecipe α) (handler : IngressErr → ConversionRecipe α) :
    ConversionRecipe α :=
  match recipe with
  | .done value => .done value
  | .fail error => handler error
  | .internE candidate rest => .internE candidate (fun value => catchError (rest value) handler)
  | .internU candidate rest => .internU candidate (fun value => catchError (rest value) handler)

instance : MonadExceptOf IngressErr ConversionRecipe where
  throw := .fail
  tryCatch := catchError

def emitExpr (term : KExpr .anon) : ConversionRecipe (KExpr .anon) := .internE term .done
def emitUniv (level : KUniv .anon) : ConversionRecipe (KUniv .anon) := .internU level .done

/-- Interpret the description using the actual production intern operations. -/
def run (recipe : ConversionRecipe α) : InternIngressM α :=
  match recipe with
  | .done value => pure value
  | .fail error => throw error
  | .internE candidate next => InternIngressM.internE candidate >>= fun value => run (next value)
  | .internU candidate next => InternIngressM.internU candidate >>= fun value => run (next value)

/-- Prediction consults no intern table. Every proposed node is kept exactly. -/
def predict (recipe : ConversionRecipe α) : Except IngressErr α :=
  match recipe with
  | .done value => .ok value
  | .fail error => .error error
  | .internE candidate next => predict (next candidate)
  | .internU candidate next => predict (next candidate)

/-- The finite expression candidates encountered along the predicted path. -/
def exprs (recipe : ConversionRecipe α) : List (KExpr .anon) :=
  match recipe with
  | .done _ | .fail _ => []
  | .internE candidate next => candidate :: exprs (next candidate)
  | .internU candidate next => exprs (next candidate)

/-- The finite universe candidates encountered along the predicted path. -/
def univs (recipe : ConversionRecipe α) : List (KUniv .anon) :=
  match recipe with
  | .done _ | .fail _ => []
  | .internE candidate next => univs (next candidate)
  | .internU candidate next => candidate :: univs (next candidate)

def univStep (stack : Array UFrame) (values : Array (KUniv .anon)) :
    ConversionRecipe (Array UFrame × Array (KUniv .anon)) := do
  let frame := stack.back!
  let mut stack := stack.pop
  let mut values := values
  match frame with
  | .process u =>
    match u with
    | .zero =>
      values := values.push (← emitUniv .mkZero)
    | .succ inner =>
      stack := stack.push .succ |>.push (.process inner)
    | .max a b =>
      stack := stack.push .max |>.push (.process b) |>.push (.process a)
    | .imax a b =>
      stack := stack.push .imax |>.push (.process b) |>.push (.process a)
    | .var idx =>
      values := values.push (← emitUniv (.mkParam idx ()))
  | .succ =>
    let inner := values.back!
    values := values.pop
    values := values.push (← emitUniv (.mkSucc inner))
  | .max =>
    let b := values.back!; values := values.pop
    let a := values.back!; values := values.pop
    values := values.push (← emitUniv (.mkMax a b))
  | .imax =>
    let b := values.back!; values := values.pop
    let a := values.back!; values := values.pop
    values := values.push (← emitUniv (.mkIMax a b))
  return (stack, values)

def univLoop (fuel : Nat) (stack : Array UFrame) (values : Array (KUniv .anon)) :
    ConversionRecipe (KUniv .anon) := do
  if stack.isEmpty then
    match values.back? with
    | some value => return value
    | none => throw "ingressUnivTree: empty result stack"
  else
    match fuel with
    | 0 => throw "ingressUnivTree: conversion step bound exhausted"
    | fuel + 1 =>
        let (stack, values) ← univStep stack values
        univLoop fuel stack values

def univTree (root : Ixon.Univ) : ConversionRecipe (KUniv .anon) :=
  univLoop (2 * univIngressSize root) #[.process root] #[]

def univIdx (ctx : IngressCtx) (idx : UInt64) :
    StateT ConvState ConversionRecipe (KUniv .anon) := do
  if let some cached := (← get).univCache[idx]? then
    return cached
  let some u := ctx.univs[idx.toNat]?
    | throw s!"invalid universe index {idx} (len {ctx.univs.size})"
  let ku ← liftM (univTree u)
  modify fun s => { s with univCache := s.univCache.insert idx ku }
  return ku

def univArgs (ctx : IngressCtx) (idxs : Array UInt64) :
    StateT ConvState ConversionRecipe (Array (KUniv .anon)) := do
  let mut out : Array (KUniv .anon) := Array.mkEmpty idxs.size
  for i in idxs do
    out := out.push (← univIdx ctx i)
  return out

def exprStep (ixonEnv : Ixon.Env) (ctx : IngressCtx)
    (stack : Array EFrame) (values : Array (KExpr .anon)) :
    StateT ConvState ConversionRecipe (Array EFrame × Array (KExpr .anon)) := do
  let frame := stack.back!
  let mut stack := stack.pop
  let mut values := values
  match frame with
  | .process e =>
    match e with
    | .share idx =>
      if let some cached := (← get).exprCache[idx]? then
        values := values.push cached
      else
        let some expansion := ctx.sharing[idx.toNat]?
          | throw s!"invalid Share index {idx}"
        stack := stack.push (.cacheShare idx) |>.push (.process expansion)
    | .var idx =>
      values := values.push (← liftM (emitExpr (.mkVar idx ())))
    | .sort uidx =>
      let u ← univIdx ctx uidx
      values := values.push (← liftM (emitExpr (.mkSort u)))
    | .ref refIdx univIdxs =>
      let some addr := ctx.refs[refIdx.toNat]?
        | throw s!"invalid Ref index {refIdx}"
      let univs ← univArgs ctx univIdxs
      values := values.push
        (← liftM (emitExpr (.mkConst ⟨addr, ()⟩ univs)))
    | .recur recIdx univIdxs =>
      let some mid := ctx.mutCtx[recIdx.toNat]?
        | throw s!"invalid Rec index {recIdx}"
      let univs ← univArgs ctx univIdxs
      values := values.push
        (← liftM (emitExpr (.mkConst mid univs)))
    | .nat blobIdx =>
      let some blobAddr := ctx.refs[blobIdx.toNat]?
        | throw s!"invalid Nat blob ref index {blobIdx}"
      let some bytes := ixonEnv.getBlob? blobAddr
        | throw s!"missing Nat blob {blobAddr}"
      let val := Nat.fromBytesLE bytes.data
      values := values.push
        (← liftM (emitExpr (.mkNat val blobAddr)))
    | .str blobIdx =>
      let some blobAddr := ctx.refs[blobIdx.toNat]?
        | throw s!"invalid Str blob ref index {blobIdx}"
      let some bytes := ixonEnv.getBlob? blobAddr
        | throw s!"missing Str blob {blobAddr}"
      let some val := String.fromUTF8? bytes
        | throw s!"Str blob {blobAddr} is not valid UTF-8"
      values := values.push
        (← liftM (emitExpr (.mkStr val blobAddr)))
    | .app f a =>
      stack := stack.push .appDone |>.push (.process a) |>.push (.process f)
    | .lam _ ty body =>
      stack := stack.push .lamDone |>.push (.process body)
        |>.push (.process ty)
    | .all _ _ ty body =>
      stack := stack.push .allDone |>.push (.process body)
        |>.push (.process ty)
    | .letE nd ty val body =>
      stack := stack.push (.letDone nd) |>.push (.process body)
        |>.push (.process val) |>.push (.process ty)
    | .prj typeRefIdx field val =>
      let some typeAddr := ctx.refs[typeRefIdx.toNat]?
        | throw s!"invalid Prj type ref index {typeRefIdx}"
      stack := stack.push (.prjDone ⟨typeAddr, ()⟩ field)
        |>.push (.process val)
  | .appDone =>
    let a := values.back!; values := values.pop
    let f := values.back!; values := values.pop
    values := values.push (← liftM (emitExpr (.mkApp f a)))
  | .lamDone =>
    let body := values.back!; values := values.pop
    let ty := values.back!; values := values.pop
    values := values.push
      (← liftM (emitExpr (.mkLam () () ty body)))
  | .allDone =>
    let body := values.back!; values := values.pop
    let ty := values.back!; values := values.pop
    values := values.push
      (← liftM (emitExpr (.mkAll () () ty body)))
  | .letDone nd =>
    let body := values.back!; values := values.pop
    let val := values.back!; values := values.pop
    let ty := values.back!; values := values.pop
    values := values.push
      (← liftM (emitExpr (.mkLet () ty val body nd)))
  | .prjDone id field =>
    let val := values.back!; values := values.pop
    values := values.push
      (← liftM (emitExpr (.mkPrj id field val)))
  | .cacheShare idx =>
    let v := values.back!
    modify fun s => { s with exprCache := s.exprCache.insert idx v }
  return (stack, values)

def exprLoop (ixonEnv : Ixon.Env) (ctx : IngressCtx) (fuel : Nat)
    (stack : Array EFrame) (values : Array (KExpr .anon)) : StateT ConvState ConversionRecipe (KExpr .anon) := do
  if stack.isEmpty then
    match values.back? with
    | some value =>
        if values.size != 1 then
          throw s!"ingressExpr: unbalanced value stack ({values.size} values)"
        return value
    | none => throw "ingressExpr: empty result stack"
  else
    match fuel with
    | 0 => throw "ingressExpr: conversion step bound exhausted"
    | fuel + 1 =>
        let (stack, values) ← exprStep ixonEnv ctx stack values
        exprLoop ixonEnv ctx fuel stack values

def expr (ixonEnv : Ixon.Env) (ctx : IngressCtx) (root : Ixon.Expr) :
    StateT ConvState ConversionRecipe (KExpr .anon) :=
  exprLoop ixonEnv ctx (2 * exprIngressSize (root :: ctx.sharing.toList))
    #[.process root] #[]

def defn (ixonEnv : Ixon.Env) (defn : Ixon.Definition)
    (constant : Ixon.Constant) (block : KId .anon)
    (mutCtx : Array (KId .anon)) (hintsOverride : Option Lean.ReducibilityHints) :
    ConversionRecipe (KConst .anon) := do
  let ctx : IngressCtx :=
    { sharing := constant.sharing, refs := constant.refs
      univs := constant.univs, mutCtx }
  let (ty, st) ← (expr ixonEnv ctx defn.typ).run {}
  let (val, _) ← (expr ixonEnv ctx defn.value).run st
  let hints := hintsOverride.getD (.regular 0)
  return .defn () () defn.kind defn.safety hints defn.lvls ty val () block

def recursor (ixonEnv : Ixon.Env) (rec : Ixon.Recursor)
    (constant : Ixon.Constant) (block : KId .anon)
    (mutCtx : Array (KId .anon)) : ConversionRecipe (KConst .anon) := do
  let ctx : IngressCtx :=
    { sharing := constant.sharing, refs := constant.refs
      univs := constant.univs, mutCtx }
  let (ty, st) ← (expr ixonEnv ctx rec.typ).run {}
  let mut st := st
  let mut rules : Array (RecRule .anon) := Array.mkEmpty rec.rules.size
  for rule in rec.rules do
    let (rhs, st') ← (expr ixonEnv ctx rule.rhs).run st
    st := st'
    rules := rules.push { ctor := (), fields := rule.fields, rhs }
  return .recr () () rec.k rec.isUnsafe rec.lvls rec.params rec.indices
    rec.motives rec.minors block 0 ty rules ()

def standalone (ixonEnv : Ixon.Env) (addr : Address)
    (constant : Ixon.Constant) : ConversionRecipe (KConst .anon) := do
  let selfId : KId .anon := ⟨addr, ()⟩
  let hintsOverride := ixonEnv.anonHints[addr]?
  match constant.info with
    | .defn d =>
      defn ixonEnv d constant selfId #[selfId] hintsOverride
    | .recr r =>
      recursor ixonEnv r constant selfId #[selfId]
    | .axio a => do
      let ctx : IngressCtx :=
        { sharing := constant.sharing, refs := constant.refs
          univs := constant.univs, mutCtx := #[] }
      let (ty, _) ← (expr ixonEnv ctx a.typ).run {}
      pure (.axio () () a.isUnsafe a.lvls ty)
    | .quot q => do
      let ctx : IngressCtx :=
        { sharing := constant.sharing, refs := constant.refs
          univs := constant.univs, mutCtx := #[] }
      let (ty, _) ← (expr ixonEnv ctx q.typ).run {}
      pure (.quot () () q.kind q.lvls ty)
    | _ =>
      throw s!"ingressAnonStandalone: {addr} is a projection or Muts block, not a standalone"

end ConversionRecipe

/-- A verified standalone declaration predicted using only its source. Blocks
and projections have no entry in this standalone catalog. Parse, integrity,
and conversion errors remain explicit. -/
def predictStandalone? (source : Ixon.Env) (addr : Address) :
    Except IngressErr (Option (KConst .anon)) := do
  let some constant ← getConstVerified source addr true | return none
  match ingressBlockAddr? addr constant.info with
  | some _ => return none
  | none => return some (← (ConversionRecipe.standalone source addr constant).predict)

end Ix.Kernel

end
end
