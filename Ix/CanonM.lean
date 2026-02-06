/-
  # CanonM: Canonicalize Lean types to Ix types with content-addressed hashing

  Converts Lean kernel types (Name, Level, Expr, ConstantInfo) to their Ix
  counterparts, embedding blake3 hashes at each node for O(1) structural equality.

  Uses pointer-based caching (`ptrAddrUnsafe`) to avoid recomputing hashes for
  shared subterms — if two Lean values share the same pointer, they map to the
  same canonical Ix value.

  Key operations:
  - `canonName` / `uncanonName`: Lean.Name <-> Ix.Name
  - `canonLevel` / `uncanonLevel`: Lean.Level <-> Ix.Level
  - `canonExpr` / `uncanonExpr`: Lean.Expr <-> Ix.Expr
  - `canonEnv` / `uncanonEnv`: whole-environment conversion
  - `compareEnvsParallel`: parallel structural equality check between environments
-/

import Lean
import Blake3
import Std.Data.HashMap
import Ix.Common
import Ix.Environment
import Ix.Address

namespace Ix.CanonM

open Std (HashMap)

@[inline] def leanExprPtr (e : Lean.Expr) : USize := unsafe ptrAddrUnsafe e
@[inline] def leanNamePtr (n : Lean.Name) : USize := unsafe ptrAddrUnsafe n
@[inline] def leanLevelPtr (l : Lean.Level) : USize := unsafe ptrAddrUnsafe l
@[inline] def leanDataValuePtr (d : Lean.DataValue) : USize := unsafe ptrAddrUnsafe d

structure CanonState where
  namePtrAddrs: HashMap USize Address := {}
  names: HashMap Address Ix.Name := {}
  levelPtrAddrs: HashMap USize Address := {}
  levels: HashMap Address Ix.Level := {}
  exprPtrAddrs: HashMap USize Address := {}
  exprs: HashMap Address Ix.Expr := {}
  dataValuePtrAddrs: HashMap USize Address := {}
  dataValues: HashMap Address Ix.DataValue := {}

abbrev CanonM := StateT CanonState Id

def internName (ptr: USize) (y : Ix.Name) : CanonM Unit := do
  let h := y.getHash
  modify fun s => { s with
    names := s.names.insertIfNew h y
    namePtrAddrs := s.namePtrAddrs.insertIfNew ptr h
  }

def internLevel (ptr: USize) (y : Ix.Level) : CanonM Unit := do
  let h := y.getHash
  modify fun s => { s with
    levels := s.levels.insertIfNew h y
    levelPtrAddrs := s.levelPtrAddrs.insertIfNew ptr h
  }

def internExpr (ptr: USize) (y : Ix.Expr) : CanonM Unit := do
  let h := y.getHash
  modify fun s => { s with
    exprs := s.exprs.insertIfNew h y
    exprPtrAddrs := s.exprPtrAddrs.insertIfNew ptr h
  }

def internDataValue (ptr: USize) (y : Ix.DataValue) : CanonM Unit := do
  let mut h := Blake3.Hasher.init ()
  h := Ix.Expr.hashDataValue h y
  let h' := ⟨(h.finalizeWithLength 32).val⟩
  modify fun s => { s with
    dataValues := s.dataValues.insertIfNew h' y
    dataValuePtrAddrs := s.dataValuePtrAddrs.insertIfNew ptr h'
  }

def canonName (n: Lean.Name) : CanonM Ix.Name := do
  let ptr := leanNamePtr n
  let s ← get
  if let .some val := s.namePtrAddrs.get? ptr |>.bind s.names.get? then return val
  else
    let n' ← match n with
      | .anonymous => pure .mkAnon
      | .str pre str => .mkStr <$> canonName pre <*> pure str
      | .num pre num => .mkNat <$> canonName pre <*> pure num
    internName ptr n'
    pure n'

def canonLevel (l: Lean.Level) : CanonM Ix.Level := do
  let ptr := leanLevelPtr l
  let s ← get
  if let .some val := s.levelPtrAddrs.get? ptr |>.bind s.levels.get? then return val
  else
    let l' ← match l with
      | .zero => pure .mkZero
      | .succ x => .mkSucc <$> canonLevel x
      | .max x y => .mkMax <$> canonLevel x <*> canonLevel y
      | .imax x y => .mkIMax <$> canonLevel x <*> canonLevel y
      | .param n => .mkParam <$> canonName n
      | .mvar n => .mkMvar <$> canonName n.name
    internLevel ptr l'
    pure l'

def canonInt : _root_.Int → Ix.Int
  | .ofNat n => .ofNat n
  | .negSucc n => .negSucc n

def canonSubstring (ss : _root_.Substring.Raw) : Ix.Substring :=
  { str := ss.str, startPos := ss.startPos.byteIdx, stopPos := ss.stopPos.byteIdx }

def canonSourceInfo : Lean.SourceInfo → Ix.SourceInfo
  | .original leading pos trailing endPos =>
    .original (canonSubstring leading) pos.byteIdx
      (canonSubstring trailing) endPos.byteIdx
  | .synthetic pos endPos canonical => .synthetic pos.byteIdx endPos.byteIdx canonical
  | .none => .none

def canonSyntaxPreresolved (sp : Lean.Syntax.Preresolved) : CanonM Ix.SyntaxPreresolved :=
  match sp with
  | .namespace name => .namespace <$> canonName name
  | .decl name aliases => .decl <$> canonName name <*> pure aliases.toArray

partial def canonSyntax : Lean.Syntax → CanonM Ix.Syntax
  | .missing => pure .missing
  | .node info kind args => do
    .node (canonSourceInfo info) <$> canonName kind <*> args.mapM canonSyntax
  | .atom info val => pure <| .atom (canonSourceInfo info) val
  | .ident info rawVal val preresolved => do
    .ident (canonSourceInfo info) (canonSubstring rawVal)
      <$> canonName val <*> preresolved.toArray.mapM canonSyntaxPreresolved

def canonDataValue (d: Lean.DataValue): CanonM Ix.DataValue := do
  let ptr := leanDataValuePtr d
  let s ← get
  if let .some val := s.dataValuePtrAddrs.get? ptr |>.bind s.dataValues.get? then return val
  let d' ← match d with
  | .ofString s => pure <| .ofString s
  | .ofBool b => pure <| .ofBool b
  | .ofName n => .ofName <$> canonName n
  | .ofNat n => pure <| .ofNat n
  | .ofInt i => pure <| .ofInt (canonInt i)
  | .ofSyntax s => .ofSyntax <$> canonSyntax s
  internDataValue ptr d'
  pure d'

def canonMData (md : Lean.MData) : CanonM (Array (Ix.Name × Ix.DataValue)) := do
  let mut result := #[]
  for (name, value) in md do
    let name' <- canonName name
    let value' <- canonDataValue value
    result := result.push (name', value')
  pure result

def canonExpr (e: Lean.Expr) : CanonM Ix.Expr := do
  let ptr := leanExprPtr e
  let s ← get
  if let .some val := s.exprPtrAddrs.get? ptr |>.bind s.exprs.get? then return val
  else
    let e' ← match e with
      | .bvar idx => pure (.mkBVar idx)
      | .fvar fvarId => .mkFVar <$> canonName fvarId.name
      | .mvar mvarId => .mkMVar <$> canonName mvarId.name
      | .sort level => .mkSort <$> canonLevel level
      | .const name levels =>
        .mkConst <$> canonName name <*> levels.toArray.mapM canonLevel
      | .app fn arg => .mkApp <$> canonExpr fn <*> canonExpr arg
      | .lam name ty body bi =>
        .mkLam <$> canonName name
          <*> canonExpr ty <*> canonExpr body <*> pure bi
      | .forallE name ty body bi =>
        .mkForallE <$> canonName name
          <*> canonExpr ty <*> canonExpr body <*> pure bi
      | .letE name ty val body nonDep =>
        .mkLetE <$> canonName name
          <*> canonExpr ty <*> canonExpr val
          <*> canonExpr body <*> pure nonDep
      | .lit l => pure (.mkLit l)
      | .mdata md expr => .mkMData <$> canonMData md <*> canonExpr expr
      | .proj typeName idx struct =>
        .mkProj <$> canonName typeName <*> pure idx <*> canonExpr struct
    internExpr ptr e'
    pure e'

def canonConstantVal (cv : Lean.ConstantVal) : CanonM Ix.ConstantVal := do
  pure {
    name := (<- canonName cv.name)
    levelParams := (<- cv.levelParams.toArray.mapM canonName)
    type := (<- canonExpr cv.type)
  }

def canonRecursorRule (r : Lean.RecursorRule) : CanonM Ix.RecursorRule := do
  pure {
    ctor := (<- canonName r.ctor)
    nfields := r.nfields
    rhs := (<- canonExpr r.rhs)
  }

def canonConst : Lean.ConstantInfo → CanonM Ix.ConstantInfo
  | .axiomInfo v => do
    pure <| .axiomInfo {
      cnst := (<- canonConstantVal v.toConstantVal)
      isUnsafe := v.isUnsafe
    }
  | .defnInfo v => do
    pure <| .defnInfo {
      cnst := (<- canonConstantVal v.toConstantVal)
      value := (<- canonExpr v.value)
      hints := v.hints
      safety := v.safety
      all := (<- v.all.toArray.mapM canonName)
    }
  | .thmInfo v => do
    pure <| .thmInfo {
      cnst := (<- canonConstantVal v.toConstantVal)
      value := (<- canonExpr v.value)
      all := (<- v.all.toArray.mapM canonName)
    }
  | .opaqueInfo v => do
    pure <| .opaqueInfo {
      cnst := (<- canonConstantVal v.toConstantVal)
      value := (<- canonExpr v.value)
      isUnsafe := v.isUnsafe
      all := (<- v.all.toArray.mapM canonName)
    }
  | .quotInfo v => do
    pure <| .quotInfo {
      cnst := (<- canonConstantVal v.toConstantVal)
      kind := v.kind
    }
  | .inductInfo v => do
    pure <| .inductInfo {
      cnst := (<- canonConstantVal v.toConstantVal)
      numParams := v.numParams
      numIndices := v.numIndices
      all := (<- v.all.toArray.mapM canonName)
      ctors := (<- v.ctors.toArray.mapM canonName)
      numNested := v.numNested
      isRec := v.isRec
      isUnsafe := v.isUnsafe
      isReflexive := v.isReflexive
    }
  | .ctorInfo v => do
    pure <| .ctorInfo {
      cnst := (<- canonConstantVal v.toConstantVal)
      induct := (<- canonName v.induct)
      cidx := v.cidx
      numParams := v.numParams
      numFields := v.numFields
      isUnsafe := v.isUnsafe
    }
  | .recInfo v => do
    pure <| .recInfo {
      cnst := (<- canonConstantVal v.toConstantVal)
      all := (<- v.all.toArray.mapM canonName)
      numParams := v.numParams
      numIndices := v.numIndices
      numMotives := v.numMotives
      numMinors := v.numMinors
      rules := (<- v.rules.toArray.mapM canonRecursorRule)
      k := v.k
      isUnsafe := v.isUnsafe
    }

structure UncanonState where
  names: HashMap Address Lean.Name := {}
  levels: HashMap Address Lean.Level := {}
  exprs: HashMap Address Lean.Expr := {}

abbrev UncanonM := StateT UncanonState Id

def uncanonName (n: Ix.Name) : UncanonM Lean.Name := do
  let addr := n.getHash
  match (← get).names.get? addr with
  | .some cached => pure cached
  | .none =>
    let result ← match n with
      | .anonymous _ => pure .anonymous
      | .str pre str _ => .str <$> uncanonName pre <*> pure str
      | .num pre num _ => .num <$> uncanonName pre <*> pure num
    modify fun s => { s with names := s.names.insert addr result }
    pure result

def uncanonLevel (l: Ix.Level) : UncanonM Lean.Level := do
  let addr := l.getHash
  match (← get).levels.get? addr with
  | .some cached => pure cached
  | .none =>
    let result ← match l with
      | .zero _ => pure .zero
      | .succ x _ => .succ <$> uncanonLevel x
      | .max x y _ => .max <$> uncanonLevel x <*> uncanonLevel y
      | .imax x y _ => .imax <$> uncanonLevel x <*> uncanonLevel y
      | .param n _ => .param <$> uncanonName n
      | .mvar n _ => Lean.Level.mvar <$> .mk <$> uncanonName n
    modify fun s => { s with levels := s.levels.insert addr result }
    pure result

def uncanonInt : Ix.Int → _root_.Int
  | .ofNat n => .ofNat n
  | .negSucc n => .negSucc n

def uncanonSubstring (ss : Ix.Substring) : _root_.Substring.Raw :=
  { str := ss.str, startPos := ⟨ss.startPos⟩, stopPos := ⟨ss.stopPos⟩ }

def uncanonSourceInfo : Ix.SourceInfo → Lean.SourceInfo
  | .original leading leadingPos trailing trailingPos =>
    .original (uncanonSubstring leading) ⟨leadingPos⟩
      (uncanonSubstring trailing) ⟨trailingPos⟩
  | .synthetic start stop canonical => .synthetic ⟨start⟩ ⟨stop⟩ canonical
  | .none => .none

def uncanonSyntaxPreresolved (sp : Ix.SyntaxPreresolved)
    : UncanonM Lean.Syntax.Preresolved :=
  match sp with
  | .namespace name => .namespace <$> uncanonName name
  | .decl name aliases => .decl <$> uncanonName name <*> pure aliases.toList

partial def uncanonSyntax : Ix.Syntax → UncanonM Lean.Syntax
  | .missing => pure .missing
  | .node info kind args => do
    .node (uncanonSourceInfo info) <$> uncanonName kind <*> args.mapM uncanonSyntax
  | .atom info val => pure <| .atom (uncanonSourceInfo info) val
  | .ident info rawVal val preresolved => do
    .ident (uncanonSourceInfo info) (uncanonSubstring rawVal)
      <$> uncanonName val <*> (preresolved.mapM uncanonSyntaxPreresolved >>= pure ∘ Array.toList)

def uncanonDataValue : Ix.DataValue → UncanonM Lean.DataValue
  | .ofString s => pure <| .ofString s
  | .ofBool b => pure <| .ofBool b
  | .ofName n => .ofName <$> uncanonName n
  | .ofNat n => pure <| .ofNat n
  | .ofInt i => pure <| .ofInt (uncanonInt i)
  | .ofSyntax s => .ofSyntax <$> uncanonSyntax s

def uncanonMData (data : Array (Ix.Name × Ix.DataValue)) : UncanonM Lean.MData := do
  let mut result : Lean.MData := {}
  for (name, value) in data do
    let name' <- uncanonName name
    let value' <- uncanonDataValue value
    result := result.insert name' value'
  pure result

def uncanonExpr (e: Ix.Expr) : UncanonM Lean.Expr := do
  let addr := e.getHash
  match (← get).exprs.get? addr with
  | .some cached => pure cached
  | .none =>
    let result ← match e with
      | .bvar idx _ => pure (.bvar idx)
      | .fvar name _ =>
        Lean.Expr.fvar <$> (.mk <$> uncanonName name)
      | .mvar name _ =>
        Lean.Expr.mvar <$> (.mk <$> uncanonName name)
      | .sort level _ => .sort <$> uncanonLevel level
      | .const name levels _ =>
        .const <$> uncanonName name <*> levels.toList.mapM uncanonLevel
      | .app fn arg _ => .app <$> uncanonExpr fn <*> uncanonExpr arg
      | .lam name ty body bi _ =>
        .lam <$> uncanonName name
          <*> uncanonExpr ty <*> uncanonExpr body <*> pure bi
      | .forallE name ty body bi _ =>
        .forallE <$> uncanonName name
          <*> uncanonExpr ty <*> uncanonExpr body <*> pure bi
      | .letE name ty val body nonDep _ =>
        .letE <$> uncanonName name
          <*> uncanonExpr ty <*> uncanonExpr val
          <*> uncanonExpr body <*> pure nonDep
      | .lit l _ => pure (.lit l)
      | .mdata data expr _ => .mdata <$> uncanonMData data <*> uncanonExpr expr
      | .proj typeName idx struct _ =>
        .proj <$> uncanonName typeName <*> pure idx <*> uncanonExpr struct
    modify fun s => { s with exprs := s.exprs.insert addr result }
    pure result

def uncanonConstantVal (cv : Ix.ConstantVal) : UncanonM Lean.ConstantVal := do
  pure {
    name := (<- uncanonName cv.name)
    levelParams := (<- cv.levelParams.toList.mapM uncanonName)
    type := (<- uncanonExpr cv.type)
  }

def uncanonRecursorRule (r : Ix.RecursorRule) : UncanonM Lean.RecursorRule := do
  pure {
    ctor := (<- uncanonName r.ctor)
    nfields := r.nfields
    rhs := (<- uncanonExpr r.rhs)
  }

def uncanonConst : Ix.ConstantInfo → UncanonM Lean.ConstantInfo
  | .axiomInfo v => do
    let cnst <- uncanonConstantVal v.cnst
    pure <| .axiomInfo {
      name := cnst.name
      levelParams := cnst.levelParams
      type := cnst.type
      isUnsafe := v.isUnsafe
    }
  | .defnInfo v => do
    let cnst <- uncanonConstantVal v.cnst
    pure <| .defnInfo {
      name := cnst.name
      levelParams := cnst.levelParams
      type := cnst.type
      value := (<- uncanonExpr v.value)
      hints := v.hints
      safety := v.safety
      all := (<- v.all.toList.mapM uncanonName)
    }
  | .thmInfo v => do
    let cnst <- uncanonConstantVal v.cnst
    pure <| .thmInfo {
      name := cnst.name
      levelParams := cnst.levelParams
      type := cnst.type
      value := (<- uncanonExpr v.value)
      all := (<- v.all.toList.mapM uncanonName)
    }
  | .opaqueInfo v => do
    let cnst <- uncanonConstantVal v.cnst
    pure <| .opaqueInfo {
      name := cnst.name
      levelParams := cnst.levelParams
      type := cnst.type
      value := (<- uncanonExpr v.value)
      isUnsafe := v.isUnsafe
      all := (<- v.all.toList.mapM uncanonName)
    }
  | .quotInfo v => do
    let cnst <- uncanonConstantVal v.cnst
    pure <| .quotInfo {
      name := cnst.name
      levelParams := cnst.levelParams
      type := cnst.type
      kind := v.kind
    }
  | .inductInfo v => do
    let cnst <- uncanonConstantVal v.cnst
    pure <| .inductInfo {
      name := cnst.name
      levelParams := cnst.levelParams
      type := cnst.type
      numParams := v.numParams
      numIndices := v.numIndices
      all := (<- v.all.toList.mapM uncanonName)
      ctors := (<- v.ctors.toList.mapM uncanonName)
      numNested := v.numNested
      isRec := v.isRec
      isUnsafe := v.isUnsafe
      isReflexive := v.isReflexive
    }
  | .ctorInfo v => do
    let cnst <- uncanonConstantVal v.cnst
    pure <| .ctorInfo {
      name := cnst.name
      levelParams := cnst.levelParams
      type := cnst.type
      induct := (<- uncanonName v.induct)
      cidx := v.cidx
      numParams := v.numParams
      numFields := v.numFields
      isUnsafe := v.isUnsafe
    }
  | .recInfo v => do
    let cnst <- uncanonConstantVal v.cnst
    pure <| .recInfo {
      name := cnst.name
      levelParams := cnst.levelParams
      type := cnst.type
      all := (<- v.all.toList.mapM uncanonName)
      numParams := v.numParams
      numIndices := v.numIndices
      numMotives := v.numMotives
      numMinors := v.numMinors
      rules := (<- v.rules.toList.mapM uncanonRecursorRule)
      k := v.k
      isUnsafe := v.isUnsafe
    }

/-- Canonicalize an entire Lean environment, sharing a single CanonState for
    deduplication across all constants. -/
def canonEnv (env : Lean.Environment) : CanonM Ix.Environment := do
  let mut consts : HashMap Ix.Name Ix.ConstantInfo := {}
  for (name, const) in env.constants do
    let name' <- canonName name
    let const' <- canonConst const
    consts := consts.insert name' const'
  return { consts := consts }

/-- Uncanonicalize an Ix environment back to a map of Lean constants. -/
def uncanonEnv (env : Ix.Environment) : UncanonM (HashMap Lean.Name Lean.ConstantInfo) := do
  let mut result : HashMap Lean.Name Lean.ConstantInfo := {}
  for (name, const) in env.consts do
    let name' ← uncanonName name
    let const' ← uncanonConst const
    result := result.insert name' const'
  return result

/-- Format milliseconds as human-readable time string. -/
def formatTime (ms : Nat) : String :=
  if ms < 1000 then s!"{ms}ms"
  else if ms < 60000 then
    let s := ms / 1000
    let frac := (ms % 1000) / 100
    s!"{s}.{frac}s"
  else
    let m := ms / 60000
    let s := (ms % 60000) / 1000
    s!"{m}m{s}s"

/- ## Optimized equality with pointer-pair caching -/

/-- A pair of pointers for caching equality results. -/
structure PtrPair where
  a : USize
  b : USize
  deriving Hashable, BEq

/-- State for equality checking with pointer-pair cache. -/
abbrev EqState := StateT (Std.HashSet PtrPair) Id

/-- Check if two names are equal, using pointer cache. -/
partial def nameEqCached (a b : Lean.Name) : EqState Bool := do
  let ptrA := leanNamePtr a
  let ptrB := leanNamePtr b
  if ptrA == ptrB then return true
  let pair := PtrPair.mk ptrA ptrB
  let cache ← get
  if cache.contains pair then return true
  let eq ← match a, b with
    | .anonymous, .anonymous => pure true
    | .str preA strA, .str preB strB =>
      if strA != strB then pure false
      else nameEqCached preA preB
    | .num preA numA, .num preB numB =>
      if numA != numB then pure false
      else nameEqCached preA preB
    | _, _ => pure false
  if eq then modify (·.insert pair)
  pure eq

/-- Check if two levels are equal, using pointer cache. -/
partial def levelEqCached (a b : Lean.Level) : EqState Bool := do
  let ptrA := leanLevelPtr a
  let ptrB := leanLevelPtr b
  if ptrA == ptrB then return true
  let pair := PtrPair.mk ptrA ptrB
  let cache ← get
  if cache.contains pair then return true
  let eq ← match a, b with
    | .zero, .zero => pure true
    | .succ a', .succ b' => levelEqCached a' b'
    | .max a1 a2, .max b1 b2 => do
      if !(← levelEqCached a1 b1) then return false
      levelEqCached a2 b2
    | .imax a1 a2, .imax b1 b2 => do
      if !(← levelEqCached a1 b1) then return false
      levelEqCached a2 b2
    | .param nA, .param nB => pure (nA == nB)
    | .mvar nA, .mvar nB => pure (nA == nB)
    | _, _ => pure false
  if eq then modify (·.insert pair)
  pure eq

/-- Check if two expressions are equal, using pointer cache. -/
partial def exprEqCached (a b : Lean.Expr) : EqState Bool := do
  let ptrA := leanExprPtr a
  let ptrB := leanExprPtr b
  if ptrA == ptrB then return true
  let pair := PtrPair.mk ptrA ptrB
  let cache ← get
  if cache.contains pair then return true
  let eq ← match a, b with
    | .bvar idxA, .bvar idxB => pure (idxA == idxB)
    | .fvar fA, .fvar fB => pure (fA == fB)
    | .mvar mA, .mvar mB => pure (mA == mB)
    | .sort lA, .sort lB => levelEqCached lA lB
    | .const nA lsA, .const nB lsB =>
      if nA != nB then return false
      if lsA.length != lsB.length then return false
      for (la, lb) in lsA.zip lsB do
        if !(← levelEqCached la lb) then return false
      pure true
    | .app fA argA, .app fB argB => do
      if !(← exprEqCached fA fB) then return false
      exprEqCached argA argB
    | .lam nA tyA bodyA biA, .lam nB tyB bodyB biB =>
      if biA != biB then return false
      if !(← nameEqCached nA nB) then return false
      if !(← exprEqCached tyA tyB) then return false
      exprEqCached bodyA bodyB
    | .forallE nA tyA bodyA biA, .forallE nB tyB bodyB biB =>
      if biA != biB then return false
      if !(← nameEqCached nA nB) then return false
      if !(← exprEqCached tyA tyB) then return false
      exprEqCached bodyA bodyB
    | .letE nA tyA valA bodyA ndA, .letE nB tyB valB bodyB ndB =>
      if ndA != ndB then return false
      if !(← nameEqCached nA nB) then return false
      if !(← exprEqCached tyA tyB) then return false
      if !(← exprEqCached valA valB) then return false
      exprEqCached bodyA bodyB
    | .lit lA, .lit lB => pure (lA == lB)
    -- Mdata entries are ignored for semantic equality (they carry annotations, not semantics)
    | .mdata _ eA, .mdata _ eB => exprEqCached eA eB
    | .proj tnA idxA sA, .proj tnB idxB sB =>
      if tnA != tnB || idxA != idxB then return false
      exprEqCached sA sB
    | _, _ => pure false
  if eq then modify (·.insert pair)
  pure eq

/-- Check if two ConstantInfo are equal, using fresh pointer cache.
    Checks cheap scalar fields first, then names, then types/values. -/
def constInfoEqCached (a b : Lean.ConstantInfo) : Bool :=
  let check : EqState Bool := do
    -- Check levelParams length first (cheap)
    if a.levelParams.length != b.levelParams.length then return false
    -- Check variant-specific cheap fields before expensive structural checks
    match a, b with
    | .axiomInfo v1, .axiomInfo v2 =>
      if v1.isUnsafe != v2.isUnsafe then return false
    | .defnInfo v1, .defnInfo v2 =>
      if v1.safety != v2.safety then return false
    | .thmInfo _, .thmInfo _ => pure ()
    | .opaqueInfo v1, .opaqueInfo v2 =>
      if v1.isUnsafe != v2.isUnsafe then return false
    | .quotInfo v1, .quotInfo v2 =>
      if v1.kind != v2.kind then return false
    | .inductInfo v1, .inductInfo v2 =>
      if v1.numParams != v2.numParams then return false
      if v1.numIndices != v2.numIndices then return false
      if v1.numNested != v2.numNested then return false
      if v1.isRec != v2.isRec then return false
      if v1.isUnsafe != v2.isUnsafe then return false
      if v1.isReflexive != v2.isReflexive then return false
      if v1.isNested != v2.isNested then return false
      if v1.all != v2.all then return false
      if v1.ctors != v2.ctors then return false
    | .ctorInfo v1, .ctorInfo v2 =>
      if v1.cidx != v2.cidx then return false
      if v1.numParams != v2.numParams then return false
      if v1.numFields != v2.numFields then return false
      if v1.isUnsafe != v2.isUnsafe then return false
      if v1.induct != v2.induct then return false
    | .recInfo v1, .recInfo v2 =>
      if v1.numParams != v2.numParams then return false
      if v1.numIndices != v2.numIndices then return false
      if v1.numMotives != v2.numMotives then return false
      if v1.numMinors != v2.numMinors then return false
      if v1.k != v2.k then return false
      if v1.isUnsafe != v2.isUnsafe then return false
      if v1.rules.length != v2.rules.length then return false
      if v1.all != v2.all then return false
    | _, _ => return false
    -- Now check names (cheaper than exprs)
    if !(← nameEqCached a.name b.name) then return false
    for (la, lb) in a.levelParams.zip b.levelParams do
      if !(← nameEqCached la lb) then return false
    -- Finally check types and values (most expensive)
    if !(← exprEqCached a.type b.type) then return false
    match a, b with
    | .axiomInfo _, .axiomInfo _ => pure true
    | .defnInfo v1, .defnInfo v2 => exprEqCached v1.value v2.value
    | .thmInfo v1, .thmInfo v2 => exprEqCached v1.value v2.value
    | .opaqueInfo v1, .opaqueInfo v2 => exprEqCached v1.value v2.value
    | .quotInfo _, .quotInfo _ => pure true
    | .inductInfo _, .inductInfo _ => pure true
    | .ctorInfo _, .ctorInfo _ => pure true
    | .recInfo v1, .recInfo v2 => do
      for (r1, r2) in v1.rules.zip v2.rules do
        if r1.ctor != r2.ctor then return false
        if r1.nfields != r2.nfields then return false
        if !(← exprEqCached r1.rhs r2.rhs) then return false
      pure true
    | _, _ => pure false
  (check.run {}).1

/-- Compare two environments in parallel using Tasks.
    One-directional: only checks that env1 entries exist and match in env2.
    Extra entries in env2 are not detected (by design for roundtrip verification).
    Returns (numMismatches, numMissing, mismatchNames, missingNames). -/
def compareEnvsParallel (env1 env2 : Std.HashMap Lean.Name Lean.ConstantInfo)
    : Nat × Nat × Array Lean.Name × Array Lean.Name := Id.run do
  let entries := env1.toArray
  let tasks := entries.map fun (name, const1) =>
    Task.spawn fun _ =>
      match env2.get? name with
      | none => (false, true, name)
      | some const2 =>
        let eq := constInfoEqCached const1 const2
        (eq, false, name)
  let mut mismatchNames : Array Lean.Name := #[]
  let mut missingNames : Array Lean.Name := #[]
  for task in tasks do
    let (eq, isMissing, name) := task.get
    if isMissing then
      missingNames := missingNames.push name
    else if !eq then
      mismatchNames := mismatchNames.push name
  (mismatchNames.size, missingNames.size, mismatchNames, missingNames)

/- ## Parallel Canonicalization -/

/-- Split an array into chunks of the given size. -/
def chunks (arr : Array α) (chunkSize : Nat) : Array (Array α) := Id.run do
  if chunkSize == 0 then return #[arr]
  let mut result : Array (Array α) := #[]
  let mut i := 0
  while i < arr.size do
    let endIdx := min (i + chunkSize) arr.size
    result := result.push (arr.extract i endIdx)
    i := endIdx
  result

/-- Process a chunk of constants with local state (pure).
    Returns just the canonicalized constants. -/
def canonChunk (chunk : Array (Lean.Name × Lean.ConstantInfo))
    : Array (Ix.Name × Ix.ConstantInfo) := Id.run do
  let mut state : CanonState := {}
  let mut results : Array (Ix.Name × Ix.ConstantInfo) := #[]
  for (name, const) in chunk do
    let (name', state') := StateT.run (canonName name) state
    let (const', state'') := StateT.run (canonConst const) state'
    state := state''
    results := results.push (name', const')
  results

/-- Canonicalize an entire Lean environment in parallel (pure).
    Returns just the constants map. -/
def canonEnvParallel (env : Lean.Environment) (numWorkers : Nat := 8)
    : HashMap Ix.Name Ix.ConstantInfo :=
  let constArr := env.constants.toList.toArray
  let chunkSize := (constArr.size + numWorkers - 1) / numWorkers
  let chunkArr := chunks constArr chunkSize
  let tasks := chunkArr.map fun chunk =>
    Task.spawn fun _ => canonChunk chunk
  Id.run do
    let mut consts : HashMap Ix.Name Ix.ConstantInfo := {}
    for task in tasks do
      for (name, const) in task.get do
        consts := consts.insert name const
    consts

/-- Process a chunk of Ix constants back to Lean (pure).
    Returns just the uncanonicalized constants. -/
def uncanonChunk (chunk : Array (Ix.Name × Ix.ConstantInfo))
    : Array (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut state : UncanonState := {}
  let mut results : Array (Lean.Name × Lean.ConstantInfo) := #[]
  for (name, const) in chunk do
    let (name', state') := StateT.run (uncanonName name) state
    let (const', state'') := StateT.run (uncanonConst const) state'
    state := state''
    results := results.push (name', const')
  results

/-- Uncanonicalize an Ix environment in parallel (pure).
    Returns a HashMap of Lean constants. -/
def uncanonEnvParallel (consts : HashMap Ix.Name Ix.ConstantInfo) (numWorkers : Nat := 8)
    : HashMap Lean.Name Lean.ConstantInfo :=
  let constArr := consts.toArray
  let chunkSize := (constArr.size + numWorkers - 1) / numWorkers
  let chunkArr := chunks constArr chunkSize
  let tasks := chunkArr.map fun chunk =>
    Task.spawn fun _ => uncanonChunk chunk
  Id.run do
    let mut result : HashMap Lean.Name Lean.ConstantInfo := {}
    for task in tasks do
      for (name, const) in task.get do
        result := result.insert name const
    result

end Ix.CanonM

