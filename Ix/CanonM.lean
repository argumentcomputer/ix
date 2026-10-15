module
/-
  # CanonM: Canonicalize Lean types to Ix types with content-addressed hashing

  Converts Lean kernel types (Name, Level, Expr, ConstantInfo) to their Ix
  counterparts, embedding blake3 hashes at each node for O(1) structural equality.

  The conversions compute a cache-free specification (`Ix.Cert.Canon.nameS`,
  `levelS`, `syntaxS`, `dataValueS`, `mdataS`, `exprS`, `constS`, below), with
  a memo: names, levels and expressions are memoised under the address of
  their Lean object (`ptrAddrUnsafe`), so a subterm Lean shares is converted
  once. Every memo entry carries its source object, its image and the proof
  that the image is the specification's. A hit is confirmed by identity
  (`withPtrEq`), whose pure meaning decides that the stored source is the
  input, so a conversion returns the specification from every state, whatever
  the addresses are (`Ix.Cert.Canon`, C1). At run time a confirmation is a
  pointer comparison: an entry keeps its source alive, so a hit under the
  input's address is the input itself. There is no hash-keyed cache: a hash
  collision cannot merge two terms.

  Key operations:
  - `canonName` / `uncanonName`: Lean.Name <-> Ix.Name
  - `canonLevel` / `uncanonLevel`: Lean.Level <-> Ix.Level
  - `canonExpr` / `uncanonExpr`: Lean.Expr <-> Ix.Expr
  - `canonEnv` / `uncanonEnv`: whole-environment conversion
  - `compareEnvsParallel`: parallel structural equality check between environments
-/

public import Ix.Common
public import Ix.Environment
public import Ix.SemanticContract
public import Ix.Address

public section

namespace Ix.CanonM

open Std (HashMap)

@[inline] def leanExprPtr (e : Lean.Expr) : USize := unsafe ptrAddrUnsafe e
@[inline] def leanNamePtr (n : Lean.Name) : USize := unsafe ptrAddrUnsafe n
@[inline] def leanLevelPtr (l : Lean.Level) : USize := unsafe ptrAddrUnsafe l

@[expose] def canonInt : _root_.Int → Ix.Int
  | .ofNat n => .ofNat n
  | .negSucc n => .negSucc n

@[expose] def canonSubstring (ss : _root_.Substring.Raw) : Ix.Substring :=
  { str := ss.str, startPos := ss.startPos.byteIdx, stopPos := ss.stopPos.byteIdx }

@[expose] def canonSourceInfo : Lean.SourceInfo → Ix.SourceInfo
  | .original leading pos trailing endPos =>
    .original (canonSubstring leading) pos.byteIdx
      (canonSubstring trailing) endPos.byteIdx
  | .synthetic pos endPos canonical => .synthetic pos.byteIdx endPos.byteIdx canonical
  | .none => .none

end Ix.CanonM

/-! ## The specification

The conversions without their memo, with the same smart constructors (so the
same hash fields). `Ix.Cert.Canon` reads them. -/

namespace Ix.Cert.Canon

/-- `canonName` without its memo. -/
@[expose] def nameS : Lean.Name → Ix.Name
  | .anonymous => .mkAnon
  | .str p s => .mkStr (nameS p) s
  | .num p n => .mkNat (nameS p) n

/-- `canonLevel` without its memo. -/
@[expose] def levelS : Lean.Level → Ix.Level
  | .zero => .mkZero
  | .succ u => .mkSucc (levelS u)
  | .max u v => .mkMax (levelS u) (levelS v)
  | .imax u v => .mkIMax (levelS u) (levelS v)
  | .param n => .mkParam (nameS n)
  | .mvar m => .mkMvar (nameS m.name)

@[expose] def preresolvedS : Lean.Syntax.Preresolved → Ix.SyntaxPreresolved
  | .namespace n => .namespace (nameS n)
  | .decl n aliases => .decl (nameS n) aliases.toArray

/-- `canonSyntax`. -/
@[expose] def syntaxS : Lean.Syntax → Ix.Syntax
  | .missing => .missing
  | .node info kind args =>
    .node (Ix.CanonM.canonSourceInfo info) (nameS kind) (args.map syntaxS)
  | .atom info val => .atom (Ix.CanonM.canonSourceInfo info) val
  | .ident info rawVal val pre =>
    .ident (Ix.CanonM.canonSourceInfo info) (Ix.CanonM.canonSubstring rawVal) (nameS val)
      (pre.toArray.map preresolvedS)

@[expose] def dataValueS : Lean.DataValue → Ix.DataValue
  | .ofString s => .ofString s
  | .ofBool b => .ofBool b
  | .ofName n => .ofName (nameS n)
  | .ofNat n => .ofNat n
  | .ofInt i => .ofInt (Ix.CanonM.canonInt i)
  | .ofSyntax s => .ofSyntax (syntaxS s)

/-- `canonMData` without its memo: the entries in order. -/
@[expose] def mdataS (d : Lean.MData) : Array (Ix.Name × Ix.DataValue) :=
  (d.entries.map fun (n, v) => (nameS n, dataValueS v)).toArray

/-- `canonExpr` without its memo. -/
@[expose] def exprS : Lean.Expr → Ix.Expr
  | .bvar i => .mkBVar i
  | .fvar x => .mkFVar (nameS x.name)
  | .mvar x => .mkMVar (nameS x.name)
  | .sort u => .mkSort (levelS u)
  | .const n us => .mkConst (nameS n) (us.map levelS).toArray
  | .app f a => .mkApp (exprS f) (exprS a)
  | .lam n t b bi => .mkLam (nameS n) (exprS t) (exprS b) bi
  | .forallE n t b bi => .mkForallE (nameS n) (exprS t) (exprS b) bi
  | .letE n t v b nd => .mkLetE (nameS n) (exprS t) (exprS v) (exprS b) nd
  | .lit l => .mkLit l
  | .mdata d e => .mkMData (mdataS d) (exprS e)
  | .proj s i e => .mkProj (nameS s) i (exprS e)

@[expose] def constValS (cv : Lean.ConstantVal) : Ix.ConstantVal :=
  { name := nameS cv.name, levelParams := (cv.levelParams.map nameS).toArray, type := exprS cv.type }

/-- `canonConst` without its memo. -/
@[expose] def constS : Lean.ConstantInfo → Ix.ConstantInfo
  | .axiomInfo v => .axiomInfo { cnst := constValS v.toConstantVal, isUnsafe := v.isUnsafe }
  | .defnInfo v => .defnInfo
      { cnst := constValS v.toConstantVal, value := exprS v.value, hints := v.hints,
        safety := v.safety, all := (v.all.map nameS).toArray }
  | .thmInfo v => .thmInfo
      { cnst := constValS v.toConstantVal, value := exprS v.value, all := (v.all.map nameS).toArray }
  | .opaqueInfo v => .opaqueInfo
      { cnst := constValS v.toConstantVal, value := exprS v.value, isUnsafe := v.isUnsafe,
        all := (v.all.map nameS).toArray }
  | .quotInfo v => .quotInfo { cnst := constValS v.toConstantVal, kind := v.kind }
  | .inductInfo v => .inductInfo
      { cnst := constValS v.toConstantVal, numParams := v.numParams, numIndices := v.numIndices,
        all := (v.all.map nameS).toArray, ctors := (v.ctors.map nameS).toArray,
        numNested := v.numNested, isRec := v.isRec, isUnsafe := v.isUnsafe,
        isReflexive := v.isReflexive }
  | .ctorInfo v => .ctorInfo
      { cnst := constValS v.toConstantVal, induct := nameS v.induct, cidx := v.cidx,
        numParams := v.numParams, numFields := v.numFields, isUnsafe := v.isUnsafe }
  | .recInfo v => .recInfo
      { cnst := constValS v.toConstantVal, all := (v.all.map nameS).toArray,
        numParams := v.numParams, numIndices := v.numIndices, numMotives := v.numMotives,
        numMinors := v.numMinors,
        rules := (v.rules.map fun r => { ctor := nameS r.ctor, nfields := r.nfields, rhs := exprS r.rhs }).toArray,
        k := v.k, isUnsafe := v.isUnsafe }

end Ix.Cert.Canon

/-! ## Decidable equality on Lean's terms

The memo confirms a hit with `withPtrEq`, whose pure fallback decides that
the stored source is the input. Lean gives `DecidableEq Lean.Name`; the
instances below are derived, except `Lean.Syntax`'s, which nests through
`Array` and is written out. They add no `BEq` (`instBEqOfDecidableEq` has a
lower priority than the `BEq` instances these types have), and at run time
they are reached only if a confirmation's pointers differ, which a memo hit
never does. -/

deriving instance DecidableEq for Lean.Literal
deriving instance DecidableEq for Lean.BinderInfo
deriving instance DecidableEq for Lean.FVarId
deriving instance DecidableEq for Lean.MVarId
deriving instance DecidableEq for Lean.LevelMVarId
deriving instance DecidableEq for Lean.Level
deriving instance DecidableEq for Substring.Raw
deriving instance DecidableEq for Lean.SourceInfo
deriving instance DecidableEq for Lean.Syntax.Preresolved

namespace Ix.CanonM

mutual
/-- Decidable equality of `Lean.Syntax`, through its argument arrays. -/
def decEqSyntax : (a b : Lean.Syntax) → Decidable (a = b)
  | .missing, .missing => isTrue rfl
  | .node i k ⟨as⟩, .node i' k' ⟨bs⟩ =>
    if h1 : i = i' then if h2 : k = k' then
      match decEqSyntaxList as bs with
      | isTrue h3 => isTrue (by subst h1 h2 h3; rfl)
      | isFalse h3 => isFalse (by intro h; injection h with _ _ h; exact h3 (by injection h))
    else isFalse (by intro h; injection h; contradiction)
    else isFalse (by intro h; injection h; contradiction)
  | .atom i v, .atom i' v' =>
    if h : i = i' ∧ v = v' then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else isFalse (by intro e; injection e with e1 e2; exact h ⟨e1, e2⟩)
  | .ident i r v p, .ident i' r' v' p' =>
    if h : i = i' ∧ r = r' ∧ v = v' ∧ p = p' then
      isTrue (by obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl)
    else isFalse (by intro e; injection e with e1 e2 e3 e4; exact h ⟨e1, e2, e3, e4⟩)
  | .missing, .node .. | .missing, .atom .. | .missing, .ident .. => isFalse (by intro h; cases h)
  | .node .., .missing | .node .., .atom .. | .node .., .ident .. => isFalse (by intro h; cases h)
  | .atom .., .missing | .atom .., .node .. | .atom .., .ident .. => isFalse (by intro h; cases h)
  | .ident .., .missing | .ident .., .node .. | .ident .., .atom .. =>
    isFalse (by intro h; cases h)
/-- Decidable equality of lists of `Lean.Syntax`. -/
def decEqSyntaxList : (as bs : List Lean.Syntax) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match decEqSyntax a b, decEqSyntaxList as bs with
    | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
    | isFalse h1, _ => isFalse (by intro h; injection h; contradiction)
    | _, isFalse h2 => isFalse (by intro h; injection h; contradiction)
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Lean.Syntax := decEqSyntax

end Ix.CanonM

deriving instance DecidableEq for Lean.DataValue
deriving instance DecidableEq for Lean.KVMap
deriving instance DecidableEq for Lean.Expr

/-! ## The memo -/

namespace Ix.CanonM

open Std (HashMap)
open Ix.Cert.Canon

/-- A memoised name: its source, its image, and the proof. -/
structure NameEntry where
  src : Lean.Name
  val : Ix.Name
  ok : val = nameS src

/-- A memoised level: its source, its image, and the proof. -/
structure LevelEntry where
  src : Lean.Level
  val : Ix.Level
  ok : val = levelS src

/-- A memoised expression: its source, its image, and the proof. -/
structure ExprEntry where
  src : Lean.Expr
  val : Ix.Expr
  ok : val = exprS src

/-- The memo: each kind's entries under the address of their source. -/
structure CanonState where
  names : HashMap USize NameEntry := {}
  levels : HashMap USize LevelEntry := {}
  exprs : HashMap USize ExprEntry := {}

abbrev CanonM := StateT CanonState Id

/-- Is `x` `y`? At run time by pointer identity first (`withPtrEqDecEq`); the
pure meaning, and the run-time fallback, decide the equality. -/
@[inline, expose] def confirm {α : Type} [DecidableEq α] (x y : α) : Decidable (x = y) :=
  withPtrEqDecEq x y fun _ => inferInstance

/-- The memo entry under `ptr`, if it is `n`'s. -/
@[inline, expose] def probeName (s : CanonState) (ptr : USize) (n : Lean.Name) :
    Option {v : Ix.Name // v = nameS n} :=
  match s.names.get? ptr with
  | some p => match confirm p.src n with
    | isTrue h => some ⟨p.val, h ▸ p.ok⟩
    | isFalse _ => none
  | none => none

/-- The memo entry under `ptr`, if it is `l`'s. -/
@[inline, expose] def probeLevel (s : CanonState) (ptr : USize) (l : Lean.Level) :
    Option {v : Ix.Level // v = levelS l} :=
  match s.levels.get? ptr with
  | some p => match confirm p.src l with
    | isTrue h => some ⟨p.val, h ▸ p.ok⟩
    | isFalse _ => none
  | none => none

/-- The memo entry under `ptr`, if it is `e`'s. -/
@[inline, expose] def probeExpr (s : CanonState) (ptr : USize) (e : Lean.Expr) :
    Option {v : Ix.Expr // v = exprS e} :=
  match s.exprs.get? ptr with
  | some p => match confirm p.src e with
    | isTrue h => some ⟨p.val, h ▸ p.ok⟩
    | isFalse _ => none
  | none => none

/-! ## The conversions, with their results' proofs -/

/-- `canonName`, with the proof that it returns `nameS n`. -/
@[expose] def canonNameS (n : Lean.Name) : CanonM {v : Ix.Name // v = nameS n} := do
  let ptr := leanNamePtr n
  if let some hit := probeName (← get) ptr n then return hit
  let r : {v : Ix.Name // v = nameS n} ← match h : n with
    | .anonymous => pure ⟨.mkAnon, by rw [h]; rfl⟩
    | .str pre str => do
      let p ← canonNameS pre
      pure ⟨.mkStr p.1 str, by rw [h, p.2]; rfl⟩
    | .num pre num => do
      let p ← canonNameS pre
      pure ⟨.mkNat p.1 num, by rw [h, p.2]; rfl⟩
  modify fun s => { s with names := s.names.insert ptr ⟨n, r.1, r.2⟩ }
  pure r

/-- Names in order. -/
@[expose] def canonNamesS : (ns : List Lean.Name) → CanonM {v : List Ix.Name // v = ns.map nameS}
  | [] => pure ⟨[], rfl⟩
  | n :: ns => do
    let a ← canonNameS n
    let b ← canonNamesS ns
    pure ⟨a.1 :: b.1, by rw [a.2, b.2]; rfl⟩

/-- `canonLevel`, with the proof that it returns `levelS l`. -/
@[expose] def canonLevelS (l : Lean.Level) : CanonM {v : Ix.Level // v = levelS l} := do
  let ptr := leanLevelPtr l
  if let some hit := probeLevel (← get) ptr l then return hit
  let r : {v : Ix.Level // v = levelS l} ← match h : l with
    | .zero => pure ⟨.mkZero, by rw [h]; rfl⟩
    | .succ x => do
      let a ← canonLevelS x
      pure ⟨.mkSucc a.1, by rw [h, a.2]; rfl⟩
    | .max x y => do
      let a ← canonLevelS x
      let b ← canonLevelS y
      pure ⟨.mkMax a.1 b.1, by rw [h, a.2, b.2]; rfl⟩
    | .imax x y => do
      let a ← canonLevelS x
      let b ← canonLevelS y
      pure ⟨.mkIMax a.1 b.1, by rw [h, a.2, b.2]; rfl⟩
    | .param n => do
      let a ← canonNameS n
      pure ⟨.mkParam a.1, by rw [h, a.2]; rfl⟩
    | .mvar n => do
      let a ← canonNameS n.name
      pure ⟨.mkMvar a.1, by rw [h, a.2]; rfl⟩
  modify fun s => { s with levels := s.levels.insert ptr ⟨l, r.1, r.2⟩ }
  pure r

/-- Levels in order. -/
@[expose] def canonLevelsS : (us : List Lean.Level) → CanonM {v : List Ix.Level // v = us.map levelS}
  | [] => pure ⟨[], rfl⟩
  | u :: us => do
    let a ← canonLevelS u
    let b ← canonLevelsS us
    pure ⟨a.1 :: b.1, by rw [a.2, b.2]; rfl⟩

/-- `canonDataValue`, with the proof that it returns `dataValueS d`. A
syntax payload is converted by the specification itself (`syntaxS`). -/
@[expose] def canonDataValueS (d : Lean.DataValue) : CanonM {v : Ix.DataValue // v = dataValueS d} :=
  match d with
  | .ofString s => pure ⟨.ofString s, rfl⟩
  | .ofBool b => pure ⟨.ofBool b, rfl⟩
  | .ofName n => do
    let a ← canonNameS n
    pure ⟨.ofName a.1, by rw [a.2]; rfl⟩
  | .ofNat n => pure ⟨.ofNat n, rfl⟩
  | .ofInt i => pure ⟨.ofInt (canonInt i), rfl⟩
  | .ofSyntax s => pure ⟨.ofSyntax (syntaxS s), rfl⟩

/-- Metadata entries in order. -/
@[expose] def canonMDataEntriesS : (l : List (Lean.Name × Lean.DataValue)) →
    CanonM {v : List (Ix.Name × Ix.DataValue) // v = l.map fun (n, v) => (nameS n, dataValueS v)}
  | [] => pure ⟨[], rfl⟩
  | (n, d) :: l => do
    let a ← canonNameS n
    let b ← canonDataValueS d
    let c ← canonMDataEntriesS l
    pure ⟨(a.1, b.1) :: c.1, by rw [a.2, b.2, c.2]; rfl⟩

/-- `canonMData`, with the proof that it returns `mdataS md`. -/
@[expose] def canonMDataS (md : Lean.MData) : CanonM {v : Array (Ix.Name × Ix.DataValue) // v = mdataS md} := do
  let r ← canonMDataEntriesS md.entries
  pure ⟨r.1.toArray, by rw [r.2]; rfl⟩

/-- `canonExpr`, with the proof that it returns `exprS e`. -/
@[expose] def canonExprS (e : Lean.Expr) : CanonM {v : Ix.Expr // v = exprS e} := do
  let ptr := leanExprPtr e
  if let some hit := probeExpr (← get) ptr e then return hit
  let r : {v : Ix.Expr // v = exprS e} ← match h : e with
    | .bvar idx => pure ⟨.mkBVar idx, by rw [h]; rfl⟩
    | .fvar fvarId => do
      let a ← canonNameS fvarId.name
      pure ⟨.mkFVar a.1, by rw [h, a.2]; rfl⟩
    | .mvar mvarId => do
      let a ← canonNameS mvarId.name
      pure ⟨.mkMVar a.1, by rw [h, a.2]; rfl⟩
    | .sort level => do
      let a ← canonLevelS level
      pure ⟨.mkSort a.1, by rw [h, a.2]; rfl⟩
    | .const name levels => do
      let a ← canonNameS name
      let b ← canonLevelsS levels
      pure ⟨.mkConst a.1 b.1.toArray, by rw [h, a.2, b.2]; rfl⟩
    | .app fn arg => do
      let a ← canonExprS fn
      let b ← canonExprS arg
      pure ⟨.mkApp a.1 b.1, by rw [h, a.2, b.2]; rfl⟩
    | .lam name ty body bi => do
      let a ← canonNameS name
      let b ← canonExprS ty
      let c ← canonExprS body
      pure ⟨.mkLam a.1 b.1 c.1 bi, by rw [h, a.2, b.2, c.2]; rfl⟩
    | .forallE name ty body bi => do
      let a ← canonNameS name
      let b ← canonExprS ty
      let c ← canonExprS body
      pure ⟨.mkForallE a.1 b.1 c.1 bi, by rw [h, a.2, b.2, c.2]; rfl⟩
    | .letE name ty val body nonDep => do
      let a ← canonNameS name
      let b ← canonExprS ty
      let c ← canonExprS val
      let d ← canonExprS body
      pure ⟨.mkLetE a.1 b.1 c.1 d.1 nonDep, by rw [h, a.2, b.2, c.2, d.2]; rfl⟩
    | .lit l => pure ⟨.mkLit l, by rw [h]; rfl⟩
    | .mdata md expr => do
      let a ← canonMDataS md
      let b ← canonExprS expr
      pure ⟨.mkMData a.1 b.1, by rw [h, a.2, b.2]; rfl⟩
    | .proj typeName idx struct => do
      let a ← canonNameS typeName
      let b ← canonExprS struct
      pure ⟨.mkProj a.1 idx b.1, by rw [h, a.2, b.2]; rfl⟩
  modify fun s => { s with exprs := s.exprs.insert ptr ⟨e, r.1, r.2⟩ }
  pure r

/-- `canonConstantVal`, with the proof that it returns `constValS cv`. -/
@[expose] def canonConstantValS (cv : Lean.ConstantVal) :
    CanonM {v : Ix.ConstantVal // v = constValS cv} := do
  let a ← canonNameS cv.name
  let b ← canonNamesS cv.levelParams
  let c ← canonExprS cv.type
  pure ⟨{ name := a.1, levelParams := b.1.toArray, type := c.1 }, by rw [a.2, b.2, c.2]; rfl⟩

/-- Recursor rules in order. -/
@[expose] def canonRecursorRulesS : (rs : List Lean.RecursorRule) →
    CanonM {v : List Ix.RecursorRule //
      v = rs.map fun r => { ctor := nameS r.ctor, nfields := r.nfields, rhs := exprS r.rhs }}
  | [] => pure ⟨[], rfl⟩
  | r :: rs => do
    let a ← canonNameS r.ctor
    let b ← canonExprS r.rhs
    let c ← canonRecursorRulesS rs
    pure ⟨{ ctor := a.1, nfields := r.nfields, rhs := b.1 } :: c.1, by rw [a.2, b.2, c.2]; rfl⟩

/-- `canonConst`, with the proof that it returns `constS c`. -/
@[expose] def canonConstS : (c : Lean.ConstantInfo) → CanonM {v : Ix.ConstantInfo // v = constS c}
  | .axiomInfo v => do
    let cv ← canonConstantValS v.toConstantVal
    pure ⟨.axiomInfo { cnst := cv.1, isUnsafe := v.isUnsafe }, by rw [cv.2]; rfl⟩
  | .defnInfo v => do
    let cv ← canonConstantValS v.toConstantVal
    let x ← canonExprS v.value
    let all ← canonNamesS v.all
    pure ⟨.defnInfo
        { cnst := cv.1, value := x.1, hints := v.hints, safety := v.safety,
          all := all.1.toArray },
      by rw [cv.2, x.2, all.2]; rfl⟩
  | .thmInfo v => do
    let cv ← canonConstantValS v.toConstantVal
    let x ← canonExprS v.value
    let all ← canonNamesS v.all
    pure ⟨.thmInfo { cnst := cv.1, value := x.1, all := all.1.toArray },
      by rw [cv.2, x.2, all.2]; rfl⟩
  | .opaqueInfo v => do
    let cv ← canonConstantValS v.toConstantVal
    let x ← canonExprS v.value
    let all ← canonNamesS v.all
    pure ⟨.opaqueInfo
        { cnst := cv.1, value := x.1, isUnsafe := v.isUnsafe, all := all.1.toArray },
      by rw [cv.2, x.2, all.2]; rfl⟩
  | .quotInfo v => do
    let cv ← canonConstantValS v.toConstantVal
    pure ⟨.quotInfo { cnst := cv.1, kind := v.kind }, by rw [cv.2]; rfl⟩
  | .inductInfo v => do
    let cv ← canonConstantValS v.toConstantVal
    let all ← canonNamesS v.all
    let ctors ← canonNamesS v.ctors
    pure ⟨.inductInfo
        { cnst := cv.1, numParams := v.numParams, numIndices := v.numIndices,
          all := all.1.toArray, ctors := ctors.1.toArray, numNested := v.numNested,
          isRec := v.isRec, isUnsafe := v.isUnsafe, isReflexive := v.isReflexive },
      by rw [cv.2, all.2, ctors.2]; rfl⟩
  | .ctorInfo v => do
    let cv ← canonConstantValS v.toConstantVal
    let induct ← canonNameS v.induct
    pure ⟨.ctorInfo
        { cnst := cv.1, induct := induct.1, cidx := v.cidx, numParams := v.numParams,
          numFields := v.numFields, isUnsafe := v.isUnsafe },
      by rw [cv.2, induct.2]; rfl⟩
  | .recInfo v => do
    let cv ← canonConstantValS v.toConstantVal
    let all ← canonNamesS v.all
    let rules ← canonRecursorRulesS v.rules
    pure ⟨.recInfo
        { cnst := cv.1, all := all.1.toArray, numParams := v.numParams,
          numIndices := v.numIndices, numMotives := v.numMotives, numMinors := v.numMinors,
          rules := rules.1.toArray, k := v.k, isUnsafe := v.isUnsafe },
      by rw [cv.2, all.2, rules.2]; rfl⟩

/-! ## The conversions -/

@[expose] def canonName (n : Lean.Name) : CanonM Ix.Name := Subtype.val <$> canonNameS n

@[expose] def canonLevel (l : Lean.Level) : CanonM Ix.Level := Subtype.val <$> canonLevelS l

/-- Syntax (a metadata payload), converted by the specification. -/
@[expose] def canonSyntax (s : Lean.Syntax) : CanonM Ix.Syntax := pure (syntaxS s)

@[expose] def canonDataValue (d : Lean.DataValue) : CanonM Ix.DataValue :=
  Subtype.val <$> canonDataValueS d

@[expose] def canonMData (md : Lean.MData) : CanonM (Array (Ix.Name × Ix.DataValue)) :=
  Subtype.val <$> canonMDataS md

@[expose] def canonExpr (e : Lean.Expr) : CanonM Ix.Expr := Subtype.val <$> canonExprS e

@[expose] def canonConstantVal (cv : Lean.ConstantVal) : CanonM Ix.ConstantVal :=
  Subtype.val <$> canonConstantValS cv

@[expose] def canonRecursorRule (r : Lean.RecursorRule) : CanonM Ix.RecursorRule := do
  let a ← canonNameS r.ctor
  let b ← canonExprS r.rhs
  pure { ctor := a.1, nfields := r.nfields, rhs := b.1 }

@[expose] def canonConst (c : Lean.ConstantInfo) : CanonM Ix.ConstantInfo :=
  Subtype.val <$> canonConstS c

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
    -- Presentation metadata is transparent; effective contracts are semantic.
    | .mdata dataA eA, .mdata dataB eB => do
      if SemanticContract.leanFields dataA != SemanticContract.leanFields dataB then return false
      exprEqCached eA eB
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

/-- Process a chunk of constants through one memo (pure), in order. Returns
    just the canonicalized constants. -/
@[expose] def canonChunk (chunk : Array (Lean.Name × Lean.ConstantInfo))
    : Array (Ix.Name × Ix.ConstantInfo) :=
  Id.run <| (chunk.mapM (m := CanonM) fun (name, const) => do
    let name' ← canonName name
    let const' ← canonConst const
    pure (name', const')).run' {}

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

end

