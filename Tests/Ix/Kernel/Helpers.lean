/-
  Shared test utilities for kernel tests.
  - Address helpers (mkAddr)
  - Name parsing (parseIxName, leanNameToIx)
  - Env-building helpers (addDef, addOpaque, addTheorem, etc.)
  - TypecheckM runner for pure tests (via runST + ExceptT)
  - Eval+quote convenience

  Default MetaMode is .meta. Anon variants provided for specific tests.
-/
import Ix.Kernel

namespace Tests.Ix.Kernel.Helpers

/-- Helper: make unique addresses from a seed byte. -/
def mkAddr (seed : UInt8) : Address :=
  Address.blake3 (ByteArray.mk #[seed, 0xAA, 0xBB])

/-- Parse a dotted name string like "Nat.add" into an Ix.Name.
    Handles `«...»` quoted name components (e.g. `Foo.«0».Bar`). -/
partial def parseIxName (s : String) : Ix.Name :=
  let parts := splitParts s.toList []
  parts.foldl (fun acc part =>
    match part with
    | .inl str => Ix.Name.mkStr acc str
    | .inr nat => Ix.Name.mkNat acc nat
  ) Ix.Name.mkAnon
where
  /-- Split a dotted name into parts: .inl for string components, .inr for numeric (guillemet). -/
  splitParts : List Char → List (String ⊕ Nat) → List (String ⊕ Nat)
    | [], acc => acc
    | '.' :: rest, acc => splitParts rest acc
    | '«' :: rest, acc =>
      let (inside, rest') := collectUntilClose rest ""
      let part := match inside.toNat? with
        | some n => .inr n
        | none => .inl inside
      splitParts rest' (acc ++ [part])
    | cs, acc =>
      let (word, rest) := collectUntilDot cs ""
      splitParts rest (if word.isEmpty then acc else acc ++ [.inl word])
  collectUntilClose : List Char → String → String × List Char
    | [], s => (s, [])
    | '»' :: rest, s => (s, rest)
    | c :: rest, s => collectUntilClose rest (s.push c)
  collectUntilDot : List Char → String → String × List Char
    | [], s => (s, [])
    | '.' :: rest, s => (s, '.' :: rest)
    | '«' :: rest, s => (s, '«' :: rest)
    | c :: rest, s => collectUntilDot rest (s.push c)

/-- Convert a Lean.Name to an Ix.Name (reproducing the Blake3 hashing). -/
partial def leanNameToIx : Lean.Name → Ix.Name
  | .anonymous => Ix.Name.mkAnon
  | .str pre s => Ix.Name.mkStr (leanNameToIx pre) s
  | .num pre n => Ix.Name.mkNat (leanNameToIx pre) n

-- BEq for Except (needed for test assertions)
instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

-- Aliases (non-private so BEq instances resolve in importers)
abbrev E := Ix.Kernel.Expr Ix.Kernel.MetaMode.meta
abbrev L := Ix.Kernel.Level Ix.Kernel.MetaMode.meta
abbrev Env := Ix.Kernel.Env Ix.Kernel.MetaMode.meta
abbrev Prims := Ix.Kernel.Primitives .meta
abbrev MId := Ix.Kernel.MetaId Ix.Kernel.MetaMode.meta

/-- Build a MetaId from a name string and seed byte. -/
def mkId (name : String) (seed : UInt8) : MId :=
  (parseIxName name, mkAddr seed)

/-! ## Env-building helpers -/

def addDef (env : Env) (id : MId) (type value : E)
    (numLevels : Nat := 0) (hints : Ix.Kernel.ReducibilityHints := .abbrev)
    (safety : Ix.Kernel.DefinitionSafety := .safe) : Env :=
  env.insert id (.defnInfo {
    toConstantVal := { numLevels, type, name := id.name, levelParams := default },
    value, hints, safety, all := #[id]
  })

def addOpaque (env : Env) (id : MId) (type value : E)
    (numLevels : Nat := 0) (isUnsafe := false) : Env :=
  env.insert id (.opaqueInfo {
    toConstantVal := { numLevels, type, name := id.name, levelParams := default },
    value, isUnsafe, all := #[id]
  })

def addTheorem (env : Env) (id : MId) (type value : E)
    (numLevels : Nat := 0) : Env :=
  env.insert id (.thmInfo {
    toConstantVal := { numLevels, type, name := id.name, levelParams := default },
    value, all := #[id]
  })

def addInductive (env : Env) (id : MId)
    (type : E) (ctors : Array MId)
    (numParams numIndices : Nat := 0) (isRec := false)
    (isUnsafe := false) (numNested := 0)
    (numLevels : Nat := 0) (all : Array MId := #[id]) : Env :=
  env.insert id (.inductInfo {
    toConstantVal := { numLevels, type, name := id.name, levelParams := default },
    numParams, numIndices, all, ctors, numNested,
    isRec, isUnsafe, isReflexive := false
  })

def addCtor (env : Env) (id : MId) (induct : MId)
    (type : E) (cidx numParams numFields : Nat)
    (isUnsafe := false) (numLevels : Nat := 0) : Env :=
  env.insert id (.ctorInfo {
    toConstantVal := { numLevels, type, name := id.name, levelParams := default },
    induct, cidx, numParams, numFields, isUnsafe
  })

def addAxiom (env : Env) (id : MId)
    (type : E) (isUnsafe := false) (numLevels : Nat := 0) : Env :=
  env.insert id (.axiomInfo {
    toConstantVal := { numLevels, type, name := id.name, levelParams := default },
    isUnsafe
  })

def addRec (env : Env) (id : MId)
    (numLevels : Nat) (type : E) (all : Array MId)
    (numParams numIndices numMotives numMinors : Nat)
    (rules : Array (Ix.Kernel.RecursorRule .meta))
    (k := false) (isUnsafe := false) : Env :=
  env.insert id (.recInfo {
    toConstantVal := { numLevels, type, name := id.name, levelParams := default },
    all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe
  })

def addQuot (env : Env) (id : MId) (type : E)
    (kind : Ix.Kernel.QuotKind) (numLevels : Nat := 0) : Env :=
  env.insert id (.quotInfo {
    toConstantVal := { numLevels, type, name := id.name, levelParams := default },
    kind
  })

/-! ## Whole-constant type checking -/

def typecheckConstK2 (kenv : Env) (id : MId) (prims : Prims := Ix.Kernel.buildPrimitives .meta)
    (quotInit := false) : Except String Unit :=
  Ix.Kernel.typecheckConst kenv prims id (quotInit := quotInit)

/-! ## TypecheckM runner -/

def runK2 (kenv : Env) (action : ∀ σ, Ix.Kernel.TypecheckM σ .meta α)
    (prims : Prims := Ix.Kernel.buildPrimitives .meta)
    (quotInit : Bool := false) : Except String α :=
  Ix.Kernel.TypecheckM.runSimple kenv prims (quotInit := quotInit) (action := action)

def runK2Empty (action : ∀ σ, Ix.Kernel.TypecheckM σ .meta α) : Except String α :=
  runK2 default action

/-! ## Eval+quote convenience -/

def evalQuote (kenv : Env) (e : E) : Except String E :=
  runK2 kenv (fun _σ => do
    let v ← Ix.Kernel.eval e #[]
    Ix.Kernel.quote v 0)

def whnfK2 (kenv : Env) (e : E) (quotInit := false) : Except String E :=
  runK2 kenv (fun _σ => Ix.Kernel.whnf e) (quotInit := quotInit)

def evalQuoteEmpty (e : E) : Except String E :=
  evalQuote default e

def whnfEmpty (e : E) : Except String E :=
  whnfK2 default e

/-! ## isDefEq convenience -/

def isDefEqK2 (kenv : Env) (a b : E) (quotInit := false) : Except String Bool :=
  runK2 kenv (fun _σ => do
    let va ← Ix.Kernel.eval a #[]
    let vb ← Ix.Kernel.eval b #[]
    Ix.Kernel.isDefEq va vb) (quotInit := quotInit)

def isDefEqEmpty (a b : E) : Except String Bool :=
  isDefEqK2 default a b

/-! ## Check convenience (for error tests) -/

def checkK2 (kenv : Env) (term : E) (expectedType : E)
    (prims : Prims := Ix.Kernel.buildPrimitives .meta) : Except String Unit :=
  runK2 kenv (fun _σ => do
    let expectedVal ← Ix.Kernel.eval expectedType #[]
    let _ ← Ix.Kernel.check term expectedVal
    pure ()) prims

def whnfQuote (kenv : Env) (e : E) (quotInit := false) : Except String E :=
  runK2 kenv (fun _σ => do
    let v ← Ix.Kernel.eval e #[]
    let v' ← Ix.Kernel.whnfVal v
    Ix.Kernel.quote v' 0) (quotInit := quotInit)

/-! ## Shared environment builders -/

/-- MyNat inductive with zero, succ, rec. Returns (env, natId, zeroId, succId, recId). -/
def buildMyNatEnv (baseEnv : Env := default) : Env × MId × MId × MId × MId :=
  let natId := mkId "MyNat" 50
  let zeroId := mkId "MyNat.zero" 51
  let succId := mkId "MyNat.succ" 52
  let recId := mkId "MyNat.rec" 53
  let natType : E := Ix.Kernel.Expr.mkSort (.succ .zero)
  let natConst : E := Ix.Kernel.Expr.mkConst natId #[]
  let env := addInductive baseEnv natId natType #[zeroId, succId]
  let env := addCtor env zeroId natId natConst 0 0 0
  let succType : E := Ix.Kernel.Expr.mkForallE natConst natConst
  let env := addCtor env succId natId succType 1 0 1
  let recType : E :=
    Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkForallE natConst natType)  -- motive
      (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 0) (Ix.Kernel.Expr.mkConst zeroId #[]))  -- base
        (Ix.Kernel.Expr.mkForallE
          (Ix.Kernel.Expr.mkForallE natConst
            (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 2) (Ix.Kernel.Expr.mkBVar 0))
              (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 3) (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst succId #[]) (Ix.Kernel.Expr.mkBVar 1)))))
          (Ix.Kernel.Expr.mkForallE natConst
            (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 3) (Ix.Kernel.Expr.mkBVar 0)))))
  let motiveDom : E := Ix.Kernel.Expr.mkForallE natConst natType
  let baseDom : E := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 0) (Ix.Kernel.Expr.mkConst zeroId #[])
  let stepDom : E := Ix.Kernel.Expr.mkForallE natConst
    (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 2) (Ix.Kernel.Expr.mkBVar 0))
      (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 3) (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst succId #[]) (Ix.Kernel.Expr.mkBVar 1))))
  let zeroRhs : E := Ix.Kernel.Expr.mkLam motiveDom
    (Ix.Kernel.Expr.mkLam baseDom (Ix.Kernel.Expr.mkLam stepDom (Ix.Kernel.Expr.mkBVar 1)))
  let succRhs : E := Ix.Kernel.Expr.mkLam motiveDom
    (Ix.Kernel.Expr.mkLam baseDom
      (Ix.Kernel.Expr.mkLam stepDom
        (Ix.Kernel.Expr.mkLam natConst
          (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 1) (Ix.Kernel.Expr.mkBVar 0))
            (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp
              (Ix.Kernel.Expr.mkConst recId #[]) (Ix.Kernel.Expr.mkBVar 3)) (Ix.Kernel.Expr.mkBVar 2))
              (Ix.Kernel.Expr.mkBVar 1)) (Ix.Kernel.Expr.mkBVar 0))))))
  let env := addRec env recId 0 recType #[natId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 2)
    (rules := #[
      { ctor := zeroId, nfields := 0, rhs := zeroRhs },
      { ctor := succId, nfields := 1, rhs := succRhs }
    ])
  (env, natId, zeroId, succId, recId)

/-- MyTrue : Prop with intro, and K-recursor. Returns (env, trueId, introId, recId). -/
def buildMyTrueEnv (baseEnv : Env := default) : Env × MId × MId × MId :=
  let trueId := mkId "MyTrue" 120
  let introId := mkId "MyTrue.intro" 121
  let recId := mkId "MyTrue.rec" 122
  let propE : E := Ix.Kernel.Expr.mkSort .zero
  let trueConst : E := Ix.Kernel.Expr.mkConst trueId #[]
  let env := addInductive baseEnv trueId propE #[introId]
  let env := addCtor env introId trueId trueConst 0 0 0
  let recType : E :=
    Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkForallE trueConst propE)  -- motive
      (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 0) (Ix.Kernel.Expr.mkConst introId #[]))  -- h : motive intro
        (Ix.Kernel.Expr.mkForallE trueConst  -- t : MyTrue
          (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 2) (Ix.Kernel.Expr.mkBVar 0))))  -- motive t
  let motiveDom : E := Ix.Kernel.Expr.mkForallE trueConst propE
  let hDom : E := Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 0) (Ix.Kernel.Expr.mkConst introId #[])
  let ruleRhs : E := Ix.Kernel.Expr.mkLam motiveDom
    (Ix.Kernel.Expr.mkLam hDom (Ix.Kernel.Expr.mkBVar 0))
  let env := addRec env recId 0 recType #[trueId]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 1)
    (rules := #[{ ctor := introId, nfields := 0, rhs := ruleRhs }])
    (k := true)
  (env, trueId, introId, recId)

/-- Pair inductive. Returns (env, pairId, pairCtorId). -/
def buildPairEnv (baseEnv : Env := default) : Env × MId × MId :=
  let pairId := mkId "Pair" 160
  let pairCtorId := mkId "Pair.mk" 161
  let tyE : E := Ix.Kernel.Expr.mkSort (.succ .zero)
  let env := addInductive baseEnv pairId
    (Ix.Kernel.Expr.mkForallE tyE (Ix.Kernel.Expr.mkForallE tyE tyE))
    #[pairCtorId] (numParams := 2)
  let ctorType := Ix.Kernel.Expr.mkForallE tyE (Ix.Kernel.Expr.mkForallE tyE
    (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkBVar 1) (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkBVar 1)
      (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst pairId #[]) (Ix.Kernel.Expr.mkBVar 3)) (Ix.Kernel.Expr.mkBVar 2)))))
  let env := addCtor env pairCtorId pairId ctorType 0 2 2
  (env, pairId, pairCtorId)

/-! ## Val inspection helpers -/

/-- Get the head const address of a whnf result (if it's a const-headed neutral or ctor). -/
def whnfHeadAddr (kenv : Env) (e : E) (prims : Prims := Ix.Kernel.buildPrimitives .meta)
    (quotInit := false) : Except String (Option Address) :=
  runK2 kenv (fun _σ => do
    let v ← Ix.Kernel.eval e #[]
    let v' ← Ix.Kernel.whnfVal v
    match v' with
    | .neutral (.const id _) _ => pure (some id.addr)
    | .ctor id _ _ _ _ _ _ => pure (some id.addr)
    | _ => pure none) prims (quotInit := quotInit)

/-- Check if whnf result is a literal nat. -/
def whnfIsNatLit (kenv : Env) (e : E) : Except String (Option Nat) :=
  runK2 kenv (fun _σ => do
    let v ← Ix.Kernel.eval e #[]
    let v' ← Ix.Kernel.whnfVal v
    match v' with
    | .lit (.natVal n) => pure (some n)
    | _ => pure none)

/-- Run with custom prims. -/
def whnfK2WithPrims (kenv : Env) (e : E) (prims : Prims) (quotInit := false) : Except String E :=
  runK2 kenv (fun _σ => Ix.Kernel.whnf e) prims (quotInit := quotInit)

/-- Get error message from a failed computation. -/
def getError (result : Except String α) : Option String :=
  match result with
  | .error e => some e
  | .ok _ => none

/-! ## Inference convenience -/

def inferK2 (kenv : Env) (e : E)
    (prims : Prims := Ix.Kernel.buildPrimitives .meta) : Except String E :=
  runK2 kenv (fun _σ => do
    let (_, typVal) ← Ix.Kernel.infer e
    let d ← Ix.Kernel.depth
    Ix.Kernel.quote typVal d) prims

def inferEmpty (e : E) : Except String E :=
  inferK2 default e

def isSortK2 (kenv : Env) (e : E) : Except String L :=
  runK2 kenv (fun _σ => do
    let (_, lvl) ← Ix.Kernel.isSort e
    pure lvl)

end Tests.Ix.Kernel.Helpers
