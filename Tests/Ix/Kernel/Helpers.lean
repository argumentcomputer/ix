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
abbrev Prims := Ix.Kernel.Primitives

/-! ## Env-building helpers -/

def addDef (env : Env) (addr : Address) (type value : E)
    (numLevels : Nat := 0) (hints : Ix.Kernel.ReducibilityHints := .abbrev)
    (safety : Ix.Kernel.DefinitionSafety := .safe) : Env :=
  env.insert addr (.defnInfo {
    toConstantVal := { numLevels, type, name := default, levelParams := default },
    value, hints, safety, all := #[addr]
  })

def addOpaque (env : Env) (addr : Address) (type value : E)
    (numLevels : Nat := 0) (isUnsafe := false) : Env :=
  env.insert addr (.opaqueInfo {
    toConstantVal := { numLevels, type, name := default, levelParams := default },
    value, isUnsafe, all := #[addr]
  })

def addTheorem (env : Env) (addr : Address) (type value : E)
    (numLevels : Nat := 0) : Env :=
  env.insert addr (.thmInfo {
    toConstantVal := { numLevels, type, name := default, levelParams := default },
    value, all := #[addr]
  })

def addInductive (env : Env) (addr : Address)
    (type : E) (ctors : Array Address)
    (numParams numIndices : Nat := 0) (isRec := false)
    (isUnsafe := false) (numNested := 0)
    (numLevels : Nat := 0) (all : Array Address := #[addr]) : Env :=
  env.insert addr (.inductInfo {
    toConstantVal := { numLevels, type, name := default, levelParams := default },
    numParams, numIndices, all, ctors, numNested,
    isRec, isUnsafe, isReflexive := false
  })

def addCtor (env : Env) (addr : Address) (induct : Address)
    (type : E) (cidx numParams numFields : Nat)
    (isUnsafe := false) (numLevels : Nat := 0) : Env :=
  env.insert addr (.ctorInfo {
    toConstantVal := { numLevels, type, name := default, levelParams := default },
    induct, cidx, numParams, numFields, isUnsafe
  })

def addAxiom (env : Env) (addr : Address)
    (type : E) (isUnsafe := false) (numLevels : Nat := 0) : Env :=
  env.insert addr (.axiomInfo {
    toConstantVal := { numLevels, type, name := default, levelParams := default },
    isUnsafe
  })

def addRec (env : Env) (addr : Address)
    (numLevels : Nat) (type : E) (all : Array Address)
    (numParams numIndices numMotives numMinors : Nat)
    (rules : Array (Ix.Kernel.RecursorRule .meta))
    (k := false) (isUnsafe := false) : Env :=
  env.insert addr (.recInfo {
    toConstantVal := { numLevels, type, name := default, levelParams := default },
    all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe
  })

def addQuot (env : Env) (addr : Address) (type : E)
    (kind : Ix.Kernel.QuotKind) (numLevels : Nat := 0) : Env :=
  env.insert addr (.quotInfo {
    toConstantVal := { numLevels, type, name := default, levelParams := default },
    kind
  })

/-! ## TypecheckM runner -/

def runK2 (kenv : Env) (action : ∀ σ, Ix.Kernel.TypecheckM σ .meta α)
    (prims : Prims := Ix.Kernel.buildPrimitives)
    (quotInit : Bool := false) : Except String α :=
  match Ix.Kernel.TypecheckM.runSimple kenv prims (quotInit := quotInit) (action := action) with
  | .ok (a, _) => .ok a
  | .error e => .error e

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
    (prims : Prims := Ix.Kernel.buildPrimitives) : Except String Unit :=
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

/-- MyNat inductive with zero, succ, rec. Returns (env, natIndAddr, zeroAddr, succAddr, recAddr). -/
def buildMyNatEnv (baseEnv : Env := default) : Env × Address × Address × Address × Address :=
  let natIndAddr := mkAddr 50
  let zeroAddr := mkAddr 51
  let succAddr := mkAddr 52
  let recAddr := mkAddr 53
  let natType : E := Ix.Kernel.Expr.mkSort (.succ .zero)
  let natConst : E := Ix.Kernel.Expr.mkConst natIndAddr #[]
  let env := addInductive baseEnv natIndAddr natType #[zeroAddr, succAddr]
  let env := addCtor env zeroAddr natIndAddr natConst 0 0 0
  let succType : E := Ix.Kernel.Expr.mkForallE natConst natConst
  let env := addCtor env succAddr natIndAddr succType 1 0 1
  let recType : E :=
    Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkForallE natConst natType)  -- motive
      (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 0) (Ix.Kernel.Expr.mkConst zeroAddr #[]))  -- base
        (Ix.Kernel.Expr.mkForallE
          (Ix.Kernel.Expr.mkForallE natConst
            (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 2) (Ix.Kernel.Expr.mkBVar 0))
              (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 3) (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst succAddr #[]) (Ix.Kernel.Expr.mkBVar 1)))))
          (Ix.Kernel.Expr.mkForallE natConst
            (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 3) (Ix.Kernel.Expr.mkBVar 0)))))
  -- Rule for zero: nfields=0, rhs = λ motive base step => base
  let zeroRhs : E := Ix.Kernel.Expr.mkLam natType
    (Ix.Kernel.Expr.mkLam (Ix.Kernel.Expr.mkBVar 0) (Ix.Kernel.Expr.mkLam natType (Ix.Kernel.Expr.mkBVar 1)))
  -- Rule for succ: nfields=1, rhs = λ motive base step n => step n (rec motive base step n)
  let succRhs : E := Ix.Kernel.Expr.mkLam natType
    (Ix.Kernel.Expr.mkLam (Ix.Kernel.Expr.mkBVar 0)
      (Ix.Kernel.Expr.mkLam natType
        (Ix.Kernel.Expr.mkLam natConst
          (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 1) (Ix.Kernel.Expr.mkBVar 0))
            (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp
              (Ix.Kernel.Expr.mkConst recAddr #[]) (Ix.Kernel.Expr.mkBVar 3)) (Ix.Kernel.Expr.mkBVar 2))
              (Ix.Kernel.Expr.mkBVar 1)) (Ix.Kernel.Expr.mkBVar 0))))))
  let env := addRec env recAddr 0 recType #[natIndAddr]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 2)
    (rules := #[
      { ctor := zeroAddr, nfields := 0, rhs := zeroRhs },
      { ctor := succAddr, nfields := 1, rhs := succRhs }
    ])
  (env, natIndAddr, zeroAddr, succAddr, recAddr)

/-- MyTrue : Prop with intro, and K-recursor. Returns (env, trueIndAddr, introAddr, recAddr). -/
def buildMyTrueEnv (baseEnv : Env := default) : Env × Address × Address × Address :=
  let trueIndAddr := mkAddr 120
  let introAddr := mkAddr 121
  let recAddr := mkAddr 122
  let propE : E := Ix.Kernel.Expr.mkSort .zero
  let trueConst : E := Ix.Kernel.Expr.mkConst trueIndAddr #[]
  let env := addInductive baseEnv trueIndAddr propE #[introAddr]
  let env := addCtor env introAddr trueIndAddr trueConst 0 0 0
  let recType : E :=
    Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkForallE trueConst propE)  -- motive
      (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 0) (Ix.Kernel.Expr.mkConst introAddr #[]))  -- h : motive intro
        (Ix.Kernel.Expr.mkForallE trueConst  -- t : MyTrue
          (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkBVar 2) (Ix.Kernel.Expr.mkBVar 0))))  -- motive t
  let ruleRhs : E := Ix.Kernel.Expr.mkLam (Ix.Kernel.Expr.mkForallE trueConst propE)
    (Ix.Kernel.Expr.mkLam propE (Ix.Kernel.Expr.mkBVar 0))
  let env := addRec env recAddr 0 recType #[trueIndAddr]
    (numParams := 0) (numIndices := 0) (numMotives := 1) (numMinors := 1)
    (rules := #[{ ctor := introAddr, nfields := 0, rhs := ruleRhs }])
    (k := true)
  (env, trueIndAddr, introAddr, recAddr)

/-- Pair inductive. Returns (env, pairIndAddr, pairCtorAddr). -/
def buildPairEnv (baseEnv : Env := default) : Env × Address × Address :=
  let pairIndAddr := mkAddr 160
  let pairCtorAddr := mkAddr 161
  let tyE : E := Ix.Kernel.Expr.mkSort (.succ .zero)
  let env := addInductive baseEnv pairIndAddr
    (Ix.Kernel.Expr.mkForallE tyE (Ix.Kernel.Expr.mkForallE tyE tyE))
    #[pairCtorAddr] (numParams := 2)
  let ctorType := Ix.Kernel.Expr.mkForallE tyE (Ix.Kernel.Expr.mkForallE tyE
    (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkBVar 1) (Ix.Kernel.Expr.mkForallE (Ix.Kernel.Expr.mkBVar 1)
      (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkApp (Ix.Kernel.Expr.mkConst pairIndAddr #[]) (Ix.Kernel.Expr.mkBVar 3)) (Ix.Kernel.Expr.mkBVar 2)))))
  let env := addCtor env pairCtorAddr pairIndAddr ctorType 0 2 2
  (env, pairIndAddr, pairCtorAddr)

/-! ## Val inspection helpers -/

/-- Get the head const address of a whnf result (if it's a const-headed neutral or ctor). -/
def whnfHeadAddr (kenv : Env) (e : E) (prims : Prims := Ix.Kernel.buildPrimitives)
    (quotInit := false) : Except String (Option Address) :=
  runK2 kenv (fun _σ => do
    let v ← Ix.Kernel.eval e #[]
    let v' ← Ix.Kernel.whnfVal v
    match v' with
    | .neutral (.const addr _ _) _ => pure (some addr)
    | .ctor addr _ _ _ _ _ _ _ => pure (some addr)
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
    (prims : Prims := Ix.Kernel.buildPrimitives) : Except String E :=
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
