/-
  Generators for Ix.* types (canonical Lean types with Blake3 hashes).
  Generators for property-based FFI roundtrip tests.
-/

import LSpec
import Tests.Gen.Basic
import Tests.Gen.Ixon
import Ix.Address
import Ix.Environment
import Ix.CondenseM
import Ix.CompileM
import Ix.DecompileM

open LSpec SlimCheck Gen

namespace Tests.Gen.Ix

/-! ## Ix type generators -/

/-- Generate Ix.Name with deeper nesting -/
def genIxName : Nat → Gen Ix.Name
  | 0 => pure Ix.Name.mkAnon
  | fuel + 1 => Gen.frequency #[
      (1, pure Ix.Name.mkAnon),
      (4, do
        let parent ← genIxName fuel
        let len ← choose Nat 1 12
        let chars ← Gen.listOf (choose Nat 97 122 >>= fun n => pure (Char.ofNat n))
        let s := String.ofList (chars.take len)
        pure (Ix.Name.mkStr parent s)),
      (3, do
        let parent ← genIxName fuel
        let n ← choose Nat 0 1000
        pure (Ix.Name.mkNat parent n))
    ] (pure Ix.Name.mkAnon)

/-- Generate Ix.Level with deeper nesting -/
def genIxLevel : Nat → Gen Ix.Level
  | 0 => Gen.frequency #[
      (3, pure Ix.Level.mkZero),
      (2, do let n ← genIxName 2; pure (Ix.Level.mkParam n))
    ] (pure Ix.Level.mkZero)
  | fuel + 1 => Gen.frequency #[
      (3, pure Ix.Level.mkZero),
      (4, do
        let x ← genIxLevel fuel
        pure (Ix.Level.mkSucc x)),
      (2, do
        let x ← genIxLevel (fuel / 2)
        let y ← genIxLevel (fuel / 2)
        pure (Ix.Level.mkMax x y)),
      (2, do
        let x ← genIxLevel (fuel / 2)
        let y ← genIxLevel (fuel / 2)
        pure (Ix.Level.mkIMax x y)),
      (3, do
        let n ← genIxName 3
        pure (Ix.Level.mkParam n)),
      (1, do
        let n ← genIxName 3
        pure (Ix.Level.mkMvar n))
    ] (pure Ix.Level.mkZero)

/-- Generate BinderInfo with varied distribution -/
def genBinderInfo : Gen Lean.BinderInfo :=
  frequency [
    (10, pure .default),
    (3, pure .implicit),
    (2, pure .strictImplicit),
    (3, pure .instImplicit),
  ]

/-- Generate a Literal -/
def genLiteral : Gen Lean.Literal :=
  frequency [
    (5, Lean.Literal.natVal <$> choose Nat 0 1000),
    (5, Lean.Literal.strVal <$> Gen.elements #["hello", "world", "foo", "bar", "test", "literal"]),
  ]

/-- Generate an Ix.Int for DataValue -/
def genIxInt : Gen Ix.Int :=
  frequency [
    (5, Ix.Int.ofNat <$> choose Nat 0 100),
    (5, Ix.Int.negSucc <$> choose Nat 0 50),
  ]

/-- Generate a random string from a list of options -/
def genIxString : Gen String :=
  Gen.elements #["foo", "bar", "test", "x", "y", "value", "item", "data", "node", "leaf"]

/-- Generate Ix.Substring -/
def genIxSubstring : Gen Ix.Substring := do
  let s ← Gen.elements #["hello world", "test string", "foo bar baz", "quick brown fox", "lorem ipsum"]
  let maxLen := s.length
  let startPos ← choose Nat 0 (maxLen / 2)
  let stopPos ← choose Nat startPos maxLen
  pure (Ix.Substring.mk s startPos stopPos)

instance : Shrinkable Ix.Name where
  shrink n := match n with
    | .anonymous _ => []
    | .str p _ _ => [p]
    | .num p _ _ => [p]

instance : Shrinkable Ix.Substring where
  shrink ss :=
    (if ss.str.length > 0 then [{ ss with str := "", startPos := 0, stopPos := 0 }] else []) ++
    (if ss.stopPos > ss.startPos then [{ ss with stopPos := ss.startPos }] else [])
instance : SampleableExt Ix.Substring := SampleableExt.mkSelfContained genIxSubstring

/-- Generate Ix.SourceInfo with all variants -/
def genIxSourceInfo : Gen Ix.SourceInfo :=
  frequency [
    (5, pure Ix.SourceInfo.none),
    (3, do
      let leading ← genIxSubstring
      let leadingPos ← choose Nat 0 100
      let trailing ← genIxSubstring
      let trailingPos ← choose Nat 0 100
      pure (Ix.SourceInfo.original leading leadingPos trailing trailingPos)),
    (2, do
      let start ← choose Nat 0 100
      let stop ← choose Nat 100 200
      let canonical ← frequency [(1, pure true), (1, pure false)]
      pure (Ix.SourceInfo.synthetic start stop canonical)),
  ]

instance : Shrinkable Ix.SourceInfo where
  shrink si := match si with
    | .none => []
    | _ => [.none]

instance : SampleableExt Ix.SourceInfo := SampleableExt.mkSelfContained genIxSourceInfo

/-- Generate Ix.SyntaxPreresolved with all variants -/
def genIxSyntaxPreresolved : Gen Ix.SyntaxPreresolved :=
  frequency [
    (1, Ix.SyntaxPreresolved.namespace <$> genIxName 3),
    (1, do
      let name ← genIxName 3
      let numAliases ← Gen.choose Nat 0 3
      let mut aliases : Array String := #[]
      for _ in [:numAliases] do
        aliases := aliases.push (← genIxString)
      pure (Ix.SyntaxPreresolved.decl name aliases)),
  ]

instance : Shrinkable Ix.SyntaxPreresolved where
  shrink sp := match sp with
    | .namespace n => .namespace <$> Shrinkable.shrink n
    | .decl n aliases =>
      [.namespace n] ++
      (if aliases.size > 0 then [.decl n aliases.pop] else []) ++
      ((.decl · aliases) <$> Shrinkable.shrink n)
instance : SampleableExt Ix.SyntaxPreresolved := SampleableExt.mkSelfContained genIxSyntaxPreresolved

/-- Generate Ix.Syntax with all variants including node -/
def genIxSyntaxAux : Nat → Gen Ix.Syntax
  | 0 => frequency [
      (10, pure Ix.Syntax.missing),
      (5, Ix.Syntax.atom <$> genIxSourceInfo <*> genIxString),
      (5, do
        let info ← genIxSourceInfo
        let rawVal ← genIxSubstring
        let name ← genIxName 2
        let numPreresolved ← Gen.choose Nat 0 2
        let mut preresolved : Array Ix.SyntaxPreresolved := #[]
        for _ in [:numPreresolved] do
          preresolved := preresolved.push (← genIxSyntaxPreresolved)
        pure (Ix.Syntax.ident info rawVal name preresolved)),
    ]
  | fuel + 1 => frequency [
      (10, pure Ix.Syntax.missing),
      (5, Ix.Syntax.atom <$> genIxSourceInfo <*> genIxString),
      (5, do
        let info ← genIxSourceInfo
        let rawVal ← genIxSubstring
        let name ← genIxName 2
        let numPreresolved ← Gen.choose Nat 0 2
        let mut preresolved : Array Ix.SyntaxPreresolved := #[]
        for _ in [:numPreresolved] do
          preresolved := preresolved.push (← genIxSyntaxPreresolved)
        pure (Ix.Syntax.ident info rawVal name preresolved)),
      (3, do
        let info ← genIxSourceInfo
        let kind ← genIxName 2
        let numChildren ← Gen.choose Nat 0 3
        let mut children : Array Ix.Syntax := #[]
        for _ in [:numChildren] do
          children := children.push (← genIxSyntaxAux (fuel / 2))
        pure (Ix.Syntax.node info kind children)),
    ]

def genIxSyntax : Gen Ix.Syntax := genIxSyntaxAux 3

/-- Generate Ix.DataValue with all variants -/
def genIxDataValue : Gen Ix.DataValue :=
  frequency [
    (10, Ix.DataValue.ofString <$> genIxString),
    (10, Ix.DataValue.ofBool <$> frequency [(1, pure true), (1, pure false)]),
    (10, Ix.DataValue.ofName <$> genIxName 3),
    (10, Ix.DataValue.ofNat <$> choose Nat 0 1000),
    (10, Ix.DataValue.ofInt <$> genIxInt),
    (5, Ix.DataValue.ofSyntax <$> genIxSyntax),
  ]

/-- Generate Ix.Expr with all variants and deeper nesting -/
def genIxExpr : Nat → Gen Ix.Expr
  | 0 => Gen.frequency #[
      (3, do let idx ← choose Nat 0 20; pure (Ix.Expr.mkBVar idx)),
      (2, do let u ← genIxLevel 3; pure (Ix.Expr.mkSort u)),
      (2, do let n ← genIxName 3; pure (Ix.Expr.mkFVar n)),
      (1, Ix.Expr.mkLit <$> genLiteral)
    ] (pure (Ix.Expr.mkBVar 0))
  | fuel + 1 => Gen.frequency #[
      -- Base cases (weighted higher to ensure termination)
      (4, do let idx ← choose Nat 0 20; pure (Ix.Expr.mkBVar idx)),
      (2, do let u ← genIxLevel 4; pure (Ix.Expr.mkSort u)),
      (2, do let n ← genIxName 4; pure (Ix.Expr.mkFVar n)),
      (1, do let n ← genIxName 4; pure (Ix.Expr.mkMVar n)),
      (2, Ix.Expr.mkLit <$> genLiteral),
      -- Const with universe levels
      (4, do
        let n ← genIxName 4
        let numLevels ← choose Nat 0 4
        let mut levels : Array Ix.Level := #[]
        for _ in [:numLevels] do
          levels := levels.push (← genIxLevel 4)
        pure (Ix.Expr.mkConst n levels)),
      -- App - function application
      (5, do
        let f ← genIxExpr (fuel / 2)
        let a ← genIxExpr (fuel / 2)
        pure (Ix.Expr.mkApp f a)),
      -- Lambda with varied binder info
      (4, do
        let n ← genIxName 3
        let bi ← genBinderInfo
        let ty ← genIxExpr (fuel / 2)
        let body ← genIxExpr (fuel / 2)
        pure (Ix.Expr.mkLam n ty body bi)),
      -- ForallE with varied binder info
      (4, do
        let n ← genIxName 3
        let bi ← genBinderInfo
        let ty ← genIxExpr (fuel / 2)
        let body ← genIxExpr (fuel / 2)
        pure (Ix.Expr.mkForallE n ty body bi)),
      -- LetE
      (3, do
        let n ← genIxName 3
        let ty ← genIxExpr (fuel / 3)
        let val ← genIxExpr (fuel / 3)
        let body ← genIxExpr (fuel / 3)
        let nonDep ← frequency [(1, pure true), (1, pure false)]
        pure (Ix.Expr.mkLetE n ty val body nonDep)),
      -- MData with metadata
      (2, do
        let numEntries ← choose Nat 1 4
        let mut entries : Array (Ix.Name × Ix.DataValue) := #[]
        for _ in [:numEntries] do
          let key ← genIxName 2
          let val ← genIxDataValue
          entries := entries.push (key, val)
        let e ← genIxExpr (fuel / 2)
        pure (Ix.Expr.mkMData entries e)),
      -- Proj
      (2, do
        let typeName ← genIxName 4
        let idx ← choose Nat 0 10
        let struct ← genIxExpr (fuel / 2)
        pure (Ix.Expr.mkProj typeName idx struct))
    ] (pure (Ix.Expr.mkBVar 0))

instance : SampleableExt Ix.Name := SampleableExt.mkSelfContained (genIxName 5)

instance : Shrinkable Ix.Level where
  shrink l := match l with
    | .zero _ => []
    | .succ x _ => [x]
    | .max x y _ => [x, y]
    | .imax x y _ => [x, y]
    | .param _ _ => [Ix.Level.mkZero]
    | .mvar _ _ => [Ix.Level.mkZero]

instance : SampleableExt Ix.Level := SampleableExt.mkSelfContained (genIxLevel 5)

instance : Shrinkable Ix.Expr where
  shrink e := match e with
    | .bvar _ _ => []
    | .fvar _ _ => [Ix.Expr.mkBVar 0]
    | .mvar _ _ => [Ix.Expr.mkBVar 0]
    | .sort _ _ => [Ix.Expr.mkBVar 0]
    | .const _ _ _ => [Ix.Expr.mkBVar 0]
    | .app f a _ => [f, a]
    | .lam _ ty body _ _ => [ty, body]
    | .forallE _ ty body _ _ => [ty, body]
    | .letE _ ty val body _ _ => [ty, val, body]
    | .lit _ _ => [Ix.Expr.mkBVar 0]
    | .mdata _ e _ => [e]
    | .proj _ _ e _ => [e]

instance : SampleableExt Ix.Expr := SampleableExt.mkSelfContained (genIxExpr 5)

/-- Generate an array of level parameter names with varied sizes -/
def genLevelParams : Gen (Array Ix.Name) := do
  let numParams ← choose Nat 0 5
  let mut params : Array Ix.Name := #[]
  for i in [:numParams] do
    -- Use varied names, not just u, v, w
    let baseName ← frequency [
      (3, pure "u"),
      (3, pure "v"),
      (2, pure "w"),
      (2, pure "α"),
      (2, pure "β"),
    ]
    params := params.push (Ix.Name.mkStr Ix.Name.mkAnon s!"{baseName}{i}")
  pure params

/-- Generate a random Ix.ConstantVal with varied complexity -/
def genIxConstantVal : Gen Ix.ConstantVal :=
  Ix.ConstantVal.mk <$> genIxName 5 <*> genLevelParams <*> genIxExpr 5

/-- Generate a random Ix.AxiomVal -/
def genIxAxiomVal : Gen Ix.AxiomVal :=
  Ix.AxiomVal.mk <$> genIxConstantVal <*> frequency [(9, pure false), (1, pure true)]

/-- Generate ReducibilityHints -/
def genReducibilityHints : Gen Lean.ReducibilityHints :=
  frequency [
    (3, pure .opaque),
    (3, pure .abbrev),
    (4, Lean.ReducibilityHints.regular <$> genUInt32),
  ]

/-- Generate DefinitionSafety -/
def genDefinitionSafety : Gen Lean.DefinitionSafety :=
  frequency [
    (8, pure .safe),
    (1, pure .unsafe),
    (1, pure .partial),
  ]

/-- Generate an array of mutually recursive names -/
def genMutualNames (baseName : Ix.Name) : Gen (Array Ix.Name) := do
  let numMutual ← choose Nat 1 4
  let mut names : Array Ix.Name := #[baseName]
  for i in [1:numMutual] do
    names := names.push (Ix.Name.mkStr baseName s!"_mutual_{i}")
  pure names

/-- Generate a random Ix.DefinitionVal -/
def genIxDefinitionVal : Gen Ix.DefinitionVal := do
  let cnst ← genIxConstantVal
  let value ← genIxExpr 5
  let hints ← genReducibilityHints
  let safety ← genDefinitionSafety
  let all ← genMutualNames cnst.name
  pure { cnst, value, hints, safety, all }

/-- Generate a random Ix.TheoremVal -/
def genIxTheoremVal : Gen Ix.TheoremVal := do
  let cnst ← genIxConstantVal
  let value ← genIxExpr 5
  let all ← genMutualNames cnst.name
  pure { cnst, value, all }

/-- Generate a random Ix.OpaqueVal -/
def genIxOpaqueVal : Gen Ix.OpaqueVal := do
  let cnst ← genIxConstantVal
  let value ← genIxExpr 5
  let isUnsafe ← frequency [(9, pure false), (1, pure true)]
  let all ← genMutualNames cnst.name
  pure { cnst, value, isUnsafe, all }

/-- Generate QuotKind -/
def genQuotKind : Gen Lean.QuotKind :=
  frequency [
    (1, pure .type),
    (1, pure .ctor),
    (1, pure .lift),
    (1, pure .ind),
  ]

/-- Generate a random Ix.QuotVal -/
def genIxQuotVal : Gen Ix.QuotVal :=
  Ix.QuotVal.mk <$> genIxConstantVal <*> genQuotKind

/-- Generate constructor names for an inductive -/
def genConstructorNames (inductName : Ix.Name) : Gen (Array Ix.Name) := do
  let numCtors ← choose Nat 1 5
  let mut ctors : Array Ix.Name := #[]
  let ctorNames := #["mk", "nil", "cons", "zero", "succ", "inl", "inr", "intro", "refl"]
  for i in [:numCtors] do
    let suffix := if i < ctorNames.size then ctorNames[i]! else s!"ctor{i}"
    ctors := ctors.push (Ix.Name.mkStr inductName suffix)
  pure ctors

/-- Generate a random Ix.InductiveVal -/
def genIxInductiveVal : Gen Ix.InductiveVal := do
  let cnst ← genIxConstantVal
  let numParams ← choose Nat 0 5
  let numIndices ← choose Nat 0 3
  let isRec ← frequency [(6, pure false), (4, pure true)]
  let isUnsafe ← frequency [(9, pure false), (1, pure true)]
  let isReflexive ← frequency [(7, pure false), (3, pure true)]
  let numNested ← choose Nat 0 3
  let all ← genMutualNames cnst.name
  let ctors ← genConstructorNames cnst.name
  pure {
    cnst
    numParams
    numIndices
    all
    ctors
    numNested
    isRec
    isUnsafe
    isReflexive
  }

/-- Generate a random Ix.ConstructorVal -/
def genIxConstructorVal : Gen Ix.ConstructorVal := do
  let cnst ← genIxConstantVal
  let induct ← genIxName 5
  let cidx ← choose Nat 0 10
  let numParams ← choose Nat 0 5
  let numFields ← choose Nat 0 8
  let isUnsafe ← frequency [(9, pure false), (1, pure true)]
  pure { cnst, induct, cidx, numParams, numFields, isUnsafe }

/-- Generate a random Ix.RecursorRule -/
def genIxRecursorRule : Gen Ix.RecursorRule := do
  let ctor ← genIxName 5
  let nfields ← choose Nat 0 8
  let rhs ← genIxExpr 5
  pure { ctor, nfields, rhs }

/-- Generate a random Ix.RecursorVal -/
def genIxRecursorVal : Gen Ix.RecursorVal := do
  let cnst ← genIxConstantVal
  let all ← genMutualNames cnst.name
  let numParams ← choose Nat 0 5
  let numIndices ← choose Nat 0 3
  let numMotives ← choose Nat 1 4
  let numMinors ← choose Nat 0 6
  let numRules ← choose Nat 1 5
  let mut rules : Array Ix.RecursorRule := #[]
  for _ in [:numRules] do
    rules := rules.push (← genIxRecursorRule)
  let k ← frequency [(7, pure false), (3, pure true)]
  let isUnsafe ← frequency [(9, pure false), (1, pure true)]
  pure { cnst, all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe }

instance : Inhabited Ix.ConstantInfo where
  default := .axiomInfo { cnst := { name := Ix.Name.mkAnon, levelParams := #[], type := Ix.Expr.mkSort Ix.Level.mkZero }, isUnsafe := false }

/-- Generate a random Ix.ConstantInfo with all variants -/
def genIxConstantInfo : Gen Ix.ConstantInfo :=
  frequency [
    (15, Ix.ConstantInfo.axiomInfo <$> genIxAxiomVal),
    (15, Ix.ConstantInfo.defnInfo <$> genIxDefinitionVal),
    (10, Ix.ConstantInfo.thmInfo <$> genIxTheoremVal),
    (10, Ix.ConstantInfo.opaqueInfo <$> genIxOpaqueVal),
    (10, Ix.ConstantInfo.quotInfo <$> genIxQuotVal),
    (15, Ix.ConstantInfo.inductInfo <$> genIxInductiveVal),
    (15, Ix.ConstantInfo.ctorInfo <$> genIxConstructorVal),
    (10, Ix.ConstantInfo.recInfo <$> genIxRecursorVal),
  ]

instance : Shrinkable Ix.ConstantInfo where
  shrink info :=
    -- Shrink to a simple axiom
    let simpleName := Ix.Name.mkAnon
    let simpleType := Ix.Expr.mkSort Ix.Level.mkZero
    let simpleCnst : Ix.ConstantVal := { name := simpleName, levelParams := #[], type := simpleType }
    match info with
    | .axiomInfo _ => []
    | _ => [.axiomInfo { cnst := simpleCnst, isUnsafe := false }]

instance : SampleableExt Ix.ConstantInfo := SampleableExt.mkSelfContained genIxConstantInfo

/-! ## Generators for Ix.RawEnvironment -/

/-- Generate small arrays for RawEnvironment to avoid memory issues -/
def genSmallArray (g : Gen α) : Gen (Array α) :=
  resize (fun s => if s > 3 then 3 else s / 2) <|
  Array.mk <$> (listOf g >>= fun l => pure (l.take 3))

/-- Generate a simple ConstantInfo (only axiomInfo for FFI stability) -/
def genSimpleConstantInfo : Gen Ix.ConstantInfo :=
  Ix.ConstantInfo.axiomInfo <$> genIxAxiomVal

/-- Generate a (Name × ConstantInfo) pair for RawEnvironment -/
def genNameConstantPair : Gen (Ix.Name × Ix.ConstantInfo) :=
  Prod.mk <$> genIxName 3 <*> genSimpleConstantInfo

/-- Generate a RawEnvironment with small arrays to avoid memory issues -/
def genIxRawEnvironment : Gen Ix.RawEnvironment :=
  Ix.RawEnvironment.mk <$> genSmallArray genNameConstantPair

instance : Shrinkable Ix.RawEnvironment where
  shrink env := if env.consts.isEmpty then [] else [{ consts := env.consts.pop }]

instance : SampleableExt Ix.RawEnvironment := SampleableExt.mkSelfContained genIxRawEnvironment

/-! ## Generators for Additional Ix Types -/

def genAddress : Gen Address := Tests.Gen.Ixon.genAddress

instance : Shrinkable Address where shrink _ := []
instance : SampleableExt Address := SampleableExt.mkSelfContained genAddress

-- Ix.Int already has genIxInt defined earlier
instance : Shrinkable Ix.Int where
  shrink i := match i with
    | .ofNat n => if n > 0 then [.ofNat (n / 2)] else []
    | .negSucc n => [.ofNat 0] ++ if n > 0 then [.negSucc (n / 2)] else []

instance : SampleableExt Ix.Int := SampleableExt.mkSelfContained genIxInt

-- Ix.Syntax already has genIxSyntax defined earlier
instance : Shrinkable Ix.Syntax where
  shrink s := match s with
    | .missing => []
    | _ => [.missing]

instance : SampleableExt Ix.Syntax := SampleableExt.mkSelfContained genIxSyntax

-- Ix.DataValue already has genIxDataValue defined earlier
instance : Shrinkable Ix.DataValue where
  shrink dv := match dv with
    | .ofBool _ => []
    | _ => [.ofBool true]

instance : SampleableExt Ix.DataValue := SampleableExt.mkSelfContained genIxDataValue

/-! ## Generators for RustCondensedBlocks and RustCompilePhases -/

/-- Generate a (Name × Name) pair for lowLinks -/
def genNamePair : Gen (Ix.Name × Ix.Name) :=
  Prod.mk <$> genIxName 3 <*> genIxName 3

/-- Generate a (Name × Array Name) pair for blocks/blockRefs -/
def genNameArrayPair : Gen (Ix.Name × Array Ix.Name) := do
  let name ← genIxName 3
  let arr ← genSmallArray (genIxName 3)
  pure (name, arr)

/-- Generate Ix.RustCondensedBlocks -/
def genRustCondensedBlocks : Gen Ix.RustCondensedBlocks :=
  Ix.RustCondensedBlocks.mk
    <$> genSmallArray genNamePair
    <*> genSmallArray genNameArrayPair
    <*> genSmallArray genNameArrayPair

instance : Shrinkable Ix.RustCondensedBlocks where
  shrink cb :=
    (if cb.lowLinks.size > 0 then [{ cb with lowLinks := cb.lowLinks.pop }] else []) ++
    (if cb.blocks.size > 0 then [{ cb with blocks := cb.blocks.pop }] else []) ++
    (if cb.blockRefs.size > 0 then [{ cb with blockRefs := cb.blockRefs.pop }] else [])

instance : SampleableExt Ix.RustCondensedBlocks := SampleableExt.mkSelfContained genRustCondensedBlocks

/-- Generate Ix.CompileM.RustCompilePhases -/
def genRustCompilePhases : Gen Ix.CompileM.RustCompilePhases :=
  Ix.CompileM.RustCompilePhases.mk
    <$> genIxRawEnvironment
    <*> genRustCondensedBlocks
    <*> Tests.Gen.Ixon.genRawEnv

instance : Shrinkable Ix.CompileM.RustCompilePhases where
  shrink p :=
    -- Shrink to empty structures
    let empty : Ix.CompileM.RustCompilePhases := {
      rawEnv := { consts := #[] },
      condensed := { lowLinks := #[], blocks := #[], blockRefs := #[] },
      compileEnv := { consts := #[], named := #[], blobs := #[], comms := #[] }
    }
    if p.rawEnv.consts.isEmpty && p.condensed.lowLinks.isEmpty && p.compileEnv.consts.isEmpty
    then []
    else [empty]

instance : SampleableExt Ix.CompileM.RustCompilePhases := SampleableExt.mkSelfContained genRustCompilePhases

/-! ## Generators for SerializeError, CompileError, and DecompileError -/

instance : Inhabited Ixon.SerializeError where
  default := .addressError

instance : Inhabited Ix.DecompileM.DecompileError where
  default := .badConstantFormat ""

instance : Inhabited Ix.CompileM.CompileError where
  default := .missingConstant ""

/-- Generate a SerializeError with all variants -/
def genSerializeError : Gen Ixon.SerializeError := do
  let s ← genIxString
  let byte ← Gen.choose Nat 0 255
  let idx ← Gen.choose Nat 0 100
  let len ← Gen.choose Nat 0 100
  Gen.frequency #[
    (1, pure (.unexpectedEof s)),
    (1, pure (.invalidTag byte.toUInt8 s)),
    (1, pure (.invalidFlag byte.toUInt8 s)),
    (1, pure (.invalidVariant idx.toUInt64 s)),
    (1, pure (.invalidBool byte.toUInt8)),
    (1, pure .addressError),
    (1, pure (.invalidShareIndex idx.toUInt64 len))
  ] (pure default)

instance : Shrinkable Ixon.SerializeError where
  shrink e := match e with
    | .addressError => []
    | _ => [.addressError]

instance : SampleableExt Ixon.SerializeError :=
  SampleableExt.mkSelfContained genSerializeError

/-- Generate a DecompileError with all variants -/
def genDecompileError : Gen Ix.DecompileM.DecompileError := do
  let addr ← genAddress
  let idx ← Gen.choose Nat 0 100
  let len ← Gen.choose Nat 0 100
  let s ← genIxString
  let se ← genSerializeError
  Gen.frequency #[
    (1, pure (.invalidRefIndex idx.toUInt64 len s)),
    (1, pure (.invalidUnivIndex idx.toUInt64 len s)),
    (1, pure (.invalidShareIndex idx.toUInt64 len s)),
    (1, pure (.invalidRecIndex idx.toUInt64 len s)),
    (1, pure (.invalidUnivVarIndex idx.toUInt64 len s)),
    (1, pure (.missingAddress addr)),
    (1, pure (.missingMetadata addr)),
    (1, pure (.blobNotFound addr)),
    (1, do let expected ← genIxString; pure (.badBlobFormat addr expected)),
    (1, pure (.badConstantFormat s)),
    (1, pure (.serializeError se))
  ] (pure default)

instance : Shrinkable Ix.DecompileM.DecompileError where
  shrink e := match e with
    | .badConstantFormat s => if s.isEmpty then [] else [.badConstantFormat ""]
    | .serializeError se =>
      [.badConstantFormat ""] ++ (.serializeError <$> Shrinkable.shrink se)
    | _ => [.badConstantFormat ""]

instance : SampleableExt Ix.DecompileM.DecompileError :=
  SampleableExt.mkSelfContained genDecompileError

/-- Generate a CompileError with all variants -/
def genCompileError : Gen Ix.CompileM.CompileError := do
  let addr ← genAddress
  let s ← genIxString
  let se ← genSerializeError
  Gen.frequency #[
    (1, pure (.missingConstant s)),
    (1, pure (.missingAddress addr)),
    (1, pure (.invalidMutualBlock s)),
    (1, pure (.unsupportedExpr s)),
    (1, do let s2 ← genIxString; pure (.unknownUnivParam s s2)),
    (1, pure (.serializeError se))
  ] (pure default)

instance : Shrinkable Ix.CompileM.CompileError where
  shrink e := match e with
    | .missingConstant s => if s.isEmpty then [] else [.missingConstant ""]
    | .serializeError se =>
      [.missingConstant ""] ++ (.serializeError <$> Shrinkable.shrink se)
    | _ => [.missingConstant ""]

instance : SampleableExt Ix.CompileM.CompileError :=
  SampleableExt.mkSelfContained genCompileError

end Tests.Gen.Ix
