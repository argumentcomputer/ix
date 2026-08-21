/-
  `Ix.Catalog`: qualified multi-library union environments ("catalogs").

  A catalog is one merged kernel `Environment` in which every constant
  `N` owned by member library `X` appears as `<prefix>.<X>.N` (lossless:
  no leading component is stripped), so libraries with colliding source
  names — two packages both declaring `Collision.Tree` — coexist in one
  environment and one `.ixe`. See `plans/upstream-from-truthmines.md`
  §3; the relocation core is absorbed from TruthMinesLib
  (`TruthMines/Internal/Relocate.lean`), reduced to the kernel level.

  Contract and deliberate simplifications:
  - **Kernel-level only.** Constants are relocated and kernel-replayed;
    instances, attributes, LCNF, and native code do not transfer.
  - **Complete bodies, unconditionally.** Member libraries and the
    toolchain base load at `OLeanLevel.private` (explicit at both
    importModules call sites), so `@[no_expose]` / module-sealed
    definitions enter the catalog as ordinary transparent definitions —
    Ix punches through the Lean module system (plan D6). The level is
    load-bearing and invisible to every downstream gate: an
    exported-level env axiomizes imported proofs and drops `_private.*`
    constants, kernel replay accepts the axioms vacuously, and
    `--audit` compares two identically-axiomized legs (#572) — so
    regressions are caught by loader-level tests, not by the build.
  - **Ownership is Lake package identity.** A constant is owned by the
    package of its source module (`Environment.getModulePackageByIdx?`);
    toolchain modules (no package identity) form the shared unqualified
    base. Every non-toolchain package in any member's import closure
    must be cataloged, and every foreign cataloged module a member
    reaches must lie inside its owner's declared root closure — fail
    closed on both, before the kernel trips on a renamed-but-never-
    replayed constant.
  - **Kernel replay regenerates auxiliaries.** Constructors and
    recursors (including nested-aux `rec_N`) are skipped and reappear
    when the kernel re-accepts the renamed `inductDecl`; their renamed
    names coincide with the renamed references because the lossless rule
    prefixes every owned name uniformly.
  - **Construction memory is bounded** by the toolchain base, the
    growing target env, one member environment at a time, and the kept
    envs of heavy-content members (plan DQ5): members stream through
    `forEachLib`; a member owning few constants is copy-staged out of
    region memory (`stagePlan`) and its env's compacted olean regions
    freed before the next member loads, while a member owning
    mathlib-scale content is staged sharing its regions, which stay
    mapped (`defaultCopyStageMaxOwned`). Without the copy-out, ~40
    corpus members sharing a mathlib closure would hold ~40
    fixup-dirtied copies of it simultaneously; without the keep-side,
    the heavy member's content materializes as heap objects ~10×
    fatter than its compacted form.

  Note on qualification: bare `Expr`/`Name`/`ConstantInfo` inside the
  `Ix` namespace resolve to ix's own mirror types, so Lean's are
  `Lean.`-qualified explicitly throughout (repo convention).
-/
module

public import Lean
public import Ix.Meta
public import Ix.CanonM
public import Ix.CompileM

public section

namespace Ix.Catalog

/-- One member library: a single-component qualifier and the root
    modules whose import closure delivers the library. Libraries must be
    listed in dependency order (dependencies first). -/
structure LibSpec where
  qualifier : Lean.Name
  roots : Array Lean.Name
  deriving Repr, Inhabited

structure CatalogSpec where
  /-- The catalog's own namespace, e.g. `TruthMines`. -/
  catalogPrefix : Lean.Name
  /-- Member libraries, dependencies first. -/
  libs : Array LibSpec
  deriving Repr, Inhabited

structure BuildResult where
  /-- Every constant of the catalog environment: the unqualified
      toolchain base plus all qualified member constants (including
      kernel-regenerated constructors/recursors). -/
  consts : Array (Lean.Name × Lean.ConstantInfo)
  /-- Declarations replayed through the kernel. -/
  replayed : Nat
  /-- Per-qualifier owned-constant counts (source constants, pre-replay). -/
  perLib : Array (Lean.Name × Nat)

/-- Parse a catalog spec from its JSON file form (`ix catalog --spec`):

    ```json
    { "prefix": "TruthMines",
      "libs": [ { "qualifier": "Batteries", "roots": ["Batteries"] } ] }
    ```

    Fail-closed on structure: unknown keys are errors, and the `groups`
    key is reserved for grouped loading (plan Item 2) so a spec written
    for a future ix fails loudly here instead of silently flattening. -/
def specFromJson (json : Lean.Json) : Except String CatalogSpec := do
  let obj ← json.getObj?
  for ⟨key, _⟩ in obj.toArray do
    match key with
    | "prefix" | "libs" => pure ()
    | "groups" => throw "`groups` is reserved for grouped loading and not yet supported"
    | _ => throw s!"unknown key `{key}` in catalog spec"
  let prefixStr ← (← json.getObjVal? "prefix").getStr?
  if prefixStr.isEmpty then throw "empty `prefix`"
  let libsArr ← (← json.getObjVal? "libs").getArr?
  if libsArr.isEmpty then throw "`libs` is empty"
  let mut libs : Array LibSpec := #[]
  for libJson in libsArr do
    let libObj ← libJson.getObj?
    for ⟨key, _⟩ in libObj.toArray do
      match key with
      | "qualifier" | "roots" => pure ()
      | _ => throw s!"unknown key `{key}` in catalog spec lib entry"
    let qualifier ← (← libJson.getObjVal? "qualifier").getStr?
    if qualifier.isEmpty then throw "empty `qualifier` in lib entry"
    let rootsArr ← (← libJson.getObjVal? "roots").getArr?
    let mut roots : Array Lean.Name := #[]
    for rootJson in rootsArr do
      let root ← rootJson.getStr?
      if root.isEmpty then throw s!"lib `{qualifier}`: empty root module name"
      roots := roots.push root.toName
    if roots.isEmpty then throw s!"lib `{qualifier}`: no root modules"
    libs := libs.push { qualifier := qualifier.toName, roots }
  return { catalogPrefix := prefixStr.toName, libs }

/-! ## Relocation core (absorbed from TruthMines `Internal.Relocate`) -/

def rename (names : Lean.NameMap Lean.Name) (name : Lean.Name) : Lean.Name :=
  names.find? name |>.getD name

/-- Rewrite both ordinary constants and the structure name embedded in
    `Expr.proj` — `getUsedConstantsAsSet` deliberately skips the latter,
    but relocation must not: changing a projected value's type without
    its type tag creates an invalid kernel projection. `Expr.replace` is
    pointer-cached, which matters for highly shared proof-term DAGs. -/
partial def relocateExpr (names : Lean.NameMap Lean.Name) (expr : Lean.Expr) :
    Lean.Expr :=
  expr.replace fun
    | .const name levels =>
      names.find? name |>.map fun name' => .const name' levels
    | .proj typeName idx value =>
      names.find? typeName |>.map fun typeName' =>
        .proj typeName' idx (relocateExpr names value)
    | _ => none

private unsafe structure ExpressionReferenceState where
  visited : Lean.PtrSet Lean.Expr := Lean.mkPtrSet
  references : Lean.NameSet := {}

private unsafe abbrev ExpressionReferenceM := StateM ExpressionReferenceState

private unsafe def expressionReferencesUnsafe (expr : Lean.Expr) :
    Lean.NameSet :=
  let rec visit (expr : Lean.Expr) : ExpressionReferenceM Unit := do
    if (← get).visited.contains expr then return
    modify fun state => { state with visited := state.visited.insert expr }
    match expr with
    | .forallE _ domain body _ | .lam _ domain body _ =>
      visit domain
      visit body
    | .mdata _ body => visit body
    | .letE _ type value body _ =>
      visit type
      visit value
      visit body
    | .app fn arg =>
      visit fn
      visit arg
    | .proj typeName _ value =>
      modify fun state => {
        state with references := state.references.insert typeName }
      visit value
    | .const name _ =>
      modify fun state => {
        state with references := state.references.insert name }
    | _ => pure ()
  (do
    visit expr
    return (← get).references : ExpressionReferenceM Lean.NameSet).run' {}

@[implemented_by expressionReferencesUnsafe]
private opaque expressionReferencesImpl (_expr : Lean.Expr) : Lean.NameSet :=
  {}

/-- All constant references of an expression, including `Expr.proj`
    structure names, with pointer-cached DAG traversal. -/
def expressionReferences (expr : Lean.Expr) : Lean.NameSet :=
  expressionReferencesImpl expr

def constantInfoReferences (info : Lean.ConstantInfo) : Lean.NameSet :=
  let result := expressionReferences info.type
  match info.value? (allowOpaque := true) with
  | some value => expressionReferences value ++ result
  | none => match info with
    | .inductInfo val => result ++ Lean.NameSet.ofList val.ctors
    | .ctorInfo val => result.insert val.name
    | .recInfo val => result ++ Lean.NameSet.ofList val.all
    | _ => result

def relocateDefinitionVal (names : Lean.NameMap Lean.Name)
    (val : Lean.DefinitionVal) : Lean.DefinitionVal :=
  { val with
    name := rename names val.name
    type := relocateExpr names val.type
    value := relocateExpr names val.value
    all := val.all.map (rename names) }

def relocateDeclaration (names : Lean.NameMap Lean.Name) :
    Lean.Declaration → Lean.Declaration
  | .axiomDecl val => .axiomDecl {
      val with
      name := rename names val.name
      type := relocateExpr names val.type }
  | .defnDecl val => .defnDecl (relocateDefinitionVal names val)
  | .thmDecl val => .thmDecl {
      val with
      name := rename names val.name
      type := relocateExpr names val.type
      value := relocateExpr names val.value
      all := val.all.map (rename names) }
  | .opaqueDecl val => .opaqueDecl {
      val with
      name := rename names val.name
      type := relocateExpr names val.type
      value := relocateExpr names val.value
      all := val.all.map (rename names) }
  | .mutualDefnDecl vals =>
      .mutualDefnDecl (vals.map (relocateDefinitionVal names))
  | .inductDecl levelParams numParams types isUnsafe =>
      .inductDecl levelParams numParams (types.map fun type => {
        name := rename names type.name
        type := relocateExpr names type.type
        ctors := type.ctors.map fun ctor => {
          name := rename names ctor.name
          type := relocateExpr names ctor.type } }) isUnsafe
  | .quotDecl => .quotDecl

def relocateConstantVal (names : Lean.NameMap Lean.Name)
    (cv : Lean.ConstantVal) : Lean.ConstantVal :=
  { cv with
    name := rename names cv.name
    type := relocateExpr names cv.type }

/-- Rewrite a `ConstantInfo` in place under a rename map — every name
    field (self, `all` lists, inductive families, recursor rules) and
    every expression. Compile-layer relocation: use when comparing
    qualified against unqualified compiles without kernel replay (the
    C5 anon-invariance gate); `buildCatalog` itself replays
    `Declaration`s instead. -/
def relocateConstantInfo (names : Lean.NameMap Lean.Name) :
    Lean.ConstantInfo → Lean.ConstantInfo
  | .axiomInfo v => .axiomInfo {
      v with toConstantVal := relocateConstantVal names v.toConstantVal }
  | .defnInfo v => .defnInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      value := relocateExpr names v.value
      all := v.all.map (rename names) }
  | .thmInfo v => .thmInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      value := relocateExpr names v.value
      all := v.all.map (rename names) }
  | .opaqueInfo v => .opaqueInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      value := relocateExpr names v.value
      all := v.all.map (rename names) }
  | .quotInfo v => .quotInfo {
      v with toConstantVal := relocateConstantVal names v.toConstantVal }
  | .inductInfo v => .inductInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      all := v.all.map (rename names)
      ctors := v.ctors.map (rename names) }
  | .ctorInfo v => .ctorInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      induct := rename names v.induct }
  | .recInfo v => .recInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      all := v.all.map (rename names)
      rules := v.rules.map fun rule => {
        rule with
        ctor := rename names rule.ctor
        rhs := relocateExpr names rule.rhs } }

/-! ## Region-evicting relocation (the streaming replay path)

  `buildCatalog` frees each member environment's compacted olean
  regions after staging its replay (`Environment.freeRegions`); without
  the free, every member's mmapped-and-fixup-dirtied olean pages stay
  resident for the life of the process, which at corpus scale means ~40
  members × a mathlib closure held simultaneously. Freeing is only
  sound if nothing that survives the member references region memory,
  and `relocateExpr` deliberately shares unchanged subterms with the
  source env — so the replay path uses this family instead: a fused
  rename + total structural copy. Every object reachable from a staged
  `Declaration` — exprs, names, levels, strings, big literals, mdata —
  is rebuilt on the ordinary heap, pointer-cached per member so the
  source DAG's sharing is preserved, and hash-consed so structurally
  equal content is copied ONCE per member — olean compaction dedups
  only within a module, so without interning the copy materializes the
  member's entire syntactic content (~100 GiB for a mathlib member;
  measured pointer-cache hit rate over batteries is only ~16%). The
  interpreter fallbacks of the safe wrappers are the sparse
  equivalents: semantically identical, region-sharing, never used in
  compiled code. -/

/-- Fresh heap copies of big numerals: scalars are immediate values and
    need no copy; heap-allocated bignums are rebuilt (`+1-1` cannot
    shortcut to its argument). Also load-bearing for the copiers below:
    a match arm that rebuilds a constructor from unchanged scrutinee
    fields is eta-reduced by the code generator to return the ORIGINAL
    (region-resident!) object, so every all-scalar reconstruction
    routes one field through this arithmetic to defeat that. -/
private def copyNat (n : Nat) : Nat := n + 1 - 1
private def copyInt (i : _root_.Int) : _root_.Int := i + 1 - 1
private def copyUInt32 (u : UInt32) : UInt32 := u + 1 - 1

/-- Pointer equality (unsafe context only). -/
private unsafe def peq {α : Type} (a b : α) : Bool :=
  ptrAddrUnsafe a == ptrAddrUnsafe b

private unsafe def peqList {α : Type} : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => peq a b && peqList as bs
  | _, _ => false

/-! Interning wrappers: olean compaction dedups PER MODULE, so
    cross-module pointer sharing in a member env is essentially zero —
    a purely pointer-cached copy materializes the member's full
    syntactic content (~100 GiB for a mathlib member). The copy is
    therefore hash-consed: children are interned before their parents,
    so structural equality of a candidate node is SHALLOW — head
    constructor, pointer-equal children, equal scalars — and the
    values' cached hash fields make the intern lookup O(1). The intern
    tables key on the fresh COPIES (never on region objects), so they
    survive `freeEnvRegions`. -/

private unsafe structure InternedName where
  value : Lean.Name
private unsafe instance : Hashable InternedName where
  hash a := a.value.hash
private unsafe instance : BEq InternedName where
  beq a b := match a.value, b.value with
    | .anonymous, .anonymous => true
    | .str p s, .str p' s' => peq p p' && peq s s'
    | .num p k, .num p' k' => peq p p' && k == k'
    | _, _ => false

private unsafe structure InternedLevel where
  value : Lean.Level
private unsafe instance : Hashable InternedLevel where
  hash a := a.value.hash
private unsafe instance : BEq InternedLevel where
  beq a b := match a.value, b.value with
    | .zero, .zero => true
    | .succ x, .succ y => peq x y
    | .max x y, .max x' y' => peq x x' && peq y y'
    | .imax x y, .imax x' y' => peq x x' && peq y y'
    | .param n, .param m => peq n m
    | .mvar x, .mvar y => peq x.name y.name
    | _, _ => false

/-- Shallow equality for interning; `fvar`/`mvar`/`mdata` are never
    interned (rare in kernel content, no cheap shallow form). -/
private unsafe structure InternedExpr where
  value : Lean.Expr
private unsafe instance : Hashable InternedExpr where
  hash a := a.value.hash
private unsafe instance : BEq InternedExpr where
  beq a b := match a.value, b.value with
    | .bvar i, .bvar j => i == j
    | .sort u, .sort v => peq u v
    | .const n ls, .const m ms => peq n m && peqList ls ms
    | .app f x, .app g y => peq f g && peq x y
    | .lam n d c bi, .lam n' d' c' bi' =>
      peq n n' && peq d d' && peq c c' && bi == bi'
    | .forallE n d c bi, .forallE n' d' c' bi' =>
      peq n n' && peq d d' && peq c c' && bi == bi'
    | .letE n t v c nd, .letE n' t' v' c' nd' =>
      peq n n' && peq t t' && peq v v' && peq c c' && nd == nd'
    | .lit (.natVal x), .lit (.natVal y) => x == y
    | .lit (.strVal x), .lit (.strVal y) => peq x y
    | .proj tn i v, .proj tn' i' v' => peq tn tn' && i == i' && peq v v'
    | _, _ => false

private unsafe structure CopyState where
  /-- Value-keyed string intern; keys are the copies themselves. -/
  strings : Std.HashMap String String := {}
  /-- Source-pointer → interned copy (skip re-traversal of repeats). -/
  namePtr : Lean.PtrMap Lean.Name Lean.Name := Lean.mkPtrMap
  nameIntern : Std.HashMap InternedName Lean.Name := {}
  levelPtr : Lean.PtrMap Lean.Level Lean.Level := Lean.mkPtrMap
  levelIntern : Std.HashMap InternedLevel Lean.Level := {}
  exprPtr : Lean.PtrMap Lean.Expr Lean.Expr := Lean.mkPtrMap
  exprIntern : Std.HashMap InternedExpr Lean.Expr := {}

private unsafe abbrev CopyM := StateM CopyState

private unsafe def copyStringC (s : String) : CopyM String := do
  match (← get).strings.get? s with
  | some c => return c
  | none =>
    let c := String.ofList s.toList
    if ptrAddrUnsafe c == ptrAddrUnsafe s then
      panic! "copyStringC returned its argument"
    modify fun st => { st with strings := st.strings.insert c c }
    return c

private unsafe def copyName (n : Lean.Name) : CopyM Lean.Name := do
  match n with
  | .anonymous => return .anonymous
  | _ =>
    match (← get).namePtr.find? n with
    | some c => return c
    | none =>
      let c ← match n with
        | .anonymous => pure Lean.Name.anonymous
        | .str p s => return .str (← copyName p) (← copyStringC s)
        | .num p k => return .num (← copyName p) (copyNat k)
      let c ← match (← get).nameIntern.get? ⟨c⟩ with
        | some interned => pure interned
        | none =>
          modify fun st =>
            { st with nameIntern := st.nameIntern.insert ⟨c⟩ c }
          pure c
      if ptrAddrUnsafe c == ptrAddrUnsafe n then
        panic! "copyName returned its argument"
      modify fun st => { st with namePtr := st.namePtr.insert n c }
      return c

private unsafe def copyLevel (l : Lean.Level) : CopyM Lean.Level := do
  match l with
  | .zero => return .zero
  | _ =>
    match (← get).levelPtr.find? l with
    | some c => return c
    | none =>
      let c ← match l with
        | .zero => pure Lean.Level.zero
        | .succ a => return .succ (← copyLevel a)
        | .max a b => return .max (← copyLevel a) (← copyLevel b)
        | .imax a b => return .imax (← copyLevel a) (← copyLevel b)
        | .param n => return .param (← copyName n)
        | .mvar id => return .mvar ⟨← copyName id.name⟩
      let c ← match (← get).levelIntern.get? ⟨c⟩ with
        | some interned => pure interned
        | none =>
          modify fun st =>
            { st with levelIntern := st.levelIntern.insert ⟨c⟩ c }
          pure c
      if ptrAddrUnsafe c == ptrAddrUnsafe l then
        panic! "copyLevel returned its argument"
      modify fun st => { st with levelPtr := st.levelPtr.insert l c }
      return c

private unsafe def copySubstring (s : Substring.Raw) : CopyM Substring.Raw := do
  let c : Substring.Raw := { s with str := (← copyStringC s.str) }
  if ptrAddrUnsafe c == ptrAddrUnsafe s then
    panic! "copySubstring returned its argument"
  return c

private unsafe def copySourceInfo (info : Lean.SourceInfo) :
    CopyM Lean.SourceInfo := do
  let c ← match info with
    | .original leading pos trailing endPos =>
      pure <| Lean.SourceInfo.original (← copySubstring leading) pos
        (← copySubstring trailing) endPos
    | .synthetic pos endPos canonical =>
      pure <| Lean.SourceInfo.synthetic ⟨copyNat pos.byteIdx⟩
        ⟨copyNat endPos.byteIdx⟩ canonical
    | .none => pure Lean.SourceInfo.none
  if ptrAddrUnsafe c == ptrAddrUnsafe info && !(info matches .none) then
    panic! "copySourceInfo returned its argument"
  return c

private unsafe def copyPreresolved (pre : Lean.Syntax.Preresolved) :
    CopyM Lean.Syntax.Preresolved := do
  let c ← match pre with
    | .namespace ns => pure <| Lean.Syntax.Preresolved.namespace (← copyName ns)
    | .decl n fields =>
      pure <| Lean.Syntax.Preresolved.decl (← copyName n)
        (← fields.mapM copyStringC)
  if ptrAddrUnsafe c == ptrAddrUnsafe pre then
    panic! "copyPreresolved returned its argument"
  return c

private unsafe def copySyntax (stx : Lean.Syntax) : CopyM Lean.Syntax := do
  let c ← match stx with
    | .missing => pure Lean.Syntax.missing
    | .node info kind args =>
      -- NOT `args.mapM`: `Array.mapM`'s unsafe implementation returns
      -- the INPUT array object when it is empty, and empty `args`
      -- arrays are common — a region-resident empty array would ride
      -- through into the staged declaration. (Lists are immune: `[]`
      -- is a tagged scalar, not a heap object.)
      let mut argsC : Array Lean.Syntax := Array.mkEmpty args.size
      for arg in args do
        argsC := argsC.push (← copySyntax arg)
      pure <| Lean.Syntax.node (← copySourceInfo info) (← copyName kind) argsC
    | .atom info val =>
      pure <| Lean.Syntax.atom (← copySourceInfo info) (← copyStringC val)
    | .ident info rawVal val preresolved =>
      pure <| Lean.Syntax.ident (← copySourceInfo info) (← copySubstring rawVal)
        (← copyName val) (← preresolved.mapM copyPreresolved)
  if ptrAddrUnsafe c == ptrAddrUnsafe stx && !(stx matches .missing) then
    panic! "copySyntax returned its argument"
  return c

private unsafe def copyDataValue (dv : Lean.DataValue) : CopyM Lean.DataValue := do
  let c ← match dv with
    | .ofString s => pure <| Lean.DataValue.ofString (← copyStringC s)
    | .ofBool b => pure (Lean.DataValue.ofBool (copyNat b.toNat == 1))
    | .ofName n => pure <| Lean.DataValue.ofName (← copyName n)
    | .ofNat n => pure (Lean.DataValue.ofNat (copyNat n))
    | .ofInt i => pure (Lean.DataValue.ofInt (copyInt i))
    | .ofSyntax s => pure <| Lean.DataValue.ofSyntax (← copySyntax s)
  -- Guard against code-generator eta (see `copyNat`): a panic here at
  -- staging time beats a segfault after the regions are freed.
  if ptrAddrUnsafe c == ptrAddrUnsafe dv then
    let arm := match dv with
      | .ofString _ => "ofString" | .ofBool _ => "ofBool"
      | .ofName _ => "ofName" | .ofNat _ => "ofNat"
      | .ofInt _ => "ofInt" | .ofSyntax _ => "ofSyntax"
    panic! s!"copyDataValue returned its argument ({arm})"
  return c

private unsafe def copyMData (md : Lean.MData) : CopyM Lean.MData := do
  let c : Lean.MData := { entries :=
    (← md.entries.mapM fun (k, v) =>
      return ((← copyName k), (← copyDataValue v))) }
  if ptrAddrUnsafe c.entries == ptrAddrUnsafe md.entries && !md.entries.isEmpty then
    panic! "copyMData returned its argument"
  return c

/-- The fused rename + total copy over expressions: `relocateExpr`'s
    rewrite at `const`/`proj` sites, with every node — including
    unchanged ones — rebuilt off region memory. -/
private unsafe def relocExprC (names : Lean.NameMap Lean.Name)
    (expr : Lean.Expr) : CopyM Lean.Expr := do
  match (← get).exprPtr.find? expr with
  | some c => return c
  | none =>
    let c ← match expr with
      | .bvar i => pure (Lean.Expr.bvar (copyNat i))
      | .fvar id => return .fvar ⟨← copyName id.name⟩
      | .mvar id => return .mvar ⟨← copyName id.name⟩
      | .sort u => return .sort (← copyLevel u)
      | .const n ls =>
        return .const (← copyName (rename names n)) (← ls.mapM copyLevel)
      | .app f a => return .app (← relocExprC names f) (← relocExprC names a)
      | .lam n d b bi =>
        return .lam (← copyName n) (← relocExprC names d)
          (← relocExprC names b) bi
      | .forallE n d b bi =>
        return .forallE (← copyName n) (← relocExprC names d)
          (← relocExprC names b) bi
      | .letE n t v b nonDep =>
        return .letE (← copyName n) (← relocExprC names t)
          (← relocExprC names v) (← relocExprC names b) nonDep
      | .lit (.natVal n) => pure (.lit (.natVal (copyNat n)))
      | .lit (.strVal s) => return .lit (.strVal (← copyStringC s))
      | .mdata md b => return .mdata (← copyMData md) (← relocExprC names b)
      | .proj tn i v =>
        return .proj (← copyName (rename names tn)) i (← relocExprC names v)
    -- Intern the candidate (skip fvar/mvar/mdata — no shallow form).
    let c ← match expr with
      | .fvar .. | .mvar .. | .mdata .. => pure c
      | _ =>
        match (← get).exprIntern.get? ⟨c⟩ with
        | some interned => pure interned
        | none =>
          modify fun st =>
            { st with exprIntern := st.exprIntern.insert ⟨c⟩ c }
          pure c
    -- Guard against code-generator eta (see `copyNat`): the `.bvar`
    -- arm regressed exactly this way — the rebuilt node was simplified
    -- to the region-resident scrutinee.
    if ptrAddrUnsafe c == ptrAddrUnsafe expr then
      panic! s!"relocExprC returned its argument ({expr.ctorName})"
    modify fun st => { st with exprPtr := st.exprPtr.insert expr c }
    return c

private unsafe def relocConstantValC (names : Lean.NameMap Lean.Name)
    (cv : Lean.ConstantVal) : CopyM Lean.ConstantVal :=
  return {
    name := (← copyName (rename names cv.name))
    levelParams := (← cv.levelParams.mapM copyName)
    type := (← relocExprC names cv.type) }

/-- `.regular` is a boxed constructor — a record update would share the
    region-resident object. -/
private def copyReducibilityHints : Lean.ReducibilityHints → Lean.ReducibilityHints
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular (copyUInt32 h)

private unsafe def relocDefinitionValC (names : Lean.NameMap Lean.Name)
    (val : Lean.DefinitionVal) : CopyM Lean.DefinitionVal :=
  return { val with
    toConstantVal := (← relocConstantValC names val.toConstantVal)
    value := (← relocExprC names val.value)
    hints := copyReducibilityHints val.hints
    all := (← val.all.mapM fun n => copyName (rename names n)) }

private unsafe def relocDeclarationC (names : Lean.NameMap Lean.Name) :
    Lean.Declaration → CopyM Lean.Declaration
  | .axiomDecl val => return .axiomDecl { val with
      toConstantVal := (← relocConstantValC names val.toConstantVal) }
  | .defnDecl val => return .defnDecl (← relocDefinitionValC names val)
  | .thmDecl val => return .thmDecl { val with
      toConstantVal := (← relocConstantValC names val.toConstantVal)
      value := (← relocExprC names val.value)
      all := (← val.all.mapM fun n => copyName (rename names n)) }
  | .opaqueDecl val => return .opaqueDecl { val with
      toConstantVal := (← relocConstantValC names val.toConstantVal)
      value := (← relocExprC names val.value)
      all := (← val.all.mapM fun n => copyName (rename names n)) }
  | .mutualDefnDecl vals =>
    return .mutualDefnDecl (← vals.mapM (relocDefinitionValC names))
  | .inductDecl levelParams numParams types isUnsafe =>
    return .inductDecl (← levelParams.mapM copyName) numParams
      (← types.mapM fun type => return {
        name := (← copyName (rename names type.name))
        type := (← relocExprC names type.type)
        ctors := (← type.ctors.mapM fun ctor => return {
          name := (← copyName (rename names ctor.name))
          type := (← relocExprC names ctor.type) }) }) isUnsafe
  | .quotDecl => return .quotDecl

/-- One staged replay item: the relocated declaration plus both names
    for diagnostics, all region-independent. -/
structure StagedDecl where
  source : Lean.Name
  target : Lean.Name
  decl : Lean.Declaration

private unsafe def stagePlanUnsafe (names : Lean.NameMap Lean.Name)
    (plan : Array (Lean.Name × Lean.Declaration)) : Array StagedDecl :=
  (plan.mapM fun (key, decl) =>
    (do
      -- The source-pointer caches are reset PER DECLARATION: they
      -- otherwise grow with the member's total visited content (~10⁹
      -- nodes ≈ 50 GiB of cache entries for a mathlib member).
      -- Intra-declaration DAG sharing — what keeps the walk linear —
      -- is preserved; cross-declaration repeats re-walk but collapse
      -- at the persistent intern tables node by node.
      modify fun (st : CopyState) => { st with
        exprPtr := Lean.mkPtrMap
        namePtr := Lean.mkPtrMap
        levelPtr := Lean.mkPtrMap }
      return { source := (← copyName key)
               target := (← copyName (rename names key))
               decl := (← relocDeclarationC names decl) } : CopyM StagedDecl))
    |>.run' {}

/-- Stage a replay plan SHARING the member env's regions: the sparse
    relocation rewrites only renamed spines, everything else stays a
    pointer into the env. Cheap and compact, but the env's regions
    must then outlive the catalog (`EnvDisposal.keepRegions`). -/
private def stageLibShared (names : Lean.NameMap Lean.Name)
    (plan : Array (Lean.Name × Lean.Declaration)) : Array StagedDecl :=
  plan.map fun (key, decl) =>
    { source := key
      target := rename names key
      decl := relocateDeclaration names decl }

/-- Stage one member's replay plan as region-independent copies:
    rename fused with a hash-consed total copy. The staged
    declarations share no memory with the member env, which makes
    `freeEnvRegions` sound after staging. The reference implementation
    is the region-sharing form — semantically identical, never used in
    compiled code. -/
@[implemented_by stagePlanUnsafe]
private opaque stagePlan (names : Lean.NameMap Lean.Name)
    (plan : Array (Lean.Name × Lean.Declaration)) : Array StagedDecl :=
  stageLibShared names plan

private unsafe def copyNameOutUnsafe (n : Lean.Name) : Lean.Name :=
  (copyName n).run' {}

/-- Fresh, region-independent copy of a single name (for module names
    and other scalars that outlive their member env). -/
@[implemented_by copyNameOutUnsafe]
private opaque copyNameOut (n : Lean.Name) : Lean.Name := n

private unsafe def freeEnvRegionsUnsafe (env : Lean.Environment) : IO Unit :=
  env.freeRegions

/-- Free a member environment's compacted olean regions. Sound only
    when nothing reachable from live data references the env's
    imported objects — `forEachLib`'s callback contract. The reference
    implementation is a no-op (leak, the pre-streaming behavior). -/
@[implemented_by freeEnvRegionsUnsafe]
private opaque freeEnvRegions (_env : Lean.Environment) : IO Unit := pure ()

/-- Accept a `DefinitionVal.all` list as unsafe-mutual grouping metadata
    only when every member is an owned definition carrying the same
    list — code-generating metaprograms may copy a recursor's `all` into
    an unrelated definition. -/
def definitionWorkGroup (owned : Lean.NameMap Lean.ConstantInfo)
    (name : Lean.Name) (val : Lean.DefinitionVal) : List Lean.Name :=
  Id.run do
    if val.safety == .safe || !val.all.contains name then
      return [name]
    for member in val.all do
      match owned.find? member with
      | some (.defnInfo memberVal) =>
        unless memberVal.safety == val.safety && memberVal.all == val.all do
          return [name]
      | _ => return [name]
    return val.all

/-- The replay-work key that produces `name`: inductive blocks key on
    `all.head`, constructors and recursors on their block's key, unsafe
    mutual definitions on the group head; everything else is its own
    item. -/
def canonicalWorkKey (owned : Lean.NameMap Lean.ConstantInfo)
    (name : Lean.Name) : Lean.Name :=
  match owned.find? name with
  | some (.inductInfo val) => val.all.head?.getD name
  | some (.ctorInfo val) =>
      match owned.find? val.induct with
      | some (.inductInfo inductiveVal) =>
          inductiveVal.all.head?.getD val.induct
      | _ => val.induct
  | some (.recInfo val) => val.all.head?.getD name
  | some (.defnInfo val) => (definitionWorkGroup owned name val).head?.getD name
  | _ => name

private def sourceInductiveDeclaration
    (find? : Lean.Name → Option Lean.ConstantInfo)
    (owned : Lean.NameMap Lean.ConstantInfo) (val : Lean.InductiveVal) :
    Except String Lean.Declaration := do
  let mut types : List Lean.InductiveType := []
  for typeName in val.all do
    let some (.inductInfo typeVal) := owned.find? typeName
      | throw s!"missing inductive `{typeName}` from mutual block rooted at `{val.name}`"
    let mut ctors : List Lean.Constructor := []
    for ctorName in typeVal.ctors do
      let some (.ctorInfo ctorVal) := find? ctorName
        | throw s!"missing constructor `{ctorName}` for inductive `{typeName}`"
      ctors := ctors.concat { name := ctorName, type := ctorVal.type }
    types := types.concat { name := typeName, type := typeVal.type, ctors }
  return .inductDecl val.levelParams val.numParams types val.isUnsafe

/-- The `Declaration` that replays `info`, or `none` when the constant
    is produced by another work item (constructors, recursors, non-head
    inductive/mutual members) or by the base env (`Quot`). `find?`
    resolves constructor lookups (callers back it by the source
    environment or the materialized constant map). -/
private def sourceDeclaration?
    (find? : Lean.Name → Option Lean.ConstantInfo)
    (owned : Lean.NameMap Lean.ConstantInfo) (name : Lean.Name)
    (info : Lean.ConstantInfo) : Except String (Option Lean.Declaration) := do
  match info with
  | .axiomInfo val => return some (.axiomDecl val)
  | .defnInfo val =>
      if val.safety != .safe then
        let group := definitionWorkGroup owned name val
        if group.head? != some name then return none
        let mut vals : List Lean.DefinitionVal := []
        for defName in group do
          let some (.defnInfo defVal) := owned.find? defName
            | throw s!"missing definition `{defName}` from mutual block rooted at `{name}`"
          vals := vals.concat defVal
        return some (.mutualDefnDecl vals)
      else
        return some (.defnDecl val)
  | .thmInfo val => return some (.thmDecl val)
  | .opaqueInfo val => return some (.opaqueDecl val)
  | .inductInfo val =>
      if val.all.head? == some name then
        return some (← sourceInductiveDeclaration find? owned val)
      else
        return none
  | .ctorInfo _ | .recInfo _ | .quotInfo _ => return none

/-! ## Kernel replay driver -/

private def renderKernelException : Lean.Kernel.Exception → String
  | .unknownConstant _ n => s!"unknown constant `{n}`"
  | .alreadyDeclared _ n => s!"`{n}` already declared"
  | .declTypeMismatch _ _ _ => "declaration type mismatch"
  | .declHasMVars _ n _ => s!"`{n}` has metavariables"
  | .declHasFVars _ n _ => s!"`{n}` has free variables"
  | .funExpected _ _ _ => "function expected"
  | .typeExpected _ _ _ => "type expected"
  | .letTypeMismatch _ _ n _ _ => s!"let type mismatch at `{n}`"
  | .exprTypeMismatch _ _ _ _ => "expression type mismatch"
  | .appTypeMismatch _ _ _ _ _ => "application type mismatch"
  | .invalidProj _ _ _ => "invalid projection"
  | .thmTypeIsNotProp _ n _ => s!"theorem type of `{n}` is not a Prop"
  | .other msg => msg
  | .deterministicTimeout => "deterministic timeout"
  | .excessiveMemory => "excessive memory"
  | .deepRecursion => "deep recursion"
  | .interrupted => "interrupted"

/-- The package that owns module `moduleIdx`, `none` for toolchain. -/
private def modulePackage? (env : Lean.Environment) (moduleIdx : Nat) :
    Option Lean.PkgId :=
  env.getModulePackageByIdx? moduleIdx

/-- The constants serialized by module `moduleIdx`, resolved through the
    environment so private-part key remapping matches ordinary lookup. -/
private def moduleConstants (env : Lean.Environment) (moduleIdx : Nat) :
    Except String (Array (Lean.Name × Lean.ConstantInfo)) := do
  let some data := env.header.moduleData[moduleIdx]?
    | throw s!"module index {moduleIdx} has no serialized module data"
  let mut result := Array.mkEmpty data.constNames.size
  for name in data.constNames do
    let some info := env.find? name
      | throw s!"module `{env.header.moduleNames[moduleIdx]!}` does not expose serialized declaration `{name}`"
    result := result.push (name, info)
  return result

private structure WorkItem where
  key : Lean.Name
  decl : Lean.Declaration
  deps : Lean.NameSet

/-- Reconstruct the kernel `Declaration`s that replay `owned` and order
    them topologically (Kahn's algorithm, name-sorted ready sets for
    determinism). Pure planning — no kernel interaction; dependencies
    outside `owned` are assumed satisfied by the caller's base
    environment. `find?` resolves constructor lookups during inductive
    reconstruction. Shared by the catalog replay driver and by
    `import_ixe` materialization (`Ix/ImportIxe.lean`). -/
def planDeclarations (owned : Lean.NameMap Lean.ConstantInfo)
    (find? : Lean.Name → Option Lean.ConstantInfo) :
    Except String (Array (Lean.Name × Lean.Declaration)) := do
  -- Work items keyed by canonical head, with owned-only dependencies.
  let mut producedBy : Lean.NameMap Lean.Name := {}
  let mut membersOfKey : Lean.NameMap (Array Lean.Name) := {}
  for (name, _) in owned do
    let key := canonicalWorkKey owned name
    producedBy := producedBy.insert name key
    membersOfKey := membersOfKey.insert key
      ((membersOfKey.find? key).getD #[] |>.push name)
  let mut items : Lean.NameMap WorkItem := {}
  for (name, info) in owned do
    let some decl ← sourceDeclaration? find? owned name info | continue
    let key := name
    -- Dependencies: references of every constant this item produces,
    -- mapped to their producing items.
    let mut deps : Lean.NameSet := {}
    for member in (membersOfKey.find? key).getD #[] do
      let some memberInfo := owned.find? member | continue
      for reference in constantInfoReferences memberInfo do
        match producedBy.find? reference with
        | some refKey => if refKey != key then deps := deps.insert refKey
        | none => pure ()
    items := items.insert key { key, decl, deps }
  -- Kahn's algorithm with name-sorted ready set for determinism.
  let mut plan : Array (Lean.Name × Lean.Declaration) := #[]
  let mut added : Lean.NameSet := {}
  let mut pending := items
  while !pending.isEmpty do
    let mut ready : Array WorkItem := #[]
    for (_, item) in pending do
      if item.deps.all (added.contains ·) then
        ready := ready.push item
    if ready.isEmpty then
      let cycle := pending.foldl (init := #[]) fun acc k _ => acc.push k
      throw s!"dependency cycle among replay items: {cycle[0:8].toArray}"
    let readySorted := ready.qsort fun a b => a.key.quickCmp b.key == .lt
    for item in readySorted do
      plan := plan.push (item.key, item.decl)
      added := added.insert item.key
      pending := pending.erase item.key
  return plan

/-- Per-module ownership sweep over one loaded library environment:
    rename entries for every cataloged package's constants, plus the
    owned map for this library's own packages. Fails closed on
    uncatalogued packages. Shared by the replay driver and the audit. -/
private def ownershipMaps (spec : CatalogSpec) (env : Lean.Environment)
    (qualOfPkg : Std.HashMap Lean.PkgId Lean.Name)
    (libPkgs : Std.HashSet Lean.PkgId) :
    Except String
      (Lean.NameMap Lean.Name × Lean.NameMap Lean.ConstantInfo) := do
  let mut renameMap : Lean.NameMap Lean.Name := {}
  let mut owned : Lean.NameMap Lean.ConstantInfo := {}
  for moduleIdx in [0:env.header.moduleNames.size] do
    match modulePackage? env moduleIdx with
    | none => pure ()  -- toolchain base: unqualified, provided by baseEnv
    | some pkg =>
      let some qualifier := qualOfPkg.get? pkg
        | throw s!"uncatalogued package `{pkg}` (module `{env.header.moduleNames[moduleIdx]!}`) — every non-toolchain package in the import closure needs a catalog entry"
      let target := spec.catalogPrefix ++ qualifier
      for (name, info) in ← moduleConstants env moduleIdx do
        renameMap := renameMap.insert name (target ++ name)
        if libPkgs.contains pkg then
          owned := owned.insert name info
  return (renameMap, owned)

/-- The I5 coverage gate: member `X`'s import closure may reach a
    module of cataloged package `Y` that `Y`'s own declared roots do
    not reach (a provider's umbrella need not import every module a
    downstream member uses). `ownershipMaps` renames that module's
    constants, but replay only ever delivers the closures of declared
    roots — nothing replays them, and the kernel would reject `X`'s
    first reference with a bare `unknown constant P.Y.N`. Detect it
    before replay: members fold through in declaration order,
    accumulating the module set each member's replay delivers; every
    foreign cataloged module in `X`'s env must already be covered.
    Under streaming, the qualifier map holds only members processed so
    far, so a provider listed after its consumer and an uncatalogued
    package surface as one unknown-provider error. Module names are
    copied into `covered`: the set outlives the env. -/
private def checkRootCoverage (lib : LibSpec) (env : Lean.Environment)
    (qualOfPkg : Std.HashMap Lean.PkgId Lean.Name)
    (libPkgs : Std.HashSet Lean.PkgId) (covered : Lean.NameSet) :
    Except String Lean.NameSet := do
  let mut covered := covered
  for moduleIdx in [0:env.header.moduleNames.size] do
    match modulePackage? env moduleIdx with
    | none => pure ()  -- toolchain base: unqualified, always present
    | some pkg =>
      let moduleName := env.header.moduleNames[moduleIdx]!
      if libPkgs.contains pkg then
        covered := covered.insert (copyNameOut moduleName)
      else
        let some qualifier := qualOfPkg.get? pkg
          | throw s!"member `{lib.qualifier}` references `{moduleName}` of \
package `{pkg}`, which no member listed so far provides — either the \
package is uncatalogued, or its provider is listed after \
`{lib.qualifier}`. Every non-toolchain package in the import closure \
needs a catalog entry, and members replay dependencies first."
        unless covered.contains moduleName do
          throw s!"member `{lib.qualifier}` references `{moduleName}`, \
owned by qualifier `{qualifier}`, but `{qualifier}`'s roots do not \
cover that module. Add `{moduleName}` to `{qualifier}`'s roots."
  return covered

/-- Members owning at most this many constants are copy-staged
    (region-independent, env freed); a member owning more — a
    mathlib-scale library — is staged sharing its env's regions, which
    then stay mapped (`EnvDisposal.keepRegions`). Keeping one heavy
    env (~8 GiB of compacted regions for mathlib) beats materializing
    its content as heap objects, which measures ~10× fatter than the
    compacted form even hash-consed. The corpus shape is many
    small-content members whose CLOSURES are heavy (copy + free wins
    there) and a handful of heavy-content members (keep + share wins
    there). -/
def defaultCopyStageMaxOwned : Nat := 100000

/-- The callback's verdict on a member environment's compacted
    regions: `freeRegions` when everything the callback returned is
    region-independent (copy-staged, or fresh strings); `keepRegions`
    when the returned data deliberately shares the env's regions
    (`stageLibShared`) — they then stay mapped for the life of the
    process. -/
inductive EnvDisposal where
  | freeRegions
  | keepRegions

/-- Stream member libraries in declaration order: import each into its
    own environment (so colliding source names never meet at import
    time), resolve the member's packages from its root modules and
    extend the package → qualifier map — members are declared
    dependencies-first, so the map is complete for every environment by
    the time its callback runs — invoke `f`, then dispose of the
    environment's compacted olean regions as `f` directs. With
    `.freeRegions` (the normal verdict) construction memory is bounded
    by one member env at a time (plan DQ5); the callback then MUST NOT
    retain the environment or anything reachable from it — copy what
    survives (`stagePlan`, `copyNameOut`, or interpolation into fresh
    strings). Imports are pinned to `OLeanLevel.private` — complete
    bodies (D6); see the module header for why no downstream gate can
    catch a level regression. Shared by `buildCatalog` and
    `auditCatalog`. -/
def forEachLib {α : Type} (spec : CatalogSpec) (init : α)
    (f : α → LibSpec → Lean.Environment →
         Std.HashMap Lean.PkgId Lean.Name → Std.HashSet Lean.PkgId →
         IO (EnvDisposal × α)) : IO α := do
  if spec.libs.isEmpty then
    throw <| IO.userError "catalog: no member libraries"
  let mut qualOfPkg : Std.HashMap Lean.PkgId Lean.Name := {}
  let mut acc := init
  for lib in spec.libs do
    let imports : Array Lean.Import := lib.roots.map ({ module := · })
    let env ← Lean.importModules imports {} (level := .private)
    let mut pkgs : Std.HashSet Lean.PkgId := {}
    for root in lib.roots do
      let some moduleIdx := env.getModuleIdx? root
        | throw <| IO.userError s!"catalog: root module `{root}` is not in `{lib.qualifier}`'s environment"
      let some pkg := modulePackage? env moduleIdx.toNat
        | throw <| IO.userError s!"catalog: root module `{root}` has no Lake package identity — toolchain modules cannot be cataloged"
      -- `PkgId` is a region-resident string; the maps outlive the env.
      let pkg : Lean.PkgId := String.ofList pkg.toList
      pkgs := pkgs.insert pkg
      match qualOfPkg.get? pkg with
      | some q =>
        unless q == lib.qualifier do
          throw <| IO.userError s!"catalog: package `{pkg}` claimed by qualifiers `{q}` and `{lib.qualifier}`"
      | none => qualOfPkg := qualOfPkg.insert pkg lib.qualifier
    let (disposal, acc') ← try
        f acc lib env qualOfPkg pkgs
      catch e =>
        freeEnvRegions env
        throw e
    if disposal matches .freeRegions then
      freeEnvRegions env
    acc := acc'
  return acc

/-- Accumulator of the streaming member pass: staged replay plans (per
    qualifier, with owned counts), the I5 coverage set, and the
    toolchain module union — all region-independent. -/
private structure BuildPass where
  staged : Array (Lean.Name × Array StagedDecl × Nat) := #[]
  covered : Lean.NameSet := {}
  toolchainSeen : Lean.NameSet := {}
  toolchainMods : Array Lean.Import := #[]

/-- Build the catalog kernel environment for `spec`. Assumes the Lean
    search path already resolves every root module (CLI callers run
    `initLeanSearchPath` first; in-process callers inherit theirs).
    `copyStageMaxOwned` is the copy-vs-share staging threshold (see
    `defaultCopyStageMaxOwned`). -/
def buildCatalog (spec : CatalogSpec)
    (copyStageMaxOwned : Nat := defaultCopyStageMaxOwned) :
    IO BuildResult := do
  -- 1. Stream the members in dependency order: check root coverage
  --    (I5), stage the replay, and accumulate the toolchain module
  --    union. Small-content members are copy-staged and their envs
  --    freed before the next loads; heavy-content members are staged
  --    sharing their env's regions, which stay mapped.
  let pass ← forEachLib spec ({} : BuildPass) fun pass lib env qualOfPkg pkgs => do
    let covered ← match checkRootCoverage lib env qualOfPkg pkgs pass.covered with
      | .ok covered => pure covered
      | .error e => throw <| IO.userError s!"catalog: {e}"
    let (renameMap, owned) ← match ownershipMaps spec env qualOfPkg pkgs with
      | .ok maps => pure maps
      | .error e =>
        throw <| IO.userError s!"catalog: library `{lib.qualifier}`: {e}"
    let plan ← match planDeclarations owned env.find? with
      | .ok plan => pure plan
      | .error e =>
        throw <| IO.userError s!"catalog: library `{lib.qualifier}`: {e}"
    let (decls, disposal) :=
      if owned.size ≤ copyStageMaxOwned then
        (stagePlan renameMap plan, EnvDisposal.freeRegions)
      else
        (stageLibShared renameMap plan, EnvDisposal.keepRegions)
    let ownedCount := owned.size
    let mut toolchainSeen := pass.toolchainSeen
    let mut toolchainMods := pass.toolchainMods
    for moduleIdx in [0:env.header.moduleNames.size] do
      if (modulePackage? env moduleIdx).isNone then
        let moduleName := env.header.moduleNames[moduleIdx]!
        if !toolchainSeen.contains moduleName then
          let moduleName := copyNameOut moduleName
          toolchainSeen := toolchainSeen.insert moduleName
          toolchainMods := toolchainMods.push { module := moduleName }
    return (disposal,
      { staged := pass.staged.push (lib.qualifier, decls, ownedCount)
        covered, toolchainSeen, toolchainMods })
  -- 2. Toolchain base: the union of toolchain modules across member
  --    environments, imported once (single provider ⇒ no collisions).
  --    Its regions are never freed — `consts` references them.
  let baseEnv ← Lean.importModules pass.toolchainMods {} (level := .private)
  -- 3. Kernel-replay the staged declarations in dependency order.
  let mut kenv := baseEnv.toKernelEnv
  let mut replayed := 0
  let mut perLib : Array (Lean.Name × Nat) := #[]
  -- Replayed declarations were already kernel-accepted at elaboration
  -- time, where per-file `set_option maxHeartbeats` overrides applied;
  -- the replay must not re-impose the default budget (mathlib's heavy
  -- proofs exceed it and would be rejected with a deterministic
  -- timeout).
  let replayOpts : Lean.Options := Lean.Options.empty.set `maxHeartbeats 0
  for (qualifier, decls, ownedCount) in pass.staged do
    for staged in decls do
      match kenv.addDecl replayOpts staged.decl with
      | .ok kenv' =>
        kenv := kenv'
        replayed := replayed + 1
      | .error e =>
        throw <| IO.userError s!"catalog: library `{qualifier}`: kernel \
rejected `{staged.target}` (source `{staged.source}`): \
{renderKernelException e}"
    perLib := perLib.push (qualifier, ownedCount)
  -- 4. Extract the full constant map (base + qualified + regenerated).
  let consts := kenv.constants.fold (init := #[]) fun acc name info =>
    acc.push (name, info)
  return { consts, replayed, perLib }

/-! ## Audit: anon-address preservation (the §3.1 invariant) -/

structure AuditResult where
  /-- Owned constants whose addresses were compared. -/
  checked : Nat
  /-- Human-readable invariant violations; empty = pass. -/
  violations : Array String

/-- Audit a built catalog against the load-bearing §3.1 invariant:
    qualification is metadata-only at the Ixon layer, so for every
    owned constant `N` of member `X`, the anon address of the
    standalone library compile at `N` equals the catalog compile's at
    `P.X.N`. Each member library is recompiled standalone (its own env,
    unqualified) and compared against one compile of the catalog —
    N+1 Rust compiles, so this is an opt-in gate (`ix catalog --audit`),
    not part of the build. `only` restricts the standalone compiles and
    comparison to the named qualifiers (`--audit-only`): at corpus
    scale the full audit is a multi-hour session, so the invariant can
    be gated on a rotating subset while the artifact still gets built.
    Members outside the subset still stream through (their packages
    extend the qualifier map) but skip the expensive legs. -/
def auditCatalog (spec : CatalogSpec)
    (catalogConsts : Array (Lean.Name × Lean.ConstantInfo))
    (only : Option Lean.NameSet := none) :
    IO AuditResult := do
  let catEnv ← Ix.CompileM.rsCompileEnvOf catalogConsts.toList
  forEachLib spec ({ checked := 0, violations := #[] } : AuditResult)
    fun acc lib env qualOfPkg pkgs => do
      if only.any (!·.contains lib.qualifier) then return (.freeRegions, acc)
      let (renameMap, owned) ←
        match ownershipMaps spec env qualOfPkg pkgs with
        | .ok maps => pure maps
        | .error e =>
          throw <| IO.userError s!"catalog audit: `{lib.qualifier}`: {e}"
      let stdEnv ← Ix.CompileM.rsCompileEnvOf env.constants.toList
      -- Only fresh strings and counts survive into the accumulator;
      -- the env (and everything region-backed) dies with the callback.
      let mut violations := acc.violations
      let mut checked := acc.checked
      for (name, _) in owned do
        let target := rename renameMap name
        let (ixSrc, _) := (CanonM.canonName name).run {}
        let (ixTgt, _) := (CanonM.canonName target).run {}
        match stdEnv.named.get? ixSrc, catEnv.named.get? ixTgt with
        | some src, some tgt =>
          checked := checked + 1
          if src.addr != tgt.addr then
            violations := violations.push
              s!"{lib.qualifier}: addr({name}) = {src.addr} standalone \
but addr({target}) = {tgt.addr} in the catalog"
        | none, _ =>
          violations := violations.push
            s!"{lib.qualifier}: standalone compile has no named entry \
for `{name}`"
        | _, none =>
          violations := violations.push
            s!"{lib.qualifier}: catalog compile has no named entry for \
`{target}`"
      return (.freeRegions, { checked, violations })

end Ix.Catalog
