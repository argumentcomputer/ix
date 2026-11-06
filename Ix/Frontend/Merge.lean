/-
  Ix.Frontend.Merge: Self-Contained, Provable AST & Type-Aware Module Merge Engine (`IxVCS`).

  Implements the 3-level conflict-free and type-contract-preserving merge calculus for `Ix`:
  1. **Declaration-Level Pushout (`mergeModuleSchedule2`, `mergeSource2`)**:
     - Hermetically normalizes declarations (`hermeticizeDecl`, `hermeticizeModule`) by folding
       lexical `namespace`/`section`/`variable`/`universe`/`open` scopes into self-contained ASTs.
     - Computes bottom-up BLAKE3-256 (`Address.admissionHash`) intrinsic and Merkle digests over
       the Tarjan SCC condensation DAG (`computeModuleDigests`).
     - Partitions module pairs into 5 disjoint blocks:
       $S$ (shared/unified) $\sqcup$ $\sigma_1(O_1)$ (left-only) $\sqcup$ $\sigma_2(O_2)$ (right-only)
       $\sqcup$ $\sigma_1(K)$ (left conflicted) $\sqcup$ $\sigma_2(K)$ (right conflicted).
     - Disambiguates conflicting declarations using first-class `.#merge` variants (`foobar.#merge._1`,
       `foobar.#merge._2` or `foobar.#merge.<branch>`) or namespace prefixes (`X.Acme.foobar`,
       `Y.Acme.foobar`), and binder-awarely rewrites all downstream callers, constructors,
       patterns, structure projections, and recursors (`rewriteModuleDecl`).
  2. **Intra-Declaration Semantic & AST Pre-Merge (`tryUnifySameNameDecls`, `tryMergeDeclSyntax3`)**:
     - **Proof Irrelevance Absorption (`Prop`)**: Two `theorem` declarations with the same name and
       definitionally equal (`isDefEq`) statement types are unified into a single theorem (selecting
       the canonically smaller `sorryAx`-free proof by 32-byte BLAKE3 Merkle `Address`) with zero
       `.#merge` disambiguation.
     - **Definitional Equality (`isDefEq`)**: Two definitions with definitionally equal types and
       values unify without `.#merge` disambiguation.
     - **Keyed 3-Way AST Merge (`tryMergeDeclSyntax3`)**: Disjoint constructor arm edits in `match`
       expressions and disjoint field edits in structure literals are spliced and verified against
       the elaborator before falling back to `.#merge` disambiguation.
  3. **3-Way Type-Contract-Preserving Merge (`mergeModuleSchedule3`, `mergeSource3`)**:
     - Enforces the invariant **"The Type System is the Contract Between Caller and Callee"**:
       - **Cases A & B (1-sided proof or body update where all callers/theorems in the other branch
         still typecheck)**: Fast-forwards the updated declaration cleanly with zero `.#merge` conflicts.
       - **Cases C & D (1-sided body update that breaks a dependent proof in the other branch that
         unfolded the old body via `rfl`/`isDefEq`, or a 1-sided type signature change)**: Rejects
         the fast-forward and splits the declaration into `.#merge._1` and `.#merge._2` so caller
         typechecking is 100% preserved across both branches.

  Every function in this module is 100% pure, total, and kernel-reducible (passing
  `checkClosureCertification` with zero `partial`, `unsafe`, `sorry`, or banned opaques).
-/
module

public import Ix.Frontend.Elab.Command

@[expose] public section

namespace Ix.Frontend

open Ix.Frontend.Parser
open Ix.Frontend.Elab

/-! ## 1. Disambiguation Modes & Conflict Metadata -/

/-- Strategy for disambiguating conflicting declarations with the same `Ix.Name`. -/
inductive DisambigMode where
  /-- Default first-class conflict naming: `orig.#merge._1` and `orig.#merge._2`
      (ordered canonically by 32-byte BLAKE3 Merkle `Address` so 2-way merge is strictly commutative). -/
  | mergeIndexed
  /-- Branch/author-tagged first-class conflict naming: `orig.#merge.<tag1>` and `orig.#merge.<tag2>`. -/
  | mergeNamed (tag1 tag2 : String)
  /-- Prefix namespace disambiguation: `<prefix1>.<orig>` and `<prefix2>.<orig>`
      (e.g. `X.Acme.foobar` and `Y.Acme.foobar`). -/
  | namespacePrefix (prefix1 prefix2 : Ix.Name)
  /-- Flat numeric suffix disambiguation: `<orig>_1` and `<orig>_2`. -/
  | indexedSuffix
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Record of a disambiguated conflict produced during a 2-way or 3-way module merge. -/
structure MergeConflictInfo where
  origName           : Ix.Name
  leftName           : Ix.Name
  rightName          : Ix.Name
  leftDigest         : Address
  rightDigest        : Address
  isSemanticConflict : Bool := false
  deriving BEq, Repr, Inhabited

/-- Complete result of a 2-way or 3-way `IxVCS` module merge. -/
structure MergeOutcome where
  sched         : ModuleSchedule
  conflicts     : Array MergeConflictInfo
  leftRenaming  : NameMap Ix.Name
  rightRenaming : NameMap Ix.Name
  moduleStx     : Ix.Syntax
  deriving Repr, Inhabited

/-! ## 2. Source-Info-Insensitive `Syntax` Comparison & BLAKE3-256 Digest Computation -/

/-- Compare two `List Ix.Syntax` lexicographically using `cmpRec`. -/
def cmpSyntaxList (cmpRec : Ix.Syntax → Ix.Syntax → Ordering) :
    List Ix.Syntax → List Ix.Syntax → Ordering
  | [], []           => .eq
  | [], _ :: _       => .lt
  | _ :: _, []       => .gt
  | a :: as, b :: bs =>
    match cmpRec a b with
    | .eq => cmpSyntaxList cmpRec as bs
    | ord => ord

/-- Pure, total, source-position-insensitive structural ordering on `Ix.Syntax`
    (used as a deterministic tie-breaker if two distinct ASTs ever share a hash). -/
def cmpSyntaxPure : Nat → Ix.Syntax → Ix.Syntax → Ordering
  | 0, _, _ => .eq
  | fuel + 1, s1, s2 =>
    match s1, s2 with
    | .missing, .missing => .eq
    | .missing, _        => .lt
    | _, .missing        => .gt
    | .atom _ v1, .atom _ v2 => strCmpPure v1 v2
    | .atom _ _, _           => .lt
    | _, .atom _ _           => .gt
    | .ident _ _ id1 p1, .ident _ _ id2 p2 =>
      match compare id1 id2 with
      | .eq => natCmpPure p1.size p2.size
      | ord => ord
    | .ident .., _ => .lt
    | _, .ident .. => .gt
    | .node _ k1 as1, .node _ k2 as2 =>
      match compare k1 k2 with
      | .eq =>
        match natCmpPure as1.size as2.size with
        | .eq => cmpSyntaxList (cmpSyntaxPure fuel) as1.toList as2.toList
        | ord => ord
      | ord => ord

/-- Source-position-insensitive structural equality on `Ix.Syntax`. -/
def syntaxBeqPure (s1 s2 : Ix.Syntax) (fuel : Nat := 256) : Bool :=
  cmpSyntaxPure fuel s1 s2 == .eq

/-- Compute a deterministic, source-position-insensitive 32-byte BLAKE3 `Address`
    for an `Ix.Syntax` tree via `Address.admissionHash`. -/
def hashSyntaxPure : Nat → Ix.Syntax → Address
  | 0, _ => Address.admissionHash (ByteArray.mk #[0])
  | fuel + 1, stx =>
    match stx with
    | .missing =>
      Address.admissionHash (ByteArray.mk #[1])
    | .atom _ val =>
      Address.admissionHash (ByteArray.mk #[2] ++ val.toUTF8)
    | .ident _ _ id _ =>
      Address.admissionHash (ByteArray.mk #[3] ++ (Name.computeHash id).hash)
    | .node _ kind args =>
      let initBytes := ByteArray.mk #[4] ++ (Name.computeHash kind).hash
      let allBytes := args.toList.foldl (fun acc child =>
        acc ++ (hashSyntaxPure fuel child).hash) initBytes
      Address.admissionHash allBytes

/-- Encode a `DeclKind` as a single tag byte for domain-separated hashing. -/
def declKindTag : DeclKind → UInt8
  | .defn       => 1
  | .abbrev     => 2
  | .thm        => 3
  | .opaqueDecl => 4
  | .axiomDecl  => 5
  | .inst       => 6
  | .ind        => 7
  | .struct     => 8
  | .cls        => 9

/-- Compute the intrinsic 32-byte BLAKE3 `Address` of a `ModuleDecl`
    (covering its `DeclKind`, `fullName`, `univParams`, and position-stripped `stx`). -/
def hashDeclIntrinsic (d : ModuleDecl) : Address :=
  let b0 := ByteArray.mk #[0xD0, declKindTag d.kind] ++ (Name.computeHash d.fullName).hash
  let b1 := d.univParams.foldl (fun acc u => acc ++ (Name.computeHash u).hash) b0
  let b2 := b1 ++ (hashSyntaxPure 256 d.stx).hash
  Address.admissionHash b2

/-- Per-declaration intrinsic and bottom-up SCC Merkle digests for a `ModuleSchedule`. -/
structure ModuleDigests where
  intrinsic : NameMap Address := NameMap.empty
  merkle    : NameMap Address := NameMap.empty
  deriving Repr, Inhabited

/-- Compute both intrinsic and bottom-up SCC Merkle BLAKE3-256 digests for all
    declarations in `sched : ModuleSchedule`. -/
def computeModuleDigests (sched : ModuleSchedule) : ModuleDigests :=
  let declList := sched.modIdx.decls.toList
  let intrinsic : NameMap Address := declList.foldl (fun acc d =>
    acc.insert d.fullName (hashDeclIntrinsic d)) NameMap.empty
  let merkle : NameMap Address := sched.sccs.toList.foldl (fun acc scc =>
    let sccDecls := scc.declIdxs.toList.filterMap (Syntax.listGet? declList)
    -- Collect sorted external dependency Merkle digests for this SCC
    let depDigests : Array Address := sccDecls.foldl (fun dAcc d =>
      let depInfo := Syntax.listGetD sched.deps.toList d.idx { declIdx := d.idx }
      let allRefIdxs := (depInfo.sigRefs ++ depInfo.bodyRefs).toList
      allRefIdxs.foldl (fun dAcc2 refIdx =>
        match Syntax.listGet? declList refIdx with
        | some refDecl =>
          if scc.declIdxs.toList.contains refIdx then dAcc2
          else
            let refHash := (acc.get? refDecl.fullName).getD
              ((intrinsic.get? refDecl.fullName).getD dummyAddr)
            dAcc2.push refHash
        | none => dAcc2) dAcc) #[]
    let sortedDeps := sortArrayBy depDigests (fun a b => bytesCmp a.hash.data.toList b.hash.data.toList == .lt)
    let depBytes := sortedDeps.toList.foldl (fun b h => b ++ h.hash) (ByteArray.mk #[0xD1])
    let sccIntrBytes := sccDecls.foldl (fun b d =>
      let ih := (intrinsic.get? d.fullName).getD dummyAddr
      b ++ ih.hash) depBytes
    let sccDigest := Address.admissionHash sccIntrBytes
    sccDecls.foldl (fun acc2 d =>
      let ih := (intrinsic.get? d.fullName).getD dummyAddr
      let dMerkle := Address.admissionHash (ByteArray.mk #[0xD2] ++ sccDigest.hash ++ ih.hash)
      acc2.insert d.fullName dMerkle) acc) NameMap.empty
  { intrinsic, merkle }

/-- Total, canonical comparison between two declarations `(d1, dig1)` and `(d2, dig2)`:
    compares their 32-byte Merkle `Address`, then their intrinsic `Address`, and finally
    `cmpSyntaxPure 256 d1.stx d2.stx`. -/
def cmpDeclCanonical (d1 : ModuleDecl) (m1 i1 : Address)
    (d2 : ModuleDecl) (m2 i2 : Address) : Ordering :=
  match bytesCmp m1.hash.data.toList m2.hash.data.toList with
  | .eq =>
    match bytesCmp i1.hash.data.toList i2.hash.data.toList with
    | .eq => cmpSyntaxPure 256 d1.stx d2.stx
    | ord => ord
  | ord => ord

/-! ## 3. Binder-Aware Reference Rewriting & Hermetic Declaration Normalization -/

/-- Apply `identMap : NameMap Ix.Name` to a resolved symbol `sym`, handling:
    1. Direct declaration match (`identMap.get? sym = some target`).
    2. Hierarchical child match (`sym = origParent ++ childSuffix` where
       `identMap.get? origParent = some newParent`, rewriting constructors `Expr.lit` $\to$
       `Expr.#merge._1.lit`, projections `Point.x` $\to$ `Point.#merge._1.x`, and recursors
       `Expr.recOn` $\to$ `Expr.#merge._1.recOn`). -/
def applySymRename (identMap : NameMap Ix.Name) (sym : Ix.Name) : Option Ix.Name :=
  match identMap.get? sym with
  | some target => some target
  | none =>
    match sym with
    | .str pre last _ =>
      if Name.isAnonymous pre then none
      else
        match identMap.get? pre with
        | some newPre => some (Name.mkStr newPre last)
        | none =>
          match pre with
          | .str pre2 mid _ =>
            if Name.isAnonymous pre2 then none
            else
              match identMap.get? pre2 with
              | some newPre2 => some (Name.mkStr (Name.mkStr newPre2 mid) last)
              | none => none
          | _ => none
    | _ => none

/-- Rewrite a surface identifier `id` in `scope` against `modIdx`:
    - When `identMap` rewrites the resolved target (or `id` directly), returns the renamed `Ix.Name`.
    - When `qualifyAll` is `true` and `id` resolves to a known module declaration/constructor/field
      `resolved != id`, returns `resolved` so the declaration becomes hermetically independent of
      `namespace`/`open` scopes. -/
def rewriteIdentInScope (scope : ScopeSnapshot) (modIdx : ModuleIndex)
    (isExtConst : Ix.Name → Bool) (identMap : NameMap Ix.Name)
    (qualifyAll : Bool) (id : Ix.Name) : Ix.Name :=
  if Name.isAnonymous id then id
  else
    let resolved := resolveIdentInScope scope modIdx isExtConst id
    match applySymRename identMap resolved with
    | some renamed => renamed
    | none =>
      match applySymRename identMap id with
      | some renamed => renamed
      | none =>
        -- Check if `id` is `<shortParent>.<ctorOrField>` where `<shortParent>` resolves in `scope`
        let resCompound? : Option Ix.Name := match id with
          | .str pre last _ =>
            if Name.isAnonymous pre then none
            else
              let resPre := resolveIdentInScope scope modIdx isExtConst pre
              let fullCand := Name.mkStr resPre last
              match applySymRename identMap fullCand with
              | some renamed => some renamed
              | none =>
                if qualifyAll && modIdx.containsSymbol fullCand then some fullCand
                else none
          | _ => none
        match resCompound? with
        | some target => target
        | none =>
          if qualifyAll && modIdx.containsSymbol resolved then resolved
          else id

/-- Construct an `.ident` node preserving `info` and `pre` with updated `newId`. -/
def mkIdentPreserveInfo (info : Ix.SourceInfo) (newId : Ix.Name)
    (pre : Array Ix.SyntaxPreresolved) : Ix.Syntax :=
  let s := Name.toStringTotal newId
  .ident info ⟨s, 0, s.utf8ByteSize⟩ newId pre

/-- Binder-aware pattern rewriter: rewrites constructor references in `pat` while recording
    pattern-bound local variables into `bound : NameSet`. -/
def rewritePattern (scope : ScopeSnapshot) (modIdx : ModuleIndex)
    (isExtConst : Ix.Name → Bool) (isExtCtor : Ix.Name → Bool)
    (identMap : NameMap Ix.Name) (qualifyAll : Bool) :
    Nat → Ix.Syntax → NameSet → Ix.Syntax × NameSet
  | 0, pat, bound => (pat, bound)
  | fuel + 1, pat, bound =>
    match pat with
    | .missing | .atom _ _ => (pat, bound)
    | .ident info _ id pre =>
      if Name.isAnonymous id then (pat, bound)
      else
        let resolved := resolveIdentInScope scope modIdx isExtConst id
        if modIdx.isModuleCtor resolved || isExtCtor resolved then
          let newId := rewriteIdentInScope scope modIdx isExtConst identMap qualifyAll id
          if newId == id then (pat, bound)
          else (mkIdentPreserveInfo info newId pre, bound)
        else
          match id with
          | .str (.anonymous _) _ _ =>
            (pat, bound.insert id)
          | _ =>
            let newId := rewriteIdentInScope scope modIdx isExtConst identMap qualifyAll id
            if newId == id then (pat, bound)
            else (mkIdentPreserveInfo info newId pre, bound)
    | .node info kind args =>
      if kind == SyntaxKind.numLit || kind == SyntaxKind.strLit ||
         kind == SyntaxKind.charLit || kind == SyntaxKind.holeTerm then
        (pat, bound)
      else if kind == SyntaxKind.appTerm then
        let fn := Syntax.listGetD args.toList 0 .missing
        let arg := Syntax.listGetD args.toList 1 .missing
        let (fn', bound1) := match fn with
          | .ident iInfo _ fnId iPre =>
            let resolved := resolveIdentInScope scope modIdx isExtConst fnId
            if modIdx.containsSymbol resolved || isExtCtor resolved || (applySymRename identMap resolved).isSome then
              let newFnId := rewriteIdentInScope scope modIdx isExtConst identMap qualifyAll fnId
              if newFnId == fnId then (fn, bound)
              else (mkIdentPreserveInfo iInfo newFnId iPre, bound)
            else
              rewritePattern scope modIdx isExtConst isExtCtor identMap qualifyAll fuel fn bound
          | _ =>
            rewritePattern scope modIdx isExtConst isExtCtor identMap qualifyAll fuel fn bound
        let (arg', bound2) := rewritePattern scope modIdx isExtConst isExtCtor identMap qualifyAll fuel arg bound1
        (.node info kind #[fn', arg'], bound2)
      else
        let (revChildren, bound') := args.toList.foldl (fun (acc, bnd) child =>
          let (child', bnd') := rewritePattern scope modIdx isExtConst isExtCtor identMap qualifyAll fuel child bnd
          (child' :: acc, bnd')) ([], bound)
        (.node info kind (Array.mk revChildren.reverse), bound')

/-- Rewrite a single binder node's domain type using `rwRec` and extend `locals` with its bound names. -/
def rewriteSingleBinder (rwRec : NameSet → Ix.Syntax → Ix.Syntax)
    (locals : NameSet) (binderStx : Ix.Syntax) : NameSet × Ix.Syntax :=
  let k := Syntax.getKind binderStx
  let binderStx' :=
    if k == SyntaxKind.explicitBinder || k == SyntaxKind.implicitBinder ||
       k == SyntaxKind.strictImplicitBinder || k == SyntaxKind.instBinder then
      match binderStx with
      | .node info bk bargs =>
        let tyNode := Syntax.listGetD bargs.toList 3 .missing
        if Syntax.isNone tyNode || Syntax.isMissing tyNode then binderStx
        else
          let tyNode' := rwRec locals tyNode
          .node info bk (arraySetD bargs 3 tyNode')
      | _ => binderStx
    else
      binderStx
  let names := extractBinderNames binderStx
  let locals' := names.foldl (fun s n => s.insert n) locals
  (locals', binderStx')

/-- Rewrite an array of binder nodes left-to-right, threading bound local names. -/
def rewriteBinderArray (rwRec : NameSet → Ix.Syntax → Ix.Syntax)
    (locals : NameSet) (binders : Array Ix.Syntax) : NameSet × Array Ix.Syntax :=
  let (locals', revBinders) := binders.toList.foldl (fun (loc, acc) b =>
    let (loc', b') := rewriteSingleBinder rwRec loc b
    (loc', b' :: acc)) (locals, [])
  (locals', Array.mk revBinders.reverse)

/-- Binder-aware term/type/tactic `Syntax` rewriter: rewrites free references via
    `rewriteIdentInScope` while respecting all local variable binders (`fun`, `forall`,
    `let`, `have`, `if h :`, `match` patterns, structure field projections, and tactics). -/
def rewriteSyntaxRefs (scope : ScopeSnapshot) (modIdx : ModuleIndex)
    (isExtConst : Ix.Name → Bool) (isExtCtor : Ix.Name → Bool)
    (identMap : NameMap Ix.Name) (qualifyAll : Bool) :
    Nat → NameSet → Ix.Syntax → Ix.Syntax
  | 0, _, stx => stx
  | fuel + 1, locals, stx =>
    let rwRec := rewriteSyntaxRefs scope modIdx isExtConst isExtCtor identMap qualifyAll fuel
    match stx with
    | .missing | .atom _ _ => stx
    | .ident info _ id pre =>
      if Name.isAnonymous id || locals.contains id then
        stx
      else
        -- Check if `id` is `<localVar>.<field>` (first component is in `locals`)
        let headComp := match Name.components id with
          | c :: _ => Name.simple c
          | []     => Name.mkAnon
        if !Name.isAnonymous headComp && locals.contains headComp then
          stx
        else
          let newId := rewriteIdentInScope scope modIdx isExtConst identMap qualifyAll id
          if newId == id then stx
          else mkIdentPreserveInfo info newId pre
    | .node info kind args =>
      -- 1. `fun binders => body`
      if kind == SyntaxKind.funTerm then
        let bNode := Syntax.listGetD args.toList 1 .missing
        let body := Syntax.listGetD args.toList 3 .missing
        let (locals', bArgs') := rewriteBinderArray rwRec locals (Syntax.getArgs bNode)
        let bNode' := match bNode with
          | .node bi bk _ => .node bi bk bArgs'
          | other => other
        let body' := rwRec locals' body
        .node info kind (arraySetD (arraySetD args 1 bNode') 3 body')
      -- 2. `forall binders, vPref body` or `(binders) → vPref body`
      else if kind == SyntaxKind.forallTerm then
        let isKwForall := match Syntax.listGet? args.toList 0 with
          | some (.atom _ kw) => kw == "forall" || kw == "∀"
          | _ => false
        let bIdx := if isKwForall then 1 else 0
        let bodyIdx := if isKwForall then 4 else 3
        let bNode := Syntax.listGetD args.toList bIdx .missing
        let body := Syntax.listGetD args.toList bodyIdx .missing
        let (locals', bArgs') := rewriteBinderArray rwRec locals (Syntax.getArgs bNode)
        let bNode' := match bNode with
          | .node bi bk _ => .node bi bk bArgs'
          | other => other
        let body' := rwRec locals' body
        .node info kind (arraySetD (arraySetD args bIdx bNode') bodyIdx body')
      -- 3. `let bPref id binders optType := val; body`
      else if kind == SyntaxKind.letTerm then
        let idStx := Syntax.listGetD args.toList 2 .missing
        let bNode := Syntax.listGetD args.toList 3 .missing
        let optTy := Syntax.listGetD args.toList 4 .missing
        let val := Syntax.listGetD args.toList 6 .missing
        let body := Syntax.listGetD args.toList 8 .missing
        let (localsBind, bArgs') := rewriteBinderArray rwRec locals (Syntax.getArgs bNode)
        let bNode' := match bNode with | .node bi bk _ => .node bi bk bArgs' | o => o
        let optTy' := rwRec localsBind optTy
        let val' := rwRec localsBind val
        let letId := Syntax.getId idStx
        let localsBody := if Name.isAnonymous letId then locals else locals.insert letId
        let body' := rwRec localsBody body
        let args1 := arraySetD (arraySetD args 3 bNode') 4 optTy'
        let args2 := arraySetD (arraySetD args1 6 val') 8 body'
        .node info kind args2
      -- 4. `let borrow` / `let rec`
      else if kind == SyntaxKind.letBorrowTerm || kind == SyntaxKind.letRecTerm then
        let idStx := Syntax.listGetD args.toList 3 .missing
        let bNode := Syntax.listGetD args.toList 4 .missing
        let optTy := Syntax.listGetD args.toList 5 .missing
        let val := Syntax.listGetD args.toList 7 .missing
        let body := Syntax.listGetD args.toList 9 .missing
        let letId := Syntax.getId idStx
        let localsInit :=
          if kind == SyntaxKind.letRecTerm && !Name.isAnonymous letId then locals.insert letId
          else locals
        let (localsBind, bArgs') := rewriteBinderArray rwRec localsInit (Syntax.getArgs bNode)
        let bNode' := match bNode with | .node bi bk _ => .node bi bk bArgs' | o => o
        let optTy' := rwRec localsBind optTy
        let val' := rwRec localsBind val
        let localsBody := if Name.isAnonymous letId then locals else locals.insert letId
        let body' := rwRec localsBody body
        let args1 := arraySetD (arraySetD args 4 bNode') 5 optTy'
        let args2 := arraySetD (arraySetD args1 7 val') 9 body'
        .node info kind args2
      -- 5. `have id optType := val; body`
      else if kind == SyntaxKind.haveTerm then
        let idStx := Syntax.listGetD args.toList 1 .missing
        let optTy := Syntax.listGetD args.toList 2 .missing
        let val := Syntax.listGetD args.toList 4 .missing
        let body := Syntax.listGetD args.toList 6 .missing
        let optTy' := rwRec locals optTy
        let val' := rwRec locals val
        let haveId := Syntax.getId idStx
        let localsBody := if Name.isAnonymous haveId then locals else locals.insert haveId
        let body' := rwRec localsBody body
        let args1 := arraySetD (arraySetD args 2 optTy') 4 val'
        .node info kind (arraySetD args1 6 body')
      -- 6. `if [h :] cond then t else e`
      else if kind == SyntaxKind.ifTerm then
        if args.size == 8 then
          let hId := Syntax.getId (Syntax.listGetD args.toList 1 .missing)
          let cond := Syntax.listGetD args.toList 3 .missing
          let thenBr := Syntax.listGetD args.toList 5 .missing
          let elseBr := Syntax.listGetD args.toList 7 .missing
          let cond' := rwRec locals cond
          let locals' := if Name.isAnonymous hId then locals else locals.insert hId
          let thenBr' := rwRec locals' thenBr
          let elseBr' := rwRec locals' elseBr
          let args1 := arraySetD (arraySetD args 3 cond') 5 thenBr'
          .node info kind (arraySetD args1 7 elseBr')
        else
          let cond := Syntax.listGetD args.toList 2 .missing
          let thenBr := Syntax.listGetD args.toList 4 .missing
          let elseBr := Syntax.listGetD args.toList 6 .missing
          let cond' := rwRec locals cond
          let thenBr' := rwRec locals thenBr
          let elseBr' := rwRec locals elseBr
          let args1 := arraySetD (arraySetD args 2 cond') 4 thenBr'
          .node info kind (arraySetD args1 6 elseBr')
      -- 7. `| pat1, pat2 => rhs` (`matchAlt`)
      else if kind == SyntaxKind.matchAlt then
        let patsNode := Syntax.listGetD args.toList 1 .missing
        let rhs := Syntax.listGetD args.toList 3 .missing
        let (revPats, locals') := (Syntax.getArgs patsNode).toList.foldl (fun (acc, bnd) p =>
          let (p', bnd') := rewritePattern scope modIdx isExtConst isExtCtor identMap qualifyAll fuel p bnd
          (p' :: acc, bnd')) ([], locals)
        let patsNode' := match patsNode with
          | .node pi pk _ => .node pi pk (Array.mk revPats.reverse)
          | other => other
        let rhs' := rwRec locals' rhs
        .node info kind (arraySetD (arraySetD args 1 patsNode') 3 rhs')
      -- 8. Projection `base.field` (`projTerm`): rewrite `base` (`args[0]`), keep `field` (`args[2]`) as short field name
      else if kind == SyntaxKind.projTerm then
        let base := Syntax.listGetD args.toList 0 .missing
        let base' := rwRec locals base
        .node info kind (arraySetD args 0 base')
      -- 9. Structure field assignment `field := val` (`structFieldAssign`): keep `args[0]` (`field`), rewrite `args[2]` (`val`)
      else if kind == SyntaxKind.structFieldAssign then
        let val := Syntax.listGetD args.toList 2 .missing
        let val' := rwRec locals val
        .node info kind (arraySetD args 2 val')
      -- 10. Tactic sequence
      else if kind == SyntaxKind.tacticSeq then
        let (_, revTacs) := args.toList.foldl (fun (loc, acc) tac =>
          let tk := Syntax.getKind tac
          if tk == SyntaxKind.tacticIntro || tk == SyntaxKind.tacticFunext || tk == SyntaxKind.tacticExt then
            let ids := (Syntax.getArgs (Syntax.getArg tac 1)).toList.map Syntax.getId
            let loc' := ids.foldl (fun s id => if Name.isAnonymous id then s else s.insert id) loc
            (loc', tac :: acc)
          else if tk == SyntaxKind.tacticHave || tk == SyntaxKind.tacticLet then
            let lId := Syntax.getId (Syntax.getArg tac 1)
            let optTy := Syntax.getArg tac 2
            let val := Syntax.getArg tac 4
            let optTy' := rwRec loc optTy
            let val' := rwRec loc val
            let tac' := match tac with
              | .node ti tk' targs => .node ti tk' (arraySetD (arraySetD targs 2 optTy') 4 val')
              | o => o
            let loc' := if Name.isAnonymous lId then loc else loc.insert lId
            (loc', tac' :: acc)
          else
            (loc, rwRec loc tac :: acc)) (locals, [])
        .node info kind (Array.mk revTacs.reverse)
      else if kind == SyntaxKind.tacticAlt || kind == SyntaxKind.tacticCase then
        let boundIds := (Syntax.getArgs (Syntax.listGetD args.toList 2 .missing)).toList.map Syntax.getId
        let locals' := boundIds.foldl (fun s id => if Name.isAnonymous id then s else s.insert id) locals
        let seq := Syntax.listGetD args.toList 4 .missing
        let seq' := rwRec locals' seq
        .node info kind (arraySetD args 4 seq')
      else if kind == SyntaxKind.tacticRw then
        let rules := Syntax.listGetD args.toList 2 .missing
        let rules' := rwRec locals rules
        .node info kind (arraySetD args 2 rules')
      else if kind == SyntaxKind.tacticSimp || kind == SyntaxKind.tacticDSimp then
        let rules := Syntax.listGetD args.toList 1 .missing
        let rules' := rwRec locals rules
        .node info kind (arraySetD args 1 rules')
      else
        let children' := Array.mk (args.toList.map (rwRec locals))
        .node info kind children'

/-- Rewrite a `ModuleDecl` under `identMap : NameMap Ix.Name` (and optionally hermetically
    normalize it by folding `scope.levelNames` and `scope.varBinders` into the declaration AST
    and qualifying all scope-resolved module references). -/
def rewriteModuleDecl (modIdx : ModuleIndex)
    (isExtConst : Ix.Name → Bool) (isExtCtor : Ix.Name → Bool)
    (identMap : NameMap Ix.Name) (hermetic : Bool)
    (decl : ModuleDecl) (fuel : Nat := 256) : ModuleDecl :=
  let scope := decl.scope
  let newFullName := (identMap.get? decl.fullName).getD decl.fullName
  let newShortName := if hermetic || newFullName != decl.fullName then newFullName else decl.shortName
  let newUnivs :=
    if hermetic then (decl.univParams ++ scope.levelNames).eraseDups
    else decl.univParams
  let rwRec := rewriteSyntaxRefs scope modIdx isExtConst isExtCtor identMap hermetic fuel
  let cmd := decl.stx
  let k := Syntax.getKind cmd
  match cmd with
  | .node info ck cargs =>
    -- Merge section `variable` binders if `hermetic` is true
    let origBindersNode := Syntax.listGetD cargs.toList 4 (Syntax.mkNullNode #[])
    let origBinders := Syntax.getArgs origBindersNode
    let combinedBinders : Array Ix.Syntax :=
      if hermetic && !scope.varBinders.isEmpty then
        let existingNames : List Ix.Name := origBinders.toList.flatMap extractBinderNames
        let neededVars := scope.varBinders.toList.filter fun vb =>
          let vNames := extractBinderNames vb
          !vNames.any (existingNames.contains ·)
        Array.mk neededVars ++ origBinders
      else
        origBinders
    let (localsSig, binders') := rewriteBinderArray rwRec NameSet.empty combinedBinders
    let newBindersNode := Syntax.mkNullNode binders'
    let newIdNode := Syntax.mkSimpleIdent newShortName
    let newUnivNode :=
      if newUnivs.isEmpty then Syntax.listGetD cargs.toList 3 (Syntax.mkNullNode #[])
      else Ix.Syntax.node .none SyntaxKind.univParamsKind (Array.mk (newUnivs.map Syntax.mkSimpleIdent))
    let cargsBase := arraySetD (arraySetD (arraySetD cargs 2 newIdNode) 3 newUnivNode) 4 newBindersNode
    let newCmd : Ix.Syntax :=
      if k == SyntaxKind.defDecl || k == SyntaxKind.abbrevDecl ||
         k == SyntaxKind.theoremDecl || k == SyntaxKind.opaqueDecl then
        let optTy := Syntax.listGetD cargsBase.toList 6 .missing
        let optTy' := rwRec localsSig optTy
        let cargs1 := arraySetD cargsBase 6 optTy'
        if cargs1.size == 9 then
          let body := Syntax.listGetD cargs1.toList 8 .missing
          let body' := rwRec localsSig body
          .node info ck (arraySetD cargs1 8 body')
        else
          let alts := Syntax.listGetD cargs1.toList 7 .missing
          let alts' := rwRec localsSig alts
          .node info ck (arraySetD cargs1 7 alts')
      else if k == SyntaxKind.axiomDecl then
        let ty := Syntax.listGetD cargsBase.toList 6 .missing
        let ty' := rwRec localsSig ty
        .node info ck (arraySetD cargsBase 6 ty')
      else if k == SyntaxKind.instanceDecl then
        let ty := Syntax.listGetD cargsBase.toList 6 .missing
        let body := Syntax.listGetD cargsBase.toList 8 .missing
        let ty' := rwRec localsSig ty
        let body' := rwRec localsSig body
        .node info ck (arraySetD (arraySetD cargsBase 6 ty') 8 body')
      else if k == SyntaxKind.inductiveDecl then
        -- Add the inductive's own name to `identMap` if renamed, and rewrite constructors & deriving
        let optTy := Syntax.listGetD cargsBase.toList 6 .missing
        let ctorsNode := Syntax.listGetD cargsBase.toList 7 .missing
        let derivNode := Syntax.listGetD cargsBase.toList 8 .missing
        let optTy' := rwRec localsSig optTy
        let ctors' := Array.mk ((Syntax.getArgs ctorsNode).toList.map fun ctorStx =>
          match ctorStx with
          | .node ci ck' cArgs =>
            let cbNode := Syntax.listGetD cArgs.toList 2 .missing
            let cOptTy := Syntax.listGetD cArgs.toList 4 .missing
            let (localsCtor, cbArgs') := rewriteBinderArray rwRec localsSig (Syntax.getArgs cbNode)
            let cbNode' := Syntax.mkNullNode cbArgs'
            let cOptTy' := rwRec localsCtor cOptTy
            Ix.Syntax.node ci ck' (arraySetD (arraySetD cArgs 2 cbNode') 4 cOptTy')
          | other => other)
        let ctorsNode' := Syntax.mkNullNode ctors'
        let derivNode' := rwRec localsSig derivNode
        let cargs1 := arraySetD (arraySetD cargsBase 6 optTy') 7 ctorsNode'
        .node info ck (arraySetD cargs1 8 derivNode')
      else if k == SyntaxKind.structureDecl || k == SyntaxKind.classDecl then
        let extNode := Syntax.listGetD cargsBase.toList 5 .missing
        let optTy := Syntax.listGetD cargsBase.toList 7 .missing
        let fieldsNode := Syntax.listGetD cargsBase.toList 9 .missing
        let derivNode := Syntax.listGetD cargsBase.toList 10 .missing
        let extNode' := rwRec localsSig extNode
        let optTy' := rwRec localsSig optTy
        let (_, revFields) := (Syntax.getArgs fieldsNode).toList.foldl (fun (loc, acc) item =>
          if Syntax.isOfKind item SyntaxKind.ctorDecl then
            match item with
            | .node ci ck' cArgs =>
              let cbNode := Syntax.listGetD cArgs.toList 2 .missing
              let cOptTy := Syntax.listGetD cArgs.toList 4 .missing
              let (locCtor, cbArgs') := rewriteBinderArray rwRec loc (Syntax.getArgs cbNode)
              let cbNode' := Syntax.mkNullNode cbArgs'
              let cOptTy' := rwRec locCtor cOptTy
              (loc, Ix.Syntax.node ci ck' (arraySetD (arraySetD cArgs 2 cbNode') 4 cOptTy') :: acc)
            | other => (loc, other :: acc)
          else if Syntax.isOfKind item SyntaxKind.fieldDecl then
            match item with
            | .node fi fk fArgs =>
              let isBracketed := match Syntax.listGet? fArgs.toList 0 with
                | some (.atom _ "(") | some (.atom _ "{") => true
                | _ => false
              let idsIdx := if isBracketed then 2 else 1
              let tyIdx  := if isBracketed then 5 else 4
              let defIdx := if isBracketed then 6 else 5
              let idsNode := Syntax.listGetD fArgs.toList idsIdx .missing
              let tyNode  := Syntax.listGetD fArgs.toList tyIdx .missing
              let defNode := Syntax.listGetD fArgs.toList defIdx .missing
              let tyNode' := rwRec loc tyNode
              let defNode' := rwRec loc defNode
              let fIds := (Syntax.getArgs idsNode).toList.map Syntax.getId
              let loc' := fIds.foldl (fun s id => if Name.isAnonymous id then s else s.insert id) loc
              let fArgs' := arraySetD (arraySetD fArgs tyIdx tyNode') defIdx defNode'
              (loc', Ix.Syntax.node fi fk fArgs' :: acc)
            | other => (loc, other :: acc)
          else
            (loc, rwRec loc item :: acc)) (localsSig, [])
        let fieldsNode' := Syntax.mkNullNode (Array.mk revFields.reverse)
        let derivNode' := rwRec localsSig derivNode
        let cargs1 := arraySetD (arraySetD cargsBase 5 extNode') 7 optTy'
        let cargs2 := arraySetD (arraySetD cargs1 9 fieldsNode') 10 derivNode'
        .node info ck cargs2
      else
        .node info ck cargsBase
    let newCtors := decl.ctorNames.map fun c =>
      match c with
      | .str _ last _ => Name.mkStr newFullName last
      | _ => c
    let newFields := decl.fieldNames.map fun f =>
      match f with
      | .str _ last _ => Name.mkStr newFullName last
      | _ => f
    let newScope : ScopeSnapshot :=
      if hermetic then { isPrivate := scope.isPrivate, isProtected := scope.isProtected }
      else scope
    { decl with
      shortName  := newShortName
      fullName   := newFullName
      univParams := newUnivs
      scope      := newScope
      stx        := newCmd
      ctorNames  := newCtors
      fieldNames := newFields }
  | _ => decl

/-- Rebuild a fresh `ModuleIndex` from an array of `ModuleDecl`s and an `IxImportMap`. -/
def buildModuleIndexFromDecls (decls : Array ModuleDecl)
    (importMap : IxImportMap := IxImportMap.empty) : ModuleIndex :=
  let initIdx : ModuleIndex := { importMap }
  decls.toList.foldl (fun acc d => acc.registerDecl d) initIdx

/-- Synthesize a `SyntaxKind.moduleKind` AST from a `ModuleSchedule`'s declarations. -/
def synthesizeModuleSyntax (sched : ModuleSchedule) : Ix.Syntax :=
  let declList := sched.modIdx.decls.toList
  let orderedCmds : List Ix.Syntax := sched.sccs.toList.flatMap fun scc =>
    let sccDecls := scc.declIdxs.toList.filterMap (Syntax.listGet? declList)
    sccDecls.map (·.stx)
  Syntax.mkNode SyntaxKind.moduleKind (Array.mk orderedCmds)

/-- Hermetically normalize every declaration in `sched : ModuleSchedule` so each declaration
    carries its own fully qualified name, universe parameters, section variables, and
    fully qualified module references. -/
def hermeticizeModule (sched : ModuleSchedule)
    (isExtConst : Ix.Name → Bool := fun _ => false)
    (isExtCtor : Ix.Name → Bool := fun _ => false) : Except String ModuleSchedule := do
  let hermDecls := Array.mk (sched.modIdx.decls.toList.map fun d =>
    rewriteModuleDecl sched.modIdx isExtConst isExtCtor NameMap.empty true d)
  let newModIdx := buildModuleIndexFromDecls hermDecls sched.modIdx.importMap
  scheduleModuleDecls newModIdx isExtConst isExtCtor

/-! ## 4. Intra-Declaration Semantic & AST Pre-Merge -/

/-- Check whether an `Ix.Expr` contains `sorryAx`. -/
def exprHasSorry : Nat → Ix.Expr → Bool
  | 0, _ => false
  | _ + 1, .const nm _ _ => nm == Name.simple "sorryAx" || nm == Name.simple "sorry"
  | f + 1, .app fn arg _ => exprHasSorry f fn || exprHasSorry f arg
  | f + 1, .lam _ t b _ _ => exprHasSorry f t || exprHasSorry f b
  | f + 1, .forallE _ t b _ _ => exprHasSorry f t || exprHasSorry f b
  | f + 1, .letE _ t v b _ _ => exprHasSorry f t || exprHasSorry f v || exprHasSorry f b
  | f + 1, .proj _ _ s _ => exprHasSorry f s
  | f + 1, .mdata _ e _ => exprHasSorry f e
  | _, _ => false

/-- Check whether two elaborated constants `ci1` and `ci2` in `baseEnv` can be unified
    semantically without creating a `.#merge` conflict:
    1. **Proof Irrelevance Absorption**: Both are `.thmInfo` (or `Prop`-typed) with the same
       level parameters and definitionally equal (`isDefEq`) statement types.
    2. **Definitional Equality**: Both are `.defnInfo` with the same level parameters and
       definitionally equal types and values. -/
def canSemanticallyUnifyConsts (baseEnv : IxElabEnv)
    (ci1 ci2 : Ix.ConstantInfo) : Bool :=
  let c1 := Expr.ConstantInfo.getCnstPure ci1
  let c2 := Expr.ConstantInfo.getCnstPure ci2
  if c1.levelParams != c2.levelParams then false
  else
    let act : IxElabM Bool := do
      let tyEq ← isDefEq 64 c1.type c2.type
      if !tyEq then return false
      else
        match ci1, ci2 with
        | .thmInfo _, .thmInfo _ =>
          return true
        | .defnInfo v1, .defnInfo v2 =>
          -- Also check if the type is a `Prop` (`Sort 0`), or if the values are `isDefEq`
          let tySort ← whnf 64 (← inferType 64 c1.type)
          match stripMData tySort with
          | .sort (.zero _) _ => return true
          | _ => isDefEq 64 v1.value v2.value
        | .axiomInfo _, .axiomInfo _ =>
          return true
        | _, _ =>
          return false
    match IxElabM.run' act {} { env := baseEnv } with
    | .ok ok => ok
    | .error _ => false

/-- Try to unify two declarations `d1` and `d2` that share the same `fullName`:
    1. Fast path: identical intrinsic hash and position-stripped syntax (`syntaxBeqPure`).
    2. Semantic path: elaborate `d1` and `d2` individually against `sharedEnv`; if both elaborate
       and satisfy `canSemanticallyUnifyConsts` (proof irrelevance for `theorem`s or `isDefEq`
       for `def`s), pick the canonically smaller declaration (preferring `sorryAx`-free proofs). -/
def tryUnifySameNameDecls (sharedEnv : IxElabEnv)
    (d1 : ModuleDecl) (m1 i1 : Address)
    (d2 : ModuleDecl) (m2 i2 : Address) : Option ModuleDecl :=
  if bytesBeq i1.hash.data.toList i2.hash.data.toList && syntaxBeqPure d1.stx d2.stx then
    some (if cmpDeclCanonical d1 m1 i1 d2 m2 i2 == .gt then d2 else d1)
  else if d1.kind != d2.kind then
    none
  else
    -- Try elaborating `d1` and `d2` as singleton modules over `sharedEnv`
    let idx1 := buildModuleIndexFromDecls #[d1]
    let idx2 := buildModuleIndexFromDecls #[d2]
    match scheduleModuleDecls idx1 (fun n => sharedEnv.contains n) (fun n => sharedEnv.isCtor n),
          scheduleModuleDecls idx2 (fun n => sharedEnv.contains n) (fun n => sharedEnv.isCtor n) with
    | .ok s1, .ok s2 =>
      match elabModuleSchedule s1 sharedEnv false, elabModuleSchedule s2 sharedEnv false with
      | .ok env1, .ok env2 =>
        match env1.find? d1.fullName, env2.find? d2.fullName with
        | some ci1, some ci2 =>
          if canSemanticallyUnifyConsts sharedEnv ci1 ci2 then
            let s1HasSorry := match ci1 with
              | .thmInfo v => exprHasSorry 64 v.value
              | .defnInfo v => exprHasSorry 64 v.value
              | _ => false
            let s2HasSorry := match ci2 with
              | .thmInfo v => exprHasSorry 64 v.value
              | .defnInfo v => exprHasSorry 64 v.value
              | _ => false
            if s1HasSorry && !s2HasSorry then some d2
            else if s2HasSorry && !s1HasSorry then some d1
            else some (if cmpDeclCanonical d1 m1 i1 d2 m2 i2 == .gt then d2 else d1)
          else
            none
        | _, _ => none
      | _, _ => none
    | _, _ => none

/-- Keyed 3-way merge of `matchAlt` sequences (`| pat => rhs` arms keyed by constructor/pattern head).
    If `left` and `right` modified disjoint arms relative to `base`, splices both edits! -/
def mergeMatchAlts3 (baseAlts leftAlts rightAlts : Ix.Syntax) : Option Ix.Syntax :=
  let bArms := (Syntax.getArgs baseAlts).toList
  let lArms := (Syntax.getArgs leftAlts).toList
  let rArms := (Syntax.getArgs rightAlts).toList
  if !Syntax.isOfKind baseAlts SyntaxKind.nullKind ||
     !Syntax.isOfKind leftAlts SyntaxKind.nullKind ||
     !Syntax.isOfKind rightAlts SyntaxKind.nullKind ||
     bArms.isEmpty ||
     !bArms.all (Syntax.isOfKind · SyntaxKind.matchAlt) ||
     bArms.length != lArms.length || bArms.length != rArms.length then
    none
  else
    let rec go : List Ix.Syntax → List Ix.Syntax → List Ix.Syntax → Option (List Ix.Syntax)
      | [], [], [] => some []
      | b :: bs, l :: ls, r :: rs =>
        let bPat := Syntax.getArg b 1
        let lPat := Syntax.getArg l 1
        let rPat := Syntax.getArg r 1
        if !syntaxBeqPure bPat lPat || !syntaxBeqPure bPat rPat then
          none
        else
          let chosen? : Option Ix.Syntax :=
            if syntaxBeqPure l r then some l
            else if syntaxBeqPure b l then some r
            else if syntaxBeqPure b r then some l
            else none
          match chosen?, go bs ls rs with
          | some arm, some rest => some (arm :: rest)
          | _, _ => none
      | _, _, _ => none
    match go bArms lArms rArms with
    | some mergedArms =>
      some (Syntax.mkNullNode (Array.mk mergedArms))
    | none => none

/-- Keyed 3-way merge of `structInst` (`{ f₁ := v₁, f₂ := v₂ }` keyed by field name). -/
def mergeStructInst3 (baseStx leftStx rightStx : Ix.Syntax) : Option Ix.Syntax :=
  if !Syntax.isOfKind baseStx SyntaxKind.structInst ||
     !Syntax.isOfKind leftStx SyntaxKind.structInst ||
     !Syntax.isOfKind rightStx SyntaxKind.structInst then
    none
  else
    let bAssigns := (Syntax.getArgs (Syntax.getArg baseStx 2)).toList
    let lAssigns := (Syntax.getArgs (Syntax.getArg leftStx 2)).toList
    let rAssigns := (Syntax.getArgs (Syntax.getArg rightStx 2)).toList
    if bAssigns.length != lAssigns.length || bAssigns.length != rAssigns.length then
      none
    else
      let rec go : List Ix.Syntax → List Ix.Syntax → List Ix.Syntax → Option (List Ix.Syntax)
        | [], [], [] => some []
        | b :: bs, l :: ls, r :: rs =>
          let bField := Syntax.getId (Syntax.getArg b 0)
          let lField := Syntax.getId (Syntax.getArg l 0)
          let rField := Syntax.getId (Syntax.getArg r 0)
          if bField != lField || bField != rField then none
          else
            let chosen? : Option Ix.Syntax :=
              if syntaxBeqPure l r then some l
              else if syntaxBeqPure b l then some r
              else if syntaxBeqPure b r then some l
              else none
            match chosen?, go bs ls rs with
            | some item, some rest => some (item :: rest)
            | _, _ => none
        | _, _, _ => none
      match go bAssigns lAssigns rAssigns with
      | some merged =>
        match leftStx with
        | .node info k args =>
          some (.node info k (arraySetD args 2 (Syntax.mkNullNode (Array.mk merged))))
        | _ => none
      | none => none

/-- Recursive 3-way AST splice on term/command `Syntax` nodes (`base`, `left`, `right`).
    Succeeds when changes in `left` and `right` relative to `base` occur in disjoint subtrees
    (including keyed `matchAlts` and `structInst` nodes). -/
def spliceSyntax3 : Nat → Ix.Syntax → Ix.Syntax → Ix.Syntax → Option Ix.Syntax
  | 0, _, _, _ => none
  | fuel + 1, b, l, r =>
    if syntaxBeqPure l r then some l
    else if syntaxBeqPure b l then some r
    else if syntaxBeqPure b r then some l
    else
      match mergeMatchAlts3 b l r with
      | some m => some m
      | none =>
        match mergeStructInst3 b l r with
        | some m => some m
        | none =>
          match b, l, r with
          | .node _ kb asB, .node info kl asL, .node _ kr asR =>
            if kb != kl || kb != kr || asB.size != asL.size || asB.size != asR.size then
              none
            else
              let rec goChildren : List Ix.Syntax → List Ix.Syntax → List Ix.Syntax → Option (List Ix.Syntax)
                | [], [], [] => some []
                | cb :: cbs, cl :: cls, cr :: crs =>
                  match spliceSyntax3 fuel cb cl cr, goChildren cbs cls crs with
                  | some c', some rest => some (c' :: rest)
                  | _, _ => none
                | _, _, _ => none
              match goChildren asB.toList asL.toList asR.toList with
              | some children' => some (.node info kl (Array.mk children'))
              | none => none
          | _, _, _ => none

/-- Attempt a 3-way AST splice on a declaration `dBase`, `dLeft`, `dRight` with the same name. -/
def tryMergeDeclSyntax3 (dBase dLeft dRight : ModuleDecl) : Option ModuleDecl :=
  if dBase.kind != dLeft.kind || dBase.kind != dRight.kind then none
  else
    match spliceSyntax3 128 dBase.stx dLeft.stx dRight.stx with
    | some mergedStx => some { dLeft with stx := mergedStx }
    | none           => none

/-! ## 5. Disambiguated Conflict Name Generation -/

/-- Pick the pair of disambiguated names `(nameForFirst, nameForSecond)` for a conflicted
    declaration `origName`, avoiding any existing names in `usedNames : NameSet`. -/
def makeDisambiguatedPair (mode : DisambigMode) (usedNames : NameSet)
    (origName : Ix.Name) : Ix.Name × Ix.Name :=
  match mode with
  | .mergeIndexed =>
    let rec findFreePair (fuel : Nat) (startIdx : Nat) : Ix.Name × Ix.Name :=
      match fuel with
      | 0 => (Name.mkMergeVariant origName "_1", Name.mkMergeVariant origName "_2")
      | fuel + 1 =>
        let cand1 := Name.mkMergeVariant origName s!"_{startIdx}"
        let cand2 := Name.mkMergeVariant origName s!"_{startIdx + 1}"
        if !usedNames.contains cand1 && !usedNames.contains cand2 then
          (cand1, cand2)
        else
          findFreePair fuel (startIdx + 1)
    findFreePair 64 1
  | .mergeNamed tag1 tag2 =>
    (Name.mkMergeVariant origName tag1, Name.mkMergeVariant origName tag2)
  | .namespacePrefix pre1 pre2 =>
    (Name.append pre1 origName, Name.append pre2 origName)
  | .indexedSuffix =>
    let comps := Name.components origName
    let basePre := Name.fromComponents comps.dropLast
    let lastStr := comps.getLastD "decl"
    (Name.mkStr basePre s!"{lastStr}_1", Name.mkStr basePre s!"{lastStr}_2")

/-! ## 6. 2-Way Disambiguating Module Merge (`mergeModuleSchedule2`, `mergeSource2`) -/

/-- Perform a 2-way module merge of `sched1` and `sched2`:
    1. Hermetically normalizes both schedules and computes their bottom-up BLAKE3-256 digests.
    2. Pre-elaborates the shared non-conflicting core so `tryUnifySameNameDecls` can absorb
       proof-irrelevant theorem differences and definitionally equal definitions.
    3. For every remaining same-name collision `origName`, orders the two variants canonically
       by 32-byte BLAKE3 Merkle `Address` (in symmetric modes `.mergeIndexed` and `.indexedSuffix`)
       and assigns disambiguated names via `makeDisambiguatedPair`.
    4. Binder-awarely rewrites all declarations in `sched1` under `leftRenaming` and all
       declarations in `sched2` under `rightRenaming`, orders the merged declaration set
       canonically, and schedules it via Tarjan SCC condensation. -/
def mergeModuleSchedule2 (sched1 sched2 : ModuleSchedule)
    (mode : DisambigMode := .mergeIndexed)
    (initEnv : IxElabEnv := IxElabEnv.empty)
    (seedPrelude : Bool := true)
    (semanticConflicts : NameSet := NameSet.empty) : Except String MergeOutcome := do
  let isExtConst (n : Ix.Name) : Bool := initEnv.contains n
  let isExtCtor (n : Ix.Name) : Bool := initEnv.isCtor n
  let h1 ← hermeticizeModule sched1 isExtConst isExtCtor
  let h2 ← hermeticizeModule sched2 isExtConst isExtCtor
  let dig1 := computeModuleDigests h1
  let dig2 := computeModuleDigests h2
  let decls1 := h1.modIdx.decls.toList
  let decls2 := h2.modIdx.decls.toList

  -- Collect all existing declaration names across both modules
  let allOrigNames : NameSet :=
    decls2.foldl (fun s d => s.insert d.fullName)
      (decls1.foldl (fun s d => s.insert d.fullName) NameSet.empty)

  -- Partition declarations present in both `h1` and `h2` into:
  -- (a) syntactically identical declarations (`sharedFast`), and
  -- (b) candidate collisions (`candidates`)
  let (sharedFastDecls, candidates) := decls1.foldl
    (fun (shAcc, candAcc) d1 =>
      match h2.modIdx.declByName.get? d1.fullName with
      | none => (shAcc, candAcc)
      | some idx2 =>
        match Syntax.listGet? decls2 idx2 with
        | none => (shAcc, candAcc)
        | some d2 =>
          if semanticConflicts.contains d1.fullName then
            (shAcc, (d1, d2) :: candAcc)
          else
            let i1 := (dig1.intrinsic.get? d1.fullName).getD dummyAddr
            let i2 := (dig2.intrinsic.get? d2.fullName).getD dummyAddr
            if bytesBeq i1.hash.data.toList i2.hash.data.toList && syntaxBeqPure d1.stx d2.stx then
              (d1 :: shAcc, candAcc)
            else
              (shAcc, (d1, d2) :: candAcc))
    ([], [])

  -- Elaborate the fast-shared core (when possible) to provide a base environment for
  -- semantic unification (proof-irrelevance absorption & `isDefEq` check)
  let sharedCoreEnv : IxElabEnv :=
    let base0 := if seedPrelude then seedCorePreludeIfMissing initEnv h1.modIdx else initEnv
    let shIdx := buildModuleIndexFromDecls (Array.mk sharedFastDecls.reverse)
    match scheduleModuleDecls shIdx (fun n => base0.contains n) (fun n => base0.isCtor n) with
    | .ok shSched =>
      match elabModuleSchedule shSched base0 false with
      | .ok env => env
      | .error _ => base0
    | .error _ => base0

  -- Classify each candidate pair into either `unifiedMap` or `conflictPairs`
  let isSymmetricMode := match mode with
    | .mergeIndexed | .indexedSuffix => true
    | .mergeNamed _ _ | .namespacePrefix _ _ => false

  let (unifiedMap, revConflicts, leftRen, rightRen, _) :=
    candidates.reverse.foldl
      (fun (uMap, cAcc, lRen, rRen, used) (d1, d2) =>
        let nm := d1.fullName
        let m1 := (dig1.merkle.get? nm).getD dummyAddr
        let i1 := (dig1.intrinsic.get? nm).getD dummyAddr
        let m2 := (dig2.merkle.get? nm).getD dummyAddr
        let i2 := (dig2.intrinsic.get? nm).getD dummyAddr
        let unified? :=
          if semanticConflicts.contains nm then none
          else tryUnifySameNameDecls sharedCoreEnv d1 m1 i1 d2 m2 i2
        match unified? with
        | some uDecl =>
          (uMap.insert nm uDecl, cAcc, lRen, rRen, used)
        | none =>
          let (candA, candB) := makeDisambiguatedPair mode used nm
          let swapOrder :=
            isSymmetricMode && cmpDeclCanonical d1 m1 i1 d2 m2 i2 == .gt
          let (leftTarget, rightTarget) :=
            if swapOrder then (candB, candA) else (candA, candB)
          let cInfo : MergeConflictInfo := {
            origName           := nm
            leftName           := leftTarget
            rightName          := rightTarget
            leftDigest         := m1
            rightDigest        := m2
            isSemanticConflict := semanticConflicts.contains nm
          }
          let used' := (used.insert leftTarget).insert rightTarget
          (uMap, cInfo :: cAcc, lRen.insert nm leftTarget, rRen.insert nm rightTarget, used'))
      (NameMap.empty, [], NameMap.empty, NameMap.empty, allOrigNames)

  let fastSet : NameSet := sharedFastDecls.foldl (fun s d => s.insert d.fullName) NameSet.empty

  -- Build rewritten declarations from `h1` (including `sharedFast`, `unifiedMap`, `O₁`, and `σ₁(K)`)
  let rewritten1 : List ModuleDecl := decls1.map fun d1 =>
    let nm := d1.fullName
    if fastSet.contains nm then
      rewriteModuleDecl h1.modIdx isExtConst isExtCtor leftRen false d1
    else
      match unifiedMap.get? nm with
      | some uDecl =>
        rewriteModuleDecl h1.modIdx isExtConst isExtCtor leftRen false uDecl
      | none =>
        rewriteModuleDecl h1.modIdx isExtConst isExtCtor leftRen false d1

  -- Build rewritten declarations from `h2` that are NOT in `fastSet` or `unifiedMap` (i.e. `O₂` and `σ₂(K)`)
  let rewritten2 : List ModuleDecl := decls2.filterMap fun d2 =>
    let nm := d2.fullName
    if fastSet.contains nm || unifiedMap.contains nm then
      none
    else
      some (rewriteModuleDecl h2.modIdx isExtConst isExtCtor rightRen false d2)

  -- Combine `rewritten1 ++ rewritten2` and sort canonically by `(fullName, cmpSyntaxPure)` so
  -- declaration order in the merged module is 100% independent of `sched1` vs `sched2` argument order!
  let allMergedDecls := Array.mk (rewritten1 ++ rewritten2)
  let sortedMergedDecls := sortArrayBy allMergedDecls fun a b =>
    match compare a.fullName b.fullName with
    | .lt => true
    | .gt => false
    | .eq => cmpSyntaxPure 256 a.stx b.stx == .lt

  let mergedImportMap := h1.modIdx.importMap.merge h2.modIdx.importMap
  let mergedModIdx := buildModuleIndexFromDecls sortedMergedDecls mergedImportMap
  let mergedSched ← scheduleModuleDecls mergedModIdx isExtConst isExtCtor
  let mergedStx := synthesizeModuleSyntax mergedSched
  -- Sort `conflicts` canonically by `origName`
  let sortedConflicts := sortArrayBy (Array.mk revConflicts.reverse) fun a b =>
    compare a.origName b.origName == .lt
  return {
    sched         := mergedSched
    conflicts     := sortedConflicts
    leftRenaming  := leftRen
    rightRenaming := rightRen
    moduleStx     := mergedStx
  }

/-- Parse and 2-way merge two `.ix` source strings `src1` and `src2`. -/
def mergeSource2 (src1 src2 : String)
    (mode : DisambigMode := .mergeIndexed)
    (initEnv : IxElabEnv := IxElabEnv.empty)
    (seedPrelude : Bool := true) : Except String MergeOutcome := do
  let (stx1, _) ← parseModuleWithEnv src1 "<left>"
  let (stx2, _) ← parseModuleWithEnv src2 "<right>"
  let modIdx1 ← buildModuleIndex stx1
  let modIdx2 ← buildModuleIndex stx2
  let base1 := if seedPrelude then seedCorePreludeIfMissing initEnv modIdx1 else initEnv
  let base2 := if seedPrelude then seedCorePreludeIfMissing initEnv modIdx2 else initEnv
  let sched1 ← scheduleModuleDecls modIdx1 (fun n => base1.contains n) (fun n => base1.isCtor n)
  let sched2 ← scheduleModuleDecls modIdx2 (fun n => base2.contains n) (fun n => base2.isCtor n)
  mergeModuleSchedule2 sched1 sched2 mode initEnv seedPrelude

/-! ## 7. 3-Way Type-Contract-Preserving Module Merge (`mergeModuleSchedule3`, `mergeSource3`) -/

/-- Perform a 3-way module merge of `leftSched` ($M_1$) and `rightSched` ($M_2$) over common
    ancestor `baseSched` ($M_0$), enforcing the **Caller-Callee Type-Checking Contract**:
    1. **1-Sided Deletion Propagation**: If $M_1$ deleted declaration $d \in M_0$ and $M_2$ left $d$
       unchanged and has no new callers of $d$ that fail without $d$, $d$ is deleted in the merge.
    2. **1-Sided Update Fast-Forward vs. Semantic Conflict Split (Cases A, B, C, D)**:
       If $M_1$ modified $d$ ($d_0 \mapsto d_1$) and $M_2$ left $d$ unchanged ($d_2 = d_0$):
       - We test substituting $d_1$ into $M_2$ (`M₂[d ↦ d₁]`) and running `elabModuleSchedule`.
       - **Cases A & B (Elaboration succeeds)**: All callers and theorems in $M_2$ still typecheck
         against $d_1$! We fast-forward $d \mapsto d_1$ in $M_2'$ so $d$ unifies cleanly with zero
         `.#merge` conflicts.
       - **Cases C & D (Elaboration fails — e.g. a theorem in $M_2$ unfolded $d_0$'s body via `rfl`,
         or $M_1$ changed $d$'s type signature)**: Fast-forwarding $d_1$ would break caller
         typechecking in $M_2$! We reject the fast-forward and mark $d$ in `semanticConflicts`,
         so `mergeModuleSchedule2` splits $d$ into `d.#merge._1` (used by $M_1$'s callers) and
         `d.#merge._2` (retaining $d_0$ for $M_2$'s callers), preserving 100% caller typechecking.
    3. **2-Sided AST Pre-Merge (`tryMergeDeclSyntax3`)**:
       If both $M_1$ and $M_2$ modified $d$, attempts a 3-way AST splice (`spliceSyntax3`,
       including keyed `match` arms and `structInst` fields) and verifies that the spliced
       declaration elaborates cleanly in both $M_1$ and $M_2$. -/
def mergeModuleSchedule3 (baseSched leftSched rightSched : ModuleSchedule)
    (mode : DisambigMode := .mergeIndexed)
    (initEnv : IxElabEnv := IxElabEnv.empty)
    (seedPrelude : Bool := true) : Except String MergeOutcome := do
  let isExtConst (n : Ix.Name) : Bool := initEnv.contains n
  let isExtCtor (n : Ix.Name) : Bool := initEnv.isCtor n
  let h0 ← hermeticizeModule baseSched isExtConst isExtCtor
  let h1 ← hermeticizeModule leftSched isExtConst isExtCtor
  let h2 ← hermeticizeModule rightSched isExtConst isExtCtor
  let dig0 := computeModuleDigests h0
  let dig1 := computeModuleDigests h1
  let dig2 := computeModuleDigests h2
  let decls0 := h0.modIdx.decls.toList
  let decls1 := h1.modIdx.decls.toList
  let decls2 := h2.modIdx.decls.toList

  let sameDeclAsBase (dBranch : ModuleDecl) (digBranch : ModuleDigests) (dBase : ModuleDecl) : Bool :=
    let iB := (digBranch.intrinsic.get? dBranch.fullName).getD dummyAddr
    let i0 := (dig0.intrinsic.get? dBase.fullName).getD dummyAddr
    bytesBeq iB.hash.data.toList i0.hash.data.toList && syntaxBeqPure dBranch.stx dBase.stx

  -- Helper to test whether replacing/removing declarations in `targetDecls` still elaborates cleanly
  let canElaborateDecls (candDecls : List ModuleDecl) (impMap : IxImportMap) : Bool :=
    let cIdx := buildModuleIndexFromDecls (Array.mk candDecls) impMap
    let baseEnv := if seedPrelude then seedCorePreludeIfMissing initEnv cIdx else initEnv
    match scheduleModuleDecls cIdx (fun n => baseEnv.contains n) (fun n => baseEnv.isCtor n) with
    | .ok cSched => (elabModuleSchedule cSched baseEnv false).isOk
    | .error _   => false

  -- Step 1: Propagate 1-sided deletions and 1-sided updates from `h1` into `decls2`,
  -- and symmetrically from `h2` into `decls1`, gated by `canElaborateDecls`!
  let (decls1', decls2', semConflicts) := decls0.foldl
    (fun (cur1, cur2, semSet) d0 =>
      let nm := d0.fullName
      let in1? := cur1.find? (fun d => d.fullName == nm)
      let in2? := cur2.find? (fun d => d.fullName == nm)
      match in1?, in2? with
      | none, none =>
        (cur1, cur2, semSet)
      | none, some d2 =>
        -- Deleted in Left, present in Right: if unchanged in Right and Right elaborates without `nm`, delete it
        if sameDeclAsBase d2 dig2 d0 then
          let cand2 := cur2.filter (fun d => d.fullName != nm)
          if canElaborateDecls cand2 h2.modIdx.importMap then
            (cur1, cand2, semSet)
          else
            (cur1, cur2, semSet.insert nm)
        else
          (cur1, cur2, semSet)
      | some d1, none =>
        -- Deleted in Right, present in Left: if unchanged in Left and Left elaborates without `nm`, delete it
        if sameDeclAsBase d1 dig1 d0 then
          let cand1 := cur1.filter (fun d => d.fullName != nm)
          if canElaborateDecls cand1 h1.modIdx.importMap then
            (cand1, cur2, semSet)
          else
            (cur1, cur2, semSet.insert nm)
        else
          (cur1, cur2, semSet)
      | some d1, some d2 =>
        let unch1 := sameDeclAsBase d1 dig1 d0
        let unch2 := sameDeclAsBase d2 dig2 d0
        if unch1 && unch2 then
          (cur1, cur2, semSet)
        else if !unch1 && unch2 then
          -- Modified in Left (`d1`), untouched in Right (`d2 == d0`):
          -- Test whether substituting `d1` into Right (`cur2`) preserves typechecking of all Right callers!
          let cand2 := cur2.map (fun d => if d.fullName == nm then d1 else d)
          if canElaborateDecls cand2 h2.modIdx.importMap then
            -- Cases A & B: Fast-forward Right's copy of `nm` to `d1`!
            (cur1, cand2, semSet)
          else
            -- Cases C & D: Right has a caller/theorem whose typechecking depends on `d0`!
            -- Mark `nm` as a semantic conflict so it is split into `nm.#merge._1` and `nm.#merge._2`.
            (cur1, cur2, semSet.insert nm)
        else if unch1 && !unch2 then
          -- Modified in Right (`d2`), untouched in Left (`d1 == d0`):
          -- Test whether substituting `d2` into Left (`cur1`) preserves typechecking of all Left callers!
          let cand1 := cur1.map (fun d => if d.fullName == nm then d2 else d)
          if canElaborateDecls cand1 h1.modIdx.importMap then
            (cand1, cur2, semSet)
          else
            (cur1, cur2, semSet.insert nm)
        else
          -- Both Left and Right modified `nm`: try 3-way AST splice (`tryMergeDeclSyntax3`)
          match tryMergeDeclSyntax3 d0 d1 d2 with
          | some splicedDecl =>
            let cand1 := cur1.map (fun d => if d.fullName == nm then splicedDecl else d)
            let cand2 := cur2.map (fun d => if d.fullName == nm then splicedDecl else d)
            if canElaborateDecls cand1 h1.modIdx.importMap &&
               canElaborateDecls cand2 h2.modIdx.importMap then
              (cand1, cand2, semSet)
            else
              (cur1, cur2, semSet)
          | none =>
            (cur1, cur2, semSet))
    (decls1, decls2, NameSet.empty)

  let propIdx1 := buildModuleIndexFromDecls (Array.mk decls1') h1.modIdx.importMap
  let propIdx2 := buildModuleIndexFromDecls (Array.mk decls2') h2.modIdx.importMap
  let propSched1 ← scheduleModuleDecls propIdx1 isExtConst isExtCtor
  let propSched2 ← scheduleModuleDecls propIdx2 isExtConst isExtCtor
  mergeModuleSchedule2 propSched1 propSched2 mode initEnv seedPrelude semConflicts

/-- Parse and 3-way merge `.ix` source strings `baseSrc`, `leftSrc`, and `rightSrc`. -/
def mergeSource3 (baseSrc leftSrc rightSrc : String)
    (mode : DisambigMode := .mergeIndexed)
    (initEnv : IxElabEnv := IxElabEnv.empty)
    (seedPrelude : Bool := true) : Except String MergeOutcome := do
  let (stx0, _) ← parseModuleWithEnv baseSrc "<base>"
  let (stx1, _) ← parseModuleWithEnv leftSrc "<left>"
  let (stx2, _) ← parseModuleWithEnv rightSrc "<right>"
  let modIdx0 ← buildModuleIndex stx0
  let modIdx1 ← buildModuleIndex stx1
  let modIdx2 ← buildModuleIndex stx2
  let base0 := if seedPrelude then seedCorePreludeIfMissing initEnv modIdx0 else initEnv
  let base1 := if seedPrelude then seedCorePreludeIfMissing initEnv modIdx1 else initEnv
  let base2 := if seedPrelude then seedCorePreludeIfMissing initEnv modIdx2 else initEnv
  let sched0 ← scheduleModuleDecls modIdx0 (fun n => base0.contains n) (fun n => base0.isCtor n)
  let sched1 ← scheduleModuleDecls modIdx1 (fun n => base1.contains n) (fun n => base1.isCtor n)
  let sched2 ← scheduleModuleDecls modIdx2 (fun n => base2.contains n) (fun n => base2.isCtor n)
  mergeModuleSchedule3 sched0 sched1 sched2 mode initEnv seedPrelude

/-! ## 8. Conflict Resolution (`resolveConflictVariant`) & Elaboration Helper -/

/-- Elaborate a `MergeOutcome` into an `IxElabEnv` (converting `ElabError` to `String`). -/
def MergeOutcome.elaborate (outcome : MergeOutcome)
    (initEnv : IxElabEnv := IxElabEnv.empty)
    (seedPrelude : Bool := true) : Except String IxElabEnv :=
  match elabModuleSchedule outcome.sched initEnv seedPrelude with
  | .ok env  => .ok env
  | .error e => .error (toString e)

/-- Resolve a `.#merge` conflict on `origName` in `sched` by selecting `chosenTag`
    (e.g. `"_1"` or `"_2"`):
    - Drops all other `origName.#merge.<otherTag>` variant declarations from `sched`.
    - Renames `origName.#merge.<chosenTag>` (and all references to any `origName.#merge.*`
      variant across the module) back to `origName`.
    - Reschedules and verifies that the resolved module elaborates and typechecks! -/
def resolveConflictVariant (sched : ModuleSchedule)
    (origName : Ix.Name) (chosenTag : String)
    (initEnv : IxElabEnv := IxElabEnv.empty)
    (seedPrelude : Bool := true) : Except String ModuleSchedule := do
  let isExtConst (n : Ix.Name) : Bool := initEnv.contains n
  let isExtCtor (n : Ix.Name) : Bool := initEnv.isCtor n
  let variants := sched.modIdx.findConflictVariants origName
  let chosenFull := Name.mkMergeVariant origName chosenTag
  if !sched.modIdx.declByName.contains chosenFull then
    throw s!"conflict variant '{Name.toStringTotal chosenFull}' not found in module"
  let collapseMap : NameMap Ix.Name := variants.foldl
    (fun acc (_, varFull) => acc.insert varFull origName)
    (NameMap.empty.insert chosenFull origName)
  let keptDecls := sched.modIdx.decls.toList.filter fun d =>
    match Name.splitMergeVariant? d.fullName with
    | some (orig, tag, []) => orig != origName || tag == chosenTag
    | _ => true
  let rewrittenDecls := Array.mk (keptDecls.map fun d =>
    rewriteModuleDecl sched.modIdx isExtConst isExtCtor collapseMap true d)
  let newModIdx := buildModuleIndexFromDecls rewrittenDecls sched.modIdx.importMap
  let baseEnv := if seedPrelude then seedCorePreludeIfMissing initEnv newModIdx else initEnv
  let newSched ← scheduleModuleDecls newModIdx (fun n => baseEnv.contains n) (fun n => baseEnv.isCtor n)
  match elabModuleSchedule newSched baseEnv false with
  | .ok _    => return newSched
  | .error e => throw s!"conflict resolution to '{Name.toStringTotal chosenFull}' failed typecheck: {e}"

/-! ## 9. Mechanized Algebraic Properties of `.#merge` Addressing & Canonical Ordering -/

/-- `Name.splitMergeVariant? (Name.mkMergeVariant orig tag)` recovers `(orig, tag, [])`
    by definitional equality (`rfl`) for every `orig : Ix.Name` and `tag : String`. -/
theorem splitMergeVariant_mkMergeVariant (orig : Ix.Name) (tag : String) :
    Name.splitMergeVariant? (Name.mkMergeVariant orig tag) = some (orig, tag, []) :=
  rfl

/-- `Name.isMergeConflict` is `true` on any `Name.mkMergeVariant orig tag` by `rfl`. -/
theorem isMergeConflict_mkMergeVariant (orig : Ix.Name) (tag : String) :
    Name.isMergeConflict (Name.mkMergeVariant orig tag) = true :=
  rfl

/-- `Name.conflictOrigName? (Name.mkMergeVariant orig tag)` recovers `some orig` by `rfl`. -/
theorem conflictOrigName_mkMergeVariant (orig : Ix.Name) (tag : String) :
    Name.conflictOrigName? (Name.mkMergeVariant orig tag) = some orig :=
  rfl

/-- `bytesBeq` is reflexive on any byte list `bs : List UInt8`. -/
theorem bytesBeq_refl (bs : List UInt8) : bytesBeq bs bs = true := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp [bytesBeq, ih]

/-- `charsBeq` is reflexive on any character list `cs : List Char`. -/
theorem charsBeq_refl (cs : List Char) : charsBeq cs cs = true := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp [charsBeq, ih]

/-- `strBeqPure` is reflexive on any `s : String`. -/
theorem strBeqPure_refl (s : String) : strBeqPure s s = true := by
  simp [strBeqPure, charsBeq_refl]

/-- `natCmpPure` is reflexive on any `n : Nat`. -/
theorem natCmpPure_refl (n : Nat) : natCmpPure n n = .eq := by
  simp [natCmpPure]

/-- `bytesCmp` is reflexive on any `bs : List UInt8`. -/
theorem bytesCmp_refl (bs : List UInt8) : bytesCmp bs bs = .eq := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have h : ¬ (b.toNat + 1 ≤ b.toNat) := by omega
    simp [bytesCmp, h, ih]

/-- `charsCmp` is reflexive on any `cs : List Char`. -/
theorem charsCmp_refl (cs : List Char) : charsCmp cs cs = .eq := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    have h : ¬ (c.toNat + 1 ≤ c.toNat) := by omega
    simp [charsCmp, h, ih]

/-- `strCmpPure` is reflexive on any `s : String`. -/
theorem strCmpPure_refl (s : String) : strCmpPure s s = .eq := by
  simp [strCmpPure, natCmpPure_refl, charsCmp_refl]

end Ix.Frontend
