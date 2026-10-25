import LSpec
import Ix.CompileM
import Ix.CompileCert.RecordRead

/-! Controls for the ordinary expression compiler's frame
(`Ix.CompileM.compileExprNoSurgery`, through the dispatching `compileExpr` on
an environment without call-site plans): App spines are flattened, partial
spines are allocated but never cached, cache hits reuse roots, failures keep
their completed children's effects, and a DAG-shared term compiles without a
walk of its tree (the former fuel `exprCompileDepth` was exponential on it). -/

namespace Tests.Ix.Compile.ExpressionFrame

open LSpec
open _root_.Ix (Name Expr)
open _root_.Ix.CompileM

private def context : CompileEnv × BlockEnv :=
  ((default : CompileEnv),
    { all := {}, current := Name.mkAnon, mutCtx := default, univCtx := [] })

private def raw (action : CompileM α) (state : BlockState := {}) :
    Except CompileError α × BlockState := (action context).run state

def controls : List (String × Bool) := Id.run do
  let f := Expr.mkBVar 0
  let a := Expr.mkBVar 1
  let b := Expr.mkBVar 2
  let inner := Expr.mkApp f a
  let outer := Expr.mkApp inner b
  let (compiled, after) := raw (compileExpr outer)
  let (innerResult, afterInner) := raw (compileExpr inner) after
  let (cached, afterCached) := raw (compileExpr outer) afterInner
  let seeded : BlockState := {
    exprCache := ({} : Std.HashMap _root_.Ix.Compile.ExactKey.ExprKey (Ixon.Expr × UInt64)).insert inner (.var 99, 99) }
  let (seedResult, seedAfter) := raw (compileExpr outer) seeded
  let broken := Expr.mkApp inner (Expr.mkMVar (Name.fromLeanName `missing))
  let (failure, failed) := raw (compileExpr broken)
  -- A 64-level shared DAG has exponentially many tree occurrences. A
  -- runtime walk of the tree would make this small regression infeasible.
  let mut shared := f
  for _ in [:64] do
    shared := Expr.mkLam Name.mkAnon shared shared .default
  let (sharedResult, sharedAfter) := raw (compileExpr shared)
  -- Semantic-contract wrappers are cached under their exact source key.
  let contract : _root_.Ix.SemanticContract.Contract := {
    kind := .lam, binder := ⟨.linear, .shared⟩ }
  let contractData := #[
    (Name.fromLeanName `ix.contract, _root_.Ix.DataValue.ofNat 3),
    (Name.fromLeanName `ix.contract.kind, _root_.Ix.DataValue.ofNat contract.kindCode),
    (Name.fromLeanName `ix.contract.code, _root_.Ix.DataValue.ofNat contract.code)]
  let binder := Expr.mkLam Name.mkAnon (Expr.mkSort _root_.Ix.Level.mkZero) f .default
  let annotated := Expr.mkMData contractData binder
  let (annotation, annotationAfter) := raw (compileExpr annotated)
  let (annotationAgain, annotationAgainAfter) := raw (compileExpr annotated) annotationAfter
  -- Supplied raw keys deliberately share a digest. They exercise the
  -- lookup boundary without claiming a cryptographic collision.
  let colliding : Expr := .bvar 1 f.getHash
  let collidingBad : Expr := .mvar (Name.fromLeanName `missing) f.getHash
  let (_, firstAfter) := raw (compileExpr f)
  let (collision, collisionAfter) := raw (compileExpr colliding) firstAfter
  let (originalAgain, originalAfter) := raw (compileExpr f) collisionAfter
  let (collisionError, collisionErrorAfter) := raw (compileExpr collidingBad) firstAfter
  return [
    ("flattened application result and root",
      compiled.toOption == some (.app (.app (.var 0) (.var 1)) (.var 2), 4)),
    ("head argument application allocation order",
      after.arena.nodes == #[.leaf, .leaf, .app 0 1, .leaf, .app 2 3]),
    ("inner spine is not cached", !after.exprCache.contains inner),
    ("maximal inner occurrence allocates its own application",
      innerResult.toOption == some (.app (.var 0) (.var 1), 5)),
    ("maximal outer occurrence reuses its root",
      cached.isOk && cached.toOption == compiled.toOption && afterCached.arena.nodes.size == 6),
    ("an inner cache entry cannot substitute into the spine",
      seedResult.isOk && seedResult.toOption == compiled.toOption),
    ("the untouched inner entry remains available",
      seedAfter.exprCache.get? inner == some (.var 99, 99)),
    ("error retains completed child effects", (match failure with
        | .error (.unsupportedExpr "metavariable") => true | _ => false) &&
      failed.arena.nodes == #[.leaf, .leaf, .app 0 1] && failed.exprCache.contains f &&
      failed.exprCache.contains a),
    ("failed whole expression is not cached", !failed.exprCache.contains broken),
    ("shared DAG has no runtime tree-size prepass",
      sharedResult.isOk && sharedAfter.arena.nodes.size == 65),
    ("semantic contract lowers the anonymous binder", match annotation with
      | .ok (.lam actual (.sort 0) (.var 0), _) => actual == contract.binder
      | _ => false),
    ("semantic contract wrapper is cached after success",
      annotation.isOk && annotationAfter.exprCache.get? annotated == annotation.toOption),
    ("repeated semantic contract reuses its result and arena",
      annotationAgain.toOption == annotation.toOption &&
        annotationAgainAfter.arena.nodes == annotationAfter.arena.nodes),
    ("different indices sharing a stored hash compile independently",
      collision.toOption == some (.var 1, 1)),
    ("colliding keys retain both cache entries",
      collisionAfter.exprCache.get? f == some (.var 0, 0) &&
      collisionAfter.exprCache.get? colliding == some (.var 1, 1) &&
      collisionAfter.exprCache.size == 2),
    ("colliding insertion preserves the original cached root",
      originalAgain.toOption == some (.var 0, 0) && originalAfter.arena.nodes.size == 2),
    ("a colliding unsupported expression still fails", (match collisionError with
      | .error (.unsupportedExpr "metavariable") => true | _ => false) &&
      collisionErrorAfter.arena.nodes == firstAfter.arena.nodes)
  ]

-- Raw compiler controls: no declaration admission or baseline designation.
def recordControls : List (String × Bool) := Id.run do
  let name := Name.fromLeanName `metadata.external
  let other := Name.fromLeanName `metadata.other
  let u := Name.fromLeanName `u
  let old := "retained blob".toUTF8
  let oldAddr := Address.admissionHash old
  let source := Expr.mkApp (Expr.mkConst name #[_root_.Ix.Level.mkParam u]) (Expr.mkLit (.natVal 17))
  let bad := Expr.mkMVar (Name.fromLeanName `missing)
  let cx : CompileEnv × BlockEnv :=
    ({ context.1 with
        nameToAddr := context.1.nameToAddr.insert name name.getHash
        p3Sources := ({} : Std.HashMap Nat Expr).insert 0 source |>.insert 1 bad },
      { context.2 with univCtx := [u] })
  let seed : BlockState := {
    refs := #[oldAddr], refsIndex := ({} : Std.HashMap Address UInt64).insert oldAddr 0,
    univs := #[.zero], univsIndex := ({} : Std.HashMap Ixon.Univ UInt64).insert .zero 0,
    blockBlobs := ({} : Std.HashMap Address ByteArray).insert oldAddr old }
  let f := Expr.mkBVar 0
  let (plain, seeded) := (compileExprNoSurgery f cx).run seed
  let (empty, _) := (compileExprWithRecords f cx).run seed
  let (metaResult, metaState) := (compileExprMeta source cx).run seeded
  let (metaAgain, metaTwice) := (compileExprMeta source cx).run metaState
  let stale := ({} : Std.HashMap Nat (Nat × UInt64)).insert 0 (99, 99)
  let dirty := { seeded with
    p3Records := seeded.p3Records.insert cx.2.current stale |>.insert other stale
    p3MetaRefs := seeded.p3MetaRefs.insert cx.2.current
      { refs := #[oldAddr], index := ({} : Std.HashMap Address UInt64).insert oldAddr 0 } }
  let (records, recorded) := (compileRecords #[0, 0] cx).run dirty
  let (reused, retained) := (compileRecords #[0] cx).run recorded
  let (failed, partialState) := (compileRecords #[0, 1] cx).run seeded
  let wrap := fun e => Expr.mkMData #[(_root_.Ix.Compile.Pass.inlineKey, .ofNat 0)] e
  let (final, finalState) := (compileExprWithRecords (wrap f) cx).run seeded
  let (valueError, _) := (compileExprWithRecords (wrap bad) cx).run seeded
  let (sourceError, _) := (compileExprWithRecords (wrap bad) ({ cx.1 with p3Sources := {} }, cx.2)).run seeded
  let readerCx : _root_.Ix.Kernel.Reader.Ctx .anon :=
    { store := fun _ => none, blob := fun _ => none, roles := {}, index := {} }
  let read := _root_.Ix.CompileCert.ExpressionRead.blockReader readerCx id (fun _ => none) finalState
  let one : Expr := .bvar 1 f.getHash
  let two : Expr := .bvar 2 f.getHash
  let (first, firstState) := (compileExprMeta one cx).run seeded
  let (second, secondState) := (compileExprMeta two cx).run firstState
  let (original, _) := (compileExprMeta f cx).run secondState
  let contract : _root_.Ix.SemanticContract.Contract := { kind := .lam, binder := ⟨.linear, .shared⟩ }
  let binder := Expr.mkLam Name.mkAnon (Expr.mkSort _root_.Ix.Level.mkZero) f .default
  let (annotated, _) := (compileExprMeta (Expr.mkMData contract.ixMetadata binder) cx).run seeded
  let malformed := Expr.mkMData #[(Name.fromLeanName `ix.contract, .ofNat 3)] bad
  let (contractError, _) := (compileExprMeta malformed cx).run seeded
  -- Explicit raw-key forgery: no claim about canonical decorator output.
  let semanticName := Name.fromLeanName `ix.contract
  let forgedKey := match semanticName with
    | .str parent text _ => Name.str parent text _root_.Ix.Compile.Pass.inlineKey.getHash
    | _ => semanticName
  let forged := Expr.mkMData #[(forgedKey, .ofNat 0)] f
  let substituted := substRecords (({} : Std.HashMap Nat (Nat × UInt64)).insert 0 (0, 0)) forged
  let ingress := _root_.Ix.LeanIngress.ingressExpr (fun _ => 0)
  let kept := fun (s : BlockState) => s.refs == seeded.refs && s.univs == seeded.univs &&
    s.refsIndex.get? oldAddr == some 0 && s.univsIndex.get? .zero == some 0 &&
    s.exprCache.size == seeded.exprCache.size && s.exprCache.get? f == seeded.exprCache.get? f &&
    s.blockNameToAddr.isEmpty && s.auxNameToAddr.isEmpty && s.blockBlobs.get? oldAddr == some old
  return [
    ("empty placeholder path agrees with ordinary compilation", empty.toOption == plain.toOption),
    ("metadata extensions grow while primary tables and cache stay fixed",
      metaResult.isOk && kept metaState && !metaState.metaUnivs.isEmpty &&
        (metaState.p3MetaRefs.get? cx.2.current).any (fun t => t.refs.size == 2)),
    ("metadata memo reuses its actual value and arena",
      metaAgain.toOption == metaResult.toOption && metaTwice.arena.nodes == metaState.arena.nodes),
    ("fresh record reset and duplicate indices produce one slot",
      records.isOk && recorded.surgerySharing.size == 1 && kept recorded &&
        (records.toOption.bind (·.get? 0)).any (fun p => p.1 == 0) &&
        (recorded.p3MetaRefs.get? cx.2.current).any (fun t => !t.index.contains oldAddr)),
    ("reset preserves the other member's records",
      (recorded.p3Records.get? other).bind (·.get? 0) == some (99, 99)),
    ("existing record is reused without new effects", reused.isOk && kept retained &&
      retained.surgerySharing == recorded.surgerySharing && retained.arena.nodes == recorded.arena.nodes),
    ("later metadata error retains the first completed record", (match failed with
      | .error (.unsupportedExpr "metavariable") => true | _ => false) &&
      partialState.surgerySharing.size == 1 && kept partialState),
    ("actual ordinary result reads through its own primary tables", final.isOk &&
      (final.toOption.bind fun v => (read.read v.1).toOption) == some (.bvar 0)),
    ("metadata virtual references are not ordinary primary references",
      (metaResult.toOption).any (fun v => !(read.read v.1).isOk)),
    ("missing record precedes the bad ordinary body", match sourceError with
      | .error (.invalidMutualBlock "Pass 3: no source occurrence for call-site record 0") => true | _ => false),
    ("valid record reaches the bad ordinary body", match valueError with
      | .error (.unsupportedExpr "metavariable") => true | _ => false),
    ("metadata cache distinguishes colliding raw terms and preserves ordinary hits",
      first.toOption.map (·.1) == some (.var 1) && second.toOption.map (·.1) == some (.var 2) &&
      secondState.p3MetaCache.size == 2 && original.toOption == plain.toOption && kept secondState),
    ("metadata compiler retains semantic binder contracts", match annotated with
      | .ok (.lam got (.sort 0) (.var 0), _) => got == contract.binder | _ => false),
    ("malformed semantic contract is rejected before its body", match contractError with
      | .error (.unsupportedExpr "malformed semantic contract frame") => true | _ => false),
    ("raw semantic-key alias witnesses why unconditional substitution erasure is false",
      forgedKey == _root_.Ix.Compile.Pass.inlineKey && !(_root_.Ix.Name.beqRaw forgedKey _root_.Ix.Compile.Pass.inlineKey) &&
      (match ingress forged with | .error (.contract "malformed semantic contract frame") => true | _ => false) &&
      (ingress substituted).toOption == some (.bvar 0))
  ]

def suite : List TestSeq := (controls ++ recordControls).map fun (label, ok) => test s!"expression frame: {label}" ok

end Tests.Ix.Compile.ExpressionFrame
