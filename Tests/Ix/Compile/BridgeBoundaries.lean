import LSpec
import Tests.Ix.Compile.BridgePortable
open LSpec Ix Ix.AuxGen Ix.CompileM
namespace Tests.Ix.Compile.BridgeBoundaries
private def nm (s : String) : Ix.Name := Ix.Name.fromLeanName s.toName
private def x := nm "x"
private def y := nm "y"
private def u := nm "u"

/-- Every refusal renders to the text CQ2.7 landed (prefix included) and
becomes the compiler error it threw before the type existed: the
elimination decision's kernel failures `invalidMutualBlock`, the rest
`unsupportedExpr`. The `Ix.Tc` texts embedded in `kernel` details (aux-cert
WB-A3's `function expected, got Sort u`) pass through unchanged. -/
private def renderingTable : Bool :=
  let a := Address.blake3 "render".toUTF8
  let rows : List (AuxKernelError × String) := [
    (.unknownLevelParam u #[x, y],
      "aux kernel bridge: unknown level param `u` not found in param_names [x, y]"),
    (.levelMVar, "aux kernel bridge: leanLevelToKuniv: level metavariable"),
    (.closedFVar x, "aux kernel bridge: free variable x in closed ingress"),
    (.closedMVar, "aux kernel bridge: expression metavariable in closed ingress"),
    (.outerMData, "aux kernel bridge: metadata stripping left an outer metadata layer"),
    (.closedBVarIndex 7, "aux kernel bridge: bound variable index 7 exceeds u64 in closed ingress"),
    (.closedProjIndex x 7,
      "aux kernel bridge: projection index 7 of x exceeds u64 in closed ingress"),
    (.unknownFVar x, "aux kernel bridge: toKexprStatic: unknown free variable x"),
    (.fvarOutsideDepth x 2,
      "aux kernel bridge: toKexprStatic: free variable x outside context depth 2"),
    (.openMVar, "aux kernel bridge: toKexprStatic: expression metavariable"),
    (.openBVarIndex 7, "aux kernel bridge: toKexprStatic: bound variable index 7 exceeds u64"),
    (.openProjIndex x 7,
      "aux kernel bridge: toKexprStatic: projection index 7 of x exceeds u64"),
    (.varOutOfRange, "aux kernel bridge: kexprToLean: Var index out of range of outer context"),
    (.missingFVarAt 3, "aux kernel bridge: kexprToLean: missing free variable at outer level 3"),
    (.duplicateFVarAt 3,
      "aux kernel bridge: kexprToLean: duplicate free variable identities at outer level 3"),
    (.leakedKernelFVar 4, "aux kernel bridge: kexprToLean: leaked kernel free variable 4"),
    (.levelParamIndex 1, "aux kernel bridge: kunivToLevel: universe parameter index 1 out of range"),
    (.constLevelArgIndex 1, "aux kernel bridge: kunivToLevelWithConstLevels: constant universe \
argument index 1 out of range"),
    (.duplicateLevelParam u, "aux kernel bridge: duplicate universe parameter 'u'"),
    (.duplicateOuterFVar x, "aux kernel bridge: duplicate outer free variable 'x'"),
    (.duplicatePushedFVar x, "aux kernel bridge: duplicate pushed free variable 'x'"),
    (.staleDepth "pushLocals", "aux kernel bridge: stale scope depth before pushLocals"),
    (.staleScope "push", "aux kernel: scope value superseded before push"),
    (.popExceedsPushed, "aux kernel bridge: popLocals exceeds pushed local count"),
    (.popNotLifo x, "aux kernel bridge: popLocals is not LIFO at 'x'"),
    (.noProvenance a, s!"bridge fault: no forward source provenance for {a}"),
    (.provenanceChanged x, "bridge fault: source address changed for x"),
    (.kernel (.inferUnknownConst a) "",
      s!"TcScope::get_level: tc.infer failed: unknown constant {(toString a).take 12}"),
    (.kernel .infer "function expected, got Sort u",
      "TcScope::get_level: tc.infer failed: function expected, got Sort u"),
    (.kernel .ensureSort "e", "TcScope::get_level: ensure_sort failed: e"),
    (.internal "inference retry exited without a result",
      "aux kernel bridge: inference retry exited without a result")]
  let decisions : List (AuxKernelError × String) := [
    (.kernel (.resultSort "T") "e", "compute_is_large_and_k: TC failed for T: e"),
    (.kernel (.largeElim "T") "e", "compute_is_large_and_k: is_large_eliminator failed for T: e")]
  rows.all (fun (e, text) => e.render == text && e.toCompileError == .unsupportedExpr text)
    && decisions.all fun (e, text) =>
      e.render == text && e.toCompileError == .invalidMutualBlock text

def suite : List TestSeq := [
  test "every refusal renders to the bridge's landed text and compiler error" renderingTable,
  .individualIO "checked egress, full Nat bytes and actual source-address compilation" none
    (do BridgePortable.evaluateBoundaries; return (true, 1, 0, none)) .done]
end Tests.Ix.Compile.BridgeBoundaries
