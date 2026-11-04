import Ix.Compile.SourceGraph.Prepass
import Ix.Cert.Hybrid

/-! Prepass, winner and diagnostic controls; synthetic records make no
Source-acceptance or canonical-name hash-collision claim. -/
namespace Tests.Ix.Cert.SourcePrepass
open _root_.Ix
open _root_.Ix.Compile.SourceGraph
open _root_.Ix.Compile.SourceGraph.Prepass

private def plain : Lean.ConstantInfo := .axiomInfo
  { name := `Prepass.a, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }
private def ctor : Lean.ConstantInfo := .ctorInfo
  { name := `Prepass.I.mk, levelParams := [], type := .sort .zero,
    induct := `Prepass.I, cidx := 2, numParams := 1, numFields := 3, isUnsafe := true }
private def ind : Lean.ConstantInfo := .inductInfo
  { name := `Prepass.I, levelParams := [], type := .sort .zero,
    numParams := 0, numIndices := 0, all := [`Prepass.I], ctors := [`Prepass.I.mk],
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
private def opaq : Lean.ConstantInfo := .opaqueInfo
  { name := `Prepass.o, levelParams := [], type := .sort (.succ .zero),
    value := .sort .zero, isUnsafe := false, all := [`Prepass.o] }
private def input := [ind, ctor, plain, opaq].toArray.map fun ci => (ci.name, ci)
private def prep := run input
private def headerOk (cv : ConstantVal) : Bool :=
  Name.beqRaw cv.name .mkAnon && cv.levelParams.isEmpty &&
  _root_.Ix.Compile.ExactKey.exprEq cv.type (Expr.mkSort Level.mkZero)
private def placeholderOk (wantCtor : Bool) : ConstantInfo → Bool
  | .axiomInfo v => !wantCtor && headerOk v.cnst && !v.isUnsafe
  | .ctorInfo v => wantCtor && headerOk v.cnst && Name.beqRaw v.induct .mkAnon &&
      v.cidx == 0 && v.numParams == 0 && v.numFields == 0 && !v.isUnsafe
  | _ => false
#guard (run #[]).leanByIx.isEmpty && (run #[]).thinConsts.isEmpty && (run #[]).labelled.isEmpty
#guard prep.labelled.size == input.size && prep.leanByIx.size == 4 && prep.thinConsts.size == 4
#guard decide (prep.labelled.map (·.1) = input.map (fun p => Name.fromLeanName p.1))
#guard input.all fun p => (prep.leanByIx.get? (Name.fromLeanName p.1)).any (fun r => r.1 == p.1)
#guard (prep.thinConsts.get? (Name.fromLeanName ctor.name)).any (placeholderOk true)
#guard [ind, plain, opaq].all fun ci => (prep.thinConsts.get? (Name.fromLeanName ci.name)).any (placeholderOk false)
private def addr (n : Nat) : Address := ⟨⟨Array.replicate 32 n.toUInt8⟩⟩
private def first : Name := .str (.anonymous (addr 0)) "first" (addr 1)
private def last : Name := .str (.anonymous (addr 0)) "last" (addr 1)
private def aliases := addNamed (addNamed {} first (ctor.name, ctor)) last (opaq.name, opaq)
#guard first == last && !Name.beqRaw first last
#guard aliases.leanByIx.size == 1 && aliases.thinConsts.size == 1 && aliases.labelled.size == 2
#guard decide (aliases.leanByIx.getKey? first = some last) && decide (aliases.thinConsts.getKey? first = some last)
#guard (aliases.thinConsts.get? first).any (placeholderOk false)
#guard decide (aliases.labelled.map (·.1) = #[first, last])
private def reversed := addNamed (addNamed {} last (opaq.name, opaq)) first (ctor.name, ctor)
#guard (reversed.thinConsts.get? last).any (placeholderOk true)
#guard decide (reversed.leanByIx.getKey? last = some first)
-- Pointwise values do not identify stored representatives or list order.
private def leftMap : Map Name Nat := .ofList [(first, 7)]
private def rightMap : Map Name Nat := .ofList [(last, 7)]
#guard leftMap.get? first == rightMap.get? first && leftMap.get? last == rightMap.get? last
#guard !decide (leftMap.getKey? first = rightMap.getKey? first)
#guard !decide (leftMap.toList = rightMap.toList)
#guard [0, 1, 2, 8].all fun w =>
  let out := (produce input w).2
  let hybrid := _root_.Ix.Cert.Hybrid.hybridEnv out.facts.code prep.leanByIx
  out.facts.code.size == 3 && prep.leanByIx.size - out.facts.code.size == 1 &&
  (hybrid.get? (Name.fromLeanName opaq.name)).any (fun | .opaqueInfo _ => true | _ => false) &&
  (out.facts.code.get? (Name.fromLeanName ind.name)).any (fun | .inductInfo _ => true | _ => false)
private def wrong : Lean.ConstantInfo := .axiomInfo
  { name := ctor.name, levelParams := [], type := .sort .zero, isUnsafe := false }
private def failed := groundConstCheck (_root_.Ix.Cert.Canon.constS ind)
  { consts := (run #[(wrong.name, wrong)]).thinConsts }
#guard match failed with | .error (.indc _ (some ci)) => placeholderOk false ci | _ => false
#guard match failed with | .error e => e.refusal (fun _ => false) ==
  "UNGROUNDED-INPUT: an inductive type whose constructor is missing or not a constructor" | _ => false
#guard match groundConstCheck (_root_.Ix.Cert.Canon.constS ind) { consts := {} } with
  | .error (.indc _ none) => true | _ => false
#guard (groundConstCheck (_root_.Ix.Cert.Canon.constS ind) { consts := prep.thinConsts }).isOk

end Tests.Ix.Cert.SourcePrepass
