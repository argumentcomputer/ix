import Ix.Compile.SourceGraph.Literal

namespace Tests.Ix.Cert.SourceGraphLiteral
open _root_.Ix
open _root_.Ix.Compile.SourceGraph

def leaf : Expr := Expr.mkSort Level.mkZero
def dag : Nat → Expr
  | 0 => leaf
  | n + 1 => let child := dag n; Expr.mkApp child child
def unshared : Nat → Nat → Expr
  | 0, seed => Expr.mkConst (Name.mkNat (Name.fromLeanName `LiteralTree) seed) #[]
  | n + 1, seed => Expr.mkApp (unshared n (2 * seed)) (unshared n (2 * seed + 1))
def sample (body : Expr) : ConstantInfo := .opaqueInfo
  ⟨⟨Name.fromLeanName `LiteralSample, #[], Expr.mkSort (.mkSucc .mkZero)⟩,
    body, false, #[Name.fromLeanName `LiteralSample]⟩
private def agrees (e : Expr) : Bool := (Literal.scan Literal.empty e).bits == Literal.tree e

#guard (List.range 13).all fun d => agrees (dag d)
#guard (List.range 13).all fun d => (Literal.scan Literal.empty (dag d)).memo.entries.size == d + 1
private def repeated := dag 8
private def first := Literal.scan Literal.empty repeated
private def again := Literal.scan first.memo repeated
#guard first.bits == (false, false) && again.bits == first.bits
#guard again.memo.entries.size == first.memo.entries.size
#guard again.memo.entries.get? ⟨repeated⟩ == some (false, false)
#guard (Literal.scanTerms Literal.empty [repeated, repeated, repeated]).memo.entries.size == 9
#guard (Literal.scan Literal.empty (unshared 6 0)).memo.entries.size == 127
#guard agrees (unshared 6 0)

private def nat := Expr.mkLit (.natVal 7)
private def str := Expr.mkLit (.strVal "literal")
private def binder := Name.fromLeanName `x
private def branches : List Expr :=
  [Expr.mkApp nat str, Expr.mkLam binder nat str .default,
   Expr.mkForallE binder nat str .default, Expr.mkLetE binder nat leaf str false,
   Expr.mkMData #[] str, Expr.mkProj binder 0 nat,
   Expr.mkBVar 0, Expr.mkFVar binder, Expr.mkMVar binder,
   leaf, Expr.mkConst binder #[], nat, str]
#guard branches.all agrees
#guard (Literal.scan Literal.empty (Expr.mkApp nat str)).bits == (true, true)
#guard (branches.map sample).all fun ci => literalUseShared ci == literalUse ci
#guard literalUseShared (sample (Expr.mkApp nat str)) == .string
#guard literalUseShared (sample nat) == .nat
#guard literalUseShared (sample leaf) == .none

-- Equal digests never identify distinct literal nodes in the memo.
private def collision : Expr := .lit (.strVal "different") nat.getHash
private def natResult := Literal.scan Literal.empty nat
private def collisionResult := Literal.scan natResult.memo collision
#guard nat.getHash == collision.getHash && !_root_.Ix.Compile.ExactKey.exprEq nat collision
#guard collisionResult.bits == (true, false) && collisionResult.memo.entries.size == 2
#guard (Literal.scan collisionResult.memo nat).bits == (false, true)
#guard (Literal.scanTerms Literal.empty [nat, collision, nat]).bits == (true, true)

-- One memo spans type and all rule RHSs, including repeated shared roots.
private def recursor : ConstantInfo := .recInfo
  ⟨⟨binder, #[], repeated⟩, #[binder], 0, 0, 1, 0,
    #[⟨binder, 0, repeated⟩, ⟨binder, 0, repeated⟩], false, false⟩
#guard (Literal.scanTerms Literal.empty (terms recursor)).memo.entries.size == 9
#guard literalUseShared recursor == literalUse recursor
#guard (captureUsingShared (sample str) {}).literals == .string
#guard (rowUsingShared binder (sample str) {}).kept.isNone
#guard (rowUsingShared binder recursor {}).kept.isSome

/-- info: 'Ix.Compile.SourceGraph.Literal.scan_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Compile.SourceGraph.Literal.scan_correct
/-- info: 'Ix.Compile.SourceGraph.Literal.scan_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Compile.SourceGraph.Literal.scan_sound
/-- info: 'Ix.Compile.SourceGraph.Literal.scan_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Compile.SourceGraph.Literal.scan_extends
/-- info: 'Ix.Compile.SourceGraph.Literal.scan_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Compile.SourceGraph.Literal.scan_hit
/-- info: 'Ix.Compile.SourceGraph.Literal.scanTerms_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Compile.SourceGraph.Literal.scanTerms_correct
/-- info: 'Ix.Compile.SourceGraph.literalUseShared_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Compile.SourceGraph.literalUseShared_eq
/-- info: 'Ix.Compile.SourceGraph.captureUsingShared_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Compile.SourceGraph.captureUsingShared_eq
/-- info: 'Ix.Compile.SourceGraph.rowUsingShared_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms _root_.Ix.Compile.SourceGraph.rowUsingShared_eq

end Tests.Ix.Cert.SourceGraphLiteral
