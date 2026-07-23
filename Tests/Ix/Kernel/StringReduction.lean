/-
  String-value reduction tests for the Rust kernel's native string
  fast paths (evaluator-grade whnf).

  Mirrors `Tests.Ix.Kernel.NatReduction`: hand-built `Lean.Declaration`
  values over raw literals, so the fixtures exercise the kernel's
  `try_reduce_string` shapes directly — the same shapes downstream
  metered evaluation drives:

    A. `String.append` on literals → concatenated literal
    B. `String.ofList`/`String.mk` on literal char lists → `Str` literal
       (the inverse of `str_lit_to_constructor`; "constructor-built
       string" acceptance shape)
    C. `String.utf8ByteSize` on literals (pre-existing native path)
    D. `decide (s₁ = s₂)` through `String.decEq` on equal literals
       (native `Decidable.isTrue` + `Decidable.decide` iota)
    E. Negative decls guarding over-reduction

  Without the native rules, the A/B shapes reduce structurally through
  the ByteArray/UTF-8 model — measured at 10⁷ rec-fuel ticks for a
  two-char constructor tree and > 4×10⁹ for a six-char append — so
  these fixtures double as wall-clock regression guards: a revert makes
  `kernel-tutorial`/`kernel-check-env` hang rather than merely fail.
-/
import Tests.Ix.Kernel.TutorialMeta

set_option linter.unusedVariables false

open Tests.Ix.Kernel.TutorialMeta

namespace Tests.Ix.Kernel.StringReduction

/-! ## Helpers — raw declaration builders -/

private def strLit (s : String) : Lean.Expr := .lit (.strVal s)

private def charOfNat (n : Nat) : Lean.Expr :=
  Lean.mkApp (Lean.mkConst ``Char.ofNat) (.lit (.natVal n))

/-- `[Char.ofNat c₁, …]` as raw `List.cons.{0} Char …` chains — the
    exact shape `str_lit_to_constructor` builds and elaborated char
    lists take. -/
private def charListLit (s : String) : Lean.Expr := Id.run do
  let charTy := Lean.mkConst ``Char
  let mut list := Lean.mkApp (Lean.mkConst ``List.nil [.zero]) charTy
  for c in s.toList.reverse do
    list := Lean.mkApp3 (Lean.mkConst ``List.cons [.zero]) charTy
      (charOfNat c.toNat) list
  return list

/-- `lhs = rhs` over `α`, proved by `Eq.refl α rhs`. -/
private def eqThm (name : Lean.Name) (α lhs rhs : Lean.Expr) : Lean.Declaration :=
  .thmDecl {
    name
    levelParams := []
    type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) α lhs rhs
    value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) α rhs
  }

private def strAppend (a b : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (Lean.mkConst ``String.append) a b

private def strThm (name : Lean.Name) (lhs : Lean.Expr) (r : String) : Lean.Declaration :=
  eqThm name (Lean.mkConst ``String) lhs (strLit r)

/-! ## A. `String.append` on literals -/

good_decl (strThm `strAppendSmall (strAppend (strLit "hello") (strLit "!")) "hello!")
good_decl (strThm `strAppendEmptyLeft (strAppend (strLit "") (strLit "x")) "x")
good_decl (strThm `strAppendEmptyRight (strAppend (strLit "x") (strLit "")) "x")
good_decl (strThm `strAppendBothEmpty (strAppend (strLit "") (strLit "")) "")
good_decl (strThm `strAppendUnicode (strAppend (strLit "L∃") (strLit "∀N")) "L∃∀N")
good_decl (strThm `strAppendChain
  (strAppend (strAppend (strLit "a") (strLit "b")) (strLit "c")) "abc")

/-! ## B. Constructor-built strings collapse to literals -/

-- NOTE: a `String.mk`-headed twin of `strOfListBanner` would compile to
-- the SAME anon constant — `String.mk` and `String.ofList` share one
-- canonical content address (see primitive.rs
-- `prim_addrs_new_string_mk_and_of_list_are_intentionally_aliased`) and
-- anon compilation erases the theorem name — so the pipeline dedups it
-- away. `strOfListBanner` therefore covers both spellings.
good_decl (strThm `strOfListBanner
  (Lean.mkApp (Lean.mkConst ``String.ofList) (charListLit "ok")) "ok")
good_decl (strThm `strOfListEmpty
  (Lean.mkApp (Lean.mkConst ``String.ofList) (charListLit "")) "")
good_decl (strThm `strOfListUnicode
  (Lean.mkApp (Lean.mkConst ``String.ofList) (charListLit "L∃∀N")) "L∃∀N")

/-! ## C. `String.utf8ByteSize` on literals (pre-existing native path) -/

good_decl (eqThm `strUtf8ByteSize (Lean.mkConst ``Nat)
  (Lean.mkApp (Lean.mkConst ``String.utf8ByteSize) (strLit "hello!"))
  (.lit (.natVal 6)))
good_decl (eqThm `strUtf8ByteSizeUnicode (Lean.mkConst ``Nat)
  (Lean.mkApp (Lean.mkConst ``String.utf8ByteSize) (strLit "L∃∀N"))
  (.lit (.natVal 8)))

/-! ## D. `decide (s₁ = s₂)` through the native `String.decEq` isTrue -/

private def strEqProp (a b : Lean.Expr) : Lean.Expr :=
  Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``String) a b

private def strDecide (a b : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (Lean.mkConst ``Decidable.decide) (strEqProp a b)
    (Lean.mkApp2 (Lean.mkConst ``String.decEq) a b)

good_decl (eqThm `strDecideEqTrue (Lean.mkConst ``Bool)
  (strDecide (strLit "ok") (strLit "ok")) (Lean.mkConst ``Bool.true))

/-! ## E. Negative decls — over-reduction guards. These must be
    REJECTED, and rejected fast (both sides land on distinct `Str`
    literals). -/

bad_decl (strThm `strAppendWrong (strAppend (strLit "a") (strLit "b")) "ba")
bad_decl (strThm `strOfListWrong
  (Lean.mkApp (Lean.mkConst ``String.ofList) (charListLit "ok")) "ko")
bad_decl (eqThm `strUtf8ByteSizeWrong (Lean.mkConst ``Nat)
  (Lean.mkApp (Lean.mkConst ``String.utf8ByteSize) (strLit "hi"))
  (.lit (.natVal 3)))

end Tests.Ix.Kernel.StringReduction
