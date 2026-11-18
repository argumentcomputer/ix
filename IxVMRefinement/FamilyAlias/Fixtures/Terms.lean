import IxVMRefinement.Core.Rep

/-! # Short forms for kernel terms written out as data

The fixtures of this directory list kernel constants as literal terms. These abbreviations keep
the listings short: levels (`lz`, `ls`, `lmx`, `lim`, `lp`), the zero-ness datum of a binder
(`pN`, `pZ`), terms (`bv`, `st`, `cn`, `ap`, `lm`, `pi`), a constant's signature (`cv`) and an
address from its bytes (`adr`). A binder's display data is the default one. -/

namespace IxVM.Refinement.Decl.FamilyAlias.Fixtures

open IxVM.Refinement.Core
open Ix.Kernel (Expr Key Level ConstantVal BinderMeta PropWhen LevelParam)

abbrev lz : KLevel := .zero
abbrev ls (u : KLevel) : KLevel := .succ u
abbrev lmx (a b : KLevel) : KLevel := .max a b
abbrev lim (a b : KLevel) : KLevel := .imax a b
abbrev lp (p : LevelParam) : KLevel := .param p

abbrev pN : PropWhen := .never
abbrev pZ (ps : List LevelParam) : PropWhen := .ifAllZero ps

abbrev bv (i : Nat) : KExpr := .bvar i
abbrev st (u : KLevel) : KExpr := .sort u
abbrev cn (k : KKey) (us : List KLevel) : KExpr := .const k us
abbrev ap (f a : KExpr) : KExpr := .app f a
abbrev lm (pw : PropWhen) (ty b : KExpr) : KExpr := .lam ty b { pw := pw }
abbrev pi (pw : PropWhen) (ty b : KExpr) : KExpr := .forallE ty b { pw := pw }

abbrev cv (k : KKey) (lps : List LevelParam) (ty : KExpr) : ConstantVal .anon := ⟨k, lps, ty⟩

/-- An address from its bytes. -/
def adr (bs : List UInt8) : _root_.Address := ⟨⟨bs.toArray⟩⟩

end IxVM.Refinement.Decl.FamilyAlias.Fixtures
