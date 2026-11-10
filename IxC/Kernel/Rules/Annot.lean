module

public import IxC.Kernel.CoreDefs

@[expose] public section

/-!
# The annotation pass, relationally (lane l5)

`annotateBody` (`Core.lean:2000`) as a relation: `Annot d e e'` says `e'` is an
annotation of `e` at depth `d`. The pass is structural except at three places,
which the relation leaves free: a binder's `pw` datum (the inference sweep
validates it, `Infer.forallE`/`Infer.lam`), a projection's structure name (the
pass normalizes it to the scrutinee type's head), and a `let`, which the pass
replaces by the annotation of its ζ-reduct. A binder's body is annotated opened,
at `.fvar d ty'` with the annotated domain, and closed again, as the pass does.

The relation describes only the shape of an annotation; what an annotated term
means is checked by inference on it. The model tier reads it through the
scoping it keeps (`Model/JudgeRules.lean`, `JudgeFrames`). It is the annotation
relation of the derivation package `rulesJ`.
-/

namespace Ix.Kernel.Rules

/-- **`e'` is an annotation of `e` at depth `d`** (`annotateBody`). -/
inductive Annot : Nat → Expr md → Expr md → Prop where
  | bvar {d i : Nat} : Annot d (.bvar i) (.bvar i)
  | fvar {d idx : Nat} {ty : Expr md} : idx < d → Annot d (.fvar idx ty) (.fvar idx ty)
  | sort {d : Nat} {u : Level} : Annot d (.sort u) (.sort u)
  | const {d : Nat} {n : Key md} {us : List Level} : Annot d (.const n us) (.const n us)
  | lit {d : Nat} {l : Literal} : Annot d (.lit l) (.lit l)
  | app {d : Nat} {f a f' a' : Expr md} :
      Annot d f f' → Annot d a a' → Annot d (.app f a) (.app f' a')
  | forallE {d : Nat} {ty body ty' body' : Expr md} {mb : BinderMeta} {pw : PropWhen} :
      Annot d ty ty' → Annot (d + 1) (body.instantiate1 (.fvar d ty')) body' →
      Annot d (.forallE ty body mb) (.forallE ty' (body'.abstract1 d) { mb with pw })
  | lam {d : Nat} {ty body ty' body' : Expr md} {mb : BinderMeta} {pw : PropWhen} :
      Annot d ty ty' → Annot (d + 1) (body.instantiate1 (.fvar d ty')) body' →
      Annot d (.lam ty body mb) (.lam ty' (body'.abstract1 d) { mb with pw })
  | proj {d : Nat} {sn T : Key md} {i : Nat} {e e' : Expr md} :
      Annot d e e' → Annot d (.proj sn i e) (.proj T i e')
  | letE {d : Nat} {ty v b e' : Expr md} {lm : LetMeta} :
      Annot d (b.instantiate1 v) e' → Annot d (.letE ty v b lm) e'

end Ix.Kernel.Rules
