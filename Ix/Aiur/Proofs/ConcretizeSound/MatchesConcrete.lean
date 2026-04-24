module
public import Ix.Aiur.Proofs.ConcretizeSound

/-!
`Source.Typ.MatchesConcreteFM` + `Source.Decls.DeclsAgreeOnDtFM`.

Hoisted upstream of `Layout.lean` (2026-05-04) so the per-`Typ`-pair sibling
lemma needed for the `dataTypeFlatSize`-vs-`typLevel` Layout-chain induction
core can consume `MatchesConcreteFM` without crossing the
`Layout → Shapes → CtorKind → Phase4 → RefClosed` import boundary.

Previously lived in `ConcretizeSound/RefClosed.lean`.
-/

public section

namespace Aiur

open Source

/-! #### Phase C scaffolding (F=0): per-`Typ` flat-size correspondence.

The dataType-level theorem `concretize_under_fullymono_dt_flat_size_agree`
factors through a per-`Typ` correspondence: for any source `Typ` and the
`Concrete.Typ` it concretizes to (via `typToConcrete ∘ rewriteTyp emptySubst
drained.mono`, which under `FullyMonomorphic` collapses since args = #[]),
`typFlatSize decls {} ty = Concrete.typFlatSize concDecls {} cty`.

`Typ.MatchesConcreteFM` is an inductive relation capturing the structural
shape produced by the FullyMono-reduced concretize composition. Under
FullyMono args = #[] always, so `.app g #[]` collapses to `.ref g` (since
`concretizeName g #[] = g`, both `rewriteTyp` and `typToConcrete` produce
`.ref g`).

`Source.Decls.DeclsAgreeOnDtFM` captures decls-level data-type agreement: for
any `g` with `.dataType` on both sides, constructor lists have the same
length and each positional argType is related by `MatchesConcreteFM`. -/

/-- Structural relation between source `Typ` and `Concrete.Typ` capturing the
post-`concretize` shape under `FullyMonomorphic`. Under FullyMono args = #[]
always, so `.app` collapses to `.ref`. -/
inductive Typ.MatchesConcreteFM : Typ → Concrete.Typ → Prop
  | unit : MatchesConcreteFM .unit .unit
  | field : MatchesConcreteFM .field .field
  | pointer {t : Typ} {ct : Concrete.Typ} :
      MatchesConcreteFM t ct → MatchesConcreteFM (.pointer t) (.pointer ct)
  | tuple {ts : Array Typ} {cts : Array Concrete.Typ} :
      ts.size = cts.size →
      (∀ i (h₁ : i < ts.size) (h₂ : i < cts.size),
        MatchesConcreteFM (ts[i]'h₁) (cts[i]'h₂)) →
      MatchesConcreteFM (.tuple ts) (.tuple cts)
  | array {t : Typ} {ct : Concrete.Typ} {n : Nat} :
      MatchesConcreteFM t ct →
      MatchesConcreteFM (.array t n) (.array ct n)
  /-- Source `.ref g` maps to concrete `.ref g`. -/
  | ref {g : Global} : MatchesConcreteFM (.ref g) (.ref g)
  /-- Source `.app g #[]` collapses to concrete `.ref g` under FullyMono. -/
  | appEmpty {g : Global} : MatchesConcreteFM (.app g #[]) (.ref g)
  /-- Source `.app g args` collapses to concrete `.ref concName` when the
  monomorphisation map resolves `(g, args)`. The size-agreement evidence
  is supplied separately by downstream consumers (which consult layoutMap +
  source decls to extract the dataType-level identity). -/
  | appResolved {g : Global} {args : Array Typ} {concName : Global} :
      MatchesConcreteFM (.app g args) (.ref concName)
  /-- Source `.app g args` falls through to concrete `.ref g` (template name)
  when the monomorphisation map does NOT resolve `(g, args)`. The args are
  recursively rewritten but `typToConcrete ∅` ignores them and returns
  `.ref g`. -/
  | appUnresolved {g : Global} {args : Array Typ} :
      MatchesConcreteFM (.app g args) (.ref g)
  | function {ins : List Typ} {out : Typ}
      {cins : List Concrete.Typ} {cout : Concrete.Typ} :
      ins.length = cins.length →
      (∀ i (h₁ : i < ins.length) (h₂ : i < cins.length),
        MatchesConcreteFM (ins[i]'h₁) (cins[i]'h₂)) →
      MatchesConcreteFM out cout →
      MatchesConcreteFM (.function ins out) (.function cins cout)

/-- Decls-level agreement under FullyMono: for any `g` that resolves to a
`.dataType` on both sides, the constructor lists match positionally with each
arg-type pair related by `MatchesConcreteFM`. Captures the structural fact
established by `concretize_under_fullymono_preserves_dataType_kind_fwd` +
positional ctor correspondence (Phase A.2/A.3 + Phase B). -/
abbrev Source.Decls.DeclsAgreeOnDtFM
    (decls : Source.Decls) (concDecls : Concrete.Decls) : Prop :=
  ∀ (g : Global) (src_dt : DataType) (cd_dt : Concrete.DataType),
    decls.getByKey g = some (.dataType src_dt) →
    concDecls.getByKey g = some (.dataType cd_dt) →
    src_dt.constructors.length = cd_dt.constructors.length ∧
    (∀ i (h₁ : i < src_dt.constructors.length)
       (h₂ : i < cd_dt.constructors.length),
      let src_c := src_dt.constructors[i]'h₁
      let cd_c := cd_dt.constructors[i]'h₂
      src_c.argTypes.length = cd_c.argTypes.length ∧
      ∀ j (hj₁ : j < src_c.argTypes.length) (hj₂ : j < cd_c.argTypes.length),
        Typ.MatchesConcreteFM (src_c.argTypes[j]'hj₁)
                              (cd_c.argTypes[j]'hj₂))

end Aiur
