/-
  Ix.Compile.Image: the image generator of Pass 3 (design document §4,
  `docs/compiler-passes.md`; decisions Q10, Q11) as total pure functions.

  For a Lean recursor `r` of a changed block, `imageOf` builds `img(r)`, a
  closed term over the canonical blocks' recursors whose type is
  `tr_N(type r)`, already developed, together with the statements of `r`'s
  computation rules over it (each holds by `rfl`) and its call-site forms
  (`Image.inline` at full applications, the image constant as the eta adapter
  of bare and partial occurrences).

  * `Expr`: locally nameless toolkit over `Ix.Expr` (fresh variables in
    `GenM`, telescopes, α-equality, Lean's `eta`, occurrence orders);
  * `Develop`: hereditary substitution (β, projection, η at the substituted
    positions; never ι);
  * `Spec`: from `Ix.Compile.Canon.BlockCanon` to the canonical inductive
    declarations and the renaming `tr_N`;
  * `Build`: eliminator choice, slot classes, levels, packing, minors with
    relocated hypotheses, the image and its rule statements.

  Not imported by the compiler (A3 wires it in after A2's migration). No
  `MetaM`, no kernel, no `partial`.
-/
module
public import Ix.Compile.Image.Expr
public import Ix.Compile.Image.Develop
public import Ix.Compile.Image.Spec
public import Ix.Compile.Image.Build
