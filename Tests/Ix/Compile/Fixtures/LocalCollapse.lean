/- Fixture of `compile-closure-whole`'s local-scope leg, elaborated at run time and in no Lake
library: an alpha-collapsed mutual Prop block (`PA`/`PB` have the same shape), and one in `Type`,
each with a user of its recursor. With the switch on, Pass 3's images of a changed Prop block are
packed with `And`/`True`, of a Type block with `PProd`/`PUnit`, constants these declarations'
own closure need not contain: the `--local` closure must carry them (the compiler's introduced
references, `Ix.EnvScope.introducedSupport`). -/
set_option Elab.async false

namespace LocalCollapse

mutual
inductive PA : Prop
  | a : PB → PA
  | z : PA
inductive PB : Prop
  | b : PA → PB
  | z : PB
end

theorem PA.toB (h : PA) : PB :=
  @PA.rec (fun _ => PB) (fun _ => PA) (fun _ ih => .b ih) .z (fun _ ih => .a ih) .z h

mutual
inductive TA
  | a : TB → TA
  | z : TA
inductive TB
  | b : TA → TB
  | z : TB
end

noncomputable def TA.depth (x : TA) : Nat :=
  @TA.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) 0 x

end LocalCollapse
