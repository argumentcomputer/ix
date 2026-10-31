/- Fixture of `compile-closure-whole`'s local-scope check, elaborated at run
time outside the Lake libraries: symmetric mutual members in `Prop` and in
`Type`, each with a user of its recursor. Every member keeps its own slot and
Lean's original recursor interface. The runner checks source reconstruction,
complete source/reader coverage, and that compilation introduces no references;
the closure with recursors alone must also compile without added support. -/
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
