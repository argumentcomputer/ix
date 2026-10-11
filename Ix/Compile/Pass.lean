/-
  Ix.Compile.Pass: Pass 3, the faithful rewrite (design document §4.5-4.6,
  decisions Q10, Q11), the default since the flip (M6, 2026-10-06) and the only mode since M6R
  slice 6 (2026-10-07), which deleted the legacy call-site surgery from both
  compilers.

  * `Names`: the reserved `_ix` names (D14), the decompile-record keys and
    the retired switch;
  * `Translate`: the call-site rewrite (Def 3.5, Def 3.6): inline at full
    applications by hereditary substitution, the image constant at bare and
    partial occurrences;
  * `ImageView`: the images of a changed block's recursors in the compiler
    (Pass 1's canonical form, Pass 2's recursors, the image generator);
  * `SideCar`: the `_ix` display names of the Ix auxiliaries and the
    metadata renaming;
  * `Cliques`: changed definition cliques through the clique transport
    (O13–O16): the members' transported values, the canonical constants,
    the scheduling edges;
  * `Driver`: the two hooks of the block compile.
-/
module
public import Ix.Compile.Pass.Names
public import Ix.Compile.Pass.Translate
public import Ix.Compile.Pass.ImageView
public import Ix.Compile.Pass.SideCar
public import Ix.Compile.Pass.Cliques
public import Ix.Compile.Pass.Driver
public import Ix.Compile.Pass.Opt.Engine
