/-
  Ix.Compile.Pass: Pass 3, the faithful rewrite (design document §4.5-4.6,
  decisions Q10, Q11), selected by `IX_PASS3=images` and off by default.

  * `Names`: the reserved `_ix` names (D14), the decompile-record keys and
    the switch;
  * `Translate`: the call-site rewrite (Def 3.5, Def 3.6): inline at full
    applications by hereditary substitution, the image constant at bare and
    partial occurrences;
  * `ImageView`: the images of a changed block's recursors in the compiler
    (Pass 1's canonical form, Pass 2's recursors, the image generator);
  * `SideCar`: the `_ix` display names of the Ix auxiliaries and the
    metadata renaming;
  * `Driver`: the two hooks of the block compile.
-/
module
public import Ix.Compile.Pass.Names
public import Ix.Compile.Pass.Translate
public import Ix.Compile.Pass.ImageView
public import Ix.Compile.Pass.SideCar
public import Ix.Compile.Pass.Driver
