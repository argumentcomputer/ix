/-
  Ix.Compile.Pass: Pass 3 of the compiler (images of a changed block's
  auxiliaries, and the faithful rewrite of their callers).

  * `Names`: the reserved `_ix` names, the display names of a changed block's
    Ix auxiliaries, the image kinds;
  * `Memo`: the memo tables' one shape;
  * `Translate`: the call-site rewrite (`_ix.inline` placeholders);
  * `ImageView`: images of a changed block in the compiler;
  * `SideCar`: the side-car edit of a changed block's registrations;
  * `Driver`: the hooks of the block compile and the image blocks.
-/
module
public import Ix.Compile.Pass.Names
public import Ix.Compile.Pass.Memo
public import Ix.Compile.Pass.Translate
public import Ix.Compile.Pass.ImageView
public import Ix.Compile.Pass.SideCar
public import Ix.Compile.Pass.Driver
