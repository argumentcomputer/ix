import Ix.CompileCert.Opt.Basic
import Ix.CompileCert.Opt.Subst
import Ix.CompileCert.Opt.Shape
import Ix.CompileCert.Opt.Rec
import Ix.CompileCert.Opt.O1
import Ix.CompileCert.Opt.O6
import Ix.CompileCert.Opt.O3

/-!
# M7 L3-def: the definitional passes, proved once over the compiler's code

The definitional optimisation passes of Pass 3 (`Ix/Compile/Pass/Opt/{O1,…,O6,O11a}.lean`, design
document §1.5) replace an occurrence `a.{us} a₁ … a_m` of an image-kind auxiliary of a changed
block by an Ix auxiliary of Pass 2 applied to (a selection of) the same arguments. Each module's
docstring calls the pass *definitional* and lists its conversion steps. This package restates
each docstring as a theorem about the compiler's own function (unfolded; no copy), in X1's
conversion `Conv` on erased terms (`Ix.CompileCert.Conv`):

* **faithfulness**: `P.apply env o = some e → ExprConv Γ e (occTerm o)`, for every `Γ` that has
  the rules the docstring's conversion uses — the *laws* (`RecLaw`, `RecOnLaw`, `IxRecOnLaw`,
  `CasesOnLaw`, …: δ of the image-kind head to its image or to Lean's construction over images,
  δ of Pass 2's auxiliary to the same construction over the canonical recursor, the shape read
  off the image). Every law is a named hypothesis; who discharges it is in the laws ledger of
  `plans/review2/M7-L3-def.md` §2;
* **the side condition** `P.Side env o` (the docstring's list) and its necessity (`P_side`).

The theorems, by pass:

| pass | faithfulness | laws |
|---|---|---|
| O1 (`rec`/`recOn`, permuted block) | `O1_faithful` | `RecLaw`, `RecOnLaw`, `IxRecOnLaw` |
| O6 (`rec`/`recOn`, selection image) | `O6_faithful` | the same |
| O3 (`casesOn`, no collapse) | `O3_faithful` | `CasesOnLaw`, `Γ.InstClosed` |

The common part: `rec_sel_conv`, `recOn_sel_conv` (`Rec.lean`), `delta_sel`, `delta_beta` (δ then
β on a telescope, `Basic.lean`, `Subst.lean`), the β-reduct of a telescope as a simultaneous
substitution and its composition (`betaN_eq_msubst`, `betaN_betaN`, `Subst.lean`).
-/
