import IxCCCorrect.Claim
import IxCCCorrect.Process
import IxCCCorrect.Tiers
import IxCCCorrect.Routes
import IxCCCorrect.Today

/-!
# `IxCCCorrect`: the target statements of IxCC

What a compiled executable's argument has to establish, written as Lean
propositions that elaborate, and what the existing theorems establish today.

* `IxCCCorrect.Claim`: the public claim (`Claim`), its ABI and its binding to a
  shipped file (`Claim.Binds`).
* `IxCCCorrect.Process`: the process of a shipped file over the existing
  processor and system-call specifications (`LoadedFile`, `execImage`), and what a
  trace shows (`stdout`, `exitStatus`, `SysAllowed`, `Kept`, `Ended`).
* `IxCCCorrect.Tiers`: kernel meaning (`Admits`, `Agrees`), the three tiers
  (`Tier1`, `Tier2`, `Tier3`) and `Correct`.
* `IxCCCorrect.Routes`: the certified and the certifying route as statements
  (`CertifiedRoute`, `CertifyingRoute`).
* `IxCCCorrect.Today`: `CorrectToday`, and the proof that today's verifier
  establishes it (`correctToday_of_accepts`).

The tiers and the routes are definitions: nothing here proves them. The library
imports the compiler (`IxCC`), the grounding library's syntax (`IxCCGrounding`) and
the kernel's model statement (`IxCK.Kernel.Denotes`), so it is outside the
production import root (`IxCC` must not import the grounding library or the
kernel's model, `IxCC.Tools.BuildGraph`).
-/
