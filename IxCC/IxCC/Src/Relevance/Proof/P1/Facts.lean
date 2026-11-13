import IxCC.Src.Relevance.Proof.P1.Defs
import IxCC.Src.Relevance.Proof.ModeEq

/-! # P1: L1's facts on the program SrcEval runs

The relevance checks run on the installed program; SrcEval runs its Lazify image, which differs only
in application modes (`Lazify.run_modeEq`). The checks do not read modes (`Proof.ModeEq`:
`check_modeEq`), and `Canonical` transports along modes (`canonical_modeEq`), so L1 (`check_soundC`,
`checkCanonical_sound`) gives `Facts` of the image. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open Proof.ModeEq

/-- Lazify changes only application modes, which no check reads: the facts L1 gives of the checked
program hold of every program equal to it up to modes. -/
theorem facts_modeEq {p₀ p : Program} {ann : Ann} {ch : Checked}
    (hc : check p₀ ann = .ok ch) (hk : checkCanonical p₀ ann ch = []) (hme : Program.ModeEq p₀ p) :
    Facts p ann ch :=
  have hc' : check p ann = .ok ch := (check_modeEq hme ann).symm.trans hc
  ⟨check_soundC hc', canonical_modeEq hme (checkCanonical_sound hk), check_reached hc'⟩

end IxCC.Src.Relevance.Proof.P1
