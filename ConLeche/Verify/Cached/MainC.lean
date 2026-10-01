module

public import ConLeche.Verify.Cached.InstalledC
public section

/-!
# The capstone letters of the fold `checkDecls`

`checkDecls` (`ConLeche/Cached/Installed.lean`) is the declaration fold
the binary runs — install every record, then check every recorded
declaration — and the subject of the main theorem
(`ConLeche.model_exists`, `ConLeche/MainTheorem.lean`).  Its letters
are the letters on the fully checked environment the driver assembles
(`ConLeche/Verify/Cached/InstalledC.lean`) read through
`checkDecls_fullyChecked`: an accept of the fold IS a fully checked
environment, and a fully checked environment carries the graded model
(`fullyChecked_sound`), so no constant of type `False` (or `Empty`) is
stored in what the fold accepts.

**At every pin list** (task #304): the fold's pin-list parameter is
free in all three letters below (`checkDecls μ pins ds`), because
nothing the model tier consumes reads which list the matched
`Nat.div`/`Nat.mod` variant came from.  The shipped binary's
statements are these at `pins := natOpPinSets`.

Retired at task #172 with the arena they were fed from: the
`checkDecls` letters (`SPC_*` and `input_SPC_*`), which took a
`WFStore` and a `List DeclP` and converted once before folding.

Retired at the SetR removal (2026-09-05) **with their subjects**: the
collapsed-lane letters `no_proof_of_Empty_SPCD_{R,R2,R2M}`, their
acceptance corollaries and the folds `foldSPC_{R,R2,R2M}`.  Every one
of them was stated over an `EnvS`/`EnvModelU`/`EnvModelUM` carrier, and those
carriers were the `ConLeche/SetR/*` tier — the B4 measurement having
shown a zero acceptance delta between the two verified configurations,
the P letter is the whole story.  This module used to be the only one
allowed to see both lanes; there is one lane.
-/

namespace ConLeche.Cached

open ConLeche ConLeche.Semantics SetTheory ConLeche.SetModel
open ConLeche.Model (EnvModelM no_constant_of_Empty no_constant_of_False)

universe w
variable {V : Type w} [SetTheory V] {μ : CheckMode}
variable {pins : List NatOpPinSet}

/-- **Acceptance**: what the fold accepts carries the model. -/
theorem checkDecls_sound (hμ : μ.verifiedChecks = true)
    {ds : Array Declaration} {env' : Env}
    (h : checkDecls μ pins ds = .ok env') :
    Nonempty (EnvModelM V μ env') := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked μ h
  exact fullyChecked_sound V hμ fc

/-- **The fold's letter about `Empty`**: the checker, running a
validating mode, never accepts a stream in which some stored constant
has type `Empty`.  Hypotheses are input-level only. -/
theorem no_proof_of_Empty_cached (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    {ds : Array Declaration} {env' : Env}
    (h : checkDecls μ pins ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := checkDecls_sound (V := V) hμ h
  exact fun c hc hty => no_constant_of_Empty mp c hc hty

/-- **The fold's letter about `False`** (task #181): the same letter at
the pinned `False` block — no hypothesis about how the stream declared
`False`.  The step the main corollary rests on is this at `.verified`. -/
theorem no_proof_of_False_cached (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    {ds : Array Declaration} {env' : Env}
    (h : checkDecls μ pins ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := checkDecls_sound (V := V) hμ h
  exact fun c hc hty => no_constant_of_False mp c hc hty

end ConLeche.Cached
