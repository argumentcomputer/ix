module

public import LSpec
public import Ix.AuxGen.LevelEgress

/-! The complete 1200-level expectations are checked by LevelReference.
This module retains the exact input corpus, range refusal and every branch
spot check; only the retired Tc twin is removed. -/

public section

namespace Tests.AuxGen.LevelEgress

open LSpec
open Ix.AuxGen
open Ix.AuxGen.Egress
open Ix.Compile.ExactKey (levelEq)
open Ix (Name Level)

private def nm (s : String) : Name := Name.mkStr .mkAnon s
private def lps : Array Name := #[nm "u", nm "v"]

/-! ## The family of IxC levels -/

/-- The levels whose atoms are `0`, `param 0`, `param 1`, built by one more
layer of `succ`, `max` and `imax` over the levels of the layer below. -/
private def layer (below : List Ix.Kernel.Level) : List Ix.Kernel.Level :=
  below ++ below.map .succ ++
    below.flatMap (fun a => below.map (.max a)) ++ below.flatMap (fun a => below.map (.imax a))

private def kernelLevels : List Ix.Kernel.Level :=
  layer (layer [.zero, .param 0, .param 1])

/-- The same family as Lean levels over the names `u`, `v`, built raw. -/
private def toLean : Ix.Kernel.Level → Level
  | .zero => Level.mkZero
  | .succ u => Level.mkSucc (toLean u)
  | .max u v => Level.mkMax (toLean u) (toLean v)
  | .imax u v => Level.mkIMax (toLean u) (toLean v)
  | .param i => Level.mkParam (lps[i]?.getD (nm "_"))

/-! ## Refusal and spot checks -/

private def refusesOutOfRange : Bool :=
  match egressLevel lps (.max (.param 0) (.param 2)) with
  | .error (.levelParamIndex 2) => true
  | _ => false

private def u : Level := Level.mkParam (nm "u")
private def v : Level := Level.mkParam (nm "v")
private def one : Level := Level.mkSucc Level.mkZero
private def two : Level := Level.mkSucc one

private def spots : Bool :=
  -- both numerals: the larger
  levelEq (tcMax one two) two
    -- `max a a`, zero on either side
    && levelEq (tcMax u u) u && levelEq (tcMax Level.mkZero u) u && levelEq (tcMax u Level.mkZero) u
    -- absorption
    && levelEq (tcMax u (Level.mkMax u v)) (Level.mkMax u v)
    && levelEq (tcMax (Level.mkMax v u) u) (Level.mkMax v u)
    -- same base, the larger offset
    && levelEq (tcMax (Level.mkSucc u) u) (Level.mkSucc u)
    -- raw otherwise
    && levelEq (tcMax u v) (Level.mkMax u v)
    -- `imax` with a never-zero right side is `max`
    && levelEq (tcIMax u (Level.mkMax one v)) (tcMax u (Level.mkMax one v))
    -- `imax a 0 = 0`, `imax 0 b = b`, `imax 1 b = b`, `imax a a = a`
    && levelEq (tcIMax u Level.mkZero) Level.mkZero && levelEq (tcIMax Level.mkZero v) v
    && levelEq (tcIMax one v) v && levelEq (tcIMax v v) v
    && levelEq (tcIMax u v) (Level.mkIMax u v)

def suite : List TestSeq := [
  test "LevelEgress: actual input corpus has 1200 positions" (kernelLevels.length == 1200)
  ++ test "LevelEgress: a parameter beyond the scope is refused" refusesOutOfRange
  ++ test "LevelEgress: the smart constructors' branches" spots
]

end Tests.AuxGen.LevelEgress
