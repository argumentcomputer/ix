/-
  Level-spelling fixtures (canonicity §10.6, stage 1).

  Constants whose stored universe-level spellings are NOT `mk*`-normal —
  one per kernel-rebuild rule M1–M7/I1–I5 — plus spelling twins inside a
  single constant (the Design-A killer), const-arg twins, Géran
  order/association twins (mk*-normal but non-canonical; stage-2
  relevant), and a WF-recursive definition whose `.eq_def` machinery
  flows through unary packing.

  Everything weird is declared via raw `addDecl` with explicit `Level`
  literals so the unnormalized spelling deterministically reaches the
  environment — surface-syntax level expressions may normalize during
  elaboration. The kernel typechecks every declaration (no
  `skipKernelTC`): it normalizes levels for CHECKING but stores the
  declaration's expressions as given, which is exactly the Mathlib
  WF-eq_def situation these fixtures reproduce.

  Consumed by: `validateAuxClosure` (validate-aux / aux-gen-diff /
  decompile-diff), and — via the Tests binary env — the whole-env
  tc-roundtrip and kernel-ixon-roundtrip suites, where the stage-1
  spelling decorations (Lean `Ix.Tc` + Rust kernel) are load-bearing.

  Import note: `Lean.Elab.BuiltinEvalCommand` (the `run_cmd` elab), NOT
  all of `Lean` — the roundtrip suites' envs are this file's module
  closure, and importing the whole Lean package would grow their corpus
  by ~40k internals (`Lean.Meta.Grind.*`, …) unrelated to level
  spellings.
-/
import Lean.Elab.BuiltinEvalCommand

namespace Tests.Ix.Compile.LevelSpellings

open Lean

run_cmd Elab.Command.liftCoreM do
  let u : Level := .param `u
  let v : Level := .param `v
  let w : Level := .param `w
  let l0 : Level := .zero
  let l1 : Level := .succ .zero
  let l2 : Level := .succ l1
  -- `imax (imax 1 u) u` — the Mathlib WF eq_def shape (I4 then I5 → u).
  let weird : Level := .imax (.imax l1 u) u
  let ax (name : Name) (levelParams : List Name) (type : Expr) :
      CoreM Unit :=
    addDecl <| .axiomDecl { name, levelParams, type, isUnsafe := false }
  let n (s : String) : Name := `Tests.Ix.Compile.LevelSpellings ++ .mkSimple s
  -- One reducible spelling per kernel mk* rule, in Sort position.
  ax (n "levelM1") [] (.sort (.max l1 l2))                    -- numerals
  ax (n "levelM2") [`u] (.sort (.max u u))                    -- max u u
  ax (n "levelM3") [`u] (.sort (.max l0 u))                   -- max 0 u
  ax (n "levelM4") [`u] (.sort (.max u l0))                   -- max u 0
  ax (n "levelM5") [`u, `v] (.sort (.max u (.max u v)))       -- absorption R
  ax (n "levelM6") [`u, `v] (.sort (.max (.max u v) v))       -- absorption L
  ax (n "levelM7") [`u] (.sort (.max (.succ u) (.succ (.succ u)))) -- offsets
  ax (n "levelI1") [`u, `v] (.sort (.imax u (.succ v)))       -- neverZero
  ax (n "levelI2") [`u] (.sort (.imax u l0))                  -- imax u 0
  ax (n "levelI3") [`u] (.sort (.imax l0 u))                  -- imax 0 u
  ax (n "levelI4") [`u] (.sort (.imax l1 u))                  -- imax 1 u
  ax (n "levelI5") [`u] (.sort (.imax u u))                   -- imax u u
  -- The exact Mathlib finding shape.
  ax (n "eqDefShape") [`u] (.sort weird)
  -- Design-A killer: BOTH spellings of one Géran class in one constant.
  ax (n "designAKiller") [`u]
    (.forallE `x (.sort weird) (.sort u) .default)
  -- Const-arg twins at type level: PUnit.{weird} → PUnit.{u}.
  ax (n "punitTwin") [`u]
    (.forallE `x (.const `PUnit [weird]) (.const `PUnit [u]) .default)
  -- Géran order/association twins: mk*-normal today (no decoration,
  -- byte-faithful roundtrip), address-convergent after stage 2.
  ax (n "orderMaxUV") [`u, `v] (.sort (.max u v))
  ax (n "orderMaxVU") [`u, `v] (.sort (.max v u))
  ax (n "orderAssocL") [`u, `v, `w] (.sort (.max (.max u v) w))
  ax (n "orderAssocR") [`u, `v, `w] (.sort (.max u (.max v w)))
  -- Const-arg twins in VALUE position (defn):
  -- constArgTwin.{u} : ∀ (α : Sort u), α → α
  --   := fun α a => @id.{imax (imax 1 u) u} α (@id.{u} α a)
  addDecl <| .defnDecl {
    name := n "constArgTwin"
    levelParams := [`u]
    type := .forallE `α (.sort u)
      (.forallE `a (.bvar 0) (.bvar 1) .default) .default
    value := .lam `α (.sort u)
      (.lam `a (.bvar 0)
        (mkApp2 (.const `id [weird]) (.bvar 1)
          (mkApp2 (.const `id [u]) (.bvar 1) (.bvar 0)))
        .default)
      .default
    hints := .abbrev
    safety := .safe }

/-- WF-recursive two-argument definition: forces unary `PSigma` packing
    and the `WellFounded.fix` machinery through the compile pipeline. -/
def wfTwo : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, n => wfTwo m n
termination_by m _ => m

/-- Forces realization (and env persistence) of `wfTwo.eq_def`, the
    constant class where Lean's metaprograms store unnormalized level
    spellings at Mathlib scale. -/
def wfTwoEqDef := @wfTwo.eq_def

end Tests.Ix.Compile.LevelSpellings
