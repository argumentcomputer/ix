import Ix.CompileM

/-! # Running the compiler monad, for proofs

`rawRun` runs a `CompileM` action from a block state and returns its outcome
together with the final state, which the monad keeps on errors too.
`Preserves p action` says that the action leaves the projection `p` of the
block state unchanged on every run, failing ones included. These are the
frame facts of the universe proofs; they hold for the compiler's actual
functions, not copies. -/

namespace Ix.CompileCert

open Ix.CompileM

/-- One run of a compiler action: its outcome and the final block state. -/
def rawRun (action : CompileM α) (context : CompileEnv × BlockEnv) (state : BlockState) :
    Except CompileError α × BlockState := (action context).run state

theorem rawRun_bind (action : CompileM α) (next : α → CompileM β)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (action >>= next) context state =
      match rawRun action context state with
      | (.ok value, after) => rawRun (next value) context after
      | (.error error, after) => (.error error, after) := by
  rcases result : (action context).run state with ⟨outcome, after⟩
  change action context state = (outcome, after) at result
  cases outcome <;>
    simp [rawRun, ExceptT.run, ExceptT.mk, bind, ReaderT.bind, ExceptT.bind, StateT.bind,
      ExceptT.bindCont, pure, StateT.pure, result]

theorem rawRun_pure (value : α) (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (pure value) context state = (.ok value, state) := rfl

theorem rawRun_read (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun getCompileEnv context state = (.ok context.1, state) := rfl

theorem rawRun_readBlock (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun getBlockEnv context state = (.ok context.2, state) := rfl

theorem rawRun_get (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun getBlockState context state = (.ok state, state) := rfl

theorem rawRun_modify (update : BlockState → BlockState)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (modifyBlockState update) context state = (.ok (), update state) := rfl

/-- The action keeps the projection `projection` of the block state, on
every run. -/
def Preserves (projection : BlockState → α) (action : CompileM β) : Prop :=
  ∀ context before, projection (rawRun action context before).2 = projection before

theorem Preserves.pure (projection : BlockState → α) (value : β) : Preserves projection (pure value) := by
  intro context before; rfl

theorem Preserves.throw (projection : BlockState → α) (error : CompileError) :
    Preserves projection (throw error : CompileM β) := by intro context before; rfl

theorem Preserves.get (projection : BlockState → α) : Preserves projection getBlockState := by
  intro context before; rfl

theorem Preserves.read (projection : BlockState → α) : Preserves projection getBlockEnv := by
  intro context before; rfl

theorem Preserves.modify (projection : BlockState → α) (update : BlockState → BlockState)
    (unchanged : ∀ before, projection (update before) = projection before) :
    Preserves projection (modifyBlockState update) := by intro context before; exact unchanged before

theorem Preserves.bind {projection : BlockState → α} {action : CompileM β} {next : β → CompileM γ}
    (first : Preserves projection action) (later : ∀ value, Preserves projection (next value)) :
    Preserves projection (action >>= next) := by
  intro context before
  rw [rawRun_bind]
  have prior := first context before
  cases ran : rawRun action context before with
  | mk outcome after =>
    rw [ran] at prior
    cases outcome with
    | error error => exact prior
    | ok value => exact (later value context after).trans prior

end Ix.CompileCert
