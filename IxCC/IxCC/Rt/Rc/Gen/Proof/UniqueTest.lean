import IxCC.Rt.Rc.Gen.Proof.AllocatorReady
import IxCC.Rt.Rc.Gen.Proof.LiveBranches
import IxCC.Rt.Rc.Gen.Proof.ImmediateStep
import IxCC.Own.Rc.Unique
import IxCC.Lir.Proof.Run

/-! The uniqueness test answers the abstract test and writes nothing (`isUnique_spec`). An
immediate's word has its tag bit set and is answered `0` without a read; a location the caller
holds a token for is a live dynamic cell (by `Balance`), whose count word is read: `0` (one
reference) gives `1`, anything else `0`. Every edge of `isUnique` is forward, so no clock is
spent. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Proof

def uniqueProgram : Program := { funcs := #[isUnique], main := 0 }

def uniqueState (mem : X86.Memory) (context : Word) (env : Env) (label pos : Nat := 0) : State :=
  { mem, ctx := context, stack := [{ fn := 0, label, pos, env }] }

theorem unique_initial (mem : X86.Memory) (context word : Word) :
    State.initial uniqueProgram [word] mem context =
      some (uniqueState mem context (({} : Env).insert 0 word)) := by
  simp [State.initial, enter, uniqueProgram, isUnique, bindParams, uniqueState]

/-- An immediate word (tag bit set): the answer is `0`, the memory unchanged. -/
theorem unique_immediate (mem : X86.Memory) (context word : Word) (clock : Nat)
    (htag : word &&& 1 = 1) :
    eval uniqueProgram clock [word] mem context = .ok ([0], mem) := by
  let e0 : Env := ({} : Env).insert 0 word
  have hb : Cond.holds .tnz .w64 word 1 = true := by simp [Cond.holds, htag]
  apply (runs_eval (unique_initial mem context word)).eq
  apply Sem.Reaches.free (s' := uniqueState mem context e0 3 0)
  · apply semStep_next.mpr
    simp [step, uniqueProgram, uniqueState, isUnique, v, i, to, Arg.eval, evalArgs, takeEdge,
      bindParams, hb, e0]
  apply Sem.Reaches.final
  have done : semStep uniqueProgram (uniqueState mem context e0 3 0) = .done ([0], mem) := by
    apply semStep_done.mpr
    simp [step, uniqueProgram, uniqueState, isUnique, i, evalArgs, Arg.eval]
  rw [done]
  exact .done

/-- A live cell of any layout: the answer is `1` exactly when it has one reference, the memory
unchanged. -/
theorem unique_cell {addresses : AddressMap} {mem : X86.Memory} {address : Word} {refs : Nat}
    {body : Body} (cell : LiveCell addresses mem address refs body) (context : Word) (clock : Nat) :
    eval uniqueProgram clock [address] mem context =
      .ok ([if refs = 1 then 1 else 0], mem) := by
  let e0 : Env := ({} : Env).insert 0 address
  let e1 := e0.insert 1 (UInt64.ofNat (refs - 1))
  have h0 : e0[0]? = some address := by simp [e0]
  have h1 : e1[1]? = some (UInt64.ofNat (refs - 1)) := by simp [e1]
  apply (runs_eval (unique_initial mem context address)).eq
  apply Sem.Reaches.free (s' := uniqueState mem context e0 1 0)
  · apply semStep_next.mpr
    simp [step, uniqueProgram, uniqueState, isUnique, v, i, to, Arg.eval, evalArgs, takeEdge,
      bindParams, cell.pointer_branch, e0]
  apply Sem.Reaches.free (s' := uniqueState mem context e1 1 1)
  · apply semStep_next.mpr
    simp [step, uniqueProgram, uniqueState, isUnique, cellAddr, Stmt.exec, Rhs.eval, Addr.eval,
      dispWord, h0, cell.count_load, e1]
  by_cases hr : refs = 1
  · have hz : Cond.holds .eq .w32 (UInt64.ofNat (refs - 1)) 0 = true := by
      subst hr; decide
    apply Sem.Reaches.free (s' := uniqueState mem context e1 2 0)
    · apply semStep_next.mpr
      simp [step, uniqueProgram, uniqueState, isUnique, v, i, to, Arg.eval, evalArgs, takeEdge,
        bindParams, h1, hz]
    apply Sem.Reaches.final
    have done : semStep uniqueProgram (uniqueState mem context e1 2 0) = .done ([1], mem) := by
      apply semStep_done.mpr
      simp [step, uniqueProgram, uniqueState, isUnique, i, evalArgs, Arg.eval]
    rw [done, show (if refs = 1 then (1 : Word) else 0) = 1 from by simp [hr]]
    exact .done
  · have hs : 1 < refs := by have := cell.positive; omega
    have hz := cell.shared_branch hs
    apply Sem.Reaches.free (s' := uniqueState mem context e1 3 0)
    · apply semStep_next.mpr
      simp [step, uniqueProgram, uniqueState, isUnique, v, i, to, Arg.eval, evalArgs, takeEdge,
        bindParams, h1, hz]
    apply Sem.Reaches.final
    have done : semStep uniqueProgram (uniqueState mem context e1 3 0) = .done ([0], mem) := by
      apply semStep_done.mpr
      simp [step, uniqueProgram, uniqueState, isUnique, i, evalArgs, Arg.eval]
    rw [done, show (if refs = 1 then (1 : Word) else 0) = 0 from by simp [hr]]
    exact .done

/-- The uniqueness test at a release cutpoint with no current value and no suspended cursor:
for any token the caller holds (a location is held when its external count is positive), it
answers `uniqueOf` and writes nothing. -/
theorem ReleaseInvariant.isUnique_answer
    {cmax heap addresses mem external context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external none [] context base bump limit slots lists)
    {value : RVal} {word : Word} (hw : valueWord addresses value = some word)
    (held : ∀ l, value = .loc l → 0 < external l) (clock : Nat) :
    eval uniqueProgram clock [word] mem context =
      .ok ([if uniqueOf heap value then 1 else 0], mem) := by
  cases value with
  | loc l =>
    have hb := h.balance l
    have hpos := held l rfl
    cases hc : heap.cell? l with
    | none => simp [dynCount, hc, cursorTokens, flattenPending, refsIn] at hb; omega
    | some c =>
      cases c with
      | dead => simp [dynCount, hc, cursorTokens, flattenPending, refsIn] at hb; omega
      | live rc mode b =>
        obtain ⟨hm, address, ha, cell⟩ := h.live.cell l rc mode b hc
        subst hm
        have hwa : word = address := by
          simp only [valueWord, ha] at hw
          exact (Option.some.inj hw).symm
        subst hwa
        rw [unique_cell cell context clock]
        simp [uniqueOf, hc]
  | lit literal =>
    rw [unique_immediate mem context word clock (valueWord_immediate_tag hw (by simp))]
    simp [uniqueOf]
  | ctor0 ctor =>
    rw [unique_immediate mem context word clock (valueWord_immediate_tag hw (by simp))]
    simp [uniqueOf]
  | erased =>
    rw [unique_immediate mem context word clock (valueWord_immediate_tag hw (by simp))]
    simp [uniqueOf]

/-- The uniqueness test answers the abstract test and writes nothing, for any token the caller
holds, from a ready allocator (the plan's `isUnique_spec`). -/
theorem isUnique_spec {cmax heap addresses mem external context base bump limit slots lists}
    (h : AllocatorReady cmax heap addresses mem external context base bump limit slots lists)
    {value : RVal} {word : Word} (hw : valueWord addresses value = some word)
    (held : ∀ l, value = .loc l → 0 < external l) (clock : Nat) :
    eval uniqueProgram clock [word] mem context =
      .ok ([if uniqueOf heap value then 1 else 0], mem) :=
  h.idle.isUnique_answer hw held clock

end IxCC.Rt.Rc.Gen
