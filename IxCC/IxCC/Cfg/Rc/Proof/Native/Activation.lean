import IxCC.Cfg.Rc.Proof.Native.FrameState
import IxCC.Cfg.Rc.Proof.JoinStep
import IxCC.Own.Plain.Proof.State

/-! The combined source/native activation invariant for induction over real
Fir code. It retains the canonical source state (including join captures and
scope), original RC Cfg position, full native frame, and fused comparison
receipt. No field assumes simulation, target execution, or a final result. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs

structure Activation (F : Fir.Program) (P : Program) (pairs : List (Nat × Cfg.Fun))
    (lp : Lir.Program) (H : Own.Heap) (addresses : AddressMap) (external : Nat → Nat)
    (live : List Fir.Var) (sourceEnv : Fir.Env) (ownedEnv : Own.Env) (roots : List Own.RVal)
    (joins : Own.Plain.Joins) (sourceJoins : List Fir.JEntry) (ownedJoins : List Own.Plain.JEntry)
    (code : Fir.Code) (bound : Nat) (function : Cfg.Fun)
    (source : Cfg.Frame) (target : Lir.Frame)
    (imm : List Fir.Var := []) : Prop where
  canonical : Own.Plain.State (Own.Plain.signatures F) H external live sourceEnv ownedEnv roots
    joins sourceJoins ownedJoins imm
  layout : At F P source ownedEnv ownedJoins (Own.Plain.lowerCode live joins code imm)
  frame : FrameState P pairs lp addresses H.size bound function source target
  scope : Own.Plain.scopeOk (Own.Plain.signatures F) live (Own.Plain.stackArities sourceJoins) code = true
  running : target.dsts = []
  fused : ∀ block, function.blocks[source.blk]? = some block →
    Rt.Proof.FusedDone (tablesOf P pairs) function block source

/-- Heap facts shared by the current activation and suspended callers. Fixed
extent comes from actual initialization; recycling does not change it. -/
structure HeapState (P : Program) (pairs : List (Nat × Cfg.Fun))
    (H : Own.Heap) (addresses : AddressMap) (mem : X86.Memory)
    (external : Nat → Nat) (roots : List Own.RVal)
    (context base bump limit : Lir.Word) (regionBytes : Nat)
    (slots : List Slot) (lists : Nat → List Lir.Word) : Prop where
  ready : Gen.AllocatorReady maxClass H addresses mem (Own.Rc.holdRoots external roots)
    context base bump limit slots lists
  ordered : Own.Rc.HeapOk H
  compatible : HeapCtorOk (tablesOf P pairs) H
  extent : limit.toNat - base.toNat ≤ regionBytes

theorem Activation.lexical {F : Fir.Program} {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {lp : Lir.Program} {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {live imm : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env} {roots : List Own.RVal}
    {joins : Own.Plain.Joins} {sourceJoins : List Fir.JEntry} {ownedJoins : List Own.Plain.JEntry}
    {code : Fir.Code} {bound : Nat} {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs lp H addresses external live sourceEnv ownedEnv roots
      joins sourceJoins ownedJoins code bound function source target imm) :
    EnvSub ownedEnv source.env ∧
    FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ownedEnv target.env ∧
    Own.Plain.EnvBounded H.size ownedEnv ∧
    FusedCtorOk (tablesOf P pairs) (Rt.Proof.Fused (tablesOf P pairs) function) ownedEnv := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, sub, _⟩ := before.layout
  exact ⟨sub, before.frame.lexical sub⟩

/-- Join declaration is a zero-step change of canonical lexical metadata.
All heap facts, physical registers, actual cursor and fused receipt remain
the same; the saved join carries the exact captured source environment. -/
theorem Activation.declare {F : Fir.Program} {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {lp : Lir.Program} {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {live imm : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env} {roots : List Own.RVal}
    {joins : Own.Plain.Joins} {sourceJoins : List Fir.JEntry} {ownedJoins : List Own.Plain.JEntry}
    {j : Fir.JoinId} {params : List Fir.Var} {rec : Bool} {body cont : Fir.Code}
    {bound : Nat} {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs lp H addresses external live sourceEnv ownedEnv roots
      joins sourceJoins ownedJoins (.jp j params rec body cont) bound function source target imm) :
    let sourceEntry : Fir.JEntry :=
      {id := j, charged := false, env := sourceEnv, params, body, isRec := rec}
    let ownedEntry : Own.Plain.JEntry := {
      id := j, charged := false, env := ownedEnv, params
      body := Own.Plain.lowerCode (live ++ params) (if rec then (j, live) :: joins else joins) body
      isRec := rec }
    Activation F P pairs lp H addresses external live sourceEnv ownedEnv roots
      ((j, live) :: joins) (sourceEntry :: sourceJoins) (ownedEntry :: ownedJoins)
      cont bound function source target imm := by
  have scopeFacts := before.scope
  simp only [Own.Plain.scopeOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at scopeFacts
  obtain ⟨_, fresh, bodyScope, contScope⟩ := scopeFacts
  refine ⟨before.canonical.declare j params rec body fresh bodyScope,
    before.layout.join, before.frame, ?_, before.running, before.fused⟩
  simpa only [Own.Plain.stackArities, List.map_cons] using contScope



end IxCC.Cfg.Rc.Native.Spec
