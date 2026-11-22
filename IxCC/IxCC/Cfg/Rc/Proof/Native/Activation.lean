import IxCC.Cfg.Rc.Proof.Native.FrameState
import IxCC.Cfg.Rc.Proof.JoinStep
import IxCC.Own.Plain.Proof.Owned.Joins
import IxCC.Own.Plain.Proof.Owned.Inversion

/-! The combined source/native activation invariant for the physical induction over the
**Own** code (heap stage 2). It holds the ownership checker's typing context
(`Own.Plain.OwnedState`: which variables are owned, borrowed or immediate, with their tokens as a
multiset of roots), the checker's verdict on the actual Own code, a cursor on that code, the
original RC Cfg position, the full native frame and the fused comparison receipt. The source
side runs the code's erasure (`eraseCode`), so an `inc` or `dec` is a source stutter. No field
assumes simulation, target execution, or a final result. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs
open IxCC.Own.Plain (Ctx JCtx checkCode)

structure Activation (F : Fir.Program) (P : Program) (pairs : List (Nat × Cfg.Fun))
    (lp : Lir.Program) (H : Own.Heap) (addresses : AddressMap) (external : Nat → Nat)
    (live : List Fir.Var) (Γ : Ctx) (Δ : JCtx) (sourceEnv : Fir.Env) (ownedEnv : Own.Env)
    (roots : List Own.RVal) (lex : Own.Plain.Joins) (sourceJoins : List Fir.JEntry)
    (ownedJoins : List Own.Plain.JEntry) (code : Own.Plain.Code) (bound : Nat)
    (function : Cfg.Fun) (source : Cfg.Frame) (target : Lir.Frame) : Prop where
  owned : Own.Plain.OwnedState (Own.Plain.signatures F) H external live Γ sourceEnv ownedEnv roots
    lex Δ sourceJoins ownedJoins
  typed : checkCode Δ Γ code = .ok ()
  layout : At F P source ownedEnv ownedJoins code
  frame : FrameState P pairs lp addresses H.size bound function source target
  scope : Own.Plain.scopeOk (Own.Plain.signatures F) live (Own.Plain.stackArities sourceJoins)
    (Own.Plain.eraseCode code) = true
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
    {live : List Fir.Var} {Γ : Ctx} {Δ : JCtx} {sourceEnv : Fir.Env} {ownedEnv : Own.Env}
    {roots : List Own.RVal} {lex : Own.Plain.Joins} {sourceJoins : List Fir.JEntry}
    {ownedJoins : List Own.Plain.JEntry} {code : Own.Plain.Code} {bound : Nat}
    {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs lp H addresses external live Γ Δ sourceEnv ownedEnv roots
      lex sourceJoins ownedJoins code bound function source target) :
    EnvSub ownedEnv source.env ∧
    FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ownedEnv target.env ∧
    Own.Plain.EnvBounded H.size ownedEnv ∧
    FusedCtorOk (tablesOf P pairs) (Rt.Proof.Fused (tablesOf P pairs) function) ownedEnv := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, sub, _⟩ := before.layout
  exact ⟨sub, before.frame.lexical sub⟩

/-- Reference-count-equal root lists hold the same external owners. -/
theorem holdRoots_sameRefs {external : Nat → Nat} {a b : List Own.RVal}
    (h : Own.Plain.SameRefs a b) : Own.Rc.holdRoots external a = Own.Rc.holdRoots external b := by
  funext l
  simp only [Own.Rc.holdRoots, h l]

/-- Join declaration is a zero-step change of the typing context's join metadata: the saved entry
is the Own body the checker typed from `Γ.enter`, and the join context maps the join to its
captured list. All heap facts, registers, the cursor and the fused receipt are unchanged. -/
theorem Activation.declare {F : Fir.Program} {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {lp : Lir.Program} {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {live : List Fir.Var} {Γ : Ctx} {Δ : JCtx} {sourceEnv : Fir.Env} {ownedEnv : Own.Env}
    {roots : List Own.RVal} {lex : Own.Plain.Joins} {sourceJoins : List Fir.JEntry}
    {ownedJoins : List Own.Plain.JEntry} {j : Fir.JoinId} {params captured : List Fir.Var}
    {rec : Bool} {body cont : Own.Plain.Code} {bound : Nat}
    {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs lp H addresses external live Γ Δ sourceEnv ownedEnv roots
      lex sourceJoins ownedJoins (.jp j params captured rec body cont) bound function source target) :
    Activation F P pairs lp H addresses external live Γ (Δ.insert j captured) sourceEnv
      ownedEnv roots ((j, live) :: lex)
      ({id := j, charged := false, env := sourceEnv, params, body := Own.Plain.eraseCode body,
        isRec := rec} :: sourceJoins)
      ({id := j, charged := false, env := ownedEnv, params, body, isRec := rec} :: ownedJoins)
      cont bound function source target := by
  obtain ⟨hnd, hneed, htyped, hcont⟩ := Own.Plain.checkCode_jp before.typed
  have scopeFacts := before.scope
  simp only [Own.Plain.eraseCode, Own.Plain.scopeOk, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at scopeFacts
  obtain ⟨hnone, fresh, bodyScope, contScope⟩ := scopeFacts
  refine ⟨before.owned.declare hnd hneed htyped hnone fresh bodyScope, hcont, before.layout.join,
    before.frame, ?_, before.running, before.fused⟩
  simpa only [Own.Plain.stackArities, List.map_cons] using contScope

end IxCC.Cfg.Rc.Native.Spec
