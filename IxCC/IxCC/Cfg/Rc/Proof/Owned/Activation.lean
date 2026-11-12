import IxCC.Cfg.Rc.Proof.Native.CodeContract
import IxCC.Cfg.Rc.Proof.Check
import IxCC.Cfg.Rc.Proof.Scoped
import IxCC.Own.Plain.Proof.Owned.Simulation
import IxCC.Own.Plain.Proof.OwnedAccepts

/-! # The activation invariant over the ownership checker's typing context (heap stage 2)

`Activation` (`Native/Activation.lean`) holds the canonical producer's state and a cursor on
`lowerCode live joins code imm`; the restated invariant holds the checker's typing context
instead (`Own.Plain.OwnedState`), the checker's verdict on the actual Own code, and a cursor on
that code. The recursive claim `PhysicalCodeOwned` fixes the Own code (`PhysicalCode` fixes the
Fir code); the source side runs `eraseCode code`, so an action is a source stutter.
`HeapState` is the canonical layer's, unchanged.

Built beside the canonical layer; the checker's acceptance is read from the admission through
`checkScopedProgram_checkOwned` (today through canonical acceptance, `checkPlainMap_checkOwned`). -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc

/-- The program gate admits only maps the ownership checker accepts. -/
theorem checkScopedProgram_checkOwned {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : checkScopedProgram F bodies P = true) : Own.Plain.checkOwned F bodies = true :=
  Own.Plain.checkPlainMap_checkOwned (checkProgram_parts (checkScopedProgram_parts h).1).1

end IxCC.Cfg.Rc

namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs
open IxCC.Own.Plain (Ctx JCtx checkCode)

/-- **The activation invariant over a typing context.** -/
structure ActivationOwned (F : Fir.Program) (P : Program) (pairs : List (Nat × Cfg.Fun))
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

theorem ActivationOwned.lexical {F : Fir.Program} {P : Program} {pairs : List (Nat × Cfg.Fun)}
    {lp : Lir.Program} {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {live : List Fir.Var} {Γ : Ctx} {Δ : JCtx} {sourceEnv : Fir.Env} {ownedEnv : Own.Env}
    {roots : List Own.RVal} {lex : Own.Plain.Joins} {sourceJoins : List Fir.JEntry}
    {ownedJoins : List Own.Plain.JEntry} {code : Own.Plain.Code} {bound : Nat}
    {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : ActivationOwned F P pairs lp H addresses external live Γ Δ sourceEnv ownedEnv roots
      lex sourceJoins ownedJoins code bound function source target) :
    EnvSub ownedEnv source.env ∧
    FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound ownedEnv target.env ∧
    Own.Plain.EnvBounded H.size ownedEnv ∧
    FusedCtorOk (tablesOf P pairs) (Rt.Proof.Fused (tablesOf P pairs) function) ownedEnv := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, sub, _⟩ := before.layout
  exact ⟨sub, before.frame.lexical sub⟩

/-- The recursive claim with the source join stack and the Own code fixed. -/
def PhysicalCodeOwned (F : Fir.Program) (P : Program) (config : Rt.Config)
    (pairs : List (Nat × Cfg.Fun)) (main clock : Nat)
    (sourceJoins : List Fir.JEntry) (code : Own.Plain.Code) : Prop :=
  ∀ (H : Own.Heap) (addresses : AddressMap) (external : Nat → Nat)
    (live : List Fir.Var) (Γ : Ctx) (Δ : JCtx) (sourceEnv : Fir.Env) (ownedEnv : Own.Env)
    (roots : List Own.RVal) (lex : Own.Plain.Joins) (ownedJoins : List Own.Plain.JEntry)
    (sourceFunction : Fir.Fun) (function : Cfg.Fun)
    (source : Cfg.Frame) (target : Lir.Frame) (memory : X86.Memory)
    (context base bump limit : Lir.Word) (regionBytes : Nat)
    (slots : List Slot) (lists : Nat → List Lir.Word) (callers : List Lir.Frame),
    F.fun? source.fn = some sourceFunction →
    ActivationOwned F P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      H addresses external live Γ Δ sourceEnv ownedEnv roots lex sourceJoins ownedJoins
      code sourceFunction.vars function source target →
    HeapState P pairs H addresses memory external roots context base bump limit regionBytes slots lists →
    ResultAt P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      H addresses external context base limit regionBytes clock
      {mem := memory, ctx := context, stack := target :: callers} callers
      (Fir.eval F clock sourceEnv sourceJoins (Own.Plain.eraseCode code))

def PhysicalAtClockOwned (F : Fir.Program) (P : Program) (config : Rt.Config)
    (pairs : List (Nat × Cfg.Fun)) (main clock : Nat) : Prop :=
  ∀ (sourceJoins : List Fir.JEntry) (code : Own.Plain.Code),
    PhysicalCodeOwned F P config pairs main clock sourceJoins code

/-- Reference-count-equal root lists hold the same external owners. -/
theorem holdRoots_sameRefs {external : Nat → Nat} {a b : List Own.RVal}
    (h : Own.Plain.SameRefs a b) : Own.Rc.holdRoots external a = Own.Rc.holdRoots external b := by
  funext l
  simp only [Own.Rc.holdRoots, h l]

end IxCC.Cfg.Rc.Native.Spec
