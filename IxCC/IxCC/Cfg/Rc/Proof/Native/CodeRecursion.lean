import IxCC.Cfg.Rc.Proof.Native.CodeContract

/-! The recursive claim with its source join stack and Own code fixed. This keeps operation
continuations narrow and exposes the induction's measure: the source code's size and join-stack
weight, then the Own code's size for an `inc` or `dec` (a source stutter). -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc.Procs

def PhysicalCode (F : Fir.Program) (P : Program) (config : Rt.Config)
    (pairs : List (Nat × Cfg.Fun)) (main clock : Nat)
    (sourceJoins : List Fir.JEntry) (code : Own.Plain.Code) : Prop :=
  ∀ (H : Own.Heap) (addresses : AddressMap) (external : Nat → Nat)
    (live : List Fir.Var) (Γ : Own.Plain.Ctx) (Δ : Own.Plain.JCtx) (sourceEnv : Fir.Env)
    (ownedEnv : Own.Env) (roots : List Own.RVal) (lex : Own.Plain.Joins)
    (ownedJoins : List Own.Plain.JEntry)
    (sourceFunction : Fir.Fun) (function : Cfg.Fun)
    (source : Cfg.Frame) (target : Lir.Frame) (memory : X86.Memory)
    (context base bump limit : Lir.Word) (regionBytes : Nat)
    (slots : List Slot) (lists : Nat → List Lir.Word) (callers : List Lir.Frame),
    F.fun? source.fn = some sourceFunction →
    Activation F P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      H addresses external live Γ Δ sourceEnv ownedEnv roots lex sourceJoins ownedJoins
      code sourceFunction.vars function source target →
    HeapState P pairs H addresses memory external roots context base bump limit regionBytes slots lists →
    ResultAt P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      H addresses external context base limit regionBytes clock
      {mem := memory, ctx := context, stack := target :: callers} callers
      (Fir.eval F clock sourceEnv sourceJoins (Own.Plain.eraseCode code))

theorem PhysicalAtClock.code {F : Fir.Program} {P : Program} {config : Rt.Config}
    {pairs : List (Nat × Cfg.Fun)} {main clock : Nat}
    (all : PhysicalAtClock F P config pairs main clock)
    (sourceJoins : List Fir.JEntry) (code : Own.Plain.Code) :
    PhysicalCode F P config pairs main clock sourceJoins code :=
  all sourceJoins code

theorem PhysicalAtClock.of_code {F : Fir.Program} {P : Program} {config : Rt.Config}
    {pairs : List (Nat × Cfg.Fun)} {main clock : Nat}
    (all : ∀ sourceJoins code, PhysicalCode F P config pairs main clock sourceJoins code) :
    PhysicalAtClock F P config pairs main clock :=
  all

end IxCC.Cfg.Rc.Native.Spec
