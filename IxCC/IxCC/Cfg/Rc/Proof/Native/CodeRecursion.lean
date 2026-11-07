import IxCC.Cfg.Rc.Proof.Native.CodeContract

/-! The recursive claim with its source syntax and join stack fixed. This
keeps operation continuations narrow and exposes the evaluator's actual
clock/code-and-join induction measure. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc.Procs

def PhysicalCode (F : Fir.Program) (P : Program) (config : Rt.Config)
    (pairs : List (Nat × Cfg.Fun)) (main clock : Nat)
    (sourceJoins : List Fir.JEntry) (code : Fir.Code) : Prop :=
  ∀ (H : Own.Heap) (addresses : AddressMap) (external : Nat → Nat)
    (live : List Fir.Var) (sourceEnv : Fir.Env) (ownedEnv : Own.Env) (roots : List Own.RVal)
    (joins : Own.Plain.Joins) (ownedJoins : List Own.Plain.JEntry)
    (sourceFunction : Fir.Fun) (function : Cfg.Fun)
    (source : Cfg.Frame) (target : Lir.Frame) (memory : X86.Memory)
    (context base bump limit : Lir.Word) (regionBytes : Nat)
    (slots : List Slot) (lists : Nat → List Lir.Word) (callers : List Lir.Frame),
    F.fun? source.fn = some sourceFunction →
    Activation F P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      H addresses external live sourceEnv ownedEnv roots joins sourceJoins ownedJoins
      code sourceFunction.vars function source target →
    HeapState P pairs H addresses memory external roots context base bump limit regionBytes slots lists →
    ResultAt P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      H addresses external context base limit regionBytes clock
      {mem := memory, ctx := context, stack := target :: callers} callers
      (Fir.eval F clock sourceEnv sourceJoins code)

theorem PhysicalAtClock.code {F : Fir.Program} {P : Program} {config : Rt.Config}
    {pairs : List (Nat × Cfg.Fun)} {main clock : Nat}
    (all : PhysicalAtClock F P config pairs main clock)
    (sourceJoins : List Fir.JEntry) (code : Fir.Code) :
    PhysicalCode F P config pairs main clock sourceJoins code := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  exact all H addresses external live sourceEnv ownedEnv roots joins sourceJoins ownedJoins
    code sourceFunction function source target memory context base bump limit regionBytes slots
    lists callers sourceLookup before heap

theorem PhysicalAtClock.of_code {F : Fir.Program} {P : Program} {config : Rt.Config}
    {pairs : List (Nat × Cfg.Fun)} {main clock : Nat}
    (all : ∀ sourceJoins code, PhysicalCode F P config pairs main clock sourceJoins code) :
    PhysicalAtClock F P config pairs main clock := by
  intro H addresses external live sourceEnv ownedEnv roots joins sourceJoins ownedJoins code
    sourceFunction function source target memory context base bump limit regionBytes slots lists
    callers sourceLookup before heap
  exact all sourceJoins code H addresses external live sourceEnv ownedEnv roots joins ownedJoins
    sourceFunction function source target memory context base bump limit regionBytes slots lists
    callers sourceLookup before heap



end IxCC.Cfg.Rc.Native.Spec
