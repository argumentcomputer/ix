import IxCC.Cfg.Rc.Proof.Native.TerminalOutcomes
import IxCC.Cfg.Rc.Proof.Native.InitialStages

/-! Static admission and the precise recursive claim for whole-code
composition. The claim contains concrete activation and heap invariants;
it is not assumed by admission or by the final driver. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc.Procs

structure CodeAdmission (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code)
    (P : Program) (config : Rt.Config) (pairs : List (Nat × Cfg.Fun))
    (functions : List Lir.Func) : Prop where
  scopedProgram : checkScopedProgram F bodies P = true
  consuming : consumeAll P = .ok pairs
  lowering : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
    (List.range P.base.size) = .ok functions
  switches : Rt.checkSwitches P.base = .ok ()

theorem CodeAdmission.of_public {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Public.Lowered}
    (checked : checkScopedProgram F bodies P = true)
    (accepted : Public.lower config F bodies P = .ok lowered) :
    ∃ main pairs functions, CodeAdmission F bodies P config pairs functions ∧
      P.base.exports.head? = some main := by
  obtain ⟨original, native, _, _⟩ := Public.Spec.lower_parts accepted
  obtain ⟨main, pairs, functions, _, switches, entry, _, consuming, lowering, _⟩ := lower_parts native
  exact ⟨main, pairs, functions, ⟨checked, consuming, lowering, switches⟩, entry⟩

/-- Recursive code simulation at a source clock. Every physical continuation
starts at the exact current Cfg/native cursor, with all source and caller
ownership represented in the given heap. Older native caller frames remain
literal until an actual return instruction resumes one. -/
def PhysicalAtClock (F : Fir.Program) (P : Program) (config : Rt.Config)
    (pairs : List (Nat × Cfg.Fun)) (main clock : Nat) : Prop :=
  ∀ (H : Own.Heap) (addresses : AddressMap) (external : Nat → Nat)
    (live : List Fir.Var) (sourceEnv : Fir.Env) (ownedEnv : Own.Env) (roots : List Own.RVal)
    (joins : Own.Plain.Joins) (sourceJoins : List Fir.JEntry) (ownedJoins : List Own.Plain.JEntry)
    (code : Fir.Code) (sourceFunction : Fir.Fun) (function : Cfg.Fun)
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


end IxCC.Cfg.Rc.Native.Spec
