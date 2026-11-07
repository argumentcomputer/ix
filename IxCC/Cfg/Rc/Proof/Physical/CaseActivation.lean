import IxCC.Cfg.Rc.Proof.Physical.CaseEntry
import IxCC.Cfg.Rc.Proof.Ordinary
import IxCC.Cfg.Rc.Proof.Native.Activation
import IxCC.Cfg.Rc.Proof.Physical.Admission
import IxCC.Own.Plain.Proof.Values

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs

/-- Execute the actual selected case arm from a checked activation. Its
source key and first-match selection determine the arm; actual native
lowering supplies dispatch and entry, including fused overflow failure. -/
theorem case_activation
    {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    (switches : Rt.checkSwitches P.base = .ok ()) {lp : Lir.Program}
    {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat} {roots : List Own.RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    {x : Fir.Var} {alts : List Fir.Alt} {default : Option Fir.Code}
    {sourceFunction : Fir.Fun} {function : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (before : Activation F P pairs lp H addresses external live ρf ρo roots joins Jf Jo
      (.case x alts default) sourceFunction.vars function source target)
    (sourceLookup : F.fun? source.fn = some sourceFunction)
    {logical : Fir.Val} (sourceValue : ρf.get? x = some logical)
    {key : Key.CtorKey} {logicalFields : List Fir.Val}
    (sourceCtor : logical.asCtor F.known = some (key, logicalFields))
    {body : Fir.Code} (selected : firCase key alts default = some body)
    {mem : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses mem external roots context base bump limit regionBytes slots lists)
    (callers : List Lir.Frame) :
    (∃ after final cost,
      Activation F P pairs lp H addresses external live ρf ρo roots joins Jf Jo body
        sourceFunction.vars function after final ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} cost
        {mem, ctx := context, stack := final :: callers} ∧
      after.fn = source.fn ∧ body.size < (Fir.Code.case x alts default).size) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  have scope : x ∈ live ∧ Own.Plain.scopeAlts (Own.Plain.signatures F) live
      (Own.Plain.stackArities Jf) alts = true ∧
      Own.Plain.scopeOpt (Own.Plain.signatures F) live (Own.Plain.stackArities Jf) default = true := by
    simpa [Own.Plain.scopeOk, Bool.and_eq_true, and_assoc] using before.scope
  obtain ⟨value, actualLogical, ownedLookup, logicalLookup, den⟩ := before.canonical.env x scope.1
  have equal : actualLogical = logical := Option.some.inj (logicalLookup.symm.trans sourceValue)
  subst actualLogical
  obtain ⟨fields, ownCtor, _⟩ := (Own.Plain.Values.asCtor_den F.known den).1 key logicalFields sourceCtor
  have known : (tablesOf P pairs).known = F.known :=
    congrArg Own.Tables.known (generate_tables (checkProgram_parts (checkScopedProgram_parts checked).1).2)
  have constructor : value.asCtor (tablesOf P pairs).known H = some (key, fields) := by
    rw [known]
    exact ownCtor
  have chosen : ownCase key (Own.Plain.lowerAlts live joins alts) (Own.Plain.lowerOpt live joins default) =
      some (Own.Plain.lowerCode live joins body) := by rw [firCase_lower, selected]; rfl
  obtain ⟨fd, _, _, _, _, _, _, lookup, range, _⟩ := before.layout
  have programSize : P.base.size = F.size := generate_size (checkProgram_parts (checkScopedProgram_parts checked).1).2
  have nativeRange : source.fn < P.base.size := by simpa only [programSize] using range
  obtain ⟨original, actual, originalLookup, receipt, actualLookup⟩ := consumed_entry consuming nativeRange
  have originalEqual : original = fd := Option.some.inj (originalLookup.symm.trans lookup)
  subst original
  have actualEqual : actual = function := Option.some.inj (actualLookup.symm.trans before.frame.lookup)
  subst actual
  have real := checked_consumed_sup checked range sourceLookup lookup receipt
  rcases case_entry consuming switches before.layout chosen before.frame nativeRange real before.fused
      ownedLookup constructor heap.ready.idle.live heap.compatible before.running context callers with success | failure
  · obtain ⟨after, final, cost, layout, frame, trace, running, sameFn, fused⟩ := success
    refine .inl ⟨after, final, cost,
      ⟨before.canonical, layout, frame, firCase_scope scope.2.1 scope.2.2 selected, running, fused⟩,
      trace, sameFn, ?_⟩
    have size := firCase_size selected
    simp only [Fir.Code.size]
    omega
  · exact .inr failure


end IxCC.Cfg.Rc.Native
