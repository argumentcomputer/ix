import IxCC.Cfg.Rc.Proof.Physical.AllocSteps
import IxCC.Cfg.Rc.Proof.Physical.AllocCaller
import IxCC.Rt.Rc.Gen.Proof.Scanned

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Gen (fieldsClass)
open IxCC.Lir
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

theorem allocation_wrapper_success {fields tag : Nat}
    (positive : 0 < fields) (small : fields ≤ maxFields) (tagBound : tag ≤ maxTag)
    {mem reserved : X86.Memory} {context address : Word}
    (execution : Lir.eval (Gen.allocProgram (CellLayout.ofFields fields tag)) 0 [] mem context = .ok ([address], reserved))
    {P : Lir.Program} {wrapper procedure destination : Nat} {env : Lir.Env} {words : Nat → Word}
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure fields))
    (procedureLookup : P.funcs[procedure]? = some (Gen.alloc (CellLayout.ofFields fields tag)))
    (values : ∀ i < fields, env[i]? = some (words i))
    (writable : ∀ i < fields, ∀ byte < 8,
      reserved.writable (fieldAddress address i + UInt64.ofNat byte) = true)
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [destination]) :
    Sem.Star (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
      {mem := publishFields reserved address words (List.range fields), ctx := context,
        stack := {caller with env := caller.env.insert destination address, dsts := []} :: callers} := by
  have enter : Lir.enter P procedure [] = some {fn := procedure, label := 0, pos := 0, env := {}} := by
    simp [Lir.enter, procedureLookup,
      Gen.alloc_eq (Gen.ofFields_layout positive small tagBound).1 (Gen.ofFields_layout (tag := tag) positive small tagBound).2,
      Gen.allocFunc, Lir.bindParams]
  have callStep := allocation_call (env := env) (rest := caller :: callers)
    (mem := mem) (ctx := context) wrapperLookup enter
  let continuation : Lir.Frame := {fn := wrapper, label := 0, pos := 1, env, dsts := [fields]}
  have procedureTrace := allocator_caller positive small tagBound execution procedureLookup
    continuation (caller :: callers) rfl
  have stores := allocation_publish (rest := caller :: callers) (ctx := context)
    wrapperLookup values writable
  have returnStep := allocation_return (env := env.insert fields address) (address := address)
    (caller := caller) (rest := callers)
    (mem := publishFields reserved address words (List.range fields)) (ctx := context)
    wrapperLookup (by simp) dest
  have combined := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans
    (procedureTrace.trans (stores.trans (Sem.Star.single (Lir.semStep_next.mpr returnStep))))
  simpa [continuation] using combined

/-- Complete concrete free-list allocation and publication wrapper. Every
operational premise is a load, branch condition or permission, discharged
from the physical arena invariant at the later program boundary. -/
theorem allocation_free_wrapper {fields tag : Nat}
    (positive : 0 < fields) (small : fields ≤ maxFields) (tagBound : tag ≤ maxTag)
    {mem : X86.Memory} {context address next : Word}
    (nonzero : address ≠ 0)
    (head : Lir.loadWord mem .w64 .zero (Gen.headAddress context (fieldsClass fields)) = some address)
    (link : Lir.loadWord mem .w64 .zero address = some next)
    (headWritable : ∀ byte < 8, mem.writable (Gen.headAddress context (fieldsClass fields) + UInt64.ofNat byte) = true)
    (headerWritable : ∀ byte < 8, mem.writable (address + UInt64.ofNat byte) = true)
    {P : Lir.Program} {wrapper procedure destination : Nat} {env : Lir.Env} {words : Nat → Word}
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure fields))
    (procedureLookup : P.funcs[procedure]? = some (Gen.alloc (CellLayout.ofFields fields tag)))
    (values : ∀ i < fields, env[i]? = some (words i))
    (payloadWritable : ∀ i < fields, ∀ byte < 8,
      mem.writable (fieldAddress address i + UInt64.ofNat byte) = true)
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [destination]) :
    Sem.Star (Lir.semStep P)
      {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
      {mem := publishFields (Gen.reserveFree mem context address next (CellLayout.ofFields fields tag) (fieldsClass fields)) address words (List.range fields),
        ctx := context, stack := {caller with env := caller.env.insert destination address, dsts := []} :: callers} := by
  apply allocation_wrapper_success positive small tagBound
    (Gen.alloc_free mem context address next _ _ 0
      (Gen.ofFields_layout positive small tagBound).1 (Gen.ofFields_layout (tag := tag) positive small tagBound).2 nonzero
      head link headWritable headerWritable)
    wrapperLookup procedureLookup values (by
      simpa [Gen.reserveFree, X86.Memory.write] using payloadWritable) caller callers dest



end IxCC.Cfg.Rc.Native
