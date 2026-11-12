import IxCC.Cfg.Rc.Proof.Physical.AllocWrapper
import IxCC.Rt.Rc.Gen.Proof.AllocBump
import IxCC.Rt.Rc.Gen.Proof.Scanned

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Gen (fieldsClass)
open IxCC.Lir
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

/-- Complete bump allocation, payload publication and ordinary caller return.
Actual allocator loads and bounds discharge the runtime execution premise. -/
theorem allocation_bump_wrapper {fields tag : Nat}
    (positive : 0 < fields) (small : fields ≤ maxFields) (tagBound : tag ≤ maxTag)
    {mem : X86.Memory} {context address limit : Word}
    (head : Lir.loadWord mem .w64 .zero (Gen.headAddress context (fieldsClass fields)) = some 0)
    (bump : Lir.loadWord mem .w64 .zero (bumpAddress context) = some address)
    (limitValue : Lir.loadWord mem .w64 .zero (limitAddress context) = some limit)
    (noCarry : ¬ address + UInt64.ofNat (classBytes (fieldsClass fields)) < address)
    (fits : Lir.Cond.holds .ule .w64 (address + UInt64.ofNat (classBytes (fieldsClass fields))) limit = true)
    (bumpWritable : ∀ byte < 8, mem.writable (bumpAddress context + UInt64.ofNat byte) = true)
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
      {mem := publishFields
        (Gen.reserveBump mem context address (address + UInt64.ofNat (classBytes (fieldsClass fields))) (CellLayout.ofFields fields tag) (fieldsClass fields))
        address words (List.range fields), ctx := context,
        stack := {caller with env := caller.env.insert destination address, dsts := []} :: callers} := by
  apply allocation_wrapper_success positive small tagBound
    (Gen.alloc_bump mem context address limit _ _ 0
      (Gen.ofFields_layout positive small tagBound).1 (Gen.ofFields_layout (tag := tag) positive small tagBound).2 head bump limitValue
      noCarry fits bumpWritable headerWritable)
    wrapperLookup procedureLookup values (by
      simpa [Gen.reserveBump, X86.Memory.write] using payloadWritable) caller callers dest


end IxCC.Cfg.Rc.Native
