import IxCC.Cfg.Rc.Proof.Physical.AllocationTokens
import IxCC.Cfg.Rc.Proof.Physical.AllocationOutcome
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedWords

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Own IxCC.Own.Rc IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Rc.Procs

/-- Source constructor evaluation, exact field-token transfer and the total
physical operation share the same newly allocated heap and returned address.
Only lexical freshness and the real source/register boundary are inputs. -/
theorem fused_allocation_source_wrapper
    {H : Heap} {external : Nat → Nat} {fields held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external (fields ++ held) live ρf ρo roots)
    (tables : Own.Tables) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (x : Fir.Var)
    (fresh : x ∉ live) (scope : args.all (Own.Plain.argIn live) = true)
    (arguments : Own.evalArgs ρo args = some fields) (arity : fields.length = ctor.arity)
    (positive : 0 < ctor.arity) (small : ctor.arity ≤ maxFields)
    (tagBound : ctor.tag ≤ maxTag) (nobj : ctor.nobj = ctor.arity)
    (nscalar : ctor.nscalar = 0) (shared : ctor.fieldKinds = List.replicate ctor.arity .shared)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (holdRoots external (roots ++ fields ++ held)) context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure bound : Nat} {env : Lir.Env}
    (words : Nat → Lir.Word)
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure ctor.arity))
    (procedureLookup : P.funcs[procedure]? = some (Gen.alloc (CellLayout.ofFields ctor.arity ctor.tag)))
    (registers : ∀ i < fields.length, env[i]? = some (words i))
    (values : ∀ j value, fields[j]? = some value → valueWord addresses value = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [x])
    {D : Nat → Prop} (related : FusedWords addresses D bound ρo caller.env)
    (real : x < bound)
    (bounded : Own.Plain.EnvBounded H.size ρo) :
    ∃ sourceValues,
      Fir.evalArgs ρf args = some sourceValues ∧
      let allocated := H.alloc .rc {ctor, fields}
      Own.Plain.evalRhs tables ρo H (.ctor ctor args) = .ok allocated ∧
      Tokens allocated.2 external held (live ++ [x])
        (ρf.insert x (.ctor ctor sourceValues)) (ρo.insert x allocated.1) (roots ++ [allocated.1]) ∧
      ((∃ address next finalMem finalSlots finalLists,
        Gen.AllocatorReady maxClass allocated.2 (placeFresh addresses H.size address) finalMem
          (holdRoots external ((roots ++ [allocated.1]) ++ held))
          context base next limit finalSlots finalLists ∧
        Sem.Star (Lir.semStep P)
          {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers} 1
          {mem := finalMem, ctx := context,
            stack := {caller with env := caller.env.insert x address, dsts := []} :: callers} ∧
        FusedWords (placeFresh addresses H.size address) D bound
          (ρo.insert x allocated.1) (caller.env.insert x address)) ∨
      Sem.Reaches (Lir.semStep P)
        {mem, ctx := context, stack := {fn := wrapper, label := 0, pos := 0, env} :: caller :: callers}
        1 (.resource .heap)) := by
  obtain ⟨sourceValues, sourceArgs, effect, tokens, _⟩ :=
    allocation_tokens before tables ctor args x fresh scope arguments arity positive
  refine ⟨sourceValues, sourceArgs, effect, tokens, ?_⟩
  have input : holdRoots external (roots ++ fields ++ held) =
      (fun location => holdRoots external (roots ++ held) location + refsIn location fields) := by
    funext location
    simp only [holdRoots, refsIn_append]
    omega
  rw [input] at ready
  have output : (fun location => holdRoots external (roots ++ held) location +
      refsIn location [(H.alloc .rc {ctor, fields}).1]) =
      holdRoots external ((roots ++ [(H.alloc .rc {ctor, fields}).1]) ++ held) := by
    funext location
    simp only [holdRoots, refsIn_append]
    omega
  rcases allocation_outcome (body := {ctor, fields}) ready (by simpa [arity] using positive)
      (by simpa [arity] using small) tagBound (by simpa [arity] using nobj) nscalar
      (by simpa [arity] using shared) words (by simpa [arity] using wrapperLookup)
      (by simpa [arity] using procedureLookup) registers values caller callers dest with success | failure
  · obtain ⟨address, next, finalMem, finalSlots, finalLists, restored, trace⟩ := success
    rw [output] at restored
    exact .inl ⟨address, next, finalMem, finalSlots, finalLists, restored, trace,
      related.publish real bounded address⟩
  · exact .inr failure


end IxCC.Cfg.Rc.Native
