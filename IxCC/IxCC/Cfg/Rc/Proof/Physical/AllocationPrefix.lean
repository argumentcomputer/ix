import IxCC.Cfg.Rc.Proof.Physical.AllocationStep
import IxCC.Cfg.Rc.Proof.Physical.AllocationState
import IxCC.Cfg.Rc.Proof.Physical.CopyPrefix
import IxCC.Cfg.Rc.Proof.Physical.FrameTransport
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedContinuation

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

/-- The complete positive constructor prefix executes actual argument copies
and publication, while retaining full-frame registers separately from source
lexical ownership. The returned source State includes all saved joins and
checked scope at the exact physically reached heap. -/
theorem allocation_prefix
    {P : Program} {pairs : List (Nat × Cfg.Fun)} (functions : Nat → Lir.Func) (main : Nat)
    {source : Cfg.Frame} {target : Lir.Frame}
    (cursor : ConsumedCursor P pairs (Public.Spec.sourceStage P functions main) source target)
    (tables : Own.Tables) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (x : Fir.Var)
    {imm : List Fir.Var} {kind : Own.Kind} {first : Nat} {tail : List Cfg.Instr}
    (head : source.rest = encodePrefix P.base.size first (Own.Plain.copies (Own.Plain.heapArgs imm args)) ++
      .bind x (.alloc ctor args kind) :: tail)
    {function : Cfg.Fun} (sourceLookup : (consumed P pairs).fun? source.fn = some function)
    {signatures : Own.Plain.Signatures} {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    (before : Own.Plain.State signatures H (holdRoots external held) live ρf ρo roots joins Jf Jo imm)
    (lexical : EnvSub ρo source.env)
    (fresh : x ∉ live) (scope : args.all (Own.Plain.argIn live) = true) (positive : 0 < ctor.arity)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {bound : Nat}
    (registers : FusedWords addresses (Rt.Proof.Fused (tablesOf P pairs) function) bound source.env target.env)
    (real : x < bound) (bounded : Own.Plain.EnvBounded H.size source.env)
    (absent : ∀ dummy, first ≤ dummy → source.env.get? dummy = none)
    (running : target.dsts = []) (callers : List Lir.Frame) :
    (∃ fields logical copied address next mem' slots' lists' final,
      Own.evalArgs ρo args = some fields ∧ Fir.evalArgs ρf args = some logical ∧
      Own.Plain.evalActions ρo H (Own.Plain.copies (Own.Plain.heapArgs imm args)) = .ok copied ∧
      let allocated := copied.alloc .rc {ctor, fields}
      Own.Plain.evalRhs tables ρo copied (.ctor ctor args) = .ok allocated ∧
      Own.Plain.State signatures allocated.2 (holdRoots external held) (live ++ [x])
        (ρf.insert x (.ctor ctor logical)) (ρo.insert x allocated.1)
        (roots ++ [allocated.1]) joins Jf Jo imm ∧
      AllocatorReady allocated.2 (placeFresh addresses copied.size address) mem'
        (holdRoots external ((roots ++ [allocated.1]) ++ held))
        context base next limit slots' lists' ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} (2 * (Own.Plain.copies (Own.Plain.heapArgs imm args)).length + 2)
        {mem := mem', ctx := context, stack := final :: callers} ∧
      ConsumedCursor P pairs (Public.Spec.sourceStage P functions main)
        {source with rest := tail, env := source.env.insert x allocated.1} final ∧
      FusedWords (placeFresh addresses copied.size address)
        (Rt.Proof.Fused (tablesOf P pairs) function) bound (source.env.insert x allocated.1) final.env ∧
      Own.Plain.EnvBounded allocated.2.size (source.env.insert x allocated.1) ∧
      EnvSub (ρo.insert x allocated.1) (source.env.insert x allocated.1) ∧
      copied.size = H.size ∧ final.dsts = [] ∧
      (∃ result, consume P (layoutOf P) (.bind x (.alloc ctor args kind)) = .ok result) ∧
      (∀ arg ∈ args, Rt.Proof.LiveArg (Rt.Proof.Fused (tablesOf P pairs) function) arg) ∧
      (∀ block, function.blocks[source.blk]? = some block →
        Rt.Proof.FusedDone (tablesOf P pairs) function block
          {source with rest := tail, env := source.env.insert x allocated.1})) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have original := Tokens.ofState before
  have framed := Tokens.extend original lexical
  rcases copy_heapArgs_prefix functions main args cursor head sourceLookup framed
      (ImmEnv.sub before.immOk lexical) scope ready
      registers absent running callers with success | failure
  · obtain ⟨fields, copied, mem₁, target₁, frameArgs, frameCopies, tokens₁, ready₁, trace₁,
      cursor₁, words₁, running₁, values₁⟩ := success
    have size : copied.size = H.size := actions_size frameCopies
    have bounded₁ : Own.Plain.EnvBounded copied.size source.env := by rw [size]; exact bounded
    obtain ⟨actual, logical₀, originalArgs, sourceArgs₀, originalDen⟩ :=
      Own.Plain.args_den before.env args scope
    have fieldsEqual : actual = fields := Option.some.inj
      ((Cfg.Proof.evalArgs_sub lexical originalArgs).symm.trans frameArgs)
    subst actual
    have copies : Own.Plain.evalActions ρo H (Own.Plain.copies (Own.Plain.heapArgs imm args)) = .ok copied := by
      rw [copies_eval_sub lexical (Tokens.present original) (Own.Plain.heapArgs imm args)
        (Own.Plain.heapArgs_scope imm scope) H]
      exact frameCopies
    obtain ⟨actualInstruction, rest, consuming, _, _⟩ := cursor₁.next rfl
    have admission : ∃ result, consume P (layoutOf P) (.bind x (.alloc ctor args kind)) = .ok result :=
      ⟨actualInstruction, consuming⟩
    obtain ⟨_, _, _, _, argsArity, _, _, _, _, _, _, index, _, shape⟩ := consume_allocation positive consuming
    rw [shape] at consuming
    have liveArgs := consumed_call_live cursor₁ rfl consuming sourceLookup
    have arity : fields.length = ctor.arity := (Own.evalArgs_length ρo originalArgs).trans argsArity
    rcases allocation_step functions main cursor₁ tables ctor args x rfl sourceLookup tokens₁
        fresh scope frameArgs positive ready₁ words₁ real bounded₁ running₁ callers with success | failure
    · obtain ⟨logical, address, next, mem', slots', lists', sourceArgs, frameEffect, tokens,
        restored, trace₂, cursor₂, words₂⟩ := success
      obtain ⟨actualLogical, logicalArgs, effect, state, denPreserved⟩ :=
        allocation_state_after before tables ctor args x fresh scope originalArgs arity positive copies
      have logicalEqual : actualLogical = logical := Option.some.inj (logicalArgs.symm.trans sourceArgs)
      subst actualLogical
      have finalBounds := (frame_allocation_transport (H := copied) (body := {ctor, fields})
        rfl words₁ bounded₁ real address).2
      refine .inl ⟨fields, logical, copied, address, next, mem', slots', lists', _, originalArgs,
        sourceArgs, copies, effect, state, restored, trace₁.trans trace₂, cursor₂, words₂,
        finalBounds, Cfg.Proof.Sub.insert lexical x _, size, rfl, admission, liveArgs, ?_⟩
      exact consumed_call_done (source := {source with rest := .bind x (.alloc ctor args kind) :: tail})
        sourceLookup cursor₁ rfl consuming
        (source.env.insert x (copied.alloc .rc {ctor, fields}).1)
    · obtain ⟨cost, terminal, resource, trace₂, failed⟩ := failure
      exact .inr ⟨2 * (Own.Plain.copies (Own.Plain.heapArgs imm args)).length + cost, terminal, resource,
        trace₁.trans trace₂, failed⟩
  · exact .inr failure


end IxCC.Cfg.Rc.Native
