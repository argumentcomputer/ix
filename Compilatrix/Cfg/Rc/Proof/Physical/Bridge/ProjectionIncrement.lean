import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ProjectionStep
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ReadyInstructions
import Compilatrix.Own.Plain.Proof.Unfold
import Compilatrix.Own.Plain.Proof.Values

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Rc.Procs Compilatrix.Cfg.Rc.Native

/-- The field has a source denotation because the actual live parent does.
The heap model's header evidence is used here; no machine header load occurs. -/
theorem projection_denotation
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    {y location refs i : Nat} {body : Own.Body} {value : RVal}
    (member : y ∈ live) (lookup : ρo.get? y = some (.loc location))
    (cell : H.cell? location = some (.live refs .dyn body))
    (field : body.fields[i]? = some value) :
    ∃ logical, Own.Proof.Den H value logical := by
  obtain ⟨parent, source, parentLookup, _, den⟩ := before.den y member
  have equal : parent = .loc location := Option.some.inj (parentLookup.symm.trans lookup)
  subst parent
  obtain ⟨refs', mode', body', values, cell', _, fields⟩ := Own.Proof.den_loc den
  have equal := cell.symm.trans cell'
  simp only [Option.some.injEq, Cell.live.injEq] at equal
  rcases equal with ⟨rfl, rfl, rfl⟩
  obtain ⟨logical, _, denotation⟩ := (Own.Plain.Values.dens_of_toFirList (by omega) fields).get field
  exact ⟨logical, denotation⟩

/-- Execute the real field load followed by the real inc1 caller instruction.
The first step binds a borrowed value, and the second creates exactly one
owned occurrence. Either complete allocator readiness is restored or the
actual maximal-count branch reaches resource.heap. -/
theorem projection_increment
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    {y location refs : Nat} {body : Own.Body}
    (member : y ∈ live) (lookup : ρo.get? y = some (.loc location))
    (cell : H.cell? location = some (.live refs .dyn body))
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : AllocatorReady H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {P : Lir.Program} {wrapper procedure dummy bound : Nat}
    (wrapperLookup : P.funcs[wrapper]? = some (incrementWrapper procedure))
    (procedureLookup : P.funcs[procedure]? = some Rt.Rc.Procs.inc)
    (caller : Lir.Frame) (callers : List Lir.Frame)
    {function : Lir.Func} {block : Lir.Block}
    (functionLookup : P.funcs[caller.fn]? = some function)
    (blockLookup : function.blocks[caller.label]? = some block)
    (x i : Nat) (value : RVal) (fresh : x ∉ live)
    (field : body.fields[i]? = some value) (tables : Own.Tables)
    (positions : caller.pos + 1 < block.body.size)
    (projection : block.body[caller.pos] = .assign x
      (.load .w64 .zero (Rt.Lower.mem y ((8+8*i : Nat) : Int))))
    (increment : block.body[caller.pos+1] = .call [dummy] wrapper [.v x, .imm 3])
    (registers : EnvWordsBelow addresses bound ρo caller.env)
    (parentReal : y < bound) (real : x < bound) (reserved : bound ≤ dummy) :
    ∃ word logical H', valueWord addresses value = some word ∧
      Own.evalRhs .rc tables ρo H (.proj y body.ctor.key i) = .ok (value, H) ∧
      Own.Plain.evalAction (ρo.insert x value) H (.inc x 1) = .ok H' ∧
      (∀ (program : Own.Plain.Program) (fuel : Nat) (joins : List Own.Plain.JEntry)
          (code : Own.Plain.Code), program.tables = tables →
        Own.Plain.eval program fuel ρo joins H
          (.bind x (.proj y body.ctor.key i) (.act (.inc x 1) code)) =
        Own.Plain.eval program fuel (ρo.insert x value) joins H' code) ∧
      Tokens H' external (value :: held) live ρf (ρo.insert x value) roots ∧
      Own.Proof.Den H' value logical ∧
      Tokens H' external held (x :: live) (ρf.insert x logical) (ρo.insert x value) (value :: roots) ∧
      ((∃ mem', AllocatorReady H' addresses mem'
          (holdRoots external (roots ++ value :: held))
          context base bump limit slots lists ∧
          Sem.Star (Lir.semStep P)
            {mem, ctx := context, stack := caller :: callers} 2
            {mem := mem', ctx := context,
              stack := {caller with
                pos := caller.pos+2
                env := (caller.env.insert x word).insert dummy 1
                dsts := []} :: callers} ∧
          EnvWordsBelow addresses bound (ρo.insert x value)
            ((caller.env.insert x word).insert dummy 1)) ∨
        Sem.Reaches (Lir.semStep P)
          {mem, ctx := context, stack := caller :: callers} 2 (.resource .heap)) := by
  obtain ⟨_, address, placement, physical⟩ := ready.idle.live.cell location refs .dyn body cell
  obtain ⟨parentWord, parentRep, parentRegister⟩ := registers y (.loc location) parentReal lookup
  have equal : parentWord = address := Option.some.inj (parentRep.symm.trans placement)
  subst parentWord
  obtain ⟨word, represented, source, load, borrowed, words, permission⟩ :=
    projection_step before lookup cell physical registers parentRegister x i value fresh field tables context
      functionLookup blockLookup (by omega) projection
  let next : Lir.Frame := {caller with pos := caller.pos+1, env := caller.env.insert x word}
  obtain ⟨H', action, tokens, values, outcome⟩ := increment_ready_instruction borrowed
    (Src.NatMap.get?_insert_self ..) permission ready wrapperLookup procedureLookup next callers
      functionLookup blockLookup positions increment words real reserved
  obtain ⟨logical, denotes⟩ := projection_denotation before member lookup cell field
  have denotes' : Own.Proof.Den H' value logical := by
    change H'.value? value = some logical
    rw [← values value]
    exact denotes
  have sourceRun : ∀ (program : Own.Plain.Program) (fuel : Nat) (joins : List Own.Plain.JEntry)
      (code : Own.Plain.Code), program.tables = tables →
      Own.Plain.eval program fuel ρo joins H
        (.bind x (.proj y body.ctor.key i) (.act (.inc x 1) code)) =
      Own.Plain.eval program fuel (ρo.insert x value) joins H' code := by
    intro program fuel joins code tablesEqual
    rw [Own.Plain.eval_bindRhs program fuel ρo joins H x (.proj y body.ctor.key i)
      (.act (.inc x 1) code) (by intro f args equal; cases equal)]
    have rhs : Own.Plain.evalRhs program.tables ρo H (.proj y body.ctor.key i) = .ok (value, H) := by
      simpa only [Own.Plain.evalRhs, tablesEqual] using source
    rw [rhs, Sem.Result.bind_ok]
    rw [Own.Plain.eval_act, action, Sem.Result.bind_ok]
  refine ⟨word, logical, H', represented, source, action, sourceRun, tokens, denotes',
    tokens.activate fresh (Src.NatMap.get?_insert_self ..) denotes', ?_⟩
  rcases outcome with ⟨mem', restored, trace, registers'⟩ | failure
  · refine .inl ⟨mem', restored, ?_, registers'⟩
    have joined := (Sem.Star.single (Lir.semStep_next.mpr load)).trans trace
    simpa only [next, Bool.toNat_false, Nat.zero_add, Nat.add_assoc] using joined
  · have joined := Sem.Reaches.star (Sem.Star.single (Lir.semStep_next.mpr load)) failure
    exact .inr (by simpa only [next, Bool.toNat_false, Nat.zero_add] using joined)



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
