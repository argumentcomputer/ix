import IxCC.Cfg.Rc.Proof.Physical.Bridge.ProjectionCursor
import IxCC.Cfg.Rc.Proof.Physical.Bridge.BorrowedCursor
import IxCC.Cfg.Rc.Proof.Native.Activation
import IxCC.Cfg.Rc.Proof.Physical.CallResume
import IxCC.Cfg.Rc.Proof.Physical.CheckedPrefix
import IxCC.Cfg.Rc.Proof.Physical.PrefixHeap
import IxCC.Cfg.Rc.Proof.Ordinary
import IxCC.Own.Plain.Proof.Projection
import IxCC.Own.Plain.Proof.Scalars

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC.Rt.Rc
open IxCC IxCC.Cfg.Rc IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Native.Spec IxCC.Rt.Rc.Procs

theorem source_projection {F : Fir.Program} {H : Own.Heap} {external : Nat → Nat}
    {live : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env} {roots : List Own.RVal}
    (denEnv : Own.Plain.EnvDen H live sourceEnv ownedEnv)
    (balance : Own.Rc.Balance H external roots)
    {y i : Nat} {key : Key.CtorKey} (member : y ∈ live) {logical : Fir.Val}
    (evaluation : Fir.evalRhs F sourceEnv (.proj y key i) = .ok logical) :
    ∃ value, Own.evalRhs .rc ({ctors := F.ctors, known := F.known} : Own.Tables)
      ownedEnv H (.proj y key i) = .ok (value, H) ∧
      Own.Proof.Den H value logical ∧ Own.Rc.CanDup H value ∧
      (∀ {imm : List Fir.Var}, Own.Plain.ImmEnv ownedEnv imm →
        imm.contains y = true → Own.Plain.ImmVal value) := by
  obtain ⟨parent, source, ho, hf, hd⟩ := denEnv y member
  simp only [Fir.evalRhs, hf] at evaluation
  cases hc : source.asCtor F.known with
  | none => simp [hc] at evaluation
  | some pair =>
    obtain ⟨key', fields⟩ := pair
    by_cases equal : key' = key
    · subst key'
      have index : fields[i]? = some logical := by
        cases hi : fields[i]? with
        | none => simp [hc, hi, Sem.Result.ofOption] at evaluation
        | some value =>
          have equal : value = logical := by simpa [hc, hi, Sem.Result.ofOption] using evaluation
          simpa [equal] using hi
      obtain ⟨values, view, fieldsDen⟩ := (Own.Plain.Values.asCtor_den F.known hd).1 key fields hc
      obtain ⟨value, field, den⟩ := fieldsDen.get' index
      refine ⟨value, ?_, den, Own.Plain.asCtor_field_canDup balance view (List.mem_of_getElem? field), ?_⟩
      · simp [Own.evalRhs, ho, view, field, Sem.Result.ofOption, Sem.Result.map]
      · intro imm himm hy_imm
        obtain ⟨parent', ho', hp_imm⟩ := himm y (List.contains_iff_mem.mp hy_imm)
        have hpeq : parent' = parent := Option.some.inj (ho'.symm.trans ho)
        subst parent'
        exact Own.Plain.asCtor_field_imm hp_imm view (List.mem_of_getElem? field)
    · simp [hc, equal] at evaluation

/-- Full canonical projection, including Nat successor views. The load or
subtraction first binds a borrowed value; the actual emitted inc1 then creates
its owned occurrence. Both instructions follow the real consumed cursor. -/
theorem projection_activation {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (checked : checkScopedProgram F bodies P = true)
    {pairs : List (Nat × Cfg.Fun)}
    (functions : Nat → Lir.Func) (main : Nat)
    {H : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
    {live imm : List Fir.Var} {sourceEnv : Fir.Env} {ownedEnv : Own.Env} {roots : List Own.RVal}
    {joins : Own.Plain.Joins} {sourceJoins : List Fir.JEntry} {ownedJoins : List Own.Plain.JEntry}
    {x y i : Nat} {key : Key.CtorKey} {body : Fir.Code}
    {sourceFd : Fir.Fun} {fd : Cfg.Fun} {source : Cfg.Frame} {target : Lir.Frame}
    (sourceLookup : F.fun? source.fn = some sourceFd)
    (before : Activation F P pairs (Public.Spec.sourceStage P functions main) H addresses external
      live sourceEnv ownedEnv roots joins sourceJoins ownedJoins (.bind x (.proj y key i) body)
      sourceFd.vars fd source target imm)
    {mem : X86.Memory} {context base bump limit : Lir.Word} {regionBytes : Nat}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (heap : HeapState P pairs H addresses mem external roots context base bump limit regionBytes slots lists)
    {logical : Fir.Val} (evaluation : Fir.evalRhs F sourceEnv (.proj y key i) = .ok logical)
    (callers : List Lir.Frame) :
    (∃ value H' mem' tail charge after,
      Own.evalRhs .rc ({ctors := F.ctors, known := F.known} : Own.Tables)
        ownedEnv H (.proj y key i) = .ok (value, H) ∧
      Sem.Star (Lir.semStep (Public.Spec.sourceStage P functions main))
        {mem, ctx := context, stack := target :: callers} charge
        {mem := mem', ctx := context, stack := after :: callers} ∧
      Activation F P pairs (Public.Spec.sourceStage P functions main) H' addresses external
        (live ++ [x]) (sourceEnv.insert x logical) (ownedEnv.insert x value) (roots ++ [value])
        joins sourceJoins ownedJoins body sourceFd.vars fd
        {source with rest := tail, env := source.env.insert x value} after
        (Own.Plain.nextImm imm x (.proj y key i)) ∧
      HeapState P pairs H' addresses mem' external (roots ++ [value])
        context base bump limit regionBytes slots lists ∧
      H'.size = H.size ∧ (∀ root, H.value? root = H'.value? root)) ∨
    Sem.Fails (Lir.semStep (Public.Spec.sourceStage P functions main))
      {mem, ctx := context, stack := target :: callers} := by
  have scope : x ∉ live ∧ y ∈ live ∧
      Own.Plain.scopeOk (Own.Plain.signatures F) (live ++ [x])
        (Own.Plain.stackArities sourceJoins) body = true := by
    simpa [Own.Plain.scopeOk, Own.Plain.rhsIn, Bool.and_eq_true, and_assoc] using before.scope
  obtain ⟨fresh, member, bodyScope⟩ := scope
  obtain ⟨value, sourceEffect, den, permission, immProp⟩ := source_projection before.canonical.env
    before.canonical.counts member evaluation
  have sub := before.lexical.1
  have fullEffect : Own.evalRhs .rc P.base.tables source.env H (.proj y key i) = .ok (value, H) := by
    rw [generate_tables (checkProgram_parts (checkScopedProgram_parts checked).1).2]
    exact Cfg.Proof.evalRhs_sub_ok sub sourceEffect
  by_cases hy_imm : imm.contains y = true
  · have himm_val : Own.Plain.ImmVal value := immProp before.canonical.immOk hy_imm
    have atBind : At F P source ownedEnv ownedJoins
        (.bind x (.proj y key i) (Own.Plain.lowerCode (live ++ [x]) joins body
          (Own.Plain.nextImm imm x (.proj y key i)))) := by
      have layout := before.layout
      dsimp only [Own.Plain.lowerCode] at layout
      rw [if_pos hy_imm] at layout
      exact layout
    obtain ⟨tail, head, continuation⟩ := atBind.bind_continuation
    have real := checked_bind_real checked atBind sourceLookup (by rfl)
    rcases projection_frame before.frame heap.ready.idle.live heap.compatible heap.ordered head real
        fullEffect before.running context callers with projected | failed
    · obtain ⟨after, running, projectTrace, projectFrame, fused⟩ := projected
      have balance : Own.Rc.Balance H external (roots ++ [value]) :=
        Own.Plain.balance_append_comm (show Own.Rc.Balance H external ([value] ++ roots) from
          Own.Plain.balance_immediate before.canonical.counts himm_val)
      have state := before.canonical.bind_rhs x (.proj y key i) fresh (fun _ => himm_val)
        den balance (fun _ _ => rfl)
      have unchanged : Own.Rc.holdRoots external (roots ++ [value]) = Own.Rc.holdRoots external roots := by
        funext location
        simp [Own.Rc.holdRoots, Own.Rc.refsIn_append, Own.Rc.refsIn, himm_val location]
      exact .inl ⟨value, H, mem, tail, 0, after, sourceEffect, projectTrace,
        ⟨state, continuation value, projectFrame, bodyScope, running, fused⟩,
        ⟨by rw [unchanged]; exact heap.ready, heap.ordered, heap.compatible, heap.extent⟩,
        rfl, fun _ => rfl⟩
    · exact .inr failed
  · have atBind : At F P source ownedEnv ownedJoins
        (.bind x (.proj y key i) (.act (.inc x 1) (Own.Plain.lowerCode (live ++ [x]) joins body
          (Own.Plain.nextImm imm x (.proj y key i))))) := by
      have layout := before.layout
      dsimp only [Own.Plain.lowerCode] at layout
      rw [if_neg hy_imm] at layout
      exact layout
    obtain ⟨borrowedTail, head, continuation⟩ := atBind.bind_continuation
    have real := checked_bind_real checked atBind sourceLookup (by rfl)
    rcases projection_frame before.frame heap.ready.idle.live heap.compatible heap.ordered head real
        fullEffect before.running context callers with projected | failed
    · obtain ⟨middle, middleRunning, projectTrace, projectFrame, _⟩ := projected
      let borrowed : Cfg.Frame := {source with rest := borrowedTail, env := source.env.insert x value}
      have prefixAt : At F P borrowed (ownedEnv.insert x value) ownedJoins
          (Own.Plain.actionPrefix [.inc x 1] (Own.Plain.lowerCode (live ++ [x]) joins body
            (Own.Plain.nextImm imm x (.proj y key i)))) := continuation value
      obtain ⟨dummy, tail, prefixHead, nextAt, absent⟩ :=
        checked_prefix_cursor checked prefixAt sourceLookup projectFrame.words
      have markerHead : borrowed.rest = marker P.base.size dummy (.inc x 1) :: tail := by
        simpa [encodePrefix] using prefixHead
      have original : Tokens H external [] live sourceEnv ownedEnv roots := Tokens.ofState before.canonical
      have borrowedTokens := (Tokens.extend original sub).borrow x value fresh
      have ready : Gen.AllocatorReady maxClass H addresses mem (Own.Rc.holdRoots external (roots ++ []))
          context base bump limit slots lists := by simpa using heap.ready
      rcases borrowed_marker_step functions main projectFrame.cursor markerHead projectFrame.lookup borrowedTokens
          (Src.NatMap.get?_insert_self ..) permission ready projectFrame.words
          (absent dummy (by omega)) middleRunning callers with incremented | failed
      · obtain ⟨H', mem', action, tokens, restored, incrementTrace, nextCursor, words, values⟩ := incremented
        let after : Lir.Frame := {middle with pos := middle.pos+1, env := middle.env.insert dummy 1, dsts := []}
        have size : H'.size = H.size := action_size action
        have balance : Own.Rc.Balance H' external (roots ++ [value]) :=
          Own.Rc.balance_hold.mpr (by simpa using tokens.balance)
        have den' : Own.Proof.Den H' value logical := by
          change H'.value? value = some logical
          rw [← values value]
          exact den
        have state := before.canonical.bind_rhs x (.proj y key i) fresh
          (fun hr => False.elim (hy_imm hr)) den' balance (fun root _ => values root)
        have consuming : consume P (layoutOf P) (marker P.base.size dummy (.inc x 1)) =
            .ok (.bind dummy (.fir (.call P.base.size [.var x, .lit (.nat 1)]))) :=
          IxCC.Cfg.Rc.Proof.Physical.Bridge.consume_increment P (layoutOf P) dummy x
        have fused := consumed_call_done projectFrame.lookup projectFrame.cursor markerHead consuming borrowed.env
        refine .inl ⟨value, H', mem', tail, 2, after, sourceEffect, ?_,
          ⟨state, nextAt,
            ⟨projectFrame.lookup, nextCursor, words, ?_, projectFrame.compatible⟩,
            bodyScope, rfl, fused⟩,
          ⟨by simpa using restored, (Own.Plain.action_shape heap.ordered action).1,
            heap.compatible.evalAction action, heap.extent⟩, size, values⟩
        · simpa only [Nat.zero_add] using projectTrace.trans incrementTrace
        · rw [size]
          exact projectFrame.bounded
      · obtain ⟨cost, final, resource, trace, failure⟩ := failed
        exact .inr ⟨_, final, resource, projectTrace.trans trace, failure⟩
    · exact .inr failed



end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
