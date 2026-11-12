import IxCC.Cfg.Rc.Proof.Physical.Bridge.IncrementTokens
import IxCC.Rt.Rc.Gen.Proof.ReadyOperations

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Rt.Rc
open IxCC IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Rc.Procs

theorem canDup_live {H : Heap} {location : Nat} (permission : CanDup H (.loc location)) :
    ∃ refs body, H.cell? location = some (.live refs .dyn body) := by
  cases cell : H.cell? location with
  | none => simp [CanDup, dynCount, cell] at permission
  | some c =>
    cases c with
    | dead => simp [CanDup, dynCount, cell] at permission
    | live refs mode body =>
      cases mode with
      | static => simp [CanDup, dynCount, cell] at permission
      | dyn => exact ⟨refs, body, rfl⟩

/-- Duplication is authorized either by a live root or a live parent edge.
The actual instruction can therefore consume a freshly borrowed register.
No target count-capacity hypothesis is needed. -/
theorem increment_ready_tokens
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {x : Fir.Var} {value : RVal}
    (before : Tokens H external held live ρf ρo roots)
    (lookup : ρo.get? x = some value) (permission : CanDup H value)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem (holdRoots external (roots ++ held))
      context base bump limit slots lists)
    {word : Lir.Word} (represented : valueWord addresses value = some word) :
    ∃ H', Own.Plain.evalAction ρo H (.inc x 1) = .ok H' ∧
      Tokens H' external (value :: held) live ρf ρo roots ∧
      (∀ root, H.value? root = H'.value? root) ∧
      ((∃ mem', Gen.AllocatorReady maxClass H' addresses mem'
          (holdRoots external (roots ++ value :: held))
          context base bump limit slots lists ∧
          Lir.eval incProgram 0 [word] mem context = .ok ([], mem')) ∨
        Lir.eval incProgram 0 [word] mem context = .resource .heap) := by
  obtain ⟨H', incremented, balance, values⟩ := inc_root before.balance permission
  have tokens : Tokens H' external (value :: held) live ρf ρo roots := by
    refine ⟨before.den.transport before.exactRoots (fun root _ => values root),
      before.exactRoots, ?_, before.distinct⟩
    intro location
    have counted := balance location
    simp only [Balance, holdRoots, refsIn] at counted ⊢
    omega
  refine ⟨H', by simp [Own.Plain.evalAction, lookup, incremented, Sem.Result.ofOption],
    tokens, values, ?_⟩
  have rebase : (fun location => holdRoots external (roots ++ held) location + refsIn location [value]) =
      holdRoots external (roots ++ value :: held) := by
    funext location
    simp only [holdRoots, refsIn_append, refsIn]
    omega
  by_cases isLocation : ∃ location, value = .loc location
  · obtain ⟨location, rfl⟩ := isLocation
    obtain ⟨refs, body, cell⟩ := canDup_live permission
    have placement : addresses location = some word := represented
    obtain ⟨_, address, mapped, physical⟩ := ready.idle.live.cell location refs .dyn body cell
    by_cases room : refs < Rt.Rc.maxCount
    · obtain ⟨effect, restored, result⟩ := ready.increment_ready cell placement room
      have equal := Option.some.inj (effect.symm.trans incremented)
      rw [equal, rebase] at restored
      exact .inl ⟨_, restored, result⟩
    · have maxed : refs = Rt.Rc.maxCount := by have bounded := physical.bounded; omega
      subst refs
      exact .inr (Gen.increment_max_failure ready.idle cell placement)
  · have immediate : ∀ location, value ≠ .loc location := fun location equal =>
      isLocation ⟨location, equal⟩
    obtain ⟨effect, _, result⟩ := Gen.increment_immediate_entry ready.idle immediate word represented
    have equal : H = H' := Option.some.inj (effect.symm.trans incremented)
    have unchanged : holdRoots external (roots ++ value :: held) = holdRoots external (roots ++ held) := by
      funext location
      simp [holdRoots, refsIn_append, refsIn, immediate location]
    exact .inl ⟨mem, by rw [← equal, unchanged]; exact ready, result⟩

/-- Move the freshly created occurrence into the lexical root list. The
register was already bound by projection; this step only records ownership. -/
theorem Tokens.activate
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {x : Fir.Var}
    {value : RVal} {logical : Fir.Val}
    (before : Tokens H external (value :: held) live ρf ρo roots)
    (fresh : x ∉ live) (lookup : ρo.get? x = some value)
    (denotation : Own.Proof.Den H value logical) :
    Tokens H external held (x :: live) (ρf.insert x logical) ρo (value :: roots) := by
  refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨fresh, before.distinct⟩⟩
  · intro y member
    rcases List.mem_cons.mp member with equal | member
    · subst y
      exact ⟨value, logical, lookup, Src.NatMap.get?_insert_self .., denotation⟩
    · obtain ⟨v, w, ho, hf, hd⟩ := before.den y member
      refine ⟨v, w, ho, ?_, hd⟩
      rw [Src.NatMap.get?_insert_ne _ _ (by intro equal; subst y; exact fresh member)]
      exact hf
  · change Own.evalArgs ρo ((x :: live).map Fir.Arg.var) = some (value :: roots)
    simp only [List.map_cons, Own.evalArgs, Own.evalArg, lookup]
    rw [before.exactRoots]
  · intro location
    have counted := before.balance location
    simp only [Balance, holdRoots, refsIn] at counted ⊢
    omega




end IxCC.Cfg.Rc.Proof.Physical.Bridge
