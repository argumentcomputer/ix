import Ix.Cert.RunOwnership
import Ix.CompileCert.PrimaryAddressFrame

/-! # A driver step keeps the resolution

`RunOwnership.StepKeeps`: applying a block's outcome (`applyAuxBlockOutcome`) keeps every
name the driver state resolves at its address, or records the name as failed. Every write
the step makes to the resolution map keeps it so, for every outcome:

* a compiled block's merge (`mergeCompiledBlock`) writes its primary claims, which its
  check (`checkCompiledBlock`) agreed with every name already resolved
  (`Ix.CompileCert.PrimaryAddressFrame`);
* recording failures leaves the map.

With `RunOwnership.scheduleOwnership_of_stepKeeps` this proves
`Obligation.ScheduleOwnership` (`scheduleOwnership`). -/

namespace Ix.Cert.StepKeeps

open Ix.CompileM Ix.Cert.Resolution Ix.Cert.RunOwnership
open Ix.Compile.ExactKey (ExactName)

/-! ## Resolution maps

The driver indexes its resolution maps by `ExactName` but writes them at `Ix.Name` keys,
which unify with `ExactName` only by unfolding it. These lemmas are stated over
`ExactName` keys and applied by unification, so that no rewrite meets the mixed keys. -/

theorem get?_erase_of_ne {t : Std.HashMap ExactName Address} {m n : ExactName} {a : Address}
    (ne : ¬m = n) (h : t.get? n = some a) : (t.erase m).get? n = some a := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase]
  have : (m == n) = false := beq_eq_false_iff_ne.mpr ne
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  rw [← Std.HashMap.get?_eq_getElem?]
  exact h

theorem get?_insert_of_agree {t : Std.HashMap ExactName Address} {m n : ExactName} {v a : Address}
    (agree : m = n → v = a) (h : t.get? n = some a) : (t.insert m v).get? n = some a := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  split
  · rename_i same
    rw [agree (eq_of_beq same)]
  · rw [← Std.HashMap.get?_eq_getElem?]
    exact h

theorem get?_insert_cases {t : Std.HashMap ExactName Address} {m n : ExactName} {v e : Address}
    (h : (t.insert m v).get? n = some e) : (m = n ∧ v = e) ∨ t.get? n = some e := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i same
    exact .inl ⟨eq_of_beq same, Option.some.inj h⟩
  · rw [← Std.HashMap.get?_eq_getElem?] at h
    exact .inr h

/-! ## The relation a step keeps -/

/-- **`c'` keeps `c`'s resolution and moves its failures as `Mono` says.** -/
def KR (c c' : CompileEnv) : Prop := Keeps c c' ∧ Mono c c'

theorem KR.refl (c : CompileEnv) : KR c c := ⟨fun _ _ h => .inl h, Mono.refl c⟩

theorem KR.trans {c₁ c₂ c₃ : CompileEnv} (h₁ : KR c₁ c₂) (h₂ : KR c₂ c₃) : KR c₁ c₃ :=
  ⟨fun n a h => (h₁.1 n a h).elim (fun h => h₂.1 n a h) (fun f => .inr (h₂.2 n f)),
    h₁.2.trans h₂.2⟩

/-- An operation that leaves the resolution map. -/
theorem KR.keep {c c' : CompileEnv} (hn : c'.nameToAddr = c.nameToAddr) (hm : Mono c c') : KR c c' :=
  ⟨fun n a h => .inl (by rw [hn]; exact h), hm⟩

/-- An operation that erases a name from the resolution map while recording it as
failed. -/
theorem KR.erase {c c' : CompileEnv} {m : ExactName} (h₁ : c'.nameToAddr = c.nameToAddr.erase m)
    (hf : c'.ungrounded.contains m = true) (hm : Mono c c') : KR c c' := by
  refine ⟨fun n a h => ?_, hm⟩
  by_cases e : m = n
  · subst e
    exact .inr hf
  · left
    rw [h₁]
    exact get?_erase_of_ne e h

/-- An operation that writes a name's resolution entry at the address the name already
resolves to, if it resolves at all. -/
theorem KR.insert {c c' : CompileEnv} {m : ExactName} {v : Address}
    (h₁ : c'.nameToAddr = c.nameToAddr.insert m v)
    (agree : ∀ a, c.nameToAddr.get? m = some a → a = v) (hm : Mono c c') : KR c c' := by
  refine ⟨fun n a h => .inl ?_, hm⟩
  rw [h₁]
  refine get?_insert_of_agree (fun e => ?_) h
  subst e
  exact (agree a h).symm

/-! ## The pieces of a step -/

/-- **A checked merge keeps the resolution**: it writes the block's primary claims, which
the check agreed with every name already resolved. -/
theorem mergeCompiledBlock_kr {acc : DriverAcc} {lo : Ix.Name} {result : BlockResult}
    {cache : BlockState} (hc : checkCompiledBlock acc.cenv lo result cache = .ok ()) :
    KR acc.cenv (mergeCompiledBlock acc lo result cache).cenv := by
  refine ⟨fun n a h => .inl ?_,
    (mergeCompiledBlock_step acc lo result cache (checkCompiledBlock_content hc)).1.2.2⟩
  rw [Ix.CompileCert.PrimaryAddressFrame.mergeCompiledBlock_primary]
  exact (Ix.CompileCert.PrimaryAddressFrame.checkCompiledBlock_primary_agrees hc).foldl_keeps h

/-! ## A step, by its outcome

The same case analysis as `Resolution.applyAuxBlockOutcome_step`. -/

theorem fst_pure_kr {c : CompileEnv} {d : DriverAcc} {x : Array Ix.Name} {y : Bool} (h : KR c d.cenv) :
    KR c (pure (d, x, y) : Id (DriverAcc × Array Ix.Name × Bool)).1.cenv := h

/-- A loop over registered names, then a return. -/
theorem loopNames_kr {c : CompileEnv} {α : Type} (xs : Array α) (init : Array Ix.Name)
    (f : α → Array Ix.Name → Id (ForInStep (Array Ix.Name)))
    (k : Array Ix.Name → Id (DriverAcc × Array Ix.Name × Bool)) (cont : ∀ L, KR c (k L).1.cenv) :
    KR c (forIn (m := Id) xs init f >>= k).1.cenv :=
  loop_bind xs init f k (fun _ => True) (fun r => KR c r.1.cenv) trivial (fun _ _ _ _ => trivial)
    fun L _ => cont L

/-- A loop over the driver state, then its continuation. -/
theorem loopAcc_kr {c : CompileEnv} {α : Type} (xs : Array α) (init : DriverAcc)
    (f : α → DriverAcc → Id (ForInStep DriverAcc)) (k : DriverAcc → Id DriverAcc)
    (hinit : KR c init.cenv) (body : ∀ x ∈ xs, ∀ s, KR c s.cenv → KR c (f x s).value.cenv)
    (cont : ∀ L, KR c L.cenv → KR c (k L).cenv) : KR c (forIn (m := Id) xs init f >>= k).cenv :=
  loop_bind xs init f k (fun d => KR c d.cenv) (fun d => KR c d.cenv) hinit body cont

/-- A loop body that records a failure, or leaves the resolution map and the failures. -/
local macro "keep_body" : tactic => `(tactic| (intro _ _ s hs; first
  | exact hs.trans (KR.keep rfl (Mono.fail rfl))
  | exact hs.trans (KR.keep rfl (Mono.of_eq rfl))))

/-- A loop over the driver state made of such bodies; the step to its initial state is
left. -/
local macro "keep_loop" : tactic => `(tactic| refine loopAcc_kr _ _ _ _ ?_ (by keep_body) fun _ h => h)

/-- **Applying a compiled block keeps the resolution**: its checked merge, or the record
of its failures. -/
theorem applyAuxBlockOutcome_compiled_kr (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (r : BlockResult) (c : BlockState) :
    KR acc.cenv (applyAuxBlockOutcome acc lo all (.compiled r c)).1.cenv := by
  unfold applyAuxBlockOutcome; simp only [Id.run]
  split
  · refine fst_pure_kr ?_
    keep_loop
    exact KR.refl _
  · rename_i hc
    have merged := mergeCompiledBlock_kr hc
    split
    · exact loopNames_kr _ _ _ _ fun _ => fst_pure_kr merged
    · exact loopNames_kr _ _ _ _ fun _ => loopNames_kr _ _ _ _ fun _ => fst_pure_kr merged

/-- **Applying a failed block keeps the resolution**: it only records its failures. -/
theorem applyAuxBlockOutcome_failed_kr (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (msg : String) : KR acc.cenv (applyAuxBlockOutcome acc lo all (.failed msg)).1.cenv := by
  unfold applyAuxBlockOutcome; simp only [Id.run]
  refine fst_pure_kr ?_
  keep_loop
  exact KR.refl _

/-- **Applying a block's outcome keeps the resolution**, for every outcome. -/
theorem applyAuxBlockOutcome_kr (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (o : AuxBlockOutcome) : KR acc.cenv (applyAuxBlockOutcome acc lo all o).1.cenv := by
  cases o with
  | compiled r c => exact applyAuxBlockOutcome_compiled_kr acc lo all r c
  | failed msg => exact applyAuxBlockOutcome_failed_kr acc lo all msg

/-- **One driver step keeps the resolution.** -/
theorem stepKeeps : StepKeeps := fun acc lo all o => (applyAuxBlockOutcome_kr acc lo all o).1

/-- **Schedule ownership**: every state of the fold's run owns the artifact's resolution
and store. -/
theorem scheduleOwnership : Obligation.ScheduleOwnership :=
  scheduleOwnership_of_stepKeeps stepKeeps

/-- info: 'Ix.Cert.StepKeeps.scheduleOwnership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scheduleOwnership

end Ix.Cert.StepKeeps
