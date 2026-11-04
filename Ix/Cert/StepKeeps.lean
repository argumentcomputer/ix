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
`Obligation.ScheduleOwnership` (`scheduleOwnership`).

A step also keeps every blob with its bytes (`stepBlobs`): only a merge writes blobs, it folds
the block's blobs into the store (`mergeCompiledBlock_blobs`), and its check refused a block
blob the store holds with other bytes (`checkCompiledBlock_blobs`, `fold_insert_exact`). -/

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

/-- `c'` holds every blob `c` holds, with the same bytes. -/
def BlobsGrow (c c' : CompileEnv) : Prop := ∀ a v, c.blobs.get? a = some v → c'.blobs.get? a = some v

/-- An inserting fold keeps every key of its start. -/
theorem fold_insert_keep {m src : Std.HashMap Address ByteArray} {a : Address} (h : m.contains a = true) :
    (src.fold (fun m k v => m.insert k v) m).contains a = true := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  suffices key : ∀ (l : List (Address × ByteArray)) (m : Std.HashMap Address ByteArray), m.contains a = true →
      (l.foldl (fun m p => m.insert p.1 p.2) m).contains a = true from key _ _ h
  intro l
  induction l with
  | nil => intro _ h; exact h
  | cons p l ih =>
    intro m h
    exact ih _ (by rw [Std.HashMap.contains_insert, h, Bool.or_true])

/-- An inserting fold holds every key of its source. -/
theorem fold_insert_add {m src : Std.HashMap Address ByteArray} {a : Address} (h : src.contains a = true) :
    (src.fold (fun m k v => m.insert k v) m).contains a = true := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (show (src.get? a).isSome = true by
      rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]; exact h)
  have hm : (a, b) ∈ src.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]; exact hb
  suffices key : ∀ (l : List (Address × ByteArray)) (m : Std.HashMap Address ByteArray), (a, b) ∈ l →
      (l.foldl (fun m p => m.insert p.1 p.2) m).contains a = true from key _ _ hm
  have keep : ∀ (l : List (Address × ByteArray)) (m : Std.HashMap Address ByteArray), m.contains a = true →
      (l.foldl (fun m p => m.insert p.1 p.2) m).contains a = true := by
    intro l
    induction l with
    | nil => intro _ h; exact h
    | cons p l ih =>
      intro m h
      exact ih _ (by rw [Std.HashMap.contains_insert, h, Bool.or_true])
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons p l ih =>
    intro m hp
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact keep _ _ Std.HashMap.contains_insert_self
    · exact ih _ hp

/-- **An inserting fold over consistent writes holds each write**: where writes with one key
carry one value, the fold maps each write's key to its value. -/
theorem foldl_insert_consistent {α β γ : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (key : γ → α) (val : γ → β) (g : Std.HashMap α β → γ → Std.HashMap α β)
    (hg : ∀ t x, g t x = t.insert (key x) (val x)) :
    ∀ (L : List γ) (t : Std.HashMap α β), (∀ p ∈ L, ∀ q ∈ L, key p = key q → val p = val q) →
      ∀ p ∈ L, (L.foldl g t).get? (key p) = some (val p) := by
  have keep : ∀ (L : List γ) (t : Std.HashMap α β) (k : α), (∀ q ∈ L, key q ≠ k) →
      (L.foldl g t).get? k = t.get? k := by
    intro L
    induction L with
    | nil => intro t k _; rfl
    | cons q L ih =>
      intro t k hq
      rw [List.foldl_cons, ih _ k (fun r hr => hq r (List.mem_cons_of_mem _ hr)), hg,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      have : (key q == k) = false := beq_eq_false_iff_ne.mpr (hq q List.mem_cons_self)
      simp only [this, Bool.false_eq_true, ↓reduceIte]
  intro L
  induction L with
  | nil => intro _ _ p hp; cases hp
  | cons x L ih =>
    intro t hc p hp
    rw [List.foldl_cons]
    by_cases h : ∃ q ∈ L, key q = key p
    · obtain ⟨q, hq, e⟩ := h
      rw [← e, hc p hp q (List.mem_cons_of_mem _ hq) e.symm]
      exact ih _ (fun p' hp' q' hq' => hc p' (List.mem_cons_of_mem _ hp') q' (List.mem_cons_of_mem _ hq'))
        q hq
    · rcases List.mem_cons.mp hp with rfl | hp'
      · rw [keep L _ _ (fun q hq e => h ⟨q, hq, e⟩), hg, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert_self]
      · exact absurd ⟨p, hp', rfl⟩ h


/-- An inserting fold over writes that agree with each other and with the start's store:
the start's entries stay, and each write's key holds its value. -/
theorem fold_insert_exact {m src : Std.HashMap Address ByteArray} (ag : Agrees m src.toList) :
    (∀ a v, m.get? a = some v → (src.fold (fun m k v => m.insert k v) m).get? a = some v) ∧
      ∀ a v, src.get? a = some v → (src.fold (fun m k v => m.insert k v) m).get? a = some v := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  have absent : ∀ (l : List (Address × ByteArray)) (t : Std.HashMap Address ByteArray) (k : Address),
      (∀ q ∈ l, q.1 ≠ k) → (l.foldl (fun m p => m.insert p.1 p.2) t).get? k = t.get? k := by
    intro l
    induction l with
    | nil => intro t k _; rfl
    | cons q l ih =>
      intro t k hq
      rw [List.foldl_cons, ih _ k (fun r hr => hq r (List.mem_cons_of_mem _ hr)),
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.get?_eq_getElem?]
      have : (q.1 == k) = false := beq_eq_false_iff_ne.mpr (hq q List.mem_cons_self)
      simp only [this, Bool.false_eq_true, ↓reduceIte]
  have added : ∀ p ∈ src.toList, (src.toList.foldl (fun m p => m.insert p.1 p.2) m).get? p.1 = some p.2 :=
    foldl_insert_consistent (fun p : Address × ByteArray => p.1) (fun p => p.2) _
      (fun _ _ => rfl) _ _ (fun p hp q hq e => ag.own p.1 p.2 q.2 hp (e ▸ hq))
  refine ⟨fun a v h => ?_, fun a v h => ?_⟩
  · by_cases hin : ∃ q ∈ src.toList, q.1 = a
    · obtain ⟨q, hq, rfl⟩ := hin
      rw [added q hq, ag.old q.1 q.2 hq v h]
    · rw [absent _ _ a fun q hq e => hin ⟨q, hq, e⟩]
      exact h
  · have hm : (a, v) ∈ src.toList := by
      rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]; exact h
    exact added (a, v) hm

/-- **An inserting fold holds the source's entries**, whatever store it starts from. -/
theorem fold_insert_last {m src : Std.HashMap Address ByteArray} {a : Address} {v : ByteArray}
    (h : src.get? a = some v) : (src.fold (fun m k v => m.insert k v) m).get? a = some v := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  have hm : (a, v) ∈ src.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]; exact h
  exact foldl_insert_consistent (fun p : Address × ByteArray => p.1) (fun p => p.2) _ (fun _ _ => rfl) _ _
    (fun p hp q hq e => by
      rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hp hq
      rw [e, hq] at hp
      exact (Option.some.inj hp).symm) (a, v) hm

/-- A merge runs only after `checkCompiledBlock`, whose blob check covers the block's blobs. -/
theorem checkCompiledBlock_blobs {cenv : CompileEnv} {lo : Ix.Name} {result : BlockResult}
    {cache : BlockState} (h : checkCompiledBlock cenv lo result cache = .ok ()) :
    Agrees cenv.blobs cache.blockBlobs.toList := by
  unfold checkCompiledBlock at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · unfold checkBlockContent at h
    split at h
    · unfold checkBlobContent at h
      split at h
      · exact checkAnonymousWrites_agrees (by assumption)
      · cases h
    · cases h

/-- **`c'` keeps `c`'s resolution, moves its failures as `Mono` says, and keeps its
blobs.** -/
def KR (c c' : CompileEnv) : Prop := Keeps c c' ∧ Mono c c' ∧ BlobsGrow c c'

theorem KR.refl (c : CompileEnv) : KR c c := ⟨fun _ _ h => .inl h, Mono.refl c, fun _ _ h => h⟩

theorem KR.trans {c₁ c₂ c₃ : CompileEnv} (h₁ : KR c₁ c₂) (h₂ : KR c₂ c₃) : KR c₁ c₃ :=
  ⟨fun n a h => (h₁.1 n a h).elim (fun h => h₂.1 n a h) (fun f => .inr (h₂.2.1 n f)),
    h₁.2.1.trans h₂.2.1, fun a v h => h₂.2.2 a v (h₁.2.2 a v h)⟩

/-- An operation that leaves the resolution map and grows the blobs. -/
theorem KR.grow {c c' : CompileEnv} (hn : c'.nameToAddr = c.nameToAddr) (hm : Mono c c')
    (hb : BlobsGrow c c') : KR c c' :=
  ⟨fun n a h => .inl (by rw [hn]; exact h), hm, hb⟩

/-- An operation that leaves the resolution map and the blobs. -/
theorem KR.keep {c c' : CompileEnv} (hn : c'.nameToAddr = c.nameToAddr) (hm : Mono c c')
    (hb : c'.blobs = c.blobs := by rfl) : KR c c' :=
  KR.grow hn hm fun a v h => by rw [hb]; exact h

/-- An operation that erases a name from the resolution map while recording it as
failed. -/
theorem KR.erase {c c' : CompileEnv} {m : ExactName} (h₁ : c'.nameToAddr = c.nameToAddr.erase m)
    (hf : c'.ungrounded.contains m = true) (hm : Mono c c') (hb : c'.blobs = c.blobs := by rfl) :
    KR c c' := by
  refine ⟨fun n a h => ?_, hm, fun a v h => by rw [hb]; exact h⟩
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
    (agree : ∀ a, c.nameToAddr.get? m = some a → a = v) (hm : Mono c c')
    (hb : c'.blobs = c.blobs := by rfl) : KR c c' := by
  refine ⟨fun n a h => .inl ?_, hm, fun a v h => by rw [hb]; exact h⟩
  rw [h₁]
  refine get?_insert_of_agree (fun e => ?_) h
  subst e
  exact (agree a h).symm

set_option hygiene false in
/-- `mergeCompiledBlock`'s loops after its first write: none touches the blobs. -/
local macro "blobs_tail" held:term : tactic => `(tactic| (
  refine loop_bind (P := fun d : DriverAcc => d.cenv.blobs = goal)
    (I := fun c : CompileEnv => c.blobs = goal) _ _ _ _ $held ?_ ?_
  · intro _ _ _ h; split <;> exact h
  · intro L' hL'
    split
    · refine loop_bind (P := fun d : DriverAcc => d.cenv.blobs = goal)
        (I := fun c : CompileEnv => c.blobs = goal) _ _ _ _ hL' ?_ ?_
      · intro cls _ s hs
        exact forIn_inv_array (fun c : CompileEnv => c.blobs = goal) _ cls (by intros; assumption) s hs
      · intro _ h; exact h
    · exact hL'))

/-- **A merge's blobs are the block's folded into the state's.** -/
theorem mergeCompiledBlock_blobs (acc : DriverAcc) (lo : Ix.Name) (result : BlockResult) (cache : BlockState) :
    (mergeCompiledBlock acc lo result cache).cenv.blobs =
      cache.blockBlobs.fold (fun m k v => m.insert k v) acc.cenv.blobs := by
  let goal := cache.blockBlobs.fold (fun m k v => m.insert k v) acc.cenv.blobs
  change _ = goal
  unfold mergeCompiledBlock
  simp only [Id.run]
  split
  · split
    · blobs_tail rfl
    · blobs_tail rfl
  · refine loop_bind (P := fun d : DriverAcc => d.cenv.blobs = goal)
      (I := fun c : CompileEnv => c.blobs = goal) _ _ _ _ rfl ?_ ?_
    · intro _ _ _ h; split <;> exact h
    · intro L hL
      blobs_tail hL

/-! ## The pieces of a step -/

/-- **A checked merge keeps the resolution**: it writes the block's primary claims, which
the check agreed with every name already resolved. -/
theorem mergeCompiledBlock_kr {acc : DriverAcc} {lo : Ix.Name} {result : BlockResult}
    {cache : BlockState} (hc : checkCompiledBlock acc.cenv lo result cache = .ok ()) :
    KR acc.cenv (mergeCompiledBlock acc lo result cache).cenv := by
  refine ⟨fun n a h => .inl ?_,
    (mergeCompiledBlock_step acc lo result cache (checkCompiledBlock_content hc)).1.2.2,
    fun a v h => by rw [mergeCompiledBlock_blobs]; exact (fold_insert_exact (checkCompiledBlock_blobs hc)).1 a v h⟩
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

/-- **One driver step keeps the blobs.** -/
theorem stepBlobs (acc : DriverAcc) (lo : Ix.Name) (all : Ix.Set Ix.Name) (o : AuxBlockOutcome) :
    BlobsGrow acc.cenv (applyAuxBlockOutcome acc lo all o).1.cenv :=
  (applyAuxBlockOutcome_kr acc lo all o).2.2

/-- **Schedule ownership**: every state of the fold's run owns the artifact's resolution
and store. -/
theorem scheduleOwnership : Obligation.ScheduleOwnership :=
  scheduleOwnership_of_stepKeeps stepKeeps

/-- info: 'Ix.Cert.StepKeeps.scheduleOwnership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scheduleOwnership

end Ix.Cert.StepKeeps
