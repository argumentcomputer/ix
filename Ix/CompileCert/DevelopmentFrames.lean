import Ix.CompileCert.FramePrimitives
import Ix.CompileCert.DevelopmentArity

/-! Placement invariants for the actual development cache. The conditional
invariant does not authorize arbitrary poisoned results from matching keys. -/
namespace Ix.CompileCert.DevelopmentFrames
open Ix (Expr)
open Ix.Compile.Image Ix.Compile.Canon
open SemanticFrames

def InstFrames (state : DevState) : Prop :=
  ∀ (bucket : UInt64) (entry : InstEntry), state.insts[bucket]? = some entry →
    Frames entry.value → Frames entry.body → Frames entry.result.1 ∧ Shell entry.body entry.result.1

theorem empty : InstFrames {} := by
  intro bucket entry found
  simp at found

theorem insert {state : DevState} (good : InstFrames state) (v e : Expr) (k : Nat)
    (result : Expr × Created) (valid : Frames result.1 ∧ Shell e result.1) :
    InstFrames { state with insts := state.insts.insert (instBucket v e k) ⟨v, e, k, result⟩ } := by
  intro bucket entry found hv he
  simp only [Std.HashMap.getElem?_insert] at found
  split at found
  · cases Option.some.inj found; exact valid
  · exact good bucket entry found hv he

theorem probe {state : DevState} (good : InstFrames state) {v e : Expr} {k : Nat}
    (hv : Frames v) (he : Frames e) {result : Expr × Created}
    (found : instProbe state v e k = some result) : Frames result.1 ∧ Shell e result.1 := by
  unfold instProbe at found
  cases hit : state.insts.get? (instBucket v e k) with
  | none => simp only [hit] at found; cases found
  | some entry =>
    simp only [hit] at found
    split at found
    · rename_i exactKeys
      simp only [Bool.and_eq_true, RawExact.exprEq_eq_true, beq_iff_eq] at exactKeys
      cases Option.some.inj found
      have valid := good _ entry hit (exactKeys.2 ▸ hv) (exactKeys.1.2 ▸ he)
      simpa only [exactKeys.1.2] using valid
    · cases found

theorem probe_fits {state : DevState} (good : InstFrames state) {v e : Expr} {k : Nat}
    (hv : Frames v) (he : Frames e) {result : Expr × Created}
    (found : instProbe state v e k = some result) (kind : Ix.SemanticContract.Kind)
    (nonLam : kind ≠ .lam) (matched : fits kind e = true) : fits kind result.1 = true :=
  FramePrimitives.fits_shell kind e result.1 nonLam (probe good hv he found).2 matched

theorem spine (e : Expr) (valid : Frames e) :
    Frames (getAppFnArgs e).1 ∧ ∀ a ∈ (getAppFnArgs e).2, Frames a := by
  induction e
  case app f a hash ih _ =>
    obtain ⟨head, args⟩ := ih valid.1
    refine ⟨head, ?_⟩
    intro x member
    simp only [getAppFnArgs, Array.mem_push] at member
    rcases member with old | rfl
    · exact args x old
    · exact valid.2
  all_goals exact ⟨valid, by simp [getAppFnArgs]⟩

theorem field {s : Ix.Name} {i : Nat} {e out : Expr} (valid : Frames e)
    (found : projCtor? s i e = some out) : Frames out := by
  rcases pair : getAppFnArgs e with ⟨head, args⟩
  have members := (spine e valid).2
  rw [pair] at members
  simp only [projCtor?, pair] at found
  split at found <;> try cases found
  split at found <;> try cases found
  exact members out (Array.mem_of_getElem? found)

private def Valid (p : α → Prop) (action : DevM α) : Prop :=
  ∀ before, InstFrames before → ∀ out after, action.run before = .ok (out, after) →
    InstFrames after ∧ p out

private theorem pureV {p : α → Prop} {value : α} (valid : p value) : Valid p (pure value) := by
  intro before good out after run
  cases Except.ok.inj run; exact ⟨good, valid⟩

private theorem bindV {p : α → Prop} {q : β → Prop} {action : DevM α} {next : α → DevM β}
    (first : Valid p action) (rest : ∀ value, p value → Valid q (next value)) :
    Valid q (action >>= next) := by
  intro before good out after run
  rw [StateT.run_bind] at run
  obtain ⟨⟨value, middle⟩, head, tail⟩ := Loop.except_bind_ok.mp run
  obtain ⟨state, valid⟩ := first before good value middle head
  exact rest value valid middle state out after tail

private theorem weakenV {p q : α → Prop} {action : DevM α} (valid : Valid p action)
    (weaken : ∀ value, p value → q value) : Valid q action := by
  intro before good out after run
  obtain ⟨state, result⟩ := valid before good out after run
  exact ⟨state, weaken out result⟩

private theorem frameV {p : α → Prop} {action : DevM α} (frame : DevelopmentArity.Frame action)
    (value : ∀ before out after, action.run before = .ok (out, after) → p out) : Valid p action := by
  intro before good out after run
  exact ⟨by simpa only [InstFrames, frame run] using good, value before out after run⟩

private theorem forInV (xs : List α) (p : β → Prop) (f : α → β → DevM (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, p b → Valid (fun r => p r.value) (f x b)) :
    ∀ b, p b → Valid p (forIn xs b f) := by
  induction xs with
  | nil => intro b hb; exact pureV hb
  | cons x xs ih =>
    intro b hb
    rw [List.forIn_cons]
    apply bindV (step x (by simp) b hb)
    intro result valid
    cases result with
    | done value => exact pureV valid
    | yield value => exact ih (fun x hx => step x (by simp [hx])) value valid

private theorem arrayForInV (xs : Array α) (p : β → Prop) (f : α → β → DevM (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, p b → Valid (fun r => p r.value) (f x b))
    (b : β) (valid : p b) : Valid p (forIn xs b f) := by
  rw [← Array.forIn_toList]
  exact forInV xs.toList p f (by simpa using step) b valid

private theorem foldV (xs : List α) (p : β → Prop) (f : β → α → DevM β)
    (step : ∀ x ∈ xs, ∀ b, p b → Valid p (f b x)) :
    ∀ b, p b → Valid p (xs.foldlM f b) := by
  induction xs with
  | nil => intro b hb; exact pureV hb
  | cons x xs ih =>
    intro b hb
    rw [List.foldlM_cons]
    exact bindV (step x (by simp) b hb) (fun b hb => ih (fun x hx => step x (by simp [hx])) b hb)

private theorem arrayFoldV (xs : Array α) (p : β → Prop) (f : β → α → DevM β)
    (step : ∀ x ∈ xs, ∀ b, p b → Valid p (f b x))
    (b : β) (valid : p b) : Valid p (xs.foldlM f b) := by
  rw [← Array.foldlM_toList]
  exact foldV xs.toList p f (by simpa using step) b valid

private theorem getV : Valid InstFrames get := by
  intro before good out after run
  cases Except.ok.inj run; exact ⟨good, good⟩

private theorem shareV {p : Expr → Prop} (e : Expr) (valid : p e) : Valid p (share e) :=
  frameV (DevelopmentArity.helperFrames e 0 0).1
    (fun _ _ _ run => (FramePrimitives.share_eq e run).symm ▸ valid)

private theorem liftV (e : Expr) (n k : Nat) (valid : Frames e) : Valid Frames (liftM e n k) :=
  frameV (DevelopmentArity.helperFrames e n k).2.2.1
    (fun _ _ _ run => (FramePrimitives.liftM e n k valid run).1)

private theorem lowerV (e : Expr) (n k : Nat) (valid : Frames e) : Valid Frames (lowerM e n k) :=
  frameV (DevelopmentArity.helperFrames e n k).2.2.2.1
    (fun _ _ _ run => (FramePrimitives.lowerM e n k valid run).1)

theorem shareAppN_run (f : Expr) (args : Array Expr) (hf : Frames f)
    (ha : ∀ a ∈ args, Frames a) {before after : DevState} {out : Expr}
    (good : InstFrames before) (run : (shareAppN f args).run before = .ok (out, after)) :
    InstFrames after ∧ Frames out := by
  have valid : Valid Frames (shareAppN f args) := by
    unfold shareAppN
    apply arrayFoldV args Frames _ ?_ f hf
    intro a member acc held
    exact shareV (Expr.mkApp acc a) ⟨held, ha a member⟩
  exact valid before good out after run

private theorem doneV (v e : Expr) (k : Nat) (result : Expr × Created)
    (valid : Frames result.1 ∧ Shell e result.1) :
    Valid (fun r => Frames r.1 ∧ Shell e r.1) (do
      modify fun state => { state with insts := state.insts.insert (instBucket v e k) ⟨v, e, k, result⟩ }
      pure result) := by
  intro before good out after run
  cases Except.ok.inj run; exact ⟨insert good v e k result valid, valid⟩

private theorem storeV {v e : Expr} {k : Nat} {action : DevM Expr} (created : Created)
    (valid : Valid (fun out => Frames out ∧ Shell e out) action) :
    Valid (fun r => Frames r.1 ∧ Shell e r.1) (do
      let out ← action
      modify fun state => { state with insts := state.insts.insert (instBucket v e k) ⟨v, e, k, (out, created)⟩ }
      pure (out, created)) := bindV valid (fun out h => doneV v e k (out, created) h)

private theorem storePlainV {v e : Expr} {k : Nat} {action : DevM Expr} (created : Created)
    (plain : ∀ out, Shell e out) (valid : Valid Frames action) :
    Valid (fun r => Frames r.1 ∧ Shell e r.1) (do
      let out ← action
      modify fun state => { state with insts := state.insts.insert (instBucket v e k) ⟨v, e, k, (out, created)⟩ }
      pure (out, created)) := storeV created (weakenV valid (fun out h => ⟨h, plain out⟩))

private theorem workers (fuel : Nat) :
    (∀ v k e, Frames v → Frames e →
      Valid (fun r => Frames r.1 ∧ Shell e r.1) (hinst fuel v k e)) ∧
    (∀ f args, Frames f → (∀ a ∈ args, Frames a) → Valid Frames (happ fuel f args)) := by
  induction fuel using Nat.strongRecOn with | ind fuel below =>
  cases fuel with
  | zero =>
    constructor
    · intro _ _ _ _ _ _ _ _ _ run; rw [hinst] at run; cases run
    · intro _ _ _ _ _ _ _ _ run; rw [happ] at run; cases run
  | succ fuel =>
    have ih := below fuel (Nat.lt_succ_self fuel)
    constructor
    · intro v k e hv he
      rw [hinst]
      apply bindV (frameV (DevelopmentArity.helperFrames e 0 k).2.2.2.2.1 (fun _ _ _ _ => trivial))
      intro range _
      split
      · exact pureV ⟨he, FramePrimitives.shell_refl e⟩
      · apply bindV getV
        intro state good
        cases hit : instProbe state v e k with
        | some result =>
          exact pureV (p := fun r : Expr × Created => Frames r.1 ∧ Shell e r.1) (probe good hv he hit)
        | none =>
          simp only
          cases e with
          | bvar i hash =>
            dsimp only
            split
            · exact storePlainV .direct (fun _ => trivial) (liftV v k 0 hv)
            · split
              · exact storePlainV .no (fun _ => trivial) (shareV (Expr.mkBVar (i - 1)) trivial)
              · apply doneV; exact ⟨he, FramePrimitives.shell_refl _⟩
          | app f a hash =>
            dsimp only
            have hs := spine (.app f a hash) he
            rcases eq : getAppFnArgs (.app f a hash) with ⟨head, args⟩
            rw [eq] at hs
            dsimp only at hs ⊢
            refine bindV (arrayForInV args (fun es => ∀ a ∈ es, Frames a) _ ?_ #[] (by simp)) ?_
            · intro a member es held
              apply bindV (ih.1 v k a hv (hs.2 a member))
              rintro ⟨a', created⟩ ha
              apply pureV
              intro x hx
              rcases Array.mem_push.mp hx with old | rfl
              · exact held x old
              · exact ha.1
            · intro args' hargs
              apply bindV (ih.1 v k head hv hs.1)
              rintro ⟨head', created⟩ hh
              dsimp only
              split
              · exact storePlainV .no (fun _ => trivial)
                  (fun b hb o t run => shareAppN_run _ _ hh.1 hargs hb run)
              · exact storePlainV .reduced (fun _ => trivial) (ih.2 _ _ hh.1 (by simpa using hargs))
              · exact storePlainV _ (fun _ => trivial)
                  (fun b hb o t run => shareAppN_run _ _ hh.1 hargs hb run)
          | proj s i x hash =>
            apply bindV (ih.1 v k x hv he)
            rintro ⟨x', created⟩ hx
            dsimp only
            split
            · exact storePlainV .no (fun _ => trivial) (shareV (Expr.mkProj s i x') hx.1)
            · split
              · apply doneV; exact ⟨field hx.1 (by assumption), trivial⟩
              · exact storePlainV .no (fun _ => trivial) (shareV (Expr.mkProj s i x') hx.1)
          | lam n t b bi hash =>
            apply bindV (ih.1 v k t hv he.1); rintro ⟨t', created⟩ ht
            apply bindV (ih.1 v (k + 1) b hv he.2); rintro ⟨b', created⟩ hb
            dsimp only
            split
            · rename_i f hash₁ hash₂
              apply bindV (frameV (DevelopmentArity.helperFrames f 0 0).2.2.2.2.2 (fun _ _ _ _ => trivial))
              intro occurs _
              split
              · exact storePlainV .direct (fun _ => trivial) (lowerV f 1 0 hb.1.1)
              · apply storePlainV (e := .lam n t b bi hash) _ (fun _ => trivial)
                apply shareV; exact ⟨ht.1, hb.1⟩
            · apply storePlainV (e := .lam n t b bi hash) _ (fun _ => trivial)
              apply shareV; exact ⟨ht.1, hb.1⟩
          | forallE n t b bi hash =>
            apply bindV (ih.1 v k t hv he.1); rintro ⟨t', created⟩ ht
            apply bindV (ih.1 v (k + 1) b hv he.2); rintro ⟨b', created⟩ hb
            apply storeV; apply shareV; exact ⟨⟨ht.1, hb.1⟩, rfl, rfl⟩
          | letE n t x b nd hash =>
            apply bindV (ih.1 v k t hv he.1); rintro ⟨t', created⟩ ht
            apply bindV (ih.1 v k x hv he.2.1); rintro ⟨x', created⟩ hx
            apply bindV (ih.1 v (k + 1) b hv he.2.2); rintro ⟨b', created⟩ hb
            apply storeV; apply shareV; exact ⟨⟨ht.1, hx.1, hb.1⟩, rfl, rfl⟩
          | mdata data x hash =>
            cases x with
            | lam n t b bi hash' =>
              dsimp only
              split
              · cases fuel with
                | zero => intro _ _ _ _ run; cases run
                | succ innerFuel =>
                  have inner := (below innerFuel (by omega)).1
                  apply bindV (inner v k t hv he.2.1); rintro ⟨t', created⟩ ht
                  apply bindV (inner v (k + 1) b hv he.2.2); rintro ⟨b', created⟩ hb
                  apply bindV (shareV (p := fun out => out = Expr.mkLam n t' b' bi) _ rfl)
                  rintro x' rfl
                  simp only [pure_bind]
                  apply storeV; apply shareV
                  refine ⟨⟨?_, ht.1, hb.1⟩, rfl⟩
                  intro present
                  obtain ⟨contract, decoded, matched⟩ := he.1 present
                  refine ⟨contract, decoded, ?_⟩
                  have shape : fits contract.kind (Expr.mkLam n t' b' bi) =
                      fits contract.kind (.lam n t b bi hash') := by cases contract.kind <;> rfl
                  exact shape.trans matched
              · rename_i absent
                apply bindV (ih.1 v k _ hv he.2); rintro ⟨x', created⟩ hx
                apply storeV; apply shareV
                exact ⟨⟨fun present => False.elim (absent present), hx.1⟩, rfl⟩
            | _ =>
              apply bindV (ih.1 v k _ hv he.2); rintro ⟨x', created⟩ hx
              apply storeV; apply shareV
              exact ⟨⟨FramePrimitives.mdata_root_shell he.1 hx.2 rfl, hx.1⟩, rfl⟩
          | _ => apply doneV; exact ⟨he, FramePrimitives.shell_refl _⟩
    · intro f args hf ha
      cases f <;> cases args <;> rw [happ.eq_def] <;> dsimp only <;>
        try exact fun b hb o t run => shareAppN_run _ _ hf (fun a h => ha a (List.mem_toArray.mp h)) hb run
      rename_i n ty body bi hash a rest
      apply bindV (ih.1 a 0 body (ha a (by simp)) hf.2)
      rintro ⟨body', created⟩ hbody
      exact ih.2 body' rest hbody.1 (fun x hx => ha x (by simp [hx]))

theorem hinst_run (fuel : Nat) (v : Expr) (k : Nat) (e : Expr) (hv : Frames v) (he : Frames e)
    {before after : DevState} {out : Expr × Created} (good : InstFrames before)
    (run : (hinst fuel v k e).run before = .ok (out, after)) :
    InstFrames after ∧ Frames out.1 ∧ Shell e out.1 :=
  (workers fuel).1 v k e hv he before good out after run

theorem happ_run (fuel : Nat) (f : Expr) (args : List Expr) (hf : Frames f)
    (ha : ∀ a ∈ args, Frames a) {before after : DevState} {out : Expr} (good : InstFrames before)
    (run : (happ fuel f args).run before = .ok (out, after)) : InstFrames after ∧ Frames out :=
  (workers fuel).2 f args hf ha before good out after run

private theorem instantiateWith_run (f : Expr) (args : Array Expr) (hf : Frames f)
    (ha : ∀ a ∈ args, Frames a) {before after : DevState} {out : Expr}
    (good : InstFrames before) (run : instantiateWith before f args = .ok (out, after)) :
    InstFrames after ∧ Frames out := by
  have shared : Valid (fun es => ∀ a ∈ es, Frames a) (args.mapM shareInput) := by
    rw [Array.mapM_eq_foldlM]
    apply arrayFoldV args _ _ ?_ #[] (by simp)
    intro a member acc held
    rw [← bind_pure_comp]
    apply bindV (frameV (DevelopmentArity.helperFrames a 0 0).2.1
      (fun _ _ _ ran => (FramePrimitives.shareInput_eq a ran).symm ▸ ha a member))
    intro out valid
    apply pureV
    intro x hx
    rcases Array.mem_push.mp hx with old | rfl
    · exact held x old
    · exact valid
  exact bindV shared (fun es valid => (workers developFuel).2 f es.toList hf
    (fun a member => valid a (by simpa using member))) before good out after run

/-- Only actual successful calls extend the empty history. Input validity
is supplied; returned validity and cache safety are conclusions. -/
inductive History : DevState → Prop where
  | empty : History {}
  | call {before after : DevState} {f : Expr} {args : Array Expr} {out : Expr}
      (previous : History before) (hf : Frames f) (ha : ∀ a ∈ args, Frames a)
      (run : instantiateWith before f args = .ok (out, after)) : History after

theorem history_sound {state : DevState} (history : History state) : InstFrames state := by
  induction history with
  | empty => exact empty
  | call previous hf ha run ih => exact (instantiateWith_run _ _ hf ha ih run).1

theorem instantiateWith_produced (f : Expr) (args : Array Expr) (hf : Frames f)
    (ha : ∀ a ∈ args, Frames a) {before after : DevState} {out : Expr}
    (history : History before) (run : instantiateWith before f args = .ok (out, after)) :
    Frames out ∧ History after :=
  ⟨(instantiateWith_run f args hf ha (history_sound history) run).2, .call history hf ha run⟩

theorem instantiateWith_fresh (f : Expr) (args : Array Expr) (hf : Frames f)
    (ha : ∀ a ∈ args, Frames a) {after : DevState} {out : Expr}
    (run : instantiateWith {} f args = .ok (out, after)) : Frames out ∧ History after :=
  instantiateWith_produced f args hf ha .empty run

theorem instantiate_fresh (f : Expr) (args : Array Expr) (hf : Frames f)
    (ha : ∀ a ∈ args, Frames a) {out : Expr} (run : instantiate f args = .ok out) : Frames out := by
  cases actual : (happ developFuel f args.toList).run {} with
  | error error => simp [instantiate, StateT.run'_eq, actual, Functor.map, Except.map] at run
  | ok result =>
    have same : result.1 = out := by simpa [instantiate, StateT.run'_eq, actual, Functor.map, Except.map] using run
    exact same ▸ (happ_run developFuel f args.toList hf (by simpa using ha) empty actual).2

/-- Successful actual input inspections give successful inspection of the
same returned result. No annotation-bit, typing or value claim is made. -/
theorem instantiateWith_inspected (f : Expr) (args : Array Expr)
    (hf : ∃ b, Ix.SemanticContract.inspect f = .ok b)
    (ha : ∀ a ∈ args, ∃ b, Ix.SemanticContract.inspect a = .ok b)
    {before after : DevState} {out : Expr} (history : History before)
    (run : instantiateWith before f args = .ok (out, after)) :
    (∃ b, Ix.SemanticContract.inspect out = .ok b) ∧ History after := by
  have result := instantiateWith_produced f args ((inspect_frames_iff f).mp hf)
    (fun a member => (inspect_frames_iff a).mp (ha a member)) history run
  exact ⟨(inspect_frames_iff out).mpr result.1, result.2⟩

theorem instantiateWith_fresh_inspected (f : Expr) (args : Array Expr)
    (hf : ∃ b, Ix.SemanticContract.inspect f = .ok b)
    (ha : ∀ a ∈ args, ∃ b, Ix.SemanticContract.inspect a = .ok b)
    {after : DevState} {out : Expr} (run : instantiateWith {} f args = .ok (out, after)) :
    (∃ b, Ix.SemanticContract.inspect out = .ok b) ∧ History after :=
  instantiateWith_inspected f args hf ha .empty run

end Ix.CompileCert.DevelopmentFrames
