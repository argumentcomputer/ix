import Ix.CompileCert.RewriteArityPrimitives

/-! Actual development-state arity. Exact retained keys do not certify an
arbitrary InstEntry.result; the eventual producer must start from history. -/
namespace Ix.CompileCert.DevelopmentArity
open Ix (Expr)
open Ix.Compile.Image Ix.Compile.Canon
open Ix.CompileCert.RecordSourceShape

def InstArity (st : DevState) : Prop :=
  ∀ (bucket : UInt64) (entry : InstEntry), st.insts[bucket]? = some entry →
    ContractArity entry.value → ContractArity entry.body → ContractArity entry.result.1

theorem empty : InstArity {} := by
  intro bucket entry found
  simp at found

theorem insert {st : DevState} (good : InstArity st) (v e : Expr) (k : Nat)
    (r : Expr × Created) (hr : ContractArity r.1) :
    InstArity { st with insts := st.insts.insert (instBucket v e k) ⟨v, e, k, r⟩ } := by
  intro bucket entry found hv he
  simp only [Std.HashMap.getElem?_insert] at found
  split at found
  · cases Option.some.inj found; exact hr
  · exact good bucket entry found hv he

theorem probe {st : DevState} (good : InstArity st) {v e : Expr} {k : Nat}
    (hv : ContractArity v) (he : ContractArity e) {r : Expr × Created}
    (found : instProbe st v e k = some r) : ContractArity r.1 := by
  unfold instProbe at found
  cases hit : st.insts.get? (instBucket v e k) with
  | none => simp only [hit] at found; cases found
  | some entry =>
    simp only [hit] at found
    split at found
    · rename_i exactKeys
      simp only [Bool.and_eq_true, RawExact.exprEq_eq_true, beq_iff_eq] at exactKeys
      cases Option.some.inj found
      exact good _ entry hit (exactKeys.2 ▸ hv) (exactKeys.1.2 ▸ he)
    · cases found

def Frame (action : DevM α) : Prop :=
  ∀ {before after out}, action.run before = .ok (out, after) → after.insts = before.insts

theorem helperFrames (e : Expr) (n k : Nat) :
    Frame (share e) ∧ Frame (shareInput e) ∧ Frame (liftM e n k) ∧
    Frame (lowerM e n k) ∧ Frame (looseRange e) ∧ Frame (occursM e k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro before after out run
  all_goals first
    | exact (congrArg (fun p => p.2.insts) (Except.ok.inj run)).symm
    | unfold shareInput at run
      dsimp only [StateT.run] at run
      split at run <;> exact (congrArg (fun p => p.2.insts) (Except.ok.inj run)).symm

theorem spine (e : Expr) (h : ContractArity e) :
    ContractArity (getAppFnArgs e).1 ∧ ∀ a ∈ (getAppFnArgs e).2, ContractArity a := by
  induction e
  case app f a hash ih _ =>
    obtain ⟨head, args⟩ := ih h.1
    refine ⟨head, ?_⟩
    intro x member
    simp only [getAppFnArgs, Array.mem_push] at member
    rcases member with old | rfl
    · exact args x old
    · exact h.2
  all_goals exact ⟨h, by simp [getAppFnArgs]⟩

theorem field {s : Ix.Name} {i : Nat} {e out : Expr} (h : ContractArity e)
    (found : projCtor? s i e = some out) : ContractArity out := by
  rcases pair : getAppFnArgs e with ⟨head, args⟩
  have members := (spine e h).2
  rw [pair] at members
  simp only [projCtor?, pair] at found
  split at found <;> try cases found
  split at found <;> try cases found
  exact members out (Array.mem_of_getElem? found)

private def Valid (p : α → Prop) (action : DevM α) : Prop :=
  ∀ before, InstArity before → ∀ out after, action.run before = .ok (out, after) →
    InstArity after ∧ p out

private theorem pureV {p : α → Prop} {v : α} (h : p v) : Valid p (pure v) := by
  intro before good out after run
  cases Except.ok.inj run; exact ⟨good, h⟩

private theorem bindV {p : α → Prop} {q : β → Prop} {a : DevM α} {f : α → DevM β}
    (first : Valid p a) (next : ∀ v, p v → Valid q (f v)) : Valid q (a >>= f) := by
  intro before good out after run
  rw [StateT.run_bind] at run
  obtain ⟨⟨v, middle⟩, head, tail⟩ := Loop.except_bind_ok.mp run
  obtain ⟨state, value⟩ := first before good v middle head
  exact next v value middle state out after tail

private theorem frameV {p : α → Prop} {action : DevM α} (frame : Frame action)
    (value : ∀ before out after, action.run before = .ok (out, after) → p out) : Valid p action := by
  intro before good out after run
  exact ⟨by simpa only [InstArity, frame run] using good, value before out after run⟩

private theorem forInV (xs : List α) (p : β → Prop) (f : α → β → DevM (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, p b → Valid (fun r => p r.value) (f x b)) :
    ∀ b, p b → Valid p (forIn xs b f) := by
  induction xs with
  | nil => intro b hb; exact pureV hb
  | cons x xs ih =>
    intro b hb
    rw [List.forIn_cons]
    apply bindV (step x (by simp) b hb)
    intro r hr
    cases r with
    | done value => exact pureV hr
    | yield value => exact ih (fun x hx => step x (by simp [hx])) value hr

private theorem arrayForInV (xs : Array α) (p : β → Prop) (f : α → β → DevM (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, p b → Valid (fun r => p r.value) (f x b))
    (b : β) (hb : p b) : Valid p (forIn xs b f) := by
  rw [← Array.forIn_toList]
  exact forInV xs.toList p f (by simpa using step) b hb

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
    (b : β) (hb : p b) : Valid p (xs.foldlM f b) := by
  rw [← Array.foldlM_toList]
  exact foldV xs.toList p f (by simpa using step) b hb

theorem shareAppN_run (f : Expr) (args : Array Expr) (hf : ContractArity f)
    (ha : ∀ a ∈ args, ContractArity a) {before after : DevState} {out : Expr}
    (good : InstArity before) (run : (shareAppN f args).run before = .ok (out, after)) :
    InstArity after ∧ ContractArity out := by
  have valid : Valid ContractArity (shareAppN f args) := by
    unfold shareAppN
    apply arrayFoldV args ContractArity _ ?_ f hf
    intro a member acc held
    exact frameV (helperFrames (Expr.mkApp acc a) 0 0).1
      (fun _ _ _ ran => RewriteArityPrimitives.share (Expr.mkApp acc a) ⟨held, ha a member⟩ ran)
  exact valid before good out after run

private theorem getV : Valid InstArity get := by
  intro before good out after run
  cases Except.ok.inj run; exact ⟨good, good⟩
private theorem shareV (e : Expr) (h : ContractArity e) : Valid ContractArity (share e) :=
  frameV (helperFrames e 0 0).1 (fun _ _ _ run => RewriteArityPrimitives.share e h run)
private theorem liftV (e : Expr) (n k : Nat) (h : ContractArity e) : Valid ContractArity (liftM e n k) :=
  frameV (helperFrames e n k).2.2.1 (fun _ _ _ run => RewriteArityPrimitives.liftM e n k h run)
private theorem lowerV (e : Expr) (n k : Nat) (h : ContractArity e) : Valid ContractArity (lowerM e n k) :=
  frameV (helperFrames e n k).2.2.2.1 (fun _ _ _ run => RewriteArityPrimitives.lowerM e n k h run)
private theorem doneV (v e : Expr) (k : Nat) (r : Expr × Created) (h : ContractArity r.1) :
    Valid (fun r => ContractArity r.1)
      (do modify fun st => { st with insts := st.insts.insert (instBucket v e k) ⟨v, e, k, r⟩ }; pure r) := by
  intro before good out after run
  cases Except.ok.inj run; exact ⟨insert good v e k r h, h⟩
private theorem storeV {v e : Expr} {k : Nat} {action : DevM Expr} (c : Created)
    (h : Valid ContractArity action) : Valid (fun r => ContractArity r.1) (do
      let x ← action
      modify fun st => { st with insts := st.insts.insert (instBucket v e k) ⟨v, e, k, (x, c)⟩ }
      pure (x, c)) := bindV h (fun x hx => doneV v e k (x, c) hx)

private theorem workers (fuel : Nat) :
    (∀ v k e, ContractArity v → ContractArity e →
      Valid (fun r => ContractArity r.1) (hinst fuel v k e)) ∧
    (∀ f args, ContractArity f → (∀ a ∈ args, ContractArity a) →
      Valid ContractArity (happ fuel f args)) := by
  induction fuel with
  | zero =>
    constructor
    · intro _ _ _ _ _ _ _ _ _ run; cases run
    · intro _ _ _ _ _ _ _ _ run; cases run
  | succ fuel ih =>
    constructor
    · intro v k e hv he
      rw [hinst]
      apply bindV (frameV (helperFrames e 0 k).2.2.2.2.1 (fun _ _ _ _ => trivial))
      intro range _
      split
      · exact pureV he
      · apply bindV getV
        intro st good
        cases hit : instProbe st v e k with
        | some r => exact pureV (p := fun r : Expr × Created => ContractArity r.1) (probe good hv he hit)
        | none =>
          simp only
          cases e with
          | bvar i hash =>
            dsimp only
            split
            · exact storeV .direct (liftV v k 0 hv)
            · split
              · exact storeV .no (shareV (Expr.mkBVar (i - 1)) trivial)
              · apply doneV; exact he
          | app f a hash =>
            dsimp only
            have hs := spine (.app f a hash) he
            rcases eq : getAppFnArgs (.app f a hash) with ⟨head, args⟩
            rw [eq] at hs
            dsimp only at hs ⊢
            refine bindV (arrayForInV args (fun es => ∀ a ∈ es, ContractArity a) _ ?_ #[] (by simp)) ?_
            · intro a member es held
              apply bindV (ih.1 v k a hv (hs.2 a member))
              rintro ⟨a', c⟩ ha
              apply pureV
              intro x hx
              rcases Array.mem_push.mp hx with old | rfl
              · exact held x old
              · exact ha
            · intro args' hargs
              apply bindV (ih.1 v k head hv hs.1)
              rintro ⟨head', c⟩ hh
              dsimp only
              split
              · exact storeV .no (fun b hb o t run => shareAppN_run _ _ hh hargs hb run)
              · exact storeV .reduced (ih.2 _ _ hh (by simpa using hargs))
              · exact storeV _ (fun b hb o t run => shareAppN_run _ _ hh hargs hb run)
          | proj s i x hash =>
            apply bindV (ih.1 v k x hv he)
            rintro ⟨x', c⟩ hx
            dsimp only
            split
            · exact storeV .no (shareV (Expr.mkProj s i x') hx)
            · split
              · apply doneV; exact field hx (by assumption)
              · exact storeV .no (shareV (Expr.mkProj s i x') hx)
          | lam n t b bi hash =>
            apply bindV (ih.1 v k t hv he.1)
            rintro ⟨t', c⟩ ht
            apply bindV (ih.1 v (k + 1) b hv he.2)
            rintro ⟨b', c⟩ hb
            dsimp only
            split
            · rename_i f hash₁ hash₂
              apply bindV (frameV (helperFrames f 0 0).2.2.2.2.2 (fun _ _ _ _ => trivial))
              intro occurs _
              split
              · exact storeV .direct (lowerV f 1 0 hb.1)
              · apply storeV; apply shareV; exact ⟨ht, hb⟩
            · apply storeV; apply shareV; exact ⟨ht, hb⟩
          | forallE n t b bi hash =>
            apply bindV (ih.1 v k t hv he.1); rintro ⟨t', c⟩ ht
            apply bindV (ih.1 v (k + 1) b hv he.2); rintro ⟨b', c⟩ hb
            apply storeV; apply shareV; exact ⟨ht, hb⟩
          | letE n t x b nd hash =>
            apply bindV (ih.1 v k t hv he.1); rintro ⟨t', c⟩ ht
            apply bindV (ih.1 v k x hv he.2.1); rintro ⟨x', c⟩ hx
            apply bindV (ih.1 v (k + 1) b hv he.2.2); rintro ⟨b', c⟩ hb
            apply storeV; apply shareV; exact ⟨ht, hx, hb⟩
          | mdata data x hash =>
            apply bindV (ih.1 v k x hv he.2); rintro ⟨x', c⟩ hx
            apply storeV; apply shareV; exact ⟨he.1, hx⟩
          | _ => apply doneV; exact he
    · intro f args hf ha
      cases f <;> cases args <;>
        try exact fun b hb o t run => shareAppN_run _ _ hf (fun a h => ha a (List.mem_toArray.mp h)) hb run
      rename_i n ty body bi hash a rest
      rw [happ]
      apply bindV (ih.1 a 0 body (ha a (by simp)) hf.2)
      rintro ⟨body', c⟩ hbody
      exact ih.2 body' rest hbody (fun x hx => ha x (by simp [hx]))

theorem hinst_run (fuel : Nat) (v : Expr) (k : Nat) (e : Expr)
    (hv : ContractArity v) (he : ContractArity e) {before after : DevState} {out : Expr × Created}
    (good : InstArity before) (run : (hinst fuel v k e).run before = .ok (out, after)) :
    InstArity after ∧ ContractArity out.1 :=
  (workers fuel).1 v k e hv he before good out after run

theorem happ_run (fuel : Nat) (f : Expr) (args : List Expr)
    (hf : ContractArity f) (ha : ∀ a ∈ args, ContractArity a) {before after : DevState} {out : Expr}
    (good : InstArity before) (run : (happ fuel f args).run before = .ok (out, after)) :
    InstArity after ∧ ContractArity out :=
  (workers fuel).2 f args hf ha before good out after run

end Ix.CompileCert.DevelopmentArity
