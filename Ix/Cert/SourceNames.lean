import Ix.Cert.CtxAgree
import Ix.Cert.ReaderUnits

/-! # Generated and ordinary names before Source collapse

Both in-process generator rungs emit nonempty declarations whose names are
derived keys. Successful Source lowering therefore classifies its raw
generated prefix. The production fiberAliasAt map has only ordinary keys
in its range, so actual conversion, hint replacement, alias substitution
and canonicalization leave ordinary declarations' names non-derived.

These are producer facts, independent of checker acceptance. Arbitrary
FiberMap values need not preserve ordinary keys. Retained generated-index
alignment, duplicate/drop replay and projection-iota level consistency
remain separate obligations; no distinctness or raw/kept equality is claimed.
-/

namespace Ix.Cert.SourceNames

open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Frontend.InModel Ix.LeanIngress

theorem ofName_not_aux (n : Ix.Kernel.Name) : (Ix.Kernel.Key.ofName n).isAux = false := by
  unfold Ix.Kernel.Key.ofName
  split <;> rfl

theorem fiberAliasAt_not_aux {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    {n : Ix.Kernel.Name} {k : Key .source} (h : (fiberAliasAt ixe roles)[n]? = some k) :
    k.isAux = false := by
  have hc : (fiberAliasAt ixe roles).contains n = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, h]; rfl
  unfold fiberAliasAt at hc
  rw [Std.HashMap.contains_ofList] at hc
  obtain ⟨e, he, hen⟩ : ∃ e ∈ (sourceAddrs ixe).toList.filterMap
      (aliasEntryAt roles ((fiberMembers (sourceAddrs ixe)).map
        fun _ ns => (fiberRep ns, ns.filterMap roleOf))), e.1 = n := by simpa using hc
  obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
  have pn : p.1 = n := (aliasEntryAt_fst hpe).symm.trans hen
  have ha : (sourceAddrs ixe)[n]? = some p.2 := by
    rw [← pn]; exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
  rcases fiberAliasAt_rep_addr ha h with ⟨name, _, rfl⟩ | ⟨role, rfl⟩
  · exact ofName_not_aux name
  · rfl

theorem subst_not_aux {ρ : FiberMap}
    (range : ∀ (n : Ix.Kernel.Name) (k : Key .source), ρ[n]? = some k → k.isAux = false)
    {k : Key .source} (hk : k.isAux = false) : (Key.subst ρ k).isAux = false := by
  cases k with
  | «role» r => rfl
  | aux => cases hk
  | id n =>
    simp only [Key.subst]
    cases h : ρ[n]? with
    | none => rfl
    | some k => exact range n k h

namespace Generated

variable {α β σ ε : Type}

class Safe (α : Type) where
  holds : α → Prop

instance (priority := 10) (α : Type) : Safe α := ⟨fun _ => True⟩
instance : Safe (Declaration md) := ⟨fun d => d.isGenerated = true⟩
instance : Safe (Ix.Kernel.ConstantInfo md) := ⟨fun ci => ci.name.isAux = true⟩
instance (priority := 1100) : Safe (Key md × Nat × Ix.Kernel.Expr md × List Nat) := ⟨fun x => x.1.isAux = true⟩
instance [Safe α] : Safe (Array α) := ⟨fun xs => ∀ x ∈ xs, Safe.holds x⟩
instance [Safe α] : Safe (List α) := ⟨fun xs => ∀ x ∈ xs, Safe.holds x⟩
instance [Safe α] [Safe β] : Safe (α × β) := ⟨fun x => Safe.holds x.1 ∧ Safe.holds x.2⟩
instance [Safe α] : Safe (ForInStep α) := ⟨fun x => match x with | .done a | .yield a => Safe.holds a⟩

theorem safe_push [Safe α] {xs : Array α} {x : α} (hs : Safe.holds xs) (hx : Safe.holds x) :
    Safe.holds (xs.push x) := by intro y hy; rcases Array.mem_push.mp hy with hy | rfl; exact hs y hy; exact hx
theorem safe_toList [Safe α] {xs : Array α} (h : Safe.holds xs) : Safe.holds xs.toList :=
  fun x hx => h x (Array.mem_toList_iff.mp hx)
theorem safe_pair [Safe α] [Safe β] {x : α} {y : β} (hx : Safe.holds x) (hy : Safe.holds y) :
    Safe.holds (x, y) := ⟨hx, hy⟩
theorem safe_fst [Safe α] [Safe β] {p : α × β} (h : Safe.holds p) : Safe.holds p.1 := h.1
theorem safe_snd [Safe α] [Safe β] {p : α × β} (h : Safe.holds p) : Safe.holds p.2 := h.2
theorem safe_yield [Safe α] {a : α} (h : Safe.holds a) : Safe.holds (.yield a : ForInStep α) := h
theorem safe_cons [Safe α] {a : α} {as : List α} (ha : Safe.holds a) (hs : Safe.holds as) :
    Safe.holds (a :: as) := by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hs x hx
theorem safe_append [Safe α] {as bs : List α} (ha : Safe.holds as) (hb : Safe.holds bs) :
    Safe.holds (as ++ bs) := by intro x hx; rcases List.mem_append.mp hx with hx | hx; exact ha x hx; exact hb x hx
theorem safe_ctors (lps : List LevelParam) (nP : Nat)
    {cs : List (Key md × Nat × Ix.Kernel.Expr md × List Nat)} (hc : Safe.holds cs) :
    Safe.holds (cs.map fun (c, nF, ty, _) => Ix.Kernel.ConstantInfo.ctorInfo ⟨c, lps, ty⟩ nP nF) := by
  intro ci hi; obtain ⟨⟨c, nF, ty, flags⟩, hm, rfl⟩ := List.mem_map.mp hi; exact hc _ hm
theorem safe_ind {block : List (Ix.Kernel.ConstantInfo md)} (n : Nat)
    (hne : block ≠ []) (hs : Safe.holds block) : Safe.holds (.indDecl block n : Declaration md) := by
  cases block with
  | nil => exact (hne rfl).elim
  | cons ci cs => simpa [Safe.holds, Declaration.isGenerated, Declaration.names, List.all_eq_true] using hs

def ExSafe [Safe α] (e : Except ε α) : Prop := ∀ a, e = .ok a → Safe.holds a
theorem ex_all [Safe α] (e : Except ε α) (h : ∀ a : α, Safe.holds a) : ExSafe e := fun a _ => h a
theorem ex_pure [Safe α] {a : α} (h : Safe.holds a) : ExSafe (.ok a : Except ε α) := by intro a' he; cases he; exact h
theorem ex_error [Safe α] (e : ε) : ExSafe (.error e : Except ε α) := by intro a h; cases h
theorem ex_error_bind [Safe β] (e : ε) (f : α → Except ε β) :
    ExSafe ((Except.error e : Except ε α) >>= f) := by intro b h; cases h
theorem ex_ite [Safe α] {p : Prop} [Decidable p] {a b : Except ε α}
    (ha : p → ExSafe a) (hb : ¬p → ExSafe b) : ExSafe (if p then a else b) := by
  by_cases h : p
  · simpa only [h, ite_true] using ha h
  · simpa only [h, ite_false] using hb h
theorem ex_dite [Safe α] {p : Prop} [Decidable p] {a : p → Except ε α} {b : ¬p → Except ε α}
    (ha : ∀ h, ExSafe (a h)) (hb : ∀ h, ExSafe (b h)) : ExSafe (dite p a b) := by
  by_cases h : p
  · simpa only [dite_eq_left h] using ha h
  · simpa only [dite_eq_right h] using hb h
theorem ex_cond [Safe α] {p : Bool} {a b : Except ε α}
    (ha : p = true → ExSafe a) (hb : p = false → ExSafe b) : ExSafe (cond p a b) := by
  cases p with | true => exact ha rfl | false => exact hb rfl
theorem ex_bind [Safe α] [Safe β] {e : Except ε α} {f : α → Except ε β}
    (he : ExSafe e) (hf : ∀ a, Safe.holds a → ExSafe (f a)) : ExSafe (e >>= f) := by
  intro b h; obtain ⟨a, ha, hb⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h; exact hf a (he a ha) b hb
theorem ex_forIn [Safe σ] (xs : List α) (body : α → σ → Except ε (ForInStep σ))
    (hb : ∀ x s, Safe.holds s → ExSafe (body x s)) : ∀ s, Safe.holds s → ExSafe (forIn xs s body) := by
  induction xs with
  | nil => intro s hs; exact ex_pure hs
  | cons x xs ih =>
    intro s hs; rw [List.forIn_cons]; apply ex_bind (hb x s hs)
    intro step hstep; cases step with
    | done v => exact ex_pure hstep
    | yield v => exact ih v hstep
theorem ex_forIn_array [Safe σ] (xs : Array α) (body : α → σ → Except ε (ForInStep σ))
    (hb : ∀ x s, Safe.holds s → ExSafe (body x s)) (s : σ) (hs : Safe.holds s) :
    ExSafe (ForIn.forIn xs s body) := by rw [← Array.forIn_toList]; exact ex_forIn _ _ hb s hs
theorem ex_mapM [Safe β] (f : α → Except ε β) (h : ∀ a, ExSafe (f a)) :
    ∀ xs : List α, ExSafe (xs.mapM f) := by
  intro xs; induction xs with
  | nil => intro ys hy; cases hy; simp [Safe.holds]
  | cons x xs ih =>
    simp only [List.mapM_cons]; apply ex_bind (h x); intro y hy; apply ex_bind ih; intro ys hys
    apply ex_pure; intro z hz; rcases List.mem_cons.mp hz with rfl | hz; exact hy; exact hys z hz

open Lean Elab Tactic in
elab "name_step" : tactic => withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  if t.isAppOf ``ExSafe then
    let e := t.getAppArgs.back!.consumeMData
    if e.isAppOf ``Bind.bind || e.isAppOf ``Except.bind then
      let a := e.getAppArgs[e.getAppArgs.size - 2]!
      if a.isAppOf ``MonadExcept.throw || a.isAppOf ``MonadExceptOf.throw || a.isAppOf ``Except.error then
        evalTactic (← `(tactic| exact ex_error_bind _ _))
      else evalTactic (← `(tactic| apply ex_bind))
    else if e.isAppOf ``ite then evalTactic (← `(tactic| apply ex_ite))
    else if e.isAppOf ``dite then evalTactic (← `(tactic| apply ex_dite))
    else if e.isAppOf ``cond then evalTactic (← `(tactic| apply ex_cond))
    else if e.isAppOf ``ForIn.forIn then evalTactic (← `(tactic| first | apply ex_forIn | apply ex_forIn_array))
    else if e.isAppOf ``List.mapM then evalTactic (← `(tactic| apply ex_mapM))
    else if e.isAppOf ``Except.ok || e.isAppOf ``Pure.pure then evalTactic (← `(tactic| apply ex_pure))
    else if e.isAppOf ``Except.error || e.isAppOf ``MonadExceptOf.throw || e.isAppOf ``MonadExcept.throw then
      evalTactic (← `(tactic| exact ex_error _))
    else throwError "not a structural exception step"
  else if t.isAppOf ``Safe.holds then
    let e := t.getAppArgs.back!.consumeMData
    if e.isAppOf ``Array.push then evalTactic (← `(tactic| apply safe_push))
    else if e.isAppOf ``Array.toList then evalTactic (← `(tactic| apply safe_toList))
    else if e.isAppOf ``Prod.mk then evalTactic (← `(tactic| apply safe_pair))
    else if e.isAppOf ``Prod.fst then evalTactic (← `(tactic| apply safe_fst))
    else if e.isAppOf ``Prod.snd then evalTactic (← `(tactic| apply safe_snd))
    else if e.isAppOf ``ForInStep.yield then evalTactic (← `(tactic| apply safe_yield))
    else if e.isAppOf ``List.cons then evalTactic (← `(tactic| apply safe_cons))
    else if e.isAppOf ``HAppend.hAppend || e.isAppOf ``List.append then evalTactic (← `(tactic| apply safe_append))
    else if e.isAppOf ``List.map then evalTactic (← `(tactic| apply safe_ctors))
    else if e.isAppOf ``Ix.Kernel.Declaration.indDecl then evalTactic (← `(tactic| apply safe_ind))
    else throwError "not a structural safe value"
  else if t.isForall then evalTactic (← `(tactic| intro))
  else throwError "not a name-classification goal"

open Lean Elab Tactic in
elab "name_all" : tactic => withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOf ``ExSafe do throwError "not an exception postcondition"
  let ty ← Meta.inferType t.getAppArgs.back!
  if (ty.find? fun e => e.isConstOf ``Ix.Kernel.Declaration || e.isConstOf ``Ix.Kernel.ConstantInfo).isSome then
    throwError "names need a producer proof"
  evalTactic (← `(tactic| solve | apply ex_all; intro a; simp only [Safe.holds, forall_const, implies_true, and_true]))

open Lean Elab Tactic in
elab "name_repeat " n:num tac:tacticSeq : tactic => do
  setGoals (← Meta.repeat' (evalTacticAtRaw tac) (← getGoals) n.getNat)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 3000 in
theorem genMutual_safe (ctx : Ix.Kernel.Frontend.InModel.Ctx md) (b : BlockRec md) : ExSafe (genMutual ctx b) := by
  unfold genMutual
  simp only [← Bool.cond_eq_ite]
  name_repeat 10000 first
    | name_all
    | name_step
    | assumption
    | rfl
    | solve | simp [Safe.holds]
    | (split)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
theorem genNested_safe (ctx : Ix.Kernel.Frontend.InModel.Ctx md) (b : BlockRec md) : ExSafe (genNested ctx b) := by
  unfold genNested
  simp only [← Bool.cond_eq_ite]
  name_repeat 20000 first
    | name_all
    | name_step
    | assumption
    | rfl
    | solve | simp [Safe.holds]
    | (split)

end Generated
/-- Every successful generator result consists of nonempty, all-derived
declarations; this says nothing about distinctness between declarations. -/
theorem generate_generated {ctx : Ix.Kernel.Frontend.InModel.Ctx md} {b : BlockRec md}
    {ds : List (Declaration md)} (h : generate ctx b = .ok ds) :
    ∀ d ∈ ds, d.isGenerated = true := by
  unfold generate at h
  split at h
  · exact Generated.genNested_safe ctx b ds h
  · exact Generated.genMutual_safe ctx b ds h

theorem generate_names {ctx : Ix.Kernel.Frontend.InModel.Ctx md} {b : BlockRec md}
    {ds : List (Declaration md)} (h : generate ctx b = .ok ds) {d : Declaration md} (hd : d ∈ ds) :
    d.names ≠ [] ∧ ∀ k ∈ d.names, k.isAux = true := by
  have hg := generate_generated h d hd
  refine ⟨fun hn => by simp [Declaration.isGenerated, hn] at hg, ?_⟩
  exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp hg).2

/-- The raw inductive read's actual generated prefix is classified. No
claim about collapse's retained indices or duplicate drops is made here. -/
theorem lowerInductive_generated {st : State md} {rb : BlockRead md} {r : Read md}
    (h : lowerInductive st rb = .ok r) :
    ∀ d ∈ r.decls.toList.take r.generated, d.isGenerated = true := by
  obtain ⟨gens, hd, hg, _, hc⟩ := CtxAgree.lowerInductive_ok h
  have names : ∀ d ∈ gens, d.isGenerated = true := by
    rcases hc with ⟨_, hgen⟩ | ⟨_, rfl⟩
    · exact generate_generated hgen
    · simp
  simpa only [hd, hg, Array.toList_push, List.toList_toArray, List.take_left] using names

/-- The generated prefix of every successful Source lowering is genuinely
generated. Ordinary lowering branches return generated = 0. -/
theorem lower_generated {st : State .source} {c : Converted} {r : Read .source}
    (h : lower st c = .ok r) : ∀ d ∈ r.decls.toList.take r.generated, d.isGenerated = true := by
  cases c with
  | «inductive» rb => exact lowerInductive_generated h
  | definitions ms =>
    have hz : r.generated = 0 := by
      unfold lower at h
      delta Ix.LeanIngress.lower.match_6 at h
      dsimp only at h
      split at h
      · rename_i hsz
        obtain ⟨l⟩ := ms
        obtain _ | ⟨m, _ | ⟨_, _⟩⟩ := l
        · cases hsz
        · obtain ⟨_, _, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
          cases h; rfl
        · simp at hsz
      · obtain ⟨_, _, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
        cases h; rfl
    simp [hz]
  | «axiom» cv => cases h; simp
  | quot kind cv => cases h; simp

open ReaderUnits

theorem convertedKeys_mono {K L : CName .source → Prop} {c : Converted}
    (h : ConvertedKeys K c) (imp : ∀ k, K k → L k) : ConvertedKeys L c := by
  cases c with
  | «inductive» rb => exact ⟨fun e he => imp _ (h.1 e he),
      fun e he => imp _ (h.2.1 e he), fun e he => imp _ (h.2.2 e he)⟩
  | definitions ms => exact fun m hm => imp _ (h m hm)
  | «axiom» cv => exact imp _ h
  | quot kind cv => exact imp _ h

theorem convertedKeys_hints {K : CName .source → Prop} {c : Converted}
    (h : ConvertedKeys K c) (hints : CName .source → Option ReducibilityHint) :
    ConvertedKeys K (c.withHints hints) := by
  cases c with
  | definitions ms =>
    intro m hm
    obtain ⟨m0, hmem, rfl⟩ := Array.mem_map.mp hm
    split <;> exact h m0 hmem
  | _ => exact h

theorem quotientKeys_not_aux {ρ : FiberMap}
    (range : ∀ (n : Ix.Kernel.Name) (k : Key .source), ρ[n]? = some k → k.isAux = false)
    {c : Converted} (h : ConvertedKeys (fun k => k.isAux = false) c) :
    ConvertedKeys (fun k => k.isAux = false) (c.quotient ρ) := by
  cases c with
  | «inductive» rb =>
    refine ⟨?_, ?_, ?_⟩
    all_goals
      intro e he
      obtain ⟨e1, he1, rfl⟩ := Array.mem_map.mp he
      obtain ⟨e0, he0, rfl⟩ := Array.mem_map.mp he1
      change (Key.subst ρ e0.1.name).isAux = false
    · exact subst_not_aux range (h.1 e0 he0)
    · exact subst_not_aux range (h.2.1 e0 he0)
    · exact subst_not_aux range (h.2.2 e0 he0)
  | definitions ms =>
    intro m hm
    obtain ⟨m1, hm1, rfl⟩ := Array.mem_map.mp hm
    obtain ⟨m0, hm0, rfl⟩ := Array.mem_map.mp hm1
    exact subst_not_aux range (h m0 hm0)
  | «axiom» cv => exact subst_not_aux range h
  | quot kind cv => exact subst_not_aux range h

/-- Ordinary declarations of an actual quotient conversion have no derived
names. The range property is discharged for the production alias map. -/
theorem quotient_lower_ordinary {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    {gr : Group} {c : Converted} (converted : convert gr = .ok c)
    (hints : CName .source → Option ReducibilityHint) {st : State .source} {r : Read .source}
    (lowered : lower st ((c.withHints hints).quotient (fiberAliasAt ixe roles)) = .ok r) :
    ∀ d ∈ r.decls.toList.drop r.generated, ∀ k ∈ d.names, k.isAux = false := by
  have names := quotientKeys_not_aux (ρ := fiberAliasAt ixe roles)
    (fun _ _ => fiberAliasAt_not_aux)
    (convertedKeys_hints (convertedKeys_mono (convert_keys converted)
      (fun _ h => GroupKeyOf.not_derived h)) hints)
  rcases lower_lowering names lowered with ⟨hg, hall⟩ | ⟨gens, d, hd, hg, hn⟩
  · simpa only [hg, List.drop_zero] using hall
  · simpa only [hd, hg, List.drop_left, List.mem_singleton, forall_eq] using hn

end Ix.Cert.SourceNames
