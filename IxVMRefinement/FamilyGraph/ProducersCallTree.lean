import IxVMRefinement.Core.CallHeaps
import IxVMRefinement.Core.Rep
import IxVMRefinement.Obs.KernelCheck13
import IxVMRefinement.Obs.KernelModeled0
import IxVMRefinement.Obs.KernelModeled1
import IxVMRefinement.Obs.KernelModeled2
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.Ingress0

/-! # Call-tree descent for `check_family` and `check_witness`

Two syntactic call-graph facts over `IxVM.program`:

1. `obsFn_check_family_modeled`: in any observed derivation of a function other than
   `KernelModeled::check_modeled_block`, every recorded call to `KernelModeled::check_family`
   is preceded by an observed call to `KernelModeled::block_is_modeled` on the same block
   address returning a non-zero field value, with its subcalls in the outer call list.
   The only callers of `check_family` and `check_modeled_block` in `IxVM.program` are
   `KernelCheck::check_const` (whose `Induct`, `Ctor`, and `Rec` modeled arms each dispatch on
   `block_is_modeled` returning non-zero) and `KernelModeled::check_modeled_block`.

2. `obsFn_check_witness_enclosing_family`: in any observed derivation of a function other than
   `KernelModeled::check_witnesses`, every recorded call to `KernelModeled::check_witness` lies
   directly in the `check_witnesses` loop of an enclosing `check_family` derivation whose
   subcalls are contained in the outer call list. The only callers of `check_witness` and
   `check_witnesses` in `IxVM.program` are `KernelModeled::check_family` and
   `KernelModeled::check_witnesses`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Typing

open Aiur (Heap SourceValue Environment Constant Value loadValue lookupMap)
open Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Obs

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Fast byte equality on string literals and syntactic call scans -/

private def bytesEq : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (a.toNat = b.toNat) && bytesEq as bs
  | _, _ => false

private theorem bytesEq_eq_true {xs ys : List UInt8} : bytesEq xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [bytesEq]
  | cons x xs ih =>
    cases ys with
    | nil => simp [bytesEq]
    | cons y ys =>
      simp only [bytesEq, Bool.and_eq_true, decide_eq_true_eq, ih, List.cons.injEq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨UInt8.toNat_inj.mp h1, h2⟩,
        fun ⟨h1, h2⟩ => ⟨congrArg UInt8.toNat h1, h2⟩⟩

private def strBytesEq (a b : String) : Bool :=
  bytesEq a.toByteArray.data.toList b.toByteArray.data.toList

private theorem strBytesEq_eq_true {a b : String} : strBytesEq a b = true ↔ a = b := by
  rw [strBytesEq, bytesEq_eq_true]
  constructor
  · intro hl
    apply String.toByteArray_inj.mp
    cases ha : a.toByteArray with
    | mk da =>
      cases hb : b.toByteArray with
      | mk db =>
        simp only [ha, hb] at hl
        cases da; cases db
        simp only [Array.toList] at hl
        rw [hl]
  · intro h; subst h; rfl

private def inTargets : List String → String → Bool
  | [], _ => false
  | t :: ts, s => strBytesEq t s || inTargets ts s

private theorem inTargets_eq_false {ts : List String} {s : String}
    (h : inTargets ts s = false) : ∀ t ∈ ts, s ≠ t := by
  induction ts with
  | nil => intro t ht; simp at ht
  | cons t₀ ts ih =>
    simp only [inTargets, Bool.or_eq_false_iff] at h
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · intro heq; subst heq
      have ht1 : strBytesEq s s = true := strBytesEq_eq_true.mpr rfl
      rw [h.1] at ht1; cases ht1
    · exact ih h.2 t ht'

private def plainBytes (s : String) : Bool :=
  match s.toByteArray.data.toList with
  | b :: _ => decide (b.toNat ≠ 36)
  | [] => true

private theorem head_ne_dollar_of_plainBytes {s : String} (h : plainBytes s = true) :
    s.toList.head? ≠ some '$' := by
  apply Aiur.Generic.head_ne_of_bytes
  unfold plainBytes at h
  cases hbs : s.toByteArray.data.toList with
  | nil => simp
  | cons b bs =>
    rw [hbs] at h
    simp only [decide_eq_true_eq] at h
    simp only [List.head?_cons, ne_eq, Option.some.injEq]
    intro heq
    exact h (congrArg UInt8.toNat heq)

mutual
  private def hasCallIn (ts : List String) : Expr F → Bool
    | .literal _ | .var _ | .global _ _ => false
    | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
    | .record _ xs | .update _ xs | .builtin _ xs => hasCallInList ts xs
    | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
    | .store x | .load x | .hint _ x _ | .neg x | .control _ x => hasCallIn ts x
    | .letValue _ v b | .binary _ v b => hasCallIn ts v || hasCallIn ts b
    | .call name _ args => inTargets ts name || hasCallInList ts args
    | .matchValue scrut arms => hasCallIn ts scrut || hasCallInArms ts arms

  private def hasCallInList (ts : List String) : List (Expr F) → Bool
    | [] => false
    | x :: xs => hasCallIn ts x || hasCallInList ts xs

  private def hasCallInArms (ts : List String) : List (Pattern F × Expr F) → Bool
    | [] => false
    | (_, b) :: rest => hasCallIn ts b || hasCallInArms ts rest
end

mutual
  private def noDollarCall : Expr F → Bool
    | .literal _ | .var _ | .global _ _ => true
    | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
    | .record _ xs | .update _ xs | .builtin _ xs => noDollarCallList xs
    | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
    | .store x | .load x | .hint _ x _ | .neg x | .control _ x => noDollarCall x
    | .letValue _ v b | .binary _ v b => noDollarCall v && noDollarCall b
    | .call name _ args => plainBytes name && noDollarCallList args
    | .matchValue scrut arms => noDollarCall scrut && noDollarCallArms arms

  private def noDollarCallList : List (Expr F) → Bool
    | [] => true
    | x :: xs => noDollarCall x && noDollarCallList xs

  private def noDollarCallArms : List (Pattern F × Expr F) → Bool
    | [] => true
    | (_, b) :: rest => noDollarCall b && noDollarCallArms rest
end

private theorem hasCallIn_arms_mem {ts : List String} {arms : List (Pattern F × Expr F)}
    {p : Pattern F} {b : Expr F} (h : hasCallInArms ts arms = false) (hm : (p, b) ∈ arms) :
    hasCallIn ts b = false := by
  induction arms with
  | nil => simp at hm
  | cons a rest ih =>
    rcases a with ⟨p₀, b₀⟩
    simp only [hasCallInArms, Bool.or_eq_false_iff] at h
    rcases List.mem_cons.mp hm with heq | hm'
    · cases heq; exact h.1
    · exact ih h.2 hm'

private theorem noDollarCall_arms_mem {arms : List (Pattern F × Expr F)}
    {p : Pattern F} {b : Expr F} (h : noDollarCallArms arms = true) (hm : (p, b) ∈ arms) :
    noDollarCall b = true := by
  induction arms with
  | nil => simp at hm
  | cons a rest ih =>
    rcases a with ⟨p₀, b₀⟩
    simp only [noDollarCallArms, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with heq | hm'
    · cases heq; exact h.1
    · exact ih h.2 hm'

private theorem selectArm_body_mem {world : World F} {types : Types} {heap : Heap F}
    {val : SourceValue F} {arms : List (Pattern F × Expr F)}
    {bindings : Environment F Nat} {body : Expr F}
    (h : selectArm world types heap val arms = .ok (some (bindings, body))) :
    ∃ p, (p, body) ∈ arms := by
  induction arms with
  | nil => simp [selectArm, pure, Except.pure] at h
  | cons a rest ih =>
    rcases a with ⟨p, b⟩
    simp only [selectArm, bind, Except.bind] at h
    cases hm : world.matchPattern types heap p val with
    | error e => simp [hm] at h
    | ok opt =>
      rw [hm] at h
      cases opt with
      | none =>
        obtain ⟨p', hp'⟩ := ih h
        exact ⟨p', List.mem_cons_of_mem _ hp'⟩
      | some bs =>
        simp [pure, Except.pure] at h
        exact ⟨p, h.2 ▸ List.mem_cons_self⟩

private theorem hasCallIn_constantExpr (ts : List String) (c : Constant F) :
    hasCallIn ts (constantExpr c) = false := by
  match c with
  | .field _ => simp only [constantExpr, hasCallIn]
  | .ptr _ a => exact Empty.elim a
  | .tuple xs =>
    simp only [constantExpr, hasCallIn]
    exact go xs
  | .construct n c xs =>
    simp only [constantExpr, hasCallIn]
    exact go xs
where
  go : (xs : List (Constant F)) → hasCallInList ts (xs.map constantExpr) = false
    | [] => rfl
    | x :: xs => by
      simp only [List.map_cons, hasCallInList, Bool.or_eq_false_iff]
      exact ⟨hasCallIn_constantExpr ts x, go xs⟩

private theorem noDollarCall_constantExpr (c : Constant F) :
    noDollarCall (constantExpr c) = true := by
  match c with
  | .field _ => simp only [constantExpr, noDollarCall]
  | .ptr _ a => exact Empty.elim a
  | .tuple xs =>
    simp only [constantExpr, noDollarCall]
    exact go xs
  | .construct n c xs =>
    simp only [constantExpr, noDollarCall]
    exact go xs
where
  go : (xs : List (Constant F)) → noDollarCallList (xs.map constantExpr) = true
    | [] => rfl
    | x :: xs => by
      simp only [List.map_cons, noDollarCallList, Bool.and_eq_true]
      exact ⟨noDollarCall_constantExpr x, go xs⟩

private theorem mapM_toExpr_ok {ps : List (Pattern F)} {es : List (Expr F)}
    (h : ps.mapM Consts.toExpr = .ok es) :
    ∀ e ∈ es, ∃ p ∈ ps, Consts.toExpr p = .ok e := by
  induction ps generalizing es with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro e he; simp at he
  | cons p ps ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hp : Consts.toExpr p with
    | error err => rw [hp] at h; cases h
    | ok e0 =>
      rw [hp] at h
      cases hps : ps.mapM Consts.toExpr with
      | error err => rw [hps] at h; cases h
      | ok es0 =>
        rw [hps] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro e he
        rcases List.mem_cons.mp he with rfl | he'
        · exact ⟨p, List.mem_cons_self, hp⟩
        · obtain ⟨p', hp', hto⟩ := ih hps e he'
          exact ⟨p', List.mem_cons_of_mem _ hp', hto⟩

private theorem hasCallInList_of_all {ts : List String} {es : List (Expr F)}
    (h : ∀ e ∈ es, hasCallIn ts e = false) : hasCallInList ts es = false := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [hasCallInList, Bool.or_eq_false_iff]
    exact ⟨h e List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

private theorem noDollarCallList_of_all {es : List (Expr F)}
    (h : ∀ e ∈ es, noDollarCall e = true) : noDollarCallList es = true := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [noDollarCallList, Bool.and_eq_true]
    exact ⟨h e List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

private theorem hasCallIn_toExpr (ts : List String) (p : Pattern F) :
    ∀ {e : Expr F}, Consts.toExpr p = .ok e → hasCallIn ts e = false := by
  match p with
  | .literal _ | .global _ _ =>
    intro e h
    simp only [Consts.toExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | .orElse _ _ _ | .wildcard | .bind _ =>
    intro e h; simp [Consts.toExpr, throw, MonadExceptOf.throw] at h
  | .load p' =>
    intro e h
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hp' : Consts.toExpr p' with
    | error _ => rw [hp'] at h; cases h
    | ok e' =>
      rw [hp'] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [hasCallIn]
      exact hasCallIn_toExpr ts p' hp'
  | .repeat p' n =>
    intro e h
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hp' : Consts.toExpr p' with
    | error _ => rw [hp'] at h; cases h
    | ok e' =>
      rw [hp'] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [hasCallIn]
      exact hasCallIn_toExpr ts p' hp'
  | .record head ps | .tuple ps | .array ps | .constructAs _ _ _ ps =>
    intro e h
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hps : ps.mapM Consts.toExpr with
    | error _ => rw [hps] at h; cases h
    | ok es =>
      rw [hps] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [hasCallIn]
      refine hasCallInList_of_all fun e' he' => ?_
      obtain ⟨p', hp', hto⟩ := mapM_toExpr_ok hps e' he'
      have : sizeOf p' < sizeOf ps := List.sizeOf_lt_of_mem hp'
      exact hasCallIn_toExpr ts p' hto
  | .construct t c ps =>
    cases t with
    | named n ts' =>
      intro e h
      simp only [Consts.toExpr, bind, Except.bind] at h
      cases hps : ps.mapM Consts.toExpr with
      | error _ => rw [hps] at h; cases h
      | ok es =>
        rw [hps] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [hasCallIn]
        refine hasCallInList_of_all fun e' he' => ?_
        obtain ⟨p', hp', hto⟩ := mapM_toExpr_ok hps e' he'
        have : sizeOf p' < sizeOf ps := List.sizeOf_lt_of_mem hp'
        exact hasCallIn_toExpr ts p' hto
    | field | tuple _ | array _ _ | ptr _ | param _ =>
      intro e h; simp [Consts.toExpr, throw, MonadExceptOf.throw] at h
termination_by sizeOf p

private theorem noDollarCall_toExpr (p : Pattern F) :
    ∀ {e : Expr F}, Consts.toExpr p = .ok e → noDollarCall e = true := by
  match p with
  | .literal _ | .global _ _ =>
    intro e h
    simp only [Consts.toExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | .orElse _ _ _ | .wildcard | .bind _ =>
    intro e h; simp [Consts.toExpr, throw, MonadExceptOf.throw] at h
  | .load p' =>
    intro e h
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hp' : Consts.toExpr p' with
    | error _ => rw [hp'] at h; cases h
    | ok e' =>
      rw [hp'] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [noDollarCall]
      exact noDollarCall_toExpr p' hp'
  | .repeat p' n =>
    intro e h
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hp' : Consts.toExpr p' with
    | error _ => rw [hp'] at h; cases h
    | ok e' =>
      rw [hp'] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [noDollarCall]
      exact noDollarCall_toExpr p' hp'
  | .record head ps | .tuple ps | .array ps | .constructAs _ _ _ ps =>
    intro e h
    simp only [Consts.toExpr, bind, Except.bind] at h
    cases hps : ps.mapM Consts.toExpr with
    | error _ => rw [hps] at h; cases h
    | ok es =>
      rw [hps] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [noDollarCall]
      refine noDollarCallList_of_all fun e' he' => ?_
      obtain ⟨p', hp', hto⟩ := mapM_toExpr_ok hps e' he'
      have : sizeOf p' < sizeOf ps := List.sizeOf_lt_of_mem hp'
      exact noDollarCall_toExpr p' hto
  | .construct t c ps =>
    cases t with
    | named n ts' =>
      intro e h
      simp only [Consts.toExpr, bind, Except.bind] at h
      cases hps : ps.mapM Consts.toExpr with
      | error _ => rw [hps] at h; cases h
      | ok es =>
        rw [hps] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [noDollarCall]
        refine noDollarCallList_of_all fun e' he' => ?_
        obtain ⟨p', hp', hto⟩ := mapM_toExpr_ok hps e' he'
        have : sizeOf p' < sizeOf ps := List.sizeOf_lt_of_mem hp'
        exact noDollarCall_toExpr p' hto
    | field | tuple _ | array _ _ | ptr _ | param _ =>
      intro e h; simp [Consts.toExpr, throw, MonadExceptOf.throw] at h
termination_by sizeOf p

/-! ## Strict descent when a body avoids the target callees -/

private theorem instanceName_ne_of_ne {types : Types} {name target : String}
    {typeArgs : Option (List Ty)} (hplain : target.toList.head? ≠ some '$')
    (hne : name ≠ target) : instanceName types name typeArgs ≠ target := by
  intro heq
  unfold instanceName Instance.symbol at heq
  split at heq
  · exact hne heq
  · apply hplain
    rw [← heq, String.toList_ofList]
    rfl

private theorem instanceName_not_mem_targets {ts : List String}
    (hplain : ∀ t ∈ ts, t.toList.head? ≠ some '$') {types : Types} {name : String}
    {typeArgs : Option (List Ty)} (h : inTargets ts name = false) :
    ∀ t ∈ ts, instanceName types name typeArgs ≠ t := by
  intro t ht
  exact instanceName_ne_of_ne (hplain t ht) (inTargets_eq_false h t ht)

private theorem instanceName_ofSymbol_not_mem_targets {ts : List String} {types : Types}
    {name : String} {typeArgs : Option (List Ty)}
    (hno : inTargets ts name = false) (hnd : plainBytes name = true) :
    ∀ key, Instance.ofSymbol (instanceName types name typeArgs) = .ok key →
      ∀ t ∈ ts, key.name ≠ t := by
  intro key hof t ht
  have hsym := Instance.ofSymbol_symbol
    ⟨name, (typeArgs.getD []).map (Ty.subst types)⟩
    (fun _ => head_ne_dollar_of_plainBytes hnd)
  change Instance.ofSymbol
    (Instance.symbol ⟨name, (typeArgs.getD []).map (Ty.subst types)⟩) = .ok key at hof
  rw [hsym] at hof
  injection hof with hkey
  subst hkey
  exact inTargets_eq_false hno t ht

/-- A strictly shorter subcall containing `cl` whose callee avoids `ts`. -/
private def StrictSubCall (ts : List String) (cl : Call F) (calls : List (Call F)) : Prop :=
  ∃ fnName args h r h' cs,
    ObsFn Obs.W fnName args h r h' cs ∧
    cl ∈ cs ∧ cs.length < calls.length ∧ (∀ x ∈ cs, x ∈ calls) ∧
    (∀ t ∈ ts, fnName ≠ t) ∧
    (∀ key, Instance.ofSymbol fnName = .ok key → ∀ t ∈ ts, key.name ≠ t)

private theorem strictSubCall_mono_left {ts : List String} {cl : Call F}
    {cs₁ cs₂ : List (Call F)} (h : StrictSubCall ts cl cs₁) :
    StrictSubCall ts cl (cs₁ ++ cs₂) := by
  obtain ⟨fnName, args, h0, r0, h0', cs, ev, hmem, hlt, hsub, hne, hkey⟩ := h
  exact ⟨fnName, args, h0, r0, h0', cs, ev, hmem, by simp; omega,
    fun x hx => List.mem_append_left _ (hsub x hx), hne, hkey⟩

private theorem strictSubCall_mono_right {ts : List String} {cl : Call F}
    {cs₁ cs₂ : List (Call F)} (h : StrictSubCall ts cl cs₂) :
    StrictSubCall ts cl (cs₁ ++ cs₂) := by
  obtain ⟨fnName, args, h0, r0, h0', cs, ev, hmem, hlt, hsub, hne, hkey⟩ := h
  exact ⟨fnName, args, h0, r0, h0', cs, ev, hmem, by simp; omega,
    fun x hx => List.mem_append_right _ (hsub x hx), hne, hkey⟩

private theorem obsFn_strictSubCall {ts : List String}
    (hplain : ∀ t ∈ ts, t.toList.head? ≠ some '$') {cl : Call F} (hclTarget : cl.name ∈ ts)
    {fnName : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn Obs.W fnName args h r h' calls)
    (hprep : ∀ types locals expr, Obs.W.prepare fnName args = .ok (types, locals, expr) →
      hasCallIn ts expr = false ∧ noDollarCall expr = true)
    (hcl : cl ∈ calls) : StrictSubCall ts cl calls := by
  revert hprep hcl
  induction ev using ObsFn.rec
    (motive_1 := fun _ _ expr _ _ _ calls _ =>
      hasCallIn ts expr = false → noDollarCall expr = true → cl ∈ calls →
      StrictSubCall ts cl calls)
    (motive_2 := fun _ _ exprs _ _ _ calls _ =>
      hasCallInList ts exprs = false → noDollarCallList exprs = true → cl ∈ calls →
      StrictSubCall ts cl calls)
    (motive_4 := fun _ _ expr _ _ _ _ calls _ =>
      hasCallIn ts expr = false → noDollarCall expr = true → cl ∈ calls →
      StrictSubCall ts cl calls)
    (motive_5 := fun _ _ exprs _ _ _ _ calls _ =>
      hasCallInList ts exprs = false → noDollarCallList exprs = true → cl ∈ calls →
      StrictSubCall ts cl calls) with
  | block _ ih hno hnd hm => exact ih hno hnd hm
  | blockExit _ ih hno hnd hm => exact ih hno hnd hm
  | literal _ _ hm => simp at hm
  | var _ _ _ hm => simp at hm
  | global _ interpreted _ ih _ _ hm =>
    exact ih (hasCallIn_toExpr ts _ interpreted) (noDollarCall_toExpr _ interpreted) hm
  | tuple _ ih hno hnd hm | array _ ih hno hnd hm | «repeat» _ ih hno hnd hm
  | index _ _ ih hno hnd hm | slice _ _ ih hno hnd hm | builtin _ _ ih hno hnd hm
  | update _ _ ih hno hnd hm | record _ ih hno hnd hm | member _ _ ih hno hnd hm
  | construct _ ih hno hnd hm | constructAs _ ih hno hnd hm | project _ _ ih hno hnd hm
  | store _ ih hno hnd hm | load _ _ ih hno hnd hm | hint _ _ ih hno hnd hm
  | neg _ _ ih hno hnd hm => exact ih hno hnd hm
  | letValue _ _ _ ih1 ih2 hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    rcases List.mem_append.mp hm with h1 | h2
    · exact strictSubCall_mono_left (ih1 hno.1 hnd.1 h1)
    · exact strictSubCall_mono_right (ih2 hno.2 hnd.2 h2)
  | binary _ _ _ ih1 ih2 hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    rcases List.mem_append.mp hm with h1 | h2
    · exact strictSubCall_mono_left (ih1 hno.1 hnd.1 h1)
    · exact strictSubCall_mono_right (ih2 hno.2 hnd.2 h2)
  | call _ callee ih1 _ hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    rcases List.mem_append.mp hm with h1 | h2
    · exact strictSubCall_mono_left (ih1 hno.2 hnd.2 h1)
    · rcases List.mem_cons.mp h2 with heq | h3
      · exact (instanceName_not_mem_targets hplain hno.1 cl.name hclTarget
          (congrArg Call.name heq.symm)).elim
      · exact ⟨_, _, _, _, _, _, callee, h3,
          by simp; omega,
          fun x hx => List.mem_append_right _ (List.mem_cons_of_mem _ hx),
          instanceName_not_mem_targets hplain hno.1,
          instanceName_ofSymbol_not_mem_targets hno.1 hnd.1⟩
  | matchValue _ selected _ ih1 ih2 hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    rcases List.mem_append.mp hm with h1 | h2
    · exact strictSubCall_mono_left (ih1 hno.1 hnd.1 h1)
    · obtain ⟨p, hp⟩ := selectArm_body_mem selected
      exact strictSubCall_mono_right
        (ih2 (hasCallIn_arms_mem hno.2 hp) (noDollarCall_arms_mem hnd.2 hp) h2)
  | nil _ _ hm => simp at hm
  | cons _ _ ih1 ih2 hno hnd hm =>
    simp only [hasCallInList, Bool.or_eq_false_iff] at hno
    simp only [noDollarCallList, Bool.and_eq_true] at hnd
    rcases List.mem_append.mp hm with h1 | h2
    · exact strictSubCall_mono_left (ih1 hno.1 hnd.1 h1)
    · exact strictSubCall_mono_right (ih2 hno.2 hnd.2 h2)
  | intro prepared _ ih =>
    intro hp hm
    exact ih (hp _ _ _ prepared).1 (hp _ _ _ prepared).2 hm
  | returned prepared _ ih =>
    intro hp hm
    exact ih (hp _ _ _ prepared).1 (hp _ _ _ prepared).2 hm
  | exit _ ih hno hnd hm | exitPayload _ ih hno hnd hm | fromBlock _ _ ih hno hnd hm
  | fromTuple _ ih hno hnd hm | fromArray _ ih hno hnd hm | fromRepeat _ ih hno hnd hm
  | fromIndex _ ih hno hnd hm | fromSlice _ ih hno hnd hm | fromBuiltin _ ih hno hnd hm
  | fromUpdate _ ih hno hnd hm | fromRecord _ ih hno hnd hm | fromMember _ ih hno hnd hm
  | fromConstruct _ ih hno hnd hm | fromConstructAs _ ih hno hnd hm
  | fromProject _ ih hno hnd hm | fromStore _ ih hno hnd hm | fromLoad _ ih hno hnd hm
  | fromHint _ ih hno hnd hm | fromNeg _ ih hno hnd hm => exact ih hno hnd hm
  | fromGlobal _ interpreted _ ih _ _ hm =>
    exact ih (hasCallIn_toExpr ts _ interpreted) (noDollarCall_toExpr _ interpreted) hm
  | fromLetValue _ ih hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    exact ih hno.1 hnd.1 hm
  | letBody _ _ _ ih1 ih2 hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    rcases List.mem_append.mp hm with h1 | h2
    · exact strictSubCall_mono_left (ih1 hno.1 hnd.1 h1)
    · exact strictSubCall_mono_right (ih2 hno.2 hnd.2 h2)
  | binaryLeft _ ih hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    exact ih hno.1 hnd.1 hm
  | binaryRight _ _ ih1 ih2 hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    rcases List.mem_append.mp hm with h1 | h2
    · exact strictSubCall_mono_left (ih1 hno.1 hnd.1 h1)
    · exact strictSubCall_mono_right (ih2 hno.2 hnd.2 h2)
  | fromCall _ ih hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    exact ih hno.2 hnd.2 hm
  | fromMatchValue _ ih hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    exact ih hno.1 hnd.1 hm
  | matchBody _ selected _ ih1 ih2 hno hnd hm =>
    simp only [hasCallIn, Bool.or_eq_false_iff] at hno
    simp only [noDollarCall, Bool.and_eq_true] at hnd
    rcases List.mem_append.mp hm with h1 | h2
    · exact strictSubCall_mono_left (ih1 hno.1 hnd.1 h1)
    · obtain ⟨p, hp⟩ := selectArm_body_mem selected
      exact strictSubCall_mono_right
        (ih2 (hasCallIn_arms_mem hno.2 hp) (noDollarCall_arms_mem hnd.2 hp) h2)
  | head _ ih hno hnd hm =>
    simp only [hasCallInList, Bool.or_eq_false_iff] at hno
    simp only [noDollarCallList, Bool.and_eq_true] at hnd
    exact ih hno.1 hnd.1 hm
  | tail _ _ ih1 ih2 hno hnd hm =>
    simp only [hasCallInList, Bool.or_eq_false_iff] at hno
    simp only [noDollarCallList, Bool.and_eq_true] at hnd
    rcases List.mem_append.mp hm with h1 | h2
    · exact strictSubCall_mono_left (ih1 hno.1 hnd.1 h1)
    · exact strictSubCall_mono_right (ih2 hno.2 hnd.2 h2)

/-! ## Identifying the program function behind an `ObsFn` -/

private theorem arguments_nil_right {params : List String} {ts : List (String × Ty)}
    (h : arguments params [] = .ok ts) : params = [] ∧ ts = [] := by
  unfold arguments at h
  split at h
  · simp [throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
  · rename_i hne
    have hlen : params.length = 0 := by simpa using hne
    have hp : params = [] := List.eq_nil_of_length_eq_zero hlen
    subst hp
    simp [pure, Except.pure, bind, Except.bind] at h
    exact ⟨rfl, h⟩

private theorem arguments_nil_left {types : List Ty} {ts : List (String × Ty)}
    (h : arguments [] types = .ok ts) : types = [] ∧ ts = [] := by
  unfold arguments at h
  split at h
  · simp [throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
  · rename_i hne
    have hlen : types.length = 0 := by simp at hne; omega
    have ht : types = [] := List.eq_nil_of_length_eq_zero hlen
    subst ht
    simp [pure, Except.pure, bind, Except.bind] at h
    exact ⟨rfl, h⟩

private theorem sourceFunction?_fn_detail {p : Program F} {name : String} {sf : SourceFunction F}
    (h : p.sourceFunction? name = some sf) :
    ∃ key f types,
      Instance.ofSymbol name = .ok key ∧
      f ∈ p.functions ∧ f.name = key.name ∧
      arguments f.typeParams key.types = .ok types ∧
      sf = { types, params := f.params.map fun (n, t) => (n, (t.subst types).toCore),
             body := f.body } := by
  unfold Program.sourceFunction? at h
  cases h1 : Instance.ofSymbol name with
  | error e => simp [h1, Except.toOption] at h
  | ok key =>
    simp only [h1, Except.toOption, bind, Option.bind] at h
    cases h2 : p.findFunction? key.name with
    | none => simp [h2] at h
    | some f =>
      simp only [h2] at h
      cases h3 : arguments f.typeParams key.types with
      | error e => simp [h3, Except.toOption] at h
      | ok types =>
        simp only [h3, Except.toOption, pure, Option.some.injEq] at h
        unfold Program.findFunction? at h2
        have hmem : f ∈ p.functions := List.mem_of_find?_eq_some h2
        have hbeq := List.find?_some h2
        exact ⟨key, f, types, rfl, hmem, beq_iff_eq.mp hbeq, h3, h.symm⟩

/-- Re-tag an `ObsFn` whose underlying program function has plain name `target` and a known
monomorphic lookup theorem `hlk` into `ObsFn Obs.W target args ...`, also determining `args.length`. -/
private theorem obsFn_retag_mono {fnName target : String} {sf sfT : SourceFunction F}
    {f : Aiur.Generic.Function F} {key : Instance} {types : Types}
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn Obs.W fnName args h r h' calls)
    (hsf : IxVM.program.sourceFunction? fnName = some sf)
    (hf : f ∈ IxVM.program.functions)
    (harg : arguments f.typeParams key.types = .ok types)
    (hsf_eq : sf = { types, params := f.params.map fun (n, t) => (n, (t.subst types).toCore),
                     body := f.body })
    (hname : f.name = target)
    (hplain : target.toList.head? ≠ some '$')
    (hlk : IxVM.program.sourceFunction? target = some sfT) :
    ObsFn Obs.W target args h r h' calls ∧ args.length = sfT.params.length := by
  -- Unfold `hlk` to prove `f.typeParams = []` and `sf = sfT`.
  have hsym : Instance.ofSymbol target = .ok ⟨target, []⟩ := by
    have := Instance.ofSymbol_symbol ⟨target, []⟩ (fun _ => hplain)
    simpa [Instance.symbol] using this
  have hfind : IxVM.program.findFunction? target = some f := by
    rw [← hname]
    exact Program.findFunction?_of_mem IxVM.functionNames_nodup hf
  have hlk' := hlk
  unfold Program.sourceFunction? at hlk'
  simp only [hsym, Except.toOption, hfind, bind, Option.bind] at hlk'
  cases hargT : arguments f.typeParams [] with
  | error e => simp [hargT, Except.toOption] at hlk'
  | ok typesT =>
    simp only [hargT, Except.toOption, pure, Option.some.injEq] at hlk'
    obtain ⟨htp, htsT⟩ := arguments_nil_right hargT
    rw [htp] at harg
    subst htsT
    obtain ⟨_, hts⟩ := arguments_nil_left harg
    subst hts
    have hsf_eq_sfT : sf = sfT := hsf_eq.trans hlk'
    have hsfS : IxVM.source.program.sourceFunction? fnName = some sf := hsf
    have hlkS : IxVM.source.program.sourceFunction? target = some sfT := hlk
    have hprepEq : Obs.W.prepare fnName args = Obs.W.prepare target args := by
      simp only [Obs.W, Source.world, sourceWorld, hsfS, hlkS, hsf_eq_sfT]
    have hlen : ∀ {t l b}, Obs.W.prepare target args = .ok (t, l, b) →
        args.length = sfT.params.length := by
      intro t l b hp
      simp only [Obs.W, Source.world, sourceWorld, hlkS, SourceFunction.prepare] at hp
      split at hp
      · rename_i hcond
        have := congrArg List.length hcond.1
        simpa using this.symm
      · cases hp
    cases ev with
    | intro prepared body =>
      rw [hprepEq] at prepared
      exact ⟨.intro prepared body, hlen prepared⟩
    | returned prepared body =>
      rw [hprepEq] at prepared
      exact ⟨.returned prepared body, hlen prepared⟩

/-! ## Certified syntactic call-graph tables over `IxVM.program` -/

private theorem ixvm_noDollarCalls :
    IxVM.program.functions.all (fun f => noDollarCall f.body) = true := by
  decide +kernel

private theorem ixvm_callers_check_family :
    IxVM.program.functions.all (fun f =>
      !hasCallIn ["KernelModeled::check_family", "KernelModeled::check_modeled_block"] f.body ||
      strBytesEq f.name "KernelCheck::check_const" ||
      strBytesEq f.name "KernelModeled::check_modeled_block") = true := by
  decide +kernel

private theorem ixvm_callers_check_witness :
    IxVM.program.functions.all (fun f =>
      !hasCallIn ["KernelModeled::check_witness", "KernelModeled::check_witnesses"] f.body ||
      strBytesEq f.name "KernelModeled::check_family" ||
      strBytesEq f.name "KernelModeled::check_witnesses") = true := by
  decide +kernel

/-! ## Address-pointer pullback through `loadValue` -/

/-- If `ptr` loads at an earlier heap `h₁` that `h₂` extends, an address representation at `h₂`
already holds at `h₁`. -/
theorem repAddressRef_pullback {ty : Aiur.Ty} {h₁ h₂ : Heap F} {addr : Bytes.Address}
    {ptr v₁ : SourceValue F} (ext : Heap.Extends h₁ h₂) (hld : loadValue h₁ ptr = .ok v₁)
    (hrep : Bytes.RepAddressRef ty h₂ addr ptr) :
    Bytes.RepAddressRef ty h₁ addr ptr := by
  obtain ⟨idx, v₂, rfl, hget₂, haddr⟩ := hrep
  unfold loadValue at hld
  dsimp only at hld
  cases hget₁ : h₁[idx]? with
  | none => simp [hget₁] at hld
  | some v =>
    have hget₂' : h₂[idx]? = some v := ext.getElem?_eq hget₁
    rw [hget₂'] at hget₂
    injection hget₂ with hv
    subst hv
    exact ⟨idx, v, rfl, hget₁, haddr⟩

private theorem block_is_modeled_loads_block {x_block r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::block_is_modeled" [x_block] h r h' cs) :
    ∃ v, loadValue h x_block = .ok v := by
  match Obs.«KernelModeled::block_is_modeled».obs ev with
  | .Muts_n0 (ev14 := ev14) .. | .Muts_n1 (ev14 := ev14) ..
  | .Muts_other (ev14 := ev14) .. | .other (ev14 := ev14) .. =>
    match Obs.«Ingress::load_verified_constant».obs ev14 with
    | .run (v1 := v1) (ld11 := ld11) .. => exact ⟨v1, ld11⟩

theorem read_payload_loads_block {x_block r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::read_payload" [x_block] h r h' cs) :
    ∃ v, loadValue h x_block = .ok v := by
  match Obs.«KernelModeled::read_payload».obs ev with
  | .Nil (v1 := v1) (ld11 := ld11) .. | .other (v1 := v1) (ld11 := ld11) .. =>
    exact ⟨v1, ld11⟩

/-! ## Call-list peeling helpers -/

private theorem peel_eq {P : Prop} {cl : Call F} {rhs calls : List (Call F)}
    (hc : calls = rhs) (hcl : cl ∈ calls)
    (k : cl ∈ rhs → rhs.length ≤ calls.length → (∀ x ∈ rhs, x ∈ calls) → P) : P :=
  k (hc ▸ hcl) (by rw [hc]) (fun x hx => hc ▸ hx)

private theorem peel_append {P : Prop} {cl : Call F} {cs₁ cs₂ calls : List (Call F)}
    (hcl : cl ∈ cs₁ ++ cs₂) (hle : (cs₁ ++ cs₂).length ≤ calls.length)
    (hsub : ∀ x ∈ cs₁ ++ cs₂, x ∈ calls)
    (h1 : cl ∈ cs₁ → cs₁.length ≤ calls.length → (∀ x ∈ cs₁, x ∈ calls) → P)
    (h2 : cl ∈ cs₂ → cs₂.length ≤ calls.length → (∀ x ∈ cs₂, x ∈ calls) → P) : P := by
  rcases List.mem_append.mp hcl with h | h
  · exact h1 h (by simp at hle; omega) (fun x hx => hsub x (List.mem_append_left _ hx))
  · exact h2 h (by simp at hle; omega) (fun x hx => hsub x (List.mem_append_right _ hx))

private theorem peel {P : Prop} {fnName : String} {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {cs rest calls : List (Call F)} {cl : Call F}
    (ev : ObsFn Obs.W fnName args h r h' cs)
    (hcl : cl ∈ (⟨fnName, args, h⟩ : Call F) :: (cs ++ rest))
    (hle : ((⟨fnName, args, h⟩ : Call F) :: (cs ++ rest)).length ≤ calls.length)
    (hsub : ∀ x ∈ ((⟨fnName, args, h⟩ : Call F) :: (cs ++ rest)), x ∈ calls)
    (hne : cl.name ≠ fnName)
    (h1 : cl ∈ cs → cs.length < calls.length → (∀ x ∈ cs, x ∈ calls) → P)
    (h2 : cl ∈ rest → rest.length ≤ calls.length → (∀ x ∈ rest, x ∈ calls) → P) : P := by
  rcases List.mem_cons.mp hcl with rfl | hmem
  · exact (hne rfl).elim
  · rcases List.mem_append.mp hmem with hcs | hrest
    · exact h1 hcs (by simp at hle; omega)
        (fun x hx => hsub x (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
    · exact h2 hrest (by simp at hle; omega)
        (fun x hx => hsub x (List.mem_cons_of_mem _ (List.mem_append_right _ hx)))

private theorem peel_last {P : Prop} {fnName : String} {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {cs calls : List (Call F)} {cl : Call F}
    (ev : ObsFn Obs.W fnName args h r h' cs)
    (hcl : cl ∈ (⟨fnName, args, h⟩ : Call F) :: cs)
    (hle : ((⟨fnName, args, h⟩ : Call F) :: cs).length ≤ calls.length)
    (hsub : ∀ x ∈ ((⟨fnName, args, h⟩ : Call F) :: cs), x ∈ calls)
    (hne : cl.name ≠ fnName)
    (h1 : cl ∈ cs → cs.length < calls.length → (∀ x ∈ cs, x ∈ calls) → P) : P := by
  rcases List.mem_cons.mp hcl with rfl | hcs
  · exact (hne rfl).elim
  · exact h1 hcs (by simp at hle; omega)
      (fun x hx => hsub x (List.mem_cons_of_mem _ hx))

private theorem peel_noKey {fnName : String} (hplain : plainBytes fnName = true) (t : String)
    (hne : fnName ≠ t) :
    ∀ key, Instance.ofSymbol fnName = .ok key → key.name ≠ t := by
  intro key hof
  have hsym := Instance.ofSymbol_symbol ⟨fnName, []⟩ (fun _ => head_ne_dollar_of_plainBytes hplain)
  simp only [Instance.symbol, List.isEmpty_nil, ↓reduceIte] at hsym
  rw [hsym] at hof
  injection hof with hkey
  subst hkey
  exact hne

private theorem peel_noKey_sym {fnName nm : String} {tys : List Ty} {t : String}
    (hsym : (Instance.mk nm tys).symbol = fnName) (htys : tys ≠ []) (hne : nm ≠ t) :
    ∀ key, Instance.ofSymbol fnName = .ok key → key.name ≠ t := by
  intro key hof
  rw [← hsym, Instance.ofSymbol_symbol_of_ne_nil ⟨nm, tys⟩ htys] at hof
  injection hof with hkey
  subst hkey
  exact hne

/-! ## Theorem 1: Every `check_family` call is backed by a non-zero `block_is_modeled` call -/

private theorem obsFn_check_family_modeled_aux (n : Nat) :
    ∀ {fnName : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
      {calls : List (Call F)} {rc xb xrb : SourceValue F} {h_cf : Heap F} {b : Bytes.Address},
      calls.length ≤ n →
      fnName ≠ "KernelModeled::check_modeled_block" →
      (∀ key, Instance.ofSymbol fnName = .ok key → key.name ≠ "KernelModeled::check_modeled_block") →
      ObsFn Obs.W fnName args h r h' calls →
      (⟨"KernelModeled::check_family", [rc, xb, xrb], h_cf⟩ : Call F) ∈ calls →
      Bytes.RepAddressRef IxVM.Refinement.Core.addrTy h_cf b xb →
      ∃ (r_mod : SourceValue F) (m_mod m_mod' : Heap F) (cs_mod : List (Call F)),
        ObsFn Obs.W "KernelModeled::block_is_modeled" [xb] m_mod r_mod m_mod' cs_mod ∧
        r_mod ≠ .field 0 ∧
        Bytes.RepAddressRef IxVM.Refinement.Core.addrTy m_mod b xb ∧
        ∀ cl ∈ cs_mod, cl ∈ calls := by
  induction n with
  | zero =>
    intro fnName args h h' r calls rc xb xrb h_cf b hlen _ _ _ hcl _
    have hnil : calls = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil; simp at hcl
  | succ n ih =>
    intro fnName args h h' r calls rc xb xrb h_cf b hlen hneFn hneKey ev hcl hb
    let cl : Call F := ⟨"KernelModeled::check_family", [rc, xb, xrb], h_cf⟩
    let ts : List String := ["KernelModeled::check_family", "KernelModeled::check_modeled_block"]
    have hplainTs : ∀ t ∈ ts, t.toList.head? ≠ some '$' := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact head_ne_dollar_of_plainBytes (by decide)
      · rcases List.mem_cons.mp ht' with rfl | ht''
        · exact head_ne_dollar_of_plainBytes (by decide)
        · simp at ht''
    have hclIn : cl.name ∈ ts := List.mem_cons_self
    cases hsf : IxVM.program.sourceFunction? fnName with
    | none =>
      have hsfS : IxVM.source.program.sourceFunction? fnName = none := hsf
      have hsub := obsFn_strictSubCall hplainTs hclIn ev (by
        intro types locals expr hprep
        simp only [Obs.W, Source.world, sourceWorld, hsfS, bind, Except.bind] at hprep
        cases hlk : lookupMap IxVM.source.tables fnName args with
        | error e => rw [hlk] at hprep; cases hprep
        | ok c =>
          rw [hlk] at hprep
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprep
          obtain ⟨_, _, rfl⟩ := hprep
          exact ⟨hasCallIn_constantExpr ts c, noDollarCall_constantExpr c⟩) hcl
      obtain ⟨fn', args', h₁, r₁, h₁', cs', ev', hcl', hlt', hsub', hne', hkey'⟩ := hsub
      obtain ⟨rm, mm, mm', csm, evm, hrm, hbm, hsubm⟩ :=
        ih (by omega) (hne' _ (by simp [ts])) (fun k hk => hkey' k hk _ (by simp [ts])) ev' hcl' hb
      exact ⟨rm, mm, mm', csm, evm, hrm, hbm, fun x hx => hsub' x (hsubm x hx)⟩
    | some sf =>
      obtain ⟨key, f, types, hof, hfMem, hfName, harg, hsfEq⟩ := sourceFunction?_fn_detail hsf
      have hnd : noDollarCall f.body = true :=
        (List.all_eq_true.mp ixvm_noDollarCalls) f hfMem
      cases hhas : hasCallIn ts f.body with
      | false =>
        have hsub := obsFn_strictSubCall hplainTs hclIn ev (by
          intro types' locals' expr' hprep
          obtain ⟨_, _, hexpr⟩ := Source.world_prepare_of_sourceFunction hsf hprep
          rw [hexpr, hsfEq]
          exact ⟨hhas, hnd⟩) hcl
        obtain ⟨fn', args', h₁, r₁, h₁', cs', ev', hcl', hlt', hsub', hne', hkey'⟩ := hsub
        obtain ⟨rm, mm, mm', csm, evm, hrm, hbm, hsubm⟩ :=
          ih (by omega) (hne' _ (by simp [ts])) (fun k hk => hkey' k hk _ (by simp [ts])) ev' hcl' hb
        exact ⟨rm, mm, mm', csm, evm, hrm, hbm, fun x hx => hsub' x (hsubm x hx)⟩
      | true =>
        have hcaller := (List.all_eq_true.mp ixvm_callers_check_family) f hfMem
        rw [hhas] at hcaller
        simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, strBytesEq_eq_true] at hcaller
        rcases hcaller with hcc | hcmb
        · -- `f` is `KernelCheck::check_const`
          obtain ⟨evCC, hargLen⟩ := obsFn_retag_mono ev hsf hfMem harg hsfEq hcc
            (head_ne_dollar_of_plainBytes (by decide)) IxVM.KernelCheck.check_const.lookup
          have hlen3 : args.length = 3 := by simpa [IxVM.KernelCheck.check_const] using hargLen
          match args, hlen3, evCC with
          | [a_rc, a_ci, a_addr], _, evCC =>
            let G : Prop :=
              ∃ (r_mod : SourceValue F) (m_mod m_mod' : Heap F) (cs_mod : List (Call F)),
                ObsFn Obs.W "KernelModeled::block_is_modeled" [xb] m_mod r_mod m_mod' cs_mod ∧
                r_mod ≠ .field 0 ∧ Bytes.RepAddressRef IxVM.Refinement.Core.addrTy m_mod b xb ∧
                ∀ x ∈ cs_mod, x ∈ calls
            have useSub : ∀ {fn' args' h₁ r₁ h₁' cs'},
                ObsFn Obs.W fn' args' h₁ r₁ h₁' cs' →
                plainBytes fn' = true → fn' ≠ "KernelModeled::check_modeled_block" →
                cl ∈ cs' → cs'.length < calls.length → (∀ x ∈ cs', x ∈ calls) → G := by
              intro fn' args' h₁ r₁ h₁' cs' ev' hpl' hne' hcl' hlt' hsub'
              obtain ⟨rm, mm, mm', csm, evm, hrm, hbm, hsubm⟩ :=
                ih (by omega) hne' (peel_noKey hpl' _ hne') ev' hcl' hb
              exact ⟨rm, mm, mm', csm, evm, hrm, hbm, fun x hx => hsub' x (hsubm x hx)⟩
            have step : ∀ {fn' args' h₁ r₁ h₁' cs' rest},
                ObsFn Obs.W fn' args' h₁ r₁ h₁' cs' →
                plainBytes fn' = true →
                fn' ≠ "KernelModeled::check_family" →
                fn' ≠ "KernelModeled::check_modeled_block" →
                cl ∈ (⟨fn', args', h₁⟩ : Call F) :: (cs' ++ rest) →
                ((⟨fn', args', h₁⟩ : Call F) :: (cs' ++ rest)).length ≤ calls.length →
                (∀ x ∈ ((⟨fn', args', h₁⟩ : Call F) :: (cs' ++ rest)), x ∈ calls) →
                (cl ∈ rest → rest.length ≤ calls.length → (∀ x ∈ rest, x ∈ calls) → G) → G :=
              fun ev' hpl' hneCF hneCMB hcl' hle' hsub' hrest =>
                peel ev' hcl' hle' hsub' (fun e => hneCF e.symm)
                  (fun h1 h2 h3 => useSub ev' hpl' hneCMB h1 h2 h3) hrest
            have stepLast : ∀ {fn' args' h₁ r₁ h₁' cs'},
                ObsFn Obs.W fn' args' h₁ r₁ h₁' cs' →
                plainBytes fn' = true →
                fn' ≠ "KernelModeled::check_family" →
                fn' ≠ "KernelModeled::check_modeled_block" →
                cl ∈ (⟨fn', args', h₁⟩ : Call F) :: cs' →
                ((⟨fn', args', h₁⟩ : Call F) :: cs').length ≤ calls.length →
                (∀ x ∈ ((⟨fn', args', h₁⟩ : Call F) :: cs'), x ∈ calls) → G :=
              fun ev' hpl' hneCF hneCMB hcl' hle' hsub' =>
                peel_last ev' hcl' hle' hsub' (fun e => hneCF e.symm)
                  (fun h1 h2 h3 => useSub ev' hpl' hneCMB h1 h2 h3)
            have handleCMB : ∀ {rcM blkM rM hM hM' csM m_mod m_mod' r_mod cs_mod},
                ObsFn Obs.W "KernelModeled::check_modeled_block" [rcM, blkM] hM rM hM' csM →
                ObsFn Obs.W "KernelModeled::block_is_modeled" [blkM] m_mod r_mod m_mod' cs_mod →
                r_mod ≠ .field 0 →
                Heap.Extends m_mod hM →
                (∀ x ∈ cs_mod, x ∈ calls) →
                cl ∈ (⟨"KernelModeled::check_modeled_block", [rcM, blkM], hM⟩ : Call F) :: csM →
                ((⟨"KernelModeled::check_modeled_block", [rcM, blkM], hM⟩ : Call F) :: csM).length ≤ calls.length →
                (∀ x ∈ ((⟨"KernelModeled::check_modeled_block", [rcM, blkM], hM⟩ : Call F) :: csM), x ∈ calls) →
                G := by
              intro rcM blkM rM hM hM' csM m_mod m_mod' r_mod cs_mod evM evMod hrm hextMod
                hsubMod hclM hleM hsubM
              rcases List.mem_cons.mp hclM with heq | hcsM
              · have hnm := congrArg Call.name heq; simp [cl] at hnm
              · match Obs.«KernelModeled::check_modeled_block».obs evM with
                | .run (m2 := m2) (cs12 := cs12) (v15 := v15) (m17 := m17) (cs25 := cs25)
                    (x_rb := x_rb) (cs53 := cs53) (ev27 := ev27) (ev14 := ev14c)
                    (ev55 := ev55) (hc80 := hc80) .. =>
                  have hleM' : csM.length ≤ calls.length := by simp at hleM; omega
                  have hsubM' : ∀ x ∈ csM, x ∈ calls := fun x hx => hsubM x (List.mem_cons_of_mem _ hx)
                  rw [hc80] at hcsM hleM' hsubM'
                  refine step ev27 (by decide) (by decide) (by decide) hcsM hleM' hsubM' fun hcsM hleM' hsubM' => ?_
                  refine step ev14c (by decide) (by decide) (by decide) hcsM hleM' hsubM' fun hcsM hleM' hsubM' => ?_
                  rcases List.mem_cons.mp hcsM with heq | hcs53
                  · -- Direct hit: `cl` is `check_family [rcM, blkM, x_rb]` at `m2`!
                    have hargs : [rc, xb, xrb] = [rcM, blkM, x_rb] := congrArg Call.args heq
                    have hheap : h_cf = m2 := congrArg Call.heap heq
                    injection hargs with _ hargs; injection hargs with hxb _
                    subst hxb; subst hheap
                    have hext : Heap.Extends m_mod _ :=
                      hextMod.trans (ev27.heap_extends.trans ev14c.heap_extends)
                    obtain ⟨v_ld, hld⟩ := block_is_modeled_loads_block evMod
                    exact ⟨r_mod, m_mod, m_mod', cs_mod, evMod, hrm,
                      repAddressRef_pullback hext hld hb, hsubMod⟩
                  · exact useSub ev55 (by decide) (by decide) hcs53 (by simp at hleM'; omega)
                      (fun x hx => hsubM' x (List.mem_cons_of_mem _ hx))
            match Obs.«KernelCheck::check_const».obs evCC with
            | .Axiom_n1 (ev14 := ev14) (ev68 := ev68) (ev105 := ev105) (ev149 := ev149)
                (hc184 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev68 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev105 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev149 (by decide) (by decide) (by decide) hcl hle hsub
            | .Axiom_other_n0 (ev14 := ev14) (ev68 := ev68) (ev105 := ev105) (ev149 := ev149)
                (ev203 := ev203) (hc254 := hc) ..
            | .Axiom_other_other (ev14 := ev14) (ev68 := ev68) (ev105 := ev105) (ev149 := ev149)
                (ev203 := ev203) (hc263 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev68 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev105 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev149 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev203 (by decide) (by decide) (by decide) hcl hle hsub
            | .Defn (ev14 := ev14) (ev311 := ev311) (ev348 := ev348) (ev385 := ev385)
                (ev429 := ev429) (ev459 := ev459) (ev481 := ev481) (hc520 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev311 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev348 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev385 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev429 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev459 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev481 (by decide) (by decide) (by decide) hcl hle hsub
            | .Thm (ev14 := ev14) (ev556 := ev556) (ev593 := ev593) (ev630 := ev630)
                (ev685 := ev685) (ev728 := ev728) (ev758 := ev758) (ev780 := ev780)
                (hc819 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev556 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev593 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev630 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev685 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev728 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev758 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev780 (by decide) (by decide) (by decide) hcl hle hsub
            | .Opaque (ev14 := ev14) (ev861 := ev861) (ev898 := ev898) (ev935 := ev935)
                (ev979 := ev979) (ev1009 := ev1009) (ev1031 := ev1031) (hc1070 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev861 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev898 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev935 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev979 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1009 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev1031 (by decide) (by decide) (by decide) hcl hle hsub
            | .Quot (ev14 := ev14) (ev1106 := ev1106) (ev1143 := ev1143) (ev1187 := ev1187)
                (ev1209 := ev1209) (hc1234 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1106 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1143 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1187 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev1209 (by decide) (by decide) (by decide) hcl hle hsub
            | .Induct_n0 (ev14 := ev14) (ev1295 := ev1295) (ev1343 := ev1343) (ev1408 := ev1408)
                (ev1452 := ev1452) (ev1482 := ev1482) (ev1505 := ev1505) (ev1531 := ev1531)
                (ev1609 := ev1609) (hc1634 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1295 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1343 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1408 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1452 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1482 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1505 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1531 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev1609 (by decide) (by decide) (by decide) hcl hle hsub
            | .Induct_other_n0 (cs1503 := cs_mod) (ev14 := ev14) (ev1295 := ev1295) (ev1343 := ev1343)
                (ev1408 := ev1408) (ev1452 := ev1452) (ev1482 := ev1482) (ev1505 := ev1505)
                (hne1635 := hneMod) (ev1663 := ev1663) (ev1711 := ev1711) (ev1759 := ev1759)
                (hm1849 := hm1849) (ev1805 := ev1805) (ev1866 := ev1866) (ev1957 := ev1957)
                (hc1974 := hc) .. =>
              have hsubMod : ∀ x ∈ cs_mod, x ∈ calls := fun x hx => by rw [hc]; simp [hx]
              have hextMod : Heap.Extends _ _ :=
                ev1505.heap_extends.trans (ev1663.heap_extends.trans
                  (ev1711.heap_extends.trans (ev1759.heap_extends.trans
                    ((hm1849 ▸ Heap.Extends.snoc _ _).trans
                      (ev1805.heap_extends.trans ev1866.heap_extends)))))
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1295 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1343 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1408 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1452 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1482 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1505 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1663 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1711 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1759 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1805 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1866 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact handleCMB ev1957 ev1505 hneMod hextMod hsubMod hcl hle hsub
            | .Induct_other_other (ev14 := ev14) (ev1295 := ev1295) (ev1343 := ev1343)
                (ev1408 := ev1408) (ev1452 := ev1452) (ev1482 := ev1482) (ev1505 := ev1505)
                (ev1663 := ev1663) (ev1711 := ev1711) (ev1759 := ev1759) (ev1805 := ev1805)
                (ev1866 := ev1866) (hc1983 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1295 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1343 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1408 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1452 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1482 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1505 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1663 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1711 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1759 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev1805 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev1866 (by decide) (by decide) (by decide) hcl hle hsub
            | .Ctor_n0_n0 (ev14 := ev14) (ev2045 := ev2045) (ev2082 := ev2082) (ev2126 := ev2126)
                (ev2159 := ev2159) (ev2332 := ev2332) (ev2403 := ev2403) (ev2429 := ev2429)
                (ev2475 := ev2475) (ev2536 := ev2536) (ev2588 := ev2588) (hc2613 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2045 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2082 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2126 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2159 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2332 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2403 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2429 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2475 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2536 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev2588 (by decide) (by decide) (by decide) hcl hle hsub
            | .Ctor_n0_other (ev14 := ev14) (ev2045 := ev2045) (ev2082 := ev2082)
                (ev2126 := ev2126) (ev2159 := ev2159) (ev2332 := ev2332) (ev2403 := ev2403)
                (ev2429 := ev2429) (ev2475 := ev2475) (ev2536 := ev2536) (hc2622 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2045 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2082 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2126 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2159 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2332 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2403 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2429 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2475 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev2536 (by decide) (by decide) (by decide) hcl hle hsub
            | .Ctor_other_n0 (cs2401 := cs_mod) (ev14 := ev14) (ev2045 := ev2045) (ev2082 := ev2082)
                (ev2126 := ev2126) (ev2159 := ev2159) (ev2332 := ev2332) (ev2403 := ev2403)
                (hne2623 := hneMod) (ev2651 := ev2651) (ev2694 := ev2694) (hc2711 := hc) .. =>
              have hsubMod : ∀ x ∈ cs_mod, x ∈ calls := fun x hx => by rw [hc]; simp [hx]
              have hextMod : Heap.Extends _ _ :=
                ev2403.heap_extends.trans ev2651.heap_extends
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2045 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2082 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2126 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2159 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2332 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2403 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2651 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact handleCMB ev2694 ev2403 hneMod hextMod hsubMod hcl hle hsub
            | .Ctor_other_other (ev14 := ev14) (ev2045 := ev2045) (ev2082 := ev2082)
                (ev2126 := ev2126) (ev2159 := ev2159) (ev2332 := ev2332) (ev2403 := ev2403)
                (ev2651 := ev2651) (hc2720 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2045 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2082 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2126 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2159 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2332 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2403 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev2651 (by decide) (by decide) (by decide) hcl hle hsub
            | .Rec_n0 (ev14 := ev14) (ev2801 := ev2801) (ev2838 := ev2838) (ev2882 := ev2882)
                (ev2912 := ev2912) (ev2942 := ev2942) (ev2964 := ev2964) (ev2986 := ev2986)
                (ev3068 := ev3068) (hc3093 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2801 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2838 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2882 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2912 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2942 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2964 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2986 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              exact stepLast ev3068 (by decide) (by decide) (by decide) hcl hle hsub
            | .Rec_other (cs2984 := cs_mod) (ev14 := ev14) (ev2801 := ev2801) (ev2838 := ev2838) (ev2882 := ev2882)
                (ev2912 := ev2912) (ev2942 := ev2942) (ev2964 := ev2964) (ev2986 := ev2986)
                (hne3094 := hneMod) (ev3157 := ev3157) (hc3182 := hc) .. =>
              have hsubMod : ∀ x ∈ cs_mod, x ∈ calls := fun x hx => by rw [hc]; simp [hx]
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine step ev14 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2801 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2838 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2882 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2912 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2942 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2964 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              refine step ev2986 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
              rcases List.mem_cons.mp hcl with heq | hcs3155
              · have hargs : [rc, xb, xrb] = _ := congrArg Call.args heq
                have hheap : h_cf = _ := congrArg Call.heap heq
                injection hargs with _ hargs; injection hargs with hxb _
                subst hxb; subst hheap
                obtain ⟨v_ld, hld⟩ := block_is_modeled_loads_block ev2986
                exact ⟨_, _, _, _, ev2986, hneMod,
                  repAddressRef_pullback ev2986.heap_extends hld hb, hsubMod⟩
              · exact useSub ev3157 (by decide) (by decide) hcs3155 (by simp at hle; omega)
                  (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
        · -- `f` is `KernelModeled::check_modeled_block`: ruled out by `hneKey`.
          exact (hneKey key hof (hfName.symm.trans hcmb)).elim

/-- **Every `check_family` call in a top-level derivation (whose callee is not
`check_modeled_block`) is backed by a non-zero `block_is_modeled` observation on the same
block.** -/
theorem obsFn_check_family_modeled {fnName : String} {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    {rc xb xrb : SourceValue F} {h_cf : Heap F} {b : Bytes.Address}
    (hplain : fnName.toList.head? ≠ some '$')
    (hne : fnName ≠ "KernelModeled::check_modeled_block")
    (ev : ObsFn Obs.W fnName args h r h' calls)
    (hcl : (⟨"KernelModeled::check_family", [rc, xb, xrb], h_cf⟩ : Call F) ∈ calls)
    (hb : Bytes.RepAddressRef IxVM.Refinement.Core.addrTy h_cf b xb) :
    ∃ (r_mod : SourceValue F) (m_mod m_mod' : Heap F) (cs_mod : List (Call F)),
      ObsFn Obs.W "KernelModeled::block_is_modeled" [xb] m_mod r_mod m_mod' cs_mod ∧
      r_mod ≠ .field 0 ∧
      Bytes.RepAddressRef IxVM.Refinement.Core.addrTy m_mod b xb ∧
      ∀ cl ∈ cs_mod, cl ∈ calls := by
  have hkey : ∀ key, Instance.ofSymbol fnName = .ok key →
      key.name ≠ "KernelModeled::check_modeled_block" := by
    intro key hof
    have hsym := Instance.ofSymbol_symbol ⟨fnName, []⟩ (fun _ => hplain)
    simp only [Instance.symbol, List.isEmpty_nil, ↓reduceIte] at hsym
    rw [hsym] at hof
    injection hof with hk; subst hk; exact hne
  exact obsFn_check_family_modeled_aux calls.length (Nat.le_refl _) hne hkey ev hcl hb

/-! ## Theorem 2: Every `check_witness` call inside `check_family` lies in an enclosing
`check_family`'s `check_witnesses` loop -/

/-- `check_witnesses` returns a linked list of `SourceValue F` pointers. -/
private theorem check_witnesses_repList_aux (n : Nat) :
    ∀ {rc xb xs xn xlist xend : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ n →
      ObsFn Obs.W "KernelModeled::check_witnesses" [rc, xb, xs, xn] h (.tuple [xlist, xend]) h' cs →
      ∃ elems : List (SourceValue F),
        List.RepList Obs.Names.«Lists::Node<&[Field; 32]>» (fun _ a b => a = b) h' elems xlist := by
  induction n with
  | zero =>
    intro rc xb xs xn xlist xend h h' cs hlen ev
    match Obs.«KernelModeled::check_witnesses».obs ev with
    | .n0 (he19 := he19) (hm29 := hm29) (he40 := he40) .. =>
      injection he19 with hpair
      injection hpair with hlist _
      subst hlist; subst he40; subst hm29
      exact ⟨[], List.allocNil_rep _ _ h⟩
    | .other (hc292 := hc) .. =>
      rw [hc] at hlen; simp at hlen
  | succ n ih =>
    intro rc xb xs xn xlist xend h h' cs hlen ev
    match Obs.«KernelModeled::check_witnesses».obs ev with
    | .n0 (he19 := he19) (hm29 := hm29) (he40 := he40) .. =>
      injection he19 with hpair
      injection hpair with hlist _
      subst hlist; subst he40; subst hm29
      exact ⟨[], List.allocNil_rep _ _ h⟩
    | .other (x_x := x_x) (x_rest := x_rest) (cs194 := cs194) (ev196 := ev196)
        (he254 := he254) (hm264 := hm264) (he291 := he291) (hc292 := hc) .. =>
      have hlt : cs194.length < cs.length := by rw [hc]; simp; omega
      obtain ⟨elems, hrep⟩ := ih (by omega) ev196
      injection he254 with hpair
      injection hpair with hlist _
      subst hlist; subst he291; subst hm264
      exact ⟨x_x :: elems, List.allocCons_rep _ (fun _ _ _ _ _ h => h) rfl hrep⟩

/-- Every `check_witness` call inside `check_witnesses` is either a direct witness step of that
loop (putting its witness value in the returned list) or lies inside a strictly shorter
non-`check_witnesses` subcall. -/
private theorem check_witnesses_descend_aux (n : Nat) :
    ∀ {rc₀ xb₀ xs xn xlist xend : SourceValue F} {h_ws h_ws' : Heap F} {cs_ws : List (Call F)}
      {rc xb xx kind s : SourceValue F} {h_w : Heap F},
      cs_ws.length ≤ n →
      ObsFn Obs.W "KernelModeled::check_witnesses" [rc₀, xb₀, xs, xn] h_ws
        (.tuple [xlist, xend]) h_ws' cs_ws →
      (⟨"KernelModeled::check_witness", [rc, xb, xx, kind, s], h_w⟩ : Call F) ∈ cs_ws →
      (rc = rc₀ ∧ xb = xb₀ ∧
        ∃ (v_w : SourceValue F) (m_w : Heap F) (cs_w : List (Call F))
          (elems : List (SourceValue F)),
          ObsFn Obs.W "KernelModeled::check_witness" [rc, xb, xx, kind, s] h_w v_w m_w cs_w ∧
          (∀ cl ∈ cs_w, cl ∈ cs_ws) ∧
          Heap.Extends h_ws h_w ∧ Heap.Extends m_w h_ws' ∧
          List.RepList Obs.Names.«Lists::Node<&[Field; 32]>» (fun _ a b => a = b) h_ws' elems xlist ∧
          xx ∈ elems) ∨
      StrictSubCall ["KernelModeled::check_witnesses"]
        ⟨"KernelModeled::check_witness", [rc, xb, xx, kind, s], h_w⟩ cs_ws := by
  induction n with
  | zero =>
    intro rc₀ xb₀ xs xn xlist xend h_ws h_ws' cs_ws rc xb xx kind s h_w hlen _ hcl
    have hnil : cs_ws = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil; simp at hcl
  | succ n ih =>
    intro rc₀ xb₀ xs xn xlist xend h_ws h_ws' cs_ws rc xb xx kind s h_w hlen ev hcl
    let cl : Call F := ⟨"KernelModeled::check_witness", [rc, xb, xx, kind, s], h_w⟩
    let ts : List String := ["KernelModeled::check_witnesses"]
    match Obs.«KernelModeled::check_witnesses».obs ev with
    | .n0 (hc41 := hc) .. =>
      rw [hc] at hcl; simp at hcl
    | .other (x_x := x_x) (x_rest := x_rest) (cs194 := cs194) (ev59 := ev59) (ev94 := ev94)
        (ev_updedcyj := evOrd) (ev167 := ev167) (ev129 := ev129) (ev196 := ev196)
        (he254 := he254) (hm264 := hm264) (he291 := he291) (hc292 := hc) .. =>
      have mkSub : ∀ {fn' args' h₁ r₁ h₁' cs'},
          ObsFn Obs.W fn' args' h₁ r₁ h₁' cs' →
          plainBytes fn' = true →
          fn' ≠ "KernelModeled::check_witnesses" →
          cl ∈ cs' → cs'.length < cs_ws.length → (∀ x ∈ cs', x ∈ cs_ws) →
          (rc = rc₀ ∧ xb = xb₀ ∧
            ∃ (v_w : SourceValue F) (m_w : Heap F) (cs_w : List (Call F))
              (elems : List (SourceValue F)),
              ObsFn Obs.W "KernelModeled::check_witness" [rc, xb, xx, kind, s] h_w v_w m_w cs_w ∧
              (∀ cl ∈ cs_w, cl ∈ cs_ws) ∧
              Heap.Extends h_ws h_w ∧ Heap.Extends m_w h_ws' ∧
              List.RepList Obs.Names.«Lists::Node<&[Field; 32]>» (fun _ a b => a = b) h_ws' elems xlist ∧
              xx ∈ elems) ∨
          StrictSubCall ts cl cs_ws :=
        fun ev' hpl' hneWS hcl' hlt' hsub' =>
          Or.inr ⟨_, _, _, _, _, _, ev', hcl', hlt', hsub',
            fun t ht => by
              rcases List.mem_cons.mp ht with rfl | ht'
              · exact hneWS
              · simp at ht',
            fun key hof t ht => by
              rcases List.mem_cons.mp ht with rfl | ht'
              · exact peel_noKey hpl' _ hneWS key hof
              · simp at ht'⟩
      refine peel_eq hc hcl fun hcl hle hsub => ?_
      refine peel ev59 hcl hle hsub (by simp [cl])
        (fun h1 h2 h3 => mkSub ev59 (by decide) (by decide) h1 h2 h3)
        fun hcl hle hsub => ?_
      refine peel ev94 hcl hle hsub (by simp [cl])
        (fun h1 h2 h3 => mkSub ev94 (by decide) (by decide) h1 h2 h3)
        fun hcl hle hsub => ?_
      refine peel evOrd hcl hle hsub (by simp [cl])
        (fun h1 h2 h3 => mkSub evOrd (by decide) (by decide) h1 h2 h3)
        fun hcl hle hsub => ?_
      refine peel ev167 hcl hle hsub (by simp [cl])
        (fun h1 h2 h3 => mkSub ev167 (by decide) (by decide) h1 h2 h3)
        fun hcl hle hsub => ?_
      rcases List.mem_cons.mp hcl with heq | hmem
      · -- Direct hit at the head `ev129`!
        have hargs : [rc, xb, xx, kind, s] = _ := congrArg Call.args heq
        have hheap : h_w = _ := congrArg Call.heap heq
        injection hargs with hrc hargs; injection hargs with hxb hargs
        injection hargs with hxx hargs; injection hargs with hkind hargs
        injection hargs with hs _
        subst hrc hxb hxx hkind hs hheap
        obtain ⟨elems, hrepRest⟩ := check_witnesses_repList_aux _ (Nat.le_refl _) ev196
        injection he254 with hpair; injection hpair with hlist _
        subst hlist; subst he291; subst hm264
        have hrepCons := List.allocCons_rep _ (fun _ _ _ _ _ h => h) (x := xx) rfl hrepRest
        have hext1 : Heap.Extends h_ws _ :=
          ev59.heap_extends.trans (ev94.heap_extends.trans
            (evOrd.heap_extends.trans ev167.heap_extends))
        exact Or.inl ⟨rfl, rfl, _, _, _, xx :: elems, ev129,
          fun x hx => hsub x (List.mem_cons_of_mem _ (List.mem_append_left _ hx)),
          hext1, ev196.heap_extends.trans (Heap.Extends.snoc _ _), hrepCons, List.mem_cons_self⟩
      · rcases List.mem_append.mp hmem with hcs127 | hrest
        · exact mkSub ev129 (by decide) (by decide) hcs127 (by simp at hle; omega)
            (fun x hx => hsub x (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
        · rcases List.mem_cons.mp hrest with heq | hcs194
          · have hnm := congrArg Call.name heq; simp [cl] at hnm
          · have hlt194 : cs194.length < cs_ws.length := by simp at hle; omega
            rcases ih (by omega) ev196 hcs194 with
              ⟨hrc, hxb, vw, mw, csw, elems, evw, hsubw, hext1, hext2, hrepRest, hmemEl⟩ | hsc
            · subst hrc hxb
              injection he254 with hpair; injection hpair with hlist _
              subst hlist; subst he291; subst hm264
              have hrepCons := List.allocCons_rep _ (fun _ _ _ _ _ h => h) (x := x_x) rfl hrepRest
              have hextPre : Heap.Extends h_ws _ :=
                ev59.heap_extends.trans (ev94.heap_extends.trans
                  (evOrd.heap_extends.trans (ev167.heap_extends.trans ev129.heap_extends)))
              exact Or.inl ⟨rfl, rfl, vw, mw, csw, x_x :: elems, evw,
                fun x hx => hsub x (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (hsubw x hx)))),
                hextPre.trans hext1, hext2.trans (Heap.Extends.snoc _ _),
                hrepCons, List.mem_cons_of_mem _ hmemEl⟩
            · obtain ⟨fn', args', h₁, r₁, h₁', cs', ev', hcl', hlt', hsub', hne', hkey'⟩ := hsc
              exact Or.inr ⟨fn', args', h₁, r₁, h₁', cs', ev', hcl',
                Nat.lt_trans hlt' hlt194,
                fun x hx => hsub x (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (hsub' x hx)))),
                hne', hkey'⟩

/-- The enclosing `check_family` data returned for any `check_witness` call inside `calls`. -/
inductive EnclosingFamilyWitness (calls : List (Call F))
    (rc xb xx kind s : SourceValue F) (h_w : Heap F) : Prop where
  | mk
      (m_rp : Heap F) (v_rp : SourceValue F) (m_rp' : Heap F) (cs_rp : List (Call F))
      (ev_rp : ObsFn Obs.W "KernelModeled::read_payload" [xb] m_rp v_rp m_rp' cs_rp)
      (m_ws : Heap F) (x_s4 x_nw : SourceValue F)
      (ev_pre_ws : ∃ x_rb x_s1 m_ga cs_ga x_na x_s2 m_gc1 cs_gc1 m_gc1' x_adv x_s3 m_gas cs_gas cs_gc2,
        ObsFn Obs.W "IxonDeserialize::get_address" [v_rp] m_rp' (.tuple [x_rb, x_s1]) m_ga cs_ga ∧
        Heap.Extends m_ga m_gc1 ∧
        ObsFn Obs.W "KernelModeled::get_count" [x_s1] m_gc1 (.tuple [x_na, x_s2]) m_gc1' cs_gc1 ∧
        ObsFn Obs.W "KernelModeled::get_addrs" [x_s2, x_na] m_gc1' (.tuple [x_adv, x_s3]) m_gas cs_gas ∧
        ObsFn Obs.W "KernelModeled::get_count" [x_s3] m_gas (.tuple [x_nw, x_s4]) m_ws cs_gc2)
      (x_outside x_s5 : SourceValue F) (m_ws' : Heap F)
      (cs_ws : List (Call F))
      (ev_ws : ObsFn Obs.W "KernelModeled::check_witnesses" [rc, xb, x_s4, x_nw]
        m_ws (.tuple [x_outside, x_s5]) m_ws' cs_ws)
      (wset : SourceValue F) (m_asb : Heap F) (cs_asb : List (Call F))
      (ev_asb : ObsFn Obs.W "KernelClaim::addr_set_build"
        [x_outside, .construct Obs.Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []]
        m_ws' wset m_asb cs_asb)
      (v_cr : SourceValue F) (m_cr : Heap F) (cs_cr : List (Call F))
      (ev_cr : ObsFn Obs.W "KernelModeled::container_recs_refs" [rc, x_outside, wset]
        m_asb v_cr m_cr cs_cr)
      (v_w : SourceValue F) (m_w : Heap F) (cs_w : List (Call F))
      (ev_w : ObsFn Obs.W "KernelModeled::check_witness" [rc, xb, xx, kind, s] h_w v_w m_w cs_w)
      (ext_rp_ws : Heap.Extends m_rp m_ws)
      (ext_ws_w : Heap.Extends m_ws h_w)
      (ext_w_ws' : Heap.Extends m_w m_ws')
      (sub_ws : ∀ cl ∈ cs_ws, cl ∈ calls)
      (sub_asb : ∀ cl ∈ cs_asb, cl ∈ calls)
      (sub_cr : ∀ cl ∈ cs_cr, cl ∈ calls)
      (sub_w : ∀ cl ∈ cs_w, cl ∈ cs_ws)
      (elems : List (SourceValue F))
      (outsideRep : List.RepList Obs.Names.«Lists::Node<&[Field; 32]>» (fun _ a b => a = b)
        m_ws' elems x_outside)
      (memOutside : xx ∈ elems)

theorem EnclosingFamilyWitness.mono {cs₁ cs₂ : List (Call F)}
    {rc xb xx kind s : SourceValue F} {h_w : Heap F}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂)
    (e : EnclosingFamilyWitness cs₁ rc xb xx kind s h_w) :
    EnclosingFamilyWitness cs₂ rc xb xx kind s h_w := by
  rcases e with ⟨m_rp, v_rp, m_rp', cs_rp, ev_rp, m_ws, x_s4, x_nw, ev_pre_ws, x_outside, x_s5,
    m_ws', cs_ws, ev_ws, wset, m_asb, cs_asb, ev_asb, v_cr, m_cr, cs_cr, ev_cr, v_w, m_w, cs_w,
    ev_w, ext_rp_ws, ext_ws_w, ext_w_ws', sub_ws, sub_asb, sub_cr, sub_w, elems, outsideRep,
    memOutside⟩
  exact ⟨m_rp, v_rp, m_rp', cs_rp, ev_rp, m_ws, x_s4, x_nw, ev_pre_ws, x_outside, x_s5, m_ws',
    cs_ws, ev_ws, wset, m_asb, cs_asb, ev_asb, v_cr, m_cr, cs_cr, ev_cr, v_w, m_w, cs_w, ev_w,
    ext_rp_ws, ext_ws_w, ext_w_ws',
    fun cl h => hsub cl (sub_ws cl h),
    fun cl h => hsub cl (sub_asb cl h),
    fun cl h => hsub cl (sub_cr cl h),
    sub_w, elems, outsideRep, memOutside⟩

private theorem obsFn_check_witness_enclosing_aux (n : Nat) :
    ∀ {fnName : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
      {calls : List (Call F)} {rc xb xx kind s : SourceValue F} {h_w : Heap F},
      calls.length ≤ n →
      fnName ≠ "KernelModeled::check_witnesses" →
      (∀ key, Instance.ofSymbol fnName = .ok key → key.name ≠ "KernelModeled::check_witnesses") →
      ObsFn Obs.W fnName args h r h' calls →
      (⟨"KernelModeled::check_witness", [rc, xb, xx, kind, s], h_w⟩ : Call F) ∈ calls →
      EnclosingFamilyWitness calls rc xb xx kind s h_w := by
  induction n with
  | zero =>
    intro fnName args h h' r calls rc xb xx kind s h_w hlen _ _ _ hcl
    have hnil : calls = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil; simp at hcl
  | succ n ih =>
    intro fnName args h h' r calls rc xb xx kind s h_w hlen hneFn hneKey ev hcl
    let cl : Call F := ⟨"KernelModeled::check_witness", [rc, xb, xx, kind, s], h_w⟩
    let ts : List String := ["KernelModeled::check_witness", "KernelModeled::check_witnesses"]
    have hplainTs : ∀ t ∈ ts, t.toList.head? ≠ some '$' := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact head_ne_dollar_of_plainBytes (by decide)
      · rcases List.mem_cons.mp ht' with rfl | ht''
        · exact head_ne_dollar_of_plainBytes (by decide)
        · simp at ht''
    have hclIn : cl.name ∈ ts := List.mem_cons_self
    cases hsf : IxVM.program.sourceFunction? fnName with
    | none =>
      have hsfS : IxVM.source.program.sourceFunction? fnName = none := hsf
      have hsub := obsFn_strictSubCall hplainTs hclIn ev (by
        intro types locals expr hprep
        simp only [Obs.W, Source.world, sourceWorld, hsfS, bind, Except.bind] at hprep
        cases hlk : lookupMap IxVM.source.tables fnName args with
        | error e => rw [hlk] at hprep; cases hprep
        | ok c =>
          rw [hlk] at hprep
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hprep
          obtain ⟨_, _, rfl⟩ := hprep
          exact ⟨hasCallIn_constantExpr ts c, noDollarCall_constantExpr c⟩) hcl
      obtain ⟨fn', args', h₁, r₁, h₁', cs', ev', hcl', hlt', hsub', hne', hkey'⟩ := hsub
      exact (ih (by omega) (hne' _ (by simp [ts])) (fun k hk => hkey' k hk _ (by simp [ts]))
        ev' hcl').mono hsub'
    | some sf =>
      obtain ⟨key, f, types, hof, hfMem, hfName, harg, hsfEq⟩ := sourceFunction?_fn_detail hsf
      have hnd : noDollarCall f.body = true :=
        (List.all_eq_true.mp ixvm_noDollarCalls) f hfMem
      cases hhas : hasCallIn ts f.body with
      | false =>
        have hsub := obsFn_strictSubCall hplainTs hclIn ev (by
          intro types' locals' expr' hprep
          obtain ⟨_, _, hexpr⟩ := Source.world_prepare_of_sourceFunction hsf hprep
          rw [hexpr, hsfEq]
          exact ⟨hhas, hnd⟩) hcl
        obtain ⟨fn', args', h₁, r₁, h₁', cs', ev', hcl', hlt', hsub', hne', hkey'⟩ := hsub
        exact (ih (by omega) (hne' _ (by simp [ts])) (fun k hk => hkey' k hk _ (by simp [ts]))
          ev' hcl').mono hsub'
      | true =>
        have hcaller := (List.all_eq_true.mp ixvm_callers_check_witness) f hfMem
        rw [hhas] at hcaller
        simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, strBytesEq_eq_true] at hcaller
        rcases hcaller with hcf | hcws
        · -- `f` is `KernelModeled::check_family`
          obtain ⟨evCF, hargLen⟩ := obsFn_retag_mono ev hsf hfMem harg hsfEq hcf
            (head_ne_dollar_of_plainBytes (by decide)) IxVM.KernelModeled.check_family.lookup
          have hlen3 : args.length = 3 := by simpa [IxVM.KernelModeled.check_family] using hargLen
          match args, hlen3, evCF with
          | [a_rc, a_blk, a_rb], _, evCF =>
            let G : Prop := EnclosingFamilyWitness calls rc xb xx kind s h_w
            have useSub : ∀ {fn' args' h₁ r₁ h₁' cs'},
                ObsFn Obs.W fn' args' h₁ r₁ h₁' cs' →
                (∀ key, Instance.ofSymbol fn' = .ok key → key.name ≠ "KernelModeled::check_witnesses") →
                fn' ≠ "KernelModeled::check_witnesses" →
                cl ∈ cs' → cs'.length < calls.length → (∀ x ∈ cs', x ∈ calls) → G :=
              fun ev' hnoKey' hne' hcl' hlt' hsub' =>
                (ih (by omega) hne' hnoKey' ev' hcl').mono hsub'
            have step : ∀ {fn' args' h₁ r₁ h₁' cs' rest},
                ObsFn Obs.W fn' args' h₁ r₁ h₁' cs' →
                plainBytes fn' = true →
                fn' ≠ "KernelModeled::check_witness" →
                fn' ≠ "KernelModeled::check_witnesses" →
                cl ∈ (⟨fn', args', h₁⟩ : Call F) :: (cs' ++ rest) →
                ((⟨fn', args', h₁⟩ : Call F) :: (cs' ++ rest)).length ≤ calls.length →
                (∀ x ∈ ((⟨fn', args', h₁⟩ : Call F) :: (cs' ++ rest)), x ∈ calls) →
                (cl ∈ rest → rest.length ≤ calls.length → (∀ x ∈ rest, x ∈ calls) → G) → G :=
              fun ev' hpl' hneW hneWS hcl' hle' hsub' hrest =>
                peel ev' hcl' hle' hsub' (fun e => hneW e.symm)
                  (fun h1 h2 h3 => useSub ev' (peel_noKey hpl' _ hneWS) hneWS h1 h2 h3) hrest
            have stepSym : ∀ {fn' nm : String} {tys : List Ty} {args' h₁ r₁ h₁' cs' rest},
                ObsFn Obs.W fn' args' h₁ r₁ h₁' cs' →
                (Instance.mk nm tys).symbol = fn' →
                tys ≠ [] →
                nm ≠ "KernelModeled::check_witnesses" →
                fn' ≠ "KernelModeled::check_witness" →
                fn' ≠ "KernelModeled::check_witnesses" →
                cl ∈ (⟨fn', args', h₁⟩ : Call F) :: (cs' ++ rest) →
                ((⟨fn', args', h₁⟩ : Call F) :: (cs' ++ rest)).length ≤ calls.length →
                (∀ x ∈ ((⟨fn', args', h₁⟩ : Call F) :: (cs' ++ rest)), x ∈ calls) →
                (cl ∈ rest → rest.length ≤ calls.length → (∀ x ∈ rest, x ∈ calls) → G) → G :=
              fun ev' hsym' htys' hneNm hneW hneWS hcl' hle' hsub' hrest =>
                peel ev' hcl' hle' hsub' (fun e => hneW e.symm)
                  (fun h1 h2 h3 => useSub ev' (peel_noKey_sym hsym' htys' hneNm) hneWS h1 h2 h3) hrest
            have stepLast : ∀ {fn' args' h₁ r₁ h₁' cs'},
                ObsFn Obs.W fn' args' h₁ r₁ h₁' cs' →
                plainBytes fn' = true →
                fn' ≠ "KernelModeled::check_witness" →
                fn' ≠ "KernelModeled::check_witnesses" →
                cl ∈ (⟨fn', args', h₁⟩ : Call F) :: cs' →
                ((⟨fn', args', h₁⟩ : Call F) :: cs').length ≤ calls.length →
                (∀ x ∈ ((⟨fn', args', h₁⟩ : Call F) :: cs'), x ∈ calls) → G :=
              fun ev' hpl' hneW hneWS hcl' hle' hsub' =>
                peel_last ev' hcl' hle' hsub' (fun e => hneW e.symm)
                  (fun h1 h2 h3 => useSub ev' (peel_noKey hpl' _ hneWS) hneWS h1 h2 h3)
            match Obs.«KernelModeled::check_family».obs evCF with
            | .run (m105 := m105) (m297 := m297) (cs107 := cs107) (cs401 := cs401) (cs433 := cs433) (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
                (ev_yqjbwijz := evOrd) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309)
                (ev344 := ev344) (ev403 := ev403) (ev435 := ev435) (ev465 := ev465)
                (ev513 := ev513) (ev601 := ev601) (ev634 := ev634) (ev664 := ev664)
                (ev686 := ev686) (ev716 := ev716) (ev759 := ev759) (ev817 := ev817)
                (ev796 := ev796) (ev852 := ev852) (ev_ursqbimm := evNoRole) (ev874 := ev874)
                (ev896 := ev896) (ev960 := ev960) (ev939 := ev939) (ev1011 := ev1011)
                (ev990 := ev990) (ev_edyzsqzv := evMV1) (ev_gkddqxhv := evCat)
                (ev_ittpynob := evMV2) (ev_biaifgpd := evMV3) (ev1203 := ev1203)
                (ev_cwwgzxtj := evFlat) (ev1246 := ev1246) (ev_mitevvsv := evLenF)
                (ev_rqpeovbn := evIz1) (ev_xrhmaojz := evIz2) (ev_whimdwjd := evVal)
                (ev1305 := ev1305) (ev1343 := ev1343) (hc1474 := hc) .. =>
              refine peel_eq hc hcl fun hcl hle hsub => ?_
              refine peel_append hcl hle hsub (fun hcs107 hle107 hsub107 => ?_)
                fun hcl hle hsub => ?_
              · -- Inside `sg112` (`KernelRoles::role_ctx_axioms`)
                cases sg112 with
                | Nil _ _ ev15 _ _ hc34 =>
                  rw [hc34] at hcs107 hle107 hsub107
                  exact stepLast ev15 (by decide) (by decide) (by decide) hcs107 hle107 hsub107
                | Node _ _ _ _ _ _ _ ev15 _ _ _ hc102 =>
                  rw [hc102] at hcs107 hle107 hsub107
                  exact stepLast ev15 (by decide) (by decide) (by decide) hcs107 hle107 hsub107
              · refine step ev126 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                refine step ev148 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                refine step ev194 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                refine step evOrd (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                refine step ev231 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                refine step ev266 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                refine step ev309 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                -- Now at `ev344 : check_witnesses`!
                refine peel ev344 hcl hle hsub (by simp [cl]) (fun hcs342 hlt342 hsub342 => ?_)
                  fun hcl hle hsub => ?_
                · -- Inside `ev344`: either direct hit (DONE!) or nested subcall (apply strong IH).
                  rcases check_witnesses_descend_aux _ (Nat.le_refl _) ev344 hcs342 with
                    ⟨hrc, hxb, vw, mw, csw, elems, evw, hsubw, hext1, hext2, hrepOut, hmemOut⟩ | hsc
                  · subst hrc hxb
                    have hext_rp_ws : Heap.Extends m105 m297 :=
                      ev126.heap_extends.trans <| ev148.heap_extends.trans <|
                        ev194.heap_extends.trans <| evOrd.heap_extends.trans <|
                        ev231.heap_extends.trans <| ev266.heap_extends.trans <| ev309.heap_extends
                    have hsub_asb : ∀ x ∈ cs401, x ∈ calls := fun x hx =>
                      hsub x (List.mem_cons_of_mem _ (List.mem_append_right _
                        (List.mem_cons_of_mem _ (List.mem_append_left _ hx))))
                    have hsub_cr : ∀ x ∈ cs433, x ∈ calls := fun x hx =>
                      hsub x (List.mem_cons_of_mem _ (List.mem_append_right _
                        (List.mem_cons_of_mem _ (List.mem_append_right _
                          (List.mem_cons_of_mem _ (List.mem_append_left _ hx))))))
                    exact .mk (ev_rp := ev126)
                      (ev_pre_ws := ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ev148,
                        ev194.heap_extends.trans evOrd.heap_extends, ev231, ev266, ev309⟩)
                      (ev_ws := ev344) (ev_asb := ev403)
                      (ev_cr := ev435) (ev_w := evw) (ext_rp_ws := hext_rp_ws)
                      (ext_ws_w := hext1) (ext_w_ws' := hext2)
                      (sub_ws := hsub342) (sub_asb := hsub_asb) (sub_cr := hsub_cr)
                      (sub_w := hsubw) (elems := elems)
                      (outsideRep := hrepOut) (memOutside := hmemOut)
                  · obtain ⟨fn', args', h₁, r₁, h₁', cs', ev', hcl', hlt', hsub', hne', hkey'⟩ := hsc
                    exact (ih (by omega) (hne' _ List.mem_cons_self)
                      (fun k hk => hkey' k hk _ List.mem_cons_self) ev' hcl').mono
                      (fun x hx => hsub342 x (hsub' x hx))
                · -- Remaining 33 calls of `check_family` after `ev344`
                  refine step ev403 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev435 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev465 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev513 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine stepSym ev601 Obs.Names.«Lists::length<Ixon::MutConst>».symbol (by simp) (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev634 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev664 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev686 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev716 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev759 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine stepSym ev817 Obs.Names.«Lists::length<&[Field; 32]>».symbol (by simp) (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev796 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev852 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step evNoRole (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine stepSym ev874 Obs.Names.«Lists::length<&[Field; 32]>».symbol (by simp) (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev896 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine stepSym ev960 Obs.Names.«Lists::concat<&[Field; 32]>».symbol (by simp) (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine stepSym ev939 Obs.Names.«Lists::concat<&[Field; 32]>».symbol (by simp) (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine stepSym ev1011 Obs.Names.«Lists::concat<&[Field; 32]>».symbol (by simp) (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine stepSym ev990 Obs.Names.«Lists::concat<&[Field; 32]>».symbol (by simp) (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step evMV1 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine stepSym evCat Obs.Names.«Lists::concat<&[Field; 32]>».symbol (by simp) (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step evMV2 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step evMV3 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev1203 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step evFlat (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev1246 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine stepSym evLenF Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol (by simp) (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step evIz1 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step evIz2 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step evVal (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  refine step ev1305 (by decide) (by decide) (by decide) hcl hle hsub fun hcl hle hsub => ?_
                  exact stepLast ev1343 (by decide) (by decide) (by decide) hcl hle hsub
        · -- `f` is `KernelModeled::check_witnesses`: ruled out by `hneKey`.
          exact (hneKey key hof (hfName.symm.trans hcws)).elim

/-- **Every `check_witness` call inside a `check_family` derivation lies directly in the
`check_witnesses` loop of an enclosing `check_family` derivation whose subcalls lie in `cs`.** -/
theorem obsFn_check_witness_enclosing_family
    {rc₀ xb₀ xrb₀ r₀ : SourceValue F} {h₀ h₀' : Heap F} {cs : List (Call F)}
    {rc xb xx kind s : SourceValue F} {h_w : Heap F}
    (ev : ObsFn Obs.W "KernelModeled::check_family" [rc₀, xb₀, xrb₀] h₀ r₀ h₀' cs)
    (hcl : (⟨"KernelModeled::check_witness", [rc, xb, xx, kind, s], h_w⟩ : Call F) ∈ cs) :
    EnclosingFamilyWitness cs rc xb xx kind s h_w :=
  obsFn_check_witness_enclosing_aux cs.length (Nat.le_refl _) (by decide)
    (peel_noKey (by decide) _ (by decide)) ev hcl

end IxVM.Refinement.Typing
