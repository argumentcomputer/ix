import IxCC.Lam.Erase.Proof.RecStar

/-! # Bound arguments and saturated heads

A saturated special head is fired by SrcEval on the slots of its arguments,
evaluated left to right; erasure `let`-binds the relevant strict ones in the
same order (`bindArgs`) and builds the head's form over the references. This
module has the shape facts of `BindR`, SrcEval's unfolding of a saturated
spine and of a constructor's firing, and the results of `Nat.succ` and of an
unboxed constructor, for the erasure simulation. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)
open IxCC.Sem (Result ClockMono SimUpTo later later_succ)

/-! ## Lets and lists -/

theorem eval_wrapLets_cons (P : Program) (k : Nat) (ρ : Env) (v : Term) (lets : List Term)
    (X : Term) :
    Lam.eval P k ρ (wrapLets (v :: lets) X) =
      (Lam.eval P k ρ v).bind fun x => Lam.eval P k (.val x :: ρ) (wrapLets lets X) :=
  Lam.eval_letE P k ρ _ _ _

theorem evalList_append_single (P : Program) (k : Nat) (ρ : Env) (t : Term) :
    ∀ ts : List Term, Lam.evalList P k ρ (ts ++ [t]) =
      (Lam.evalList P k ρ ts).bind fun vs => (Lam.eval P k ρ t).bind fun v => .ok (vs ++ [v])
  | [] => by
    simp only [List.nil_append, Lam.evalList_cons, Lam.evalList_nil, Sem.Result.bind_ok,
      List.nil_append]
  | t' :: ts => by
    simp only [List.cons_append, Lam.evalList_cons, Sem.Result.bind_assoc]
    apply Sem.Result.bind_congr
    intro v
    rw [evalList_append_single P k ρ t ts, Sem.Result.bind_assoc]
    apply Sem.Result.bind_congr
    intro vs
    rw [Sem.Result.bind_ok, Sem.Result.bind_assoc]
    apply Sem.Result.bind_congr
    intro w
    rfl

theorem eval_evalList_single (P : Program) (k : Nat) (ρ : Env) (t : Term) :
    Lam.eval P k ρ t = (Lam.evalList P k ρ [t]).bind fun vs => .ok (vs.headD .box) := by
  simp only [Lam.evalList_cons, Lam.evalList_nil, Sem.Result.bind_ok, Sem.Result.bind_assoc,
    List.headD_cons]
  exact (Sem.Result.bind_pure _).symm

theorem slotsOf_append (p : Src.Program) (k : Nat) (ls : Levels) (ρ : Src.Env) :
    ∀ (as bs : List Src.Term.Arg), Src.slotsOf p k ls ρ (as ++ bs) =
      (Src.slotsOf p k ls ρ as).bind fun xs =>
        (Src.slotsOf p k ls ρ bs).bind fun ys => .ok (xs ++ ys)
  | [], bs => by
    simp only [List.nil_append, Src.slotsOf, Sem.Result.bind_ok]
    exact (Sem.Result.bind_pure _).symm
  | a :: as, bs => by
    simp only [List.cons_append, Src.slotsOf, Sem.Result.bind_assoc]
    apply Sem.Result.bind_congr
    intro s
    rw [slotsOf_append p k ls ρ as bs, Sem.Result.bind_assoc]
    apply Sem.Result.bind_congr
    intro xs
    simp only [Sem.Result.bind_ok, List.cons_append]
    rw [Sem.Result.bind_assoc]
    rfl

/-- A spine's slots, split after `n` arguments. -/
theorem slotsOf_split {α : Type} (p : Src.Program) (k : Nat) (ls : Levels) (ρ : Src.Env)
    (args : List Src.Term.Arg) (n : Nat) (F : List Src.Slot → Result α) :
    (Src.slotsOf p k ls ρ args).bind F =
      (Src.slotsOf p k ls ρ (args.take n)).bind fun xs =>
        (Src.slotsOf p k ls ρ (args.drop n)).bind fun ys => F (xs ++ ys) := by
  conv => lhs; rw [← List.take_append_drop n args]
  rw [slotsOf_append, Sem.Result.bind_assoc]
  apply Sem.Result.bind_congr
  intro xs
  rw [Sem.Result.bind_assoc]
  rfl

theorem forceAll_length (p : Src.Program) (k : Nat) :
    ∀ (ss : List Src.Slot) {vs : List Src.Value}, Src.forceAll p k ss = .ok vs →
      vs.length = ss.length
  | [], vs, h => by rw [Src.forceAll_nil] at h; cases h; rfl
  | s :: ss, vs, h => by
    rw [Src.forceAll_cons] at h
    cases hs : Src.force p k s with
    | ok v =>
      rw [hs, Sem.Result.bind_ok] at h
      cases hr : Src.forceAll p k ss with
      | ok vs' =>
        rw [hr, Sem.Result.bind_ok] at h
        cases h
        simp [forceAll_length p k ss hr]
      | _ => rw [hr] at h; cases h
    | _ => rw [hs] at h; cases h

theorem map_fst_zipIdx {α : Type} (g : α × Nat → α × Bool) (hg : ∀ p, (g p).1 = p.1) :
    ∀ (xs : List α) (n : Nat), ((xs.zipIdx n).map g).map (·.1) = xs
  | [], _ => rfl
  | x :: xs, n => by
    simp only [List.zipIdx_cons, List.map_cons, hg]
    rw [map_fst_zipIdx g hg xs (n + 1)]

theorem map_fst_pair {α : Type} (b : Bool) (xs : List α) :
    (xs.map (·, b)).map (·.1) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, ih]

/-! ## `bindArgs` -/

section BindShape

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

/-- The context after the lets: the same one with a Lam binder per let. -/
theorem BindR.cx_eq : ∀ {cx : Cx} {xs : List (Src.Term.Arg × Bool)} {lets : List Term}
    {refs : List Ref} {cx' : Cx}, BindR I G cx xs lets refs cx' → cx' = cx.extra lets.length
  | _, _, _, _, _, .nil => by simp [Cx.extra]
  | _, _, _, _, _, .irr _ h => h.cx_eq
  | _, _, _, _, _, .name _ h => h.cx_eq
  | cx, _, _, _, _, .strict _ _ h => by
    rw [h.cx_eq]
    simp only [Cx.extra, List.length_cons]
    congr 1
    omega

theorem BindR.refs_length : ∀ {cx : Cx} {xs : List (Src.Term.Arg × Bool)} {lets : List Term}
    {refs : List Ref} {cx' : Cx}, BindR I G cx xs lets refs cx' → refs.length = xs.length
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .irr _ h => by simp [h.refs_length]
  | _, _, _, _, _, .name _ h => by simp [h.refs_length]
  | _, _, _, _, _, .strict _ _ h => by simp [h.refs_length]

/-- A by-name reference only where the flag allows it. -/
theorem BindR.name_flag : ∀ {cx : Cx} {xs : List (Src.Term.Arg × Bool)} {lets : List Term}
    {refs : List Ref} {cx' : Cx}, BindR I G cx xs lets refs cx' →
      ∀ {j : Nat} {a : Src.Term}, refs[j]? = some (.name a) → ∃ x, xs[j]? = some (x, true)
  | _, _, _, _, _, .nil, _, _, h => by simp at h
  | _, _, _, _, _, .irr _ _, 0, _, h => by simp at h
  | _, _, _, _, _, .irr _ hr, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact hr.name_flag h
  | _, _, _, _, _, .name _ _, 0, _, _ => ⟨_, rfl⟩
  | _, _, _, _, _, .name _ hr, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact hr.name_flag h
  | _, _, _, _, _, .strict _ _ _, 0, _, h => by simp at h
  | _, _, _, _, _, .strict _ _ hr, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact hr.name_flag h

/-- A let-bound reference is a fresh level. -/
theorem BindR.lvl_ge : ∀ {cx : Cx} {xs : List (Src.Term.Arg × Bool)} {lets : List Term}
    {refs : List Ref} {cx' : Cx}, BindR I G cx xs lets refs cx' →
      ∀ {j l : Nat}, refs[j]? = some (.lvl l) → cx.depth ≤ l
  | _, _, _, _, _, .nil, _, _, h => by simp at h
  | _, _, _, _, _, .irr _ _, 0, _, h => by simp at h
  | _, _, _, _, _, .irr _ hr, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h
    exact hr.lvl_ge h
  | _, _, _, _, _, .name _ _, 0, _, h => by simp at h
  | _, _, _, _, _, .name _ hr, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h
    exact hr.lvl_ge h
  | _, _, _, _, _, .strict _ _ _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Ref.lvl.injEq] at h
    omega
  | _, _, _, _, _, .strict _ _ hr, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h
    have := hr.lvl_ge h
    simp only [Cx.extra] at this
    omega

/-- A reference by name only at a position flagged for it. -/
theorem BindR.getD_name {cx : Cx} {xs : List (Src.Term.Arg × Bool)} {lets : List Term}
    {refs : List Ref} {cx' : Cx} (h : BindR I G cx xs lets refs cx') {i : Nat} {a : Src.Term}
    (e : refs.getD i .box = .name a) : ∃ x, xs[i]? = some (x, true) := by
  have hi : i < refs.length := by
    refine Nat.lt_of_not_le fun hge => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at e
    cases e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at e
  exact h.name_flag (by rw [List.getElem?_eq_getElem hi]; simpa using e)

/-- No reference by name when no position is flagged. -/
theorem BindR.getD_ne_name {cx : Cx} {args : List Src.Term.Arg} {lets : List Term}
    {refs : List Ref} {cx' : Cx} (h : BindR I G cx (args.map (·, false)) lets refs cx')
    (i : Nat) (a : Src.Term) : refs.getD i .box ≠ .name a := fun e => by
  obtain ⟨x, hx⟩ := h.getD_name e
  simp only [List.getElem?_map, Option.map_eq_some_iff, Prod.mk.injEq] at hx
  obtain ⟨_, _, _, h'⟩ := hx
  cases h'

/-- A reference by name only where a numbered flag holds. -/
theorem BindR.getD_name_zipIdx {cx : Cx} {args : List Src.Term.Arg}
    {g : Src.Term.Arg × Nat → Src.Term.Arg × Bool} {lets : List Term} {refs : List Ref}
    {cx' : Cx} (h : BindR I G cx ((args.zipIdx 0).map g) lets refs cx') {i : Nat} {a : Src.Term}
    (e : refs.getD i .box = .name a) : ∃ x, (g (x, i)).2 = true := by
  obtain ⟨x, hx⟩ := h.getD_name e
  simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_eq_some_iff] at hx
  obtain ⟨y, hy, e'⟩ := hx
  obtain ⟨z, _, rfl⟩ := hy
  refine ⟨z, ?_⟩
  rw [Nat.zero_add] at e'
  rw [e']

/-- As `getD_name_zipIdx`, for the reference at a position. -/
theorem BindR.name_flag_zipIdx {cx : Cx} {args : List Src.Term.Arg}
    {g : Src.Term.Arg × Nat → Src.Term.Arg × Bool} {lets : List Term} {refs : List Ref}
    {cx' : Cx} (h : BindR I G cx ((args.zipIdx 0).map g) lets refs cx') {i : Nat} {a : Src.Term}
    (e : refs[i]? = some (.name a)) : ∃ x, (g (x, i)).2 = true := by
  obtain ⟨x, hx⟩ := h.name_flag e
  simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_eq_some_iff] at hx
  obtain ⟨y, hy, e'⟩ := hx
  obtain ⟨z, _, rfl⟩ := hy
  refine ⟨z, ?_⟩
  rw [Nat.zero_add] at e'
  rw [e']

theorem BindR.nil_inv {cx : Cx} {lets : List Term} {refs : List Ref} {cx' : Cx}
    (h : BindR I G cx [] lets refs cx') : lets = [] ∧ refs = [] ∧ cx' = cx := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- Every reference related to its slot: in particular where the head reads. -/
theorem FormArgs.of_forall2 {h : Head} {ls : Levels} {ρ : Src.Env} {ρ'' : Env} {refs : List Ref}
    {ss : List Src.Slot} (hf : Forall2 (RefSlot I G ls ρ ρ'') refs ss) :
    FormArgs I G h ls ρ ρ'' refs ss where
  length := hf.length.symm
  at_ i ref s hr hs _ := by
    obtain ⟨y, hy, hry⟩ := hf.get hr
    rw [hs] at hy
    cases hy
    exact hry

/-- A reference's slot at the corresponding position. -/
theorem Forall2.getD_refSlot {ls : Levels} {ρ : Src.Env} {ρ'' : Env} {refs : List Ref}
    {ss : List Src.Slot} (hf : Forall2 (RefSlot I G ls ρ ρ'') refs ss) {i : Nat}
    (hi : i < ss.length) : RefSlot I G ls ρ ρ'' (refs.getD i .box) (ss.getD i default) := by
  have hi' : i < refs.length := hf.length ▸ hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  obtain ⟨y, hy, hry⟩ := hf.get (List.getElem?_eq_getElem hi')
  rw [List.getElem?_eq_getElem hi] at hy
  cases hy
  exact hry

end BindShape

/-! ## Saturated spines in SrcEval -/

namespace Setting

variable (S : Setting)

/-- A saturated special head's spine: the head's slots, the firing, then
the extra arguments. -/
theorem eval_sat {c : CId} {h : Head} (hh : S.I.headOf c = some h) (us : List Ixon.Univ)
    (args : List Src.Term.Arg) (hle : headArity S.I h ≤ args.length) (k : Nat) (ls : Levels)
    (ρ : Src.Env) :
    Src.eval S.p k ls ρ (Src.Term.mkApps (.const c us) args) =
      ((Src.slotsOf S.p k ls ρ (args.take (headArity S.I h))).bind
        (Src.fire S.p k h (us.map (Src.evalUniv ls)))).bind
          (Src.applySpine S.p k ls ρ · (args.drop (headArity S.I h))) := by
  rw [Src.eval_mkApps, Src.eval_const, evalConst_head S.p S.ch hh, Src.headValue_eq,
    ← headArity_eq S.p S.ch]
  by_cases h0 : headArity S.I h = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte, List.take_zero, List.drop_zero, Src.slotsOf,
      Sem.Result.bind_ok]
  · have htl : (args.take (headArity S.I h)).length = headArity S.I h := by
      simp only [List.length_take]; omega
    simp only [beq_iff_eq, h0, ↓reduceIte, Sem.Result.bind_ok]
    conv => lhs; rw [← List.take_append_drop (headArity S.I h) args]
    rw [Src.applySpine_append, Src.applySpine_pap_sat S.p k ls ρ h _ [] _
      (fun e => by rw [e] at htl; simp at htl; omega)
      (by rw [← headArity_eq S.p S.ch, List.length_nil, Nat.zero_add]; exact htl)]
    simp only [List.nil_append]

theorem ctorResult_con {c : CId} (hz : S.I.known.natZero ≠ some c)
    (hs : S.I.known.natSucc ≠ some c) (ls : Levels) (pss : List Src.Slot)
    (fvs : List Src.Value) : Src.ctorResult S.p c ls pss fvs = .ok (.con c ls pss fvs) := by
  have hz' : (some c == S.p.known.natZero) = false := beq_false_of_ne (Ne.symm hz)
  have hs' : (some c == S.p.known.natSucc) = false := beq_false_of_ne (Ne.symm hs)
  simp only [Src.ctorResult, hz', hs', Bool.false_eq_true, ↓reduceIte]

theorem ctorResult_zero {c : CId} (hz : S.I.known.natZero = some c) (ls : Levels)
    (pss : List Src.Slot) (fvs : List Src.Value) :
    Src.ctorResult S.p c ls pss fvs = .ok (.lit 0) := by
  have hz' : (some c == S.p.known.natZero) = true := beq_iff_eq.2 hz.symm
  simp only [Src.ctorResult, hz', ↓reduceIte]

theorem ctorResult_succ {c : CId} (hz : S.I.known.natZero ≠ some c)
    (hs : S.I.known.natSucc = some c) (ls : Levels) (pss : List Src.Slot) (n : Nat) :
    Src.ctorResult S.p c ls pss [.lit n] = .ok (.lit (n + 1)) := by
  have hz' : (some c == S.p.known.natZero) = false := beq_false_of_ne (Ne.symm hz)
  have hs' : (some c == S.p.known.natSucc) = true := beq_iff_eq.2 hs.symm
  simp only [Src.ctorResult, hz', hs', Bool.false_eq_true, ↓reduceIte]

theorem ctorResult_succ_stuck {c : CId} (hz : S.I.known.natZero ≠ some c)
    (hs : S.I.known.natSucc = some c) (ls : Levels) (pss : List Src.Slot)
    {fvs : List Src.Value} (hf : ∀ n, fvs ≠ [.lit n]) :
    Src.ctorResult S.p c ls pss fvs = .stuck := by
  have hz' : (some c == S.p.known.natZero) = false := beq_false_of_ne (Ne.symm hz)
  have hs' : (some c == S.p.known.natSucc) = true := beq_iff_eq.2 hs.symm
  simp only [Src.ctorResult, hz', hs', Bool.false_eq_true, ↓reduceIte]

/-- The heads' declarations. -/
theorem headOf_quotMk {c₀ c : CId} (h : S.I.headOf c₀ = some (.quotMk c)) :
    ∃ lv ty, S.I.decl? c = some (.quot .ctor lv ty) := by
  unfold Input.headOf at h
  split at h
  · cases h
  · cases h
  · cases h
  · split at h
    · cases h
    · cases h
    · next lv ty heq => cases h; exact ⟨lv, ty, heq⟩
    · cases h
    · cases h

theorem kindAt_sub {r : CId} {q : Profile} {w : Src.PropWhen} {srcs : List Src.FieldSrc}
    (hk : S.I.kindAt r q = some (.subsingleton w srcs)) :
    S.I.recKind.get? r = some (.subsingleton w srcs) := by
  obtain ⟨k₀, hk₀, hkk⟩ : ∃ k₀, S.I.recKind.get? r = some k₀ ∧ k₀.atProfile q =
      .subsingleton w srcs := by
    simpa [Input.kindAt] using hk
  cases k₀ with
  | subsingleton w' srcs' =>
    simp only [Src.RecKind.atProfile] at hkk
    split at hkk
    · cases hkk; exact hk₀
    · cases hkk
  | _ => simp [Src.RecKind.atProfile] at hkk

/-- A constructor fired on its parameters then its fields. -/
theorem fire_ctor_split {c : CId} {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat}
    {ty : Src.Term} (hd : S.I.decl? c = some (.ctor sf lv ind cidx np nf ty)) (k : Nat)
    (ls : Levels) {pss : List Src.Slot} (hp : pss.length = np) (fss : List Src.Slot) :
    Src.fire S.p k (.ctor c) ls (pss ++ fss) =
      (Src.forceAll S.p k fss).bind (Src.ctorResult S.p c ls pss) := by
  have hd' : S.p.decl? c = some (.ctor sf lv ind cidx np nf ty) := hd
  rw [Src.fire_ctor]
  simp only [hd']
  rw [List.drop_left' hp, List.take_left' hp]

section

variable {S} (wf : ProgWF S.I)
include wf

/-- An unboxed constructor's value: its only kept field. -/
theorem vr_unboxed {c : CId} {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat}
    {ty : Src.Term} (hd : S.I.decl? c = some (.ctor sf lv ind cidx np nf ty)) {j : Nat}
    (hu : S.I.unbox? ind [] = some j) {ls : Levels} {ps : List Src.Slot} {fvs : List Src.Value}
    (hlen : fvs.length = nf) {v' : Val} (hk : KeptR S.I S.G c 0 fvs [v']) :
    VR S.I S.G (.con c ls ps fvs) v' := by
  obtain ⟨k₀, hk₀, hkj, hkother⟩ := unbox?_spec hu
  have hc : c = k₀ := by
    have := wf.ctorIn hd
    rw [hk₀] at this
    cases cidx with
    | zero => simpa using this.symm
    | succ n => simp at this
  subst hc
  have hlenK := hk.length
  have hjlt : j < fvs.length := by
    refine Nat.lt_of_not_le fun hge => ?_
    have : keptBelow S.I c 0 fvs.length = 0 := by
      simp only [keptBelow, Nat.zero_add, List.length_eq_zero_iff, List.filter_eq_nil_iff,
        List.mem_range]
      intro x hx
      have hne : x ≠ j := by omega
      simp [hkother x hne]
    simp [this] at hlenK
  obtain ⟨a, ha⟩ : ∃ a, fvs[j]? = some a := ⟨_, List.getElem?_eq_getElem hjlt⟩
  obtain ⟨f', hf', hvf⟩ := hk.get_kept (j := j) ha (by simpa using hkj)
  have hkb : keptBelow S.I c 0 j = 0 := by
    simp only [keptBelow, Nat.zero_add, List.length_eq_zero_iff, List.filter_eq_nil_iff,
      List.mem_range]
    intro x hx
    have hne : x ≠ j := by omega
    simp [hkother x hne]
  rw [hkb] at hf'
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hf'
  subst hf'
  refine VR.unboxed hd hlen hu ha hvf fun i f hf hi => hk.get_drop (j := i) hf ?_
  simpa using hkother i hi

end

end Setting

/-- `Nat.succ`'s Lam form on a literal. -/
theorem primResult_succ (K : Known) (n : Nat) :
    Lam.primResult K .natAdd [.lit (.nat n), .lit (.nat 1)] = .ok (.lit (.nat (n + 1))) := rfl

end IxCC.Lam.Erase.Proof
