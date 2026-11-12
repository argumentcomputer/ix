import IxCC.Lam.Erase.Proof.Bind

/-! # Globals, projections and by-name variants

The pieces of the term simulation that need no recursion on the
erasure: a global's body, the spine steps of an application, a projection's
continuation (dropped, unboxed or keyed field), and a by-name variant's
leading arguments, which meet only the λs of its δ body. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)
open IxCC.Sem (Result ClockMono SimUpTo later later_succ)

namespace Setting

variable (S : Setting)

theorem eval_glob_of {g : GlobalId} {gl : Global} (h : S.L.global? g = some gl) (k : Nat)
    (ρ : Env) : Lam.eval S.L k ρ (.glob g) = later k fun k => Lam.eval S.L k [] gl.body := by
  rw [Lam.eval_glob, h]; rfl

theorem _root_.IxCC.Lam.Erase.Proof.WrapR.lams {I : Input}
    {G : Key.GKey → GlobalId → Prop} {h : Head} {q : Profile} {body : Term}
    (hw : WrapR I G h q body) :
    ∃ inner, body = Term.lams (List.replicate (headArity I h) .strict) inner := by
  cases hw with
  | prim _ => exact ⟨_, rfl⟩
  | word _ _ _ => exact ⟨_, rfl⟩
  | other _ _ _ => exact ⟨_, rfl⟩

theorem glob_of {key : Key.GKey} {g : GlobalId} (hg : S.G key g) :
    ∃ gl, S.L.global? g = some gl ∧ gl.key = key ∧ BodyR S.I S.G key gl.body :=
  S.prog key g hg

/-- The Src side of an argument list's application, with the slot evaluated
first (for `SimUpTo.bind`). -/
theorem applySpine_cons_strict (k : Nat) (ls : Levels) (ρ : Src.Env) (f : Src.Value)
    (a : Src.Term) (r : Src.Rel) (rest : List Src.Term.Arg) (hr : r.irrAt ls = false) :
    Src.applySpine S.p k ls ρ f ((a, .strict, r) :: rest) =
      (Src.eval S.p k ls ρ a).bind fun x =>
        (Src.apply S.p k f (.val x)).bind fun v => Src.applySpine S.p k ls ρ v rest := by
  simp only [Src.applySpine, Src.slotOf, hr, Bool.false_eq_true, ↓reduceIte,
    Sem.Result.bind_assoc, Sem.Result.bind_ok]

theorem applySpine_cons_irr (k : Nat) (ls : Levels) (ρ : Src.Env) (f : Src.Value)
    (a : Src.Term) (m : Src.Mode) (r : Src.Rel) (rest : List Src.Term.Arg)
    (hr : r.irrAt ls = true) :
    Src.applySpine S.p k ls ρ f ((a, m, r) :: rest) =
      (Src.apply S.p k f (.val (.irr (some a) ρ ls))).bind fun v =>
        Src.applySpine S.p k ls ρ v rest := by
  simp only [Src.applySpine, Src.slotOf, hr, ↓reduceIte, Sem.Result.bind_ok]

theorem applyArgs_cons_strict (k : Nat) (ρ' : Env) (f : Val) (a : Term)
    (rest : List (Term × Mode)) :
    Lam.applyArgs S.L k ρ' f ((a, .strict) :: rest) =
      (Lam.eval S.L k ρ' a).bind fun x =>
        (Lam.apply S.L k f (.val x)).bind fun v => Lam.applyArgs S.L k ρ' v rest := by
  simp only [Lam.applyArgs, Lam.argSlot, Sem.Result.bind_assoc, Sem.Result.bind_ok]

/-! ## Projections -/

theorem kept_of_cls {I : Input} {k : CId} {fields : List Src.Relevance.FieldClass} {i : Nat}
    {cls : Src.Relevance.FieldClass} (hf : I.fields? k = some fields) (hcls : fields[i]? = some cls)
    (q : Profile) : I.kept k q i = !cls.dropP q := by
  simp [Input.kept, hf, hcls]

theorem projectField_of {s k : CId} (hk : S.I.ctorsOf s = [k]) (i : Nat) (v : Src.Value) :
    S.p.projectField s i v =
      match v with
      | .con c _ _ fs => if c = k then Result.ofOption fs[i]? else .stuck
      | _ => .stuck := by
  obtain ⟨sf, lv, np, ni, ty, hd⟩ : ∃ sf lv np ni ty,
      S.p.decl? s = some (.induct sf lv np ni ty [k]) := by
    simp only [Input.ctorsOf, input_decl] at hk
    split at hk
    · next sf lv np ni ty ctors hd => rw [hk] at hd; exact ⟨_, _, _, _, _, hd⟩
    · cases hk
  cases v with
  | con c _ _ fs =>
    simp only [Src.Program.projectField, hd, List.length_singleton, List.head?_cons]
    by_cases h : c = k
    · subst h; simp
    · simp [h, Ne.symm h]
  | _ => rfl

/-- Lam's keyed projection of a value. -/
def projKey (c : Key.CtorKey) (i : Nat) : Val → Result Val
  | .con c' fs => if c' = c then Result.ofOption fs[i]? else .stuck
  | _ => .stuck

theorem eval_proj_key (k : Nat) (ρ' : Env) (c : Key.CtorKey) (i : Nat) (e : Term) :
    Lam.eval S.L k ρ' (.proj c i e) = (Lam.eval S.L k ρ' e).bind (projKey c i) := by
  rw [Lam.eval_proj]
  exact Sem.Result.bind_congr _ fun w => by cases w <;> rfl

section Proj

variable {S} (wf : ProgWF S.I)
include wf

/-- The only constructor of a structure declares it at index 0. -/
theorem ctor_of_single {s k : CId} (hk : S.I.ctorsOf s = [k]) :
    ∃ sf lv np nf ty, S.I.decl? k = some (.ctor sf lv s 0 np nf ty) :=
  wf.ctorOf (t := s) (i := 0) (by rw [hk]; rfl)

theorem proj_drop_cont {m : Nat} {s k : CId} {i : Nat} (hk : S.I.ctorsOf s = [k])
    (hkept : S.I.kept k [] i = false) {v : Src.Value} {v' : Val} (hv : VR S.I S.G v v') :
    SimUpTo (VR S.I S.G) m (fun _ => S.p.projectField s i v) (fun _ => .ok .box) := by
  rw [show (fun _ : Nat => S.p.projectField s i v) = fun _ => _ from
    funext fun _ => S.projectField_of hk i v]
  obtain ⟨sf, lv, np, nf, ty, hdk⟩ := S.ctor_of_single wf hk
  cases v with
  | con c ls ps fs =>
    dsimp only
    by_cases hc : c = k
    · subst hc
      simp only [if_pos rfl]
      cases hfi : fs[i]? with
      | none => exact SimUpTo.stuck _
      | some f =>
        have hirr : f.isIrr = true := by
          obtain ⟨_, hvr⟩ := hv.con_inv hdk
          rcases hvr with ⟨j, a, hu, _, _, hrest⟩ | ⟨_, fs', _, hkr⟩
          · refine hrest i f hfi fun hij => ?_
            subst hij
            obtain ⟨k', hk', hkj, _⟩ := unbox?_spec hu
            rw [hk] at hk'
            cases hk'
            rw [hkj] at hkept
            cases hkept
          · exact hkr.get_drop (j := i) hfi (by simpa using hkept)
        cases f with
        | irr t ρ₀ ls₀ => exact SimUpTo.ok VR.irr
        | _ => simp [Src.Value.isIrr] at hirr
    · simp only [if_neg hc]
      exact SimUpTo.stuck _
  | _ => exact SimUpTo.stuck _

theorem proj_unbox_cont {m : Nat} {s k : CId} {i : Nat} (hk : S.I.ctorsOf s = [k])
    (hu : (S.I.unbox? s []).isSome = true) (hkept : S.I.kept k [] i = true) {v : Src.Value}
    {v' : Val} (hv : VR S.I S.G v v') :
    SimUpTo (VR S.I S.G) m (fun _ => S.p.projectField s i v) (fun _ => .ok v') := by
  rw [show (fun _ : Nat => S.p.projectField s i v) = fun _ => _ from
    funext fun _ => S.projectField_of hk i v]
  obtain ⟨sf, lv, np, nf, ty, hdk⟩ := S.ctor_of_single wf hk
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 hu
  obtain ⟨k', hk', _, honly⟩ := unbox?_spec hj
  rw [hk] at hk'
  cases hk'
  have hij : i = j := by
    refine Classical.byContradiction fun hne => ?_
    rw [honly i hne] at hkept
    cases hkept
  subst hij
  cases v with
  | con c ls ps fs =>
    dsimp only
    by_cases hc : c = k
    · subst hc
      simp only [if_pos rfl]
      obtain ⟨_, hvr⟩ := hv.con_inv hdk
      rcases hvr with ⟨j', a, hu', hj', ha, _⟩ | ⟨hu', _⟩
      · rw [hj] at hu'
        cases hu'
        rw [hj']
        exact SimUpTo.ok ha
      · rw [hj] at hu'; cases hu'
    · simp only [if_neg hc]
      exact SimUpTo.stuck _
  | _ => exact SimUpTo.stuck _

theorem proj_key_cont {m : Nat} {s k : CId} {i : Nat} (hk : S.I.ctorsOf s = [k])
    (hu : S.I.unbox? s [] = none) (hkept : S.I.kept k [] i = true) {v : Src.Value}
    {v' : Val} (hv : VR S.I S.G v v') :
    SimUpTo (VR S.I S.G) m (fun _ => S.p.projectField s i v)
      (fun _ => projKey (S.I.ctorKey k) (S.I.rank k [] i) v') := by
  rw [show (fun _ : Nat => S.p.projectField s i v) = fun _ => _ from
    funext fun _ => S.projectField_of hk i v]
  obtain ⟨sf, lv, np, nf, ty, hdk⟩ := S.ctor_of_single wf hk
  cases v with
  | con c ls ps fs =>
    dsimp only
    by_cases hc : c = k
    · subst hc
      simp only [if_pos rfl]
      obtain ⟨_, hvr⟩ := hv.con_inv hdk
      rcases hvr with ⟨j', a, hu', _⟩ | ⟨_, fs', rfl, hkr⟩
      · rw [hu] at hu'; cases hu'
      · simp only [projKey, if_pos rfl]
        cases hfi : fs[i]? with
        | none => exact SimUpTo.stuck _
        | some f =>
          obtain ⟨f', hf', hvf⟩ := hkr.get_kept (j := i) hfi (by simpa using hkept)
          rw [rank_eq_keptBelow, hf']
          exact SimUpTo.ok hvf
    · simp only [if_neg hc]
      exact SimUpTo.stuck _
  | _ => exact SimUpTo.stuck _

end Proj

/-! ## By-name variants -/

section

variable {S} {m : Nat} (hap : S.ApplySim m)
include hap

/-- The leading arguments of a by-name variant meet the δ body's own λs:
`name` arguments only ever reach λ binders. -/
theorem lazy_sim : ∀ {cx : Cx} {ms : List Mode} {args : List Src.Term.Arg}
    {args' : List (Term × Mode)}, LazyArgsR S.I S.G cx ms args args' →
    ∀ {ρ : Src.Env} {ρ' : Env} {ls : Levels}, EnvR S.I S.G cx ρ ρ' → Agree ls cx.prof →
      ∀ {f : Src.Value} {f' : Val}, VR S.I S.G f f' → CloTele f args.length →
        SimUpTo (VR S.I S.G) m (fun k => Src.applySpine S.p k ls ρ f args)
          (fun k => Lam.applyArgs S.L k ρ' f' args')
  | _, _, _, _, .nil, ρ, ρ', ls, _, _, f, f', hf, _ =>
    (SimUpTo.ok hf).congr (fun _ => rfl) (fun _ => rfl)
  | _, _, _, _, .irr (a := a) (r := r) (rest := rest) _ hr hrest, ρ, ρ', ls, he, hag, f, f', hf,
      htele => by
    have hr' : _ = true := (hag.irr _).symm.trans hr
    obtain ⟨b, d, body, ρ₀, ls₀, rfl, hn⟩ : ∃ b d body ρ₀ ls₀, f = .clo b d body ρ₀ ls₀ ∧
        (rest.length + 1) ≤ body.lamCount + 1 := by
      rcases htele with h | h
      · simp at h
      · simpa using h
    refine (SimUpTo.bind' (Lam.apply_mono S.L _ _) (fun v => Lam.applyArgs_mono S.L _ v _)
      (hap hf (SR.val (VR.irr (t := some a) (ρ := ρ) (ls := ls))) (.inl ⟨_, _, _, _, _, rfl⟩))
      fun v v' hv hsrc => lazy_sim hrest he hag hv ?_).congr
      (fun k => S.applySpine_cons_irr k ls ρ _ _ _ _ rest hr') (fun k => ?_)
    · rcases Nat.eq_zero_or_pos rest.length with h0 | hpos
      · exact .inl h0
      · obtain ⟨k, _, hk⟩ := hsrc
        cases body with
        | lam b₂ d₂ body₂ =>
          rw [apply_clo_lam hk]
          exact .inr ⟨_, _, _, _, _, rfl, by simp [Src.Term.lamCount] at hn; omega⟩
        | _ => simp only [Src.Term.lamCount] at hn; omega
    · simp only [Lam.applyArgs, Lam.argSlot, Lam.eval_box', Sem.Result.bind_ok]
  | _, _, _, _, .name (a := a) (r := r) (rest := rest) _ hr hta hrest, ρ, ρ', ls, he, hag, f, f',
      hf, htele => by
    have hr' : _ = false := (hag.irr _).symm.trans hr
    obtain ⟨b, d, body, ρ₀, ls₀, rfl, hn⟩ : ∃ b d body ρ₀ ls₀, f = .clo b d body ρ₀ ls₀ ∧
        (rest.length + 1) ≤ body.lamCount + 1 := by
      rcases htele with h | h
      · simp at h
      · simpa using h
    refine (SimUpTo.bind' (Lam.apply_mono S.L _ _) (fun v => Lam.applyArgs_mono S.L _ v _)
      (hap hf (SR.name hta he.er he.depth he.minors he.minorsLt hag) (.inl ⟨_, _, _, _, _, rfl⟩))
      fun v v' hv hsrc => lazy_sim hrest he hag hv ?_).congr (fun k => ?_) (fun k => ?_)
    · rcases Nat.eq_zero_or_pos rest.length with h0 | hpos
      · exact .inl h0
      · obtain ⟨k, _, hk⟩ := hsrc
        cases body with
        | lam b₂ d₂ body₂ =>
          rw [apply_clo_lam hk]
          exact .inr ⟨_, _, _, _, _, rfl, by simp [Src.Term.lamCount] at hn; omega⟩
        | _ => simp only [Src.Term.lamCount] at hn; omega
    · simp only [Src.applySpine, Src.slotOf, hr', Bool.false_eq_true, ↓reduceIte,
        Sem.Result.bind_ok]
    · simp only [Lam.applyArgs, Lam.argSlot, Sem.Result.bind_ok]

end

end Setting

end IxCC.Lam.Erase.Proof
