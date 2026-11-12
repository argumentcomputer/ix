import IxCC.Lam.Erase.Proof.Proj
import IxCC.Lam.Erase.Proof.Word

/-! # The erasure simulation on terms

`TR cx t t'` simulates at clock bound `m` from related environments, given
every lower bound (`Level`) and application at `m` (`ApplySim`): by
structural recursion on the derivation, mutually with a spine's arguments
(applied one by one, or evaluated for a primitive), a saturated head's
bound arguments and a constructor's fields. Every rule of SrcEval meets its
Lam counterpart at the same clock, except that Lam may spend more
(wrappers, delayed minors), which `SimUpTo.laterR` absorbs. -/

set_option autoImplicit false
-- The mutual block shares its section hypotheses; not every member uses each.
set_option linter.unusedSectionVars false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)
open IxCC.Sem (Result ClockMono SimUpTo later later_succ)

namespace Setting

section

variable {S : Setting} (wf : ProgWF S.I) {m : Nat} (hlt : ∀ m' < m, S.Level m')
  (hap : S.ApplySim m)
include wf hlt hap

mutual

theorem tr_sim : ∀ {cx : Cx} {t : Src.Term} {t' : Term}, TR S.I S.G cx t t' →
    ∀ {ρ : Src.Env} {ρ' : Env} {ls : Levels}, EnvR S.I S.G cx ρ ρ' → Agree ls cx.prof →
      SimUpTo (VR S.I S.G) m (fun k => Src.eval S.p k ls ρ t) (fun k => Lam.eval S.L k ρ' t')
  | cx, _, _, .varSome (i := i) (l := l) hi, ρ, ρ', ls, he, _ => by
    obtain ⟨s, s', hs, hs', hss⟩ := he.er.get hi
    refine (S.force_sim (fun m' h => (hlt m' h).tr) hss).congr (fun k => ?_) (fun k => ?_)
    · rw [Src.eval_var, hs]
    · rw [Cx.lvl_eq, Lam.eval_var, he.depth, hs']
  | _, _, _, .varNone hi, ρ, ρ', ls, he, _ => by
    obtain ⟨s, hs, t, ρ₀, ls₀, rfl⟩ := he.er.getNone hi
    refine (SimUpTo.ok (VR.irr (t := t) (ρ := ρ₀) (ls := ls₀))).congr (fun k => ?_)
      (fun k => Lam.eval_box' S.L k ρ')
    rw [Src.eval_var, hs]; exact Src.force_val S.p k _
  | _, _, _, .sort, ρ, ρ', ls, _, _ =>
    (SimUpTo.ok VR.irr).congr (fun k => Src.eval_sort S.p k ls ρ _) (fun k => Lam.eval_box' S.L k ρ')
  | _, _, _, .pi, ρ, ρ', ls, _, _ =>
    (SimUpTo.ok VR.irr).congr (fun k => Src.eval_pi S.p k ls ρ _ _ _ _)
      (fun k => Lam.eval_box' S.L k ρ')
  | _, _, _, .natLit, ρ, ρ', ls, _, _ =>
    (SimUpTo.ok VR.lit).congr (fun k => Src.eval_natLit S.p k ls ρ _)
      (fun k => Lam.eval_lit S.L k ρ' _)
  | _, _, _, .lam _ hb, ρ, ρ', ls, he, hag =>
    (SimUpTo.ok (VR.clo he.er he.depth he.minors he.minorsLt hag hb)).congr
      (fun k => Src.eval_lam S.p k ls ρ _ _ _) (fun k => Lam.eval_lam S.L k ρ' _ _ _)
  | _, _, _, .letIrr (v := v) hr hb, ρ, ρ', ls, he, hag => by
    have hr' : _ = true := (hag.irr _).symm.trans hr
    refine (tr_sim hb (he.bind (SR.val (VR.irr (t := some v) (ρ := ρ) (ls := ls)))) hag).congr
      (fun k => ?_) (fun k => ?_)
    · simp only [Src.eval_letE, hr', ↓reduceIte]
    · rw [Lam.eval_letE, Lam.eval_box', Sem.Result.bind_ok]
  | _, _, _, .letRel hr hv hb, ρ, ρ', ls, he, hag => by
    have hr' : _ = false := (hag.irr _).symm.trans hr
    refine (SimUpTo.bind (Lam.eval_mono S.L _ _) (fun x => Lam.eval_mono S.L _ _)
      (tr_sim hv he hag) fun x x' hx => tr_sim hb (he.bind (SR.val hx)) hag).congr
      (fun k => ?_) (fun k => Lam.eval_letE S.L k ρ' _ _ _)
    simp only [Src.eval_letE, hr', Bool.false_eq_true, ↓reduceIte]
  | _, _, _, .projDrop (s := s) (i := i) (k := k) hte hk hf hcls hdrop, ρ, ρ', ls, he, hag => by
    have hkept : S.I.kept k [] i = false := by rw [kept_of_cls hf hcls, hdrop]; rfl
    refine (SimUpTo.bind (Lam.eval_mono S.L _ _) (fun _ => ClockMono.const _) (tr_sim hte he hag)
      fun v v' hv => proj_drop_cont wf hk hkept hv).congr
      (fun k => Src.eval_proj S.p k ls ρ s i _) (fun k => ?_)
    rw [Lam.eval_letE]
    exact Sem.Result.bind_congr _ fun x => Lam.eval_box' S.L k _
  | _, _, _, .projUnbox (s := s) (i := i) (k := k) hte hk hf hcls hdrop hu, ρ, ρ', ls, he,
      hag => by
    have hkept : S.I.kept k [] i = true := by rw [kept_of_cls hf hcls, hdrop]; rfl
    refine (SimUpTo.bind (Lam.eval_mono S.L _ _) (fun _ => ClockMono.const _) (tr_sim hte he hag)
      fun v v' hv => proj_unbox_cont wf hk hu hkept hv).congr
      (fun k => Src.eval_proj S.p k ls ρ s i _) (fun k => (Sem.Result.bind_pure _).symm)
  | _, _, _, .projKey (s := s) (i := i) (k := k) hte hk hf hcls hdrop hu _, ρ, ρ', ls, he,
      hag => by
    have hkept : S.I.kept k [] i = true := by rw [kept_of_cls hf hcls, hdrop]; rfl
    exact (SimUpTo.bind (Lam.eval_mono S.L _ _) (fun _ => ClockMono.const _) (tr_sim hte he hag)
      fun v v' hv => proj_key_cont wf hk hu hkept hv).congr
      (fun k => Src.eval_proj S.p k ls ρ s i _) (fun k => S.eval_proj_key k ρ' _ _ _)
  | _, _, _, .app _ _ hh ha, ρ, ρ', ls, he, hag =>
    (SimUpTo.bind (Lam.eval_mono S.L _ _) (fun f => Lam.applyArgs_mono S.L _ f _)
      (tr_sim hh he hag) fun f f' hf => args_sim ha he hag hf).congr
      (fun k => Src.eval_mkApps S.p k ls ρ _ _) (fun k => Lam.eval_apps S.L k ρ' _ _)
  | cx, _, _, .plain (c := c) (us := us) (g := g) hus hb _ hg ha, ρ, ρ', ls, he, hag => by
    obtain ⟨gl, hgl, _, hbody⟩ := S.glob_of hg
    cases hbody with
    | const hb' hbt =>
      rw [hb] at hb'
      cases hb'
      have hag' := hag.inst us (S.I.lvls c) hus
      refine (SimUpTo.bind (Lam.eval_mono S.L [] gl.body).later
        (fun f => Lam.applyArgs_mono S.L _ f _)
        (SimUpTo.later (n := m) fun m' hm' => (hlt m' (by omega)).tr hbt (EnvR.empty _) hag')
        fun f f' hf => args_sim ha he hag hf).congr (fun k => ?_) (fun k => ?_)
      · rw [Src.eval_mkApps, Src.eval_const, evalConst_delta S.p S.ch hb]
      · rw [Lam.eval_apps, S.eval_glob_of hgl]
  | cx, _, _, .variant (c := c) (us := us) (args := args) (b := b) (a := a) (g := g)
      (lazyArgs := lazyArgs) (rest' := rest') hus hb hlz
      hle hhas hg hlazy hrest, ρ, ρ', ls, he, hag => by
    obtain ⟨gl, hgl, _, hbody⟩ := S.glob_of hg
    cases hbody with
    | byName hlz' hb' hcount hb0 hset =>
      rw [hlz] at hlz'; cases hlz'
      rw [hb] at hb'; cases hb'
      have hms : (lazyModes S.I c (qOf S.I cx c us) a).length = a := by simp [lazyModes]
      have htr : TR S.I S.G (bodyCx (qOf S.I cx c us)) b gl.body :=
        hb0.setModes (by rw [hms]; exact hcount) hset
      have hag' := hag.inst us (S.I.lvls c) hus
      have hapos : 0 < a := by
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · subst h0; simp [lazyModes, hasName] at hhas
        · exact h0
      cases b with
      | lam b₁ d₁ body₁ =>
        refine (SimUpTo.bind' (d := fun v k => Src.applySpine S.p k ls ρ v args)
          (d' := fun w k => Lam.applyArgs S.L k ρ' w (lazyArgs ++ rest'))
          (Lam.eval_mono S.L [] gl.body).later
          (fun f => Lam.applyArgs_mono S.L _ f _)
          (SimUpTo.later (n := m) fun m' hm' =>
            (hlt m' (by omega)).tr htr (EnvR.empty _) hag')
          fun v v' hv hsrc => ?_).congr (fun k => ?_) (fun k => ?_)
        · obtain ⟨k, _, hk⟩ := hsrc
          have hv₁ : v = .clo b₁ d₁ body₁ [] (us.map (Src.evalUniv ls)) := by
            cases k with
            | zero => cases hk
            | succ k => rw [later_succ, Src.eval_lam] at hk; cases hk; rfl
          subst hv₁
          refine (SimUpTo.bind (Lam.applyArgs_mono S.L _ _ _)
            (fun w => Lam.applyArgs_mono S.L _ w _)
            (lazy_sim hap hlazy he hag hv (.inr ⟨_, _, _, _, _, rfl, ?_⟩))
            fun w w' hw => args_sim hrest he hag hw).congr (fun k => ?_) (fun k => ?_)
          · simp only [Src.Term.lamCount] at hcount
            simp only [List.length_take]
            omega
          · conv => lhs; rw [← List.take_append_drop a args]
            rw [Src.applySpine_append]
          · rw [Lam.applyArgs_append]
        · rw [Src.eval_mkApps, Src.eval_const, evalConst_delta S.p S.ch hb]
        · rw [Lam.eval_apps, S.eval_glob_of hgl]
      | _ => simp only [Src.Term.lamCount] at hcount; omega
  | cx, _, _, .wrap (c := c) (us := us) (h := h) (g := g) hus hh hlen hg ha, ρ, ρ', ls, he,
      hag => by
    obtain ⟨gl, hgl, _, hbody⟩ := S.glob_of hg
    cases hbody with
    | wrapper hw =>
      obtain ⟨inner, hin⟩ := hw.lams
      rw [hin] at hw
      have hag' := hag.inst us (S.I.lvls c) hus
      have hpos : 0 < headArity S.I h := by omega
      have hv : VR S.I S.G (.pap h (us.map (Src.evalUniv ls)) [])
          (.clos [] (Term.lams (List.replicate (headArity S.I h - 1) .strict) inner)) := by
        have := VR.pap (args := []) (vs := []) hw hag' hpos .nil
        simpa using this
      refine (SimUpTo.bind (ClockMono.const _).later (fun f => Lam.applyArgs_mono S.L _ f _)
        (SimUpTo.laterR (ClockMono.const _) (SimUpTo.ok hv))
        fun f f' hf => args_sim ha he hag hf).congr (fun k => ?_) (fun k => ?_)
      · have hpos' : 0 < S.p.headArity h := by rw [← headArity_eq S.p S.ch]; exact hpos
        have h0 : (S.p.headArity h == 0) = false := by simp; omega
        rw [Src.eval_mkApps, Src.eval_const, evalConst_head S.p S.ch hh, Src.headValue_eq]
        simp only [h0, Bool.false_eq_true, ↓reduceIte]
      · rw [Lam.eval_apps, S.eval_glob_of hgl, hin]
        cases k with
        | zero => rfl
        | succ k =>
          simp only [later_succ]
          obtain ⟨a', ha'⟩ : ∃ a', headArity S.I h = a' + 1 :=
            ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
          rw [ha', List.replicate_succ, Lam.eval_lams_cons]
          simp
  | cx, _, _, .sat (c := c) (us := us) (args := args) (h := h) hus hh hle hsat hargs, ρ, ρ', ls,
      he, hag => by
    have hag' := hag.inst us (S.I.lvls c) hus
    exact (SimUpTo.bind (Lam.eval_mono S.L _ _) (fun f => Lam.applyArgs_mono S.L _ f _)
      (sat_sim hsat hh (by simp only [List.length_take]; omega) he hag hag')
      fun f f' hf => args_sim hargs he hag hf).congr (fun k => S.eval_sat hh us args hle k ls ρ)
      (fun k => Lam.eval_apps S.L k ρ' _ _)

theorem args_sim : ∀ {cx : Cx} {args : List Src.Term.Arg} {args' : List (Term × Mode)},
    ArgsR S.I S.G cx args args' →
    ∀ {ρ : Src.Env} {ρ' : Env} {ls : Levels}, EnvR S.I S.G cx ρ ρ' → Agree ls cx.prof →
      ∀ {f : Src.Value} {f' : Val}, VR S.I S.G f f' →
        SimUpTo (VR S.I S.G) m (fun k => Src.applySpine S.p k ls ρ f args)
          (fun k => Lam.applyArgs S.L k ρ' f' args')
  | _, _, _, .nil, ρ, ρ', ls, _, _, f, f', hf =>
    (SimUpTo.ok hf).congr (fun _ => rfl) (fun _ => rfl)
  | _, _, _, .irr hr ha, ρ, ρ', ls, he, hag, f, f', hf => by
    have hr' : _ = true := (hag.irr _).symm.trans hr
    refine (SimUpTo.bind (Lam.apply_mono S.L _ _) (fun v => Lam.applyArgs_mono S.L _ v _)
      (hap hf (SR.val VR.irr) (.inr ⟨_, _, rfl, rfl⟩)) fun v v' hv => args_sim ha he hag hv).congr
      (fun k => S.applySpine_cons_irr k ls ρ f _ _ _ _ hr') (fun k => ?_)
    simp only [Lam.applyArgs, Lam.argSlot, Lam.eval_box', Sem.Result.bind_ok]
  | _, _, _, .strict hr ha hrest, ρ, ρ', ls, he, hag, f, f', hf => by
    have hr' : _ = false := (hag.irr _).symm.trans hr
    exact (SimUpTo.bind (Lam.eval_mono S.L _ _)
      (fun x => (Lam.apply_mono S.L _ _).bind fun v => Lam.applyArgs_mono S.L _ v _)
      (tr_sim ha he hag) fun x x' hx =>
        SimUpTo.bind (Lam.apply_mono S.L _ _) (fun v => Lam.applyArgs_mono S.L _ v _)
          (hap hf (SR.val hx) (.inr ⟨_, _, rfl, rfl⟩)) fun v v' hv => args_sim hrest he hag hv).congr
      (fun k => S.applySpine_cons_strict k ls ρ f _ _ _ hr') (fun k => S.applyArgs_cons_strict k ρ' f' _ _)

/-- A primitive's arguments, all evaluated before it applies. -/
theorem argVals_sim : ∀ {cx : Cx} {args : List Src.Term.Arg} {args' : List (Term × Mode)},
    ArgsR S.I S.G cx args args' →
    ∀ {ρ : Src.Env} {ρ' : Env} {ls : Levels}, EnvR S.I S.G cx ρ ρ' → Agree ls cx.prof →
      SimUpTo (Forall2 (VR S.I S.G)) m
        (fun k => (Src.slotsOf S.p k ls ρ args).bind (Src.forceAll S.p k))
        (fun k => Lam.evalList S.L k ρ' (args'.map (·.1)))
  | _, _, _, .nil, ρ, ρ', ls, _, _ =>
    (SimUpTo.ok .nil).congr
      (fun k => by simp only [Src.slotsOf, Sem.Result.bind_ok, Src.forceAll_nil])
      (fun k => Lam.evalList_nil S.L k ρ')
  | _, _, _, .irr (a := a) hr ha, ρ, ρ', ls, he, hag => by
    have hr' : _ = true := (hag.irr _).symm.trans hr
    refine (SimUpTo.bind (Lam.evalList_mono S.L _ _) (fun _ => ClockMono.const _)
      (argVals_sim ha he hag) fun xs vs h =>
        SimUpTo.ok (Forall2.cons (VR.irr (t := some a) (ρ := ρ) (ls := ls)) h)).congr
      (fun k => ?_) (fun k => ?_)
    · simp only [Src.slotsOf, Src.slotOf, hr', ↓reduceIte, Sem.Result.bind_ok,
        Sem.Result.bind_assoc, Src.forceAll_cons, Src.force_val]
    · simp only [List.map_cons, Lam.evalList_cons, Lam.eval_box', Sem.Result.bind_ok]
  | _, _, _, .strict (rest := rest) (rest' := rest') hr ha hrest, ρ, ρ', ls, he, hag => by
    have hr' : _ = false := (hag.irr _).symm.trans hr
    refine (SimUpTo.bind
      (d := fun x k => ((Src.slotsOf S.p k ls ρ rest).bind (Src.forceAll S.p k)).bind
        fun xs => .ok (x :: xs))
      (d' := fun x' k => (Lam.evalList S.L k ρ' (rest'.map (·.1))).bind fun vs => .ok (x' :: vs))
      (Lam.eval_mono S.L _ _)
      (fun _ => (Lam.evalList_mono S.L _ _).bind fun _ => ClockMono.const _)
      (tr_sim ha he hag) fun x x' hx =>
        SimUpTo.bind (d := fun xs _ => .ok (x :: xs)) (d' := fun vs _ => .ok (x' :: vs))
          (Lam.evalList_mono S.L _ _) (fun _ => ClockMono.const _)
          (argVals_sim hrest he hag) fun xs vs h => SimUpTo.ok (Forall2.cons hx h)).congr
      (fun k => ?_) (fun k => ?_)
    · simp only [Src.slotsOf, Src.slotOf, hr', Bool.false_eq_true, ↓reduceIte,
        Sem.Result.bind_ok, Sem.Result.bind_assoc, Src.forceAll_cons, Src.force_val]
    · simp only [List.map_cons, Lam.evalList_cons]

/-- A head's arguments bound in order: the relevant strict ones `let`-bound
(SrcEval evaluates the same ones to value slots), by-name ones kept as thunks,
irrelevant ones □. -/
theorem bind_sim : ∀ {cx : Cx} {xs : List (Src.Term.Arg × Bool)} {lets : List Term}
    {refs : List Ref} {cx' : Cx}, BindR S.I S.G cx xs lets refs cx' →
    ∀ {ρ : Src.Env} {ρ' : Env} {ls : Levels}, EnvR S.I S.G cx ρ ρ' → Agree ls cx.prof →
    ∀ {K : List Src.Slot → Nat → Result Src.Value} {X : Term},
      (∀ ss ys, Forall2 (RefSlot S.I S.G ls ρ (ys ++ ρ')) refs ss →
        EnvR S.I S.G cx' ρ (ys ++ ρ') →
        SimUpTo (VR S.I S.G) m (K ss) (fun k => Lam.eval S.L k (ys ++ ρ') X)) →
      SimUpTo (VR S.I S.G) m
        (fun k => (Src.slotsOf S.p k ls ρ (xs.map (·.1))).bind fun ss => K ss k)
        (fun k => Lam.eval S.L k ρ' (wrapLets lets X))
  | _, _, _, _, _, .nil, ρ, ρ', ls, he, _, K, X, hK =>
    (hK [] [] .nil he).congr (fun k => by simp only [List.map_nil, Src.slotsOf, Sem.Result.bind_ok])
      (fun k => rfl)
  | _, _, _, _, _, .irr (a := a) (r := r) hr hrest, ρ, ρ', ls, he, hag, K, X, hK => by
    have hr' : _ = true := (hag.irr _).symm.trans hr
    refine (bind_sim hrest he hag (K := fun ss => K (.val (.irr (some a) ρ ls) :: ss))
      fun ss ys hrs he' => hK _ ys (.cons (.box ⟨_, _, _, rfl⟩) hrs) he').congr
      (fun k => ?_) (fun k => rfl)
    simp only [List.map_cons, Src.slotsOf, Src.slotOf, hr', ↓reduceIte, Sem.Result.bind_ok,
      Sem.Result.bind_assoc]
  | _, _, _, _, _, .name (a := a) (r := r) hr hrest, ρ, ρ', ls, he, hag, K, X, hK => by
    have hr' : _ = false := (hag.irr _).symm.trans hr
    refine (bind_sim hrest he hag (K := fun ss => K (.name a ρ ls :: ss))
      fun ss ys hrs he' => hK _ ys (.cons .name hrs) he').congr (fun k => ?_) (fun k => rfl)
    simp only [List.map_cons, Src.slotsOf, Src.slotOf, hr', Bool.false_eq_true, ↓reduceIte,
      Sem.Result.bind_ok, Sem.Result.bind_assoc]
  | cx, _, _, _, _, .strict (a := a) (r := r) (v := v) hr ha hrest, ρ, ρ', ls, he, hag, K, X,
      hK => by
    have hr' : _ = false := (hag.irr _).symm.trans hr
    refine (SimUpTo.bind (Lam.eval_mono S.L _ _) (fun _ => Lam.eval_mono S.L _ _)
      (tr_sim ha he hag) fun x x' hx =>
        bind_sim hrest (he.extra1 (.val x')) hag (K := fun ss => K (.val x :: ss))
          fun ss ys hrs he' => ?_).congr (fun k => ?_) (fun k => eval_wrapLets_cons S.L k ρ' v _ X)
    · have e : (ys ++ [Slot.val x']) ++ ρ' = ys ++ (.val x' :: ρ') := by simp
      have hlvl : RefSlot S.I S.G ls ρ (ys ++ (.val x' :: ρ')) (.lvl cx.depth) (.val x) :=
        (RefSlot.lvl (by simp [he.depth]) (by simp [he.depth]) hx).extend ys
      have := hK (.val x :: ss) (ys ++ [.val x'])
      rw [e] at this
      exact this (.cons hlvl hrs) he'
    · simp only [List.map_cons, Src.slotsOf, Src.slotOf, hr', Bool.false_eq_true, ↓reduceIte,
        Sem.Result.bind_ok, Sem.Result.bind_assoc]

/-- A constructor's fields, evaluated after its parameters' lets. -/
theorem fields_sim : ∀ {cx cx' : Cx} {c : CId} {q : Profile} {j : Nat}
    {args : List Src.Term.Arg} {fs : List Term}, FieldsR S.I S.G cx cx' c q j args fs →
    ∀ {ρ : Src.Env} {ρ'' : Env} {ls : Levels}, EnvR S.I S.G cx' ρ ρ'' → Agree ls cx.prof →
      cx'.prof = cx.prof →
      SimUpTo (fun fvs vs => KeptR S.I S.G c j fvs vs ∧ fvs.length = args.length ∧
          vs.length = fs.length) m
        (fun k => (Src.slotsOf S.p k ls ρ args).bind (Src.forceAll S.p k))
        (fun k => Lam.evalList S.L k ρ'' fs)
  | _, _, _, _, _, _, _, .nil, ρ, ρ'', ls, _, _, _ =>
    (SimUpTo.ok ⟨.nil, rfl, rfl⟩).congr
      (fun k => by simp only [Src.slotsOf, Sem.Result.bind_ok, Src.forceAll_nil])
      (fun k => Lam.evalList_nil S.L k ρ'')
  | _, _, c, q, j, _, _, .keptIrr (a := a) hk hr hrest, ρ, ρ'', ls, he, hag, hp => by
    have hr' : _ = true := (hag.irr _).symm.trans (by rw [← hp]; exact hr)
    have hk' : S.I.kept c [] j = true := by rw [← Input.kept_prof S.I c q j]; exact hk
    refine (SimUpTo.bind (Lam.evalList_mono S.L _ _) (fun _ => ClockMono.const _)
      (fields_sim hrest he hag hp) fun fvs vs h =>
        SimUpTo.ok ⟨.kept hk' (VR.irr (t := some a) (ρ := ρ) (ls := ls)) h.1,
          by simp [h.2.1], by simp [h.2.2]⟩).congr (fun k => ?_) (fun k => ?_)
    · simp only [Src.slotsOf, Src.slotOf, hr', ↓reduceIte, Sem.Result.bind_ok,
        Sem.Result.bind_assoc, Src.forceAll_cons, Src.force_val]
    · simp only [Lam.evalList_cons, Lam.eval_box', Sem.Result.bind_ok]
  | _, _, c, q, j, _, _, .keptRel (rest := rest) (fs := fs) hk hr ha hrest, ρ, ρ'', ls, he, hag,
      hp => by
    have hr' : _ = false := (hag.irr _).symm.trans (by rw [← hp]; exact hr)
    have hk' : S.I.kept c [] j = true := by rw [← Input.kept_prof S.I c q j]; exact hk
    refine (SimUpTo.bind
      (d := fun x k => ((Src.slotsOf S.p k ls ρ rest).bind (Src.forceAll S.p k)).bind
        fun fvs => .ok (x :: fvs))
      (d' := fun x' k => (Lam.evalList S.L k ρ'' fs).bind fun vs => .ok (x' :: vs))
      (Lam.eval_mono S.L _ _)
      (fun _ => (Lam.evalList_mono S.L _ _).bind fun _ => ClockMono.const _)
      (tr_sim ha he (by rw [hp]; exact hag)) fun x x' hx =>
        SimUpTo.bind (d := fun fvs _ => .ok (x :: fvs)) (d' := fun vs _ => .ok (x' :: vs))
          (Lam.evalList_mono S.L _ _) (fun _ => ClockMono.const _)
          (fields_sim hrest he hag hp) fun fvs vs h =>
            SimUpTo.ok ⟨.kept hk' hx h.1, by simp [h.2.1], by simp [h.2.2]⟩).congr
      (fun k => ?_) (fun k => ?_)
    · simp only [Src.slotsOf, Src.slotOf, hr', Bool.false_eq_true, ↓reduceIte,
        Sem.Result.bind_ok, Sem.Result.bind_assoc, Src.forceAll_cons, Src.force_val]
    · simp only [Lam.evalList_cons]
  | _, _, c, q, j, _, _, .drop (a := a) hk hr hrest, ρ, ρ'', ls, he, hag, hp => by
    have hr' : _ = true := (hag.irr _).symm.trans hr
    have hk' : S.I.kept c [] j = false := by rw [← Input.kept_prof S.I c q j]; exact hk
    refine (SimUpTo.bind (Lam.evalList_mono S.L _ _) (fun _ => ClockMono.const _)
      (fields_sim hrest he hag hp) fun fvs vs h =>
        SimUpTo.ok ⟨.drop (f := .irr (some a) ρ ls) hk' rfl h.1, by simp [h.2.1],
          h.2.2⟩).congr (fun k => ?_) (fun k => (Sem.Result.bind_pure _).symm)
    simp only [Src.slotsOf, Src.slotOf, hr', ↓reduceIte, Sem.Result.bind_ok,
      Sem.Result.bind_assoc, Src.forceAll_cons, Src.force_val]

/-- A saturated special head in place: its arguments' slots, then the
firing, against the head's form. -/
theorem sat_sim : ∀ {cx : Cx} {h : Head} {q : Profile} {args : List Src.Term.Arg} {t₀ : Term},
    SatR S.I S.G cx h q args t₀ → ∀ {c₀ : CId}, S.I.headOf c₀ = some h →
    args.length = headArity S.I h →
    ∀ {ρ : Src.Env} {ρ' : Env} {ls ls' : Levels}, EnvR S.I S.G cx ρ ρ' → Agree ls cx.prof →
      Agree ls' q →
      SimUpTo (VR S.I S.G) m (fun k => (Src.slotsOf S.p k ls ρ args).bind (Src.fire S.p k h ls'))
        (fun k => Lam.eval S.L k ρ' t₀)
  | _, _, _, _, _, .prim (op := op) hargs, _, _, _, ρ, ρ', ls, ls', he, hag, _ =>
    (SimUpTo.bind (Lam.evalList_mono S.L _ _) (fun _ => ClockMono.const _)
      (argVals_sim hargs he hag) fun _ _ hxs => prim_value_sim wf op hxs).congr
      (fun k => by
        rw [Sem.Result.bind_assoc]
        exact Sem.Result.bind_congr _ fun ss => Src.fire_prim S.p k ls' op ss)
      (fun k => Lam.eval_prim S.L k ρ' _ _)
  | _, _, _, _, _, .word (w := w) (op := op) hu hu' hargs, _, _, _, ρ, ρ', ls, ls', he, hag, _ =>
    (SimUpTo.bind (Lam.evalList_mono S.L _ _) (fun _ => ClockMono.const _)
      (argVals_sim hargs he hag) fun _ _ hxs => word_value_sim S hu hu' hxs).congr
      (fun k => by
        rw [Sem.Result.bind_assoc]
        exact Sem.Result.bind_congr _ fun ss => Src.fire_word S.p k ls' w op ss)
      (fun k => Lam.eval_prim S.L k ρ' _ _)
  | _, _, _, _, _, .natZero (c := c) (args := args) hd hz, _, _, hlen, ρ, ρ', ls, ls', _, _,
      _ => by
    obtain ⟨sf', lv', N, cidx', ty', hdz⟩ := wf.zeroPin hz
    rw [hd] at hdz
    cases hdz
    have hnil : args = [] := List.eq_nil_of_length_eq_zero (by simpa [headArity, hd] using hlen)
    subst hnil
    refine (SimUpTo.ok (VR.lit (n := 0))).congr (fun k => ?_) (fun k => Lam.eval_lit S.L k ρ' _)
    have e : Src.fire S.p k (.ctor c) ls' [] = Src.fire S.p k (.ctor c) ls' ([] ++ []) := rfl
    simp only [Src.slotsOf, Sem.Result.bind_ok]
    rw [e, S.fire_ctor_split hd k ls' rfl [], Src.forceAll_nil, Sem.Result.bind_ok,
      S.ctorResult_zero hz]
  | _, _, _, _, _, .natSucc (c := c) (args := args) (np := np) (nf := nf) (lets := lets)
      (fs := fs) hd hz hs hbind hargs, _, _, hlen, ρ, ρ', ls, ls', he, hag, _ => by
    have hlen' : args.length = np + nf := by simpa [headArity, hd] using hlen
    refine (bind_sim hbind he hag
      (K := fun pss k => (Src.slotsOf S.p k ls ρ (args.drop np)).bind fun fss =>
        Src.fire S.p k (.ctor c) ls' (pss ++ fss))
      (X := .prim .natAdd (fs.map (·.1) ++ [.lit (.nat 1)])) fun pss ys hrs he' => ?_).congr
      (fun k => by rw [map_fst_pair]; exact slotsOf_split S.p k ls ρ args np _) (fun k => rfl)
    have hpl : pss.length = np := by
      rw [← hrs.length, hbind.refs_length]; simp; omega
    refine (SimUpTo.bind (d := fun xs _ => Src.ctorResult S.p c ls' pss xs)
      (d' := fun vs _ => Lam.primResult S.L.known .natAdd (vs ++ [.lit (.nat 1)]))
      (Lam.evalList_mono S.L _ _) (fun _ => ClockMono.const _)
      (argVals_sim hargs he' (by rw [hbind.cx_eq]; exact hag)) fun xs vs hxs => ?_).congr
      (fun k => ?_) (fun k => ?_)
    · by_cases hx : ∃ n, xs = [.lit n]
      · obtain ⟨n, rfl⟩ := hx
        cases hxs with
        | cons hv hrest =>
          cases hrest
          cases hv
          exact (SimUpTo.ok VR.lit).congr (fun _ => S.ctorResult_succ hz hs ls' pss n)
            (fun _ => primResult_succ _ n)
      · exact (SimUpTo.stuck _).congr
          (fun _ => S.ctorResult_succ_stuck hz hs ls' pss fun n e => hx ⟨n, e⟩) (fun _ => rfl)
    · rw [Sem.Result.bind_assoc]
      exact Sem.Result.bind_congr _ fun fss => S.fire_ctor_split hd k ls' hpl fss
    · rw [Lam.eval_prim, evalList_append_single, Sem.Result.bind_assoc]
      exact Sem.Result.bind_congr _ fun vs => by rw [Lam.eval_lit, Sem.Result.bind_ok,
        Sem.Result.bind_ok]
  | _, _, _, _, _, .ctorUnbox (c := c) (q := q) (args := args) (ind := ind) (np := np)
      (nf := nf) (f := f) hd hz hs hbind hfields hu, _, _, hlen, ρ, ρ', ls, ls', he, hag, _ => by
    have hlen' : args.length = np + nf := by simpa [headArity, hd] using hlen
    refine (bind_sim hbind he hag
      (K := fun pss k => (Src.slotsOf S.p k ls ρ (args.drop np)).bind fun fss =>
        Src.fire S.p k (.ctor c) ls' (pss ++ fss)) (X := f) fun pss ys hrs he' => ?_).congr
      (fun k => by rw [map_fst_pair]; exact slotsOf_split S.p k ls ρ args np _) (fun k => rfl)
    have hpl : pss.length = np := by
      rw [← hrs.length, hbind.refs_length]; simp; omega
    refine (SimUpTo.bind (d := fun fvs _ => Src.ctorResult S.p c ls' pss fvs)
      (d' := fun vs _ => .ok (vs.headD .box))
      (Lam.evalList_mono S.L _ _) (fun _ => ClockMono.const _)
      (fields_sim hfields he' hag (by rw [hbind.cx_eq]; rfl)) fun fvs vs hr => ?_).congr
      (fun k => ?_) (fun k => eval_evalList_single S.L k _ f)
    · obtain ⟨hkr, hl1, hl2⟩ := hr
      match vs, hl2, hkr with
      | [v'], _, hkr =>
        exact (SimUpTo.ok (vr_unboxed wf hd (by rw [← Input.unbox?_prof S.I ind q]; exact hu)
          (by rw [hl1]; simp; omega) hkr)).congr (fun _ => S.ctorResult_con hz hs ls' pss fvs)
          (fun _ => rfl)
      | [], h, _ => simp at h
      | _ :: _ :: _, h, _ => simp at h
    · rw [Sem.Result.bind_assoc]
      exact Sem.Result.bind_congr _ fun fss => S.fire_ctor_split hd k ls' hpl fss
  | _, _, _, _, _, .ctorBox (c := c) (q := q) (args := args) (ind := ind) (np := np) (nf := nf)
      (fields := fields) hd hz hs hbind hfields hu, _, _, hlen, ρ, ρ', ls, ls', he, hag, _ => by
    have hlen' : args.length = np + nf := by simpa [headArity, hd] using hlen
    refine (bind_sim hbind he hag
      (K := fun pss k => (Src.slotsOf S.p k ls ρ (args.drop np)).bind fun fss =>
        Src.fire S.p k (.ctor c) ls' (pss ++ fss))
      (X := .con (S.I.ctorKey c) fields) fun pss ys hrs he' => ?_).congr
      (fun k => by rw [map_fst_pair]; exact slotsOf_split S.p k ls ρ args np _) (fun k => rfl)
    have hpl : pss.length = np := by
      rw [← hrs.length, hbind.refs_length]; simp; omega
    refine (SimUpTo.bind (d := fun fvs _ => Src.ctorResult S.p c ls' pss fvs)
      (d' := fun vs _ => .ok (.con (S.I.ctorKey c) vs))
      (Lam.evalList_mono S.L _ _) (fun _ => ClockMono.const _)
      (fields_sim hfields he' hag (by rw [hbind.cx_eq]; rfl)) fun fvs vs hr => ?_).congr
      (fun k => ?_) (fun k => Lam.eval_con S.L k _ _ _)
    · obtain ⟨hkr, hl1, _⟩ := hr
      exact (SimUpTo.ok (VR.con hd (by rw [hl1]; simp; omega)
        (by rw [← Input.unbox?_prof S.I ind q]; exact hu) hkr)).congr
        (fun _ => S.ctorResult_con hz hs ls' pss fvs) (fun _ => rfl)
    · rw [Sem.Result.bind_assoc]
      exact Sem.Result.bind_congr _ fun fss => S.fire_ctor_split hd k ls' hpl fss
  | _, _, _, _, _, .quotMk (c := c) (args := args) (e := e) hbind hre, _, hh, hlen, ρ, ρ', ls,
      ls', he, hag, _ => by
    obtain ⟨lv, ty, hq⟩ := S.headOf_quotMk hh
    refine (bind_sim hbind he hag (K := fun ss k => Src.fire S.p k (.quotMk c) ls' ss) (X := e)
      fun ss ys hrs he' => ?_).congr (fun k => by rw [map_fst_pair]) (fun k => rfl)
    have hl : ss.length = 3 := by
      rw [← hrs.length, hbind.refs_length]; simpa [headArity] using hlen
    match ss, hl, hrs with
    | [_, _, _], _, hrs =>
      exact S.quotMk_form hq he'.depth (hrs.getD_refSlot (i := 2) (by simp)) hre
        (hbind.getD_ne_name 2)
  | _, _, _, _, _, .quotLift (c := c) (args := args) (f := f) (x := x) hbind hrf hrq, _, _, hlen,
      ρ, ρ', ls, ls', he, hag, _ => by
    refine (bind_sim hbind he hag (K := fun ss k => Src.fire S.p k (.quotLift c) ls' ss)
      (X := .tick (.app f x .strict)) fun ss ys hrs he' => ?_).congr
      (fun k => by rw [map_fst_pair]) (fun k => rfl)
    have hl : ss.length = 6 := by
      rw [← hrs.length, hbind.refs_length]; simpa [headArity] using hlen
    match ss, hl, hrs with
    | [_, _, _, _, _, _], _, hrs =>
      exact quotLift_form hlt he'.depth (hrs.getD_refSlot (i := 3) (by simp)) hrf
        (hbind.getD_ne_name 3) (hrs.getD_refSlot (i := 5) (by simp)) hrq (hbind.getD_ne_name 5)
  | _, _, _, _, _, .casesEmpty (c := c) (r := r) hres hd hbind hk, _, _, _, ρ, ρ', ls, ls', he,
      hag, hag' =>
    (bind_sim hbind he hag (K := fun ss k => Src.fire S.p k (.cases c) ls' ss) (X := .tick .trap)
      fun ss ys _ _ => cases_empty_form hres hd hk hag' ss).congr
      (fun k => by rw [map_fst_zipIdx _ (fun ⟨_, _⟩ => rfl)]) (fun k => rfl)
  | cx, _, _, _, _, .casesSub (c := c) (r := r) (np := np) (nmin := nmin) (ni := ni)
      (refs := refs) (body := body) hres hd hbind hk hbody, _, _, hlen, ρ, ρ', ls, ls', he, hag, hag' => by
    have hmin := wf.subMinor hd (S.kindAt_sub hk)
    refine (bind_sim hbind he hag (K := fun ss k => Src.fire S.p k (.cases c) ls' ss)
      (X := .tick body) fun ss ys hrs he' => ?_).congr
      (fun k => by rw [map_fst_zipIdx _ (fun ⟨_, _⟩ => rfl)]) (fun k => rfl)
    have hl : ss.length = np + 1 + ni + 1 + nmin := by
      rw [← hrs.length, hbind.refs_length]; simpa [headArity, hres, hd] using hlen
    refine cases_sub_form wf hlt hres hd hk he' (by rw [hbind.cx_eq]; exact hag) hag'
      (FormArgs.of_forall2 hrs) hl (fun i hi a e => ?_) (fun i l e sig => ?_) hmin hbody
    · obtain ⟨x, hx⟩ := hbind.getD_name_zipIdx e
      simp only [decide_eq_true_eq] at hx
      omega
    · have hge : cx.depth ≤ l := by
        have hi : i < refs.length := by
          refine Nat.lt_of_not_le fun hge => ?_
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at e
          cases e
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at e
        exact hbind.lvl_ge (by rw [List.getElem?_eq_getElem hi]; simpa using e)
      rw [hbind.cx_eq]
      exact he.minorsLt.lookup_none hge sig
  | cx, _, _, _, _, .casesUnbox (c := c) (r := r) (np := np) (nmin := nmin) (ni := ni)
      (refs := refs) (l := l) (body := body) hres hd hbind hk hl hu hbody,
      _, _, hlen, ρ, ρ', ls, ls', he, hag, hag' => by
    refine (bind_sim hbind he hag (K := fun ss k => Src.fire S.p k (.cases c) ls' ss)
      (X := .tick body) fun ss ys hrs he' => ?_).congr
      (fun k => by rw [map_fst_zipIdx _ (fun ⟨_, _⟩ => rfl)]) (fun k => rfl)
    have hl' : ss.length = np + 1 + ni + 1 + nmin := by
      rw [← hrs.length, hbind.refs_length]; simpa [headArity, hres, hd] using hlen
    refine cases_unbox_form wf hlt hres hd hk hu he' (by rw [hbind.cx_eq]; exact hag) hag'
      (FormArgs.of_forall2 hrs) hl' hl (fun sig => ?_) hbody
    have hge : cx.depth ≤ l := by
      have hi : np + 1 + ni < refs.length := by
        refine Nat.lt_of_not_le fun hge => ?_
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hl
        cases hl
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hl
      exact hbind.lvl_ge (by rw [List.getElem?_eq_getElem hi]; simpa using hl)
    rw [hbind.cx_eq]
    exact he.minorsLt.lookup_none hge sig
  | _, _, _, _, _, .casesOrd (cx' := cx') (c := c) (r := r) (np := np) (nmin := nmin) (ni := ni) (l := l)
      (alts := alts) hres hd hbind hk hl hu halts, _, _, hlen, ρ, ρ', ls, ls', he, hag, hag' => by
    refine (bind_sim hbind he hag (K := fun ss k => Src.fire S.p k (.cases c) ls' ss)
      (X := .tick (.case (cx'.lvl l) alts none)) fun ss ys hrs he' => ?_).congr
      (fun k => by rw [map_fst_zipIdx _ (fun ⟨_, _⟩ => rfl)]) (fun k => rfl)
    have hl' : ss.length = np + 1 + ni + 1 + nmin := by
      rw [← hrs.length, hbind.refs_length]; simpa [headArity, hres, hd] using hlen
    exact cases_ord_form wf hlt hres hd hk hu he' (by rw [hbind.cx_eq]; exact hag) hag'
      (FormArgs.of_forall2 hrs) hl' hl halts
  | _, _, _, _, _, .recr (r := r) (np := np) (nmot := nmot) (nmin := nmin) (ni := ni)
      (argTerms := argTerms) (g := g) hd hbind _ hargs hg, _, _, hlen, ρ, ρ', ls, ls', he, hag,
      hag' => by
    refine (bind_sim hbind he hag (K := fun ss k => Src.fire S.p k (.recr r) ls' ss)
      (X := Term.apps (.glob g) argTerms) fun ss ys hrs he' => ?_).congr
      (fun k => by rw [map_fst_zipIdx _ (fun ⟨_, _⟩ => rfl)]) (fun k => rfl)
    have hl : ss.length = np + nmot + nmin + ni + 1 := by
      rw [← hrs.length, hbind.refs_length]; simpa [headArity, hd] using hlen
    refine recr_form wf hlt hd he' (by rw [hbind.cx_eq]; exact hag) hag'
      (FormArgs.of_forall2 hrs) hl (fun j a hnm e => ?_) hargs hg
    obtain ⟨x, hx⟩ := hbind.name_flag_zipIdx e
    simp only [decide_eq_true_eq] at hx
    exact hnm hx

end

end

end Setting

end IxCC.Lam.Erase.Proof
