import IxCC.Lam.Erase.Proof.Reg

/-! # Erasure registers every constructor key it emits

Every builder of `Lam.Erase` keeps the constructor table's rows and
invariant (`CtorInv`) and returns terms whose constructor keys all have rows
in the final table (`RegT`): `ctorForm`, `ruleAlt` and `projForm` register a
key before they emit it, and everything else only combines terms. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)

/-- The recursive call erasure's helpers receive registers its keys. -/
def RecReg (I : Input) (rec : Rec) : Prop :=
  ∀ cx t, CSound I (rec cx t) fun t' T => RegT T t'

/-- An alternative whose key has a row and whose body registers its keys. -/
def AltReg (T : CTab) (a : Alt) : Prop :=
  ∃ k n b, a = .mk k n b ∧ (∃ n', T k n') ∧ RegT T b

theorem RegT.case_of {T : CTab} {s : Term} {alts : List Alt} {d : Option Term} (hs : RegT T s)
    (ha : ∀ a ∈ alts, AltReg T a) (hd : ∀ t ∈ d, RegT T t) : RegT T (.case s alts d) :=
  .case hs (fun k n b h => by
      obtain ⟨k', n', b', e, hk, _⟩ := ha _ h
      cases e
      exact hk)
    (fun k n b h => by
      obtain ⟨k', n', b', e, _, hb⟩ := ha _ h
      cases e
      exact hb) hd

theorem CSound.filterMapM_all {I : Input} {γ β : Type} {f : γ → M (Option β)}
    {P : β → CTab → Prop} :
    ∀ {xs : List γ}, (∀ x ∈ xs, CSound I (f x) fun o T => ∀ y ∈ o, P y T) →
      CSound I (xs.filterMapM f) fun ys T => ∀ y ∈ ys, P y T
  | [], _ => CSound.pure fun _ _ h => by cases h
  | x :: xs, h => by
    rw [List.filterMapM_cons]
    refine CSound.bind (h x List.mem_cons_self) fun o => ?_
    have ih := CSound.filterMapM_all (f := f) (P := P) fun z hz => h z (List.mem_cons_of_mem _ hz)
    cases o with
    | none => exact ih.imp fun ys T hys _ => hys
    | some y =>
      exact CSound.bind ih fun ys => CSound.pure fun T hys hy z hz =>
        (List.mem_cons.1 hz).elim (fun e => e ▸ hy y rfl) (hys z)

/-! ## Arguments -/

section Args

variable {I : Input} {rec : Rec} (hrec : RecReg I rec)
include hrec

theorem reg_strictArg (cx : Cx) (x : Src.Term.Arg) :
    CSound I (strictArg rec cx x) fun y T => RegT T y.1 := by
  obtain ⟨a, m, r⟩ := x
  unfold strictArg
  by_cases hr : r.irrP cx.prof = true
  · simp only [hr, ↓reduceIte]
    exact CSound.pure fun _ => .box
  · have hr' : r.irrP cx.prof = false := by simpa using hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte]
    cases m with
    | strict => exact CSound.bind (hrec cx a) fun t => CSound.pure fun _ ht => ht
    | byName => exact CSound.decline

theorem reg_strictArgs (cx : Cx) (args : List Src.Term.Arg) :
    CSound I (strictArgs rec cx args) fun ys T => ∀ y ∈ ys, RegT T y.1 :=
  CSound.mapM_all fun x _ => reg_strictArg hrec cx x

theorem reg_bindArgs : ∀ (cx : Cx) (xs : List (Src.Term.Arg × Bool)),
    CSound I (bindArgs rec cx xs) fun r T => ∀ v ∈ r.1, RegT T v
  | cx, [] => by
    unfold bindArgs
    exact CSound.pure fun _ _ h => by cases h
  | cx, ((a, m, r), ok) :: rest => by
    unfold bindArgs
    by_cases hr : r.irrP cx.prof = true
    · simp only [hr, ↓reduceIte]
      exact CSound.bind (reg_bindArgs cx rest) fun ⟨ls, rs, cx'⟩ =>
        CSound.pure fun _ h => h
    · have hr' : r.irrP cx.prof = false := by simpa using hr
      simp only [hr', Bool.false_eq_true, ↓reduceIte]
      cases m with
      | byName =>
        dsimp only
        cases ok with
        | true =>
          simp only [↓reduceIte]
          exact CSound.bind (reg_bindArgs cx rest) fun ⟨ls, rs, cx'⟩ =>
            CSound.pure fun _ h => h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact CSound.decline_bind
      | strict =>
        exact CSound.bind (hrec cx a) fun v =>
          CSound.bind (reg_bindArgs (cx.extra 1) rest) fun ⟨ls, rs, cx'⟩ =>
            CSound.pure fun _ h hv w hw => (List.mem_cons.1 hw).elim (fun e => e ▸ hv) (h w)

theorem reg_refTerm (cx : Cx) (ref : Ref) :
    CSound I (refTerm rec cx ref) fun t T => RegT T t := by
  cases ref with
  | box => exact CSound.pure fun _ => .box
  | lvl l => exact CSound.pure fun _ => .var _
  | name a => exact hrec cx a

omit hrec in
theorem fieldArgs_reg {T : CTab} (cx : Cx) (fields : List (Option Nat)) :
    ∀ a ∈ fields.map (fun
      | some l => (cx.lvl l, Mode.strict)
      | none => (Term.box, Mode.strict)), RegT T a.1 := by
  intro a ha
  obtain ⟨o, _, rfl⟩ := List.mem_map.1 ha
  cases o with
  | some l => exact .var _
  | none => exact .box

theorem reg_minorApp (cx : Cx) (minor : Ref) (fields : List (Option Nat)) :
    CSound I (minorApp rec cx minor fields) fun t T => RegT T t := by
  unfold minorApp
  cases minor with
  | box => exact CSound.pure fun _ => RegT.apps .box (fieldArgs_reg cx fields)
  | lvl l => exact CSound.pure fun _ => RegT.apps (.var _) (fieldArgs_reg cx fields)
  | name m =>
    dsimp only
    exact CSound.bind (hrec _ _) fun body' =>
      CSound.pure fun _ h => RegT.apps (.tick h) fun a ha =>
        fieldArgs_reg cx fields a (List.mem_of_mem_drop ha)

end Args

/-! ## `ruleAlt` -/

theorem reg_ruleAlt (I : Input) (r : CId) (q : Profile) (base : Nat) (ind : CId) (j : Nat)
    (rule : Src.Rule) :
    CSound I (ruleAlt I r q base ind j rule) fun x T => T x.1 x.2.1 := by
  unfold ruleAlt
  split
  · next s lv ind' cidx np nf ty hd =>
    dsimp only
    split
    · next hc =>
      exact CSound.bind (csound_registerCtor I _ _ _
        ⟨rule.ctor, s, lv, ind', cidx, np, nf, ty, hd, rfl, Input.keptCount_prof I _ _ _⟩)
        fun _ => CSound.pure fun _ h => h
    · exact CSound.decline_bind
  · exact CSound.decline

/-! ## Saturated forms -/

section Forms

variable {I : Input} {rec : Rec} (hrec : RecReg I rec)
include hrec

theorem reg_primForm (wf : ProgWF I) (cx : Cx) (op : Src.PrimOp) (args : List Src.Term.Arg) :
    CSound I (primForm I rec cx op args) fun t T => RegT T t := by
  unfold primForm
  dsimp only
  have hk : CSound I (strictArgs rec cx args >>= fun args' =>
      (Pure.pure (Term.prim (Prim.ofSrc op) (args'.map (·.1))) : M Term)) fun t T => RegT T t :=
    CSound.bind (reg_strictArgs hrec cx args) fun args' => CSound.pure fun _ h =>
      .prim fun a ha => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
        exact h y hy
  split
  · exact CSound.bind (csound_registerBool I wf) fun _ => hk.imp fun _ _ h _ => h
  · exact hk

theorem reg_quotMkForm (cx : Cx) (args : List Src.Term.Arg) :
    CSound I (quotMkForm rec cx args) fun t T => RegT T t := by
  unfold quotMkForm
  exact CSound.bind (reg_bindArgs hrec cx _) fun ⟨lets, refs, cx'⟩ =>
    CSound.bind (reg_refTerm hrec cx' _) fun e => CSound.pure fun _ he hb => RegT.wrapLets hb he

theorem reg_quotLiftForm (cx : Cx) (args : List Src.Term.Arg) :
    CSound I (quotLiftForm rec cx args) fun t T => RegT T t := by
  unfold quotLiftForm
  exact CSound.bind (reg_bindArgs hrec cx _) fun ⟨lets, refs, cx'⟩ =>
    CSound.bind (reg_refTerm hrec cx' _) fun f =>
      CSound.bind (reg_refTerm hrec cx' _) fun x =>
        CSound.pure fun _ hx hf hb => RegT.wrapLets hb (.tick (.app hf hx))

theorem reg_ctorForm (cx : Cx) (c : CId) (q : Profile) (args : List Src.Term.Arg) :
    CSound I (ctorForm I rec cx c q args) fun t T => RegT T t := by
  unfold ctorForm
  split
  · next sf lv ind cidx np nf ty hd =>
    split
    · exact CSound.pure fun _ => .lit _
    · refine CSound.bind (reg_bindArgs hrec cx _) fun ⟨lets, refs, cx'⟩ => ?_
      dsimp only
      split
      · exact CSound.bind (reg_strictArgs hrec cx' _) fun fs =>
          CSound.pure fun _ hf hb => RegT.wrapLets hb (.prim fun a ha => by
            rcases List.mem_append.1 ha with ha | ha
            · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
              exact hf y hy
            · simp only [List.mem_singleton] at ha
              subst ha
              exact .lit _)
      · refine CSound.bind (CSound.filterMapM_all (P := fun f T => RegT T f)
          fun x _ => ?_) fun fields => ?_
        · obtain ⟨⟨a, m, r⟩, j⟩ := x
          dsimp only
          split
          · exact CSound.bind (reg_strictArg hrec cx' (a, m, r)) fun y =>
              CSound.pure fun _ hy z hz => by cases hz; exact hy
          · split
            · exact CSound.decline_bind
            · exact CSound.pure fun _ _ h => by cases h
        · split
          · split
            · next f =>
              exact CSound.pure fun _ hF hb => RegT.wrapLets hb (hF f List.mem_cons_self)
            · exact CSound.decline
          · exact CSound.bind (csound_registerCtor I _ _ _
              ⟨c, sf, lv, ind, cidx, np, nf, ty, hd, rfl, Input.keptCount_prof I _ _ _⟩)
              fun _ => CSound.pure fun _ hk hF hb => RegT.wrapLets hb (.con ⟨_, hk⟩ hF)
  · exact CSound.decline

theorem reg_casesForm (cx : Cx) (c r : CId) (q : Profile) (args : List Src.Term.Arg) :
    CSound I (casesForm I rec cx c r q args) fun t T => RegT T t := by
  unfold casesForm
  split
  · next sf k lv np nmot nmin ni ind rules ty hd =>
    dsimp only
    refine CSound.bind (reg_bindArgs hrec cx _) fun ⟨lets, refs, cx'⟩ => ?_
    dsimp only
    split
    · exact CSound.bind (CSound.pure (R := fun b _ => b = Term.trap.tick) fun _ => rfl) fun body =>
        CSound.pure fun _ hbody hb => by subst hbody; exact RegT.wrapLets hb (.tick .trap)
    · exact CSound.bind (reg_minorApp hrec cx' _ _) fun body =>
        CSound.pure fun _ hm hb => RegT.wrapLets hb (.tick hm)
    · split
      · exact CSound.decline_bind
      · split
        · exact CSound.bind (reg_minorApp hrec cx' _ _) fun body =>
            CSound.pure fun _ hm hb => RegT.wrapLets hb (.tick hm)
        · refine CSound.bind (reg_refTerm hrec cx' _) fun scrut =>
            CSound.bind (CSound.mapM_all (P := fun a T => AltReg T a) fun x _ => ?_) fun alts =>
              CSound.bind (CSound.pure (R := fun b _ => b = (scrut.case alts none).tick)
                fun _ => rfl) fun body => CSound.pure fun _ hbody halts hsc hb => ?_
          · obtain ⟨rule, j⟩ := x
            dsimp only
            exact CSound.bind (reg_ruleAlt I r q cx'.depth ind j rule) fun ⟨key, arity, fields⟩ =>
              CSound.bind (reg_minorApp hrec _ _ _) fun body =>
                CSound.pure fun _ hm ha => ⟨key, arity, body, rfl, ⟨_, ha⟩, hm⟩
          · subst hbody
            exact RegT.wrapLets hb (.tick (RegT.case_of hsc halts fun _ h => by cases h))
    · exact CSound.decline_bind
  · exact CSound.decline

theorem reg_recForm (cx : Cx) (r : CId) (q : Profile) (args : List Src.Term.Arg) :
    CSound I (recForm I rec cx r q args) fun t T => RegT T t := by
  unfold recForm
  split
  · next sf k lv np nmot nmin ni ind rules ty hd =>
    dsimp only
    refine CSound.bind (reg_bindArgs hrec cx _) fun ⟨lets, refs, cx'⟩ => ?_
    dsimp only
    refine CSound.ite (fun _ => CSound.decline_bind) fun _ => ?_
    refine CSound.bind (CSound.mapM_all (P := fun y T => RegT T y.1) fun x _ => ?_) fun argTerms =>
      CSound.bind (csound_globalId I _) fun g =>
        CSound.pure fun _ _ ha hb => RegT.wrapLets hb (RegT.apps (.glob g) ha)
    obtain ⟨ref, i⟩ := x
    dsimp only
    refine CSound.ite (fun _ => ?_) fun _ => ?_
    · exact CSound.bind (reg_refTerm hrec cx' ref) fun t => CSound.pure fun _ h => h
    · cases ref with
      | box =>
        dsimp only
        refine CSound.ite (fun _ => CSound.decline_bind) fun _ => ?_
        exact CSound.pure fun _ => .box
      | lvl l =>
        dsimp only
        refine CSound.ite (fun _ => CSound.decline_bind) fun _ => ?_
        refine CSound.ite (fun _ => CSound.decline_bind) fun _ => ?_
        exact CSound.pure fun _ => .var _
      | name m =>
        dsimp only
        refine CSound.ite (fun _ => CSound.decline_bind) fun _ => ?_
        refine CSound.ite (fun _ => ?_) fun _ => ?_
        · exact CSound.bind (hrec cx' m) fun t => CSound.pure fun _ ht => ht
        · split
          · split
            · refine CSound.ite (fun _ => ?_) fun _ => CSound.decline
              exact CSound.pure fun _ => .var _
            · exact CSound.decline
          · refine CSound.ite (fun _ => CSound.decline_bind) fun _ => ?_
            refine CSound.bind (hrec cx' m) fun t => ?_
            split
            · next t' hs => exact CSound.pure fun _ ht => RegT.setModes hs ht
            · exact CSound.decline
  · exact CSound.decline

theorem reg_saturated (wf : ProgWF I) (cx : Cx) (h : Head) (q : Profile)
    (args : List Src.Term.Arg) :
    CSound I (saturated I rec cx h q args) fun t T => RegT T t := by
  unfold saturated
  cases h with
  | prim op => exact reg_primForm hrec wf cx op args
  | ctor c => exact reg_ctorForm hrec cx c q args
  | quotMk c => exact reg_quotMkForm hrec cx args
  | quotLift c => exact reg_quotLiftForm hrec cx args
  | cases c =>
    dsimp only
    split
    · next r hres => exact reg_casesForm hrec cx c r q args
    · exact CSound.decline
  | recr r => exact reg_recForm hrec cx r q args

end Forms

/-! ## Spines and terms -/

section Spines

variable {I : Input} {rec : Rec} (hrec : RecReg I rec)
include hrec

theorem reg_special (wf : ProgWF I) (cx : Cx) (h : Head) (q : Profile) (args : List Src.Term.Arg) :
    CSound I (special I rec cx h q args) fun t T => RegT T t := by
  unfold special
  dsimp only
  refine CSound.ite (fun _ => ?_) fun _ => ?_
  · exact CSound.bind (csound_globalId I _) fun g =>
      CSound.bind (reg_strictArgs hrec cx args) fun args' =>
        CSound.pure fun _ ha _ => RegT.apps (.glob g) ha
  · exact CSound.bind (reg_saturated hrec wf cx h _ _) fun t =>
      CSound.bind (reg_strictArgs hrec cx _) fun args' =>
        CSound.pure fun _ ha hs => RegT.apps hs ha

theorem reg_plainConst (cx : Cx) (c : CId) (q : Profile) (args : List Src.Term.Arg) :
    CSound I (plainConst I rec cx c q args) fun t T => RegT T t := by
  unfold plainConst
  dsimp only
  split
  · refine CSound.bind (CSound.mapM_all (P := fun y T => RegT T y.1) fun x _ => ?_) fun lazyArgs =>
      CSound.bind (csound_globalId I _) fun g =>
        CSound.bind (reg_strictArgs hrec cx _) fun rest' =>
          CSound.pure fun _ hr _ hl => RegT.apps (.glob g) fun a ha =>
            (List.mem_append.1 ha).elim (hl a) (hr a)
    obtain ⟨⟨x, sm, r⟩, i⟩ := x
    dsimp only
    split
    · exact CSound.pure fun _ => .box
    · exact CSound.bind (hrec cx x) fun t => CSound.pure fun _ ht => ht
    · exact CSound.decline
    · exact CSound.decline
  · exact CSound.bind (csound_globalId I _) fun g =>
      CSound.bind (reg_strictArgs hrec cx args) fun args' =>
        CSound.pure fun _ ha _ => RegT.apps (.glob g) ha

theorem reg_constSpine (wf : ProgWF I) (cx : Cx) (c : CId) (us : List Ixon.Univ)
    (args : List Src.Term.Arg) :
    CSound I (constSpine I rec cx c us args) fun t T => RegT T t := by
  unfold constSpine
  dsimp only
  refine CSound.ite (fun _ => CSound.decline_bind) fun _ => ?_
  split
  · exact reg_special hrec wf cx _ _ args
  · exact reg_special hrec wf cx _ _ args
  · exact reg_plainConst hrec cx c _ args
  · exact reg_plainConst hrec cx c _ args
  · split
    · exact reg_special hrec wf cx _ _ args
    · exact reg_special hrec wf cx _ _ args
    · exact reg_special hrec wf cx _ _ args
    · exact reg_special hrec wf cx _ _ args
    · exact reg_plainConst hrec cx c _ args
    · refine CSound.ite (fun _ => ?_) fun _ => CSound.decline
      exact reg_plainConst hrec cx c _ args
    · exact CSound.decline
    · exact CSound.decline

theorem reg_projForm (cx : Cx) (s i : Nat) (e : Src.Term) :
    CSound I (projForm I rec cx s i e) fun t T => RegT T t := by
  unfold projForm
  refine CSound.bind (hrec cx e) fun e' => ?_
  split
  · next k hk =>
    split
    · next fields hf =>
      split
      · next cls hcls =>
        refine CSound.ite (fun _ => CSound.pure fun _ he => .letE he .box) fun _ => ?_
        refine CSound.ite (fun _ => CSound.pure fun _ he => he) fun _ => ?_
        split
        · next sf lv ind cidx np nf ty hd =>
          exact CSound.bind (csound_registerCtor I _ _ _
            ⟨k, sf, lv, ind, cidx, np, nf, ty, hd, rfl, rfl⟩)
            fun _ => CSound.pure fun _ hr he => .proj ⟨_, hr⟩ he
        · exact CSound.decline
      · exact CSound.decline
    · exact CSound.decline
  · exact CSound.decline

end Spines

/-- Erasure of terms registers its keys at every fuel. -/
theorem reg_term (I : Input) (wf : ProgWF I) : ∀ n : Nat, RecReg I (term I n)
  | 0 => fun cx t => by
    unfold term
    exact CSound.decline
  | n + 1 => fun cx t => by
    have ih := reg_term I wf n
    unfold term
    dsimp only
    cases t with
    | var i =>
      dsimp only
      split
      · exact CSound.pure fun _ => .var _
      · exact CSound.pure fun _ => .box
      · exact CSound.decline
    | sort u => exact CSound.pure fun _ => .box
    | pi b res d c => exact CSound.pure fun _ => .box
    | natLit k => exact CSound.pure fun _ => .lit _
    | strLit _ => exact CSound.decline
    | lam b d body =>
      exact CSound.bind (ih cx.bind body) fun t => CSound.pure fun _ h => .lam h
    | letE c r ty v b =>
      dsimp only
      refine CSound.ite (fun _ => ?_) fun _ => ?_
      · exact CSound.bind (CSound.pure (R := fun v' _ => v' = Term.box) fun _ => rfl) fun v' =>
          CSound.bind (ih cx.bind b) fun b' => CSound.pure fun _ hb hv => by
            subst hv; exact .letE .box hb
      · exact CSound.bind (ih cx v) fun v' => CSound.bind (ih cx.bind b) fun b' =>
          CSound.pure fun _ hb hv => .letE hv hb
    | proj s i e => exact reg_projForm ih cx s i e
    | const c us =>
      dsimp only
      exact reg_constSpine ih wf cx c us []
    | app f a m r =>
      dsimp only
      split
      · exact reg_constSpine ih wf cx _ _ _
      · exact CSound.bind (ih cx _) fun h' =>
          CSound.bind (reg_strictArgs ih cx _) fun args' =>
            CSound.pure fun _ ha hh => RegT.apps hh ha

end IxCC.Lam.Erase.Proof
