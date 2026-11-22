import IxCC.Anf.Proof.Convert.Step

/-! # ANF conversion: term lists and spine arguments

`convList` converts terms left to right, each with a meta-continuation that
converts the rest; `convArgs` does the same for a spine's arguments, turning
a `name` argument into the thunk closure `fn [_] t'`. Their simulations at
`fuel + 1` from `ConvAt n fuel` (P1). -/

set_option autoImplicit false

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Lam (Kind Mode argSlot applyArgs)
open IxCC.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec)
open IxCC.Ixon

namespace Setting

variable {S : Setting} {n fuel : Nat}

theorem convList_step (ih : S.ConvAt n fuel) {cx : Cx} {ts : List Lam.Term}
    {f : Nat → Nat → List Opd → M Exp} {e : Exp} {ρ : Lam.Env} {ρ' : List Val} {J' : List JClo}
    {ks : List Kind} {SKL : List Lam.Val → Nat → Result Lam.Val}
    (h : convList S.A (fuel + 1) cx ts f = .ok e) (henv : EnvR S.A S.G ks cx.vars ρ ρ')
    (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj) (hf : S.KFunR n ρ' J' S.OpdsR f SKL)
    (hts : ∀ t ∈ ts, TermOk S.G ks t) :
    SimUpTo S.V n (fun k => (Lam.evalList S.L k ρ ts).bind (SKL · k))
      (fun k => eval S.Q k ρ' J' e) := by
  cases ts with
  | nil =>
    rw [convList.eq_2 S.A (fuel + 1) cx f (Nat.succ_ne_zero _)] at h
    refine (hf h hd (List.suffix_refl _) hdj (List.suffix_refl _) [] ⟨[], rfl, .nil⟩).congr
      (fun k => ?_) (fun _ => rfl)
    rw [Lam.evalList_nil]; rfl
  | cons t ts =>
    rw [convList] at h
    refine (ih.conv (SK := fun v k => (Lam.evalList S.L k ρ ts).bind fun vs => SKL (v :: vs) k)
      h henv hd hdj ?_ (hts t List.mem_cons_self)).congr (fun k => ?_) (fun _ => rfl)
    · intro d' dj' o e' ρ'' J'' hf' hd' hρ hdj' hJ x ⟨w, hw, hxw⟩
      refine ih.convList hf' (henv.suffix hρ) hd' hdj' ?_ (fun t ht => hts t (List.mem_cons_of_mem _ ht))
      intro d'' dj'' os e'' ρ''' J''' hf'' hd'' hρ' hdj'' hJ' xs ⟨ws, hws, hxs⟩
      refine hf hf'' hd'' (hρ.trans hρ') hdj'' (hJ.trans hJ') (x :: xs) ⟨w :: ws, ?_, .cons hxw hxs⟩
      simp only [List.mapM_cons, Option.bind_eq_bind, Opd.val_suffix hρ' hw, Option.bind_some, hws,
        Option.pure_def]
    · show (Lam.evalList S.L k ρ (t :: ts)).bind (SKL · k) =
        (Lam.eval S.L k ρ t).bind fun v => (Lam.evalList S.L k ρ ts).bind fun vs => SKL (v :: vs) k
      rw [Lam.evalList_cons, Result.bind_assoc]
      exact Result.bind_congr _ fun v => by rw [Result.bind_assoc]; rfl

theorem convArgs_step (ih : S.ConvAt n fuel) {cx : Cx} {args : List (Lam.Term × Mode)}
    {f : Nat → Nat → List Opd → M Exp} {e : Exp} {ρ : Lam.Env} {ρ' : List Val} {J' : List JClo}
    {ks : List Kind} {tele : List Mode} {sigs : List (List Mode)} {i : Nat}
    {SKS : List Lam.Slot → Nat → Result Lam.Val}
    (h : convArgs S.A (fuel + 1) cx args f = .ok e) (henv : EnvR S.A S.G ks cx.vars ρ ρ')
    (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj)
    (hf : S.KFunR n ρ' J' (fun ss os ρ => S.SlotsMatch tele sigs i ss os ρ ∧ ss.length = args.length)
      f SKS) (hargs : ArgsOk S.G ks tele sigs i args) :
    SimUpTo S.V n (fun k => lamArgs S.L k ρ args SKS) (fun k => eval S.Q k ρ' J' e) := by
  cases args with
  | nil =>
    rw [convArgs.eq_2 S.A (fuel + 1) cx f (Nat.succ_ne_zero _)] at h
    exact (hf h hd (List.suffix_refl _) hdj (List.suffix_refl _) [] ⟨⟨[], rfl, .nil⟩, rfl⟩).congr
      (fun k => lamArgs_nil S.L k ρ SKS) (fun _ => rfl)
  | cons a rest =>
    obtain ⟨a, m⟩ := a
    cases m with
    | strict =>
      rw [convArgs.eq_3] at h
      cases hargs with
      | strict hexp ha hrest =>
      refine (ih.conv (SK := fun v k => lamArgs S.L k ρ rest fun ss => SKS (.val v :: ss))
        h henv hd hdj ?_ ha).congr (fun k => ?_) (fun _ => rfl)
      · intro d' dj' o e' ρ'' J'' hf' hd' hρ hdj' hJ x ⟨w, hw, hxw⟩
        refine ih.convArgs hf' (henv.suffix hρ) hd' hdj' ?_ hrest
        intro d'' dj'' os e'' ρ''' J''' hf'' hd'' hρ' hdj'' hJ' ss ⟨⟨ws, hws, hss⟩, hlen⟩
        refine hf hf'' hd'' (hρ.trans hρ') hdj'' (hJ.trans hJ') (.val x :: ss)
          ⟨⟨w :: ws, ?_, ?_⟩, by simp [hlen]⟩
        · simp only [List.mapM_cons, Option.bind_eq_bind, Opd.val_suffix hρ' hw, Option.bind_some,
            hws, Option.pure_def]
        · refine .cons ?_ hss
          rw [expKind_strict (by simpa [expected] using hexp)]
          exact .val hxw
      · show lamArgs S.L k ρ ((a, .strict) :: rest) SKS =
          (Lam.eval S.L k ρ a).bind fun v => lamArgs S.L k ρ rest fun ss => SKS (.val v :: ss)
        rw [lamArgs_cons]
        simp only [argSlot, Result.bind_assoc, Result.bind_ok]
    | name =>
      rw [convArgs.eq_4] at h
      obtain ⟨body, hbody, h⟩ := Lam.ModesOk.bind_ok h
      cases hargs with
      | name hexp hna hrest =>
      -- the thunk closure is free; then the rest with the thunk bound
      have hth : ThunkR S.A S.G (sigs.getD i []) ρ a (.clos ρ' 1 body []) :=
        .mk henv (by rw [hd]; exact hbody) (by simpa [expected] using hna) rfl
      rw [emit] at h
      obtain ⟨e', he', h⟩ := Lam.ModesOk.bind_ok h
      cases h
      have hsim := ih.convArgs he' (henv.cons' (.clos ρ' 1 body [])) (by simp [hd]) hdj
        (SKS := fun ss => SKS (.name ρ a :: ss)) ?_ hrest
      · refine hsim.congr (fun k => ?_) (fun k => ?_)
        · rw [lamArgs_cons]; rfl
        · rw [eval_bind, evalBind_fn S.Q k ρ' _ body (List.cons_ne_nil _ _)]; rfl
      · intro d'' dj'' os e'' ρ''' J''' hf'' hd'' hρ' hdj'' hJ' ss ⟨⟨ws, hws, hss⟩, hlen⟩
        refine hf hf'' hd'' ((List.suffix_cons _ ρ').trans hρ') hdj''
          ((List.suffix_refl J').trans hJ') (.name ρ a :: ss)
          ⟨⟨.clos ρ' 1 body [] :: ws, ?_, ?_⟩, by simp [hlen]⟩
        · have hv : (Opd.lvl cx.d).val ρ''' = some (.clos ρ' 1 body []) := by
            rw [← hd]; exact Opd.val_suffix hρ' (Opd.val_lvl_top ρ' _)
          simp only [List.mapM_cons, Option.bind_eq_bind, hv, Option.bind_some, hws, Option.pure_def]
        · refine .cons ?_ hss
          have hm : tele.getD i .strict = .name := by simpa [expected] using hexp
          simp only [expKind, hm, if_true]
          exact .name hth

end Setting

end IxCC.Anf.Convert.Proof
