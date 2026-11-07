import IxCC.Lam.Erase.Proof.BuildForms

/-! # Erasure of terms meets its specification

`Erase.term` at any fuel is sound (`RecSound`): every term it returns is a
`TR` erasure of its input, against every key relation containing the final
key table; a constant's spine goes through `constSpine` (a special head in
place or through its wrapper, or a δ body's global or its by-name variant),
a projection through `projForm` (M2.2). -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)

section Lazy

variable {I : Input}

/-- One leading argument of a by-name variant. -/
def LazyOne (I : Input) (G : Key.GKey → GlobalId → Prop) (cx : Cx) (m : Mode) (x : Src.Term.Arg)
    (y : Term × Mode) : Prop :=
  (m = .strict ∧ x.2.2.irrP cx.prof = true ∧ y = (.box, .strict)) ∨
    (m = .name ∧ x.2.2.irrP cx.prof = false ∧ x.2.1 = .byName ∧ TR I G cx x.1 y.1 ∧ y.2 = .name)

theorem LazyArgsR.of_one {G : Key.GKey → GlobalId → Prop} {cx : Cx} {m : Mode} {ms : List Mode}
    {x : Src.Term.Arg} {xs : List Src.Term.Arg} {y : Term × Mode} {ys : List (Term × Mode)}
    (h : LazyOne I G cx m x y) (hr : LazyArgsR I G cx ms xs ys) :
    LazyArgsR I G cx (m :: ms) (x :: xs) (y :: ys) := by
  obtain ⟨a, sm, r⟩ := x
  rcases h with ⟨hm, hr', rfl⟩ | ⟨hm, hr', hsm, ht, hy⟩
  · exact .irr hm hr' hr
  · obtain ⟨t, md⟩ := y
    dsimp only at hsm ht hy
    subst hsm hy
    exact .name hm hr' ht hr

theorem sound_lazyArgs {cx : Cx} {ms : List Mode} {F : Src.Term.Arg × Nat → M (Term × Mode)}
    (hF : ∀ x i, Sound (F (x, i)) fun y G => LazyOne I G cx (ms.getD i .strict) x y) :
    ∀ (xs : List Src.Term.Arg) (j : Nat), xs.length + j ≤ ms.length →
      Sound ((xs.zipIdx j).mapM F) fun ys G => LazyArgsR I G cx (ms.drop j) xs ys
  | [], _, _ => Sound.pure fun _ => .nil
  | x :: xs, j, hl => by
    rw [List.zipIdx_cons, List.mapM_cons]
    have hj : j < ms.length := by simp at hl; omega
    have hdrop : ms.drop j = ms.getD j .strict :: ms.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        Option.getD_some]
    rw [hdrop]
    exact Sound.bind (hF x j) fun y =>
      Sound.bind (sound_lazyArgs hF xs (j + 1) (by simp at hl ⊢; omega)) fun ys =>
        Sound.pure fun _ hr hy => LazyArgsR.of_one hy hr

end Lazy

theorem spine_go_ne : ∀ (t : Src.Term) (acc : List Src.Term.Arg), acc ≠ [] →
    (Src.Term.spine.go t acc).2 ≠ []
  | .app f a m r, acc, _ => by
    simp only [Src.Term.spine.go]
    exact spine_go_ne f _ (by simp)
  | .var _, _, h | .sort _, _, h | .const .., _, h | .lam .., _, h | .pi .., _, h
  | .letE .., _, h | .proj .., _, h | .natLit _, _, h | .strLit _, _, h => by
    simpa [Src.Term.spine.go] using h

section Spines

variable {I : Input} {rec : Rec} (hrec : RecSound I rec)
include hrec

theorem sound_special (cx : Cx) {c : CId} {us : List Ixon.Univ} {h : Head}
    (hus : us.length ≤ I.lvls c) (hh : I.headOf c = some h) (args : List Src.Term.Arg) :
    Sound (special I rec cx h (I.profileOf c cx.prof us) args) fun t G =>
      TR I G cx (Src.Term.mkApps (.const c us) args) t := by
  unfold special
  dsimp only
  refine Sound.ite (fun hlt => ?_) fun hge => ?_
  · exact Sound.bind (sound_globalId _) fun g =>
      Sound.bind (sound_strictArgs hrec cx args) fun args' =>
        Sound.pure fun _ ha hg => .wrap hus hh hlt hg ha
  · exact Sound.bind (sound_saturated hrec cx h _ _) fun t =>
      Sound.bind (sound_strictArgs hrec cx _) fun args' =>
        Sound.pure fun _ ha hs => .sat hus hh (by omega) hs ha

theorem sound_plainConst (cx : Cx) {c : CId} {us : List Ixon.Univ} (hus : us.length ≤ I.lvls c)
    {b : Src.Term} (hb : I.deltaBody c = some b) (args : List Src.Term.Arg) :
    Sound (plainConst I rec cx c (I.profileOf c cx.prof us) args) fun t G =>
      TR I G cx (Src.Term.mkApps (.const c us) args) t := by
  unfold plainConst
  dsimp only
  have hplain : (∀ a, I.lazy.get? c = some a → a ≤ args.length →
      hasName (lazyModes I c (I.profileOf c cx.prof us) a) = false) →
      Sound (globalId (.const c (I.profileOf c cx.prof us)) >>= fun g =>
        strictArgs rec cx args >>= fun args' => (Pure.pure (Term.apps (.glob g) args') : M Term))
        fun t G => TR I G cx (Src.Term.mkApps (.const c us) args) t := fun hl =>
    Sound.bind (sound_globalId _) fun g =>
      Sound.bind (sound_strictArgs hrec cx args) fun args' =>
        Sound.pure fun _ ha hg => .plain hus hb hl hg ha
  cases hlz : I.lazy.get? c with
  | none =>
    exact hplain fun a h _ => by rw [hlz] at h; cases h
  | some a =>
    dsimp only
    by_cases hc : (decide (args.length ≥ a) && hasName (lazyModes I c (I.profileOf c cx.prof us) a)) =
        true
    · rw [if_pos hc]
      dsimp only
      have hle : a ≤ args.length := by simp at hc; exact hc.1
      have hhas : hasName (lazyModes I c (I.profileOf c cx.prof us) a) = true := by
        simp at hc; exact hc.2
      refine Sound.bind (sound_lazyArgs (cx := cx) (ms := lazyModes I c (I.profileOf c cx.prof us) a)
        (fun x i => ?_) (args.take a) 0
        (by simp [lazyModes]; omega)) fun lazyArgs =>
          Sound.bind (sound_globalId _) fun g =>
            Sound.bind (sound_strictArgs hrec cx _) fun rest' =>
              Sound.pure fun _ hr hg hl => .variant hus hb hlz hle hhas hg (by simpa using hl) hr
      obtain ⟨x, sm, r⟩ := x
      dsimp only
      split
      · next hm hr => exact Sound.pure fun _ => .inl ⟨hm, hr, rfl⟩
      · next _ hm hr =>
        exact Sound.bind (hrec cx x) fun t => Sound.pure fun _ ht =>
          .inr ⟨hm, hr, rfl, ht, rfl⟩
      · exact Sound.decline
      · exact Sound.decline
    · rw [if_neg hc]
      exact hplain fun a' h hle => by
        rw [hlz] at h
        cases h
        cases hn : hasName (lazyModes I c (I.profileOf c cx.prof us) a)
        · rfl
        · exfalso; apply hc; simp [hle, hn]

theorem sound_constSpine (cx : Cx) (c : CId) (us : List Ixon.Univ) (args : List Src.Term.Arg) :
    Sound (constSpine I rec cx c us args) fun t G =>
      TR I G cx (Src.Term.mkApps (.const c us) args) t := by
  unfold constSpine
  dsimp only
  refine Sound.ite (fun _ => Sound.decline_bind) fun hus => ?_
  have hus' : us.length ≤ I.lvls c := by omega
  split
  · next op hr => exact sound_special hrec cx hus' (by simp [Input.headOf, hr]) args
  · next r' hr => exact sound_special hrec cx hus' (by simp [Input.headOf, hr]) args
  · next g vs thm hr =>
    exact sound_plainConst hrec cx hus' (b := .const g vs) (by simp [Input.deltaBody, hr]) args
  · next thm body hr =>
    exact sound_plainConst hrec cx hus' (b := body) (by simp [Input.deltaBody, hr]) args
  · next hr =>
    split
    · next hd => exact sound_special hrec cx hus' (by simp [Input.headOf, hr, hd]) args
    · next hd => exact sound_special hrec cx hus' (by simp [Input.headOf, hr, hd]) args
    · next hd => exact sound_special hrec cx hus' (by simp [Input.headOf, hr, hd]) args
    · next hd => exact sound_special hrec cx hus' (by simp [Input.headOf, hr, hd]) args
    · next lv ty v hd =>
      exact sound_plainConst hrec cx hus' (b := v) (by simp [Input.deltaBody, hr, hd]) args
    · next lv ty v hd =>
      refine Sound.ite (fun hop => ?_) fun _ => Sound.decline
      exact sound_plainConst hrec cx hus' (b := v) (by simp [Input.deltaBody, hr, hd, hop]) args
    · exact Sound.decline
    · exact Sound.decline

theorem sound_projForm (cx : Cx) (s i : Nat) (e : Src.Term) :
    Sound (projForm I rec cx s i e) fun t G => TR I G cx (.proj s i e) t := by
  unfold projForm
  refine Sound.bind (hrec cx e) fun e' => ?_
  split
  · next k hk =>
    split
    · next fields hf =>
      split
      · next cls hcls =>
        refine Sound.ite (fun hdrop => Sound.pure fun _ he => .projDrop he hk hf hcls hdrop)
          fun hdrop => ?_
        have hdrop' : cls.dropP [] = false := by simpa using hdrop
        refine Sound.ite (fun hu => Sound.pure fun _ he => .projUnbox he hk hf hcls hdrop' hu)
          fun hu => ?_
        have hu' : I.unbox? s [] = none := by simpa using hu
        split
        · next sf lv ind cidx np nf ty hd =>
          exact Sound.bind (sound_registerCtor _ _ _) fun _ =>
            Sound.pure fun _ _ he => .projKey he hk hf hcls hdrop' hu' hd
        · exact Sound.decline
      · exact Sound.decline
    · exact Sound.decline
  · exact Sound.decline

end Spines

/-- Erasure of terms is sound at every fuel. -/
theorem sound_term (I : Input) : ∀ n : Nat, RecSound I (term I n)
  | 0 => fun cx t => by
    unfold term
    exact Sound.decline
  | n + 1 => fun cx t => by
    have ih := sound_term I n
    unfold term
    dsimp only
    cases t with
    | var i =>
      dsimp only
      split
      · next l hl => exact Sound.pure fun _ => .varSome hl
      · next hl => exact Sound.pure fun _ => .varNone hl
      · exact Sound.decline
    | sort u => exact Sound.pure fun _ => .sort
    | pi b res d c => exact Sound.pure fun _ => .pi
    | natLit k => exact Sound.pure fun _ => .natLit
    | strLit _ => exact Sound.decline
    | lam b d body =>
      exact Sound.bind (ih cx.bind body) fun t => Sound.pure fun _ h => .lam .strict h
    | letE c r ty v b =>
      dsimp only
      refine Sound.ite (fun hr => ?_) fun hr => ?_
      · exact Sound.bind (Sound.pure (Q := fun v' _ => v' = Term.box) fun _ => rfl) fun v' =>
          Sound.bind (ih cx.bind b) fun b' => Sound.pure fun _ hb hv => by
            subst hv; exact .letIrr hr hb
      · have hr' : r.irrP cx.prof = false := by simpa using hr
        exact Sound.bind (ih cx v) fun v' => Sound.bind (ih cx.bind b) fun b' =>
          Sound.pure fun _ hb hv => .letRel hr' hv hb
    | proj s i e => exact sound_projForm ih cx s i e
    | const c us =>
      dsimp only
      exact sound_constSpine ih cx c us []
    | app f a m r =>
      dsimp only
      have hsp : (Src.Term.app f a m r).spineL =
          ((Src.Term.app f a m r).spine.1, (Src.Term.app f a m r).spine.2) := rfl
      have heq := spineL_mkApps hsp
      have hne : (Src.Term.app f a m r).spine.2 ≠ [] := by
        simp only [Src.Term.spine, Src.Term.spine.go]
        exact spine_go_ne f _ (by simp)
      generalize (Src.Term.app f a m r).spine.1 = hd at heq ⊢
      generalize (Src.Term.app f a m r).spine.2 = args at heq hne ⊢
      rw [heq]
      split
      · next c us => exact sound_constSpine ih cx c us args
      · next hnc =>
        exact Sound.bind (ih cx hd) fun h' => Sound.bind (sound_strictArgs ih cx args) fun args' =>
          Sound.pure fun _ ha hh => .app (fun c us e => hnc c us e) hne hh ha

end IxCC.Lam.Erase.Proof
