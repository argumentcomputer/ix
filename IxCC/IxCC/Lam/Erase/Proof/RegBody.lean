import IxCC.Lam.Erase.Proof.RegBuild
import IxCC.Lam.Erase.Proof.ProgWF

/-! # Every constructor key of an erased program has a row

The bodies of the globals (`keyBody`) register their keys, the queue loop
keeps every erased body's keys registered as the table grows, and so a
successful erasure ends with a table (`CtorInv`) in which every constructor
key of every global has a row (`erase_reg`). -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels NatMap)

section

variable (I : Input) (wf : ProgWF I)
include wf

theorem reg_rec_ : RecReg I (rec_ I) := reg_term I wf termFuel

theorem reg_constBody (c : CId) (q : Profile) :
    CSound I (constBody I c q) fun t T => RegT T t := by
  unfold constBody
  dsimp only
  split
  · exact reg_rec_ I wf _ _
  · exact reg_rec_ I wf _ _
  · exact CSound.decline
  · split
    · exact reg_rec_ I wf _ _
    · refine CSound.ite (fun _ => reg_rec_ I wf _ _) fun _ => CSound.decline
    · exact CSound.decline
    · exact CSound.decline

theorem reg_ruleBody (r : CId) (q : Profile) (pre depth : Nat)
    (minors : List (Nat × List Mode)) (rule : Src.Rule) (fields : List (Option Nat)) :
    CSound I (ruleBody I r q pre depth minors rule fields) fun t T => RegT T t := by
  unfold ruleBody
  dsimp only
  refine CSound.ite (fun _ => ?_) fun _ => CSound.decline_bind
  split
  · refine CSound.bind (reg_rec_ I wf _ _) fun h => ?_
    refine CSound.bind (CSound.mapM_all (P := fun y T => RegT T y.1) fun x _ => ?_) fun args' => ?_
    · obtain ⟨a, m, rl⟩ := x
      dsimp only
      refine CSound.ite (fun _ => CSound.pure fun _ => .box) fun _ => ?_
      refine CSound.ite (fun _ => ?_) fun _ => ?_
      · exact CSound.bind (reg_rec_ I wf _ _) fun t => CSound.pure fun _ ht => ht
      · exact CSound.bind (reg_rec_ I wf _ _) fun t => CSound.pure fun _ ht => ht
    · refine CSound.ite (fun _ => ?_) fun _ => CSound.pure fun _ ha hh => RegT.apps hh ha
      split
      · refine CSound.ite (fun _ => CSound.pure fun _ ha hh => RegT.apps hh ha) fun _ =>
          CSound.decline_bind
      · exact CSound.decline_bind
  · exact reg_rec_ I wf _ _

theorem reg_recStarBody (r : CId) (q : Profile) :
    CSound I (recStarBody I r q) fun t T => RegT T t := by
  unfold recStarBody
  dsimp only
  split
  · next sf k lv np nmot nmin ni ind rules ty hd =>
    split
    · exact CSound.bind (CSound.pure (R := fun b _ => b = Term.trap) fun _ => rfl) fun body =>
        CSound.pure fun _ hb => by subst hb; exact RegT.lams .trap
    · split
      · exact CSound.bind (reg_ruleBody I wf r q _ _ _ _ _) fun body =>
          CSound.pure fun _ hb => RegT.lams hb
      · exact CSound.decline_bind
    · refine CSound.ite (fun _ => CSound.decline_bind) fun _ => ?_
      refine CSound.bind (CSound.mapM_all (P := fun a T => AltReg T a) fun x _ => ?_) fun alts =>
        CSound.bind (CSound.pure (R := fun b _ => b = (Term.var 0).case alts none) fun _ => rfl)
          fun body => CSound.pure fun _ hb ha => by
            subst hb
            exact RegT.lams (RegT.case_of (.var 0) ha fun _ h => by cases h)
      obtain ⟨rule, j⟩ := x
      dsimp only
      exact CSound.bind (reg_ruleAlt I r q _ ind j rule) fun ⟨key, n, fields⟩ =>
        CSound.bind (reg_ruleBody I wf r q _ _ _ rule fields) fun body =>
          CSound.pure fun _ hb ha => ⟨key, n, body, rfl, ⟨_, ha⟩, hb⟩
    · exact CSound.decline_bind
  · exact CSound.decline

theorem reg_wrapperBody (h : Head) (q : Profile) :
    CSound I (wrapperBody I h q) fun t T => RegT T t := by
  unfold wrapperBody
  cases h with
  | prim op =>
    exact CSound.pure fun _ => RegT.lams (.prim fun a ha => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 ha
      exact .var _)
  | ctor c | quotMk c | quotLift c | recr c | cases c =>
    dsimp only
    refine CSound.ite (fun _ => ?_) fun _ => CSound.decline_bind
    exact CSound.bind (reg_saturated (reg_rec_ I wf) wf _ _ q _) fun t =>
      CSound.pure fun _ hs => RegT.lams hs

theorem reg_keyBody (key : Key.GKey) :
    CSound I (keyBody I key) fun t T => RegT T t.1 := by
  unfold keyBody
  dsimp only
  split
  · exact CSound.bind (reg_constBody I wf _ _) fun body => CSound.pure fun _ h => h
  · split
    · refine CSound.ite (fun _ => ?_) fun _ => CSound.decline_bind
      refine CSound.bind (reg_constBody I wf _ _) fun b₀ => ?_
      split
      · next t hs => exact CSound.pure fun _ h => RegT.setModes hs h
      · exact CSound.decline
    · exact CSound.decline
  · exact CSound.bind (reg_recStarBody I wf _ _) fun body => CSound.pure fun _ h => h
  · exact CSound.bind (reg_wrapperBody I wf _ _) fun body => CSound.pure fun _ h => h
  · exact CSound.decline

/-- Every erased body's keys have rows. -/
def GlobReg (s : St) : Prop :=
  ∀ g gl, s.globals.get? g = some gl → ∀ T : CTab, (∀ k n, tabOf s k n → T k n) → RegT T gl.body

omit wf in
theorem tabOf_mono {s s' : St}
    (h : ∀ c info, s.ctors.get? c = some info → s'.ctors.get? c = some info)
    {k : Key.CtorKey} {n : Nat} : tabOf s k n → tabOf s' k n :=
  fun ⟨c, info, hc, hk, hn⟩ => ⟨c, info, h c info hc, hk, hn⟩

theorem reg_loop : ∀ (fuel : Nat) (s s' : St), (loop I fuel).run s = .ok ((), s') →
    (∀ c info, s.ctors.get? c = some info → s'.ctors.get? c = some info) ∧
      (CtorInv I s → CtorInv I s') ∧ (GlobReg s → GlobReg s') ∧ (IdsSurj s → IdsSurj s')
  | 0, s, s', e => by
    unfold loop at e
    exact ((CSound.decline (I := I) (R := fun _ _ => False) s () s' e).2 (fun _ _ => True)
      fun _ _ _ => trivial).elim
  | fuel + 1, s, s', e => by
    unfold loop at e
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at e
    cases hf : s.front with
    | cons p rest =>
      obtain ⟨key, g⟩ := p
      rw [hf] at e
      dsimp only at e
      obtain ⟨_, s₁, e₁, e₂⟩ := Sound.bind_run e
      simp only [StateT.run_set] at e₁
      cases e₁
      obtain ⟨⟨body, res⟩, s₂, e₃, e₄⟩ := Sound.bind_run e₂
      obtain ⟨hg₂, hbody⟩ := reg_keyBody I wf key _ _ _ e₃
      obtain ⟨_, s₃, e₅, e₆⟩ := Sound.bind_run e₄
      simp only [StateT.run_modify] at e₅
      injection e₅ with e₅
      injection e₅ with _ e₅
      have hc₃ : s₃.ctors = s₂.ctors := by rw [← e₅]
      have ho₃ : s₃.ctorOrder = s₂.ctorOrder := by rw [← e₅]
      have hgl₃ : s₃.globals = s₂.globals.insert g ⟨key, body, res⟩ := by rw [← e₅]
      have hsub : ∀ c info, s.ctors.get? c = some info → s₃.ctors.get? c = some info :=
        fun c info h => by rw [hc₃]; exact hg₂.ctors c info h
      have hi₃ : s₃.ids = s₂.ids := by rw [← e₅]
      have hn₃ : s₃.next = s₂.next := by rw [← e₅]
      obtain ⟨h₁, h₂, h₃, h₄⟩ := reg_loop fuel s₃ s' e₆
      refine ⟨fun c info h => h₁ c info (hsub c info h),
        fun h => h₂ (CtorInv.frame hc₃ ho₃ (hg₂.inv (CtorInv.frame (s := s) rfl rfl h))),
        fun hs => h₃ fun g' gl hgl T hT => ?_,
        fun hs => h₄ (IdsSurj.frame hi₃ hn₃ (hg₂.surj (IdsSurj.frame (s := s) rfl rfl hs)))⟩
      have hT₂ : ∀ k n, tabOf s₂ k n → T k n := fun k n h => hT k n (by rw [tabOf, hc₃]; exact h)
      rw [hgl₃, NatMap.get?_insert] at hgl
      split at hgl
      · cases hgl
        exact hbody T hT₂
      · rw [hg₂.globals] at hgl
        exact hs g' gl hgl T fun k n h => hT k n (tabOf_mono hsub h)
    | nil =>
      rw [hf] at e
      dsimp only at e
      cases hb : s.back with
      | nil =>
        rw [hb] at e
        simp only [StateT.run_pure] at e
        cases e
        exact ⟨fun _ _ h => h, id, id, id⟩
      | cons p ps =>
        rw [hb] at e
        dsimp only at e
        obtain ⟨_, s₁, e₁, e₂⟩ := Sound.bind_run e
        simp only [StateT.run_set] at e₁
        cases e₁
        obtain ⟨h₁, h₂, h₃, h₄⟩ := reg_loop fuel _ s' e₂
        exact ⟨h₁, fun h => h₂ (CtorInv.frame (s := s) rfl rfl h), fun hs => h₃ hs,
          fun hs => h₄ (IdsSurj.frame (s := s) rfl rfl hs)⟩

omit wf in
theorem reg_rootId (c : CId) : CSound I (rootId I c) fun _ _ => True := by
  unfold rootId
  dsimp only
  split <;> first
    | exact csound_globalId I _
    | exact CSound.ite (fun _ => csound_globalId I _) fun _ => CSound.decline
    | exact CSound.decline

end

/-- **The constructor table of an erased program**: a successful erasure
ends in a state whose table keeps its invariant and has a row for every
constructor key of every global body. -/
theorem erase_reg {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program}
    {st : Erase.Stats} (h : erase p ch = .ok (L, st)) :
    ∃ s : St, (Erase.run (Input.ofProgram p ch)).run {} = .ok (L.roots, s) ∧
      L.globals = s.globals ∧ L.size = s.next ∧
      L.ctors = s.ctorOrder.reverse.filterMap s.ctors.get? ∧
      CtorInv (Input.ofProgram p ch) s ∧ IdsSurj s ∧
      ∀ g gl, L.global? g = some gl → RegT (tabOf s) gl.body := by
  have wf := erase_progWF h
  unfold erase at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  · next roots s hrun =>
    split at h
    · cases h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨s, hrun, rfl, rfl, rfl, ?_⟩
    unfold Erase.run at hrun
    dsimp only at hrun
    have main : ∀ (s₀ : St), (do
        let roots ← List.mapM (rootId (Input.ofProgram p ch)) (Input.ofProgram p ch).roots
        loop (Input.ofProgram p ch) loopFuel
        pure roots : M (List GlobalId)).run s₀ = .ok (roots, s) → s₀ = {} →
        CtorInv (Input.ofProgram p ch) s ∧ IdsSurj s ∧
          ∀ g gl, s.globals.get? g = some gl → RegT (tabOf s) gl.body := by
      intro s₀ e h0
      subst h0
      obtain ⟨rs, s_r, er, e'⟩ := Sound.bind_run e
      obtain ⟨_, s_l, el, ep⟩ := Sound.bind_run e'
      simp only [StateT.run_pure] at ep
      injection ep with ep
      injection ep with _ hs
      subst hs
      obtain ⟨hg_r, -⟩ := CSound.mapM_all (P := fun _ _ => True)
        (fun c _ => reg_rootId (Input.ofProgram p ch) c) {} rs s_r er
      obtain ⟨_, hinv, hglob, hsurj⟩ := reg_loop (Input.ofProgram p ch) wf loopFuel s_r s_l el
      have hgr : GlobReg s_r := by
        intro g gl hgl
        rw [hg_r.globals] at hgl
        simp [NatMap.get?] at hgl
      exact ⟨hinv (hg_r.inv (CtorInv.empty _)), hsurj (hg_r.surj fun g hg => by cases hg),
        fun g gl hgl => hglob hgr g gl hgl _ fun _ _ h => h⟩
    split at hrun
    · next s₁ hs =>
      by_cases hkept : (Input.ofProgram p ch).kept s₁ [] 0 = true
      · simp only [hkept, ↓reduceIte] at hrun
        exact main {} hrun rfl
      · simp only [hkept] at hrun
        exact (((CSound.decline_bind (I := Input.ofProgram p ch) (R := fun _ _ => False)) {} _ _
          hrun).2 (fun _ _ => True) fun _ _ _ => trivial).elim
    · exact main {} hrun rfl

end IxCC.Lam.Erase.Proof
