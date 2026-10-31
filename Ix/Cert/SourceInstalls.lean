import Ix.Cert.SourceDeclares
import IxC.Kernel.Verify.Rename.UnionFold

/-! # What an accepted declaration installs

The converse of `Ix.Kernel.checkDecl_post` (which bounds what a declaration may
install): an accepted declaration installs a constant under each name it installs
itself (`selfInstalls`), and later declarations keep it (growth only conses), so a
reference accept's environment holds a constant under each of them
(`accepts_installs`).

A declaration installs every name it declares, except three, by the kernel's
specification:
* `sorryAx`'s declaration is accepted and installs nothing;
* `Quot.sound`'s axiom declaration, and the quotient constants' declarations other
  than the type's, are compared with the pinned quotient block and install nothing of
  their own: the type's declaration installs the whole block.
A pinned basis block (an inductive declaration that is one of the pins) installs its
pin, whose names are the block's. -/

namespace Ix.Cert.SourceInstalls

open Ix.Kernel

variable {md : Mode}

/-! ## Installed names -/

/-- `c` is stored under `k`. -/
def Installed (e : Env md) (k : Key md) : Prop := ∃ c ∈ e.consts, c.name = k

/-- `e'` keeps `e`'s constants. -/
def Keeps (e e' : Env md) : Prop := ∀ c ∈ e.consts, c ∈ e'.consts

theorem Keeps.refl (e : Env md) : Keeps e e := fun _ h => h

theorem Keeps.trans {e₁ e₂ e₃ : Env md} (h₁ : Keeps e₁ e₂) (h₂ : Keeps e₂ e₃) : Keeps e₁ e₃ :=
  fun c hc => h₂ c (h₁ c hc)

theorem Keeps.installed {e e' : Env md} (h : Keeps e e') {k : Key md} (hk : Installed e k) :
    Installed e' k :=
  let ⟨c, hc, hn⟩ := hk; ⟨c, h c hc, hn⟩

theorem Keeps.push (e : Env md) (c : Ix.Kernel.ConstantInfo md) : Keeps e ⟨c :: e.consts⟩ :=
  fun _ h => List.mem_cons_of_mem _ h

theorem Grows.keeps {Q : Key md → Prop} {e e' : Env md} (h : Grows Q e e') : Keeps e e' := by
  obtain ⟨new, h, -⟩ := h
  intro c hc
  rw [h]
  exact List.mem_append_right _ hc

theorem installed_push (e : Env md) (c : Ix.Kernel.ConstantInfo md) : Installed ⟨c :: e.consts⟩ c.name :=
  ⟨c, List.mem_cons_self, rfl⟩

/-- **The names a declaration installs itself.** -/
def selfInstalls : Declaration md → List (Key md)
  | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ => [cv.name]
  | .axiomDecl cv => if cv.name = quotSoundName ∨ cv.name = sorryAxName then [] else [cv.name]
  | .quotDecl .type _ => (BasisKind.quotK.declsA (md := md)).map (·.name)
  | .quotDecl _ _ => []
  | .basisDecl kind => kind.declsA.map (·.name)
  | .indDecl block _ => block.map (·.name)

/-! ## The pinned basis -/

/-- A run of basis installs keeps its environment and installs every constant it is given. -/
theorem foldlM_installBasis :
    ∀ (l : List (Ix.Kernel.ConstantInfo md)) (env e : Env md),
      (l.foldlM installBasisDecl env : CheckM md (Env md)) = .ok e →
        Keeps env e ∧ ∀ ci ∈ l, ci ∈ e.consts
  | [], env, e, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨Keeps.refl _, fun _ h => nomatch h⟩
  | ci :: l, env, e, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨e₁, h₁, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    have hpush : e₁ = ⟨ci :: env.consts⟩ := by
      unfold installBasisDecl at h₁
      split at h₁
      · simp only [pure, Except.pure, Except.ok.injEq] at h₁
        exact h₁.symm
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h₁
    subst hpush
    obtain ⟨keep, mem⟩ := foldlM_installBasis l _ e h
    refine ⟨(Keeps.push _ _).trans keep, fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact keep _ List.mem_cons_self
    · exact mem c hc

/-- **A basis install installs its pin.** -/
theorem checkBasisDecl_installs {env e : Env md} {kind : BasisKind}
    (h : (checkBasisDecl env kind : CheckM md (Env md)) = .ok e) :
    Keeps env e ∧ ∀ k ∈ kind.declsA.map (·.name), Installed e k := by
  unfold checkBasisDecl at h
  have run : (kind.declsA.foldlM installBasisDecl env : CheckM md (Env md)) = .ok e := by
    split at h
    · dsimp only at h
      split at h
      · exact h
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · exact h
  obtain ⟨keep, mem⟩ := foldlM_installBasis _ env e run
  refine ⟨keep, fun k hk => ?_⟩
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
  exact ⟨ci, mem ci hci, rfl⟩

/-- A pinned basis block's names are its pin's. -/
theorem basisPinHit_names {block : List (Ix.Kernel.ConstantInfo md)} {kind : BasisKind}
    (h : basisPinHit block = some kind) : block.map (·.name) = kind.decls.map (·.name) := by
  unfold basisPinHit at h
  have hfind := (Option.filter_eq_some_iff.mp h).1
  have := List.find?_some hfind
  exact (beq_iff_eq.mp this).symm

/-- The annotated pins name what the pins name. -/
theorem declsA_names (kind : BasisKind) :
    (kind.declsA (md := md)).map (·.name) = (kind.decls (md := md)).map (·.name) := by
  cases kind <;> cases md <;> decide

/-! ## What one declaration installs -/

variable {mode : CheckMode} {ops : (CheckerOps md) (CheckM md)}

/-- A checked constant's name is not reserved for the pinned basis. -/
theorem checkConstantVal_unreserved (env : Env md) (cv : Ix.Kernel.ConstantVal md) :
    ExPost (checkConstantVal ops env cv) (fun _ => reservedBasisNames.contains cv.name = false) := by
  unfold checkConstantVal
  by_cases hf : (env.find? cv.name).isSome = true
  · simp [hf]
  · by_cases hr : reservedBasisNames.contains cv.name = true
    · have hm : cv.name ∈ reservedBasisNames := by simpa using hr
      simp [hf, hm]
    · simp only [Bool.not_eq_true] at hr
      exact ExPost.of_forall fun _ => hr

/-- Every name a declaration installs itself is installed. -/
def InstallsAll (e : Env md) (d : Declaration md) : Prop := ∀ k ∈ selfInstalls d, Installed e k

theorem installsAll_of_nil {e : Env md} {d : Declaration md} (h : selfInstalls d = []) :
    InstallsAll e d := by
  intro k hk
  rw [h] at hk
  cases hk

/-- **An accepted declaration installs the names it installs itself**, inductive
blocks aside (`checkDecl_installs` adds them). -/
theorem checkDecl_installs_value (ev : Evidences md) (env : Env md) (d : Declaration md)
    (hind : ∀ block nP, d ≠ .indDecl block nP) :
    ExPost (checkDecl mode ops ev env d) (fun e => InstallsAll e d) := by
  cases d with
  | defnDecl cv value hint =>
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    rw [ExPost.post_bind]
    refine ExPost.mono (fun env2 h2 => ?_) (checkDefnVal_post env cvA value hint)
    obtain ⟨v, rfl⟩ := h2
    have hg : InstallsAll ⟨.defnInfo cvA v hint :: env.consts⟩ (.defnDecl cv value hint) := by
      intro k hk
      simp only [selfInstalls, List.mem_singleton] at hk
      subst hk
      exact ⟨_, List.mem_cons_self, h.1⟩
    simp [hg]
    intro _ _ _ _
    split <;> simp [hg]
  | thmDecl cv value =>
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    refine ExPost.mono (fun e he => ?_) (checkThmVal_post env cvA value)
    obtain ⟨v, rfl⟩ := he
    intro k hk
    simp only [selfInstalls, List.mem_singleton] at hk
    subst hk
    exact ⟨_, List.mem_cons_self, h.1⟩
  | opaqueDecl cv value =>
    unfold checkDecl
    rw [ExPost.post_bind]
    refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
    refine ExPost.mono (fun e he => ?_) (checkOpaqueVal_post env cvA value)
    subst he
    intro k hk
    simp only [selfInstalls, List.mem_singleton] at hk
    subst hk
    exact ⟨_, List.mem_cons_self, h.1⟩
  | axiomDecl cv =>
    by_cases hs : cv.name = quotSoundName ∨ cv.name = sorryAxName
    · exact ExPost.of_forall fun e => installsAll_of_nil (by simp [selfInstalls, hs])
    · have hq : ¬ cv.name = quotSoundName := fun h => hs (.inl h)
      have hsy : ¬ cv.name = sorryAxName := fun h => hs (.inr h)
      unfold checkDecl
      dsimp only
      simp only [hq, ↓reduceIte]
      rw [ExPost.post_bind]
      refine ExPost.mono (fun cvA h => ?_) (checkConstantVal_post env cv)
      have hg : InstallsAll ⟨.axiomInfo cvA :: env.consts⟩ (.axiomDecl cv) := by
        intro k hk
        simp only [selfInstalls, hs, ↓reduceIte, List.mem_singleton] at hk
        subst hk
        exact ⟨_, List.mem_cons_self, h.1⟩
      split
      · simpa using hg
      · split
        · simp
        · split
          · rename_i hsorry
            exact absurd (h.1 ▸ hsorry) hsy
          · simp
  | basisDecl kind =>
    unfold checkDecl
    intro e he
    exact (checkBasisDecl_installs he).2
  | quotDecl k cv =>
    unfold checkDecl
    simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
    intro _
    cases k with
    | type => exact fun e he => (checkBasisDecl_installs he).2
    | _ => exact ExPost.of_forall fun e => installsAll_of_nil rfl
  | indDecl block nP => exact absurd rfl (hind block nP)

/-! ## Inductive blocks: the modeled route -/

/-- A run of steps each of which keeps its environment, installs the step's name and
has `U` of its element, installs every name and has `U` of every element. -/
theorem foldlM_installs {α : Type} (step : Env md → α → CheckM md (Env md)) (nm : α → Key md)
    (U : α → Prop) :
    ∀ (l : List α) (env : Env md),
      (∀ e x, x ∈ l → ExPost (step e x) (fun e' => Keeps e e' ∧ Installed e' (nm x) ∧ U x)) →
      ExPost (l.foldlM step env) (fun e => Keeps env e ∧ ∀ x ∈ l, Installed e (nm x) ∧ U x)
  | [], env, _ => fun e he => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at he
    subst he
    exact ⟨Keeps.refl _, fun _ h => nomatch h⟩
  | x :: l, env, h => by
    simp only [List.foldlM_cons, ExPost.post_bind]
    refine ExPost.mono (fun e he => ?_) (h env x List.mem_cons_self)
    refine ExPost.mono (fun e' he' => ⟨he.1.trans he'.1, fun y hy => ?_⟩)
      (foldlM_installs step nm U l e fun e'' y hy => h e'' y (List.mem_cons_of_mem _ hy))
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨he'.1.installed he.2.1, he.2.2⟩
    · exact he'.2 y hy

/-- A run of steps each of which keeps its environment keeps it. -/
theorem foldlM_keeps {α : Type} (step : Env md → α → CheckM md (Env md)) :
    ∀ (l : List α) (env : Env md), (∀ e x, ExPost (step e x) (Keeps e)) →
      ExPost (l.foldlM step env) (Keeps env)
  | [], env, _ => fun e he => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at he
    subst he
    exact Keeps.refl _
  | x :: l, env, h => by
    simp only [List.foldlM_cons, ExPost.post_bind]
    exact ExPost.mono (fun e he => ExPost.mono (fun e' he' => he.trans he') (foldlM_keeps step l e h))
      (h env x)

theorem checkMemberVal_unreserved (blockNames : List (Key md)) (env' : Env md)
    (cv : Ix.Kernel.ConstantVal md) :
    ExPost (checkMemberVal ops blockNames env' cv)
      (fun _ => reservedBasisNames.contains cv.name = false) := by
  unfold checkMemberVal
  rw [ExPost.post_bind]
  exact ExPost.mono (fun _ h => ExPost.of_forall fun _ => h) (checkConstantVal_unreserved env' cv)

theorem checkMemberVal_named (blockNames : List (Key md)) (env' : Env md)
    (cv : Ix.Kernel.ConstantVal md) :
    ExPost (checkMemberVal ops blockNames env' cv)
      (fun r => r.name = cv.name ∧ reservedBasisNames.contains cv.name = false) :=
  fun a ha => ⟨(checkMemberVal_post blockNames env' cv a ha).1, checkMemberVal_unreserved blockNames env' cv a ha⟩

/-- **A modeled member is installed**, under an unreserved name. -/
theorem checkIndMember_installs (blockNames : List (Key md)) (caps : IndCaps md) (env' : Env md)
    (ci : Ix.Kernel.ConstantInfo md) :
    ExPost (checkIndMember ops blockNames caps env' ci)
      (fun e => Keeps env' e ∧ Installed e ci.name ∧ reservedBasisNames.contains ci.name = false) := by
  unfold checkIndMember
  rw [ExPost.post_bind]
  refine ExPost.mono (fun cvA h => ?_) (checkMemberVal_named blockNames env' ci.toConstantVal)
  cases ci with
  | indInfo cv c => exact (ExPost.post_pure).mpr ⟨Keeps.push _ _, ⟨_, List.mem_cons_self, h.1⟩, h.2⟩
  | ctorInfo cv a b => exact (ExPost.post_pure).mpr ⟨Keeps.push _ _, ⟨_, List.mem_cons_self, h.1⟩, h.2⟩
  | _ => simp

/-- The recursors' provisioning checks every recursor of the block. -/
theorem provisionRecs_covers (blockNames : List (Key md)) :
    ∀ (envAcc : Env md) (recs : List (Ix.Kernel.ConstantInfo md)),
      ExPost (provisionRecs ops blockNames envAcc recs)
        (fun r => ∀ ci ∈ recs, (∃ c ∈ r.2, c.1.name = ci.name) ∧
          reservedBasisNames.contains ci.name = false)
  | envAcc, [] => by simp [provisionRecs]
  | envAcc, ci :: rest => by
    unfold provisionRecs
    cases ci with
    | recInfo cv mI rP rules =>
      dsimp only
      rw [ExPost.post_bind]
      refine ExPost.mono (fun cvA h => ?_) (checkMemberVal_named blockNames envAcc _)
      rw [ExPost.post_bind]
      refine ExPost.mono (fun r hr => ?_) (provisionRecs_covers blockNames _ rest)
      obtain ⟨envSelf, others⟩ := r
      simp only [ExPost.post_pure]
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨⟨_, List.mem_cons_self, h.1⟩, h.2⟩
      · obtain ⟨⟨c', hc', hn⟩, hres⟩ := hr c hc
        exact ⟨⟨c', List.mem_cons_of_mem _ hc', hn⟩, hres⟩
    | _ => simp

/-- **A modeled block's recursors are installed**, under unreserved names. -/
theorem checkIndRecs_installs (blockNames : List (Key md)) (env₂ : Env md)
    (recs : List (Ix.Kernel.ConstantInfo md)) :
    ExPost (checkIndRecs mode ops blockNames env₂ recs)
      (fun e => Keeps env₂ e ∧ ∀ ci ∈ recs, Installed e ci.name ∧
        reservedBasisNames.contains ci.name = false) := by
  unfold checkIndRecs
  by_cases he : recs.isEmpty = true
  · have hnil : recs = [] := List.isEmpty_iff.mp he
    simp only [he, ↓reduceIte, ExPost.post_pure]
    exact ⟨Keeps.refl _, fun ci hci => by rw [hnil] at hci; cases hci⟩
  simp only [he, Bool.false_eq_true, ↓reduceIte, ExPost.post_bind, ExPost.post_ite,
    ExPost.post_throw, imp_true_iff, and_true]
  intro _
  refine ExPost.mono (fun r hr => ?_) (provisionRecs_covers blockNames env₂ recs)
  obtain ⟨envSelf, checked⟩ := r
  dsimp only at hr ⊢
  refine ExPost.mono (fun e he => ⟨he.1, fun ci hci => ?_⟩)
    (foldlM_installs _ (fun c => c.1.name) (fun _ => True) checked env₂ (fun e c _ => ?_))
  · obtain ⟨⟨c, hc, hn⟩, hres⟩ := hr ci hci
    exact ⟨hn ▸ (he.2 c hc).1, hres⟩
  · rw [ExPost.post_bind]
    refine ExPost.of_forall fun rules' => ?_
    simp only [ExPost.post_pure]
    exact ⟨Keeps.push _ _, installed_push _ _, trivial⟩

/-- **A modeled block installs every member**, under unreserved names. -/
theorem checkModeled_installs (env : Env md) (block : List (Ix.Kernel.ConstantInfo md)) :
    ExPost (checkModeled mode ops env block)
      (fun e => ∀ ci ∈ block, Installed e ci.name ∧ reservedBasisNames.contains ci.name = false) := by
  unfold checkModeled
  simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true, ExPost.post_bind]
  intro _
  split
  · simp only [ExPost.post_pure, ExPost.post_bind]
    refine ExPost.mono (fun env₂ h₂ => ?_) (foldlM_installs _ (·.name)
      (fun ci => reservedBasisNames.contains ci.name = false) _ env fun e ci _ =>
        checkIndMember_installs _ _ e ci)
    refine ExPost.mono (fun env₃ h₃ => ?_)
      (checkIndRecs_installs (mode := mode) (ops := ops) _ env₂ _)
    have at₃ : ∀ ci ∈ block, Installed env₃ ci.name ∧ reservedBasisNames.contains ci.name = false := by
      intro ci hci
      cases ci with
      | recInfo cv mI rP rules => exact h₃.2 _ (List.mem_filter.mpr ⟨hci, rfl⟩)
      | _ =>
        obtain ⟨i, u⟩ := h₂.2 _ (List.mem_filter.mpr ⟨hci, rfl⟩)
        exact ⟨h₃.1.installed i, u⟩
    simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, ExPost.post_pure,
      imp_true_iff, and_true]
    intro _ _
    refine ⟨fun _ => ExPost.mono (fun e he ci hci => ⟨he.installed (at₃ ci hci).1, (at₃ ci hci).2⟩)
      (foldlM_keeps _ _ env₃ fun e i => ?_), fun _ => at₃⟩
    refine ExPost.mono (fun e' he' => ?_) (installProjFnStep_post _ _ _ _ _ e i)
    rcases he' with rfl | ⟨c, -, rfl⟩
    · exact Keeps.refl _
    · exact Keeps.push _ _
  · simp only [ExPost.post_bind]
    refine ExPost.mono (fun env₂ h₂ => ?_) (foldlM_installs _ (·.name)
      (fun ci => reservedBasisNames.contains ci.name = false) _ env fun e ci _ =>
        checkIndMember_installs _ _ e ci)
    refine ExPost.mono (fun env₃ h₃ ci hci => ?_)
      (checkIndRecs_installs (mode := mode) (ops := ops) _ env₂ _)
    cases ci with
    | recInfo cv mI rP rules => exact h₃.2 _ (List.mem_filter.mpr ⟨hci, rfl⟩)
    | _ =>
      obtain ⟨i, u⟩ := h₂.2 _ (List.mem_filter.mpr ⟨hci, rfl⟩)
      exact ⟨h₃.1.installed i, u⟩

/-! ## Inductive blocks: the native route -/

/-- A recognised block's constructors and recursor are all of its tail. -/
theorem sumSplit_cover :
    ∀ {l : List (Ix.Kernel.ConstantInfo md)} {cs : List (Ix.Kernel.ConstantVal md × Nat × Nat)}
      {cvR : Ix.Kernel.ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)},
      sumSplit l = some (cs, cvR, mI, rP, rules) →
      ∀ ci ∈ l, ci = .recInfo cvR mI rP rules ∨ ∃ c ∈ cs, ci = .ctorInfo c.1 c.2.1 c.2.2
  | [.recInfo _ _ _ _], _, _, _, _, _, h => by
    simp only [sumSplit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    intro ci hci
    exact .inl (List.mem_singleton.mp hci)
  | .ctorInfo cvC nP nF :: rest, cs, cvR, mI, rP, rules, h => by
    simp only [sumSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs', q⟩, hq, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ih := sumSplit_cover hq
    intro ci hci
    rcases List.mem_cons.mp hci with rfl | hci
    · exact .inr ⟨_, List.mem_cons_self, rfl⟩
    · rcases ih ci hci with h | ⟨c, hc, h⟩
      · exact .inl h
      · exact .inr ⟨c, List.mem_cons_of_mem _ hc, h⟩
  | [], _, _, _, _, _, h => nomatch h
  | .recInfo _ _ _ _ :: _ :: _, _, _, _, _, _, h => nomatch h
  | .axiomInfo _ :: _, _, _, _, _, _, h => nomatch h
  | .defnInfo _ _ _ :: _, _, _, _, _, _, h => nomatch h
  | .thmInfo _ _ :: _, _, _, _, _, _, h => nomatch h
  | .indInfo _ _ :: _, _, _, _, _, _, h => nomatch h
  | .projInfo _ :: _, _, _, _, _, _, h => nomatch h

/-- **A block the native route recognises** is its former, its constructors and its
recursor, none under a reserved name. -/
theorem nativeShape?_members {nP : Nat} {block : List (Ix.Kernel.ConstantInfo md)}
    {s : InductiveShape md} (hs : nativeShape? nP block = some s) :
    ∀ ci ∈ block, (ci.name = s.cvT.name ∨ (∃ c ∈ s.ctors, ci.name = c.1.name) ∨ ci.name = s.cvR.name) ∧
      reservedBasisNames.contains ci.name = false := by
  unfold nativeShape? at hs
  split at hs
  · rename_i cvT caps rest
    split at hs
    · rename_i cs cvR mI rP rules hsplit
      have cover := sumSplit_cover hsplit
      dsimp only at hs
      split at hs
      · cases hs
      · split at hs
        · rename_i hcond
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hcond
          obtain ⟨⟨hT, hR⟩, hcs⟩ := hcond
          have key : s.cvT = cvT ∧ s.cvR = cvR ∧ s.ctors = cs.map fun c => (c.1, c.2.2) := by
            split at hs <;> (simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl, rfl⟩)
          obtain ⟨k1, k2, k3⟩ := key
          intro ci hci
          rcases List.mem_cons.mp hci with rfl | hci
          · exact ⟨.inl (by rw [k1]; rfl), hT⟩
          · rcases cover ci hci with rfl | ⟨c, hc, rfl⟩
            · exact ⟨.inr (.inr (by rw [k2]; rfl)), hR⟩
            · refine ⟨.inr (.inl ⟨(c.1, c.2.2), by rw [k3]; exact List.mem_map_of_mem hc, rfl⟩), ?_⟩
              have := hcs c hc
              exact this.2
        · cases hs
    · cases hs
  · cases hs

theorem nativeParts?_members {nP : Nat} {block : List (Ix.Kernel.ConstantInfo md)} {p : NativeParts md}
    (h : nativeParts? nP block = some p) :
    ∀ ci ∈ block, (ci.name = p.cvT.name ∨ (∃ c ∈ p.ctors, ci.name = c.1.name) ∨ ci.name = p.cvR.name) ∧
      reservedBasisNames.contains ci.name = false := by
  simp only [nativeParts?, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  exact nativeShape?_members hs

/-- The constructors' cons installs each of them. -/
theorem consSumCtors_installs (nP : Nat) :
    ∀ (cs : List (Ix.Kernel.ConstantVal md × Nat)) (env : Env md),
      Keeps env (consSumCtors nP cs env) ∧ ∀ c ∈ cs, Installed (consSumCtors nP cs env) c.1.name
  | [], env => ⟨Keeps.refl _, fun _ h => nomatch h⟩
  | c :: cs, env => by
    obtain ⟨keep, inst⟩ := consSumCtors_installs nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩
    refine ⟨(Keeps.push _ _).trans keep, fun c' hc' => ?_⟩
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact keep.installed (installed_push _ _)
    · exact inst c' hc'

/-- The native pass installs the former. -/
theorem checkNativePass_installs (env : Env md) (p₀ : NativeParts md) (isRec : Bool) :
    ExPost (checkNativePass ops env p₀ isRec) (fun r => Installed r.1.env₁ p₀.cvT.name) := by
  unfold checkNativePass
  rw [ExPost.post_bind]
  refine ExPost.mono (fun r hr => ?_) (checkSumInd_post env p₀.toInductiveShape _)
  obtain ⟨env₁, cvTa, p₁⟩ := r
  obtain ⟨h₁, h₂, -⟩ := hr
  dsimp only at h₁ h₂ ⊢
  rw [ExPost.post_bind]
  refine ExPost.of_forall fun _ => ?_
  rw [ExPost.post_bind]
  refine ExPost.of_forall fun kinds => ?_
  simp only [ExPost.post_pure]
  rw [h₁]
  exact ⟨_, List.mem_cons_self, h₂⟩

/-- The native install after the pass installs the constructors and the recursor. -/
theorem checkNativeTail_installs (env : Env md) (q : NativePass md (Env md)) :
    ExPost (checkNativeTail ops env q) (fun e =>
      Keeps q.env₁ e ∧ (∀ c ∈ q.ctorsA, Installed e c.1.name) ∧ Installed e q.p.cvR.name) := by
  unfold checkNativeTail
  simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, true_and, imp_true_iff]
  intro _
  refine ExPost.of_forall fun _ => ExPost.of_forall fun _ =>
    ⟨fun _ => ⟨fun _ => ?_, trivial⟩, trivial⟩
  refine ExPost.mono (fun r hr => ?_) (checkNativeRec_post _ _ _ _)
  refine ExPost.mono (fun e he => ?_) (checkNativeTable_post (Q := fun _ => True) _ _ _ _ trivial)
  obtain ⟨keepC, instC⟩ := consSumCtors_installs q.p.nP q.ctorsA q.env₁
  have keepE := (Keeps.push _ _).trans (Grows.keeps he)
  exact ⟨keepC.trans keepE, fun c hc => keepE.installed (instC c hc),
    (Grows.keeps he).installed ⟨_, List.mem_cons_self, hr.1⟩⟩

/-- **The native route installs the former, the constructors and the recursor.** -/
theorem checkNative_installs (env : Env md) (p₀ : NativeParts md) :
    ExPost (checkNative ops env p₀) (fun e =>
      Installed e p₀.cvT.name ∧ (∀ c ∈ p₀.ctors, Installed e c.1.name) ∧ Installed e p₀.cvR.name) := by
  have tail : ∀ q : NativePass md (Env md),
      (Installed q.env₁ p₀.cvT.name ∧ q.p.cvR = p₀.cvR ∧
        q.ctorsA.map (·.1.name) = p₀.ctors.map (·.1.name)) →
      ExPost (checkNativeTail ops env q) (fun e =>
        Installed e p₀.cvT.name ∧ (∀ c ∈ p₀.ctors, Installed e c.1.name) ∧ Installed e p₀.cvR.name) := by
    intro q ⟨hT, hR, hC⟩
    refine ExPost.mono (fun e he => ⟨he.1.installed hT, fun c hc => ?_, hR ▸ he.2.2⟩)
      (checkNativeTail_installs env q)
    have hm : c.1.name ∈ q.ctorsA.map (·.1.name) := hC ▸ List.mem_map_of_mem hc
    obtain ⟨c', hc', he'⟩ := List.mem_map.mp hm
    rw [← he']
    exact he.2.1 c' hc'
  have pass : ∀ isRec, ExPost (checkNativePass ops env p₀ isRec) (fun r =>
      Installed r.1.env₁ p₀.cvT.name ∧ r.1.p.cvR = p₀.cvR ∧
        r.1.ctorsA.map (·.1.name) = p₀.ctors.map (·.1.name)) := fun isRec r hr =>
    ⟨checkNativePass_installs env p₀ isRec r hr,
      (checkNativePass_post (Q := fun _ => True) env p₀ isRec trivial r hr).2.2.1,
      (checkNativePass_post (Q := fun _ => True) env p₀ isRec trivial r hr).2.2.2.2.1⟩
  unfold checkNative
  simp only [ExPost.post_bind, ExPost.post_ite, ExPost.post_throw, imp_true_iff]
  refine ⟨fun _ => ExPost.mono (fun r hr => ⟨fun _ => tail r.1 hr, fun _ => ?_⟩) (pass _), trivial⟩
  exact ExPost.mono (fun r hr => ⟨fun _ => tail r.1 hr, trivial⟩) (pass _)

/-! ## Inductive declarations -/

theorem quotName_reserved : reservedBasisNames.contains (quotName : Key md) = true := by
  cases md <;> decide

/-- No pinned inductive block holds the quotient type's name. -/
theorem pin_noQuot {block : List (Ix.Kernel.ConstantInfo md)} {kind : BasisKind}
    (h : basisPinHit block = some kind) : (quotName : Key md) ∉ (kind.decls (md := md)).map (·.name) := by
  unfold basisPinHit at h
  have hmem := List.mem_of_find?_eq_some (Option.filter_eq_some_iff.mp h).1
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> cases md <;> decide

/-- **An accepted inductive declaration installs every member**, and none is the
quotient type's name. -/
theorem checkDecl_installs_ind (ev : Evidences md) (env : Env md)
    (block : List (Ix.Kernel.ConstantInfo md)) (nP : Nat) :
    ExPost (checkDecl mode ops ev env (.indDecl block nP))
      (fun e => InstallsAll e (.indDecl block nP) ∧ (quotName : Key md) ∉ block.map (·.name)) := by
  unfold checkDecl
  rw [ExPost.post_bind]
  refine ExPost.of_forall fun _ => ?_
  split
  · rename_i kind hkind
    refine ExPost.mono (fun e he => ⟨fun k hk => ?_, ?_⟩) (fun e he => checkBasisDecl_installs he)
    · have hk' : k ∈ kind.declsA.map (·.name) := by
        rw [declsA_names, ← basisPinHit_names hkind]
        exact hk
      exact he.2 k hk'
    · rw [basisPinHit_names hkind]
      exact pin_noQuot hkind
  · simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
    intro _
    split
    · rename_i p hp
      refine ExPost.mono (fun e he => ⟨fun k hk => ?_, fun hq => ?_⟩) (checkNative_installs env p)
      · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
        rcases (nativeParts?_members hp ci hci).1 with h | ⟨c, hc, h⟩ | h
        · rw [h]; exact he.1
        · rw [h]; exact he.2.1 c hc
        · rw [h]; exact he.2.2
      · obtain ⟨ci, hci, hn⟩ := List.mem_map.mp hq
        have hu := (nativeParts?_members hp ci hci).2
        rw [hn, quotName_reserved] at hu
        cases hu
    · refine ExPost.mono (fun e he => ⟨fun k hk => ?_, fun hq => ?_⟩) (checkModeled_installs env block)
      · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
        exact (he ci hci).1
      · obtain ⟨ci, hci, hn⟩ := List.mem_map.mp hq
        have hu := (he ci hci).2
        rw [hn, quotName_reserved] at hu
        cases hu

/-- **An accepted declaration installs the names it installs itself.** -/
theorem checkDecl_installs (ev : Evidences md) (env : Env md) (d : Declaration md) :
    ExPost (checkDecl mode ops ev env d) (fun e => InstallsAll e d) := by
  cases d with
  | indDecl block nP => exact ExPost.mono (fun e he => he.1) (checkDecl_installs_ind ev env block nP)
  | _ => exact checkDecl_installs_value ev env _ (fun _ _ h => nomatch h)

/-! ## The quotient records -/

/-- A record that matches the pinned quotient block is named as the pin's slot. -/
theorem quotPinHit_name {k : Ix.Kernel.QuotKind} {cv : Ix.Kernel.ConstantVal md} (h : quotPinHit k cv = true) :
    cv.name = ((BasisKind.quotK.decls (md := md)).getD k.slot (.axiomInfo default)).toConstantVal.name := by
  unfold quotPinHit ConstantVal.canonEq at h
  have hc := (ConstantVal.canonEqFast_iff _ _).mpr (of_decide_eq_true h)
  unfold ConstantVal.canonEqFast at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact hc.1.1

/-- The pinned quotient block's slots are named as its annotated pin's constants. -/
theorem quotSlot_name (k : Ix.Kernel.QuotKind) :
    ((BasisKind.quotK.decls (md := md)).getD k.slot (.axiomInfo default)).toConstantVal.name ∈
      (BasisKind.quotK.declsA (md := md)).map (·.name) := by
  cases k <;> cases md <;> decide

/-- Only the quotient type's slot is named as the quotient type. -/
theorem quotSlot_type {k : Ix.Kernel.QuotKind}
    (h : ((BasisKind.quotK.decls (md := md)).getD k.slot (.axiomInfo default)).toConstantVal.name =
      quotName) : k = .type := by
  cases k <;> cases md <;> first | rfl | (revert h; decide)

/-- **An accepted declaration that declares the quotient type's name is the quotient
type's record.** -/
theorem checkDecl_declares_quot (ev : Evidences md) (env : Env md) (d : Declaration md)
    (hq : (quotName : Key md) ∈ d.names) :
    ExPost (checkDecl mode ops ev env d) (fun _ => ∃ cv, d = .quotDecl .type cv) := by
  have reserved : ∀ cv : Ix.Kernel.ConstantVal md, cv.name = quotName →
      ExPost (checkConstantVal ops env cv) (fun _ => False) := fun cv hn =>
    ExPost.mono (fun _ h => by rw [hn, quotName_reserved] at h; cases h)
      (checkConstantVal_unreserved env cv)
  cases d with
  | defnDecl cv value hint =>
    have hn : cv.name = quotName := (List.mem_singleton.mp hq).symm
    unfold checkDecl
    rw [ExPost.post_bind]
    exact ExPost.mono (fun _ h => h.elim) (reserved cv hn)
  | thmDecl cv value =>
    have hn : cv.name = quotName := (List.mem_singleton.mp hq).symm
    unfold checkDecl
    rw [ExPost.post_bind]
    exact ExPost.mono (fun _ h => h.elim) (reserved cv hn)
  | opaqueDecl cv value =>
    have hn : cv.name = quotName := (List.mem_singleton.mp hq).symm
    unfold checkDecl
    rw [ExPost.post_bind]
    exact ExPost.mono (fun _ h => h.elim) (reserved cv hn)
  | axiomDecl cv =>
    have hn : cv.name = quotName := (List.mem_singleton.mp hq).symm
    have hs : ¬ cv.name = quotSoundName := by rw [hn]; cases md <;> decide
    unfold checkDecl
    simp only [hs, ↓reduceIte]
    rw [ExPost.post_bind]
    exact ExPost.mono (fun _ h => h.elim) (reserved cv hn)
  | basisDecl kind => cases hq
  | quotDecl k cv =>
    have hn : cv.name = quotName := (List.mem_singleton.mp hq).symm
    unfold checkDecl
    simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
    intro hpin
    have hk := quotSlot_type ((quotPinHit_name hpin).symm.trans hn)
    subst hk
    exact ExPost.of_forall fun _ => ⟨cv, rfl⟩
  | indDecl block nP =>
    exact ExPost.mono (fun _ he => absurd hq he.2) (checkDecl_installs_ind ev env block nP)

/-- An accepted quotient record is named as one of the pinned quotient constants. -/
theorem checkDecl_quot_name (ev : Evidences md) (env : Env md) (k : Ix.Kernel.QuotKind)
    (cv : Ix.Kernel.ConstantVal md) :
    ExPost (checkDecl mode ops ev env (.quotDecl k cv))
      (fun _ => cv.name ∈ (BasisKind.quotK.declsA (md := md)).map (·.name)) := by
  unfold checkDecl
  simp only [ExPost.post_ite, ExPost.post_throw, imp_true_iff, and_true]
  intro hpin
  rw [quotPinHit_name hpin]
  exact ExPost.of_forall fun _ => quotSlot_name k

/-! ## Reference accepts -/

/-- Every declaration of an accepted run was accepted at some environment of the run,
whose result the run's end keeps. -/
theorem foldlM_steps (ev : Evidences md) :
    ∀ (ds : List (Declaration md)) (env e : Env md),
      ds.foldlM (checkDecl mode ops ev) env = .ok e →
      ∀ d ∈ ds, ∃ e₀ e₁, checkDecl mode ops ev e₀ d = .ok e₁ ∧ Keeps e₁ e
  | [], _, _, _, d, hd => nomatch hd
  | d :: ds, env, e, h, d', hd' => by
    rw [List.foldlM_cons] at h
    obtain ⟨e₁, h₁, rest⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact ⟨env, e₁, h₁, Grows.keeps (foldlM_checkDecl_post mode ops ev ds e₁ e rest)⟩
    · exact foldlM_steps ev ds e₁ e rest d' hd'

/-- **A reference accept installs every name each of its declarations installs itself.** -/
theorem accepts_installs {μ : CheckMode} {ev : Evidences md} {ds : List (Declaration md)}
    {env : Env md} (h : Cached.AcceptsRef μ ev ds env) {d : Declaration md} (hd : d ∈ ds) :
    InstallsAll env d := by
  obtain ⟨F, h⟩ := h
  obtain ⟨e₀, e₁, step, keep⟩ := foldlM_steps (mode := μ) (ops := fueledOps μ F) ev ds _ _ h d hd
  exact fun k hk => keep.installed (checkDecl_installs ev e₀ d e₁ step k hk)

/-- **A reference accept with a record declaring the quotient type installs the whole
pinned quotient block.** -/
theorem accepts_quot {μ : CheckMode} {ev : Evidences md} {ds : List (Declaration md)}
    {env : Env md} (h : Cached.AcceptsRef μ ev ds env) {d₀ : Declaration md} (hd : d₀ ∈ ds)
    (hq : (quotName : Key md) ∈ d₀.names) :
    ∀ k ∈ (BasisKind.quotK.declsA (md := md)).map (·.name), Installed env k := by
  obtain ⟨F, run⟩ := h
  obtain ⟨e₀, e₁, step, -⟩ := foldlM_steps (mode := μ) (ops := fueledOps μ F) ev ds _ _ run d₀ hd
  obtain ⟨cv, rfl⟩ := checkDecl_declares_quot ev e₀ d₀ hq e₁ step
  exact accepts_installs ⟨F, run⟩ hd

/-- **A reference accept installs every name its declarations declare**, `sorryAx`
aside, when one of its records declares the quotient type (the prepared stream's
front always has one). -/
theorem accepts_names {μ : CheckMode} {ev : Evidences md} {ds : List (Declaration md)}
    {env : Env md} (h : Cached.AcceptsRef μ ev ds env)
    (hquot : ∃ d₀ ∈ ds, (quotName : Key md) ∈ d₀.names)
    {d : Declaration md} (hd : d ∈ ds) {k : Key md} (hk : k ∈ d.names) (hs : k ≠ sorryAxName) :
    Installed env k := by
  obtain ⟨d₀, hd₀, hq⟩ := hquot
  have quot := accepts_quot h hd₀ hq
  have own := accepts_installs h hd
  cases d with
  | defnDecl cv value hint => exact own k hk
  | thmDecl cv value => exact own k hk
  | opaqueDecl cv value => exact own k hk
  | axiomDecl cv =>
    have hn : k = cv.name := List.mem_singleton.mp hk
    subst hn
    by_cases hsnd : cv.name = quotSoundName
    · rw [hsnd]
      exact quot _ (by cases md <;> decide)
    · refine own cv.name ?_
      simp [selfInstalls, hsnd, hs]
  | basisDecl kind => cases hk
  | quotDecl qk cv =>
    have hn : k = cv.name := List.mem_singleton.mp hk
    subst hn
    obtain ⟨F, run⟩ := h
    obtain ⟨e₀, e₁, step, -⟩ := foldlM_steps (mode := μ) (ops := fueledOps μ F) ev ds _ _ run _ hd
    exact quot _ (checkDecl_quot_name ev e₀ qk cv e₁ step)
  | indDecl block nP => exact own k hk

/-! ## The prepared stream's front

The committed prelude passed its shape check (`Reader.checkPreludeShape`): its
declarations name the pinned prelude roles, one of them the quotient type. The
prepared stream's front holds, for each prelude declaration, the stream's own record
declaring its name or the prelude's declaration itself (`frontSpec_cover`), so some
record of every prepared stream declares the quotient type (`prepared_quot`). -/

theorem pickSpec_declares {n : Option (Key md)} :
    ∀ {l : List (Declaration md)} {d : Declaration md}, (Frontend.pickSpec n l).1 = some d →
      Frontend.declares n d = true
  | [], d, h => by simp [Frontend.pickSpec] at h
  | x :: xs, d, h => by
    simp only [Frontend.pickSpec] at h
    split at h
    · rename_i hx
      cases h
      exact hx
    · exact pickSpec_declares h

theorem frontSpec_cover :
    ∀ (ps ds : List (Declaration md)), ∀ p ∈ ps, ∃ d ∈ (Frontend.frontSpec ps ds).1,
      d = p ∨ Frontend.declares (Frontend.preludeKey p) d = true
  | [], _, p, hp => nomatch hp
  | p :: ps, ds, p', hp' => by
    simp only [Frontend.frontSpec]
    rcases List.mem_cons.mp hp' with rfl | hp'
    · cases hm : (Frontend.pickSpec (Frontend.preludeKey p') ds).1 with
      | none => exact ⟨p', by simp, .inl rfl⟩
      | some d => exact ⟨d, by simp, .inr (pickSpec_declares hm)⟩
    · obtain ⟨d, hd, h⟩ := frontSpec_cover ps _ p' hp'
      exact ⟨d, List.mem_cons_of_mem _ hd, h⟩

/-- The committed prelude's declarations name the pinned prelude roles. -/
theorem builtinPrelude_shape {pre : Ix.Kernel.Reader.Prelude md}
    (h : Ix.Kernel.Reader.builtinPrelude = .ok pre) :
    pre.ix.decls.toList.map (·.names) = preludeShape.map (·.map (Key.role (md := md))) := by
  unfold Ix.Kernel.Reader.builtinPrelude at h
  obtain ⟨t, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  unfold Ix.Kernel.Reader.preludeFor at h
  obtain ⟨pre', -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  obtain ⟨u, hshape, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  obtain ⟨u', -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  unfold Ix.Kernel.Reader.checkPreludeShape at hshape
  dsimp only at hshape
  split at hshape
  · rename_i heq
    exact beq_iff_eq.mp heq
  · cases hshape

/-- **Some record of every prepared stream declares the quotient type.** -/
theorem prepared_quot {pre : Ix.Kernel.Reader.Prelude md}
    (h : Ix.Kernel.Reader.builtinPrelude = .ok pre) (decls : Array (Declaration md)) :
    ∃ d₀ ∈ (Frontend.preparePrelude pre.ix decls).toList, (quotName : Key md) ∈ d₀.names := by
  have hmem : [Key.role (md := md) .quot] ∈ pre.ix.decls.toList.map (·.names) := by
    rw [builtinPrelude_shape h]
    exact List.mem_map.mpr ⟨[.quot], by decide, rfl⟩
  obtain ⟨p₀, hp₀, hn⟩ := List.mem_map.mp hmem
  obtain ⟨d, hd, hdp⟩ := frontSpec_cover pre.ix.decls.toList decls.toList p₀ hp₀
  refine ⟨d, ?_, ?_⟩
  · rw [Frontend.preparePrelude_front, Array.toList_append, (Frontend.frontOf_toList _ _ _).1]
    exact List.mem_append_left _ (List.mem_append_right _ hd)
  · rcases hdp with rfl | hdp
    · rw [hn]
      exact List.mem_singleton_self _
    · unfold Frontend.declares Frontend.preludeKey at hdp
      rw [hn] at hdp
      simpa using hdp

/-- info: 'Ix.Cert.SourceInstalls.accepts_names' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms accepts_names

/-- info: 'Ix.Cert.SourceInstalls.prepared_quot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prepared_quot

end Ix.Cert.SourceInstalls
