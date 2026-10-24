import IxC.Kernel.Verify.Cached.Reference

/-! # Evidence only gates the checker (Route A, B6a)

The role table's evidence enters IxC's checker at two gates of
`Ix.Kernel.checkDecl`, both on a definition: `evidenceDefeqOk` for a
structural `Nat` operation and `checkDivModEvidence` for a well-founded one.
Each either throws or passes; neither changes what is installed. So a run
that succeeds with evidence `ev` succeeds with any `ev'` that passes every
gate `ev` passes (`Covers`), and installs the same environment
(`checkDecl_covers`, `checkDeclsPure_covers`, `AcceptsRef.covers`). Source
mode and Ixon mode check under different evidence (the certificate theorems
of the checked environment against the role table's synthesized records);
this is the step that moves an acceptance from one to the other, once the
other's gates are shown to pass (B6b). -/

namespace Ix.Cert.Evidence

open Ix.Kernel

variable {md : Mode}

/-- `ev'` passes every evidence gate that `ev` passes. -/
structure Covers (ops : (CheckerOps md) (CheckM md)) (ev ev' : Evidences md) : Prop where
  defeq : ∀ c, evidenceDefeqOk ev c = true → evidenceDefeqOk ev' c = true
  divMod : ∀ env env2 c, checkDivModEvidence ops ev env env2 c = .ok () →
    checkDivModEvidence ops ev' env env2 c = .ok ()

/-- The structural and the well-founded `Nat` operations are different names. -/
theorem natNames_disjoint (c : Key md) :
    ¬ (natOpNames.contains c = true ∧ natDivModNames.contains c = true) := by
  rintro ⟨h1, h2⟩
  simp only [List.contains_iff_mem] at h1 h2
  simp only [natOpNames, natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> subst h1 <;> simp_all

/-- **One declaration**: a check that succeeds under `ev` succeeds under a
covering `ev'`, with the same environment. -/
theorem checkDecl_covers {mode : CheckMode} {ops : (CheckerOps md) (CheckM md)}
    {ev ev' : Evidences md} (h : Covers ops ev ev') {env env' : Env md} {d : Declaration md}
    (hd : checkDecl mode ops ev env d = .ok env') : checkDecl mode ops ev' env d = .ok env' := by
  cases d with
  | defnDecl cv value hint =>
    simp only [checkDecl] at hd ⊢
    cases h1 : checkConstantVal ops env cv with
    | error e => rw [h1] at hd; cases hd
    | ok cv' =>
      rw [h1] at hd
      simp only [bind, Except.bind] at hd ⊢
      cases h2 : checkDefnVal ops env cv' value hint with
      | error e => rw [h2] at hd; cases hd
      | ok env2 =>
        rw [h2] at hd
        simp only at hd ⊢
        have disjoint := natNames_disjoint (md := md) cv'.name
        by_cases hn : natOpNames.contains cv'.name = true
        · have hm : natDivModNames.contains cv'.name = false := by
            cases e : natDivModNames.contains cv'.name
            · rfl
            · exact absurd ⟨hn, e⟩ disjoint
          have hev : evidenceDefeqOk ev cv'.name = true := by
            cases e : evidenceDefeqOk ev cv'.name
            · simp only [hn, hm, e] at hd; cases hd
            · rfl
          simpa only [hn, hm, hev, h.defeq _ hev, ↓reduceIte, Bool.false_eq_true] using hd
        · by_cases hm : natDivModNames.contains cv'.name = true
          · cases e : checkDivModEvidence ops ev env env2 cv'.name with
            | error err => simp only [hn, hm, e] at hd; cases hd
            | ok u =>
              cases u
              simpa only [hn, hm, e, h.divMod _ _ _ e, ↓reduceIte, Bool.false_eq_true] using hd
          · simpa only [hn, hm, ↓reduceIte, Bool.false_eq_true] using hd
  | _ => exact hd

/-- The fold over a list of declarations, from any environment. -/
theorem foldlM_covers {mode : CheckMode} {ops : (CheckerOps md) (CheckM md)}
    {ev ev' : Evidences md} (h : Covers ops ev ev') :
    ∀ (ds : List (Declaration md)) (env₀ env : Env md),
      ds.foldlM (checkDecl mode ops ev) env₀ = .ok env →
        ds.foldlM (checkDecl mode ops ev') env₀ = .ok env
  | [], _, _, hd => hd
  | d :: ds, env₀, env, hd => by
    simp only [List.foldlM_cons, bind, Except.bind] at hd ⊢
    cases e : checkDecl mode ops ev env₀ d with
    | error err => rw [e] at hd; cases hd
    | ok env₁ =>
      rw [e] at hd
      rw [checkDecl_covers h e]
      exact foldlM_covers h ds env₁ env hd

/-- **The pure fold**: an accept under `ev` is an accept under a covering
`ev'`, of the same environment. -/
theorem checkDeclsPure_covers {mode : CheckMode} {ops : (CheckerOps md) (CheckM md)}
    {ev ev' : Evidences md} (h : Covers ops ev ev') {ds : List (Declaration md)} {env : Env md}
    (hd : checkDeclsPure mode ops ev ds = .ok env) : checkDeclsPure mode ops ev' ds = .ok env :=
  foldlM_covers h ds _ _ hd

/-- **Reference acceptance** (IxC step 7.1) moves to any evidence that covers
`ev` at every fuel. -/
theorem acceptsRef_covers {μ : CheckMode} {ev ev' : Evidences md}
    (h : ∀ F, Covers (fueledOps μ F) ev ev') {ds : List (Declaration md)} {env : Env md}
    (hd : Cached.AcceptsRef μ ev ds env) : Cached.AcceptsRef μ ev' ds env := by
  obtain ⟨F, hF⟩ := hd
  exact ⟨F, checkDeclsPure_covers (h F) hF⟩

end Ix.Cert.Evidence
