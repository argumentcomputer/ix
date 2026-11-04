module

public import IxC.Kernel.Verify.Rename.Decl5
public import IxC.Kernel.Verify.Cached.Reference

@[expose] public section

/-!
# The renaming walk: the fold and reference acceptance (step 7.3, chunk (iv))

The pure fold at a renamed input (`checkDeclsPure_sim`) and **reference
acceptance under renaming** (`AcceptsRef.rename`): renaming an accepted run's
keys by `Key.map f`, `f` injective on the ids its declarations and evidence
name, gives an accepted run whose environment answers every lookup at a
renamed key with the renamed constant (`EnvRel`), at the same fuel.
-/

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}

/-- The empty environments are related, at any scope allowing the prelude and
any link they satisfy. -/
theorem EnvRelG.empty {P : KeyScope md} {L : Env md → Env md' → Prop} (hf : InjOn f P)
    (hpre : P.Pre) (hL : L (Env.empty : Env md) (Env.empty : Env md')) :
    EnvRelG P f L (Env.empty : Env md) (Env.empty : Env md') where
  inj := hf
  find _ _ := rfl
  good _ _ _ h := by cases h
  absent _ _ := rfl
  pre := hpre
  link := hL

/-- The empty environments are related. -/
theorem EnvRel.empty (hf : InjOn f P) : EnvRel P f (Env.empty : Env md) (Env.empty : Env md') where
  inj := hf
  all _ h := nomatch h
  eq := rfl

/-- **The pure fold at a renamed input**, at any scope and link: every
declaration installs no operation, or the scope allows every role. -/
theorem checkDeclsPure_simG (mode : CheckMode) {P : KeyScope md} {L : Env md → Env md' → Prop}
    [LinkPush P f L] {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}
    (hops : OpsSim P f L ops ops') {ev : Evidences md} (hev : ev.Good P)
    {ds : List (Declaration md)} (hds : ∀ d ∈ ds, d.Good P) (hop : P.All ∨ ∀ d ∈ ds, d.NoOp)
    {env₀ : Env md} {env₀' : Env md'} (h₀ : EnvRelG P f L env₀ env₀') :
    SimR (EnvRelG P f L) (ds.foldlM (checkDecl mode ops ev) env₀)
      ((ds.map (Declaration.mapKeys f)).foldlM (checkDecl mode ops' (ev.mapKeys f)) env₀') := by
  have hstep := fun (a : Env md) (a' : Env md') (d : Declaration md) (ha : EnvRelG P f L a a')
    (hd : d.Good P ∧ (d.NoOp ∨ P.All)) => checkDecl_sim mode hops hev ha hd.1 hd.2
  exact SimR.foldlM_map hstep ds
    (fun d hd => ⟨hds d hd, hop.elim Or.inr (fun h => Or.inl (h d hd))⟩) h₀

/-- **The pure fold at a renamed input.** -/
theorem checkDeclsPure_sim (mode : CheckMode) {ops : (CheckerOps md) (CheckM md)}
    {ops' : (CheckerOps md') (CheckM md')}
    (hops : OpsSim (KeyScope.ofId P) f (LitLink (KeyScope.ofId P) f) ops ops')
    (hf : InjOn f P) {ev : Evidences md} (hev : ev.Good (KeyScope.ofId P))
    {ds : List (Declaration md)} (hds : ∀ d ∈ ds, d.Good (KeyScope.ofId P)) :
    SimR (EnvRel P f) (checkDeclsPure mode ops ev ds)
      (checkDeclsPure mode ops' (ev.mapKeys f) (ds.map (Declaration.mapKeys f))) := by
  unfold checkDeclsPure
  have h := checkDeclsPure_simG mode hops hev hds (Or.inl (KeyScope.ofId_all P))
    (EnvRel.empty hf).toG
  intro a ha
  obtain ⟨a', h', hrel⟩ := h a ha
  exact ⟨a', h', hrel.toLit⟩

/-- **Reference acceptance under renaming**: an accepted run, its keys renamed
by `Key.map f` with `f` injective on the ids it names, is accepted, at the
same fuel, installing an environment related to the original by `EnvRel`
(every lookup at a renamed key answers the renamed constant). -/
theorem Cached.AcceptsRef.rename (μ : CheckMode) (hf : InjOn f P) {ev : Evidences md}
    (hev : ev.Good (KeyScope.ofId P)) {ds : List (Declaration md)}
    (hds : ∀ d ∈ ds, d.Good (KeyScope.ofId P)) {env : Env md}
    (h : Cached.AcceptsRef μ ev ds env) :
    ∃ env', Cached.AcceptsRef μ (ev.mapKeys f) (ds.map (Declaration.mapKeys f)) env' ∧
      EnvRel P f env env' := by
  rw [Cached.AcceptsRef.iff] at h
  obtain ⟨F, hF⟩ := h
  obtain ⟨env', h', hrel⟩ :=
    checkDeclsPure_sim μ
      (fueledOps_sim (P := KeyScope.ofId P) (f := f) (L := LitLink (KeyScope.ofId P) f) μ F)
      hf hev hds env hF
  exact ⟨env', Cached.AcceptsRef.iff.mpr ⟨F, h'⟩, hrel⟩

end Ix.Kernel
