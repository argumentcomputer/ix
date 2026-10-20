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

/-- The empty environments are related. -/
theorem EnvRel.empty (hf : InjOn f P) : EnvRel P f (Env.empty : Env md) (Env.empty : Env md') where
  inj := hf
  all _ h := nomatch h
  eq := rfl

/-- **The pure fold at a renamed input.** -/
theorem checkDeclsPure_sim (mode : CheckMode) {ops : (CheckerOps md) (CheckM md)}
    {ops' : (CheckerOps md') (CheckM md')} (hops : OpsSim P f ops ops') (hf : InjOn f P)
    {ev : Evidences md} (hev : ev.Good P) {ds : List (Declaration md)}
    (hds : ∀ d ∈ ds, d.Good P) :
    SimR (EnvRel P f) (checkDeclsPure mode ops ev ds)
      (checkDeclsPure mode ops' (ev.mapKeys f) (ds.map (Declaration.mapKeys f))) := by
  unfold checkDeclsPure
  have hstep := fun (a : Env md) (a' : Env md') (d : Declaration md) (ha : EnvRel P f a a')
    (hd : d.Good P) => checkDecl_sim mode hops hev ha hd
  exact SimR.foldlM_map hstep ds hds (EnvRel.empty hf)

/-- **Reference acceptance under renaming**: an accepted run, its keys renamed
by `Key.map f` with `f` injective on the ids it names, is accepted, at the
same fuel, installing an environment related to the original by `EnvRel`
(every lookup at a renamed key answers the renamed constant). -/
theorem Cached.AcceptsRef.rename (μ : CheckMode) (hf : InjOn f P) {ev : Evidences md}
    (hev : ev.Good P) {ds : List (Declaration md)} (hds : ∀ d ∈ ds, d.Good P) {env : Env md}
    (h : Cached.AcceptsRef μ ev ds env) :
    ∃ env', Cached.AcceptsRef μ (ev.mapKeys f) (ds.map (Declaration.mapKeys f)) env' ∧
      EnvRel P f env env' := by
  rw [Cached.AcceptsRef.iff] at h
  obtain ⟨F, hF⟩ := h
  obtain ⟨env', h', hrel⟩ := checkDeclsPure_sim μ (fueledOps_sim (P := P) (f := f) μ F) hf hev hds
    env hF
  exact ⟨env', Cached.AcceptsRef.iff.mpr ⟨F, h'⟩, hrel⟩

end Ix.Kernel
