import Ix.CompileCert.Opt.O1

/-!
# M7 L3-def: O6, an image that is an Ix recursor applied to a selection of its arguments
(`Ix/Compile/Pass/Opt/O6.lean`)

The docstring's *Faithfulness (definitional)*: "`rec`: the output is `img(r)`'s body at the
arguments: one δ (img) and `n` β-steps. The arguments `σ` and `σ′` drop are not used by the body
…: β discards them. `recOn`: as O1's `recOn` …, with the unused arguments discarded by β." The
same two conversions as O1 (`rec_sel_conv`, `recOn_sel_conv`), on any selection shape:

* `O6_some`, **`O6_faithful`** (laws `RecLaw`, `RecOnLaw`, `IxRecOnLaw`), `O6.Side`, `O6_side`.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Pass.Opt

/-- What a firing of O6 established. -/
theorem O6_some {env : OptEnv} {o : Occ} {e : Expr} (h : O6.apply env o = some e) :
    ∃ k r b s ls ms', classify o.head = some (k, r) ∧ env.blockOf o.head = some b ∧
      b.shapes.get? r = some s ∧ s.isSelection = true ∧
      standardTelescope env s k o.head = some s.arity ∧ s.arity ≤ o.args.size ∧
      O5.levels s o.us = some ls ∧
      pick (o.args.extract s.np (s.np + s.nm)) s.motiveSrc = some ms' ∧
      ((k = .kRec ∧ ∃ mins',
          pick (o.args.extract (s.np + s.nm) (s.np + s.nm + s.nmin)) (s.minorSrc.filterMap id) = some mins' ∧
          e = mkAppN (Expr.mkConst s.ixRec ls) (o.args.extract 0 s.np ++ ms' ++ mins' ++
            o.args.extract (s.np + s.nm + s.nmin) s.arity ++ o.args.extract s.arity o.args.size)) ∨
       (k = .kRecOn ∧ ∃ ixRecOn mins', ixAuxOf s.ixRec .kRecOn = some ixRecOn ∧
          env.resolves ixRecOn = true ∧
          pick (o.args.extract (s.np + s.nm + s.ni + 1) s.arity) (s.minorSrc.filterMap id) = some mins' ∧
          e = mkAppN (Expr.mkConst ixRecOn ls) (o.args.extract 0 s.np ++ ms' ++
            o.args.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1) ++ mins' ++
            o.args.extract s.arity o.args.size))) := by
  unfold O6.apply at h
  obtain ⟨⟨k, r⟩, hc, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hk, h⟩ := oguard h
  obtain ⟨b, hb, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨s, hs, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hsel, h⟩ := oguard h
  obtain ⟨n, hn, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hsz, h⟩ := oguard h
  obtain ⟨ls, hls, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨ms', hms, h⟩ := obind.1 h
  try dsimp only at h
  have hkk := kind_rec_or_recOn hk
  have hn' : n = s.arity := by
    have := standardTelescope_eq hn
    rcases hkk with rfl | rfl <;> exact this
  subst hn'
  refine ⟨k, r, b, s, ls, ms', hc, hb, hs, bnot_false hsel, hn, by omega, hls, hms, ?_⟩
  rcases hkk with rfl | rfl
  · have h := oite_true (show (AuxKind.kRec == AuxKind.kRec) = true from rfl) h
    obtain ⟨mins', hmins, h⟩ := obind.1 h
    simp only [pure, Option.some.injEq] at h
    exact .inl ⟨rfl, mins', hmins, h.symm⟩
  · have h := oite_false (show ¬ (AuxKind.kRecOn == AuxKind.kRec) = true by decide) h
    obtain ⟨ixRecOn, hix, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨hres, h⟩ := oguard h
    obtain ⟨mins', hmins, h⟩ := obind.1 h
    simp only [pure, Option.some.injEq] at h
    exact .inr ⟨rfl, ixRecOn, mins', hix, bnot_false hres, hmins, h.symm⟩


/-- **O6 is definitional**: its output converts to the occurrence. -/
theorem O6_faithful {Γ : Env} {env : OptEnv} (hrec : RecLaw Γ env) (hon : RecOnLaw Γ env)
    (hix : IxRecOnLaw Γ env) {o : Occ} {e : Expr} (h : O6.apply env o = some e) :
    ExprConv Γ e (occTerm o) := by
  obtain ⟨k, r, b, s, ls, ms', hc, hb, hs, hsel, -, hn, hls, hms, hbr⟩ := O6_some h
  have hls' := O5_levels_eq hls
  rcases hbr with ⟨rfl, mins', hmins, rfl⟩ | ⟨rfl, ixRecOn, mins', hixa, hres, hmins, rfl⟩
  · obtain ⟨v, hδ, hv⟩ := hrec o.head r b s o.us hc hb hs
    rw [← hls'] at hv
    exact rec_sel_conv hδ hv hsel hn hms hmins
  · obtain ⟨⟨v₁, hδ₁, hv₁⟩, ⟨v₂, hδ₂, hv₂⟩⟩ := hon o.head r b s o.us hc hb hs
    rw [← hls'] at hv₂
    obtain ⟨v₃, hδ₃, hv₃⟩ := hix s ixRecOn ls ⟨o.head, b, r, hb, hs⟩ hixa hres
    exact recOn_sel_conv hδ₁ hv₁ hδ₂ hv₂ hδ₃ hv₃ hsel hn hms hmins

/-- **O6's side condition** (the docstring's list). -/
def O6.Side (env : OptEnv) (o : Occ) : Prop :=
  ∃ k r b s ls, classify o.head = some (k, r) ∧ (k = .kRec ∨ k = .kRecOn) ∧
    env.blockOf o.head = some b ∧ b.shapes.get? r = some s ∧ s.isSelection = true ∧
    standardTelescope env s k o.head = some s.arity ∧ s.arity ≤ o.args.size ∧
    O5.levels s o.us = some ls ∧
    (k = .kRecOn → ∃ ixRecOn, ixAuxOf s.ixRec .kRecOn = some ixRecOn ∧ env.resolves ixRecOn = true)

theorem O6_side {env : OptEnv} {o : Occ} {e : Expr} (h : O6.apply env o = some e) : O6.Side env o := by
  obtain ⟨k, r, b, s, ls, _ms, hc, hb, hs, hsel, hn, hsz, hls, _, hbr⟩ := O6_some h
  refine ⟨k, r, b, s, ls, hc, ?_, hb, hs, hsel, hn, hsz, hls, ?_⟩
  · rcases hbr with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact .inl rfl
    · exact .inr rfl
  · intro hk
    rcases hbr with ⟨rfl, -⟩ | ⟨-, ixRecOn, -, hixa, hres, -⟩
    · cases hk
    · exact ⟨ixRecOn, hixa, hres⟩

end Ix.CompileCert.Opt
