import Ix.CompileCert.Opt.Rec

/-!
# M7 L3-def: O1, the recursor of a permuted block (`Ix/Compile/Pass/Opt/O1.lean`)

The docstring's *Faithfulness (definitional)*: "`rec`: … one δ (img), `n` β. `recOn`: Lean's
`r.recOn := λ ps ms is t mins. r ps ms mins is t`, and Pass 2 builds the Ix `recOn` by the same
construction on the canonical block … So `img(r.recOn) a⃗ ≡δβ img(r) ps ms mins is t ≡δβ ρ ps
(ms∘π⁻¹) (mins∘π′⁻¹) is t ≡δβ ρ.recOn ps (ms∘π⁻¹) is t (mins∘π′⁻¹)`." Restated over the
compiler's function `Ix.Compile.Pass.Opt.O1.apply`, unfolded (no core copy):

* `O1_some`: what a successful run established (the decomposition of the `Option` do-block);
* **`O1_faithful`**: `O1.apply env o = some e → ExprConv Γ e (occTerm o)`, given the laws
  `RecLaw` (decision 3: `r` denotes its image, whose shape the block records), `RecOnLaw`
  (Def 3.5: Lean's `x.recOn` is `mkRecOn` over `x.rec`) and `IxRecOnLaw` (AuxLaws: Pass 2's
  `ρ.recOn` is `mkRecOn` over `ρ`);
* `O1.Side`: the side condition, the docstring's list ("`classify` gives `rec` or `recOn`; the
  block's change kind is permutation-only; `img(r)` has a shape that is a permutation; Lean's
  auxiliary has the standard telescope and the recursor's universe parameters; O5 accepts the
  levels; for `recOn` the Ix `recOn` resolves in `E`; `m ≥ n`"); `O1_side`: a firing satisfies it.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Pass.Opt

/-- The kinds O1 and O6 accept. -/
theorem kind_rec_or_recOn {k : AuxKind} (hk : ¬ (k != .kRec && k != .kRecOn) = true) :
    k = .kRec ∨ k = .kRecOn := by
  cases k
  · exact .inl rfl
  · exact .inr rfl
  all_goals exact absurd rfl hk

theorem bnot_false {b : Bool} (h : ¬ (!b) = true) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

/-- What a firing of O1 established. -/
theorem O1_some {env : OptEnv} {o : Occ} {e : Expr} (h : O1.apply env o = some e) :
    ∃ k r b s ls, classify o.head = some (k, r) ∧ env.blockOf o.head = some b ∧
      permutationOnly b.change = true ∧ b.shapes.get? r = some s ∧ s.isPerm = true ∧
      standardTelescope env s k o.head = some s.arity ∧ s.arity ≤ o.args.size ∧
      O5.levels s o.us = some ls ∧
      ((k = .kRec ∧ ∃ ms' mins',
          pick (o.args.extract s.np (s.np + s.nm)) s.motiveSrc = some ms' ∧
          pick (o.args.extract (s.np + s.nm) (s.np + s.nm + s.nmin)) (s.minorSrc.filterMap id) = some mins' ∧
          e = mkAppN (Expr.mkConst s.ixRec ls) (o.args.extract 0 s.np ++ ms' ++ mins' ++
            o.args.extract (s.np + s.nm + s.nmin) s.arity ++ o.args.extract s.arity o.args.size)) ∨
       (k = .kRecOn ∧ ∃ ixRecOn ms' mins', ixAuxOf s.ixRec .kRecOn = some ixRecOn ∧
          env.resolves ixRecOn = true ∧
          pick (o.args.extract s.np (s.np + s.nm)) s.motiveSrc = some ms' ∧
          pick (o.args.extract (s.np + s.nm + s.ni + 1) s.arity) (s.minorSrc.filterMap id) = some mins' ∧
          e = mkAppN (Expr.mkConst ixRecOn ls) (o.args.extract 0 s.np ++ ms' ++
            o.args.extract (s.np + s.nm) (s.np + s.nm + s.ni + 1) ++ mins' ++
            o.args.extract s.arity o.args.size))) := by
  unfold O1.apply at h
  obtain ⟨⟨k, r⟩, hc, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hk, h⟩ := oguard h
  obtain ⟨b, hb, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hperm, h⟩ := oguard h
  obtain ⟨s, hs, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hisp, h⟩ := oguard h
  obtain ⟨n, hn, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hsz, h⟩ := oguard h
  obtain ⟨ls, hls, h⟩ := obind.1 h
  try dsimp only at h
  have hkk := kind_rec_or_recOn hk
  have hn' : n = s.arity := by
    have := standardTelescope_eq hn
    rcases hkk with rfl | rfl <;> exact this
  subst hn'
  refine ⟨k, r, b, s, ls, hc, hb, bnot_false hperm, hs, bnot_false hisp, hn, by omega, hls, ?_⟩
  rcases hkk with rfl | rfl
  · dsimp only at h
    obtain ⟨ms', hms, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨mins', hmins, h⟩ := obind.1 h
    simp only [pure, Option.some.injEq] at h
    exact .inl ⟨rfl, ms', mins', hms, hmins, h.symm⟩
  · dsimp only at h
    obtain ⟨ixRecOn, hix, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨hres, h⟩ := oguard h
    obtain ⟨ms', hms, h⟩ := obind.1 h
    try dsimp only at h
    obtain ⟨mins', hmins, h⟩ := obind.1 h
    simp only [pure, Option.some.injEq] at h
    exact .inr ⟨rfl, ixRecOn, ms', mins', hix, bnot_false hres, hms, hmins, h.symm⟩


/-- **O1 is definitional**: its output converts to the occurrence (one δ of the image and `n`
β-steps for `rec`; δβ of Lean's `x.recOn`, of the image and of Pass 2's `ρ.recOn` for `recOn`). -/
theorem O1_faithful {Γ : Env} {env : OptEnv} (hrec : RecLaw Γ env) (hon : RecOnLaw Γ env)
    (hix : IxRecOnLaw Γ env) {o : Occ} {e : Expr} (h : O1.apply env o = some e) :
    ExprConv Γ e (occTerm o) := by
  obtain ⟨k, r, b, s, ls, hc, hb, -, hs, hisp, -, hn, hls, hbr⟩ := O1_some h
  have hls' := O5_levels_eq hls
  obtain ⟨hsel, -, -⟩ := isPerm_sel hisp
  rcases hbr with ⟨rfl, ms', mins', hms, hmins, rfl⟩ | ⟨rfl, ixRecOn, ms', mins', hixa, hres, hms, hmins, rfl⟩
  · obtain ⟨v, hδ, hv⟩ := hrec o.head r b s o.us hc hb hs
    rw [← hls'] at hv
    exact rec_sel_conv hδ hv hsel hn hms hmins
  · obtain ⟨⟨v₁, hδ₁, hv₁⟩, ⟨v₂, hδ₂, hv₂⟩⟩ := hon o.head r b s o.us hc hb hs
    rw [← hls'] at hv₂
    obtain ⟨v₃, hδ₃, hv₃⟩ := hix s ixRecOn ls ⟨o.head, b, r, hb, hs⟩ hixa hres
    exact recOn_sel_conv hδ₁ hv₁ hδ₂ hv₂ hδ₃ hv₃ hsel hn hms hmins

/-- **O1's side condition** (the docstring's list, every check the code makes). -/
def O1.Side (env : OptEnv) (o : Occ) : Prop :=
  ∃ k r b s ls, classify o.head = some (k, r) ∧ (k = .kRec ∨ k = .kRecOn) ∧
    env.blockOf o.head = some b ∧ permutationOnly b.change = true ∧ b.shapes.get? r = some s ∧
    s.isPerm = true ∧ standardTelescope env s k o.head = some s.arity ∧ s.arity ≤ o.args.size ∧
    O5.levels s o.us = some ls ∧
    (k = .kRecOn → ∃ ixRecOn, ixAuxOf s.ixRec .kRecOn = some ixRecOn ∧ env.resolves ixRecOn = true)

/-- A firing satisfies the side condition. -/
theorem O1_side {env : OptEnv} {o : Occ} {e : Expr} (h : O1.apply env o = some e) : O1.Side env o := by
  obtain ⟨k, r, b, s, ls, hc, hb, hp, hs, hisp, hn, hsz, hls, hbr⟩ := O1_some h
  refine ⟨k, r, b, s, ls, hc, ?_, hb, hp, hs, hisp, hn, hsz, hls, ?_⟩
  · rcases hbr with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact .inl rfl
    · exact .inr rfl
  · intro hk
    rcases hbr with ⟨rfl, -⟩ | ⟨-, ixRecOn, -, -, hixa, hres, -⟩
    · cases hk
    · exact ⟨ixRecOn, hixa, hres⟩

end Ix.CompileCert.Opt
