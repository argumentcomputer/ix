module

public import IxC.Kernel.Verify.Rename.Fold
public import IxC.Kernel.Denotes

@[expose] public section

/-!
# Models pulled back along a renaming (step 7.3, chunk (iv))

A model of the renamed environment is a model of the original one: every
constant `k` denotes what its renaming `k.map f` denotes there
(`pullCval`). The transport is `Denotes.pullback` (a good term denotes, in
`env`, what its renaming denotes in `env'`); `Model.pullback` assembles the
model, and `defn_value_pullback` carries the value clause of a value model
(`Ix.Cert.ValueModel`, assembled by the statements).
-/

namespace Ix.Kernel

open SetTheory Ix.Kernel.SetModel

universe w

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {V : Type w} [SetTheory V]

/-- **The pulled-back constant values**: `k` denotes what `k.map f` does. -/
def pullCval (f : md.Id → md'.Id) (cval' : Key md' → (LevelParam → Nat) → V) :
    Key md → (LevelParam → Nat) → V :=
  fun k φ => cval' (k.map f) φ

/-- **A good term denotes, in `env`, what its renaming denotes in a related
`env'`**, at the pulled-back constant values. -/
theorem Denotes.pullback {env : Env md} {env' : Env md'} (h : EnvRel P f env env')
    {cval' : Key md' → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {e' : Expr md'} {v : V} (hd : Denotes cval' env' φ ρ e' v) :
    ∀ {e : Expr md}, e' = e.mapKeys f → e.Good (KeyScope.ofId P) →
      Denotes (pullCval f cval') env φ ρ e v := by
  induction hd with
  | bvar =>
    intro e he _
    cases e <;> simp [Expr.mapKeys] at he
    subst he
    exact .bvar
  | sort =>
    intro e he _
    cases e <;> simp [Expr.mapKeys] at he
    subst he
    exact .sort
  | @const ρ n us ci hf hlen =>
    intro e he hg
    cases e <;> simp [Expr.mapKeys] at he
    rename_i m us'
    obtain ⟨rfl, rfl⟩ := he
    have hm : m.Good (KeyScope.ofId P) := hg
    rw [h.find m hm] at hf
    obtain ⟨ci₀, hci₀, rfl⟩ := Option.map_eq_some_iff.mp hf
    have hlps : (ci₀.mapKeys f).toConstantVal.levelParams = ci₀.toConstantVal.levelParams := by
      simp [ConstantInfo.mapKeys_toConstantVal]
    rw [hlps] at hlen ⊢
    exact .const hci₀ hlen
  | app _ _ ihf iha =>
    intro e he hg
    cases e <;> simp [Expr.mapKeys] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .app (ihf rfl hg.1) (iha rfl hg.2)
  | lam _ _ hP ihA ihF =>
    intro e he hg
    cases e <;> simp [Expr.mapKeys] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact .lam (ihA rfl hg.1) (fun x hx => ihF x hx rfl hg.2) hP
  | pi _ _ hP ihA ihB =>
    intro e he hg
    cases e <;> simp [Expr.mapKeys] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact .pi (ihA rfl hg.1) (fun x hx => ihB x hx rfl hg.2) hP
  | @proj_table ρ T i e₀ entry P₀ ht _ ihe =>
    intro e he hg
    cases e <;> simp [Expr.mapKeys] at he
    rename_i T₀ i₀ e₁
    obtain ⟨rfl, rfl, rfl⟩ := he
    rw [h.findProj? hg.1] at ht
    obtain ⟨entry₀, hentry₀, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact .proj_table hentry₀ (ihe rfl hg.2)
  | @proj_fst ρ T e₀ P₀ ht _ ihe =>
    intro e he hg
    cases e <;> simp [Expr.mapKeys] at he
    rename_i T₀ i₀ e₁
    obtain ⟨rfl, rfl, rfl⟩ := he
    rw [h.findProj? hg.1] at ht
    exact .proj_fst (Option.map_eq_none_iff.mp ht) (ihe rfl hg.2)
  | @proj_snd ρ T e₀ P₀ ht _ ihe =>
    intro e he hg
    cases e <;> simp [Expr.mapKeys] at he
    rename_i T₀ i₀ e₁
    obtain ⟨rfl, rfl, rfl⟩ := he
    rw [h.findProj? hg.1] at ht
    exact .proj_snd (Option.map_eq_none_iff.mp ht) (ihe rfl hg.2)
  | @natLit ρ n X _ ih =>
    intro e he _
    cases e <;> simp [Expr.mapKeys] at he
    subst he
    exact .natLit (ih (natLitToConstructor_mapKeys n).symm (natLitToConstructor_good (KeyScope.ofId_pre P) n))
  | @strLit ρ s X _ ih =>
    intro e he _
    cases e <;> simp [Expr.mapKeys] at he
    subst he
    exact .strLit (ih (strLitToConstructor_mapKeys s).symm (strLitToConstructor_good (KeyScope.ofId_pre P) (KeyScope.ofId_str P) s))

/-- A constant's denotation at the pulled-back values is its renaming's. -/
theorem Denotes.const_push {env : Env md} {env' : Env md'} (h : EnvRel P f env env')
    {cval' : Key md' → (LevelParam → Nat) → V} {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {k : Key md} {us : List Level} {v : V}
    (hd : Denotes (pullCval f cval') env φ ρ (.const k us) v) :
    Denotes cval' env' φ ρ (.const (k.map f) us) v := by
  cases hd with
  | const hf hlen =>
    rename_i ci
    have hf' := h.find_some hf
    have hlps : (ConstantInfo.mapKeys f ci).toConstantVal.levelParams =
        ci.toConstantVal.levelParams := by
      simp [ConstantInfo.mapKeys_toConstantVal]
    have hd' := Denotes.const (cval := cval') (φ := φ) (ρ := ρ) (us := us) hf'
      (by rw [hlps]; exact hlen)
    rw [hlps] at hd'
    exact hd'

/-- **A model of the renamed environment is a model of the original.** -/
def Model.pullback {env : Env md} {env' : Env md'} (h : EnvRel P f env env')
    (M : Model V env') : Model V env where
  cval := pullCval f M.cval
  mem c hc φ ρ := by
    obtain ⟨T, hT, hmem⟩ := M.mem _ (h.mem hc) φ ρ
    have hty : (c.mapKeys f).toConstantVal.type = c.toConstantVal.type.mapKeys f := by
      simp [ConstantInfo.mapKeys_toConstantVal]
    rw [hty] at hT
    refine ⟨T, Denotes.pullback h hT rfl (h.all c hc).toConstantVal.2, ?_⟩
    have hn : (c.mapKeys f).name = c.name.map f := ConstantInfo.mapKeys_name f c
    rw [hn] at hmem
    exact hmem
  false_empty φ ρ F hF := M.false_empty φ ρ F (Denotes.const_push h hF)
  eq_equality u φ ρ E A a b hE := M.eq_equality u φ ρ E A a b (Denotes.const_push h hE)

/-- **The value clause, pulled back**: if every definition of `env'` denotes
its value, so does every definition of `env` at the pulled-back values. -/
theorem defn_value_pullback {env : Env md} {env' : Env md'} (h : EnvRel P f env env')
    {cval' : Key md' → (LevelParam → Nat) → V}
    (hv : ∀ (cv : ConstantVal md') (value : Expr md') (hint : ReducibilityHint),
      ConstantInfo.defnInfo cv value hint ∈ env'.consts →
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes cval' env' φ ρ value (cval' cv.name φ)) :
    ∀ (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
      ConstantInfo.defnInfo cv value hint ∈ env.consts →
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
        Denotes (pullCval f cval') env φ ρ value (pullCval f cval' cv.name φ) := by
  intro cv value hint hc φ ρ
  have hc' := h.mem hc
  have hg := h.all _ hc
  exact Denotes.pullback h (hv _ _ hint hc' φ ρ) rfl hg.2

end Ix.Kernel
