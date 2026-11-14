import IxVMRefinement.Assembly.ClaimsL1L6
import IxVMRefinement.Assembly.PrefixLoad
import Ix.IxVM.Consistency.Restrict
import IxC.Kernel.Model.StoreCompanions

/-! # Obligation `L7` assembly: `claimedEnv` model restriction, prefix fold, and `IxVM.consistent`

Closes obligation `L7` (`IxVM.Consistency.L7`) and reduces `IxVM.Consistency.CircuitConsistent` to
`DeclsStrong Checked` and `WalkedBareBridge Checked`:

* `refsIn_mono`, `refsIn_liftLooseBVars`, `refsIn_instantiate1Lift`, `annotates_refsIn`,
  `refsIn_instPisAtLift`, `structProjBodiesGo_spec`, and `structProjBodies_spec`: preservation of
  `Expr.RefsIn K` across binder-lifting substitution, `IxVM.Consistency.Annotates` (including
  ζ-reduction), and `Ix.Kernel.structProjBodies`;
* `installs_claimed_stored` and `findProj?_some_inv`: every constant in `(claimedEnv env).consts`
  is either a `.projInfo` table (whose type is a closed sort) or `StoredAs` a `ConstantInfoNonAux`
  declaration constant;
* `StrongEnvProps`, `DeclsStrong`, `DeclsStrong.toDecls`, and `claimedEnv_models_of_installs`:
  discharges all premises of `IxVM.Consistency.claimedModel` (including `hctor` and `hbody` via
  `Ix.Kernel.Model.TableBodies`) to build `Ix.Kernel.Model V (claimedEnv env)` in every set theory;
* `installs_and_inv_of_prefix_checked`, `seedStored_of_installs`, `WalkedBareBridge`,
  `walkedBareBridge_of_subEnv`, `consistentRead_of_declsStrong`, `l7_of_declsStrong`, and
  `consistent_of_declsStrong`: folds `DeclsStrong` over `preparePrelude pre.ix decls`, places the
  seeds (`SeedStored`), and proves `L7 (mkSeams Checked)` and `CircuitConsistent`. -/

universe u

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open Ix.Kernel (Mode)

/-! ## `Expr.RefsIn` preservation under `Annotates` and `structProjBodies` -/

/-- Monotonicity of `Expr.RefsIn` in the key predicate. -/
theorem refsIn_mono {md : Mode} {K₁ K₂ : Ix.Kernel.Key md → Prop}
    (h : ∀ k, K₁ k → K₂ k) : ∀ {e : Ix.Kernel.Expr md}, e.RefsIn K₁ → e.RefsIn K₂ := by
  intro e
  induction e with
  | bvar _ | fvar _ _ | sort _ | lit _ => intro _; trivial
  | const n _ => exact h n
  | app _ _ ihf iha => intro ⟨hf, ha⟩; exact ⟨ihf hf, iha ha⟩
  | lam _ _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | forallE _ _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | letE _ _ _ _ iht ihv ihb => intro ⟨ht, hv, hb⟩; exact ⟨iht ht, ihv hv, ihb hb⟩
  | proj _ _ _ ihe => exact ihe

/-- Lifting loose bound variables preserves `Expr.RefsIn`. -/
theorem refsIn_liftLooseBVars {md : Mode} {K : Ix.Kernel.Key md → Prop} (amt : Nat) :
    ∀ (e : Ix.Kernel.Expr md) (cut : Nat), e.RefsIn K →
      (Ix.Kernel.Expr.liftLooseBVars amt cut e).RefsIn K
  | .bvar _, cut, _ => by
    rw [Ix.Kernel.Expr.liftLooseBVars]
    split <;> trivial
  | .fvar _ _, _, _ | .sort _, _, _ | .lit _, _, _ => trivial
  | .const _ _, _, hk => hk
  | .app f a, cut, ⟨hf, ha⟩ =>
    ⟨refsIn_liftLooseBVars amt f cut hf, refsIn_liftLooseBVars amt a cut ha⟩
  | .lam ty b _, cut, ⟨ht, hb⟩ =>
    ⟨refsIn_liftLooseBVars amt ty cut ht, refsIn_liftLooseBVars amt b (cut + 1) hb⟩
  | .forallE ty b _, cut, ⟨ht, hb⟩ =>
    ⟨refsIn_liftLooseBVars amt ty cut ht, refsIn_liftLooseBVars amt b (cut + 1) hb⟩
  | .letE ty v b _, cut, ⟨ht, hv, hb⟩ =>
    ⟨refsIn_liftLooseBVars amt ty cut ht, refsIn_liftLooseBVars amt v cut hv,
      refsIn_liftLooseBVars amt b (cut + 1) hb⟩
  | .proj _ _ e, cut, he => refsIn_liftLooseBVars amt e cut he

/-- Capture-avoiding single substitution (`instantiate1Lift`) preserves `Expr.RefsIn`. -/
theorem refsIn_instantiate1Lift {md : Mode} {K : Ix.Kernel.Key md → Prop}
    {v : Ix.Kernel.Expr md} (hv : v.RefsIn K) :
    ∀ (e : Ix.Kernel.Expr md) (d : Nat), e.RefsIn K → (e.instantiate1Lift v d).RefsIn K
  | .bvar _, d, _ => by
    rw [Ix.Kernel.Expr.instantiate1Lift]
    split
    · exact refsIn_liftLooseBVars d v 0 hv
    · split <;> trivial
  | .fvar _ _, _, _ | .sort _, _, _ | .lit _, _, _ => trivial
  | .const _ _, _, hk => hk
  | .app f a, d, ⟨hf, ha⟩ =>
    ⟨refsIn_instantiate1Lift hv f d hf, refsIn_instantiate1Lift hv a d ha⟩
  | .lam ty b _, d, ⟨ht, hb⟩ =>
    ⟨refsIn_instantiate1Lift hv ty d ht, refsIn_instantiate1Lift hv b (d + 1) hb⟩
  | .forallE ty b _, d, ⟨ht, hb⟩ =>
    ⟨refsIn_instantiate1Lift hv ty d ht, refsIn_instantiate1Lift hv b (d + 1) hb⟩
  | .letE ty val b _, d, ⟨ht, hval, hb⟩ =>
    ⟨refsIn_instantiate1Lift hv ty d ht, refsIn_instantiate1Lift hv val d hval,
      refsIn_instantiate1Lift hv b (d + 1) hb⟩
  | .proj _ _ e, d, he => refsIn_instantiate1Lift hv e d he

/-- **`Annotates` preserves `Expr.RefsIn`** (including ζ-reduction of `letE` binders). -/
theorem annotates_refsIn {K : Ix.Kernel.Key .anon → Prop}
    {e' e : Ix.Kernel.Expr .anon} (h : IxVM.Consistency.Annotates e' e) :
    e.RefsIn K → e'.RefsIn K := by
  induction h with
  | bvar | fvar _ _ | sort | lit => intro _; trivial
  | const => intro hk; exact hk
  | app _ _ ihf iha => intro ⟨hf, ha⟩; exact ⟨ihf hf, iha ha⟩
  | lam _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | forallE _ _ iht ihb => intro ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | proj _ ihe => intro he; exact ihe he
  | letE _ ih =>
    intro ⟨_, hv, hb⟩
    exact ih (refsIn_instantiate1Lift hv _ 0 hb)

/-- Telescope instantiation (`instPisAtLift`) preserves `Expr.RefsIn`. -/
theorem refsIn_instPisAtLift {md : Mode} {K : Ix.Kernel.Key md → Prop}
    (as : List (Ix.Kernel.Expr md)) :
    ∀ {e r : Ix.Kernel.Expr md},
      (∀ a ∈ as, a.RefsIn K) → e.RefsIn K →
      Ix.Kernel.Expr.instPisAtLift as e = some r → r.RefsIn K := by
  induction as with
  | nil =>
    intro e r _ he h
    simp only [Ix.Kernel.Expr.instPisAtLift, Option.some.injEq] at h
    rwa [← h]
  | cons a as ih =>
    intro e r has he h
    cases e with
    | forallE _ body _ =>
      exact ih (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (refsIn_instantiate1Lift (has a List.mem_cons_self) body 0 he.2) h
    | _ => cases h

/-- `structProjBodiesGo` produces exactly `k` field bodies, each satisfying `Expr.RefsIn K`. -/
theorem structProjBodiesGo_spec {md : Mode} {K : Ix.Kernel.Key md → Prop}
    (T : Ix.Kernel.Key md) (k : Nat) :
    ∀ (i : Nat) {r : Ix.Kernel.Expr md} {bs : List (Ix.Kernel.Expr md)},
      r.RefsIn K → Ix.Kernel.structProjBodiesGo T k i r = some bs →
      bs.length = k ∧ ∀ b ∈ bs, b.RefsIn K := by
  induction k with
  | zero =>
    intro _ _ bs _ h
    simp only [Ix.Kernel.structProjBodiesGo, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ hm => nomatch hm⟩
  | succ k ih =>
    intro i r bs hr h
    cases r with
    | forallE fdom body _ =>
      obtain ⟨hfdom, hbody⟩ := hr
      simp only [Ix.Kernel.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨bs₀, hgo, rfl⟩ := h
      have harg : (Ix.Kernel.structProjArgP T i).RefsIn K := trivial
      obtain ⟨hlen, hall⟩ :=
        ih (i + 1) (refsIn_instantiate1Lift harg body 0 hbody) hgo
      refine ⟨by simp [hlen], fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | htl
      · exact hfdom
      · exact hall b htl
    | _ => cases h

/-- **`structProjBodies` specification**: returns `nF` field bodies, each inheriting `Expr.RefsIn K`
from the constructor's type `cty`. -/
theorem structProjBodies_spec {md : Mode} {K : Ix.Kernel.Key md → Prop}
    (T : Ix.Kernel.Key md) (nP nF : Nat) {cty : Ix.Kernel.Expr md}
    {bodies : Array (Ix.Kernel.Expr md)}
    (hcty : cty.RefsIn K)
    (hbodies : Ix.Kernel.structProjBodies T nP nF cty = some bodies) :
    bodies.size = nF ∧ ∀ b ∈ bodies.toList, b.RefsIn K := by
  unfold Ix.Kernel.structProjBodies at hbodies
  cases hinst : Ix.Kernel.Expr.instPisAtLift (Ix.Kernel.structProjPs nP) cty with
  | none => rw [hinst] at hbodies; cases hbodies
  | some r =>
    rw [hinst, Option.map_eq_some_iff] at hbodies
    obtain ⟨bs, hgo, rfl⟩ := hbodies
    have hps : ∀ a ∈ Ix.Kernel.structProjPs (md := md) nP, a.RefsIn K := by
      intro a ha
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
      trivial
    have hr := refsIn_instPisAtLift (Ix.Kernel.structProjPs nP) hps hcty hinst
    obtain ⟨hlen, hall⟩ := structProjBodiesGo_spec T nF 0 hr hgo
    simpa using ⟨hlen, hall⟩

/-! ## Origin of constants and projection tables in `claimedEnv` -/

private theorem forall₂_mem_left {α β : Type _} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | _, _, .nil, _, hm => nomatch hm
  | _, _, .cons hr htl, x, hm => by
    rcases List.mem_cons.mp hm with rfl | hmem
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hry⟩ := forall₂_mem_left htl x hmem
      exact ⟨y, List.mem_cons_of_mem _ hy, hry⟩

/-- Every constant in `(claimedEnv env).consts` built by `Installs ds env` over `DeclNonAux`
declarations is either a `.projInfo` table or `StoredAs` a `ConstantInfoNonAux` declared constant. -/
theorem installs_claimed_stored {ds : List (Ix.Kernel.Declaration .anon)}
    {env : Ix.Kernel.Env .anon}
    (h : IxVM.Consistency.Installs ds env)
    (hna : ∀ d ∈ ds, DeclNonAux d)
    {c : Ix.Kernel.ConstantInfo .anon}
    (hc : c ∈ (IxVM.Consistency.claimedEnv env).consts) :
    (∃ tbl, c = .projInfo tbl) ∨
      ∃ d ∈ ds, ∃ ci₀ ∈ IxVM.Consistency.installs d,
        IxVM.Consistency.StoredAs c ci₀ ∧ ConstantInfoNonAux ci₀ := by
  by_cases hproj : ∃ tbl, c = .projInfo tbl
  · exact Or.inl hproj
  · have hnproj : ∀ tbl, c ≠ .projInfo tbl := fun tbl heq => hproj ⟨tbl, heq⟩
    obtain ⟨hc_mem, hc_keep⟩ := List.mem_filter.mp hc
    have hc_not_aux : IxVM.Consistency.isModelAux c = false := by simpa using hc_keep
    rcases installs_consts_origin h c hc_mem with ⟨d, hd, ci₀, hci₀, hname⟩ | ⟨b, s, haux⟩
    · obtain ⟨ci', hfind, hst⟩ := h.stored hd hci₀
      have hci_eq : c = ci' :=
        IxVM.Consistency.eq_of_name_eq h.nodup hc_mem
          (Ix.Kernel.Semantics.Env.find?_mem hfind)
          (hname.trans (Ix.Kernel.Semantics.Env.find?_name hfind).symm)
      subst hci_eq
      exact Or.inr ⟨d, hd, ci₀, hci₀, hst, (hna d hd).1 ci₀ hci₀⟩
    · have haux_true : IxVM.Consistency.isModelAux c = true := by
        unfold IxVM.Consistency.isModelAux
        rw [haux]
        cases c with
        | projInfo tbl => exact absurd rfl (hnproj tbl)
        | _ => rfl
      rw [hc_not_aux] at haux_true
      cases haux_true

/-- Inversion of `env.findProj? T i = some entry`. -/
theorem findProj?_some_inv {env : Ix.Kernel.Env .anon} {T : Ix.Kernel.Key .anon}
    {i : Nat} {entry : Ix.Kernel.ProjEntry .anon}
    (h : env.findProj? T i = some entry) :
    ∃ tbl : Ix.Kernel.ProjTable .anon,
      env.find? (Ix.Kernel.projTableName T) = some (.projInfo tbl) ∧
      tbl.structName = T ∧
      i < tbl.numFields ∧
      entry = tbl.entry i ∧
      entry.ctor = tbl.ctor := by
  unfold Ix.Kernel.Env.findProj? at h
  cases hfind : env.find? (Ix.Kernel.projTableName T) with
  | none => rw [hfind] at h; cases h
  | some ci =>
    rw [hfind] at h
    cases ci with
    | projInfo tbl =>
      dsimp only at h
      split at h
      · rename_i hlt
        injection h with hent
        have hname := Ix.Kernel.Semantics.Env.find?_name hfind
        change Ix.Kernel.Key.aux tbl.structName .projTable =
          Ix.Kernel.Key.aux T .projTable at hname
        injection hname with hT
        exact ⟨tbl, rfl, hT, hlt, hent.symm, by rw [← hent]; rfl⟩
      · cases h
    | _ => cases h

/-! ## `StrongEnvProps`, `DeclsStrong`, and `claimedEnv` model restriction -/

/-- Store-level projection-table companion properties required to restrict a model to `claimedEnv`:
`Ix.Kernel.Model.TableBodies env` together with non-auxiliary constructor keys on projection tables
of kept structures. -/
def StrongEnvProps (env : Ix.Kernel.Env .anon) : Prop :=
  Ix.Kernel.Model.TableBodies env ∧
  ∀ n tbl, env.find? n = some (.projInfo tbl) →
    NonAuxKey tbl.ctor ∨ ¬ IxVM.Consistency.KeptKey env tbl.structName

theorem strongEnvProps_empty : StrongEnvProps Ix.Kernel.Env.empty :=
  ⟨Ix.Kernel.Model.TableBodies.empty,
    fun _ _ h => by simp [Ix.Kernel.Env.find?, Ix.Kernel.Env.empty] at h⟩

/-- Step combinator for `StrongEnvProps` along any lookup-preserving extension `env → env₂`. -/
theorem strongEnvProps_step {env env₂ : Ix.Kernel.Env .anon}
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {x : Ix.Kernel.ConstantInfo .anon},
      env.find? k = some x → env₂.find? k = some x)
    (h : StrongEnvProps env)
    (htb : Ix.Kernel.Model.TableBodies env₂)
    (hnew : ∀ n tbl, env₂.find? n = some (.projInfo tbl) → env.find? n = none →
      NonAuxKey tbl.ctor ∨ ¬ IxVM.Consistency.KeptKey env₂ tbl.structName) :
    StrongEnvProps env₂ := by
  refine ⟨htb, fun n tbl hf => ?_⟩
  cases hold : env.find? n with
  | none => exact hnew n tbl hf hold
  | some c =>
    have h2 := hfind hold
    rw [hf] at h2
    obtain rfl := Option.some.inj h2
    rcases h.2 n tbl hold with hna | hnk
    · exact Or.inl hna
    · exact Or.inr fun hk₂ => hnk fun ci hf₁ => hk₂ ci (hfind hf₁)

/-- Step combinator for `StrongEnvProps` when no `.projInfo` entry is added. -/
theorem strongEnvProps_step_noProj {env env₂ : Ix.Kernel.Env .anon}
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {x : Ix.Kernel.ConstantInfo .anon},
      env.find? k = some x → env₂.find? k = some x)
    (h : StrongEnvProps env)
    (hno : Ix.Kernel.Model.NewSat env env₂ Ix.Kernel.Model.NotProj) :
    StrongEnvProps env₂ :=
  strongEnvProps_step hfind h
    (Ix.Kernel.Model.tableBodies_step_noProj hfind h.1 hno)
    fun n tbl hf hn => by
      rcases hno n (.projInfo tbl) hf with hold | hnp
      · rw [hold] at hn; cases hn
      · exact absurd rfl (hnp tbl)

/-- Strengthened `L5` fold obligation carrying `StrongEnvProps` alongside `EnvModelOk`. -/
def DeclsStrong
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) : Prop :=
  ∃ Inv : (V : Type u) → [Ix.Kernel.SetTheory V] → Ix.Kernel.Env .anon → Prop,
    (∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V Ix.Kernel.Env.empty) ∧
    (∀ (V : Type u) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env .anon),
      Inv V env → Ix.Kernel.Model.EnvModelOk V .verified env ∧ StrongEnvProps env) ∧
    ∀ (calls : List (Call F)) (env : Ix.Kernel.Env .anon) (d : Ix.Kernel.Declaration .anon),
      IxVM.Consistency.Bounded calls → Checked calls env d →
        ∃ env₂, IxVM.Consistency.InstallStep env d env₂ ∧
          ∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V env → Inv V env₂

/-- `DeclsStrong Checked` directly implies `IxVM.Consistency.Decls (mkSeams Checked)`. -/
theorem DeclsStrong.toDecls
    {Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop}
    (h : DeclsStrong.{u} Checked) :
    IxVM.Consistency.Decls.{u} (mkSeams Checked) := by
  obtain ⟨Inv, hemp, hok, hstep⟩ := h
  exact ⟨Inv, hemp, fun V _ env hinv => (hok V env hinv).1, hstep⟩

/-- **Model existence for `claimedEnv env`** in every set theory from `Installs ds env`,
`DeclNonAux` on `ds`, `EnvModelOk`, and `StrongEnvProps`. -/
theorem claimedEnv_models_of_installs {ds : List (Ix.Kernel.Declaration .anon)}
    {env : Ix.Kernel.Env .anon}
    (hinst : IxVM.Consistency.Installs ds env)
    (hna : ∀ d ∈ ds, DeclNonAux d)
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V],
      Ix.Kernel.Model.EnvModelOk V .verified env ∧ StrongEnvProps env) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V],
      Nonempty (Ix.Kernel.Model V (IxVM.Consistency.claimedEnv env)) := by
  intro V _
  obtain ⟨hok, htables, hprojCtor⟩ := hmodel V
  obtain ⟨M⟩ := IxVM.Consistency.model_of_envModelOk hok
  have hnd := hinst.nodup
  have hmono : ∀ {e : Ix.Kernel.Expr .anon},
      e.RefsIn NonAuxKey → e.RefsIn (IxVM.Consistency.KeptKey env) :=
    fun hr => refsIn_mono (fun _ hk => IxVM.Consistency.keptKey_of_not_aux hk) hr
  have htype : ∀ c ∈ (IxVM.Consistency.claimedEnv env).consts,
      c.toConstantVal.type.RefsIn (IxVM.Consistency.KeptKey env) := by
    intro c hc
    rcases installs_claimed_stored hinst hna hc with ⟨tbl, rfl⟩ | ⟨_, _, ci₀, _, hst, hci₀⟩
    · trivial
    · exact hmono (annotates_refsIn hst.1.2.2 hci₀.2.1)
  have hvalue : ∀ cv value hint,
      Ix.Kernel.ConstantInfo.defnInfo cv value hint ∈ (IxVM.Consistency.claimedEnv env).consts →
      value.RefsIn (IxVM.Consistency.KeptKey env) := by
    intro cv value hint hc
    rcases installs_claimed_stored hinst hna hc with ⟨_, heq⟩ | ⟨_, _, ci₀, _, hst, hci₀⟩
    · cases heq
    · cases ci₀ with
      | defnInfo _ v₀ _ => exact hmono (annotates_refsIn hst.2.1 hci₀.2.2)
      | _ => exact hst.2.elim
  have hrhs : ∀ cv mI rP rules,
      Ix.Kernel.ConstantInfo.recInfo cv mI rP rules ∈ (IxVM.Consistency.claimedEnv env).consts →
      ∀ rl ∈ rules, rl.rhs.RefsIn (IxVM.Consistency.KeptKey env) := by
    intro cv mI rP rules hc rl hrl
    rcases installs_claimed_stored hinst hna hc with ⟨_, heq⟩ | ⟨_, _, ci₀, _, hst, hci₀⟩
    · cases heq
    · cases ci₀ with
      | recInfo _ _ _ rules₀ =>
        obtain ⟨rl₀, hrl₀_mem, hrl_st⟩ := forall₂_mem_left hst.2.2.2 rl hrl
        exact hmono (annotates_refsIn hrl_st.2.2 (hci₀.2.2 rl₀ hrl₀_mem).2)
      | _ => exact hst.2.elim
  have hctor : ∀ T i entry, (IxVM.Consistency.claimedEnv env).findProj? T i = some entry →
      IxVM.Consistency.KeptKey env T → IxVM.Consistency.KeptKey env entry.ctor := by
    intro T i entry hfp hKT
    rw [IxVM.Consistency.claimedEnv_findProj? hnd T i] at hfp
    obtain ⟨tbl, hfind_tbl, hT_eq, -, -, hctor_eq⟩ := findProj?_some_inv hfp
    rw [hctor_eq]
    rcases hprojCtor (Ix.Kernel.projTableName T) tbl hfind_tbl with hna_ctor | hnk
    · exact IxVM.Consistency.keptKey_of_not_aux hna_ctor
    · rw [hT_eq] at hnk
      exact (hnk hKT).elim
  have hbody : ∀ T i entry, (IxVM.Consistency.claimedEnv env).findProj? T i = some entry →
      IxVM.Consistency.KeptKey env T → entry.body.RefsIn (IxVM.Consistency.KeptKey env) := by
    intro T i entry hfp hKT
    have hK_ctor := hctor T i entry hfp hKT
    rw [IxVM.Consistency.claimedEnv_findProj? hnd T i] at hfp
    obtain ⟨tbl, hfind_tbl, -, hi_lt, rfl, hctor_eq⟩ := findProj?_some_inv hfp
    rw [hctor_eq] at hK_ctor
    obtain ⟨cvC, hfind_ctor, hbodies, -⟩ := htables (Ix.Kernel.projTableName T) tbl hfind_tbl
    have hfind_claimed :
        (IxVM.Consistency.claimedEnv env).find? tbl.ctor =
          some (.ctorInfo cvC tbl.numParams tbl.numFields) := by
      rwa [IxVM.Consistency.claimedEnv_find? hK_ctor]
    have hcty_refs : cvC.type.RefsIn (IxVM.Consistency.KeptKey env) :=
      htype (.ctorInfo cvC tbl.numParams tbl.numFields)
        (Ix.Kernel.Semantics.Env.find?_mem hfind_claimed)
    obtain ⟨hsz, hall⟩ :=
      structProjBodies_spec tbl.structName tbl.numParams tbl.numFields hcty_refs hbodies
    have hi_sz : i < tbl.bodies.size := by omega
    change (tbl.bodies.getD i default).RefsIn (IxVM.Consistency.KeptKey env)
    have hgetD_eq : tbl.bodies.getD i default = tbl.bodies[i] := by
      unfold Array.getD
      simp only [hi_sz, ↓reduceDIte]
      rfl
    rw [hgetD_eq]
    refine hall tbl.bodies[i] ?_
    rw [← Array.getElem_toList]
    exact List.getElem_mem _
  exact ⟨IxVM.Consistency.claimedModel M hnd htype hvalue hrhs hctor hbody⟩

/-! ## Prefix fold, `SeedStored`, `WalkedBareBridge`, and `L7` -/

/-- Prefix fold of `DeclsStrong` along a declaration list `full` when each step is `Checked` at its
installed prefix environment. -/
theorem installs_and_inv_of_prefix_checked
    {Inv : (V : Type u) → [Ix.Kernel.SetTheory V] → Ix.Kernel.Env .anon → Prop}
    {Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop}
    {calls : List (Call F)}
    (hemp : ∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V Ix.Kernel.Env.empty)
    (hstep : ∀ (env : Ix.Kernel.Env .anon) (d : Ix.Kernel.Declaration .anon),
      Checked calls env d →
        ∃ env₂, IxVM.Consistency.InstallStep env d env₂ ∧
          ∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V env → Inv V env₂)
    (full : List (Ix.Kernel.Declaration .anon))
    (hchk : ∀ ds_pre d ds_suf env_pre,
      full = ds_pre ++ d :: ds_suf →
      IxVM.Consistency.Installs ds_pre env_pre →
      Checked calls env_pre d) :
    ∃ env, IxVM.Consistency.Installs full env ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V env := by
  have go : ∀ (ds_rem ds_pre : List (Ix.Kernel.Declaration .anon))
      (env_pre : Ix.Kernel.Env .anon),
      full = ds_pre ++ ds_rem →
      IxVM.Consistency.Installs ds_pre env_pre →
      (∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V env_pre) →
      ∃ env, IxVM.Consistency.Installs full env ∧
        ∀ (V : Type u) [Ix.Kernel.SetTheory V], Inv V env := by
    intro ds_rem
    induction ds_rem with
    | nil =>
      intro ds_pre env_pre hfull hinst hinv
      rw [List.append_nil] at hfull
      subst hfull
      exact ⟨env_pre, hinst, hinv⟩
    | cons d ds_suf ih =>
      intro ds_pre env_pre hfull hinst hinv
      obtain ⟨env₂, hstep_d, hpres⟩ :=
        hstep env_pre d (hchk ds_pre d ds_suf env_pre hfull hinst)
      exact ih (ds_pre ++ [d]) env₂ (by simpa [List.append_assoc] using hfull)
        (hinst.snoc hstep_d) (fun V _ => hpres V (hinv V))
  exact go full [] Ix.Kernel.Env.empty rfl .nil hemp

/-- `SeedStored b ds env a` follows immediately from `Installs ds.toList env`, `AddressKey b a k`,
and membership of `ci₀` (`ci₀.name = k`) in `installs d` for some `d ∈ ds.toList`. -/
theorem seedStored_of_installs {b : Ix.Kernel.Admission.Binding}
    {ds : Array (Ix.Kernel.Declaration .anon)} {env : Ix.Kernel.Env .anon}
    {a : _root_.Address} {k : Ix.Kernel.Key .anon}
    {d : Ix.Kernel.Declaration .anon} {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (hinst : IxVM.Consistency.Installs ds.toList env)
    (hkey : IxVM.Refinement.AddressKey b a k)
    (hname : ci₀.name = k)
    (hd : d ∈ ds.toList)
    (hci₀ : ci₀ ∈ IxVM.Consistency.installs d) :
    IxVM.Consistency.SeedStored b ds env a := by
  obtain ⟨ci, hfind, hst⟩ := hinst.stored hd hci₀
  rw [hname] at hfind
  exact ⟨k, ci₀, ci, hkey, hname, ⟨d, hd, hci₀⟩, hfind, hst⟩

/-- Bridge from `Claim.WalkedL6` to `StreamReadBare` and per-declaration `Checked` at each
installed prefix (universe-independent; `ReadIn`, `DeclNonAux`, `SeedStored`, and `claimedEnv`
model restriction are all discharged automatically from this witness). -/
def WalkedBareBridge
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) : Prop :=
  ∀ {calls : List (Call F)} {clm : Ix.Claim} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {seeds : List _root_.Address}
    {V : IxVM.Refinement.View} {extra : List ByteArray},
    IxVM.Consistency.Bounded calls →
    IxVM.Consistency.InScope clm →
    IxVM.Consistency.ClaimSeeds clm V seeds →
    IxVM.Consistency.ReaderTable clm V b →
    Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t →
    IxVM.Consistency.LoadedBy calls E₀ →
    (∀ a ∈ seeds, ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a) →
    Claim.WalkedL6 calls t E₀ seeds →
    b.bytes ∈ extra →
    (∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra) →
    ¬ V.HashedCollision extra calls →
    ∃ (E : Ixon.Env) (order : List _root_.Address) (pre : Ix.Kernel.Reader.Prelude .anon)
      (st' : Ix.Kernel.Reader.State .anon) (decls : Array (Ix.Kernel.Reader.CDecl .anon)),
      IxVM.Refinement.Draws E E₀ ∧
      IxVM.Consistency.UsedClosureOrderAt t E
        (fun a => a ∈ seeds ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList)
        order ∧
      Ix.Kernel.Reader.preludeFor t = .ok pre ∧
      (∀ a lc, E.consts.get? a = some lc → _root_.Address.blake3Pure lc.rawBytes = a) ∧
      (∀ a bytes, E.blobs.get? a = some bytes → _root_.Address.blake3Pure bytes = a) ∧
      (∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
        ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c) ∧
      StreamReadBare
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        pre.state (Ix.Cert.Stream.decodedOf E order) st' decls ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true ∧
      (∀ ds_pre d ds_suf env_pre,
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList = ds_pre ++ d :: ds_suf →
        IxVM.Consistency.Installs ds_pre env_pre →
        Checked calls env_pre d) ∧
      (∀ a ∈ seeds,
        IxVM.Consistency.IsBlockAt E₀ a ∨
        ∃ (k : Ix.Kernel.Key .anon) (d : Ix.Kernel.Declaration .anon)
          (ci₀ : Ix.Kernel.ConstantInfo .anon),
          IxVM.Refinement.AddressKey b a k ∧ ci₀.name = k ∧
          d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList ∧
          ci₀ ∈ IxVM.Consistency.installs d)

/-- Helper packaging `subEnv E₀ Keep supp` + `closureOrderByRank ... (twoTierRank Wk rank iblock)`
into the existential target of `WalkedBareBridge`, discharging `Draws`, `UsedClosureOrderAt`,
authentication, and `deConstantExact` automatically. -/
theorem walkedBareWitness_of_subEnv
    {Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop}
    {calls : List (Call F)} {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {seeds : List _root_.Address}
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (Keep : _root_.Address → Prop) (supp : List SuppEntry)
    {Wk : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (iblock : _root_.Address → _root_.Address)
    (hsupp_rec : ∀ entry ∈ supp, IxVM.Refinement.IsRecursorRecord entry.2.2)
    (hsupp_auth : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧ Ixon.deConstantExact raw = .ok c)
    (hwk_keep : ∀ x, Wk x → Keep x)
    (hwk_step : ∀ x y, Wk x → Core.S0.WalkEdge E₀ x y → Wk y ∧ rank y < rank x)
    (hwk_rec : ∀ x, Wk x → ∃ c, Ix.Cert.recordAt E₀ x = some c)
    (hextra_rec : ∀ x c, ¬ Wk x → Ix.Cert.recordAt (subEnv E₀ Keep supp) x = some c →
      IxVM.Refinement.IsRecursorRecord c)
    (hextra_refs : ∀ a c, ¬ Wk a → Ix.Cert.recordAt (subEnv E₀ Keep supp) a = some c →
      ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ r cr,
        c.refs[i]? = some r →
        Ix.Cert.recordAt (subEnv E₀ Keep supp) r = some cr →
        Ix.Cert.ownerOf r cr ≠ a →
        (Wk (Ix.Cert.ownerOf r cr) ∧ rank (Ix.Cert.ownerOf r cr) ≤ rank (iblock a)) ∨
          (¬ Wk (Ix.Cert.ownerOf r cr) ∧ rank (iblock (Ix.Cert.ownerOf r cr)) < rank (iblock a)))
    {pre : Ix.Kernel.Reader.Prelude .anon}
    {st' : Ix.Kernel.Reader.State .anon} {decls : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (hreads :
      let E := subEnv E₀ Keep supp
      let S := fun a => a ∈ seeds ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList
      let order := closureOrderByRank t E S (twoTierRank Wk rank iblock)
      StreamReadBare
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        pre.state (Ix.Cert.Stream.decodedOf E order) st' decls)
    (hkeeps : Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true)
    (hchk : ∀ ds_pre d ds_suf env_pre,
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList = ds_pre ++ d :: ds_suf →
      IxVM.Consistency.Installs ds_pre env_pre →
      Checked calls env_pre d)
    (hseeds : ∀ a ∈ seeds,
      IxVM.Consistency.IsBlockAt E₀ a ∨
      ∃ (k : Ix.Kernel.Key .anon) (d : Ix.Kernel.Declaration .anon)
        (ci₀ : Ix.Kernel.ConstantInfo .anon),
        IxVM.Refinement.AddressKey b a k ∧ ci₀.name = k ∧
        d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList ∧
        ci₀ ∈ IxVM.Consistency.installs d) :
    ∃ (E : Ixon.Env) (order : List _root_.Address) (pre : Ix.Kernel.Reader.Prelude .anon)
      (st' : Ix.Kernel.Reader.State .anon) (decls : Array (Ix.Kernel.Reader.CDecl .anon)),
      IxVM.Refinement.Draws E E₀ ∧
      IxVM.Consistency.UsedClosureOrderAt t E
        (fun a => a ∈ seeds ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList)
        order ∧
      Ix.Kernel.Reader.preludeFor t = .ok pre ∧
      (∀ a lc, E.consts.get? a = some lc → _root_.Address.blake3Pure lc.rawBytes = a) ∧
      (∀ a bytes, E.blobs.get? a = some bytes → _root_.Address.blake3Pure bytes = a) ∧
      (∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
        ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c) ∧
      StreamReadBare
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        pre.state (Ix.Cert.Stream.decodedOf E order) st' decls ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true ∧
      (∀ ds_pre d ds_suf env_pre,
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList = ds_pre ++ d :: ds_suf →
        IxVM.Consistency.Installs ds_pre env_pre →
        Checked calls env_pre d) ∧
      (∀ a ∈ seeds,
        IxVM.Consistency.IsBlockAt E₀ a ∨
        ∃ (k : Ix.Kernel.Key .anon) (d : Ix.Kernel.Declaration .anon)
          (ci₀ : Ix.Kernel.ConstantInfo .anon),
          IxVM.Refinement.AddressKey b a k ∧ ci₀.name = k ∧
          d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList ∧
          ci₀ ∈ IxVM.Consistency.installs d) := by
  let E := subEnv E₀ Keep supp
  let S := fun a => a ∈ seeds ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList
  let order := closureOrderByRank t E S (twoTierRank Wk rank iblock)
  refine ⟨E, order, pre, st', decls,
    subEnv_draws E₀ Keep supp hsupp_rec,
    subEnv_twoTier_usedClosureOrderAt t E₀ Keep supp S iblock
      hwk_keep hwk_step hwk_rec hextra_rec hextra_refs,
    hpre,
    fun a lc hget => (subEnv_consts_authentic_exact hload hexact₀ hsupp_auth hget).1,
    fun a bytes hget => (hload.2 a bytes hget).2,
    fun a _ lc hget => (subEnv_consts_authentic_exact hload hexact₀ hsupp_auth hget).2,
    hreads, hkeeps, hchk, hseeds⟩

/-- **`ConsistentRead` from `DeclsStrong` and `WalkedBareBridge`**. -/
theorem consistentRead_of_declsStrong
    {Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop}
    (hStrong : DeclsStrong.{u} Checked)
    (hBridge : WalkedBareBridge Checked)
    {calls : List (Call F)} {clm : Ix.Claim} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {seeds : List _root_.Address}
    {V : IxVM.Refinement.View} {extra : List ByteArray}
    (hbound : IxVM.Consistency.Bounded calls)
    (hscope : IxVM.Consistency.InScope clm)
    (hseeds_clm : IxVM.Consistency.ClaimSeeds clm V seeds)
    (hrt : IxVM.Consistency.ReaderTable clm V b)
    (hadm : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hseedOk : ∀ a ∈ seeds, ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a)
    (hwalk : Claim.WalkedL6 calls t E₀ seeds)
    (hb_extra : b.bytes ∈ extra)
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hnoCol : ¬ V.HashedCollision extra calls) :
    IxVM.Consistency.ConsistentRead.{u} calls b seeds := by
  obtain ⟨Inv, hemp, hok, hstep⟩ := hStrong
  obtain ⟨E, order, pre, st', decls, hdraws, hord, hpre, hauth_rec, hauth_blob, hdec,
    hreads, hkeeps, hchk, hseeds⟩ :=
    hBridge hbound hscope hseeds_clm hrt hadm hload hseedOk hwalk hb_extra hcomm_extra hnoCol
  let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
    (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
  let ev := Ix.Kernel.Reader.evidenceOf cx st' t
  let ds := Ix.Kernel.Frontend.preparePrelude pre.ix decls
  have hreadIn : IxVM.Consistency.ReadIn b E (fun a => a ∈ seeds) ev ds :=
    readIn_of_streamReadBare hadm hord hpre hauth_rec hauth_blob hdec hreads hkeeps
  have hna : ∀ d ∈ ds.toList, DeclNonAux d :=
    preparePrelude_declNonAux hpre hreads
  obtain ⟨env, hinst, hinv⟩ :=
    installs_and_inv_of_prefix_checked hemp
      (fun env_pre d hd => hstep calls env_pre d hbound hd)
      ds.toList hchk
  have hseedStored : ∀ a ∈ seeds,
      IxVM.Consistency.IsBlockAt E₀ a ∨ IxVM.Consistency.SeedStored b ds env a := by
    intro a ha
    rcases hseeds a ha with hblk | ⟨k, d, ci₀, hkey, hname, hd, hci₀⟩
    · exact Or.inl hblk
    · exact Or.inr (seedStored_of_installs hinst hkey hname hd hci₀)
  have hmodels : ∀ (W : Type u) [Ix.Kernel.SetTheory W],
      Nonempty (Ix.Kernel.Model W (IxVM.Consistency.claimedEnv env)) :=
    claimedEnv_models_of_installs hinst hna (fun W _ => hok W env (hinv W))
  exact ⟨E₀, E, ev, ds, env, hload, hdraws, hreadIn, hinst, hseedStored, hmodels⟩

/-- **Obligation `L7` at `mkSeams Checked`** from `DeclsStrong` and `WalkedBareBridge`. -/
theorem l7_of_declsStrong
    {Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop}
    (hStrong : DeclsStrong.{u} Checked)
    (hBridge : WalkedBareBridge Checked) :
    IxVM.Consistency.L7.{u} (mkSeams Checked) := by
  intro _h1 _hDecls hClaim d value heap calls ev hbound bytes c hde hpack hscope V seeds b hseeds hRT
  rcases hClaim d value heap calls ev hbound bytes c hde hpack hscope V seeds b hseeds hRT with
    hcol | ⟨t, E₀, hadm, hload, hseedOk, hwalk⟩
  · exact Or.inl hcol
  · by_cases hcol : V.HashedCollision (bytes :: b.bytes :: IxVM.Consistency.committedImages) calls
    · exact Or.inl hcol
    · exact Or.inr (consistentRead_of_declsStrong hStrong hBridge hbound hscope hseeds hRT
        hadm hload hseedOk hwalk
        (List.mem_cons_of_mem _ List.mem_cons_self)
        (fun img hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
        hcol)

/-- **Circuit-level consistency (`IxVM.Consistency.CircuitConsistent`)** from `DeclsStrong` and
`WalkedBareBridge`, wiring `L0`–`L7` through `IxVM.consistent`. -/
theorem consistent_of_declsStrong
    {Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop}
    (hStrong : DeclsStrong.{u} Checked)
    (hBridge : WalkedBareBridge Checked) :
    IxVM.Consistency.CircuitConsistent.{u} :=
  consistent_of_decls_l7 Checked hStrong.toDecls (l7_of_declsStrong hStrong hBridge)

/-! ## Role-aware bare bridge (`DrawsRoleLocal`, `ReadInRole`, `TableAdmittedComplete`) -/

/-- Store draw relation allowing unwalked role-closure records/blobs at addresses absent from `E₀`
to come from `E_view` (`V.env`) or recursor records, while agreeing byte-for-byte with `E₀` at
every address `E₀` stores. -/
def DrawsRoleLocal (E E₀ E_view : Ixon.Env) : Prop :=
  (∀ a lc, E.consts.get? a = some lc →
    (∃ lc₀, E₀.consts.get? a = some lc₀ ∧ lc₀.rawBytes = lc.rawBytes) ∨
    (E₀.consts.contains a = false ∧
      ((∃ lcV, E_view.consts.get? a = some lcV ∧ lcV.rawBytes = lc.rawBytes) ∨
       (∃ c, lc.get? = some c ∧ IxVM.Refinement.IsRecursorRecord c)))) ∧
  (∀ a bytes, E.blobs.get? a = some bytes →
    E₀.blobs.get? a = some bytes ∨
    (E₀.blobs.contains a = false ∧ E_view.blobs.get? a = some bytes))

/-- `ReadIn` seeded by `seeds` together with `IxVM.Refinement.BindingSeeds t`, ensuring every role
and evidence theorem bound by `t` in `E` enters the closure order alongside `seeds`. -/
def ReadInRole (b : Ix.Kernel.Admission.Binding) (E : Ixon.Env) (seeds : _root_.Address → Prop)
    (ev : Ix.Kernel.Evidences .anon) (ds : Array (Ix.Kernel.Declaration .anon)) : Prop :=
  ∃ (t : Ix.Kernel.RoleTable) (order : List _root_.Address)
    (pre : Ix.Kernel.Reader.Prelude .anon) (limits : Ix.Kernel.Admission.Limits),
    Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t ∧
    IxVM.Consistency.UsedClosureOrderAt t E
      (fun a => seeds a ∨ IxVM.Refinement.BindingSeeds t a) order ∧
    Ix.Kernel.Reader.preludeFor t = .ok pre ∧
    Ix.Kernel.Admission.prepareBare _root_.Address.admissionHash b pre limits
      (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E) = .ok (ev, ds)

/-- **`ReadInRole` from `StreamReadBare`** under `UsedClosureOrderAt` seeded with
`seeds ∨ BindingSeeds t`. -/
theorem readInRole_of_streamReadBare {b : Ix.Kernel.Admission.Binding} {E : Ixon.Env}
    {seeds : _root_.Address → Prop} {t : Ix.Kernel.RoleTable} {order : List _root_.Address}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st' : Ix.Kernel.Reader.State .anon}
    {decls : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (hord : IxVM.Consistency.UsedClosureOrderAt t E
      (fun a => seeds a ∨ IxVM.Refinement.BindingSeeds t a) order)
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (hauth_rec : ∀ a lc, E.consts.get? a = some lc → _root_.Address.blake3Pure lc.rawBytes = a)
    (hauth_blob : ∀ a bytes, E.blobs.get? a = some bytes → _root_.Address.blake3Pure bytes = a)
    (hdec : ∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hreads : StreamReadBare
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
      pre.state (Ix.Cert.Stream.decodedOf E order) st' decls)
    (hkeeps : Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true) :
    ReadInRole b E seeds
      (Ix.Kernel.Reader.evidenceOf
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        st' t)
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls) := by
  obtain ⟨limits, hbatch, hdecoded⟩ := closure_decodesBare E hdec
  refine ⟨t, order, pre, limits, hadm, hord, hpre, ?_⟩
  exact prepareBare_ok hbatch (Ix.Cert.Stream.closure_unique E hord.nodup)
    (closure_authentic_of_env E order hauth_rec hauth_blob) hadm hdecoded hreads hkeeps

/-- Role-aware `ConsistentRead` with `DrawsRoleLocal E E₀ V.env` and `ReadInRole`. -/
def ConsistentReadRole (V : IxVM.Refinement.View) (calls : List (Call F))
    (b : Ix.Kernel.Admission.Binding) (seeds : List _root_.Address) : Prop :=
  ∃ (E₀ E : Ixon.Env) (ev : Ix.Kernel.Evidences .anon)
    (ds : Array (Ix.Kernel.Declaration .anon)) (env : Ix.Kernel.Env .anon),
    IxVM.Consistency.LoadedBy calls E₀ ∧
    DrawsRoleLocal E E₀ V.env ∧
    ReadInRole b E (fun a => a ∈ seeds) ev ds ∧
    IxVM.Consistency.Installs ds.toList env ∧
    (∀ a ∈ seeds, IxVM.Consistency.IsBlockAt E₀ a ∨ IxVM.Consistency.SeedStored b ds env a) ∧
    ∀ (W : Type u) [Ix.Kernel.SetTheory W],
      Nonempty (Ix.Kernel.Model W (IxVM.Consistency.claimedEnv env))

/-- Unpacked witness of an admitted role table `b` in view `V` whose role closure `order_role` is
stored in `V.env`, exact-decoded, used-ref closed, free of non-direct projection rewrites, and
accepted by `Ix.Kernel.Cached.AcceptsRef`. -/
structure TableAdmittedAt (V : IxVM.Refinement.View) (b : Ix.Kernel.Admission.Binding)
    (t : Ix.Kernel.RoleTable) (E_role : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (order_role : List _root_.Address) (envA : Ix.Kernel.Env .anon)
    (pre : Ix.Kernel.Reader.Prelude .anon) (st_role : Ix.Kernel.Reader.State .anon)
    (decls_role : Array (Ix.Kernel.Reader.CDecl .anon)) : Prop where
  tableAdmitted : IxVM.Refinement.TableAdmitted V b
  admitBinding : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t
  litBound : IxVM.Refinement.LiteralSupportBound t
  draws : IxVM.Refinement.Draws E_role V.env
  seeds_in : ∀ a, IxVM.Refinement.BindingSeeds t a → E_role.consts.contains a = true
  closureOrder : Ix.Cert.ClosureOrderAt t E_role (IxVM.Refinement.BindingSeeds t) order_role
  orderStored : ∀ a ∈ order_role, E_role.consts.contains a = true
  preludeFor : Ix.Kernel.Reader.preludeFor t = .ok pre
  prepareWith :
    Ix.Kernel.Admission.prepareWith _root_.Address.admissionHash b pre limits
      (Ix.Cert.recordsOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
      (Ix.Cert.hintsOf E_role) =
    .ok (Ix.Kernel.Reader.evidenceOf
           (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
             (Ix.Cert.Stream.decodedOf E_role order_role)
             (Ix.Cert.blobsOf E_role order_role) (Ix.Cert.hintsOf E_role))
           st_role t,
         Ix.Kernel.Frontend.preparePrelude pre.ix decls_role)
  streamRead :
    Ix.Kernel.Reader.StreamRead
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf E_role order_role)
        (Ix.Cert.blobsOf E_role order_role) (Ix.Cert.hintsOf E_role))
      pre.state (Ix.Cert.Stream.decodedOf E_role order_role) st_role decls_role
  keepsPrelude : Ix.Kernel.Reader.State.keepsPrelude pre.state st_role = true
  noProjRewrites : st_role.projRewrites = 0
  acceptsRef :
    Ix.Kernel.Cached.AcceptsRef .verified
      (Ix.Kernel.Reader.evidenceOf
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E_role order_role)
          (Ix.Cert.blobsOf E_role order_role) (Ix.Cert.hintsOf E_role))
        st_role t)
      ((Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList.map
        IxVM.Refinement.thmToOpaqueDefn)
      envA
  theoremsInProp :
    IxVM.Refinement.TheoremsInProp envA
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList
  bindingSpecs :
    IxVM.Refinement.BindingSpecs t b envA
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList
  viewConsts :
    ∀ a ∈ order_role, ∀ lc, E_role.consts.get? a = some lc →
      (∃ lcV, V.env.consts.get? a = some lcV ∧ lcV.rawBytes = lc.rawBytes) ∧
      (∀ c, Ixon.deConstantExact lc.rawBytes = .ok c → lc.get? = some c)
  usedRefs :
    ∀ a ∈ order_role, ∀ c, Ix.Cert.recordAt E_role a = some c →
      ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ r, c.refs[i]? = some r →
        E_role.consts.contains r = true
  noCommittedCollision :
    ∀ x held img, V.Preimage x held → img ∈ IxVM.Consistency.committedImages →
      _root_.Address.blake3Pure held = x → _root_.Address.blake3Pure img = x → held = img
  usedClosureOrder :
    IxVM.Consistency.UsedClosureOrderAt t E_role (IxVM.Refinement.BindingSeeds t) order_role
  boundConsistent :
    ∀ r a layout ref rec_proj,
      t.addressOf? r = some a →
      Ix.Kernel.Egress.writeProjection layout ref = .ok rec_proj →
      _root_.Address.blake3Pure (Ixon.serConstant rec_proj) = a →
      IxVM.Refinement.compilerTrust r = false ∧ Ix.Cert.recordAt E_role a = some rec_proj
  singleRecBlock :
    ∀ a ∈ order_role, ∀ shape,
      (Ix.Cert.artifactRecIndex E_role).blocks[a]? = some shape →
      ∀ r₁ ∈ shape.recs, ∀ r₂ ∈ shape.recs,
        r₁.block ≠ a → r₂.block ≠ a → r₁.block = r₂.block

/-- Existential form of `TableAdmittedAt`. -/
def TableAdmittedComplete (V : IxVM.Refinement.View) (b : Ix.Kernel.Admission.Binding) : Prop :=
  ∃ t E_role limits order_role envA pre st_role decls_role,
    TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role

/-- Role-aware bridge from `Claim.WalkedL6` + `TableAdmittedComplete` to `StreamReadBare` and
per-declaration `Checked` at each installed prefix. -/
def WalkedBareBridgeRole
    (Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop) : Prop :=
  ∀ {calls : List (Call F)} {clm : Ix.Claim} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {seeds : List _root_.Address}
    {V : IxVM.Refinement.View} {extra : List ByteArray},
    IxVM.Consistency.Bounded calls →
    IxVM.Consistency.InScope clm →
    IxVM.Consistency.ClaimSeeds clm V seeds →
    IxVM.Consistency.ReaderTable clm V b →
    TableAdmittedComplete V b →
    Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t →
    IxVM.Consistency.LoadedBy calls E₀ →
    (∀ a ∈ seeds, ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a) →
    Claim.WalkedL6 calls t E₀ seeds →
    b.bytes ∈ extra →
    (∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra) →
    ¬ V.HashedCollision extra calls →
    ∃ (E : Ixon.Env) (order : List _root_.Address) (pre : Ix.Kernel.Reader.Prelude .anon)
      (st' : Ix.Kernel.Reader.State .anon) (decls : Array (Ix.Kernel.Reader.CDecl .anon)),
      DrawsRoleLocal E E₀ V.env ∧
      IxVM.Consistency.UsedClosureOrderAt t E
        (fun a => a ∈ seeds ∨ IxVM.Refinement.BindingSeeds t a) order ∧
      Ix.Kernel.Reader.preludeFor t = .ok pre ∧
      (∀ a lc, E.consts.get? a = some lc → _root_.Address.blake3Pure lc.rawBytes = a) ∧
      (∀ a bytes, E.blobs.get? a = some bytes → _root_.Address.blake3Pure bytes = a) ∧
      (∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
        ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c) ∧
      StreamReadBare
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        pre.state (Ix.Cert.Stream.decodedOf E order) st' decls ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true ∧
      (∀ ds_pre d ds_suf env_pre,
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList = ds_pre ++ d :: ds_suf →
        IxVM.Consistency.Installs ds_pre env_pre →
        Checked calls env_pre d) ∧
      (∀ a ∈ seeds,
        IxVM.Consistency.IsBlockAt E₀ a ∨
        ∃ (k : Ix.Kernel.Key .anon) (d : Ix.Kernel.Declaration .anon)
          (ci₀ : Ix.Kernel.ConstantInfo .anon),
          IxVM.Refinement.AddressKey b a k ∧ ci₀.name = k ∧
          d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList ∧
          ci₀ ∈ IxVM.Consistency.installs d)

/-- **`ConsistentReadRole` from `DeclsStrong` and `WalkedBareBridgeRole`**. -/
theorem consistentReadRole_of_declsStrong
    {Checked : List (Call F) → Ix.Kernel.Env .anon → Ix.Kernel.Declaration .anon → Prop}
    (hStrong : DeclsStrong.{u} Checked)
    (hBridge : WalkedBareBridgeRole Checked)
    {calls : List (Call F)} {clm : Ix.Claim} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {seeds : List _root_.Address}
    {V : IxVM.Refinement.View} {extra : List ByteArray}
    (hbound : IxVM.Consistency.Bounded calls)
    (hscope : IxVM.Consistency.InScope clm)
    (hseeds_clm : IxVM.Consistency.ClaimSeeds clm V seeds)
    (hrt : IxVM.Consistency.ReaderTable clm V b)
    (hadmV : TableAdmittedComplete V b)
    (hadm : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hseedOk : ∀ a ∈ seeds, ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a)
    (hwalk : Claim.WalkedL6 calls t E₀ seeds)
    (hb_extra : b.bytes ∈ extra)
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hnoCol : ¬ V.HashedCollision extra calls) :
    ConsistentReadRole.{u} V calls b seeds := by
  obtain ⟨Inv, hemp, hok, hstep⟩ := hStrong
  obtain ⟨E, order, pre, st', decls, hdraws, hord, hpre, hauth_rec, hauth_blob, hdec,
    hreads, hkeeps, hchk, hseeds⟩ :=
    hBridge hbound hscope hseeds_clm hrt hadmV hadm hload hseedOk hwalk hb_extra hcomm_extra hnoCol
  let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
    (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
  let ev := Ix.Kernel.Reader.evidenceOf cx st' t
  let ds := Ix.Kernel.Frontend.preparePrelude pre.ix decls
  have hreadIn : ReadInRole b E (fun a => a ∈ seeds) ev ds :=
    readInRole_of_streamReadBare hadm hord hpre hauth_rec hauth_blob hdec hreads hkeeps
  have hna : ∀ d ∈ ds.toList, DeclNonAux d :=
    preparePrelude_declNonAux hpre hreads
  obtain ⟨env, hinst, hinv⟩ :=
    installs_and_inv_of_prefix_checked hemp
      (fun env_pre d hd => hstep calls env_pre d hbound hd)
      ds.toList hchk
  have hseedStored : ∀ a ∈ seeds,
      IxVM.Consistency.IsBlockAt E₀ a ∨ IxVM.Consistency.SeedStored b ds env a := by
    intro a ha
    rcases hseeds a ha with hblk | ⟨k, d, ci₀, hkey, hname, hd, hci₀⟩
    · exact Or.inl hblk
    · exact Or.inr (seedStored_of_installs hinst hkey hname hd hci₀)
  have hmodels : ∀ (W : Type u) [Ix.Kernel.SetTheory W],
      Nonempty (Ix.Kernel.Model W (IxVM.Consistency.claimedEnv env)) :=
    claimedEnv_models_of_installs hinst hna (fun W _ => hok W env (hinv W))
  exact ⟨E₀, E, ev, ds, env, hload, hdraws, hreadIn, hinst, hseedStored, hmodels⟩

end IxVM.Refinement.Assembly
