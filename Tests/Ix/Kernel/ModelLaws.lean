import IxC.Kernel.Denotes
import IxC.Kernel.Semantics.EnvFacts
import Ix.IxVM.Consistency.Restrict

/-! # The model's laws rule out wrong meanings

`Ix.Kernel.Model` asks more of an interpretation than that every stored
constant inhabit its type: a stored definition must denote what its value
denotes (`Model.defn_value`). Without that law, an environment with

```
def P : Prop := False
theorem bad : P := True.intro
```

would have a model, one in which `P` is true, even though Lean reads `P` as
`False`; so a checker that wrongly accepted `bad` would still be called
consistent. With the law it has none (`no_model_of_false_def`): whatever else
the environment holds and whatever `bad`'s stored value is, `P` denotes what
`False` denotes, the empty set, and `bad` cannot be a member of it. -/

open _root_.Ix.Kernel _root_.Ix.Kernel.SetTheory

namespace Tests.Ix.Kernel.ModelLaws

universe w

variable {md : Mode} {V : Type w} [SetTheory V]

/-- **A definition of `False` has no model with an inhabitant.** In an
environment that stores `def P : Prop := False` (any reducibility hint) and a
theorem of type `P` (any value), there is no model. -/
theorem no_model_of_false_def {env : Env md} {P bad : Key md} {cvP cvB : ConstantVal md}
    {hint : ReducibilityHint} {v : Expr md}
    (hP : env.find? P = some (.defnInfo cvP (.const falseName []) hint))
    (hbad : env.find? bad = some (.thmInfo cvB v))
    (hty : cvB.type = .const P []) :
    Model V env → False := by
  intro M
  have hPname : cvP.name = P := _root_.Ix.Kernel.Semantics.Env.find?_name hP
  obtain ⟨T, hT, hmem⟩ :=
    M.mem _ (_root_.Ix.Kernel.Semantics.Env.find?_mem hbad) (fun _ => 0) (fun _ => empty)
  change Denotes M.cval env (fun _ => 0) (fun _ => empty) cvB.type T at hT
  rw [hty] at hT
  cases hT with
  | const hf _ =>
    rw [hP] at hf
    cases hf
    -- `P`'s value is `False`, which denotes the empty set
    have hval := M.defn_value cvP _ hint (_root_.Ix.Kernel.Semantics.Env.find?_mem hP)
      (Level.substFn (fun _ => 0) cvP.levelParams []) (fun _ => empty)
    have hempty : M.cval cvP.name (Level.substFn (fun _ => 0) cvP.levelParams []) = empty :=
      M.false_empty _ _ _ hval
    rw [hPname] at hempty
    have hmem' : M.cval cvB.name (fun _ => 0)
        ∈ˢ M.cval P (Level.substFn (fun _ => 0) cvP.levelParams []) := hmem
    rw [hempty] at hmem'
    exact not_mem_empty _ hmem'

/--
info: 'Tests.Ix.Kernel.ModelLaws.no_model_of_false_def' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms no_model_of_false_def

/-! ## Stated over what the consistency statement gives

`IxVM.Consistency.ConsistentRead` does not hand over lookups: it gives the reader's
declarations `ds`, an environment they install (`Installs`, each constant stored as
declared, `StoredAs`), and a model of its claimed sub-environment. The examples below are
stated over those. -/

open _root_.IxVM.Consistency in
/-- **Declarations that define `P : Prop` as `False` and prove `P` install no environment
with a model.** If `ds` installs `env`, `ds` holds `def P : Prop := False` and a theorem
of type `P`, and both are at input or role keys, then the claimed sub-environment of `env`
has no model: both are stored as declared, so δ reads `P`'s own value. -/
theorem no_model_of_false_def_installs {ds : List (Declaration .anon)} {env : Env .anon}
    (hI : Installs ds env) {cvP cvB : ConstantVal .anon} {hint : ReducibilityHint}
    {v : Expr .anon}
    (hP : .defnDecl cvP (.const falseName []) hint ∈ ds) (hB : .thmDecl cvB v ∈ ds)
    (hty : cvB.type = .const cvP.name [])
    (hPk : ∀ b t, cvP.name ≠ .aux b t) (hBk : ∀ b t, cvB.name ≠ .aux b t) :
    Model V (claimedEnv env) → False := by
  obtain ⟨ciP, hfP, hsP⟩ :=
    hI.claimed hP (ci₀ := .defnInfo cvP (.const falseName []) hint) (List.mem_singleton_self _) hPk
  obtain ⟨ciB, hfB, hsB⟩ := hI.claimed hB (ci₀ := .thmInfo cvB v) (List.mem_singleton_self _) hBk
  cases ciP with
  | defnInfo cvP' vP hP' =>
    obtain ⟨hav, rfl⟩ := hsP.2
    obtain rfl := hav.const_inv
    cases ciB with
    | thmInfo cvB' vB =>
      have hann : Annotates cvB'.type cvB.type := hsB.1.2.2
      rw [hty] at hann
      exact no_model_of_false_def (P := cvP.name) (bad := cvB.name) hfP hfB hann.const_inv
    | _ => exact False.elim hsB.2
  | _ => exact False.elim hsP.2

open _root_.IxVM.Consistency in
/-- **No `ConsistentRead` reads `def P : Prop := False` with a theorem of type `P`**: in
every set theory, the reading a `ConsistentRead` exhibits holds no such pair at input or
role keys. -/
theorem consistentRead_no_false_def (V : Type w) [SetTheory V]
    {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {seeds : List _root_.Address}
    (h : ConsistentRead.{w} calls seeds) :
    ∃ (b : _root_.Ix.Kernel.Admission.Binding) (E : _root_.Ixon.Env) (ev : Evidences .anon)
      (ds : Array (Declaration .anon)),
      ReadIn b E (fun a => a ∈ seeds) ev ds ∧
      ∀ (cvP cvB : ConstantVal .anon) (hint : ReducibilityHint) (v : Expr .anon),
        .defnDecl cvP (.const falseName []) hint ∈ ds.toList → .thmDecl cvB v ∈ ds.toList →
        cvB.type = .const cvP.name [] → (∀ b t, cvP.name ≠ .aux b t) →
        (∀ b t, cvB.name ≠ .aux b t) → False := by
  obtain ⟨b, -, E, ev, ds, env, -, -, -, hread, hI, -, hmodel⟩ := h
  obtain ⟨M⟩ := hmodel V
  exact ⟨b, E, ev, ds, hread, fun _ _ _ _ hP hB hty hPk hBk =>
    no_model_of_false_def_installs hI hP hB hty hPk hBk M⟩

/--
info: 'Tests.Ix.Kernel.ModelLaws.consistentRead_no_false_def' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms consistentRead_no_false_def


/-! ## ι rules out a recursor's wrong meaning

```
def P : Prop := Nat.rec (motive := fun _ => Prop) False (fun _ _ => T) 0
theorem bad : P
```

Lean reads `P` as `False` by `Nat.rec`'s rule for `Nat.zero`. Without the ι law, a model
could read `P` as true. With it there is none, whatever the stored binder annotations are
(`Annotates` leaves them free). -/

section NatRec

open _root_.IxVM.Consistency _root_.Ix.Kernel.SetModel

/-- `∀ (t : Nat), Sort u`, the type of `Nat.rec`'s motive, at binder metadata `m`. -/
def motT (m : BinderMeta) : Expr .anon :=
  .forallE (.const natName []) (.sort (.param BasisDSL.uN)) m

/-- `motive Nat.zero`, under the motive. -/
def zeroT : Expr .anon := .app (.bvar 0) (.const natZeroName [])

/-- `∀ (n : Nat), motive n → motive (Nat.succ n)`, under the motive and the zero case. -/
def succT (m₁ m₂ : BinderMeta) : Expr .anon :=
  .forallE (.const natName [])
    (.forallE (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
      m₂) m₁

/-- `Nat.rec`'s type. -/
def recT (d m₁ m₂ s₁ s₂ m₃ m₄ : BinderMeta) : Expr .anon :=
  .forallE (motT d) (.forallE zeroT (.forallE (succT s₁ s₂)
    (.forallE (.const natName []) (.app (.bvar 3) (.bvar 0)) m₄) m₃) m₂) m₁

/-- The right-hand side of `Nat.rec`'s rule for `Nat.zero`: `fun motive zero succ => zero`. -/
def zeroRhs (d s₁ s₂ l₁ l₂ l₃ : BinderMeta) : Expr .anon :=
  .lam (motT d) (.lam zeroT (.lam (succT s₁ s₂) (.bvar 1) l₃) l₂) l₁

/-- `Nat.rec.{1} (fun _ : Nat => Prop) False (fun (_ : Nat) (_ : Prop) => T) 0`. -/
def pValue (kT : Key .anon) (a b c : BinderMeta) : Expr .anon :=
  .app (.app (.app (.app (.const natRecName [.succ .zero])
    (.lam (.const natName []) (.sort .zero) a))
    (.const falseName []))
    (.lam (.const natName []) (.lam (.sort .zero) (.const kT []) c) b))
    (.lit (.natVal 0))

/-- The pinned `Nat.rec`, up to its binder metadata and install-computed rule fields. -/
theorem natRecA_shape : ∃ (d m₁ m₂ s₁ s₂ m₃ m₄ e t₁ t₂ l₁ l₂ l₃ : BinderMeta)
    (cp : Nat) (fi : RecRuleFire .anon) (k et pb : Bool) (rl₁ : RecRule .anon),
    (natRecA : ConstantInfo .anon) =
      .recInfo ⟨natRecName, [BasisDSL.uN], recT d m₁ m₂ s₁ s₂ m₃ m₄⟩ 3 3
        [⟨natZeroName, 0, cp, fi, zeroRhs e t₁ t₂ l₁ l₂ l₃, k, et, pb⟩, rl₁] :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem natZeroA_shape :
    (natZeroA : ConstantInfo .anon) = .ctorInfo ⟨natZeroName, [], .const natName []⟩ 0 0 := rfl

theorem natSuccA_shape : ∃ m : BinderMeta, (natSuccA : ConstantInfo .anon) =
    .ctorInfo ⟨natSuccName, [], .forallE (.const natName []) (.const natName []) m⟩ 0 1 :=
  ⟨_, rfl⟩

/-! ### Annotations of these shapes -/

theorem ann_bvar {t : Expr .anon} {i : Nat} (h : Annotates t (.bvar i)) : t = .bvar i := by
  cases h; rfl

theorem ann_sort {t : Expr .anon} {l : Level} (h : Annotates t (.sort l)) : t = .sort l := by
  cases h; rfl

theorem ann_lit {t : Expr .anon} {l : Literal} (h : Annotates t (.lit l)) : t = .lit l := by
  cases h; rfl

theorem ann_app {t f a : Expr .anon} (h : Annotates t (.app f a)) :
    ∃ f' a', t = .app f' a' ∧ Annotates f' f ∧ Annotates a' a := by
  cases h with
  | app h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

theorem ann_lam {t ty b : Expr .anon} {m : BinderMeta} (h : Annotates t (.lam ty b m)) :
    ∃ ty' b' m', t = .lam ty' b' m' ∧ Annotates ty' ty ∧ Annotates b' b := by
  cases h with
  | lam h₁ h₂ => exact ⟨_, _, _, rfl, h₁, h₂⟩

theorem ann_pi {t ty b : Expr .anon} {m : BinderMeta} (h : Annotates t (.forallE ty b m)) :
    ∃ ty' b' m', t = .forallE ty' b' m' ∧ Annotates ty' ty ∧ Annotates b' b := by
  cases h with
  | forallE h₁ h₂ => exact ⟨_, _, _, rfl, h₁, h₂⟩

theorem ann_motT {t : Expr .anon} {m : BinderMeta} (h : Annotates t (motT m)) :
    ∃ m', t = motT m' := by
  obtain ⟨ty, b, m', rfl, h₁, h₂⟩ := ann_pi h
  rw [h₁.const_inv, ann_sort h₂]
  exact ⟨m', rfl⟩

theorem ann_zeroT {t : Expr .anon} (h : Annotates t zeroT) : t = zeroT := by
  obtain ⟨f, a, rfl, h₁, h₂⟩ := ann_app h
  rw [ann_bvar h₁, h₂.const_inv]
  rfl

theorem ann_succT {t : Expr .anon} {m₁ m₂ : BinderMeta} (h : Annotates t (succT m₁ m₂)) :
    ∃ m₁' m₂', t = succT m₁' m₂' := by
  obtain ⟨ty, b, m₁', rfl, h₁, h₂⟩ := ann_pi h
  obtain ⟨ty₂, b₂, m₂', rfl, h₃, h₄⟩ := ann_pi h₂
  obtain ⟨f₃, a₃, rfl, h₅, h₆⟩ := ann_app h₃
  obtain ⟨f₄, a₄, rfl, h₇, h₈⟩ := ann_app h₄
  obtain ⟨f₈, a₈, rfl, h₉, h₁₀⟩ := ann_app h₈
  rw [h₁.const_inv, ann_bvar h₅, ann_bvar h₆, ann_bvar h₇, h₉.const_inv, ann_bvar h₁₀]
  exact ⟨m₁', m₂', rfl⟩

theorem ann_recT {t : Expr .anon} {d m₁ m₂ s₁ s₂ m₃ m₄ : BinderMeta}
    (h : Annotates t (recT d m₁ m₂ s₁ s₂ m₃ m₄)) :
    ∃ d' m₁' m₂' s₁' s₂' m₃' m₄', t = recT d' m₁' m₂' s₁' s₂' m₃' m₄' := by
  obtain ⟨ty₁, b₁, m₁', rfl, h₁, h₂⟩ := ann_pi h
  obtain ⟨ty₂, b₂, m₂', rfl, h₃, h₄⟩ := ann_pi h₂
  obtain ⟨ty₃, b₃, m₃', rfl, h₅, h₆⟩ := ann_pi h₄
  obtain ⟨ty₄, b₄, m₄', rfl, h₇, h₈⟩ := ann_pi h₆
  obtain ⟨f, a, rfl, h₉, h₁₀⟩ := ann_app h₈
  obtain ⟨d', rfl⟩ := ann_motT h₁
  obtain ⟨s₁', s₂', rfl⟩ := ann_succT h₅
  rw [ann_zeroT h₃, h₇.const_inv, ann_bvar h₉, ann_bvar h₁₀]
  exact ⟨d', m₁', m₂', s₁', s₂', m₃', m₄', rfl⟩

theorem ann_zeroRhs {t : Expr .anon} {d s₁ s₂ l₁ l₂ l₃ : BinderMeta}
    (h : Annotates t (zeroRhs d s₁ s₂ l₁ l₂ l₃)) :
    ∃ d' s₁' s₂' l₁' l₂' l₃', t = zeroRhs d' s₁' s₂' l₁' l₂' l₃' := by
  obtain ⟨ty₁, b₁, l₁', rfl, h₁, h₂⟩ := ann_lam h
  obtain ⟨ty₂, b₂, l₂', rfl, h₃, h₄⟩ := ann_lam h₂
  obtain ⟨ty₃, b₃, l₃', rfl, h₅, h₆⟩ := ann_lam h₄
  obtain ⟨d', rfl⟩ := ann_motT h₁
  obtain ⟨s₁', s₂', rfl⟩ := ann_succT h₅
  rw [ann_zeroT h₃, ann_bvar h₆]
  exact ⟨d', s₁', s₂', l₁', l₂', l₃', rfl⟩

theorem ann_pValue {t : Expr .anon} {kT : Key .anon} {a b c : BinderMeta}
    (h : Annotates t (pValue kT a b c)) : ∃ a' b' c', t = pValue kT a' b' c' := by
  obtain ⟨f₁, x₁, rfl, h₁, h₂⟩ := ann_app h
  obtain ⟨f₂, x₂, rfl, h₃, h₄⟩ := ann_app h₁
  obtain ⟨f₃, x₃, rfl, h₅, h₆⟩ := ann_app h₃
  obtain ⟨f₄, x₄, rfl, h₇, h₈⟩ := ann_app h₅
  obtain ⟨ty₈, b₈, a', rfl, h₉, h₁₀⟩ := ann_lam h₈
  obtain ⟨ty₄, b₄, b', rfl, h₁₁, h₁₂⟩ := ann_lam h₄
  obtain ⟨ty₁₂, b₁₂, c', rfl, h₁₃, h₁₄⟩ := ann_lam h₁₂
  rw [ann_lit h₂, h₆.const_inv, h₇.const_inv, h₉.const_inv, ann_sort h₁₀, h₁₁.const_inv,
    ann_sort h₁₃, h₁₄.const_inv]
  exact ⟨a', b', c', rfl⟩

/-! ### Reading denotations back -/

variable {cval : Key .anon → (LevelParam → Nat) → V} {env : Env .anon} {φ : LevelParam → Nat}

theorem den_bvar_inv {ρ : BVarIdx → V} {i : Nat} {X : V}
    (h : Denotes cval env φ ρ (.bvar i) X) : X = ρ i := by
  cases h; rfl

theorem den_sort_inv {ρ : BVarIdx → V} {l : Level} {X : V}
    (h : Denotes cval env φ ρ (.sort l) X) : X = univ (Level.eval φ l) := by
  cases h; rfl

theorem den_app_inv {ρ : BVarIdx → V} {f a : Expr .anon} {X : V}
    (h : Denotes cval env φ ρ (.app f a) X) :
    ∃ F A, X = app F A ∧ Denotes cval env φ ρ f F ∧ Denotes cval env φ ρ a A := by
  cases h with
  | app hf ha => exact ⟨_, _, rfl, hf, ha⟩

theorem den_lam_inv {ρ : BVarIdx → V} {ty b : Expr .anon} {m : BinderMeta} {X : V}
    (h : Denotes cval env φ ρ (.lam ty b m) X) :
    ∃ A F, X = lamR (regime φ m.pw) A F ∧ Denotes cval env φ ρ ty A ∧
      (∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) b (F x)) ∧
      (regime φ m.pw = 0 → ∀ x, x ∈ˢ A → F x = pt) := by
  cases h with
  | lam hA hF hP => exact ⟨_, _, rfl, hA, hF, hP⟩

theorem den_pi_inv {ρ : BVarIdx → V} {ty b : Expr .anon} {m : BinderMeta} {X : V}
    (h : Denotes cval env φ ρ (.forallE ty b m) X) :
    ∃ A B, X = piR (regime φ m.pw) A B ∧ Denotes cval env φ ρ ty A ∧
      (∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) b (B x)) ∧
      (regime φ m.pw = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) := by
  cases h with
  | pi hA hB hP => exact ⟨_, _, rfl, hA, hB, hP⟩

theorem den_natLit_inv {ρ : BVarIdx → V} {n : Nat} {X : V}
    (h : Denotes cval env φ ρ (.lit (.natVal n)) X) :
    Denotes cval env φ ρ (natLitToConstructor n) X := by
  cases h with
  | natLit h => exact h

theorem substFn_nil' (φ : LevelParam → Nat) : Level.substFn φ [] [] = φ := funext fun _ => rfl

/-- A constant without level parameters denotes its value at the assignment in force. -/
theorem den_const_nil {ρ : BVarIdx → V} {n : Key .anon} {X : V}
    (h : Denotes cval env φ ρ (.const n []) X) :
    X = cval n φ ∧ ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = [] := by
  cases h with
  | @const _ _ _ ci hf hlen =>
    have hps : ci.toConstantVal.levelParams = [] :=
      List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    refine ⟨?_, ci, hf, hps⟩
    rw [hps, substFn_nil']

theorem den_const_nil_intro {ρ : BVarIdx → V} {n : Key .anon} {ci : ConstantInfo .anon}
    (hf : env.find? n = some ci) (hps : ci.toConstantVal.levelParams = []) :
    Denotes cval env φ ρ (.const n []) (cval n φ) := by
  have h := Denotes.const (cval := cval) (φ := φ) (ρ := ρ) (us := []) hf (by simp [hps])
  rwa [hps, substFn_nil'] at h

/-! ### Facts about the universes -/

theorem univ0_ne_pt : (univ 0 : V) ≠ pt := by
  intro h
  have h₁ : (empty : V) ∈ˢ pt := by rw [← h]; exact empty_mem_univ 0
  have h₂ : (unitSet : V) ∈ˢ pt := by rw [← h]; exact unitSet_mem_univ 0
  rw [mem_pt] at h₁ h₂
  exact unitSet_ne_empty (h₂.trans h₁.symm)

theorem univ1_not_mem_univ0 : ¬ (univ 1 : V) ∈ˢ univ 0 := by
  intro h
  rw [univ_zero] at h
  exact univ0_ne_pt (eq_pt_of_mem_univZero h (univ_mem_univ 0))

theorem ne_pt_of_mem_univ0 {T : V} (h : T ∈ˢ univ 0) : T ≠ pt := fun he =>
  have hT0 : T ∈ˢ (univZero : V) := by rw [← univ_zero]; exact h
  truthVal_ne_pt _ ((mem_univZero_eq_truthVal hT0).symm.trans he)

/-! ### The motive, the cases and the right-hand side, in any annotation -/

/-- The motive `fun _ : Nat => Prop` maps every number to `Prop`, and is a member of
`Nat → Sort u` at `u = 1`, whatever the binder annotations. -/
theorem mot_facts {ρ : BVarIdx → V} {N Z0 Mv : V} {a : BinderMeta}
    (hN : ∀ ρ X, Denotes cval env φ ρ (.const natName []) X → X = N) (hZ0 : Z0 ∈ˢ N)
    (hMv : Denotes cval env φ ρ (.lam (.const natName []) (.sort .zero) a) Mv) :
    (∀ x, x ∈ˢ N → app Mv x = univ 0) ∧
      (φ BasisDSL.uN = 1 → ∀ (ρ' : BVarIdx → V) (d : BinderMeta) (X : V),
        Denotes cval env φ ρ' (motT d) X → Mv ∈ˢ X) := by
  obtain ⟨A, F, rfl, hA, hF, hP⟩ := den_lam_inv hMv
  obtain rfl := hN _ _ hA
  have hF0 : ∀ x, x ∈ˢ A → F x = univ 0 := fun x hx => den_sort_inv (hF x hx)
  have hr : regime φ a.pw ≠ 0 := fun h => univ0_ne_pt ((hF0 Z0 hZ0).symm.trans (hP h Z0 hZ0))
  refine ⟨fun x hx => by rw [app_lamR_pos hr hx]; exact hF0 x hx, ?_⟩
  intro hφ ρ' d X hX
  obtain ⟨A', B, rfl, hA', hB, hP'⟩ := den_pi_inv hX
  obtain rfl := (hN _ _ hA').symm
  have hB1 : ∀ x, x ∈ˢ A → B x = univ 1 := fun x hx => by
    rw [den_sort_inv (hB x hx)]; simp [Level.eval, hφ]
  have hr' : regime φ d.pw ≠ 0 := fun h =>
    univ1_not_mem_univ0 (by rw [← hB1 Z0 hZ0]; exact hP' h Z0 hZ0)
  exact lamR_mem_zero_agree ⟨fun h => absurd h hr, fun h => absurd h hr'⟩
    (fun x hx => by rw [hF0 x hx, hB1 x hx]; exact univ_mem_univ 0)

/-- `False`'s denotation, the empty set, is a member of `motive Nat.zero`. -/
theorem zero_mem {ρ : BVarIdx → V} {N Z0 Mv X : V}
    (hZ : ∀ ρ X, Denotes cval env φ ρ (.const natZeroName []) X → X = Z0) (hZ0 : Z0 ∈ˢ N)
    (happ : ∀ x, x ∈ˢ N → app Mv x = univ 0)
    (hX : Denotes cval env φ (push Mv ρ) zeroT X) : (empty : V) ∈ˢ X := by
  obtain ⟨F, A, rfl, hF, hA⟩ := den_app_inv hX
  have hFv : F = Mv := den_bvar_inv hF
  rw [hFv, hZ _ _ hA, happ Z0 hZ0]
  exact empty_mem_univ 0

/-- The successor case `fun (_ : Nat) (_ : Prop) => T`, for a proposition `T`, is a member
of `∀ n, motive n → motive (Nat.succ n)`, whatever the binder annotations. -/
theorem succ_mem {ρ ρ' : BVarIdx → V} {N Z0 Mv Fv S0 Tv Sv X : V} {kT : Key .anon}
    {b c s₁ s₂ : BinderMeta}
    (hN : ∀ ρ X, Denotes cval env φ ρ (.const natName []) X → X = N) (hZ0 : Z0 ∈ˢ N)
    (hS : ∀ ρ X, Denotes cval env φ ρ (.const natSuccName []) X → X = S0)
    (hSN : ∀ n, n ∈ˢ N → app S0 n ∈ˢ N)
    (hT : ∀ ρ X, Denotes cval env φ ρ (.const kT []) X → X = Tv) (hTv : Tv ∈ˢ univ 0)
    (happ : ∀ x, x ∈ˢ N → app Mv x = univ 0)
    (hSv : Denotes cval env φ ρ
      (.lam (.const natName []) (.lam (.sort .zero) (.const kT []) c) b) Sv)
    (hX : Denotes cval env φ (push Fv (push Mv ρ')) (succT s₁ s₂) X) : Sv ∈ˢ X := by
  obtain ⟨A, G, rfl, hA, hG, hPG⟩ := den_lam_inv hSv
  obtain rfl := hN _ _ hA
  -- the inner abstraction: `fun _ : Prop => T`
  have hc : regime φ c.pw ≠ 0 := by
    intro h
    obtain ⟨A₂, F₂, -, hA₂, hF₂, hP₂⟩ := den_lam_inv (hG Z0 hZ0)
    have hA₂' : A₂ = univ 0 := den_sort_inv hA₂
    have he : (empty : V) ∈ˢ A₂ := by rw [hA₂']; exact empty_mem_univ 0
    exact ne_pt_of_mem_univ0 hTv ((hT _ _ (hF₂ _ he)).symm.trans (hP₂ h _ he))
  have hGx : ∀ x, x ∈ˢ A → ∃ F₂, G x = lamR (regime φ c.pw) (univ 0) F₂ ∧
      ∀ y, y ∈ˢ (univ 0 : V) → F₂ y = Tv := by
    intro x hx
    obtain ⟨A₂, F₂, he, hA₂, hF₂, -⟩ := den_lam_inv (hG x hx)
    have hA₂' : A₂ = univ 0 := den_sort_inv hA₂
    subst hA₂'
    exact ⟨F₂, he, fun y hy => hT _ _ (hF₂ y hy)⟩
  have hb : regime φ b.pw ≠ 0 := by
    intro h
    obtain ⟨F₂, he, -⟩ := hGx Z0 hZ0
    exact lamR_ne_pt hc (he.symm.trans (hPG h Z0 hZ0))
  -- the case's type
  obtain ⟨A', Bo, rfl, hA', hBo, hPo⟩ := den_pi_inv hX
  obtain rfl := (hN _ _ hA').symm
  have hBo' : ∀ n, n ∈ˢ A → ∃ B', Bo n = piR (regime φ s₂.pw) (univ 0) B' ∧
      (∀ y, y ∈ˢ (univ 0 : V) → B' y = univ 0) ∧
      (regime φ s₂.pw = 0 → ∀ y, y ∈ˢ (univ 0 : V) → B' y ∈ˢ univ 0) := by
    intro n hn
    obtain ⟨A₃, B', he, hA₃, hB', hP₃⟩ := den_pi_inv (hBo n hn)
    obtain ⟨f₃, x₃, rfl, hf₃, hx₃⟩ := den_app_inv hA₃
    have hf₃' : f₃ = Mv := den_bvar_inv hf₃
    have hx₃' : x₃ = n := den_bvar_inv hx₃
    rw [hf₃', hx₃', happ n hn] at he hB' hP₃
    refine ⟨B', he, fun y hy => ?_, hP₃⟩
    obtain ⟨f₄, x₄, hB'y, hf₄, hx₄⟩ := den_app_inv (hB' y hy)
    obtain ⟨f₅, x₅, rfl, hf₅, hx₅⟩ := den_app_inv hx₄
    have hf₄' : f₄ = Mv := den_bvar_inv hf₄
    have hf₅' : f₅ = S0 := hS _ _ hf₅
    have hx₅' : x₅ = n := den_bvar_inv hx₅
    rw [hB'y, hf₄', hf₅', hx₅', happ _ (hSN n hn)]
  have hs₂ : regime φ s₂.pw ≠ 0 := by
    intro h
    obtain ⟨B', -, hB'1, hB'0⟩ := hBo' Z0 hZ0
    have he : (empty : V) ∈ˢ (univ 0 : V) := empty_mem_univ 0
    have h' := hB'0 h _ he
    rw [hB'1 _ he] at h'
    exact not_mem_self _ h'
  have hGB : ∀ n, n ∈ˢ A → G n ∈ˢ Bo n := by
    intro n hn
    obtain ⟨F₂, hG₂, hF₂⟩ := hGx n hn
    obtain ⟨B', hBo₂, hB'1, -⟩ := hBo' n hn
    rw [hG₂, hBo₂]
    exact lamR_mem_zero_agree ⟨fun h => absurd h hc, fun h => absurd h hs₂⟩
      (fun y hy => by rw [hF₂ y hy, hB'1 y hy]; exact hTv)
  have hs₁ : regime φ s₁.pw ≠ 0 := by
    intro h
    obtain ⟨F₂, hG₂, -⟩ := hGx Z0 hZ0
    have hmem := hGB Z0 hZ0
    have hpt := eq_pt_of_mem_univZero (by rw [← univ_zero]; exact hPo h Z0 hZ0) hmem
    exact lamR_ne_pt hc (hG₂.symm.trans hpt)
  exact lamR_mem_zero_agree ⟨fun h => absurd h hb, fun h => absurd h hs₁⟩ hGB

/-! ### What `StoredAs` says of each kind -/

theorem storedAs_rec_inv {ci : ConstantInfo .anon} {cv₀ : ConstantVal .anon} {mI rP : Nat}
    {rules₀ : List (RecRule .anon)} (h : StoredAs ci (.recInfo cv₀ mI rP rules₀)) :
    ∃ cv rules, ci = .recInfo cv mI rP rules ∧ ValStored cv cv₀ ∧
      List.Forall₂ RuleStored rules rules₀ := by
  cases ci with
  | recInfo cv mI' rP' rules =>
    obtain ⟨rfl, rfl, hr⟩ := h.2
    exact ⟨cv, rules, rfl, h.1, hr⟩
  | _ => exact False.elim h.2

theorem storedAs_ctor_inv {ci : ConstantInfo .anon} {cv₀ : ConstantVal .anon} {nP nF : Nat}
    (h : StoredAs ci (.ctorInfo cv₀ nP nF)) :
    ∃ cv, ci = .ctorInfo cv nP nF ∧ ValStored cv cv₀ := by
  cases ci with
  | ctorInfo cv nP' nF' =>
    obtain ⟨rfl, rfl⟩ := h.2
    exact ⟨cv, rfl, h.1⟩
  | _ => exact False.elim h.2

theorem storedAs_defn_inv {ci : ConstantInfo .anon} {cv₀ : ConstantVal .anon} {v₀ : Expr .anon}
    {hint : ReducibilityHint} (h : StoredAs ci (.defnInfo cv₀ v₀ hint)) :
    ∃ cv v, ci = .defnInfo cv v hint ∧ ValStored cv cv₀ ∧ Annotates v v₀ := by
  cases ci with
  | defnInfo cv v hint' =>
    obtain ⟨hv, rfl⟩ := h.2
    exact ⟨cv, v, rfl, h.1, hv⟩
  | _ => exact False.elim h.2

theorem storedAs_thm_inv {ci : ConstantInfo .anon} {cv₀ : ConstantVal .anon} {v₀ : Expr .anon}
    (h : StoredAs ci (.thmInfo cv₀ v₀)) : ∃ cv v, ci = .thmInfo cv v ∧ ValStored cv cv₀ := by
  cases ci with
  | thmInfo cv v => exact ⟨cv, v, rfl, h.1⟩
  | _ => exact False.elim h.2

theorem mem_of_find {env : Env .anon} {n : Key .anon} {ci : ConstantInfo .anon}
    (h : env.find? n = some ci) : ci ∈ env.consts :=
  _root_.Ix.Kernel.Semantics.Env.find?_mem h

theorem instSelf1 (e : Expr .anon) :
    e.instantiateLevelParams [BasisDSL.uN] [.param BasisDSL.uN] = e :=
  Expr.instantiateLevelParams_self [BasisDSL.uN] e

/-- The level assignment the example reads at: every universe parameter is `1`. -/
def φ1 : LevelParam → Nat := fun _ => 1

theorem roleKey_ne_aux (r : Role) (k : Key .anon) (t : Derived) :
    (Key.role r : Key .anon) ≠ .aux k t := fun h => by cases h

/-- **ι rules out `P := Nat.rec … 0` read as true.** If `ds` installs `env`, and `ds` holds
the pinned `Nat` block, a constant `T` declared of type `Prop`, the definition
`P := Nat.rec.{1} (fun _ : Nat => Prop) False (fun _ _ => T) 0` (at any binder annotations)
and a theorem of type `P`, at input or role keys, then the claimed sub-environment of `env`
has no model: ι for `Nat.zero` makes `P` denote what `False` denotes. -/
theorem no_model_of_natRec_false_installs {ds : List (Declaration .anon)} {env : Env .anon}
    (hI : Installs ds env) (hNat : ∃ d ∈ ds, installs d = BasisKind.natK.declsA)
    {kT : Key .anon} {ciT₀ : ConstantInfo .anon} (hT : ∃ d ∈ ds, ciT₀ ∈ installs d)
    (hTn : ciT₀.name = kT) (hTty : ciT₀.toConstantVal.type = .sort .zero)
    (hTk : ∀ b t, kT ≠ .aux b t)
    {cvP cvB : ConstantVal .anon} {hint : ReducibilityHint} {v : Expr .anon} {a b c : BinderMeta}
    (hP : .defnDecl cvP (pValue kT a b c) hint ∈ ds) (hB : .thmDecl cvB v ∈ ds)
    (hty : cvB.type = .const cvP.name [])
    (hPk : ∀ b t, cvP.name ≠ .aux b t) (hBk : ∀ b t, cvB.name ≠ .aux b t) :
    Model V (claimedEnv env) → False := by
  intro M
  obtain ⟨dN, hdN, hinsN⟩ := hNat
  -- the stored `Nat.rec`, and its rule for `Nat.zero`
  obtain ⟨dR, mR₁, mR₂, sR₁, sR₂, mR₃, mR₄, e, t₁, t₂, l₁, l₂, l₃, cp, fi, kk, et, pb, rl₁, hRA⟩ :=
    natRecA_shape
  obtain ⟨ciR, hfR, hsR⟩ := hI.claimed hdN (ci₀ := natRecA)
    (by rw [hinsN]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    (by rw [hRA]; exact roleKey_ne_aux _)
  rw [hRA] at hfR hsR
  obtain ⟨⟨nR, lpsR, tyR⟩, rulesR, rfl, hvR, hrR⟩ := storedAs_rec_inv hsR
  simp only [ValStored] at hvR
  obtain ⟨rfl, rfl, hannR⟩ := hvR
  obtain ⟨dR', mR₁', mR₂', sR₁', sR₂', mR₃', mR₄', rfl⟩ := ann_recT hannR
  obtain ⟨rl₀, rl₁', rfl, hrl₀⟩ : ∃ rl₀ rl₁', rulesR = [rl₀, rl₁'] ∧
      RuleStored rl₀ ⟨natZeroName, 0, cp, fi, zeroRhs e t₁ t₂ l₁ l₂ l₃, kk, et, pb⟩ := by
    cases hrR with
    | cons h₀ h₁ =>
      cases h₁ with
      | cons _ h₂ => cases h₂; exact ⟨_, _, rfl, h₀⟩
  obtain ⟨hctor₀, -, hrhs₀⟩ := hrl₀
  obtain ⟨e', t₁', t₂', l₁', l₂', l₃', hrhs₀'⟩ := ann_zeroRhs hrhs₀
  -- the stored `Nat.zero` and `Nat.succ`
  obtain ⟨ciZ, hfZ, hsZ⟩ := hI.claimed hdN (ci₀ := natZeroA)
    (by rw [hinsN]; simp [BasisKind.declsA])
    (by rw [natZeroA_shape]; exact roleKey_ne_aux _)
  rw [natZeroA_shape] at hfZ hsZ
  obtain ⟨⟨nZ, lpsZ, tyZ⟩, rfl, hvZ⟩ := storedAs_ctor_inv hsZ
  simp only [ValStored] at hvZ
  obtain ⟨rfl, rfl, hannZ⟩ := hvZ
  obtain rfl := hannZ.const_inv
  obtain ⟨mS, hSA⟩ := natSuccA_shape
  obtain ⟨ciS, hfS, hsS⟩ := hI.claimed hdN (ci₀ := natSuccA)
    (by rw [hinsN]; simp [BasisKind.declsA])
    (by rw [hSA]; exact roleKey_ne_aux _)
  rw [hSA] at hfS hsS
  obtain ⟨⟨nS, lpsS, tyS⟩, rfl, hvS⟩ := storedAs_ctor_inv hsS
  simp only [ValStored] at hvS
  obtain ⟨rfl, rfl, hannS⟩ := hvS
  obtain ⟨tyS₁, bS, mS', rfl, hS₁, hS₂⟩ := ann_pi hannS
  obtain rfl := hS₁.const_inv
  obtain rfl := hS₂.const_inv
  -- the stored `T`, `P` and the theorem
  obtain ⟨dT, hdT, hciT⟩ := hT
  obtain ⟨ciT, hfT, hsT⟩ := hI.claimed hdT hciT (by rw [hTn]; exact hTk)
  have hannT : Annotates ciT.toConstantVal.type (.sort .zero) := by rw [← hTty]; exact hsT.1.2.2
  have hTname : ciT.name = kT := hsT.name_eq.trans hTn
  obtain ⟨ciP, hfP, hsP⟩ :=
    hI.claimed hP (ci₀ := .defnInfo cvP (pValue kT a b c) hint) (List.mem_singleton_self _) hPk
  obtain ⟨cvP', vP, rfl, hvP, hannP⟩ := storedAs_defn_inv hsP
  obtain ⟨a', b', c', rfl⟩ := ann_pValue hannP
  obtain ⟨ciB, hfB, hsB⟩ := hI.claimed hB (ci₀ := .thmInfo cvB v) (List.mem_singleton_self _) hBk
  obtain ⟨cvB', vB, rfl, hvB⟩ := storedAs_thm_inv hsB
  have hannB : Annotates cvB'.type (.const cvP.name []) := by rw [← hty]; exact hvB.2.2
  -- what the model says of `Nat`, `Nat.zero`, `Nat.succ` and `T`
  have hconst : ∀ {n : Key .anon} {ρ : BVarIdx → V} {X : V},
      Denotes M.cval (claimedEnv env) φ1 ρ (.const n []) X → X = M.cval n φ1 :=
    fun h => (den_const_nil h).1
  obtain ⟨TZ, hTZ, hZmem⟩ := M.mem _ (mem_of_find hfZ) φ1 (fun _ => empty)
  obtain ⟨hTZv, ciN, hfN, hpsN⟩ := den_const_nil hTZ
  have hZ0 : M.cval natZeroName φ1 ∈ˢ M.cval natName φ1 := by rw [← hTZv]; exact hZmem
  obtain ⟨TS, hTS, hSmem⟩ := M.mem _ (mem_of_find hfS) φ1 (fun _ => empty)
  obtain ⟨AS, BS, rfl, hAS, hBS, hPS⟩ := den_pi_inv hTS
  obtain rfl := hconst hAS
  have hSN : ∀ n, n ∈ˢ M.cval natName φ1 → app (M.cval natSuccName φ1) n ∈ˢ M.cval natName φ1 := by
    intro n hn
    rw [← hconst (hBS n hn)]
    exact app_mem_piR hSmem hn (fun hr x hx => by rw [← univ_zero]; exact hPS hr x hx)
  obtain ⟨TT, hTT, hTmem⟩ := M.mem _ (mem_of_find hfT) φ1 (fun _ => empty)
  rw [ann_sort hannT] at hTT
  have hTv : M.cval kT φ1 ∈ˢ (univ 0 : V) := by
    have hTT' : TT = univ 0 := den_sort_inv hTT
    rw [← hTname, ← hTT']; exact hTmem
  -- `P`'s value
  have hval := M.defn_value _ _ hint (mem_of_find hfP) φ1 (fun _ => empty)
  obtain ⟨F₁, L, hPv, hF₁, hL⟩ := den_app_inv hval
  obtain ⟨F₂, Sv, rfl, hF₂, hSv⟩ := den_app_inv hF₁
  obtain ⟨F₃, Fv, rfl, hF₃, hFv⟩ := den_app_inv hF₂
  obtain ⟨Rv, Mv, rfl, hRv, hMv⟩ := den_app_inv hF₃
  have hFv0 : Fv = empty := M.false_empty _ _ _ hFv
  have hL0 : L = M.cval natZeroName φ1 := hconst (den_natLit_inv hL)
  have hRv' : Rv = M.cval natRecName (Level.substFn φ1 [BasisDSL.uN] [.succ .zero]) := by
    cases hRv with
    | @const _ _ _ ci hf _ => obtain rfl := Option.some.inj (hfR.symm.trans hf); rfl
  obtain ⟨happ, hmot⟩ := mot_facts (fun _ _ h => hconst h) hZ0 hMv
  -- the recursor's type, read at the motive, the zero case and the successor case
  obtain ⟨TR, hTR, -⟩ := M.mem _ (mem_of_find hfR) φ1 (fun _ => empty)
  obtain ⟨X₁, B₁, -, hX₁, hB₁, -⟩ := den_pi_inv hTR
  have hMvX₁ : Mv ∈ˢ X₁ := hmot rfl _ _ _ hX₁
  obtain ⟨X₂, B₂, -, hX₂, hB₂, -⟩ := den_pi_inv (hB₁ Mv hMvX₁)
  have hFvX₂ : Fv ∈ˢ X₂ := by rw [hFv0]; exact zero_mem (fun _ _ h => hconst h) hZ0 happ hX₂
  obtain ⟨X₃, B₃, -, hX₃, hB₃, -⟩ := den_pi_inv (hB₂ Fv hFvX₂)
  have hsucc := fun {ρ' : BVarIdx → V} {s₁ s₂ : BinderMeta} {X : V}
      (hX : Denotes M.cval (claimedEnv env) φ1 (push Fv (push Mv ρ')) (succT s₁ s₂) X) =>
    succ_mem (fun _ _ h => hconst h) hZ0 (fun _ _ h => hconst h) hSN (fun _ _ h => hconst h) hTv
      happ hSv hX
  have hSvX₃ : Sv ∈ˢ X₃ := hsucc hX₃
  have hfits : Fits M.cval (claimedEnv env) φ1 (fun _ => empty)
      ((recT dR' mR₁' mR₂' sR₁' sR₂' mR₃' mR₄').instantiateLevelParams [BasisDSL.uN]
        [.param BasisDSL.uN])
      [Mv, Fv, Sv] (push Sv (push Fv (push Mv (fun _ => empty))))
      (.forallE (.const natName []) (.app (.bvar 3) (.bvar 0)) mR₄') := by
    rw [instSelf1]
    exact .cons hX₁ hMvX₁ (.cons hX₂ hFvX₂ (.cons hX₃ hSvX₃ .nil))
  -- ι for `Nat.zero`
  obtain ⟨H, hH, heq⟩ := M.iota_rule natRecName _ 3 3 _ rl₀ hfR (by simp)
    ⟨natZeroName, [], .const natName []⟩ 0 0 (by rw [hctor₀]; exact hfZ)
    [.param BasisDSL.uN] φ1 (fun _ => empty) _ (fun _ => empty) [Mv, Fv, Sv] []
    (.const natName []) _ _ mR₄' natName [] _ (M.cval natZeroName φ1) (M.cval natName φ1)
    rfl rfl rfl (Denotes.const hfR rfl) hfits rfl (den_const_nil_intro hfN hpsN)
    (by rw [hctor₀]; exact den_const_nil_intro hfZ rfl) .nil hZ0 .nil .nil
  have heq' : app (app (app (app (M.cval natRecName
      (Level.substFn φ1 [BasisDSL.uN] [.param BasisDSL.uN])) Mv) Fv) Sv) (M.cval natZeroName φ1)
      = app (app (app H Mv) Fv) Sv := heq
  -- the right-hand side `fun motive zero succ => zero` returns the zero case
  have hH' : Denotes M.cval (claimedEnv env) φ1 (fun _ => empty)
      ((zeroRhs e' t₁' t₂' l₁' l₂' l₃').instantiateLevelParams [BasisDSL.uN]
        [.param BasisDSL.uN]) H := by
    rw [← hrhs₀']; exact hH
  rw [instSelf1] at hH'
  obtain ⟨A₇, F₇, rfl, hA₇, hF₇, hP₇⟩ := den_lam_inv hH'
  have hMv₇ : Mv ∈ˢ A₇ := hmot rfl _ _ _ hA₇
  obtain ⟨A₈, F₈, hF₇e, hA₈, hF₈, hP₈⟩ := den_lam_inv (hF₇ Mv hMv₇)
  have hFv₈ : Fv ∈ˢ A₈ := by rw [hFv0]; exact zero_mem (fun _ _ h => hconst h) hZ0 happ hA₈
  obtain ⟨A₉, F₉, hF₈e, hA₉, hF₉, hP₉⟩ := den_lam_inv (hF₈ Fv hFv₈)
  have hSv₉ : Sv ∈ˢ A₉ := hsucc hA₉
  have hF₉e : F₉ Sv = Fv := den_bvar_inv (hF₉ Sv hSv₉)
  have hr₉ : regime φ1 l₃'.pw ≠ 0 := fun h =>
    pt_ne_empty ((hP₉ h Sv hSv₉).symm.trans (hF₉e.trans hFv0))
  have hr₈ : regime φ1 l₂'.pw ≠ 0 := fun h =>
    lamR_ne_pt hr₉ (hF₈e.symm.trans (hP₈ h Fv hFv₈))
  have hr₇ : regime φ1 l₁'.pw ≠ 0 := fun h =>
    lamR_ne_pt hr₈ (hF₇e.symm.trans (hP₇ h Mv hMv₇))
  have hH0 : app (app (app (lamR (regime φ1 l₁'.pw) A₇ F₇) Mv) Fv) Sv = empty := by
    rw [app_lamR_pos hr₇ hMv₇, hF₇e, app_lamR_pos hr₈ hFv₈, hF₈e, app_lamR_pos hr₉ hSv₉, hF₉e,
      hFv0]
  -- so `P` denotes the empty set, and the theorem cannot be a member of it
  have hRR : M.cval natRecName (Level.substFn φ1 [BasisDSL.uN] [.succ .zero]) =
      M.cval natRecName (Level.substFn φ1 [BasisDSL.uN] [.param BasisDSL.uN]) :=
    M.cval_params _ _ hfR _ _ (fun p hp => by
      simp only [ConstantInfo.toConstantVal, List.mem_singleton] at hp
      subst hp
      first | rfl | simp [Level.substFn, Level.eval, φ1])
  have hP0 : M.cval cvP'.name φ1 = empty := by
    rw [hPv, hL0, hRv', hRR, heq', hH0]
  obtain ⟨TB, hTB, hBmem⟩ := M.mem _ (mem_of_find hfB) φ1 (fun _ => empty)
  have hTB2 : Denotes M.cval (claimedEnv env) φ1 (fun _ => empty) cvB'.type TB := hTB
  rw [hannB.const_inv] at hTB2
  have hTB' : TB = M.cval cvP.name φ1 := hconst hTB2
  rw [hTB', ← hvP.1, hP0] at hBmem
  exact not_mem_empty _ hBmem

open _root_.IxVM.Consistency in
/-- **No `ConsistentRead` reads `P := Nat.rec … 0` with a theorem of type `P`**: in every
set theory, the reading a `ConsistentRead` exhibits, if it holds the pinned `Nat` block
and a proposition `T`, holds no such pair at input or role keys. -/
theorem consistentRead_no_natRec_false (V : Type w) [SetTheory V]
    {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {seeds : List _root_.Address}
    (h : ConsistentRead.{w} calls seeds) :
    ∃ (b : _root_.Ix.Kernel.Admission.Binding) (E : _root_.Ixon.Env) (ev : Evidences .anon)
      (ds : Array (Declaration .anon)),
      ReadIn b E (fun a => a ∈ seeds) ev ds ∧
      ∀ (kT : Key .anon) (ciT₀ : ConstantInfo .anon) (cvP cvB : ConstantVal .anon)
        (hint : ReducibilityHint) (v : Expr .anon) (a b c : BinderMeta),
        (∃ d ∈ ds.toList, installs d = BasisKind.natK.declsA) →
        (∃ d ∈ ds.toList, ciT₀ ∈ installs d) → ciT₀.name = kT →
        ciT₀.toConstantVal.type = .sort .zero → (∀ b t, kT ≠ .aux b t) →
        .defnDecl cvP (pValue kT a b c) hint ∈ ds.toList → .thmDecl cvB v ∈ ds.toList →
        cvB.type = .const cvP.name [] → (∀ b t, cvP.name ≠ .aux b t) →
        (∀ b t, cvB.name ≠ .aux b t) → False := by
  obtain ⟨b, -, E, ev, ds, env, -, -, -, hread, hI, -, hmodel⟩ := h
  obtain ⟨M⟩ := hmodel V
  exact ⟨b, E, ev, ds, hread, fun _ _ _ _ _ _ _ _ _ hNat hT hTn hTty hTk hP hB hty hPk hBk =>
    no_model_of_natRec_false_installs hI hNat hT hTn hTty hTk hP hB hty hPk hBk M⟩

end NatRec

/--
info: 'Tests.Ix.Kernel.ModelLaws.consistentRead_no_natRec_false' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms consistentRead_no_natRec_false

end Tests.Ix.Kernel.ModelLaws
