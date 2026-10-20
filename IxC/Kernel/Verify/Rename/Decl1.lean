module

public import IxC.Kernel.Verify.Rename.Pins
public import IxC.Kernel.CheckerBase

@[expose] public section

/-!
# The renaming walk through the declaration checker's helpers

The declaration checker's results are environments, and the renamed run's
environment is not a function of the original's alone (it extends the renamed
starting environment), so the declaration-level walk is relational:
`SimR R x x'` says every success of `x` is matched by a success of `x'`
related by `R`. The environments are related by `EnvRel`, which a push of a
good constant (and its renaming) preserves (`EnvRel.push`).

Then the telescope views' goodness, the evidence the fold receives at renamed
keys, and the helpers of `IxC/Kernel/CheckerBase.lean` at renamed arguments,
over any operation records related by `OpsSim` (the pure record at every fuel
is, `fueledOps_sim`).
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}

/-! ## Relational success simulation -/

/-- **Relational success simulation**: every success of `x` is matched by a
success of `x'`, the two related by `R`. -/
def SimR {ε ε' α α' : Type} (R : α → α' → Prop) (x : Except ε α) (x' : Except ε' α') : Prop :=
  ∀ a, x = .ok a → ∃ a', x' = .ok a' ∧ R a a'

namespace SimR

variable {ε ε' α α' β β' : Type} {R : α → α' → Prop}

theorem pure' {a : α} {a' : α'} (h : R a a') : SimR R (pure a : Except ε α) (pure a' : Except ε' α') :=
  fun _ hb => by cases hb; exact ⟨a', rfl, h⟩

theorem throw' {e : ε} {x' : Except ε' α'} : SimR R (throw e : Except ε α) x' :=
  fun _ h => nomatch h

theorem throw_bind {γ : Type} {e : ε} {k : γ → Except ε α} {x' : Except ε' α'} :
    SimR R ((throw e : Except ε γ) >>= k) x' :=
  fun _ h => nomatch h

theorem of_fail {x : Except ε α} {x' : Except ε' α'} (h : ∀ a, x ≠ .ok a) : SimR R x x' :=
  fun a ha => absurd ha (h a)

/-- Peel one bind whose first run is simulated functionally. -/
theorem bindE {G : β → Prop} {m : β → β'} {x : Except ε β} {x' : Except ε' β'}
    {k : β → Except ε α} {k' : β' → Except ε' α'} (hx : SimE G m x x')
    (hk : ∀ b, G b → SimR R (k b) (k' (m b))) : SimR R (x >>= k) (x' >>= k') := by
  intro a ha
  cases hxb : x with
  | error e => rw [hxb] at ha; exact nomatch ha
  | ok b =>
    rw [hxb] at ha
    obtain ⟨hG, hx'⟩ := hx b hxb
    rw [hx']
    exact hk b hG a ha

/-- Peel one bind whose first run is simulated relationally. -/
theorem bind {R₁ : β → β' → Prop} {x : Except ε β} {x' : Except ε' β'}
    {k : β → Except ε α} {k' : β' → Except ε' α'} (hx : SimR R₁ x x')
    (hk : ∀ b b', R₁ b b' → SimR R (k b) (k' b')) : SimR R (x >>= k) (x' >>= k') := by
  intro a ha
  cases hxb : x with
  | error e => rw [hxb] at ha; exact nomatch ha
  | ok b =>
    rw [hxb] at ha
    obtain ⟨b', hx', hR⟩ := hx b hxb
    rw [hx']
    exact hk b b' hR a ha

theorem ite {c c' : Prop} [Decidable c] [Decidable c'] {t e : Except ε α} {t' e' : Except ε' α'}
    (hc : c ↔ c') (ht : c → SimR R t t') (he : ¬c → SimR R e e') :
    SimR R (if c then t else e) (if c' then t' else e') := by
  by_cases h : c
  · rw [if_pos h, if_pos (hc.mp h)]; exact ht h
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]; exact he h

theorem congr {x : Except ε α} {x'₁ x'₂ : Except ε' α'} (h : x'₁ = x'₂) (hs : SimR R x x'₁) :
    SimR R x x'₂ :=
  h ▸ hs

theorem mono {R' : α → α' → Prop} {x : Except ε α} {x' : Except ε' α'}
    (hR : ∀ a a', R a a' → R' a a') (hs : SimR R x x') : SimR R' x x' :=
  fun a h => let ⟨a', h', hr⟩ := hs a h; ⟨a', h', hR a a' hr⟩

/-- A functional simulation is a relational one. -/
theorem ofE {G : α → Prop} {m : α → α'} {x : Except ε α} {x' : Except ε' α'} (h : SimE G m x x')
    (hR : ∀ a, G a → R a (m a)) : SimR R x x' :=
  fun a ha => let ⟨hg, h'⟩ := h a ha; ⟨m a, h', hR a hg⟩

end SimR

/-! ## Environments extended by a good constant -/

/-- **A push of a good constant** (and of its renaming) keeps two related
environments related. -/
theorem EnvRel.push {env : Env md} {env' : Env md'} (hE : EnvRel P f env env')
    {c : ConstantInfo md} (hc : c.Good P) :
    EnvRel P f ⟨c :: env.consts⟩ ⟨c.mapKeys f :: env'.consts⟩ where
  inj := hE.inj
  all d hd := by
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hE.all d hd
  eq := by rw [hE.eq]; rfl

/-! ## Telescope views of good terms -/

/-- A good binder list. -/
def Expr.BindersGood (P : md.Id → Prop) (bs : List (Expr md × BinderMeta)) : Prop :=
  ∀ b ∈ bs, b.1.Good P

theorem Expr.stripPis_good : ∀ {k : Nat} {e : Expr md} {bs : List (Expr md × BinderMeta)}
    {b : Expr md}, e.Good P → Expr.stripPis k e = some (bs, b) → Expr.BindersGood P bs ∧ b.Good P
  | 0, e, bs, b, he, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ h => (nomatch h), he⟩
  | k + 1, .forallE ty body m, bs, b, he, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨bs₀, b₀⟩, h₀, rfl, rfl⟩ := h
    simp only [Expr.Good] at he
    obtain ⟨hbs, hb⟩ := Expr.stripPis_good he.2 h₀
    refine ⟨?_, hb⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he.1
    · exact hbs x hx
  | _ + 1, .bvar _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, h | _ + 1, .sort _, _, _, _, h
  | _ + 1, .const _ _, _, _, _, h | _ + 1, .app _ _, _, _, _, h | _ + 1, .lam _ _ _, _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, _, h | _ + 1, .lit _, _, _, _, h | _ + 1, .proj _ _ _, _, _, _, h =>
    nomatch h

theorem Expr.stripLams_good : ∀ {k : Nat} {e : Expr md} {bs : List (Expr md × BinderMeta)}
    {b : Expr md}, e.Good P → Expr.stripLams k e = some (bs, b) → Expr.BindersGood P bs ∧ b.Good P
  | 0, e, bs, b, he, h => by
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ h => (nomatch h), he⟩
  | k + 1, .lam ty body m, bs, b, he, h => by
    simp only [Expr.stripLams, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨bs₀, b₀⟩, h₀, rfl, rfl⟩ := h
    simp only [Expr.Good] at he
    obtain ⟨hbs, hb⟩ := Expr.stripLams_good he.2 h₀
    refine ⟨?_, hb⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he.1
    · exact hbs x hx
  | _ + 1, .bvar _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, h | _ + 1, .sort _, _, _, _, h
  | _ + 1, .const _ _, _, _, _, h | _ + 1, .app _ _, _, _, _, h | _ + 1, .forallE _ _ _, _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, _, h | _ + 1, .lit _, _, _, _, h | _ + 1, .proj _ _ _, _, _, _, h =>
    nomatch h

theorem Expr.instPisAt_good : ∀ {as : List (Expr md)} {e : Expr md} {ds : List (Expr md)}
    {r : Expr md}, Expr.GoodList P as → e.Good P → Expr.instPisAt as e = some (ds, r) →
      Expr.GoodList P ds ∧ r.Good P
  | [], e, ds, r, _, he, h => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, he⟩
  | a :: as, .forallE dom body m, ds, r, has, he, h => by
    simp only [Expr.instPisAt, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨ds₀, r₀⟩, h₀, rfl, rfl⟩ := h
    simp only [Expr.goodList_cons] at has
    simp only [Expr.Good] at he
    obtain ⟨hds, hr⟩ := Expr.instPisAt_good has.2 (Expr.Good.instantiate1 he.2 has.1 0) h₀
    exact ⟨by simp [he.1, hds], hr⟩
  | _ :: _, .bvar _, _, _, _, _, h | _ :: _, .fvar _ _, _, _, _, _, h
  | _ :: _, .sort _, _, _, _, _, h | _ :: _, .const _ _, _, _, _, _, h
  | _ :: _, .app _ _, _, _, _, _, h | _ :: _, .lam _ _ _, _, _, _, _, h
  | _ :: _, .letE _ _ _ _, _, _, _, _, h | _ :: _, .lit _, _, _, _, _, h
  | _ :: _, .proj _ _ _, _, _, _, _, h => nomatch h

theorem Expr.instLamsAt_good : ∀ {as : List (Expr md)} {e : Expr md} {ds : List (Expr md)}
    {r : Expr md}, Expr.GoodList P as → e.Good P → Expr.instLamsAt as e = some (ds, r) →
      Expr.GoodList P ds ∧ r.Good P
  | [], e, ds, r, _, he, h => by
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, he⟩
  | a :: as, .lam dom body m, ds, r, has, he, h => by
    simp only [Expr.instLamsAt, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨ds₀, r₀⟩, h₀, rfl, rfl⟩ := h
    simp only [Expr.goodList_cons] at has
    simp only [Expr.Good] at he
    obtain ⟨hds, hr⟩ := Expr.instLamsAt_good has.2 (Expr.Good.instantiate1 he.2 has.1 0) h₀
    exact ⟨by simp [he.1, hds], hr⟩
  | _ :: _, .bvar _, _, _, _, _, h | _ :: _, .fvar _ _, _, _, _, _, h
  | _ :: _, .sort _, _, _, _, _, h | _ :: _, .const _ _, _, _, _, _, h
  | _ :: _, .app _ _, _, _, _, _, h | _ :: _, .forallE _ _ _, _, _, _, _, h
  | _ :: _, .letE _ _ _ _, _, _, _, _, h | _ :: _, .lit _, _, _, _, _, h
  | _ :: _, .proj _ _ _, _, _, _, _, h => nomatch h

theorem Expr.pisToLams_good : ∀ {k : Nat} {e b r : Expr md}, e.Good P → b.Good P →
    Expr.pisToLams k e b = some r → r.Good P
  | 0, _, b, r, _, hb, h => by
    simp only [Expr.pisToLams, Option.some.injEq] at h; exact h ▸ hb
  | k + 1, .forallE ty rest m, b, r, he, hb, h => by
    simp only [Expr.pisToLams, Option.map_eq_some_iff] at h
    obtain ⟨r₀, h₀, rfl⟩ := h
    simp only [Expr.Good] at he
    exact ⟨he.1, Expr.pisToLams_good he.2 hb h₀⟩
  | _ + 1, .bvar _, _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, _, h | _ + 1, .sort _, _, _, _, _, h
  | _ + 1, .const _ _, _, _, _, _, h | _ + 1, .app _ _, _, _, _, _, h
  | _ + 1, .lam _ _ _, _, _, _, _, h | _ + 1, .letE _ _ _ _, _, _, _, _, h
  | _ + 1, .lit _, _, _, _, _, h | _ + 1, .proj _ _ _, _, _, _, _, h => nomatch h

/-- `openPisAtFvars` at a renamed telescope. -/
theorem openPisAtFvars_mapKeys : ∀ (n : Nat) (e : Expr md) (i : Nat),
    openPisAtFvars n (e.mapKeys f) i = (openPisAtFvars n e i).map (Expr.mapDoms f)
  | 0, e, i => rfl
  | n + 1, .forallE dom body m, i => by
    simp only [Expr.mapKeys, openPisAtFvars]
    have h := openPisAtFvars_mapKeys n (body.instantiate1 (.fvar i dom)) (i + 1)
    simp only [Expr.mapKeys_instantiate1, Expr.mapKeys] at h
    rw [h]
    cases openPisAtFvars n (body.instantiate1 (.fvar i dom)) (i + 1) <;> rfl
  | _ + 1, .bvar _, _ | _ + 1, .fvar _ _, _ | _ + 1, .sort _, _ | _ + 1, .const _ _, _
  | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _, _ | _ + 1, .letE _ _ _ _, _ | _ + 1, .lit _, _
  | _ + 1, .proj _ _ _, _ => rfl

theorem Expr.openPisAtFvars_good : ∀ {n : Nat} {e : Expr md} {i : Nat} {fvs : List (Expr md)}
    {r : Expr md}, e.Good P → Ix.Kernel.openPisAtFvars n e i = some (fvs, r) →
      Expr.GoodList P fvs ∧ r.Good P
  | 0, e, i, fvs, r, he, h => by
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, he⟩
  | n + 1, .forallE dom body m, i, fvs, r, he, h => by
    simp only [Ix.Kernel.openPisAtFvars] at h
    simp only [Expr.Good] at he
    have hfv : (Expr.fvar i dom : Expr md).Good P := by simpa using he.1
    split at h
    · rename_i fvs₀ r₀ h₀
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hfvs, hr⟩ := Expr.openPisAtFvars_good (Expr.Good.instantiate1 he.2 hfv 0) h₀
      exact ⟨by simp [he.1, hfvs], hr⟩
    · exact nomatch h
  | _ + 1, .bvar _, _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, _, h
  | _ + 1, .sort _, _, _, _, _, h | _ + 1, .const _ _, _, _, _, _, h
  | _ + 1, .app _ _, _, _, _, _, h | _ + 1, .lam _ _ _, _, _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, _, _, h | _ + 1, .lit _, _, _, _, _, h
  | _ + 1, .proj _ _ _, _, _, _, _, h => nomatch h

/-! ## The evidence at renamed keys -/

@[simp] theorem opRole?_map (c : Key md) : opRole? (c.map f) = opRole? c := by
  simp only [opRole?, Key.map_eq_role_iff]

@[simp] theorem Evidence.isDefeqKind_mapKeys (e : Evidence (Key md × Expr md)) (b : Bool) :
    (e.mapKeys f).isDefeqKind b = e.isDefeqKind b := by
  cases e <;> rfl

theorem evidenceDefeqOk_ren (ev : Evidences md) (c : Key md) :
    evidenceDefeqOk (ev.mapKeys f) (c.map f) = evidenceDefeqOk ev c := by
  unfold evidenceDefeqOk
  rw [opRole?_map]
  cases opRole? c with
  | none => rfl
  | some r =>
    simp only [Evidences.mapKeys_of, List.length_map, natOpEquations_map, List.all_map,
      Function.comp_def, Evidence.isDefeqKind_mapKeys]

@[simp] theorem divModCertStmts_map (c : Key md) :
    divModCertStmts (c.map f) =
      (divModCertStmts c).map fun p => (p.1.map (Expr.mapKeys f), p.2.mapKeys f) := by
  simp only [divModCertStmts, Key.map_eq_role_iff, apply_ite (List.map _), List.map_cons,
    List.map_nil, Expr.mapKeys, Key.map_role, apply_ite (Expr.mapKeys f)]

theorem Option.cons_map {α β : Type} (g : α → β) (a : α) (o : Option (List α)) :
    (do let x ← some (g a); let l ← Option.map (List.map g) o; pure (x :: l)) =
      Option.map (List.map g) (do let x ← some a; let l ← o; pure (x :: l)) := by
  cases o <;> rfl

theorem evidenceProofs_ren (ev : Evidences md) (c : Key md) :
    evidenceProofs (ev.mapKeys f) (c.map f) = (evidenceProofs ev c).map (List.map (Expr.mapKeys f)) := by
  unfold evidenceProofs
  rw [opRole?_map]
  cases opRole? c with
  | none => rfl
  | some r =>
    simp only [Evidences.mapKeys_of, List.length_map, divModCertStmts_map]
    split
    · generalize ev.of r = es
      induction es with
      | nil => rfl
      | cons e es ih =>
        cases e with
        | defeq => rfl
        | proof p =>
          obtain ⟨k, v⟩ := p
          simp only [List.map_cons, List.mapM_cons, Evidence.mapKeys.eq_2]
          rw [ih]
          exact Option.cons_map _ _ _
    · rfl

theorem Option.cons_some {α : Type} {a : α} {o : Option (List α)} {l : List α}
    (h : (do let x ← some a; let t ← o; pure (x :: t)) = some l) : ∃ t, o = some t ∧ l = a :: t := by
  cases o with
  | none => exact nomatch h
  | some t => cases h; exact ⟨t, rfl, rfl⟩

theorem evidenceProofs_good {ev : Evidences md} (hev : ev.Good P) {c : Key md}
    {ps : List (Expr md)} (h : evidenceProofs ev c = some ps) : Expr.GoodList P ps := by
  unfold evidenceProofs at h
  cases hr : opRole? c with
  | none => rw [hr] at h; exact nomatch h
  | some r =>
    rw [hr] at h
    simp only at h
    split at h
    · have hg := hev.of r
      generalize ev.of r = es at h hg
      induction es generalizing ps with
      | nil => simp only [List.mapM_nil] at h; cases h; simp
      | cons e es ih =>
        simp only [List.mem_cons, forall_eq_or_imp] at hg
        cases e with
        | defeq => simp only [List.mapM_cons] at h; exact nomatch h
        | proof p =>
          obtain ⟨k, v⟩ := p
          simp only [List.mapM_cons] at h
          obtain ⟨t, ht, rfl⟩ := Option.cons_some h
          simp only [Evidence.Good.eq_2] at hg
          simp [hg.1.2, ih ht hg.2]
    · exact nomatch h

/-! ## The helpers of the declaration checker -/

section Helpers

variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

theorem checkConstantVal_sim (hops : OpsSim P f ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') {cv : ConstantVal md} (hcv : cv.Good P) :
    SimE (ConstantVal.Good P) (ConstantVal.mapKeys f) (checkConstantVal ops env cv)
      (checkConstantVal ops' env' (cv.mapKeys f)) := by
  unfold checkConstantVal
  simp only [ConstantVal.mapKeys_name, ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
    hE.find_isSome hcv.1, reservedBasisNames_contains_map, Key.map_isProjFnShape,
    Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys, Expr.allLevelParamsDefined_mapKeys]
  refine SimE.ite Iff.rfl (fun _ => SimE.throw_bind) (fun _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => SimE.throw_bind) (fun _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => SimE.throw_bind) (fun _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.ite Iff.rfl (fun _ => SimE.throw_bind) (fun _ => ?_)
  refine SimE.bind (hops.annotate hE 0 cv.type hcv.2) (fun type ht => ?_)
  refine SimE.ite (by simp) (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.ite (by rw [constsResolve_ren hE ht]) (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.bind (hops.inferType hE 0 type ht) (fun stype hst => ?_)
  refine SimE.bind (hops.ensureSort hE 0 stype hst) (fun _ _ => ?_)
  exact SimE.pure' ⟨hcv.1, ht⟩ rfl

theorem domsMatchAux_ren {g : Nat → Expr md → Expr md} {g' : Nat → Expr md' → Expr md'}
    (hg : ∀ i e, e.Good P → (g i e).mapKeys f = g' i (e.mapKeys f))
    (hgg : ∀ i e, e.Good P → (g i e).Good P) (hf : InjOn f P)
    {bs₁ bs₂ : List (Expr md × BinderMeta)} (h₁ : Expr.BindersGood P bs₁)
    (h₂ : Expr.BindersGood P bs₂) (o₁ o₂ n : Nat) :
    domsMatchAux g' (Expr.mapBinders f bs₁) (Expr.mapBinders f bs₂) o₁ o₂ n =
      domsMatchAux g bs₁ bs₂ o₁ o₂ n := by
  unfold domsMatchAux
  apply List.all_congr_mem
  intro i _
  simp only [Expr.mapBinders, List.getElem?_map]
  cases hb₁ : bs₁[o₁ + i]? with
  | none => rfl
  | some b₁ =>
    cases hb₂ : bs₂[o₂ + i]? with
    | none => rfl
    | some b₂ =>
      have g₁ := h₁ b₁ (List.mem_of_getElem? hb₁)
      have g₂ := h₂ b₂ (List.mem_of_getElem? hb₂)
      simp only [Option.map_some]
      rw [← hg i b₂.1 g₂, Expr.mapKeys_beq hf g₁ (hgg i _ g₂)]

theorem checkTypedList_sim (hops : OpsSim P f ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') (d : Nat) :
    ∀ (as ts : List (Expr md)), Expr.GoodList P as → Expr.GoodList P ts →
      SimV (checkTypedList ops env d as ts)
        (checkTypedList ops' env' d (as.map (Expr.mapKeys f)) (ts.map (Expr.mapKeys f)))
  | [], [], _, _ => SimV.pureT ()
  | [], _ :: _, _, _ => SimE.throw'
  | _ :: _, [], _, _ => SimE.throw'
  | a :: as, t :: ts, has, hts => by
    simp only [Expr.goodList_cons] at has hts
    simp only [List.map_cons, checkTypedList]
    refine SimE.bind (hops.inferType hE d a has.1) (fun ty hty => ?_)
    refine SimE.bind (hops.isDefEq hE d ty t hty hts.1) (fun b _ => ?_)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
    exact checkTypedList_sim hops hE d as ts has.2 hts.2

theorem checkAnnotList_sim (hops : OpsSim P f ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') (d : Nat) :
    ∀ (as : List (Expr md)), Expr.GoodList P as →
      SimV (checkAnnotList ops env d as) (checkAnnotList ops' env' d (as.map (Expr.mapKeys f)))
  | [], _ => SimV.pureT ()
  | a :: as, has => by
    simp only [Expr.goodList_cons] at has
    simp only [List.map_cons, checkAnnotList]
    refine SimE.bind (hops.annotate hE d a has.1) (fun aA haA => ?_)
    refine SimE.ite (by rw [Expr.mapKeys_beq hE.inj haA has.1]) (fun _ => ?_)
      (fun _ => SimE.throw_bind)
    exact checkAnnotList_sim hops hE d as has.2

theorem checkDefEqList_sim (hops : OpsSim P f ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') (d : Nat) :
    ∀ (as bs : List (Expr md)), Expr.GoodList P as → Expr.GoodList P bs →
      SimV (checkDefEqList ops env d as bs)
        (checkDefEqList ops' env' d (as.map (Expr.mapKeys f)) (bs.map (Expr.mapKeys f)))
  | [], [], _, _ => SimV.pureT ()
  | [], _ :: _, _, _ => SimE.throw'
  | _ :: _, [], _, _ => SimE.throw'
  | a :: as, b :: bs, has, hbs => by
    simp only [Expr.goodList_cons] at has hbs
    simp only [List.map_cons, checkDefEqList]
    refine SimE.bind (hops.isDefEq hE d a b has.1 hbs.1) (fun c _ => ?_)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
    exact checkDefEqList_sim hops hE d as bs has.2 hbs.2

theorem checkProjShape_sim (pty ctorTy : Expr md)
    (nP nF : Nat) :
    SimV (checkProjShape pty ctorTy nP nF : CheckM md Unit)
      (checkProjShape (pty.mapKeys f) (ctorTy.mapKeys f) nP nF : CheckM md' Unit) := by
  unfold checkProjShape
  simp only [Expr.stripPis_mapKeys]
  cases h₁ : Expr.stripPis nP pty with
  | none => exact SimE.throw'
  | some p =>
    obtain ⟨_, _⟩ := p
    cases h₂ : Expr.stripPis (nP + nF) ctorTy with
    | none => exact SimE.throw'
    | some q =>
      obtain ⟨cbs, cbody⟩ := q
      simp only [Option.map_some, Expr.mapTele, Expr.getAppArgs_mapKeys, List.length_map]
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
      rw [← Expr.mapKeys_getAppFn]
      cases Expr.getAppFn cbody <;> first | exact SimV.pureT () | exact SimE.throw'

@[simp] theorem Expr.mapKeys_beq_bvar' (e : Expr md) (k : Nat) :
    (e.mapKeys f == Expr.bvar k) = (e == Expr.bvar k) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Expr.mapKeys_eq_bvar_iff]

theorem map_fvarTypeD_mapKeys (as : List (Expr md)) :
    (as.map (Expr.mapKeys f)).map Expr.fvarTypeD = (as.map Expr.fvarTypeD).map (Expr.mapKeys f) := by
  simp [List.map_map, Function.comp_def]

theorem Expr.GoodList.map_fvarTypeD {as : List (Expr md)} (h : Expr.GoodList P as) :
    Expr.GoodList P (as.map Expr.fvarTypeD) := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [Expr.goodList_cons] at h
    simp [h.1.fvarTypeD, ih h.2]

theorem checkProjRule_sim (hops : OpsSim P f ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') {pty : Expr md} (hp : pty.Good P) {cvj : ConstantVal md}
    (hcv : cvj.Good P) (lps : List LevelParam) (nP nF i : Nat) :
    SimX P f (checkProjRule ops env pty cvj lps nP nF i)
      (checkProjRule ops' env' (pty.mapKeys f) (cvj.mapKeys f) lps nP nF i) := by
  unfold checkProjRule
  have hpl : Expr.pisToLams (nP + nF) ((cvj.mapKeys f).type) (.bvar (nF - 1 - i)) =
      (Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i))).map (Expr.mapKeys f) :=
    Expr.pisToLams_mapKeys (nP + nF) cvj.type (.bvar (nF - 1 - i))
  rw [hpl]
  cases h₁ : Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) with
  | none => exact SimE.throw'
  | some rhs =>
  have hrhs : rhs.Good P := Expr.pisToLams_good (b := .bvar (nF - 1 - i)) hcv.2 trivial h₁
  simp only [Option.map_some, Expr.hasFvar_mapKeys, Expr.looseBVarsBounded_mapKeys,
    ConstantVal.mapKeys_type]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.bind (hops.annotate hE 0 rhs hrhs) (fun rhsA hA => ?_)
  refine SimE.ite (by simp [constsResolve_ren hE hA]) (fun _ => ?_) (fun _ => SimE.throw_bind)
  simp only [Expr.stripLams_mapKeys]
  cases h₂ : Expr.stripLams (nP + nF) rhsA with
  | none => exact SimE.throw'
  | some p =>
  obtain ⟨rb, rr⟩ := p
  obtain ⟨hrb, hrr⟩ := Expr.stripLams_good hA h₂
  simp only [Option.map_some, Expr.mapTele, Expr.mapKeys_beq_bvar']
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  simp only [Expr.stripPis_mapKeys]
  cases h₃ : Expr.stripPis (nP + nF) cvj.type with
  | none => exact SimE.throw'
  | some q =>
  obtain ⟨cb, cr⟩ := q
  obtain ⟨hcb, _⟩ := Expr.stripPis_good hcv.2 h₃
  simp only [Option.map_some, Expr.mapTele]
  rw [domsMatchAux_ren (g := fun _ e => e) (fun _ _ _ => rfl) (fun _ _ h => h) hE.inj hrb hcb]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  rw [openPisAtFvars_mapKeys]
  cases h₄ : openPisAtFvars nP pty 0 with
  | none => exact SimE.throw'
  | some s =>
  obtain ⟨fvsP, rP⟩ := s
  obtain ⟨hfvs, _⟩ := Expr.openPisAtFvars_good hp h₄
  simp only [Option.map_some, Expr.mapDoms, Expr.instPisAt_mapKeys]
  cases h₅ : Expr.instPisAt fvsP cvj.type with
  | none => exact SimE.throw'
  | some t =>
  obtain ⟨cdomsP, crestP⟩ := t
  obtain ⟨hcd, hcr⟩ := Expr.instPisAt_good hfvs hcv.2 h₅
  simp only [Option.map_some, Expr.mapDoms]
  refine SimE.bind (SimE.congr (by rw [map_fvarTypeD_mapKeys])
    (checkDefEqList_sim hops hE (nP + nF) _ _ hfvs.map_fvarTypeD hcd)) (fun _ _ => ?_)
  rw [openPisAtFvars_mapKeys]
  cases h₆ : openPisAtFvars nF crestP nP with
  | none => exact SimE.throw'
  | some u =>
  obtain ⟨xFvs, _⟩ := u
  obtain ⟨hx, _⟩ := Expr.openPisAtFvars_good hcr h₆
  simp only [Option.map_some, Expr.mapDoms, ← List.map_append, Expr.instLamsAt_mapKeys]
  have hfx : Expr.GoodList P (fvsP ++ xFvs) := by simp [hfvs, hx]
  cases h₇ : Expr.instLamsAt (fvsP ++ xFvs) rhsA with
  | none => exact SimE.throw'
  | some w =>
  obtain ⟨ldoms, _⟩ := w
  obtain ⟨hld, _⟩ := Expr.instLamsAt_good hfx hA h₇
  simp only [Option.map_some, Expr.mapDoms]
  refine SimE.bind (SimE.congr (by rw [map_fvarTypeD_mapKeys])
    (checkDefEqList_sim hops hE (nP + nF) _ _ hfx.map_fvarTypeD hld)) (fun _ _ => ?_)
  refine SimE.bind (hops.inferType hE 0 rhsA hA) (fun _ _ => ?_)
  exact SimE.pure' hA rfl

end Helpers

end Ix.Kernel
