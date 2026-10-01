module

public import ConLeche.Verify.Denote.Tele
public import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.InstLevels

public section

/-!
# Real-argument instantiation, read through the reverse opening

`denote` of an `Expr.instSeq` at real arguments is the denote of the
*reverse-opened* subject with the arguments' denotations chained back
in (`denote_openRev`) — the recursion `denote`'s own β-lemma produces,
which is why the opener indices ascend with the substitution order
rather than with the binder order.  For a subject with no free
variables the opened denote is base-independent
(`denote_openRev_base`), which is what lets a *stored* expression — a
nested rule's parameter pin — be the meeting point of the fire site's
instantiation and the install's: both sides reduce to the base-`0`
reverse opening, and `RecRulesTT`'s nested parameter premise is stated
there.
-/

namespace ConLeche.Verify

open ConLeche.Term

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- The reverse opening's leaves sit below the opened depth. -/
theorem openRev_fvarsBelow {e : Expr} {d : Nat}
    (hfb : Expr.fvarsBelow d e) :
    ∀ n, Expr.fvarsBelow (d + n) (openRev d n e) := by
  intro n
  induction n with
  | zero => exact Expr.fvarsBelow_mono (by omega) hfb
  | succ n ih =>
    show Expr.fvarsBelow (d + (n + 1))
      ((openRev d n e).instantiate1 (.fvar (d + n) _) 0)
    refine Expr.fvarsBelow_instantiate1_gen ?_ 0
      (Expr.fvarsBelow_mono (by omega) ih)
    show Expr.fvarsBelow (d + (n + 1)) (.fvar (d + n) _)
    simp [Expr.fvarsBelow]

/-- Instantiation strips one loose level at any cut below the bound. -/
private theorem bounded_instantiate1_le {a : Expr}
    (hba : a.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k m : Nat), k ≤ m →
      e.looseBVarsBounded (m + 1) = true →
      (e.instantiate1 a k).looseBVarsBounded m = true := by
  intro e
  induction e with
  | bvar i =>
    intro k m hkm hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1]
    split
    · exact Expr.looseBVarsBounded_mono (by omega) hba
    · split
      · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
        omega
      · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
        omega
  | fvar idx ty ih => intro k m _ _; rfl
  | sort u => intro k m _ _; rfl
  | const n us => intro k m _ _; rfl
  | lit l => intro k m _ _; rfl
  | app f x ihf ihx =>
    intro k m hkm hb
    simp only [Expr.instantiate1, Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb ⊢
    exact ⟨ihf k m hkm hb.1, ihx k m hkm hb.2⟩
  | lam ty body bi ihty ihbody =>
    intro k m hkm hb
    simp only [Expr.instantiate1, Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb ⊢
    exact ⟨ihty k m hkm hb.1, ihbody (k + 1) (m + 1) (by omega) hb.2⟩
  | forallE ty body bi ihty ihbody =>
    intro k m hkm hb
    simp only [Expr.instantiate1, Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb ⊢
    exact ⟨ihty k m hkm hb.1, ihbody (k + 1) (m + 1) (by omega) hb.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro k m hkm hb
    simp only [Expr.instantiate1, Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb ⊢
    exact ⟨⟨ihty k m hkm hb.1.1, ihval k m hkm hb.1.2⟩,
      ihbody (k + 1) (m + 1) (by omega) hb.2⟩
  | proj s i x ih =>
    intro k m hkm hb
    simp only [Expr.instantiate1, Expr.looseBVarsBounded] at hb ⊢
    exact ih k m hkm hb

/-- The reverse opening consumes the loose variables. -/
theorem openRev_bounded {e : Expr} {d : Nat} :
    ∀ n m, e.looseBVarsBounded (n + m) = true →
      (openRev d n e).looseBVarsBounded m = true := by
  intro n
  induction n generalizing e with
  | zero =>
    intro m h
    rw [Nat.zero_add] at h
    exact h
  | succ n ih =>
    intro m h
    show ((openRev d n e).instantiate1 _ 0).looseBVarsBounded m = true
    refine bounded_instantiate1_le rfl _ 0 m (by omega) ?_
    exact ih (m + 1) (by
      rw [show n + (m + 1) = n + 1 + m from by omega]
      exact h)

end ConLeche.Verify

namespace ConLeche.Verify

open ConLeche.Term

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- The reverse opening is well-scoped at the opened depth. -/
theorem openRev_WScoped {e : Expr} {d : Nat}
    (hws : Expr.WScoped d e) :
    ∀ n, Expr.WScoped (d + n) (openRev d n e) := by
  intro n
  induction n with
  | zero => exact hws.mono (by omega)
  | succ n ih =>
    show Expr.WScoped (d + (n + 1))
      ((openRev d n e).instantiate1 (.fvar (d + n) _) 0)
    have h1 := Expr.WScoped.instantiate1 (d := d + n)
      (ty := .sort .zero)
      (by simp [Expr.WScoped]) 0 ih
    exact h1.mono (by omega)

/-- The reverse opening of a constant-frame subject shifts with its
base. -/
theorem openRev_shiftFrom {e : Expr} (hnf : e.hasFvar = false) :
    ∀ (d n : Nat), (openRev d n e).shiftFrom 0 = openRev (d + 1) n e := by
  intro d n
  induction n with
  | zero =>
    exact Expr.shiftFrom_eq_self
      ((Expr.WScoped.of_not_hasFvar (d := 0) hnf).fvarsBelow)
  | succ n ih =>
    show ((openRev d n e).instantiate1
      (.fvar (d + n) (.sort .zero)) 0).shiftFrom 0 = _
    rw [Expr.shiftFrom_instantiate1 (Nat.zero_le (d + n)), ih]
    show (openRev (d + 1) n e).instantiate1
      (.fvar (d + n + 1) (.sort .zero)) 0 = _
    rw [show d + n + 1 = d + 1 + n from by omega]
    rfl

/-- **The base-independence of the opened denote**: a constant-frame
subject's reverse opening denotes the same term at every base. -/
theorem denote_openRev_base (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {e : Expr} (hnf : e.hasFvar = false) {n : Nat}
    (hb : e.looseBVarsBounded n = true) :
    ∀ d : Nat, denote cval env φ (d + n) (openRev d n e) =
      denote cval env φ n (openRev 0 n e) := by
  intro d
  induction d with
  | zero => rw [Nat.zero_add]
  | succ d ih =>
    have h1 : openRev (d + 1) n e = (openRev d n e).shiftFrom 0 :=
      (openRev_shiftFrom hnf d n).symm
    rw [show d + 1 + n = (d + n) + 1 from by omega, h1,
      denote_shiftFrom hcl (openRev d n e) (d + n) (Nat.zero_le _)
        (openRev_fvarsBelow
          ((Expr.WScoped.of_not_hasFvar (d := d) hnf).fvarsBelow) n),
      ih]
    cases hden : denote cval env φ n (openRev 0 n e) with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.some.injEq]
      rw [Nat.sub_zero]
      refine Term.liftN_eq_self ?_ 1
      have hbv := denote_bvarsBelow hcl n (openRev 0 n e)
        (by
          have h2 := openRev_WScoped (d := 0)
            (Expr.WScoped.of_not_hasFvar hnf) n
          rwa [Nat.zero_add] at h2)
        (openRev_bounded n 0 (by simpa using hb)) hden
      exact hbv.mono (by omega)

/-- **Real-argument instantiation, read through the reverse
opening.** -/
theorem denote_openRev (hcl : ∀ n ψ, Term.Closed (cval n ψ)) :
    ∀ (as : List Expr) {e : Expr} {d : Nat},
      (∀ a ∈ as, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
        Expr.fvarsBelow d a) →
      Expr.fvarsBelow d e → e.looseBVarsBounded as.length = true →
      ∀ {vs : List Term}, DenoteSpine cval env φ d as vs →
      denote cval env φ d (Expr.instSeq as (as.length - 1) e) =
        (denote cval env φ (d + as.length)
          (openRev d as.length e)).map (Term.instRevChain vs) := by
  intro as
  induction as with
  | nil =>
    intro e d _ _ _ vs hsp
    cases hsp
    show denote cval env φ d e = (denote cval env φ (d + 0) e).map _
    cases denote cval env φ d e <;> rfl
  | cons a as ih =>
    intro e d hargs hfb hb vs hsp
    cases hsp with
    | @cons _ va _ vs' ha hsp' => ?_
    have hargs' : ∀ x ∈ as, Expr.WScoped d x ∧
        x.looseBVarsBounded 0 = true ∧ Expr.fvarsBelow d x :=
      fun x hx => hargs x (List.mem_cons_of_mem _ hx)
    obtain ⟨hwa, hba, hfa⟩ := hargs a List.mem_cons_self
    -- one real argument in
    show denote cval env φ d
      (Expr.instSeq as ((a :: as).length - 1 - 1)
        (e.instantiate1 a ((a :: as).length - 1))) = _
    rw [show (a :: as).length - 1 - 1 = as.length - 1 from by simp,
      show (a :: as).length - 1 = as.length from by simp]
    rw [ih (e := e.instantiate1 a as.length)
      hargs'
      (Expr.fvarsBelow_instantiate1_gen hfa _ hfb)
      (Expr.looseBVarsBounded_instantiate1_gen hba (by
        simpa using hb))
      hsp']
    -- the opened side: commute the argument out, then β at the top
    rw [openRev_instantiate1_top hba d as.length e]
    have ha' : denote cval env φ (d + as.length) a =
        some (va.liftN as.length) := by
      rw [denote_lift hcl hfa (d + as.length) (by omega), ha,
        show d + as.length - d = as.length from by omega]
      rfl
    rw [denote_beta (ty := .sort .zero) hcl
      (openRev_fvarsBelow hfb as.length)
      (hwa.mono (by omega)) hba ha' 0]
    show ((denote cval env φ (d + as.length + 1)
      (openRev d (as.length + 1) e)).map
        (Term.inst · (va.liftN as.length) 0)).map
        (Term.instRevChain vs') = _
    rw [Option.map_map,
      show d + as.length + 1 = d + (a :: as).length from by
        simp only [List.length_cons]
        omega,
      show (a :: as).length = as.length + 1 from rfl]
    cases denote cval env φ (d + (as.length + 1))
        (openRev d (as.length + 1) e) with
    | none => rfl
    | some X =>
      simp only [Option.map_some, Option.some.injEq, Function.comp_apply]
      show Term.instRevChain vs' (X.inst (va.liftN as.length) 0) = _
      rw [show Term.instRevChain (va :: vs') X =
        Term.instRevChain vs' (X.inst (va.liftN vs'.length) 0) from rfl,
        hsp'.length]

/-- The reverse opening commutes with level instantiation: the opener
annotations are `.sort .zero`, fixed points of the substitution. -/
theorem openRev_instantiateLevelParams (ks : List Name)
    (us : List Level) :
    ∀ (d n : Nat) (e : Expr),
      openRev d n (e.instantiateLevelParams ks us)
        = (openRev d n e).instantiateLevelParams ks us := by
  intro d n
  induction n with
  | zero => intro e; rfl
  | succ n ih =>
    intro e
    show (openRev d n (e.instantiateLevelParams ks us)).instantiate1
        (.fvar (d + n) (.sort .zero)) 0 = _
    rw [ih,
      show (openRev d (n + 1) e).instantiateLevelParams ks us
        = ((openRev d n e).instantiate1
            (.fvar (d + n) (.sort .zero))
            0).instantiateLevelParams ks us from rfl,
      Expr.instantiateLevelParams_instantiate1 ks us (openRev d n e) 0]
    rfl

/-- The reverse opening commutes with constant renaming (the opener
annotations mention no constants). -/
theorem openRev_renameConsts (f : Name → Name) :
    ∀ (d n : Nat) (e : Expr),
      openRev d n (e.renameConsts f)
        = (openRev d n e).renameConsts f := by
  intro d n
  induction n with
  | zero => intro e; rfl
  | succ n ih =>
    intro e
    show (openRev d n (e.renameConsts f)).instantiate1
        (.fvar (d + n) (.sort .zero)) 0 = _
    rw [ih,
      show (openRev d (n + 1) e).renameConsts f
        = ((openRev d n e).instantiate1
            (.fvar (d + n) (.sort .zero))
            0).renameConsts f from rfl,
      Expr.renameConsts_instantiate1 f (openRev d n e) 0]
    rfl

/-- A bound on every leaf index bounds the free variables. -/
theorem Expr.fvarsBelow_of_fvarLeaves :
    ∀ {e : Expr} {n : Nat},
      (∀ l ∈ e.fvarLeaves, l.1 < n) → Expr.fvarsBelow n e := by
  intro e
  induction e <;> intro n h <;>
    simp only [Expr.fvarsBelow, Expr.fvarLeaves] at h ⊢ <;>
    try trivial
  case fvar idx ty ih => exact h (idx, ty) List.mem_cons_self
  case app f a ihf iha =>
    exact ⟨ihf fun l hl => h l (List.mem_append_left _ hl),
      iha fun l hl => h l (List.mem_append_right _ hl)⟩
  case lam ty b m ihty ihb =>
    exact ⟨ihty fun l hl => h l (List.mem_append_left _ hl),
      ihb fun l hl => h l (List.mem_append_right _ hl)⟩
  case forallE ty b m ihty ihb =>
    exact ⟨ihty fun l hl => h l (List.mem_append_left _ hl),
      ihb fun l hl => h l (List.mem_append_right _ hl)⟩
  case letE ty v b ihty ihv ihb =>
    refine ⟨ihty fun l hl => h l ?_, ihv fun l hl => h l ?_,
      ihb fun l hl => h l ?_⟩
    · exact List.mem_append_left _ (List.mem_append_left _ hl)
    · exact List.mem_append_left _ (List.mem_append_right _ hl)
    · exact List.mem_append_right _ hl
  case proj s i e ihe => exact ihe h

end ConLeche.Verify
