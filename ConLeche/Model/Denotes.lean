module

public import ConLeche.Denotes
public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Verify.Close
import ConLeche.Verify.Denote.VClosed
import ConLeche.SetModel.TupleTower
import ConLeche.Semantics.Tower.TowerLeaf
import ConLeche.Model.Annot.BitLemmas

public section

/-!
# The model the invariant carries, read through `Denotes`

`ConLeche/Denotes.lean` states what a model of an environment is;
this module builds one from the graded invariant `EnvModelM`
(`Model/Annot/EnvModelM.lean`) the fold establishes.  Three steps:

* **the leaves become sets**: `cvalOf acval n ψ` is the interpretation
  of the (closed) annotated leaf `acval n ψ` — under every variable
  environment the same set (`interp_cvalOf`);
* **the bridge** `Denotes_of_denoteMeta`: wherever the invariant's
  reading `denoteMeta` reads a term at depth `d`, and the reading is
  graded and bit-valid (`WellDenotedV`), `interp` of the reading is a
  `Denotes`-denotation of the term's CLOSURE (`Expr.closeN`, the
  checker's opened `fvar`s turned back into the de Bruijn indices the
  relation reads) at the interpreted leaves.  The regime premises of
  the two binder rules are exactly the invariant's sort facts:
  `AnnotValid`'s `pi` clause and `WellDenoted`'s `lam` clause.
* **the model** `Model.ofEnvModelM`: `mem` from `type_reads` and
  `mem_type` at depth `0` (a stored type has no `fvar`, so it is its
  own closure); `false_empty` from the pinned `False` leaf
  (`EnvModel.cvalE_pinned`: the leaf is `.const .empty [0]`, whose
  interpretation is the empty set); `eq_equality` from the invariant's
  `eq_law` field, whose value clause is exactly the three-fold
  application the statement asks about.  `eq_law` is premised on the
  *pinned* `Eq` being stored, and the `Denotes` hypothesis supplies
  only that *something* is stored at `eqName`; the two are joined by
  `basis_pinnedL`'s declaration clause, which since task #283 holds of
  a stored reserved name whatever its kind.
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche.SetTheory.Tower (projS)
open ConLeche (Env Expr Name Level ConstantInfo)
open ConLeche.Expr (closeN)

universe w

variable {V : Type w} [SetTheory V]

/-- The set-valued leaf of an annotated valuation. -/
noncomputable def cvalOf (acval : Name → (Name → Nat) → AnnotTerm)
    (n : Name) (ψ : Name → Nat) : V :=
  interp V (fun _ => SetTheory.empty) (acval n ψ)

/-- A closed leaf interprets to its `cvalOf` under every environment. -/
theorem interp_cvalOf {acval : Name → (Name → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) (n : Name) (ψ : Name → Nat)
    (ρ : Nat → V) : interp V ρ (acval n ψ) = cvalOf acval n ψ :=
  interp_closed (V := V) (hcl n ψ) ρ _

omit [SetTheory V] in
theorem push_eq_cons (x : V) (ρ : Nat → V) : ConLeche.push x ρ = cons x ρ := by
  funext i; cases i <;> rfl

theorem field_eq_projS : ∀ (i : Nat) (p : V), ConLeche.field i p = projS i p
  | 0, _ => rfl
  | i + 1, p => field_eq_projS i (ssnd p)

theorem regime_eq_pwBit (φ : Name → Nat) (pw : ConLeche.PropWhen) :
    ConLeche.regime φ pw = pwBit φ pw := rfl

/-! ### The literal spines -/

/-- A constant stored without universe parameters, at the empty
instantiation. -/
private theorem Denotes_const_nil {cval : Name → (Name → Nat) → V} {env : Env}
    {φ : Name → Nat} {ρ : Nat → V} {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) (h0 : ci.toConstantVal.levelParams = []) :
    Denotes cval env φ ρ (.const n []) (cval n (Level.substFn φ [] [])) := by
  have h := Denotes.const (cval := cval) (env := env) (φ := φ) (ρ := ρ) hf
    (us := []) (by rw [h0]; rfl)
  rwa [h0] at h

/-- A constant stored with one universe parameter, at `[.zero]`, valued
at the stored parameter list as `denoteMeta` spells it. -/
private theorem Denotes_const_one {cval : Name → (Name → Nat) → V} {env : Env}
    {φ : Name → Nat} {ρ : Nat → V} {n : Name} {ci : ConstantInfo} {p : Name}
    (hf : env.find? n = some ci) (h1 : ci.toConstantVal.levelParams = [p]) :
    Denotes cval env φ ρ (.const n [.zero])
      (cval n (Level.substFn φ (levelParamsAt env n) [.zero])) := by
  have h := Denotes.const (cval := cval) (env := env) (φ := φ) (ρ := ρ) hf
    (us := [.zero]) (by rw [h1]; rfl)
  rw [show levelParamsAt env n = ci.toConstantVal.levelParams by
    simp only [levelParamsAt, hf]]
  exact h

/-- Under the `Nat`-literal guard, the constructor form of a literal
denotes the annotated numeral `denoteMeta` reads. -/
theorem Denotes_natLitToConstructor {acval : Name → (Name → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat}
    (hsup : ConLeche.natLitSupported env = true) (ρ : Nat → V) :
    ∀ k, Denotes (cvalOf (V := V) acval) env φ ρ (ConLeche.natLitToConstructor k)
      (interp V ρ (natLitAV (acval natZeroName (Level.substFn φ [] []))
        (acval natSuccName (Level.substFn φ [] [])) k)) := by
  obtain ⟨-, -, cv0, i0, j0, cv1, i1, j1, -, hz, hs, -, hz0, hs0, -, -, -⟩ :=
    natLitSupported_inv hsup
  intro k
  induction k with
  | zero =>
    rw [ConLeche.natLitToConstructor, natLitAV, interp_cvalOf hcl]
    exact Denotes_const_nil hz hz0
  | succ k ih =>
    rw [ConLeche.natLitToConstructor, natLitAV, interp_app, interp_cvalOf hcl]
    exact Denotes.app (Denotes_const_nil hs hs0) (Denotes.natLit ih)

/-- Under the `String`-literal guard, the character-list spine of a
literal's constructor form denotes the annotated spine `denoteMeta`
reads. -/
private theorem Denotes_charList {acval : Name → (Name → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat}
    (hsup : ConLeche.strLitSupported env = true) (ρ : Nat → V) :
    ∀ l : List Char,
      Denotes (cvalOf (V := V) acval) env φ ρ
        (l.foldr
          (init := .app (.const listNilName [.zero]) (.const charName []))
          fun c e =>
            .app (.app (.app (.const listConsName [.zero]) (.const charName []))
              (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e)
        (interp V ρ (charListAV
          (.app (acval listNilName
              (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (.app (acval listConsName
              (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (acval charOfNatName (Level.substFn φ [] []))
          (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] []))
          l)) := by
  obtain ⟨hnat, -, -, -, ciN, ciC, ciH, ciF, -, pN, pC,
    -, -, -, hN, hC, hH, hF, -, -, -, hN1, hC1, hH0, hF0, -, -, -, -, -, -, -⟩ :=
    strLitSupported_inv hsup
  intro l
  induction l with
  | nil =>
    simp only [List.foldr_nil, charListAV, interp_app, interp_cvalOf hcl]
    exact Denotes.app (Denotes_const_one hN hN1) (Denotes_const_nil hH hH0)
  | cons c cs ih =>
    simp only [List.foldr_cons, charListAV, interp_app, interp_cvalOf hcl]
    exact Denotes.app
      (Denotes.app (Denotes.app (Denotes_const_one hC hC1) (Denotes_const_nil hH hH0))
        (Denotes.app (Denotes_const_nil hF hF0)
          (Denotes.natLit (Denotes_natLitToConstructor hcl hnat ρ _))))
      ih

/-- Under the `String`-literal guard, the constructor form of a literal
denotes what `denoteMeta` reads for the literal. -/
theorem Denotes_strLitToConstructor {acval : Name → (Name → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat}
    (hsup : ConLeche.strLitSupported env = true) (ρ : Nat → V) (s : String) :
    Denotes (cvalOf (V := V) acval) env φ ρ (ConLeche.strLitToConstructor s)
      (interp V ρ (.app (acval stringOfListName (Level.substFn φ [] []))
        (charListAV
          (.app (acval listNilName
              (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (.app (acval listConsName
              (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (acval charOfNatName (Level.substFn φ [] []))
          (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] []))
          s.toList))) := by
  obtain ⟨-, -, ciO, -, -, -, -, -, -, -, -, -, hO, -, -, -, -, -, -, hO0,
    -, -, -, -, -, -, -, -, -, -, -, -⟩ := strLitSupported_inv hsup
  unfold ConLeche.strLitToConstructor
  rw [interp_app, interp_cvalOf hcl]
  exact Denotes.app (Denotes_const_nil hO hO0) (Denotes_charList hcl hsup ρ _)

/-! ### The bridge -/

/-- Grading and bit-validity descend `.fst` to its subject. -/
private theorem wellDenotedV_of_fst {ρ : Nat → V} {e : AnnotTerm}
    (h : WellDenotedV V ρ (.fst e)) : WellDenotedV V ρ e := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_fst] at h1
  rw [AnnotValid_fst] at h2
  exact ⟨h1.1, h2⟩

/-- Grading and bit-validity descend `.snd` to its subject. -/
private theorem wellDenotedV_of_snd {ρ : Nat → V} {e : AnnotTerm}
    (h : WellDenotedV V ρ (.snd e)) : WellDenotedV V ρ e := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_snd] at h1
  rw [AnnotValid_snd] at h2
  exact ⟨h1.1, h2⟩

/-- Grading and bit-validity descend a tower projection to its subject. -/
theorem wellDenotedV_of_projAV {ρ : Nat → V} :
    ∀ (i : Nat) (e : AnnotTerm), WellDenotedV V ρ (projAV i e) → WellDenotedV V ρ e := by
  intro i
  induction i with
  | zero => intro e h; exact wellDenotedV_of_fst h
  | succ i ih => intro e h; exact wellDenotedV_of_snd (ih (.snd e) h)

/-- A term with no `fvar` is scoped below every depth. -/
private theorem fvarsBelow_zero_of_not_hasFvar :
    ∀ {e : Expr}, e.hasFvar = false → Expr.fvarsBelow 0 e := by
  intro e
  induction e <;> simp_all [Expr.fvarsBelow, Expr.hasFvar]

/-- **The bridge**: wherever `denoteMeta` reads a term whose reading is
graded and bit-valid, `interp` of the reading is a denotation of the
term's closure under `Denotes` at the interpreted leaves. -/
theorem Denotes_of_denoteMeta {acval : Name → (Name → Nat) → AnnotTerm}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) {env : Env} {φ : Name → Nat} :
    ∀ (d : Nat) (e : Expr) {ta : AnnotTerm},
      denoteMeta acval env φ d e = some ta →
      Expr.fvarsBelow d e → e.looseBVarsBounded 0 = true →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta →
        Denotes (cvalOf (V := V) acval) env φ ρ (closeN d e) (interp V ρ ta) := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro ta h _ _ ρ _
    rw [denoteMeta_sort] at h
    obtain rfl := Option.some.inj h
    rw [interp_sort]
    exact Denotes.sort
  | case2 d idx ty =>
    intro ta h _ _ ρ _
    rw [denoteMeta_fvar] at h
    obtain rfl := Option.some.inj h
    show Denotes _ _ _ _ (Expr.bvar (0 + (d - 1 - idx))) _
    rw [Nat.zero_add, interp_bvar]
    exact Denotes.bvar
  | case3 d n us ci hf hlen =>
    intro ta h _ _ ρ _
    rw [denoteMeta_const hf hlen] at h
    obtain rfl := Option.some.inj h
    rw [interp_cvalOf hcl]
    exact Denotes.const hf hlen
  | case4 d n us ci hf hlen =>
    intro ta h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ta h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body mb ihty ihbody =>
    intro ta h hfb hlb ρ hw
    obtain ⟨tA, bA, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
    have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
    rw [Bool.and_eq_true] at hlb'
    obtain ⟨hw1, hw2⟩ := hw
    rw [WellDenoted_pi] at hw1
    rw [AnnotValid_pi] at hw2
    show Denotes _ _ _ _ (Expr.forallE (closeN d ty 0) (closeN d body 1) mb) _
    rw [interp_pi, ← regime_eq_pwBit]
    refine Denotes.pi (ihty hta hfb'.1 hlb'.1 ρ ⟨hw1.1, hw2.1⟩) (fun x hx => ?_) ?_
    · rw [push_eq_cons]
      have hb := ihbody hba (Expr.fvarsBelow_instantiate1 0 hfb'.2)
        (ConLeche.looseBVarsBounded_instantiate1 body 0 hlb'.2) (cons x ρ)
        ⟨hw1.2 x hx, hw2.2.1 x hx⟩
      rwa [Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2] at hb
    · intro h0 x hx
      rw [regime_eq_pwBit] at h0
      rw [univ_zero]
      exact hw2.2.2 h0 x hx
  | case7 d ty body mb ihty ihbody =>
    intro ta h hfb hlb ρ hw
    obtain ⟨tA, bA, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
    have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
    rw [Bool.and_eq_true] at hlb'
    obtain ⟨hw1, hw2⟩ := hw
    rw [WellDenoted_lam] at hw1
    rw [AnnotValid_lam] at hw2
    obtain ⟨hwA, hwb, B, hfib, hzero⟩ := hw1
    show Denotes _ _ _ _ (Expr.lam (closeN d ty 0) (closeN d body 1) mb) _
    rw [interp_lam, ← regime_eq_pwBit]
    refine Denotes.lam (ihty hta hfb'.1 hlb'.1 ρ ⟨hwA, hw2.1⟩) (fun x hx => ?_) ?_
    · rw [push_eq_cons]
      have hb := ihbody hba (Expr.fvarsBelow_instantiate1 0 hfb'.2)
        (ConLeche.looseBVarsBounded_instantiate1 body 0 hlb'.2) (cons x ρ)
        ⟨hwb x hx, hw2.2 x hx⟩
      rwa [Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2] at hb
    · intro h0 x hx
      rw [regime_eq_pwBit] at h0
      exact eq_pt_of_mem_univZero (hzero h0 x hx) (hfib x hx)
  | case8 d fe a ihf iha =>
    intro ta h hfb hlb ρ hw
    obtain ⟨fA, aA, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    have hfb' : Expr.fvarsBelow d fe ∧ Expr.fvarsBelow d a := hfb
    have hlb' : (fe.looseBVarsBounded 0 && a.looseBVarsBounded 0) = true := hlb
    rw [Bool.and_eq_true] at hlb'
    obtain ⟨hw1, hw2⟩ := hw
    rw [WellDenoted_app] at hw1
    rw [AnnotValid_app] at hw2
    show Denotes _ _ _ _ (Expr.app (closeN d fe 0) (closeN d a 0)) _
    rw [interp_app]
    exact Denotes.app (ihf hfa hfb'.1 hlb'.1 ρ ⟨hw1.1, hw2.1⟩)
      (iha haa hfb'.2 hlb'.2 ρ ⟨hw1.2.1, hw2.2⟩)
  | case9 d ty val body =>
    intro ta h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro ta h hfb hlb ρ hw
    obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv h
    have hfb' : Expr.fvarsBelow d e := hfb
    have hlb' : e.looseBVarsBounded 0 = true := hlb
    show Denotes _ _ _ _ (Expr.proj sn i (closeN d e 0)) _
    rcases hcase with ⟨entry, hfp, rfl⟩ | ⟨hfp, hdec⟩
    · have hie := ihe hia hfb' hlb' ρ (wellDenotedV_of_projAV _ _ hw)
      rw [projAV_interp, ← field_eq_projS]
      exact Denotes.proj_table hfp hie
    · match i, hdec with
      | 0, hdec =>
        obtain rfl := Option.some.inj hdec
        have hie := ihe hia hfb' hlb' ρ (wellDenotedV_of_fst hw)
        rw [interp_fst]
        exact Denotes.proj_fst hfp hie
      | 1, hdec =>
        obtain rfl := Option.some.inj hdec
        have hie := ihe hia hfb' hlb' ρ (wellDenotedV_of_snd hw)
        rw [interp_snd]
        exact Denotes.proj_snd hfp hie
      | _ + 2, hdec => exact nomatch hdec
  | case11 d k hsup =>
    intro ta h _ _ ρ _
    rw [denoteMeta, if_pos hsup] at h
    obtain rfl := Option.some.inj h
    exact Denotes.natLit (Denotes_natLitToConstructor hcl hsup ρ k)
  | case12 d k hsup =>
    intro ta h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ta h _ _ ρ _
    rw [denoteMeta, if_pos hsup] at h
    obtain rfl := Option.some.inj h
    exact Denotes.strLit (Denotes_strLitToConstructor hcl hsup ρ s)
  | case14 d s hsup =>
    intro ta h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ta h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

/-! ### The model -/

/-- **The model, read off the invariant**: `Model V env` from
`EnvModelM V μ env`. -/
noncomputable def Model.ofEnvModelM {μ : ConLeche.CheckMode} {env : Env}
    (m : EnvModelM V μ env) : ConLeche.Model V env where
  cval := cvalOf m.base2.acval
  mem := by
    intro c hc φ ρ
    obtain ⟨ta, hta⟩ := m.type_reads c hc φ
    have hwf := m.base2.wf c hc
    have hnf : c.toConstantVal.type.hasFvar = false := hwf.1
    have hlb : c.toConstantVal.type.looseBVarsBounded 0 = true := hwf.2.2.2.1
    have hbr := Denotes_of_denoteMeta (V := V) m.base2.cval_closedL 0
      c.toConstantVal.type hta (fvarsBelow_zero_of_not_hasFvar hnf) hlb ρ
      (m.type_wellDenotedV c hc φ ta hta ρ)
    rw [Expr.closeN_of_hasFvar _ 0 0 hnf] at hbr
    refine ⟨interp V ρ ta, hbr, ?_⟩
    rw [← interp_cvalOf m.base2.cval_closedL]
    exact m.mem_type c hc φ ta hta ρ
  false_empty := by
    intro φ ρ F h
    suffices hs : ∀ (ψ : Name → Nat) (ci : ConstantInfo),
        env.find? falseName = some ci →
        cvalOf (V := V) m.base2.acval falseName ψ = SetTheory.empty by
      cases h with
      | const hf hlen => exact hs _ _ hf
    intro ψ ci hf
    have hpd : ConLeche.Verify.pinnedStructT falseName ψ
        = some (Term.const .empty [0]) := by
      simp +decide [ConLeche.Verify.pinnedStructT]
    have he : (m.base2.acval falseName ψ).erase = Term.const .empty [0] :=
      m.base2.cvalE_pinned (n := falseName) (by decide) (by rw [hf]; rfl) ψ hpd
    rw [cvalOf, erase_eq_const he, interp_const]
    rfl
  eq_equality := by
    intro u φ ρ E A a b h hA ha hb
    cases h with
    | const hf hlen =>
      have hpin := (m.base2.basis_pinned _ _ hf (by decide)).1
      rw [show ConLeche.pinnedInfo ConLeche.eqName = ConLeche.eqA from rfl]
        at hpin
      subst hpin
      rw [show (ConLeche.eqA : ConstantInfo).toConstantVal.levelParams
        = [ConLeche.uN] from rfl]
      have hψ : Level.substFn φ [ConLeche.uN] [u] ConLeche.uN = Level.eval φ u := by
        simp [Level.substFn]
      have hlaw := (m.eq_law hf (Level.substFn φ [ConLeche.uN] [u])).1 ρ A a b
        (by rw [hψ]; exact hA) ha hb
      rw [interp_cvalOf m.base2.cval_closedL] at hlaw
      exact hlaw

end ConLeche.Model
