import Ix.Cert.SourceLaws
import Ix.Cert.ConversionValues
import IxC.Kernel.Verify.StrLitExpr
import IxC.Kernel.Verify.InferLeaves
import IxC.Kernel.Model.Rules.RedSoundKit
import IxC.Kernel.Model.Rules.IotaSoundKit
import IxC.Kernel.Model.IndTele

/-! # Public telescope fits and the internal fits

The value-level Source laws (`Ix.Cert.SourceLaws`) state their premises with
public denotations: values fit a telescope (`Fits`) when each lies in its binder
domain's denotation. A strong model's internal laws state the same premises
over the invariant's readings: a value-level fit (`Model.TeleFit`), or an
annotation-level fit at an ambient valuation (`Model.TeleFitPA`). This module
moves public fits to internal ones.
* **Denotations move between valuations that agree on the loose variables**
  (`Denotes.congr_below`).
* **A public fit is an internal value-level fit** (`teleFit_of_fits`). Each binder
  domain's public denotation is the interpretation of its reading, by the
  kernel's bridge `Model.Denotes_of_denoteMeta` read at the depth the binders
  open to.
* **A value-level fit is an annotation-level fit** at any arguments that
  interpret to the values (`teleFitPA_of_teleFit`), by the substitution law
  `interp_inst`. -/

namespace Ix.Cert.ValueFits

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel.Expr (closeN)
open Ix.Kernel.Term

universe w

variable {md : Mode} {V : Type w} [SetTheory V]

/-! ## Valuations that agree on the loose variables -/

/-- **A denotation depends on the valuation only at the term's loose variables.** -/
theorem Denotes.congr_below {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {e : Ix.Kernel.Expr md} {v : V}
    (h : Denotes cval env φ ρ e v) :
    ∀ (n : Nat) (ρ' : BVarIdx → V), e.looseBVarsBounded n = true →
      (∀ i, i < n → ρ' i = ρ i) → Denotes cval env φ ρ' e v := by
  induction h with
  | @bvar ρ i =>
    intro n ρ' hb hρ
    have hi : i < n := by simpa [Ix.Kernel.Expr.looseBVarsBounded] using hb
    rw [← hρ i hi]
    exact .bvar
  | sort => intro _ _ _ _; exact .sort
  | const hf hlen => intro _ _ _ _; exact .const hf hlen
  | app _ _ ihf iha =>
    intro n ρ' hb hρ
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact .app (ihf n ρ' hb.1 hρ) (iha n ρ' hb.2 hρ)
  | @lam ρ ty body m A F _ _ hP ihA ihF =>
    intro n ρ' hb hρ
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine .lam (ihA n ρ' hb.1 hρ) (fun x hx => ihF x hx (n + 1) (push x ρ') hb.2 ?_) hP
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hρ i (by omega)
  | @pi ρ ty body m A B _ _ hP ihA ihB =>
    intro n ρ' hb hρ
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine .pi (ihA n ρ' hb.1 hρ) (fun x hx => ihB x hx (n + 1) (push x ρ') hb.2 ?_) hP
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hρ i (by omega)
  | proj_table ht _ ih =>
    intro n ρ' hb hρ
    exact .proj_table ht (ih n ρ' hb hρ)
  | proj_fst ht _ ih =>
    intro n ρ' hb hρ
    exact .proj_fst ht (ih n ρ' hb hρ)
  | proj_snd ht _ ih =>
    intro n ρ' hb hρ
    exact .proj_snd ht (ih n ρ' hb hρ)
  | @natLit ρ k X _ ih =>
    intro n ρ' _ hρ
    exact .natLit (ih n ρ' (natLitToConstructor_looseBVars k) hρ)
  | @strLit ρ s X _ ih =>
    intro n ρ' _ hρ
    exact .strLit (ih n ρ' (strLitToConstructor_looseBVars s n) hρ)

/-- A closed term denotes alike under every valuation. -/
theorem Denotes.congr_closed {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {e : Ix.Kernel.Expr md} {v : V}
    (h : Denotes cval env φ ρ e v) (hb : e.looseBVarsBounded 0 = true) (ρ' : BVarIdx → V) :
    Denotes cval env φ ρ' e v :=
  Denotes.congr_below h 0 ρ' hb (fun _ hi => absurd hi (Nat.not_lt_zero _))

/-- The closure at depth `d` of a term with no loose variable below the cut `k` and
free variables below `d` has its loose variables below `k + d`. -/
theorem closeN_looseBVarsBounded (d : Nat) :
    ∀ (e : Ix.Kernel.Expr md) (k : Nat), Expr.fvarsBelow d e → e.looseBVarsBounded k = true →
      (closeN d e k).looseBVarsBounded (k + d) = true := by
  intro e
  induction e with
  | bvar i =>
    intro k _ hb
    simp only [closeN, Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] at hb ⊢
    omega
  | fvar idx ty _ =>
    intro k hf _
    simp only [Expr.fvarsBelow] at hf
    simp only [closeN, Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq]
    omega
  | sort => intros; rfl
  | const => intros; rfl
  | app f a ihf iha =>
    intro k hf hb
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [closeN, Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf k hf.1 hb.1, iha k hf.2 hb.2⟩
  | lam ty body m iht ihb =>
    intro k hf hb
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [closeN, Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨iht k hf.1 hb.1, ?_⟩
    have := ihb (k + 1) hf.2 hb.2
    rwa [show k + 1 + d = k + d + 1 from by omega] at this
  | forallE ty body m iht ihb =>
    intro k hf hb
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [closeN, Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨iht k hf.1 hb.1, ?_⟩
    have := ihb (k + 1) hf.2 hb.2
    rwa [show k + 1 + d = k + d + 1 from by omega] at this
  | letE ty val body l iht ihv ihb =>
    intro k hf hb
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [closeN, Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨⟨iht k hf.1 hb.1.1, ihv k hf.2.1 hb.1.2⟩, ?_⟩
    have := ihb (k + 1) hf.2.2 hb.2
    rwa [show k + 1 + d = k + d + 1 from by omega] at this
  | lit => intros; rfl
  | proj s i e ih =>
    intro k hf hb
    simp only [Ix.Kernel.Expr.looseBVarsBounded] at hb
    simp only [closeN, Ix.Kernel.Expr.looseBVarsBounded]
    exact ih k hf hb

/-! ## Public fits are internal fits -/

section Bridge

variable {acval : Key md → (LevelParam → Nat) → AnnotTerm} {env : Env md} {φ : LevelParam → Nat}

/-- **A public fit, read at depth `d`, is an internal value-level fit.** The term `e`
is opened to depth `d` (its free variables below `d`, no loose bound variable), and
its public form is its closure `closeN d e`. The valuations agree below `d`. -/
theorem teleFit_of_fits (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) :
    ∀ (vs : List V) (d : Nat) (e : Ix.Kernel.Expr md) {ta : AnnotTerm} (σ ρ ρ' : BVarIdx → V)
      (R : Ix.Kernel.Expr md),
      denoteMeta acval env φ d e = some ta → Expr.fvarsBelow d e →
      e.looseBVarsBounded 0 = true → WellDenotedV V σ ta → (∀ i, i < d → σ i = ρ i) →
      Fits (cvalOf (V := V) acval) env φ ρ (closeN d e) vs ρ' R →
      ∃ rest, TeleFit V σ ta vs rest := by
  intro vs
  induction vs with
  | nil =>
    intro d e ta σ ρ ρ' R _ _ _ _ _ _
    exact ⟨_, TeleFit.nil⟩
  | cons x xs ih =>
    intro d e ta σ ρ ρ' R hread hfb hlb hw hσ hfit
    cases e with
    | forallE ty body mb =>
      obtain ⟨tA, bA, hta, hba, rfl⟩ := denoteMeta_forallE_inv hread
      have hfb' : Expr.fvarsBelow d ty ∧ Expr.fvarsBelow d body := hfb
      have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
      rw [Bool.and_eq_true] at hlb'
      obtain ⟨hw1, hw2⟩ := hw
      rw [WellDenoted_pi] at hw1
      rw [AnnotValid_pi] at hw2
      have hfit' : Fits (cvalOf (V := V) acval) env φ ρ
          (.forallE (closeN d ty 0) (closeN d body 1) mb) (x :: xs) ρ' R := hfit
      cases hfit' with
      | cons hA hx hrest =>
        -- the domain's public denotation is its reading's interpretation
        have hbr := Denotes_of_denoteMeta (V := V) hcl d ty hta hfb'.1 hlb'.1 σ ⟨hw1.1, hw2.1⟩
        have hbrρ := Denotes.congr_below hbr d ρ (by simpa using closeN_looseBVarsBounded d ty 0 hfb'.1 hlb'.1) (fun i hi => (hσ i hi).symm)
        rename_i Av
        have hAv : Av = interp V σ tA := Denotes_functional hA hbrρ
        subst hAv
        obtain ⟨rest, hrest'⟩ := ih (d + 1) (body.instantiate1 (.fvar d ty)) (cons x σ) (push x ρ) ρ' R
          hba (Expr.fvarsBelow_instantiate1 0 hfb'.2)
          (Ix.Kernel.looseBVarsBounded_instantiate1 body 0 hlb'.2)
          ⟨hw1.2 x hx, hw2.2.1 x hx⟩
          (fun i hi => by
            cases i with
            | zero => rfl
            | succ i => exact hσ i (by omega))
          (by rwa [Expr.closeN_instantiate1 body 0 hlb'.2 hfb'.2])
        exact ⟨rest, TeleFit.cons hx hrest'⟩
    | _ => cases hfit

/-- The empty fit leaves the term and the valuation as they are. -/
theorem Fits.nil_inv {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {φ : LevelParam → Nat} {ρ ρ' : BVarIdx → V} {T R : Ix.Kernel.Expr md}
    (h : Fits cval env φ ρ T [] ρ' R) : ρ' = ρ ∧ R = T := by
  cases h
  exact ⟨rfl, rfl⟩

/-- **A public fit, read**, with what the peel leaves: the canonical opening
variables it opened (`args`, one per value, annotated with their domains), the
term left after them (`eR`, whose closure is the fit's residual body), its reading
(`taR`), graded under the valuation extended by the values, which agrees with the
fit's final valuation on the opened variables. -/
theorem fits_read (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase) :
    ∀ (vs : List V) (d : Nat) (e : Ix.Kernel.Expr md) {ta : AnnotTerm} (σ ρ ρ' : BVarIdx → V)
      (R : Ix.Kernel.Expr md),
      denoteMeta acval env φ d e = some ta → Expr.WScoped d e →
      e.looseBVarsBounded 0 = true → WellDenotedV V σ ta → (∀ i, i < d → σ i = ρ i) →
      Fits (cvalOf (V := V) acval) env φ ρ (closeN d e) vs ρ' R →
      (∃ rest, TeleFit V σ ta vs rest) ∧
      ∃ (args : List (Ix.Kernel.Expr md)) (eR : Ix.Kernel.Expr md) (taR : AnnotTerm),
        args.length = vs.length ∧
        (∀ k, k < vs.length → ∃ ty, args[k]? = some (.fvar (d + k) ty)) ∧
        (∀ a ∈ args, Expr.WScoped (d + vs.length) a ∧ a.looseBVarsBounded 0 = true) ∧
        piResidual e args = some eR ∧ Expr.WScoped (d + vs.length) eR ∧
        eR.looseBVarsBounded 0 = true ∧ R = closeN (d + vs.length) eR 0 ∧
        denoteMeta acval env φ (d + vs.length) eR = some taR ∧
        WellDenotedV V (consN vs σ) taR ∧ (∀ i, i < d + vs.length → consN vs σ i = ρ' i) := by
  intro vs
  induction vs with
  | nil =>
    intro d e ta σ ρ ρ' R hread hw hlb hgr hσ hfit
    obtain ⟨rfl, rfl⟩ := Fits.nil_inv hfit
    refine ⟨⟨_, TeleFit.nil⟩, [], e, ta, rfl, ?_, ?_, rfl, ?_, hlb, ?_, ?_, hgr, ?_⟩
    · intro k hk
      exact absurd hk (Nat.not_lt_zero _)
    · intro a ha
      exact nomatch ha
    · simpa using hw
    · simp
    · simpa using hread
    · intro i hi
      exact hσ i (by simpa using hi)
  | cons x xs ih =>
    intro d e ta σ ρ ρ' R hread hw hlb hgr hσ hfit
    cases e with
    | forallE ty body mb =>
      obtain ⟨tA, bA, hta, hba, rfl⟩ := denoteMeta_forallE_inv hread
      have hw' : Expr.WScoped d ty ∧ Expr.WScoped d body := by
        simpa only [Expr.WScoped] using hw
      have hlb' : (ty.looseBVarsBounded 0 && body.looseBVarsBounded 1) = true := hlb
      rw [Bool.and_eq_true] at hlb'
      obtain ⟨hw1, hw2⟩ := hgr
      rw [WellDenoted_pi] at hw1
      rw [AnnotValid_pi] at hw2
      have hfit' : Fits (cvalOf (V := V) acval) env φ ρ
          (.forallE (closeN d ty 0) (closeN d body 1) mb) (x :: xs) ρ' R := hfit
      cases hfit' with
      | cons hA hx hrest =>
        have hbr := Denotes_of_denoteMeta (V := V) hcl d ty hta hw'.1.fvarsBelow hlb'.1 σ
          ⟨hw1.1, hw2.1⟩
        have hbrρ := Denotes.congr_below hbr d ρ
          (by simpa using closeN_looseBVarsBounded d ty 0 hw'.1.fvarsBelow hlb'.1)
          (fun i hi => (hσ i hi).symm)
        rename_i Av
        have hAv : Av = interp V σ tA := Denotes_functional hA hbrρ
        subst hAv
        have hwA : Expr.WScoped (d + 1) (Ix.Kernel.Expr.fvar d ty) := by
          simp only [Expr.WScoped]
          exact ⟨Nat.lt_succ_self d, hw'.1⟩
        have hwB : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
          Expr.WScoped.instantiate1_gen hwA 0 (hw'.2.mono (Nat.le_succ d))
        obtain ⟨⟨rest, hr⟩, args, eR, taR, hlen, hshape, hargs, hpr, hweR, hlbR, hR, hrd, hgrR,
            hσR⟩ :=
          ih (d + 1) (body.instantiate1 (.fvar d ty)) (cons x σ) (push x ρ) ρ' R hba hwB
            (Ix.Kernel.looseBVarsBounded_instantiate1 body 0 hlb'.2) ⟨hw1.2 x hx, hw2.2.1 x hx⟩
            (fun i hi => by
              cases i with
              | zero => rfl
              | succ i => exact hσ i (by omega))
            (by rwa [Expr.closeN_instantiate1 body 0 hlb'.2 hw'.2.fvarsBelow])
        have hdl : d + (x :: xs).length = d + 1 + xs.length := by
          simp only [List.length_cons]; omega
        refine ⟨⟨rest, TeleFit.cons hx hr⟩, .fvar d ty :: args, eR, taR, by simp [hlen], ?_, ?_,
          hpr, by rw [hdl]; exact hweR, hlbR, by rw [hdl]; exact hR, by rw [hdl]; exact hrd,
          hgrR, by rw [hdl]; exact hσR⟩
        · intro k hk
          cases k with
          | zero => exact ⟨ty, by simp⟩
          | succ k =>
            obtain ⟨ty', hty'⟩ := hshape k (by simp at hk; omega)
            exact ⟨ty', by simpa [show d + (k + 1) = d + 1 + k from by omega] using hty'⟩
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · refine ⟨?_, rfl⟩
            rw [hdl]
            exact hwA.mono (by omega)
          · rw [hdl]
            exact hargs a ha
    | _ => cases hfit

/-- **A public fit of a closed term** gives an internal value-level fit at every
ambient valuation. -/
theorem teleFit_of_fits_closed (hcl : ∀ n ψ, Term.Closed (acval n ψ).erase)
    {e : Ix.Kernel.Expr md} {ta : AnnotTerm} (hread : denoteMeta acval env φ 0 e = some ta)
    (hnf : e.hasFvar = false) (hlb : e.looseBVarsBounded 0 = true)
    (hgr : ∀ σ : Nat → V, WellDenotedV V σ ta) {ρ ρ' : BVarIdx → V} {R : Ix.Kernel.Expr md}
    {vs : List V} (hfit : Fits (cvalOf (V := V) acval) env φ ρ e vs ρ' R) (σ : Nat → V) :
    ∃ rest, TeleFit V σ ta vs rest :=
  (fits_read hcl vs 0 e σ ρ ρ' R hread (Expr.WScoped.of_not_hasFvar hnf) hlb (hgr σ)
    (fun _ hi => absurd hi (Nat.not_lt_zero _))
    (by rwa [Expr.closeN_of_hasFvar e 0 0 hnf])).1

end Bridge

/-! ## Value-level fits are annotation-level fits -/

/-- A value-level fit forces a ∀-chain of its length. -/
theorem piChain_of_teleFit {ρ : Nat → V} {T : AnnotTerm} {vs : List V} {rest : V}
    (h : TeleFit V ρ T vs rest) : Rules.PiChain vs.length T := by
  induction h with
  | nil => trivial
  | cons _ _ ih => exact ih

/-- **A fit instantiates** (the converse of `Rules.teleFit_of_inst`). -/
theorem teleFit_inst {aa : AnnotTerm} :
    ∀ {L : List V} {E : AnnotTerm} {k : Nat} {ρ : Nat → V} {rest : V},
      Rules.PiChain L.length E →
      TeleFit V (instE k (interp V (shiftE k 0 ρ) aa) ρ) E L rest →
      ∃ rest', TeleFit V ρ (E.inst aa k) L rest' := by
  intro L
  induction L with
  | nil => intro E k ρ rest _ _; exact ⟨_, TeleFit.nil⟩
  | cons y ys ih =>
    intro E k ρ rest hpc h
    obtain ⟨u, v, A, B, rfl, hB⟩ := Rules.piChain_succ_inv hpc
    cases h with
    | cons hmem hfit =>
      rw [cons_instE, ← shiftE_succ_cons y k ρ] at hfit
      obtain ⟨r, hr⟩ := ih hB hfit
      refine ⟨r, ?_⟩
      rw [AnnotTerm.inst_pi]
      exact TeleFit.cons (by rw [interp_inst]; exact hmem) hr

/-- **A value-level fit is an annotation-level fit** at any arguments that
interpret to the values. -/
theorem teleFitPA_of_teleFit {ρ : Nat → V} :
    ∀ {T : AnnotTerm} {as : List AnnotTerm} {rest : V},
      Rules.PiChain as.length T → TeleFit V ρ T (as.map (interp V ρ)) rest →
      ∃ resta, TeleFitPA V ρ T as resta
  | T, [], _, _, _ => ⟨T, .nil⟩
  | _, a :: as, rest, hpc, h => by
    obtain ⟨u, v, A, B, rfl, hB⟩ := Rules.piChain_succ_inv hpc
    cases h with
    | cons hmem hfit =>
      have h0 : TeleFit V (instE 0 (interp V (shiftE 0 0 ρ) a) ρ) B
          (as.map (interp V ρ)) rest := by
        rw [shiftE_zero_zero, instE_zero]
        exact hfit
      obtain ⟨r, hr⟩ := teleFit_inst (by simpa using hB) h0
      obtain ⟨resta, hpa⟩ := teleFitPA_of_teleFit (Rules.PiChain.inst a 0 hB) hr
      exact ⟨resta, .cons hmem hpa⟩

/-! ## Closing the canonical openers -/

/-- **Opening with the canonical variables and closing at the full depth is the
identity** on a term without free variables, at any base `j`: the canonical
opener's variable `j + q` replaces bound variable `m - 1 - q`, which the closure
at depth `j + m` turns back into bound variable `m - 1 - q`. -/
theorem closeN_instSeq_openFvars :
    ∀ (m j : Nat) (e : Ix.Kernel.Expr md), Expr.fvarsBelow j e → e.looseBVarsBounded m = true →
      closeN (j + m) (Expr.instSeq (Verify.openFvars j m) (m - 1) e) 0 = closeN j e m := by
  intro m
  induction m with
  | zero =>
    intro j e _ _
    rfl
  | succ m ih =>
    intro j e hf hb
    rw [Verify.openFvars_succ, show m + 1 - 1 = m from by omega]
    show closeN (j + (m + 1)) (Expr.instSeq (Verify.openFvars (j + 1) m) (m - 1)
      (e.instantiate1 (.fvar j (.sort .zero)) m)) 0 = closeN j e (m + 1)
    rw [show j + (m + 1) = (j + 1) + m from by omega,
      ih (j + 1) _ (Expr.fvarsBelow_instantiate1 m hf)
        (Ix.Kernel.looseBVarsBounded_instantiate1 e m hb),
      Expr.closeN_instantiate1 e m hb hf]

/-- Closing commutes with the application spine. -/
theorem getAppArgs_closeN (d : Nat) :
    ∀ (e : Ix.Kernel.Expr md), (closeN d e 0).getAppArgs = e.getAppArgs.map (closeN d · 0) := by
  intro e
  induction e with
  | app f a ihf _ =>
    simp only [closeN, Ix.Kernel.Expr.getAppArgs, ihf, List.map_append, List.map_cons,
      List.map_nil]
  | fvar => rfl
  | bvar => rfl
  | sort => rfl
  | const => rfl
  | lam => rfl
  | forallE => rfl
  | letE => rfl
  | lit => rfl
  | proj => rfl

/-- The arguments of a graded application spine are graded. -/
theorem wellDenotedV_mkAppN_args {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) (f : AnnotTerm), WellDenotedV V ρ (AnnotTerm.mkAppN f as) →
      ∀ a ∈ as, WellDenotedV V ρ a
  | [], _, _ => by intro a ha; exact nomatch ha
  | b :: bs, f, h => by
    intro a ha
    have h' := wellDenotedV_mkAppN_args bs (.app f b) h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact WellDenotedV_app_arg (WellDenotedV_mkAppN_head bs h)
    · exact h' a ha

end Ix.Cert.ValueFits
