import IxCC.Anf.Proof.Rel.Basic
import IxCC.Anf.Proof.Lang

/-! # The fundamental lemma and adequacy

**Fundamental lemma** (design note 02 §7.2, M2.3): for any structural
value relation `R` (`Rel.Structural`), every Anf expression simulates
itself, the source run in program `P` and the target run in program `Q`,
from related environments and join closures, at every clock bound `n` — given
that applying related values, calling a global and reading a global's value
simulate at `n` (`AppSim`, `CallSim`, `GlobSim`) and the lemma itself below
`n` (`fund_step`; jumps and ticks run one clock down). It is the
compatibility lemmas (`Rel/Basic`) assembled by structural recursion.
Applying a closure of the same code (`app_idc`) needs the lemma below `n`
and application of the result to the rest at `n`.

**The identity instance** (`IdV`: same code everywhere) satisfies the
interface at every bound by strong induction (`Ident.level`), so every
program simulates itself and refines itself (`Ident.refines`).

**Adequacy**: a structural relation that keeps observations, with the
interface at every bound, gives `Sem.Refines P Q` on runs from the roots
(`refines_of`); passes compose by `Sem.Refines.trans` (the composition
argument that replaces transitivity of the relation). -/

set_option autoImplicit false

namespace IxCC.Anf.Rel

open IxCC.Sem (Result ClockMono SimUpTo Sim later later_succ later_zero)

variable (P Q : Program) (R : Val → Val → Prop)

/-- Every expression simulates itself at clock bound `n`. -/
def FundAt (n : Nat) : Prop :=
  ∀ ⦃ρ ρ' : List Val⦄ ⦃J J' : List JClo⦄, Pw R ρ ρ' → JR R J J' →
    ∀ e : Exp, SimUpTo R n (fun k => eval P k ρ J e) (fun k => eval Q k ρ' J' e)

variable {P Q R}

theorem JR.get : ∀ {J J' : List JClo}, JR R J J' → ∀ (j : Nat),
    (J[j]? = none ∧ J'[j]? = none) ∨ ∃ ρ ρ' J0 J0' m b r, J[j]? = some (.mk ρ J0 m b r) ∧
      J'[j]? = some (.mk ρ' J0' m b r) ∧ Pw R ρ ρ' ∧ JR R J0 J0'
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons hρ h0 _, 0 => .inr ⟨_, _, _, _, _, _, _, rfl, rfl, hρ, h0⟩
  | _, _, .cons _ _ h, j + 1 => by simpa using h.get j

section

variable {n : Nat} (hS : Structural R) (hK : Q.known = P.known)
  (hlow : ∀ m < n, FundAt P Q R m) (ha : AppSim P Q R n) (hc : CallSim P Q R n)
  (hg : GlobSim P Q R n)
include hS hK hlow ha hc hg

theorem fund_bind {ρ ρ' : List Val} (hρ : Pw R ρ ρ') :
    ∀ b : Bind, SimUpTo R n (fun k => evalBind P k ρ b) (fun k => evalBind Q k ρ' b)
  | .atom a => compat_atom hS hρ a
  | .con c as => compat_con hS hρ c as
  | .proj c i x => compat_proj hS hρ c i x
  | .prim p as => compat_prim hS hK hρ p as
  | .glob g => compat_glob hS hg ρ ρ' g
  | .call g as => compat_call hS hc hρ g as
  | .app f as => compat_app hS ha hρ f as
  | .fn ps b => compat_fn hS hρ ps b

mutual

theorem fund_exp {ρ ρ' : List Val} {J J' : List JClo} (hρ : Pw R ρ ρ') (hJ : JR R J J') :
    ∀ e : Exp, SimUpTo R n (fun k => eval P k ρ J e) (fun k => eval Q k ρ' J' e)
  | .bind c b e =>
    compat_bind (fund_bind hS hK hlow ha hc hg hρ b) fun _ _ hvw => fund_exp (.cons hvw hρ) hJ e
  | .join m r b e => compat_join (fund_exp hρ (.cons hρ hJ hJ) e)
  | .jump j as => by
    refine SimUpTo.congr ?_ (fun k => eval_jump P k ρ J j as) (fun k => eval_jump Q k ρ' J' j as)
    rcases hJ.get j with ⟨h1, h2⟩ | ⟨ρj, ρj', J0, J0', m, b, r, h1, h2, hρj, hJ0⟩
    · rw [h1]; exact SimUpTo.stuck _
    · rw [h1, h2]
      simp only [Result.ofOption, Result.bind_ok]
      rcases atoms_eval_rel hS hρ as with ⟨h3, h4⟩ | ⟨vs, ws, h3, h4, hvs⟩
      · rw [h3]; exact SimUpTo.stuck _
      · rw [h3, h4]
        simp only [Result.bind_ok]
        refine compat_jumpTo hvs (fun _ _ _ _ _ _ _ _ _ e1 e2 => ?_) (fun _ _ _ _ _ _ _ _ _ _ e1 e2 => ?_)
        · cases e1; cases e2
          refine ⟨rfl, fun i hi _ => hlow i (by omega) (hvs.reverse.append hρj) ?_ b⟩
          cases r
          · exact hJ0
          · exact .cons hρj hJ0 hJ0
        · cases e1; cases e2; rfl
  | .case x alts d => by
    refine SimUpTo.congr ?_ (fun k => eval_case P k ρ J x alts d) (fun k => eval_case Q k ρ' J' x alts d)
    rcases atom_eval_rel hS hρ x with ⟨h1, h2⟩ | ⟨v, w, h1, h2, hvw⟩
    · rw [h1]; exact SimUpTo.stuck _
    · rw [h1, h2, hK]
      simp only [Result.ofOption, Result.bind_ok]
      rcases asCtor_rel hS P.known hvw with h3 | ⟨c, fs, fs', h3, h4, hfs⟩
      · rw [h3]; exact SimUpTo.stuck _
      · rw [h3, h4]
        exact fund_alts hρ hJ c hfs d (fund_opt hρ hJ d) alts
  | .ret a => compat_ret hS hρ a
  | .tick e => compat_tick fun m hm => hlow m (by omega) hρ hJ e
  | .trap => compat_trap

theorem fund_opt {ρ ρ' : List Val} {J J' : List JClo} (hρ : Pw R ρ ρ') (hJ : JR R J J') :
    ∀ d : Option Exp, ∀ e, d = some e →
      SimUpTo R n (fun k => eval P k ρ J e) (fun k => eval Q k ρ' J' e)
  | none => fun _ h => nomatch h
  | some e => fun _ h => by cases h; exact fund_exp hρ hJ e

theorem fund_alts {ρ ρ' : List Val} {J J' : List JClo} (hρ : Pw R ρ ρ') (hJ : JR R J J')
    (c : Key.CtorKey) {fs fs' : List Val} (hfs : Pw R fs fs') (d : Option Exp)
    (hd : ∀ e, d = some e → SimUpTo R n (fun k => eval P k ρ J e) (fun k => eval Q k ρ' J' e)) :
    ∀ alts : List Alt,
      SimUpTo R n (fun k => evalAlts P k ρ J c fs alts d) (fun k => evalAlts Q k ρ' J' c fs' alts d)
  | [] => by
    refine SimUpTo.congr ?_ (fun k => evalAlts_nil P k ρ J c fs d) (fun k => evalAlts_nil Q k ρ' J' c fs' d)
    cases d with
    | none => exact SimUpTo.stuck _
    | some e => exact hd e rfl
  | .mk key m body :: rest => by
    refine SimUpTo.congr ?_ (fun k => evalAlts_cons P k ρ J c fs key m body rest d)
      (fun k => evalAlts_cons Q k ρ' J' c fs' key m body rest d)
    have hl := hfs.length
    by_cases hsel : key = c ∧ m = fs.length
    · have hsel' : key = c ∧ m = fs'.length := ⟨hsel.1, by rw [hl]; exact hsel.2⟩
      exact (fund_exp (hfs.reverse.append hρ) hJ body).congr (fun _ => if_pos hsel)
        (fun _ => if_pos hsel')
    · have hsel' : ¬ (key = c ∧ m = fs'.length) := by rw [hl]; exact hsel
      exact (fund_alts hρ hJ c hfs d hd rest).congr (fun _ => if_neg hsel) (fun _ => if_neg hsel')

end

/-- **Fundamental lemma**, one clock bound: from the interface at `n` and
the lemma below `n`. -/
theorem fund_step : FundAt P Q R n := fun _ _ _ _ hρ hJ e =>
  fund_exp hS hK hlow ha hc hg hρ hJ e

end

/-- Applying a closure to related arguments where both sides have the same
code: the body one clock down (the fundamental lemma below `n`), then the
rest of the arguments at `n`. -/
theorem app_idc (hS : Structural R) {n : Nat} (hlow : ∀ m < n, FundAt P Q R m)
    {ρ ρ' got got' : List Val} {m : Nat} {b : Exp} (hρ : Pw R ρ ρ') (hgot : Pw R got got')
    {vs ws : List Val} (hvs : Pw R vs ws)
    (hrest : ∀ ⦃f g : Val⦄ ⦃us us' : List Val⦄, R f g → Pw R us us' → us.length < vs.length →
      SimUpTo R n (fun k => applyN P k f us) (fun k => applyN Q k g us')) :
    SimUpTo R n (fun k => applyN P k (.clos ρ m b got) vs) (fun k => applyN Q k (.clos ρ' m b got') ws) := by
  have hgl := hgot.length
  have hvl := hvs.length
  have hg' : got'.length = got.length := hgl
  cases vs with
  | nil =>
    cases hvs
    exact (SimUpTo.ok (hS.idc ρ ρ' m b got got' hρ hgot)).congr (fun k => applyN_nil' P k _)
      (fun k => applyN_nil' Q k _)
  | cons v vs' =>
    obtain ⟨w, ws', rfl⟩ : ∃ w ws', ws = w :: ws' := by
      cases ws with
      | nil => cases hvs
      | cons w ws' => exact ⟨w, ws', rfl⟩
    by_cases hg : got.length < m
    · by_cases hu : got.length + (v :: vs').length < m
      · -- under-saturated: the extended closures
        refine (SimUpTo.later fun _ _ => SimUpTo.ok (hS.idc ρ ρ' m b _ _ hρ (hgot.append hvs))).congr
          (fun k => ?_) (fun k => ?_)
        · rw [applyN_clos]; simp only [hg, hu, if_true]
        · have hu' : got'.length + (w :: ws').length < m := by rw [hgl, hvl]; exact hu
          rw [applyN_clos]; simp only [show got'.length < m by omega, hu', if_true]
      · -- saturated: the body, then the rest
        have hall := hgot.append hvs
        refine (SimUpTo.bind (d := fun r k => applyN P k r ((got ++ v :: vs').drop m))
          (d' := fun r k => applyN Q k r ((got' ++ w :: ws').drop m))
          (ClockMono.later (eval_mono Q _ [] b)) (fun r => applyN_mono Q r _)
          (SimUpTo.later fun i hi => hlow i (by omega) ((hall.take m).reverse.append hρ) .nil b)
          fun r r' hr => ?_).congr (fun k => ?_) (fun k => ?_)
        · by_cases hnil : ((got ++ v :: vs').drop m) = []
          · have : ((got' ++ w :: ws').drop m) = [] := by
              rw [List.drop_eq_nil_iff] at hnil ⊢; simp at hnil hvl ⊢; omega
            rw [hnil, this]
            exact (SimUpTo.ok hr).congr (fun k => applyN_nil' P k r) (fun k => applyN_nil' Q k r')
          · exact hrest hr (hall.drop m) (by simp at hnil ⊢; omega)
        · rw [applyN_clos]
          simp only [hg, hu, if_true, if_false]
          cases k with
          | zero => rfl
          | succ k => simp only [later_succ, enter]
        · rw [applyN_clos]
          simp only [show got'.length < m by omega, if_true,
            show ¬ (got'.length + (w :: ws').length < m) by simp at hvl hu ⊢; omega, if_false]
          cases k with
          | zero => rfl
          | succ k => simp only [later_succ, enter]
    · refine (SimUpTo.later (c₁ := fun _ => (.stuck : Result Val)) (c₂ := fun _ => .stuck)
        fun _ _ => SimUpTo.stuck _).congr (fun k => ?_) (fun k => ?_)
      · rw [applyN_clos]; simp only [hg, if_false]
      · rw [applyN_clos]; simp only [show ¬ got'.length < m by omega, if_false]

/-! ## Adequacy -/

theorem run_simUpTo (hS : Structural R) {n : Nat} (hg : GlobSim P Q R n) (ha : AppSim P Q R n)
    (r : GlobalId) {xs ws : List Val} (hxs : Pw R xs ws) :
    SimUpTo R n (fun k => run P k r xs) (fun k => run Q k r ws) :=
  (SimUpTo.bind (evalBind_mono Q [] _) (fun g => applyN_mono Q g ws) (compat_glob hS hg [] [] r)
    fun _ _ hfg => ha hfg hxs).congr (fun k => run_eq P k r xs) (fun k => run_eq Q k r ws)

/-- **Adequacy**: a structural relation that keeps observations, with the
interface at every clock bound, gives refinement on runs from the roots. -/
theorem refines_of (hS : Structural R) (hroots : Q.roots = P.roots)
    (hobs : ∀ v w, R v w → obsV v = obsV w) (hg : ∀ n, GlobSim P Q R n) (ha : ∀ n, AppSim P Q R n) :
    Sem.Refines P Q := by
  refine Sem.Refines.of_sim (R := R) hobs fun i => ⟨id, ?_⟩
  show Sim R id (anfRun P i) (anfRun Q i)
  unfold anfRun
  rw [hroots]
  cases P.roots[i.1]? with
  | none => exact ⟨fun _ _ => ⟨0, .stuck⟩, fun _ h => nomatch h⟩
  | some r =>
    have hxs : Pw R (i.2.map fun n => Val.lit (.nat n)) (i.2.map fun n => Val.lit (.nat n)) := by
      induction i.2 with
      | nil => exact .nil
      | cons n ns ih => exact .cons (hS.lit _) ih
    exact SimUpTo.sim fun n => run_simUpTo hS (hg n) (ha n) r hxs

end IxCC.Anf.Rel
