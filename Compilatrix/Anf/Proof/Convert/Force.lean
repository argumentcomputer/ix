import Compilatrix.Anf.Proof.Convert.Head

/-! # ANF conversion: forcing thunks

Reading a `name` variable forces its thunk: Lam evaluates the thunk's term
one clock down; Anf applies the thunk closure `fn [_] t'` to □, which runs
`t'` one clock down (P1, M2.3). A plain thunk (its binder's signature has no
`name`) gives a plain value (`force_sim`, from the body simulation below the
bound); a minor thunk (an erased recursor's minor, dispatched by name)
gives a telescope closure whose binders fit its dispatch signature
(`minor_sim`, by induction on the clock: a forwarded minor forces the
thunk it forwards). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Convert.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Lam (Kind Mode argSlot applyArgs)
open Compilatrix.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec)
open Compilatrix.Ixon

namespace Setting

variable (S : Setting)

/-- The head of a spine at argument position `i`: a plain value whose
remaining positions are strict, or a telescope closure fitting the spine's
expected kinds. -/
def GroupHead (tele : List Mode) (sigs : List (List Mode)) (i : Nat) (v : Lam.Val) (w : Val) : Prop :=
  (S.V v w ∧ ∀ p, i ≤ p → tele.getD p .strict = .strict) ∨
    ∃ tk, CloR S.A S.G tk i v w ∧ Compat tele sigs tk

/-- A forced minor thunk: a telescope closure fitting the signature. -/
def MinorR (sig : List Mode) (v : Lam.Val) (w : Val) : Prop :=
  ∃ tk, CloR S.A S.G tk 0 v w ∧ Compat sig [] tk

variable {S}

theorem force_later (k : Nat) (ρs : Lam.Env) (ts : Lam.Term) :
    Lam.force S.L k (.name ρs ts) = later k fun k => Lam.eval S.L k ρs ts := by
  rw [Lam.force_name]; cases k <;> rfl

theorem applyN_thunk (k : Nat) (ρt : List Val) (bt : Exp) :
    applyN S.Q k (.clos ρt 1 bt []) [.box] = later k fun k => eval S.Q k (.box :: ρt) [] bt := by
  rw [applyN_enter S.Q k (by simp) (by simp)]
  simp only [List.nil_append, List.take_succ_cons, List.take_zero, List.reverse_cons,
    List.reverse_nil, List.singleton_append, List.drop_succ_cons, List.drop_zero]
  cases k with
  | zero => rfl
  | succ k =>
    simp only [later_succ]
    cases eval S.Q k (.box :: ρt) [] bt with
    | ok v => simp only [Result.bind_ok, applyN_nil']
    | _ => rfl

omit S in
theorem NameArgOk.termOk {G : Src.NatMap GInfo} {ks : List Kind} {sig : List Mode} {t : Lam.Term}
    (h : NameArgOk G ks sig t) (hs : hasName sig = false) : TermOk G ks t := by
  cases h with
  | plain _ h => exact h
  | fwd hn _ => rw [hs] at hn; cases hn
  | tele hn _ _ _ _ _ => rw [hs] at hn; cases hn

/-- Plain thunks force to plain values. -/
theorem force_sim {n : Nat} (hb : ∀ m < n, BodySim S.L S.Q S.A S.G m) {sig : List Mode}
    {ρs : Lam.Env} {ts : Lam.Term} {w : Val} (hs : hasName sig = false)
    (ht : ThunkR S.A S.G sig ρs ts w) :
    SimUpTo S.V n (fun k => Lam.force S.L k (.name ρs ts)) (fun k => applyN S.Q k w [.box]) := by
  cases ht with
  | mk henv hconv hna hw =>
    subst hw
    exact (SimUpTo.later fun m hm => hb m (by omega) hconv (by simp) (henv.cons' .box)
      (NameArgOk.termOk hna hs)).congr (fun k => force_later k ρs ts) (fun k => applyN_thunk k _ _)

/-- The kinds a minor λ's telescope gives fit its dispatch signature. -/
theorem compat_minor {sig : List Mode} {ps : List (Mode × V3.BinderContract)} {kinds : List Kind}
    (htake : (ps.map (·.1)).take sig.length = sig) (hdrop : Mode.name ∉ (ps.map (·.1)).drop sig.length)
    (hma : ModesAgree ps kinds) (hk : ∀ s, Kind.name s ∈ kinds → hasName s = false) :
    Compat sig [] kinds := by
  intro p
  unfold expKind
  rcases Nat.lt_or_ge p kinds.length with hp | hp
  · have hpk : kinds.getD p .strict = kinds[p] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]; rfl
    have hpp : p < ps.length := by rw [hma.1]; exact hp
    have hagree := hma.2 p ps[p] kinds[p] (List.getElem?_eq_getElem hpp) (List.getElem?_eq_getElem hp)
    rw [hpk]
    rcases Nat.lt_or_ge p sig.length with hs | hs
    · have hsp : sig.getD p .strict = ps[p].1 := by
        rw [List.getD_eq_getElem?_getD, ← htake]
        simp [List.getElem?_take, hs, hpp]
      rw [hsp]
      cases hm : ps[p].1 with
      | strict =>
        rw [hm] at hagree
        simp only [if_neg (by decide : ¬ (Mode.strict = Mode.name))]
        cases hq : kinds[p] with
        | strict => exact .inl rfl
        | name s => rw [hq] at hagree; cases hagree
      | name =>
        rw [hm] at hagree
        simp only [if_pos rfl, List.getD_nil]
        cases hq : kinds[p] with
        | strict => rw [hq] at hagree; cases hagree
        | name s =>
          have : hasName s = false := hk s (by rw [← hq]; exact List.getElem_mem hp)
          exact .inr ⟨[], s, rfl, rfl, rfl, this⟩
    · have hsp : sig.getD p .strict = .strict := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hs]; rfl
      rw [hsp]
      simp only [if_neg (by decide : ¬ (Mode.strict = Mode.name))]
      have hnot : ps[p].1 ≠ .name := by
        intro e
        apply hdrop
        rw [List.mem_iff_getElem?]
        refine ⟨p - sig.length, ?_⟩
        rw [List.getElem?_drop, show sig.length + (p - sig.length) = p by omega]
        simp [hpp, e]
      cases hq : kinds[p] with
      | strict => exact .inl rfl
      | name s =>
        rw [hq] at hagree
        cases hm : ps[p].1 with
        | strict => rw [hm] at hagree; cases hagree
        | name => exact absurd hm hnot
  · rw [List.getD_eq_getElem?_getD (l := kinds), List.getElem?_eq_none hp]
    rcases Nat.lt_or_ge p sig.length with hs | hs
    · have hpp : p < ps.length := by
        have : sig.length ≤ ps.length := by
          rw [← htake]; simp only [List.length_take, List.length_map]; omega
        omega
      rw [hma.1] at hpp; omega
    · rw [List.getD_eq_getElem?_getD (l := sig), List.getElem?_eq_none hs]
      exact .inl rfl

theorem _root_.Compilatrix.Anf.Convert.Proof.EnvR.get_kind {A : Arities} {G : Src.NatMap GInfo} {ks : List Kind} {vars : List VarInfo}
    {ρ : Lam.Env} {ρt : List Val} (h : EnvR A G ks vars ρ ρt) {i : Nat} {q : Kind}
    (hq : ks[i]? = some q) : ∃ vi, vars[i]? = some vi := by
  have hl := h.length
  have hi : i < vars.length := by
    have : i < ks.length := by
      rcases Nat.lt_or_ge i ks.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hq; cases hq
    omega
  exact ⟨_, List.getElem?_eq_getElem hi⟩

/-- Minor thunks force to telescope closures fitting their signatures. -/
theorem minor_sim (n : Nat) : ∀ {sig : List Mode} {ρs : Lam.Env} {ts : Lam.Term} {w : Val},
    hasName sig = true → ThunkR S.A S.G sig ρs ts w →
    SimUpTo (S.MinorR sig) n (fun k => Lam.force S.L k (.name ρs ts))
      (fun k => applyN S.Q k w [.box]) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro sig ρs ts w hs ht
  cases ht with
  | @mk _ _ _ k0 vars0 ρt fuel bt _ henv hconv hna hw =>
  subst hw
  refine SimUpTo.congr ?_ (fun k => force_later k ρs ts) (fun k => applyN_thunk k _ _)
  cases fuel with
  | zero => rw [conv] at hconv; cases hconv
  | succ fuel =>
  cases hna with
  | plain h _ => rw [hs] at h; cases h
  | fwd _ hi =>
    rename_i i
    -- a forwarded minor: the thunk forces the thunk it forwards
    obtain ⟨vi, hvi⟩ := henv.get_kind hi
    obtain ⟨q, s, w', hq, hs', hw', hsr, hth⟩ := henv.get hvi
    rw [hi] at hq
    cases hq
    rw [conv] at hconv
    simp only [hvi, hth, Kind.isName, if_true] at hconv
    cases hconv
    cases hsr with
    | name hth' =>
      refine SimUpTo.later fun m hm => (ih m (by omega) hs hth').congr (fun k => ?_) (fun k => ?_)
      · exact Lam.eval_var_of S.L k ρs hs'
      · rw [eval_bind, evalBind_app]
        have ha : (vi.opd.atom (ρt.length + 1)).eval (.box :: ρt) = some w' := by
          have := Opd.val_atom (Opd.val_append [.box] hw')
          simpa using this
        have hbox : evalAtoms (Val.box :: ρt) [Atom.box] = some [.box] := rfl
        rw [ha, hbox]
        simp only [Result.ofOption, Result.bind_ok]
        conv => rhs; rw [← Result.bind_pure (applyN S.Q k w' [.box])]
        exact Result.bind_congr _ fun v => by rw [eval_ret']; rfl
  | @tele _ _ m c b kinds _ htake hdrop hks hkn htm =>
    rw [lam_telescope_eq] at htake hdrop hks htm
    rcases htel : telescope (.lam m c b) with ⟨ps, body⟩
    rw [conv] at hconv
    simp only [htel] at hconv htake hdrop hks htm
    obtain ⟨b', hb', hemit⟩ := Lam.ModesOk.bind_ok hconv
    cases hemit
    have hlams : Lam.Term.lam m c b = lamsWith ps body := by
      rw [← lamsWith_telescope (.lam m c b), htel]
    have hnl : NotLam body := by
      have := notLam_telescope (.lam m c b); rw [htel] at this; exact this
    obtain ⟨p, ps', rfl⟩ : ∃ p ps', ps = p :: ps' := by
      cases ps with
      | nil => simp only [lamsWith] at hlams; rw [← hlams] at hnl; exact absurd hnl id
      | cons p ps' => exact ⟨p, ps', rfl⟩
    have hb : b = lamsWith ps' body := by
      obtain ⟨pm, pc⟩ := p
      simp only [lamsWith, Lam.Term.lam.injEq] at hlams
      exact hlams.2.2
    have hma := modesAgree_of_kindsSpec hks
    have hclo : S.MinorR sig (.clos ρs b) (.clos (.box :: ρt) (p :: ps').length b' []) :=
      ⟨kinds, .mk (ss := []) (got := []) hnl hma (by simp) (henv.cons' .box) .nil hb' htm rfl
        (by simp [hb, lamsWith]) rfl, compat_minor htake hdrop hma hkn⟩
    refine SimUpTo.later fun _ _ => (SimUpTo.ok hclo).congr (fun k => ?_) (fun k => ?_)
    · exact Lam.eval_lam S.L k ρs m c b
    · rw [eval_bind, evalBind_fn S.Q k _ _ _ (by simp)]
      simp [eval_ret', Atom.eval, Result.ofOption]

end Setting

end Compilatrix.Anf.Convert.Proof
