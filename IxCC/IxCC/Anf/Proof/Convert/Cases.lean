import IxCC.Anf.Proof.Convert.Lists

/-! # ANF conversion: `case`

A `case` is converted with its scrutinee's operand; its alternatives bind
their fields above the current target depth. With a meta-continuation and
more than one branch, the continuation becomes a join point of one
parameter and every branch jumps to it (non-tail `case`, 02 §6.1): the jump
charges, which only makes the target run deeper (tick dominance). The
simulations of `convAlts`, `caseBody` and `caseOn` at `fuel + 1` (P1,
M2.3). -/

set_option autoImplicit false

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Lam (Kind Mode argSlot applyArgs)
open IxCC.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec)
open IxCC.Ixon

theorem except_map_ok {ε α β : Type} {f : α → β} {x : Except ε α} {b : β} (h : f <$> x = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => cases h; exact ⟨a, rfl, rfl⟩

namespace Setting

variable {S : Setting} {n fuel : Nat}

theorem convAlts_step (ih : S.ConvAt n fuel) {cx : Cx} {alts : List Lam.Alt} {k : Kont}
    {alts' : List Alt} {ρ : Lam.Env} {ρ' : List Val} {J' : List JClo} {ks : List Kind}
    {SK : Lam.Val → Nat → Result Lam.Val}
    (h : convAlts S.A (fuel + 1) cx alts k = .ok alts') (henv : EnvR S.A S.G ks cx.vars ρ ρ')
    (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj) (hk : S.KontR n cx.dj k SK ρ' J')
    (halts : S.AltsOk ks alts) {c : Key.CtorKey} {fs : List Lam.Val} {fs' : List Val}
    {dflt : Option Lam.Term} {dflt' : Option Exp} (hfs : VRs S.A S.G fs fs')
    (hdf : S.DfltSim n ρ ρ' J' SK dflt dflt') :
    SimUpTo S.V n (fun k => (Lam.evalAlts S.L k ρ c fs alts dflt).bind (SK · k))
      (fun k => evalAlts S.Q k ρ' J' c fs' alts' dflt') := by
  cases alts with
  | nil =>
    rw [convAlts.eq_2 S.A (fuel + 1) cx k (Nat.succ_ne_zero _)] at h
    cases h
    rcases hdf with ⟨rfl, rfl⟩ | ⟨t, e, rfl, rfl, hsim⟩
    · exact (SimUpTo.stuck _).congr (fun k => by rw [Lam.evalAlts_nil]; rfl)
        (fun k => by rw [evalAlts_nil])
    · exact hsim.congr (fun k => by rw [Lam.evalAlts_nil]) (fun k => by rw [evalAlts_nil])
  | cons a rest =>
    obtain ⟨key, m, body⟩ := a
    rw [convAlts] at h
    obtain ⟨b, hb, h⟩ := Lam.ModesOk.bind_ok h
    obtain ⟨rest', hrest, h⟩ := Lam.ModesOk.bind_ok h
    cases h
    have hlen := hfs.length
    by_cases hsel : key = c ∧ m = fs.length
    · obtain ⟨rfl, rfl⟩ := hsel
      have henv' := hfs.reverse_append henv
      rw [hd] at henv'
      refine (ih.conv hb henv' (by simp [hd, hlen]; omega) hdj
        (hk.suffix (List.suffix_append _ _) (List.suffix_refl _) hdj hdj)
        (halts _ List.mem_cons_self)).congr (fun k => ?_) (fun k => ?_)
      · rw [Lam.evalAlts_cons, if_pos ⟨rfl, rfl⟩]
      · rw [evalAlts_cons, if_pos ⟨rfl, hlen.symm⟩]
    · refine (ih.convAlts (c := c) hrest henv hd hdj hk (fun a ha => halts a (List.mem_cons_of_mem _ ha))
        hfs hdf).congr (fun k => ?_) (fun k => ?_)
      · rw [Lam.evalAlts_cons, if_neg hsel]
      · rw [evalAlts_cons, if_neg (by rw [hlen]; exact hsel)]

theorem caseBody_step (ih : S.ConvAt n fuel) {cx : Cx} {o : Opd} {alts : List Lam.Alt}
    {dflt : Option Lam.Term} {k : Kont} {e : Exp} {ρ : Lam.Env} {ρ' : List Val} {J' : List JClo}
    {ks : List Kind} {SK : Lam.Val → Nat → Result Lam.Val} {v : Lam.Val} {w : Val}
    (h : caseBody S.A (fuel + 1) cx o alts dflt k = .ok e) (henv : EnvR S.A S.G ks cx.vars ρ ρ')
    (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj) (hk : S.KontR n cx.dj k SK ρ' J')
    (ho : o.val ρ' = some w) (hv : S.V v w) (halts : S.AltsOk ks alts) (hdflt : S.DfltOk ks dflt) :
    SimUpTo S.V n (fun k => (S.caseSrc k ρ v alts dflt).bind (SK · k))
      (fun k => eval S.Q k ρ' J' e) := by
  rw [caseBody] at h
  obtain ⟨alts', halts', h⟩ := Lam.ModesOk.bind_ok h
  -- the default's conversion
  obtain ⟨dflt', hdf, rfl⟩ : ∃ dflt', S.DfltSim n ρ ρ' J' SK dflt dflt' ∧
      e = .case (o.atom cx.d) alts' dflt' := by
    cases dflt with
    | none =>
      cases h
      exact ⟨none, .inl ⟨rfl, rfl⟩, rfl⟩
    | some t =>
      obtain ⟨d', hd', h⟩ := Lam.ModesOk.bind_ok h
      obtain ⟨e', he', rfl⟩ := except_map_ok hd'
      cases h
      exact ⟨some e', .inr ⟨t, e', rfl, rfl, ih.conv he' henv hd hdj hk (hdflt t rfl)⟩, rfl⟩
  have hsrc : ∀ k, S.caseSrc k ρ v alts dflt = (match v.asCtor S.L.known with
      | some (c, fs) => Lam.evalAlts S.L k ρ c fs alts dflt
      | none => .stuck) := fun _ => rfl
  have htgt : ∀ k, eval S.Q k ρ' J' (.case (o.atom cx.d) alts' dflt') =
      (match w.asCtor S.L.known with
       | some (c, fs) => evalAlts S.Q k ρ' J' c fs alts' dflt'
       | none => .stuck) := fun k => by
    rw [eval_case, ← hd, Opd.val_atom ho, S.known]; rfl
  rcases asCtor_rel (K := S.L.known) hv with ⟨h1, h2⟩ | ⟨c, fs, fs', h1, h2, hfs⟩
  · refine (SimUpTo.stuck (fun _ => .stuck)).congr (fun k => ?_) (fun k => ?_)
    · rw [hsrc, h1]; rfl
    · rw [htgt, h2]
  · refine (ih.convAlts (c := c) halts' henv hd hdj hk halts hfs hdf).congr (fun k => ?_) (fun k => ?_)
    · rw [hsrc, h1]
    · rw [htgt, h2]

theorem caseOn_step (ih : S.ConvAt n fuel) {cx : Cx} {o : Opd} {alts : List Lam.Alt}
    {dflt : Option Lam.Term} {k : Kont} {e : Exp} {ρ : Lam.Env} {ρ' : List Val} {J' : List JClo}
    {ks : List Kind} {SK : Lam.Val → Nat → Result Lam.Val} {v : Lam.Val} {w : Val}
    (h : caseOn S.A (fuel + 1) cx o alts dflt k = .ok e) (henv : EnvR S.A S.G ks cx.vars ρ ρ')
    (hd : ρ'.length = cx.d) (hdj : J'.length = cx.dj) (hk : S.KontR n cx.dj k SK ρ' J')
    (ho : o.val ρ' = some w) (hv : S.V v w) (halts : S.AltsOk ks alts) (hdflt : S.DfltOk ks dflt) :
    SimUpTo S.V n (fun k => (S.caseSrc k ρ v alts dflt).bind (SK · k))
      (fun k => eval S.Q k ρ' J' e) := by
  cases k with
  | bind c f =>
    rw [caseOn.eq_2] at h
    by_cases hb : (alts.length + if dflt.isSome = true then 1 else 0) ≤ 1
    · rw [if_pos hb] at h
      exact ih.caseBody h henv hd hdj hk ho hv halts hdflt
    · rw [if_neg hb] at h
      obtain ⟨jb, hjb, h⟩ := Lam.ModesOk.bind_ok h
      obtain ⟨body, hbody, h⟩ := Lam.ModesOk.bind_ok h
      cases h
      have hk' : S.KontR n (cx.dj + 1) (.jump cx.dj) SK ρ' (.mk ρ' J' 1 jb false :: J') := by
        refine ⟨by omega, ρ', J', jb, by simp, fun x w' hxw => ?_⟩
        exact hk hjb (by simp [hd]) (List.suffix_cons _ _) hdj (List.suffix_refl _) x
          ⟨w', by rw [← hd]; exact Opd.val_lvl_top ρ' w', hxw⟩
      exact (ih.caseBody (cx := { cx with dj := cx.dj + 1 }) hbody henv hd (by simp [hdj]) hk' ho hv
        halts hdflt).congr (fun _ => rfl) (fun k => eval_join' S.Q k ρ' J' 1 false jb body)
  | ret =>
    rw [caseOn.eq_3 _ _ _ _ _ _ _ (fun _ _ h => by cases h)] at h
    exact ih.caseBody h henv hd hdj hk ho hv halts hdflt
  | jump l =>
    rw [caseOn.eq_3 _ _ _ _ _ _ _ (fun _ _ h => by cases h)] at h
    exact ih.caseBody h henv hd hdj hk ho hv halts hdflt

end Setting

end IxCC.Anf.Convert.Proof
