import IxCC.Anf.Proof.Convert.Base

/-! # ANF conversion: environments and closures

Spine application on the Lam side, closure application on the Anf side, and
the environment lemmas of the P1 simulation (M2.3): lookup, growth of the
target environment (levels keep their values), and pushing a body's
parameters. -/

set_option autoImplicit false

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Lam (Kind Mode)
open IxCC.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName)
open IxCC.Ixon

variable (L : Lam.Program)

theorem applyAll_append (k : Nat) : ∀ (f : Lam.Val) (ss₁ ss₂ : List Lam.Slot),
    Lam.applyAll L k f (ss₁ ++ ss₂) = (Lam.applyAll L k f ss₁).bind (Lam.applyAll L k · ss₂)
  | f, [], ss₂ => by simp [Lam.applyAll_nil]
  | f, s :: ss₁, ss₂ => by
    simp only [List.cons_append, Lam.applyAll_cons, Sem.Result.bind_assoc]
    exact Sem.Result.bind_congr _ fun v => applyAll_append k v ss₁ ss₂

theorem applyAll_not_clos (k : Nat) (f : Lam.Val) (s : Lam.Slot) (ss : List Lam.Slot)
    (h : ∀ ρ b, f ≠ .clos ρ b) : Lam.applyAll L k f (s :: ss) = .stuck := by
  rw [Lam.applyAll_cons, Lam.apply_not_clos L k f s h]; rfl

/-! ## Anf on closures -/

variable (Q : Program)

theorem applyN_under (k : Nat) {ρt : List Val} {n : Nat} {bt : Exp} {got ws : List Val}
    (hws : ws ≠ []) (hlt : got.length + ws.length < n) :
    applyN Q k (.clos ρt n bt got) ws = later k fun _ => .ok (.clos ρt n bt (got ++ ws)) := by
  obtain ⟨v, rest, rfl⟩ : ∃ v rest, ws = v :: rest := List.exists_cons_of_ne_nil hws
  rw [applyN_clos]
  cases k with
  | zero => rfl
  | succ k =>
    simp only [later_succ]
    rw [if_pos (by omega), if_pos hlt]

theorem applyN_enter (k : Nat) {ρt : List Val} {n : Nat} {bt : Exp} {got ws : List Val}
    (hgot : got.length < n) (hge : n ≤ got.length + ws.length) :
    applyN Q k (.clos ρt n bt got) ws =
      (later k fun k => eval Q k (((got ++ ws).take n).reverse ++ ρt) [] bt).bind fun r =>
        applyN Q k r ((got ++ ws).drop n) := by
  cases ws with
  | nil => simp at hge; omega
  | cons v rest =>
    rw [applyN_clos]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [later_succ]
      rw [if_pos hgot, if_neg (by omega)]
      rfl

theorem applyN_not_clos' (k : Nat) (f : Val) (ws : List Val) (hws : ws ≠ [])
    (h : ∀ ρ n b got, f ≠ .clos ρ n b got) : applyN Q k f ws = .stuck := by
  obtain ⟨v, rest, rfl⟩ : ∃ v rest, ws = v :: rest := List.exists_cons_of_ne_nil hws
  exact applyN_not_clos Q k f v rest h

/-! ## Environments -/

variable {A : Arities} {G : Src.NatMap Lam.ModesOk.GInfo}

theorem EnvR.length : ∀ {ks : List Kind} {vars : List VarInfo} {ρ : Lam.Env} {ρt : List Val},
    EnvR A G ks vars ρ ρt → vars.length = ρ.length ∧ ks.length = ρ.length
  | _, _, _, _, .nil => ⟨rfl, rfl⟩
  | _, _, _, _, .cons _ _ _ h => by have ih := h.length; simp [ih.1, ih.2]

theorem EnvR.suffix : ∀ {ks : List Kind} {vars : List VarInfo} {ρ : Lam.Env} {ρt ρt' : List Val},
    EnvR A G ks vars ρ ρt → ρt <:+ ρt' → EnvR A G ks vars ρ ρt'
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, .cons ht hv hs' h, hs => .cons ht (Opd.val_suffix hs hv) hs' (h.suffix hs)

theorem EnvR.cons' {ks : List Kind} {vars : List VarInfo} {ρ : Lam.Env} {ρt : List Val}
    (h : EnvR A G ks vars ρ ρt) (x : Val) : EnvR A G ks vars ρ (x :: ρt) :=
  h.suffix (List.suffix_cons x ρt)

theorem EnvR.get : ∀ {ks : List Kind} {vars : List VarInfo} {ρ : Lam.Env} {ρt : List Val},
    EnvR A G ks vars ρ ρt → ∀ {i : Nat} {vi : VarInfo}, vars[i]? = some vi →
    ∃ q s w, ks[i]? = some q ∧ ρ[i]? = some s ∧ vi.opd.val ρt = some w ∧ SlotR A G q s w ∧
      vi.thunk = q.isName
  | _, _, _, _, .nil, _, _, hi => by simp at hi
  | _, _, _, _, .cons ht hv hs _, 0, _, hi => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨_, _, _, rfl, rfl, hv, hs, ht⟩
  | _, _, _, _, .cons _ _ _ h, i + 1, _, hi => by
      simp only [List.getElem?_cons_succ] at hi ⊢
      exact h.get hi

theorem SlotsR.length : ∀ {tk : List Kind} {ss : List Lam.Slot} {ws : List Val},
    SlotsR A G tk ss ws → ws.length = ss.length ∧ ss.length ≤ tk.length
  | _, _, _, .nil => by simp
  | _, _, _, .cons _ h => by have ih := h.length; simp; omega

theorem SlotsR.append : ∀ {tk : List Kind} {ss : List Lam.Slot} {ws : List Val},
    SlotsR A G tk ss ws → ∀ (tk' : List Kind) {ss' : List Lam.Slot} {ws' : List Val},
    SlotsR A G tk' ss' ws' → tk.length = ss.length →
    SlotsR A G (tk ++ tk') (ss ++ ss') (ws ++ ws')
  | _, _, _, .nil, _, _, _, h', hl => by simp at hl; subst hl; simpa using h'
  | _, _, _, .cons hs h, tk', _, _, h', hl => .cons hs (h.append tk' h' (by simpa using hl))

/-- The parameters of a body under `d` captured target values: parameter `i`
at level `d + i`, innermost first. -/
theorem pushParams_eq (vars : List VarInfo) (d : Nat) (thunks : List Bool) :
    pushParams vars d thunks =
      ((thunks.zipIdx 0).map fun (t, i) => ({ opd := .lvl (d + i), thunk := t } : VarInfo)).reverse ++
        vars := rfl

theorem envR_pushAux {k0 : List Kind} {vars0 : List VarInfo} {ρ0 : Lam.Env} {ρt : List Val}
    (d : Nat) : ∀ {tk : List Kind} {ss : List Lam.Slot} {ws : List Val} (start : Nat),
      SlotsR A G tk ss ws → tk.length = ss.length →
      (∀ i w, ws[i]? = some w → (Opd.lvl (d + start + i)).val ρt = some w) →
      EnvR A G k0 vars0 ρ0 ρt →
      EnvR A G (tk.reverse ++ k0)
        ((((tk.map Kind.isName).zipIdx start).map fun (t, i) =>
          ({ opd := .lvl (d + i), thunk := t } : VarInfo)).reverse ++ vars0)
        (ss.reverse ++ ρ0) ρt
  | [], [], [], _, _, _, _, h => by simpa using h
  | q :: tk, s :: ss, w :: ws, start, .cons hs hss, hl, hv, h => by
    have h' : EnvR A G (q :: k0) ({ opd := .lvl (d + start), thunk := q.isName } :: vars0)
        (s :: ρ0) ρt := .cons rfl (by simpa using hv 0 w rfl) hs h
    have ih := envR_pushAux d (start + 1) hss (by simpa using hl)
      (fun i w' hw => by
        have := hv (i + 1) w' (by simpa using hw)
        rwa [show d + start + (i + 1) = d + (start + 1) + i by omega] at this) h'
    simp only [List.map_cons, List.zipIdx_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    exact ih
  | [], _ :: _, _, _, h, _, _, _ => nomatch h
  | _ :: _, [], _, _, _, hl, _, _ => by simp at hl
  | [], [], _ :: _, _, h, _, _, _ => nomatch h
  | _ :: _, _ :: _, [], _, h, _, _, _ => nomatch h

/-- Pushing the parameters of a body: the supplied slots against the
argument values above the captured target environment. -/
theorem EnvR.push {k0 : List Kind} {vars0 : List VarInfo} {ρ0 : Lam.Env} {ρt : List Val}
    (h : EnvR A G k0 vars0 ρ0 ρt) {tk : List Kind} {ss : List Lam.Slot} {ws : List Val}
    (hss : SlotsR A G tk ss ws) (hl : tk.length = ss.length) :
    EnvR A G (tk.reverse ++ k0) (pushParams vars0 ρt.length (tk.map Kind.isName))
      (ss.reverse ++ ρ0) (ws.reverse ++ ρt) := by
  have hwl := hss.length.1
  rw [pushParams_eq]
  refine envR_pushAux ρt.length 0 hss hl (fun i w hw => ?_) (h.suffix (List.suffix_append _ _))
  have hi : i < ws.length := by
    rcases Nat.lt_or_ge i ws.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hw; cases hw
  simp only [Opd.val, List.length_append, List.length_reverse]
  rw [if_pos (by omega), List.getElem?_append_left (by simp; omega), List.getElem?_reverse (by omega)]
  rw [show ws.length - 1 - (ws.length + ρt.length - 1 - (ρt.length + 0 + i)) = i by omega]
  exact hw

end IxCC.Anf.Convert.Proof
