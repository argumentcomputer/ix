import IxCC.Anf.Proof.Convert.Env

/-! # ANF conversion: application

Applying related closures to related arguments simulates at clock bound
`n`, given that bodies simulate below `n` (`app_sim`, P1). A Lam
spine applies one slot at a time and charges at each; Anf applies a group
of arguments with one charge (`applyN`). Both charge at the same depth: a
Lam closure that still lacks binders returns the next closure without
running anything, so a group of `m` arguments costs Lam `m` charges at the
same clock and Anf one. When a group saturates the telescope, both run the
body one clock down and apply its value to the rest at the same clock. -/

set_option autoImplicit false

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Lam (Kind Mode)
open IxCC.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName)
open IxCC.Ixon

variable (L : Lam.Program) (Q : Program) (A : Arities) (G : Src.NatMap Lam.ModesOk.GInfo)

/-- A converted body simulates its Lam body at clock bound `m`, from
related environments. -/
def BodySim (m : Nat) : Prop :=
  ∀ ⦃fuel : Nat⦄ ⦃vars : List VarInfo⦄ ⦃d : Nat⦄ ⦃body : Lam.Term⦄ ⦃bt : Exp⦄ ⦃ρ : Lam.Env⦄
    ⦃ρt : List Val⦄ ⦃ks : List Kind⦄,
    conv A fuel { vars, d, dj := 0 } body .ret = .ok bt → ρt.length = d → EnvR A G ks vars ρ ρt →
    TermOk G ks body →
    SimUpTo (VR A G) m (fun k => Lam.eval L k ρ body) (fun k => eval Q k ρt [] bt)

/-- Argument slots against values from position `i` of a telescope with
binder kinds `tk` (strict beyond it). -/
inductive ArgsR : List Kind → Nat → List Lam.Slot → List Val → Prop
  | nil {tk : List Kind} {i : Nat} : ArgsR tk i [] []
  | cons {tk : List Kind} {i : Nat} {s : Lam.Slot} {ss : List Lam.Slot} {w : Val} {ws : List Val} :
      SlotR A G (tk.getD i .strict) s w → ArgsR tk (i + 1) ss ws → ArgsR tk i (s :: ss) (w :: ws)

/-- After `i` arguments of a telescope with binder kinds `tk`: a partial
closure, or (saturated) a plain value. -/
def Res (tk : List Kind) (i : Nat) (v : Lam.Val) (w : Val) : Prop :=
  if i < tk.length then CloR A G tk i v w else VR A G v w

variable {L Q A G}

/-! ## Argument lists -/

theorem ArgsR.length {tk : List Kind} : ∀ {i : Nat} {ss : List Lam.Slot} {ws : List Val},
    ArgsR A G tk i ss ws → ws.length = ss.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => by simp [h.length]

theorem ArgsR.drop {tk : List Kind} : ∀ {i : Nat} {ss : List Lam.Slot} {ws : List Val} (r : Nat),
    ArgsR A G tk i ss ws → ArgsR A G tk (i + r) (ss.drop r) (ws.drop r)
  | _, _, _, 0, h => h
  | _, _, _, _ + 1, .nil => .nil
  | i, _, _, r + 1, .cons _ h => by
    have := h.drop r
    rwa [show i + 1 + r = i + (r + 1) by omega] at this

theorem ArgsR.take {tk : List Kind} : ∀ {i : Nat} {ss : List Lam.Slot} {ws : List Val} (r : Nat),
    ArgsR A G tk i ss ws → ArgsR A G tk i (ss.take r) (ws.take r)
  | _, _, _, 0, _ => .nil
  | _, _, _, _ + 1, .nil => .nil
  | _, _, _, r + 1, .cons hs h => .cons hs (h.take r)

theorem getD_nil_strict (j : Nat) : ([] : List Kind).getD j .strict = .strict := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_beyond {tk : List Kind} {i : Nat} (h : tk.length ≤ i) : tk.getD i .strict = .strict := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem mem_drop_mono {α : Type} {l : List α} {a : α} {i j : Nat} (h : i ≤ j) (ha : a ∈ l.drop j) :
    a ∈ l.drop i :=
  (List.drop_sublist_drop_left l h).subset ha

/-- Beyond the telescope every position is strict. -/
theorem ArgsR.beyond {tk : List Kind} : ∀ {i : Nat} {ss : List Lam.Slot} {ws : List Val} (j : Nat),
    tk.length ≤ i → ArgsR A G tk i ss ws → ArgsR A G [] j ss ws
  | _, _, _, _, _, .nil => .nil
  | _, _, _, j, hi, .cons hs h =>
    .cons (by rw [getD_nil_strict]; rw [getD_beyond hi] at hs; exact hs)
      (ArgsR.beyond (j + 1) (by omega) h)

/-- Strict positions from `j` on: any telescope whose remaining binders are
strict takes them. -/
theorem ArgsR.strict {tk : List Kind} : ∀ {j : Nat} {i : Nat} {ss : List Lam.Slot} {ws : List Val},
    (∀ q ∈ tk.drop j, q = .strict) → ArgsR A G [] i ss ws → ArgsR A G tk j ss ws
  | _, _, _, _, _, .nil => .nil
  | j, i, _, _, hrem, .cons hs h => by
    refine .cons ?_ (ArgsR.strict (fun q hq => hrem q (mem_drop_mono (Nat.le_succ j) hq)) h)
    rw [getD_nil_strict] at hs
    rcases Nat.lt_or_ge j tk.length with hj | hj
    · have hmem : tk[j] ∈ tk.drop j := by
        rw [List.drop_eq_getElem_cons hj]; exact List.mem_cons_self
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hrem _ hmem]
      exact hs
    · rw [getD_beyond hj]; exact hs

/-- Supplied arguments within the telescope, as `SlotsR` on the rest of its
kinds. -/
theorem ArgsR.slots {tk : List Kind} : ∀ {i : Nat} {ss : List Lam.Slot} {ws : List Val},
    i + ss.length ≤ tk.length → ArgsR A G tk i ss ws → SlotsR A G (tk.drop i) ss ws
  | _, _, _, _, .nil => .nil
  | i, _ :: ss, _, hl, .cons hs h => by
    have hi : i < tk.length := by simp at hl; omega
    rw [List.drop_eq_getElem_cons hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hs
    exact .cons hs (h.slots (by simp at hl ⊢; omega))

theorem SlotsR.take_kinds {tk : List Kind} : ∀ {ss : List Lam.Slot} {ws : List Val},
    SlotsR A G tk ss ws → SlotsR A G (tk.take ss.length) ss ws
  | _, _, .nil => .nil
  | _ :: _, _, .cons hs h => by simpa using SlotsR.cons hs h.take_kinds

/-- The supplied slots of a closure extended by more arguments within its
telescope. -/
theorem SlotsR.extend {tk : List Kind} {ss₀ : List Lam.Slot} {got : List Val}
    (h₀ : SlotsR A G tk ss₀ got) {ss : List Lam.Slot} {ws : List Val}
    (h : ArgsR A G tk ss₀.length ss ws) (hl : ss₀.length + ss.length ≤ tk.length) :
    SlotsR A G (tk.take (ss₀.length + ss.length)) (ss₀ ++ ss) (got ++ ws) := by
  have h1 := h₀.take_kinds
  have h2 := h.slots hl
  have e : tk.take (ss₀.length + ss.length) =
      tk.take ss₀.length ++ (tk.drop ss₀.length).take ss.length := by
    rw [List.take_add]
  rw [e]
  exact h1.append _ h2.take_kinds (by simp; have := h₀.length.2; omega)

theorem SlotsR.prefix : ∀ {tk₁ : List Kind} {ss : List Lam.Slot} {ws : List Val},
    SlotsR A G tk₁ ss ws → ∀ {tk₂ : List Kind}, tk₁ <+: tk₂ → SlotsR A G tk₂ ss ws
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .cons hs h, tk₂, ⟨u, hu⟩ => by
    subst hu
    exact .cons hs (h.prefix (List.prefix_append _ u))

theorem SlotsR.of_take {tk : List Kind} {n : Nat} {ss : List Lam.Slot} {ws : List Val}
    (h : SlotsR A G (tk.take n) ss ws) : SlotsR A G tk ss ws :=
  h.prefix (List.take_prefix n tk)

theorem modesAgree_thunks {ps : List (Mode × V3.BinderContract)} {tk : List Kind}
    (h : ModesAgree ps tk) : ps.map (·.1 == .name) = tk.map Kind.isName := by
  obtain ⟨hl, hk⟩ := h
  apply List.ext_getElem (by simp [hl])
  intro i h₁ h₂
  simp only [List.getElem_map]
  exact hk i _ _ (List.getElem?_eq_getElem (by simpa using h₁))
    (List.getElem?_eq_getElem (by simpa using h₂))

/-- A plain value: the remaining binders of a partial closure are strict. -/
theorem Res.vr {tk : List Kind} {i : Nat} {v : Lam.Val} {w : Val} (h : Res A G tk i v w)
    (hrem : ∀ q ∈ tk.drop i, q = .strict) : VR A G v w := by
  unfold Res at h
  split at h
  · exact .clo h hrem
  · exact h

/-! ## The simulation -/

/-- Application at clock bound `n`: of a partial closure to arguments of its
binder kinds (`gen`), and of a plain value to strict arguments (`vr`). -/
theorem app_sim (n : Nat) (hb : ∀ m < n, BodySim L Q A G m) : ∀ len : Nat,
    (∀ {tk : List Kind} {j : Nat} {fv : Lam.Val} {w : Val} {ss : List Lam.Slot} {ws : List Val},
      ss.length ≤ len → CloR A G tk j fv w → ArgsR A G tk j ss ws → ss ≠ [] →
      SimUpTo (Res A G tk (j + ss.length)) n (fun k => Lam.applyAll L k fv ss)
        (fun k => applyN Q k w ws)) ∧
    (∀ {fv : Lam.Val} {w : Val} {ss : List Lam.Slot} {ws : List Val},
      ss.length ≤ len → VR A G fv w → ArgsR A G [] 0 ss ws → ss ≠ [] →
      SimUpTo (VR A G) n (fun k => Lam.applyAll L k fv ss) (fun k => applyN Q k w ws))
  | 0 => ⟨fun hl _ _ hne => absurd (List.length_eq_zero_iff.1 (by omega)) hne,
          fun hl _ _ hne => absurd (List.length_eq_zero_iff.1 (by omega)) hne⟩
  | len + 1 => by
    have ih := app_sim n hb len
    have gen : ∀ {tk : List Kind} {j : Nat} {fv : Lam.Val} {w : Val} {ss : List Lam.Slot}
        {ws : List Val}, ss.length ≤ len + 1 → CloR A G tk j fv w → ArgsR A G tk j ss ws →
        ss ≠ [] → SimUpTo (Res A G tk (j + ss.length)) n (fun k => Lam.applyAll L k fv ss)
          (fun k => applyN Q k w ws) := by
      intro tk j fv w ss ws hlen hc hargs hne
      obtain ⟨hnl, hma, hlt, henv, hss0, hconv, htm, hj, hfv, hw⟩ := hc
      rename_i ps body ρ0 k0 vars0 ρt ss₀ got fuel bt
      subst hj hfv hw
      have hgl := hss0.length
      have hwl := hargs.length
      have htk : ps.length = tk.length := hma.1
      by_cases hunder : ss₀.length + ss.length < ps.length
      · -- under-saturated: the next closure on both sides
        have hres : Res A G tk (ss₀.length + ss.length)
            (.clos ((ss₀ ++ ss).reverse ++ ρ0) (lamsWith (ps.drop ((ss₀ ++ ss).length + 1)) body))
            (.clos ρt ps.length bt (got ++ ws)) := by
          unfold Res
          rw [if_pos (by omega)]
          refine .mk hnl hma (by simp; omega) henv
            ((hss0.extend hargs (by omega)).of_take) hconv htm (by simp) rfl rfl
        refine (SimUpTo.later fun m _ => SimUpTo.ok hres).congr (fun k => ?_) (fun k => ?_)
        · rw [applyAll_tele_partial L k body _ _ ss hne (by simp; omega)]
          rw [List.drop_drop, List.reverse_append, List.append_assoc, List.length_append,
            show ss₀.length + 1 + ss.length = ss₀.length + ss.length + 1 by omega]
        · have hwne : ws ≠ [] := fun e => hne (List.length_eq_zero_iff.1 (by rw [← hwl, e]; rfl))
          rw [applyN_under Q k hwne (by omega)]
      · -- saturated: the body one clock down, then the rest at the same clock
        obtain ⟨r, hrdef⟩ : ∃ r, r = ps.length - ss₀.length := ⟨_, rfl⟩
        have hr : r ≤ ss.length := by omega
        have hr1 : 1 ≤ r := by omega
        have hsplit : ss = ss.take r ++ ss.drop r := (List.take_append_drop r ss).symm
        have hwsplit : ws = ws.take r ++ ws.drop r := (List.take_append_drop r ws).symm
        have hsl : (ss.take r).length = r := by simp; omega
        -- the body's environments
        have hslots : SlotsR A G tk (ss₀ ++ ss.take r) (got ++ ws.take r) := by
          have := hss0.extend (hargs.take r) (by simp; omega)
          rw [show ss₀.length + (ss.take r).length = tk.length by omega, List.take_length] at this
          exact this
        have henv' := henv.push hslots (by simp; omega)
        have hconv' : conv A fuel (Cx.mk (pushParams vars0 ρt.length (tk.map Kind.isName))
            (ρt.length + ps.length) 0) body .ret = .ok bt := by
          rw [← modesAgree_thunks hma]; exact hconv
        have hbody : SimUpTo (VR A G) n
            (fun k => later k fun k => Lam.eval L k ((ss₀ ++ ss.take r).reverse ++ ρ0) body)
            (fun k => later k fun k => eval Q k ((got ++ ws.take r).reverse ++ ρt) [] bt) :=
          SimUpTo.later fun m hm => hb m (by omega) hconv' (by simp; omega) henv' htm
        have hrest : ∀ v v', VR A G v v' →
            SimUpTo (Res A G tk (ss₀.length + ss.length)) n
              (fun k => Lam.applyAll L k v (ss.drop r)) (fun k => applyN Q k v' (ws.drop r)) := by
          intro v v' hv
          have hres : ∀ {x : Lam.Val} {y : Val}, VR A G x y →
              Res A G tk (ss₀.length + ss.length) x y := fun hxy => by
            unfold Res; rw [if_neg (by omega)]; exact hxy
          by_cases hnil : ss.drop r = []
          · have hwnil : ws.drop r = [] := by
              rw [List.drop_eq_nil_iff] at hnil ⊢; omega
            rw [hnil, hwnil]
            exact (SimUpTo.ok (hres hv)).congr (fun k => Lam.applyAll_nil L k v)
              (fun k => applyN_nil' Q k v')
          · have hrestargs : ArgsR A G [] 0 (ss.drop r) (ws.drop r) :=
              ArgsR.beyond 0 (by omega) (hargs.drop r)
            exact (ih.2 (by simp; omega) hv hrestargs hnil).weaken fun _ _ h => hres h
        refine (SimUpTo.bind (ClockMono.later (eval_mono Q _ [] bt))
            (fun v' => applyN_mono Q v' _) hbody fun v v' hv => hrest v v' hv).congr
          (fun k => ?_) (fun k => ?_)
        · show Lam.applyAll L k _ ss = _
          conv => lhs; rw [hsplit]
          rw [applyAll_append, applyAll_tele L k body _ _ _ (by simp; omega)]
          simp [List.reverse_append, List.append_assoc]
        · rw [applyN_enter Q k (by omega) (by omega)]
          have e1 : (got ++ ws).take ps.length = got ++ ws.take r := by
            rw [List.take_append, List.take_of_length_le (by omega)]
            congr 2; omega
          have e2 : (got ++ ws).drop ps.length = ws.drop r := by
            rw [List.drop_append, List.drop_of_length_le (by omega)]
            simp only [List.nil_append]; congr 1; omega
          rw [e1, e2]
    refine ⟨gen, ?_⟩
    intro fv w ss ws hlen hv hargs hne
    cases hv with
    | clo hc hrem =>
      rename_i tk j
      have := gen hlen hc (ArgsR.strict hrem hargs) hne
      refine this.weaken fun x y hxy => hxy.vr fun q hq => hrem q ?_
      exact mem_drop_mono (Nat.le_add_right j ss.length) hq
    | _ =>
      obtain ⟨s, ss', rfl⟩ := List.exists_cons_of_ne_nil hne
      exact (SimUpTo.stuck _).congr
        (fun k => applyAll_not_clos L k _ s ss' (by intros; nofun)) (fun _ => rfl)

end IxCC.Anf.Convert.Proof
