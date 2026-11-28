import IxCC.Own.Proof.Mono
import IxCC.Own.Proof.Heap
import IxCC.Own.Immortal
import IxCC.Fir.Proof.Mono
import IxCC.Sem.ValModel

/-! # The Phase 1 Own refinement (`Own.immortal_refines`)

The Phase 1 Own program of a Fir program `F` is the
embedding `Own.immortal F` run under the immortal allocation policy. It runs
in **lock step** with `F` at every clock (`lock`): the same charges, so the
same clock; a Fir value is an Own value that denotes it in the final heap
(`Den`, `Heap.value?`); a Fir timeout or trap is Own's; and the heap only
grows (`Ext`) and stays immortal (`Heap.immortalOk`: every cell live,
static, saturated, its fields immediates or older cells). A stuck Fir run
imposes nothing.

The invariant: Fir's environment and join stack are Own's up to
denotation (`EnvO`, `JO`: the same entries, Own's bodies the embedding of
Fir's), in a heap that is `immortalOk`. The proof is a strong induction on
the clock and, within one clock, a well-founded induction on Fir's measure
(the code plus the uncharged join bodies), through both evaluators'
bind-form equations (decision D-1). The only premise on `F` is that its
`Bool` pins, where its table lists them, have no fields (`BoolsOk`), so
that a Boolean primitive's Fir constructor is Own's field-less immediate;
`Fir.lower` checks it. -/

set_option autoImplicit false

namespace IxCC.Own.Proof

open IxCC.Sem (Result later ClockMono Sim Forall2 ModelRel)
open IxCC.Fir (Var FunId JoinId Arg)

/-- The `Bool` pins of a Fir program, where its table lists them, have no
fields. -/
def BoolsOk (F : Fir.Program) : Prop :=
  ∀ (b : Bool) (c : Key.CtorKey) (info : Fir.CtorInfo),
    (if b then F.known.boolTrue else F.known.boolFalse) = some c →
      Fir.CtorInfo.ofKey F.ctors c = some info → info.arity = 0

/-- Every Fir variable is an Own variable denoting its value. -/
def EnvO (H : Heap) (ρf : Fir.Env) (ρo : Env) : Prop :=
  ∀ x w, ρf.get? x = some w → ∃ v, ρo.get? x = some v ∧ Den H v w

/-- A Fir join entry and its Own entry. -/
def EntO (H : Heap) (ef : Fir.JEntry) (eo : JEntry) : Prop :=
  eo.id = ef.id ∧ eo.charged = ef.charged ∧ eo.isRec = ef.isRec ∧ eo.params = ef.params ∧
    eo.body = immCode ef.body ∧ EnvO H ef.env eo.env

/-- Fir's join stack against Own's, entry by entry. -/
abbrev JO (H : Heap) : List Fir.JEntry → List JEntry → Prop := Forall2 (EntO H)

/-- Lock step: Fir's outcome against Own's, from heap `H`. -/
inductive Lock (H : Heap) : Result Fir.Val → Result (RVal × Heap) → Prop
  | ok {w : Fir.Val} {v : RVal} {H' : Heap} : Den H' v w → H'.immortalOk = true → Ext H H' →
      Lock H (.ok w) (.ok (v, H'))
  | timeout : Lock H .timeout .timeout
  | trap : Lock H .trap .trap
  | resource (f : Sem.Resource) : Lock H (.resource f) (.resource f)
  | stuck {r : Result (RVal × Heap)} : Lock H .stuck r

/-! ## Environments -/

section

variable {H H' : Heap}

theorem EnvO.ext (hx : Ext H H') {ρf : Fir.Env} {ρo : Env} (h : EnvO H ρf ρo) : EnvO H' ρf ρo :=
  fun x w hw => (h x w hw).imp fun _ ⟨hv, hd⟩ => ⟨hv, hd.ext hx⟩

theorem EnvO.insert {ρf : Fir.Env} {ρo : Env} (h : EnvO H ρf ρo) (x : Var) {v : RVal} {w : Fir.Val}
    (hd : Den H v w) : EnvO H (ρf.insert x w) (ρo.insert x v) := by
  intro y w' hw'
  by_cases hy : y = x
  · subst hy
    rw [Src.NatMap.get?_insert_self] at hw'
    cases hw'
    exact ⟨v, Src.NatMap.get?_insert_self _ _ _, hd⟩
  · rw [Src.NatMap.get?_insert_ne _ _ hy] at hw'
    obtain ⟨v', hv', hd'⟩ := h y w' hw'
    exact ⟨v', by rw [Src.NatMap.get?_insert_ne _ _ hy]; exact hv', hd'⟩

theorem EnvO.bindAll {ρf : Fir.Env} {ρo : Env} (h : EnvO H ρf ρo) :
    ∀ (xs : List Var) {vs : List RVal} {ws : List Fir.Val}, Forall2 (Den H) vs ws →
      EnvO H (Fir.bindAll ρf xs ws) (Own.bindAll ρo xs vs)
  | [], _, _, hvs => by cases hvs <;> exact h
  | _ :: _, _, _, .nil => h
  | x :: xs, _, _, .cons hd hvs => (h.insert x hd).bindAll xs hvs

theorem envO_leaf (H : Heap) : EnvO H .leaf .leaf := fun _ _ h => by simp [Src.NatMap.get?] at h

theorem JO.ext (hx : Ext H H') {Jf : List Fir.JEntry} {Jo : List JEntry} (h : JO H Jf Jo) : JO H' Jf Jo :=
  h.mono fun _ _ ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆.ext hx⟩

theorem JO.lookup {j : JoinId} :
    ∀ {Jf : List Fir.JEntry} {Jo : List JEntry}, JO H Jf Jo → ∀ {ef : Fir.JEntry} {rf : List Fir.JEntry},
      Fir.lookupJ j Jf = some (ef, rf) →
      ∃ eo ro, lookupJ j Jo = some (eo, ro) ∧ EntO H ef eo ∧ JO H rf ro
  | _, _, .nil, _, _, h => by simp [Fir.lookupJ] at h
  | ef' :: Jf, eo' :: Jo, .cons he hJ, ef, rf, h => by
    simp only [Fir.lookupJ] at h
    simp only [lookupJ, he.1]
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [↓reduceIte, *]
      exact ⟨_, _, rfl, he, hJ⟩
    · simp only [↓reduceIte, *]
      exact JO.lookup hJ h

theorem JO.after {ef : Fir.JEntry} {eo : JEntry} (he : EntO H ef eo) {rf : List Fir.JEntry}
    {ro : List JEntry} (hr : JO H rf ro) : JO H (ef.after rf) (eo.after ro) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := he
  unfold Fir.JEntry.after JEntry.after
  rw [h₃]
  split
  · exact .cons ⟨h₁, rfl, rfl, h₄, h₅, h₆⟩ hr
  · exact hr

end

/-! ## Values -/

section

variable {H : Heap}

theorem den_lit_inv {v : RVal} {l : Lam.Lit} (h : Den H v (.lit l)) : v = .lit l := by
  cases v with
  | lit l' => simp only [Den, Heap.value?, toFir, Option.some.injEq, Fir.Val.lit.injEq] at h; rw [h]
  | ctor0 c => simp [Den, Heap.value?, toFir] at h
  | erased => simp [Den, Heap.value?, toFir] at h
  | loc ℓ =>
    obtain ⟨_, _, _, _, _, hw, _⟩ := den_loc h
    cases hw

theorem den_erased_inv {v : RVal} (h : Den H v .erased) : v = .erased := by
  cases v with
  | lit l' => simp [Den, Heap.value?, toFir] at h
  | ctor0 c => simp [Den, Heap.value?, toFir] at h
  | erased => rfl
  | loc ℓ =>
    obtain ⟨_, _, _, _, _, hw, _⟩ := den_loc h
    cases hw

theorem dens_of_toFirList {fuel : Nat} (hf : fuel ≤ H.size + 1) :
    ∀ {vs : List RVal} {ws : List Fir.Val}, toFirList H fuel vs = some ws → Forall2 (Den H) vs ws
  | [], ws, h => by simp only [toFirList, Option.some.injEq] at h; subst h; exact .nil
  | v :: vs, ws, h => by
    simp only [toFirList] at h
    cases hv : toFir H fuel v with
    | none => rw [hv] at h; cases h
    | some w =>
      cases hvs : toFirList H fuel vs with
      | none => rw [hv, hvs] at h; cases h
      | some ws' =>
        rw [hv, hvs] at h
        simp only [Option.some.injEq] at h
        subst h
        exact .cons (toFir_ext (Ext.refl H) hf hv) (dens_of_toFirList hf hvs)

theorem asCtor_den (K : Lam.Known) {v : RVal} {w : Fir.Val} (h : Den H v w) :
    (∀ key fs, w.asCtor K = some (key, fs) → ∃ vs, v.asCtor K H = some (key, vs) ∧ Forall2 (Den H) vs fs) ∧
      (w.asCtor K = none → v.asCtor K H = none) := by
  cases v with
  | lit l =>
    have : w = .lit l := by simp only [Den, Heap.value?, toFir, Option.some.injEq] at h; exact h.symm
    subst this
    rcases l with (_ | n) | s
    · refine ⟨fun key fs hk => ?_, fun hk => ?_⟩
      · simp only [Fir.Val.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hk
        obtain ⟨c, hc, rfl, rfl⟩ := hk
        exact ⟨[], by simp [RVal.asCtor, hc], .nil⟩
      · simp only [Fir.Val.asCtor, Option.map_eq_none_iff] at hk
        simp [RVal.asCtor, hk]
    · refine ⟨fun key fs hk => ?_, fun hk => ?_⟩
      · simp only [Fir.Val.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hk
        obtain ⟨c, hc, rfl, rfl⟩ := hk
        exact ⟨[.lit (.nat n)], by simp [RVal.asCtor, hc], .cons (den_lit H _) .nil⟩
      · simp only [Fir.Val.asCtor, Option.map_eq_none_iff] at hk
        simp [RVal.asCtor, hk]
    · exact ⟨fun _ _ hk => by simp [Fir.Val.asCtor] at hk, fun _ => rfl⟩
  | ctor0 c =>
    have : w = .ctor c [] := by simp only [Den, Heap.value?, toFir, Option.some.injEq] at h; exact h.symm
    subst this
    exact ⟨fun key fs hk => by
      simp only [Fir.Val.asCtor, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨[], rfl, .nil⟩, fun hk => by simp [Fir.Val.asCtor] at hk⟩
  | erased =>
    have : w = .erased := by simp only [Den, Heap.value?, toFir, Option.some.injEq] at h; exact h.symm
    subst this
    exact ⟨fun _ _ hk => by simp [Fir.Val.asCtor] at hk, fun _ => rfl⟩
  | loc ℓ =>
    obtain ⟨r, m, b, ws, hc, rfl, hws⟩ := den_loc h
    refine ⟨fun key fs hk => ?_, fun hk => by simp [Fir.Val.asCtor] at hk⟩
    simp only [Fir.Val.asCtor, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact ⟨b.fields, by simp [RVal.asCtor, hc], dens_of_toFirList (by omega) hws⟩

theorem natArgs_den : ∀ {vs : List RVal} {ws : List Fir.Val}, Forall2 (Den H) vs ws →
    Own.natArgs vs = Fir.natArgs ws
  | _, _, .nil => rfl
  | v :: _, w :: _, .cons hd hvs => by
    cases w with
    | lit l =>
      rw [den_lit_inv hd]
      rcases l with n | s
      · simp [Own.natArgs, Fir.natArgs, natArgs_den hvs]
      · rfl
    | ctor c fs =>
      cases v with
      | lit l => simp [Den, Heap.value?, toFir] at hd
      | _ => rfl
    | erased => rw [den_erased_inv hd]; rfl

theorem evalArg_den {ρf : Fir.Env} {ρo : Env} (h : EnvO H ρf ρo) (a : Arg) {w : Fir.Val}
    (hw : a.eval ρf = some w) : ∃ v, evalArg ρo a = some v ∧ Den H v w := by
  cases a with
  | var x => exact h x w hw
  | lit l => cases hw; exact ⟨_, rfl, den_lit H l⟩
  | erased => cases hw; exact ⟨_, rfl, den_erased H⟩

theorem evalArgs_den {ρf : Fir.Env} {ρo : Env} (h : EnvO H ρf ρo) :
    ∀ (as : List Arg) {ws : List Fir.Val}, Fir.evalArgs ρf as = some ws →
      ∃ vs, evalArgs ρo as = some vs ∧ Forall2 (Den H) vs ws
  | [], ws, hw => by simp only [Fir.evalArgs, Option.some.injEq] at hw; subst hw; exact ⟨[], rfl, .nil⟩
  | a :: as, ws, hw => by
    rw [Fir.evalArgs_cons] at hw
    cases ha : a.eval ρf with
    | none => rw [ha] at hw; cases hw
    | some w =>
      rw [ha] at hw
      cases has : Fir.evalArgs ρf as with
      | none => rw [has] at hw; cases hw
      | some ws' =>
        rw [has] at hw
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hw
        subst hw
        obtain ⟨v, hv, hd⟩ := evalArg_den h a ha
        obtain ⟨vs, hvs, hds⟩ := evalArgs_den h as has
        exact ⟨v :: vs, by rw [evalArgs_cons, hv, hvs]; rfl, .cons hd hds⟩

end

/-! ## Lock-step combinators -/

namespace Lock

variable {H : Heap}

theorem ext {H' : Heap} (hx : Ext H H') {r : Result Fir.Val} {s : Result (RVal × Heap)}
    (h : Lock H' r s) : Lock H r s := by
  cases h with
  | ok hd hok hx' => exact .ok hd hok (hx.trans hx')
  | timeout => exact .timeout
  | trap => exact .trap
  | resource f => exact .resource f
  | stuck => exact .stuck

theorem bind {r : Result Fir.Val} {s : Result (RVal × Heap)} {f : Fir.Val → Result Fir.Val}
    {g : RVal × Heap → Result (RVal × Heap)} (h : Lock H r s)
    (hk : ∀ w v H', Den H' v w → H'.immortalOk = true → Ext H H' → Lock H' (f w) (g (v, H'))) :
    Lock H (r.bind f) (s.bind g) := by
  cases h with
  | ok hd hok hx => exact (hk _ _ _ hd hok hx).ext hx
  | timeout => exact .timeout
  | trap => exact .trap
  | resource f => exact .resource f
  | stuck => exact .stuck

theorem later {k : Nat} {r : Nat → Result Fir.Val} {s : Nat → Result (RVal × Heap)}
    (h : ∀ k', k = k' + 1 → Lock H (r k') (s k')) : Lock H (Sem.later k r) (Sem.later k s) := by
  cases k with
  | zero => exact .timeout
  | succ k' => exact h k' rfl

theorem ofOption {α : Type} {o : Option α} {f : α → Result Fir.Val} {s : Result (RVal × Heap)}
    (h : ∀ x, o = some x → Lock H (f x) s) : Lock H ((Result.ofOption o).bind f) s := by
  cases o with
  | none => exact .stuck
  | some x => exact h x rfl

end Lock

/-! ## Right-hand sides -/

section

variable {F : Fir.Program} {H : Heap}

/-- An immortal allocation of denoting fields keeps the heap immortal. -/
theorem immortalOk_alloc (hH : H.immortalOk = true) {c : Fir.CtorInfo} {vs : List RVal} {ws : List Fir.Val}
    (hds : Forall2 (Den H) vs ws) (hl : vs.length = c.arity) (hc : c.fieldless = false) :
    (H.alloc .immortal { ctor := c, fields := vs }).2.immortalOk = true := by
  have hlocs : ∀ ℓ', RVal.loc ℓ' ∈ vs → ℓ' < H.size := by
    intro ℓ' hm
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
    obtain ⟨w, -, hd⟩ := hds.get hi
    obtain ⟨_, _, _, _, hcell, _, _⟩ := den_loc hd
    exact cell?_some hcell
  have zip_append : ∀ (l : List Cell) (x : Cell) (i : Nat),
      (l ++ [x]).zipIdx i = l.zipIdx i ++ [(x, i + l.length)] := by
    intro l x
    induction l with
    | nil => intro i; simp
    | cons y l ih => intro i; simp [ih, Nat.add_assoc, Nat.add_comm 1]
  unfold Heap.immortalOk at hH ⊢
  simp only [Heap.alloc, Array.toList_push, zip_append, List.all_append, hH, Bool.true_and,
    List.all_cons, List.all_nil, Bool.and_true, AllocPol.mode, Nat.zero_add]
  simp only [Fir.CtorInfo.fieldless, beq_eq_false_iff_ne, ne_eq] at hc
  simp only [hl, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  refine ⟨by omega, fun x hx => ?_⟩
  cases x with
  | loc ℓ' => simpa [Heap.size] using hlocs ℓ' hx
  | _ => rfl

/-! ### Array primitives

Fir computes an array primitive by `Src.ArrOp.eval` at `Fir.model`; Own by the same function over
pending values (`pmodel`), then places the result (`arrStep`). A pending value denotes a Fir value
(`PDen`): an Own value by `Den`, a pending array by its elements. That relation respects the two
models (`modelRel_pden`), so `Src.ArrOp.eval_refines` relates the two outcomes, and placing a
denoting pending value under the immortal policy gives a denoting value in an extended immortal
heap (`place_den`). -/

mutual

/-- A pending Own value denotes a Fir value in `H`. -/
inductive PDen (H : Heap) : PVal → Fir.Val → Prop
  | val {v : RVal} {w : Fir.Val} : Den H v w → PDen H (.val v) w
  | arr {ps : List PVal} {ws : List Fir.Val} :
      PDens H ps ws → PDen H (.arr ps) (.ctor (Fir.arrInfo ws.length) ws)

/-- Pending values denote Fir values, one by one. -/
inductive PDens (H : Heap) : List PVal → List Fir.Val → Prop
  | nil : PDens H [] []
  | cons {p : PVal} {w : Fir.Val} {ps : List PVal} {ws : List Fir.Val} :
      PDen H p w → PDens H ps ws → PDens H (p :: ps) (w :: ws)

end

mutual

theorem PDen.ext {H H' : Heap} (hx : Ext H H') :
    ∀ (p : PVal) {w : Fir.Val}, PDen H p w → PDen H' p w
  | .val _, _, h => by cases h with | val hd => exact .val (hd.ext hx)
  | .arr ps, _, h => by cases h with | arr hps => exact .arr (PDens.ext hx ps hps)

theorem PDens.ext {H H' : Heap} (hx : Ext H H') :
    ∀ (ps : List PVal) {ws : List Fir.Val}, PDens H ps ws → PDens H' ps ws
  | [], _, h => by cases h; exact .nil
  | p :: ps, _, h => by
    cases h with | cons hp hps => exact .cons (PDen.ext hx p hp) (PDens.ext hx ps hps)

end

theorem pdens_of_forall2 {H : Heap} :
    ∀ {ws : List Fir.Val} {ps : List PVal}, Forall2 (fun w p => PDen H p w) ws ps → PDens H ps ws
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (pdens_of_forall2 hs)

theorem forall2_of_pdens {H : Heap} :
    ∀ {ps : List PVal} {ws : List Fir.Val}, PDens H ps ws → Forall2 (fun w p => PDen H p w) ws ps
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h (forall2_of_pdens hs)

theorem forall2_val_of_dens {H : Heap} :
    ∀ {vs : List RVal} {ws : List Fir.Val}, Forall2 (Den H) vs ws →
      Forall2 (fun w p => PDen H p w) ws (vs.map PVal.val)
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (.val h) (forall2_val_of_dens hs)

/-- **Denotation respects the two array models**, Fir's as the source and Own's pending one as
the target. -/
theorem modelRel_pden (H : Heap) : ModelRel Fir.model (pmodel H) (fun w p => PDen H p w) where
  nat _ := .val (den_lit H _)
  asNat {w p n} h hw := by
    cases w with
    | lit l =>
      cases l with
      | nat m =>
        simp only [Fir.model, Fir.Val.asNat, Option.some.injEq] at hw
        subst hw
        cases h with
        | val hd => rw [den_lit_inv hd]; rfl
      | str _ => simp [Fir.model, Fir.Val.asNat] at hw
    | ctor _ _ => simp [Fir.model, Fir.Val.asNat] at hw
    | erased => simp [Fir.model, Fir.Val.asNat] at hw
  arr h := .arr (pdens_of_forall2 h)
  asArr {w p ws} h hw := by
    cases w with
    | ctor c ws0 =>
      simp only [Fir.model, Fir.Val.asArr] at hw
      split at hw
      · next hc =>
        simp only [Option.some.injEq] at hw
        subst hw
        cases h with
        | val hd =>
          rename_i v
          cases v with
          | loc ℓ =>
            obtain ⟨r, m, b, ws', hcell, hw', hl⟩ := den_loc hd
            cases hw'
            refine ⟨b.fields.map PVal.val, ?_,
              forall2_val_of_dens (dens_of_toFirList (Nat.le_succ _) hl)⟩
            simp [pmodel, PVal.asArr, RVal.asArr, hcell, hc]
          | ctor0 c' =>
            simp only [Den, Heap.value?, toFir, Option.some.injEq, Fir.Val.ctor.injEq] at hd
            obtain ⟨rfl, rfl⟩ := hd
            exact ⟨[], by simp [pmodel, PVal.asArr, RVal.asArr, hc], .nil⟩
          | lit _ => simp [Den, Heap.value?, toFir] at hd
          | erased => simp [Den, Heap.value?, toFir] at hd
        | arr hps => exact ⟨_, rfl, forall2_of_pdens hps⟩
      · cases hw
    | lit _ => simp [Fir.model, Fir.Val.asArr] at hw
    | erased => simp [Fir.model, Fir.Val.asArr] at hw
  list _ := .val (den_erased H)
  asList _ hw := by simp [Fir.model] at hw

mutual

/-- Placing a denoting pending value under the immortal policy: a denoting value in an extended
immortal heap. -/
theorem place_den {H : Heap} (hH : H.immortalOk = true) :
    ∀ (p : PVal) {w : Fir.Val}, PDen H p w →
      Den (p.place .immortal H).2 (p.place .immortal H).1 w ∧ Ext H (p.place .immortal H).2 ∧
        (p.place .immortal H).2.immortalOk = true
  | .val _, _, h => by
    cases h with
    | val hd => exact ⟨hd, Ext.refl H, hH⟩
  | .arr ps, _, h => by
    cases h with
    | arr hps =>
      rename_i ws
      obtain ⟨hds, hx, hok⟩ := placeList_den hH ps hps
      simp only [PVal.place]
      generalize PVal.placeList .immortal H ps = r at hds hx hok ⊢
      obtain ⟨vs, H'⟩ := r
      dsimp only at hds hx hok ⊢
      cases vs with
      | nil =>
        cases hds
        exact ⟨den_ctor0 H' _, hx, hok⟩
      | cons v vs' =>
        have hlen := hds.length
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
        rw [← hlen]
        refine ⟨den_alloc .immortal H' _ hds, hx.trans (Ext.alloc .immortal H' _), ?_⟩
        refine immortalOk_alloc hok hds ?_ ?_
        · simp [Fir.CtorInfo.arity, Fir.arrInfo]
        · simp [Fir.CtorInfo.fieldless, Fir.CtorInfo.arity, Fir.arrInfo]

theorem placeList_den {H : Heap} (hH : H.immortalOk = true) :
    ∀ (ps : List PVal) {ws : List Fir.Val}, PDens H ps ws →
      Forall2 (Den (PVal.placeList .immortal H ps).2) (PVal.placeList .immortal H ps).1 ws ∧
        Ext H (PVal.placeList .immortal H ps).2 ∧
        (PVal.placeList .immortal H ps).2.immortalOk = true
  | [], _, h => by
    cases h
    exact ⟨.nil, Ext.refl H, hH⟩
  | p :: ps, _, h => by
    cases h with
    | cons hp hps =>
      obtain ⟨hd1, hx1, hok1⟩ := place_den hH p hp
      obtain ⟨hds2, hx2, hok2⟩ := placeList_den hok1 ps (PDens.ext hx1 ps hps)
      simp only [PVal.placeList]
      exact ⟨.cons (hd1.ext hx2) hds2, hx1.trans hx2, hok2⟩

end

/-- **An array primitive in lock step**: Fir's `Src.ArrOp.eval` against Own's `arrStep`. -/
theorem arrStep_lock {vs : List RVal} {ws : List Fir.Val} (hH : H.immortalOk = true)
    (hds : Forall2 (Den H) vs ws) (op : Src.ArrOp) :
    Lock H (op.eval Fir.model ws) (arrStep .immortal H op vs) := by
  have hR := Src.ArrOp.eval_refines (modelRel_pden H) op (forall2_val_of_dens hds)
  unfold arrStep
  generalize op.eval Fir.model ws = r at hR ⊢
  generalize hs : op.eval (pmodel H) (vs.map PVal.val) = s at hR ⊢
  have hns : ∀ f, s ≠ .resource f := fun f h => Src.ArrOp.eval_ne_resource _ op _ f (hs.trans h)
  cases hR with
  | ok hp =>
    obtain ⟨hd, hx, hok⟩ := place_den hH _ hp
    exact .ok hd hok hx
  | timeout => exact .timeout
  | trap => exact .trap
  | stuck => exact .stuck
  | resource f => exact absurd rfl (hns f)

theorem isArrPrim_immRhs (r : Fir.Rhs) : (immRhs r).isArrPrim = r.isArrPrim := by
  cases r <;> rfl

mutual

/-- The embedding keeps a body free of array-primitive bindings. -/
theorem immCode_arrFree : ∀ (c : Fir.Code), c.arrFree = true → (immCode c).arrFree = true
  | .bind _ r k, h => by
    simp only [Fir.Code.arrFree, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [immCode, Code.arrFree, isArrPrim_immRhs, h.1, Bool.not_false, Bool.true_and]
    exact immCode_arrFree k h.2
  | .jp _ _ _ b k, h => by
    simp only [Fir.Code.arrFree, Bool.and_eq_true] at h
    simp only [immCode, Code.arrFree, immCode_arrFree b h.1, immCode_arrFree k h.2, Bool.and_self]
  | .case _ alts d, h => by
    simp only [Fir.Code.arrFree, Bool.and_eq_true] at h
    simp only [immCode, Code.arrFree, immAlts_arrFree alts h.1, immOpt_arrFree d h.2, Bool.and_self]
  | .jmp .., _ => rfl
  | .ret _, _ => rfl
  | .tcall .., _ => rfl
  | .trap, _ => rfl

theorem immAlts_arrFree : ∀ (alts : List Fir.Alt), Fir.Code.altsArrFree alts = true →
    Code.altsArrFree (immAlts alts) = true
  | [], _ => rfl
  | .mk _ b :: as, h => by
    simp only [Fir.Code.altsArrFree, Bool.and_eq_true] at h
    simp only [immAlts, Code.altsArrFree, immCode_arrFree b h.1, immAlts_arrFree as h.2,
      Bool.and_self]

theorem immOpt_arrFree :
    ∀ (d : Option Fir.Code), Fir.Code.optArrFree d = true → Code.optArrFree (immOpt d) = true
  | none, _ => rfl
  | some c, h => immCode_arrFree c h

end

theorem rhs_lock (hb : BoolsOk F) (hH : H.immortalOk = true) (ρf : Fir.Env) (ρo : Env) (henv : EnvO H ρf ρo) (r : Fir.Rhs)
    (hr : ∀ f as, r ≠ .call f as) (ha : r.isArrPrim = false) :
    Lock H (Fir.evalRhs F ρf r) (evalRhs .immortal (immortal F).tables ρo H (immRhs r)) := by
  cases r with
  | arg a =>
    simp only [Fir.evalRhs, immRhs, evalRhs]
    cases hw : a.eval ρf with
    | none => exact .stuck
    | some w =>
      obtain ⟨v, hv, hd⟩ := evalArg_den henv a hw
      simp only [Result.ofOption, hv]
      exact .ok hd hH (Ext.refl H)
  | ctor c as =>
    simp only [Fir.evalRhs, immRhs, evalRhs]
    cases hws : Fir.evalArgs ρf as with
    | none => exact .stuck
    | some ws =>
      obtain ⟨vs, hvs, hds⟩ := evalArgs_den henv as hws
      simp only [hvs]
      have hlen : vs.length = ws.length := hds.length
      by_cases hl : ws.length = c.arity
      · simp only [hl, hlen, ↓reduceIte]
        cases hf : c.fieldless with
        | true =>
          simp only [↓reduceIte]
          have : ws = [] := by
            simp only [Fir.CtorInfo.fieldless, beq_iff_eq] at hf
            exact List.eq_nil_of_length_eq_zero (by omega)
          subst this
          exact .ok (den_ctor0 H c) hH (Ext.refl H)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact .ok (den_alloc .immortal H c hds) (immortalOk_alloc hH hds (by omega) hf) (Ext.alloc _ _ _)
      · simp only [hl, hlen, ↓reduceIte]; exact .stuck
  | proj x c i =>
    simp only [Fir.evalRhs, immRhs, evalRhs]
    cases hw : ρf.get? x with
    | none => exact .stuck
    | some w =>
      obtain ⟨v, hv, hd⟩ := henv x w hw
      simp only [hv]
      obtain ⟨hsome, _⟩ := asCtor_den F.known hd
      cases hk : w.asCtor F.known with
      | none => exact .stuck
      | some p =>
        obtain ⟨key, fs⟩ := p
        obtain ⟨vs, hvs, hds⟩ := hsome key fs hk
        simp only [immortal, Program.tables, hvs]
        by_cases hkc : key = c
        · simp only [hkc, ↓reduceIte]
          cases hfi : fs[i]? with
          | none =>
            have : vs[i]? = none := by
              rw [List.getElem?_eq_none_iff] at hfi ⊢; rw [hds.length]; exact hfi
            simp only [this, Result.ofOption]; exact .stuck
          | some wf =>
            obtain ⟨vf, hvf, hdf⟩ := hds.get' hfi
            simp only [hvf, Result.ofOption, Result.map, Result.bind_ok]
            exact .ok hdf hH (Ext.refl H)
        · simp only [hkc, ↓reduceIte]; exact .stuck
  | prim op as =>
    simp only [Fir.evalRhs, immRhs, evalRhs]
    cases hws : Fir.evalArgs ρf as with
    | none => exact .stuck
    | some ws =>
      obtain ⟨vs, hvs, hds⟩ := evalArgs_den henv as hws
      simp only [hvs, Fir.primResult, primResult, natArgs_den hds, immortal, Program.tables,
        Fir.arrResult_of_not_arr (show op.isArr = false from ha)]
      cases hn : Fir.natArgs ws with
      | none => dsimp only; exact .stuck
      | some ns =>
        dsimp only
        cases hs : op.sem ns with
        | none => dsimp only; exact .stuck
        | some pr =>
          cases pr with
          | nat n =>
            simp only [Result.map, Result.bind_ok]
            exact .ok (den_lit H _) hH (Ext.refl H)
          | bool b =>
            cases hpin : (if b then F.known.boolTrue else F.known.boolFalse) with
            | none =>
              simp only [Fir.boolVal, hpin, Result.ofOption]; exact .stuck
            | some c =>
              simp only [Fir.boolVal, hpin, ctor0Of, Fir.Program.ctorInfo?]
              cases hi : Fir.CtorInfo.ofKey F.ctors c with
              | none => simp only [Option.map_none, Result.ofOption]; exact .stuck
              | some info =>
                have ha := hb b c info hpin hi
                have hfl : info.fieldless = true := by
                  simp only [Fir.CtorInfo.fieldless, beq_iff_eq]; exact ha
                simp only [Option.map_some, Result.ofOption, hfl, ↓reduceIte, Result.map, Result.bind_ok]
                exact .ok (den_ctor0 H info) hH (Ext.refl H)
  | call f as => exact absurd rfl (hr f as)

end

/-! ## The lock step -/

section

variable {F : Fir.Program} (hb : BoolsOk F)

theorem immortal_fun? (f : FunId) : (immortal F).fun? f = (F.fun? f).map immFun := by
  simp only [Program.fun?, immortal, Fir.Program.fun?]
  exact get?_map immFun F.funs f

variable {k : Nat}
  (ih : ∀ j < k, ∀ (ρf : Fir.Env) (Jf : List Fir.JEntry) (c : Fir.Code) (ρo : Env) (Jo : List JEntry)
    (H : Heap), EnvO H ρf ρo → JO H Jf Jo → H.immortalOk = true →
    Lock H (Fir.eval F j ρf Jf c) (eval .immortal (immortal F) j ρo Jo H (immCode c)))
include hb ih

omit hb in
theorem call_lock (f : FunId) {H : Heap} (hH : H.immortalOk = true) {vs : List RVal} {ws : List Fir.Val}
    (hds : Forall2 (Den H) vs ws) :
    Lock H (Fir.evalCall F k f ws) (evalCall .immortal (immortal F) k f vs H) := by
  rw [Fir.evalCall_eq, evalCall_eq, immortal_fun?]
  cases hf : F.fun? f with
  | none => exact .stuck
  | some fd =>
    simp only [Result.ofOption, Option.map_some, Result.bind_ok, Fir.callFun, callFun, immFun]
    rw [List.length_map]
    by_cases hl : ws.length = fd.params.length
    · have hl' : vs.length = fd.params.length := by rw [hds.length]; exact hl
      simp only [hl, hl', ↓reduceIte]
      refine Lock.later fun k' hk => ?_
      exact ih k' (by omega) _ [] fd.body _ [] H ((envO_leaf H).bindAll _ hds) .nil hH
    · have hl' : ¬ vs.length = fd.params.length := by rw [hds.length]; exact hl
      simp only [hl, hl', ↓reduceIte]
      exact .stuck

set_option linter.unusedSectionVars false in
mutual

theorem eval_lock (ρf : Fir.Env) (Jf : List Fir.JEntry) (c : Fir.Code) (ρo : Env) (Jo : List JEntry)
    (H : Heap) (henv : EnvO H ρf ρo) (hJ : JO H Jf Jo) (hH : H.immortalOk = true) :
    Lock H (Fir.eval F k ρf Jf c) (eval .immortal (immortal F) k ρo Jo H (immCode c)) := by
  match c with
  | .bind x r c' =>
    by_cases hr : ∃ f as, r = .call f as
    · obtain ⟨f, as, rfl⟩ := hr
      rw [Fir.eval_bindCall]
      simp only [immCode, immRhs]
      rw [eval_bindCall]
      refine Lock.ofOption fun ws hws => ?_
      obtain ⟨vs, hvs, hds⟩ := evalArgs_den henv as hws
      rw [hvs]
      simp only [Result.ofOption, Result.bind_ok]
      refine (call_lock ih f hH hds).bind fun w v H' hd hok hx => ?_
      exact eval_lock _ Jf c' _ Jo H' ((henv.ext hx).insert x hd) (hJ.ext hx) hok
    · have hr' : ∀ f as, r ≠ .call f as := fun f as h => hr ⟨f, as, h⟩
      rw [Fir.eval_bindRhs _ _ _ _ _ _ _ hr']
      cases ha : r.isArrPrim
      · simp only [immCode]
        rw [eval_bindRhs _ _ _ _ _ _ _ _ _ (by cases r <;> simp_all [immRhs])
          (by rw [isArrPrim_immRhs]; exact ha)]
        refine (rhs_lock hb hH ρf ρo henv r hr' ha).bind fun w v H' hd hok hx => ?_
        exact eval_lock _ Jf c' _ Jo H' ((henv.ext hx).insert x hd) (hJ.ext hx) hok
      · obtain ⟨op, as, rfl⟩ := Fir.Rhs.isArrPrim_eq_true ha
        simp only [immCode, immRhs]
        rw [eval_bindArr]
        simp only [Fir.evalRhs]
        cases hws : Fir.evalArgs ρf as with
        | none => exact .stuck
        | some ws =>
          obtain ⟨vs, hvs, hds⟩ := evalArgs_den henv as hws
          simp only [hvs, Result.ofOption, Result.bind_ok, Fir.primResult_arr]
          refine (arrStep_lock hH hds op).bind fun w v H' hd hok hx => ?_
          exact eval_lock _ Jf c' _ Jo H' ((henv.ext hx).insert x hd) (hJ.ext hx) hok
  | .jp j ps r b c' =>
    rw [Fir.eval_jp]
    simp only [immCode]
    rw [eval_jp]
    refine eval_lock _ _ c' ρo _ H henv (.cons ⟨rfl, rfl, rfl, ?_, rfl, henv⟩ hJ) hH
    simp [Function.comp_def]
  | .jmp j as =>
    rw [Fir.eval_jmp]
    simp only [immCode]
    rw [eval_jmp]
    refine Lock.ofOption fun p hp => ?_
    obtain ⟨ef, rf⟩ := p
    obtain ⟨eo, ro, hlo, he, hr⟩ := JO.lookup hJ hp
    rw [hlo]
    simp only [Result.ofOption, Result.bind_ok]
    refine Lock.ofOption fun ws hws => ?_
    obtain ⟨vs, hvs, hds⟩ := evalArgs_den henv as hws
    rw [hvs]
    simp only [Result.bind_ok]
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := he
    unfold Fir.jumpTo jumpTo
    rw [h₄, h₂, h₅]
    by_cases hl : ws.length = ef.params.length
    · have hl' : vs.length = ef.params.length := by rw [hds.length]; exact hl
      simp only [hl, hl', ↓reduceIte]
      have henv' := h₆.bindAll ef.params hds
      have hJ' := JO.after ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ hr
      split
      · next hc =>
        exact Lock.later fun k' hk => by
          exact ih k' (by omega) _ _ ef.body _ _ H henv' hJ' hH
      · next hc =>
        have := Fir.jump_measure hp (by simpa using hc)
        skip
        exact eval_lock _ _ ef.body _ _ H henv' hJ' hH
    · have hl' : ¬ vs.length = ef.params.length := by rw [hds.length]; exact hl
      simp only [hl, hl', ↓reduceIte]
      exact .stuck
  | .case x alts d =>
    rw [Fir.eval_case]
    simp only [immCode]
    rw [eval_case]
    refine Lock.ofOption fun w hw => ?_
    obtain ⟨v, hv, hd⟩ := henv x w hw
    rw [hv]
    simp only [Result.ofOption, Result.bind_ok]
    obtain ⟨hsome, hnone⟩ := asCtor_den F.known hd
    cases hk : w.asCtor F.known with
    | none => exact .stuck
    | some p =>
      obtain ⟨key, fs⟩ := p
      obtain ⟨vs, hvs, _⟩ := hsome key fs hk
      simp only [immortal, hvs]
      exact evalAlts_lock ρf Jf key alts d ρo Jo H henv hJ hH
  | .ret a =>
    rw [Fir.eval_ret]
    simp only [immCode]
    rw [eval_ret]
    cases hw : a.eval ρf with
    | none => exact .stuck
    | some w =>
      obtain ⟨v, hv, hd⟩ := evalArg_den henv a hw
      simp only [Result.ofOption, hv, Result.bind_ok]
      exact .ok hd hH (Ext.refl H)
  | .tcall f as =>
    rw [Fir.eval_tcall]
    simp only [immCode]
    rw [eval_tcall]
    refine Lock.ofOption fun ws hws => ?_
    obtain ⟨vs, hvs, hds⟩ := evalArgs_den henv as hws
    rw [hvs]
    simp only [Result.ofOption, Result.bind_ok]
    exact call_lock ih f hH hds
  | .trap =>
    rw [Fir.eval_trap]
    simp only [immCode]
    rw [eval_trap]
    exact .trap
termination_by c.size + Fir.jweight Jf
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Fir.Code.size]; omega)
    | (simp only [Fir.Code.size, Fir.jweight, Fir.JEntry.weight, Bool.false_eq_true, ↓reduceIte]; omega)
    | (simp only [Fir.Code.size] at this ⊢; omega)

theorem evalAlts_lock (ρf : Fir.Env) (Jf : List Fir.JEntry) (key : Key.CtorKey) (alts : List Fir.Alt)
    (d : Option Fir.Code) (ρo : Env) (Jo : List JEntry) (H : Heap) (henv : EnvO H ρf ρo)
    (hJ : JO H Jf Jo) (hH : H.immortalOk = true) :
    Lock H (Fir.evalAlts F k ρf Jf key alts d)
      (evalAlts .immortal (immortal F) k ρo Jo H key (immAlts alts) (immOpt d)) := by
  match alts, d with
  | [], some c =>
    rw [Fir.evalAlts_nil]
    simp only [immAlts, immOpt]
    rw [evalAlts_nil]
    exact eval_lock ρf Jf c ρo Jo H henv hJ hH
  | [], none =>
    rw [Fir.evalAlts_nil]
    exact .stuck
  | .mk key' body :: rest, d =>
    rw [Fir.evalAlts_cons]
    simp only [immAlts]
    rw [evalAlts_cons]
    split
    · exact eval_lock ρf Jf body ρo Jo H henv hJ hH
    · exact evalAlts_lock ρf Jf key rest d ρo Jo H henv hJ hH
termination_by Fir.Code.altsSize alts + Fir.Code.optSize d + Fir.jweight Jf + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [Fir.Code.altsSize, Fir.Code.optSize]
  all_goals first
    | omega
    | (have := Fir.Code.size_pos body; omega)

end

end

/-- **Lock step at every clock**: Fir and its immortal embedding agree on
every outcome but a stuck Fir run, from related environments, join stacks
and an immortal heap. -/
theorem lock {F : Fir.Program} (hb : BoolsOk F) :
    ∀ (k : Nat) (ρf : Fir.Env) (Jf : List Fir.JEntry) (c : Fir.Code) (ρo : Env) (Jo : List JEntry)
      (H : Heap), EnvO H ρf ρo → JO H Jf Jo → H.immortalOk = true →
      Lock H (Fir.eval F k ρf Jf c) (eval .immortal (immortal F) k ρo Jo H (immCode c)) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih => exact eval_lock hb ih

/-- A run of function `f`, lock step at every clock. -/
theorem run_lock {F : Fir.Program} (hb : BoolsOk F) (k : Nat) (f : FunId) {H : Heap}
    (hH : H.immortalOk = true) {vs : List RVal} {ws : List Fir.Val} (hds : Forall2 (Den H) vs ws) :
    Lock H (Fir.run F k f ws) (run .immortal (immortal F) k f vs H) :=
  call_lock (fun j _ => lock hb j) f hH hds

end IxCC.Own.Proof
