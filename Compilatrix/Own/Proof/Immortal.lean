import Compilatrix.Own.Proof.Mono
import Compilatrix.Own.Proof.Heap
import Compilatrix.Own.Immortal
import Compilatrix.Fir.Proof.Mono

/-! # The Phase 1 Own refinement (`Own.immortal_refines`)

Design note 03 §4.4: the Phase 1 Own program of a Fir program `F` is the
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

namespace Compilatrix.Own.Proof

open Compilatrix.Sem (Result later ClockMono Sim Forall2)
open Compilatrix.Fir (Var FunId JoinId Arg)

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

theorem rhs_lock (hb : BoolsOk F) (hH : H.immortalOk = true) (ρf : Fir.Env) (ρo : Env) (henv : EnvO H ρf ρo) (r : Fir.Rhs)
    (hr : ∀ f as, r ≠ .call f as) :
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
      simp only [hvs, Fir.primResult, primResult, natArgs_den hds, immortal, Program.tables]
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
      simp only [immCode]
      rw [eval_bindRhs _ _ _ _ _ _ _ _ _ (by cases r <;> simp_all [immRhs])]
      refine (rhs_lock hb hH ρf ρo henv r hr').bind fun w v H' hd hok hx => ?_
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

end Compilatrix.Own.Proof
