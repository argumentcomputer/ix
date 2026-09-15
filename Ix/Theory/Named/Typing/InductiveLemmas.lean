/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Kernel.Verify.Audit.AxiomAudit
import Ix.Theory.Named.Typing.Lemmas
import Ix.Theory.Named.Typing.Env
import Ix.Theory.Named.Typing.Meta
import Ix.Theory.Named.Typing.Strong

open Ix.Theory (VLevel)

namespace Ix.Theory.Named

/- Lean 4.31 no longer unfolds these structural recursors implicitly in a
number of `simp`/`simpa` calls below.  Keep the compatibility normalization
local to this proof module: all rules only reduce on a visible constructor. -/
attribute [local simp] VExpr.appN VExpr.bvarRevRange VExpr.forallN VExpr.lamN
  VExpr.liftTelN VExpr.liftN VExpr.inst VExpr.instL VLevel.inst

/-! ## Basic facts about the stage-1 generation helpers -/

end Ix.Theory.Named

namespace Ix.Theory.VLevel

theorem params'_length : (params' n k).length = n := by simp [params']

theorem params'_wf : ∀ l ∈ params' n k, l.WF (n + k) := by
  simp only [params', List.mem_map, List.mem_range]
  rintro _ ⟨i, hi, rfl⟩; exact Nat.add_lt_add_right hi _

theorem params'_one_wf : ∀ l ∈ params' n 1, l.WF (n + 1) := params'_wf

theorem params_map_inst_params' :
    (params n).map (VLevel.inst (params' n k)) = params' n k :=
  inst_map_id params'_length

end Ix.Theory.VLevel

namespace Ix.Theory.Named

attribute [local simp] VExpr.appN VExpr.bvarRevRange VExpr.forallN VExpr.lamN
  VExpr.liftTelN VExpr.liftN VExpr.inst VExpr.instL VLevel.inst

namespace VExpr

theorem forallN_append (As Bs : List VExpr) (e : VExpr) :
    forallN (As ++ Bs) e = forallN As (forallN Bs e) := by
  induction As with
  | nil => rfl
  | cons A As ih => simp [forallN, ih]

theorem instL_forallN (ls : List VLevel) (As : List VExpr) (e : VExpr) :
    (forallN As e).instL ls = forallN (As.map (instL ls)) (e.instL ls) := by
  induction As with
  | nil => rfl
  | cons A As ih => simp [forallN, instL, ih]

/-- Substituting a variable for the sole loose variable is a lift. -/
theorem inst_bvar_of_closedN (h : ClosedN e (k+1)) :
    e.inst (.bvar n) k = e.liftN n k := by
  induction e generalizing k with simp_all [ClosedN, inst, liftN]
  | bvar i =>
    simp only [instVar]
    rcases Nat.lt_trichotomy i k with h' | rfl | h'
    · simp [h', liftVar_lt h']
    · simp [liftVar_le (Nat.le_refl _), liftN]
    · omega

theorem ClosedN.appN {f : VExpr} (hf : f.ClosedN k) {as : List VExpr}
    (has : ∀ a ∈ as, ClosedN a k) : (appN f as).ClosedN k := by
  induction as generalizing f with
  | nil => exact hf
  | cons a as ih =>
    exact ih ⟨hf, has _ (.head _)⟩ fun a h => has _ (.tail _ h)

theorem LevelWF.appN {f : VExpr} (hf : f.LevelWF U) {as : List VExpr}
    (has : ∀ a ∈ as, LevelWF U a) : (appN f as).LevelWF U := by
  induction as generalizing f with
  | nil => exact hf
  | cons a as ih =>
    exact ih ⟨hf, has _ (.head _)⟩ fun a h => has _ (.tail _ h)

theorem LevelWF.forallN {As : List VExpr} (hAs : ∀ A ∈ As, LevelWF U A)
    {e : VExpr} (he : e.LevelWF U) : (forallN As e).LevelWF U := by
  induction As with
  | nil => exact he
  | cons A As ih =>
    exact ⟨hAs _ (.head _), ih fun A h => hAs _ (.tail _ h)⟩

theorem LevelWF.lamN {As : List VExpr} (hAs : ∀ A ∈ As, LevelWF U A)
    {e : VExpr} (he : e.LevelWF U) : (lamN As e).LevelWF U := by
  induction As with
  | nil => exact he
  | cons A As ih =>
    exact ⟨hAs _ (.head _), ih fun A h => hAs _ (.tail _ h)⟩

theorem appN_append (f : VExpr) : ∀ (as bs : List VExpr),
    f.appN (as ++ bs) = (f.appN as).appN bs
  | [], _ => rfl
  | a :: as, bs => appN_append (f.app a) as bs

theorem bvarRevRange_liftN_low : ∀ (m off n : Nat),
    (bvarRevRange off m).map (liftN n · 0) = bvarRevRange (n + off) m
  | 0, _, _ => rfl
  | m+1, off, n => by
    show VExpr.bvar _ :: _ = VExpr.bvar _ :: _
    rw [bvarRevRange_liftN_low m off n]
    congr 2
    show liftVar n (off + m) 0 = n + off + m
    rw [liftVar_le (Nat.zero_le _)]; omega

theorem bvarRevRange_liftN_high : ∀ (m off n k : Nat), off + m ≤ k →
    (bvarRevRange off m).map (liftN n · k) = bvarRevRange off m
  | 0, _, _, _, _ => rfl
  | m+1, off, n, k, h => by
    show VExpr.bvar _ :: _ = VExpr.bvar _ :: _
    rw [bvarRevRange_liftN_high m off n k (by omega)]
    congr 2
    exact liftVar_lt (by omega)

/-- Instantiating at a fresh (lifted-over) position is the identity. -/
theorem inst_liftN1 : ∀ (e a : VExpr) (k : Nat), (e.liftN 1 k).inst a k = e := by
  intro e
  induction e with intro a k
  | bvar j =>
    show VExpr.instVar (liftVar 1 j k) a k = .bvar j
    unfold liftVar VExpr.instVar
    split
    · rfl
    · next h =>
      rw [if_neg (by omega), if_neg (by omega)]
      congr 1; omega
  | sort | const => rfl
  | app f b ihf ihb => simp [liftN, inst, ihf, ihb]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [liftN, inst, ihA, ihb]

/-- Lifting a telescope of closed binders acts only on the body. -/
theorem liftN_forallN_closed : ∀ {As : List VExpr}, (∀ A ∈ As, A.ClosedN 0) →
    ∀ (e : VExpr) (n k : Nat),
    (forallN As e).liftN n k = forallN As (e.liftN n (k + As.length))
  | [], _, e, n, k => rfl
  | A :: As, hAs, e, n, k => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    rw [(hAs _ (.head _)).liftN_eq (Nat.zero_le _),
      liftN_forallN_closed (fun A h => hAs _ (.tail _ h)) e n (k+1),
      show k+1+As.length = k+(As.length+1) from by omega]
    rfl

/-- Lifting through a dependent telescope. -/
theorem liftN_forallN (n : Nat) : ∀ (tel : List VExpr) (X : VExpr) (k : Nat),
    (forallN tel X).liftN n k = forallN (liftTelN n tel k) (X.liftN n (k + tel.length))
  | [], _, _ => rfl
  | A :: tel, X, k => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    rw [liftN_forallN n tel X (k+1),
      show k+1+tel.length = k+(tel.length+1) from by omega]
    rfl

theorem liftTelN_length (n : Nat) : ∀ (tel : List VExpr) (k : Nat),
    (liftTelN n tel k).length = tel.length
  | [], _ => rfl
  | _ :: tel, k => by simp [liftTelN, liftTelN_length n tel (k+1)]

theorem liftTelN_liftTelN (a b : Nat) : ∀ (tel : List VExpr) (k : Nat),
    liftTelN b (liftTelN a tel k) k = liftTelN (a+b) tel k
  | [], _ => rfl
  | A :: tel, k => by
    show _ :: _ = _ :: _
    rw [liftN'_liftN_hi, liftTelN_liftTelN a b tel (k+1)]

theorem liftTelN_getElem? (n : Nat) : ∀ (tel : List VExpr) (k q : Nat),
    (liftTelN n tel k)[q]? = tel[q]?.map fun A => A.liftN n (k+q)
  | [], _, q => by simp [liftTelN]
  | A :: tel, k, 0 => by simp [liftTelN]
  | A :: tel, k, q+1 => by
    simp only [liftTelN, List.getElem?_cons_succ]
    rw [liftTelN_getElem? n tel (k+1) q, show k+1+q = k+(q+1) from by omega]

theorem liftTelN_take (n : Nat) : ∀ (tel : List VExpr) (k q : Nat),
    (liftTelN n tel k).take q = liftTelN n (tel.take q) k
  | [], _, q => by simp [liftTelN]
  | A :: tel, k, 0 => rfl
  | A :: tel, k, q+1 => by
    show A.liftN n k :: (liftTelN n tel (k+1)).take q = _
    rw [liftTelN_take n tel (k+1) q]
    rfl

/-- Merging a telescope lift over another when the outer cutoff sits right
past the inner lift. -/
theorem liftTelN_liftTelN_hi (a b : Nat) : ∀ (tel : List VExpr) (k : Nat),
    liftTelN b (liftTelN a tel k) (k + a) = liftTelN (a + b) tel k
  | [], _ => rfl
  | A :: tel, k => by
    show (A.liftN a k).liftN b (k+a) :: _ = _
    rw [liftN'_liftN' (Nat.le_add_right _ _) (by omega),
      show k + a + 1 = (k+1) + a from by omega,
      liftTelN_liftTelN_hi a b tel (k+1)]
    rfl

/-- `liftTelN_liftTelN_hi` with the outer cutoff generalized, for
syntactic rewriting. -/
theorem liftTelN_liftTelN_hi' (a b : Nat) (tel : List VExpr) (k : Nat) {cut : Nat}
    (hcut : cut = k + a) :
    liftTelN b (liftTelN a tel k) cut = liftTelN (a + b) tel k := by
  rw [hcut]; exact liftTelN_liftTelN_hi a b tel k

/-- Merge telescope lifts when the outer cutoff lies anywhere inside the
range opened by the inner lift. This is the shape needed when new ambient
binders are inserted below a recursive argument's own Pi telescope. -/
theorem liftTelN_liftTelN_mid (a b : Nat) : ∀ (tel : List VExpr) (k cut : Nat),
    k ≤ cut → cut ≤ a + k →
    liftTelN b (liftTelN a tel k) cut = liftTelN (a+b) tel k
  | [], _, _, _, _ => rfl
  | A :: tel, k, cut, h₁, h₂ => by
    show (A.liftN a k).liftN b cut :: _ = _
    rw [VExpr.liftN'_liftN' h₁ h₂,
      liftTelN_liftTelN_mid a b tel (k+1) (cut+1)
        (Nat.succ_le_succ h₁) (by omega)]
    rfl

theorem liftTelN_instL (ls : List VLevel) (n : Nat) : ∀ (tel : List VExpr) (k : Nat),
    (liftTelN n tel k).map (instL ls) = liftTelN n (tel.map (instL ls)) k
  | [], _ => rfl
  | A :: tel, k => by
    show (A.liftN n k).instL ls :: _ = (A.instL ls).liftN n k :: _
    rw [instL_liftN, liftTelN_instL ls n tel (k+1)]

/-- Pulling a lift out of the middle of a two-step lift: the outer lift at
the seam between the two inner ones lands on the variables the innermost
lift moved. -/
theorem liftN_liftN_mid : ∀ (e : VExpr) {j c : Nat} (k d : Nat), c ≤ j →
    ((e.liftN 1 j).liftN d c).liftN k (j + d) = (e.liftN (k+1) j).liftN d c := by
  intro e
  induction e with intro j c k d hc
  | bvar i =>
    show VExpr.bvar (liftVar k (liftVar d (liftVar 1 i j) c) (j+d)) =
      .bvar (liftVar d (liftVar (k+1) i j) c)
    congr 1
    rcases Nat.lt_or_ge i j with h1 | h1
    · rw [liftVar_lt h1, liftVar_lt (show i < j from h1)]
      rcases Nat.lt_or_ge i c with h2 | h2
      · rw [liftVar_lt h2, liftVar_lt (show i < j+d from by omega)]
      · rw [liftVar_le h2, liftVar_lt (show d+i < j+d from by omega)]
    · rw [liftVar_le h1, liftVar_le h1,
        liftVar_le (show c ≤ 1+i from by omega),
        liftVar_le (show c ≤ k+1+i from by omega),
        liftVar_le (show j+d ≤ d+(1+i) from by omega)]
      omega
  | sort | const => intros; rfl
  | app f a ihf iha => simp [liftN, ihf _ _ hc, iha _ _ hc]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [liftN]
    refine congr (congrArg _ (ihA _ _ hc)) ?_
    have := ihb (j := j+1) (c := c+1) k d (by omega)
    rwa [show j+1+d = j+d+1 from by omega] at this

/-- Telescope form of `liftN_liftN_mid`. The outer lift is inserted at the
seam between the lift below the telescope and the lift that opened the
telescope's original ambient context. -/
theorem liftTelN_liftN_mid : ∀ (tel : List VExpr) {j c : Nat} (k d : Nat), c ≤ j →
    liftTelN k (liftTelN d (liftTelN 1 tel j) c) (j+d) =
      liftTelN d (liftTelN (k+1) tel j) c
  | [], _, _, _, _, _ => rfl
  | A :: tel, j, c, k, d, hc => by
    show ((A.liftN 1 j).liftN d c).liftN k (j+d) :: _ =
      (A.liftN (k+1) j).liftN d c :: _
    rw [liftN_liftN_mid A k d hc]
    congr 1
    rw [show j+d+1 = j+1+d from by omega]
    exact liftTelN_liftN_mid tel k d (Nat.succ_le_succ hc)

/-- Disjoint lifts commute: an outer lift below an inner one slides past
it, pushing the inner cutoff up. -/
theorem liftN_liftN_comm : ∀ (e : VExpr) (n k c K : Nat), c ≤ K →
    (e.liftN k K).liftN n c = (e.liftN n c).liftN k (K + n) := by
  intro e
  induction e with intro n k c K hc
  | bvar i =>
    show VExpr.bvar (liftVar n (liftVar k i K) c) = .bvar (liftVar k (liftVar n i c) (K+n))
    congr 1
    rcases Nat.lt_or_ge i c with h2 | h2
    · rw [liftVar_lt (show i < K from by omega), liftVar_lt h2,
        liftVar_lt (show i < K+n from by omega)]
    · rcases Nat.lt_or_ge i K with h1 | h1
      · rw [liftVar_lt h1, liftVar_le h2,
          liftVar_lt (show n+i < K+n from by omega)]
      · rw [liftVar_le h1, liftVar_le (show c ≤ k+i from by omega), liftVar_le h2,
          liftVar_le (show K+n ≤ n+i from by omega)]
        omega
  | sort | const => intros; rfl
  | app f a ihf iha => simp [liftN, ihf _ _ _ _ hc, iha _ _ _ _ hc]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [liftN]
    refine congr (congrArg _ (ihA _ _ _ _ hc)) ?_
    have := ihb n k (c+1) (K+1) (by omega)
    rwa [show K+1+n = K+n+1 from by omega] at this

/-- Generalized form of `liftN_liftN_mid`: expanding an arbitrary lift at
the seam above a disjoint lower lift adds the new width to that arbitrary
lift. -/
theorem liftN_liftN_midN (e : VExpr) {j c : Nat}
    (a k d : Nat) (hc : c ≤ j) :
    ((e.liftN a j).liftN d c).liftN k (j+d) =
      (e.liftN (a+k) j).liftN d c := by
  rw [← liftN_liftN_comm (e.liftN a j) d k c j hc]
  rw [liftN'_liftN_hi]

/-- Telescope form of `liftN_liftN_midN`. -/
theorem liftTelN_liftN_midN :
    ∀ (tel : List VExpr) {j c : Nat} (a k d : Nat), c ≤ j →
      liftTelN k (liftTelN d (liftTelN a tel j) c) (j+d) =
        liftTelN d (liftTelN (a+k) tel j) c
  | [], _, _, _, _, _, _ => rfl
  | A :: tel, j, c, a, k, d, hc => by
    show ((A.liftN a j).liftN d c).liftN k (j+d) :: _ = _
    rw [liftN_liftN_midN A a k d hc]
    congr 1
    rw [show j+d+1 = j+1+d from by omega]
    exact liftTelN_liftN_midN tel a k d (Nat.succ_le_succ hc)

/-- Instantiation under a telescope: the entry at depth `q` instantiates
at `k+q`. -/
def instTelN (a : VExpr) : List VExpr → Nat → List VExpr
  | [], _ => []
  | A :: As, k => A.inst a k :: instTelN a As (k+1)

attribute [local simp] instTelN

theorem instTelN_length (a : VExpr) : ∀ (tel : List VExpr) (k : Nat),
    (instTelN a tel k).length = tel.length
  | [], _ => rfl
  | _ :: tel, k => by simp [instTelN, instTelN_length a tel (k+1)]

theorem instN_forallN (a : VExpr) : ∀ (tel : List VExpr) (X : VExpr) (k : Nat),
    (forallN tel X).inst a k = forallN (instTelN a tel k) (X.inst a (k + tel.length))
  | [], _, _ => rfl
  | A :: tel, X, k => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    rw [instN_forallN a tel X (k+1),
      show k+1+tel.length = k+(tel.length+1) from by omega]
    rfl

/-- Iterated instantiation of a body under `es.length` binders, consuming
the spine outermost-first. -/
def instRev : VExpr → List VExpr → VExpr
  | C, [] => C
  | C, e :: es => instRev (C.inst e es.length) es

theorem instRev_closedN : ∀ (es : List VExpr) {C : VExpr}, C.ClosedN 0 →
    instRev C es = C
  | [], _, _ => rfl
  | e :: es, C, hC => by
    show instRev (C.inst e es.length) es = C
    rw [hC.instN_eq (Nat.zero_le _)]
    exact instRev_closedN es hC

theorem instRev_bvar_ge : ∀ (es : List VExpr) {i : Nat}, es.length ≤ i →
    instRev (.bvar i) es = .bvar (i - es.length)
  | [], i, _ => by simp [instRev]
  | e :: es, i, h => by
    have h' : es.length < i := by
      simp only [List.length_cons] at h
      omega
    show instRev ((VExpr.bvar i).inst e es.length) es = _
    rw [show (VExpr.bvar i).inst e es.length = .bvar (i-1) from by
        show VExpr.instVar i e es.length = _
        unfold VExpr.instVar
        rw [if_neg (by omega), if_neg (by omega)],
      instRev_bvar_ge es (by omega)]
    congr 1
    simp only [List.length_cons]
    omega

/-- The spine consumes a fully lifted body without a trace. -/
theorem instRev_liftN_len : ∀ (es : List VExpr) (X : VExpr),
    instRev (X.liftN es.length) es = X
  | [], X => by simp [instRev, liftN_zero]
  | e :: es, X => by
    show instRev ((X.liftN (es.length+1)).inst e es.length) es = X
    rw [show X.liftN (es.length+1) = (X.liftN es.length).liftN 1 es.length from
        (liftN'_liftN' (Nat.zero_le _) (by omega)).symm,
      inst_liftN]
    exact instRev_liftN_len es X

theorem instRev_bvar_lt_cons (es : List VExpr) (e : VExpr) {i : Nat} (hi : i < es.length) :
    instRev (.bvar i) (e :: es) = instRev (.bvar i) es := by
  show instRev ((VExpr.bvar i).inst e es.length) es = _
  congr 1
  show VExpr.instVar i e es.length = .bvar i
  unfold VExpr.instVar
  rw [if_pos hi]

theorem mem_bvarRevRange : ∀ {m off : Nat} {x : VExpr}, x ∈ bvarRevRange off m →
    ∃ i, x = .bvar i ∧ off ≤ i ∧ i < off + m
  | m+1, off, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨off + m, rfl, by omega, by omega⟩
    · obtain ⟨i, rfl, h1, h2⟩ := mem_bvarRevRange h
      exact ⟨i, rfl, h1, by omega⟩

/-- The last `es.length` variables consume to the spine itself. -/
theorem map_instRev_bvarRevRange : ∀ (es : List VExpr),
    (bvarRevRange 0 es.length).map (instRev · es) = es
  | [] => rfl
  | e :: es => by
    show instRev (.bvar (0 + es.length)) (e :: es) ::
      (bvarRevRange 0 es.length).map (instRev · (e :: es)) = e :: es
    congr 1
    · show instRev ((VExpr.bvar (0 + es.length)).inst e es.length) es = e
      rw [Nat.zero_add,
        show (VExpr.bvar es.length).inst e es.length = e.liftN es.length from by
          show VExpr.instVar es.length e es.length = _
          unfold VExpr.instVar
          rw [if_neg (Nat.lt_irrefl _), if_pos rfl]]
      exact instRev_liftN_len es e
    · rw [List.map_congr_left fun x hx => ?_, map_instRev_bvarRevRange es]
      obtain ⟨i, rfl, -, h2⟩ := mem_bvarRevRange hx
      exact instRev_bvar_lt_cons es e (by omega)

theorem map_instRev_bvarRevRange_ge (es : List VExpr) : ∀ (q off : Nat),
    es.length ≤ off →
    (bvarRevRange off q).map (instRev · es) = bvarRevRange (off - es.length) q
  | 0, _, _ => rfl
  | q+1, off, h => by
    show instRev (.bvar (off+q)) es :: _ = _
    rw [instRev_bvar_ge es (by omega), map_instRev_bvarRevRange_ge es q off h]
    congr 2
    omega

theorem instRev_appN (es : List VExpr) : ∀ (f : VExpr) (as : List VExpr),
    instRev (appN f as) es = appN (instRev f es) (as.map (instRev · es)) := by
  induction es with intro f as
  | nil => simp [instRev, List.map_id']
  | cons e es ih =>
    show instRev ((appN f as).inst e es.length) es = _
    rw [instN_appN, ih]
    simp [instRev, List.map_map, Function.comp_def]

theorem instRev_forallE_sort (u : VLevel) : ∀ (es : List VExpr) (D : VExpr),
    instRev (.forallE D (.sort u)) es = .forallE (instRev D es) (.sort u)
  | [], _ => rfl
  | e :: es, D => instRev_forallE_sort u es (D.inst e es.length)

theorem bvarRevRange_append : ∀ (m k : Nat),
    bvarRevRange k m ++ bvarRevRange 0 k = bvarRevRange 0 (k + m)
  | 0, k => by simp [bvarRevRange]
  | m+1, k => by
    show VExpr.bvar (k + m) :: (bvarRevRange k m ++ bvarRevRange 0 k) = _
    rw [bvarRevRange_append m k, show k + (m+1) = (k+m)+1 from rfl]
    show _ = VExpr.bvar (0 + (k+m)) :: bvarRevRange 0 (k+m)
    rw [Nat.zero_add]

theorem appHead_appN : ∀ (as : List VExpr) (f : VExpr), (appN f as).appHead = f.appHead
  | [], _ => rfl
  | a :: as, f => appHead_appN as (f.app a)

theorem appArgs_appN : ∀ (as acc : List VExpr) (f : VExpr),
    (appN f as).appArgs acc = f.appArgs (as ++ acc)
  | [], _, _ => rfl
  | a :: as, acc, f => by
    show (VExpr.appN (f.app a) as).appArgs acc = _
    rw [appArgs_appN as acc (f.app a)]
    rfl

theorem appN_appHead_appArgs : ∀ (e : VExpr) (acc : List VExpr),
    appN e.appHead (e.appArgs acc) = appN e acc
  | .app f a, acc => by
    show appN f.appHead (f.appArgs (a :: acc)) = _
    rw [appN_appHead_appArgs f (a :: acc)]
    rfl
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lam _ _, _ | .forallE _ _, _ => rfl

end VExpr

/-! ## Anatomy of the stage-3 predicate -/

namespace VInductDecl

/-- A constructor-type telescope splits as fields over the result. -/
theorem forallN_ctorFields_resultOf : ∀ (e : VExpr),
    VExpr.forallN (ctorFields e) e.resultOf = e
  | .forallE B rest => congrArg (VExpr.forallE B) (forallN_ctorFields_resultOf rest)
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ => rfl

/-- Unpack a recursive-field check into its structural content. -/
theorem isRecField_eq {U T np ni j B} (h : isRecField U T np ni j B = true) :
    B = VExpr.appN (.const T (VLevel.params U))
      (VExpr.bvarRevRange j np ++ recFieldIdxs np B) ∧
    (recFieldIdxs np B).length = ni ∧
    ∀ e ∈ recFieldIdxs np B, e.hasConst T = false := by
  simp only [isRecField, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, fun e he => by simpa [Bool.not_eq_true'] using h4 e he⟩
  · have hB : B = VExpr.appN B.appHead (B.appArgs []) :=
      (VExpr.appN_appHead_appArgs B []).symm
    conv => lhs; rw [hB, h1,
      show VExpr.appArgs B [] =
        (VExpr.appArgs B []).take np ++ (VExpr.appArgs B []).drop np from
        (List.take_append_drop ..).symm,
      h3]
    rfl
  · simp only [recFieldIdxs, List.length_drop, h2]
    omega

/-- Unpack recursive-argument analysis beneath a possibly empty Pi telescope.
The terminal family application is seen under both the preceding constructor
fields (`j`) and the returned recursive binders. -/
theorem recTarget?_eq {U T np ni j B As idxs}
    (h : recTarget? U T np ni j B = some (As, idxs)) :
    B = VExpr.forallN As
      (VExpr.appN (.const T (VLevel.params U))
        (VExpr.bvarRevRange (j + As.length) np ++ idxs)) ∧
    idxs.length = ni ∧
    (∀ e ∈ idxs, e.hasConst T = false) ∧
    ∀ (q : Nat) (A : VExpr), As[q]? = some A → A.hasConst T = false := by
  induction B generalizing j As idxs with
  | forallE A rest _ ih =>
    simp only [recTarget?] at h
    split at h
    · contradiction
    · next hA =>
      split at h
      · next As' idxs' hrest =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hshape, hlen, hfree, hbinders⟩ := ih hrest
        refine ⟨?_, hlen, hfree, ?_⟩
        · show VExpr.forallE A rest = VExpr.forallE A _
          rw [hshape, show j + 1 + As'.length = j + (As'.length + 1) from by omega]
          simp only [List.length_cons]
        · intro q A' hq
          match q, hq with
          | 0, hq =>
            obtain rfl : A = A' := by simpa using hq
            cases hAT : A.hasConst T with
            | false => rfl
            | true => exact (hA hAT).elim
          | q+1, hq => exact hbinders q A' (by simpa using hq)
      · contradiction
  | bvar i | sort i | const i | app i i | lam i i =>
    simp only [recTarget?] at h
    split at h
    · next hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hshape, hlen, hfree⟩ := isRecField_eq hrec
      exact ⟨by simpa using hshape, hlen, hfree, by simp⟩
    · contradiction

/-- Public recursive-argument anatomy, including the stable field and
one-family target indices carried by the descriptor. -/
theorem recArg?_eq {U T np ni j B r}
    (h : recArg? U T np ni j B = some r) :
    r.fieldIndex = j ∧ r.targetType = 0 ∧
    B = VExpr.forallN r.binders
      (VExpr.appN (.const T (VLevel.params U))
        (VExpr.bvarRevRange (j + r.binders.length) np ++ r.indices)) ∧
    r.indices.length = ni ∧
    (∀ e ∈ r.indices, e.hasConst T = false) ∧
    ∀ (q : Nat) (A : VExpr), r.binders[q]? = some A → A.hasConst T = false := by
  unfold recArg? at h
  split at h
  · next binders indices htarget =>
    simp only [Option.some.injEq] at h
    subst r
    obtain ⟨hshape, hlen, hfree, hbinders⟩ := recTarget?_eq htarget
    exact ⟨rfl, rfl, hshape, hlen, hfree, hbinders⟩
  · contradiction

/-- With no Pi binders, recursive-argument recognition is exactly the direct
recursive-field check. -/
theorem recTarget?_nil {U T np ni j B idxs}
    (h : recTarget? U T np ni j B = some ([], idxs)) :
    isRecField U T np ni j B = true ∧ idxs = recFieldIdxs np B := by
  cases B with
  | forallE A rest =>
    simp only [recTarget?] at h
    split at h
    · contradiction
    · cases hrest : recTarget? U T np ni (j+1) rest with
      | none => simp [hrest] at h
      | some out =>
        obtain ⟨As, is⟩ := out
        simp [hrest] at h
  | bvar i | sort i | const i | app i i | lam i i =>
    simp only [recTarget?] at h
    split at h
    · next hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨hrec, h.2.symm⟩
    · contradiction

theorem recArg?_nil {U T np ni j B r}
    (h : recArg? U T np ni j B = some r) (hr : r.binders = []) :
    isRecField U T np ni j B = true ∧ r.indices = recFieldIdxs np B := by
  unfold recArg? at h
  split at h
  · next binders indices htarget =>
    simp only [Option.some.injEq] at h
    subst r
    simp only at hr
    subst binders
    exact recTarget?_nil htarget
  · contradiction

/-- A direct recursive-field success normalizes to the descriptor with an
empty binder telescope. -/
theorem recArg?_of_isRecField {U T np ni j B}
    (h : isRecField U T np ni j B = true) :
    recArg? U T np ni j B = some
      { fieldIndex := j, binders := [], targetType := 0,
        indices := recFieldIdxs np B } := by
  cases B with
  | forallE A rest => simp [isRecField, VExpr.appHead] at h
  | bvar i | sort i | const i | app i i | lam i i =>
    simp_all [recArg?, recTarget?]

theorem stage3Ctor_eq {U T np ni} : ∀ {j₀ : Nat} {e : VExpr},
    stage3Ctor U T np ni j₀ e = true →
    e = VExpr.forallN (ctorFields e)
      (VExpr.appN (.const T (VLevel.params U))
        (VExpr.bvarRevRange (j₀ + (ctorFields e).length) np ++
          recFieldIdxs np e.resultOf)) ∧
    (recFieldIdxs np e.resultOf).length = ni ∧
    (∀ x ∈ recFieldIdxs np e.resultOf, x.hasConst T = false) ∧
    ∀ q B, (ctorFields e)[q]? = some B → stage3Field U T np ni (j₀ + q) B = true := by
  intro j₀ e h
  induction e generalizing j₀ with
  | forallE B rest _ ih =>
    rw [show stage3Ctor U T np ni j₀ (.forallE B rest) =
      (stage3Field U T np ni j₀ B && stage3Ctor U T np ni (j₀+1) rest) from rfl,
      Bool.and_eq_true] at h
    have ⟨ih1, ih2, ih3, ih4⟩ := ih h.2
    refine ⟨?_, ih2, ih3, ?_⟩
    · show VExpr.forallE _ _ = VExpr.forallE _ _
      conv => lhs; rw [ih1]
      rw [show j₀+1+(ctorFields rest).length = j₀+((ctorFields rest).length+1) from by omega]
      rfl
    · intro q B' hB'
      match q, hB' with
      | 0, hB' =>
        obtain rfl : B = B' := by simpa [ctorFields] using hB'
        exact h.1
      | q+1, hB' =>
        have := ih4 q B' (by simpa [ctorFields] using hB')
        rwa [show j₀+1+q = j₀+(q+1) from by omega] at this
  | bvar i =>
    exact ⟨(isRecField_eq h).1, (isRecField_eq h).2.1, (isRecField_eq h).2.2,
      fun q B h' => by simp [ctorFields] at h'⟩
  | sort l =>
    exact ⟨(isRecField_eq h).1, (isRecField_eq h).2.1, (isRecField_eq h).2.2,
      fun q B h' => by simp [ctorFields] at h'⟩
  | const c ls =>
    exact ⟨(isRecField_eq h).1, (isRecField_eq h).2.1, (isRecField_eq h).2.2,
      fun q B h' => by simp [ctorFields] at h'⟩
  | app f a _ _ =>
    exact ⟨(isRecField_eq h).1, (isRecField_eq h).2.1, (isRecField_eq h).2.2,
      fun q B h' => by simp [ctorFields] at h'⟩
  | lam A b _ _ =>
    exact ⟨(isRecField_eq h).1, (isRecField_eq h).2.1, (isRecField_eq h).2.2,
      fun q B h' => by simp [ctorFields] at h'⟩

/-- Failure of the legacy singleton predicate is exactly failure to produce
the one-family checked descriptor. -/
theorem checked?_eq_none_iff {decl : VInductDecl} :
    decl.checked? = none ↔ decl.singletonStage3 = false := by
  unfold singletonStage3
  cases decl.checked? <;> simp

/-- Successful singleton acceptance retains the descriptor rather than
discarding it. -/
theorem exists_checked_of_singletonStage3 {decl : VInductDecl}
    (h : decl.singletonStage3 = true) :
    ∃ checked, decl.checked? = some checked := by
  unfold singletonStage3 at h
  cases hc : decl.checked? with
  | none => simp [hc] at h
  | some checked => exact ⟨checked, rfl⟩

/-- Public Stage-3 rejection is exactly failure to retain a complete mutual
generation descriptor. -/
theorem identityBlockGeneration?_eq_none_iff {decl : VInductDecl} :
    decl.identityBlockGeneration? = none ↔ decl.stage3 = false := by
  unfold stage3
  cases decl.identityBlockGeneration? <;> simp

/-- Public Stage-3 acceptance retains the exact block descriptor used by the
transaction. -/
theorem exists_blockGeneration_of_stage3 {decl : VInductDecl}
    (h : decl.stage3 = true) :
    ∃ generation, decl.identityBlockGeneration? = some generation := by
  unfold stage3 at h
  cases hgeneration : decl.identityBlockGeneration? with
  | none => simp [hgeneration] at h
  | some generation => exact ⟨generation, rfl⟩

/-- Proof-level constructor-header coherence exported from the computational
normalization-shape check. -/
def CtorHeaderEq (source view : VConstVal) : Prop :=
  source.name = view.name ∧ source.uvars = view.uvars

/-- Proof-level family-header coherence, including constructor order. -/
def TypeHeaderEq (source view : VInductiveType) : Prop :=
  source.name = view.name ∧ source.uvars = view.uvars ∧
    List.Forall₂ CtorHeaderEq source.ctors view.ctors

theorem sameCtorHeaders_iff_forall₂ : ∀ {source view},
    sameCtorHeaders source view = true ↔
      List.Forall₂ CtorHeaderEq source view
  | [], [] => ⟨fun _ => .nil, fun _ => rfl⟩
  | [], _ :: _ => by
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h; nomatch h
  | _ :: _, [] => by
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h; nomatch h
  | source :: sources, view :: views => by
    constructor
    · intro h
      simp only [sameCtorHeaders, Bool.and_eq_true, beq_iff_eq] at h
      exact .cons ⟨h.1.1, h.1.2⟩ (sameCtorHeaders_iff_forall₂.1 h.2)
    · intro h
      obtain ⟨hhead, htail⟩ := List.forall₂_cons.1 h
      simp only [sameCtorHeaders, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hhead.1, hhead.2⟩, sameCtorHeaders_iff_forall₂.2 htail⟩

theorem sameTypeHeaders_iff_forall₂ : ∀ {source view},
    sameTypeHeaders source view = true ↔
      List.Forall₂ TypeHeaderEq source view
  | [], [] => ⟨fun _ => .nil, fun _ => rfl⟩
  | [], _ :: _ => by
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h; nomatch h
  | _ :: _, [] => by
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h; nomatch h
  | source :: sources, view :: views => by
    constructor
    · intro h
      simp only [sameTypeHeaders, Bool.and_eq_true, beq_iff_eq] at h
      exact .cons
        ⟨h.1.1.1, h.1.1.2, sameCtorHeaders_iff_forall₂.1 h.1.2⟩
        (sameTypeHeaders_iff_forall₂.1 h.2)
    · intro h
      obtain ⟨hhead, htail⟩ := List.forall₂_cons.1 h
      simp only [sameTypeHeaders, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨hhead.1, hhead.2.1⟩,
        sameCtorHeaders_iff_forall₂.2 hhead.2.2⟩,
        sameTypeHeaders_iff_forall₂.2 htail⟩

/-- Every accepted normalization preserves declaration arity and all
family/constructor identities in order. -/
theorem Normalization.shape {source : VInductDecl}
    (norm : Normalization source) :
    source.uvars = norm.view.uvars ∧
    source.nparams = norm.view.nparams ∧
    List.Forall₂ TypeHeaderEq source.types norm.view.types := by
  have h := norm.shape_eq
  simp only [normalizationShape, Bool.and_eq_true, beq_iff_eq,
    sameTypeHeaders_iff_forall₂] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The singleton source family paired with the checked singleton analysis
view. This is the raw payload future normalized generation must insert. -/
theorem NormalizedChecked.source_anatomy {source : VInductDecl}
    (block : NormalizedChecked source) :
    ∃ raw,
      source.types = [raw] ∧
      raw.name = block.checked.type.name ∧
      raw.uvars = block.checked.type.uvars ∧
      List.Forall₂ CtorHeaderEq raw.ctors block.checked.type.ctors := by
  have htypes := block.normalization.shape.2.2
  rw [block.source_types_eq, block.checked.types_eq] at htypes
  obtain ⟨htype, -⟩ := List.forall₂_cons.1 htypes
  exact ⟨block.sourceType, block.source_types_eq,
    htype.1, htype.2.1, htype.2.2⟩

theorem NormalizedChecked.uvars_eq {source : VInductDecl}
    (block : NormalizedChecked source) :
    source.uvars = block.normalization.view.uvars :=
  block.normalization.shape.1

theorem NormalizedChecked.nparams_eq {source : VInductDecl}
    (block : NormalizedChecked source) :
    source.nparams = block.normalization.view.nparams :=
  block.normalization.shape.2.1

/-- Unpack the complete executable layout certificate used by mixed
raw/view generation. -/
theorem GenerationChecked.shape {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.block.rawParams.length = source.nparams ∧
    gen.block.rawParams.length = gen.block.checked.params.length ∧
    gen.block.rawIndices.length = gen.block.checked.indices.length ∧
    gen.block.ctorPairs.length = gen.block.sourceType.ctors.length ∧
    gen.block.ctorPairs.length = gen.block.checked.constructors.length ∧
    ∀ ctor ∈ gen.block.ctorPairs,
      ctor.raw.name = ctor.view.value.name ∧
      ctor.raw.uvars = ctor.view.value.uvars ∧
      (VExpr.telN source.nparams ctor.raw.type).length = source.nparams ∧
      (ctor.rawFields source.nparams).length = ctor.view.fields.length := by
  have h := gen.shape_eq
  simp only [NormalizedChecked.generationShape,
    NormalizedCtor.generationShape, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hparams, hparams'⟩, hindices⟩, hraws⟩, hviews⟩,
    hctors⟩ := h
  refine ⟨hparams, hparams', hindices, hraws, hviews, ?_⟩
  intro ctor hctor
  obtain ⟨⟨⟨hname, hU⟩, htel⟩, hfields⟩ := hctors ctor hctor
  exact ⟨hname, hU, htel, hfields⟩

theorem pairNormalizedCtors_map_raw :
    ∀ (raws : List VConstVal) (views : List CheckedCtor),
      raws.length = views.length →
      (pairNormalizedCtors raws views).map (·.raw) = raws
  | [], [], _ => rfl
  | raw :: raws, view :: views, h => by
    simp only [pairNormalizedCtors, List.map_cons, List.cons.injEq, true_and]
    apply pairNormalizedCtors_map_raw
    simpa using h

theorem pairNormalizedCtors_map_view :
    ∀ (raws : List VConstVal) (views : List CheckedCtor),
      raws.length = views.length →
      (pairNormalizedCtors raws views).map (·.view) = views
  | [], [], _ => rfl
  | raw :: raws, view :: views, h => by
    simp only [pairNormalizedCtors, List.map_cons, List.cons.injEq, true_and]
    apply pairNormalizedCtors_map_view
    simpa using h

/-- Membership in an identity pairing recovers the single raw constructor
that supplied both sides of the pair. -/
theorem pairNormalizedCtors_map_self_mem
    {U : Nat} {T : Name} {np ni : Nat} :
    ∀ {cs : List VConstVal} {ctor : NormalizedCtor},
      ctor ∈ pairNormalizedCtors cs
        (cs.map (CheckedCtor.ofDirect U T np ni)) →
      ∃ c ∈ cs, ctor =
        ⟨c, CheckedCtor.ofDirect U T np ni c⟩
  | [], _, h => by simp [pairNormalizedCtors] at h
  | c :: cs, ctor, h => by
    simp only [List.map_cons, pairNormalizedCtors, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨c, .head _, rfl⟩
    · obtain ⟨c', hc', rfl⟩ :=
        pairNormalizedCtors_map_self_mem h
      exact ⟨c', .tail _ hc', rfl⟩

/-- Every raw constructor occurs in its canonical identity pair. -/
theorem pairNormalizedCtors_map_self_contains
    {U : Nat} {T : Name} {np ni : Nat} :
    ∀ {cs : List VConstVal} {c : VConstVal},
      c ∈ cs →
      (⟨c, CheckedCtor.ofDirect U T np ni c⟩ :
        NormalizedCtor) ∈
        pairNormalizedCtors cs
          (cs.map (CheckedCtor.ofDirect U T np ni))
  | _ :: _, _, .head _ => .head _
  | _ :: _, _, .tail _ hc =>
      .tail _ (pairNormalizedCtors_map_self_contains hc)

/-- The identity generation path pairs each stored constructor with its own
direct analyzer descriptor. -/
theorem Checked.identityGeneration_ctor
    {source : VInductDecl} (checked : source.Checked)
    {ctor : NormalizedCtor}
    (hctor : ctor ∈ checked.identityGeneration.block.ctorPairs) :
    ∃ c ∈ checked.type.ctors, ctor =
      ⟨c, CheckedCtor.ofDirect source.uvars checked.type.name
        source.nparams checked.indices.length c⟩ := by
  apply pairNormalizedCtors_map_self_mem
  simpa only [Checked.identityGeneration, Checked.identityBlock,
    NormalizedChecked.ctorPairs, checked.constructors_eq] using hctor

/-- Positional pairing neither drops nor reorders raw constructors. -/
theorem GenerationChecked.rawCtors_eq {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.block.ctorPairs.map (·.raw) = gen.block.sourceType.ctors := by
  apply pairNormalizedCtors_map_raw
  exact gen.shape.2.2.2.1.symm.trans gen.shape.2.2.2.2.1

/-- Every checked constructor appears in the same paired position. -/
theorem GenerationChecked.viewCtors_eq {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.block.ctorPairs.map (·.view) = gen.block.checked.constructors := by
  apply pairNormalizedCtors_map_view
  exact gen.shape.2.2.2.1.symm.trans gen.shape.2.2.2.2.1

/-! ### Block-generation positional facts -/

theorem pairNormalizedFamilies_map_raw :
    ∀ (raws : List VInductiveType) (views : List CheckedFamilyData),
      raws.length = views.length →
      (pairNormalizedFamilies raws views).map (·.raw) = raws
  | [], [], _ => rfl
  | raw :: raws, view :: views, h => by
    simp only [pairNormalizedFamilies, List.map_cons,
      List.cons.injEq, true_and]
    apply pairNormalizedFamilies_map_raw
    simpa using h

theorem pairNormalizedFamilies_map_view :
    ∀ (raws : List VInductiveType) (views : List CheckedFamilyData),
      raws.length = views.length →
      (pairNormalizedFamilies raws views).map (·.view) = views
  | [], [], _ => rfl
  | raw :: raws, view :: views, h => by
    simp only [pairNormalizedFamilies, List.map_cons,
      List.cons.injEq, true_and]
    apply pairNormalizedFamilies_map_view
    simpa using h

/-- Unpack the executable positional gate for mutual generation. -/
theorem BlockGenerationChecked.shape {source : VInductDecl}
    (gen : BlockGenerationChecked source) :
    gen.block.rawParams.length = source.nparams ∧
      gen.block.rawParams.length = gen.block.checked.params.length ∧
      gen.families.length = source.types.length ∧
      gen.families.length = gen.block.checked.families.data.length ∧
      ∀ family ∈ gen.families,
        family.raw.name = family.view.value.name ∧
        family.raw.uvars = family.view.value.uvars ∧
        (family.rawParams source.nparams).length = source.nparams ∧
        (family.rawIndices source.nparams).length =
          family.view.indices.length ∧
        family.ctorPairs.length = family.raw.ctors.length ∧
        family.ctorPairs.length = family.view.constructors.length ∧
        ∀ ctor ∈ family.ctorPairs,
          ctor.raw.name = ctor.view.value.name ∧
          ctor.raw.uvars = ctor.view.value.uvars ∧
          (VExpr.telN source.nparams ctor.raw.type).length =
            source.nparams ∧
          (ctor.rawFields source.nparams).length = ctor.view.fields.length := by
  have h := gen.shape_eq
  simp only [NormalizedCheckedBlock.blockGenerationShape,
    NormalizedFamily.generationShape, NormalizedCtor.generationShape,
    Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨h, -⟩ := h
  obtain ⟨⟨⟨⟨hparams, hparams'⟩, hraws⟩, hviews⟩, hfamilies⟩ := h
  refine ⟨hparams, hparams', hraws, hviews, ?_⟩
  intro family hfamily
  obtain ⟨⟨⟨⟨⟨⟨hname, hU⟩, htel⟩, hindices⟩,
    hrawCtors⟩, hviewCtors⟩, hctors⟩ := hfamilies family hfamily
  refine ⟨hname, hU, htel, hindices, hrawCtors, hviewCtors, ?_⟩
  intro ctor hctor
  obtain ⟨⟨⟨hctorName, hctorU⟩, hctorTel⟩, hctorFields⟩ :=
    hctors ctor hctor
  exact ⟨hctorName, hctorU, hctorTel, hctorFields⟩

theorem BlockGenerationChecked.family_uvars {source : VInductDecl}
    (gen : BlockGenerationChecked source) {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    family.raw.uvars = source.uvars := by
  have h := gen.shape_eq
  simp only [NormalizedCheckedBlock.blockGenerationShape,
    Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact (h.2 family hfamily).1

theorem BlockGenerationChecked.ctor_uvars {source : VInductDecl}
    (gen : BlockGenerationChecked source) {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) {ctor : NormalizedCtor}
    (hctor : ctor ∈ family.ctorPairs) :
    ctor.raw.uvars = source.uvars := by
  have h := gen.shape_eq
  simp only [NormalizedCheckedBlock.blockGenerationShape,
    Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact (h.2 family hfamily).2 ctor hctor

theorem BlockGenerationChecked.families_map_raw {source : VInductDecl}
    (gen : BlockGenerationChecked source) :
    gen.families.map (·.raw) = source.types := by
  apply pairNormalizedFamilies_map_raw
  exact gen.shape.2.2.1.symm.trans gen.shape.2.2.2.1

theorem NormalizedFamily.ctorPairs_map_raw
    {source : VInductDecl} {gen : BlockGenerationChecked source}
    {family : NormalizedFamily} (hfamily : family ∈ gen.families) :
    family.ctorPairs.map (·.raw) = family.raw.ctors := by
  apply pairNormalizedCtors_map_raw
  exact (gen.shape.2.2.2.2 family hfamily).2.2.2.2.1.symm.trans
    (gen.shape.2.2.2.2 family hfamily).2.2.2.2.2.1

@[simp] theorem NormalizedFamily.blockCtors_map_raw
    (family : NormalizedFamily) :
    family.blockCtors.map (·.ctor.raw) = family.ctorPairs.map (·.raw) := by
  unfold NormalizedFamily.blockCtors
  induction family.ctorPairs with
  | nil => rfl
  | cons ctor ctors ih =>
    simp only [List.map_cons, List.cons.injEq, true_and]
    exact ih

theorem flatMap_congr_of_mem {α β : Type} (xs : List α)
    (f g : α → List β) (h : ∀ x ∈ xs, f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (.head _), ih (fun y hy => h y (.tail _ hy))]

theorem map_flatMap_eq {α β γ : Type} (xs : List α)
    (f : α → List β) (g : β → γ) :
    (xs.flatMap f).map g = xs.flatMap (fun x => (f x).map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append]
    rw [ih]

theorem BlockGenerationChecked.flatCtors_map_raw
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    gen.flatCtors.map (·.ctor.raw) = source.blockConstructorConstants := by
  rw [VInductDecl.blockConstructorConstants, ← gen.families_map_raw]
  unfold BlockGenerationChecked.flatCtors NormalizedCheckedBlock.flatCtors
  rw [map_flatMap_eq]
  simp only [List.flatMap_map]
  apply flatMap_congr_of_mem
  intro family hfamily
  rw [family.blockCtors_map_raw]
  exact family.ctorPairs_map_raw hfamily

theorem BlockGenerationChecked.flatCtor_uvars
    {source : VInductDecl} (gen : BlockGenerationChecked source)
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) :
    constructor.ctor.raw.uvars = source.uvars := by
  simp only [BlockGenerationChecked.flatCtors,
    NormalizedCheckedBlock.flatCtors, List.mem_flatMap] at hconstructor
  obtain ⟨family, hfamily, hconstructor⟩ := hconstructor
  simp only [NormalizedFamily.blockCtors, List.mem_map] at hconstructor
  obtain ⟨ctor, hctor, rfl⟩ := hconstructor
  exact gen.ctor_uvars hfamily hctor

/-- The validation staging fold is definitionally the family-constant phase
of block generation, modulo the explicit `toVConstVal` map. -/
theorem blockTypeConstants_foldlM_eq_stageInductiveTypes
    (env : VEnv) (source : VInductDecl) :
    source.blockTypeConstants.foldlM
      (fun env type => env.addConst type.name type.toVConstant) env =
      env.stageInductiveTypes source.types := by
  unfold VInductDecl.blockTypeConstants VEnv.stageInductiveTypes
  induction source.types generalizing env with
  | nil => rfl
  | cons type types ih =>
    simp only [List.map_cons, List.foldlM_cons]
    apply Option.bind_congr
    intro env' _
    exact ih env'

/-- Identity normalization is computationally the legacy analyzer. -/
theorem Normalization.identity_checked? (source : VInductDecl) :
    (Normalization.identity source).checked? = source.checked? := rfl

/-- A successful normalized analysis retains the exact normalization that was
analyzed; callers do not need to restate this projection as an unrelated
equality. -/
theorem Normalization.check?_normalization
    {source : VInductDecl} {norm : Normalization source}
    {block : NormalizedChecked source}
    (h : norm.check? = some block) :
    block.normalization = norm := by
  unfold Normalization.check? at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  rfl

/-- A successful generation analysis is indexed by the same normalization
retained in its checked block. -/
theorem Normalization.generation?_normalization
    {source : VInductDecl} {norm : Normalization source}
    {generation : GenerationChecked source}
    (h : norm.generation? = some generation) :
    generation.block.normalization = norm := by
  unfold Normalization.generation? at h
  obtain ⟨block, hblock, hgeneration⟩ :=
    Option.bind_eq_some_iff.mp h
  have hnorm := Normalization.check?_normalization hblock
  unfold NormalizedChecked.generation? at hgeneration
  split at hgeneration
  · have hgeneration' := Option.some.inj hgeneration
    rw [← hgeneration']
    exact hnorm
  · contradiction

theorem identityChecked?_isSome (source : VInductDecl) :
    (identityChecked? source).isSome = source.checked?.isSome := by
  obtain ⟨U, np, types⟩ := source
  cases types with
  | nil => rfl
  | cons type types =>
    cases types with
    | nil =>
      unfold identityChecked? Normalization.check?
      split
      · next sourceType hsource =>
        have htype : type = sourceType := by simpa using hsource
        subst sourceType
        split
        · next checked hchecked =>
          rw [← Normalization.identity_checked?]
          exact (congrArg (fun x => x.isSome) hchecked).symm
        · next hchecked =>
          rw [← Normalization.identity_checked?]
          exact (congrArg (fun x => x.isSome) hchecked).symm
      · next hsource => exact (hsource type rfl).elim
    | cons type' types => rfl

#guard_named_axioms Ix.Theory.Named.VInductDecl.Normalization.shape [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.NormalizedChecked.source_anatomy [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationChecked.shape [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationChecked.rawCtors_eq [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationChecked.viewCtors_eq [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Normalization.check?_normalization [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Normalization.generation?_normalization [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.identityChecked?_isSome [propext, Classical.choice, Quot.sound]

/- Identity-normalization compatibility is part of the public artifact
boundary. The conversion itself is computational; its proof fields inherit
the standard `Classical.choice` dependency already present in
`Normalization.identity`'s reflexive header check. -/
#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.analyzer_eq [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.identityBlock_generationShape [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.motiveType_eq_legacy [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.minorTypes_eq_legacy [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.recursor_eq_legacy [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.generatedRules_eq_legacy [propext, Classical.choice, Quot.sound]

/-- The four executable checks retained by a successful descriptor. Keeping
this bridge centralized lets the public proof API expose logical facts without
each consumer re-destructing `stage3Core`. -/
theorem Checked.analysis_accepted {decl : VInductDecl} (checked : decl.Checked) :
    stage3DirectCore decl.uvars decl.nparams checked.type = true ∧
    namesOK checked.type = true ∧ closedOK checked.type = true ∧
    levelsOK decl.uvars checked.type = true := by
  cases decl with
  | mk U np tys =>
    have htypes : tys = [checked.type] := checked.types_eq
    have hcore := checked.accepted
    simp only [stage3Core, htypes, Bool.and_eq_true] at hcore
    exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2⟩

/-- Every successful descriptor has pairwise-distinct generated type,
constructor, and recursor names. Downstream proofs should consume this fact
instead of unfolding the boolean analyzer. -/
theorem Checked.names_nodup {decl : VInductDecl} (checked : decl.Checked) :
    checked.names.Nodup := by
  rw [checked.names_eq]
  exact of_decide_eq_true (by simpa [namesOK] using checked.analysis_accepted.2.1)

/-- A checked family's type metadata has no loose term variables. -/
theorem Checked.type_closed {decl : VInductDecl} (checked : decl.Checked) :
    checked.type.type.ClosedN 0 := by
  have hclosed := checked.analysis_accepted.2.2.1
  simp only [closedOK, Bool.and_eq_true, List.all_eq_true] at hclosed
  exact of_decide_eq_true hclosed.1

/-- Every constructor type retained by a successful descriptor has no loose
term variables. -/
theorem Checked.ctor_closed {decl : VInductDecl} (checked : decl.Checked)
    {ctor : VConstVal} (hctor : ctor ∈ checked.type.ctors) : ctor.type.ClosedN 0 := by
  have hclosed := checked.analysis_accepted.2.2.1
  simp only [closedOK, Bool.and_eq_true, List.all_eq_true] at hclosed
  exact of_decide_eq_true (hclosed.2 ctor hctor)

/-- Every universe annotation in a checked family's type is in range. -/
theorem Checked.type_levelWF {decl : VInductDecl} (checked : decl.Checked) :
    checked.type.type.LevelWF decl.uvars := by
  have hlevels := checked.analysis_accepted.2.2.2
  simp only [levelsOK, Bool.and_eq_true, List.all_eq_true] at hlevels
  exact of_decide_eq_true hlevels.1

/-- Every universe annotation in a checked constructor type is in range. -/
theorem Checked.ctor_levelWF {decl : VInductDecl} (checked : decl.Checked)
    {ctor : VConstVal} (hctor : ctor ∈ checked.type.ctors) :
    ctor.type.LevelWF decl.uvars := by
  have hlevels := checked.analysis_accepted.2.2.2
  simp only [levelsOK, Bool.and_eq_true, List.all_eq_true] at hlevels
  exact of_decide_eq_true (hlevels.2 ctor hctor)

/-- The direct one-family facts carried by the descriptor, including the
new pre-declaration prohibition on self-reference in parameter/index domains. -/
theorem Checked.direct_anatomy {decl : VInductDecl} (checked : decl.Checked) :
    checked.type.uvars = decl.uvars ∧ checked.params.length = decl.nparams ∧
    checked.resultLevel.WF decl.uvars ∧
    (∀ P ∈ checked.params, P.hasConst checked.type.name = false) ∧
    (∀ I ∈ checked.indices, I.hasConst checked.type.name = false) ∧
    ∀ c ∈ checked.type.ctors, c.uvars = decl.uvars ∧
      VExpr.telN decl.nparams c.type = VExpr.telN decl.nparams checked.type.type ∧
      stage3Ctor decl.uvars checked.type.name decl.nparams checked.indices.length 0
        (VExpr.dropN decl.nparams c.type) = true := by
  have hdirect := checked.analysis_accepted.1
  simp only [stage3DirectCore, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hdirect
  obtain ⟨⟨⟨⟨hU, hparams⟩, hresult⟩, hformer⟩, hctors⟩ := hdirect
  simp only [typeFormerOK, Bool.and_eq_true, List.all_eq_true] at hformer
  refine ⟨hU, by simpa [checked.params_eq] using hparams, ?_, ?_, ?_, ?_⟩
  · rw [checked.result_eq] at hresult
    simpa using hresult
  · simpa [checked.params_eq] using hformer.1
  · simpa [checked.indices_eq] using hformer.2
  · intro c hc
    simpa [checked.indices_eq, and_assoc] using hctors c hc

/-- The raw family payload has the source declaration's universe arity. -/
theorem NormalizedChecked.sourceType_uvars_eq {source : VInductDecl}
    (block : NormalizedChecked source) :
    block.sourceType.uvars = source.uvars := by
  obtain ⟨raw, hsource, _, hrawU, _⟩ := block.source_anatomy
  have hraw : raw = block.sourceType := by
    simpa using hsource.symm.trans block.source_types_eq
  subst raw
  exact hrawU.trans
    (block.checked.direct_anatomy.1.trans block.uvars_eq.symm)

/-- The raw and checked family identities agree. -/
theorem NormalizedChecked.sourceType_name_eq {source : VInductDecl}
    (block : NormalizedChecked source) :
    block.sourceType.name = block.checked.type.name := by
  obtain ⟨raw, hsource, hname, _, _⟩ := block.source_anatomy
  have hraw : raw = block.sourceType := by
    simpa using hsource.symm.trans block.source_types_eq
  subst raw
  exact hname

/-- Every paired raw constructor has the source declaration's universe
arity. -/
theorem GenerationChecked.ctor_uvars_eq {source : VInductDecl}
    (gen : GenerationChecked source) {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    ctor.raw.uvars = source.uvars := by
  have hview : ctor.view ∈ gen.block.checked.constructors := by
    rw [← gen.viewCtors_eq]
    exact List.mem_map.2 ⟨ctor, hctor, rfl⟩
  rw [gen.block.checked.constructors_eq] at hview
  have hviewU :
      ctor.view.value.uvars = gen.block.normalization.view.uvars := by
    obtain ⟨c, hc, hcview⟩ := List.mem_map.1 hview
    rw [← hcview]
    exact (gen.block.checked.direct_anatomy.2.2.2.2.2 c hc).1
  have hpairU := (gen.shape.2.2.2.2.2 ctor hctor).2.1
  exact hpairU.trans (hviewU.trans gen.block.uvars_eq.symm)

/-- A paired checked constructor is exactly the direct analyzer result for
the corresponding constructor in the normalized view. The statement is
rewritten to the raw block's public header, whose equality is certified by
normalization shape. -/
theorem GenerationChecked.viewCtor_ofDirect {source : VInductDecl}
    (gen : GenerationChecked source) {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    ∃ c ∈ gen.block.checked.type.ctors,
      ctor.view = CheckedCtor.ofDirect source.uvars
        gen.block.sourceType.name source.nparams
        gen.block.checked.indices.length c := by
  have hview : ctor.view ∈ gen.block.checked.constructors := by
    rw [← gen.viewCtors_eq]
    exact List.mem_map.2 ⟨ctor, hctor, rfl⟩
  rw [gen.block.checked.constructors_eq] at hview
  obtain ⟨c, hc, hcview⟩ := List.mem_map.1 hview
  refine ⟨c, hc, ?_⟩
  rw [gen.block.uvars_eq, gen.block.nparams_eq,
    gen.block.sourceType_name_eq]
  exact hcview.symm

/-- Re-index declaration well-formedness onto the normalized checked data. -/
theorem Checked.wf_of_decl {decl : VInductDecl} (checked : decl.Checked)
    (hdecl : decl.WF env) : checked.WF env := by
  obtain ⟨-, hwf⟩ := hdecl
  obtain ⟨htel, hctors⟩ := hwf checked.type (by
    rw [checked.types_eq]
    exact .head _)
  have hsort : sortLevel decl.nparams checked.type = checked.resultLevel := by
    simp only [sortLevel, checked.result_eq]
  unfold Checked.WF
  refine ⟨?_, fun c hc => ?_⟩
  · simpa [checked.params_eq, checked.indices_eq] using htel
  · simpa [checked.params_eq, checked.indices_eq, hsort] using hctors c hc

/-- Normalized semantic evidence reconstructs the legacy declaration-level
`WF` contract. This is the compatibility direction used while clients migrate
to `Checked.WF`. -/
theorem Checked.to_declWF {decl : VInductDecl} (checked : decl.Checked)
    (hchecked : decl.checked? = some checked) (hwf : checked.WF env) : decl.WF env := by
  refine ⟨by simp [singletonStage3, hchecked], ?_⟩
  intro ty hty
  rw [checked.types_eq] at hty
  obtain rfl := List.mem_singleton.1 hty
  have hsort : sortLevel decl.nparams checked.type = checked.resultLevel := by
    simp only [sortLevel, checked.result_eq]
  unfold Checked.WF at hwf
  simpa [checked.params_eq, checked.indices_eq, hsort] using hwf

/-- The environment-indexed declaration contract is exactly the existence of
the analyzer result together with semantic evidence for its normalized data. -/
theorem wf_iff_exists_checked {decl : VInductDecl} :
    decl.WF env ↔ ∃ checked, decl.checked? = some checked ∧ checked.WF env := by
  constructor
  · intro hdecl
    obtain ⟨checked, hchecked⟩ := exists_checked_of_singletonStage3 hdecl.1
    exact ⟨checked, hchecked, checked.wf_of_decl hdecl⟩
  · rintro ⟨checked, hchecked, hwf⟩
    exact checked.to_declWF hchecked hwf

/- Keep the first exported descriptor invariants on the same accepted Theory
axiom baseline as the transaction API. -/
#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.names_nodup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.type_closed [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.ctor_closed [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.analysis_accepted [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.type_levelWF [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.ctor_levelWF [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.direct_anatomy [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.wf_of_decl [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.to_declWF [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.wf_iff_exists_checked [propext, Quot.sound]

/-- Unpack `stage3` for a declaration already known (from `addInduct`
success) to have a singleton type list. -/
theorem singletonStage3_anatomy {U np ty}
    (h : singletonStage3 ⟨U, np, [ty]⟩ = true) :
    ty.uvars = U ∧ (VExpr.telN np ty.type).length = np ∧
    (∃ l, VExpr.resultOf (VExpr.dropN np ty.type) = .sort l ∧ l.WF U) ∧
    (∀ I ∈ ctorFields (VExpr.dropN np ty.type), I.hasConst ty.name = false) ∧
    ∀ c ∈ ty.ctors, c.uvars = U ∧
      VExpr.telN np c.type = VExpr.telN np ty.type ∧
      stage3Ctor U ty.name np (ctorFields (VExpr.dropN np ty.type)).length 0
        (VExpr.dropN np c.type) = true := by
  obtain ⟨checked, -⟩ := exists_checked_of_singletonStage3 h
  have hcore := checked.accepted
  simp only [stage3Core, Bool.and_eq_true] at hcore
  have hdirect := hcore.1
  simp only [stage3DirectCore, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hdirect
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h6⟩ := hdirect
  simp only [typeFormerOK, Bool.and_eq_true, List.all_eq_true] at h4
  refine ⟨h1, h2, ?_, fun I hI => by simpa [Bool.not_eq_true'] using h4.2 I hI,
    fun c hc => by simpa [and_assoc] using h6 c hc⟩
  split at h3
  · next l heq => exact ⟨l, heq, by simpa using h3⟩
  · exact Bool.noConfusion h3

end VInductDecl

/-! ## Context and spine lemmas -/

theorem Lookup.append {A : VExpr} : ∀ (Δ : List VExpr) {Γ},
    Lookup (Δ ++ A :: Γ) Δ.length (A.liftN (Δ.length + 1))
  | [], _ => .zero
  | B :: Δ, Γ => by
    simpa [← VExpr.liftN_succ] using (Lookup.append (A := A) Δ (Γ := Γ)).succ (A := B)

theorem Lookup.append_closed {A : VExpr} (hA : A.ClosedN 0) (Δ : List VExpr) {Γ} :
    Lookup (Δ ++ A :: Γ) Δ.length A := by
  simpa [hA.liftN_eq (Nat.zero_le _)] using Lookup.append (A := A) Δ (Γ := Γ)

theorem Lookup.of_getElem? : ∀ {Γ : List VExpr} {i : Nat} {A : VExpr},
    Γ[i]? = some A → Lookup Γ i (A.liftN (i+1))
  | B :: _, 0, A, h => by
    obtain rfl : B = A := by simpa using h
    exact .zero
  | B :: Γ, i+1, A, h => by
    have := Lookup.of_getElem? (Γ := Γ) (i := i) (A := A) (by simpa using h)
    simpa [← VExpr.liftN_succ] using this.succ (A := B)

theorem Lookup.of_getElem?_closed {Γ : List VExpr} {i : Nat} {A : VExpr}
    (h : Γ[i]? = some A) (hA : A.ClosedN 0) : Lookup Γ i A := by
  simpa [hA.liftN_eq (Nat.zero_le _)] using Lookup.of_getElem? h

/-- Right-associated: the element right past a two-part prefix. -/
theorem getElem?_rstack3 {α} (Δ mid : List α) (a : α) (Γ : List α) {i : Nat}
    (h : i = Δ.length + mid.length) : (Δ ++ (mid ++ a :: Γ))[i]? = some a := by
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
    show i - Δ.length - mid.length = 0 from by omega]
  rfl

/-- Right-associated: an element inside the middle block. -/
theorem getElem?_rstack_mid {α} (Δ mid Γ : List α) {i : Nat}
    (h1 : Δ.length ≤ i) (h2 : i - Δ.length < mid.length) :
    (Δ ++ (mid ++ Γ))[i]? = mid[i - Δ.length]? := by
  rw [List.getElem?_append_right h1, List.getElem?_append_left h2]

/-- The element right past a two-part prefix. -/
theorem getElem?_stack3 {α} (Δ mid Γ : List α) (a : α) {i : Nat}
    (h : i = Δ.length + mid.length) : (Δ ++ mid ++ a :: Γ)[i]? = some a := by
  rw [List.append_assoc, List.getElem?_append_right (by omega),
    show i - Δ.length = mid.length from by omega,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- An element inside the middle block of a three-part context. -/
theorem getElem?_stack_mid {α} (Δ mid Γ : List α) {i : Nat}
    (h1 : Δ.length ≤ i) (h2 : i - Δ.length < mid.length) :
    (Δ ++ mid ++ Γ)[i]? = mid[i - Δ.length]? := by
  rw [List.append_assoc, List.getElem?_append_right h1,
    List.getElem?_append_left h2]

namespace VEnv

/-- A typed Theory expression cannot mention a constant absent from its
environment. -/
theorem HasType.hasConst_false_of_absent
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {name : Name} {e A : VExpr}
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (absent : env.constants name = none)
    (typed : env.HasType U Γ e A) :
    e.hasConst name = false := by
  induction e generalizing Γ A with
  | bvar | sort => rfl
  | const constant levels =>
      by_cases equality : constant = name
      · subst constant
        obtain ⟨ci, present, levelWF, arity⟩ :=
          typed.const_inv henv hΓ
        rw [absent] at present
        contradiction
      · simp [VExpr.hasConst, equality]
  | app function argument functionIH argumentIH =>
      obtain ⟨domain, body, functionType, argumentType⟩ :=
        typed.app_inv henv hΓ
      simp only [VExpr.hasConst, functionIH hΓ functionType,
        argumentIH hΓ argumentType, Bool.false_or]
  | lam domain body domainIH bodyIH =>
      obtain ⟨domainType, bodyWF⟩ := typed.lam_inv henv hΓ
      obtain ⟨domainLevel, domainHasType⟩ := domainType
      obtain ⟨bodyType, bodyHasType⟩ := bodyWF
      have nextContextWF : OnCtx (domain :: Γ) (env.IsType U) := by
        change OnCtx Γ (env.IsType U) ∧ env.IsType U Γ domain
        exact ⟨hΓ, ⟨domainLevel, domainHasType⟩⟩
      simp only [VExpr.hasConst, domainIH hΓ domainHasType,
        bodyIH nextContextWF bodyHasType, Bool.false_or]
  | forallE domain body domainIH bodyIH =>
      obtain ⟨domainType, bodyType⟩ := typed.forallE_inv henv
      obtain ⟨domainLevel, domainHasType⟩ := domainType
      obtain ⟨bodyLevel, bodyHasType⟩ := bodyType
      have nextContextWF : OnCtx (domain :: Γ) (env.IsType U) := by
        change OnCtx Γ (env.IsType U) ∧ env.IsType U Γ domain
        exact ⟨hΓ, ⟨domainLevel, domainHasType⟩⟩
      simp only [VExpr.hasConst, domainIH hΓ domainHasType,
        bodyIH nextContextWF bodyHasType, Bool.false_or]

/-- The spine `bvarRevRange Δ.length As.length` selects exactly the binders
`As` (reversed into the context past `Δ`), when all of `As` are closed. -/
theorem hasType_bvarRevRange {env : VEnv} {U : Nat} :
    ∀ {As : List VExpr}, (∀ A ∈ As, A.ClosedN 0) → ∀ {Δ Γ₀ : List VExpr},
    List.Forall₂ (env.HasType U (Δ ++ As.reverse ++ Γ₀))
      (VExpr.bvarRevRange Δ.length As.length) As
  | [], _, _, _ => .nil
  | A :: As, h, Δ, Γ₀ => by
    refine .cons (.bvar ?_) ?_
    · have := Lookup.append_closed (h _ (.head _)) (Δ ++ As.reverse) (Γ := Γ₀)
      simpa [List.append_assoc] using this
    · have := hasType_bvarRevRange (env := env) (U := U) (As := As)
        (fun A h' => h _ (.tail _ h')) (Δ := Δ) (Γ₀ := A :: Γ₀)
      simpa [List.append_assoc] using this

theorem ClosedN.forallN_of_all {As : List VExpr} (hAs : ∀ A ∈ As, A.ClosedN 0)
    {B : VExpr} (hB : B.ClosedN 0) {k : Nat} : (VExpr.forallN As B).ClosedN k := by
  induction As generalizing k with
  | nil => exact hB.mono (Nat.zero_le _)
  | cons A As ih =>
    exact ⟨(hAs _ (.head _)).mono (Nat.zero_le _), ih fun A h => hAs _ (.tail _ h)⟩

/-- Substituting a variable for the innermost binder of a lifted term is a
smaller lift: the telescope-self-application identity. Unconditional. -/
theorem _root_.Ix.Theory.Named.VExpr.liftN_succ_inst_bvar (e : VExpr) :
    ∀ (s k : Nat), (e.liftN (s+1) (k+1)).inst (.bvar s) k = e.liftN s k := by
  induction e with intro s k
  | bvar j =>
    show VExpr.instVar (liftVar (s+1) j (k+1)) (.bvar s) k = .bvar (liftVar s j k)
    unfold liftVar
    rcases Nat.lt_trichotomy j k with h | rfl | h
    · rw [if_pos (Nat.lt_succ_of_lt h), if_pos h]
      simp [VExpr.instVar, h]
    · rw [if_pos (Nat.lt_succ_self _), if_neg (Nat.lt_irrefl _)]
      show VExpr.instVar j (.bvar s) j = _
      rw [show VExpr.instVar j (.bvar s) j = (VExpr.bvar s).liftN j from by
        unfold VExpr.instVar; rw [if_neg (Nat.lt_irrefl _), if_pos rfl]]
      show VExpr.bvar (liftVar j s) = _
      rw [liftVar_base, Nat.add_comm]
    · rw [if_neg (by omega), if_neg (by omega)]
      simp only [VExpr.instVar]
      rw [if_neg (by omega), if_neg (by omega)]
      congr 1; omega
  | sort | const => intros; rfl
  | app f a ihf iha => simp [VExpr.liftN, VExpr.inst, ihf, iha]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp [VExpr.liftN, VExpr.inst, ihA s k, ihb s (k+1)]

/-- Applying `f : (∀ As, B).liftN Δ.length` to the spine of variables
referring to its own binders, sitting in the context right below `Δ`.
The lift on the type in the hypothesis is what makes the invariant close
over the recursion; no closedness is needed. -/
theorem HasType.appN_selfSpine {env : VEnv} {U : Nat} :
    ∀ {As : List VExpr} {B : VExpr} {Δ Γ : List VExpr} {f},
    env.HasType U (Δ ++ As.reverse ++ Γ) f
      ((VExpr.forallN As B).liftN (Δ.length + As.length)) →
    env.HasType U (Δ ++ As.reverse ++ Γ)
      (f.appN (VExpr.bvarRevRange Δ.length As.length)) (B.liftN Δ.length)
  | [], B, Δ, Γ, f, hf => by simpa using hf
  | A :: As, B, Δ, Γ, f, hf => by
    have harg : env.HasType U (Δ ++ (A :: As).reverse ++ Γ)
        (.bvar (Δ.length + As.length)) (A.liftN (Δ.length + As.length + 1)) := by
      have := Lookup.append (A := A) (Δ ++ As.reverse) (Γ := Γ)
      simp only [List.length_append, List.length_reverse] at this
      exact .bvar (by simpa [List.append_assoc, Nat.add_assoc] using this)
    have happ := HasType.app hf harg
    simp only [List.length_cons, Nat.add_succ] at happ
    rw [VExpr.liftN_succ_inst_bvar] at happ
    have := HasType.appN_selfSpine (As := As) (B := B) (Δ := Δ) (Γ := A :: Γ)
      (f := f.app (.bvar (Δ.length + As.length))) (by simpa [List.append_assoc] using happ)
    simpa [List.append_assoc, VExpr.bvarRevRange] using this

/-- The closed-telescope entry point for `appN_selfSpine`. -/
theorem HasType.appN_selfSpine' {env : VEnv} {U : Nat}
    {As : List VExpr} {B : VExpr} {Δ Γ : List VExpr} {f}
    (hcl : (VExpr.forallN As B).ClosedN 0)
    (hf : env.HasType U (Δ ++ As.reverse ++ Γ) f (VExpr.forallN As B)) :
    env.HasType U (Δ ++ As.reverse ++ Γ)
      (f.appN (VExpr.bvarRevRange Δ.length As.length)) (B.liftN Δ.length) :=
  HasType.appN_selfSpine (by rwa [hcl.liftN_eq (Nat.zero_le _)])

/-- Application of a closed non-dependent telescope. -/
theorem HasType.appN_closed {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {As : List VExpr}, (∀ A ∈ As, A.ClosedN 0) → ∀ {B : VExpr}, B.ClosedN 0 →
    ∀ {f args}, env.HasType U Γ f (VExpr.forallN As B) →
    List.Forall₂ (env.HasType U Γ) args As →
    env.HasType U Γ (f.appN args) B
  | [], _, _, _, _, _, hf, .nil => hf
  | A :: As, hAs, B, hB, f, a :: as, hf, .cons ha hargs => by
    have h2 : env.HasType U Γ (f.app a) ((VExpr.forallN As B).inst a) := .app hf ha
    rw [(ClosedN.forallN_of_all (fun A h => hAs _ (.tail _ h)) hB).instN_eq
      (Nat.zero_le _)] at h2
    exact appN_closed (fun A h => hAs _ (.tail _ h)) hB (f := f.app a) h2 hargs

theorem isType_forallN_free {env : VEnv} {U : Nat} {As : List VExpr}
    (hAs : ∀ A ∈ As, ∀ Γ, env.IsType U Γ A)
    {B : VExpr} (hB : ∀ Γ, env.IsType U Γ B) : ∀ Γ, env.IsType U Γ (VExpr.forallN As B) := by
  induction As with
  | nil => exact hB
  | cons A As ih =>
    exact fun Γ => (hAs _ (.head _) Γ).forallE
      (ih (fun A h => hAs _ (.tail _ h)) (A :: Γ))

theorem HasType.lamN {env : VEnv} {U : Nat} : ∀ {As Γ body B},
    OnTel env U Γ As → env.HasType U (As.reverse ++ Γ) body B →
    env.HasType U Γ (VExpr.lamN As body) (VExpr.forallN As B)
  | [], _, _, _, _, hb => hb
  | A :: As, Γ, body, B, ⟨⟨_, hA⟩, hT⟩, hb =>
    HasType.lam hA (HasType.lamN hT (by simpa [List.append_assoc] using hb))

theorem IsType.forallN {env : VEnv} {U : Nat} : ∀ {As Γ B},
    OnTel env U Γ As → env.IsType U (As.reverse ++ Γ) B →
    env.IsType U Γ (VExpr.forallN As B)
  | [], _, _, _, hB => hB
  | A :: As, Γ, B, ⟨hA, hT⟩, hB =>
    IsType.forallE hA (IsType.forallN hT (by simpa [List.append_assoc] using hB))

theorem onTel_of_free {env : VEnv} {U : Nat} : ∀ {As Γ},
    (∀ A ∈ As, ∀ Γ', env.IsType U Γ' A) → OnTel env U Γ As
  | [], _, _ => trivial
  | _ :: _, _, h =>
    ⟨h _ (.head _) _, onTel_of_free fun _ h' Γ' => h _ (.tail _ h') Γ'⟩

theorem OnTel.append {env : VEnv} {U : Nat} : ∀ {As Bs Γ},
    OnTel env U Γ As → OnTel env U (As.reverse ++ Γ) Bs → OnTel env U Γ (As ++ Bs)
  | [], _, _, _, h2 => h2
  | _ :: As, Bs, Γ, ⟨hA, h1⟩, h2 =>
    ⟨hA, OnTel.append h1 (by simpa [List.append_assoc] using h2)⟩

theorem OnTel.of_append {env : VEnv} {U : Nat} : ∀ {As Bs Γ},
    OnTel env U Γ (As ++ Bs) → OnTel env U Γ As ∧ OnTel env U (As.reverse ++ Γ) Bs
  | [], _, _, h => ⟨trivial, h⟩
  | A :: As, Bs, Γ, ⟨hA, hT⟩ => by
    obtain ⟨h1, h2⟩ := OnTel.of_append (As := As) hT
    exact ⟨⟨hA, h1⟩, by simpa [List.append_assoc] using h2⟩

/-- Push a context lift under a reversed telescope: inserting binders below
shifts each telescope entry at its own depth. -/
theorem _root_.Ix.Theory.Named.Ctx.LiftN.consTel {n : Nat} : ∀ (As : List VExpr) {k : Nat}
    {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
    Ctx.LiftN n (As.length + k) (As.reverse ++ Γ)
      ((VExpr.liftTelN n As k).reverse ++ Γ')
  | [], k, Γ, Γ', W => by simpa using W
  | A :: As, k, Γ, Γ', W => by
    have h := Ctx.LiftN.consTel As (Ctx.LiftN.succ (A := A) W)
    rw [show As.length + (k+1) = (A :: As).length + k from by simp; omega] at h
    simpa [VExpr.liftTelN, List.append_assoc] using h

/-- Weakening a telescope: inserting binders at depth `k` of the context
shifts each entry at its own depth. -/
theorem OnTel.weakN {env : VEnv} {U n : Nat} (henv : env.Ordered) :
    ∀ {As Γ Γ' k}, Ctx.LiftN n k Γ Γ' → OnTel env U Γ As →
    OnTel env U Γ' (VExpr.liftTelN n As k)
  | [], _, _, _, _, _ => trivial
  | _ :: _, _, _, _, W, ⟨hA, hT⟩ =>
    ⟨hA.weakN henv W, OnTel.weakN henv W.succ hT⟩

/-- Universe instantiation of a telescope. -/
theorem OnTel.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {As Γ}, OnTel env U Γ As →
    OnTel env U' (Γ.map (VExpr.instL ls)) (As.map (VExpr.instL ls))
  | [], _, _ => trivial
  | _ :: As, Γ, ⟨hA, hT⟩ =>
    ⟨hA.instL hls, by simpa using OnTel.instL hls (As := As) (Γ := _ :: Γ) hT⟩

/-! ### Spine typing -/

theorem SpineWF.hasType_appN {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {es : List VExpr} {A B f : VExpr}, env.SpineWF U Γ A es B →
    env.HasType U Γ f A → env.HasType U Γ (f.appN es) B := by
  intro es
  induction es with intro A B f h hf
  | nil => cases h; exact hf
  | cons e es ih =>
      cases h with
      | cons he hrest =>
        exact ih hrest (hf.app he)

/-- Concatenate two adjacent, well-typed application spines. -/
theorem SpineWF.append {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {es : List VExpr} {A B : VExpr}, env.SpineWF U Γ A es B →
      ∀ {es' : List VExpr} {C : VExpr}, env.SpineWF U Γ B es' C →
        env.SpineWF U Γ A (es ++ es') C
  | [], _, _, .nil, _, _, h' => h'
  | _ :: _, _, _, .cons he hrest, _, _, h' =>
      .cons he (SpineWF.append hrest h')

/-- Split a well-typed application spine at an explicit list prefix. -/
theorem SpineWF.split {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {front suffix : List VExpr} {A B : VExpr},
      env.SpineWF U Γ A (front ++ suffix) B →
      ∃ cursor, env.SpineWF U Γ A front cursor ∧
        env.SpineWF U Γ cursor suffix B
  | [], suffix, A, B, h => ⟨A, .nil, by simpa using h⟩
  | _ :: front, suffix, _, _, .cons he hrest => by
      obtain ⟨cursor, hfront, hsuffix⟩ := SpineWF.split hrest
      exact ⟨cursor, .cons he hfront, hsuffix⟩

/-- Extend a well-typed application spine by one final argument. -/
theorem SpineWF.snoc {env : VEnv} {U : Nat} {Γ : List VExpr} {e D C : VExpr} :
    ∀ {es : List VExpr} {A : VExpr}, env.SpineWF U Γ A es (.forallE D C) →
    env.HasType U Γ e D → env.SpineWF U Γ A (es ++ [e]) (C.inst e)
  | [], _, .nil, he => .cons he .nil
  | _ :: _, _, .cons ha hrest, he =>
    .cons ha (SpineWF.snoc hrest he)

/-- Retarget a spine judgment along a pi with the same domains: the
result is the iterated instantiation of the new codomain. -/
theorem SpineWF.retarget {env : VEnv} {U : Nat} {Γ : List VExpr} {es : List VExpr} :
    ∀ {Δ : List VExpr} {C B : VExpr}, env.SpineWF U Γ (VExpr.forallN Δ C) es B →
    es.length = Δ.length → ∀ (C' : VExpr),
    env.SpineWF U Γ (VExpr.forallN Δ C') es (VExpr.instRev C' es) := by
  induction es with intro Δ C B h hlen C'
  | nil =>
    obtain rfl : Δ = [] := by
      cases Δ with
      | nil => rfl
      | cons _ _ => simp at hlen
    cases h
    exact .nil
  | cons e es ih =>
    cases Δ with
    | nil => simp at hlen
    | cons A Δ =>
      cases h with
      | cons he hrest =>
        have hlen' : es.length = Δ.length := by simpa using hlen
        refine .cons he ?_
        rw [VExpr.instN_forallN] at hrest
        have := ih hrest (by simp [VExpr.instTelN_length, hlen']) (C'.inst e Δ.length)
        show env.SpineWF U Γ ((VExpr.forallN Δ C').inst e) es
          (VExpr.instRev (C'.inst e es.length) es)
        rw [VExpr.instN_forallN, Nat.zero_add, hlen']
        exact this

/-- A spine consuming a full telescope and ending in the same sort has
exactly one argument per telescope binder. -/
theorem SpineWF.forallN_sort_length
    {env : VEnv} {U : Nat} {Γ : List VExpr} {l : VLevel} :
    ∀ {As es}, env.SpineWF U Γ (VExpr.forallN As (.sort l)) es (.sort l) →
      es.length = As.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | A :: As, e :: es, h => by
    cases h with
    | cons he hrest =>
      rw [VExpr.instN_forallN] at hrest
      have hlen := SpineWF.forallN_sort_length hrest
      simpa [VExpr.instTelN_length] using congrArg Nat.succ hlen

end VEnv

/-! ## The induction-hypothesis telescope under lifting -/

namespace VInductDecl

/-- `ihsFrom` after the motive-directed lift into the rule context. -/
def ihsR (m k : Nat) : List (Nat × List VExpr) → Nat → List VExpr
  | [], _ => []
  | (j, idxs) :: rs, p =>
    VExpr.appN (.bvar (k + (m + p)))
      ((idxs.map fun e => ((e.liftN 1 j).liftN (m-j+p)).liftN k (m+p)) ++
        [.bvar (m-1-j+p)]) ::
    ihsR m k rs (p+1)

/-- Recursive-field positions are bounded by the field count. -/
theorem recPairs_lt {U : Nat} {T : Name} {np ni : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ q ∈ recPairs U T np ni Bs j₀, q.1 < j₀ + Bs.length
  | B :: Bs, j₀, q, h => by
    unfold recPairs at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · simp
      · have := recPairs_lt _ h
        simp only [List.length_cons]; omega
    · have := recPairs_lt _ h
      simp only [List.length_cons]; omega

theorem recPairs_ge {U : Nat} {T : Name} {np ni : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ q ∈ recPairs U T np ni Bs j₀, j₀ ≤ q.1
  | _ :: Bs, j₀, q, h => by
    unfold recPairs at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (recPairs_ge _ h)
    · exact Nat.le_of_succ_le (recPairs_ge _ h)

/-- Recursive positions really hold a recursive field, and the recorded
index arguments are its index arguments. -/
theorem recPairs_getElem {U : Nat} {T : Name} {np ni : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ q ∈ recPairs U T np ni Bs j₀, ∃ B, Bs[q.1 - j₀]? = some B ∧
      isRecField U T np ni q.1 B = true ∧ q.2 = recFieldIdxs np B
  | B :: Bs, j₀, q, h => by
    unfold recPairs at h
    split at h
    · next heq =>
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨B, by simp, heq, rfl⟩
      · have h1 := recPairs_ge _ h
        obtain ⟨B', hB', hrec, hidx⟩ := recPairs_getElem _ h
        refine ⟨B', ?_, hrec, hidx⟩
        rw [show q.1 - j₀ = (q.1 - (j₀+1)) + 1 from by omega]
        simpa using hB'
    · have h1 := recPairs_ge _ h
      obtain ⟨B', hB', hrec, hidx⟩ := recPairs_getElem _ h
      refine ⟨B', ?_, hrec, hidx⟩
      rw [show q.1 - j₀ = (q.1 - (j₀+1)) + 1 from by omega]
      simpa using hB'

/-- Every analyzed recursive argument names a field within the source
telescope. -/
theorem recArgs_lt {U : Nat} {T : Name} {np ni : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ r ∈ recArgs U T np ni Bs j₀, r.fieldIndex < j₀ + Bs.length
  | B :: Bs, j₀, r, h => by
    unfold recArgs at h
    split at h
    · next r₀ hr₀ =>
      rcases List.mem_cons.1 h with rfl | h
      · have hj := (recArg?_eq hr₀).1
        simp only [List.length_cons]
        omega
      · have := recArgs_lt _ h
        simp only [List.length_cons]; omega
    · have := recArgs_lt _ h
      simp only [List.length_cons]; omega

/-- Recursive-argument field positions never precede the starting depth. -/
theorem recArgs_ge {U : Nat} {T : Name} {np ni : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ r ∈ recArgs U T np ni Bs j₀, j₀ ≤ r.fieldIndex
  | _ :: Bs, j₀, r, h => by
    unfold recArgs at h
    split at h
    · next r₀ hr₀ =>
      rcases List.mem_cons.1 h with rfl | h
      · simp [(recArg?_eq hr₀).1]
      · exact Nat.le_of_succ_le (recArgs_ge _ h)
    · exact Nat.le_of_succ_le (recArgs_ge _ h)

/-- An analyzed recursive argument is backed by the field at its recorded
position, and re-analysis returns the same normalized descriptor. -/
theorem recArgs_getElem {U : Nat} {T : Name} {np ni : Nat} :
    ∀ {Bs : List VExpr} {j₀ : Nat}, ∀ r ∈ recArgs U T np ni Bs j₀,
    ∃ B, Bs[r.fieldIndex - j₀]? = some B ∧
      recArg? U T np ni r.fieldIndex B = some r
  | B :: Bs, j₀, r, h => by
    unfold recArgs at h
    split at h
    · next r₀ hr₀ =>
      rcases List.mem_cons.1 h with rfl | h
      · have hj := (recArg?_eq hr₀).1
        subst hj
        exact ⟨B, by simp, hr₀⟩
      · have hge := recArgs_ge _ h
        obtain ⟨B', hB', hr⟩ := recArgs_getElem _ h
        refine ⟨B', ?_, hr⟩
        rw [show r.fieldIndex - j₀ = (r.fieldIndex - (j₀+1)) + 1 from by omega]
        simpa using hB'
    · have hge := recArgs_ge _ h
      obtain ⟨B', hB', hr⟩ := recArgs_getElem _ h
      refine ⟨B', ?_, hr⟩
      rw [show r.fieldIndex - j₀ = (r.fieldIndex - (j₀+1)) + 1 from by omega]
      simpa using hB'

theorem ihsFrom_liftN (m k : Nat) : ∀ (rs : List (Nat × List VExpr)),
    (∀ q ∈ rs, q.1 < m) → ∀ (p : Nat) (X : VExpr),
    (VExpr.forallN (ihsFrom m rs p) X).liftN k (m + p) =
    VExpr.forallN (ihsR m k rs p) (X.liftN k (m + p + rs.length))
  | [], _, _, _ => rfl
  | (j, idxs) :: rs, hm, p, X => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append, List.map_map,
        show ((VExpr.bvar (m+p)).liftN k (m+p)) = .bvar (k+(m+p)) from by
          show VExpr.bvar (liftVar k (m+p) (m+p)) = _
          rw [liftVar_le (Nat.le_refl _)],
        show ([VExpr.bvar (m-1-j+p)]).map (VExpr.liftN k · (m+p)) =
            [VExpr.bvar (m-1-j+p)] from by
          show [VExpr.bvar (liftVar k (m-1-j+p) (m+p))] = _
          rw [liftVar_lt (show m-1-j+p < m+p from by
            have := hm _ (List.Mem.head _); simp at this; omega)]]
      rfl
    · rw [show m + p + 1 = m + (p+1) from rfl,
        ihsFrom_liftN m k rs (fun q h => hm q (.tail _ h)) (p+1) X,
        show m + (p+1) + rs.length = m + p + (rs.length+1) from by omega]
      rfl

/-- `ihsFrom_liftN` with the cutoff generalized, for syntactic rewriting. -/
theorem ihsFrom_liftN' (m k : Nat) (rs : List (Nat × List VExpr))
    (hm : ∀ q ∈ rs, q.1 < m) (p : Nat) (X : VExpr) {cut : Nat} (hcut : cut = m + p) :
    (VExpr.forallN (ihsFrom m rs p) X).liftN k cut =
    VExpr.forallN (ihsR m k rs p) (X.liftN k (m + p + rs.length)) := by
  rw [hcut]; exact ihsFrom_liftN m k rs hm p X

theorem ihsR_liftN1 (m k : Nat) : ∀ (rs : List (Nat × List VExpr)) (p c : Nat), c ≤ p →
    (∀ q ∈ rs, q.1 < m) → ∀ (X : VExpr),
    VExpr.forallN (ihsR m k rs (p+1)) (X.liftN 1 (c + rs.length)) =
    (VExpr.forallN (ihsR m k rs p) X).liftN 1 c
  | [], p, c, _, _, X => by simp [ihsR, VExpr.forallN]
  | (j, idxs) :: rs, p, c, hc, hm, X => by
    have hjm : j < m := by have := hm _ (List.Mem.head _); simpa using this
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append, List.map_map,
        show ((VExpr.bvar (k+(m+p))).liftN 1 c) = .bvar (k+(m+(p+1))) from by
          show VExpr.bvar (liftVar 1 (k+(m+p)) c) = _
          rw [liftVar_le (by omega)]
          congr 1; omega,
        show ([VExpr.bvar (m-1-j+p)]).map (VExpr.liftN 1 · c) =
            [VExpr.bvar (m-1-j+(p+1))] from by
          show [VExpr.bvar (liftVar 1 (m-1-j+p) c)] = _
          rw [liftVar_le (by omega)]
          congr 2; omega]
      refine congrArg (VExpr.appN _) (congrArg (· ++ [VExpr.bvar (m-1-j+(p+1))]) ?_)
      refine List.map_congr_left fun e _ => .symm ?_
      show (((e.liftN 1 j).liftN (m-j+p)).liftN k (m+p)).liftN 1 c = _
      rw [VExpr.liftN_liftN_comm _ 1 k c (m+p) (by omega),
        show ((e.liftN 1 j).liftN (m-j+p)).liftN 1 c =
          (e.liftN 1 j).liftN (m-j+(p+1)) from by
          rw [VExpr.liftN'_liftN' (Nat.zero_le _) (by omega)]
          rfl]
      rfl
    · rw [show c + ((j, idxs) :: rs).length = (c+1) + rs.length from by simp; omega]
      exact ihsR_liftN1 m k rs (p+1) (c+1) (by omega) (fun q h => hm q (.tail _ h)) X

theorem ihsFrom_length (m : Nat) : ∀ (rs : List (Nat × List VExpr)) (p : Nat),
    (ihsFrom m rs p).length = rs.length
  | [], _ => rfl
  | (_, _) :: rs, p => by simp [ihsFrom, ihsFrom_length m rs (p+1)]

theorem ihsFromRecArgs_length (m : Nat) : ∀ (rs : List RecArg) (p : Nat),
    (ihsFromRecArgs m rs p).length = rs.length
  | [], _ => rfl
  | _ :: rs, p => by simp [ihsFromRecArgs, ihsFromRecArgs_length m rs (p+1)]

theorem minorTypes_length (U : Nat) (T : Name) (np : Nat) (ty : VInductiveType) :
    ∀ (cs : List VConstVal) (i : Nat), (minorTypes U T np ty cs i).length = cs.length
  | [], _ => rfl
  | _ :: cs, i => by simp [minorTypes, minorTypes_length U T np ty cs (i+1)]

theorem minorTypesRec_length (U : Nat) (T : Name) (np : Nat) (ty : VInductiveType) :
    ∀ (cs : List VConstVal) (i : Nat), (minorTypesRec U T np ty cs i).length = cs.length
  | [], _ => rfl
  | _ :: cs, i => by
    simp [minorTypesRec, minorTypesRec_length U T np ty cs (i+1)]

theorem bvarRevRange_liftN_ge : ∀ (m off n k : Nat), k ≤ off →
    (VExpr.bvarRevRange off m).map (VExpr.liftN n · k) = VExpr.bvarRevRange (n + off) m
  | 0, _, _, _, _ => rfl
  | m+1, off, n, k, h => by
    show VExpr.bvar _ :: _ = VExpr.bvar _ :: _
    rw [bvarRevRange_liftN_ge m off n k h]
    congr 2
    show liftVar n (off + m) k = n + off + m
    rw [liftVar_le (by omega)]; omega

theorem bvarRevRange_instL : ∀ (m off : Nat) (ls : List VLevel),
    (VExpr.bvarRevRange off m).map (VExpr.instL ls) = VExpr.bvarRevRange off m
  | 0, _, _ => rfl
  | m+1, off, ls => by
    show _ :: _ = _ :: _
    rw [bvarRevRange_instL m off ls]
    rfl

/-- The transported type of an analyzed recursive field is exactly its
generated functional-IH domain telescope followed by the transported family
target. -/
theorem recArg_minor_fieldType {U : Nat} {T : Name} {np ni : Nat}
    {B : VExpr} {r₀ : RecArg}
    (hr : recArg? U T np ni r₀.fieldIndex B = some r₀)
    (m p : Nat) (hj : r₀.fieldIndex < m)
    (mode : ElimMode := .large) :
    let ls := mode.sourceLevels U
    let r := r₀.instL ls
    ((B.instL ls).liftN 1 r.fieldIndex).liftN
        (m-r.fieldIndex+p) =
      VExpr.forallN (r.minorBinders m p)
        (VExpr.appN (.const T ls)
          (VExpr.bvarRevRange (m+p+r.binders.length+1) np ++
            r.indices.map fun e =>
              (e.liftN 1 (r.fieldIndex+r.binders.length)).liftN
                (m-r.fieldIndex+p) r.binders.length)) := by
  dsimp only
  obtain ⟨-, -, hB, -, -, -⟩ := recArg?_eq hr
  conv => lhs; rw [hB]
  simp only [RecArg.instL, VExpr.instL_forallN, VExpr.instL_appN,
    List.map_append, bvarRevRange_instL,
    show (VExpr.const T (VLevel.params U)).instL (mode.sourceLevels U) =
      .const T (mode.sourceLevels U) from by
        simp [VExpr.instL, ElimMode.sourceLevels,
          VLevel.params_map_inst_params'],
    VExpr.liftN_forallN, VExpr.liftN_appN]
  simp only [List.length_map, VExpr.liftTelN_length, Nat.zero_add]
  rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    show
      m - r₀.fieldIndex + p + (1 + (r₀.fieldIndex + r₀.binders.length)) =
        m + p + r₀.binders.length + 1 from by omega]
  simp only [List.map_map, RecArg.minorBinders]
  apply congrArg (VExpr.forallN _)
  apply congrArg (VExpr.appN (.const T (mode.sourceLevels U)))
  apply congrArg (VExpr.bvarRevRange (m + p + r₀.binders.length + 1) np ++ ·)
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply]

/-- Rule-context analogue of `recArg_minor_fieldType`: transport a recursive
field beneath the motive and all constructor minors, then beneath the later
constructor fields. -/
theorem recArg_rule_fieldType {U : Nat} {T : Name} {np ni : Nat}
    {B : VExpr} {r₀ : RecArg}
    (hr : recArg? U T np ni r₀.fieldIndex B = some r₀)
    (m k : Nat) (hj : r₀.fieldIndex < m)
    (mode : ElimMode := .large) :
    let ls := mode.sourceLevels U
    let r := r₀.instL ls
    ((B.instL ls).liftN (k+1) r.fieldIndex).liftN
        (m-r.fieldIndex) =
      VExpr.forallN (r.ruleBinders m k)
        (VExpr.appN (.const T ls)
          (VExpr.bvarRevRange (m+k+r.binders.length+1) np ++
            r.indices.map fun e =>
              (e.liftN (k+1) (r.fieldIndex+r.binders.length)).liftN
                (m-r.fieldIndex) r.binders.length)) := by
  dsimp only
  obtain ⟨-, -, hB, -, -, -⟩ := recArg?_eq hr
  conv => lhs; rw [hB]
  simp only [RecArg.instL, VExpr.instL_forallN, VExpr.instL_appN,
    List.map_append, bvarRevRange_instL,
    show (VExpr.const T (VLevel.params U)).instL (mode.sourceLevels U) =
      .const T (mode.sourceLevels U) from by
        simp [VExpr.instL, ElimMode.sourceLevels,
          VLevel.params_map_inst_params'],
    VExpr.liftN_forallN, VExpr.liftN_appN]
  simp only [List.length_map, VExpr.liftTelN_length, Nat.zero_add]
  rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    show m - r₀.fieldIndex + (k + 1 + (r₀.fieldIndex + r₀.binders.length)) =
      m + k + r₀.binders.length + 1 from by omega]
  simp only [List.map_map, RecArg.ruleBinders]
  apply congrArg (VExpr.forallN _)
  apply congrArg (VExpr.appN (.const T (mode.sourceLevels U)))
  apply congrArg (VExpr.bvarRevRange (m+k+r₀.binders.length+1) np ++ ·)
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply]

theorem RecArg.minorBinders_shift (r : RecArg) (m p : Nat) :
    r.minorBinders m p =
      VExpr.liftTelN p (r.minorBinders m 0) 0 := by
  simp only [RecArg.minorBinders, Nat.add_zero]
  rw [VExpr.liftTelN_liftTelN]

/-- The `p` parameter of a minor IH is exactly weakening over the `p`
previous IH binders. -/
theorem RecArg.minorIH_shift (r : RecArg) (m p : Nat)
    (hj : r.fieldIndex < m) :
    r.minorIH m p = (r.minorIH m 0).liftN p := by
  simp only [RecArg.minorIH, VExpr.liftN_forallN]
  rw [← r.minorBinders_shift m p]
  rw [show (r.minorBinders m 0).length = r.binders.length by
    simp [RecArg.minorBinders, VExpr.liftTelN_length], Nat.zero_add]
  apply congrArg (VExpr.forallN _)
  rw [VExpr.liftN_appN, List.map_append, List.map_map]
  show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
  congr 1
  · rw [show (VExpr.bvar (m + 0 + r.binders.length)).liftN
        p r.binders.length = .bvar (m+p+r.binders.length) from by
      simp only [VExpr.liftN]
      rw [liftVar_le (by omega)]
      congr 1
      omega]
  · congr 1
    · apply List.map_congr_left
      intro e _
      simp only [Function.comp_apply, Nat.add_zero]
      rw [VExpr.liftN'_liftN_hi]
    · congr 1
      simp only [Nat.add_zero, VExpr.liftN_appN]
      rw [show (VExpr.bvar (m - 1 - r.fieldIndex + r.binders.length)).liftN
          p r.binders.length =
          .bvar (m - 1 - r.fieldIndex + p + r.binders.length) from by
        simp only [VExpr.liftN]
        rw [liftVar_le (by omega)]
        congr 1
        omega,
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]

/-- Lifting a base minor-IH through the constructor-minor stack produces the
normal form expected of the corresponding recursive call in an iota rule. -/
theorem RecArg.minorIH_zero_lift_ruleIH (r : RecArg) (m k : Nat)
    (hj : r.fieldIndex < m) :
    (r.minorIH m 0).liftN k m = r.ruleIH m k := by
  simp only [RecArg.minorIH, RecArg.ruleIH, VExpr.liftN_forallN,
    VExpr.liftTelN_length, RecArg.minorBinders, RecArg.ruleBinders, Nat.add_zero]
  congr 1
  · rw [show m = r.fieldIndex + (m-r.fieldIndex) from by omega]
    rw [show r.fieldIndex + (m-r.fieldIndex) - r.fieldIndex =
      m-r.fieldIndex from by omega]
    rw [VExpr.liftTelN_liftN_mid r.binders k (m-r.fieldIndex) (Nat.zero_le _)]
  · congr 1
    rw [VExpr.liftN_appN, List.map_append, List.map_map]
    show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
    congr 1
    · simp only [VExpr.liftN]
      rw [liftVar_le (Nat.le_refl _)]
      congr 1
      omega
    · congr 1
      · apply List.map_congr_left
        intro e _
        simp only [Function.comp_apply]
        rw [show m + r.binders.length =
            (r.fieldIndex + r.binders.length) + (m-r.fieldIndex) from by omega,
          VExpr.liftN_liftN_mid e k (m-r.fieldIndex) (by omega)]
      · congr 1
        simp only [VExpr.liftN_appN]
        rw [show (VExpr.bvar (m - 1 - r.fieldIndex + r.binders.length)).liftN
            k (m + r.binders.length) =
            .bvar (m - 1 - r.fieldIndex + r.binders.length) from by
              simp only [VExpr.liftN]
              rw [liftVar_lt (by omega)],
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]

/-- General normalization for a minor-IH already shifted past `p` earlier IH
binders. In rule context it is the base `ruleIH`, weakened by the same `p`. -/
theorem RecArg.minorIH_lift_ruleIH (r : RecArg) (m k p : Nat)
    (hj : r.fieldIndex < m) :
    (r.minorIH m p).liftN k (m+p) = (r.ruleIH m k).liftN p := by
  rw [r.minorIH_shift m p hj]
  rw [← VExpr.liftN_liftN_comm (r.minorIH m 0) p k 0 m (Nat.zero_le _)]
  rw [r.minorIH_zero_lift_ruleIH m k hj]

theorem ruleIHs_length (m k : Nat) : ∀ (rs : List RecArg) (p : Nat),
    (ruleIHs m k rs p).length = rs.length
  | [], _ => rfl
  | _ :: rs, p => by simp [ruleIHs, ruleIHs_length m k rs (p+1)]

/-- Lifting the generalized minor-IH telescope into a rule context normalizes
each entry to `ruleIHs`; this is the list form of
`RecArg.minorIH_lift_ruleIH`. -/
theorem ihsFromRecArgs_liftN (m k : Nat) : ∀ (rs : List RecArg),
    (∀ r ∈ rs, r.fieldIndex < m) → ∀ (p : Nat) (X : VExpr),
    (VExpr.forallN (ihsFromRecArgs m rs p) X).liftN k (m+p) =
      VExpr.forallN (ruleIHs m k rs p) (X.liftN k (m+p+rs.length))
  | [], _, _, _ => rfl
  | r :: rs, hm, p, X => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · exact r.minorIH_lift_ruleIH m k p (hm r (.head _))
    · rw [show m+p+1 = m+(p+1) from by omega,
        ihsFromRecArgs_liftN m k rs (fun q hq => hm q (.tail _ hq)) (p+1) X,
        show m+(p+1)+rs.length = m+p+((r :: rs).length) from by simp; omega]

theorem ihsFromRecArgs_liftN' (m k : Nat) (rs : List RecArg)
    (hm : ∀ r ∈ rs, r.fieldIndex < m) (p : Nat) (X : VExpr)
    {cut : Nat} (hcut : cut = m+p) :
    (VExpr.forallN (ihsFromRecArgs m rs p) X).liftN k cut =
      VExpr.forallN (ruleIHs m k rs p) (X.liftN k (m+p+rs.length)) := by
  rw [hcut]
  exact ihsFromRecArgs_liftN m k rs hm p X

/-- Weakening a normalized functional-IH telescope by one binder is the same
as incrementing its starting depth. -/
theorem ruleIHs_liftN1 (m k : Nat) : ∀ (rs : List RecArg) (p c : Nat), c ≤ p →
    ∀ (X : VExpr),
    VExpr.forallN (ruleIHs m k rs (p+1)) (X.liftN 1 (c+rs.length)) =
      (VExpr.forallN (ruleIHs m k rs p) X).liftN 1 c
  | [], p, c, _, X => by simp [ruleIHs, VExpr.forallN]
  | r :: rs, p, c, hc, X => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN'_liftN' (Nat.zero_le _) hc]
    · rw [show c+(r :: rs).length = (c+1)+rs.length from by simp; omega]
      exact ruleIHs_liftN1 m k rs (p+1) (c+1) (by omega) X

/-- The key normalization: lifting a parameter spine past `off` binders. -/
theorem recApp'_liftN {U : Nat} {T : Name} {np : Nat} {n k off : Nat} (h : k ≤ off) :
    (recApp' U T np off).liftN n k = recApp' U T np (n + off) := by
  simp only [recApp', VExpr.liftN_appN]
  rw [bvarRevRange_liftN_ge _ _ _ _ h]
  rfl

theorem recApp_liftN {U : Nat} {T : Name} {np : Nat} {n k off : Nat} (h : k ≤ off) :
    (recApp U T np off).liftN n k = recApp U T np (n + off) := by
  simp only [recApp, VExpr.liftN_appN]
  rw [bvarRevRange_liftN_ge _ _ _ _ h]
  rfl

theorem recApp_instL {U : Nat} {T : Name} {np off : Nat} :
    (recApp U T np off).instL (VLevel.params' U 1) = recApp' U T np off := by
  simp only [recApp, recApp', VExpr.instL_appN]
  rw [bvarRevRange_instL]
  simp [VExpr.instL, VLevel.params_map_inst_params', ElimMode.sourceLevels,
    ElimMode.offset]

theorem recApp'_congr {U : Nat} {T : Name} {np : Nat} {off off' : Nat}
    (h : off = off') : recApp' U T np off = recApp' U T np off' := h ▸ rfl

theorem _root_.Ix.Theory.Named.VExpr.bvarRevRange_congr {off off' : Nat} (m : Nat)
    (h : off = off') : VExpr.bvarRevRange off m = VExpr.bvarRevRange off' m := h ▸ rfl

theorem _root_.Ix.Theory.Named.VExpr.bvarRevRange_congr' {m m' : Nat} (off : Nat)
    (h : m = m') : VExpr.bvarRevRange off m = VExpr.bvarRevRange off m' := h ▸ rfl

theorem bvarRevRange_closedN : ∀ (m off k : Nat), off + m ≤ k →
    ∀ e ∈ VExpr.bvarRevRange off m, e.ClosedN k
  | 0, _, _, _, _, h => nomatch h
  | m+1, off, k, hk, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact show off + m < k by omega
    · exact bvarRevRange_closedN m off k (by omega) e h

theorem bvarRevRange_levelWF {Uv : Nat} : ∀ (m off : Nat),
    ∀ e ∈ VExpr.bvarRevRange off m, e.LevelWF Uv
  | 0, _, _, h => nomatch h
  | m+1, off, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · trivial
    · exact bvarRevRange_levelWF m off e h

theorem ihsFrom_levelWF {Uv : Nat} {m : Nat} : ∀ (rs : List (Nat × List VExpr)) (p : Nat),
    (∀ q ∈ rs, ∀ e ∈ q.2, e.LevelWF Uv) → ∀ e ∈ ihsFrom m rs p, e.LevelWF Uv
  | (j, idxs) :: rs, p, hidx, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · refine VExpr.LevelWF.appN (f := .bvar (m+p)) trivial fun e he => ?_
      rcases List.mem_append.1 he with he | he
      · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
        exact ((hidx _ (List.Mem.head _) e₀ he₀).liftN).liftN
      · rcases List.mem_cons.1 he with rfl | he
        · trivial
        · cases he
    · exact ihsFrom_levelWF rs (p+1) (fun q hq => hidx q (.tail _ hq)) e h

/-- Closedness of a telescope of closed binders over an open body. -/
theorem _root_.Ix.Theory.Named.VExpr.ClosedN.forallN_closed_binders :
    ∀ {As : List VExpr}, (∀ A ∈ As, A.ClosedN 0) →
    ∀ {X : VExpr} {k : Nat}, X.ClosedN (k + As.length) →
    (VExpr.forallN As X).ClosedN k
  | [], _, _, _, hX => hX
  | _ :: As, hAs, X, k, hX =>
    ⟨(hAs _ (.head _)).mono (Nat.zero_le _),
      VExpr.ClosedN.forallN_closed_binders (fun A h => hAs _ (.tail _ h))
        (by rw [show k+1+As.length = k+(As.length+1) from by omega]; exact hX)⟩

end VInductDecl

namespace VExpr

theorem forallN_telN_dropN : ∀ (n : Nat) (e : VExpr),
    forallN (telN n e) (dropN n e) = e
  | 0, _ => rfl
  | n+1, .forallE A rest => congrArg (VExpr.forallE A) (forallN_telN_dropN n rest)
  | _+1, .bvar _ | _+1, .sort _ | _+1, .const _ _ | _+1, .app _ _ | _+1, .lam _ _ => rfl

theorem resultOf_forallN : ∀ (As : List VExpr) (B : VExpr),
    resultOf (forallN As B) = resultOf B
  | [], _ => rfl
  | _ :: As, B => resultOf_forallN As B

theorem resultOf_appN_app (f a : VExpr) :
    ∀ es, resultOf ((f.app a).appN es) = (f.app a).appN es
  | [] => rfl
  | b :: bs => resultOf_appN_app (f.app a) b bs

theorem resultOf_appN_const (T : Name) (ls : List VLevel) :
    ∀ es, resultOf ((VExpr.const T ls).appN es) =
      (VExpr.const T ls).appN es
  | [] => rfl
  | a :: as => resultOf_appN_app (VExpr.const T ls) a as

end VExpr

namespace VEnv

theorem OnTel.mono {env env' : VEnv} {U : Nat} (henv : env ≤ env') :
    ∀ {As Γ}, OnTel env U Γ As → OnTel env' U Γ As
  | [], _, _ => trivial
  | _ :: _, _, ⟨hA, hT⟩ => ⟨hA.mono henv, OnTel.mono henv hT⟩

/-- A well-formed telescope is pointwise definitionally equal to itself. -/
theorem OnTel.telDefEq_refl {env : VEnv} {U : Nat} :
    ∀ {Γ As}, OnTel env U Γ As → TelDefEq env U Γ As As
  | _, [], _ => trivial
  | _, _ :: _, ⟨⟨u, hA⟩, hT⟩ =>
    ⟨⟨u, hA⟩, OnTel.telDefEq_refl hT⟩

/-- A structural telescope equality has equal arity. -/
theorem TelDefEq.length_eq {env : VEnv} {U : Nat} :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' → As.length = As'.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, ⟨_, hT⟩ =>
    congrArg Nat.succ (TelDefEq.length_eq hT)

/-- The raw side of a structural telescope equality is a well-formed
telescope. -/
theorem TelDefEq.raw_onTel {env : VEnv} {U : Nat} :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' → OnTel env U Γ As
  | _, [], [], _ => trivial
  | _, _ :: _, _ :: _, ⟨⟨_, hA⟩, hT⟩ =>
    ⟨⟨_, hA.hasType.1⟩, TelDefEq.raw_onTel hT⟩

/-- Extend a structural telescope equality by an identical, well-formed
suffix. The suffix is checked in the completed left-hand context, exactly as
required by `TelDefEq`'s raw-context convention. -/
theorem TelDefEq.append_refl {env : VEnv} {U : Nat} :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' →
      ∀ {Bs}, OnTel env U (As.reverse ++ Γ) Bs →
        TelDefEq env U Γ (As ++ Bs) (As' ++ Bs)
  | _, [], [], _, _, hBs => by
      simpa using hBs.telDefEq_refl
  | Γ, A :: As, A' :: As', ⟨hA, hT⟩, Bs, hBs => by
      refine ⟨hA, ?_⟩
      apply TelDefEq.append_refl hT
      simpa [List.reverse_cons, List.append_assoc] using hBs

/-- Structural telescope equality is monotone in the environment. -/
theorem TelDefEq.mono {env env' : VEnv} {U : Nat} (henv : env ≤ env') :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' → TelDefEq env' U Γ As As'
  | _, [], [], _ => trivial
  | _, _ :: _, _ :: _, ⟨⟨u, hA⟩, hT⟩ =>
    ⟨⟨u, hA.mono henv⟩, TelDefEq.mono henv hT⟩

/-- Instantiate every universe in a structural telescope equality. -/
theorem TelDefEq.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' →
      TelDefEq env U' (Γ.map (VExpr.instL ls))
        (As.map (VExpr.instL ls)) (As'.map (VExpr.instL ls))
  | _, [], [], _ => trivial
  | _, _ :: As, _ :: As', ⟨⟨u, hA⟩, hT⟩ => by
    refine ⟨⟨u.inst ls, hA.instL hls⟩, ?_⟩
    simpa using TelDefEq.instL hls hT

/-- Extend an existing definitionally equal context by a structurally equal
raw/view telescope. -/
theorem TelDefEq.extendCtx {env : VEnv} {U : Nat} {Γ₀ : List VExpr} :
    ∀ {Γ Γ' As As'}, IsDefEqCtx env U Γ₀ Γ Γ' →
      TelDefEq env U Γ As As' →
      IsDefEqCtx env U Γ₀ (As.reverse ++ Γ) (As'.reverse ++ Γ')
  | Γ, Γ', [], [], hΓ, _ => by simpa using hΓ
  | Γ, Γ', _ :: As, _ :: As', hΓ, ⟨⟨_, hA⟩, hT⟩ => by
    simpa [List.reverse_cons, List.append_assoc] using
      TelDefEq.extendCtx (.succ hΓ hA) hT

/-- The completed raw and view contexts of a structural telescope equality
are definitionally equal over their common prefix. -/
theorem TelDefEq.ctx {env : VEnv} {U : Nat} {Γ As As' : List VExpr}
    (h : TelDefEq env U Γ As As') :
    IsDefEqCtx env U Γ (As.reverse ++ Γ) (As'.reverse ++ Γ) :=
  h.extendCtx .zero

/-- Any aligned prefix remains a structural telescope equality. -/
theorem TelDefEq.take {env : VEnv} {U : Nat} :
    ∀ (n : Nat) {Γ As As'}, TelDefEq env U Γ As As' →
      TelDefEq env U Γ (As.take n) (As'.take n)
  | 0, _, _, _, _ => trivial
  | _ + 1, _, [], [], _ => trivial
  | n + 1, _, _ :: _, _ :: _, ⟨hA, hT⟩ =>
    ⟨hA, TelDefEq.take n hT⟩

/-- Drop an aligned prefix, retaining the exact raw context accumulated by
the removed binders. -/
theorem TelDefEq.drop {env : VEnv} {U : Nat} :
    ∀ (n : Nat) {Γ As As'}, TelDefEq env U Γ As As' →
      TelDefEq env U ((As.take n).reverse ++ Γ)
        (As.drop n) (As'.drop n)
  | 0, _, _, _, h => by simpa using h
  | _ + 1, _, [], [], _ => trivial
  | n + 1, Γ, A :: As, _ :: As', ⟨_, hT⟩ => by
    have h := TelDefEq.drop n hT
    simpa [List.take_succ_cons, List.drop_succ_cons,
      List.reverse_cons, List.append_assoc] using h

/-- Recover the pointwise equality at one aligned binder position together
with its exact preceding raw context. -/
theorem TelDefEq.getElem? {env : VEnv} {U : Nat} :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' →
      ∀ {n A A'}, As[n]? = some A → As'[n]? = some A' →
        ∃ u, env.IsDefEq U ((As.take n).reverse ++ Γ) A A' (.sort u)
  | _, [], [], _, n, _, _, hA, _ => by simp at hA
  | Γ, _ :: As, _ :: As', ⟨hhead, htail⟩, 0, A, A', hA, hA' => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hA'
    subst A
    subst A'
    simpa using hhead
  | Γ, A₀ :: As, A₀' :: As', ⟨_, htail⟩, n + 1, A, A', hA, hA' => by
    simp only [List.getElem?_cons_succ] at hA hA'
    have h := TelDefEq.getElem? htail hA hA'
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using h

/-- Weakening preserves structural telescope equality and shifts both
surfaces at their binder-relative cutoffs. -/
theorem TelDefEq.weakN {env : VEnv} {U n : Nat} (ord : env.Ordered)
    {Γ Γ' : List VExpr} {k : Nat} (W : Ctx.LiftN n k Γ Γ') :
    ∀ {As As'}, TelDefEq env U Γ As As' →
      TelDefEq env U Γ'
        (VExpr.liftTelN n As k) (VExpr.liftTelN n As' k)
  | [], [], _ => trivial
  | _ :: As, _ :: As', ⟨⟨u, hA⟩, hT⟩ => by
    refine ⟨⟨u, hA.weakN ord W⟩, ?_⟩
    simpa [VExpr.liftTelN] using TelDefEq.weakN ord W.succ hT

/-- Substitute one typed term through a structural telescope equality. -/
theorem TelDefEq.instN {env : VEnv} {U : Nat} (ord : env.Ordered)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr}
    (h₀ : env.HasType U Γ₀ e₀ A₀) {k : Nat} {Γ₁ Γ : List VExpr}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) :
    ∀ {As As'}, TelDefEq env U Γ₁ As As' →
      TelDefEq env U Γ
        (VExpr.instTelN e₀ As k) (VExpr.instTelN e₀ As' k)
  | [], [], _ => trivial
  | _ :: As, _ :: As', ⟨⟨u, hA⟩, hT⟩ => by
    refine ⟨⟨u, by simpa using hA.instN ord h₀ W⟩, ?_⟩
    simpa [VExpr.instTelN] using
      TelDefEq.instN ord h₀ W.succ hT

/-- Pointwise telescope equality extends to the corresponding iterated Pi
types once their terminal bodies are definitionally equal in the completed
raw context. This is the construction-side counterpart of `spine_sort`; it
does not require Pi injectivity. -/
theorem TelDefEq.forallN_defeq {env : VEnv} {U : Nat} :
    ∀ {Γ As As' C C' u},
      TelDefEq env U Γ As As' →
      env.IsDefEq U (As.reverse ++ Γ) C C' (.sort u) →
      ∃ v, env.IsDefEq U Γ
        (VExpr.forallN As C) (VExpr.forallN As' C') (.sort v)
  | _, [], [], _, _, u, _, hC => ⟨u, hC⟩
  | Γ, A :: As, A' :: As', C, C', u,
      ⟨⟨uA, hA⟩, hT⟩, hC => by
    have hC' : env.IsDefEq U (As.reverse ++ A :: Γ)
        C C' (.sort u) := by
      simpa [List.reverse_cons, List.append_assoc] using hC
    obtain ⟨v, hbody⟩ :=
      TelDefEq.forallN_defeq hT hC'
    exact ⟨.imax uA v, .forallEDF hA hbody⟩

/-- A fully applied spine accepted by the view telescope is also accepted by
the raw telescope. This is the substitution-aware consumer of `TelDefEq`;
it avoids any appeal to whole-Pi injectivity. -/
theorem TelDefEq.spine_sort {env : VEnv} {U : Nat} (ord : env.Ordered) :
    ∀ {Γ As As' es l}, TelDefEq env U Γ As As' →
      env.SpineWF U Γ (VExpr.forallN As' (.sort l)) es (.sort l) →
      es.length = As.length →
      env.SpineWF U Γ (VExpr.forallN As (.sort l)) es (.sort l)
  | _, [], [], [], _, _, hsp, _ => by simpa using hsp
  | _, [], [], _ :: _, _, _, _, hlen => by simp at hlen
  | Γ, A :: As, A' :: As', e :: es, l, ⟨⟨_, hA⟩, hT⟩,
      .cons he hrest, hlen => by
    have heRaw : env.HasType U Γ e A := hA.defeq' he
    have hTinst := TelDefEq.instN ord heRaw (.zero) hT
    have hrest' : env.SpineWF U Γ
        (VExpr.forallN (VExpr.instTelN e As' 0) (.sort l))
        es (.sort l) := by
      simpa [VExpr.instN_forallN] using hrest
    have hlen' : es.length = As.length := by simpa using hlen
    have hlenInst :
        es.length = (VExpr.instTelN e As 0).length := by
      rw [VExpr.instTelN_length]
      exact hlen'
    have hout := TelDefEq.spine_sort ord hTinst hrest' hlenInst
    refine .cons heRaw ?_
    simpa [VExpr.instN_forallN] using hout

/-- Extend a definitionally equal context by the same well-formed telescope
on both sides. -/
theorem OnTel.extendDefEqCtx {env : VEnv} {U : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    (hΓ : IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    ∀ {As}, OnTel env U Γ₁ As →
      IsDefEqCtx env U Γ₀ (As.reverse ++ Γ₁) (As.reverse ++ Γ₂)
  | [], _ => by simpa using hΓ
  | _ :: As, ⟨⟨_, hA⟩, hT⟩ => by
    simpa [List.reverse_cons, List.append_assoc] using
      OnTel.extendDefEqCtx (.succ hΓ hA) hT

/-- Transport a telescope across definitionally equal base contexts. -/
theorem OnTel.defeqDFC {env : VEnv} {U : Nat} (ord : env.Ordered)
    {Γ₀ Γ₁ Γ₂ : List VExpr} (hΓ : IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    ∀ {As}, OnTel env U Γ₁ As → OnTel env U Γ₂ As
  | [], _ => trivial
  | _ :: As, ⟨hA, hT⟩ => by
    obtain ⟨u, hAt⟩ := hA
    exact ⟨⟨u, hAt.defeqDFC ord hΓ⟩,
      OnTel.defeqDFC ord (.succ hΓ hAt) hT⟩

/-- The view side of a structural telescope equality is itself well formed.
Each tail is transported from the accumulated raw context to the accumulated
view context before recursion continues. -/
theorem TelDefEq.view_onTel {env : VEnv} {U : Nat} (ord : env.Ordered) :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' → OnTel env U Γ As'
  | _, [], [], _ => trivial
  | _, _ :: _, _ :: _, ⟨⟨u, hA⟩, hT⟩ =>
      ⟨⟨u, hA.hasType.2⟩,
        (TelDefEq.view_onTel ord hT).defeqDFC ord
          (.succ .zero hA)⟩

/-- Transport a structural telescope equality across definitionally equal
base contexts while retaining its raw/view surfaces. -/
theorem TelDefEq.defeqDFC {env : VEnv} {U : Nat} (ord : env.Ordered)
    {Γ₀ Γ₁ Γ₂ : List VExpr} (hΓ : IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    ∀ {As As'}, TelDefEq env U Γ₁ As As' → TelDefEq env U Γ₂ As As'
  | [], [], _ => trivial
  | A :: As, _ :: As', ⟨⟨u, hA⟩, hT⟩ => by
      have hA' := hA.defeqDFC ord hΓ
      refine ⟨⟨u, hA'⟩, ?_⟩
      exact TelDefEq.defeqDFC ord
        (.succ hΓ hA.hasType.1) hT

/-- Select Lean's kernel-observable parameter surface without losing the
structural equality to the analyzer-owned parameter telescope. Ordinary
parameters keep the raw domain; annotated parameters use the checked domain.
-/
theorem TelDefEq.generationParams {env : VEnv} {U : Nat}
    (ord : env.Ordered) :
    ∀ {Γ raw view}, TelDefEq env U Γ raw view →
      TelDefEq env U Γ (VInductDecl.generationParams raw view) view
  | _, [], [], _ => trivial
  | Γ, raw :: raws, view :: views, ⟨⟨u, head⟩, tail⟩ => by
    simp only [VInductDecl.generationParams,
      VInductDecl.generationParam]
    split
    · refine ⟨⟨u, head.hasType.2⟩, ?_⟩
      exact (TelDefEq.generationParams ord tail).defeqDFC ord
        (.succ (.zero (Γ₀ := Γ)) head)
    · exact ⟨⟨u, head⟩, TelDefEq.generationParams ord tail⟩

#guard_named_axioms Ix.Theory.Named.VEnv.TelDefEq.generationParams [propext, Quot.sound]

/-- Transport application-spine typing across definitionally equal
contexts. -/
theorem SpineWF.defeqDFC {env : VEnv} {U : Nat} (ord : env.Ordered)
    {Γ₀ Γ₁ Γ₂ : List VExpr} (hΓ : IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    ∀ {A es B}, SpineWF env U Γ₁ A es B → SpineWF env U Γ₂ A es B
  | _, [], _, .nil => .nil
  | _, _ :: _, _, .cons he hT =>
    .cons (he.defeqDFC ord hΓ) (SpineWF.defeqDFC ord hΓ hT)

#guard_named_axioms Ix.Theory.Named.VEnv.TelDefEq.raw_onTel [propext]

#guard_named_axioms Ix.Theory.Named.VEnv.TelDefEq.instL [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.TelDefEq.ctx [propext]

end VEnv

namespace VInductDecl
open VEnv

/-- The exact raw family telescope accepted for generation is well formed in
the pre-environment. -/
theorem GenerationChecked.WF.rawFamily_onTel {source : VInductDecl}
    {gen : GenerationChecked source} {env : VEnv} (h : gen.WF env) :
    env.OnTel source.uvars []
      (gen.block.rawParams ++ gen.block.rawIndices) :=
  h.familyTel.raw_onTel

/-- The granular family telescope/result contract proves that the stored raw
family constant can be inserted without appealing to whole-`forall`
injectivity. -/
theorem GenerationChecked.WF.rawFamily_isType {source : VInductDecl}
    {gen : GenerationChecked source} {env : VEnv} (h : gen.WF env) :
    env.IsType source.uvars [] gen.block.sourceType.type := by
  rw [← VExpr.forallN_telN_dropN source.nparams gen.block.sourceType.type,
    ← forallN_ctorFields_resultOf
      (VExpr.dropN source.nparams gen.block.sourceType.type),
    ← VExpr.forallN_append]
  have hresult₀ : env.IsType source.uvars
      (gen.block.rawParams ++ gen.block.rawIndices).reverse
      gen.block.rawResult :=
    ⟨_, h.familyResult.hasType.1⟩
  have hresult : env.IsType source.uvars
      ((gen.block.rawParams ++ gen.block.rawIndices).reverse ++ [])
      gen.block.rawResult := by
    simpa using hresult₀
  have hout := IsType.forallN h.rawFamily_onTel hresult
  simpa [NormalizedChecked.rawParams, NormalizedChecked.rawIndices,
    NormalizedChecked.rawResult] using hout

/-- The exact raw telescope stored in a paired constructor is well formed in
the post-family environment. -/
theorem NormalizedCtor.WF.rawDeclared_onTel {source : VInductDecl}
    {block : NormalizedChecked source} {ctor : NormalizedCtor} {env : VEnv}
    (h : ctor.WF block env) :
    env.OnTel source.uvars [] (ctor.declaredBinders source.nparams) :=
  h.declaredTel.raw_onTel

/-- The granular constructor telescope/result contract proves that the exact
stored raw constructor can be inserted. -/
theorem NormalizedCtor.WF.rawDeclared_isType {source : VInductDecl}
    {block : NormalizedChecked source} {ctor : NormalizedCtor} {env : VEnv}
    (h : ctor.WF block env) :
    env.IsType source.uvars [] ctor.raw.type := by
  rw [← VExpr.forallN_telN_dropN source.nparams ctor.raw.type,
    ← forallN_ctorFields_resultOf (VExpr.dropN source.nparams ctor.raw.type),
    ← VExpr.forallN_append]
  have hresult₀ : env.IsType source.uvars
      (ctor.declaredBinders source.nparams).reverse
      (ctor.rawResult source.nparams) :=
    ⟨_, h.declaredResult.hasType.1⟩
  have hresult : env.IsType source.uvars
      ((ctor.declaredBinders source.nparams).reverse ++ [])
      (ctor.rawResult source.nparams) := by
    simpa using hresult₀
  have hout := IsType.forallN h.rawDeclared_onTel hresult
  simpa [NormalizedCtor.declaredBinders, NormalizedCtor.rawFields,
    NormalizedCtor.rawResult] using hout

/-- The raw family/field telescope actually emitted in mixed artifacts is
well formed independently of the constructor's stored parameter surface. -/
theorem NormalizedCtor.WF.rawEmitted_onTel {source : VInductDecl}
    {block : NormalizedChecked source} {ctor : NormalizedCtor} {env : VEnv}
    (h : ctor.WF block env) :
    env.OnTel source.uvars [] (ctor.emittedBinders block) :=
  h.emittedTel.raw_onTel

/-- A granular constructor certificate is monotone after its staged family
insertion. -/
theorem NormalizedCtor.WF.mono {source : VInductDecl}
    {block : NormalizedChecked source} {ctor : NormalizedCtor}
    {env env' : VEnv} (henv : env ≤ env') (h : ctor.WF block env) :
    ctor.WF block env' where
  declaredTel := h.declaredTel.mono henv
  declaredResult := h.declaredResult.mono henv
  emittedTel := h.emittedTel.mono henv
  emittedResult := h.emittedResult.mono henv

/-- Retrieve the insertion-ready proof for any paired raw constructor in the
precise post-family environment named by the block certificate. -/
theorem GenerationChecked.WF.rawCtor_isType {source : VInductDecl}
    {gen : GenerationChecked source} {env envT : VEnv} (h : gen.WF env)
    (hadd : env.addConst gen.block.sourceType.name
      gen.block.sourceType.toVConstant = some envT)
    {ctor : NormalizedCtor} (hctor : ctor ∈ gen.block.ctorPairs) :
    envT.IsType source.uvars [] ctor.raw.type :=
  (h.ctors envT hadd ctor hctor).rawDeclared_isType

/-! Mutual declaration-stage consequences. -/

theorem NormalizedFamily.WF.rawFamily_onTel {source : VInductDecl}
    {gen : BlockGenerationChecked source} {family : NormalizedFamily}
    {env : VEnv} (h : family.WF gen env) :
    env.OnTel source.uvars []
      (family.rawParams source.nparams ++
        family.rawIndices source.nparams) :=
  h.familyTel.raw_onTel

theorem NormalizedFamily.WF.rawFamily_isType {source : VInductDecl}
    {gen : BlockGenerationChecked source} {family : NormalizedFamily}
    {env : VEnv} (h : family.WF gen env) :
    env.IsType source.uvars [] family.raw.type := by
  rw [← VExpr.forallN_telN_dropN source.nparams family.raw.type,
    ← forallN_ctorFields_resultOf
      (VExpr.dropN source.nparams family.raw.type),
    ← VExpr.forallN_append]
  have hresult₀ : env.IsType source.uvars
      (family.rawParams source.nparams ++
        family.rawIndices source.nparams).reverse
      (family.rawResult source.nparams) :=
    ⟨_, h.familyResult.hasType.1⟩
  have hresult : env.IsType source.uvars
      ((family.rawParams source.nparams ++
        family.rawIndices source.nparams).reverse ++ [])
      (family.rawResult source.nparams) := by
    simpa using hresult₀
  have hout := IsType.forallN h.rawFamily_onTel hresult
  simpa [NormalizedFamily.rawParams, NormalizedFamily.rawIndices,
    NormalizedFamily.rawResult] using hout

theorem NormalizedFamily.WF.mono {source : VInductDecl}
    {gen : BlockGenerationChecked source} {family : NormalizedFamily}
    {env env' : VEnv} (henv : env ≤ env') (h : family.WF gen env) :
    family.WF gen env' where
  familyTel := h.familyTel.mono henv
  familyResult := h.familyResult.mono henv

theorem NormalizedBlockCtor.WF.rawDeclared_onTel
    {source : VInductDecl} {gen : BlockGenerationChecked source}
    {constructor : NormalizedBlockCtor} {env : VEnv}
    (h : NormalizedBlockCtor.WF gen constructor env) :
    env.OnTel source.uvars []
      (NormalizedBlockCtor.declaredBinders
        (source := source) constructor) :=
  h.declaredTel.raw_onTel

theorem NormalizedBlockCtor.WF.rawDeclared_isType
    {source : VInductDecl} {gen : BlockGenerationChecked source}
    {constructor : NormalizedBlockCtor} {env : VEnv}
    (h : NormalizedBlockCtor.WF gen constructor env) :
    env.IsType source.uvars [] constructor.ctor.raw.type := by
  rw [← VExpr.forallN_telN_dropN source.nparams
      constructor.ctor.raw.type,
    ← forallN_ctorFields_resultOf
      (VExpr.dropN source.nparams constructor.ctor.raw.type),
    ← VExpr.forallN_append]
  have hresult₀ : env.IsType source.uvars
      (NormalizedBlockCtor.declaredBinders
        (source := source) constructor).reverse
      (NormalizedBlockCtor.rawResult
        (source := source) constructor) :=
    ⟨_, h.declaredResult.hasType.1⟩
  have hresult : env.IsType source.uvars
      ((NormalizedBlockCtor.declaredBinders
        (source := source) constructor).reverse ++ [])
      (NormalizedBlockCtor.rawResult
        (source := source) constructor) := by
    simpa using hresult₀
  have hout := IsType.forallN h.rawDeclared_onTel hresult
  simpa [NormalizedBlockCtor.declaredBinders,
    NormalizedBlockCtor.rawResult, NormalizedCtor.declaredBinders,
    NormalizedCtor.rawFields, NormalizedCtor.rawResult] using hout

theorem NormalizedBlockCtor.WF.rawEmitted_onTel
    {source : VInductDecl} {gen : BlockGenerationChecked source}
    {constructor : NormalizedBlockCtor} {env : VEnv}
    (h : NormalizedBlockCtor.WF gen constructor env) :
    env.OnTel source.uvars []
      (NormalizedBlockCtor.emittedBinders gen constructor) :=
  h.emittedTel.raw_onTel

theorem NormalizedBlockCtor.WF.mono
    {source : VInductDecl} {gen : BlockGenerationChecked source}
    {constructor : NormalizedBlockCtor} {env env' : VEnv}
    (henv : env ≤ env') (h : NormalizedBlockCtor.WF gen constructor env) :
    NormalizedBlockCtor.WF gen constructor env' where
  declaredTel := h.declaredTel.mono henv
  declaredResult := h.declaredResult.mono henv
  emittedTel := h.emittedTel.mono henv
  emittedResult := h.emittedResult.mono henv
  owner := h.owner
  recursive := fun recursive hrecursive => by
    obtain ⟨family, hfamily, hordinal, hfield, hwf⟩ :=
      h.recursive recursive hrecursive
    exact ⟨family, hfamily, hordinal, hfield,
      ⟨hwf.1.mono henv, hwf.2.mono henv⟩⟩
  resultSpine := h.resultSpine.mono henv

theorem BlockGenerationChecked.WF.rawFamily_isType
    {source : VInductDecl} {gen : BlockGenerationChecked source}
    {env blockEnv : VEnv} (h : gen.WF env blockEnv)
    {family : NormalizedFamily} (hfamily : family ∈ gen.families) :
    env.IsType source.uvars [] family.raw.type :=
  (h.families family hfamily).rawFamily_isType

theorem BlockGenerationChecked.WF.rawCtor_isType
    {source : VInductDecl} {gen : BlockGenerationChecked source}
    {env blockEnv : VEnv} (h : gen.WF env blockEnv)
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) :
    blockEnv.IsType source.uvars [] constructor.ctor.raw.type :=
  (h.constructors constructor hconstructor).rawDeclared_isType

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationChecked.WF.rawFamily_isType [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationChecked.WF.rawCtor_isType [propext, Quot.sound]

theorem RecArg.WF.mono {env env' : VEnv} {U : Nat} {l : VLevel}
    {Is Γ : List VExpr} {r : RecArg} (henv : env ≤ env')
    (h : r.WF U env l Is Γ) : r.WF U env' l Is Γ :=
  ⟨h.1.mono henv, h.2.mono henv⟩

/-- The checked recursive/non-recursive field interpretation is monotone in
the environment. -/
theorem checkedBlockFieldsWF_mono {env env' : VEnv} {U : Nat}
    {resultLevel : VLevel} {familyIndices : List (List VExpr)}
    (henv : env ≤ env') : ∀ {fields classifications Γ j},
    checkedBlockFieldsWF env U resultLevel familyIndices
      fields classifications Γ j →
    checkedBlockFieldsWF env' U resultLevel familyIndices
      fields classifications Γ j
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, _, h => by
    simp [checkedBlockFieldsWF] at h
  | _ :: _, [], _, _, h => by
    simp [checkedBlockFieldsWF] at h
  | B :: Bs, none :: classifications, Γ, j,
      ⟨⟨u, hB, hlevel⟩, htail⟩ =>
    ⟨⟨u, hB.mono henv, hlevel⟩,
      checkedBlockFieldsWF_mono henv htail⟩
  | B :: Bs, some recursive :: classifications, Γ, j, h => by
    simp only [checkedBlockFieldsWF] at h ⊢
    obtain ⟨⟨hfield, hrecursive⟩, htail⟩ := h
    refine ⟨⟨hfield, ?_⟩,
      checkedBlockFieldsWF_mono henv htail⟩
    cases htarget : familyIndices[recursive.targetType]? with
    | none => simp [htarget] at hrecursive
    | some indices =>
      rw [htarget] at hrecursive
      exact hrecursive.mono henv

/-- The erased family-spine semantics is monotone in the environment. -/
theorem checkedFamilyListsWF_mono {source : VInductDecl}
    {params : List VExpr} {env env' : VEnv} {resultLevel : VLevel}
    {familyIndices : List (List VExpr)} (henv : env ≤ env') :
    ∀ levels indices constructors,
      checkedFamilyListsWF source params env resultLevel familyIndices
        levels indices constructors →
      checkedFamilyListsWF source params env' resultLevel familyIndices
        levels indices constructors := by
  intro levels
  induction levels with
  | nil =>
    intro indices constructors h
    cases indices <;> cases constructors <;>
      simp_all [checkedFamilyListsWF]
  | cons level levels ih =>
    intro indices constructors h
    cases indices with
    | nil => simp [checkedFamilyListsWF] at h
    | cons index indices =>
      cases constructors with
      | nil => simp [checkedFamilyListsWF] at h
      | cons familyConstructors constructors =>
        simp only [checkedFamilyListsWF] at h ⊢
        obtain ⟨hlevel, hindices, hconstructors, htail⟩ := h
        exact ⟨hlevel, hindices.mono henv,
          fun constructor hconstructor =>
            ⟨checkedBlockFieldsWF_mono henv
                (hconstructors constructor hconstructor).1,
              (hconstructors constructor hconstructor).2.mono henv⟩,
          ih indices constructors htail⟩

theorem CheckedBlock.WF.mono {source : VInductDecl}
    {checked : source.CheckedBlock} {env env' : VEnv}
    {resultLevel : VLevel} (henv : env ≤ env')
    (h : checked.WF env resultLevel) :
    checked.WF env' resultLevel :=
  checkedFamilyListsWF_mono henv _ _ _ h

/-- Transport recursive-argument evidence across definitionally equal base
contexts. The private binder telescope is transported first, then the
terminal family-index spine is transported beneath that same telescope. -/
theorem RecArg.WF.defeqDFC {env : VEnv} {U : Nat} {l : VLevel}
    {Is Γ₀ Γ₁ Γ₂ : List VExpr} {r : RecArg} (ord : env.Ordered)
    (hΓ : env.IsDefEqCtx U Γ₀ Γ₁ Γ₂)
    (h : r.WF U env l Is Γ₁) : r.WF U env l Is Γ₂ := by
  have htel := h.1.defeqDFC ord hΓ
  have hctx := h.1.extendDefEqCtx hΓ
  exact ⟨htel, h.2.defeqDFC ord hctx⟩

theorem fieldsWF_mono {U : Nat} {T : Name} {np : Nat} {env env' : VEnv} {l : VLevel}
    {Is : List VExpr} (henv : env ≤ env') : ∀ {Γ j Bs},
    fieldsWF U T np env l Is Γ j Bs → fieldsWF U T np env' l Is Γ j Bs
  | _, _, [], _ => trivial
  | _, _, _ :: _, ⟨hB, hSp, hT⟩ => by
    refine ⟨?_, fun hrec => (hSp hrec).mono henv, fieldsWF_mono henv hT⟩
    rcases hB with hrec | hfun | ⟨hnone, u, h, hl⟩
    · exact .inl hrec
    · obtain ⟨r, hr, hne, hwf⟩ := hfun
      exact .inr (.inl ⟨r, hr, hne, hwf.mono henv⟩)
    · exact .inr (.inr ⟨hnone, u, h.mono henv, hl⟩)

/-- The checked-view semantic certificate is monotone in the environment. -/
theorem Checked.WF.mono {decl : VInductDecl} {checked : decl.Checked}
    {env env' : VEnv} (henv : env ≤ env') (h : checked.WF env) :
    checked.WF env' := by
  unfold Checked.WF at h ⊢
  refine ⟨h.1.mono henv, fun c hc => ?_⟩
  exact ⟨fieldsWF_mono henv (h.2 c hc).1, (h.2 c hc).2.mono henv⟩

/-- Exact syntactic decomposition of an accepted family view into its
parameter telescope, index telescope, and terminal sort. -/
theorem Checked.type_eq
    {source : VInductDecl} (checked : source.Checked) :
    checked.type.type =
      VExpr.forallN checked.params
        (VExpr.forallN checked.indices (.sort checked.resultLevel)) := by
  rw [← VExpr.forallN_telN_dropN source.nparams checked.type.type,
    ← forallN_ctorFields_resultOf
      (VExpr.dropN source.nparams checked.type.type),
    checked.result_eq, checked.params_eq, checked.indices_eq]

/-- The semantic checker contract types the family before that family is
inserted. This is the exact premise needed by the first transaction step. -/
theorem Checked.WF.family_isType
    {source : VInductDecl} {checked : source.Checked}
    {env : VEnv} (h : checked.WF env) :
    env.IsType source.uvars [] checked.type.type := by
  rw [← VExpr.forallN_telN_dropN source.nparams checked.type.type,
    ← forallN_ctorFields_resultOf
      (VExpr.dropN source.nparams checked.type.type),
    checked.result_eq, ← VExpr.forallN_append]
  exact IsType.forallN
    (by simpa [checked.params_eq, checked.indices_eq] using h.1)
    ⟨_, HasType.sort checked.direct_anatomy.2.2.1⟩

/-- Once the retained family constant has the checked family type, the
checked constructor-result spine types the exact normalized family
application.  This fact depends only on analyzer semantics and the constant's
ordinary typing judgment; callers do not need to restate result typing for
each constructor candidate. -/
theorem GenerationChecked.checkedResultTarget_hasType
    {source : VInductDecl} (gen : GenerationChecked source)
    {env : VEnv} (henv : env.Ordered)
    (hchecked : gen.block.checked.WF env)
    (familyConst : env.HasType source.uvars []
      (.const gen.block.sourceType.name (VLevel.params source.uvars))
      gen.block.checked.type.type)
    {ctor : NormalizedCtor} (hctor : ctor ∈ gen.block.ctorPairs) :
    env.HasType source.uvars (ctor.viewBinders gen.block).reverse
      (ctor.resultTarget gen.block)
      (.sort gen.block.checked.resultLevel) := by
  have htype := gen.block.checked.type_eq
  have hfamily : env.HasType source.uvars
      (ctor.view.fields.reverse ++ gen.block.checked.params.reverse)
      (VExpr.appN
        (.const gen.block.sourceType.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange ctor.view.fields.length
          gen.block.checked.params.length))
      (VExpr.forallN
        (VExpr.liftTelN ctor.view.fields.length
          gen.block.checked.indices 0)
        (.sort gen.block.checked.resultLevel)) := by
    have hconst : env.HasType source.uvars
        (ctor.view.fields.reverse ++
          gen.block.checked.params.reverse ++ [])
        (.const gen.block.sourceType.name (VLevel.params source.uvars))
        (VExpr.forallN gen.block.checked.params
          (VExpr.forallN gen.block.checked.indices
            (.sort gen.block.checked.resultLevel))) := by
      simpa only [htype] using familyConst.weak0 henv
    have happ := HasType.appN_selfSpine'
      (As := gen.block.checked.params)
      (B := VExpr.forallN gen.block.checked.indices
        (.sort gen.block.checked.resultLevel))
      (Δ := ctor.view.fields.reverse) (Γ := [])
      (by simpa only [← htype] using gen.block.checked.type_closed)
      hconst
    rw [List.length_reverse, VExpr.liftN_forallN] at happ
    simpa using happ
  have hspine : env.SpineWF source.uvars
      (ctor.view.fields.reverse ++ gen.block.checked.params.reverse)
      (VExpr.forallN
        (VExpr.liftTelN ctor.view.fields.length
          gen.block.checked.indices 0)
        (.sort gen.block.checked.resultLevel))
      ctor.view.resultIndices
      (.sort gen.block.checked.resultLevel) := by
    obtain ⟨c, hc, hview⟩ := gen.viewCtor_ofDirect hctor
    have h := (hchecked.2 c hc).2
    rw [hview]
    simpa [CheckedCtor.ofDirect, gen.block.uvars_eq,
      gen.block.nparams_eq] using h
  have hresult := hspine.hasType_appN hfamily
  rw [← VExpr.appN_append] at hresult
  have hparams : gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hfields := (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
  rw [hparams, ← hfields] at hresult
  simpa [NormalizedCtor.viewBinders,
    NormalizedCtor.resultTarget] using hresult

/-- A paired checked constructor's stored view type is exactly its analyzed
binder telescope followed by the normalized family result application. -/
theorem GenerationChecked.viewCtorType_eq
    {source : VInductDecl} (gen : GenerationChecked source)
    {ctor : NormalizedCtor} (hctor : ctor ∈ gen.block.ctorPairs) :
    ctor.view.value.type =
      VExpr.forallN (ctor.viewBinders gen.block)
        (ctor.resultTarget gen.block) := by
  obtain ⟨c, hc, hview⟩ := gen.viewCtor_ofDirect hctor
  have hcAn := gen.block.checked.direct_anatomy.2.2.2.2.2 c hc
  have htype := VExpr.forallN_telN_dropN
    gen.block.normalization.view.nparams c.type
  rw [hcAn.2.1, (stage3Ctor_eq hcAn.2.2).1] at htype
  have hfields := (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
  have hfields' :
      (ctor.rawFields gen.block.normalization.view.nparams).length =
        (ctorFields (VExpr.dropN
          gen.block.normalization.view.nparams c.type)).length := by
    simpa [gen.block.nparams_eq, hview,
      CheckedCtor.ofDirect] using hfields
  simpa [← VExpr.forallN_append, NormalizedCtor.viewBinders,
    NormalizedCtor.resultTarget, hview, hfields',
    CheckedCtor.ofDirect, gen.block.uvars_eq,
    gen.block.nparams_eq, gen.block.sourceType_name_eq,
    gen.block.checked.params_eq, Nat.zero_add] using htype.symm

#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.type_eq [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationChecked.viewCtorType_eq [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationChecked.checkedResultTarget_hasType [propext, Quot.sound]

/-- Final-environment invariant for mixed raw/view generation. It contains
only facts stable after the raw family and constructors have been inserted;
the staged pre-family/post-family split remains in `GenerationChecked.WF`. -/
theorem GenerationChecked.sourceLevels_wf {source : VInductDecl}
    (gen : GenerationChecked source) :
    ∀ l ∈ gen.sourceLevels, l.WF gen.recUvars :=
  VLevel.params'_wf

@[simp] theorem GenerationChecked.sourceLevels_eq {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.sourceLevels =
      VLevel.params' source.uvars gen.elimination.offset := rfl

@[simp] theorem GenerationChecked.recUvars_eq {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.recUvars = source.uvars + gen.elimination.offset := rfl

@[simp] theorem GenerationChecked.recLevels_eq {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.recLevels = VLevel.params gen.recUvars := rfl

theorem GenerationChecked.sourceLevels_length {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.sourceLevels.length = source.uvars :=
  VLevel.params'_length

theorem GenerationChecked.motiveLevel_wf {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.motiveLevel.WF gen.recUvars := by
  cases h : gen.elimination <;>
    simp [GenerationChecked.motiveLevel,
      GenerationChecked.recUvars, ElimMode.recUvars,
      ElimMode.offset, ElimMode.motiveLevel, VLevel.WF, h]

theorem GenerationChecked.recLevels_wf {source : VInductDecl}
    (gen : GenerationChecked source) :
    ∀ l ∈ gen.recLevels, l.WF gen.recUvars :=
  VLevel.params_wf

theorem GenerationChecked.recLevels_length {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.recLevels.length = gen.recUvars :=
  VLevel.params_length

structure GenerationEnv {source : VInductDecl}
    (gen : GenerationChecked source) (env : VEnv) : Prop where
  ord : env.Ordered
  checked : gen.block.checked.WF env
  familyTel :
    env.TelDefEq source.uvars []
      (gen.block.rawParams ++ gen.block.rawIndices)
      (gen.block.checked.params ++ gen.block.checked.indices)
  familyResult :
    env.IsDefEq source.uvars
      (gen.block.rawParams ++ gen.block.rawIndices).reverse
      gen.block.rawResult (.sort gen.block.checked.resultLevel)
      (.sort (.succ gen.block.checked.resultLevel))
  ctorWF :
    ∀ ctor ∈ gen.block.ctorPairs, ctor.WF gen.block env
  familyConst :
    env.constants gen.block.sourceType.name =
      some gen.block.sourceType.toVConstant
  ctorConst :
    ∀ ctor ∈ gen.block.ctorPairs,
      env.constants ctor.raw.name = some ctor.raw.toVConstant

/-- Promote a staged generation certificate into the final invariant once the
transaction supplies environment growth and exact raw constant lookups. -/
theorem GenerationChecked.WF.toGenerationEnv {source : VInductDecl}
    {gen : GenerationChecked source} {pre envT env : VEnv}
    (h : gen.WF pre)
    (hadd : pre.addConst gen.block.sourceType.name
      gen.block.sourceType.toVConstant = some envT)
    (hlePre : pre ≤ env) (hleT : envT ≤ env) (ord : env.Ordered)
    (hfamily : env.constants gen.block.sourceType.name =
      some gen.block.sourceType.toVConstant)
    (hctors : ∀ ctor ∈ gen.block.ctorPairs,
      env.constants ctor.raw.name = some ctor.raw.toVConstant) :
    GenerationEnv gen env where
  ord := ord
  checked := h.blockWF.2.mono hlePre
  familyTel := h.familyTel.mono hlePre
  familyResult := h.familyResult.mono hlePre
  ctorWF := fun ctor hctor => (h.ctors envT hadd ctor hctor).mono hleT
  familyConst := hfamily
  ctorConst := hctors

theorem BlockGenerationChecked.sourceLevels_wf {source : VInductDecl}
    (gen : BlockGenerationChecked source) :
    ∀ l ∈ gen.sourceLevels, l.WF gen.recUvars :=
  VLevel.params'_wf

@[simp] theorem BlockGenerationChecked.sourceLevels_eq
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    gen.sourceLevels =
      VLevel.params' source.uvars gen.elimination.offset := rfl

@[simp] theorem BlockGenerationChecked.recUvars_eq
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    gen.recUvars = source.uvars + gen.elimination.offset := rfl

@[simp] theorem BlockGenerationChecked.recLevels_eq
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    gen.recLevels = VLevel.params gen.recUvars := rfl

theorem BlockGenerationChecked.sourceLevels_length
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    gen.sourceLevels.length = source.uvars :=
  VLevel.params'_length

theorem BlockGenerationChecked.motiveLevel_wf
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    gen.motiveLevel.WF gen.recUvars := by
  cases h : gen.elimination <;>
    simp [BlockGenerationChecked.motiveLevel,
      BlockGenerationChecked.recUvars, ElimMode.recUvars,
      ElimMode.offset, ElimMode.motiveLevel, VLevel.WF, h]

theorem BlockGenerationChecked.recLevels_wf
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    ∀ l ∈ gen.recLevels, l.WF gen.recUvars :=
  VLevel.params_wf

theorem BlockGenerationChecked.recLevels_length
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    gen.recLevels.length = gen.recUvars :=
  VLevel.params_length

/-- Stable final-environment invariant for mutual artifact generation. -/
structure BlockGenerationEnv {source : VInductDecl}
    (gen : BlockGenerationChecked source) (env : VEnv) : Prop where
  ord : env.Ordered
  resultLevelWF : gen.validated.resultLevel.WF source.uvars
  checked :
    gen.block.checked.WF env gen.validated.resultLevel
  paramsTel :
    env.TelDefEq source.uvars [] gen.block.rawParams
      gen.block.checked.params
  familyWF : ∀ family ∈ gen.families, family.WF gen env
  ctorWF : ∀ constructor ∈ gen.flatCtors,
    NormalizedBlockCtor.WF gen constructor env
  familyConst : ∀ family ∈ gen.families,
    env.constants family.raw.name = some family.raw.toVConstant
  ctorConst : ∀ constructor ∈ gen.flatCtors,
    env.constants constructor.ctor.raw.name =
      some constructor.ctor.raw.toVConstant

theorem BlockGenerationChecked.WF.toBlockGenerationEnv
    {source : VInductDecl} {gen : BlockGenerationChecked source}
    {pre blockEnv env : VEnv} (h : gen.WF pre blockEnv)
    (hlePre : pre ≤ env) (hleBlock : blockEnv ≤ env)
    (ord : env.Ordered)
    (hfamilies : ∀ family ∈ gen.families,
      env.constants family.raw.name = some family.raw.toVConstant)
    (hctors : ∀ constructor ∈ gen.flatCtors,
      env.constants constructor.ctor.raw.name =
        some constructor.ctor.raw.toVConstant) :
    BlockGenerationEnv gen env where
  ord := ord
  resultLevelWF := h.resultLevelWF
  checked := h.blockWF.2.mono hlePre
  paramsTel := h.paramsTel.mono hlePre
  familyWF := fun family hfamily =>
    (h.families family hfamily).mono hlePre
  ctorWF := fun constructor hconstructor =>
    (h.constructors constructor hconstructor).mono hleBlock
  familyConst := hfamilies
  ctorConst := hctors

theorem NormalizedFamily.rawType_eq {source : VInductDecl}
    (family : NormalizedFamily) :
    family.raw.type =
      VExpr.forallN (family.rawParams source.nparams)
        (VExpr.forallN (family.rawIndices source.nparams)
          (family.rawResult source.nparams)) := by
  conv => lhs
          rw [← VExpr.forallN_telN_dropN source.nparams family.raw.type,
            ← forallN_ctorFields_resultOf
              (VExpr.dropN source.nparams family.raw.type)]
  rfl

namespace BlockGenerationEnv

variable {source : VInductDecl} {gen : BlockGenerationChecked source}
  {env : VEnv} (S : BlockGenerationEnv gen env)
include S

theorem mono {env' : VEnv} (henv : env ≤ env') (ord : env'.Ordered) :
    BlockGenerationEnv gen env' where
  ord := ord
  resultLevelWF := S.resultLevelWF
  checked := S.checked.mono henv
  paramsTel := S.paramsTel.mono henv
  familyWF := fun family hfamily => (S.familyWF family hfamily).mono henv
  ctorWF := fun constructor hconstructor =>
    (S.ctorWF constructor hconstructor).mono henv
  familyConst := fun family hfamily =>
    henv.constants (S.familyConst family hfamily)
  ctorConst := fun constructor hconstructor =>
    henv.constants (S.ctorConst constructor hconstructor)

theorem generationParams_defeq :
    env.TelDefEq source.uvars []
      (generationParams gen.block.rawParams gen.block.checked.params)
      gen.block.checked.params :=
  S.paramsTel.generationParams S.ord

theorem generationParams_length :
    (generationParams gen.block.rawParams
      gen.block.checked.params).length = source.nparams := by
  exact (generationParams_length_of_eq S.paramsTel.length_eq).trans
    gen.shape.1

theorem generationParams_ctx :
    env.IsDefEqCtx source.uvars []
      (generationParams gen.block.rawParams
        gen.block.checked.params).reverse
      gen.block.checked.params.reverse := by
  simpa using S.generationParams_defeq.ctx

theorem generationParams_ctx_rec :
    env.IsDefEqCtx gen.recUvars [] gen.paramsTel.reverse
      (gen.block.checked.params.map
        (VExpr.instL gen.sourceLevels)).reverse := by
  have h := S.generationParams_defeq.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  simpa [BlockGenerationChecked.paramsTel, List.map_reverse] using h.ctx

theorem rawFamily_onTel {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.OnTel source.uvars []
      (family.rawParams source.nparams ++
        family.rawIndices source.nparams) :=
  (S.familyWF family hfamily).familyTel.raw_onTel

theorem familyConst_decl {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) {Γ : List VExpr} :
    env.HasType source.uvars Γ
      (.const family.raw.name (VLevel.params source.uvars))
      family.raw.type := by
  have hwf : family.raw.toVConstant.WF env := by
    show env.IsType family.raw.uvars [] family.raw.type
    rw [gen.family_uvars hfamily]
    exact (S.familyWF family hfamily).rawFamily_isType
  have h := HasType.const0 (S.familyConst family hfamily) hwf
  rw [gen.family_uvars hfamily] at h
  exact h.weak0 S.ord

theorem ctorConst_decl {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) {Γ : List VExpr} :
    env.HasType source.uvars Γ
      (.const constructor.ctor.raw.name (VLevel.params source.uvars))
      constructor.ctor.raw.type := by
  have hwf : constructor.ctor.raw.toVConstant.WF env := by
    show env.IsType constructor.ctor.raw.uvars []
      constructor.ctor.raw.type
    rw [gen.flatCtor_uvars hconstructor]
    exact (S.ctorWF constructor hconstructor).rawDeclared_isType
  have h := HasType.const0 (S.ctorConst constructor hconstructor) hwf
  rw [gen.flatCtor_uvars hconstructor] at h
  exact h.weak0 S.ord

theorem rawParams_defeq {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.TelDefEq source.uvars []
      (family.rawParams source.nparams) gen.block.checked.params := by
  have h := (S.familyWF family hfamily).familyTel.take source.nparams
  have hraw :
      (family.rawParams source.nparams ++
        family.rawIndices source.nparams).take source.nparams =
        family.rawParams source.nparams := by
    let Ps := family.rawParams source.nparams
    let Is := family.rawIndices source.nparams
    have hlen : Ps.length = source.nparams :=
      (gen.shape.2.2.2.2 family hfamily).2.2.1
    change (Ps ++ Is).take source.nparams = Ps
    rw [← hlen, List.take_append, List.take_length]
    simp
  have hviewLen : gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hview :
      (gen.block.checked.params ++ family.view.indices).take
          source.nparams = gen.block.checked.params := by
    rw [← hviewLen, List.take_append, List.take_length]
    simp
  rw [hraw, hview] at h
  exact h

theorem emittedFamilyTel {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.TelDefEq source.uvars []
      (family.rawParams source.nparams ++ family.rawIndices source.nparams)
      (gen.block.checked.params ++ family.rawIndices source.nparams) := by
  have hindices : env.OnTel source.uvars
      (family.rawParams source.nparams).reverse
      (family.rawIndices source.nparams) := by
    simpa using (S.rawFamily_onTel hfamily).of_append.2
  exact (S.rawParams_defeq hfamily).append_refl (by simpa using hindices)

theorem emittedFamily_onTel {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.OnTel source.uvars []
      (gen.block.checked.params ++ family.rawIndices source.nparams) :=
  (S.emittedFamilyTel hfamily).view_onTel S.ord

theorem generationFamilyTel {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.TelDefEq source.uvars []
      (generationParams gen.block.rawParams gen.block.checked.params ++
        family.rawIndices source.nparams)
      (gen.block.checked.params ++ family.rawIndices source.nparams) := by
  have hindicesChecked : env.OnTel source.uvars
      gen.block.checked.params.reverse (family.rawIndices source.nparams) := by
    simpa using (S.emittedFamily_onTel hfamily).of_append.2
  have hindicesGeneration : env.OnTel source.uvars
      (generationParams gen.block.rawParams
        gen.block.checked.params).reverse
      (family.rawIndices source.nparams) :=
    hindicesChecked.defeqDFC S.ord
      (S.generationParams_ctx.symm S.ord)
  exact S.generationParams_defeq.append_refl
    (by simpa using hindicesGeneration)

theorem generationFamily_onTel {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.OnTel source.uvars []
      (generationParams gen.block.rawParams gen.block.checked.params ++
        family.rawIndices source.nparams) :=
  (S.generationFamilyTel hfamily).raw_onTel

theorem emittedFamily_ctx {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.IsDefEqCtx source.uvars []
      (family.rawParams source.nparams ++
        family.rawIndices source.nparams).reverse
      (gen.block.checked.params ++
        family.rawIndices source.nparams).reverse := by
  simpa using (S.emittedFamilyTel hfamily).ctx

theorem generationFamily_ctx {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.IsDefEqCtx source.uvars []
      (generationParams gen.block.rawParams gen.block.checked.params ++
        family.rawIndices source.nparams).reverse
      (gen.block.checked.params ++
        family.rawIndices source.nparams).reverse := by
  simpa using (S.generationFamilyTel hfamily).ctx

theorem familyConst_emitted_decl {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.HasType source.uvars []
      (.const family.raw.name (VLevel.params source.uvars))
      (VExpr.forallN
        (gen.block.checked.params ++ family.rawIndices source.nparams)
        (family.rawResult source.nparams)) := by
  have hc : env.HasType source.uvars []
      (.const family.raw.name (VLevel.params source.uvars))
      (VExpr.forallN
        (family.rawParams source.nparams ++ family.rawIndices source.nparams)
        (family.rawResult source.nparams)) := by
    rw [VExpr.forallN_append, ← family.rawType_eq]
    exact S.familyConst_decl hfamily
  obtain ⟨_, htel⟩ := (S.emittedFamilyTel hfamily).forallN_defeq
    (by simpa [VEnv.HasType] using
      (S.familyWF family hfamily).familyResult.hasType.1)
  exact htel.defeq hc

theorem familyConst_generation_decl {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.HasType source.uvars []
      (.const family.raw.name (VLevel.params source.uvars))
      (VExpr.forallN
        (generationParams gen.block.rawParams gen.block.checked.params ++
          family.rawIndices source.nparams)
        (family.rawResult source.nparams)) := by
  have hresultChecked :=
    (S.familyWF family hfamily).familyResult.defeqDFC S.ord
      (S.emittedFamily_ctx hfamily)
  have hresultGeneration := hresultChecked.defeqDFC S.ord
    ((S.generationFamily_ctx hfamily).symm S.ord)
  obtain ⟨_, htel⟩ := (S.generationFamilyTel hfamily).forallN_defeq
    (by simpa [VEnv.HasType] using hresultGeneration.hasType.1)
  exact htel.defeq' (S.familyConst_emitted_decl hfamily)

theorem familyApp_hasType {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.HasType gen.recUvars
      ((gen.idxTel family).reverse ++ gen.paramsTel.reverse)
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange (gen.idxTel family).length source.nparams ++
          VExpr.bvarRevRange 0 (gen.idxTel family).length))
      (.sort (gen.validated.resultLevel.inst gen.sourceLevels)) := by
  let ls := gen.sourceLevels
  have hconst₀ := (S.familyConst_generation_decl hfamily).instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hconst₁ : env.HasType gen.recUvars []
      (.const family.raw.name ls)
      (VExpr.forallN (gen.paramsTel ++ gen.idxTel family)
        ((family.rawResult source.nparams).instL ls)) := by
    simpa [ls, BlockGenerationChecked.paramsTel,
      BlockGenerationChecked.idxTel, VExpr.instL_forallN,
      VExpr.instL, VLevel.params_map_inst_params'] using hconst₀
  have hclosed :
      (VExpr.forallN (gen.paramsTel ++ gen.idxTel family)
        ((family.rawResult source.nparams).instL ls)).ClosedN 0 :=
    (hconst₁.closedN' S.ord.closed trivial).2.2
  have hconst : env.HasType gen.recUvars
      ((gen.paramsTel ++ gen.idxTel family).reverse)
      (.const family.raw.name ls)
      (VExpr.forallN (gen.paramsTel ++ gen.idxTel family)
        ((family.rawResult source.nparams).instL ls)) :=
    hconst₁.weak0 S.ord
  have happ := HasType.appN_selfSpine'
    (Δ := []) (Γ := []) hclosed (by simpa using hconst)
  simp only [List.length_nil, VExpr.liftN_zero, List.nil_append,
    List.append_nil] at happ
  have hlen : (gen.paramsTel ++ gen.idxTel family).length =
      (gen.idxTel family).length + source.nparams := by
    simp only [List.length_append, BlockGenerationChecked.paramsTel,
      BlockGenerationChecked.idxTel, List.length_map]
    rw [S.generationParams_length]
    omega
  rw [VExpr.bvarRevRange_congr' 0 hlen,
    ← VExpr.bvarRevRange_append] at happ
  have hresult := (S.familyWF family hfamily).familyResult.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  simp only [List.map_reverse] at hresult
  have hctxChecked := ((S.emittedFamilyTel hfamily).instL
    (U' := gen.recUvars) gen.sourceLevels_wf).ctx
  simp only [List.map_nil, List.append_nil] at hctxChecked
  have hresultChecked := hresult.defeqDFC S.ord hctxChecked
  have hctxGeneration := ((S.generationFamilyTel hfamily).instL
    (U' := gen.recUvars) gen.sourceLevels_wf).ctx
  simp only [List.map_nil, List.append_nil] at hctxGeneration
  have hresultGeneration := hresultChecked.defeqDFC S.ord
    (hctxGeneration.symm S.ord)
  have hresult' : env.IsDefEq gen.recUvars
      ((gen.idxTel family).reverse ++ gen.paramsTel.reverse)
      ((family.rawResult source.nparams).instL ls)
      (.sort (gen.validated.resultLevel.inst ls))
      (.sort (.succ (gen.validated.resultLevel.inst ls))) := by
    simpa [ls, BlockGenerationChecked.paramsTel,
      BlockGenerationChecked.idxTel, List.map_reverse, VLevel.inst] using
      hresultGeneration
  exact hresult'.defeq (by
    simpa [List.reverse_append] using happ)

theorem motive_isType {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.IsType gen.recUvars gen.paramsTel.reverse
      (gen.motiveType family) := by
  have htel₀ := (S.generationFamily_onTel hfamily).instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have htel : env.OnTel gen.recUvars []
      (gen.paramsTel ++ gen.idxTel family) := by
    simpa [BlockGenerationChecked.paramsTel,
      BlockGenerationChecked.idxTel] using htel₀
  have hidx : env.OnTel gen.recUvars gen.paramsTel.reverse
      (gen.idxTel family) := by
    simpa using htel.of_append.2
  refine IsType.forallN hidx ?_
  exact ⟨_, by
    simpa [BlockGenerationChecked.motiveType] using
      HasType.forallE (S.familyApp_hasType hfamily)
        (HasType.sort gen.motiveLevel_wf)⟩

end BlockGenerationEnv

/-- Exact decomposition of the stored raw family type. -/
theorem NormalizedChecked.rawType_eq {source : VInductDecl}
    (block : NormalizedChecked source) :
    block.sourceType.type =
      VExpr.forallN block.rawParams
        (VExpr.forallN block.rawIndices block.rawResult) := by
  conv => lhs
          rw [← VExpr.forallN_telN_dropN source.nparams
            block.sourceType.type,
            ← forallN_ctorFields_resultOf
              (VExpr.dropN source.nparams block.sourceType.type)]
  rfl

/-- Exact decomposition of a stored raw constructor type into its declared
parameter/field telescope and terminal result. -/
theorem NormalizedCtor.rawType_eq {source : VInductDecl}
    (ctor : NormalizedCtor) :
    ctor.raw.type =
      VExpr.forallN (ctor.declaredBinders source.nparams)
        (ctor.rawResult source.nparams) := by
  conv => lhs
          rw [← VExpr.forallN_telN_dropN source.nparams
            ctor.raw.type,
            ← forallN_ctorFields_resultOf
              (VExpr.dropN source.nparams ctor.raw.type)]
  rw [NormalizedCtor.declaredBinders, NormalizedCtor.rawFields,
    NormalizedCtor.rawResult, ← VExpr.forallN_append]

namespace GenerationEnv

variable {source : VInductDecl} {gen : GenerationChecked source}
  {env : VEnv} (S : GenerationEnv gen env)
include S
-- `S` is included throughout so every lemma below is reachable as `S.lemma`,
-- including those whose statement and proof never mention it.
set_option linter.unusedSectionVars false

/-- The final mixed-generation invariant is monotone once the larger
environment is known to remain ordered. -/
theorem mono {env' : VEnv} (henv : env ≤ env') (ord : env'.Ordered) :
    GenerationEnv gen env' where
  ord := ord
  checked := S.checked.mono henv
  familyTel := S.familyTel.mono henv
  familyResult := S.familyResult.mono henv
  ctorWF := fun ctor hctor => (S.ctorWF ctor hctor).mono henv
  familyConst := henv.constants S.familyConst
  ctorConst := fun ctor hctor => henv.constants (S.ctorConst ctor hctor)

/-- The checked result universe is well formed at the source declaration's
universe arity. -/
theorem resultLevel_WF :
    gen.block.checked.resultLevel.WF source.uvars := by
  rw [gen.block.uvars_eq]
  exact gen.block.checked.direct_anatomy.2.2.1

theorem rawFamily_onTel :
    env.OnTel source.uvars []
      (gen.block.rawParams ++ gen.block.rawIndices) :=
  S.familyTel.raw_onTel

/-- The family parameter prefix is structurally definitionally equal to the
checked locals retained by validation. -/
theorem rawParams_defeq :
    env.TelDefEq source.uvars [] gen.block.rawParams
      gen.block.checked.params := by
  have h := S.familyTel.take source.nparams
  have hraw :
      (gen.block.rawParams ++ gen.block.rawIndices).take source.nparams =
        gen.block.rawParams := by
    rw [← gen.shape.1, List.take_append, List.take_length]
    simp
  have hviewLen : gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hview :
      (gen.block.checked.params ++ gen.block.checked.indices).take
          source.nparams = gen.block.checked.params := by
    rw [← hviewLen, List.take_append, List.take_length]
    simp
  rw [hraw, hview] at h
  exact h

/-- Raw and checked parameter contexts denote the same local telescope. -/
theorem rawParams_ctx :
    env.IsDefEqCtx source.uvars [] gen.block.rawParams.reverse
      gen.block.checked.params.reverse :=
  by simpa using S.rawParams_defeq.ctx

/-- The exact parameter surface emitted in recursor metadata remains
definitionally equal to the analyzer-owned parameters. -/
theorem generationParams_defeq :
    env.TelDefEq source.uvars [] gen.block.generationParams
      gen.block.checked.params := by
  exact S.rawParams_defeq.generationParams S.ord

theorem generationParams_ctx :
    env.IsDefEqCtx source.uvars [] gen.block.generationParams.reverse
      gen.block.checked.params.reverse :=
  by simpa using S.generationParams_defeq.ctx

theorem generationParams_length :
    gen.block.generationParams.length = source.nparams := by
  have hrawView := S.rawParams_defeq.length_eq
  exact (VInductDecl.generationParams_length_of_eq hrawView).trans
    gen.shape.1

theorem generationParams_ctx_rec :
    env.IsDefEqCtx (gen.recUvars) [] gen.paramsTel.reverse
      (gen.block.checked.params.map
        (VExpr.instL (gen.sourceLevels))).reverse := by
  have h := S.generationParams_defeq.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  simpa [GenerationChecked.paramsTel, List.map_reverse] using h.ctx

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.generationParams_defeq [propext, Quot.sound]

/-- Stored constructor fields are well formed over the exact generated
parameter surface after universe transport. -/
theorem generationFields_onTel_rec {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.OnTel (gen.recUvars) gen.paramsTel.reverse
      (ctor.fieldsR source.uvars source.nparams gen.elimination) := by
  have hemitted := (S.ctorWF ctor hctor).rawEmitted_onTel
  have hfields₀ := (OnTel.of_append
    (As := gen.block.checked.params) hemitted).2
  have hfields₁ := hfields₀.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hfieldsChecked : env.OnTel (gen.recUvars)
      (gen.block.checked.params.map
        (VExpr.instL (gen.sourceLevels))).reverse
      (ctor.fieldsR source.uvars source.nparams gen.elimination) := by
    simpa [NormalizedCtor.fieldsR, List.map_reverse] using hfields₁
  exact hfieldsChecked.defeqDFC S.ord
    (S.generationParams_ctx_rec.symm S.ord)

theorem generationFieldPrefix_ctx_rec {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) (j : Nat) :
    env.IsDefEqCtx (gen.recUvars) []
      ((ctor.fieldsR source.uvars source.nparams gen.elimination |>.take j).reverse ++
        gen.paramsTel.reverse)
      ((ctor.fieldsR source.uvars source.nparams gen.elimination |>.take j).reverse ++
        (gen.block.checked.params.map
          (VExpr.instL (gen.sourceLevels))).reverse) := by
  have hfields := S.generationFields_onTel_rec hctor
  rw [← List.take_append_drop j
    (ctor.fieldsR source.uvars source.nparams gen.elimination)] at hfields
  exact (hfields.of_append.1).extendDefEqCtx
    S.generationParams_ctx_rec

/-- The family telescope used by generated artifacts keeps raw index syntax
but uses the checked parameter prefix consumed by validation. -/
theorem emittedFamilyTel :
    env.TelDefEq source.uvars []
      (gen.block.rawParams ++ gen.block.rawIndices)
      (gen.block.checked.params ++ gen.block.rawIndices) := by
  have hindices : env.OnTel source.uvars gen.block.rawParams.reverse
      gen.block.rawIndices := by
    simpa using S.rawFamily_onTel.of_append.2
  exact S.rawParams_defeq.append_refl (by simpa using hindices)

/-- The emitted mixed family telescope is well formed. -/
theorem emittedFamily_onTel :
    env.OnTel source.uvars []
      (gen.block.checked.params ++ gen.block.rawIndices) :=
  S.emittedFamilyTel.view_onTel S.ord

/-- Replace the checked parameter prefix by the kernel-observable generation
surface while leaving the stored raw index telescope unchanged. -/
theorem generationFamilyTel :
    env.TelDefEq source.uvars []
      (gen.block.generationParams ++ gen.block.rawIndices)
      (gen.block.checked.params ++ gen.block.rawIndices) := by
  have hindicesChecked : env.OnTel source.uvars
      gen.block.checked.params.reverse gen.block.rawIndices := by
    simpa using S.emittedFamily_onTel.of_append.2
  have hindicesGeneration : env.OnTel source.uvars
      gen.block.generationParams.reverse gen.block.rawIndices :=
    hindicesChecked.defeqDFC S.ord
      (S.generationParams_ctx.symm S.ord)
  exact S.generationParams_defeq.append_refl
    (by simpa using hindicesGeneration)

theorem generationFamily_onTel :
    env.OnTel source.uvars []
      (gen.block.generationParams ++ gen.block.rawIndices) :=
  S.generationFamilyTel.raw_onTel

theorem generationFamily_ctx :
    env.IsDefEqCtx source.uvars []
      (gen.block.generationParams ++ gen.block.rawIndices).reverse
      (gen.block.checked.params ++ gen.block.rawIndices).reverse :=
  by simpa using S.generationFamilyTel.ctx

/-- Completed raw and emitted family contexts are definitionally equal. -/
theorem emittedFamily_ctx :
    env.IsDefEqCtx source.uvars []
      (gen.block.rawParams ++ gen.block.rawIndices).reverse
      (gen.block.checked.params ++ gen.block.rawIndices).reverse :=
  by simpa using S.emittedFamilyTel.ctx

theorem rawFamily_isType :
    env.IsType source.uvars [] gen.block.sourceType.type := by
  rw [gen.block.rawType_eq, ← VExpr.forallN_append]
  have hresult₀ : env.IsType source.uvars
      (gen.block.rawParams ++ gen.block.rawIndices).reverse
      gen.block.rawResult :=
    ⟨_, S.familyResult.hasType.1⟩
  have hresult : env.IsType source.uvars
      ((gen.block.rawParams ++ gen.block.rawIndices).reverse ++ [])
      gen.block.rawResult := by
    simpa using hresult₀
  exact IsType.forallN S.rawFamily_onTel hresult

theorem rawCtor_isType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.IsType source.uvars [] ctor.raw.type :=
  (S.ctorWF ctor hctor).rawDeclared_isType

/-- The raw family constant at declaration universes, in any context. -/
theorem familyConst_decl {Γ : List VExpr} :
    env.HasType source.uvars Γ
      (.const gen.block.sourceType.name (VLevel.params source.uvars))
      gen.block.sourceType.type := by
  have hwf : gen.block.sourceType.toVConstant.WF env := by
    show env.IsType gen.block.sourceType.uvars []
      gen.block.sourceType.type
    rw [gen.block.sourceType_uvars_eq]
    exact S.rawFamily_isType
  have h := HasType.const0 S.familyConst hwf
  rw [gen.block.sourceType_uvars_eq] at h
  exact h.weak0 S.ord

/-- A stored raw constructor constant at declaration universes, in any
context. -/
theorem ctorConst_decl {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {Γ : List VExpr} :
    env.HasType source.uvars Γ
      (.const ctor.raw.name (VLevel.params source.uvars))
      ctor.raw.type := by
  have hwf : ctor.raw.toVConstant.WF env := by
    show env.IsType ctor.raw.uvars [] ctor.raw.type
    rw [gen.ctor_uvars_eq hctor]
    exact S.rawCtor_isType hctor
  have h := HasType.const0 (S.ctorConst ctor hctor) hwf
  rw [gen.ctor_uvars_eq hctor] at h
  exact h.weak0 S.ord

/-- The stored constructor constant applied to the checked-parameter/raw-field
self-spine emitted by mixed artifacts. The constructor's declared parameter
prefix need only be definitionally equal to this checked family prefix. -/
theorem ctorApp_emitted_decl {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.HasType source.uvars
      ((ctor.rawFields source.nparams).reverse ++
        gen.block.checked.params.reverse)
      (VExpr.appN
        (.const ctor.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (ctor.rawFields source.nparams).length source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.rawFields source.nparams).length))
      (ctor.resultTarget gen.block) := by
  let E := ctor.emittedBinders gen.block
  let V := ctor.viewBinders gen.block
  have hc : env.HasType source.uvars []
      (.const ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN (ctor.declaredBinders source.nparams)
        (ctor.rawResult source.nparams)) := by
    rw [← ctor.rawType_eq]
    exact S.ctorConst_decl hctor
  obtain ⟨_, hdecl⟩ :=
    (S.ctorWF ctor hctor).declaredTel.forallN_defeq
      (by
        simpa using (S.ctorWF ctor hctor).declaredResult)
  have hview : env.HasType source.uvars []
      (.const ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN V (ctor.resultTarget gen.block)) := by
    simpa [V] using hdecl.defeq hc
  have hresult : env.HasType source.uvars E.reverse
      (ctor.resultTarget gen.block)
      (.sort gen.block.checked.resultLevel) := by
    simpa [E] using
      (S.ctorWF ctor hctor).emittedResult.hasType.2
  obtain ⟨_, hemit⟩ :=
    (S.ctorWF ctor hctor).emittedTel.forallN_defeq
      (by simpa [E, VEnv.HasType] using hresult)
  have hcE₀ : env.HasType source.uvars []
      (.const ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN E (ctor.resultTarget gen.block)) := by
    exact hemit.defeq' (by simpa [V] using hview)
  have hclosed :
      (VExpr.forallN E (ctor.resultTarget gen.block)).ClosedN 0 :=
    (hcE₀.closedN' S.ord.closed trivial).2.2
  have hcE : env.HasType source.uvars E.reverse
      (.const ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN E (ctor.resultTarget gen.block)) :=
    hcE₀.weak0 S.ord
  have happ := HasType.appN_selfSpine'
    (As := E) (B := ctor.resultTarget gen.block)
    (Δ := []) (Γ := []) hclosed (by simpa using hcE)
  simp only [List.length_nil, VExpr.liftN_zero,
    List.nil_append, List.append_nil] at happ
  have hEctx :
      E.reverse =
        (ctor.rawFields source.nparams).reverse ++
          gen.block.checked.params.reverse := by
    simp [E, NormalizedCtor.emittedBinders,
      List.reverse_append]
  have hElen :
      E.length =
        (ctor.rawFields source.nparams).length +
          source.nparams := by
    have hp : gen.block.checked.params.length = source.nparams :=
      gen.shape.2.1.symm.trans gen.shape.1
    simp [E, NormalizedCtor.emittedBinders, hp]
    omega
  rw [hEctx, hElen,
    ← VExpr.bvarRevRange_append source.nparams
      (ctor.rawFields source.nparams).length] at happ
  exact happ

/-- The raw family constant instantiated into recursor universes. -/
theorem familyConst_rec {Γ : List VExpr} :
    env.HasType (gen.recUvars) Γ
      (.const gen.block.sourceType.name
        (gen.sourceLevels))
      (gen.block.sourceType.type.instL
        (gen.sourceLevels)) := by
  have h := (S.familyConst_decl (Γ := [])).instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  rw [show
    (VExpr.const gen.block.sourceType.name
      (VLevel.params source.uvars)).instL
        (gen.sourceLevels) =
      .const gen.block.sourceType.name
        (gen.sourceLevels) by
    simp [VExpr.instL, VLevel.params_map_inst_params']] at h
  exact h.weak0 S.ord

/-- The raw family type decomposed in recursor universes. -/
theorem rawType_rec_eq :
    gen.block.sourceType.type.instL (gen.sourceLevels) =
      VExpr.forallN
        (gen.block.rawParams.map
          (VExpr.instL (gen.sourceLevels)))
        (VExpr.forallN gen.idxTel
          (gen.block.rawResult.instL
            (gen.sourceLevels))) := by
  rw [gen.block.rawType_eq, VExpr.instL_forallN,
    VExpr.instL_forallN]
  rfl

/-- The family constant may be viewed through the checked-parameter/raw-index
telescope emitted by generated artifacts. -/
theorem familyConst_emitted_decl :
    env.HasType source.uvars []
      (.const gen.block.sourceType.name (VLevel.params source.uvars))
      (VExpr.forallN
        (gen.block.checked.params ++ gen.block.rawIndices)
        gen.block.rawResult) := by
  have hc : env.HasType source.uvars []
      (.const gen.block.sourceType.name (VLevel.params source.uvars))
      (VExpr.forallN
        (gen.block.rawParams ++ gen.block.rawIndices)
        gen.block.rawResult) := by
    rw [VExpr.forallN_append, ← gen.block.rawType_eq]
    exact S.familyConst_decl
  obtain ⟨_, htel⟩ := S.emittedFamilyTel.forallN_defeq
    (by simpa [VEnv.HasType] using S.familyResult.hasType.1)
  exact htel.defeq hc

/-- The family constant viewed through the exact parameter syntax retained
by generated kernel metadata. -/
theorem familyConst_generation_decl :
    env.HasType source.uvars []
      (.const gen.block.sourceType.name (VLevel.params source.uvars))
      (VExpr.forallN
        (gen.block.generationParams ++ gen.block.rawIndices)
        gen.block.rawResult) := by
  have hresultChecked := S.familyResult.defeqDFC S.ord
    S.emittedFamily_ctx
  have hresultGeneration := hresultChecked.defeqDFC S.ord
    (S.generationFamily_ctx.symm S.ord)
  obtain ⟨_, htel⟩ := S.generationFamilyTel.forallN_defeq
    (by simpa [VEnv.HasType] using hresultGeneration.hasType.1)
  exact htel.defeq' S.familyConst_emitted_decl

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.familyConst_generation_decl [propext, Quot.sound]

/-- The family applied to its checked-parameter/raw-index self-spine has the
normalized result sort. -/
theorem familyApp_hasType :
    env.HasType (gen.recUvars)
      (gen.idxTel.reverse ++ gen.paramsTel.reverse)
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange gen.idxTel.length source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length))
      (.sort
        (gen.block.checked.resultLevel.inst
          (gen.sourceLevels))) := by
  let ls := gen.sourceLevels
  have hconst₀ := S.familyConst_generation_decl.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hconst₁ : env.HasType (gen.recUvars) []
      (.const gen.block.sourceType.name ls)
      (VExpr.forallN (gen.paramsTel ++ gen.idxTel)
        (gen.block.rawResult.instL ls)) := by
    simpa [ls, GenerationChecked.paramsTel,
      GenerationChecked.idxTel, VExpr.instL_forallN,
      VExpr.instL, VLevel.params_map_inst_params'] using hconst₀
  have hcanonicalClosed :
      (VExpr.forallN (gen.paramsTel ++ gen.idxTel)
        (gen.block.rawResult.instL ls)).ClosedN 0 := by
    exact (hconst₁.closedN' S.ord.closed trivial).2.2
  have hconst : env.HasType (gen.recUvars)
      ((gen.paramsTel ++ gen.idxTel).reverse)
      (.const gen.block.sourceType.name ls)
      (VExpr.forallN (gen.paramsTel ++ gen.idxTel)
        (gen.block.rawResult.instL ls)) :=
    hconst₁.weak0 S.ord
  have happ := HasType.appN_selfSpine'
    (Δ := []) (Γ := []) hcanonicalClosed (by
      simpa using hconst)
  simp only [List.length_nil, VExpr.liftN_zero, List.nil_append,
    List.append_nil] at happ
  have hlen :
      (gen.paramsTel ++ gen.idxTel).length =
        gen.idxTel.length + source.nparams := by
    simp only [List.length_append, GenerationChecked.paramsTel,
      GenerationChecked.idxTel, List.length_map]
    rw [S.generationParams_length]
    omega
  rw [VExpr.bvarRevRange_congr' 0 hlen,
    ← VExpr.bvarRevRange_append] at happ
  have hresult := S.familyResult.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  simp only [List.map_reverse] at hresult
  have hctxChecked := (S.emittedFamilyTel.instL
    (U' := gen.recUvars) gen.sourceLevels_wf).ctx
  simp only [List.map_nil, List.append_nil] at hctxChecked
  have hresultChecked := hresult.defeqDFC S.ord hctxChecked
  have hctxGeneration := (S.generationFamilyTel.instL
    (U' := gen.recUvars) gen.sourceLevels_wf).ctx
  simp only [List.map_nil, List.append_nil] at hctxGeneration
  have hresultGeneration := hresultChecked.defeqDFC S.ord
    (hctxGeneration.symm S.ord)
  have hresult' : env.IsDefEq (gen.recUvars)
      (gen.idxTel.reverse ++ gen.paramsTel.reverse)
      (gen.block.rawResult.instL ls)
      (.sort (gen.block.checked.resultLevel.inst ls))
      (.sort (.succ (gen.block.checked.resultLevel.inst ls))) := by
    simpa [ls, GenerationChecked.paramsTel, GenerationChecked.idxTel,
      List.map_reverse, VLevel.inst] using hresultGeneration
  exact hresult'.defeq (by
    simpa [List.reverse_append] using happ)

/-- The mixed motive is a well-formed type over the checked parameter
context. -/
theorem motive_isType :
    env.IsType (gen.recUvars) gen.paramsTel.reverse
      gen.motiveType := by
  have htel₀ := S.generationFamily_onTel.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have htel :
      env.OnTel (gen.recUvars) []
        (gen.paramsTel ++ gen.idxTel) := by
    simpa [GenerationChecked.paramsTel, GenerationChecked.idxTel] using htel₀
  have hidx : env.OnTel (gen.recUvars) gen.paramsTel.reverse
      gen.idxTel := by
    simpa using htel.of_append.2
  refine IsType.forallN hidx ?_
  exact ⟨_, by
    simpa [GenerationChecked.motiveType] using
      HasType.forallE S.familyApp_hasType
        (HasType.sort gen.motiveLevel_wf)⟩

end GenerationEnv

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.motive_isType [propext, Quot.sound]

theorem BlockGenerationChecked.motiveTypesAux_length
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    ∀ (families : List NormalizedFamily) (i : Nat),
      (gen.motiveTypesAux families i).length = families.length
  | [], _ => rfl
  | _ :: families, i => by
    simp only [BlockGenerationChecked.motiveTypesAux, List.length_cons]
    rw [gen.motiveTypesAux_length families (i + 1)]

theorem BlockGenerationChecked.motiveTypes_length
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    gen.motiveTypes.length = gen.familyCount := by
  unfold BlockGenerationChecked.motiveTypes
  exact gen.motiveTypesAux_length gen.families 0

/-- Pairing arbitrary stored families with a dependent checked-family spine
does not change the checked ordinal at any surviving position. -/
theorem CheckedFamilies.pairNormalizedFamilies_getElem?_ordinal
    {source : VInductDecl} {params : List VExpr}
    {ordinal : Nat} {types : List VInductiveType}
    (families : CheckedFamilies source params ordinal types) :
    ∀ {raws i family},
      (pairNormalizedFamilies raws families.data)[i]? = some family →
      family.view.ordinal = ordinal + i := by
  induction families with
  | nil =>
    intro raws i family h
    simp [CheckedFamilies.data, pairNormalizedFamilies] at h
  | @cons ordinal type types head tail ih =>
    intro raws i family h
    cases raws with
    | nil => simp [pairNormalizedFamilies] at h
    | cons raw raws =>
      cases i with
      | zero =>
        simp only [CheckedFamilies.data, pairNormalizedFamilies,
          List.getElem?_cons_zero] at h
        injection h with hfamily
        subst family
        rfl
      | succ i =>
        simp only [CheckedFamilies.data, pairNormalizedFamilies,
          List.getElem?_cons_succ] at h
        have hord := ih h
        omega

/-- Every retained family is found at its checked source ordinal. -/
theorem BlockGenerationChecked.family_getElem?_ordinal
    {source : VInductDecl} (gen : BlockGenerationChecked source)
    {family : NormalizedFamily} (hfamily : family ∈ gen.families) :
    gen.families[family.view.ordinal]? = some family := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hfamily
  have hi' :
      (pairNormalizedFamilies source.types
        gen.block.checked.families.data)[i]? = some family := by
    simpa [BlockGenerationChecked.families,
      NormalizedCheckedBlock.familyPairs] using hi
  have hord :=
    CheckedFamilies.pairNormalizedFamilies_getElem?_ordinal
      gen.block.checked.families hi'
  have hord' : family.view.ordinal = i := by
    simpa using hord
  rwa [hord']

theorem BlockGenerationChecked.family_ordinal_lt
    {source : VInductDecl} (gen : BlockGenerationChecked source)
    {family : NormalizedFamily} (hfamily : family ∈ gen.families) :
    family.view.ordinal < gen.familyCount := by
  obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.1
    (gen.family_getElem?_ordinal hfamily)
  exact h

/-- Selecting a retained family by its checked ordinal recovers its exact
raw constant name. -/
@[simp] theorem BlockGenerationChecked.familyNameAt_ordinal
    {source : VInductDecl} (gen : BlockGenerationChecked source)
    {family : NormalizedFamily} (hfamily : family ∈ gen.families) :
    gen.familyNameAt family.view.ordinal = family.raw.name := by
  simp [BlockGenerationChecked.familyNameAt,
    gen.family_getElem?_ordinal hfamily]

/-- Positional lookup through the progressively weakened mutual motive
telescope. -/
theorem BlockGenerationChecked.motiveTypesAux_getElem?
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    ∀ (families : List NormalizedFamily) (i q : Nat),
      (gen.motiveTypesAux families i)[q]? =
        families[q]?.map fun family =>
          (gen.motiveType family).liftN (i + q)
  | [], _, q => by simp [BlockGenerationChecked.motiveTypesAux]
  | _ :: _, _, 0 => by simp [BlockGenerationChecked.motiveTypesAux]
  | _ :: families, i, q + 1 => by
    simp only [BlockGenerationChecked.motiveTypesAux,
      List.getElem?_cons_succ]
    rw [gen.motiveTypesAux_getElem? families (i + 1) q,
      show i + 1 + q = i + (q + 1) by omega]

theorem BlockGenerationChecked.motiveTypes_getElem?_ordinal
    {source : VInductDecl} (gen : BlockGenerationChecked source)
    {family : NormalizedFamily} (hfamily : family ∈ gen.families) :
    gen.motiveTypes[family.view.ordinal]? =
      some ((gen.motiveType family).liftN family.view.ordinal) := by
  rw [show gen.motiveTypes = gen.motiveTypesAux gen.families 0 from rfl,
    gen.motiveTypesAux_getElem?]
  rw [gen.family_getElem?_ordinal hfamily]
  simp

/-- Paired block constructors retain the raw/view field arity certified by
normalization. -/
theorem BlockGenerationChecked.flatCtor_fields_length
    {source : VInductDecl} (gen : BlockGenerationChecked source)
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) :
    (constructor.ctor.rawFields source.nparams).length =
      constructor.ctor.view.fields.length := by
  simp only [BlockGenerationChecked.flatCtors,
    NormalizedCheckedBlock.flatCtors, List.mem_flatMap] at hconstructor
  obtain ⟨family, hfamily, hconstructor⟩ := hconstructor
  simp only [NormalizedFamily.blockCtors, List.mem_map] at hconstructor
  obtain ⟨ctor, hctor, rfl⟩ := hconstructor
  exact ((gen.shape.2.2.2.2 family hfamily).2.2.2.2.2.2
    ctor hctor).2.2.2

/-- Syntactic lifting law for any member of the mutual motive telescope. -/
theorem BlockGenerationChecked.motiveType_liftN
    {source : VInductDecl} (gen : BlockGenerationChecked source)
    (family : NormalizedFamily) (n : Nat) :
    (gen.motiveType family).liftN n =
      VExpr.forallN (VExpr.liftTelN n (gen.idxTel family) 0)
        (.forallE
          (VExpr.appN
            (.const family.raw.name gen.sourceLevels)
            (VExpr.bvarRevRange (n + (gen.idxTel family).length)
                source.nparams ++
              VExpr.bvarRevRange 0 (gen.idxTel family).length))
          (.sort gen.motiveLevel)) := by
  rw [show gen.motiveType family =
      VExpr.forallN (gen.idxTel family)
        (.forallE
          (VExpr.appN
            (.const family.raw.name gen.sourceLevels)
            (VExpr.bvarRevRange (gen.idxTel family).length source.nparams ++
              VExpr.bvarRevRange 0 (gen.idxTel family).length))
          (.sort gen.motiveLevel)) from rfl,
    VExpr.liftN_forallN]
  refine congrArg _ ?_
  show VExpr.forallE _ _ = VExpr.forallE _ _
  refine congr (congrArg _ ?_) rfl
  rw [VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
  rfl

/-- Apply a selected mutual motive variable to its target-family indices and
a typed major premise. -/
theorem BlockGenerationChecked.motiveVarApp_hasType
    {source : VInductDecl} (gen : BlockGenerationChecked source)
    (family : NormalizedFamily) {env : VEnv} {l : VLevel}
    {Γ : List VExpr} {K q : Nat} {idxs : List VExpr} {a : VExpr}
    (hM : env.HasType gen.recUvars Γ (.bvar K)
      ((gen.motiveType family).liftN (q + K + 1)))
    (hidx : env.SpineWF gen.recUvars Γ
      (VExpr.forallN
        (VExpr.liftTelN (q + K + 1) (gen.idxTel family) 0)
        (.sort l))
      idxs (.sort l))
    (hlen : idxs.length = (gen.idxTel family).length)
    (ha : env.HasType gen.recUvars Γ a
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange (q + K + 1) source.nparams ++ idxs))) :
    env.HasType gen.recUvars Γ
      (VExpr.appN (.bvar K) (idxs ++ [a]))
      (.sort gen.motiveLevel) := by
  rw [gen.motiveType_liftN family] at hM
  have hshape := hidx.retarget
    (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            (q + K + 1 + (gen.idxTel family).length)
            source.nparams ++
          VExpr.bvarRevRange 0 (gen.idxTel family).length))
      (.sort gen.motiveLevel))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _
      (C := .const family.raw.name gen.sourceLevels) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show q + K + 1 + (gen.idxTel family).length - idxs.length =
      q + K + 1 from by rw [hlen]; omega,
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hApp := hshape.hasType_appN hM
  rw [VExpr.appN_append]
  exact HasType.app hApp (by simpa using ha)

/-- A recursive raw field, after inserting the full mutual motive telescope
and the constructor-local binders, is the family application expected by its
generated induction hypothesis. -/
theorem blockMinor_fieldType_of_eq
    {source : VInductDecl} {familyName : Name}
    {B : VExpr} {r₀ : RecArg}
    (hB : B = VExpr.forallN r₀.binders
      (VExpr.appN (.const familyName (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (r₀.fieldIndex + r₀.binders.length) source.nparams ++
          r₀.indices)))
    (d m p : Nat) (hj : r₀.fieldIndex < m)
    (mode : ElimMode := .large) :
    let ls := mode.sourceLevels source.uvars
    let r := r₀.instL ls
    ((B.instL ls).liftN d r.fieldIndex).liftN
        (m - r.fieldIndex + p) =
      VExpr.forallN
        (BlockGenerationChecked.blockMinorBinders d m p r)
        (VExpr.appN (.const familyName ls)
          (VExpr.bvarRevRange
              (m + p + r.binders.length + d) source.nparams ++
            r.indices.map fun e =>
              (e.liftN d (r.fieldIndex + r.binders.length)).liftN
                (m - r.fieldIndex + p) r.binders.length)) := by
  dsimp only
  conv => lhs; rw [hB]
  simp only [RecArg.instL, VExpr.instL_forallN, VExpr.instL_appN,
    List.map_append, bvarRevRange_instL,
    show (VExpr.const familyName (VLevel.params source.uvars)).instL
        (mode.sourceLevels source.uvars) =
      .const familyName (mode.sourceLevels source.uvars) from by
        simp [VExpr.instL, ElimMode.sourceLevels,
          VLevel.params_map_inst_params'],
    VExpr.liftN_forallN, VExpr.liftN_appN]
  simp only [List.length_map, VExpr.liftTelN_length, Nat.zero_add]
  rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    show m - r₀.fieldIndex + p +
        (d + (r₀.fieldIndex + r₀.binders.length)) =
      m + p + r₀.binders.length + d from by omega]
  simp only [List.map_map,
    BlockGenerationChecked.blockMinorBinders]
  apply congrArg (VExpr.forallN _)
  apply congrArg (VExpr.appN
    (.const familyName (mode.sourceLevels source.uvars)))
  apply congrArg
    (VExpr.bvarRevRange (m + p + r₀.binders.length + d)
      source.nparams ++ ·)
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply]

/-- Raw mixed fields preserve their arity under recursor-universe
instantiation. -/
theorem NormalizedCtor.fieldsR_length {source : VInductDecl}
    (ctor : NormalizedCtor) {mode : ElimMode} :
    (ctor.fieldsR source.uvars source.nparams mode).length =
      (ctor.rawFields source.nparams).length :=
  List.length_map ..

/-- Pointwise lookup through the raw mixed field universe transport. -/
theorem NormalizedCtor.fieldsR_getElem? {source : VInductDecl}
    {ctor : NormalizedCtor} {q : Nat} {mode : ElimMode} :
    (ctor.fieldsR source.uvars source.nparams mode)[q]? =
      (ctor.rawFields source.nparams)[q]?.map
        (VExpr.instL (mode.sourceLevels source.uvars)) :=
  List.getElem?_map ..

/-- Unpack one mixed recursive descriptor to the retained declaration-level
descriptor from the checked view. -/
theorem NormalizedCtor.recArgsR_mem {source : VInductDecl}
    {ctor : NormalizedCtor} {r : RecArg} {mode : ElimMode}
    (hr : r ∈ ctor.recArgsR source.uvars mode) :
    ∃ r₀, r₀ ∈ ctor.view.recursive ∧
      r = r₀.instL (mode.sourceLevels source.uvars) := by
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
  exact ⟨r₀, hr₀, rfl⟩

theorem liftTelN_congr {a a' : Nat} (tel : List VExpr) (k : Nat)
    (h : a = a') :
    VExpr.liftTelN a tel k = VExpr.liftTelN a' tel k := h ▸ rfl

theorem BlockGenerationChecked.blockIHsFromRecArgs_length (d m : Nat) :
    ∀ (rs : List RecArg) (p : Nat),
      (BlockGenerationChecked.blockIHsFromRecArgs d m rs p).length = rs.length
  | [], _ => rfl
  | _ :: rs, p => by
    simp [BlockGenerationChecked.blockIHsFromRecArgs,
      BlockGenerationChecked.blockIHsFromRecArgs_length d m rs (p + 1)]

/-- Rule-context normal form of one mutual induction hypothesis. The
recursive result is routed to the motive selected by `targetType`. -/
def BlockGenerationChecked.blockRuleIH
    (d k m : Nat) (r : RecArg) : VExpr :=
  let n := r.binders.length
  VExpr.forallN
    (BlockGenerationChecked.blockRuleBinders (d+k) m r)
    (VExpr.appN
      (.bvar (d - 1 - r.targetType + k + m + n))
      ((r.indices.map fun e =>
          (e.liftN (d+k) (r.fieldIndex+n)).liftN
            (m-r.fieldIndex) n) ++
        [VExpr.appN (.bvar (m-1-r.fieldIndex+n))
          (VExpr.bvarRevRange 0 n)]))

/-- Rule-context induction hypotheses, weakened past their preceding
hypothesis binders. -/
def BlockGenerationChecked.blockRuleIHs (d k m : Nat) :
    List RecArg → Nat → List VExpr
  | [], _ => []
  | r :: rs, p =>
    (BlockGenerationChecked.blockRuleIH d k m r).liftN p ::
      BlockGenerationChecked.blockRuleIHs d k m rs (p+1)

theorem BlockGenerationChecked.blockMinorBinders_shift
    (d : Nat) (r : RecArg) (m p : Nat) :
    BlockGenerationChecked.blockMinorBinders d m p r =
      VExpr.liftTelN p
        (BlockGenerationChecked.blockMinorBinders d m 0 r) 0 := by
  simp only [BlockGenerationChecked.blockMinorBinders, Nat.add_zero]
  rw [VExpr.liftTelN_liftTelN]

/-- The shift parameter of a mutual minor IH is precisely weakening past
the preceding IH binders. -/
theorem BlockGenerationChecked.blockMinorIH_shift
    (d : Nat) (r : RecArg) (m p : Nat) (hj : r.fieldIndex < m) :
    BlockGenerationChecked.blockMinorIH d m p r =
      (BlockGenerationChecked.blockMinorIH d m 0 r).liftN p := by
  simp only [BlockGenerationChecked.blockMinorIH,
    VExpr.liftN_forallN]
  rw [← BlockGenerationChecked.blockMinorBinders_shift d r m p]
  rw [show
      (BlockGenerationChecked.blockMinorBinders d m 0 r).length =
        r.binders.length by
      simp [BlockGenerationChecked.blockMinorBinders,
        VExpr.liftTelN_length],
    Nat.zero_add]
  apply congrArg (VExpr.forallN _)
  rw [VExpr.liftN_appN, List.map_append, List.map_map]
  show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
  congr 1
  · rw [show
      (VExpr.bvar
        (d - 1 - r.targetType + m + 0 + r.binders.length)).liftN
          p r.binders.length =
        .bvar (d - 1 - r.targetType + m + p + r.binders.length) from by
      simp only [VExpr.liftN]
      rw [liftVar_le (by omega)]
      congr 1
      ac_rfl]
  · congr 1
    · apply List.map_congr_left
      intro e _
      simp only [Function.comp_apply, Nat.add_zero]
      rw [VExpr.liftN'_liftN_hi]
    · congr 1
      simp only [Nat.add_zero, VExpr.liftN_appN]
      rw [show
          (VExpr.bvar
            (m - 1 - r.fieldIndex + r.binders.length)).liftN
              p r.binders.length =
            .bvar (m - 1 - r.fieldIndex + p + r.binders.length) from by
          simp only [VExpr.liftN]
          rw [liftVar_le (by omega)]
          congr 1
          omega,
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]

/-- Lifting a base mutual minor IH through all constructor minors yields the
rule-context normal form. -/
theorem BlockGenerationChecked.blockMinorIH_zero_lift_ruleIH
    (d : Nat) (r : RecArg) (m k : Nat) (hj : r.fieldIndex < m) :
    (BlockGenerationChecked.blockMinorIH d m 0 r).liftN k m =
      BlockGenerationChecked.blockRuleIH d k m r := by
  simp only [BlockGenerationChecked.blockMinorIH,
    BlockGenerationChecked.blockRuleIH,
    BlockGenerationChecked.blockMinorBinders,
    BlockGenerationChecked.blockRuleBinders,
    VExpr.liftN_forallN, VExpr.liftTelN_length, Nat.add_zero]
  congr 1
  · rw [show m = r.fieldIndex + (m-r.fieldIndex) by omega]
    rw [show r.fieldIndex + (m-r.fieldIndex) - r.fieldIndex =
      m-r.fieldIndex by omega]
    rw [VExpr.liftTelN_liftN_midN r.binders d k
      (m-r.fieldIndex) (Nat.zero_le _)]
  · congr 1
    rw [VExpr.liftN_appN, List.map_append, List.map_map]
    show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
    congr 1
    · simp only [VExpr.liftN]
      rw [liftVar_le (by omega)]
      congr 1
      ac_rfl
    · congr 1
      · apply List.map_congr_left
        intro e _
        simp only [Function.comp_apply]
        rw [show m + r.binders.length =
            (r.fieldIndex+r.binders.length) + (m-r.fieldIndex) by omega,
          VExpr.liftN_liftN_midN e d k (m-r.fieldIndex) (by omega)]
      · congr 1
        simp only [VExpr.liftN_appN]
        rw [show
            (VExpr.bvar
              (m - 1 - r.fieldIndex + r.binders.length)).liftN
                k (m+r.binders.length) =
              .bvar (m - 1 - r.fieldIndex + r.binders.length) from by
            simp only [VExpr.liftN]
            rw [liftVar_lt (by omega)],
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]

/-- General mutual minor-IH normalization after `p` earlier hypotheses. -/
theorem BlockGenerationChecked.blockMinorIH_lift_ruleIH
    (d : Nat) (r : RecArg) (m k p : Nat)
    (hj : r.fieldIndex < m) :
    (BlockGenerationChecked.blockMinorIH d m p r).liftN k (m+p) =
      (BlockGenerationChecked.blockRuleIH d k m r).liftN p := by
  rw [BlockGenerationChecked.blockMinorIH_shift d r m p hj]
  rw [← VExpr.liftN_liftN_comm
    (BlockGenerationChecked.blockMinorIH d m 0 r)
    p k 0 m (Nat.zero_le _)]
  rw [BlockGenerationChecked.blockMinorIH_zero_lift_ruleIH d r m k hj]

theorem BlockGenerationChecked.blockRuleIHs_length (d k m : Nat) :
    ∀ (rs : List RecArg) (p : Nat),
      (BlockGenerationChecked.blockRuleIHs d k m rs p).length = rs.length
  | [], _ => rfl
  | _ :: rs, p => by
    simp [BlockGenerationChecked.blockRuleIHs,
      BlockGenerationChecked.blockRuleIHs_length d k m rs (p+1)]

/-- Lift the complete mutual minor-IH telescope into rule context. -/
theorem BlockGenerationChecked.blockIHs_liftN (d m k : Nat) :
    ∀ (rs : List RecArg),
    (∀ r ∈ rs, r.fieldIndex < m) → ∀ (p : Nat) (X : VExpr),
    (VExpr.forallN
      (BlockGenerationChecked.blockIHsFromRecArgs d m rs p) X).liftN
        k (m+p) =
      VExpr.forallN
        (BlockGenerationChecked.blockRuleIHs d k m rs p)
        (X.liftN k (m+p+rs.length))
  | [], _, _, _ => rfl
  | r :: rs, hm, p, X => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · exact BlockGenerationChecked.blockMinorIH_lift_ruleIH
        d r m k p (hm r (.head _))
    · rw [show m+p+1 = m+(p+1) by omega,
        BlockGenerationChecked.blockIHs_liftN d m k rs
          (fun q hq => hm q (.tail _ hq)) (p+1) X,
        show m+(p+1)+rs.length =
          m+p+(r :: rs).length from by simp; omega]

theorem BlockGenerationChecked.blockIHs_liftN'
    (d m k : Nat) (rs : List RecArg)
    (hm : ∀ r ∈ rs, r.fieldIndex < m)
    (p : Nat) (X : VExpr) {cut : Nat} (hcut : cut = m+p) :
    (VExpr.forallN
      (BlockGenerationChecked.blockIHsFromRecArgs d m rs p) X).liftN
        k cut =
      VExpr.forallN
        (BlockGenerationChecked.blockRuleIHs d k m rs p)
        (X.liftN k (m+p+rs.length)) := by
  rw [hcut]
  exact BlockGenerationChecked.blockIHs_liftN d m k rs hm p X

theorem BlockGenerationChecked.blockRuleIHs_liftN1 (d k m : Nat) :
    ∀ (rs : List RecArg) (p c : Nat), c ≤ p → ∀ (X : VExpr),
    VExpr.forallN
      (BlockGenerationChecked.blockRuleIHs d k m rs (p+1))
      (X.liftN 1 (c+rs.length)) =
      (VExpr.forallN
        (BlockGenerationChecked.blockRuleIHs d k m rs p) X).liftN 1 c
  | [], p, c, _, X => by
    simp [BlockGenerationChecked.blockRuleIHs, VExpr.forallN]
  | r :: rs, p, c, hc, X => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN'_liftN' (Nat.zero_le _) hc]
    · rw [show c+(r :: rs).length = (c+1)+rs.length from by
          simp
          omega]
      exact BlockGenerationChecked.blockRuleIHs_liftN1
        d k m rs (p+1) (c+1) (by omega) X

/-- Consume one routed recursive-call term for every mutual rule IH. -/
theorem hasType_appN_blockRuleIHs
    {source : VInductDecl} {gen : BlockGenerationChecked source}
    {env : VEnv} {Γ : List VExpr} {d m k : Nat}
    {argOf : RecArg → VExpr} {Dfin : VExpr} :
    ∀ {rs : List RecArg} {g : VExpr},
    (∀ r ∈ rs, env.HasType gen.recUvars Γ (argOf r)
      (BlockGenerationChecked.blockRuleIH d k m r)) →
    env.HasType gen.recUvars Γ g
      (VExpr.forallN
        (BlockGenerationChecked.blockRuleIHs d k m rs 0)
        (Dfin.liftN rs.length)) →
    env.HasType gen.recUvars Γ (g.appN (rs.map argOf)) Dfin
  | [], g, _, hg => by
    simpa [BlockGenerationChecked.blockRuleIHs] using hg
  | r :: rs, g, hargs, hg => by
    have happ := VEnv.HasType.app hg (by
      simpa [BlockGenerationChecked.blockRuleIHs] using
        hargs r (.head _))
    simp only [List.length_cons] at happ
    rw [show Dfin.liftN (rs.length+1) =
        (Dfin.liftN rs.length).liftN 1 (0+rs.length) from by
          rw [Nat.zero_add,
            VExpr.liftN'_liftN' (Nat.zero_le _) (by omega)],
      BlockGenerationChecked.blockRuleIHs_liftN1
        d k m rs 0 0 (Nat.le_refl _) (Dfin.liftN rs.length),
      VExpr.inst_liftN1] at happ
    exact hasType_appN_blockRuleIHs
      (rs := rs) (fun q hq => hargs q (.tail _ hq)) happ

theorem BlockGenerationChecked.minorTypesAux_length
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    ∀ (constructors : List NormalizedBlockCtor) (i : Nat),
      (gen.minorTypesAux constructors i).length = constructors.length
  | [], _ => rfl
  | _ :: constructors, i => by
    simp [BlockGenerationChecked.minorTypesAux,
      gen.minorTypesAux_length constructors (i + 1)]

theorem BlockGenerationChecked.minorTypes_length
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    gen.minorTypes.length = gen.minorCount := by
  simpa [BlockGenerationChecked.minorTypes] using
    gen.minorTypesAux_length gen.flatCtors 0

/-- Positional lookup through the progressively weakened flattened mutual
minor telescope. -/
theorem BlockGenerationChecked.minorTypesAux_getElem?
    {source : VInductDecl} (gen : BlockGenerationChecked source) :
    ∀ (constructors : List NormalizedBlockCtor) (i q : Nat),
      (gen.minorTypesAux constructors i)[q]? =
        constructors[q]?.map fun constructor =>
          (gen.minorType constructor).liftN (i+q)
  | [], _, q => by simp [BlockGenerationChecked.minorTypesAux]
  | _ :: _, _, 0 => by simp [BlockGenerationChecked.minorTypesAux]
  | _ :: constructors, i, q+1 => by
    simp only [BlockGenerationChecked.minorTypesAux,
      List.getElem?_cons_succ]
    rw [gen.minorTypesAux_getElem? constructors (i+1) q,
      show i+1+q = i+(q+1) by omega]

namespace BlockGenerationEnv

variable {source : VInductDecl} {gen : BlockGenerationChecked source}
  {env : VEnv} (S : BlockGenerationEnv gen env)
include S

theorem paramsTel_onTel :
    env.OnTel gen.recUvars [] gen.paramsTel := by
  have h := S.generationParams_defeq.raw_onTel.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  simpa [BlockGenerationChecked.paramsTel] using h

theorem motiveTypesAux_onTel
    (families : List NormalizedFamily)
    (hsub : ∀ family ∈ families, family ∈ gen.families)
    (Δ : List VExpr) (i : Nat) (hΔ : Δ.length = i) :
    env.OnTel gen.recUvars (Δ ++ gen.paramsTel.reverse)
      (gen.motiveTypesAux families i) := by
  induction families generalizing Δ i with
  | nil => trivial
  | cons family families ih =>
    exact ⟨by
      rw [← hΔ]
      exact (S.motive_isType (hsub family (.head _))).weakN S.ord
        (.zero Δ),
    ih (fun family hfamily => hsub family (.tail _ hfamily))
      (_ :: Δ) (i + 1) (by simp [hΔ])⟩

theorem motiveTypes_onTel :
    env.OnTel gen.recUvars gen.paramsTel.reverse gen.motiveTypes := by
  simpa [BlockGenerationChecked.motiveTypes] using
    motiveTypesAux_onTel S gen.families (fun _ h => h) [] 0 rfl

/-- Constructor fields instantiated for recursor generation are well typed
over the generation parameter telescope. -/
theorem generationFields_onTel_rec
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) :
    env.OnTel gen.recUvars gen.paramsTel.reverse
      (constructor.ctor.fieldsR source.uvars source.nparams
        gen.elimination) := by
  have hemitted := (S.ctorWF constructor hconstructor).rawEmitted_onTel
  have hfields₀ := (VEnv.OnTel.of_append
    (As := gen.block.checked.params) hemitted).2
  have hfields₁ := hfields₀.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hfieldsChecked : env.OnTel gen.recUvars
      (gen.block.checked.params.map
        (VExpr.instL gen.sourceLevels)).reverse
      (constructor.ctor.fieldsR source.uvars source.nparams
        gen.elimination) := by
    simpa [NormalizedCtor.fieldsR, List.map_reverse] using hfields₁
  exact hfieldsChecked.defeqDFC S.ord
    (S.generationParams_ctx_rec.symm S.ord)

/-- The checked and generation parameter contexts stay definitionally equal
beneath every instantiated constructor-field prefix. -/
theorem generationFieldPrefix_ctx_rec
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) (j : Nat) :
    env.IsDefEqCtx gen.recUvars []
      ((constructor.ctor.fieldsR source.uvars source.nparams
        gen.elimination |>.take j).reverse ++ gen.paramsTel.reverse)
      ((constructor.ctor.fieldsR source.uvars source.nparams
        gen.elimination |>.take j).reverse ++
        (gen.block.checked.params.map
          (VExpr.instL gen.sourceLevels)).reverse) := by
  have hfields := S.generationFields_onTel_rec hconstructor
  rw [← List.take_append_drop j
    (constructor.ctor.fieldsR source.uvars source.nparams
      gen.elimination)] at hfields
  exact (hfields.of_append.1).extendDefEqCtx
    S.generationParams_ctx_rec

/-- Definitionally equal raw/view contexts at any mutual constructor-field
prefix. -/
theorem emittedPrefix_ctx {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) (j : Nat) :
    env.IsDefEqCtx source.uvars []
      ((constructor.ctor.rawFields source.nparams |>.take j).reverse ++
        gen.block.checked.params.reverse)
      ((constructor.ctor.view.fields.take j).reverse ++
        gen.block.checked.params.reverse) := by
  have h := ((S.ctorWF constructor hconstructor).emittedTel.take
    (source.nparams + j)).ctx
  have hviewLen :
      gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hraw :
      (gen.block.checked.params ++
        constructor.ctor.rawFields source.nparams).take
          (source.nparams + j) =
        gen.block.checked.params ++
          (constructor.ctor.rawFields source.nparams).take j := by
    rw [← hviewLen]
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  have hview :
      (gen.block.checked.params ++ constructor.ctor.view.fields).take
          (source.nparams + j) =
        gen.block.checked.params ++
          constructor.ctor.view.fields.take j := by
    rw [← hviewLen]
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  simp only [NormalizedBlockCtor.emittedBinders,
    NormalizedBlockCtor.viewBinders] at h
  rw [hraw, hview] at h
  simpa [List.reverse_append] using h

/-- Pointwise raw/view field-domain equality for a mutual constructor, in
the preceding raw context. -/
theorem emittedField_defeq {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    {j : Nat} {B B' : VExpr}
    (hB : (constructor.ctor.rawFields source.nparams)[j]? = some B)
    (hB' : constructor.ctor.view.fields[j]? = some B') :
    ∃ u, env.IsDefEq source.uvars
      ((constructor.ctor.rawFields source.nparams |>.take j).reverse ++
        gen.block.checked.params.reverse)
      B B' (.sort u) := by
  have hviewLen :
      gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hraw :
      getElem?
        (gen.block.checked.params ++
          constructor.ctor.rawFields source.nparams)
        (source.nparams + j) = some B := by
    rw [List.getElem?_append_right (by rw [hviewLen]; omega), hviewLen]
    simpa using hB
  have hview :
      getElem?
        (gen.block.checked.params ++ constructor.ctor.view.fields)
        (source.nparams + j) = some B' := by
    rw [List.getElem?_append_right (by rw [hviewLen]; omega), hviewLen]
    simpa using hB'
  obtain ⟨u, h⟩ :=
    (S.ctorWF constructor hconstructor).emittedTel.getElem? hraw hview
  have htake :
      (gen.block.checked.params ++
        constructor.ctor.rawFields source.nparams).take
          (source.nparams + j) =
        gen.block.checked.params ++
          (constructor.ctor.rawFields source.nparams).take j := by
    rw [← hviewLen]
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  simp only [NormalizedBlockCtor.emittedBinders] at h
  rw [htake, List.reverse_append] at h
  exact ⟨u, by simpa using h⟩

/-- The generated and checked index telescopes of every family are
definitionally equal after universe instantiation. -/
theorem familyIndexTel_defeq_rec {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.TelDefEq gen.recUvars gen.paramsTel.reverse
      (gen.idxTel family)
      (family.view.indices.map (VExpr.instL gen.sourceLevels)) := by
  have h := (S.familyWF family hfamily).familyTel.drop source.nparams
  have hrawTake :
      (family.rawParams source.nparams ++
        family.rawIndices source.nparams).take source.nparams =
        family.rawParams source.nparams := by
    let Ps := family.rawParams source.nparams
    let Is := family.rawIndices source.nparams
    have hlen : Ps.length = source.nparams :=
      (gen.shape.2.2.2.2 family hfamily).2.2.1
    change (Ps ++ Is).take source.nparams = Ps
    rw [← hlen, List.take_append, List.take_length]
    simp
  have hrawDrop :
      (family.rawParams source.nparams ++
        family.rawIndices source.nparams).drop source.nparams =
        family.rawIndices source.nparams := by
    let Ps := family.rawParams source.nparams
    let Is := family.rawIndices source.nparams
    have hlen : Ps.length = source.nparams :=
      (gen.shape.2.2.2.2 family hfamily).2.2.1
    change (Ps ++ Is).drop source.nparams = Is
    rw [← hlen, List.drop_append]
    simp
  have hviewLen : gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hviewDrop :
      (gen.block.checked.params ++ family.view.indices).drop
          source.nparams = family.view.indices := by
    rw [← hviewLen, List.drop_append]
    simp
  rw [hrawTake, hrawDrop, hviewDrop] at h
  simp only [List.append_nil] at h
  have hparams : env.IsDefEqCtx source.uvars []
      (family.rawParams source.nparams).reverse
      gen.block.checked.params.reverse := by
    simpa using (S.rawParams_defeq hfamily).ctx
  have hemitted := h.defeqDFC S.ord hparams
  have hgeneration := hemitted.defeqDFC S.ord
    (S.generationParams_ctx.symm S.ord)
  have hrec := hgeneration.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  simpa [BlockGenerationChecked.paramsTel,
    BlockGenerationChecked.idxTel, List.map_reverse] using hrec

/-- Transport the analyzer's recursive-argument certificate from checked
source syntax to the generated field and target-family index telescopes, then
weaken it beneath arbitrary motive/local prefixes. -/
theorem recArg_transport
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    {r₀ : RecArg} {family : NormalizedFamily}
    (hfamily : family ∈ gen.families)
    (hsem : r₀.WF source.uvars env gen.validated.resultLevel
      family.view.indices
      ((constructor.ctor.view.fields.take r₀.fieldIndex).reverse ++
        gen.block.checked.params.reverse))
    (hjlt : r₀.fieldIndex < constructor.ctor.view.fields.length)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    let r := r₀.instL gen.sourceLevels
    let As := VExpr.liftTelN d
      (VExpr.liftTelN g r.binders r.fieldIndex) 0
    env.OnTel gen.recUvars
        (As₂ ++ ((VExpr.liftTelN g
          ((constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination).take r.fieldIndex) 0).reverse ++
          (mid ++ gen.paramsTel.reverse))) As ∧
      env.SpineWF gen.recUvars
        (As.reverse ++
          (As₂ ++ ((VExpr.liftTelN g
            ((constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).take r.fieldIndex) 0).reverse ++
            (mid ++ gen.paramsTel.reverse))))
        (VExpr.forallN
          (VExpr.liftTelN
            (r.fieldIndex + r.binders.length + g + d)
            (gen.idxTel family) 0)
          (.sort (gen.validated.resultLevel.inst gen.sourceLevels)))
        (r.indices.map fun e =>
          (e.liftN g (r.fieldIndex + r.binders.length)).liftN d
            r.binders.length)
        (.sort (gen.validated.resultLevel.inst gen.sourceLevels)) := by
  dsimp only
  let ls := gen.sourceLevels
  have hjraw :
      r₀.fieldIndex <
        (constructor.ctor.rawFields source.nparams).length := by
    rw [gen.flatCtor_fields_length hconstructor]
    exact hjlt
  have hraw := hsem.defeqDFC S.ord
    ((S.emittedPrefix_ctx hconstructor r₀.fieldIndex).symm S.ord)
  have htel₁ := hraw.1.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hsp₁ := hraw.2.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have htelChecked : env.OnTel gen.recUvars
      ((constructor.ctor.fieldsR source.uvars source.nparams
        gen.elimination |>.take r₀.fieldIndex).reverse ++
        (gen.block.checked.params.map (VExpr.instL ls)).reverse)
      (r₀.binders.map (VExpr.instL ls)) := by
    simpa [NormalizedCtor.fieldsR, List.map_append,
      List.map_reverse, List.map_take] using htel₁
  have hspChecked : env.SpineWF gen.recUvars
      ((r₀.binders.map (VExpr.instL ls)).reverse ++
        ((constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination |>.take r₀.fieldIndex).reverse ++
          (gen.block.checked.params.map (VExpr.instL ls)).reverse))
      (VExpr.instL ls
        (VExpr.forallN
          (VExpr.liftTelN
            (r₀.fieldIndex + r₀.binders.length)
            family.view.indices 0)
          (.sort gen.validated.resultLevel)))
      (r₀.indices.map (VExpr.instL ls))
      (VExpr.instL ls (.sort gen.validated.resultLevel)) := by
    simpa [List.map_append, List.map_reverse,
      NormalizedCtor.fieldsR, List.map_take] using hsp₁
  have hprefix :=
    S.generationFieldPrefix_ctx_rec hconstructor r₀.fieldIndex
  have htelGeneration := htelChecked.defeqDFC S.ord
    (hprefix.symm S.ord)
  have hfull := htelGeneration.extendDefEqCtx hprefix
  have hspGeneration := hspChecked.defeqDFC S.ord (hfull.symm S.ord)
  simp only [VExpr.instL_forallN,
    VExpr.liftTelN_instL] at htelGeneration hspGeneration
  have hjlen :
      ((constructor.ctor.fieldsR source.uvars source.nparams
        gen.elimination).take r₀.fieldIndex).length = r₀.fieldIndex := by
    simp only [NormalizedCtor.fieldsR, List.length_take,
      List.length_map]
    omega
  have hidxField := (S.familyIndexTel_defeq_rec hfamily).weakN S.ord
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse)
      ((constructor.ctor.fieldsR source.uvars source.nparams
        gen.elimination).take r₀.fieldIndex).reverse)
  rw [List.length_reverse, hjlen] at hidxField
  have hidxPrivate := hidxField.weakN S.ord
    (Ctx.LiftN.zero
      (Γ := ((constructor.ctor.fieldsR source.uvars source.nparams
        gen.elimination).take r₀.fieldIndex).reverse ++
        gen.paramsTel.reverse)
      (r₀.binders.map (VExpr.instL ls)).reverse)
  simp only [List.length_reverse, List.length_map] at hidxPrivate
  rw [VExpr.liftTelN_liftTelN,
    VExpr.liftTelN_liftTelN] at hidxPrivate
  have hidxLenView := hsem.2.forallN_sort_length
  simp only [VExpr.liftTelN_length] at hidxLenView
  have hidxLen :
      (r₀.indices.map (VExpr.instL ls)).length =
        (VExpr.liftTelN
          (r₀.fieldIndex + r₀.binders.length)
          (gen.idxTel family) 0).length := by
    simp only [List.length_map, VExpr.liftTelN_length,
      BlockGenerationChecked.idxTel]
    exact hidxLenView.trans
      (gen.shape.2.2.2.2 family hfamily).2.2.2.1.symm
  have hspRaw :=
    hidxPrivate.spine_sort S.ord hspGeneration hidxLen
  have W₁ := Ctx.LiftN.consTel (n := mid.length)
    ((constructor.ctor.fieldsR source.uvars source.nparams
      gen.elimination).take r₀.fieldIndex)
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [hjlen, Nat.add_zero] at W₁
  have htel₂ := htelGeneration.weakN S.ord W₁
  have hsp₂ := hspRaw.weakN S.ord
    (Ctx.LiftN.consTel
      (r₀.binders.map (VExpr.instL ls)) W₁)
  rw [hg] at htel₂ hsp₂
  have W₂ := Ctx.LiftN.zero
    (Γ := (VExpr.liftTelN g
        ((constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).take r₀.fieldIndex) 0).reverse ++
      (mid ++ gen.paramsTel.reverse)) As₂ (h := hd)
  have htel₃ := htel₂.weakN S.ord W₂
  have hsp₃ := hsp₂.weakN S.ord
    (Ctx.LiftN.consTel
      (VExpr.liftTelN g
        (r₀.binders.map (VExpr.instL ls)) r₀.fieldIndex) W₂)
  refine ⟨?_, ?_⟩
  · simpa [ls, RecArg.instL, List.append_assoc] using htel₃
  · simp only [List.length_map, VExpr.liftTelN_length,
      Nat.add_zero] at hsp₃
    rw [VExpr.liftN_forallN, VExpr.liftN_forallN,
      VExpr.liftTelN_liftTelN_hi'
        (r₀.fieldIndex + r₀.binders.length) g _ 0 (by omega),
      VExpr.liftTelN_liftTelN_mid
        (r₀.fieldIndex + r₀.binders.length + g) d _ 0
        r₀.binders.length (Nat.zero_le _) (by omega)] at hsp₃
    rw [show r₀.binders.length + r₀.fieldIndex =
      r₀.fieldIndex + r₀.binders.length from Nat.add_comm _ _] at hsp₃
    simpa [ls, RecArg.instL, VExpr.instL, VExpr.liftN,
      List.map_map, Function.comp_def, List.append_assoc] using hsp₃

theorem recArgMinor_isType {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) {r : RecArg}
    (hrmem : r ∈ constructor.ctor.recArgsR source.uvars gen.elimination)
    (Δ : List VExpr) (p : Nat) (hΔ : Δ.length = p) :
    env.IsType gen.recUvars
      (Δ ++
        (VExpr.liftTelN gen.familyCount
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination) 0).reverse ++
        (gen.motiveTypes.reverse ++ gen.paramsTel.reverse))
      (BlockGenerationChecked.blockMinorIH gen.familyCount
        (constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).length p r) := by
  obtain ⟨r₀, hr₀, rfl⟩ :=
    NormalizedCtor.recArgsR_mem hrmem
  obtain ⟨family, hfamily, hord, ⟨Bview, hBview, hshape⟩, hsem⟩ :=
    (S.ctorWF constructor hconstructor).recursive r₀ hr₀
  let ls := gen.sourceLevels
  let r := r₀.instL ls
  let d := gen.familyCount
  let Bs := constructor.ctor.fieldsR source.uvars source.nparams
    gen.elimination
  let m := Bs.length
  let j := r₀.fieldIndex
  let Fs := VExpr.liftTelN d Bs 0
  let As := BlockGenerationChecked.blockMinorBinders d m p r
  let idxs := r.indices.map fun e =>
    (e.liftN d (r.fieldIndex + r.binders.length)).liftN
      (m - r.fieldIndex + p) r.binders.length
  let Γ := Δ ++ Fs.reverse ++
    (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)
  let q := family.view.ordinal
  let K := d - 1 - r.targetType + m + p + r.binders.length
  have hjview : r₀.fieldIndex < constructor.ctor.view.fields.length :=
    (List.getElem?_eq_some_iff.1 hBview).1
  have hjm : j < m := by
    have hfields := gen.flatCtor_fields_length hconstructor
    simp only [j, m, Bs, NormalizedCtor.fieldsR_length]
    omega
  have hjraw :
      r₀.fieldIndex <
        (constructor.ctor.rawFields source.nparams).length := by
    simpa [j, m, Bs, NormalizedCtor.fieldsR_length] using hjm
  let Braw :=
    (constructor.ctor.rawFields source.nparams)[r₀.fieldIndex]
  have hBraw :
      (constructor.ctor.rawFields source.nparams)[r₀.fieldIndex]? =
        some Braw :=
    List.getElem?_eq_getElem hjraw
  have hd : gen.motiveTypes.reverse.length = d := by
    simp [d, gen.motiveTypes_length]
  have hd' : gen.motiveTypes.length = d := by
    simpa using hd
  have hFsLen : Fs.length = m := by
    simp [Fs, m, VExpr.liftTelN_length]
  have hstackLen :
      (Δ ++ (Fs.drop j).reverse).length = m - j + p := by
    simp only [List.length_append, List.length_reverse,
      List.length_drop, hFsLen, hΔ]
    omega
  have ht := S.recArg_transport hconstructor hfamily hsem hjview
    gen.motiveTypes.reverse hd
    (Δ ++ (Fs.drop j).reverse) hstackLen
  simp only [RecArg.instL] at ht
  have hctx :
      (Δ ++ (Fs.drop j).reverse) ++
          ((VExpr.liftTelN d (Bs.take j) 0).reverse ++
            (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)) = Γ := by
    dsimp only [Γ, Fs]
    rw [← VExpr.liftTelN_take, List.append_assoc,
      ← List.append_assoc
        ((VExpr.liftTelN d Bs 0).drop j).reverse,
      ← List.reverse_append, List.take_append_drop,
      ← List.append_assoc]
  dsimp only [j] at ht hctx
  have htel : env.OnTel gen.recUvars Γ As := by
    rw [hctx] at ht
    simpa [r, As, m, j, Bs, RecArg.instL,
      BlockGenerationChecked.blockMinorBinders] using ht.1
  have hsp : env.SpineWF gen.recUvars
      (As.reverse ++ Γ)
      (VExpr.forallN
        (VExpr.liftTelN
          (m + p + r.binders.length + d) (gen.idxTel family) 0)
        (.sort (gen.validated.resultLevel.inst ls)))
      idxs
      (.sort (gen.validated.resultLevel.inst ls)) := by
    rw [hctx] at ht
    simpa [r, As, idxs, m, j, Bs, d, ls, RecArg.instL,
      BlockGenerationChecked.blockMinorBinders,
      List.append_assoc,
      show j + r₀.binders.length + d + (m - j + p) =
        m + p + r₀.binders.length + d from by omega] using ht.2
  have hF : Γ[m - 1 - j + p]? =
      some ((Braw.instL ls).liftN d j) := by
    dsimp only [Γ, Fs]
    rw [getElem?_stack_mid Δ
        (VExpr.liftTelN d Bs 0).reverse
        (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)
        (i := m - 1 - j + p) (by rw [hΔ]; omega)
        (by simp only [hΔ, List.length_reverse,
          VExpr.liftTelN_length]; omega),
      show m - 1 - j + p - Δ.length = m - 1 - j from by
        rw [hΔ]
        omega,
      List.getElem?_reverse (by rw [hFsLen]; omega),
      VExpr.liftTelN_length,
      show m - 1 - (m - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?,
      NormalizedCtor.fieldsR_getElem?, hBraw]
    simp [ls]
  have hlu := Lookup.of_getElem? hF
  rw [show m - 1 - j + p + 1 = m - j + p from by omega] at hlu
  dsimp only [j, r] at hlu
  have hf0 := VEnv.HasType.bvar
    (env := env) (U := gen.recUvars) hlu
  obtain ⟨u, hdom₀⟩ :=
    S.emittedField_defeq hconstructor hBraw hBview
  have hdom₁ := hdom₀.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hdomChecked : env.IsDefEq gen.recUvars
      ((constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination |>.take r₀.fieldIndex).reverse ++
        (gen.block.checked.params.map (VExpr.instL ls)).reverse)
      (Braw.instL ls) (Bview.instL ls) ((VExpr.sort u).instL ls) := by
    simpa [NormalizedCtor.fieldsR, List.map_append,
      List.map_reverse, List.map_take] using hdom₁
  have hprefix :=
    S.generationFieldPrefix_ctx_rec hconstructor r₀.fieldIndex
  have hdomGeneration := hdomChecked.defeqDFC S.ord
    (hprefix.symm S.ord)
  have hjlen : (Bs.take r₀.fieldIndex).length =
      r₀.fieldIndex := by
    simp only [Bs, NormalizedCtor.fieldsR,
      List.length_take, List.length_map]
    omega
  have Wmid := Ctx.LiftN.consTel (n := d)
    (Bs.take r₀.fieldIndex)
    (Ctx.LiftN.zero (n := d) (Γ := gen.paramsTel.reverse)
      gen.motiveTypes.reverse (h := hd))
  rw [hjlen, Nat.add_zero] at Wmid
  have hdom₂ := hdomGeneration.weakN S.ord Wmid
  have Wstack := Ctx.LiftN.zero
    (Γ := (VExpr.liftTelN d (Bs.take j) 0).reverse ++
      (gen.motiveTypes.reverse ++ gen.paramsTel.reverse))
    (Δ ++ (Fs.drop j).reverse) (h := hstackLen)
  have hdom₃ := hdom₂.weakN S.ord Wstack
  rw [hctx] at hdom₃
  have hfView := hdom₃.defeq hf0
  have hfield := blockMinor_fieldType_of_eq hshape d m p
    (by simpa [j] using hjm) gen.elimination
  simp only [RecArg.instL] at hfield
  rw [hfield] at hfView
  have hf := hfView.weakN S.ord
    (Ctx.LiftN.zero (Γ := Γ) As.reverse)
  have hmajor := VEnv.HasType.appN_selfSpine
    (env := env) (U := gen.recUvars)
    (As := As)
    (B := VExpr.appN
      (.const family.raw.name ls)
      (VExpr.bvarRevRange
        (m + p + r.binders.length + d) source.nparams ++ idxs))
    (Δ := []) (Γ := Γ) (by
      simpa [As, r, idxs, j, d, ls, RecArg.instL,
        List.length_reverse, List.map_map,
        Function.comp_def] using hf)
  simp only [List.length_nil, VExpr.liftN_zero,
    List.nil_append] at hmajor
  have hAsLen : As.length = r.binders.length := by
    simp [As, BlockGenerationChecked.blockMinorBinders,
      VExpr.liftTelN_length]
  have hmajor' : env.HasType gen.recUvars (As.reverse ++ Γ)
      ((VExpr.bvar (m - 1 - r.fieldIndex + p + As.length)).appN
        (VExpr.bvarRevRange 0 As.length))
      (VExpr.appN
        (.const family.raw.name ls)
        (VExpr.bvarRevRange
          (m + p + r.binders.length + d) source.nparams ++ idxs)) := by
    simpa [As, d, r, RecArg.instL,
      BlockGenerationChecked.blockMinorBinders,
      VExpr.liftN, liftVar_le, Nat.add_comm] using hmajor
  rw [hAsLen] at hmajor'
  have hq : q < d := by
    simpa [q, d] using gen.family_ordinal_lt hfamily
  have hmot : gen.motiveTypes.reverse[d - 1 - q]? =
      some ((gen.motiveType family).liftN q) := by
    rw [List.getElem?_reverse (by rw [hd']; omega),
      show gen.motiveTypes.length - 1 - (d - 1 - q) = q from by
        rw [hd']
        omega,
      gen.motiveTypes_getElem?_ordinal hfamily]
  have hM0 := getElem?_rstack_mid
    (As.reverse ++ (Δ ++ Fs.reverse))
    gen.motiveTypes.reverse gen.paramsTel.reverse
    (i := K)
    (by
      simp only [List.length_append, List.length_reverse,
        hAsLen, hΔ, hFsLen]
      dsimp only [K, q, d, r]
      simp only [RecArg.instL]
      omega)
    (by
      simp only [List.length_append, List.length_reverse,
        hAsLen, hΔ, hFsLen, hd]
      dsimp only [K, q, d, r]
      simp only [RecArg.instL]
      omega)
  have hdiff :
      K - (As.reverse ++ (Δ ++ Fs.reverse)).length = d - 1 - q := by
    simp only [List.length_append, List.length_reverse,
      hAsLen, hΔ, hFsLen]
    dsimp only [K, q, d, r]
    simp only [RecArg.instL]
    omega
  rw [hdiff, hmot] at hM0
  have hMget : (As.reverse ++ Γ)[K]? =
      some ((gen.motiveType family).liftN q) := by
    simpa [Γ, List.append_assoc] using hM0
  have hMraw := VEnv.HasType.bvar
    (env := env) (U := gen.recUvars)
    (Lookup.of_getElem? hMget)
  have hM : env.HasType gen.recUvars (As.reverse ++ Γ) (.bvar K)
      ((gen.motiveType family).liftN (q + K + 1)) := by
    simpa [VExpr.liftN_liftN, Nat.add_assoc] using hMraw
  have hlen : idxs.length = (gen.idxTel family).length := by
    simp only [idxs, List.length_map,
      BlockGenerationChecked.idxTel]
    have hidx := hsem.2.forallN_sort_length
    simp only [VExpr.liftTelN_length] at hidx
    simpa [r, RecArg.instL] using hidx.trans
      (gen.shape.2.2.2.2 family hfamily).2.2.2.1.symm
  have hshift : q + K + 1 = m + p + r.binders.length + d := by
    dsimp only [q, K, d, r]
    simp only [RecArg.instL]
    omega
  have hbody := gen.motiveVarApp_hasType family
    (q := q) (K := K)
    hM (by simpa [hshift] using hsp) hlen
      (by simpa [hshift] using hmajor')
  refine VEnv.IsType.forallN htel ⟨gen.motiveLevel, ?_⟩
  simpa [BlockGenerationChecked.blockMinorIH,
    r, As, idxs, m, d, K, q, Γ, Fs, Bs,
    List.append_assoc] using hbody

/-- The global mutual-IH telescope for one constructor is well formed at
every recursive suffix. -/
theorem ihs_onTel {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) :
    ∀ (rsSuf : List RecArg),
    (∀ r ∈ rsSuf,
      r ∈ constructor.ctor.recArgsR source.uvars gen.elimination) →
    ∀ (Δ : List VExpr) (p : Nat), Δ.length = p →
    env.OnTel gen.recUvars
      (Δ ++
        (VExpr.liftTelN gen.familyCount
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination) 0).reverse ++
        (gen.motiveTypes.reverse ++ gen.paramsTel.reverse))
      (BlockGenerationChecked.blockIHsFromRecArgs gen.familyCount
        (constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).length rsSuf p)
  | [], _, _, _, _ => trivial
  | r :: rsSuf, hqs, Δ, p, hΔ =>
    ⟨S.recArgMinor_isType hconstructor
        (hqs r (.head _)) Δ p hΔ,
      BlockGenerationEnv.ihs_onTel hconstructor rsSuf
        (fun q hq => hqs q (.tail _ hq))
        (_ :: Δ) (p + 1) (by simp [hΔ])⟩

theorem viewResultIndices_length
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) :
    constructor.ctor.view.resultIndices.length =
      constructor.familyIndices.length := by
  have h := (S.ctorWF constructor hconstructor).resultSpine.forallN_sort_length
  simpa only [VExpr.liftTelN_length] using h

/-- Transport one mutual constructor's checked result spine to the selected
raw family-index telescope and through arbitrary middle/top binders. -/
theorem result_transport
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    {family : NormalizedFamily} (hfamily : family ∈ gen.families)
    (hindices : family.view.indices = constructor.familyIndices)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.SpineWF gen.recUvars
      (As₂ ++
        ((VExpr.liftTelN g
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination) 0).reverse ++
          (mid ++ gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          ((constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length + g + d)
          (gen.idxTel family) 0)
        (.sort (gen.validated.resultLevel.inst gen.sourceLevels)))
      ((constructor.ctor.resultIndicesR source.uvars gen.elimination).map
        fun e =>
          (e.liftN g
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length).liftN d)
      (.sort (gen.validated.resultLevel.inst gen.sourceLevels)) := by
  let ls := gen.sourceLevels
  have hview := (S.ctorWF constructor hconstructor).resultSpine
  rw [← hindices] at hview
  have hctx := (S.ctorWF constructor hconstructor).emittedTel.ctx
  simp only [NormalizedBlockCtor.emittedBinders,
    NormalizedBlockCtor.viewBinders, List.reverse_append,
    List.append_nil] at hctx
  have hraw := hview.defeqDFC S.ord (hctx.symm S.ord)
  have hfields := gen.flatCtor_fields_length hconstructor
  rw [← hfields] at hraw
  have h1 := hraw.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have h1Checked : env.SpineWF gen.recUvars
      ((constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).reverse ++
        (gen.block.checked.params.map (VExpr.instL ls)).reverse)
      (VExpr.instL ls
        (VExpr.forallN
          (VExpr.liftTelN
            (constructor.ctor.rawFields source.nparams).length
            family.view.indices 0)
          (.sort gen.validated.resultLevel)))
      (constructor.ctor.view.resultIndices.map (VExpr.instL ls))
      ((VExpr.sort gen.validated.resultLevel).instL ls) := by
    simpa [NormalizedCtor.fieldsR, List.map_append,
      List.map_reverse] using h1
  have hfieldsCtx :=
    (S.generationFields_onTel_rec hconstructor).extendDefEqCtx
      S.generationParams_ctx_rec
  have h1Generation := h1Checked.defeqDFC S.ord
    (hfieldsCtx.symm S.ord)
  rw [VExpr.instL_forallN, VExpr.liftTelN_instL] at h1Generation
  rw [← NormalizedCtor.fieldsR_length
    (source := source) (mode := gen.elimination) constructor.ctor] at h1Generation
  have hidx := (S.familyIndexTel_defeq_rec hfamily).weakN S.ord
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse)
      (constructor.ctor.fieldsR source.uvars source.nparams
        gen.elimination).reverse)
  rw [List.length_reverse] at hidx
  have hlen :
      (constructor.ctor.view.resultIndices.map (VExpr.instL ls)).length =
        (VExpr.liftTelN
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination).length
          (gen.idxTel family) 0).length := by
    simp only [List.length_map, VExpr.liftTelN_length,
      BlockGenerationChecked.idxTel]
    exact (S.viewResultIndices_length hconstructor).trans
      ((congrArg List.length hindices).symm.trans
        (gen.shape.2.2.2.2 family hfamily).2.2.2.1.symm)
  have h1Raw := hidx.spine_sort S.ord h1Generation hlen
  have W₁ := Ctx.LiftN.consTel (n := mid.length)
    (constructor.ctor.fieldsR source.uvars source.nparams
      gen.elimination)
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [Nat.add_zero] at W₁
  have h2 := h1Raw.weakN S.ord W₁
  rw [VExpr.liftN_forallN, hg] at h2
  have h3 := h2.weakN S.ord
    (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  rw [VExpr.liftN_forallN] at h3
  rw [VExpr.liftTelN_liftTelN_hi'
      (constructor.ctor.fieldsR source.uvars source.nparams
        gen.elimination).length g _ 0 (by omega),
    VExpr.liftTelN_liftTelN] at h3
  simpa [ls, NormalizedCtor.resultIndicesR,
    VExpr.instL, VExpr.liftN, List.map_map,
    Function.comp_def, List.append_assoc] using h3

/-- The raw mutual constructor applied to its emitted self-spine at source
universes. -/
theorem ctorApp_emitted_decl
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) :
    env.HasType source.uvars
      ((constructor.ctor.rawFields source.nparams).reverse ++
        gen.block.checked.params.reverse)
      (VExpr.appN
        (.const constructor.ctor.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (constructor.ctor.rawFields source.nparams).length
            source.nparams ++
          VExpr.bvarRevRange 0
            (constructor.ctor.rawFields source.nparams).length))
      (NormalizedBlockCtor.resultTarget gen constructor) := by
  let E := NormalizedBlockCtor.emittedBinders gen constructor
  let V := NormalizedBlockCtor.viewBinders gen constructor
  have hc : env.HasType source.uvars []
      (.const constructor.ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN
        (NormalizedBlockCtor.declaredBinders
          (source := source) constructor)
        (NormalizedBlockCtor.rawResult
          (source := source) constructor)) := by
    rw [NormalizedBlockCtor.declaredBinders,
      NormalizedBlockCtor.rawResult,
      ← constructor.ctor.rawType_eq]
    exact S.ctorConst_decl hconstructor
  obtain ⟨_, hdecl⟩ :=
    (S.ctorWF constructor hconstructor).declaredTel.forallN_defeq
      (by simpa using
        (S.ctorWF constructor hconstructor).declaredResult)
  have hview : env.HasType source.uvars []
      (.const constructor.ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN V
        (NormalizedBlockCtor.resultTarget gen constructor)) := by
    simpa [V] using hdecl.defeq hc
  have hresult : env.HasType source.uvars E.reverse
      (NormalizedBlockCtor.resultTarget gen constructor)
      (.sort gen.validated.resultLevel) := by
    simpa [E] using
      (S.ctorWF constructor hconstructor).emittedResult.hasType.2
  obtain ⟨_, hemit⟩ :=
    (S.ctorWF constructor hconstructor).emittedTel.forallN_defeq
      (by simpa [E, VEnv.HasType] using hresult)
  have hcE₀ : env.HasType source.uvars []
      (.const constructor.ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN E
        (NormalizedBlockCtor.resultTarget gen constructor)) := by
    exact hemit.defeq' (by simpa [V] using hview)
  have hclosed :
      (VExpr.forallN E
        (NormalizedBlockCtor.resultTarget gen constructor)).ClosedN 0 :=
    (hcE₀.closedN' S.ord.closed trivial).2.2
  have hcE : env.HasType source.uvars E.reverse
      (.const constructor.ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN E
        (NormalizedBlockCtor.resultTarget gen constructor)) :=
    hcE₀.weak0 S.ord
  have happ := VEnv.HasType.appN_selfSpine'
    (As := E)
    (B := NormalizedBlockCtor.resultTarget gen constructor)
    (Δ := []) (Γ := []) hclosed (by simpa using hcE)
  simp only [List.length_nil, VExpr.liftN_zero,
    List.nil_append, List.append_nil] at happ
  have hEctx :
      E.reverse =
        (constructor.ctor.rawFields source.nparams).reverse ++
          gen.block.checked.params.reverse := by
    simp [E, NormalizedBlockCtor.emittedBinders,
      List.reverse_append]
  have hElen :
      E.length =
        (constructor.ctor.rawFields source.nparams).length +
          source.nparams := by
    have hp : gen.block.checked.params.length = source.nparams :=
      gen.shape.2.1.symm.trans gen.shape.1
    simp [E, NormalizedBlockCtor.emittedBinders, hp]
    omega
  rw [hEctx, hElen,
    ← VExpr.bvarRevRange_append source.nparams
      (constructor.ctor.rawFields source.nparams).length] at happ
  exact happ

/-- The exact emitted mutual-constructor application in recursor universes,
retargeted to its owner family. -/
theorem ctorApp_emitted_rec
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    {family : NormalizedFamily}
    (hname : family.raw.name = constructor.familyName) :
    env.HasType gen.recUvars
      ((constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).reverse ++ gen.paramsTel.reverse)
      (VExpr.appN
        (.const constructor.ctor.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length source.nparams ++
          VExpr.bvarRevRange 0
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length))
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length source.nparams ++
          constructor.ctor.resultIndicesR source.uvars gen.elimination)) := by
  let ls := gen.sourceLevels
  have h := (S.ctorApp_emitted_decl hconstructor).instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hChecked : env.HasType gen.recUvars
      ((constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).reverse ++
        (gen.block.checked.params.map (VExpr.instL ls)).reverse)
      ((VExpr.appN
        (.const constructor.ctor.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (constructor.ctor.rawFields source.nparams).length
            source.nparams ++
          VExpr.bvarRevRange 0
            (constructor.ctor.rawFields source.nparams).length)).instL ls)
      ((NormalizedBlockCtor.resultTarget gen constructor).instL ls) := by
    simpa [NormalizedCtor.fieldsR, List.map_append,
      List.map_reverse] using h
  have hfieldsCtx :=
    (S.generationFields_onTel_rec hconstructor).extendDefEqCtx
      S.generationParams_ctx_rec
  have hGeneration := hChecked.defeqDFC S.ord
    (hfieldsCtx.symm S.ord)
  rw [← NormalizedCtor.fieldsR_length
    (source := source) (mode := gen.elimination) constructor.ctor] at hGeneration
  simpa [ls, hname, NormalizedCtor.fieldsR,
    BlockGenerationChecked.paramsTel,
    NormalizedBlockCtor.resultTarget,
    NormalizedCtor.resultIndicesR,
    VExpr.instL_appN, List.map_append,
    bvarRevRange_instL, List.map_reverse,
    VExpr.instL, VLevel.params_map_inst_params'] using hGeneration

/-- Transport the emitted mutual-constructor application beneath arbitrary
middle and top binders. -/
theorem ctorApp_transport
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    {family : NormalizedFamily}
    (hname : family.raw.name = constructor.familyName)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.HasType gen.recUvars
      (As₂ ++
        ((VExpr.liftTelN g
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination) 0).reverse ++
          (mid ++ gen.paramsTel.reverse)))
      (VExpr.appN (.const constructor.ctor.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            (d + (g +
              (constructor.ctor.fieldsR source.uvars source.nparams
                gen.elimination).length)) source.nparams ++
          VExpr.bvarRevRange d
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length))
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            (d + (g +
              (constructor.ctor.fieldsR source.uvars source.nparams
                gen.elimination).length)) source.nparams ++
          (constructor.ctor.resultIndicesR source.uvars gen.elimination).map
            fun e =>
              (e.liftN g
                (constructor.ctor.fieldsR source.uvars source.nparams
                  gen.elimination).length).liftN d)) := by
  let Bs := constructor.ctor.fieldsR source.uvars source.nparams
    gen.elimination
  have W₁ := Ctx.LiftN.consTel (n := mid.length) Bs
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [Nat.add_zero] at W₁
  have h₁ := (S.ctorApp_emitted_rec hconstructor hname).weakN
    S.ord W₁
  rw [hg] at h₁
  have hmid : env.HasType gen.recUvars
      ((VExpr.liftTelN g Bs 0).reverse ++
        (mid ++ gen.paramsTel.reverse))
      (VExpr.appN (.const constructor.ctor.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange (g + Bs.length) source.nparams ++
          VExpr.bvarRevRange 0 Bs.length))
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange (g + Bs.length) source.nparams ++
          (constructor.ctor.resultIndicesR source.uvars
            gen.elimination).map (VExpr.liftN g · Bs.length))) := by
    simpa [Bs, VExpr.liftN_appN, List.map_append,
      bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
      VExpr.bvarRevRange_liftN_high Bs.length 0 g Bs.length (by omega),
      VExpr.liftN] using h₁
  have htop := hmid.weakN S.ord
    (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  simpa [Bs, VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
    VExpr.liftN, List.map_map, Function.comp_def,
    List.append_assoc] using htop

/-- The raw field telescope of a mutual constructor is well formed after
inserting all block motives. -/
theorem fields_onTel_minor
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) :
    env.OnTel gen.recUvars
      (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)
      (VExpr.liftTelN gen.familyCount
        (constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination) 0) := by
  have hd : gen.motiveTypes.reverse.length = gen.familyCount := by
    simp [gen.motiveTypes_length]
  have hout := (S.generationFields_onTel_rec hconstructor).weakN S.ord
    (Ctx.LiftN.zero (n := gen.familyCount)
      (Γ := gen.paramsTel.reverse) gen.motiveTypes.reverse (h := hd))
  simpa using hout

/-- Every flattened mutual constructor minor is a type over the global
motive telescope. -/
theorem minor_isType
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) :
    env.IsType gen.recUvars
      (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)
      (gen.minorType constructor) := by
  obtain ⟨family, hfamily, howner, hname, hindices⟩ :=
    (S.ctorWF constructor hconstructor).owner
  let d := gen.familyCount
  let Bs := constructor.ctor.fieldsR source.uvars source.nparams
    gen.elimination
  let m := Bs.length
  let rs := constructor.ctor.recArgsR source.uvars gen.elimination
  let IHs := BlockGenerationChecked.blockIHsFromRecArgs d m rs 0
  let Fs := VExpr.liftTelN d Bs 0
  let Γ := IHs.reverse ++
    (Fs.reverse ++
      (gen.motiveTypes.reverse ++ gen.paramsTel.reverse))
  let q := family.view.ordinal
  let K := d - 1 - constructor.owner + m + rs.length
  simp only [BlockGenerationChecked.minorType]
  refine VEnv.IsType.forallN (by
    simpa [Bs, d] using S.fields_onTel_minor hconstructor) ?_
  refine VEnv.IsType.forallN (by
    simpa [Bs, m, rs, IHs, Fs, d, List.append_assoc] using
      S.ihs_onTel hconstructor rs (fun r hr => hr) [] 0 rfl) ?_
  have hrlen : IHs.reverse.length = rs.length := by
    simp [IHs, BlockGenerationChecked.blockIHsFromRecArgs_length]
  have hd : gen.motiveTypes.reverse.length = d := by
    simp [d, gen.motiveTypes_length]
  have hd' : gen.motiveTypes.length = d := by
    simpa using hd
  have hFsLen : Fs.length = m := by
    simp [Fs, m, VExpr.liftTelN_length]
  have hq : q < d := by
    simpa [q, d] using gen.family_ordinal_lt hfamily
  have hmot : gen.motiveTypes.reverse[d - 1 - q]? =
      some ((gen.motiveType family).liftN q) := by
    rw [List.getElem?_reverse (by rw [hd']; omega),
      show gen.motiveTypes.length - 1 - (d - 1 - q) = q from by
        rw [hd']
        omega,
      gen.motiveTypes_getElem?_ordinal hfamily]
  have hM0 := getElem?_rstack_mid
    (IHs.reverse ++ Fs.reverse)
    gen.motiveTypes.reverse gen.paramsTel.reverse
    (i := K)
    (by
      simp only [List.length_append, List.length_reverse,
        hrlen, hFsLen]
      dsimp only [K, q, d]
      omega)
    (by
      simp only [List.length_append, List.length_reverse,
        hrlen, hFsLen, hd]
      dsimp only [K, q, d]
      omega)
  have hdiff :
      K - (IHs.reverse ++ Fs.reverse).length = d - 1 - q := by
    simp only [List.length_append, List.length_reverse,
      hrlen, hFsLen]
    dsimp only [K, q, d]
    omega
  rw [hdiff, hmot] at hM0
  have hMget : Γ[K]? =
      some ((gen.motiveType family).liftN q) := by
    simpa [Γ, List.append_assoc] using hM0
  have hMraw := VEnv.HasType.bvar
    (env := env) (U := gen.recUvars)
    (Lookup.of_getElem? hMget)
  have hM : env.HasType gen.recUvars Γ (.bvar K)
      ((gen.motiveType family).liftN (q + K + 1)) := by
    simpa [VExpr.liftN_liftN, Nat.add_assoc] using hMraw
  have hSp := S.result_transport hconstructor hfamily hindices
    gen.motiveTypes.reverse hd IHs.reverse hrlen
  have hSp' : env.SpineWF gen.recUvars Γ
      (VExpr.forallN
        (VExpr.liftTelN (m + d + rs.length)
          (gen.idxTel family) 0)
        (.sort (gen.validated.resultLevel.inst gen.sourceLevels)))
      ((constructor.ctor.resultIndicesR source.uvars
          gen.elimination).map fun e =>
        (e.liftN d m).liftN rs.length)
      (.sort (gen.validated.resultLevel.inst gen.sourceLevels)) := by
    simpa [Γ, Fs, Bs, m, d, List.append_assoc] using hSp
  have hlen :
      ((constructor.ctor.resultIndicesR source.uvars
          gen.elimination).map fun e =>
        (e.liftN d m).liftN rs.length).length =
        (gen.idxTel family).length := by
    simp only [List.length_map, NormalizedCtor.resultIndicesR,
      BlockGenerationChecked.idxTel]
    exact (S.viewResultIndices_length hconstructor).trans
      ((congrArg List.length hindices).symm.trans
        (gen.shape.2.2.2.2 family hfamily).2.2.2.1.symm)
  have hctorApp := S.ctorApp_transport hconstructor hname
    gen.motiveTypes.reverse hd IHs.reverse hrlen
  have hctorApp' : env.HasType gen.recUvars Γ
      (VExpr.appN
        (.const constructor.ctor.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange (m + d + rs.length) source.nparams ++
          VExpr.bvarRevRange rs.length m))
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange (m + d + rs.length) source.nparams ++
          (constructor.ctor.resultIndicesR source.uvars
            gen.elimination).map fun e =>
              (e.liftN d m).liftN rs.length)) := by
    simpa [Γ, Fs, Bs, m, d, IHs, rs,
      List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hctorApp
  have hshift : q + K + 1 = m + d + rs.length := by
    dsimp only [q, K, d]
    omega
  have hbody := gen.motiveVarApp_hasType family
    (q := q) (K := K)
    hM (by simpa [hshift, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hSp') hlen
      (by simpa [hshift, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hctorApp')
  exact ⟨gen.motiveLevel, by
    simpa [Γ, Fs, Bs, m, rs, IHs, d, K, q,
      BlockGenerationChecked.blockMinorIH,
      List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hbody⟩

/-- Any suffix of the globally flattened constructor list generates a
well-formed minor telescope at its positional depth. -/
theorem minorTypesAux_onTel :
    ∀ (constructors : List NormalizedBlockCtor),
      (∀ constructor ∈ constructors, constructor ∈ gen.flatCtors) →
      ∀ (Δ : List VExpr) (i : Nat), Δ.length = i →
        env.OnTel gen.recUvars
          (Δ ++ (gen.motiveTypes.reverse ++ gen.paramsTel.reverse))
          (gen.minorTypesAux constructors i)
  | [], _, _, _, _ => trivial
  | constructor :: constructors, hsub, Δ, i, hΔ =>
    ⟨by
      rw [← hΔ]
      exact (S.minor_isType
        (hsub constructor (.head _))).weakN S.ord (.zero Δ),
    BlockGenerationEnv.minorTypesAux_onTel constructors
      (fun constructor hconstructor => hsub constructor (.tail _ hconstructor))
      (_ :: Δ) (i + 1) (by simp [hΔ])⟩

/-- The complete global constructor-minor telescope is well formed beneath
all mutual motives. -/
theorem minorTypes_onTel :
    env.OnTel gen.recUvars
      (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)
      gen.minorTypes := by
  simpa [BlockGenerationChecked.minorTypes] using
    S.minorTypesAux_onTel gen.flatCtors
      (fun _ h => h) [] 0 rfl

theorem idxTel_onTel {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.OnTel gen.recUvars gen.paramsTel.reverse
      (gen.idxTel family) := by
  have h := (S.generationFamily_onTel hfamily).instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have h' : env.OnTel gen.recUvars []
      (gen.paramsTel ++ gen.idxTel family) := by
    simpa [BlockGenerationChecked.paramsTel,
      BlockGenerationChecked.idxTel] using h
  simpa using h'.of_append.2

/-- Transport a selected family applied to its index self-spine beneath
arbitrary middle and top binders. -/
theorem familyApp_transport {family : NormalizedFamily}
    (hfamily : family ∈ gen.families)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.HasType gen.recUvars
      (As₂ ++
        ((VExpr.liftTelN g (gen.idxTel family) 0).reverse ++
          (mid ++ gen.paramsTel.reverse)))
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            (d + (g + (gen.idxTel family).length)) source.nparams ++
          VExpr.bvarRevRange d (gen.idxTel family).length))
      (.sort (gen.validated.resultLevel.inst gen.sourceLevels)) := by
  have W₁ := Ctx.LiftN.consTel (n := mid.length) (gen.idxTel family)
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [Nat.add_zero] at W₁
  have h₁ := (S.familyApp_hasType hfamily).weakN S.ord W₁
  rw [hg] at h₁
  have hmid : env.HasType gen.recUvars
      ((VExpr.liftTelN g (gen.idxTel family) 0).reverse ++
        (mid ++ gen.paramsTel.reverse))
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            (g + (gen.idxTel family).length) source.nparams ++
          VExpr.bvarRevRange 0 (gen.idxTel family).length))
      (.sort (gen.validated.resultLevel.inst gen.sourceLevels)) := by
    simpa [VExpr.liftN_appN, List.map_append,
      bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
      VExpr.bvarRevRange_liftN_high
        (gen.idxTel family).length 0 g (gen.idxTel family).length
        (by omega),
      VExpr.liftN] using h₁
  have htop := hmid.weakN S.ord
    (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  simpa [VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
    VExpr.liftN, List.append_assoc] using htop

/-- The generated recursor type for every selected mutual family is well
formed over the empty context. -/
theorem recType_isType {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    env.IsType gen.recUvars [] (gen.recType family) := by
  let d := gen.familyCount
  let k := gen.minorCount
  let q := family.view.ordinal
  let Is := gen.idxTel family
  let ni := Is.length
  let LiftedIs := VExpr.liftTelN (d + k) Is 0
  let A := VExpr.appN (.const family.raw.name gen.sourceLevels)
    (VExpr.bvarRevRange (ni + d + k) source.nparams ++
      VExpr.bvarRevRange 0 ni)
  let Base := gen.minorTypes.reverse ++
    (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)
  let Γ := A :: (LiftedIs.reverse ++ Base)
  let K := d - 1 - q + k + ni + 1
  refine VEnv.IsType.forallN S.paramsTel_onTel ?_
  simp only [List.append_nil]
  refine VEnv.IsType.forallN S.motiveTypes_onTel ?_
  refine VEnv.IsType.forallN S.minorTypes_onTel ?_
  have hdk :
      (gen.minorTypes.reverse ++ gen.motiveTypes.reverse).length = d + k := by
    simp only [List.length_append, List.length_reverse,
      gen.minorTypes_length, gen.motiveTypes_length]
    dsimp only [d, k]
    omega
  have hI : env.OnTel gen.recUvars Base LiftedIs := by
    have h := (S.idxTel_onTel hfamily).weakN S.ord
      (Ctx.LiftN.zero (n := d + k)
        (Γ := gen.paramsTel.reverse)
        (gen.minorTypes.reverse ++ gen.motiveTypes.reverse)
        (h := hdk))
    simpa [Base, LiftedIs, Is, List.append_assoc] using h
  refine VEnv.IsType.forallN hI ?_
  have hmaj₀ := S.familyApp_transport hfamily
    (gen.minorTypes.reverse ++ gen.motiveTypes.reverse)
    (g := d + k) hdk [] (d := 0) rfl
  rw [VExpr.bvarRevRange_congr source.nparams
    (show 0 + (d + k + Is.length) = ni + d + k by
      dsimp only [ni]
      omega)] at hmaj₀
  have hmaj : env.HasType gen.recUvars
      (LiftedIs.reverse ++ Base) A
      (.sort (gen.validated.resultLevel.inst gen.sourceLevels)) := by
    simpa [A, Base, LiftedIs, Is, List.append_assoc] using hmaj₀
  refine VEnv.IsType.forallE ⟨_, hmaj⟩ ?_
  have hILen : LiftedIs.length = ni := by
    simp [LiftedIs, ni, VExpr.liftTelN_length]
  have hq : q < d := by
    simpa [q, d] using gen.family_ordinal_lt hfamily
  have hd : gen.motiveTypes.length = d := by
    simpa [d] using gen.motiveTypes_length
  have hmot : gen.motiveTypes.reverse[d - 1 - q]? =
      some ((gen.motiveType family).liftN q) := by
    rw [List.getElem?_reverse (by rw [hd]; omega),
      show gen.motiveTypes.length - 1 - (d - 1 - q) = q from by
        rw [hd]
        omega,
      gen.motiveTypes_getElem?_ordinal hfamily]
  have hM0 := getElem?_rstack_mid
    ([A] ++ LiftedIs.reverse ++ gen.minorTypes.reverse)
    gen.motiveTypes.reverse gen.paramsTel.reverse
    (i := K)
    (by
      simp only [List.length_append, List.length_singleton,
        List.length_reverse, hILen, gen.minorTypes_length]
      dsimp only [K, q, d, k, ni, Is]
      omega)
    (by
      simp only [List.length_append, List.length_singleton,
        List.length_reverse, hILen, gen.minorTypes_length]
      rw [hd]
      dsimp only [K, q, d, k, ni, Is]
      omega)
  have hdiff :
      K - ([A] ++ LiftedIs.reverse ++ gen.minorTypes.reverse).length =
        d - 1 - q := by
    simp only [List.length_append, List.length_singleton,
      List.length_reverse, hILen, gen.minorTypes_length]
    dsimp only [K, q, d, k, ni, Is]
    omega
  rw [hdiff, hmot] at hM0
  have hMget : Γ[K]? =
      some ((gen.motiveType family).liftN q) := by
    simpa [Γ, Base, List.append_assoc] using hM0
  have hmlu := Lookup.of_getElem? hMget
  rw [show ((gen.motiveType family).liftN q).liftN (K + 1) =
      ((gen.motiveType family).liftN (d + k)).liftN (ni + 1) from by
        rw [VExpr.liftN_liftN, VExpr.liftN_liftN]
        congr 1
        dsimp only [K, q, d, k]
        omega,
    gen.motiveType_liftN family] at hmlu
  have hfun : env.HasType gen.recUvars Γ (.bvar K)
      ((VExpr.forallN LiftedIs
        (.forallE
          (VExpr.appN (.const family.raw.name gen.sourceLevels)
            (VExpr.bvarRevRange (d + k + ni) source.nparams ++
              VExpr.bvarRevRange 0 ni))
          (.sort gen.motiveLevel))).liftN
        (1 + LiftedIs.length)) := by
    exact .bvar (by
      simpa [Γ, Base, LiftedIs, Is, ni,
        VExpr.liftTelN_length, List.append_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmlu)
  have hMapp := VEnv.HasType.appN_selfSpine
    (As := LiftedIs)
    (Δ := [A])
    (Γ := Base)
    (f := .bvar K) hfun
  have hMapp' : env.HasType gen.recUvars Γ
      ((VExpr.bvar K).appN (VExpr.bvarRevRange 1 ni))
      (.forallE (A.liftN 1) (.sort gen.motiveLevel)) := by
    simpa [Γ, Base, A, LiftedIs, Is, ni, hILen,
      VExpr.liftN, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hMapp
  have h0 : Γ[0]? = some A := rfl
  have harg := VEnv.HasType.bvar
    (env := env) (U := gen.recUvars)
    (Lookup.of_getElem? h0)
  have harg' : env.HasType gen.recUvars Γ (.bvar 0) (A.liftN 1) := by
    simpa [Γ, List.append_assoc] using harg
  have happ := VEnv.HasType.app hMapp' harg'
  exact ⟨gen.motiveLevel, by
    simpa [BlockGenerationChecked.recType,
      Γ, Base, A, LiftedIs, Is, ni, d, k, q, K,
      VExpr.liftTelN_length, VExpr.inst, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using happ⟩

/-- Every family-selected mutual recursor constant is well formed in the
environment containing the complete raw block. -/
theorem recursor_wf {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    (gen.recursor family).WF env :=
  S.recType_isType hfamily

theorem recType_levelWF {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    (gen.recType family).LevelWF gen.recUvars := by
  obtain ⟨_, h⟩ := S.recType_isType hfamily
  exact (h.levelWF trivial).1

theorem recType_closedN {family : NormalizedFamily}
    (hfamily : family ∈ gen.families) :
    (gen.recType family).ClosedN 0 := by
  obtain ⟨_, h⟩ := S.recType_isType hfamily
  exact VExpr.WF.closedN S.ord ⟨_, h⟩ trivial

/-- The selected family recursor constant has its generated mutual recursor
type in every local context. -/
theorem recursor_hasType {family : NormalizedFamily}
    (hfamily : family ∈ gen.families)
    (hrec : env.constants (.str family.raw.name "rec") =
      some (gen.recursor family)) {Γ : List VExpr} :
    env.HasType gen.recUvars Γ
      (.const (.str family.raw.name "rec") gen.recLevels)
      (gen.recType family) := by
  have h := VEnv.HasType.const (Γ := Γ) hrec
    VLevel.params_wf VLevel.params_length
  rw [show (gen.recursor family).uvars = gen.recUvars from rfl,
    show (gen.recursor family).type = gen.recType family from rfl] at h
  rwa [(S.recType_levelWF hfamily).instL_id] at h

/-- Applying a selected recursor to the shared parameters, motives, and
flattened minors exposes its index-and-major spine. -/
theorem recBase_hasType {family : NormalizedFamily}
    (hfamily : family ∈ gen.families)
    (hrec : env.constants (.str family.raw.name "rec") =
      some (gen.recursor family))
    (Δ : List VExpr) :
    env.HasType gen.recUvars
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)))
      (gen.recBase Δ.length family.view.ordinal)
      ((VExpr.forallN
        (VExpr.liftTelN
          (gen.familyCount + gen.minorCount)
          (gen.idxTel family) 0)
        (.forallE
          (VExpr.appN (.const family.raw.name gen.sourceLevels)
            (VExpr.bvarRevRange
                ((gen.idxTel family).length +
                  gen.familyCount + gen.minorCount)
                source.nparams ++
              VExpr.bvarRevRange 0 (gen.idxTel family).length))
          (.app
            (VExpr.appN
              (.bvar
                (gen.familyCount - 1 - family.view.ordinal +
                  gen.minorCount + (gen.idxTel family).length + 1))
              (VExpr.bvarRevRange 1 (gen.idxTel family).length))
            (.bvar 0)))).liftN Δ.length) := by
  have hf : env.HasType gen.recUvars
      (Δ ++
        (gen.paramsTel ++ gen.motiveTypes ++ gen.minorTypes).reverse ++ [])
      (.const (.str family.raw.name "rec") gen.recLevels)
      ((VExpr.forallN
        (gen.paramsTel ++ gen.motiveTypes ++ gen.minorTypes)
        (VExpr.forallN
          (VExpr.liftTelN
            (gen.familyCount + gen.minorCount)
            (gen.idxTel family) 0)
          (.forallE
            (VExpr.appN (.const family.raw.name gen.sourceLevels)
              (VExpr.bvarRevRange
                  ((gen.idxTel family).length +
                    gen.familyCount + gen.minorCount)
                  source.nparams ++
                VExpr.bvarRevRange 0 (gen.idxTel family).length))
            (.app
              (VExpr.appN
                (.bvar
                  (gen.familyCount - 1 - family.view.ordinal +
                    gen.minorCount + (gen.idxTel family).length + 1))
                (VExpr.bvarRevRange 1 (gen.idxTel family).length))
              (.bvar 0))))).liftN
        (Δ.length +
          (gen.paramsTel ++ gen.motiveTypes ++ gen.minorTypes).length)) := by
    rw [show VExpr.forallN
        (gen.paramsTel ++ gen.motiveTypes ++ gen.minorTypes)
        (VExpr.forallN
          (VExpr.liftTelN
            (gen.familyCount + gen.minorCount)
            (gen.idxTel family) 0)
          (.forallE
            (VExpr.appN (.const family.raw.name gen.sourceLevels)
              (VExpr.bvarRevRange
                  ((gen.idxTel family).length +
                    gen.familyCount + gen.minorCount)
                  source.nparams ++
                VExpr.bvarRevRange 0 (gen.idxTel family).length))
            (.app
              (VExpr.appN
                (.bvar
                  (gen.familyCount - 1 - family.view.ordinal +
                    gen.minorCount + (gen.idxTel family).length + 1))
                (VExpr.bvarRevRange 1 (gen.idxTel family).length))
              (.bvar 0)))) = gen.recType family from by
          rw [VExpr.forallN_append, VExpr.forallN_append]
          rfl,
      (S.recType_closedN hfamily).liftN_eq (Nat.zero_le _)]
    exact S.recursor_hasType hfamily hrec
  have hspine := VEnv.HasType.appN_selfSpine
    (env := env) (U := gen.recUvars) hf
  simp only [List.reverse_append, List.append_nil, List.append_assoc, List.length_append,
    gen.minorTypes_length, gen.motiveTypes_length] at hspine
  rw [show gen.paramsTel.length = source.nparams from by
      simpa [BlockGenerationChecked.paramsTel] using
        S.generationParams_length,
    VExpr.bvarRevRange_congr' Δ.length
      (show source.nparams + (gen.familyCount + gen.minorCount) =
        source.nparams + gen.familyCount + gen.minorCount by omega)] at hspine
  simpa [BlockGenerationChecked.recBase,
    gen.familyNameAt_ordinal hfamily,
    List.append_assoc] using hspine

/-- Applying a selected family recursor to indices and a major premise
returns the correspondingly selected motive application. -/
theorem recApp_hasType {family : NormalizedFamily}
    (hfamily : family ∈ gen.families)
    (hrec : env.constants (.str family.raw.name "rec") =
      some (gen.recursor family))
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF gen.recUvars
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          (Δ.length + gen.familyCount + gen.minorCount)
          (gen.idxTel family) 0)
        (.sort (gen.validated.resultLevel.inst gen.sourceLevels)))
      idxs (.sort (gen.validated.resultLevel.inst gen.sourceLevels)))
    (hlen : idxs.length = (gen.idxTel family).length)
    (ha : env.HasType gen.recUvars
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)))
      a
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            (Δ.length + gen.familyCount + gen.minorCount)
            source.nparams ++ idxs))) :
    env.HasType gen.recUvars
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)))
      (VExpr.appN (gen.recBase Δ.length family.view.ordinal)
        (idxs ++ [a]))
      (VExpr.appN
        (.bvar
          (gen.familyCount - 1 - family.view.ordinal +
            gen.minorCount + Δ.length))
        (idxs ++ [a])) := by
  have hq := gen.family_ordinal_lt hfamily
  have hb := S.recBase_hasType hfamily hrec Δ
  rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
    liftTelN_congr _ _
      (show gen.familyCount + gen.minorCount + Δ.length =
        Δ.length + gen.familyCount + gen.minorCount by omega)] at hb
  have hcod :
      (VExpr.forallE
        (VExpr.appN (.const family.raw.name gen.sourceLevels)
          (VExpr.bvarRevRange
              ((gen.idxTel family).length +
                gen.familyCount + gen.minorCount)
              source.nparams ++
            VExpr.bvarRevRange 0 (gen.idxTel family).length))
        (.app
          (VExpr.appN
            (.bvar
              (gen.familyCount - 1 - family.view.ordinal +
                gen.minorCount + (gen.idxTel family).length + 1))
            (VExpr.bvarRevRange 1 (gen.idxTel family).length))
          (.bvar 0))).liftN Δ.length
            (0 + (VExpr.liftTelN
              (gen.familyCount + gen.minorCount)
              (gen.idxTel family) 0).length) =
      VExpr.forallE
        (VExpr.appN (.const family.raw.name gen.sourceLevels)
          (VExpr.bvarRevRange
              ((gen.idxTel family).length + Δ.length +
                gen.familyCount + gen.minorCount)
              source.nparams ++
            VExpr.bvarRevRange 0 (gen.idxTel family).length))
        (.app
          (VExpr.appN
            (.bvar
              (gen.familyCount - 1 - family.view.ordinal +
                gen.minorCount + (gen.idxTel family).length +
                Δ.length + 1))
            (VExpr.bvarRevRange 1 (gen.idxTel family).length))
          (.bvar 0)) := by
    rw [VExpr.liftTelN_length, Nat.zero_add]
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append,
        bvarRevRange_liftN_ge _ _ _ _ (by omega),
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
        VExpr.bvarRevRange_congr source.nparams
          (show Δ.length +
              ((gen.idxTel family).length +
                gen.familyCount + gen.minorCount) =
            (gen.idxTel family).length + Δ.length +
              gen.familyCount + gen.minorCount by omega)]
      rfl
    · show VExpr.app _ _ = VExpr.app _ _
      congr 1
      · rw [VExpr.liftN_appN,
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
        show VExpr.appN
          (.bvar (liftVar Δ.length
            (gen.familyCount - 1 - family.view.ordinal +
              gen.minorCount + (gen.idxTel family).length + 1)
            ((gen.idxTel family).length + 1))) _ = _
        rw [liftVar_le (by omega)]
        congr 1
        ac_rfl
  rw [hcod] at hb
  have hshape := hidx.retarget
    (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            ((gen.idxTel family).length + Δ.length +
              gen.familyCount + gen.minorCount)
            source.nparams ++
          VExpr.bvarRevRange 0 (gen.idxTel family).length))
      (.sort gen.motiveLevel))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _
      (C := .const family.raw.name gen.sourceLevels) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _
      (by rw [hlen]; omega),
    show (gen.idxTel family).length + Δ.length +
        gen.familyCount + gen.minorCount - idxs.length =
      Δ.length + gen.familyCount + gen.minorCount from by
        rw [hlen]
        omega,
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hfull := hshape.snoc ha
  simp only [VExpr.inst] at hfull
  change env.SpineWF gen.recUvars _
    (VExpr.forallN
      (VExpr.liftTelN
        (Δ.length + gen.familyCount + gen.minorCount)
        (gen.idxTel family) 0)
      (VExpr.forallN
        [VExpr.appN (.const family.raw.name gen.sourceLevels)
          (VExpr.bvarRevRange
              ((gen.idxTel family).length + Δ.length +
                gen.familyCount + gen.minorCount)
              source.nparams ++
            VExpr.bvarRevRange 0 (gen.idxTel family).length)]
        (.sort gen.motiveLevel)))
    (idxs ++ [a]) (.sort gen.motiveLevel) at hfull
  rw [← VExpr.forallN_append] at hfull
  have hfullLen : (idxs ++ [a]).length =
      (VExpr.liftTelN
          (Δ.length + gen.familyCount + gen.minorCount)
          (gen.idxTel family) 0 ++
        [VExpr.appN (.const family.raw.name gen.sourceLevels)
          (VExpr.bvarRevRange
              ((gen.idxTel family).length + Δ.length +
                gen.familyCount + gen.minorCount)
              source.nparams ++
            VExpr.bvarRevRange 0 (gen.idxTel family).length)]).length := by
    simp only [List.length_append, List.length_singleton,
      VExpr.liftTelN_length, hlen]
  have hactual := hfull.retarget hfullLen
    (VExpr.app
      (VExpr.appN
        (.bvar
          (gen.familyCount - 1 - family.view.ordinal +
            gen.minorCount + (gen.idxTel family).length +
            Δ.length + 1))
        (VExpr.bvarRevRange 1 (gen.idxTel family).length))
      (.bvar 0))
  rw [VExpr.forallN_append] at hactual
  have happ := hactual.hasType_appN hb
  rw [show VExpr.app
      (VExpr.appN
        (.bvar
          (gen.familyCount - 1 - family.view.ordinal +
            gen.minorCount + (gen.idxTel family).length +
            Δ.length + 1))
        (VExpr.bvarRevRange 1 (gen.idxTel family).length))
      (.bvar 0) =
      VExpr.appN
        (.bvar
          (gen.familyCount - 1 - family.view.ordinal +
            gen.minorCount + (gen.idxTel family).length +
            Δ.length + 1))
        (VExpr.bvarRevRange 0 ((gen.idxTel family).length + 1)) from by
      rw [VExpr.bvarRevRange_congr' 0
          (show (gen.idxTel family).length + 1 =
            1 + (gen.idxTel family).length by omega),
        ← VExpr.bvarRevRange_append (gen.idxTel family).length 1]
      simpa [VExpr.bvarRevRange, VExpr.appN] using
        (VExpr.appN_append
          (.bvar
            (gen.familyCount - 1 - family.view.ordinal +
              gen.minorCount + (gen.idxTel family).length +
              Δ.length + 1))
          (VExpr.bvarRevRange 1 (gen.idxTel family).length)
          [VExpr.bvar 0]).symm,
    VExpr.instRev_appN,
    VExpr.instRev_bvar_ge _ (by
      simp only [List.length_append, List.length_singleton]
      rw [hlen]
      omega),
    VExpr.bvarRevRange_congr' 0
      (show (gen.idxTel family).length + 1 =
        (idxs ++ [a]).length by simp [hlen]),
    VExpr.map_instRev_bvarRevRange] at happ
  rw [show gen.familyCount - 1 - family.view.ordinal +
      gen.minorCount + (gen.idxTel family).length + Δ.length + 1 -
        (idxs ++ [a]).length =
      gen.familyCount - 1 - family.view.ordinal +
        gen.minorCount + Δ.length from by
    simp only [List.length_append, List.length_singleton]
    rw [hlen]
    omega] at happ
  simpa [List.length_append, hlen,
    BlockGenerationChecked.recBase,
    gen.familyNameAt_ordinal hfamily] using happ

/-- The constructor application appearing in a mutual rule has the selected
owner-family application as its type. -/
theorem ctorAppRule_hasType
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    {family : NormalizedFamily} (_hfamily : family ∈ gen.families)
    (hname : family.raw.name = constructor.familyName) :
    env.HasType gen.recUvars
      ((VExpr.liftTelN
          (gen.familyCount + gen.minorCount)
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination) 0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)))
      (VExpr.appN
        (.const constructor.ctor.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            ((constructor.ctor.fieldsR source.uvars source.nparams
                gen.elimination).length +
              gen.familyCount + gen.minorCount)
            source.nparams ++
          VExpr.bvarRevRange 0
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length))
      (VExpr.appN (.const family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            ((constructor.ctor.fieldsR source.uvars source.nparams
                gen.elimination).length +
              gen.familyCount + gen.minorCount)
            source.nparams ++
          (constructor.ctor.resultIndicesR source.uvars
            gen.elimination).map fun e =>
              e.liftN (gen.familyCount + gen.minorCount)
                (constructor.ctor.fieldsR source.uvars source.nparams
                  gen.elimination).length)) := by
  have h := S.ctorApp_transport hconstructor hname
    (gen.minorTypes.reverse ++ gen.motiveTypes.reverse)
    (g := gen.familyCount + gen.minorCount)
    (by
      simp only [List.length_append, List.length_reverse,
        gen.minorTypes_length, gen.motiveTypes_length]
      omega)
    [] (d := 0) rfl
  rw [VExpr.bvarRevRange_congr source.nparams
    (show
      0 + (gen.familyCount + gen.minorCount +
        (constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).length) =
      (constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).length +
        gen.familyCount + gen.minorCount by omega)] at h
  simpa [List.append_assoc] using h

/-- Parameters, every motive, every flattened minor, and the selected
constructor fields form the binder telescope of a mutual rule. -/
theorem ruleBinders_onTel
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors) :
    env.OnTel gen.recUvars []
      (gen.paramsTel ++ gen.motiveTypes ++ gen.minorTypes ++
        VExpr.liftTelN
          (gen.familyCount + gen.minorCount)
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination) 0) := by
  have hF₀ := S.fields_onTel_minor hconstructor
  have hF := hF₀.weakN S.ord
    (Ctx.LiftN.zero
      (Γ := gen.motiveTypes.reverse ++ gen.paramsTel.reverse)
      gen.minorTypes.reverse)
  rw [VExpr.liftTelN_liftTelN,
    liftTelN_congr _ _
      (show gen.familyCount + gen.minorTypes.reverse.length =
        gen.familyCount + gen.minorCount by
          simp only [List.length_reverse, gen.minorTypes_length])] at hF
  refine OnTel.append
    (OnTel.append
      (OnTel.append S.paramsTel_onTel
        (by simpa only [List.append_nil] using S.motiveTypes_onTel))
      (by simpa only [List.append_nil, List.reverse_append,
          List.append_assoc] using S.minorTypes_onTel)) ?_
  simpa only [List.append_nil, List.append_assoc,
    List.reverse_append] using hF

/-- The constructor-headed left side of a mutual iota rule has the owner
motive application as its type. -/
theorem recRuleApp_hasType
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    (hrecs : ∀ family ∈ gen.families,
      env.constants (.str family.raw.name "rec") =
        some (gen.recursor family)) :
    env.HasType gen.recUvars
      ((VExpr.liftTelN
          (gen.familyCount + gen.minorCount)
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination) 0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)))
      (VExpr.appN
        (gen.recBase
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination).length constructor.owner)
        (((constructor.ctor.resultIndicesR source.uvars
              gen.elimination).map fun e =>
            e.liftN (gen.familyCount + gen.minorCount)
              (constructor.ctor.fieldsR source.uvars source.nparams
                gen.elimination).length) ++
          [VExpr.appN
            (.const constructor.ctor.raw.name gen.sourceLevels)
            (VExpr.bvarRevRange
                ((constructor.ctor.fieldsR source.uvars source.nparams
                    gen.elimination).length +
                  gen.familyCount + gen.minorCount)
                source.nparams ++
              VExpr.bvarRevRange 0
                (constructor.ctor.fieldsR source.uvars source.nparams
                  gen.elimination).length)]))
      (VExpr.appN
        (.bvar
          (gen.familyCount - 1 - constructor.owner +
            gen.minorCount +
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length))
        (((constructor.ctor.resultIndicesR source.uvars
              gen.elimination).map fun e =>
            e.liftN (gen.familyCount + gen.minorCount)
              (constructor.ctor.fieldsR source.uvars source.nparams
                gen.elimination).length) ++
          [VExpr.appN
            (.const constructor.ctor.raw.name gen.sourceLevels)
            (VExpr.bvarRevRange
                ((constructor.ctor.fieldsR source.uvars source.nparams
                    gen.elimination).length +
                  gen.familyCount + gen.minorCount)
                source.nparams ++
              VExpr.bvarRevRange 0
                (constructor.ctor.fieldsR source.uvars source.nparams
                  gen.elimination).length)])) := by
  obtain ⟨family, hfamily, howner, hname, hindices⟩ :=
    (S.ctorWF constructor hconstructor).owner
  let Bs := constructor.ctor.fieldsR source.uvars source.nparams
    gen.elimination
  let common := gen.familyCount + gen.minorCount
  let mid := gen.minorTypes.reverse ++ gen.motiveTypes.reverse
  have hmid : mid.length = common := by
    simp only [mid, common, List.length_append, List.length_reverse,
      gen.minorTypes_length, gen.motiveTypes_length]
    omega
  have hSp₀ := S.result_transport hconstructor hfamily hindices
    mid hmid [] (d := 0) rfl
  have hSp : env.SpineWF gen.recUvars
      ((VExpr.liftTelN common Bs 0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN (Bs.length + common)
          (gen.idxTel family) 0)
        (.sort (gen.validated.resultLevel.inst gen.sourceLevels)))
      ((constructor.ctor.resultIndicesR source.uvars gen.elimination).map
        fun e => e.liftN common Bs.length)
      (.sort (gen.validated.resultLevel.inst gen.sourceLevels)) := by
    simpa [Bs, common, mid, List.append_assoc,
      Nat.add_assoc] using hSp₀
  have hidxLen :
      ((constructor.ctor.resultIndicesR source.uvars gen.elimination).map
        fun e => e.liftN common Bs.length).length =
      (gen.idxTel family).length := by
    have hlen := hSp.forallN_sort_length
    simpa only [VExpr.liftTelN_length] using hlen
  have ha := S.ctorAppRule_hasType hconstructor hfamily hname
  have hout := S.recApp_hasType hfamily (hrecs family hfamily)
    (VExpr.liftTelN common Bs 0).reverse
    (by simpa [common, List.length_reverse, VExpr.liftTelN_length,
        Nat.add_assoc] using hSp)
    hidxLen
    (by simpa only [Bs, common, List.length_reverse,
        VExpr.liftTelN_length] using ha)
  simpa only [Bs, common, howner, List.length_reverse,
    VExpr.liftTelN_length] using hout

/-- Every recursive field contributes a well-typed rule call to the
recursor selected by that field's certified target family. -/
theorem blockRuleCall_hasType
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    (hrecs : ∀ family ∈ gen.families,
      env.constants (.str family.raw.name "rec") =
        some (gen.recursor family))
    {r : RecArg}
    (hr : r ∈ constructor.ctor.recArgsR source.uvars gen.elimination) :
    env.HasType gen.recUvars
      ((VExpr.liftTelN
          (gen.familyCount + gen.minorCount)
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination) 0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)))
      (BlockGenerationChecked.blockRuleCall
        (gen.familyCount + gen.minorCount)
        (constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).length
        (gen.recBase
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination).length r.targetType) r)
      (BlockGenerationChecked.blockRuleIH
        gen.familyCount gen.minorCount
        (constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).length r) := by
  obtain ⟨r₀, hr₀, rfl⟩ := NormalizedCtor.recArgsR_mem hr
  obtain ⟨family, hfamily, hord, ⟨Bview, hBview, hshape⟩, hsem⟩ :=
    (S.ctorWF constructor hconstructor).recursive r₀ hr₀
  let ls := gen.sourceLevels
  let r := r₀.instL ls
  let d := gen.familyCount
  let k := gen.minorCount
  let common := d+k
  let Bs := constructor.ctor.fieldsR source.uvars source.nparams
    gen.elimination
  let m := Bs.length
  let j := r₀.fieldIndex
  let Fs := VExpr.liftTelN common Bs 0
  let As := BlockGenerationChecked.blockRuleBinders common m r
  let idxs := r.indices.map fun e =>
    (e.liftN common (r.fieldIndex+r.binders.length)).liftN
      (m-r.fieldIndex) r.binders.length
  let Γ := Fs.reverse ++
    (gen.minorTypes.reverse ++
      (gen.motiveTypes.reverse ++ gen.paramsTel.reverse))
  have hjview : r₀.fieldIndex < constructor.ctor.view.fields.length :=
    (List.getElem?_eq_some_iff.1 hBview).1
  have hjm : j < m := by
    have hfields := gen.flatCtor_fields_length hconstructor
    simp only [j, m, Bs, NormalizedCtor.fieldsR_length]
    omega
  have hjraw : r₀.fieldIndex <
      (constructor.ctor.rawFields source.nparams).length := by
    simpa [j, m, Bs, NormalizedCtor.fieldsR_length] using hjm
  let Braw :=
    (constructor.ctor.rawFields source.nparams)[r₀.fieldIndex]
  have hBraw :
      (constructor.ctor.rawFields source.nparams)[r₀.fieldIndex]? =
        some Braw :=
    List.getElem?_eq_getElem hjraw
  have hcommon :
      (gen.minorTypes.reverse ++ gen.motiveTypes.reverse).length =
        common := by
    simp only [List.length_append, List.length_reverse,
      gen.minorTypes_length, gen.motiveTypes_length]
    dsimp only [common, d, k]
    omega
  have hFsLen : Fs.length = m := by
    simp [Fs, m, VExpr.liftTelN_length]
  have ht := S.recArg_transport hconstructor hfamily hsem hjview
    (gen.minorTypes.reverse ++ gen.motiveTypes.reverse) hcommon
    (Fs.drop j).reverse (d := m-j) (by
      simp only [List.length_reverse, List.length_drop, hFsLen])
  dsimp only [r, j, RecArg.instL] at ht
  have hctx :
      (Fs.drop j).reverse ++
          ((VExpr.liftTelN common (Bs.take j) 0).reverse ++
            ((gen.minorTypes.reverse ++ gen.motiveTypes.reverse) ++
              gen.paramsTel.reverse)) = Γ := by
    dsimp only [Γ, Fs]
    rw [← VExpr.liftTelN_take, List.append_assoc,
      ← List.append_assoc
        (((VExpr.liftTelN common Bs 0).drop j).reverse),
      ← List.reverse_append, List.take_append_drop,
      ← List.append_assoc]
  have htel : env.OnTel gen.recUvars Γ As := by
    rw [hctx] at ht
    simpa [r, As, m, common, j, RecArg.instL,
      BlockGenerationChecked.blockRuleBinders] using ht.1
  have hsp : env.SpineWF gen.recUvars
      (As.reverse ++ Γ)
      (VExpr.forallN
        (VExpr.liftTelN
          (m + r.binders.length + common)
          (gen.idxTel family) 0)
        (.sort (gen.validated.resultLevel.inst ls)))
      idxs
      (.sort (gen.validated.resultLevel.inst ls)) := by
    rw [hctx] at ht
    simpa [r, As, idxs, m, common, j, ls,
      RecArg.instL, BlockGenerationChecked.blockRuleBinders,
      List.append_assoc,
      show j + r₀.binders.length + common + (m-j) =
        m + r₀.binders.length + common by omega] using ht.2
  have hF : Γ[m-1-j]? =
      some ((Braw.instL ls).liftN common j) := by
    dsimp only [Γ, Fs]
    rw [List.getElem?_append_left
        (by
          simp only [List.length_reverse, VExpr.liftTelN_length]
          omega),
      List.getElem?_reverse (by rw [hFsLen]; omega),
      VExpr.liftTelN_length,
      show m - 1 - (m - 1 - j) = j by omega,
      VExpr.liftTelN_getElem?,
      NormalizedCtor.fieldsR_getElem?, hBraw]
    simp [ls]
  have hlu := Lookup.of_getElem? hF
  rw [show m-1-j+1 = m-j by omega] at hlu
  dsimp only [j, r] at hlu
  have hf0 := VEnv.HasType.bvar
    (env := env) (U := gen.recUvars) hlu
  obtain ⟨u, hdom₀⟩ :=
    S.emittedField_defeq hconstructor hBraw hBview
  have hdom₁ := hdom₀.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hdomChecked : env.IsDefEq gen.recUvars
      ((constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination |>.take r₀.fieldIndex).reverse ++
        (gen.block.checked.params.map (VExpr.instL ls)).reverse)
      (Braw.instL ls) (Bview.instL ls) ((VExpr.sort u).instL ls) := by
    simpa [NormalizedCtor.fieldsR, List.map_append,
      List.map_reverse, List.map_take] using hdom₁
  have hprefix :=
    S.generationFieldPrefix_ctx_rec hconstructor r₀.fieldIndex
  have hdomGeneration := hdomChecked.defeqDFC S.ord
    (hprefix.symm S.ord)
  have hjlen : (Bs.take r₀.fieldIndex).length =
      r₀.fieldIndex := by
    simp only [Bs, NormalizedCtor.fieldsR,
      List.length_take, List.length_map]
    omega
  have Wmid := Ctx.LiftN.consTel (n := common)
    (Bs.take r₀.fieldIndex)
    (Ctx.LiftN.zero (n := common) (Γ := gen.paramsTel.reverse)
      (gen.minorTypes.reverse ++ gen.motiveTypes.reverse)
      (h := hcommon))
  rw [hjlen, Nat.add_zero] at Wmid
  have hdom₂ := hdomGeneration.weakN S.ord Wmid
  have Wstack := Ctx.LiftN.zero (n := m-j)
    (Γ := (VExpr.liftTelN common (Bs.take j) 0).reverse ++
      ((gen.minorTypes.reverse ++ gen.motiveTypes.reverse) ++
        gen.paramsTel.reverse))
    (Fs.drop j).reverse
    (h := by
      simp only [List.length_reverse, List.length_drop, hFsLen])
  have hdom₃ := hdom₂.weakN S.ord Wstack
  rw [hctx] at hdom₃
  have hfView := hdom₃.defeq hf0
  have hfield := blockMinor_fieldType_of_eq hshape common m 0
    (by simpa [j] using hjm) gen.elimination
  simp only [RecArg.instL] at hfield
  dsimp only [j] at hfView
  simp only [Nat.add_zero] at hfield
  rw [hfield] at hfView
  have hf := hfView.weakN S.ord
    (Ctx.LiftN.zero (Γ := Γ) As.reverse)
  have hmajor := VEnv.HasType.appN_selfSpine
    (env := env) (U := gen.recUvars)
    (As := As)
    (B := VExpr.appN (.const family.raw.name ls)
      (VExpr.bvarRevRange
        (m + r.binders.length + common) source.nparams ++ idxs))
    (Δ := []) (Γ := Γ) (by
      simpa [As, r, idxs, j, common, ls, RecArg.instL,
        BlockGenerationChecked.blockRuleBinders,
        BlockGenerationChecked.blockMinorBinders,
        List.length_reverse, List.map_map,
        Function.comp_def] using hf)
  simp only [List.length_nil, VExpr.liftN_zero,
    List.nil_append] at hmajor
  have hAsLen : As.length = r.binders.length := by
    simp [As, BlockGenerationChecked.blockRuleBinders,
      VExpr.liftTelN_length]
  have hmajor' : env.HasType gen.recUvars (As.reverse ++ Γ)
      ((VExpr.bvar (m-1-r.fieldIndex+As.length)).appN
        (VExpr.bvarRevRange 0 As.length))
      (VExpr.appN (.const family.raw.name ls)
        (VExpr.bvarRevRange
          (m+r.binders.length+common) source.nparams ++ idxs)) := by
    simpa [As, common, r, RecArg.instL,
      BlockGenerationChecked.blockRuleBinders,
      VExpr.liftN, liftVar_le, Nat.add_comm] using hmajor
  rw [hAsLen] at hmajor'
  have hlen : idxs.length = (gen.idxTel family).length := by
    have hidx := hsem.2.forallN_sort_length
    simp only [idxs, List.length_map, VExpr.liftTelN_length,
      BlockGenerationChecked.idxTel] at hidx ⊢
    simpa [r, RecArg.instL] using hidx.trans
      (gen.shape.2.2.2.2 family hfamily).2.2.2.1.symm
  have hcall := S.recApp_hasType hfamily (hrecs family hfamily)
    (As.reverse ++ Fs.reverse)
    (by
      simpa [Γ, List.append_assoc, hAsLen, hFsLen,
        common, d, k,
        Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hsp)
    hlen
    (by
      simpa [Γ, List.append_assoc, hAsLen, hFsLen,
        common, d, k,
        Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hmajor')
  have hbaseLift :
      (gen.recBase m r.targetType).liftN r.binders.length =
        gen.recBase (m+r.binders.length) r.targetType := by
    simp only [BlockGenerationChecked.recBase, VExpr.liftN_appN, VExpr.liftN]
    rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _)]
    apply congrArg (VExpr.appN _)
    apply VExpr.bvarRevRange_congr
    omega
  have hlam := HasType.lamN htel (by
    simpa [Γ, Fs, hAsLen, hFsLen, hbaseLift,
      List.append_assoc, hord, r, RecArg.instL,
      common, d, k,
      Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcall)
  have hrecPos : r₀.binders.length + m = m + r₀.binders.length := by
    omega
  have hfieldPos :
      r₀.binders.length + (m-1-r₀.fieldIndex) =
        m-1-r₀.fieldIndex+r₀.binders.length := by
    omega
  have hmotivePos :
      r₀.binders.length +
          (gen.familyCount - 1 - r₀.targetType + (gen.minorCount+m)) =
        gen.familyCount - 1 - r₀.targetType + gen.minorCount + m +
          r₀.binders.length := by
    ac_rfl
  rw [hrecPos, hfieldPos, hmotivePos] at hlam
  change env.HasType gen.recUvars Γ
    (BlockGenerationChecked.blockRuleCall common m
      (gen.recBase m r.targetType) r)
    (VExpr.forallN As
      (VExpr.appN
        (.bvar (d - 1 - r.targetType + k + m + r.binders.length))
        (idxs ++
          [VExpr.appN
            (.bvar (m - 1 - r.fieldIndex + r.binders.length))
            (VExpr.bvarRevRange 0 r.binders.length)])))
  have hcallEq :
      BlockGenerationChecked.blockRuleCall common m
          (gen.recBase m r.targetType) r =
        VExpr.lamN As
          (VExpr.appN
            (gen.recBase (m+r.binders.length) r.targetType)
            (idxs ++
              [VExpr.appN
                (.bvar (m-1-r.fieldIndex+r.binders.length))
                (VExpr.bvarRevRange 0 r.binders.length)])) := by
    simp [BlockGenerationChecked.blockRuleCall, As, idxs, hbaseLift]
  rw [hcallEq]
  simpa [r, RecArg.instL, List.length_map] using hlam

/-- The selected flattened mutual minor applied to its fields and routed
recursive calls has the owner's motive as its result. -/
theorem minorApp_hasType {i : Nat}
    {constructor : NormalizedBlockCtor}
    (hci : gen.flatCtors[i]? = some constructor)
    (hrecs : ∀ family ∈ gen.families,
      env.constants (.str family.raw.name "rec") =
        some (gen.recursor family)) :
    env.HasType gen.recUvars
      ((VExpr.liftTelN
          (gen.familyCount + gen.minorCount)
          (constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination) 0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)))
      (VExpr.appN
        (.bvar
          (gen.minorCount - 1 - i +
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length))
        (VExpr.bvarRevRange 0
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length ++
          (constructor.ctor.recArgsR source.uvars gen.elimination).map
            fun r =>
              BlockGenerationChecked.blockRuleCall
                (gen.familyCount + gen.minorCount)
                (constructor.ctor.fieldsR source.uvars source.nparams
                  gen.elimination).length
                (gen.recBase
                  (constructor.ctor.fieldsR source.uvars source.nparams
                    gen.elimination).length r.targetType) r))
      (VExpr.appN
        (.bvar
          (gen.familyCount - 1 - constructor.owner + gen.minorCount +
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination).length))
        (((constructor.ctor.resultIndicesR source.uvars
              gen.elimination).map fun e =>
            e.liftN (gen.familyCount + gen.minorCount)
              (constructor.ctor.fieldsR source.uvars source.nparams
                gen.elimination).length) ++
          [VExpr.appN
            (.const constructor.ctor.raw.name gen.sourceLevels)
            (VExpr.bvarRevRange
                ((constructor.ctor.fieldsR source.uvars source.nparams
                    gen.elimination).length + gen.familyCount +
                  gen.minorCount)
                source.nparams ++
              VExpr.bvarRevRange 0
                (constructor.ctor.fieldsR source.uvars source.nparams
                  gen.elimination).length)])) := by
  obtain ⟨hik, -⟩ := List.getElem?_eq_some_iff.1 hci
  have hconstructor := List.mem_of_getElem? hci
  obtain ⟨family, hfamily, howner, -, -⟩ :=
    (S.ctorWF constructor hconstructor).owner
  let d := gen.familyCount
  let k := gen.minorCount
  let common := d+k
  let Bs := constructor.ctor.fieldsR source.uvars source.nparams
    gen.elimination
  let m := Bs.length
  let rs := constructor.ctor.recArgsR source.uvars gen.elimination
  let Fs := VExpr.liftTelN common Bs 0
  let D := VExpr.appN
    (.bvar (d - 1 - constructor.owner + m + rs.length))
    (((constructor.ctor.resultIndicesR source.uvars
          gen.elimination).map fun e =>
        (e.liftN d m).liftN rs.length) ++
      [VExpr.appN
        (.const constructor.ctor.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange (rs.length+m+d) source.nparams ++
          VExpr.bvarRevRange rs.length m)])
  let Dfin := VExpr.appN
    (.bvar (d - 1 - constructor.owner + k + m))
    (((constructor.ctor.resultIndicesR source.uvars
          gen.elimination).map fun e => e.liftN common m) ++
      [VExpr.appN
        (.const constructor.ctor.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange (m+common) source.nparams ++
          VExpr.bvarRevRange 0 m)])
  have hownerLt : constructor.owner < d := by
    rw [← howner]
    simpa [d] using gen.family_ordinal_lt hfamily
  have hrsLt : ∀ r ∈ rs, r.fieldIndex < m := by
    intro r hr
    obtain ⟨r₀, hr₀, rfl⟩ :=
      NormalizedCtor.recArgsR_mem (show
        r ∈ constructor.ctor.recArgsR source.uvars gen.elimination from
          by simpa [rs] using hr)
    obtain ⟨family₀, hfamily₀, htarget,
        ⟨Bview, hfield, hshape⟩, hsem⟩ :=
      (S.ctorWF constructor hconstructor).recursive r₀ hr₀
    have hj := (List.getElem?_eq_some_iff.1 hfield).1
    simp only [RecArg.instL]
    dsimp only [m, Bs]
    rw [NormalizedCtor.fieldsR_length]
    rw [gen.flatCtor_fields_length hconstructor]
    exact hj
  have hik' : i < k := by
    simpa [k] using hik
  rw [VExpr.appN_append]
  have hminorAt :
      gen.minorTypes[i]? =
        some ((gen.minorType constructor).liftN i) := by
    simpa [BlockGenerationChecked.minorTypes, hci] using
      (gen.minorTypesAux_getElem? gen.flatCtors 0 i)
  have hlu0 :
      (Fs.reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveTypes.reverse ++ gen.paramsTel.reverse)))[
          k - 1 - i + m]? =
        some ((gen.minorType constructor).liftN i) := by
    rw [getElem?_rstack_mid _ _ _
        (by simp [Fs, m, VExpr.liftTelN_length] <;> omega)
        (by simp [Fs, m, k, gen.minorTypes_length,
          VExpr.liftTelN_length] <;> omega),
      show k - 1 - i + m - Fs.reverse.length = k - 1 - i by
        simp [Fs, m, VExpr.liftTelN_length],
      List.getElem?_reverse (by
        rw [gen.minorTypes_length]
        omega),
      show gen.minorTypes.length - 1 - (k - 1 - i) = i by
        rw [gen.minorTypes_length]
        dsimp only [k]
        omega,
      hminorAt]
  have hlu := Lookup.of_getElem? hlu0
  rw [VExpr.liftN_liftN,
    show i + (k - 1 - i + m + 1) = m+k by omega] at hlu
  have hminorEq :
      (gen.minorType constructor).liftN (m+k) =
        (VExpr.forallN Fs
          ((VExpr.forallN
            (BlockGenerationChecked.blockIHsFromRecArgs d m rs 0)
            D).liftN k m)).liftN m := by
    simp only [BlockGenerationChecked.minorType]
    conv => lhs; rw [VExpr.liftN_forallN,
        VExpr.liftTelN_liftTelN,
        liftTelN_congr _ _
          (show d + (m+k) = common+m by
            dsimp only [common]
            omega),
        show 0 + (VExpr.liftTelN d Bs 0).length = m by
          simp [m, VExpr.liftTelN_length]]
    conv => rhs; rw [VExpr.liftN_forallN,
        VExpr.liftTelN_liftTelN,
        show 0 + Fs.length = m by
          simp [Fs, m, VExpr.liftTelN_length],
        VExpr.liftN'_liftN_hi,
        Nat.add_comm k m]
  have hfields := HasType.appN_selfSpine
    (env := env) (U := gen.recUvars)
    (As := Fs)
    (B := (VExpr.forallN
      (BlockGenerationChecked.blockIHsFromRecArgs d m rs 0)
      D).liftN k m)
    (Δ := [])
    (Γ := gen.minorTypes.reverse ++
      (gen.motiveTypes.reverse ++ gen.paramsTel.reverse))
    (f := .bvar (k-1-i+m))
    (by
      have hb := VEnv.HasType.bvar
        (env := env) (U := gen.recUvars) hlu
      rw [hminorEq] at hb
      simpa [Fs, VExpr.liftTelN_length] using hb)
  simp only [List.length_nil, VExpr.liftN_zero] at hfields
  rw [BlockGenerationChecked.blockIHs_liftN'
    d m k rs hrsLt 0 D (cut := m) rfl] at hfields
  have hD : D.liftN k (m+0+rs.length) =
      Dfin.liftN rs.length := by
    dsimp only [D, Dfin]
    rw [VExpr.liftN_appN, VExpr.liftN_appN,
      List.map_append, List.map_append,
      List.map_map, List.map_map]
    show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
    congr 1
    · show
        VExpr.bvar
            (liftVar k
              (d - 1 - constructor.owner + m + rs.length)
              (m+0+rs.length)) =
          VExpr.bvar
            (liftVar rs.length
              (d - 1 - constructor.owner + k + m) 0)
      rw [liftVar_le (by omega), liftVar_le (Nat.zero_le _)]
      congr 1
      omega
    · congr 1
      · apply List.map_congr_left
        intro e _
        simp only [Function.comp_apply]
        rw [show m+0+rs.length = m+rs.length by omega,
          VExpr.liftN_liftN_midN e d k rs.length (Nat.zero_le _)]
      · congr 1
        simp only []
        rw [show m+0+rs.length = m+rs.length by omega,
          VExpr.liftN_appN, VExpr.liftN_appN,
          List.map_append, List.map_append,
          bvarRevRange_liftN_ge _ _ _ _ (by omega),
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
          bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
          bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
          VExpr.bvarRevRange_congr source.nparams
            (show k + (rs.length+m+d) =
              rs.length + (m+common) by
                dsimp only [common]
                omega),
          VExpr.bvarRevRange_congr m
            (show rs.length = rs.length+0 by omega)]
        rfl
  rw [hD] at hfields
  have hres := hasType_appN_blockRuleIHs
    (env := env) (gen := gen) (d := d) (m := m) (k := k)
    (rs := rs)
    (argOf := fun r =>
      BlockGenerationChecked.blockRuleCall common m
        (gen.recBase m r.targetType) r)
    (Dfin := Dfin)
    (fun r hr => by
      simpa [d, k, common, m, Bs] using
        S.blockRuleCall_hasType hconstructor hrecs
          (show r ∈ constructor.ctor.recArgsR source.uvars
              gen.elimination by simpa [rs] using hr))
    hfields
  simpa [Fs, Bs, m, rs, d, k, common, Dfin,
    VExpr.liftTelN_length, Nat.add_assoc] using hres

/-- Every flattened mutual iota rule is well formed once all family
recursors are available. -/
theorem rule_WF {i : Nat}
    {constructor : NormalizedBlockCtor}
    (hci : gen.flatCtors[i]? = some constructor)
    (hrecs : ∀ family ∈ gen.families,
      env.constants (.str family.raw.name "rec") =
        some (gen.recursor family)) :
    (gen.rule i constructor).WF env := by
  have hconstructor := List.mem_of_getElem? hci
  refine ⟨?_, ?_⟩
  · show env.HasType gen.recUvars []
      (VExpr.lamN
        (gen.paramsTel ++ gen.motiveTypes ++ gen.minorTypes ++
          VExpr.liftTelN
            (gen.familyCount + gen.minorCount)
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination) 0)
        _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBinders_onTel hconstructor) ?_
    simp only [List.reverse_append, List.append_nil,
      List.append_assoc]
    simpa only [Nat.add_assoc] using
      S.recRuleApp_hasType hconstructor hrecs
  · show env.HasType gen.recUvars []
      (VExpr.lamN
        (gen.paramsTel ++ gen.motiveTypes ++ gen.minorTypes ++
          VExpr.liftTelN
            (gen.familyCount + gen.minorCount)
            (constructor.ctor.fieldsR source.uvars source.nparams
              gen.elimination) 0)
        _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBinders_onTel hconstructor) ?_
    simp only [List.reverse_append, List.append_nil,
      List.append_assoc]
    simpa only [Nat.add_assoc] using
      S.minorApp_hasType hci hrecs

end BlockGenerationEnv

/-- The public inductive-declaration contract is monotone in its prefix
environment. This lets replay fixtures prepend independently verified
declarations without rebuilding the block's Stage-3 derivation. -/
theorem WF.mono {env env' : VEnv} (henv : env ≤ env')
    (H : VInductDecl.WF env decl) : VInductDecl.WF env' decl := by
  refine ⟨H.1, fun ty hty => ?_⟩
  obtain ⟨htel, hctors⟩ := H.2 ty hty
  exact ⟨htel.mono henv, fun c hc =>
    ⟨fieldsWF_mono henv (hctors c hc).1, (hctors c hc).2.mono henv⟩⟩

/-- Extract the carried index-spine typing of the recursive field at
position `q` from a `fieldsWF` chain. -/
theorem fieldsWF_spine {U : Nat} {T : Name} {np : Nat} {env : VEnv} {l : VLevel}
    {Is : List VExpr} : ∀ {Bs : List VExpr} {Γ₀ : List VExpr} {j₀ : Nat},
    fieldsWF U T np env l Is Γ₀ j₀ Bs →
    ∀ q B, Bs[q]? = some B → isRecField U T np Is.length (j₀+q) B = true →
    env.SpineWF U ((Bs.take q).reverse ++ Γ₀)
      (VExpr.forallN (VExpr.liftTelN (j₀+q) Is 0) (.sort l)) (recFieldIdxs np B) (.sort l)
  | [], _, _, _, q, B, hB, _ => by simp at hB
  | B' :: Bs, Γ₀, j₀, ⟨_, hSp, hT⟩, 0, B, hB, hrec => by
    obtain rfl : B' = B := by simpa using hB
    simpa using hSp (by simpa using hrec)
  | B' :: Bs, Γ₀, j₀, ⟨_, _, hT⟩, q+1, B, hB, hrec => by
    have := fieldsWF_spine hT q B (by simpa using hB)
      (by rwa [show j₀+1+q = j₀+(q+1) from by omega])
    rw [show j₀+1+q = j₀+(q+1) from by omega] at this
    simpa [List.append_assoc] using this

/-- Extract the uniform semantic evidence for any analyzed recursive
argument. Direct fields are re-expressed as the empty-telescope case; genuine
recursive Pi fields return the evidence stored by `fieldsWF`. -/
theorem fieldsWF_recArg {U : Nat} {T : Name} {np : Nat} {env : VEnv} {l : VLevel}
    {Is : List VExpr} : ∀ {Bs : List VExpr} {Γ₀ : List VExpr} {j₀ : Nat},
    fieldsWF U T np env l Is Γ₀ j₀ Bs →
    ∀ q B r, Bs[q]? = some B →
      recArg? U T np Is.length (j₀+q) B = some r →
      r.WF U env l Is ((Bs.take q).reverse ++ Γ₀)
  | [], _, _, _, q, B, r, hB, _ => by simp at hB
  | B' :: Bs, Γ₀, j₀, ⟨hclass, hSp, htail⟩, 0, B, r, hB, hr => by
    obtain rfl : B' = B := by simpa using hB
    simp only [Nat.add_zero] at hr
    rcases hclass with hdirect | hfun | ⟨hnone, -, -, -⟩
    · have hcanon := recArg?_of_isRecField hdirect
      rw [hcanon] at hr
      obtain rfl := Option.some.inj hr
      exact ⟨trivial, by simpa [RecArg.WF] using hSp hdirect⟩
    · obtain ⟨r', hr', -, hwf⟩ := hfun
      rw [hr'] at hr
      obtain rfl := Option.some.inj hr
      simpa using hwf
    · rw [hnone] at hr
      contradiction
  | B' :: Bs, Γ₀, j₀, ⟨_, _, htail⟩, q+1, B, r, hB, hr => by
    have h := fieldsWF_recArg htail q B r (by simpa using hB)
      (by rwa [show j₀+1+q = j₀+(q+1) from by omega])
    simpa [List.append_assoc] using h

namespace GenerationEnv

variable {source : VInductDecl} {gen : GenerationChecked source}
  {env : VEnv} (S : GenerationEnv gen env)
include S
-- `S` is included throughout so every lemma below is reachable as `S.lemma`,
-- including those whose statement and proof never mention it.
set_option linter.unusedSectionVars false

/-- Checked field semantics for one paired constructor, re-indexed onto the
raw block header used by mixed generation. -/
theorem viewFieldsWF {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    fieldsWF source.uvars gen.block.sourceType.name source.nparams env
      gen.block.checked.resultLevel gen.block.checked.indices
      gen.block.checked.params.reverse 0 ctor.view.fields := by
  obtain ⟨c, hc, hview⟩ := gen.viewCtor_ofDirect hctor
  have h := (S.checked.2 c hc).1
  rw [hview]
  simpa [CheckedCtor.ofDirect, gen.block.uvars_eq,
    gen.block.nparams_eq, gen.block.sourceType_name_eq] using h

/-- Every retained recursive descriptor comes from re-analysis of the field
at its recorded position in the checked view. -/
theorem viewRecArg_data {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hr : r ∈ ctor.view.recursive) :
    ∃ B, ctor.view.fields[r.fieldIndex]? = some B ∧
      recArg? source.uvars gen.block.sourceType.name source.nparams
        gen.block.checked.indices.length r.fieldIndex B = some r := by
  obtain ⟨c, -, hview⟩ := gen.viewCtor_ofDirect hctor
  rw [hview] at hr ⊢
  simp only [CheckedCtor.ofDirect] at hr ⊢
  obtain ⟨B, hB, hrec⟩ := recArgs_getElem r hr
  exact ⟨B, by simpa using hB, hrec⟩

/-- Retained recursive descriptors have the checked family-index arity. -/
theorem viewRecArg_indices_length {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hr : r ∈ ctor.view.recursive) :
    r.indices.length = gen.block.checked.indices.length := by
  obtain ⟨B, hB, hrec⟩ := S.viewRecArg_data hctor hr
  exact (recArg?_eq hrec).2.2.2.1

/-- Retained recursive descriptors point inside the normalized field list. -/
theorem viewRecArg_lt {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hr : r ∈ ctor.view.recursive) :
    r.fieldIndex < ctor.view.fields.length := by
  obtain ⟨c, -, hview⟩ := gen.viewCtor_ofDirect hctor
  rw [hview] at hr ⊢
  simp only [CheckedCtor.ofDirect] at hr ⊢
  simpa using recArgs_lt r hr

/-- The checked-view certificate supplies recursive-argument semantics in
the exact normalized prefix context. -/
theorem viewRecArg_WF {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hr : r ∈ ctor.view.recursive) :
    r.WF source.uvars env gen.block.checked.resultLevel
      gen.block.checked.indices
      ((ctor.view.fields.take r.fieldIndex).reverse ++
        gen.block.checked.params.reverse) := by
  obtain ⟨B, hB, hrec⟩ := S.viewRecArg_data hctor hr
  have h := fieldsWF_recArg (S.viewFieldsWF hctor)
    r.fieldIndex B r hB (by simpa using hrec)
  simpa using h

/-- Definitionally equal raw/view contexts at any constructor-field prefix.
This is the structural bridge used before instantiation and weakening. -/
theorem emittedPrefix_ctx {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) (j : Nat) :
    env.IsDefEqCtx source.uvars []
      ((ctor.rawFields source.nparams |>.take j).reverse ++
        gen.block.checked.params.reverse)
      ((ctor.view.fields.take j).reverse ++
        gen.block.checked.params.reverse) := by
  have h := ((S.ctorWF ctor hctor).emittedTel.take
    (source.nparams + j)).ctx
  have hviewLen :
      gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hraw :
      (gen.block.checked.params ++ ctor.rawFields source.nparams).take
          (source.nparams + j) =
        gen.block.checked.params ++
          (ctor.rawFields source.nparams).take j := by
    rw [← hviewLen]
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  have hview :
      (gen.block.checked.params ++ ctor.view.fields).take
          (source.nparams + j) =
        gen.block.checked.params ++ ctor.view.fields.take j := by
    rw [← hviewLen]
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  simp only [NormalizedCtor.emittedBinders,
    NormalizedCtor.viewBinders] at h
  rw [hraw, hview] at h
  simpa [List.reverse_append] using h

/-- The pointwise raw/view field-domain equality at a paired position, in
the preceding raw context. -/
theorem emittedField_defeq {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {j : Nat} {B B' : VExpr}
    (hB : (ctor.rawFields source.nparams)[j]? = some B)
    (hB' : ctor.view.fields[j]? = some B') :
    ∃ u, env.IsDefEq source.uvars
      ((ctor.rawFields source.nparams |>.take j).reverse ++
        gen.block.checked.params.reverse)
      B B' (.sort u) := by
  have hviewLen :
      gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hraw :
      getElem?
        (gen.block.checked.params ++ ctor.rawFields source.nparams)
        (source.nparams + j) = some B := by
    rw [List.getElem?_append_right (by
      rw [hviewLen]
      omega), hviewLen]
    simpa using hB
  have hview :
      getElem?
        (gen.block.checked.params ++ ctor.view.fields)
        (source.nparams + j) = some B' := by
    rw [List.getElem?_append_right (by
      rw [hviewLen]
      omega), hviewLen]
    simpa using hB'
  obtain ⟨u, h⟩ :=
    (S.ctorWF ctor hctor).emittedTel.getElem? hraw hview
  have htake :
      (gen.block.checked.params ++ ctor.rawFields source.nparams).take
          (source.nparams + j) =
        gen.block.checked.params ++
          (ctor.rawFields source.nparams).take j := by
    rw [← hviewLen]
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  simp only [NormalizedCtor.emittedBinders] at h
  rw [htake, List.reverse_append] at h
  exact ⟨u, by simpa using h⟩

/-- Recursive-argument semantics transported from the checked view into the
raw constructor-field prefix that mixed artifacts actually bind. -/
theorem rawRecArg_WF {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hr : r ∈ ctor.view.recursive) :
    r.WF source.uvars env gen.block.checked.resultLevel
      gen.block.checked.indices
      ((ctor.rawFields source.nparams |>.take r.fieldIndex).reverse ++
        gen.block.checked.params.reverse) := by
  exact (S.viewRecArg_WF hctor hr).defeqDFC S.ord
    ((S.emittedPrefix_ctx hctor r.fieldIndex).symm S.ord)

/-- The family telescope contract restricted to the index suffix. -/
theorem rawIndexTel_defeq :
    env.TelDefEq source.uvars gen.block.rawParams.reverse
      gen.block.rawIndices gen.block.checked.indices := by
  have h := S.familyTel.drop source.nparams
  have hrawTake :
      (gen.block.rawParams ++ gen.block.rawIndices).take source.nparams =
        gen.block.rawParams := by
    rw [← gen.shape.1, List.take_append, List.take_length]
    simp
  have hrawDrop :
      (gen.block.rawParams ++ gen.block.rawIndices).drop source.nparams =
        gen.block.rawIndices := by
    rw [← gen.shape.1, List.drop_append]
    simp
  have hviewLen :
      gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hviewDrop :
      (gen.block.checked.params ++ gen.block.checked.indices).drop
          source.nparams =
        gen.block.checked.indices := by
    rw [← hviewLen, List.drop_append]
    simp
  rw [hrawTake, hrawDrop, hviewDrop] at h
  simpa using h

/-- The raw/view index relation transported to the checked parameter base
used by generated artifacts. -/
theorem emittedIndexTel_defeq :
    env.TelDefEq source.uvars gen.block.checked.params.reverse
      gen.block.rawIndices gen.block.checked.indices :=
  S.rawIndexTel_defeq.defeqDFC S.ord S.rawParams_ctx

/-- The raw/view index telescope relation transported into recursor
universes. -/
theorem rawIndexTel_defeq_rec :
    env.TelDefEq (gen.recUvars) gen.paramsTel.reverse gen.idxTel
      (gen.block.checked.indices.map
        (VExpr.instL (gen.sourceLevels))) := by
  have hdecl := S.emittedIndexTel_defeq.defeqDFC S.ord
    (S.generationParams_ctx.symm S.ord)
  have h := hdecl.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  simpa [GenerationChecked.paramsTel, GenerationChecked.idxTel,
    List.map_reverse] using h

/-- Transport all retained recursive-argument evidence into a mixed
minor/rule context. Raw constructor fields and raw family indices are the
emitted surfaces; recursive classification and index expressions remain the
checked-view data. -/
theorem recArg_transport {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r₀ : RecArg}
    (hr₀ : r₀ ∈ ctor.view.recursive)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    let r := r₀.instL (gen.sourceLevels)
    let As := VExpr.liftTelN d
      (VExpr.liftTelN g r.binders r.fieldIndex) 0
    env.OnTel (gen.recUvars)
        (As₂ ++ ((VExpr.liftTelN g
          ((ctor.fieldsR source.uvars source.nparams gen.elimination).take
            r.fieldIndex) 0).reverse ++
          (mid ++ gen.paramsTel.reverse))) As ∧
      env.SpineWF (gen.recUvars)
        (As.reverse ++
          (As₂ ++ ((VExpr.liftTelN g
            ((ctor.fieldsR source.uvars source.nparams gen.elimination).take
              r.fieldIndex) 0).reverse ++
            (mid ++ gen.paramsTel.reverse))))
        (VExpr.forallN
          (VExpr.liftTelN
            (r.fieldIndex + r.binders.length + g + d) gen.idxTel 0)
          (.sort (gen.block.checked.resultLevel.inst
            (gen.sourceLevels))))
        (r.indices.map fun e =>
          (e.liftN g (r.fieldIndex + r.binders.length)).liftN d
            r.binders.length)
        (.sort (gen.block.checked.resultLevel.inst
          (gen.sourceLevels))) := by
  dsimp only
  let ls := gen.sourceLevels
  have hjlt :
      r₀.fieldIndex < (ctor.rawFields source.nparams).length := by
    have hview := S.viewRecArg_lt hctor hr₀
    have hfields :=
      (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
    omega
  have hsem := S.rawRecArg_WF hctor hr₀
  have htel₁ := hsem.1.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hsp₁ := hsem.2.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have htelChecked : env.OnTel (gen.recUvars)
      ((ctor.fieldsR source.uvars source.nparams gen.elimination |>.take
        r₀.fieldIndex).reverse ++
        (gen.block.checked.params.map (VExpr.instL ls)).reverse)
      (r₀.binders.map (VExpr.instL ls)) := by
    simpa [NormalizedCtor.fieldsR, List.map_append,
      List.map_reverse, List.map_take] using htel₁
  have hspChecked : env.SpineWF (gen.recUvars)
      ((r₀.binders.map (VExpr.instL ls)).reverse ++
        ((ctor.fieldsR source.uvars source.nparams gen.elimination |>.take
          r₀.fieldIndex).reverse ++
          (gen.block.checked.params.map (VExpr.instL ls)).reverse))
      (VExpr.instL ls
        (VExpr.forallN
          (VExpr.liftTelN
            (r₀.fieldIndex + r₀.binders.length)
            gen.block.checked.indices 0)
          (.sort gen.block.checked.resultLevel)))
      (r₀.indices.map (VExpr.instL ls))
      (VExpr.instL ls (.sort gen.block.checked.resultLevel)) := by
    simpa [List.map_append, List.map_reverse,
      NormalizedCtor.fieldsR, List.map_take] using hsp₁
  have hprefix := S.generationFieldPrefix_ctx_rec hctor r₀.fieldIndex
  have htelGeneration := htelChecked.defeqDFC S.ord
    (hprefix.symm S.ord)
  have hfull := htelGeneration.extendDefEqCtx hprefix
  have hspGeneration := hspChecked.defeqDFC S.ord (hfull.symm S.ord)
  simp only [VExpr.instL_forallN, VExpr.liftTelN_instL] at htelGeneration hspGeneration
  have hjlen :
      ((ctor.fieldsR source.uvars source.nparams gen.elimination).take
        r₀.fieldIndex).length = r₀.fieldIndex := by
    simp only [NormalizedCtor.fieldsR, List.length_take,
      List.length_map]
    omega
  have hidxField := S.rawIndexTel_defeq_rec.weakN S.ord
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse)
      ((ctor.fieldsR source.uvars source.nparams gen.elimination).take
        r₀.fieldIndex).reverse)
  rw [List.length_reverse, hjlen] at hidxField
  have hidxPrivate := hidxField.weakN S.ord
    (Ctx.LiftN.zero
      (Γ := ((ctor.fieldsR source.uvars source.nparams gen.elimination).take
          r₀.fieldIndex).reverse ++ gen.paramsTel.reverse)
      (r₀.binders.map (VExpr.instL ls)).reverse)
  simp only [List.length_reverse, List.length_map] at hidxPrivate
  rw [VExpr.liftTelN_liftTelN,
    VExpr.liftTelN_liftTelN] at hidxPrivate
  have hidxLen :
      (r₀.indices.map (VExpr.instL ls)).length =
        (VExpr.liftTelN
          (r₀.fieldIndex + r₀.binders.length) gen.idxTel 0).length := by
    simp only [List.length_map, VExpr.liftTelN_length,
      GenerationChecked.idxTel]
    exact (S.viewRecArg_indices_length hctor hr₀).trans
      gen.shape.2.2.1.symm
  have hspRaw :=
    hidxPrivate.spine_sort S.ord hspGeneration hidxLen
  have W₁ := Ctx.LiftN.consTel (n := mid.length)
    ((ctor.fieldsR source.uvars source.nparams gen.elimination).take
      r₀.fieldIndex)
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [hjlen, Nat.add_zero] at W₁
  have htel₂ := htelGeneration.weakN S.ord W₁
  have hsp₂ := hspRaw.weakN S.ord
    (Ctx.LiftN.consTel
      (r₀.binders.map (VExpr.instL ls)) W₁)
  rw [hg] at htel₂ hsp₂
  have W₂ := Ctx.LiftN.zero
    (Γ := (VExpr.liftTelN g
        ((ctor.fieldsR source.uvars source.nparams gen.elimination).take
          r₀.fieldIndex) 0).reverse ++
      (mid ++ gen.paramsTel.reverse)) As₂ (h := hd)
  have htel₃ := htel₂.weakN S.ord W₂
  have hsp₃ := hsp₂.weakN S.ord
    (Ctx.LiftN.consTel
      (VExpr.liftTelN g
        (r₀.binders.map (VExpr.instL ls)) r₀.fieldIndex) W₂)
  refine ⟨?_, ?_⟩
  · simpa [ls, RecArg.instL, List.append_assoc] using htel₃
  · simp only [List.length_map, VExpr.liftTelN_length,
      Nat.add_zero] at hsp₃
    rw [VExpr.liftN_forallN, VExpr.liftN_forallN,
      VExpr.liftTelN_liftTelN_hi'
        (r₀.fieldIndex + r₀.binders.length) g _ 0 (by omega),
      VExpr.liftTelN_liftTelN_mid
        (r₀.fieldIndex + r₀.binders.length + g) d _ 0
        r₀.binders.length (Nat.zero_le _) (by omega)] at hsp₃
    rw [show r₀.binders.length + r₀.fieldIndex =
      r₀.fieldIndex + r₀.binders.length from Nat.add_comm _ _] at hsp₃
    simpa [ls, RecArg.instL, VExpr.instL, VExpr.liftN,
      List.map_map, Function.comp_def, List.append_assoc] using hsp₃

end GenerationEnv

/-- Syntactic lifting law for the mixed motive. -/
theorem GenerationChecked.motiveType_liftN {source : VInductDecl}
    (gen : GenerationChecked source) (n : Nat) :
    gen.motiveType.liftN n =
      VExpr.forallN (VExpr.liftTelN n gen.idxTel 0)
        (.forallE
          (VExpr.appN
            (.const gen.block.sourceType.name
              (gen.sourceLevels))
            (VExpr.bvarRevRange (n + gen.idxTel.length)
                source.nparams ++
              VExpr.bvarRevRange 0 gen.idxTel.length))
          (.sort gen.motiveLevel)) := by
  rw [show gen.motiveType =
      VExpr.forallN gen.idxTel
        (.forallE
          (VExpr.appN
            (.const gen.block.sourceType.name
              (gen.sourceLevels))
            (VExpr.bvarRevRange gen.idxTel.length source.nparams ++
              VExpr.bvarRevRange 0 gen.idxTel.length))
          (.sort gen.motiveLevel)) from rfl,
    VExpr.liftN_forallN]
  refine congrArg _ ?_
  show VExpr.forallE _ _ = VExpr.forallE _ _
  refine congr (congrArg _ ?_) rfl
  rw [VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
  rfl

/-- Apply a mixed motive variable to a raw-index spine and a typed family
major. -/
theorem GenerationChecked.motiveVarApp_hasType {source : VInductDecl}
    (gen : GenerationChecked source) {env : VEnv} {l : VLevel}
    {Γ : List VExpr} {K : Nat} {idxs : List VExpr} {a : VExpr}
    (hM : env.HasType (gen.recUvars) Γ (.bvar K)
      (gen.motiveType.liftN (K+1)))
    (hidx : env.SpineWF (gen.recUvars) Γ
      (VExpr.forallN (VExpr.liftTelN (K+1) gen.idxTel 0)
        (.sort l))
      idxs (.sort l))
    (hlen : idxs.length = gen.idxTel.length)
    (ha : env.HasType (gen.recUvars) Γ a
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange (K+1) source.nparams ++ idxs))) :
    env.HasType (gen.recUvars) Γ
      (VExpr.appN (.bvar K) (idxs ++ [a])) (.sort gen.motiveLevel) := by
  rw [gen.motiveType_liftN] at hM
  have hshape := hidx.retarget
    (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange (K+1 + gen.idxTel.length)
            source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length))
      (.sort gen.motiveLevel))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _
      (C := .const gen.block.sourceType.name
        (gen.sourceLevels)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show K+1+gen.idxTel.length-idxs.length = K+1 from by
      rw [hlen, Nat.add_sub_cancel],
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hApp := hshape.hasType_appN hM
  rw [VExpr.appN_append]
  exact HasType.app hApp (by simpa using ha)

/-- Mixed minor generation preserves constructor-list arity at every suffix
depth. -/
theorem GenerationChecked.minorTypesAux_length
    {source : VInductDecl} (gen : GenerationChecked source) :
    ∀ (ctors : List NormalizedCtor) (i : Nat),
      (gen.minorTypesAux ctors i).length = ctors.length
  | [], _ => rfl
  | _ :: ctors, i => by
    simp [GenerationChecked.minorTypesAux,
      gen.minorTypesAux_length ctors (i+1)]

/-- The complete mixed minor telescope has one entry per paired raw/view
constructor. -/
theorem GenerationChecked.minorTypes_length
    {source : VInductDecl} (gen : GenerationChecked source) :
    gen.minorTypes.length = gen.block.ctorPairs.length := by
  simpa [GenerationChecked.minorTypes] using
    gen.minorTypesAux_length gen.block.ctorPairs 0

/-- Positional lookup through mixed minor generation. -/
theorem GenerationChecked.minorTypesAux_getElem?
    {source : VInductDecl} (gen : GenerationChecked source) :
    ∀ (ctors : List NormalizedCtor) (i q : Nat),
      (gen.minorTypesAux ctors i)[q]? =
        ctors[q]?.map fun ctor =>
          VExpr.liftN (i+q)
            (GenerationChecked.minorType
              (source := source) ctor gen.elimination)
  | [], _, q => by simp [GenerationChecked.minorTypesAux]
  | _ :: _, _, 0 => by simp [GenerationChecked.minorTypesAux]
  | _ :: ctors, i, q+1 => by
    simp only [GenerationChecked.minorTypesAux,
      List.getElem?_cons_succ]
    rw [gen.minorTypesAux_getElem? ctors (i+1) q,
      show i+1+q = i+(q+1) by omega]

namespace GenerationEnv

variable {source : VInductDecl} {gen : GenerationChecked source}
  {env : VEnv} (S : GenerationEnv gen env)
include S
-- `S` is included throughout so every lemma below is reachable as `S.lemma`,
-- including those whose statement and proof never mention it.
set_option linter.unusedSectionVars false

/-- One mixed generalized induction-hypothesis entry is a type. The bound
field keeps its raw domain; `emittedField_defeq` converts it to the retained
recursive-Pi view only at the semantic application point. -/
theorem recArgMinor_isType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hrmem : r ∈ ctor.recArgsR source.uvars gen.elimination)
    (Δ : List VExpr) (p : Nat) (hΔ : Δ.length = p) :
    env.IsType (gen.recUvars)
      (Δ ++
        (VExpr.liftTelN 1
          (ctor.fieldsR source.uvars source.nparams gen.elimination) 0).reverse ++
        (gen.motiveType :: gen.paramsTel.reverse))
      (r.minorIH
        (ctor.fieldsR source.uvars source.nparams gen.elimination).length p) := by
  obtain ⟨r₀, hr₀, rfl⟩ :=
    NormalizedCtor.recArgsR_mem hrmem
  obtain ⟨Bview, hBview, hrec⟩ :=
    S.viewRecArg_data hctor hr₀
  let ls := gen.sourceLevels
  let r := r₀.instL ls
  let Bs := ctor.fieldsR source.uvars source.nparams gen.elimination
  let m := Bs.length
  let j := r₀.fieldIndex
  let Fs := VExpr.liftTelN 1 Bs 0
  let As := r.minorBinders m p
  let idxs := r.indices.map fun e =>
    (e.liftN 1 (r.fieldIndex+r.binders.length)).liftN
      (m-r.fieldIndex+p) r.binders.length
  let Γ := Δ ++ Fs.reverse ++
    (gen.motiveType :: gen.paramsTel.reverse)
  have hjm : j < m := by
    have hview := S.viewRecArg_lt hctor hr₀
    have hfields :=
      (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
    simp only [j, m, Bs, NormalizedCtor.fieldsR_length]
    omega
  have hjraw :
      r₀.fieldIndex < (ctor.rawFields source.nparams).length := by
    simpa [j, m, Bs, NormalizedCtor.fieldsR_length] using hjm
  let Braw := (ctor.rawFields source.nparams)[r₀.fieldIndex]
  have hBraw :
      (ctor.rawFields source.nparams)[r₀.fieldIndex]? =
        some Braw :=
    List.getElem?_eq_getElem hjraw
  have hFsLen : Fs.length = m := by
    simp [Fs, m, VExpr.liftTelN_length]
  have hstackLen :
      (Δ ++ (Fs.drop j).reverse).length = m-j+p := by
    simp only [List.length_append, List.length_reverse,
      List.length_drop, hFsLen, hΔ]
    omega
  have ht := S.recArg_transport hctor hr₀ [gen.motiveType] rfl
    (Δ ++ (Fs.drop j).reverse) hstackLen
  simp only [List.length_singleton, RecArg.instL] at ht
  have hctx :
      (Δ ++ (Fs.drop j).reverse) ++
          ((VExpr.liftTelN 1 (Bs.take j) 0).reverse ++
            ([gen.motiveType] ++ gen.paramsTel.reverse)) = Γ := by
    dsimp only [Γ, Fs]
    rw [← VExpr.liftTelN_take, List.append_assoc,
      ← List.append_assoc
        ((VExpr.liftTelN 1 Bs 0).drop j).reverse,
      ← List.reverse_append, List.take_append_drop,
      List.singleton_append, ← List.append_assoc]
  dsimp only [j] at ht hctx
  have htel : env.OnTel (gen.recUvars) Γ As := by
    rw [hctx] at ht
    simpa [r, As, m, j, Bs, RecArg.instL,
      RecArg.minorBinders] using ht.1
  have hsp : env.SpineWF (gen.recUvars)
      (As.reverse ++ Γ)
      (VExpr.forallN
        (VExpr.liftTelN
          (m+p+r.binders.length+1) gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst ls)))
      idxs
      (.sort (gen.block.checked.resultLevel.inst ls)) := by
    rw [hctx] at ht
    simpa [r, As, idxs, m, j, Bs, ls, RecArg.instL,
      RecArg.minorBinders,
      List.append_assoc,
      show j + r₀.binders.length + 1 + (m-j+p) =
        m+p+r₀.binders.length+1 from by omega] using ht.2
  have hF : Γ[m-1-j+p]? =
      some ((Braw.instL ls).liftN 1 j) := by
    dsimp only [Γ, Fs]
    rw [getElem?_stack_mid Δ
        (VExpr.liftTelN 1 Bs 0).reverse
        (gen.motiveType :: gen.paramsTel.reverse)
        (i := m-1-j+p) (by rw [hΔ]; omega)
        (by simp only [hΔ, List.length_reverse,
          VExpr.liftTelN_length]; omega),
      show m - 1 - j + p - Δ.length = m - 1 - j from by
        rw [hΔ]
        omega,
      List.getElem?_reverse (by rw [hFsLen]; omega),
      VExpr.liftTelN_length,
      show m - 1 - (m - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?,
      NormalizedCtor.fieldsR_getElem?, hBraw]
    simp [ls]
  have hlu := Lookup.of_getElem? hF
  rw [show m-1-j+p+1 = m-j+p from by omega] at hlu
  dsimp only [j, r] at hlu
  have hf0 := VEnv.HasType.bvar
    (env := env) (U := gen.recUvars) hlu
  obtain ⟨u, hdom₀⟩ :=
    S.emittedField_defeq hctor hBraw hBview
  have hdom₁ := hdom₀.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hdomChecked : env.IsDefEq (gen.recUvars)
      ((ctor.fieldsR source.uvars source.nparams gen.elimination |>.take
          r₀.fieldIndex).reverse ++
        (gen.block.checked.params.map (VExpr.instL ls)).reverse)
      (Braw.instL ls) (Bview.instL ls) ((VExpr.sort u).instL ls) := by
    simpa [NormalizedCtor.fieldsR, List.map_append,
      List.map_reverse, List.map_take] using hdom₁
  have hprefix := S.generationFieldPrefix_ctx_rec hctor r₀.fieldIndex
  have hdomGeneration := hdomChecked.defeqDFC S.ord
    (hprefix.symm S.ord)
  have hjlen : (Bs.take r₀.fieldIndex).length =
      r₀.fieldIndex := by
    simp only [Bs, NormalizedCtor.fieldsR,
      List.length_take, List.length_map]
    omega
  have Wmid := Ctx.LiftN.consTel (n := 1)
    (Bs.take r₀.fieldIndex)
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse)
      [gen.motiveType])
  rw [hjlen, Nat.add_zero] at Wmid
  have hdom₂ := hdomGeneration.weakN S.ord Wmid
  have Wstack := Ctx.LiftN.zero
    (Γ := (VExpr.liftTelN 1 (Bs.take j) 0).reverse ++
      ([gen.motiveType] ++ gen.paramsTel.reverse))
    (Δ ++ (Fs.drop j).reverse) (h := hstackLen)
  have hdom₃ := hdom₂.weakN S.ord Wstack
  rw [hctx] at hdom₃
  have hfView := hdom₃.defeq hf0
  have hfield := recArg_minor_fieldType hrec m p
    (by simpa [j] using hjm) gen.elimination
  simp only [RecArg.instL] at hfield
  rw [hfield] at hfView
  have hf := hfView.weakN S.ord
    (Ctx.LiftN.zero (Γ := Γ) As.reverse)
  have hmajor := VEnv.HasType.appN_selfSpine
    (env := env) (U := gen.recUvars)
    (As := As)
    (B := VExpr.appN
      (.const gen.block.sourceType.name ls)
      (VExpr.bvarRevRange
        (m+p+r.binders.length+1) source.nparams ++ idxs))
    (Δ := []) (Γ := Γ) (by
      simpa [As, r, idxs, j, ls, RecArg.instL,
        List.length_reverse, List.map_map,
        Function.comp_def] using hf)
  simp only [List.length_nil, VExpr.liftN_zero,
    List.nil_append] at hmajor
  have hAsLen : As.length = r.binders.length := by
    simp [As, RecArg.minorBinders, VExpr.liftTelN_length]
  change env.HasType (gen.recUvars) (As.reverse ++ Γ)
    ((VExpr.bvar (m-1-r.fieldIndex+p+As.length)).appN
      (VExpr.bvarRevRange 0 As.length))
    (VExpr.appN
      (.const gen.block.sourceType.name ls)
      (VExpr.bvarRevRange
        (m+p+r.binders.length+1) source.nparams ++ idxs)) at hmajor
  rw [hAsLen] at hmajor
  have hMget :
      (As.reverse ++ Γ)[m+p+r.binders.length]? =
        some gen.motiveType := by
    have hM0 := getElem?_rstack3 As.reverse
      (Δ ++ Fs.reverse) gen.motiveType gen.paramsTel.reverse
      (i := m+p+r.binders.length)
      (by
        simp [As, RecArg.minorBinders, r, m, Fs, hΔ,
          VExpr.liftTelN_length, RecArg.instL]
        omega)
    simpa [Γ, List.append_assoc] using hM0
  have hM := VEnv.HasType.bvar
    (env := env) (U := gen.recUvars)
    (Lookup.of_getElem? hMget)
  have hlen : idxs.length = gen.idxTel.length := by
    simpa [idxs, r, RecArg.instL,
      GenerationChecked.idxTel] using
      (S.viewRecArg_indices_length hctor hr₀).trans
        gen.shape.2.2.1.symm
  have hbody := gen.motiveVarApp_hasType
    (l := gen.block.checked.resultLevel.inst ls)
    hM hsp hlen hmajor
  refine IsType.forallN htel ⟨gen.motiveLevel, ?_⟩
  simpa [RecArg.minorIH, r, As, idxs, m, Γ, Fs, Bs,
    List.append_assoc] using hbody

/-- The complete mixed functional-IH telescope is well formed at any suffix
and depth. -/
theorem ihs_onTel {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    ∀ (rsSuf : List RecArg),
    (∀ r ∈ rsSuf, r ∈ ctor.recArgsR source.uvars gen.elimination) →
    ∀ (Δ : List VExpr) (p : Nat), Δ.length = p →
    env.OnTel (gen.recUvars)
      (Δ ++
        (VExpr.liftTelN 1
          (ctor.fieldsR source.uvars source.nparams gen.elimination) 0).reverse ++
        (gen.motiveType :: gen.paramsTel.reverse))
      (ihsFromRecArgs
        (ctor.fieldsR source.uvars source.nparams gen.elimination).length rsSuf p)
  | [], _, _, _, _ => trivial
  | r :: rsSuf, hqs, Δ, p, hΔ =>
    ⟨S.recArgMinor_isType hctor
        (hqs r (.head _)) Δ p hΔ,
      GenerationEnv.ihs_onTel hctor rsSuf
        (fun q hq => hqs q (.tail _ hq))
        (_ :: Δ) (p+1) (by simp [hΔ])⟩

/-- The retained constructor result has exactly the checked family-index
arity. -/
theorem viewResultIndices_length {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    ctor.view.resultIndices.length =
      gen.block.checked.indices.length := by
  obtain ⟨c, hc, hview⟩ := gen.viewCtor_ofDirect hctor
  have hstage :=
    (gen.block.checked.direct_anatomy.2.2.2.2.2 c hc).2.2
  have hlen := (stage3Ctor_eq hstage).2.1
  rw [hview]
  rw [gen.block.nparams_eq]
  simpa [CheckedCtor.ofDirect] using hlen

/-- Checked result-index spine semantics for a paired constructor. -/
theorem viewResultSpine {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.SpineWF source.uvars
      (ctor.view.fields.reverse ++
        gen.block.checked.params.reverse)
      (VExpr.forallN
        (VExpr.liftTelN ctor.view.fields.length
          gen.block.checked.indices 0)
        (.sort gen.block.checked.resultLevel))
      ctor.view.resultIndices
      (.sort gen.block.checked.resultLevel) := by
  obtain ⟨c, hc, hview⟩ := gen.viewCtor_ofDirect hctor
  have h := (S.checked.2 c hc).2
  rw [hview]
  simpa [CheckedCtor.ofDirect, gen.block.uvars_eq,
    gen.block.nparams_eq] using h

/-- Constructor-result semantics transported to the exact emitted
checked-parameter/raw-field context and raw family-index telescope. -/
theorem rawResultSpine {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.SpineWF source.uvars
      ((ctor.rawFields source.nparams).reverse ++
        gen.block.checked.params.reverse)
      (VExpr.forallN
        (VExpr.liftTelN
          (ctor.rawFields source.nparams).length
          gen.block.rawIndices 0)
        (.sort gen.block.checked.resultLevel))
      ctor.view.resultIndices
      (.sort gen.block.checked.resultLevel) := by
  have hctx := (S.ctorWF ctor hctor).emittedTel.ctx
  simp only [NormalizedCtor.emittedBinders,
    NormalizedCtor.viewBinders, List.reverse_append,
    List.append_nil] at hctx
  have hsp := (S.viewResultSpine hctor).defeqDFC S.ord
    (hctx.symm S.ord)
  have hfields :=
    (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
  rw [← hfields] at hsp
  have hidx := S.emittedIndexTel_defeq.weakN S.ord
    (Ctx.LiftN.zero (Γ := gen.block.checked.params.reverse)
      (ctor.rawFields source.nparams).reverse)
  rw [List.length_reverse] at hidx
  have hlen :
      ctor.view.resultIndices.length =
        (VExpr.liftTelN
          (ctor.rawFields source.nparams).length
          gen.block.rawIndices 0).length := by
    simp only [VExpr.liftTelN_length]
    exact (S.viewResultIndices_length hctor).trans
      gen.shape.2.2.1.symm
  exact hidx.spine_sort S.ord hsp hlen

/-- Transport the mixed constructor result spine into a minor or rule
context. -/
theorem result_transport {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.SpineWF (gen.recUvars)
      (As₂ ++
        ((VExpr.liftTelN g
          (ctor.fieldsR source.uvars source.nparams gen.elimination) 0).reverse ++
          (mid ++ gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          ((ctor.fieldsR source.uvars source.nparams gen.elimination).length + g + d)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (gen.sourceLevels))))
      ((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
        (e.liftN g
          (ctor.fieldsR source.uvars source.nparams gen.elimination).length).liftN d)
      (.sort (gen.block.checked.resultLevel.inst
        (gen.sourceLevels))) := by
  let ls := gen.sourceLevels
  have h1 := (S.rawResultSpine hctor).instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have h1Checked : env.SpineWF (gen.recUvars)
      ((ctor.fieldsR source.uvars source.nparams gen.elimination).reverse ++
        (gen.block.checked.params.map (VExpr.instL ls)).reverse)
      (VExpr.instL ls
        (VExpr.forallN
          (VExpr.liftTelN (ctor.rawFields source.nparams).length
            gen.block.rawIndices 0)
          (.sort gen.block.checked.resultLevel)))
      (ctor.view.resultIndices.map (VExpr.instL ls))
      ((VExpr.sort gen.block.checked.resultLevel).instL ls) := by
    simpa [NormalizedCtor.fieldsR, List.map_append,
      List.map_reverse] using h1
  have hfieldsCtx := (S.generationFields_onTel_rec hctor).extendDefEqCtx
    S.generationParams_ctx_rec
  have h1Generation := h1Checked.defeqDFC S.ord
    (hfieldsCtx.symm S.ord)
  rw [VExpr.instL_forallN, VExpr.liftTelN_instL,
    show
      (gen.block.rawIndices.map (VExpr.instL ls)) =
        gen.idxTel by rfl] at h1Generation
  rw [← NormalizedCtor.fieldsR_length
    (source := source) (mode := gen.elimination) ctor] at h1Generation
  have W₁ := Ctx.LiftN.consTel (n := mid.length)
    (ctor.fieldsR source.uvars source.nparams gen.elimination)
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [Nat.add_zero] at W₁
  have h2 := h1Generation.weakN S.ord W₁
  rw [VExpr.liftN_forallN, hg] at h2
  have h3 := h2.weakN S.ord
    (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  rw [VExpr.liftN_forallN] at h3
  rw [VExpr.liftTelN_liftTelN_hi'
      (ctor.fieldsR source.uvars source.nparams gen.elimination).length
      g _ 0 (by omega),
    VExpr.liftTelN_liftTelN] at h3
  simpa [ls, NormalizedCtor.resultIndicesR,
    VExpr.instL, VExpr.liftN, List.map_map,
    Function.comp_def, List.append_assoc] using h3

/-- The exact emitted constructor application transported into recursor
universes, before inserting the motive or any induction-hypothesis stack. -/
theorem ctorApp_emitted_rec {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.HasType (gen.recUvars)
      ((ctor.fieldsR source.uvars source.nparams gen.elimination).reverse ++
        gen.paramsTel.reverse)
      (VExpr.appN
        (.const ctor.raw.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (ctor.fieldsR source.uvars source.nparams gen.elimination).length
            source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.fieldsR source.uvars source.nparams gen.elimination).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (ctor.fieldsR source.uvars source.nparams gen.elimination).length
            source.nparams ++
          ctor.resultIndicesR source.uvars gen.elimination)) := by
  let ls := gen.sourceLevels
  have h := (S.ctorApp_emitted_decl hctor).instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hChecked : env.HasType (gen.recUvars)
      ((ctor.fieldsR source.uvars source.nparams gen.elimination).reverse ++
        (gen.block.checked.params.map (VExpr.instL ls)).reverse)
      ((VExpr.appN
        (.const ctor.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
          (ctor.rawFields source.nparams).length source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.rawFields source.nparams).length)).instL ls)
      ((ctor.resultTarget gen.block).instL ls) := by
    simpa [NormalizedCtor.fieldsR, List.map_append,
      List.map_reverse] using h
  have hfieldsCtx := (S.generationFields_onTel_rec hctor).extendDefEqCtx
    S.generationParams_ctx_rec
  have hGeneration := hChecked.defeqDFC S.ord
    (hfieldsCtx.symm S.ord)
  rw [← NormalizedCtor.fieldsR_length
    (source := source) (mode := gen.elimination) ctor] at hGeneration
  simpa [ls, NormalizedCtor.fieldsR,
    GenerationChecked.paramsTel,
    NormalizedCtor.resultTarget,
    NormalizedCtor.resultIndicesR,
    VExpr.instL_appN, List.map_append,
    bvarRevRange_instL, List.map_reverse,
    VExpr.instL, VLevel.params_map_inst_params'] using hGeneration

/-- Transport the emitted constructor application under binders inserted
between parameters and fields, then under an arbitrary top stack. -/
theorem ctorApp_transport {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.HasType (gen.recUvars)
      (As₂ ++
        ((VExpr.liftTelN g
          (ctor.fieldsR source.uvars source.nparams gen.elimination) 0).reverse ++
          (mid ++ gen.paramsTel.reverse)))
      (VExpr.appN
        (.const ctor.raw.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (d + (g +
              (ctor.fieldsR source.uvars source.nparams gen.elimination).length))
            source.nparams ++
          VExpr.bvarRevRange d
            (ctor.fieldsR source.uvars source.nparams gen.elimination).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (d + (g +
              (ctor.fieldsR source.uvars source.nparams gen.elimination).length))
            source.nparams ++
          (ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            (e.liftN g
              (ctor.fieldsR source.uvars source.nparams gen.elimination).length).liftN d)) := by
  let Bs := ctor.fieldsR source.uvars source.nparams gen.elimination
  have W₁ := Ctx.LiftN.consTel (n := mid.length) Bs
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [Nat.add_zero] at W₁
  have h₁ := (S.ctorApp_emitted_rec hctor).weakN S.ord W₁
  rw [hg] at h₁
  have hmid : env.HasType (gen.recUvars)
      ((VExpr.liftTelN g Bs 0).reverse ++
        (mid ++ gen.paramsTel.reverse))
      (VExpr.appN
        (.const ctor.raw.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange (g + Bs.length) source.nparams ++
          VExpr.bvarRevRange 0 Bs.length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange (g + Bs.length) source.nparams ++
          (ctor.resultIndicesR source.uvars gen.elimination).map
            (VExpr.liftN g · Bs.length))) := by
    simpa [Bs, VExpr.liftN_appN, List.map_append,
      bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
      VExpr.bvarRevRange_liftN_high
        Bs.length 0 g Bs.length (by omega),
      VExpr.liftN] using h₁
  have htop := hmid.weakN S.ord
    (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  simpa [Bs, VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
    VExpr.liftN, List.map_map, Function.comp_def,
    List.append_assoc] using htop

/-- Constructor application in the exact mixed minor-premise context. -/
theorem ctorAppMinor_hasType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) (Δ : List VExpr) :
    env.HasType (gen.recUvars)
      (Δ ++
        (VExpr.liftTelN 1
          (ctor.fieldsR source.uvars source.nparams gen.elimination) 0).reverse ++
        (gen.motiveType :: gen.paramsTel.reverse))
      (VExpr.appN
        (.const ctor.raw.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (Δ.length +
              (ctor.fieldsR source.uvars source.nparams gen.elimination).length + 1)
            source.nparams ++
          VExpr.bvarRevRange Δ.length
            (ctor.fieldsR source.uvars source.nparams gen.elimination).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (Δ.length +
              (ctor.fieldsR source.uvars source.nparams gen.elimination).length + 1)
            source.nparams ++
          (ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            (e.liftN 1
              (ctor.fieldsR source.uvars source.nparams gen.elimination).length).liftN
                Δ.length)) := by
  have h := S.ctorApp_transport hctor [gen.motiveType]
    (g := 1) rfl Δ (d := Δ.length) rfl
  rw [VExpr.bvarRevRange_congr source.nparams
    (show
      Δ.length +
          (1 +
            (ctor.fieldsR source.uvars source.nparams gen.elimination).length) =
        Δ.length +
          (ctor.fieldsR source.uvars source.nparams gen.elimination).length + 1 by
      omega)] at h
  simpa [List.append_assoc] using h

/-- The exact raw field telescope used by a mixed minor is well formed after
universe instantiation and insertion of the motive. -/
theorem fields_onTel_minor {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.OnTel (gen.recUvars)
      (gen.motiveType :: gen.paramsTel.reverse)
      (VExpr.liftTelN 1
        (ctor.fieldsR source.uvars source.nparams gen.elimination) 0) := by
  have hout := (S.generationFields_onTel_rec hctor).weakN S.ord
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse)
      [gen.motiveType])
  simpa using hout

/-- Every mixed constructor minor is a type over the checked parameter telescope
and mixed motive. Raw field syntax is preserved; recursive classifications
and result indices come from the checked view. -/
theorem minor_isType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.IsType (gen.recUvars)
      (gen.motiveType :: gen.paramsTel.reverse)
      (GenerationChecked.minorType
        (source := source) ctor gen.elimination) := by
  let Bs := ctor.fieldsR source.uvars source.nparams gen.elimination
  let m := Bs.length
  let rs := ctor.recArgsR source.uvars gen.elimination
  let IHs := ihsFromRecArgs m rs 0
  let Fs := VExpr.liftTelN 1 Bs 0
  let Γ := IHs.reverse ++
    (Fs.reverse ++
      (gen.motiveType :: gen.paramsTel.reverse))
  simp only [GenerationChecked.minorType]
  refine IsType.forallN (by
    simpa [Bs] using S.fields_onTel_minor hctor) ?_
  refine IsType.forallN (by
    simpa [Bs, m, rs, IHs, Fs, List.append_assoc] using
      S.ihs_onTel hctor rs (fun r hr => hr) [] 0 rfl) ?_
  have hrlen : IHs.reverse.length = rs.length := by
    simp [IHs, ihsFromRecArgs_length]
  have hMget : Γ[m + rs.length]? =
      some gen.motiveType := by
    have h := getElem?_rstack3 IHs.reverse Fs.reverse
      gen.motiveType gen.paramsTel.reverse
      (i := m + rs.length)
      (by
        simp [IHs, Fs, m, ihsFromRecArgs_length,
          VExpr.liftTelN_length]
        omega)
    simpa [Γ] using h
  have hM : env.HasType (gen.recUvars) Γ
      (.bvar (m + rs.length))
      (gen.motiveType.liftN (m + rs.length + 1)) :=
    VEnv.HasType.bvar (Lookup.of_getElem? hMget)
  have hSp := S.result_transport hctor [gen.motiveType]
    (g := 1) rfl IHs.reverse
    (d := rs.length) hrlen
  rw [show m + 1 + rs.length =
    m + rs.length + 1 by omega] at hSp
  have hSp' : env.SpineWF (gen.recUvars) Γ
      (VExpr.forallN
        (VExpr.liftTelN (m + rs.length + 1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (gen.sourceLevels))))
      ((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
        (e.liftN 1 m).liftN rs.length)
      (.sort (gen.block.checked.resultLevel.inst
        (gen.sourceLevels))) := by
    simpa [Γ, Fs, Bs, m, List.append_assoc] using hSp
  have hlen :
      ((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
        (e.liftN 1 m).liftN rs.length).length =
        gen.idxTel.length := by
    simp only [List.length_map, NormalizedCtor.resultIndicesR,
      GenerationChecked.idxTel]
    exact (S.viewResultIndices_length hctor).trans
      gen.shape.2.2.1.symm
  have hctorApp := S.ctorAppMinor_hasType hctor IHs.reverse
  rw [hrlen,
    VExpr.bvarRevRange_congr source.nparams
      (show rs.length + m + 1 = m + rs.length + 1 by omega)] at hctorApp
  have hctorApp' : env.HasType (gen.recUvars) Γ
      (VExpr.appN
        (.const ctor.raw.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (m + rs.length + 1) source.nparams ++
          VExpr.bvarRevRange rs.length m))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (m + rs.length + 1) source.nparams ++
          (ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            (e.liftN 1 m).liftN rs.length)) := by
    simpa [Γ, Fs, Bs, m, IHs, rs,
      List.append_assoc] using hctorApp
  have hbody := gen.motiveVarApp_hasType hM hSp' hlen hctorApp'
  rw [VExpr.bvarRevRange_congr source.nparams
    (show m + rs.length + 1 =
      rs.length + m + 1 by omega)] at hbody
  exact ⟨gen.motiveLevel, by
    simpa [Γ, Fs, Bs, m, rs, IHs,
      List.append_assoc] using hbody⟩

/-- The checked parameter telescope is well formed in recursor universes. -/
theorem paramsTel_onTel :
    env.OnTel (gen.recUvars) [] gen.paramsTel := by
  have h := S.generationFamily_onTel.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have h' : env.OnTel (gen.recUvars) []
      (gen.paramsTel ++ gen.idxTel) := by
    simpa [GenerationChecked.paramsTel,
      GenerationChecked.idxTel] using h
  exact h'.of_append.1

/-- The raw index telescope is well formed over the checked parameters. -/
theorem idxTel_onTel :
    env.OnTel (gen.recUvars)
      gen.paramsTel.reverse gen.idxTel := by
  have h := S.generationFamily_onTel.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have h' : env.OnTel (gen.recUvars) []
      (gen.paramsTel ++ gen.idxTel) := by
    simpa [GenerationChecked.paramsTel,
      GenerationChecked.idxTel] using h
  simpa using h'.of_append.2

/-- Any suffix of paired constructors generates a well-formed mixed minor
telescope at its positional depth. -/
theorem minorTypesAux_onTel :
    ∀ (ctors : List NormalizedCtor),
      (∀ ctor ∈ ctors, ctor ∈ gen.block.ctorPairs) →
      ∀ (Δ : List VExpr) (i : Nat), Δ.length = i →
        env.OnTel (gen.recUvars)
          (Δ ++
            (gen.motiveType :: gen.paramsTel.reverse))
          (gen.minorTypesAux ctors i)
  | [], _, _, _, _ => trivial
  | ctor :: ctors, hsub, Δ, i, hΔ =>
    ⟨by
      rw [← hΔ]
      exact (S.minor_isType
        (hsub ctor (.head _))).weakN S.ord
          (.zero Δ),
    GenerationEnv.minorTypesAux_onTel ctors
      (fun ctor hctor => hsub ctor (.tail _ hctor))
      (_ :: Δ) (i+1) (by simp [hΔ])⟩

/-- The complete mixed minor telescope is well formed over parameters and
motive. -/
theorem minorTypes_onTel :
    env.OnTel (gen.recUvars)
      (gen.motiveType :: gen.paramsTel.reverse)
      gen.minorTypes := by
  simpa [GenerationChecked.minorTypes] using
    S.minorTypesAux_onTel gen.block.ctorPairs
      (fun _ h => h) [] 0 rfl

/-- Transport the fully applied raw family under binders inserted below its
indices and then under an arbitrary top stack. -/
theorem familyApp_transport
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.HasType (gen.recUvars)
      (As₂ ++
        ((VExpr.liftTelN g gen.idxTel 0).reverse ++
          (mid ++ gen.paramsTel.reverse)))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (d + (g + gen.idxTel.length))
            source.nparams ++
          VExpr.bvarRevRange d gen.idxTel.length))
      (.sort (gen.block.checked.resultLevel.inst
        (gen.sourceLevels))) := by
  have W₁ := Ctx.LiftN.consTel (n := mid.length) gen.idxTel
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [Nat.add_zero] at W₁
  have h₁ := S.familyApp_hasType.weakN S.ord W₁
  rw [hg] at h₁
  have hmid : env.HasType (gen.recUvars)
      ((VExpr.liftTelN g gen.idxTel 0).reverse ++
        (mid ++ gen.paramsTel.reverse))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (g + gen.idxTel.length) source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length))
      (.sort (gen.block.checked.resultLevel.inst
        (gen.sourceLevels))) := by
    simpa [VExpr.liftN_appN, List.map_append,
      bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
      VExpr.bvarRevRange_liftN_high
        gen.idxTel.length 0 g gen.idxTel.length (by omega),
      VExpr.liftN] using h₁
  have htop := hmid.weakN S.ord
    (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  simpa [VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
    VExpr.liftN, List.append_assoc] using htop

/-- The mixed recursor type is well formed. Its telescope retains raw
parameter and index syntax while its motive and minors use the checked
recursive classification. -/
theorem recType_isType :
    env.IsType (gen.recUvars) [] gen.recType := by
  refine IsType.forallN S.paramsTel_onTel ?_
  simp only [List.append_nil]
  refine IsType.forallE S.motive_isType ?_
  refine IsType.forallN S.minorTypes_onTel ?_
  have hI : env.OnTel (gen.recUvars)
      (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse))
      (VExpr.liftTelN (gen.block.ctorPairs.length + 1)
        gen.idxTel 0) := by
    have h := S.idxTel_onTel.weakN S.ord
      (Ctx.LiftN.zero
        (n := gen.block.ctorPairs.length + 1)
        (Γ := gen.paramsTel.reverse)
        (gen.minorTypes.reverse ++ [gen.motiveType])
        (h := by simp [gen.minorTypes_length]))
    simpa [List.append_assoc] using h
  refine IsType.forallN hI ?_
  have hmaj₀ := S.familyApp_transport
    (gen.minorTypes.reverse ++ [gen.motiveType])
    (g := gen.block.ctorPairs.length + 1)
    (by simp [gen.minorTypes_length])
    [] (d := 0) rfl
  rw [VExpr.bvarRevRange_congr source.nparams
    (show
      0 + ((gen.block.ctorPairs.length + 1) +
        gen.idxTel.length) =
      gen.idxTel.length + gen.block.ctorPairs.length + 1 by omega)] at hmaj₀
  have hmaj : env.HasType (gen.recUvars)
      ((VExpr.liftTelN (gen.block.ctorPairs.length + 1)
          gen.idxTel 0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (gen.idxTel.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length))
      (.sort (gen.block.checked.resultLevel.inst
        (gen.sourceLevels))) := by
    simpa [List.append_assoc] using hmaj₀
  refine IsType.forallE ⟨_, hmaj⟩ ?_
  have hM := getElem?_rstack3
    [VExpr.appN
      (.const gen.block.sourceType.name
        (gen.sourceLevels))
      (VExpr.bvarRevRange
          (gen.idxTel.length +
            gen.block.ctorPairs.length + 1)
          source.nparams ++
        VExpr.bvarRevRange 0 gen.idxTel.length)]
    ((VExpr.liftTelN (gen.block.ctorPairs.length + 1)
        gen.idxTel 0).reverse ++
      gen.minorTypes.reverse)
    gen.motiveType gen.paramsTel.reverse
    (i := gen.idxTel.length +
      gen.block.ctorPairs.length + 1)
    (by
      simp only [List.length_singleton, List.length_append,
        List.length_reverse, VExpr.liftTelN_length,
        gen.minorTypes_length]
      omega)
  have hmlu := Lookup.of_getElem? (by
    simpa only [List.singleton_append,
      List.append_assoc] using hM)
  rw [show gen.motiveType.liftN
        (gen.idxTel.length +
          gen.block.ctorPairs.length + 1 + 1) =
      (gen.motiveType.liftN
        (gen.block.ctorPairs.length + 1)).liftN
          (gen.idxTel.length + 1) from by
      rw [VExpr.liftN_liftN]
      congr 1
      omega,
    gen.motiveType_liftN] at hmlu
  have hfun : env.HasType (gen.recUvars)
      (VExpr.appN
          (.const gen.block.sourceType.name
            (gen.sourceLevels))
          (VExpr.bvarRevRange
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length) ::
        ((VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            gen.idxTel 0).reverse ++
          (gen.minorTypes.reverse ++
            (gen.motiveType :: gen.paramsTel.reverse))))
      (.bvar
        (gen.idxTel.length +
          gen.block.ctorPairs.length + 1))
      ((VExpr.forallN
        (VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.forallE
          (VExpr.appN
            (.const gen.block.sourceType.name
              (gen.sourceLevels))
            (VExpr.bvarRevRange
                (gen.block.ctorPairs.length + 1 +
                  gen.idxTel.length)
                source.nparams ++
              VExpr.bvarRevRange 0 gen.idxTel.length))
          (.sort gen.motiveLevel))).liftN
        (1 + (VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          gen.idxTel 0).length)) := by
    exact .bvar (by
      simpa [List.append_assoc, VExpr.liftTelN_length,
        Nat.add_comm] using hmlu)
  have hMapp := HasType.appN_selfSpine
    (As := VExpr.liftTelN
      (gen.block.ctorPairs.length + 1)
      gen.idxTel 0)
    (Δ := [VExpr.appN
      (.const gen.block.sourceType.name
        (gen.sourceLevels))
      (VExpr.bvarRevRange
          (gen.idxTel.length +
            gen.block.ctorPairs.length + 1)
          source.nparams ++
        VExpr.bvarRevRange 0 gen.idxTel.length)])
    (Γ := gen.minorTypes.reverse ++
      (gen.motiveType :: gen.paramsTel.reverse))
    (f := .bvar
      (gen.idxTel.length +
        gen.block.ctorPairs.length + 1))
    hfun
  have h0 :
      (VExpr.appN
          (.const gen.block.sourceType.name
            (gen.sourceLevels))
          (VExpr.bvarRevRange
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length) ::
        ((VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            gen.idxTel 0).reverse ++
          (gen.minorTypes.reverse ++
            (gen.motiveType :: gen.paramsTel.reverse))))[0]? =
        some (VExpr.appN
          (.const gen.block.sourceType.name
            (gen.sourceLevels))
          (VExpr.bvarRevRange
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length)) := rfl
  have harg := HasType.bvar
    (env := env) (U := gen.recUvars)
    (Lookup.of_getElem? h0)
  have harg' : env.HasType (gen.recUvars)
      ([VExpr.appN
          (.const gen.block.sourceType.name
            (gen.sourceLevels))
          (VExpr.bvarRevRange
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length)] ++
        (VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          gen.idxTel 0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (.bvar 0)
      ((VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (gen.block.ctorPairs.length + 1 +
              gen.idxTel.length)
            source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length)).liftN 1) := by
    simpa [List.append_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using harg
  have happ := HasType.app hMapp harg'
  exact ⟨_, by
    simpa [GenerationChecked.recType, List.append_assoc,
      VExpr.liftTelN_length] using happ⟩

/-- The mixed generated recursor constant is well formed. -/
theorem recursor_wf : gen.recursor.WF env :=
  S.recType_isType

end GenerationEnv

theorem minorTypes_getElem? {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    ∀ (cs : List VConstVal) (i₀ q : Nat),
    (minorTypes U T np ty cs i₀)[q]? =
      cs[q]?.map fun c => VExpr.liftN (i₀+q) (minorType U T np ty c)
  | [], _, q => by simp [minorTypes]
  | c :: cs, i₀, 0 => by simp [minorTypes]
  | c :: cs, i₀, q+1 => by
    simp only [minorTypes, List.getElem?_cons_succ]
    rw [minorTypes_getElem? cs (i₀+1) q, show i₀+1+q = i₀+(q+1) from by omega]

theorem minorTypesRec_getElem? {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    ∀ (cs : List VConstVal) (i₀ q : Nat),
    (minorTypesRec U T np ty cs i₀)[q]? =
      cs[q]?.map fun c => VExpr.liftN (i₀+q) (minorTypeRec U T np ty c)
  | [], _, q => by simp [minorTypesRec]
  | c :: cs, i₀, 0 => by simp [minorTypesRec]
  | c :: cs, i₀, q+1 => by
    simp only [minorTypesRec, List.getElem?_cons_succ]
    rw [minorTypesRec_getElem? cs (i₀+1) q,
      show i₀+1+q = i₀+(q+1) from by omega]

theorem recApp'_levelWF {U : Nat} {T : Name} {np off : Nat} :
    (recApp' U T np off).LevelWF (U+1) :=
  VExpr.LevelWF.appN (f := .const T (VLevel.params' U 1)) VLevel.params'_one_wf
    (bvarRevRange_levelWF _ _)

theorem idxTel_length {U np : Nat} {ty : VInductiveType} :
    (idxTel U np ty).length = (ctorFields (VExpr.dropN np ty.type)).length :=
  List.length_map ..

theorem idxTel_levelWF {U np : Nat} {ty : VInductiveType} :
    ∀ A ∈ idxTel U np ty, A.LevelWF (U+1) := by
  intro A hA
  obtain ⟨A₀, -, rfl⟩ := List.mem_map.1 hA
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

theorem ctorIdxs_length {U np : Nat} {c : VConstVal} :
    (ctorIdxs U np c).length =
      (recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))).length :=
  List.length_map ..

theorem ctorIdxs_levelWF {U np : Nat} {c : VConstVal} :
    ∀ e ∈ ctorIdxs U np c, e.LevelWF (U+1) := by
  intro e he
  obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

theorem recPairsR_lt {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} :
    ∀ q ∈ recPairsR U T np ni c, q.1 < (ctorFields (VExpr.dropN np c.type)).length := by
  intro q hq
  obtain ⟨⟨j, idxs⟩, hmem, rfl⟩ := List.mem_map.1 hq
  simpa using recPairs_lt _ hmem

theorem recPairsR_idx_levelWF {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} :
    ∀ q ∈ recPairsR U T np ni c, ∀ e ∈ q.2, e.LevelWF (U+1) := by
  intro q hq e he
  obtain ⟨⟨j, idxs⟩, -, rfl⟩ := List.mem_map.1 hq
  obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

/-- Unpack a recursor-universe recursive position: the underlying field and
its (declaration-universe) index arguments. -/
theorem recPairsR_mem {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} {q}
    (hq : q ∈ recPairsR U T np ni c) :
    ∃ B, (ctorFields (VExpr.dropN np c.type))[q.1]? = some B ∧
      isRecField U T np ni q.1 B = true ∧
      q.2 = (recFieldIdxs np B).map (VExpr.instL (VLevel.params' U 1)) := by
  obtain ⟨⟨j, idxs⟩, hmem, rfl⟩ := List.mem_map.1 hq
  obtain ⟨B, hB, hrec, hidx⟩ := recPairs_getElem _ hmem
  exact ⟨B, by simpa using hB, hrec, by
    simpa using congrArg
      (List.map (VExpr.instL (ElimMode.large.sourceLevels U))) hidx⟩

/-- Recursor-universe transport preserves each recursive argument's source
field position. -/
theorem recArgsR_lt {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} :
    ∀ r ∈ recArgsR U T np ni c,
      r.fieldIndex < (ctorFields (VExpr.dropN np c.type)).length := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
  simpa [RecArg.instL] using recArgs_lt _ hr₀

/-- Every generated recursive-target index is level-well-formed in the
recursor universe context. -/
theorem recArgsR_idx_levelWF {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} :
    ∀ r ∈ recArgsR U T np ni c, ∀ e ∈ r.indices, e.LevelWF (U+1) := by
  intro r hr e he
  obtain ⟨r₀, -, rfl⟩ := List.mem_map.1 hr
  obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

/-- Every generated recursive-Pi domain is level-well-formed after universe
transport. -/
theorem recArgsR_binder_levelWF {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} :
    ∀ r ∈ recArgsR U T np ni c, ∀ A ∈ r.binders, A.LevelWF (U+1) := by
  intro r hr A hA
  obtain ⟨r₀, -, rfl⟩ := List.mem_map.1 hr
  obtain ⟨A₀, -, rfl⟩ := List.mem_map.1 hA
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

/-- Unpack a recursor-universe recursive descriptor to the source field and
its declaration-universe analysis result. -/
theorem recArgsR_mem {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} {r}
    (hr : r ∈ recArgsR U T np ni c) :
    ∃ r₀ B, r = r₀.instL (VLevel.params' U 1) ∧
      (ctorFields (VExpr.dropN np c.type))[r₀.fieldIndex]? = some B ∧
      recArg? U T np ni r₀.fieldIndex B = some r₀ := by
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
  obtain ⟨B, hB, hrec⟩ := recArgs_getElem _ hr₀
  exact ⟨r₀, B, rfl, by simpa using hB, hrec⟩

theorem motiveType_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    (motiveType U T np ty).LevelWF (U+1) := by
  refine VExpr.LevelWF.forallN idxTel_levelWF ⟨?_, Nat.succ_pos U⟩
  refine VExpr.LevelWF.appN (f := .const T (VLevel.params' U 1)) VLevel.params'_one_wf
    fun e h => ?_
  rcases List.mem_append.1 h with h | h
  · exact bvarRevRange_levelWF _ _ _ h
  · exact bvarRevRange_levelWF _ _ _ h

theorem motiveType_liftN {U : Nat} {T : Name} {np n : Nat} {ty : VInductiveType} :
    (motiveType U T np ty).liftN n =
    VExpr.forallN (VExpr.liftTelN n (idxTel U np ty) 0)
      (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (n + (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.sort (.param 0))) := by
  rw [show motiveType U T np ty = VExpr.forallN (idxTel U np ty)
      (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (idxTel U np ty).length np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.sort (.param 0))) from rfl,
    VExpr.liftN_forallN]
  refine congrArg _ ?_
  show VExpr.forallE _ _ = VExpr.forallE _ _
  refine congr (congrArg _ ?_) rfl
  rw [VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
  rfl

theorem liftTelN_levelWF {Uv n : Nat} : ∀ {tel : List VExpr} {k : Nat},
    (∀ A ∈ tel, A.LevelWF Uv) → ∀ A ∈ VExpr.liftTelN n tel k, A.LevelWF Uv
  | [], _, _, _, h => nomatch h
  | _ :: tel, k, hAs, A', h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact (hAs _ (.head _)).liftN
    · exact liftTelN_levelWF (fun A h => hAs _ (.tail _ h)) A' h

theorem RecArg.minorBinders_levelWF {Uv m p : Nat} {r : RecArg}
    (hbind : ∀ A ∈ r.binders, A.LevelWF Uv) :
    ∀ A ∈ r.minorBinders m p, A.LevelWF Uv :=
  liftTelN_levelWF (liftTelN_levelWF hbind)

theorem RecArg.minorIH_levelWF {Uv m p : Nat} {r : RecArg}
    (hbind : ∀ A ∈ r.binders, A.LevelWF Uv)
    (hidx : ∀ e ∈ r.indices, e.LevelWF Uv) :
    (r.minorIH m p).LevelWF Uv := by
  simp only [RecArg.minorIH]
  refine VExpr.LevelWF.forallN (r.minorBinders_levelWF hbind)
    (VExpr.LevelWF.appN (f := .bvar _) trivial fun e he => ?_)
  rcases List.mem_append.1 he with he | he
  · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    exact ((hidx e₀ he₀).liftN).liftN
  · rcases List.mem_cons.1 he with rfl | he
    · exact VExpr.LevelWF.appN (f := .bvar _) trivial (bvarRevRange_levelWF _ _)
    · cases he

theorem ihsFromRecArgs_levelWF {Uv m : Nat} :
    ∀ (rs : List RecArg) (p : Nat),
    (∀ r ∈ rs, ∀ A ∈ r.binders, A.LevelWF Uv) →
    (∀ r ∈ rs, ∀ e ∈ r.indices, e.LevelWF Uv) →
    ∀ e ∈ ihsFromRecArgs m rs p, e.LevelWF Uv
  | [], _, _, _, _, h => nomatch h
  | r :: rs, p, hbind, hidx, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact r.minorIH_levelWF
        (hbind r (.head _)) (hidx r (.head _))
    · exact ihsFromRecArgs_levelWF rs (p+1)
        (fun q hq => hbind q (.tail _ hq))
        (fun q hq => hidx q (.tail _ hq)) e h

theorem minorType_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType}
    {c : VConstVal} : (minorType U T np ty c).LevelWF (U+1) := by
  simp only [minorType]
  refine VExpr.LevelWF.forallN (liftTelN_levelWF fun B hB => ?_)
    (VExpr.LevelWF.forallN (ihsFrom_levelWF _ _ recPairsR_idx_levelWF) ?_)
  · obtain ⟨B₀, _, rfl⟩ := List.mem_map.1 hB
    exact VExpr.LevelWF.instL VLevel.params'_one_wf
  · refine VExpr.LevelWF.appN (f := .bvar _) trivial fun e h => ?_
    rcases List.mem_append.1 h with h | h
    · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 h
      exact ((ctorIdxs_levelWF _ he₀).liftN).liftN
    · rcases List.mem_cons.1 h with rfl | h
      · refine VExpr.LevelWF.appN (f := .const c.name (VLevel.params' U 1))
          VLevel.params'_one_wf fun e h => ?_
        rcases List.mem_append.1 h with h | h
        · exact bvarRevRange_levelWF _ _ _ h
        · exact bvarRevRange_levelWF _ _ _ h
      · cases h

theorem minorTypeRec_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType}
    {c : VConstVal} : (minorTypeRec U T np ty c).LevelWF (U+1) := by
  simp only [minorTypeRec]
  refine VExpr.LevelWF.forallN (liftTelN_levelWF fun B hB => ?_)
    (VExpr.LevelWF.forallN
      (ihsFromRecArgs_levelWF _ _ recArgsR_binder_levelWF recArgsR_idx_levelWF) ?_)
  · obtain ⟨B₀, _, rfl⟩ := List.mem_map.1 hB
    exact VExpr.LevelWF.instL VLevel.params'_one_wf
  · refine VExpr.LevelWF.appN (f := .bvar _) trivial fun e h => ?_
    rcases List.mem_append.1 h with h | h
    · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 h
      exact ((ctorIdxs_levelWF _ he₀).liftN).liftN
    · rcases List.mem_cons.1 h with rfl | h
      · refine VExpr.LevelWF.appN (f := .const c.name (VLevel.params' U 1))
          VLevel.params'_one_wf fun e h => ?_
        rcases List.mem_append.1 h with h | h
        · exact bvarRevRange_levelWF _ _ _ h
        · exact bvarRevRange_levelWF _ _ _ h
      · cases h

theorem minorTypes_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    ∀ (cs : List VConstVal) (i : Nat), ∀ e ∈ minorTypes U T np ty cs i, e.LevelWF (U+1)
  | _ :: cs, i, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact minorType_levelWF.liftN
    · exact minorTypes_levelWF cs (i+1) e h

theorem minorTypesRec_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    ∀ (cs : List VConstVal) (i : Nat),
      ∀ e ∈ minorTypesRec U T np ty cs i, e.LevelWF (U+1)
  | _ :: cs, i, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact minorTypeRec_levelWF.liftN
    · exact minorTypesRec_levelWF cs (i+1) e h

theorem recType_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    (recType U T np ty).LevelWF (U+1) := by
  refine VExpr.LevelWF.forallN (fun A hA => ?_)
    ⟨motiveType_levelWF, VExpr.LevelWF.forallN (minorTypes_levelWF _ _)
      (VExpr.LevelWF.forallN (liftTelN_levelWF idxTel_levelWF)
        ⟨?_, ?_, trivial⟩)⟩
  · obtain ⟨A₀, _, rfl⟩ := List.mem_map.1 hA
    exact VExpr.LevelWF.instL VLevel.params'_one_wf
  · refine VExpr.LevelWF.appN (f := .const T (VLevel.params' U 1)) VLevel.params'_one_wf
      fun e h => ?_
    rcases List.mem_append.1 h with h | h
    · exact bvarRevRange_levelWF _ _ _ h
    · exact bvarRevRange_levelWF _ _ _ h
  · exact VExpr.LevelWF.appN (f := .bvar _) trivial (bvarRevRange_levelWF _ _)

theorem recTypeRec_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    (recTypeRec U T np ty).LevelWF (U+1) := by
  refine VExpr.LevelWF.forallN (fun A hA => ?_)
    ⟨motiveType_levelWF, VExpr.LevelWF.forallN (minorTypesRec_levelWF _ _)
      (VExpr.LevelWF.forallN (liftTelN_levelWF idxTel_levelWF)
        ⟨?_, ?_, trivial⟩)⟩
  · obtain ⟨A₀, _, rfl⟩ := List.mem_map.1 hA
    exact VExpr.LevelWF.instL VLevel.params'_one_wf
  · refine VExpr.LevelWF.appN (f := .const T (VLevel.params' U 1)) VLevel.params'_one_wf
      fun e h => ?_
    rcases List.mem_append.1 h with h | h
    · exact bvarRevRange_levelWF _ _ _ h
    · exact bvarRevRange_levelWF _ _ _ h
  · exact VExpr.LevelWF.appN (f := .bvar _) trivial (bvarRevRange_levelWF _ _)

/-- Consume the induction-hypothesis telescope with well-typed values. -/
theorem hasType_appN_ihs {env : VEnv} {U : Nat} {Γ : List VExpr} {m k : Nat}
    {argOf : Nat × List VExpr → VExpr} {Dfin : VExpr} :
    ∀ {rs : List (Nat × List VExpr)} {g : VExpr}, (∀ q ∈ rs, q.1 < m) →
    (∀ q ∈ rs, env.HasType U Γ (argOf q)
      (VExpr.appN (.bvar (k + m))
        ((q.2.map fun e => ((e.liftN 1 q.1).liftN (m-q.1)).liftN k m) ++
          [.bvar (m-1-q.1)]))) →
    env.HasType U Γ g (VExpr.forallN (ihsR m k rs 0) (Dfin.liftN rs.length)) →
    env.HasType U Γ (g.appN (rs.map argOf)) Dfin
  | [], g, _, _, hg => by simpa [ihsR] using hg
  | (j, idxs) :: rs, g, hm, hargs, hg => by
    have happ := VEnv.HasType.app hg (hargs (j, idxs) (.head _))
    simp only [List.length_cons] at happ
    rw [show Dfin.liftN (rs.length+1) =
        (Dfin.liftN rs.length).liftN 1 (0 + rs.length) from by
        rw [Nat.zero_add, VExpr.liftN'_liftN' (Nat.zero_le _) (by omega)],
      ihsR_liftN1 m k rs 0 0 (Nat.le_refl _) (fun q hq => hm q (.tail _ hq))
        (Dfin.liftN rs.length),
      VExpr.inst_liftN1] at happ
    exact hasType_appN_ihs (rs := rs) (fun q hq => hm q (.tail _ hq))
      (fun q hq => hargs q (.tail _ hq)) happ

/-- Consume a normalized functional-IH telescope with one generated recursive
call per recursive argument. -/
theorem hasType_appN_ruleIHs {env : VEnv} {U : Nat} {Γ : List VExpr} {m k : Nat}
    {argOf : RecArg → VExpr} {Dfin : VExpr} :
    ∀ {rs : List RecArg} {g : VExpr},
    (∀ r ∈ rs, env.HasType U Γ (argOf r) (r.ruleIH m k)) →
    env.HasType U Γ g
      (VExpr.forallN (ruleIHs m k rs 0) (Dfin.liftN rs.length)) →
    env.HasType U Γ (g.appN (rs.map argOf)) Dfin
  | [], g, _, hg => by simpa [ruleIHs] using hg
  | r :: rs, g, hargs, hg => by
    have happ := VEnv.HasType.app hg (by
      simpa [ruleIHs] using hargs r (.head _))
    simp only [List.length_cons] at happ
    rw [show Dfin.liftN (rs.length+1) =
        (Dfin.liftN rs.length).liftN 1 (0+rs.length) from by
          rw [Nat.zero_add, VExpr.liftN'_liftN' (Nat.zero_le _) (by omega)],
      ruleIHs_liftN1 m k rs 0 0 (Nat.le_refl _) (Dfin.liftN rs.length),
      VExpr.inst_liftN1] at happ
    exact hasType_appN_ruleIHs (rs := rs)
      (fun q hq => hargs q (.tail _ hq)) happ

namespace GenerationEnv

variable {source : VInductDecl} {gen : GenerationChecked source}
  {env : VEnv} (S : GenerationEnv gen env)
include S
-- `S` is included throughout so every lemma below is reachable as `S.lemma`,
-- including those whose statement and proof never mention it.
set_option linter.unusedSectionVars false

/-! ## Mixed iota-rule preservation -/

/-- Syntactic universe well-formedness follows from semantic well-formedness
of the closed mixed recursor type. -/
theorem recType_levelWF :
    gen.recType.LevelWF (gen.recUvars) := by
  obtain ⟨_, h⟩ := S.recType_isType
  exact (h.levelWF trivial).1

/-- The mixed recursor type is closed. -/
theorem recType_closedN : gen.recType.ClosedN 0 := by
  obtain ⟨_, h⟩ := S.recType_isType
  exact VExpr.WF.closedN S.ord ⟨_, h⟩ trivial

/-- The inserted mixed recursor constant at its identity universe list. -/
theorem recursor_hasType
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) {Γ} :
    env.HasType (gen.recUvars) Γ
      (.const (.str gen.block.sourceType.name "rec")
        (gen.recLevels))
      gen.recType := by
  have h := HasType.const (Γ := Γ) hrec
    VLevel.params_wf VLevel.params_length
  rw [show gen.recursor.uvars =
      gen.recUvars from rfl,
    show gen.recursor.type = gen.recType from rfl] at h
  rwa [S.recType_levelWF.instL_id] at h

/-- Apply the mixed recursor to parameters, motive, and every constructor
minor. The remaining type binds the indices and major premise. -/
theorem recBase_hasType
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor)
    (Δ : List VExpr) :
    env.HasType (gen.recUvars)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.const (.str gen.block.sourceType.name "rec")
          (gen.recLevels))
        (VExpr.bvarRevRange Δ.length
          (source.nparams +
            gen.block.ctorPairs.length + 1)))
      ((VExpr.forallN
        (VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.forallE
          (VExpr.appN
            (.const gen.block.sourceType.name
              (gen.sourceLevels))
            (VExpr.bvarRevRange
                (gen.idxTel.length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0 gen.idxTel.length))
          (.app
            (VExpr.appN
              (.bvar
                (gen.idxTel.length +
                  gen.block.ctorPairs.length + 1))
              (VExpr.bvarRevRange 1 gen.idxTel.length))
            (.bvar 0)))).liftN Δ.length) := by
  have hf : env.HasType (gen.recUvars)
      (Δ ++
        (gen.paramsTel ++
          gen.motiveType :: gen.minorTypes).reverse ++ [])
      (.const (.str gen.block.sourceType.name "rec")
        (gen.recLevels))
      ((VExpr.forallN
        (gen.paramsTel ++
          gen.motiveType :: gen.minorTypes)
        (VExpr.forallN
          (VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            gen.idxTel 0)
          (.forallE
            (VExpr.appN
              (.const gen.block.sourceType.name
                (gen.sourceLevels))
              (VExpr.bvarRevRange
                  (gen.idxTel.length +
                    gen.block.ctorPairs.length + 1)
                  source.nparams ++
                VExpr.bvarRevRange 0 gen.idxTel.length))
            (.app
              (VExpr.appN
                (.bvar
                  (gen.idxTel.length +
                    gen.block.ctorPairs.length + 1))
                (VExpr.bvarRevRange 1 gen.idxTel.length))
              (.bvar 0))))).liftN
        (Δ.length +
          (gen.paramsTel ++
            gen.motiveType :: gen.minorTypes).length)) := by
    rw [show VExpr.forallN
        (gen.paramsTel ++
          gen.motiveType :: gen.minorTypes)
        (VExpr.forallN
          (VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            gen.idxTel 0)
          (.forallE
            (VExpr.appN
              (.const gen.block.sourceType.name
                (gen.sourceLevels))
              (VExpr.bvarRevRange
                  (gen.idxTel.length +
                    gen.block.ctorPairs.length + 1)
                  source.nparams ++
                VExpr.bvarRevRange 0 gen.idxTel.length))
            (.app
              (VExpr.appN
                (.bvar
                  (gen.idxTel.length +
                    gen.block.ctorPairs.length + 1))
                (VExpr.bvarRevRange 1 gen.idxTel.length))
              (.bvar 0)))) =
        gen.recType from by
          rw [VExpr.forallN_append]
          rfl,
      S.recType_closedN.liftN_eq (Nat.zero_le _)]
    exact S.recursor_hasType hrec
  have hspine := HasType.appN_selfSpine
    (env := env) (U := gen.recUvars) hf
  simp only [List.reverse_append, List.reverse_cons, List.append_nil, List.append_assoc,
    List.singleton_append, List.length_append, List.length_cons, gen.minorTypes_length] at hspine
  rw [show gen.paramsTel.length = source.nparams from by
      simp [GenerationChecked.paramsTel,
        S.generationParams_length],
    VExpr.bvarRevRange_congr' Δ.length
      (show source.nparams +
          (gen.block.ctorPairs.length + 1) =
        source.nparams +
          gen.block.ctorPairs.length + 1 by omega)] at hspine
  simpa [List.append_assoc] using hspine

/-- Apply the inserted mixed recursor to a typed index spine and major. -/
theorem recApp_hasType
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor)
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (gen.recUvars)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          (Δ.length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (gen.sourceLevels))))
      idxs
      (.sort (gen.block.checked.resultLevel.inst
        (gen.sourceLevels))))
    (hlen : idxs.length = gen.idxTel.length)
    (ha : env.HasType (gen.recUvars)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      a
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (Δ.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          idxs))) :
    env.HasType (gen.recUvars)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (VExpr.appN
          (.const (.str gen.block.sourceType.name "rec")
            (gen.recLevels))
          (VExpr.bvarRevRange Δ.length
            (source.nparams +
              gen.block.ctorPairs.length + 1)))
        (idxs ++ [a]))
      (VExpr.appN
        (.bvar
          (Δ.length +
            gen.block.ctorPairs.length))
        (idxs ++ [a])) := by
  have hb := S.recBase_hasType hrec Δ
  rw [VExpr.liftN_forallN,
    VExpr.liftTelN_liftTelN,
    liftTelN_congr _ _
      (show gen.block.ctorPairs.length + 1 +
          Δ.length =
        Δ.length + gen.block.ctorPairs.length + 1 by omega)] at hb
  have hcod :
      (VExpr.forallE
        (VExpr.appN
          (.const gen.block.sourceType.name
            (gen.sourceLevels))
          (VExpr.bvarRevRange
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length))
        (.app
          (VExpr.appN
            (.bvar
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1))
            (VExpr.bvarRevRange 1 gen.idxTel.length))
          (.bvar 0))).liftN Δ.length
            (0 + (VExpr.liftTelN
              (gen.block.ctorPairs.length + 1)
              gen.idxTel 0).length) =
      VExpr.forallE
        (VExpr.appN
          (.const gen.block.sourceType.name
            (gen.sourceLevels))
          (VExpr.bvarRevRange
              (gen.idxTel.length + Δ.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length))
        (.app
          (VExpr.appN
            (.bvar
              (gen.idxTel.length + Δ.length +
                gen.block.ctorPairs.length + 1))
            (VExpr.bvarRevRange 1 gen.idxTel.length))
          (.bvar 0)) := by
    rw [VExpr.liftTelN_length, Nat.zero_add]
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append,
        bvarRevRange_liftN_ge _ _ _ _ (by omega),
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
        VExpr.bvarRevRange_congr source.nparams
          (show Δ.length +
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1) =
            gen.idxTel.length + Δ.length +
              gen.block.ctorPairs.length + 1 by omega)]
      rfl
    · show VExpr.app _ _ = VExpr.app _ _
      congr 1
      · rw [VExpr.liftN_appN,
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
        show VExpr.appN
          (.bvar (liftVar Δ.length
            (gen.idxTel.length +
              gen.block.ctorPairs.length + 1)
            (gen.idxTel.length + 1))) _ = _
        rw [liftVar_le (by omega),
          show Δ.length +
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1) =
            gen.idxTel.length + Δ.length +
              gen.block.ctorPairs.length + 1 by omega]
  rw [hcod] at hb
  have hshape := hidx.retarget
    (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (gen.idxTel.length + Δ.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length))
      (.sort gen.motiveLevel))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _
      (C := .const gen.block.sourceType.name
        (gen.sourceLevels)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _
      (by rw [hlen]; omega),
    show gen.idxTel.length + Δ.length +
        gen.block.ctorPairs.length + 1 - idxs.length =
      Δ.length + gen.block.ctorPairs.length + 1 from by
        rw [hlen]
        omega,
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hfull := hshape.snoc ha
  simp only [VExpr.inst] at hfull
  change env.SpineWF (gen.recUvars) _
    (VExpr.forallN
      (VExpr.liftTelN
        (Δ.length + gen.block.ctorPairs.length + 1)
        gen.idxTel 0)
      (VExpr.forallN
        [VExpr.appN
          (.const gen.block.sourceType.name
            (gen.sourceLevels))
          (VExpr.bvarRevRange
              (gen.idxTel.length + Δ.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length)]
        (.sort gen.motiveLevel)))
    (idxs ++ [a]) (.sort gen.motiveLevel) at hfull
  rw [← VExpr.forallN_append] at hfull
  have hfullLen : (idxs ++ [a]).length =
      (VExpr.liftTelN
          (Δ.length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0 ++
        [VExpr.appN
          (.const gen.block.sourceType.name
            (gen.sourceLevels))
          (VExpr.bvarRevRange
              (gen.idxTel.length + Δ.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0
              gen.idxTel.length)]).length := by
    simp only [List.length_append, List.length_singleton,
      VExpr.liftTelN_length, hlen]
  have hactual := hfull.retarget hfullLen
    (VExpr.app
      (VExpr.appN
        (.bvar
          (gen.idxTel.length + Δ.length +
            gen.block.ctorPairs.length + 1))
        (VExpr.bvarRevRange 1 gen.idxTel.length))
      (.bvar 0))
  rw [VExpr.forallN_append] at hactual
  have happ := hactual.hasType_appN hb
  rw [show VExpr.app
      (VExpr.appN
        (.bvar
          (gen.idxTel.length + Δ.length +
            gen.block.ctorPairs.length + 1))
        (VExpr.bvarRevRange 1 gen.idxTel.length))
      (.bvar 0) =
      VExpr.appN
        (.bvar
          (gen.idxTel.length + Δ.length +
            gen.block.ctorPairs.length + 1))
        (VExpr.bvarRevRange 0
          (gen.idxTel.length + 1)) from by
      rw [VExpr.bvarRevRange_congr' 0
          (show gen.idxTel.length + 1 =
            1 + gen.idxTel.length by omega),
        ← VExpr.bvarRevRange_append
          gen.idxTel.length 1]
      simpa [VExpr.bvarRevRange, VExpr.appN] using
        (VExpr.appN_append
          (.bvar
            (gen.idxTel.length + Δ.length +
              gen.block.ctorPairs.length + 1))
          (VExpr.bvarRevRange 1 gen.idxTel.length)
          [VExpr.bvar 0]).symm,
    VExpr.instRev_appN,
    VExpr.instRev_bvar_ge _ (by
      simp only [List.length_append,
        List.length_singleton]
      rw [hlen]
      omega),
    VExpr.bvarRevRange_congr' 0
      (show gen.idxTel.length + 1 =
        (idxs ++ [a]).length by simp [hlen]),
    VExpr.map_instRev_bvarRevRange] at happ
  rw [show gen.idxTel.length + Δ.length +
      gen.block.ctorPairs.length + 1 -
        (idxs ++ [a]).length =
      Δ.length + gen.block.ctorPairs.length from by
    simp only [List.length_append, List.length_singleton]
    rw [hlen]
    omega] at happ
  simpa [List.length_append, hlen] using happ

/-- The mixed motive variable applied to an index spine and major. -/
theorem motiveApp_hasType
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (gen.recUvars)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          (Δ.length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (gen.sourceLevels))))
      idxs
      (.sort (gen.block.checked.resultLevel.inst
        (gen.sourceLevels))))
    (hlen : idxs.length = gen.idxTel.length)
    (ha : env.HasType (gen.recUvars)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      a
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            (Δ.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          idxs))) :
    env.HasType (gen.recUvars)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.bvar
          (Δ.length +
            gen.block.ctorPairs.length))
        (idxs ++ [a]))
      (.sort gen.motiveLevel) := by
  have hM := getElem?_rstack3 Δ
    gen.minorTypes.reverse gen.motiveType
    gen.paramsTel.reverse
    (i := Δ.length + gen.block.ctorPairs.length)
    (by simp only [List.length_reverse,
      gen.minorTypes_length])
  exact gen.motiveVarApp_hasType
    (.bvar (Lookup.of_getElem? hM))
    hidx hlen ha

/-- The raw constructor-headed major in the complete mixed rule context. -/
theorem ctorAppRule_hasType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.HasType (gen.recUvars)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.const ctor.raw.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            ((ctor.fieldsR
                source.uvars source.nparams gen.elimination).length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            ((ctor.fieldsR
                source.uvars source.nparams gen.elimination).length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          (ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length)) := by
  have h := S.ctorApp_transport hctor
    (gen.minorTypes.reverse ++ [gen.motiveType])
    (g := gen.block.ctorPairs.length + 1)
    (by simp [gen.minorTypes_length])
    [] (d := 0) rfl
  rw [VExpr.bvarRevRange_congr source.nparams
    (show
      0 + (gen.block.ctorPairs.length + 1 +
        (ctor.fieldsR
          source.uvars source.nparams gen.elimination).length) =
      (ctor.fieldsR
          source.uvars source.nparams gen.elimination).length +
        gen.block.ctorPairs.length + 1 by omega)] at h
  simpa [List.append_assoc] using h

/-- The complete mixed rule binder telescope is well formed. -/
theorem ruleBinders_onTel {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.OnTel (gen.recUvars) []
      (gen.paramsTel ++
        gen.motiveType :: gen.minorTypes ++
        VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0) := by
  have hF₀ := S.fields_onTel_minor hctor
  have hF := hF₀.weakN S.ord
    (Ctx.LiftN.zero
      (Γ := gen.motiveType :: gen.paramsTel.reverse)
      gen.minorTypes.reverse)
  rw [VExpr.liftTelN_liftTelN,
    liftTelN_congr _ _
      (show 1 + gen.minorTypes.reverse.length =
        gen.block.ctorPairs.length + 1 by
          simp [gen.minorTypes_length, Nat.add_comm])] at hF
  refine OnTel.append
    (OnTel.append S.paramsTel_onTel ⟨?_, ?_⟩) ?_
  · simpa only [List.append_nil] using S.motive_isType
  · simpa only [List.append_nil] using S.minorTypes_onTel
  · simpa only [List.append_nil, List.append_assoc,
      List.reverse_append, List.reverse_cons,
      List.singleton_append] using hF

/-- The type recorded on every mixed iota rule is itself a type. -/
theorem ruleType_isType {i : Nat} {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.IsType (gen.recUvars) []
      ((gen.rule i ctor).type) := by
  show env.IsType (gen.recUvars) []
    (VExpr.forallN
      (gen.paramsTel ++
        gen.motiveType :: gen.minorTypes ++
        VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0)
      (VExpr.appN
        (.bvar
          (gen.block.ctorPairs.length +
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length))
        (((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (gen.sourceLevels))
            (VExpr.bvarRevRange
                ((ctor.fieldsR
                    source.uvars source.nparams gen.elimination).length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length)])))
  refine IsType.forallN (S.ruleBinders_onTel hctor) ?_
  simp only [List.reverse_append, List.reverse_cons,
    List.append_nil, List.append_assoc,
    List.singleton_append]
  have hSp₀ := S.result_transport hctor
    (gen.minorTypes.reverse ++ [gen.motiveType])
    (g := gen.block.ctorPairs.length + 1)
    (by simp [gen.minorTypes_length])
    [] (d := 0) rfl
  have hSp : env.SpineWF (gen.recUvars)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          ((ctor.fieldsR
              source.uvars source.nparams gen.elimination).length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (gen.sourceLevels))))
      ((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
        e.liftN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length)
      (.sort (gen.block.checked.resultLevel.inst
        (gen.sourceLevels))) := by
    simpa [List.append_assoc, Nat.add_assoc] using hSp₀
  have hidxLen :
      ((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
        e.liftN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length).length =
      gen.idxTel.length := by
    simp only [List.length_map,
      NormalizedCtor.resultIndicesR,
      GenerationChecked.idxTel]
    exact (S.viewResultIndices_length hctor).trans
      gen.shape.2.2.1.symm
  have hctorApp := S.ctorAppRule_hasType hctor
  have hSp' : env.SpineWF (gen.recUvars)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          ((VExpr.liftTelN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination)
              0).reverse.length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (gen.sourceLevels))))
      ((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
        e.liftN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length)
      (.sort (gen.block.checked.resultLevel.inst
        (gen.sourceLevels))) := by
    simpa only [List.length_reverse,
      VExpr.liftTelN_length] using hSp
  have hctorApp' : env.HasType (gen.recUvars)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.const ctor.raw.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            ((ctor.fieldsR
                source.uvars source.nparams gen.elimination).length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            ((VExpr.liftTelN
                (gen.block.ctorPairs.length + 1)
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination)
                0).reverse.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          (ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length)) := by
    simpa only [List.length_reverse,
      VExpr.liftTelN_length] using hctorApp
  refine ⟨gen.motiveLevel, ?_⟩
  have hm := S.motiveApp_hasType
    (VExpr.liftTelN
      (gen.block.ctorPairs.length + 1)
      (ctor.fieldsR source.uvars source.nparams gen.elimination)
      0).reverse
    hSp' hidxLen hctorApp'
  rw [List.length_reverse, VExpr.liftTelN_length,
    show
      (ctor.fieldsR
          source.uvars source.nparams gen.elimination).length +
          gen.block.ctorPairs.length =
        gen.block.ctorPairs.length +
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length by omega,
    show
      gen.block.ctorPairs.length +
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length + 1 =
        (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length +
          gen.block.ctorPairs.length + 1 by omega] at hm
  exact hm

/-- A retained recursive descriptor generates a well-typed direct or
lambda-valued recursive call in the complete mixed rule context. -/
theorem ruleCall_hasType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor)
    {r : RecArg}
    (hr : r ∈ ctor.recArgsR source.uvars gen.elimination) :
    env.HasType (gen.recUvars)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (r.ruleCall
        (ctor.fieldsR source.uvars source.nparams gen.elimination).length
        gen.block.ctorPairs.length
        (VExpr.appN
          (.const
            (.str gen.block.sourceType.name "rec")
            (gen.recLevels))
          (VExpr.bvarRevRange
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length
            (source.nparams +
              gen.block.ctorPairs.length + 1))))
      (r.ruleIH
        (ctor.fieldsR source.uvars source.nparams gen.elimination).length
        gen.block.ctorPairs.length) := by
  obtain ⟨r₀, hr₀, rfl⟩ :=
    NormalizedCtor.recArgsR_mem hr
  obtain ⟨Bview, hBview, hrecArg⟩ :=
    S.viewRecArg_data hctor hr₀
  let ls := gen.sourceLevels
  let r := r₀.instL ls
  let Bs := ctor.fieldsR source.uvars source.nparams gen.elimination
  let m := Bs.length
  let k := gen.block.ctorPairs.length
  let j := r₀.fieldIndex
  let Fs := VExpr.liftTelN (k+1) Bs 0
  let As := r.ruleBinders m k
  let idxs := r.indices.map fun e =>
    (e.liftN (k+1)
      (r.fieldIndex+r.binders.length)).liftN
        (m-r.fieldIndex) r.binders.length
  let Γ := Fs.reverse ++
    (gen.minorTypes.reverse ++
      (gen.motiveType :: gen.paramsTel.reverse))
  have hjm : j < m := by
    have hview := S.viewRecArg_lt hctor hr₀
    have hfields :=
      (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
    simp only [j, m, Bs, NormalizedCtor.fieldsR_length]
    omega
  have hjraw :
      r₀.fieldIndex <
        (ctor.rawFields source.nparams).length := by
    simpa [j, m, Bs,
      NormalizedCtor.fieldsR_length] using hjm
  let Braw :=
    (ctor.rawFields source.nparams)[r₀.fieldIndex]
  have hBraw :
      (ctor.rawFields source.nparams)[r₀.fieldIndex]? =
        some Braw :=
    List.getElem?_eq_getElem hjraw
  have hFsLen : Fs.length = m := by
    simp [Fs, m, VExpr.liftTelN_length]
  have ht := S.recArg_transport hctor hr₀
    (gen.minorTypes.reverse ++ [gen.motiveType])
    (g := k+1) (by simp [k, gen.minorTypes_length])
    (Fs.drop j).reverse (d := m-j) (by
      simp only [List.length_reverse, List.length_drop,
        hFsLen])
  dsimp only [r, j, RecArg.instL] at ht
  have hctx :
      (Fs.drop j).reverse ++
          ((VExpr.liftTelN (k+1)
              (Bs.take j) 0).reverse ++
            ((gen.minorTypes.reverse ++
              [gen.motiveType]) ++
              gen.paramsTel.reverse)) = Γ := by
    dsimp only [Γ, Fs]
    rw [← VExpr.liftTelN_take, List.append_assoc,
      ← List.append_assoc
        (((VExpr.liftTelN (k+1) Bs 0).drop j).reverse),
      ← List.reverse_append, List.take_append_drop,
      List.singleton_append, ← List.append_assoc]
  have htel : env.OnTel
      (gen.recUvars) Γ As := by
    rw [hctx] at ht
    simpa [r, As, m, k, j, RecArg.instL,
      RecArg.ruleBinders] using ht.1
  have hsp : env.SpineWF (gen.recUvars)
      (As.reverse ++ Γ)
      (VExpr.forallN
        (VExpr.liftTelN
          (m+k+r.binders.length+1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst ls)))
      idxs
      (.sort (gen.block.checked.resultLevel.inst ls)) := by
    rw [hctx] at ht
    simpa [r, As, idxs, m, k, j, ls,
      RecArg.instL, RecArg.ruleBinders,
      List.append_assoc,
      show j + r₀.binders.length + (k+1) + (m-j) =
        m+k+r₀.binders.length+1 by omega] using ht.2
  have hF : Γ[m-1-j]? =
      some ((Braw.instL ls).liftN (k+1) j) := by
    dsimp only [Γ, Fs]
    rw [List.getElem?_append_left
        (by
          simp only [List.length_reverse,
            VExpr.liftTelN_length]
          omega),
      List.getElem?_reverse (by rw [hFsLen]; omega),
      VExpr.liftTelN_length,
      show m - 1 - (m - 1 - j) = j by omega,
      VExpr.liftTelN_getElem?,
      NormalizedCtor.fieldsR_getElem?, hBraw]
    simp [ls]
  have hlu := Lookup.of_getElem? hF
  dsimp only [j, r] at hlu
  rw [show m-1-r₀.fieldIndex+1 =
      m-r₀.fieldIndex by omega] at hlu
  have hf0 := VEnv.HasType.bvar
    (env := env) (U := gen.recUvars) hlu
  obtain ⟨u, hdom₀⟩ :=
    S.emittedField_defeq hctor hBraw hBview
  have hdom₁ := hdom₀.instL
    (U' := gen.recUvars)
    gen.sourceLevels_wf
  have hdomChecked : env.IsDefEq (gen.recUvars)
      ((ctor.fieldsR source.uvars source.nparams gen.elimination |>.take
          r₀.fieldIndex).reverse ++
        (gen.block.checked.params.map (VExpr.instL ls)).reverse)
      (Braw.instL ls) (Bview.instL ls) ((VExpr.sort u).instL ls) := by
    simpa [NormalizedCtor.fieldsR, List.map_append,
      List.map_reverse, List.map_take] using hdom₁
  have hprefix := S.generationFieldPrefix_ctx_rec hctor r₀.fieldIndex
  have hdomGeneration := hdomChecked.defeqDFC S.ord
    (hprefix.symm S.ord)
  have hjlen :
      (Bs.take r₀.fieldIndex).length =
        r₀.fieldIndex := by
    simp only [Bs, NormalizedCtor.fieldsR,
      List.length_take, List.length_map]
    omega
  have Wmid := Ctx.LiftN.consTel
    (n := k+1)
    (Bs.take r₀.fieldIndex)
    (Ctx.LiftN.zero
      (n := k+1)
      (Γ := gen.paramsTel.reverse)
      (gen.minorTypes.reverse ++
        [gen.motiveType])
      (h := by simp [k, gen.minorTypes_length]))
  rw [hjlen, Nat.add_zero] at Wmid
  have hdom₂ := hdomGeneration.weakN S.ord Wmid
  have Wstack := Ctx.LiftN.zero
    (n := m-j)
    (Γ := (VExpr.liftTelN (k+1)
        (Bs.take j) 0).reverse ++
      ((gen.minorTypes.reverse ++
        [gen.motiveType]) ++
        gen.paramsTel.reverse))
    (Fs.drop j).reverse
    (h := by
      simp only [List.length_reverse, List.length_drop,
        hFsLen])
  have hdom₃ := hdom₂.weakN S.ord Wstack
  rw [hctx] at hdom₃
  have hfView := hdom₃.defeq hf0
  have hfield := recArg_rule_fieldType
    hrecArg m k (by simpa [j] using hjm) gen.elimination
  simp only [RecArg.instL] at hfield
  dsimp only [j] at hfView
  simp only [Nat.add_zero] at hfView
  rw [hfield] at hfView
  have hf := hfView.weakN S.ord
    (Ctx.LiftN.zero (Γ := Γ) As.reverse)
  have hmajor := VEnv.HasType.appN_selfSpine
    (env := env) (U := gen.recUvars)
    (As := As)
    (B := VExpr.appN
      (.const gen.block.sourceType.name ls)
      (VExpr.bvarRevRange
          (m+k+r.binders.length+1)
          source.nparams ++
        idxs))
    (Δ := []) (Γ := Γ) (by
      simpa [As, r, idxs, j, ls,
        RecArg.instL, RecArg.ruleBinders,
        List.length_reverse, List.map_map,
        Function.comp_def] using hf)
  simp only [List.length_nil, VExpr.liftN_zero,
    List.nil_append] at hmajor
  have hAsLen :
      As.length = r.binders.length := by
    simp [As, RecArg.ruleBinders,
      VExpr.liftTelN_length]
  change env.HasType (gen.recUvars)
    (As.reverse ++ Γ)
    ((VExpr.bvar
      (m-1-r.fieldIndex+As.length)).appN
        (VExpr.bvarRevRange 0 As.length))
    (VExpr.appN
      (.const gen.block.sourceType.name ls)
      (VExpr.bvarRevRange
          (m+k+r.binders.length+1)
          source.nparams ++
        idxs)) at hmajor
  rw [hAsLen] at hmajor
  have hlen : idxs.length = gen.idxTel.length := by
    simpa [idxs, r, RecArg.instL,
      GenerationChecked.idxTel] using
      (S.viewRecArg_indices_length hctor hr₀).trans
        gen.shape.2.2.1.symm
  have hcall := S.recApp_hasType hrec
    (As.reverse ++ Fs.reverse)
    (by
      simpa [Γ, List.append_assoc, hAsLen, hFsLen,
        Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hsp)
    hlen
    (by
      simpa [Γ, List.append_assoc, hAsLen, hFsLen,
        Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hmajor)
  have hbaseLift :
      (VExpr.appN
        (.const
          (.str gen.block.sourceType.name "rec")
          (gen.recLevels))
        (VExpr.bvarRevRange m
          (source.nparams+(k+1)))).liftN
          r.binders.length =
      VExpr.appN
        (.const
          (.str gen.block.sourceType.name "rec")
          (gen.recLevels))
        (VExpr.bvarRevRange
          (m+r.binders.length)
          (source.nparams+(1+k))) := by
    rw [VExpr.liftN_appN]
    simp only [VExpr.liftN]
    rw [bvarRevRange_liftN_ge _ _ _ _
      (Nat.zero_le _)]
    rw [show source.nparams+(k+1) =
      source.nparams+(1+k) by omega]
    apply congrArg (VExpr.appN _)
    apply VExpr.bvarRevRange_congr
    omega
  have hbaseRange :
      VExpr.appN
        ((VExpr.const
          (.str gen.block.sourceType.name "rec")
          (gen.recLevels)).app
            (VExpr.bvar
              (source.nparams +
                (k + (m + r.binders.length)))))
        (VExpr.bvarRevRange
          (m+r.binders.length)
          (source.nparams+k)) =
      VExpr.appN
        (.const
          (.str gen.block.sourceType.name "rec")
          (gen.recLevels))
        (VExpr.bvarRevRange
          (m+r.binders.length)
          (source.nparams+(1+k))) := by
    rw [show source.nparams + (k + (m + r.binders.length)) =
        (m+r.binders.length) + (source.nparams+k) by omega,
      show source.nparams+(1+k) = (source.nparams+k)+1 by omega]
    rfl
  have hlam := HasType.lamN htel (by
    simpa [Γ, Fs, hAsLen, hFsLen,
      List.append_assoc, VExpr.liftN_appN,
      bvarRevRange_liftN_ge _ _ _ _
        (Nat.zero_le _),
      Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcall)
  simp only [VExpr.liftTelN_length] at hlam
  rw [hbaseRange] at hlam
  simpa only [RecArg.ruleCall, RecArg.ruleIH,
    r, Bs, ls, As, idxs, m, k, Γ, Fs, hbaseLift,
    VExpr.liftTelN_length, List.append_assoc,
    Nat.add_assoc] using hlam

/-- The selected mixed constructor minor applied to all raw fields and to one
generated direct or functional recursive call for every retained `RecArg`. -/
theorem minorApp_hasType {i : Nat} {ctor : NormalizedCtor}
    (hci : gen.block.ctorPairs[i]? = some ctor)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) :
    env.HasType (gen.recUvars)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.bvar
          (gen.block.ctorPairs.length - 1 - i +
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length))
        (VExpr.bvarRevRange 0
            (ctor.fieldsR source.uvars source.nparams gen.elimination).length ++
          List.map (fun r =>
              r.ruleCall
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length
                gen.block.ctorPairs.length
                (VExpr.appN
                  (.const
                    (.str gen.block.sourceType.name "rec")
                    (gen.recLevels))
                  (VExpr.bvarRevRange
                    (ctor.fieldsR
                      source.uvars source.nparams gen.elimination).length
                    (source.nparams +
                      gen.block.ctorPairs.length + 1))))
            (ctor.recArgsR source.uvars gen.elimination)))
      (VExpr.appN
        (.bvar
          (gen.block.ctorPairs.length +
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length))
        (((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (gen.sourceLevels))
            (VExpr.bvarRevRange
                ((ctor.fieldsR
                    source.uvars source.nparams gen.elimination).length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length)])) := by
  obtain ⟨hik, -⟩ :=
    List.getElem?_eq_some_iff.1 hci
  have hctor := List.mem_of_getElem? hci
  let rs := ctor.recArgsR source.uvars gen.elimination
  have hrs :
      rs = ctor.recArgsR source.uvars gen.elimination := rfl
  have hrsLt : ∀ r ∈ rs,
      r.fieldIndex <
        (ctor.fieldsR
          source.uvars source.nparams gen.elimination).length := by
    intro r hr
    obtain ⟨r₀, hr₀, rfl⟩ :=
      NormalizedCtor.recArgsR_mem (hrs ▸ hr)
    have hview := S.viewRecArg_lt hctor hr₀
    have hfields :=
      (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
    simp only [RecArg.instL,
      NormalizedCtor.fieldsR_length]
    omega
  rw [VExpr.appN_append]
  have hminorAt :
      gen.minorTypes[i]? =
        some
          (VExpr.liftN i
            (GenerationChecked.minorType
              (source := source) ctor gen.elimination)) := by
    simpa [GenerationChecked.minorTypes, hci] using
      gen.minorTypesAux_getElem?
        gen.block.ctorPairs 0 i
  have hlu0 :
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))[
          gen.block.ctorPairs.length - 1 - i +
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length]? =
        some
          (VExpr.liftN i
            (GenerationChecked.minorType
              (source := source) ctor gen.elimination)) := by
    rw [getElem?_rstack_mid _ _ _
        (by
          simp only [List.length_reverse,
            VExpr.liftTelN_length]
          omega)
        (by
          simp only [List.length_reverse,
            VExpr.liftTelN_length,
            gen.minorTypes_length]
          omega),
      show
        gen.block.ctorPairs.length - 1 - i +
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length -
            (VExpr.liftTelN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination)
              0).reverse.length =
          gen.block.ctorPairs.length - 1 - i by
        simp only [List.length_reverse,
          VExpr.liftTelN_length]
        omega,
      List.getElem?_reverse
        (by
          simp only [gen.minorTypes_length]
          omega),
      show
        gen.minorTypes.length - 1 -
            (gen.block.ctorPairs.length - 1 - i) =
          i by
        simp only [gen.minorTypes_length]
        omega,
      hminorAt]
  have hlu := Lookup.of_getElem? hlu0
  rw [VExpr.liftN_liftN,
    show
      i +
          (gen.block.ctorPairs.length - 1 - i +
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length + 1) =
        (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length +
          gen.block.ctorPairs.length by omega] at hlu
  have hminorEq :
      (GenerationChecked.minorType
              (source := source) ctor gen.elimination).liftN
          ((ctor.fieldsR
              source.uvars source.nparams gen.elimination).length +
            gen.block.ctorPairs.length) =
        (VExpr.forallN
          (VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination)
            0)
          ((VExpr.forallN
            (ihsFromRecArgs
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length
              rs 0)
            (VExpr.appN
              (.bvar
                ((ctor.fieldsR
                    source.uvars source.nparams gen.elimination).length +
                  rs.length))
              (((ctor.resultIndicesR source.uvars gen.elimination).map
                  fun e =>
                    (e.liftN 1
                      (ctor.fieldsR
                        source.uvars source.nparams gen.elimination).length).liftN
                      rs.length) ++
                [VExpr.appN
                  (.const ctor.raw.name
                    (gen.sourceLevels))
                  (VExpr.bvarRevRange
                      (rs.length +
                        (ctor.fieldsR
                          source.uvars source.nparams gen.elimination).length +
                        1)
                      source.nparams ++
                    VExpr.bvarRevRange rs.length
                      (ctor.fieldsR
                        source.uvars source.nparams gen.elimination).length)]))).liftN
              gen.block.ctorPairs.length
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length)).liftN
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length := by
    simp only [GenerationChecked.minorType, rs]
    conv => lhs; rw [VExpr.liftN_forallN,
        VExpr.liftTelN_liftTelN,
        liftTelN_congr _ _
          (show
            (1 : Nat) +
                ((ctor.fieldsR
                    source.uvars source.nparams gen.elimination).length +
                  gen.block.ctorPairs.length) =
              gen.block.ctorPairs.length + 1 +
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length by
            omega),
        show
          (0 : Nat) +
              (VExpr.liftTelN 1
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination)
                0).length =
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length by
          simp [VExpr.liftTelN_length]]
    conv => rhs; rw [VExpr.liftN_forallN,
        VExpr.liftTelN_liftTelN,
        show
          (0 : Nat) +
              (VExpr.liftTelN
                (gen.block.ctorPairs.length + 1)
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination)
                0).length =
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length by
          simp [VExpr.liftTelN_length],
        VExpr.liftN'_liftN_hi,
        Nat.add_comm gen.block.ctorPairs.length
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length]
  have hfields := HasType.appN_selfSpine
    (env := env) (U := gen.recUvars)
    (As := VExpr.liftTelN
      (gen.block.ctorPairs.length + 1)
      (ctor.fieldsR source.uvars source.nparams gen.elimination)
      0)
    (B :=
      (VExpr.forallN
        (ihsFromRecArgs
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length
          rs 0)
        (VExpr.appN
          (.bvar
            ((ctor.fieldsR
                source.uvars source.nparams gen.elimination).length +
              rs.length))
          (((ctor.resultIndicesR source.uvars gen.elimination).map
              fun e =>
                (e.liftN 1
                  (ctor.fieldsR
                    source.uvars source.nparams gen.elimination).length).liftN
                  rs.length) ++
            [VExpr.appN
              (.const ctor.raw.name
                (gen.sourceLevels))
              (VExpr.bvarRevRange
                  (rs.length +
                    (ctor.fieldsR
                      source.uvars source.nparams gen.elimination).length +
                    1)
                  source.nparams ++
                VExpr.bvarRevRange rs.length
                  (ctor.fieldsR
                    source.uvars source.nparams gen.elimination).length)]))).liftN
        gen.block.ctorPairs.length
        (ctor.fieldsR
          source.uvars source.nparams gen.elimination).length)
    (Δ := [])
    (Γ := gen.minorTypes.reverse ++
      (gen.motiveType :: gen.paramsTel.reverse))
    (f := .bvar
      (gen.block.ctorPairs.length - 1 - i +
        (ctor.fieldsR
          source.uvars source.nparams gen.elimination).length))
    (by
      have hb := VEnv.HasType.bvar
        (env := env) (U := gen.recUvars) hlu
      rw [hminorEq] at hb
      simpa [VExpr.liftTelN_length] using hb)
  simp only [List.length_nil,
    VExpr.liftTelN_length,
    VExpr.liftN_zero] at hfields
  rw [ihsFromRecArgs_liftN'
    (ctor.fieldsR source.uvars source.nparams gen.elimination).length
    gen.block.ctorPairs.length rs hrsLt 0
    (VExpr.appN
      (.bvar
        ((ctor.fieldsR
            source.uvars source.nparams gen.elimination).length +
          rs.length))
      (((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
          (e.liftN 1
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length).liftN
            rs.length) ++
        [VExpr.appN
          (.const ctor.raw.name
            (gen.sourceLevels))
          (VExpr.bvarRevRange
              (rs.length +
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length + 1)
              source.nparams ++
            VExpr.bvarRevRange rs.length
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length)]))
    (cut :=
      (ctor.fieldsR
        source.uvars source.nparams gen.elimination).length)
    rfl] at hfields
  have hD :
      (VExpr.appN
        (.bvar
          ((ctor.fieldsR
              source.uvars source.nparams gen.elimination).length +
            rs.length))
        (((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            (e.liftN 1
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length).liftN
              rs.length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (gen.sourceLevels))
            (VExpr.bvarRevRange
                (rs.length +
                  (ctor.fieldsR
                    source.uvars source.nparams gen.elimination).length + 1)
                source.nparams ++
              VExpr.bvarRevRange rs.length
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length)])).liftN
        gen.block.ctorPairs.length
        ((ctor.fieldsR
            source.uvars source.nparams gen.elimination).length +
          0 + rs.length) =
      (VExpr.appN
        (.bvar
          (gen.block.ctorPairs.length +
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length))
        (((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (gen.sourceLevels))
            (VExpr.bvarRevRange
                ((ctor.fieldsR
                    source.uvars source.nparams gen.elimination).length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length)])).liftN
        rs.length := by
    rw [VExpr.liftN_appN, VExpr.liftN_appN,
      List.map_append, List.map_append,
      List.map_map, List.map_map]
    show VExpr.appN _ (_ ++ [_]) =
      VExpr.appN _ (_ ++ [_])
    congr 1
    · show
        VExpr.bvar
            (liftVar gen.block.ctorPairs.length
              ((ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length +
                rs.length)
              ((ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length +
                0 + rs.length)) =
          VExpr.bvar
            (liftVar rs.length
              (gen.block.ctorPairs.length +
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length)
              0)
      rw [liftVar_le (by omega),
        liftVar_le (Nat.zero_le _)]
      congr 1
      omega
    · congr 1
      · apply List.map_congr_left
        intro e _
        simp only [Function.comp_apply]
        rw [show
            (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length +
                0 + rs.length =
              (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length +
                rs.length by omega,
          VExpr.liftN_liftN_mid e
            gen.block.ctorPairs.length rs.length
            (Nat.zero_le _)]
      · congr 1
        simp only []
        rw [show
            (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length +
                0 + rs.length =
              (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length +
                rs.length by omega]
        rw [VExpr.liftN_appN,
          VExpr.liftN_appN,
          List.map_append, List.map_append,
          bvarRevRange_liftN_ge _ _ _ _ (by omega),
          VExpr.bvarRevRange_liftN_high _ _ _ _
            (by omega),
          bvarRevRange_liftN_ge _ _ _ _
            (Nat.zero_le _),
          bvarRevRange_liftN_ge _ _ _ _
            (Nat.zero_le _),
          VExpr.bvarRevRange_congr source.nparams
            (show
              gen.block.ctorPairs.length +
                  (rs.length +
                    (ctor.fieldsR
                      source.uvars source.nparams gen.elimination).length +
                    1) =
                rs.length +
                  ((ctor.fieldsR
                      source.uvars source.nparams gen.elimination).length +
                    gen.block.ctorPairs.length + 1) by
              omega),
          VExpr.bvarRevRange_congr _
            (show rs.length = rs.length + 0 by omega)]
        rfl
  rw [hD] at hfields
  have hres := hasType_appN_ruleIHs
    (env := env) (U := gen.recUvars)
    (m :=
      (ctor.fieldsR
        source.uvars source.nparams gen.elimination).length)
    (k := gen.block.ctorPairs.length)
    (rs := rs)
    (argOf := fun r =>
      r.ruleCall
        (ctor.fieldsR
          source.uvars source.nparams gen.elimination).length
        gen.block.ctorPairs.length
        (VExpr.appN
          (.const
            (.str gen.block.sourceType.name "rec")
            (gen.recLevels))
          (VExpr.bvarRevRange
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length
            (source.nparams +
              gen.block.ctorPairs.length + 1))))
    (fun r hr =>
      S.ruleCall_hasType hctor hrec (hrs ▸ hr))
    hfields
  simpa only [hrs] using hres

/-- The constructor-headed left side of a mixed iota rule. -/
theorem recRuleApp_hasType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) :
    env.HasType (gen.recUvars)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (VExpr.appN
          (.const
            (.str gen.block.sourceType.name "rec")
            (gen.recLevels))
          (VExpr.bvarRevRange
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length
            (source.nparams +
              gen.block.ctorPairs.length + 1)))
        (((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (gen.sourceLevels))
            (VExpr.bvarRevRange
                ((ctor.fieldsR
                    source.uvars source.nparams gen.elimination).length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length)]))
      (VExpr.appN
        (.bvar
          (gen.block.ctorPairs.length +
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length))
        (((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (gen.sourceLevels))
            (VExpr.bvarRevRange
                ((ctor.fieldsR
                    source.uvars source.nparams gen.elimination).length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination).length)])) := by
  have hSp₀ := S.result_transport hctor
    (gen.minorTypes.reverse ++ [gen.motiveType])
    (g := gen.block.ctorPairs.length + 1)
    (by simp [gen.minorTypes_length])
    [] (d := 0) rfl
  have hSp : env.SpineWF (gen.recUvars)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          ((VExpr.liftTelN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination)
              0).reverse.length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.sort
          (gen.block.checked.resultLevel.inst
            (gen.sourceLevels))))
      ((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
        e.liftN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length)
      (.sort
        (gen.block.checked.resultLevel.inst
          (gen.sourceLevels))) := by
    simpa [List.append_assoc, Nat.add_assoc,
      List.length_reverse, VExpr.liftTelN_length]
      using hSp₀
  have hidxLen :
      ((ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
        e.liftN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length).length =
        gen.idxTel.length := by
    simp only [List.length_map,
      NormalizedCtor.resultIndicesR,
      GenerationChecked.idxTel]
    exact (S.viewResultIndices_length hctor).trans
      gen.shape.2.2.1.symm
  have ha₀ := S.ctorAppRule_hasType hctor
  have ha : env.HasType (gen.recUvars)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams gen.elimination)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.const ctor.raw.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            ((ctor.fieldsR
                source.uvars source.nparams gen.elimination).length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (gen.sourceLevels))
        (VExpr.bvarRevRange
            ((VExpr.liftTelN
                (gen.block.ctorPairs.length + 1)
                (ctor.fieldsR
                  source.uvars source.nparams gen.elimination)
                0).reverse.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          (ctor.resultIndicesR source.uvars gen.elimination).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams gen.elimination).length)) := by
    simpa only [List.length_reverse,
      VExpr.liftTelN_length] using ha₀
  have hr := S.recApp_hasType hrec
    (VExpr.liftTelN
      (gen.block.ctorPairs.length + 1)
      (ctor.fieldsR source.uvars source.nparams gen.elimination)
      0).reverse
    hSp hidxLen ha
  rw [List.length_reverse, VExpr.liftTelN_length,
    show
      (ctor.fieldsR
          source.uvars source.nparams gen.elimination).length +
          gen.block.ctorPairs.length =
        gen.block.ctorPairs.length +
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length by
      omega,
    show
      gen.block.ctorPairs.length +
          (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length + 1 =
        (ctor.fieldsR
            source.uvars source.nparams gen.elimination).length +
          gen.block.ctorPairs.length + 1 by
      omega] at hr
  exact hr

/-- Every per-constructor mixed iota rule is well formed in an environment
containing the generated recursor constant. -/
theorem rule_WF {i : Nat} {ctor : NormalizedCtor}
    (hci : gen.block.ctorPairs[i]? = some ctor)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) :
    (gen.rule i ctor).WF env := by
  have hctor := List.mem_of_getElem? hci
  refine ⟨?_, ?_⟩
  · show env.HasType (gen.recUvars) []
      (VExpr.lamN
        (gen.paramsTel ++
          gen.motiveType :: gen.minorTypes ++
          VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination)
            0)
        _)
      (VExpr.forallN _ _)
    refine HasType.lamN
      (S.ruleBinders_onTel hctor) ?_
    simp only [List.reverse_append,
      List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.recRuleApp_hasType hctor hrec
  · show env.HasType (gen.recUvars) []
      (VExpr.lamN
        (gen.paramsTel ++
          gen.motiveType :: gen.minorTypes ++
          VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            (ctor.fieldsR
              source.uvars source.nparams gen.elimination)
            0)
        _)
      (VExpr.forallN _ _)
    refine HasType.lamN
      (S.ruleBinders_onTel hctor) ?_
    simp only [List.reverse_append,
      List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.minorApp_hasType hci hrec

end GenerationEnv

theorem ctorFieldsR_length {U np : Nat} {c : VConstVal} :
    (ctorFieldsR U np c).length = (ctorFields (VExpr.dropN np c.type)).length :=
  List.length_map ..

theorem ctorFieldsR_getElem? {U np : Nat} {c : VConstVal} {q : Nat} :
    (ctorFieldsR U np c)[q]? =
    (ctorFields (VExpr.dropN np c.type))[q]?.map (VExpr.instL (VLevel.params' U 1)) :=
  List.getElem?_map ..

/-! ## The post-family environment invariant -/

/-- The facts available immediately after inserting a checked family,
before any constructor has been installed. Constructor types may refer to the
family, so this is the precise staging invariant needed to validate them. -/
structure DirectFamilyEnv (env : VEnv) (U : Nat) (T : Name)
    (np : Nat) (l : VLevel) (ty : VInductiveType) : Prop where
  ord : env.Ordered
  hl : l.WF U
  hsort : VExpr.resultOf (VExpr.dropN np ty.type) = .sort l
  hlen : (VExpr.telN np ty.type).length = np
  hT : env.constants T = some ⟨U, ty.type⟩
  hparams :
    OnTel env U []
      (VExpr.telN np ty.type ++
        ctorFields (VExpr.dropN np ty.type))

section DirectFamily

variable {env : VEnv} {U : Nat} {T : Name} {np : Nat}
  {l : VLevel} {ty : VInductiveType}
  (S : DirectFamilyEnv env U T np l ty)
include S

theorem DirectFamilyEnv.tyType_eq :
    ty.type =
      VExpr.forallN (VExpr.telN np ty.type)
        (VExpr.forallN
          (ctorFields (VExpr.dropN np ty.type)) (.sort l)) := by
  conv => lhs
          rw [← VExpr.forallN_telN_dropN np ty.type,
            ← forallN_ctorFields_resultOf
              (VExpr.dropN np ty.type), S.hsort]

theorem DirectFamilyEnv.tyType_isType :
    env.IsType U [] ty.type := by
  rw [S.tyType_eq, ← VExpr.forallN_append]
  exact IsType.forallN S.hparams ⟨_, HasType.sort S.hl⟩

theorem DirectFamilyEnv.tconst_decl {Γ} :
    env.HasType U Γ (.const T (VLevel.params U)) ty.type :=
  (HasType.const0 S.hT S.tyType_isType).weak0 S.ord

/-- Applying the newly inserted family to its parameter self-spine exposes
the index telescope in any constructor-field context. -/
theorem DirectFamilyEnv.recAppPi_hasType_decl (Δ : List VExpr) :
    env.HasType U (Δ ++ (VExpr.telN np ty.type).reverse)
      (recApp U T np Δ.length)
      ((VExpr.forallN
        (ctorFields (VExpr.dropN np ty.type)) (.sort l)).liftN
          Δ.length) := by
  have hcl : ty.type.ClosedN 0 :=
    Ordered.closedC (ci := ⟨U, ty.type⟩) S.ord S.hT
  have hf : env.HasType U
      (Δ ++ (VExpr.telN np ty.type).reverse ++ [])
      (.const T (VLevel.params U))
      ((VExpr.forallN (VExpr.telN np ty.type)
        (VExpr.forallN
          (ctorFields (VExpr.dropN np ty.type)) (.sort l))).liftN
            (Δ.length + (VExpr.telN np ty.type).length)) := by
    rw [← S.tyType_eq, hcl.liftN_eq (Nat.zero_le _)]
    exact S.tconst_decl
  have hout := HasType.appN_selfSpine (env := env) (U := U) hf
  rw [S.hlen] at hout
  simpa [recApp, List.append_nil] using hout

/-- Checked constructor fields form a telescope as soon as the family is
available; no constructor lookup is needed for recursive occurrences. -/
theorem DirectFamilyEnv.fieldsWF_onTel_decl :
    ∀ (Bs : List VExpr) (Δd : List VExpr) (j : Nat),
      Δd.length = j →
      fieldsWF U T np env l
        (ctorFields (VExpr.dropN np ty.type))
        (Δd ++ (VExpr.telN np ty.type).reverse) j Bs →
      OnTel env U
        (Δd ++ (VExpr.telN np ty.type).reverse) Bs
  | [], _, _, _, _ => trivial
  | B :: Bs, Δd, j, hΔ, ⟨hB, hSp, hrest⟩ => by
    refine ⟨?_, DirectFamilyEnv.fieldsWF_onTel_decl
      Bs (B :: Δd) (j+1) (by simp [hΔ]) hrest⟩
    rcases hB with hrec | hfun | ⟨-, u, h, -⟩
    · obtain ⟨hBeq, -, -⟩ := isRecField_eq hrec
      have hTapp := S.recAppPi_hasType_decl Δd
      rw [hΔ, VExpr.liftN_forallN] at hTapp
      have hgoal : env.HasType U
          (Δd ++ (VExpr.telN np ty.type).reverse)
          B (.sort l) := by
        rw [hBeq, VExpr.appN_append]
        exact (hSp hrec).hasType_appN hTapp
      exact ⟨_, hgoal⟩
    · obtain ⟨r, hr, -, hrtel, hrsp⟩ := hfun
      obtain ⟨hrj, -, hBeq, -, -, -⟩ := recArg?_eq hr
      rw [hBeq]
      refine IsType.forallN hrtel ⟨l, ?_⟩
      have hTapp :=
        S.recAppPi_hasType_decl (r.binders.reverse ++ Δd)
      rw [VExpr.liftN_forallN] at hTapp
      have hbase : env.HasType U
          (r.binders.reverse ++
            (Δd ++ (VExpr.telN np ty.type).reverse))
          (recApp U T np (j + r.binders.length))
          (VExpr.forallN
            (VExpr.liftTelN (j + r.binders.length)
              (ctorFields (VExpr.dropN np ty.type)) 0)
            (.sort l)) := by
        simpa [List.append_assoc, hΔ, Nat.add_comm] using hTapp
      rw [hrj] at hrsp
      simpa [recApp, VExpr.appN_append] using
        hrsp.hasType_appN hbase
    · exact ⟨u, h⟩

/-- The analyzed result spine types the exact family application at the end
of a constructor declaration. -/
theorem DirectFamilyEnv.ctorResult_hasType_decl
    {c : VConstVal}
    (hresult : env.SpineWF U
      ((ctorFields (VExpr.dropN np c.type)).reverse ++
        (VExpr.telN np ty.type).reverse)
      (VExpr.forallN
        (VExpr.liftTelN
          (ctorFields (VExpr.dropN np c.type)).length
          (ctorFields (VExpr.dropN np ty.type)) 0)
        (.sort l))
      (recFieldIdxs np
        (VExpr.resultOf (VExpr.dropN np c.type)))
      (.sort l)) :
    env.HasType U
      ((ctorFields (VExpr.dropN np c.type)).reverse ++
        (VExpr.telN np ty.type).reverse)
      (VExpr.appN (.const T (VLevel.params U))
        (VExpr.bvarRevRange
          (ctorFields (VExpr.dropN np c.type)).length np ++
          recFieldIdxs np
            (VExpr.resultOf (VExpr.dropN np c.type))))
      (.sort l) := by
  have hTapp := S.recAppPi_hasType_decl
    ((ctorFields (VExpr.dropN np c.type)).reverse)
  rw [List.length_reverse, VExpr.liftN_forallN] at hTapp
  rw [VExpr.appN_append]
  exact hresult.hasType_appN hTapp

end DirectFamily

/-- A checked family insertion constructs the post-family invariant directly
from the checker contract. -/
theorem Checked.WF.toDirectFamilyEnv
    {source : VInductDecl} {checked : source.Checked}
    {pre envT : VEnv} (hpre : pre.Ordered)
    (h : checked.WF pre)
    (hadd : pre.addConst checked.type.name
      checked.type.toVConstant = some envT) :
    DirectFamilyEnv envT source.uvars checked.type.name
      source.nparams checked.resultLevel checked.type where
  ord := by
    have hfamily : checked.type.toVConstant.WF pre := by
      show pre.IsType checked.type.uvars [] checked.type.type
      rw [checked.direct_anatomy.1]
      exact h.family_isType
    exact .const hpre hfamily hadd
  hl := checked.direct_anatomy.2.2.1
  hsort := checked.result_eq
  hlen := by simpa [checked.params_eq] using
    checked.direct_anatomy.2.1
  hT := by
    have hout := addConst_self hadd
    change envT.constants checked.type.name =
      some ⟨checked.type.uvars, checked.type.type⟩ at hout
    rw [checked.direct_anatomy.1] at hout
    exact hout
  hparams := by
    simpa [checked.params_eq, checked.indices_eq] using
      h.1.mono (addConst_le hadd)

/-! ## The stage-3 environment invariant -/

/-- Everything the piece-typing lemmas need about an environment that
already contains the block's type constant and constructors. -/
structure Stage3Env (env : VEnv) (U : Nat) (T : Name) (np : Nat) (l : VLevel)
    (ty : VInductiveType) : Prop where
  ord : env.Ordered
  hl : l.WF U
  hsort : VExpr.resultOf (VExpr.dropN np ty.type) = .sort l
  hlen : (VExpr.telN np ty.type).length = np
  hT : env.constants T = some ⟨U, ty.type⟩
  hcs : ∀ c ∈ ty.ctors, env.constants c.name = some ⟨U, c.type⟩
  htel : ∀ c ∈ ty.ctors, VExpr.telN np c.type = VExpr.telN np ty.type
  hs3 : ∀ c ∈ ty.ctors, stage3Ctor U T np (ctorFields (VExpr.dropN np ty.type)).length 0
    (VExpr.dropN np c.type) = true
  hparams : OnTel env U [] (VExpr.telN np ty.type ++ ctorFields (VExpr.dropN np ty.type))
  hfields : ∀ c ∈ ty.ctors, fieldsWF U T np env l (ctorFields (VExpr.dropN np ty.type))
    (VExpr.telN np ty.type).reverse 0 (ctorFields (VExpr.dropN np c.type))
  hresult : ∀ c ∈ ty.ctors, env.SpineWF U
    ((ctorFields (VExpr.dropN np c.type)).reverse ++ (VExpr.telN np ty.type).reverse)
    (VExpr.forallN (VExpr.liftTelN (ctorFields (VExpr.dropN np c.type)).length
      (ctorFields (VExpr.dropN np ty.type)) 0) (.sort l))
    (recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))) (.sort l)

variable {env : VEnv} {U : Nat} {T : Name} {np : Nat} {l : VLevel} {ty : VInductiveType}
  (S : Stage3Env env U T np l ty)
include S
-- `S` is included throughout so every lemma below is reachable as `S.lemma`,
-- including those whose statement and proof never mention it.
set_option linter.unusedSectionVars false

theorem Stage3Env.mono {env' : VEnv} (henv : env ≤ env') (ord' : env'.Ordered) :
    Stage3Env env' U T np l ty where
  ord := ord'
  hl := S.hl
  hsort := S.hsort
  hlen := S.hlen
  hT := henv.constants S.hT
  hcs := fun c hc => henv.constants (S.hcs c hc)
  htel := S.htel
  hs3 := S.hs3
  hparams := S.hparams.mono henv
  hfields := fun c hc => fieldsWF_mono henv (S.hfields c hc)
  hresult := fun c hc => (S.hresult c hc).mono henv

/-- The block's type split at the parameters and indices. -/
theorem Stage3Env.tyType_eq : ty.type =
    VExpr.forallN (VExpr.telN np ty.type)
      (VExpr.forallN (ctorFields (VExpr.dropN np ty.type)) (.sort l)) := by
  conv => lhs; rw [← VExpr.forallN_telN_dropN np ty.type,
    ← forallN_ctorFields_resultOf (VExpr.dropN np ty.type), S.hsort]

/-- The type of the block constant is a type. -/
theorem Stage3Env.tyType_isType : env.IsType U [] ty.type := by
  rw [S.tyType_eq, ← VExpr.forallN_append]
  exact IsType.forallN S.hparams ⟨_, HasType.sort S.hl⟩

/-- The block constant at the declaration universes, in any context. -/
theorem Stage3Env.tconst_decl {Γ} :
    env.HasType U Γ (.const T (VLevel.params U)) ty.type :=
  (HasType.const0 S.hT S.tyType_isType).weak0 S.ord

/-- The type of the block constant, instantiated to the recursor universes. -/
theorem Stage3Env.tyType_instL :
    ty.type.instL (VLevel.params' U 1) =
    VExpr.forallN (paramsTel U np ty)
      (VExpr.forallN (idxTel U np ty) (.sort (l.inst (VLevel.params' U 1)))) := by
  conv => lhs; rw [S.tyType_eq]
  rw [VExpr.instL_forallN, VExpr.instL_forallN]
  rfl

/-- The block constant at the recursor universes, in any context. -/
theorem Stage3Env.tconst {Γ} :
    env.HasType (U+1) Γ (.const T (VLevel.params' U 1)) (ty.type.instL (VLevel.params' U 1)) := by
  have := (S.tconst_decl (Γ := [])).instL (U' := U+1) VLevel.params'_one_wf
  rw [show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
    .const T (VLevel.params' U 1) from by
      simp [VExpr.instL, VLevel.params_map_inst_params']] at this
  exact this.weak0 S.ord

/-- The parameter spine applied to the block constant, `Δ` binders past
the parameter telescope (declaration universes): the index pi. -/
theorem Stage3Env.recAppPi_hasType_decl (Δ : List VExpr) :
    env.HasType U (Δ ++ (VExpr.telN np ty.type).reverse) (recApp U T np Δ.length)
      ((VExpr.forallN (ctorFields (VExpr.dropN np ty.type)) (.sort l)).liftN Δ.length) := by
  have hcl : ty.type.ClosedN 0 := Ordered.closedC (ci := ⟨U, ty.type⟩) S.ord S.hT
  have hf : env.HasType U (Δ ++ (VExpr.telN np ty.type).reverse ++ [])
      (.const T (VLevel.params U))
      ((VExpr.forallN (VExpr.telN np ty.type)
        (VExpr.forallN (ctorFields (VExpr.dropN np ty.type)) (.sort l))).liftN
        (Δ.length + (VExpr.telN np ty.type).length)) := by
    rw [← S.tyType_eq, hcl.liftN_eq (Nat.zero_le _)]
    exact S.tconst_decl
  have := HasType.appN_selfSpine (env := env) (U := U) hf
  rw [S.hlen] at this
  simpa [recApp, List.append_nil] using this

/-- The parameter spine at the recursor universes: the index pi. -/
theorem Stage3Env.recAppPi_hasType (Δ : List VExpr) :
    env.HasType (U+1) (Δ ++ (paramsTel U np ty).reverse) (recApp' U T np Δ.length)
      ((VExpr.forallN (idxTel U np ty)
        (.sort (l.inst (VLevel.params' U 1)))).liftN Δ.length) := by
  have hcl : (ty.type.instL (VLevel.params' U 1)).ClosedN 0 :=
    (Ordered.closedC (ci := ⟨U, ty.type⟩) S.ord S.hT).instL
  have hf : env.HasType (U+1) (Δ ++ (paramsTel U np ty).reverse ++ [])
      (.const T (VLevel.params' U 1))
      ((VExpr.forallN (paramsTel U np ty)
        (VExpr.forallN (idxTel U np ty) (.sort (l.inst (VLevel.params' U 1))))).liftN
        (Δ.length + (paramsTel U np ty).length)) := by
    rw [← S.tyType_instL, hcl.liftN_eq (Nat.zero_le _)]
    exact S.tconst
  have := HasType.appN_selfSpine (env := env) (U := U+1) hf
  rw [show (paramsTel U np ty).length = np from by
    simp [paramsTel, List.length_map, S.hlen]] at this
  simpa [recApp', List.append_nil] using this

/-- The block applied to the full parameter-and-index self-spine is a
sort, in the context of the indices over the parameters. -/
theorem Stage3Env.motiveTApp_hasType :
    env.HasType (U+1) ((idxTel U np ty).reverse ++ (paramsTel U np ty).reverse)
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (idxTel U np ty).length np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (l.inst (VLevel.params' U 1))) := by
  have hcl : (ty.type.instL (VLevel.params' U 1)).ClosedN 0 :=
    (Ordered.closedC (ci := ⟨U, ty.type⟩) S.ord S.hT).instL
  have hf : env.HasType (U+1)
      ([] ++ (paramsTel U np ty ++ idxTel U np ty).reverse ++ [])
      (.const T (VLevel.params' U 1))
      ((VExpr.forallN (paramsTel U np ty ++ idxTel U np ty)
        (.sort (l.inst (VLevel.params' U 1)))).liftN
        (List.length ([] : List VExpr) +
          (paramsTel U np ty ++ idxTel U np ty).length)) := by
    rw [VExpr.forallN_append, ← S.tyType_instL, hcl.liftN_eq (Nat.zero_le _)]
    exact S.tconst
  have h2 := HasType.appN_selfSpine (env := env) (U := U+1) hf
  rw [show List.length ([] : List VExpr) = 0 from rfl,
    VExpr.bvarRevRange_congr' 0 (show (paramsTel U np ty ++ idxTel U np ty).length =
      (idxTel U np ty).length + np from by
      simp [paramsTel, List.length_map, S.hlen]; omega),
    ← VExpr.bvarRevRange_append] at h2
  simpa [List.append_nil, List.reverse_append] using h2

/-- Field telescopes are well-formed in context, at the declaration
universes: recursive fields by the partial parameter application of the
block followed by the carried index-spine typing. -/
theorem Stage3Env.fieldsWF_onTel_decl :
    ∀ (Bs : List VExpr) (Δd : List VExpr) (j : Nat), Δd.length = j →
    fieldsWF U T np env l (ctorFields (VExpr.dropN np ty.type))
      (Δd ++ (VExpr.telN np ty.type).reverse) j Bs →
    OnTel env U (Δd ++ (VExpr.telN np ty.type).reverse) Bs
  | [], _, _, _, _ => trivial
  | B :: Bs, Δd, j, hΔ, ⟨hB, hSp, hT⟩ => by
    refine ⟨?_, Stage3Env.fieldsWF_onTel_decl Bs (B :: Δd) (j+1) (by simp [hΔ]) hT⟩
    rcases hB with hrec | hfun | ⟨-, u, h, -⟩
    · obtain ⟨hBeq, -, -⟩ := isRecField_eq hrec
      have hTapp := S.recAppPi_hasType_decl Δd
      rw [hΔ, VExpr.liftN_forallN] at hTapp
      have hgoal : env.HasType U (Δd ++ (VExpr.telN np ty.type).reverse) B (.sort l) := by
        rw [hBeq, VExpr.appN_append]
        exact (hSp hrec).hasType_appN hTapp
      exact ⟨_, hgoal⟩
    · obtain ⟨r, hr, -, hrtel, hrsp⟩ := hfun
      obtain ⟨hrj, -, hBeq, -, -, -⟩ := recArg?_eq hr
      rw [hBeq]
      refine IsType.forallN hrtel ⟨l, ?_⟩
      have hTapp := S.recAppPi_hasType_decl (r.binders.reverse ++ Δd)
      rw [VExpr.liftN_forallN] at hTapp
      have hbase : env.HasType U
          (r.binders.reverse ++ (Δd ++ (VExpr.telN np ty.type).reverse))
          (recApp U T np (j + r.binders.length))
          (VExpr.forallN
            (VExpr.liftTelN (j + r.binders.length)
              (ctorFields (VExpr.dropN np ty.type)) 0) (.sort l)) := by
        simpa [List.append_assoc, hΔ, Nat.add_comm] using hTapp
      rw [hrj] at hrsp
      simpa [recApp, VExpr.appN_append] using hrsp.hasType_appN hbase
    · exact ⟨u, h⟩

/-- Field telescopes are well-formed in context, at the recursor
universes. -/
theorem Stage3Env.fieldsWF_onTel :
    ∀ (Bs : List VExpr) (Δd : List VExpr) (j : Nat), Δd.length = j →
    fieldsWF U T np env l (ctorFields (VExpr.dropN np ty.type))
      (Δd ++ (VExpr.telN np ty.type).reverse) j Bs →
    OnTel env (U+1)
      ((Δd ++ (VExpr.telN np ty.type).reverse).map (VExpr.instL (VLevel.params' U 1)))
      (Bs.map (VExpr.instL (VLevel.params' U 1)))
  | Bs, Δd, j, hΔ, hfields => by
    exact (S.fieldsWF_onTel_decl Bs Δd j hΔ hfields).instL VLevel.params'_one_wf

/-- The constructor's type, split at the parameters. -/
theorem Stage3Env.ctorType_eq {c : VConstVal} (hc : c ∈ ty.ctors) :
    c.type = VExpr.forallN (VExpr.telN np ty.type)
      (VExpr.forallN (ctorFields (VExpr.dropN np c.type))
        (VExpr.appN (.const T (VLevel.params U))
          (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
            recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))))) := by
  conv => lhs; rw [← VExpr.forallN_telN_dropN np c.type, S.htel c hc,
    (stage3Ctor_eq (S.hs3 c hc)).1]

theorem Stage3Env.ctorType_instL {c : VConstVal} (hc : c ∈ ty.ctors) :
    c.type.instL (VLevel.params' U 1) =
    VExpr.forallN (paramsTel U np ty)
      (VExpr.forallN (ctorFieldsR U np c)
        (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
            ctorIdxs U np c))) := by
  conv => lhs; rw [S.ctorType_eq hc, VExpr.instL_forallN, VExpr.instL_forallN,
    VExpr.instL_appN, List.map_append, bvarRevRange_instL,
    show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
      .const T (VLevel.params' U 1) from by
      simp [VExpr.instL, VLevel.params_map_inst_params']]
  rfl

/-- The constructor's result, typed by the partial parameter application
and the carried result-spine typing (declaration universes). -/
theorem Stage3Env.ctorResult_hasType_decl {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.HasType U
      ((ctorFields (VExpr.dropN np c.type)).reverse ++ (VExpr.telN np ty.type).reverse)
      (VExpr.appN (.const T (VLevel.params U))
        (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
          recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))))
      (.sort l) := by
  have hTapp := S.recAppPi_hasType_decl ((ctorFields (VExpr.dropN np c.type)).reverse)
  rw [List.length_reverse, VExpr.liftN_forallN] at hTapp
  rw [VExpr.appN_append,
    VExpr.bvarRevRange_congr np (show 0 + (ctorFields (VExpr.dropN np c.type)).length =
      (ctorFields (VExpr.dropN np c.type)).length from by omega)]
  exact (S.hresult c hc).hasType_appN hTapp

/-- A constructor's declared type is well-formed (declaration universes). -/
theorem Stage3Env.ctorType_isType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.IsType U [] c.type := by
  rw [S.ctorType_eq hc]
  refine IsType.forallN (S.hparams.of_append.1) ?_
  simp only [List.append_nil]
  refine IsType.forallN
    (S.fieldsWF_onTel_decl _ [] 0 rfl (by simpa using S.hfields c hc)) ?_
  exact ⟨_, by simpa using S.ctorResult_hasType_decl hc⟩

/-- The constructor constant at the recursor universes, any context. -/
theorem Stage3Env.cConst {c : VConstVal} (hc : c ∈ ty.ctors) {Γ} :
    env.HasType (U+1) Γ (.const c.name (VLevel.params' U 1))
      (c.type.instL (VLevel.params' U 1)) := by
  have h0 := HasType.const0 (S.hcs c hc) (S.ctorType_isType hc)
  have := h0.instL (U' := U+1) VLevel.params'_one_wf
  rw [show (VExpr.const c.name (VLevel.params U)).instL (VLevel.params' U 1) =
    .const c.name (VLevel.params' U 1) from by
      simp [VExpr.instL, VLevel.params_map_inst_params']] at this
  exact this.weak0 S.ord

/-- The index telescope is well-formed over the parameters, at the
recursor universes. -/
theorem Stage3Env.idxTel_onTel :
    OnTel env (U+1) (paramsTel U np ty).reverse (idxTel U np ty) := by
  have h0 := (S.hparams.of_append.2).instL (U' := U+1) VLevel.params'_one_wf
  simpa [paramsTel, idxTel, List.map_reverse] using h0

theorem Stage3Env.motive_isType :
    env.IsType (U+1) (paramsTel U np ty).reverse (motiveType U T np ty) := by
  refine IsType.forallN S.idxTel_onTel ?_
  exact ⟨_, HasType.forallE S.motiveTApp_hasType (HasType.sort (Nat.succ_pos U))⟩

/-- Transport a recursive field's index-spine typing into a rule or minor
context: instantiate the universes, insert `mid` (motive, or motive and
minors) at the field's depth `j`, and push a `d`-entry stack underneath. -/
theorem Stage3Env.spine_transport {c : VConstVal} (hc : c ∈ ty.ctors)
    {j : Nat} {B : VExpr}
    (hBj : (ctorFields (VExpr.dropN np c.type))[j]? = some B)
    (hrec : isRecField U T np (ctorFields (VExpr.dropN np ty.type)).length j B = true)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.SpineWF (U+1)
      (As₂ ++ ((VExpr.liftTelN g ((ctorFieldsR U np c).take j) 0).reverse ++
        (mid ++ (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN (j + g + d) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      (((recFieldIdxs np B).map (VExpr.instL (VLevel.params' U 1))).map
        fun e => (e.liftN g j).liftN d)
      (.sort (l.inst (VLevel.params' U 1))) := by
  have hjlen : ((ctorFieldsR U np c).take j).length = j := by
    have h1 := (List.getElem?_eq_some_iff.1 hBj).1
    simp only [ctorFieldsR, List.length_take, List.length_map]
    omega
  -- (1) declaration-universe spine from the fieldsWF chain
  have h0 := fieldsWF_spine (S.hfields c hc) j B (by simpa using hBj)
    (by simpa using hrec)
  rw [Nat.zero_add] at h0
  -- (2) universe instantiation
  have h1 := h0.instL (U' := U+1) VLevel.params'_one_wf
  rw [VExpr.instL_forallN, VExpr.liftTelN_instL,
    show (((ctorFields (VExpr.dropN np c.type)).take j).reverse ++
        (VExpr.telN np ty.type).reverse).map (VExpr.instL (VLevel.params' U 1)) =
      ((ctorFieldsR U np c).take j).reverse ++ (paramsTel U np ty).reverse from by
      simp [ctorFieldsR, paramsTel, List.map_reverse, List.map_take]] at h1
  -- (3) insert `mid` at depth `j`
  have W₁ := Ctx.LiftN.consTel (n := mid.length) ((ctorFieldsR U np c).take j)
    (Ctx.LiftN.zero (Γ := (paramsTel U np ty).reverse) mid)
  rw [hjlen, Nat.add_zero] at W₁
  have h2 := h1.weakN S.ord W₁
  rw [VExpr.liftN_forallN, hg] at h2
  -- (4) push the stack underneath
  have h3 := h2.weakN S.ord (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  rw [VExpr.liftN_forallN] at h3
  rw [VExpr.liftTelN_liftTelN_hi' j g _ 0 (by omega), VExpr.liftTelN_liftTelN,
    show (ctorFields (VExpr.dropN np ty.type)).map (VExpr.instL (VLevel.params' U 1)) =
      idxTel U np ty from rfl] at h3
  simpa [VExpr.instL, VExpr.liftN, List.map_map, Function.comp_def,
    List.append_assoc] using h3

/-- Transport all semantic evidence for a recursive argument beneath a Pi
telescope. This is the functional counterpart of `spine_transport`: it
transports both the argument telescope and the terminal family-index spine.
-/
theorem Stage3Env.recArg_transport {c : VConstVal} (hc : c ∈ ty.ctors)
    {r₀ : RecArg} {B : VExpr}
    (hB : (ctorFields (VExpr.dropN np c.type))[r₀.fieldIndex]? = some B)
    (hr : recArg? U T np (idxTel U np ty).length r₀.fieldIndex B = some r₀)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    let r := r₀.instL (VLevel.params' U 1)
    let As := VExpr.liftTelN d (VExpr.liftTelN g r.binders r.fieldIndex) 0
    OnTel env (U+1)
        (As₂ ++ ((VExpr.liftTelN g
          ((ctorFieldsR U np c).take r.fieldIndex) 0).reverse ++
          (mid ++ (paramsTel U np ty).reverse))) As ∧
      env.SpineWF (U+1)
        (As.reverse ++
          (As₂ ++ ((VExpr.liftTelN g
            ((ctorFieldsR U np c).take r.fieldIndex) 0).reverse ++
            (mid ++ (paramsTel U np ty).reverse))))
        (VExpr.forallN
          (VExpr.liftTelN
            (r.fieldIndex + r.binders.length + g + d) (idxTel U np ty) 0)
          (.sort (l.inst (VLevel.params' U 1))))
        (r.indices.map fun e =>
          (e.liftN g (r.fieldIndex + r.binders.length)).liftN d r.binders.length)
        (.sort (l.inst (VLevel.params' U 1))) := by
  dsimp only
  have hjlt : r₀.fieldIndex < (ctorFields (VExpr.dropN np c.type)).length :=
    (List.getElem?_eq_some_iff.1 hB).1
  have hsem := fieldsWF_recArg (S.hfields c hc) r₀.fieldIndex B r₀ hB (by
    simpa [idxTel_length] using hr)
  have htel₁ := hsem.1.instL (U' := U+1) VLevel.params'_one_wf
  have hsp₁ := hsem.2.instL (U' := U+1) VLevel.params'_one_wf
  have hctx :
      (((ctorFields (VExpr.dropN np c.type)).take r₀.fieldIndex).reverse ++
        (VExpr.telN np ty.type).reverse).map (VExpr.instL (VLevel.params' U 1)) =
      ((ctorFieldsR U np c).take r₀.fieldIndex).reverse ++
        (paramsTel U np ty).reverse := by
    simp [ctorFieldsR, paramsTel, List.map_reverse, List.map_take]
  rw [hctx] at htel₁
  rw [List.map_append, List.map_reverse, hctx] at hsp₁
  simp only [VExpr.instL_forallN, VExpr.liftTelN_instL] at htel₁ hsp₁
  have hjlen : ((ctorFieldsR U np c).take r₀.fieldIndex).length =
      r₀.fieldIndex := by
    simp only [ctorFieldsR, List.length_take, List.length_map]
    omega
  have W₁ := Ctx.LiftN.consTel (n := mid.length)
    ((ctorFieldsR U np c).take r₀.fieldIndex)
    (Ctx.LiftN.zero (Γ := (paramsTel U np ty).reverse) mid)
  rw [hjlen, Nat.add_zero] at W₁
  have htel₂ := htel₁.weakN S.ord W₁
  have hsp₂ := hsp₁.weakN S.ord
    (Ctx.LiftN.consTel
      (r₀.binders.map (VExpr.instL (VLevel.params' U 1))) W₁)
  rw [hg] at htel₂ hsp₂
  have W₂ := Ctx.LiftN.zero
    (Γ := (VExpr.liftTelN g
        ((ctorFieldsR U np c).take r₀.fieldIndex) 0).reverse ++
      (mid ++ (paramsTel U np ty).reverse)) As₂ (h := hd)
  have htel₃ := htel₂.weakN S.ord W₂
  have hsp₃ := hsp₂.weakN S.ord
    (Ctx.LiftN.consTel
      (VExpr.liftTelN g
        (r₀.binders.map (VExpr.instL (VLevel.params' U 1))) r₀.fieldIndex) W₂)
  refine ⟨?_, ?_⟩
  · simpa [RecArg.instL, List.append_assoc] using htel₃
  · simp only [List.length_map, VExpr.liftTelN_length, Nat.add_zero] at hsp₃
    rw [VExpr.liftN_forallN, VExpr.liftN_forallN,
      VExpr.liftTelN_liftTelN_hi' (r₀.fieldIndex + r₀.binders.length) g _ 0
        (by omega),
      VExpr.liftTelN_liftTelN_mid
        (r₀.fieldIndex + r₀.binders.length + g) d _ 0 r₀.binders.length
        (Nat.zero_le _) (by omega),
      show (ctorFields (VExpr.dropN np ty.type)).map
          (VExpr.instL (VLevel.params' U 1)) = idxTel U np ty from rfl] at hsp₃
    rw [show r₀.binders.length + r₀.fieldIndex =
      r₀.fieldIndex + r₀.binders.length from Nat.add_comm _ _] at hsp₃
    simpa [RecArg.instL, VExpr.instL, VExpr.liftN, List.map_map,
      Function.comp_def, List.append_assoc] using hsp₃

omit S in
/-- Apply a motive variable to a typed family-index spine and major premise.
Unlike `Stage3Env.motiveApp_hasType`, this helper is independent of the
recursor's minor-premise stack, so it also applies under a recursive
argument's private Pi telescope. -/
theorem motiveVarApp_hasType {Γ : List VExpr} {K : Nat}
    {idxs : List VExpr} {a : VExpr}
    (hM : env.HasType (U+1) Γ (.bvar K)
      ((motiveType U T np ty).liftN (K+1)))
    (hidx : env.SpineWF (U+1) Γ
      (VExpr.forallN (VExpr.liftTelN (K+1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))))
    (hlen : idxs.length = (idxTel U np ty).length)
    (ha : env.HasType (U+1) Γ a
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (K+1) np ++ idxs))) :
    env.HasType (U+1) Γ
      (VExpr.appN (.bvar K) (idxs ++ [a])) (.sort (.param 0)) := by
  rw [motiveType_liftN] at hM
  have hshape := hidx.retarget
    (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (K+1 + (idxTel U np ty).length) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show K+1+(idxTel U np ty).length-idxs.length = K+1 from by
      rw [hlen, Nat.add_sub_cancel],
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hApp := hshape.hasType_appN hM
  rw [VExpr.appN_append]
  exact HasType.app hApp (by simpa using ha)

/-- One generalized induction-hypothesis entry is a type in the minor
premise context. Recursive Pi arguments become Pi-valued hypotheses whose
body applies both the motive and the recursive field to the same private
self-spine. -/
theorem Stage3Env.recArgMinor_isType {c : VConstVal} (hc : c ∈ ty.ctors)
    {r : RecArg}
    (hrmem : r ∈ recArgsR U T np (idxTel U np ty).length c)
    (Δ : List VExpr) (p : Nat) (hΔ : Δ.length = p) :
    env.IsType (U+1)
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (r.minorIH (ctorFieldsR U np c).length p) := by
  obtain ⟨r₀, B, rfl, hB, hr₀⟩ := recArgsR_mem hrmem
  let r := r₀.instL (VLevel.params' U 1)
  let m := (ctorFieldsR U np c).length
  let j := r₀.fieldIndex
  let Fs := VExpr.liftTelN 1 (ctorFieldsR U np c) 0
  let As := r.minorBinders m p
  let idxs := r.indices.map fun e =>
    (e.liftN 1 (r.fieldIndex+r.binders.length)).liftN (m-r.fieldIndex+p) r.binders.length
  let Γ := Δ ++ Fs.reverse ++
    (motiveType U T np ty :: (paramsTel U np ty).reverse)
  have hjm : j < m := by
    simpa [j, m, RecArg.instL, ctorFieldsR_length] using recArgsR_lt _ hrmem
  have hFsLen : Fs.length = m := by simp [Fs, m, VExpr.liftTelN_length]
  have hstackLen : (Δ ++ (Fs.drop j).reverse).length = m-j+p := by
    simp only [List.length_append, List.length_reverse, List.length_drop, hFsLen, hΔ]
    omega
  have ht := S.recArg_transport hc hB hr₀ [motiveType U T np ty] rfl
    (Δ ++ (Fs.drop j).reverse) hstackLen
  simp only [List.length_singleton, RecArg.instL] at ht
  have hctx :
      (Δ ++ (Fs.drop j).reverse) ++
          ((VExpr.liftTelN 1 ((ctorFieldsR U np c).take j) 0).reverse ++
            ([motiveType U T np ty] ++ (paramsTel U np ty).reverse)) = Γ := by
    dsimp only [Γ, Fs]
    rw [← VExpr.liftTelN_take, List.append_assoc,
      ← List.append_assoc ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).drop j).reverse,
      ← List.reverse_append, List.take_append_drop, List.singleton_append,
      ← List.append_assoc]
  dsimp only [j] at ht hctx
  have htel : OnTel env (U+1) Γ As := by
    rw [hctx] at ht
    simpa [r, As, m, j, RecArg.instL,
      RecArg.minorBinders] using ht.1
  have hsp : env.SpineWF (U+1) (As.reverse ++ Γ)
      (VExpr.forallN
        (VExpr.liftTelN (m+p+r.binders.length+1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))) := by
    rw [hctx] at ht
    simpa [r, As, idxs, m, j, RecArg.instL,
      RecArg.minorBinders, List.append_assoc,
      show j + r₀.binders.length + 1 + (m-j+p) =
        m+p+r₀.binders.length+1 from by omega] using ht.2
  have hF : Γ[m-1-j+p]? =
      some ((B.instL (VLevel.params' U 1)).liftN 1 j) := by
    dsimp only [Γ, Fs]
    rw [getElem?_stack_mid Δ
        (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse
        (motiveType U T np ty :: (paramsTel U np ty).reverse)
        (i := m-1-j+p) (by rw [hΔ]; omega)
        (by simp only [hΔ, List.length_reverse, VExpr.liftTelN_length]; omega),
      show m - 1 - j + p - Δ.length = m - 1 - j from by rw [hΔ]; omega,
      List.getElem?_reverse (by rw [hFsLen]; omega),
      VExpr.liftTelN_length,
      show m - 1 - (m - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?, ctorFieldsR_getElem?, hB]
    simp
  have hlu := Lookup.of_getElem? hF
  rw [show m-1-j+p+1 = m-j+p from by omega] at hlu
  dsimp only [j, r] at hlu
  have hfield := recArg_minor_fieldType hr₀ m p (by simpa [j] using hjm)
  simp only [RecArg.instL, ElimMode.large_sourceLevels] at hfield
  rw [hfield] at hlu
  have hf0 := VEnv.HasType.bvar (env := env) (U := U+1) hlu
  have hf := hf0.weakN S.ord (Ctx.LiftN.zero (Γ := Γ) As.reverse)
  have hmajor := VEnv.HasType.appN_selfSpine (env := env) (U := U+1)
    (As := As) (B := VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (m+p+r.binders.length+1) np ++ idxs))
    (Δ := []) (Γ := Γ) (by
      simpa [As, r, idxs, j, RecArg.instL, List.length_reverse,
        List.map_map, Function.comp_def] using hf)
  simp only [List.length_nil, VExpr.liftN_zero, List.nil_append] at hmajor
  have hAsLen : As.length = r.binders.length := by
    simp [As, RecArg.minorBinders, VExpr.liftTelN_length]
  change env.HasType (U+1) (As.reverse ++ Γ)
    ((VExpr.bvar (m-1-r.fieldIndex+p+As.length)).appN
      (VExpr.bvarRevRange 0 As.length))
    (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (m+p+r.binders.length+1) np ++ idxs)) at hmajor
  rw [hAsLen] at hmajor
  have hMget : (As.reverse ++ Γ)[m+p+r.binders.length]? =
      some (motiveType U T np ty) := by
    have hM0 := getElem?_rstack3 As.reverse (Δ ++ Fs.reverse)
      (motiveType U T np ty) (paramsTel U np ty).reverse
      (i := m+p+r.binders.length)
      (by simp [As, RecArg.minorBinders, r, m, Fs, hΔ, VExpr.liftTelN_length,
        RecArg.instL]; omega)
    simpa [Γ, List.append_assoc] using hM0
  have hM := VEnv.HasType.bvar (env := env) (U := U+1)
    (Lookup.of_getElem? hMget)
  have hlen : idxs.length = (idxTel U np ty).length := by
    simpa [idxs, r, RecArg.instL] using (recArg?_eq hr₀).2.2.2.1
  have hbody := motiveVarApp_hasType (env := env) (U := U) (T := T)
    (np := np) (l := l) (ty := ty) hM hsp hlen hmajor
  refine IsType.forallN htel ⟨VLevel.param 0, ?_⟩
  simpa [RecArg.minorIH, r, As, idxs, m, Γ, Fs, List.append_assoc] using hbody

/-- Well-formedness of the generalized induction-hypothesis telescope. Each
entry is supplied by `recArgMinor_isType`; recursive Pi arguments therefore
contribute one functional IH, not one IH per private binder. -/
theorem Stage3Env.ihsRec_onTel {c : VConstVal} (hc : c ∈ ty.ctors) :
    ∀ (rsSuf : List RecArg),
    (∀ r ∈ rsSuf, r ∈ recArgsR U T np (idxTel U np ty).length c) →
    ∀ (Δ : List VExpr) (p : Nat), Δ.length = p →
    OnTel env (U+1)
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (ihsFromRecArgs (ctorFieldsR U np c).length rsSuf p)
  | [], _, _, _, _ => trivial
  | r :: rsSuf, hqs, Δ, p, hΔ =>
    ⟨S.recArgMinor_isType hc (hqs r (.head _)) Δ p hΔ,
      Stage3Env.ihsRec_onTel hc rsSuf (fun q hq => hqs q (.tail _ hq))
        (_ :: Δ) (p+1) (by simp [hΔ])⟩

/-- Transport the constructor result's index-spine typing into a rule or
minor context, like `spine_transport` but at the bottom of the full field
telescope. -/
theorem Stage3Env.result_transport {c : VConstVal} (hc : c ∈ ty.ctors)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.SpineWF (U+1)
      (As₂ ++ ((VExpr.liftTelN g (ctorFieldsR U np c) 0).reverse ++
        (mid ++ (paramsTel U np ty).reverse)))
      (VExpr.forallN
        (VExpr.liftTelN ((ctorFieldsR U np c).length + g + d) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e => (e.liftN g (ctorFieldsR U np c).length).liftN d)
      (.sort (l.inst (VLevel.params' U 1)))
    := by
  have hml : (ctorFieldsR U np c).length =
      (ctorFields (VExpr.dropN np c.type)).length := ctorFieldsR_length
  -- (1) the carried result spine, universes instantiated
  have h1 := (S.hresult c hc).instL (U' := U+1) VLevel.params'_one_wf
  rw [VExpr.instL_forallN, VExpr.liftTelN_instL,
    show ((ctorFields (VExpr.dropN np c.type)).reverse ++
        (VExpr.telN np ty.type).reverse).map (VExpr.instL (VLevel.params' U 1)) =
      (ctorFieldsR U np c).reverse ++ (paramsTel U np ty).reverse from by
      simp [ctorFieldsR, paramsTel, List.map_reverse],
    liftTelN_congr _ _ hml.symm] at h1
  -- (2) insert `mid` at the bottom of the fields
  have W₁ := Ctx.LiftN.consTel (n := mid.length) (ctorFieldsR U np c)
    (Ctx.LiftN.zero (Γ := (paramsTel U np ty).reverse) mid)
  rw [Nat.add_zero] at W₁
  have h2 := h1.weakN S.ord W₁
  rw [VExpr.liftN_forallN, hg] at h2
  -- (3) push the stack underneath
  have h3 := h2.weakN S.ord (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  rw [VExpr.liftN_forallN] at h3
  rw [VExpr.liftTelN_liftTelN_hi' (ctorFieldsR U np c).length g _ 0 (by omega),
    VExpr.liftTelN_liftTelN,
    show (ctorFields (VExpr.dropN np ty.type)).map (VExpr.instL (VLevel.params' U 1)) =
      idxTel U np ty from rfl] at h3
  simpa [ctorIdxs, VExpr.instL, VExpr.liftN, List.map_map, Function.comp_def,
    List.append_assoc] using h3

/-- Well-formedness of the induction-hypothesis telescope of a minor
premise, at any suffix of the recursive positions and any depth. -/
theorem Stage3Env.ihs_onTel {c : VConstVal} (hc : c ∈ ty.ctors) :
    ∀ (rsSuf : List (Nat × List VExpr)),
    (∀ q ∈ rsSuf, q ∈ recPairsR U T np (idxTel U np ty).length c) →
    ∀ (Δ : List VExpr) (p : Nat), Δ.length = p →
    OnTel env (U+1)
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (ihsFrom (ctorFieldsR U np c).length rsSuf p)
  | [], _, _, _, _ => trivial
  | (j, idxs) :: rsSuf, hqs, Δ, p, hΔ => by
    have hq := hqs _ (List.Mem.head _)
    obtain ⟨B, hBj0, hrec0, hidx0⟩ := recPairsR_mem hq
    have hBj : (ctorFields (VExpr.dropN np c.type))[j]? = some B := hBj0
    have hrec : isRecField U T np (ctorFields (VExpr.dropN np ty.type)).length j B =
        true := by
      have h : isRecField U T np (idxTel U np ty).length j B = true := hrec0
      rwa [idxTel_length] at h
    have hidx' : idxs = (recFieldIdxs np B).map (VExpr.instL (VLevel.params' U 1)) := hidx0
    have hjlt : j < (ctorFields (VExpr.dropN np c.type)).length := by
      simpa using recPairsR_lt _ hq
    have hml : (ctorFieldsR U np c).length =
        (ctorFields (VExpr.dropN np c.type)).length := ctorFieldsR_length
    have hml2 : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
        (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
    have hni : (recFieldIdxs np B).length = (ctorFields (VExpr.dropN np ty.type)).length :=
      (isRecField_eq hrec).2.1
    refine ⟨?_, Stage3Env.ihs_onTel hc rsSuf (fun q hq' => hqs q (.tail _ hq'))
      (_ :: Δ) (p+1) (by simp [hΔ])⟩
    -- the motive variable
    have hM := getElem?_stack3 Δ
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (paramsTel U np ty).reverse (motiveType U T np ty)
      (i := (ctorFieldsR U np c).length + p)
      (by simp only [hΔ, List.length_reverse, VExpr.liftTelN_length]; omega)
    have hmlu := Lookup.of_getElem? hM
    rw [motiveType_liftN] at hmlu
    -- the transported index spine
    have hSp := S.spine_transport hc hBj hrec [motiveType U T np ty] (g := 1) rfl
      (Δ ++ ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).drop j).reverse)
      (d := (ctorFieldsR U np c).length - j + p)
      (by simp only [List.length_append, List.length_reverse, List.length_drop,
            hml2, hΔ]
          omega)
    rw [show (Δ ++ ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).drop j).reverse) ++
        ((VExpr.liftTelN 1 ((ctorFieldsR U np c).take j) 0).reverse ++
          ([motiveType U T np ty] ++ (paramsTel U np ty).reverse)) =
      Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse) from by
        rw [← VExpr.liftTelN_take, List.append_assoc,
          ← List.append_assoc (((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).drop j).reverse),
          ← List.reverse_append, List.take_append_drop, List.singleton_append,
          ← List.append_assoc],
      liftTelN_congr _ _ (show j + 1 + ((ctorFieldsR U np c).length - j + p) =
        (ctorFieldsR U np c).length + p + 1 from by omega),
      ← hidx'] at hSp
    -- retarget onto the motive's pi and compute the instantiation
    have hlen : (idxs.map fun e => (e.liftN 1 j).liftN
        ((ctorFieldsR U np c).length - j + p)).length =
      (VExpr.liftTelN ((ctorFieldsR U np c).length + p + 1) (idxTel U np ty) 0).length := by
      simp only [List.length_map, VExpr.liftTelN_length, hidx', idxTel_length]
      exact hni
    have hRe := hSp.retarget hlen (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((ctorFieldsR U np c).length + p + 1 + (idxTel U np ty).length) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
    rw [show VExpr.instRev (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + p + 1 +
          (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.sort (.param 0)))
        (idxs.map fun e => (e.liftN 1 j).liftN ((ctorFieldsR U np c).length - j + p)) =
      .forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + p + 1) np ++
          idxs.map fun e => (e.liftN 1 j).liftN ((ctorFieldsR U np c).length - j + p)))
        (.sort (.param 0)) from by
      rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
        VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
        List.map_append,
        VExpr.map_instRev_bvarRevRange_ge _ _ _ (by
          simp only [List.length_map]
          rw [hidx', List.length_map, hni, ← idxTel_length (U := U) (ty := ty)]
          omega),
        show (ctorFieldsR U np c).length + p + 1 + (idxTel U np ty).length -
            (idxs.map fun e => (e.liftN 1 j).liftN
              ((ctorFieldsR U np c).length - j + p)).length =
          (ctorFieldsR U np c).length + p + 1 from by
          simp only [List.length_map]
          rw [hidx', List.length_map, hni, ← idxTel_length (U := U) (ty := ty)]
          omega,
        VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length =
          (idxs.map fun e => (e.liftN 1 j).liftN
            ((ctorFieldsR U np c).length - j + p)).length from by
          simp only [List.length_map]
          rw [hidx', List.length_map, hni, ← idxTel_length (U := U) (ty := ty)]),
        VExpr.map_instRev_bvarRevRange]] at hRe
    -- the motive applied to the index arguments
    have hApp := hRe.hasType_appN (f := .bvar ((ctorFieldsR U np c).length + p)) (.bvar hmlu)
    -- the recursive-field variable
    have hF := getElem?_stack_mid Δ
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (motiveType U T np ty :: (paramsTel U np ty).reverse)
      (i := (ctorFieldsR U np c).length - 1 - j + p)
      (by rw [hΔ]; omega)
      (by simp only [hΔ, List.length_reverse, VExpr.liftTelN_length]; omega)
    rw [show (ctorFieldsR U np c).length - 1 - j + p - Δ.length =
        (ctorFieldsR U np c).length - 1 - j from by rw [hΔ]; omega,
      List.getElem?_reverse (by simp only [VExpr.liftTelN_length]; omega),
      VExpr.liftTelN_length,
      show (ctorFieldsR U np c).length - 1 -
        ((ctorFieldsR U np c).length - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?, ctorFieldsR_getElem?, hBj] at hF
    simp only [Option.map_some] at hF
    have hflu := Lookup.of_getElem? hF
    rw [show (((B.instL (VLevel.params' U 1)).liftN 1 (0+j)).liftN
        ((ctorFieldsR U np c).length - 1 - j + p + 1)) =
      VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + p + 1) np ++
          idxs.map fun e => (e.liftN 1 j).liftN
            ((ctorFieldsR U np c).length - j + p)) from by
      conv => lhs; rw [(isRecField_eq hrec).1]
      rw [VExpr.instL_appN, List.map_append, bvarRevRange_instL,
        show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
          .const T (VLevel.params' U 1) from by
          simp [VExpr.instL, VLevel.params_map_inst_params'],
        VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
        bvarRevRange_liftN_ge _ _ _ _ (by omega),
        bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
        VExpr.bvarRevRange_congr np (show (ctorFieldsR U np c).length - 1 - j + p + 1 +
          (1 + j) = (ctorFieldsR U np c).length + p + 1 from by omega),
        ← hidx', List.map_map]
      refine congrArg (VExpr.appN _) (congrArg (VExpr.bvarRevRange _ np ++ ·) ?_)
      refine List.map_congr_left fun e _ => ?_
      show (e.liftN 1 (0+j)).liftN ((ctorFieldsR U np c).length - 1 - j + p + 1) = _
      rw [show (0+j) = j from Nat.zero_add j,
        show (ctorFieldsR U np c).length - 1 - j + p + 1 =
          (ctorFieldsR U np c).length - j + p from by omega]] at hflu
    have happ2 : env.HasType (U+1)
        (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse))
        (VExpr.appN (.bvar ((ctorFieldsR U np c).length + p))
          ((idxs.map fun e => (e.liftN 1 j).liftN
            ((ctorFieldsR U np c).length - j + p)) ++
            [.bvar ((ctorFieldsR U np c).length - 1 - j + p)]))
        ((VExpr.sort (.param 0)).inst
          (.bvar ((ctorFieldsR U np c).length - 1 - j + p))) := by
      rw [VExpr.appN_append]
      exact HasType.app hApp (.bvar hflu)
    exact ⟨_, happ2⟩
theorem Stage3Env.ctorAppMin_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (Δ : List VExpr) :
    env.HasType (U+1)
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np ++
          VExpr.bvarRevRange Δ.length (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN Δ.length)) := by
  have hml : (ctorFieldsR U np c).length =
      (ctorFields (VExpr.dropN np c.type)).length := ctorFieldsR_length
  have hml2 : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
      (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
  have hcl : (c.type.instL (VLevel.params' U 1)).ClosedN 0 :=
    (Ordered.closedC (ci := ⟨U, c.type⟩) S.ord (S.hcs c hc)).instL
  -- step A: consume the parameter telescope
  have hfA : env.HasType (U+1)
      ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        [motiveType U T np ty]) ++ (paramsTel U np ty).reverse ++ [])
      (.const c.name (VLevel.params' U 1))
      ((VExpr.forallN (paramsTel U np ty)
        (VExpr.forallN (ctorFieldsR U np c)
          (VExpr.appN (.const T (VLevel.params' U 1))
            (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
              ctorIdxs U np c)))).liftN
        ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np ty]).length + (paramsTel U np ty).length)) := by
    rw [← S.ctorType_instL hc, hcl.liftN_eq (Nat.zero_le _)]
    exact S.cConst hc
  have hA := HasType.appN_selfSpine (env := env) (U := U+1) hfA
  -- step B: consume the field telescope
  rw [VExpr.liftN_forallN] at hA
  have hBeq : VExpr.forallN
      (VExpr.liftTelN ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np ty]).length) (ctorFieldsR U np c) 0)
      ((VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
          ctorIdxs U np c)).liftN
        ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np ty]).length) (0 + (ctorFieldsR U np c).length)) =
      (VExpr.forallN (VExpr.liftTelN 1 (ctorFieldsR U np c) 0)
        ((VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
            ctorIdxs U np c)).liftN 1 (0 + (ctorFieldsR U np c).length))).liftN
        (Δ.length + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length) := by
    conv => rhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
      show (0:Nat) + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
        0 + (ctorFieldsR U np c).length from by rw [hml2],
      VExpr.liftN'_liftN_hi]
    rw [liftTelN_congr _ _ (show (1:Nat) + (Δ.length +
        (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length) =
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        [motiveType U T np ty]).length from by
      simp only [List.length_append, List.length_reverse, VExpr.liftTelN_length,
        List.length_singleton]
      omega),
      show (1 + (Δ.length + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length)) =
        (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np ty]).length from by
        simp only [List.length_append, List.length_reverse, VExpr.liftTelN_length,
          List.length_singleton]
        omega]
  rw [hBeq] at hA
  have hB := HasType.appN_selfSpine (env := env) (U := U+1)
    (Δ := Δ) (Γ := motiveType U T np ty :: (paramsTel U np ty).reverse)
    (As := VExpr.liftTelN 1 (ctorFieldsR U np c) 0)
    (B := (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
        ctorIdxs U np c)).liftN 1 (0 + (ctorFieldsR U np c).length))
    (by simpa [List.append_assoc, List.append_nil] using hA)
  rw [show (paramsTel U np ty).length = np from by
      simp [paramsTel, List.length_map, S.hlen],
    VExpr.bvarRevRange_congr np (show Δ.length +
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length + 1) =
      Δ.length + (ctorFieldsR U np c).length + 1 from by omega),
    VExpr.liftTelN_length] at hB
  rw [show ((VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
        ctorIdxs U np c)).liftN 1 (0 + (ctorFieldsR U np c).length)).liftN Δ.length =
    VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np ++
        (ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN Δ.length) from by
    rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
      Nat.zero_add ((ctorFieldsR U np c).length),
      bvarRevRange_liftN_ge _ _ _ _ (by omega),
      bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
      VExpr.bvarRevRange_congr np (show Δ.length +
        (1 + (0 + (ctorFields (VExpr.dropN np c.type)).length)) =
        Δ.length + (ctorFieldsR U np c).length + 1 from by omega),
      List.map_map]
    rfl] at hB
  rw [show VExpr.appN (.const c.name (VLevel.params' U 1))
      (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np ++
        VExpr.bvarRevRange Δ.length (ctorFieldsR U np c).length) =
    (VExpr.appN (.const c.name (VLevel.params' U 1))
      (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np)).appN
      (VExpr.bvarRevRange Δ.length (ctorFieldsR U np c).length) from
    VExpr.appN_append ..]
  exact hB

/-- The minor premise for a constructor is a type over
`params ++ [motive]`. -/
theorem Stage3Env.minor_isType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.IsType (U+1) (motiveType U T np ty :: (paramsTel U np ty).reverse)
      (minorType U T np ty c) := by
  simp only [minorType]
  refine IsType.forallN ?_ ?_
  · have h0 := S.fieldsWF_onTel _ [] 0 rfl (by simpa using S.hfields c hc)
    have h1 := h0.weakN S.ord (.zero [motiveType U T np ty])
    simpa [ctorFieldsR, List.map_reverse, paramsTel] using h1
  · refine IsType.forallN (S.ihs_onTel hc _ (fun q hq => hq) [] 0 rfl) ?_
    have hml2 : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
        (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
    have hrlen : ((ihsFrom (ctorFieldsR U np c).length
        (recPairsR U T np (idxTel U np ty).length c) 0).reverse).length =
        (recPairsR U T np (idxTel U np ty).length c).length := by
      simp [ihsFrom_length]
    -- the motive variable
    have hM := getElem?_rstack3 ((ihsFrom (ctorFieldsR U np c).length
        (recPairsR U T np (idxTel U np ty).length c) 0).reverse)
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (motiveType U T np ty) (paramsTel U np ty).reverse
      (i := (ctorFieldsR U np c).length +
        (recPairsR U T np (idxTel U np ty).length c).length)
      (by simp only [List.length_reverse, ihsFrom_length, VExpr.liftTelN_length]; omega)
    have hmlu := Lookup.of_getElem? hM
    rw [motiveType_liftN] at hmlu
    -- the transported result spine
    have hSp := S.result_transport hc [motiveType U T np ty] (g := 1) rfl
      ((ihsFrom (ctorFieldsR U np c).length
        (recPairsR U T np (idxTel U np ty).length c) 0).reverse)
      (d := (recPairsR U T np (idxTel U np ty).length c).length) hrlen
    rw [liftTelN_congr _ _ (show (ctorFieldsR U np c).length + 1 +
        (recPairsR U T np (idxTel U np ty).length c).length =
      (ctorFieldsR U np c).length +
        (recPairsR U T np (idxTel U np ty).length c).length + 1 from by omega)] at hSp
    have hlen : ((ctorIdxs U np c).map fun e =>
        (e.liftN 1 (ctorFieldsR U np c).length).liftN
          (recPairsR U T np (idxTel U np ty).length c).length).length =
      (VExpr.liftTelN ((ctorFieldsR U np c).length +
        (recPairsR U T np (idxTel U np ty).length c).length + 1)
        (idxTel U np ty) 0).length := by
      simp only [List.length_map, VExpr.liftTelN_length, ctorIdxs_length, idxTel_length]
      have hc3 := stage3Ctor_eq (S.hs3 c hc)
      exact hc3.2.1
    have hRe := hSp.retarget hlen (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
        (recPairsR U T np (idxTel U np ty).length c).length + 1 +
          (idxTel U np ty).length) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
    rw [show VExpr.instRev (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
          (recPairsR U T np (idxTel U np ty).length c).length + 1 +
            (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.sort (.param 0)))
        ((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN
            (recPairsR U T np (idxTel U np ty).length c).length) =
      .forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
          (recPairsR U T np (idxTel U np ty).length c).length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recPairsR U T np (idxTel U np ty).length c).length))
        (.sort (.param 0)) from by
      rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
        VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
        List.map_append,
        VExpr.map_instRev_bvarRevRange_ge _ _ _ (by
          rw [hlen, VExpr.liftTelN_length]; omega),
        show (ctorFieldsR U np c).length +
            (recPairsR U T np (idxTel U np ty).length c).length + 1 +
            (idxTel U np ty).length -
            ((ctorIdxs U np c).map fun e =>
              (e.liftN 1 (ctorFieldsR U np c).length).liftN
                (recPairsR U T np (idxTel U np ty).length c).length).length =
          (ctorFieldsR U np c).length +
            (recPairsR U T np (idxTel U np ty).length c).length + 1 from by
          rw [hlen, VExpr.liftTelN_length]
          omega,
        VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length =
          ((ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recPairsR U T np (idxTel U np ty).length c).length).length from by
          rw [hlen, VExpr.liftTelN_length]),
        VExpr.map_instRev_bvarRevRange]] at hRe
    -- the motive applied to the result indices
    have hApp := hRe.hasType_appN (f := .bvar ((ctorFieldsR U np c).length +
      (recPairsR U T np (idxTel U np ty).length c).length)) (.bvar hmlu)
    -- the constructor application
    have hctor := S.ctorAppMin_hasType hc
      ((ihsFrom (ctorFieldsR U np c).length
        (recPairsR U T np (idxTel U np ty).length c) 0).reverse)
    rw [hrlen] at hctor
    rw [VExpr.bvarRevRange_congr np (show
        (recPairsR U T np (idxTel U np ty).length c).length +
          (ctorFieldsR U np c).length + 1 =
        (ctorFieldsR U np c).length +
          (recPairsR U T np (idxTel U np ty).length c).length + 1 from by omega)] at hctor
    have happ2 : env.HasType (U+1)
        ((ihsFrom (ctorFieldsR U np c).length
          (recPairsR U T np (idxTel U np ty).length c) 0).reverse ++
          ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse)))
        (VExpr.appN (.bvar ((ctorFieldsR U np c).length +
          (recPairsR U T np (idxTel U np ty).length c).length))
          (((ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recPairsR U T np (idxTel U np ty).length c).length) ++
            [VExpr.appN (.const c.name (VLevel.params' U 1))
              (VExpr.bvarRevRange ((recPairsR U T np (idxTel U np ty).length c).length +
                (ctorFieldsR U np c).length + 1) np ++
                VExpr.bvarRevRange (recPairsR U T np (idxTel U np ty).length c).length
                  (ctorFieldsR U np c).length)]))
        ((VExpr.sort (.param 0)).inst
          (VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((recPairsR U T np (idxTel U np ty).length c).length +
              (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange (recPairsR U T np (idxTel U np ty).length c).length
                (ctorFieldsR U np c).length))) := by
      rw [VExpr.appN_append,
        VExpr.bvarRevRange_congr np (show
          (recPairsR U T np (idxTel U np ty).length c).length +
            (ctorFieldsR U np c).length + 1 =
          (ctorFieldsR U np c).length +
            (recPairsR U T np (idxTel U np ty).length c).length + 1 from by omega)]
      exact HasType.app hApp (by simpa [List.append_assoc] using hctor)
    exact ⟨_, by simpa [List.append_assoc] using happ2⟩

/-- The generalized minor premise is a type over `params ++ [motive]`.
This is the preservation theorem used by `minorTypeRec`; it differs from
`minor_isType` only in the functional-IH telescope supplied for recursive
Pi arguments. -/
theorem Stage3Env.minor_isTypeRec {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.IsType (U+1) (motiveType U T np ty :: (paramsTel U np ty).reverse)
      (minorTypeRec U T np ty c) := by
  simp only [minorTypeRec]
  refine IsType.forallN ?_ ?_
  · have h0 := S.fieldsWF_onTel _ [] 0 rfl (by simpa using S.hfields c hc)
    have h1 := h0.weakN S.ord (.zero [motiveType U T np ty])
    simpa [ctorFieldsR, List.map_reverse, paramsTel] using h1
  · refine IsType.forallN (S.ihsRec_onTel hc _ (fun q hq => hq) [] 0 rfl) ?_
    have hml2 : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
        (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
    have hrlen : ((ihsFromRecArgs (ctorFieldsR U np c).length
        (recArgsR U T np (idxTel U np ty).length c) 0).reverse).length =
        (recArgsR U T np (idxTel U np ty).length c).length := by
      simp [ihsFromRecArgs_length]
    -- the motive variable
    have hM := getElem?_rstack3 ((ihsFromRecArgs (ctorFieldsR U np c).length
        (recArgsR U T np (idxTel U np ty).length c) 0).reverse)
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (motiveType U T np ty) (paramsTel U np ty).reverse
      (i := (ctorFieldsR U np c).length +
        (recArgsR U T np (idxTel U np ty).length c).length)
      (by simp only [List.length_reverse, ihsFromRecArgs_length,
        VExpr.liftTelN_length]; omega)
    have hmlu := Lookup.of_getElem? hM
    rw [motiveType_liftN] at hmlu
    -- the transported result spine
    have hSp := S.result_transport hc [motiveType U T np ty] (g := 1) rfl
      ((ihsFromRecArgs (ctorFieldsR U np c).length
        (recArgsR U T np (idxTel U np ty).length c) 0).reverse)
      (d := (recArgsR U T np (idxTel U np ty).length c).length) hrlen
    rw [liftTelN_congr _ _ (show (ctorFieldsR U np c).length + 1 +
        (recArgsR U T np (idxTel U np ty).length c).length =
      (ctorFieldsR U np c).length +
        (recArgsR U T np (idxTel U np ty).length c).length + 1 from by omega)] at hSp
    have hlen : ((ctorIdxs U np c).map fun e =>
        (e.liftN 1 (ctorFieldsR U np c).length).liftN
          (recArgsR U T np (idxTel U np ty).length c).length).length =
      (VExpr.liftTelN ((ctorFieldsR U np c).length +
        (recArgsR U T np (idxTel U np ty).length c).length + 1)
        (idxTel U np ty) 0).length := by
      simp only [List.length_map, VExpr.liftTelN_length, ctorIdxs_length, idxTel_length]
      have hc3 := stage3Ctor_eq (S.hs3 c hc)
      exact hc3.2.1
    have hRe := hSp.retarget hlen (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
        (recArgsR U T np (idxTel U np ty).length c).length + 1 +
          (idxTel U np ty).length) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
    rw [show VExpr.instRev (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
          (recArgsR U T np (idxTel U np ty).length c).length + 1 +
            (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.sort (.param 0)))
        ((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN
            (recArgsR U T np (idxTel U np ty).length c).length) =
      .forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
          (recArgsR U T np (idxTel U np ty).length c).length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recArgsR U T np (idxTel U np ty).length c).length))
        (.sort (.param 0)) from by
      rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
        VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
        List.map_append,
        VExpr.map_instRev_bvarRevRange_ge _ _ _ (by
          rw [hlen, VExpr.liftTelN_length]; omega),
        show (ctorFieldsR U np c).length +
            (recArgsR U T np (idxTel U np ty).length c).length + 1 +
            (idxTel U np ty).length -
            ((ctorIdxs U np c).map fun e =>
              (e.liftN 1 (ctorFieldsR U np c).length).liftN
                (recArgsR U T np (idxTel U np ty).length c).length).length =
          (ctorFieldsR U np c).length +
            (recArgsR U T np (idxTel U np ty).length c).length + 1 from by
          rw [hlen, VExpr.liftTelN_length]
          omega,
        VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length =
          ((ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recArgsR U T np (idxTel U np ty).length c).length).length from by
          rw [hlen, VExpr.liftTelN_length]),
        VExpr.map_instRev_bvarRevRange]] at hRe
    -- the motive applied to the result indices
    have hApp := hRe.hasType_appN (f := .bvar ((ctorFieldsR U np c).length +
      (recArgsR U T np (idxTel U np ty).length c).length)) (.bvar hmlu)
    -- the constructor application
    have hctor := S.ctorAppMin_hasType hc
      ((ihsFromRecArgs (ctorFieldsR U np c).length
        (recArgsR U T np (idxTel U np ty).length c) 0).reverse)
    rw [hrlen] at hctor
    rw [VExpr.bvarRevRange_congr np (show
        (recArgsR U T np (idxTel U np ty).length c).length +
          (ctorFieldsR U np c).length + 1 =
        (ctorFieldsR U np c).length +
          (recArgsR U T np (idxTel U np ty).length c).length + 1 from by omega)] at hctor
    have happ2 : env.HasType (U+1)
        ((ihsFromRecArgs (ctorFieldsR U np c).length
          (recArgsR U T np (idxTel U np ty).length c) 0).reverse ++
          ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse)))
        (VExpr.appN (.bvar ((ctorFieldsR U np c).length +
          (recArgsR U T np (idxTel U np ty).length c).length))
          (((ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recArgsR U T np (idxTel U np ty).length c).length) ++
            [VExpr.appN (.const c.name (VLevel.params' U 1))
              (VExpr.bvarRevRange ((recArgsR U T np (idxTel U np ty).length c).length +
                (ctorFieldsR U np c).length + 1) np ++
                VExpr.bvarRevRange (recArgsR U T np (idxTel U np ty).length c).length
                  (ctorFieldsR U np c).length)]))
        ((VExpr.sort (.param 0)).inst
          (VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((recArgsR U T np (idxTel U np ty).length c).length +
              (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange (recArgsR U T np (idxTel U np ty).length c).length
                (ctorFieldsR U np c).length))) := by
      rw [VExpr.appN_append,
        VExpr.bvarRevRange_congr np (show
          (recArgsR U T np (idxTel U np ty).length c).length +
            (ctorFieldsR U np c).length + 1 =
          (ctorFieldsR U np c).length +
            (recArgsR U T np (idxTel U np ty).length c).length + 1 from by omega)]
      exact HasType.app hApp (by simpa [List.append_assoc] using hctor)
    exact ⟨_, by simpa [List.append_assoc] using happ2⟩

/-- The minor premises, in position, are a telescope over
`params ++ [motive]`. -/
theorem Stage3Env.minorTypes_onTel :
    ∀ (cs' : List VConstVal), (∀ c ∈ cs', c ∈ ty.ctors) →
    ∀ (Δ : List VExpr) (i : Nat), Δ.length = i →
    OnTel env (U+1) (Δ ++ (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (minorTypes U T np ty cs' i)
  | [], _, _, _, _ => trivial
  | c :: cs', hsub, Δ, i, hΔ =>
    ⟨by
      rw [← hΔ]
      exact (S.minor_isType (hsub c (.head _))).weakN S.ord (.zero Δ),
    Stage3Env.minorTypes_onTel cs' (fun c h => hsub c (.tail _ h)) (_ :: Δ) (i+1)
      (by simp [hΔ])⟩

/-- Generalized minor premises, including functional recursive hypotheses,
form a telescope over `params ++ [motive]`. -/
theorem Stage3Env.minorTypesRec_onTel :
    ∀ (cs' : List VConstVal), (∀ c ∈ cs', c ∈ ty.ctors) →
    ∀ (Δ : List VExpr) (i : Nat), Δ.length = i →
    OnTel env (U+1) (Δ ++ (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (minorTypesRec U T np ty cs' i)
  | [], _, _, _, _ => trivial
  | c :: cs', hsub, Δ, i, hΔ =>
    ⟨by
      rw [← hΔ]
      exact (S.minor_isTypeRec (hsub c (.head _))).weakN S.ord (.zero Δ),
    Stage3Env.minorTypesRec_onTel cs' (fun c h => hsub c (.tail _ h)) (_ :: Δ) (i+1)
      (by simp [hΔ])⟩

/-- The generated recursor type is well-formed. -/
theorem Stage3Env.recType_isType : env.IsType (U+1) [] (recType U T np ty) := by
  have hP : OnTel env (U+1) [] (paramsTel U np ty) := by
    have := S.hparams.of_append.1.instL (U' := U+1) VLevel.params'_one_wf
    simpa [paramsTel] using this
  refine IsType.forallN hP ?_
  simp only [List.append_nil]
  refine IsType.forallE S.motive_isType ?_
  refine IsType.forallN
    (by simpa using S.minorTypes_onTel ty.ctors (fun _ h => h) [] 0 rfl) ?_
  have hI : OnTel env (U+1)
      ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0) := by
    have h := S.idxTel_onTel.weakN S.ord
      (Ctx.LiftN.zero (n := ty.ctors.length + 1)
        (Γ := (paramsTel U np ty).reverse)
        ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
        (h := by simp [minorTypes_length]))
    simpa [List.append_assoc] using h
  refine IsType.forallN hI ?_
  have hmaj : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (l.inst (VLevel.params' U 1))) := by
    have W := Ctx.LiftN.consTel (n := ty.ctors.length + 1) (idxTel U np ty)
      (Ctx.LiftN.zero (n := ty.ctors.length + 1)
        (Γ := (paramsTel U np ty).reverse)
        ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
        (h := by simp [minorTypes_length]))
    have h := S.motiveTApp_hasType.weakN S.ord W
    simp only [Nat.add_zero, VExpr.liftN_appN, VExpr.liftN, List.map_append] at h
    rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
      VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
      VExpr.bvarRevRange_congr np (show
        ty.ctors.length + 1 + (idxTel U np ty).length =
          (idxTel U np ty).length + ty.ctors.length + 1 from by omega)] at h
    simpa [List.append_assoc] using h
  refine IsType.forallE ⟨_, hmaj⟩ ?_
  have hM := getElem?_rstack3
    [VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length)]
    ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
      (minorTypes U T np ty ty.ctors).reverse)
    (motiveType U T np ty) (paramsTel U np ty).reverse
    (i := (idxTel U np ty).length + ty.ctors.length + 1)
    (by simp only [List.length_singleton, List.length_append, List.length_reverse,
      VExpr.liftTelN_length, minorTypes_length]; omega)
  have hmlu := Lookup.of_getElem? (by
    simpa only [List.singleton_append, List.append_assoc] using hM)
  rw [show (motiveType U T np ty).liftN
        ((idxTel U np ty).length + ty.ctors.length + 1 + 1) =
      ((motiveType U T np ty).liftN (ty.ctors.length + 1)).liftN
        ((idxTel U np ty).length + 1) from by
      rw [VExpr.liftN_liftN]
      congr 1
      omega,
    motiveType_liftN] at hmlu
  have hfun : env.HasType (U+1)
      (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length) ::
        ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
          ((minorTypes U T np ty ty.ctors).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse))))
      (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
      ((VExpr.forallN
        (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
        (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange (ty.ctors.length + 1 + (idxTel U np ty).length) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length))
          (.sort (.param 0)))).liftN
        (1 + (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).length)) := by
    exact .bvar (by
      simpa [List.append_assoc, VExpr.liftTelN_length, Nat.add_comm] using hmlu)
  have hMapp := HasType.appN_selfSpine
    (As := VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
    (Δ := [VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length)])
    (Γ := (minorTypes U T np ty ty.ctors).reverse ++
      (motiveType U T np ty :: (paramsTel U np ty).reverse))
    (f := .bvar ((idxTel U np ty).length + ty.ctors.length + 1))
    hfun
  have h0 :
      (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length) ::
        ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
          ((minorTypes U T np ty ty.ctors).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse))))[0]? =
        some (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)) := rfl
  have harg := HasType.bvar (env := env) (U := U+1) (Lookup.of_getElem? h0)
  have harg' : env.HasType (U+1)
      ([VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)] ++
        (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (.bvar 0)
      ((VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (ty.ctors.length + 1 + (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length)).liftN
        [VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)].length) := by
    simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using harg
  have happ := HasType.app hMapp harg'
  exact ⟨_, by
    simpa [List.append_assoc, VExpr.liftTelN_length] using happ⟩

/-- The generalized recursor type, whose constructor minors include
functional IHs for recursive Pi arguments, is well-formed. -/
theorem Stage3Env.recTypeRec_isType : env.IsType (U+1) [] (recTypeRec U T np ty) := by
  have hP : OnTel env (U+1) [] (paramsTel U np ty) := by
    have := S.hparams.of_append.1.instL (U' := U+1) VLevel.params'_one_wf
    simpa [paramsTel] using this
  refine IsType.forallN hP ?_
  simp only [List.append_nil]
  refine IsType.forallE S.motive_isType ?_
  refine IsType.forallN
    (by simpa using S.minorTypesRec_onTel ty.ctors (fun _ h => h) [] 0 rfl) ?_
  have hI : OnTel env (U+1)
      ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0) := by
    have h := S.idxTel_onTel.weakN S.ord
      (Ctx.LiftN.zero (n := ty.ctors.length + 1)
        (Γ := (paramsTel U np ty).reverse)
        ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
        (h := by simp [minorTypesRec_length]))
    simpa [List.append_assoc] using h
  refine IsType.forallN hI ?_
  have hmaj : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (l.inst (VLevel.params' U 1))) := by
    have W := Ctx.LiftN.consTel (n := ty.ctors.length + 1) (idxTel U np ty)
      (Ctx.LiftN.zero (n := ty.ctors.length + 1)
        (Γ := (paramsTel U np ty).reverse)
        ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
        (h := by simp [minorTypesRec_length]))
    have h := S.motiveTApp_hasType.weakN S.ord W
    simp only [Nat.add_zero, VExpr.liftN_appN, VExpr.liftN, List.map_append] at h
    rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
      VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
      VExpr.bvarRevRange_congr np (show
        ty.ctors.length + 1 + (idxTel U np ty).length =
          (idxTel U np ty).length + ty.ctors.length + 1 from by omega)] at h
    simpa [List.append_assoc] using h
  refine IsType.forallE ⟨_, hmaj⟩ ?_
  have hM := getElem?_rstack3
    [VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length)]
    ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
      (minorTypesRec U T np ty ty.ctors).reverse)
    (motiveType U T np ty) (paramsTel U np ty).reverse
    (i := (idxTel U np ty).length + ty.ctors.length + 1)
    (by simp only [List.length_singleton, List.length_append, List.length_reverse,
      VExpr.liftTelN_length, minorTypesRec_length]; omega)
  have hmlu := Lookup.of_getElem? (by
    simpa only [List.singleton_append, List.append_assoc] using hM)
  rw [show (motiveType U T np ty).liftN
        ((idxTel U np ty).length + ty.ctors.length + 1 + 1) =
      ((motiveType U T np ty).liftN (ty.ctors.length + 1)).liftN
        ((idxTel U np ty).length + 1) from by
      rw [VExpr.liftN_liftN]
      congr 1
      omega,
    motiveType_liftN] at hmlu
  have hfun : env.HasType (U+1)
      (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length) ::
        ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
          ((minorTypesRec U T np ty ty.ctors).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse))))
      (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
      ((VExpr.forallN
        (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
        (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange (ty.ctors.length + 1 + (idxTel U np ty).length) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length))
          (.sort (.param 0)))).liftN
        (1 + (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).length)) := by
    exact .bvar (by
      simpa [List.append_assoc, VExpr.liftTelN_length, Nat.add_comm] using hmlu)
  have hMapp := HasType.appN_selfSpine
    (As := VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
    (Δ := [VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length)])
    (Γ := (minorTypesRec U T np ty ty.ctors).reverse ++
      (motiveType U T np ty :: (paramsTel U np ty).reverse))
    (f := .bvar ((idxTel U np ty).length + ty.ctors.length + 1))
    hfun
  have h0 :
      (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length) ::
        ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
          ((minorTypesRec U T np ty ty.ctors).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse))))[0]? =
        some (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)) := rfl
  have harg := HasType.bvar (env := env) (U := U+1) (Lookup.of_getElem? h0)
  have harg' : env.HasType (U+1)
      ([VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)] ++
        (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (.bvar 0)
      ((VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (ty.ctors.length + 1 + (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length)).liftN
        [VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)].length) := by
    simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using harg
  have happ := HasType.app hMapp harg'
  exact ⟨_, by
    simpa [List.append_assoc, VExpr.liftTelN_length] using happ⟩

theorem Stage3Env.recConstRec_wf : (recConstRec U T np ty).WF env :=
  S.recTypeRec_isType

theorem Stage3Env.recConst_wf : (recConst U T np ty).WF env :=
  S.recType_isType

/-! ## The iota rules -/

/-- The recursor type is closed, by well-formedness. -/
theorem Stage3Env.recType_closedN : (recType U T np ty).ClosedN 0 := by
  obtain ⟨u, h⟩ := S.recType_isType
  exact VExpr.WF.closedN S.ord ⟨_, h⟩ trivial

theorem Stage3Env.recTypeRec_closedN : (recTypeRec U T np ty).ClosedN 0 := by
  obtain ⟨u, h⟩ := S.recTypeRec_isType
  exact VExpr.WF.closedN S.ord ⟨_, h⟩ trivial

/-- The recursor constant at its own (identity) universe list. -/
theorem Stage3Env.recConst_hasType
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) {Γ} :
    env.HasType (U+1) Γ (.const (.str T "rec") (VLevel.params (U+1)))
      (recType U T np ty) := by
  have := HasType.const (Γ := Γ) hrec VLevel.params_wf VLevel.params_length
  rw [show (recConst U T np ty).uvars = U + 1 from rfl,
    show (recConst U T np ty).type = recType U T np ty from rfl] at this
  rwa [recType_levelWF.instL_id] at this

theorem Stage3Env.recConstRec_hasType
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty)) {Γ} :
    env.HasType (U+1) Γ (.const (.str T "rec") (VLevel.params (U+1)))
      (recTypeRec U T np ty) := by
  have := HasType.const (Γ := Γ) hrec VLevel.params_wf VLevel.params_length
  rw [show (recConstRec U T np ty).uvars = U + 1 from rfl,
    show (recConstRec U T np ty).type = recTypeRec U T np ty from rfl] at this
  rwa [recTypeRec_levelWF.instL_id] at this

/-- The recursor applied to its parameter, motive, and minor-premise
spine.  The remaining type is the (lifted) index telescope followed by
the major premise. -/
theorem Stage3Env.recBase_hasType
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty))
    (Δ : List VExpr) :
    env.HasType (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange Δ.length (np + ty.ctors.length + 1)))
      ((VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
        (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length))
          (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
            (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)))).liftN Δ.length) := by
  have hf : env.HasType (U+1)
      (Δ ++ (paramsTel U np ty ++
        motiveType U T np ty :: minorTypes U T np ty ty.ctors).reverse ++ [])
      (.const (.str T "rec") (VLevel.params (U+1)))
      ((VExpr.forallN (paramsTel U np ty ++
        motiveType U T np ty :: minorTypes U T np ty ty.ctors)
        (VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
          (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
            (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (idxTel U np ty).length))
            (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
              (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0))))).liftN
        (Δ.length + (paramsTel U np ty ++
          motiveType U T np ty :: minorTypes U T np ty ty.ctors).length)) := by
    rw [show VExpr.forallN (paramsTel U np ty ++
        motiveType U T np ty :: minorTypes U T np ty ty.ctors)
        (VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
          (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
            (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (idxTel U np ty).length))
            (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
              (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)))) =
        recType U T np ty from by rw [VExpr.forallN_append]; rfl,
      S.recType_closedN.liftN_eq (Nat.zero_le _)]
    exact S.recConst_hasType hrec
  have hspine := HasType.appN_selfSpine (env := env) (U := U+1) hf
  simp only [List.reverse_append, List.reverse_cons, List.append_nil, List.append_assoc,
    List.singleton_append, List.length_append, List.length_cons, minorTypes_length] at hspine
  rw [show (paramsTel U np ty).length = np from by
      simp [paramsTel, List.length_map, S.hlen],
    VExpr.bvarRevRange_congr' Δ.length (show
      np + (ty.ctors.length + 1) = np + ty.ctors.length + 1 from by omega)] at hspine
  simpa [List.append_assoc] using hspine

theorem Stage3Env.recBaseRec_hasType
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty))
    (Δ : List VExpr) :
    env.HasType (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange Δ.length (np + ty.ctors.length + 1)))
      ((VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
        (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length))
          (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
            (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)))).liftN Δ.length) := by
  have hf : env.HasType (U+1)
      (Δ ++ (paramsTel U np ty ++
        motiveType U T np ty :: minorTypesRec U T np ty ty.ctors).reverse ++ [])
      (.const (.str T "rec") (VLevel.params (U+1)))
      ((VExpr.forallN (paramsTel U np ty ++
        motiveType U T np ty :: minorTypesRec U T np ty ty.ctors)
        (VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
          (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
            (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (idxTel U np ty).length))
            (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
              (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0))))).liftN
        (Δ.length + (paramsTel U np ty ++
          motiveType U T np ty :: minorTypesRec U T np ty ty.ctors).length)) := by
    rw [show VExpr.forallN (paramsTel U np ty ++
        motiveType U T np ty :: minorTypesRec U T np ty ty.ctors)
        (VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
          (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
            (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (idxTel U np ty).length))
            (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
              (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)))) =
        recTypeRec U T np ty from by rw [VExpr.forallN_append]; rfl,
      S.recTypeRec_closedN.liftN_eq (Nat.zero_le _)]
    exact S.recConstRec_hasType hrec
  have hspine := HasType.appN_selfSpine (env := env) (U := U+1) hf
  simp only [List.reverse_append, List.reverse_cons, List.append_nil, List.append_assoc,
    List.singleton_append, List.length_append, List.length_cons, minorTypesRec_length] at hspine
  rw [show (paramsTel U np ty).length = np from by
      simp [paramsTel, List.length_map, S.hlen],
    VExpr.bvarRevRange_congr' Δ.length (show
      np + (ty.ctors.length + 1) = np + ty.ctors.length + 1 from by omega)] at hspine
  simpa [List.append_assoc] using hspine

/-- Apply the generated recursor to an index spine and its major premise.
This is shared by constructor-headed rule left sides and by the recursive
calls appearing in minor-premise right sides. -/
theorem Stage3Env.recApp_hasType
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty))
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN
        (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))))
    (hlen : idxs.length = (idxTel U np ty).length)
    (ha : env.HasType (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))) a
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + ty.ctors.length + 1) np ++ idxs))) :
    env.HasType (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange Δ.length (np + ty.ctors.length + 1)))
        (idxs ++ [a]))
      (VExpr.appN (.bvar (Δ.length + ty.ctors.length)) (idxs ++ [a])) := by
  have hb := S.recBase_hasType hrec Δ
  rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
    liftTelN_congr _ _ (show ty.ctors.length + 1 + Δ.length =
      Δ.length + ty.ctors.length + 1 from by omega)] at hb
  have hcod :
      (VExpr.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0))).liftN Δ.length
          (0 + (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).length) =
      VExpr.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.app (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)) := by
    rw [VExpr.liftTelN_length, Nat.zero_add]
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append,
        bvarRevRange_liftN_ge _ _ _ _ (by omega),
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
        VExpr.bvarRevRange_congr np (show Δ.length +
          ((idxTel U np ty).length + ty.ctors.length + 1) =
          (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 from by omega)]
      rfl
    · show VExpr.app _ _ = VExpr.app _ _
      congr 1
      · rw [VExpr.liftN_appN,
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
        show VExpr.appN (.bvar (liftVar Δ.length
          ((idxTel U np ty).length + ty.ctors.length + 1)
          ((idxTel U np ty).length + 1))) _ = _
        rw [liftVar_le (by omega), show Δ.length +
          ((idxTel U np ty).length + ty.ctors.length + 1) =
          (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 from by omega]
  rw [hcod] at hb
  have hshape := hidx.retarget (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 - idxs.length =
      Δ.length + ty.ctors.length + 1 from by rw [hlen]; omega,
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hfull := hshape.snoc ha
  simp only [VExpr.inst] at hfull
  change env.SpineWF (U+1) _
    (VExpr.forallN
      (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
      (VExpr.forallN [VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length)]
        (.sort (.param 0))))
    (idxs ++ [a]) (.sort (.param 0)) at hfull
  rw [← VExpr.forallN_append] at hfull
  have hfullLen : (idxs ++ [a]).length =
      (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0 ++
        [VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
              ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)]).length := by
    simp only [List.length_append, List.length_singleton, VExpr.liftTelN_length, hlen]
  have hactual := hfull.retarget hfullLen
    (VExpr.app
      (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1))
        (VExpr.bvarRevRange 1 (idxTel U np ty).length))
      (.bvar 0))
  rw [VExpr.forallN_append] at hactual
  have happ := hactual.hasType_appN hb
  rw [show VExpr.app
      (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1))
        (VExpr.bvarRevRange 1 (idxTel U np ty).length))
      (.bvar 0) =
      VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
        ty.ctors.length + 1)) (VExpr.bvarRevRange 0 ((idxTel U np ty).length + 1)) from by
        rw [VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length + 1 =
          1 + (idxTel U np ty).length from by omega),
          ← VExpr.bvarRevRange_append (idxTel U np ty).length 1]
        simpa [VExpr.bvarRevRange, VExpr.appN] using (VExpr.appN_append
          (.bvar ((idxTel U np ty).length + Δ.length + ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length) [VExpr.bvar 0]).symm,
    VExpr.instRev_appN,
    VExpr.instRev_bvar_ge _ (by
      simp only [List.length_append, List.length_singleton]
      rw [hlen]
      omega),
    VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length + 1 =
      (idxs ++ [a]).length from by simp [hlen]),
    VExpr.map_instRev_bvarRevRange] at happ
  rw [show (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 -
      (idxs ++ [a]).length = Δ.length + ty.ctors.length from by
    simp only [List.length_append, List.length_singleton]
    rw [hlen]
    omega] at happ
  simpa [List.length_append, hlen] using happ

theorem Stage3Env.recAppRec_hasType
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty))
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN
        (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))))
    (hlen : idxs.length = (idxTel U np ty).length)
    (ha : env.HasType (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))) a
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + ty.ctors.length + 1) np ++ idxs))) :
    env.HasType (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange Δ.length (np + ty.ctors.length + 1)))
        (idxs ++ [a]))
      (VExpr.appN (.bvar (Δ.length + ty.ctors.length)) (idxs ++ [a])) := by
  have hb := S.recBaseRec_hasType hrec Δ
  rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
    liftTelN_congr _ _ (show ty.ctors.length + 1 + Δ.length =
      Δ.length + ty.ctors.length + 1 from by omega)] at hb
  have hcod :
      (VExpr.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0))).liftN Δ.length
          (0 + (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).length) =
      VExpr.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.app (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)) := by
    rw [VExpr.liftTelN_length, Nat.zero_add]
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append,
        bvarRevRange_liftN_ge _ _ _ _ (by omega),
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
        VExpr.bvarRevRange_congr np (show Δ.length +
          ((idxTel U np ty).length + ty.ctors.length + 1) =
          (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 from by omega)]
      rfl
    · show VExpr.app _ _ = VExpr.app _ _
      congr 1
      · rw [VExpr.liftN_appN,
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
        show VExpr.appN (.bvar (liftVar Δ.length
          ((idxTel U np ty).length + ty.ctors.length + 1)
          ((idxTel U np ty).length + 1))) _ = _
        rw [liftVar_le (by omega), show Δ.length +
          ((idxTel U np ty).length + ty.ctors.length + 1) =
          (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 from by omega]
  rw [hcod] at hb
  have hshape := hidx.retarget (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 - idxs.length =
      Δ.length + ty.ctors.length + 1 from by rw [hlen]; omega,
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hfull := hshape.snoc ha
  simp only [VExpr.inst] at hfull
  change env.SpineWF (U+1) _
    (VExpr.forallN
      (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
      (VExpr.forallN [VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length)]
        (.sort (.param 0))))
    (idxs ++ [a]) (.sort (.param 0)) at hfull
  rw [← VExpr.forallN_append] at hfull
  have hfullLen : (idxs ++ [a]).length =
      (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0 ++
        [VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
              ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)]).length := by
    simp only [List.length_append, List.length_singleton, VExpr.liftTelN_length, hlen]
  have hactual := hfull.retarget hfullLen
    (VExpr.app
      (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1))
        (VExpr.bvarRevRange 1 (idxTel U np ty).length))
      (.bvar 0))
  rw [VExpr.forallN_append] at hactual
  have happ := hactual.hasType_appN hb
  rw [show VExpr.app
      (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1))
        (VExpr.bvarRevRange 1 (idxTel U np ty).length))
      (.bvar 0) =
      VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
        ty.ctors.length + 1)) (VExpr.bvarRevRange 0 ((idxTel U np ty).length + 1)) from by
        rw [VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length + 1 =
          1 + (idxTel U np ty).length from by omega),
          ← VExpr.bvarRevRange_append (idxTel U np ty).length 1]
        simpa [VExpr.bvarRevRange, VExpr.appN] using (VExpr.appN_append
          (.bvar ((idxTel U np ty).length + Δ.length + ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length) [VExpr.bvar 0]).symm,
    VExpr.instRev_appN,
    VExpr.instRev_bvar_ge _ (by
      simp only [List.length_append, List.length_singleton]
      rw [hlen]
      omega),
    VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length + 1 =
      (idxs ++ [a]).length from by simp [hlen]),
    VExpr.map_instRev_bvarRevRange] at happ
  rw [show (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 -
      (idxs ++ [a]).length = Δ.length + ty.ctors.length from by
    simp only [List.length_append, List.length_singleton]
    rw [hlen]
    omega] at happ
  simpa [List.length_append, hlen] using happ

/-- The motive variable applied to a well-typed index spine and major
premise has the recursor's elimination sort. -/
theorem Stage3Env.motiveApp_hasType
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN
        (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))))
    (hlen : idxs.length = (idxTel U np ty).length)
    (ha : env.HasType (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))) a
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + ty.ctors.length + 1) np ++ idxs))) :
    env.HasType (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.bvar (Δ.length + ty.ctors.length)) (idxs ++ [a]))
      (.sort (.param 0)) := by
  have hM := getElem?_rstack3 Δ (minorTypes U T np ty ty.ctors).reverse
    (motiveType U T np ty) (paramsTel U np ty).reverse
    (i := Δ.length + ty.ctors.length)
    (by simp only [List.length_reverse, minorTypes_length])
  have hmlu := Lookup.of_getElem? hM
  rw [motiveType_liftN] at hmlu
  have hshape := hidx.retarget (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (Δ.length + ty.ctors.length + 1 +
          (idxTel U np ty).length) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show Δ.length + ty.ctors.length + 1 + (idxTel U np ty).length - idxs.length =
      Δ.length + ty.ctors.length + 1 from by rw [hlen]; omega,
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hfull := hshape.snoc ha
  simp only [VExpr.inst] at hfull
  exact hfull.hasType_appN (.bvar hmlu)

theorem Stage3Env.motiveAppRec_hasType
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN
        (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))))
    (hlen : idxs.length = (idxTel U np ty).length)
    (ha : env.HasType (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))) a
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + ty.ctors.length + 1) np ++ idxs))) :
    env.HasType (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.bvar (Δ.length + ty.ctors.length)) (idxs ++ [a]))
      (.sort (.param 0)) := by
  have hM := getElem?_rstack3 Δ (minorTypesRec U T np ty ty.ctors).reverse
    (motiveType U T np ty) (paramsTel U np ty).reverse
    (i := Δ.length + ty.ctors.length)
    (by simp only [List.length_reverse, minorTypesRec_length])
  exact motiveVarApp_hasType (env := env) (U := U) (T := T) (np := np)
    (l := l) (ty := ty) (.bvar (Lookup.of_getElem? hM)) hidx hlen ha

/-- The constructor-headed major of an iota rule, in the rule's binder
context (parameter spine past the motive, minors and fields). -/
theorem Stage3Env.ctorAppRule_hasType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
  have W := Ctx.LiftN.consTel (n := ty.ctors.length)
    (VExpr.liftTelN 1 (ctorFieldsR U np c) 0)
    (Ctx.LiftN.zero (n := ty.ctors.length)
      (Γ := motiveType U T np ty :: (paramsTel U np ty).reverse)
      (minorTypes U T np ty ty.ctors).reverse
      (h := by simp [minorTypes_length]))
  have h := (S.ctorAppMin_hasType hc []).weakN S.ord W
  have hlen : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
      (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
  rw [hlen] at h
  simp only [List.length_nil, Nat.zero_add, VExpr.liftN_appN, VExpr.liftN, List.map_append,
    List.map_map] at h
  rw [VExpr.liftTelN_liftTelN,
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)] at h
  simp only [Function.comp_def, VExpr.liftN_zero, Nat.add_zero] at h
  have hmap : (ctorIdxs U np c).map (fun e =>
      (e.liftN 1 (ctorFieldsR U np c).length).liftN
        ty.ctors.length (ctorFieldsR U np c).length) =
      (ctorIdxs U np c).map (fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) := by
    apply List.map_congr_left
    intro e _
    rw [VExpr.liftN'_liftN_hi]
    congr 1
    omega
  rw [hmap] at h
  simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem Stage3Env.ctorAppRuleRec_hasType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
  have W := Ctx.LiftN.consTel (n := ty.ctors.length)
    (VExpr.liftTelN 1 (ctorFieldsR U np c) 0)
    (Ctx.LiftN.zero (n := ty.ctors.length)
      (Γ := motiveType U T np ty :: (paramsTel U np ty).reverse)
      (minorTypesRec U T np ty ty.ctors).reverse
      (h := by simp [minorTypesRec_length]))
  have h := (S.ctorAppMin_hasType hc []).weakN S.ord W
  have hlen : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
      (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
  rw [hlen] at h
  simp only [List.length_nil, Nat.zero_add, VExpr.liftN_appN, VExpr.liftN, List.map_append,
    List.map_map] at h
  rw [VExpr.liftTelN_liftTelN,
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)] at h
  simp only [Function.comp_def, VExpr.liftN_zero, Nat.add_zero] at h
  have hmap : (ctorIdxs U np c).map (fun e =>
      (e.liftN 1 (ctorFieldsR U np c).length).liftN
        ty.ctors.length (ctorFieldsR U np c).length) =
      (ctorIdxs U np c).map (fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) := by
    apply List.map_congr_left
    intro e _
    rw [VExpr.liftN'_liftN_hi]
    congr 1
    omega
  rw [hmap] at h
  simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem Stage3Env.ruleBinders_onTel {c : VConstVal} (hc : c ∈ ty.ctors) :
    OnTel env (U+1) []
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypes U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) := by
  have hP : OnTel env (U+1) [] (paramsTel U np ty) := by
    have := S.hparams.of_append.1.instL (U' := U+1) VLevel.params'_one_wf
    simpa [paramsTel] using this
  have hF : OnTel env (U+1)
      ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) := by
    have h0 := S.fieldsWF_onTel _ [] 0 rfl (by simpa using S.hfields c hc)
    have h1 := h0.weakN S.ord
      (.zero ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty]))
    rw [liftTelN_congr _ _ (show ((minorTypes U T np ty ty.ctors).reverse ++
        [motiveType U T np ty]).length = ty.ctors.length + 1 from by
      simp only [List.length_append, List.length_reverse, minorTypes_length,
        List.length_singleton])] at h1
    simpa [ctorFieldsR, List.map_reverse, paramsTel,
      List.append_assoc] using h1
  refine OnTel.append (OnTel.append hP ⟨?_, ?_⟩) ?_
  · simpa only [List.append_nil] using S.motive_isType
  · have := S.minorTypes_onTel ty.ctors (fun _ h => h) [] 0 rfl
    simpa only [List.nil_append, List.append_nil] using this
  · simpa only [List.append_nil, List.append_assoc, List.reverse_append,
      List.reverse_cons, List.singleton_append] using hF

theorem Stage3Env.ruleBindersRec_onTel {c : VConstVal} (hc : c ∈ ty.ctors) :
    OnTel env (U+1) []
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypesRec U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) := by
  have hP : OnTel env (U+1) [] (paramsTel U np ty) := by
    have := S.hparams.of_append.1.instL (U' := U+1) VLevel.params'_one_wf
    simpa [paramsTel] using this
  have hF : OnTel env (U+1)
      ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) := by
    have h0 := S.fieldsWF_onTel _ [] 0 rfl (by simpa using S.hfields c hc)
    have h1 := h0.weakN S.ord
      (.zero ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty]))
    rw [liftTelN_congr _ _ (show ((minorTypesRec U T np ty ty.ctors).reverse ++
        [motiveType U T np ty]).length = ty.ctors.length + 1 from by
      simp only [List.length_append, List.length_reverse, minorTypesRec_length,
        List.length_singleton])] at h1
    simpa [ctorFieldsR, List.map_reverse, paramsTel,
      List.append_assoc] using h1
  refine OnTel.append (OnTel.append hP ⟨?_, ?_⟩) ?_
  · simpa only [List.append_nil] using S.motive_isType
  · have := S.minorTypesRec_onTel ty.ctors (fun _ h => h) [] 0 rfl
    simpa only [List.nil_append, List.append_nil] using this
  · simpa only [List.append_nil, List.append_assoc, List.reverse_append,
      List.reverse_cons, List.singleton_append] using hF

theorem Stage3Env.ruleType_isType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c) :
    env.IsType (U+1) [] ((rule U T np ty i c).type) := by
  have hc := List.mem_of_getElem? hci
  show env.IsType (U+1) [] (VExpr.forallN
    (paramsTel U np ty ++ motiveType U T np ty :: minorTypes U T np ty ty.ctors ++
      VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
      (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
        [VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])))
  refine IsType.forallN (S.ruleBinders_onTel hc) ?_
  simp only [List.reverse_append, List.reverse_cons, List.append_nil, List.append_assoc,
    List.singleton_append]
  have hSp0 := S.result_transport hc
    ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := ty.ctors.length + 1) (by simp [minorTypes_length]) [] (d := 0) rfl
  have hSp : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((ctorFieldsR U np c).length + ty.ctors.length + 1)
        (idxTel U np ty) 0) (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa [List.append_assoc, Nat.add_assoc] using hSp0
  have hidxLen : ((ctorIdxs U np c).map fun e =>
      e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length).length =
      (idxTel U np ty).length := by
    simp only [List.length_map, ctorIdxs_length, idxTel_length]
    exact (stage3Ctor_eq (S.hs3 c hc)).2.1
  have hctor := S.ctorAppRule_hasType hc
  have hSp' : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse.length +
          ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using hSp
  have hctor' : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse.length +
            ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using hctor
  refine ⟨.param 0, ?_⟩
  have hm := S.motiveApp_hasType
    (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse
    hSp' hidxLen hctor'
  rw [List.length_reverse, VExpr.liftTelN_length,
    show (ctorFieldsR U np c).length + ty.ctors.length =
      ty.ctors.length + (ctorFieldsR U np c).length from by omega,
    show ty.ctors.length + (ctorFieldsR U np c).length + 1 =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega] at hm
  exact hm

theorem Stage3Env.ruleTypeRec_isType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c) :
    env.IsType (U+1) [] ((ruleRec U T np ty i c).type) := by
  have hc := List.mem_of_getElem? hci
  show env.IsType (U+1) [] (VExpr.forallN
    (paramsTel U np ty ++ motiveType U T np ty :: minorTypesRec U T np ty ty.ctors ++
      VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
      (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
        [VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])))
  refine IsType.forallN (S.ruleBindersRec_onTel hc) ?_
  simp only [List.reverse_append, List.reverse_cons, List.append_nil, List.append_assoc,
    List.singleton_append]
  have hSp0 := S.result_transport hc
    ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := ty.ctors.length + 1) (by simp [minorTypesRec_length]) [] (d := 0) rfl
  have hSp : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((ctorFieldsR U np c).length + ty.ctors.length + 1)
        (idxTel U np ty) 0) (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa [List.append_assoc, Nat.add_assoc] using hSp0
  have hidxLen : ((ctorIdxs U np c).map fun e =>
      e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length).length =
      (idxTel U np ty).length := by
    simp only [List.length_map, ctorIdxs_length, idxTel_length]
    exact (stage3Ctor_eq (S.hs3 c hc)).2.1
  have hctor := S.ctorAppRuleRec_hasType hc
  have hSp' : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse.length +
          ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using hSp
  have hctor' : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse.length +
            ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using hctor
  refine ⟨.param 0, ?_⟩
  have hm := S.motiveAppRec_hasType
    (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse
    hSp' hidxLen hctor'
  rw [List.length_reverse, VExpr.liftTelN_length,
    show (ctorFieldsR U np c).length + ty.ctors.length =
      ty.ctors.length + (ctorFieldsR U np c).length from by omega,
    show ty.ctors.length + (ctorFieldsR U np c).length + 1 =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega] at hm
  exact hm

/-- A recursive field gives a well-typed recursive call in the full iota
rule context, carrying that field's own index arguments. -/
theorem Stage3Env.recCallRule_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty))
    {q : Nat × List VExpr}
    (hq : q ∈ recPairsR U T np (idxTel U np ty).length c) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange (ctorFieldsR U np c).length
            (np + ty.ctors.length + 1)))
        ((q.2.map fun e =>
          (e.liftN (ty.ctors.length + 1) q.1).liftN
            ((ctorFieldsR U np c).length - q.1)) ++
          [.bvar ((ctorFieldsR U np c).length - 1 - q.1)]))
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        ((q.2.map fun e =>
          (e.liftN (ty.ctors.length + 1) q.1).liftN
            ((ctorFieldsR U np c).length - q.1)) ++
          [.bvar ((ctorFieldsR U np c).length - 1 - q.1)])) := by
  obtain ⟨B, hBj, hrecB0, hidx⟩ := recPairsR_mem hq
  have hrecB : isRecField U T np
      (ctorFields (VExpr.dropN np ty.type)).length q.1 B = true := by
    rwa [← idxTel_length (U := U) (ty := ty)]
  have hjm : q.1 < (ctorFieldsR U np c).length := by
    simpa [ctorFieldsR_length] using recPairsR_lt _ hq
  have hml2 : (VExpr.liftTelN (ty.ctors.length + 1)
      (ctorFieldsR U np c) 0).length = (ctorFieldsR U np c).length :=
    VExpr.liftTelN_length ..
  have hSp0 := S.spine_transport hc hBj hrecB
    ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := ty.ctors.length + 1) (by simp [minorTypes_length])
    ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).drop q.1).reverse
    (d := (ctorFieldsR U np c).length - q.1) (by
      simp only [List.length_reverse, List.length_drop, hml2])
  rw [show
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).drop q.1).reverse ++
          ((VExpr.liftTelN (ty.ctors.length + 1)
            ((ctorFieldsR U np c).take q.1) 0).reverse ++
            (((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty]) ++
              (paramsTel U np ty).reverse)) =
        (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
          ((minorTypes U T np ty ty.ctors).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse)) from by
      rw [← VExpr.liftTelN_take, List.append_assoc,
        ← List.append_assoc
          (((VExpr.liftTelN (ty.ctors.length + 1)
            (ctorFieldsR U np c) 0).drop q.1).reverse),
        ← List.reverse_append, List.take_append_drop, List.singleton_append,
        ← List.append_assoc],
    liftTelN_congr _ _ (show q.1 + (ty.ctors.length + 1) +
        ((ctorFieldsR U np c).length - q.1) =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega),
    ← hidx] at hSp0
  have hni : q.2.length = (idxTel U np ty).length := by
    rw [hidx, List.length_map, idxTel_length]
    exact (isRecField_eq hrecB).2.1
  have hSp : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1)
        (idxTel U np ty) 0) (.sort (l.inst (VLevel.params' U 1))))
      (q.2.map fun e => (e.liftN (ty.ctors.length + 1) q.1).liftN
        ((ctorFieldsR U np c).length - q.1))
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using hSp0
  have hSpLen : (q.2.map fun e =>
      (e.liftN (ty.ctors.length + 1) q.1).liftN
        ((ctorFieldsR U np c).length - q.1)).length =
      (idxTel U np ty).length := by simpa using hni
  have hF : ((VExpr.liftTelN (ty.ctors.length + 1)
      (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))[
      (ctorFieldsR U np c).length - 1 - q.1]? =
      some ((B.instL (VLevel.params' U 1)).liftN
        (ty.ctors.length + 1) q.1) := by
    rw [List.getElem?_append_left
        (by simp only [List.length_reverse, VExpr.liftTelN_length]; omega),
      List.getElem?_reverse (by simp only [VExpr.liftTelN_length]; omega),
      VExpr.liftTelN_length,
      show (ctorFieldsR U np c).length - 1 -
        ((ctorFieldsR U np c).length - 1 - q.1) = q.1 from by omega,
      VExpr.liftTelN_getElem?, ctorFieldsR_getElem?, hBj]
    simp only [Option.map_some, Nat.zero_add]
  have hflu := Lookup.of_getElem? hF
  rw [show (((B.instL (VLevel.params' U 1)).liftN
      (ty.ctors.length + 1) q.1).liftN
        ((ctorFieldsR U np c).length - 1 - q.1 + 1)) =
      VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          q.2.map fun e => (e.liftN (ty.ctors.length + 1) q.1).liftN
            ((ctorFieldsR U np c).length - q.1)) from by
    conv => lhs; rw [(isRecField_eq hrecB).1]
    rw [VExpr.instL_appN, List.map_append, bvarRevRange_instL,
      show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
        .const T (VLevel.params' U 1) from by
        simp [VExpr.instL, VLevel.params_map_inst_params'],
      VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
      bvarRevRange_liftN_ge _ _ _ _ (by omega),
      bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
      VExpr.bvarRevRange_congr np (show
        (ctorFieldsR U np c).length - 1 - q.1 + 1 +
          (ty.ctors.length + 1 + q.1) =
        (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega),
      ← hidx, List.map_map]
    apply congrArg (VExpr.appN (.const T (VLevel.params' U 1)))
    apply congrArg (VExpr.bvarRevRange
      ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++ ·)
    apply List.map_congr_left
    intro e _
    rw [show (ctorFieldsR U np c).length - 1 - q.1 + 1 =
      (ctorFieldsR U np c).length - q.1 from by omega]
    simp only [Function.comp_apply]
    ] at hflu
  have ha : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (.bvar ((ctorFieldsR U np c).length - 1 - q.1))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((VExpr.liftTelN (ty.ctors.length + 1)
            (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1) np ++
          q.2.map fun e => (e.liftN (ty.ctors.length + 1) q.1).liftN
            ((ctorFieldsR U np c).length - q.1))) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using
      (VEnv.HasType.bvar (env := env) (U := U+1) hflu)
  have hr := S.recApp_hasType hrec
    (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse
    hSp hSpLen ha
  rw [List.length_reverse, VExpr.liftTelN_length,
    show (ctorFieldsR U np c).length + ty.ctors.length =
      ty.ctors.length + (ctorFieldsR U np c).length from by omega] at hr
  exact hr

/-- A generalized recursive argument yields the direct or lambda-valued
recursive call required by its functional IH in the complete rule context. -/
theorem Stage3Env.ruleCallRec_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty))
    {r : RecArg} (hr : r ∈ recArgsR U T np (idxTel U np ty).length c) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (r.ruleCall (ctorFieldsR U np c).length ty.ctors.length
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange (ctorFieldsR U np c).length
            (np + ty.ctors.length + 1))))
      (r.ruleIH (ctorFieldsR U np c).length ty.ctors.length) := by
  obtain ⟨r₀, B, rfl, hB, hr₀⟩ := recArgsR_mem hr
  let r := r₀.instL (VLevel.params' U 1)
  let m := (ctorFieldsR U np c).length
  let k := ty.ctors.length
  let j := r₀.fieldIndex
  let Fs := VExpr.liftTelN (k+1) (ctorFieldsR U np c) 0
  let As := r.ruleBinders m k
  let idxs := r.indices.map fun e =>
    (e.liftN (k+1) (r.fieldIndex+r.binders.length)).liftN
      (m-r.fieldIndex) r.binders.length
  let Γ := Fs.reverse ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
    (motiveType U T np ty :: (paramsTel U np ty).reverse))
  have hjm : j < m := by
    simpa [j, m, RecArg.instL, ctorFieldsR_length] using recArgsR_lt _ hr
  have hFsLen : Fs.length = m := by
    simp [Fs, m, VExpr.liftTelN_length]
  have ht := S.recArg_transport hc hB hr₀
    ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := k+1) (by simp [k, minorTypesRec_length])
    (Fs.drop j).reverse (d := m-j) (by
      simp only [List.length_reverse, List.length_drop, hFsLen])
  dsimp only [r, j, RecArg.instL] at ht
  have hctx :
      (Fs.drop j).reverse ++
          ((VExpr.liftTelN (k+1) ((ctorFieldsR U np c).take j) 0).reverse ++
            (((minorTypesRec U T np ty ty.ctors).reverse ++
              [motiveType U T np ty]) ++ (paramsTel U np ty).reverse)) = Γ := by
    dsimp only [Γ, Fs]
    rw [← VExpr.liftTelN_take, List.append_assoc,
      ← List.append_assoc
        (((VExpr.liftTelN (k+1) (ctorFieldsR U np c) 0).drop j).reverse),
      ← List.reverse_append, List.take_append_drop, List.singleton_append,
      ← List.append_assoc]
  have htel : OnTel env (U+1) Γ As := by
    rw [hctx] at ht
    simpa [r, As, m, k, j, RecArg.instL, RecArg.ruleBinders] using ht.1
  have hsp : env.SpineWF (U+1) (As.reverse ++ Γ)
      (VExpr.forallN
        (VExpr.liftTelN (m+k+r.binders.length+1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))) := by
    rw [hctx] at ht
    simpa [r, As, idxs, m, k, j, RecArg.instL, RecArg.ruleBinders,
      List.append_assoc,
      show j + r₀.binders.length + (k+1) + (m-j) =
        m+k+r₀.binders.length+1 from by omega] using ht.2
  have hF : Γ[m-1-j]? =
      some ((B.instL (VLevel.params' U 1)).liftN (k+1) j) := by
    dsimp only [Γ, Fs]
    rw [List.getElem?_append_left
        (by simp only [List.length_reverse, VExpr.liftTelN_length]; omega),
      List.getElem?_reverse (by rw [hFsLen]; omega),
      VExpr.liftTelN_length,
      show m - 1 - (m - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?, ctorFieldsR_getElem?, hB]
    simp
  have hlu := Lookup.of_getElem? hF
  dsimp only [j, r] at hlu
  rw [show m-1-r₀.fieldIndex+1 = m-r₀.fieldIndex from by omega]
    at hlu
  have hfield := recArg_rule_fieldType hr₀ m k (by simpa [j] using hjm)
  simp only [RecArg.instL, ElimMode.large_sourceLevels] at hfield
  rw [hfield] at hlu
  have hf0 := VEnv.HasType.bvar (env := env) (U := U+1) hlu
  have hf := hf0.weakN S.ord (Ctx.LiftN.zero (Γ := Γ) As.reverse)
  have hmajor := VEnv.HasType.appN_selfSpine (env := env) (U := U+1)
    (As := As) (B := VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (m+k+r.binders.length+1) np ++ idxs))
    (Δ := []) (Γ := Γ) (by
      simpa [As, r, idxs, j, RecArg.instL, RecArg.ruleBinders,
        List.length_reverse, List.map_map, Function.comp_def] using hf)
  simp only [List.length_nil, VExpr.liftN_zero, List.nil_append] at hmajor
  have hAsLen : As.length = r.binders.length := by
    simp [As, RecArg.ruleBinders, VExpr.liftTelN_length]
  change env.HasType (U+1) (As.reverse ++ Γ)
    ((VExpr.bvar (m-1-r.fieldIndex+As.length)).appN
      (VExpr.bvarRevRange 0 As.length))
    (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (m+k+r.binders.length+1) np ++ idxs)) at hmajor
  rw [hAsLen] at hmajor
  have hlen : idxs.length = (idxTel U np ty).length := by
    simpa [idxs, r, RecArg.instL] using (recArg?_eq hr₀).2.2.2.1
  have hcall := S.recAppRec_hasType hrec (As.reverse ++ Fs.reverse)
    (by simpa [Γ, List.append_assoc, hAsLen, hFsLen, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hsp)
    hlen
    (by simpa [Γ, List.append_assoc, hAsLen, hFsLen, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hmajor)
  have hbaseLift :
      (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange m (np+(k+1)))).liftN r.binders.length =
      VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange (m+r.binders.length) (np+(k+1))) := by
    rw [VExpr.liftN_appN]
    simp only [VExpr.liftN]
    rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _)]
    apply congrArg (VExpr.appN _)
    apply VExpr.bvarRevRange_congr
    omega
  have hbaseRange :
      VExpr.appN
        ((VExpr.const (.str T "rec") (VLevel.params (U+1))).app
          (VExpr.bvar (np + (k + (m + r.binders.length)))))
        (VExpr.bvarRevRange (m+r.binders.length) (np+k)) =
      VExpr.appN
        (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange (m+r.binders.length) (np+(k+1))) := by
    rw [show np + (k + (m + r.binders.length)) =
        (m+r.binders.length) + (np+k) by omega,
      show np+(k+1) = (np+k)+1 by omega]
    rfl
  have hlam := HasType.lamN htel (by
    simpa [Γ, Fs, hAsLen, hFsLen, List.append_assoc,
      VExpr.liftN_appN, bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcall)
  rw [hbaseRange] at hlam
  simpa only [RecArg.ruleCall, RecArg.ruleIH, r, As, idxs, m, k, Γ, Fs,
    hbaseLift, List.append_assoc, Nat.add_assoc] using hlam


/-- The right-hand side of an indexed iota rule: the constructor's minor
premise applied to its fields and to one indexed recursive call per recursive
field. -/
theorem Stage3Env.minorApp_hasType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.bvar (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length))
        (VExpr.bvarRevRange 0 (ctorFieldsR U np c).length ++
          List.map (fun q => VExpr.appN
              (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
                (VExpr.bvarRevRange (ctorFieldsR U np c).length
                  (np + ty.ctors.length + 1)))
              ((q.2.map fun e =>
                (e.liftN (ty.ctors.length + 1) q.1).liftN
                  ((ctorFieldsR U np c).length - q.1)) ++
                [.bvar ((ctorFieldsR U np c).length - 1 - q.1)]))
            (recPairsR U T np (idxTel U np ty).length c)))
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])) := by
  obtain ⟨hik, -⟩ := List.getElem?_eq_some_iff.1 hci
  have hc := List.mem_of_getElem? hci
  let rs := recPairsR U T np (idxTel U np ty).length c
  have hrs : rs = recPairsR U T np (idxTel U np ty).length c := rfl
  have hrsLt : ∀ q ∈ rs, q.1 < (ctorFieldsR U np c).length := by
    intro q hq
    simpa [hrs, ctorFieldsR_length] using recPairsR_lt _ hq
  rw [VExpr.appN_append]
  have hlu0 : ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
      ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))[
      ty.ctors.length - 1 - i + (ctorFieldsR U np c).length]? =
      some (VExpr.liftN i (minorType U T np ty c)) := by
    rw [getElem?_rstack_mid _ _ _
        (by simp only [List.length_reverse, VExpr.liftTelN_length]; omega)
        (by simp only [List.length_reverse, VExpr.liftTelN_length, minorTypes_length]
            omega),
      show ty.ctors.length - 1 - i + (ctorFieldsR U np c).length -
        ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse).length =
        ty.ctors.length - 1 - i from by
          simp only [List.length_reverse, VExpr.liftTelN_length]
          omega,
      List.getElem?_reverse (by simp only [minorTypes_length]; omega),
      show (minorTypes U T np ty ty.ctors).length - 1 -
          (ty.ctors.length - 1 - i) = i from by
        simp only [minorTypes_length]
        omega,
      minorTypes_getElem?, hci, Nat.zero_add]
    rfl
  have hlu := Lookup.of_getElem? hlu0
  rw [VExpr.liftN_liftN,
    show i + (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length + 1) =
      (ctorFieldsR U np c).length + ty.ctors.length from by omega] at hlu
  have hminorEq : (minorType U T np ty c).liftN
      ((ctorFieldsR U np c).length + ty.ctors.length) =
      (VExpr.forallN
        (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
        ((VExpr.forallN (ihsFrom (ctorFieldsR U np c).length rs 0)
          (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
            (((ctorIdxs U np c).map fun e =>
              (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
              [VExpr.appN (.const c.name (VLevel.params' U 1))
                (VExpr.bvarRevRange (rs.length +
                    (ctorFieldsR U np c).length + 1) np ++
                  VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))).liftN
            ty.ctors.length (ctorFieldsR U np c).length)).liftN
        (ctorFieldsR U np c).length := by
    simp only [minorType, rs, ElimMode.large_sourceLevels]
    conv => lhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
        liftTelN_congr _ _ (show (1:Nat) +
          ((ctorFieldsR U np c).length + ty.ctors.length) =
          ty.ctors.length + 1 + (ctorFieldsR U np c).length from by omega),
        show (0:Nat) + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
          (ctorFieldsR U np c).length from by simp [VExpr.liftTelN_length]]
    conv => rhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
        show (0:Nat) + (VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).length = (ctorFieldsR U np c).length from by
          simp [VExpr.liftTelN_length],
        VExpr.liftN'_liftN_hi,
        Nat.add_comm ty.ctors.length (ctorFieldsR U np c).length]
  have hfields := HasType.appN_selfSpine (env := env) (U := U+1)
    (As := VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (B := (VExpr.forallN (ihsFrom (ctorFieldsR U np c).length rs 0)
      (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
        (((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))).liftN
        ty.ctors.length (ctorFieldsR U np c).length)
    (Δ := [])
    (Γ := (minorTypes U T np ty ty.ctors).reverse ++
      (motiveType U T np ty :: (paramsTel U np ty).reverse))
    (f := .bvar (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length)) (by
      have hb := VEnv.HasType.bvar (env := env) (U := U+1) hlu
      rw [hminorEq] at hb
      simpa [VExpr.liftTelN_length] using hb)
  simp only [List.length_nil, VExpr.liftTelN_length, VExpr.liftN_zero] at hfields
  rw [ihsFrom_liftN' (ctorFieldsR U np c).length ty.ctors.length rs
    hrsLt 0
    (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
      (((ctorIdxs U np c).map fun e =>
        (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
        [VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
            VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))
    (cut := (ctorFieldsR U np c).length) rfl] at hfields
  have hD :
      (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
        (((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)])).liftN
        ty.ctors.length ((ctorFieldsR U np c).length + 0 + rs.length) =
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])).liftN rs.length := by
    rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
      List.map_map, List.map_map]
    show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
    congr 1
    · show VExpr.bvar (liftVar ty.ctors.length
          ((ctorFieldsR U np c).length + rs.length)
          ((ctorFieldsR U np c).length + 0 + rs.length)) =
        VExpr.bvar (liftVar rs.length
          (ty.ctors.length + (ctorFieldsR U np c).length) 0)
      rw [liftVar_le (by omega), liftVar_le (Nat.zero_le _)]
      congr 1
      omega
    · congr 1
      · apply List.map_congr_left
        intro e _
        simp only [Function.comp_apply]
        rw [show (ctorFieldsR U np c).length + 0 + rs.length =
          (ctorFieldsR U np c).length + rs.length from by omega,
          VExpr.liftN_liftN_mid e ty.ctors.length rs.length (Nat.zero_le _)]
      · congr 1
        simp only []
        rw [show (ctorFieldsR U np c).length + 0 + rs.length =
          (ctorFieldsR U np c).length + rs.length from by omega]
        rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
          bvarRevRange_liftN_ge _ _ _ _ (by omega),
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
          bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
          bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
          VExpr.bvarRevRange_congr np (show ty.ctors.length +
            (rs.length + (ctorFieldsR U np c).length + 1) =
            rs.length + ((ctorFieldsR U np c).length + ty.ctors.length + 1) from by
              omega),
          VExpr.bvarRevRange_congr _ (show rs.length = rs.length + 0 from by omega)]
        rfl
  rw [hD] at hfields
  have hres := hasType_appN_ihs (env := env) (U := U+1)
    (m := (ctorFieldsR U np c).length) (k := ty.ctors.length)
    (rs := rs)
    (argOf := fun (j, idxs) =>
      VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange (ctorFieldsR U np c).length
            (np + ty.ctors.length + 1)))
        ((idxs.map fun e => (e.liftN (ty.ctors.length + 1) j).liftN
          ((ctorFieldsR U np c).length - j)) ++
          [.bvar ((ctorFieldsR U np c).length - 1 - j)]))
    hrsLt (fun q hq => by
      have hr := S.recCallRule_hasType hc hrec (hrs ▸ hq)
      have hargs : (q.2.map fun e =>
          ((e.liftN 1 q.1).liftN ((ctorFieldsR U np c).length - q.1)).liftN
            ty.ctors.length (ctorFieldsR U np c).length) =
          q.2.map fun e => (e.liftN (ty.ctors.length + 1) q.1).liftN
            ((ctorFieldsR U np c).length - q.1) := by
        apply List.map_congr_left
        intro e _
        rw [← VExpr.liftN_liftN_mid e ty.ctors.length
          ((ctorFieldsR U np c).length - q.1) (Nat.zero_le _),
          show q.1 + ((ctorFieldsR U np c).length - q.1) =
            (ctorFieldsR U np c).length from by
              have := hrsLt q hq
              omega]
      rw [hargs]
      exact hr)
    hfields
  simpa only [hrs, List.nil_append] using hres

/-- Generalized iota RHS: apply the selected constructor minor to every field
and then to the direct or functional recursive call generated for each
`RecArg`. -/
theorem Stage3Env.minorAppRec_hasType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty)) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.bvar (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length))
        (VExpr.bvarRevRange 0 (ctorFieldsR U np c).length ++
          List.map (fun r => r.ruleCall (ctorFieldsR U np c).length ty.ctors.length
              (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
                (VExpr.bvarRevRange (ctorFieldsR U np c).length
                  (np + ty.ctors.length + 1))))
            (recArgsR U T np (idxTel U np ty).length c)))
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])) := by
  obtain ⟨hik, -⟩ := List.getElem?_eq_some_iff.1 hci
  have hc := List.mem_of_getElem? hci
  let rs := recArgsR U T np (idxTel U np ty).length c
  have hrs : rs = recArgsR U T np (idxTel U np ty).length c := rfl
  have hrsLt : ∀ r ∈ rs, r.fieldIndex < (ctorFieldsR U np c).length := by
    intro r hr
    simpa [hrs, ctorFieldsR_length] using recArgsR_lt _ hr
  rw [VExpr.appN_append]
  have hlu0 : ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
      ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))[
      ty.ctors.length - 1 - i + (ctorFieldsR U np c).length]? =
      some (VExpr.liftN i (minorTypeRec U T np ty c)) := by
    rw [getElem?_rstack_mid _ _ _
        (by simp only [List.length_reverse, VExpr.liftTelN_length]; omega)
        (by simp only [List.length_reverse, VExpr.liftTelN_length,
          minorTypesRec_length]; omega),
      show ty.ctors.length - 1 - i + (ctorFieldsR U np c).length -
        ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse).length =
        ty.ctors.length - 1 - i from by
          simp only [List.length_reverse, VExpr.liftTelN_length]
          omega,
      List.getElem?_reverse (by simp only [minorTypesRec_length]; omega),
      show (minorTypesRec U T np ty ty.ctors).length - 1 -
          (ty.ctors.length - 1 - i) = i from by
        simp only [minorTypesRec_length]
        omega,
      minorTypesRec_getElem?, hci, Nat.zero_add]
    rfl
  have hlu := Lookup.of_getElem? hlu0
  rw [VExpr.liftN_liftN,
    show i + (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length + 1) =
      (ctorFieldsR U np c).length + ty.ctors.length from by omega] at hlu
  have hminorEq : (minorTypeRec U T np ty c).liftN
      ((ctorFieldsR U np c).length + ty.ctors.length) =
      (VExpr.forallN
        (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
        ((VExpr.forallN (ihsFromRecArgs (ctorFieldsR U np c).length rs 0)
          (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
            (((ctorIdxs U np c).map fun e =>
              (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
              [VExpr.appN (.const c.name (VLevel.params' U 1))
                (VExpr.bvarRevRange (rs.length +
                    (ctorFieldsR U np c).length + 1) np ++
                  VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))).liftN
            ty.ctors.length (ctorFieldsR U np c).length)).liftN
        (ctorFieldsR U np c).length := by
    simp only [minorTypeRec, rs, ElimMode.large_sourceLevels]
    conv => lhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
        liftTelN_congr _ _ (show (1:Nat) +
          ((ctorFieldsR U np c).length + ty.ctors.length) =
          ty.ctors.length + 1 + (ctorFieldsR U np c).length from by omega),
        show (0:Nat) + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
          (ctorFieldsR U np c).length from by simp [VExpr.liftTelN_length]]
    conv => rhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
        show (0:Nat) + (VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).length = (ctorFieldsR U np c).length from by
          simp [VExpr.liftTelN_length],
        VExpr.liftN'_liftN_hi,
        Nat.add_comm ty.ctors.length (ctorFieldsR U np c).length]
  have hfields := HasType.appN_selfSpine (env := env) (U := U+1)
    (As := VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (B := (VExpr.forallN (ihsFromRecArgs (ctorFieldsR U np c).length rs 0)
      (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
        (((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))).liftN
        ty.ctors.length (ctorFieldsR U np c).length)
    (Δ := [])
    (Γ := (minorTypesRec U T np ty ty.ctors).reverse ++
      (motiveType U T np ty :: (paramsTel U np ty).reverse))
    (f := .bvar (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length)) (by
      have hb := VEnv.HasType.bvar (env := env) (U := U+1) hlu
      rw [hminorEq] at hb
      simpa [VExpr.liftTelN_length] using hb)
  simp only [List.length_nil, VExpr.liftTelN_length, VExpr.liftN_zero] at hfields
  rw [ihsFromRecArgs_liftN' (ctorFieldsR U np c).length ty.ctors.length rs
    hrsLt 0
    (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
      (((ctorIdxs U np c).map fun e =>
        (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
        [VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
            VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))
    (cut := (ctorFieldsR U np c).length) rfl] at hfields
  have hD :
      (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
        (((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)])).liftN
        ty.ctors.length ((ctorFieldsR U np c).length + 0 + rs.length) =
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])).liftN rs.length := by
    rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
      List.map_map, List.map_map]
    show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
    congr 1
    · show VExpr.bvar (liftVar ty.ctors.length
          ((ctorFieldsR U np c).length + rs.length)
          ((ctorFieldsR U np c).length + 0 + rs.length)) =
        VExpr.bvar (liftVar rs.length
          (ty.ctors.length + (ctorFieldsR U np c).length) 0)
      rw [liftVar_le (by omega), liftVar_le (Nat.zero_le _)]
      congr 1
      omega
    · congr 1
      · apply List.map_congr_left
        intro e _
        simp only [Function.comp_apply]
        rw [show (ctorFieldsR U np c).length + 0 + rs.length =
          (ctorFieldsR U np c).length + rs.length from by omega,
          VExpr.liftN_liftN_mid e ty.ctors.length rs.length (Nat.zero_le _)]
      · congr 1
        simp only []
        rw [show (ctorFieldsR U np c).length + 0 + rs.length =
          (ctorFieldsR U np c).length + rs.length from by omega]
        rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
          bvarRevRange_liftN_ge _ _ _ _ (by omega),
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
          bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
          bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
          VExpr.bvarRevRange_congr np (show ty.ctors.length +
            (rs.length + (ctorFieldsR U np c).length + 1) =
            rs.length + ((ctorFieldsR U np c).length + ty.ctors.length + 1) from by
              omega),
          VExpr.bvarRevRange_congr _ (show rs.length = rs.length + 0 from by omega)]
        rfl
  rw [hD] at hfields
  have hres := hasType_appN_ruleIHs (env := env) (U := U+1)
    (m := (ctorFieldsR U np c).length) (k := ty.ctors.length)
    (rs := rs)
    (argOf := fun r => r.ruleCall (ctorFieldsR U np c).length ty.ctors.length
      (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange (ctorFieldsR U np c).length
          (np + ty.ctors.length + 1))))
    (fun r hr => S.ruleCallRec_hasType hc hrec (hrs ▸ hr)) hfields
  simpa only [hrs] using hres

/-- The constructor-headed left side of an indexed iota rule. -/
theorem Stage3Env.recRuleApp_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange (ctorFieldsR U np c).length
            (np + ty.ctors.length + 1)))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)]))
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])) := by
  have hSp0 := S.result_transport hc
    ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := ty.ctors.length + 1) (by simp [minorTypes_length]) [] (d := 0) rfl
  have hSp : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1)
        (idxTel U np ty) 0) (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa [List.append_assoc, Nat.add_assoc, List.length_reverse,
      VExpr.liftTelN_length] using hSp0
  have hidxLen : ((ctorIdxs U np c).map fun e =>
      e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length).length =
      (idxTel U np ty).length := by
    simp only [List.length_map, ctorIdxs_length, idxTel_length]
    exact (stage3Ctor_eq (S.hs3 c hc)).2.1
  have ha0 := S.ctorAppRule_hasType hc
  have ha : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((VExpr.liftTelN (ty.ctors.length + 1)
            (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using ha0
  have hr := S.recApp_hasType hrec
    (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse
    hSp hidxLen ha
  rw [List.length_reverse, VExpr.liftTelN_length,
    show (ctorFieldsR U np c).length + ty.ctors.length =
      ty.ctors.length + (ctorFieldsR U np c).length from by omega,
    show ty.ctors.length + (ctorFieldsR U np c).length + 1 =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega] at hr
  exact hr

/-- The constructor-headed left side of a generalized indexed iota rule. -/
theorem Stage3Env.recRuleAppRec_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty)) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange (ctorFieldsR U np c).length
            (np + ty.ctors.length + 1)))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)]))
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])) := by
  have hSp0 := S.result_transport hc
    ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := ty.ctors.length + 1) (by simp [minorTypesRec_length]) [] (d := 0) rfl
  have hSp : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1)
        (idxTel U np ty) 0) (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa [List.append_assoc, Nat.add_assoc, List.length_reverse,
      VExpr.liftTelN_length] using hSp0
  have hidxLen : ((ctorIdxs U np c).map fun e =>
      e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length).length =
      (idxTel U np ty).length := by
    simp only [List.length_map, ctorIdxs_length, idxTel_length]
    exact (stage3Ctor_eq (S.hs3 c hc)).2.1
  have ha0 := S.ctorAppRuleRec_hasType hc
  have ha : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((VExpr.liftTelN (ty.ctors.length + 1)
            (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using ha0
  have hr := S.recAppRec_hasType hrec
    (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse
    hSp hidxLen ha
  rw [List.length_reverse, VExpr.liftTelN_length,
    show (ctorFieldsR U np c).length + ty.ctors.length =
      ty.ctors.length + (ctorFieldsR U np c).length from by omega,
    show ty.ctors.length + (ctorFieldsR U np c).length + 1 =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega] at hr
  exact hr

/-- Well-formedness of the iota rule for the `i`-th constructor. -/
theorem Stage3Env.rule_WF {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) :
    (rule U T np ty i c).WF env := by
  have hc := List.mem_of_getElem? hci
  refine ⟨?_, ?_⟩
  · show env.HasType (U+1) [] (VExpr.lamN
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypes U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBinders_onTel hc) ?_
    simp only [List.reverse_append, List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.recRuleApp_hasType hc hrec
  · show env.HasType (U+1) [] (VExpr.lamN
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypes U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBinders_onTel hc) ?_
    simp only [List.reverse_append, List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.minorApp_hasType hci hrec

/-- Well-formedness of the generalized iota rule for the `i`-th constructor. -/
theorem Stage3Env.ruleRec_WF {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty)) :
    (ruleRec U T np ty i c).WF env := by
  have hc := List.mem_of_getElem? hci
  refine ⟨?_, ?_⟩
  · show env.HasType (U+1) [] (VExpr.lamN
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypesRec U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBindersRec_onTel hc) ?_
    simp only [List.reverse_append, List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.recRuleAppRec_hasType hc hrec
  · show env.HasType (U+1) [] (VExpr.lamN
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypesRec U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBindersRec_onTel hc) ?_
    simp only [List.reverse_append, List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.minorAppRec_hasType hci hrec

/-- `ctorType_eq` from the per-constructor facts directly (for use before
the constructor is in the environment). -/
theorem Stage3Env.ctorType_eq' {c : VConstVal}
    (htelc : VExpr.telN np c.type = VExpr.telN np ty.type)
    (hs3c : stage3Ctor U T np
      (ctorFields (VExpr.dropN np ty.type)).length 0 (VExpr.dropN np c.type)) :
    c.type = VExpr.forallN (VExpr.telN np ty.type)
      (VExpr.forallN (ctorFields (VExpr.dropN np c.type))
        (VExpr.appN (.const T (VLevel.params U))
          (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
            recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))))) := by
  conv => lhs; rw [← VExpr.forallN_telN_dropN np c.type, htelc,
    (stage3Ctor_eq hs3c).1]

/-- `ctorType_isType` from the per-constructor facts directly. -/
theorem Stage3Env.ctorType_isType' {c : VConstVal}
    (htelc : VExpr.telN np c.type = VExpr.telN np ty.type)
    (hs3c : stage3Ctor U T np
      (ctorFields (VExpr.dropN np ty.type)).length 0 (VExpr.dropN np c.type))
    (hfc : fieldsWF U T np env l (ctorFields (VExpr.dropN np ty.type))
      (VExpr.telN np ty.type).reverse 0 (ctorFields (VExpr.dropN np c.type)))
    (hresultc : env.SpineWF U
      ((ctorFields (VExpr.dropN np c.type)).reverse ++
        (VExpr.telN np ty.type).reverse)
      (VExpr.forallN (VExpr.liftTelN
        (ctorFields (VExpr.dropN np c.type)).length
        (ctorFields (VExpr.dropN np ty.type)) 0) (.sort l))
      (recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))) (.sort l)) :
    env.IsType U [] c.type := by
  rw [S.ctorType_eq' htelc hs3c]
  refine IsType.forallN S.hparams.of_append.1 ?_
  simp only [List.append_nil]
  refine IsType.forallN
    (S.fieldsWF_onTel_decl _ [] 0 rfl (by simpa using hfc)) ?_
  have hTapp := S.recAppPi_hasType_decl
    ((ctorFields (VExpr.dropN np c.type)).reverse)
  rw [List.length_reverse, VExpr.liftN_forallN] at hTapp
  have hres := hresultc.hasType_appN hTapp
  exact ⟨_, by
    rw [VExpr.appN_append, Nat.zero_add]
    exact hres⟩

omit S in
/-- In the identity path, each paired constructor receives the granular
raw/view certificate required immediately after the family insertion. -/
theorem Checked.WF.identityCtorWF
    {source : VInductDecl} {checked : source.Checked}
    {pre envT : VEnv} (hpre : pre.Ordered)
    (h : checked.WF pre)
    (hadd : pre.addConst checked.type.name
      checked.type.toVConstant = some envT)
    {ctor : NormalizedCtor}
    (hctor : ctor ∈
      checked.identityGeneration.block.ctorPairs) :
    ctor.WF checked.identityGeneration.block envT := by
  obtain ⟨c, hc, rfl⟩ :=
    checked.identityGeneration_ctor hctor
  let S := h.toDirectFamilyEnv hpre hadd
  have hcAn := checked.direct_anatomy.2.2.2.2.2 c hc
  have hfields : fieldsWF source.uvars checked.type.name
      source.nparams envT checked.resultLevel
      (ctorFields (VExpr.dropN source.nparams checked.type.type))
      (VExpr.telN source.nparams checked.type.type).reverse 0
      (ctorFields (VExpr.dropN source.nparams c.type)) := by
    simpa [checked.params_eq, checked.indices_eq] using
      fieldsWF_mono (addConst_le hadd) (h.2 c hc).1
  have hfieldTel : OnTel envT source.uvars
      (VExpr.telN source.nparams checked.type.type).reverse
      (ctorFields (VExpr.dropN source.nparams c.type)) :=
    S.fieldsWF_onTel_decl _ [] 0 rfl hfields
  have hbinders : OnTel envT source.uvars []
      (VExpr.telN source.nparams checked.type.type ++
        ctorFields (VExpr.dropN source.nparams c.type)) :=
    S.hparams.of_append.1.append (by simpa using hfieldTel)
  have htelRefl := hbinders.telDefEq_refl
  have hresultSpine : envT.SpineWF source.uvars
      ((ctorFields
          (VExpr.dropN source.nparams c.type)).reverse ++
        (VExpr.telN source.nparams checked.type.type).reverse)
      (VExpr.forallN
        (VExpr.liftTelN
          (ctorFields
            (VExpr.dropN source.nparams c.type)).length
          (ctorFields
            (VExpr.dropN source.nparams checked.type.type)) 0)
        (.sort checked.resultLevel))
      (recFieldIdxs source.nparams
        (VExpr.resultOf
          (VExpr.dropN source.nparams c.type)))
      (.sort checked.resultLevel) := by
    simpa [checked.params_eq, checked.indices_eq] using
      (h.2 c hc).2.mono (addConst_le hadd)
  have hresultTyped :=
    S.ctorResult_hasType_decl hresultSpine
  have hrawResult :
      VExpr.resultOf (VExpr.dropN source.nparams c.type) =
        VExpr.appN
          (.const checked.type.name
            (VLevel.params source.uvars))
          (VExpr.bvarRevRange
            (ctorFields
              (VExpr.dropN source.nparams c.type)).length
            source.nparams ++
            recFieldIdxs source.nparams
              (VExpr.resultOf
                (VExpr.dropN source.nparams c.type))) := by
    have hout := congrArg VExpr.resultOf
      (stage3Ctor_eq hcAn.2.2).1
    rw [VExpr.resultOf_forallN,
      VExpr.resultOf_appN_const] at hout
    simpa only [Nat.zero_add] using hout
  have hresultDF : envT.IsDefEq source.uvars
      ((ctorFields
          (VExpr.dropN source.nparams c.type)).reverse ++
        (VExpr.telN source.nparams checked.type.type).reverse)
      (VExpr.resultOf (VExpr.dropN source.nparams c.type))
      (VExpr.appN
        (.const checked.type.name
          (VLevel.params source.uvars))
        (VExpr.bvarRevRange
          (ctorFields
            (VExpr.dropN source.nparams c.type)).length
          source.nparams ++
          recFieldIdxs source.nparams
            (VExpr.resultOf
              (VExpr.dropN source.nparams c.type))))
      (.sort checked.resultLevel) := by
    exact Eq.mpr
      (congrArg
        (fun e => envT.IsDefEq source.uvars
          ((ctorFields
              (VExpr.dropN source.nparams c.type)).reverse ++
            (VExpr.telN source.nparams
              checked.type.type).reverse)
          e
          (VExpr.appN
            (.const checked.type.name
              (VLevel.params source.uvars))
            (VExpr.bvarRevRange
              (ctorFields
                (VExpr.dropN source.nparams c.type)).length
              source.nparams ++
              recFieldIdxs source.nparams
                (VExpr.resultOf
                  (VExpr.dropN source.nparams c.type))))
          (.sort checked.resultLevel))
        hrawResult)
      hresultTyped
  constructor
  · simpa [NormalizedCtor.declaredBinders,
      NormalizedCtor.rawFields,
      NormalizedCtor.viewBinders, CheckedCtor.ofDirect,
      checked.params_eq, hcAn.2.1] using htelRefl
  · simpa [NormalizedCtor.declaredBinders,
      NormalizedCtor.rawFields, NormalizedCtor.rawResult,
      NormalizedCtor.resultTarget, CheckedCtor.ofDirect,
      checked.params_eq, hcAn.2.1] using hresultDF
  · simpa [NormalizedCtor.emittedBinders,
      NormalizedCtor.rawFields,
      NormalizedCtor.viewBinders, CheckedCtor.ofDirect,
      Checked.identityGeneration, Checked.identityBlock,
      NormalizedChecked.rawParams, checked.params_eq] using htelRefl
  · simpa [NormalizedCtor.emittedBinders,
      NormalizedCtor.rawFields, NormalizedCtor.rawResult,
      NormalizedCtor.resultTarget, CheckedCtor.ofDirect,
      Checked.identityGeneration, Checked.identityBlock,
      NormalizedChecked.rawParams, checked.params_eq] using hresultDF

omit S in
/-- Every semantically checked direct declaration admits the identity mixed
generation certificate. This is the public bridge from the legacy checker
contract to the normalized transaction. -/
theorem Checked.WF.identityGeneration
    {source : VInductDecl} {checked : source.Checked}
    {env : VEnv} (h : checked.WF env) (henv : env.Ordered) :
    checked.identityGeneration.WF env := by
  have hfamily := h.family_isType
  have hnorm : checked.identityGeneration.block.normalization.WF env := by
    refine ⟨checked.type, checked.type, checked.types_eq, ?_, ?_, ?_⟩
    · simpa only [Checked.identityGeneration, Checked.identityBlock,
        Normalization.identity] using checked.types_eq
    · obtain ⟨u, hu⟩ := hfamily
      exact ⟨.sort u, hu⟩
    · intro envT hadd
      have hadd' : env.addConst checked.type.name
          checked.type.toVConstant = some envT := by
        simpa only [Checked.identityGeneration,
          Checked.identityBlock] using hadd
      have hall : ∀ c ∈ checked.type.ctors,
          envT.IsDefEqU source.uvars [] c.type c.type := by
        intro c hc
        have hpair :
            (⟨c, CheckedCtor.ofDirect source.uvars
              checked.type.name source.nparams
              checked.indices.length c⟩ : NormalizedCtor) ∈
              checked.identityGeneration.block.ctorPairs := by
          simpa only [Checked.identityGeneration,
            Checked.identityBlock, NormalizedChecked.ctorPairs,
            checked.constructors_eq] using
              (pairNormalizedCtors_map_self_contains hc :
                (⟨c, CheckedCtor.ofDirect source.uvars
                  checked.type.name source.nparams
                  checked.indices.length c⟩ :
                  NormalizedCtor) ∈
                    pairNormalizedCtors checked.type.ctors
                      (checked.type.ctors.map
                        (CheckedCtor.ofDirect source.uvars
                          checked.type.name source.nparams
                          checked.indices.length)))
        obtain ⟨u, hu⟩ :=
          (h.identityCtorWF henv hadd' hpair).rawDeclared_isType
        exact ⟨.sort u, hu⟩
      have hrel : List.Forall₂
          (fun c c' => envT.IsDefEqU source.uvars []
            c.type c'.type)
          checked.type.ctors checked.type.ctors := by
        let R : VConstVal → VConstVal → Prop :=
          fun c c' => envT.IsDefEqU source.uvars []
            c.type c'.type
        let rec diagonal :
            ∀ cs : List VConstVal,
              (∀ c ∈ cs, R c c) →
              List.Forall₂ R cs cs
          | [], _ => .nil
          | c :: cs, hs =>
              .cons (hs c (.head _))
                (diagonal cs fun c hc => hs c (.tail _ hc))
        exact diagonal checked.type.ctors hall
      simpa only [Checked.identityGeneration,
        Checked.identityBlock, Normalization.identity] using hrel
  refine {
    blockWF := ⟨hnorm, h⟩
    familyTel := ?_
    familyResult := ?_
    ctors := ?_
  }
  · simpa only [Checked.identityGeneration,
      Checked.identityBlock, NormalizedChecked.rawParams,
      NormalizedChecked.rawIndices, checked.params_eq,
      checked.indices_eq] using h.1.telDefEq_refl
  · simpa only [Checked.identityGeneration,
      Checked.identityBlock, NormalizedChecked.rawParams,
      NormalizedChecked.rawIndices, NormalizedChecked.rawResult,
      checked.params_eq, checked.indices_eq,
      checked.result_eq] using
        (VEnv.IsDefEq.sortDF
          checked.direct_anatomy.2.2.1
          checked.direct_anatomy.2.2.1 rfl :
          env.IsDefEq source.uvars
            (checked.params ++ checked.indices).reverse
            (.sort checked.resultLevel)
            (.sort checked.resultLevel)
            (.sort (.succ checked.resultLevel)))
  · intro envT hadd ctor hctor
    have hadd' : env.addConst checked.type.name
        checked.type.toVConstant = some envT := by
      simpa only [Checked.identityGeneration,
        Checked.identityBlock] using hadd
    exact h.identityCtorWF henv hadd' hctor

end VInductDecl

/-! ## `addInduct_WF` -/

theorem _root_.List.mem_zipIdx_getElem? {α} : ∀ {l : List α} {n : Nat} {a : α} {i : Nat},
    (a, i) ∈ l.zipIdx n → n ≤ i ∧ l[i - n]? = some a
  | b :: l, n, a, i, h => by
    simp only [List.zipIdx] at h
    rcases List.mem_cons.1 h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
      simp
    · obtain ⟨h1, h2⟩ := List.mem_zipIdx_getElem? h
      refine ⟨by omega, ?_⟩
      rw [show i - n = (i - (n+1)) + 1 from by omega]
      simpa using h2

namespace VInductDecl

theorem rulesFold_WF : ∀ (dfs : List VDefEq) {env₃ : VEnv},
    env₃.Ordered → (∀ df ∈ dfs, df.WF env₃) →
    (dfs.foldl VEnv.addDefEq env₃).Ordered
  | [], _, ord, _ => ord
  | df :: dfs, env₃, ord, hdfs => by
    rw [List.foldl_cons]
    exact rulesFold_WF dfs (.defeq ord (hdfs df (.head _)))
      (fun df' hdf' => (hdfs df' (.tail _ hdf')).mono VEnv.addDefEq_le)

/-- Every rule emitted from the paired constructor list is well formed in the
environment containing the mixed recursor. -/
theorem GenerationEnv.generatedRules_WF
    {source : VInductDecl}
    {gen : GenerationChecked source} {env : VEnv}
    (S : GenerationEnv gen env)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) :
    ∀ df ∈ gen.generatedRules, df.WF env := by
  intro df hdf
  change df ∈
    gen.block.ctorPairs.zipIdx.map
      (fun (ctor, i) => gen.rule i ctor) at hdf
  obtain ⟨⟨ctor, i⟩, hmem, rfl⟩ :=
    List.mem_map.1 hdf
  obtain ⟨-, hci⟩ :=
    List.mem_zipIdx_getElem? hmem
  rw [Nat.sub_zero] at hci
  exact S.rule_WF hci hrec

/-- Folding all mixed generated rules preserves environment ordering. -/
theorem GenerationEnv.generatedRulesFold_ordered
    {source : VInductDecl}
    {gen : GenerationChecked source} {env : VEnv}
    (S : GenerationEnv gen env)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) :
    (gen.generatedRules.foldl
      VEnv.addDefEq env).Ordered :=
  rulesFold_WF gen.generatedRules S.ord
    (S.generatedRules_WF hrec)

/-- Every rule emitted from the flattened mutual constructor list is well
formed in an environment containing every generated family recursor. -/
theorem BlockGenerationEnv.generatedRules_WF
    {source : VInductDecl}
    {gen : BlockGenerationChecked source} {env : VEnv}
    (S : BlockGenerationEnv gen env)
    (hrecs : ∀ family ∈ gen.families,
      env.constants (.str family.raw.name "rec") =
        some (gen.recursor family)) :
    ∀ df ∈ gen.generatedRules, df.WF env := by
  intro df hdf
  change df ∈
    gen.flatCtors.zipIdx.map
      (fun (constructor, i) => gen.rule i constructor) at hdf
  obtain ⟨⟨constructor, i⟩, hmem, rfl⟩ := List.mem_map.1 hdf
  obtain ⟨-, hci⟩ := List.mem_zipIdx_getElem? hmem
  rw [Nat.sub_zero] at hci
  exact S.rule_WF hci hrecs

/-- Folding every generated mutual rule preserves environment ordering. -/
theorem BlockGenerationEnv.generatedRulesFold_ordered
    {source : VInductDecl}
    {gen : BlockGenerationChecked source} {env : VEnv}
    (S : BlockGenerationEnv gen env)
    (hrecs : ∀ family ∈ gen.families,
      env.constants (.str family.raw.name "rec") =
        some (gen.recursor family)) :
    (gen.generatedRules.foldl VEnv.addDefEq env).Ordered :=
  rulesFold_WF gen.generatedRules S.ord
    (S.generatedRules_WF hrecs)

/-- Folding definitional equations only grows the environment and registers
every equation in the input list. -/
theorem rulesFold_spec : ∀ (dfs : List VDefEq) (env : VEnv),
    env ≤ dfs.foldl VEnv.addDefEq env ∧
      ∀ df ∈ dfs, (dfs.foldl VEnv.addDefEq env).defeqs df
  | [], _ => ⟨.rfl, nofun⟩
  | df :: dfs, env => by
    rw [List.foldl_cons]
    obtain ⟨hle, hmem⟩ := rulesFold_spec dfs (env.addDefEq df)
    refine ⟨VEnv.addDefEq_le.trans hle, fun df' hdf' => ?_⟩
    rcases List.mem_cons.1 hdf' with rfl | hdf'
    · exact hle.defeqs VEnv.addDefEq_self
    · exact hmem df' hdf'

/-- A successful constructor fold grows the environment, registers every
constructor, and certifies that every constructor name was fresh in the
fold's input environment. -/
theorem ctorFold_spec : ∀ (cs : List VConstVal) {env₀ env₁ : VEnv},
    List.foldlM (fun env (c : VConstVal) => env.addConst c.name c.toVConstant) env₀ cs =
      some env₁ →
    env₀ ≤ env₁ ∧
      (∀ c ∈ cs, env₁.constants c.name = some c.toVConstant) ∧
      ∀ c ∈ cs, env₀.constants c.name = none
  | [], _, _, hfold => by
    cases hfold
    exact ⟨.rfl, nofun, nofun⟩
  | c :: cs, env₀, env₁, hfold => by
    rw [List.foldlM_cons] at hfold
    obtain ⟨env₀', hadd, hrest⟩ := Option.bind_eq_some_iff.1 hfold
    obtain ⟨hle, hlook, hfresh⟩ := ctorFold_spec cs hrest
    have haddLe := VEnv.addConst_le hadd
    refine ⟨haddLe.trans hle, ?_, ?_⟩
    · intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact hle.constants (VEnv.addConst_self hadd)
      · exact hlook c' hc'
    · intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact VEnv.addConst_fresh hadd
      · exact haddLe.constants_none (hfresh c' hc')

/-- Sequentially inserting constants that are all well formed in the fold's
initial environment preserves ordering. Monotonicity transports the remaining
constant certificates after each insertion. -/
theorem constFold_ordered : ∀ (cs : List VConstVal) {env₀ env₁ : VEnv},
    env₀.Ordered →
    (∀ c ∈ cs, c.toVConstant.WF env₀) →
    List.foldlM
      (fun env (c : VConstVal) => env.addConst c.name c.toVConstant)
      env₀ cs = some env₁ →
    env₁.Ordered
  | [], _, _, ord, _, hfold => by
    cases hfold
    exact ord
  | c :: cs, env₀, env₁, ord, hwf, hfold => by
    rw [List.foldlM_cons] at hfold
    obtain ⟨env₀', hadd, hrest⟩ := Option.bind_eq_some_iff.1 hfold
    have hle := VEnv.addConst_le hadd
    have ord' : env₀'.Ordered :=
      .const ord (hwf c (.head _)) hadd
    exact constFold_ordered cs ord'
      (fun c' hc' => (hwf c' (.tail _ hc')).mono hle) hrest

/-- Adding the constructors of a stage-3 block preserves order and records
their lookups. -/
theorem ctorFold_WF {U : Nat} {T : Name} {np : Nat} {l : VLevel} {ty : VInductiveType}
    (hsort : VExpr.resultOf (VExpr.dropN np ty.type) = .sort l)
    (hlen : (VExpr.telN np ty.type).length = np) (hl : l.WF U) :
    ∀ (cs' : List VConstVal) {env₀ env₁ : VEnv},
    env₀.Ordered → env₀.constants T = some ⟨U, ty.type⟩ →
    VEnv.OnTel env₀ U []
      (VExpr.telN np ty.type ++ ctorFields (VExpr.dropN np ty.type)) →
    (∀ c ∈ cs', c.uvars = U ∧ VExpr.telN np c.type = VExpr.telN np ty.type ∧
      stage3Ctor U T np (ctorFields (VExpr.dropN np ty.type)).length 0
        (VExpr.dropN np c.type) ∧
      fieldsWF U T np env₀ l (ctorFields (VExpr.dropN np ty.type))
        (VExpr.telN np ty.type).reverse 0 (ctorFields (VExpr.dropN np c.type)) ∧
      env₀.SpineWF U
        ((ctorFields (VExpr.dropN np c.type)).reverse ++
          (VExpr.telN np ty.type).reverse)
        (VExpr.forallN (VExpr.liftTelN
          (ctorFields (VExpr.dropN np c.type)).length
          (ctorFields (VExpr.dropN np ty.type)) 0) (.sort l))
        (recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))) (.sort l)) →
    List.foldlM (fun env (c : VConstVal) => env.addConst c.name c.toVConstant) env₀ cs' =
      some env₁ →
    env₁.Ordered ∧ env₀ ≤ env₁ ∧
      ∀ c ∈ cs', env₁.constants c.name = some ⟨U, c.type⟩
  | [], env₀, env₁, ord, _, _, _, hfold => by
    cases hfold
    exact ⟨ord, .rfl, nofun⟩
  | c :: cs', env₀, env₁, ord, hT, hpar, hcs, hfold => by
    rw [List.foldlM_cons] at hfold
    obtain ⟨env₀', hadd, hrest⟩ := Option.bind_eq_some_iff.1 hfold
    obtain ⟨hcU, htelc, hs3c, hfc, hresultc⟩ := hcs c (.head _)
    have S₀ : Stage3Env env₀ U T np l ⟨⟨⟨ty.uvars, ty.type⟩, ty.name⟩, []⟩ :=
      ⟨ord, hl, hsort, hlen, hT, nofun, nofun, nofun, hpar, nofun, nofun⟩
    have hwfc : c.toVConstant.WF env₀ := by
      show env₀.IsType c.toVConstant.uvars [] c.toVConstant.type
      rw [show c.toVConstant.uvars = c.uvars from rfl, hcU]
      exact S₀.ctorType_isType' htelc hs3c hfc hresultc
    have ord' : env₀'.Ordered := .const ord hwfc hadd
    have hle' := VEnv.addConst_le hadd
    obtain ⟨ord₁, hle₁, hlook⟩ := ctorFold_WF hsort hlen hl cs' ord'
      (hle'.constants hT) (hpar.mono hle')
      (fun c' hc' => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := hcs c' (.tail _ hc')
        exact ⟨h1, h2, h3, fieldsWF_mono hle' h4, h5.mono hle'⟩)
      hrest
    refine ⟨ord₁, hle'.trans hle₁, fun c' hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · have hself := VEnv.addConst_self hadd
      rw [show c'.toVConstant = ⟨U, c'.type⟩ from by rw [← hcU]] at hself
      exact hle₁.constants hself
    · exact hlook c' hc'

end VInductDecl

namespace VEnv
open VInductDecl

/-- Recover the exact intermediate environments from a successful normalized
generation transaction. The data-bearing trace is wrapped in `Nonempty` so
proof consumers can eliminate it without adding a choice axiom merely to
recover bookkeeping states. -/
theorem addInductGeneration_trace {source : VInductDecl}
    {gen : source.GenerationChecked}
    (hadd : addInductGeneration env gen = some env') :
    Nonempty (AddInductGenerationTrace env env' gen) := by
  unfold addInductGeneration at hadd
  obtain ⟨typeEnv, addType, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨ctorEnv, addCtors, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨recEnv, addRec, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact ⟨⟨typeEnv, ctorEnv, recEnv, addType, addCtors, addRec, rfl⟩⟩

/-- The normalized core is atomic: failure returns no observable intermediate
environment, while success exposes one complete trace. -/
theorem addInductGeneration_atomic {source : VInductDecl}
    (env : VEnv) (gen : source.GenerationChecked) :
    addInductGeneration env gen = none ∨
      ∃ env', addInductGeneration env gen = some env' ∧
        Nonempty (AddInductGenerationTrace env env' gen) := by
  cases hadd : addInductGeneration env gen with
  | none => exact .inl rfl
  | some env' =>
    exact .inr ⟨env', rfl, addInductGeneration_trace hadd⟩

/-- A successful normalized generation transaction only grows its input
environment. -/
theorem AddInductGenerationTrace.le {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen) : env ≤ env' := by
  have htype := addConst_le H.addType
  have hctors := (ctorFold_spec gen.block.sourceType.ctors H.addCtors).1
  have hrec := addConst_le H.addRec
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact htype.trans (hctors.trans (hrec.trans hrules))

/-- The raw family name was fresh before a successful normalized
transaction. -/
theorem AddInductGenerationTrace.family_fresh {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen) :
    env.constants gen.block.sourceType.name = none :=
  addConst_fresh H.addType

/-- The final environment contains the exact raw family constant. -/
theorem AddInductGenerationTrace.family_lookup {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen) :
    env'.constants gen.block.sourceType.name =
      some gen.block.sourceType.toVConstant := by
  have hctors := (ctorFold_spec gen.block.sourceType.ctors H.addCtors).1
  have hrec := addConst_le H.addRec
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact (hctors.trans (hrec.trans hrules)).constants
    (addConst_self H.addType)

/-- Every raw constructor name was fresh in the transaction's input
environment. -/
theorem AddInductGenerationTrace.ctor_fresh {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    {ctor : VConstVal} (hctor : ctor ∈ gen.block.sourceType.ctors) :
    env.constants ctor.name = none := by
  have htype := addConst_le H.addType
  have hfresh :=
    (ctorFold_spec gen.block.sourceType.ctors H.addCtors).2.2 ctor hctor
  exact htype.constants_none hfresh

/-- The final environment contains every exact raw constructor constant. -/
theorem AddInductGenerationTrace.ctor_lookup {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    {ctor : VConstVal} (hctor : ctor ∈ gen.block.sourceType.ctors) :
    env'.constants ctor.name = some ctor.toVConstant := by
  have hlookup :=
    (ctorFold_spec gen.block.sourceType.ctors H.addCtors).2.1 ctor hctor
  have hrec := addConst_le H.addRec
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact (hrec.trans hrules).constants hlookup

/-- The generated recursor name was fresh before a successful normalized
transaction. -/
theorem AddInductGenerationTrace.rec_fresh {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen) :
    env.constants (.str gen.block.sourceType.name "rec") = none := by
  have htype := addConst_le H.addType
  have hctors := (ctorFold_spec gen.block.sourceType.ctors H.addCtors).1
  exact (htype.trans hctors).constants_none (addConst_fresh H.addRec)

/-- The final environment contains the exact mixed generated recursor. -/
theorem AddInductGenerationTrace.rec_lookup {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen) :
    env'.constants (.str gen.block.sourceType.name "rec") =
      some gen.recursor := by
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact hrules.constants (addConst_self H.addRec)

/-- The final environment registers every mixed generated iota rule. -/
theorem AddInductGenerationTrace.rule_mem {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    {df : VDefEq} (hdf : df ∈ gen.generatedRules) :
    env'.defeqs df := by
  simpa only [H.addRules] using
    (rulesFold_spec gen.generatedRules H.recEnv).2 df hdf

/-! ### Block-wide transaction facts -/

/-- Recover every phase boundary from a successful block-wide transaction. -/
theorem addInductBlockGeneration_trace {source : VInductDecl}
    {gen : source.BlockGenerationChecked}
    (hadd : addInductBlockGeneration env gen = some env') :
    Nonempty (AddInductBlockGenerationTrace env env' gen) := by
  unfold addInductBlockGeneration at hadd
  obtain ⟨typeEnv, addTypes, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨ctorEnv, addCtors, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨recEnv, addRecs, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact ⟨⟨typeEnv, ctorEnv, recEnv, addTypes, addCtors, addRecs, rfl⟩⟩

/-- The block-wide transaction is atomic at its public `Option` boundary. -/
theorem addInductBlockGeneration_atomic {source : VInductDecl}
    (env : VEnv) (gen : source.BlockGenerationChecked) :
    addInductBlockGeneration env gen = none ∨
      ∃ env', addInductBlockGeneration env gen = some env' ∧
        Nonempty (AddInductBlockGenerationTrace env env' gen) := by
  cases hadd : addInductBlockGeneration env gen with
  | none => exact .inl rfl
  | some env' =>
    exact .inr ⟨env', rfl, addInductBlockGeneration_trace hadd⟩

/-- Every phase of a successful block transaction only grows the Theory
environment. -/
theorem AddInductBlockGenerationTrace.le {source : VInductDecl}
    {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen) : env ≤ env' := by
  have htypes :=
    (ctorFold_spec source.blockTypeConstants H.addTypes).1
  have hctors :=
    (ctorFold_spec source.blockConstructorConstants H.addCtors).1
  have hrecs := (ctorFold_spec gen.recursors H.addRecs).1
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact htypes.trans (hctors.trans (hrecs.trans hrules))

/-- Every source family name was fresh before a successful block
transaction. -/
theorem AddInductBlockGenerationTrace.family_fresh
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen)
    {type : VInductiveType} (htype : type ∈ source.types) :
    env.constants type.name = none := by
  have hmem : type.toVConstVal ∈ source.blockTypeConstants := by
    exact List.mem_map.2 ⟨type, htype, rfl⟩
  simpa [VInductDecl.blockTypeConstants] using
    (ctorFold_spec source.blockTypeConstants H.addTypes).2.2
      type.toVConstVal hmem

/-- The final environment contains every exact raw family constant. -/
theorem AddInductBlockGenerationTrace.family_lookup
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen)
    {type : VInductiveType} (htype : type ∈ source.types) :
    env'.constants type.name = some type.toVConstant := by
  have hmem : type.toVConstVal ∈ source.blockTypeConstants := by
    exact List.mem_map.2 ⟨type, htype, rfl⟩
  have hlookup :=
    (ctorFold_spec source.blockTypeConstants H.addTypes).2.1
      type.toVConstVal hmem
  have hctors :=
    (ctorFold_spec source.blockConstructorConstants H.addCtors).1
  have hrecs := (ctorFold_spec gen.recursors H.addRecs).1
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact (hctors.trans (hrecs.trans hrules)).constants hlookup

/-- Every flattened raw constructor name was fresh in the transaction's
input environment. -/
theorem AddInductBlockGenerationTrace.ctor_fresh
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ source.blockConstructorConstants) :
    env.constants constructor.name = none := by
  have htypes :=
    (ctorFold_spec source.blockTypeConstants H.addTypes).1
  have hfresh :=
    (ctorFold_spec source.blockConstructorConstants H.addCtors).2.2
      constructor hconstructor
  exact htypes.constants_none hfresh

/-- The final environment contains every exact raw constructor constant. -/
theorem AddInductBlockGenerationTrace.ctor_lookup
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ source.blockConstructorConstants) :
    env'.constants constructor.name = some constructor.toVConstant := by
  have hlookup :=
    (ctorFold_spec source.blockConstructorConstants H.addCtors).2.1
      constructor hconstructor
  have hrecs := (ctorFold_spec gen.recursors H.addRecs).1
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact (hrecs.trans hrules).constants hlookup

/-- Every generated recursor name was fresh before the block transaction. -/
theorem AddInductBlockGenerationTrace.rec_fresh
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen)
    {recursor : VConstVal} (hrecursor : recursor ∈ gen.recursors) :
    env.constants recursor.name = none := by
  have htypes :=
    (ctorFold_spec source.blockTypeConstants H.addTypes).1
  have hctors :=
    (ctorFold_spec source.blockConstructorConstants H.addCtors).1
  have hfresh :=
    (ctorFold_spec gen.recursors H.addRecs).2.2 recursor hrecursor
  exact (htypes.trans hctors).constants_none hfresh

/-- The final environment contains every generated recursor. -/
theorem AddInductBlockGenerationTrace.rec_lookup
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen)
    {recursor : VConstVal} (hrecursor : recursor ∈ gen.recursors) :
    env'.constants recursor.name = some recursor.toVConstant := by
  have hlookup :=
    (ctorFold_spec gen.recursors H.addRecs).2.1 recursor hrecursor
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact hrules.constants hlookup

/-- The final environment registers every block-generated iota rule. -/
theorem AddInductBlockGenerationTrace.rule_mem
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen)
    {df : VDefEq} (hdf : df ∈ gen.generatedRules) :
    env'.defeqs df := by
  simpa only [H.addRules] using
    (rulesFold_spec gen.generatedRules H.recEnv).2 df hdf

/-- Preserve ordering through the all-families phase. -/
private theorem addInductBlockGeneration_families_ordered
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    {blockEnv : VEnv}
    (H : AddInductBlockGenerationTrace env env' gen)
    (henv : env.Ordered) (hgen : gen.WF env blockEnv) :
    H.typeEnv.Ordered := by
  apply constFold_ordered source.blockTypeConstants henv ?_ H.addTypes
  intro type htype
  simp only [VInductDecl.blockTypeConstants, List.mem_map] at htype
  obtain ⟨raw, hraw, rfl⟩ := htype
  have hraw' : raw ∈ gen.families.map (·.raw) := by
    rw [gen.families_map_raw]
    exact hraw
  obtain ⟨family, hfamily, rfl⟩ := List.mem_map.1 hraw'
  show env.IsType family.raw.uvars [] family.raw.type
  rw [gen.family_uvars hfamily]
  exact hgen.rawFamily_isType hfamily

/-- Preserve ordering through the globally flattened constructor phase. -/
private theorem addInductBlockGeneration_constructors_ordered
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    {blockEnv : VEnv}
    (H : AddInductBlockGenerationTrace env env' gen)
    (hgen : gen.WF env blockEnv) (ordT : H.typeEnv.Ordered) :
    H.ctorEnv.Ordered := by
  have hstage : env.stageInductiveTypes source.types = some blockEnv :=
    hgen.blockWF.1.1
  rw [← blockTypeConstants_foldlM_eq_stageInductiveTypes env source,
    H.addTypes] at hstage
  have htypeEnv : H.typeEnv = blockEnv := Option.some.inj hstage
  subst blockEnv
  apply constFold_ordered source.blockConstructorConstants ordT ?_ H.addCtors
  intro ctor hctor
  have hctor' : ctor ∈ gen.flatCtors.map (·.ctor.raw) := by
    rw [gen.flatCtors_map_raw]
    exact hctor
  obtain ⟨constructor, hconstructor, rfl⟩ := List.mem_map.1 hctor'
  show H.typeEnv.IsType constructor.ctor.raw.uvars []
    constructor.ctor.raw.type
  rw [gen.flatCtor_uvars hconstructor]
  exact hgen.rawCtor_isType hconstructor

/-- Assemble the mutual generation invariant once every raw family and every
globally flattened constructor has been inserted. -/
private theorem addInductBlockGeneration_constructor_generationEnv
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    {blockEnv : VEnv}
    (H : AddInductBlockGenerationTrace env env' gen)
    (hgen : gen.WF env blockEnv) (ordC : H.ctorEnv.Ordered) :
    BlockGenerationEnv gen H.ctorEnv := by
  obtain ⟨hleET, hfamilyLookup, -⟩ :=
    ctorFold_spec source.blockTypeConstants H.addTypes
  obtain ⟨hleTC, hctorLookup, -⟩ :=
    ctorFold_spec source.blockConstructorConstants H.addCtors
  have hstage : env.stageInductiveTypes source.types = some blockEnv :=
    hgen.blockWF.1.1
  rw [← blockTypeConstants_foldlM_eq_stageInductiveTypes env source,
    H.addTypes] at hstage
  have htypeEnv : H.typeEnv = blockEnv := Option.some.inj hstage
  rw [htypeEnv] at hleET hfamilyLookup hleTC
  have hfamilies : ∀ family ∈ gen.families,
      H.ctorEnv.constants family.raw.name =
        some family.raw.toVConstant := by
    intro family hfamily
    apply hleTC.constants
    apply hfamilyLookup family.raw.toVConstVal
    simp only [VInductDecl.blockTypeConstants, List.mem_map]
    refine ⟨family.raw, ?_, rfl⟩
    rw [← gen.families_map_raw]
    exact List.mem_map.2 ⟨family, hfamily, rfl⟩
  have hctors : ∀ constructor ∈ gen.flatCtors,
      H.ctorEnv.constants constructor.ctor.raw.name =
        some constructor.ctor.raw.toVConstant := by
    intro constructor hconstructor
    apply hctorLookup constructor.ctor.raw
    rw [← gen.flatCtors_map_raw]
    exact List.mem_map.2 ⟨constructor, hconstructor, rfl⟩
  exact hgen.toBlockGenerationEnv (hleET.trans hleTC) hleTC ordC
    hfamilies hctors

/-- Preserve ordering while inserting the family-indexed recursor list. -/
private theorem addInductBlockGeneration_recursors_ordered
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen)
    (S : BlockGenerationEnv gen H.ctorEnv) :
    H.recEnv.Ordered := by
  apply constFold_ordered gen.recursors S.ord ?_ H.addRecs
  intro recursor hrecursor
  simp only [BlockGenerationChecked.recursors, List.mem_map] at hrecursor
  obtain ⟨family, hfamily, rfl⟩ := hrecursor
  exact S.recursor_wf hfamily

/-- The recursor fold stores the exact generated recursor selected by every
family ordinal. -/
private theorem addInductBlockGeneration_recursor_lookup
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen)
    {family : NormalizedFamily} (hfamily : family ∈ gen.families) :
    H.recEnv.constants (.str family.raw.name "rec") =
      some (gen.recursor family) := by
  let recursor : VConstVal :=
    ⟨gen.recursor family, .str family.raw.name "rec"⟩
  have hrecursor : recursor ∈ gen.recursors :=
    List.mem_map.2 ⟨family, hfamily, rfl⟩
  simpa [recursor] using
    (ctorFold_spec gen.recursors H.addRecs).2.1 recursor hrecursor

/-- Preserve ordering through the block-wide generated-rule fold. -/
private theorem addInductBlockGeneration_rules_ordered
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    (H : AddInductBlockGenerationTrace env env' gen)
    (S : BlockGenerationEnv gen H.recEnv) : env'.Ordered := by
  have hout := S.generatedRulesFold_ordered
    (fun family hfamily =>
      addInductBlockGeneration_recursor_lookup H hfamily)
  simpa only [H.addRules] using hout

/-- The block-wide transaction preserves ordering through all families,
constructors, family-indexed recursors, and flattened iota rules. -/
theorem addInductBlockGeneration_WF
    {source : VInductDecl} {gen : source.BlockGenerationChecked}
    {blockEnv : VEnv}
    (henv : env.Ordered) (hgen : gen.WF env blockEnv)
    (hadd : addInductBlockGeneration env gen = some env') :
    env'.Ordered := by
  rcases addInductBlockGeneration_trace hadd with ⟨H⟩
  have ordT : H.typeEnv.Ordered :=
    addInductBlockGeneration_families_ordered H henv hgen
  have ordC : H.ctorEnv.Ordered :=
    addInductBlockGeneration_constructors_ordered H hgen ordT
  have S : BlockGenerationEnv gen H.ctorEnv :=
    addInductBlockGeneration_constructor_generationEnv H hgen ordC
  have ordR : H.recEnv.Ordered :=
    addInductBlockGeneration_recursors_ordered H S
  have hleCR := (ctorFold_spec gen.recursors H.addRecs).1
  have SR : BlockGenerationEnv gen H.recEnv :=
    S.mono hleCR ordR
  exact addInductBlockGeneration_rules_ordered H SR

/-- Preserve ordering across the raw family insertion, the first generated
component of an inductive transaction. -/
private theorem addInductGeneration_family_ordered {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    (henv : env.Ordered) (hgen : gen.WF env) : H.typeEnv.Ordered := by
  have hfamilyWF : gen.block.sourceType.toVConstant.WF env := by
    show env.IsType gen.block.sourceType.uvars []
      gen.block.sourceType.type
    rw [gen.block.sourceType_uvars_eq]
    exact hgen.rawFamily_isType
  exact .const henv hfamilyWF H.addType

/-- Preserve ordering across the complete raw constructor fold. The proof is
uniform in the source list, so the empty-constructor case is the ordinary
zero-step fold rather than a separate preservation path. -/
private theorem addInductGeneration_constructors_ordered
    {source : VInductDecl} {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    (hgen : gen.WF env) (ordT : H.typeEnv.Ordered) :
    H.ctorEnv.Ordered := by
  have hctorWF :
      ∀ c ∈ gen.block.sourceType.ctors,
        c.toVConstant.WF H.typeEnv := by
    intro c hc
    have hc' : c ∈ gen.block.ctorPairs.map (·.raw) := by
      rw [gen.rawCtors_eq]
      exact hc
    obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.1 hc'
    show H.typeEnv.IsType ctor.raw.uvars [] ctor.raw.type
    rw [gen.ctor_uvars_eq hctor]
    exact hgen.rawCtor_isType H.addType hctor
  exact constFold_ordered gen.block.sourceType.ctors ordT hctorWF
    H.addCtors

/-- Assemble the mixed-generation invariant after the exact family and
constructor components have been inserted. -/
private theorem addInductGeneration_constructor_generationEnv
    {source : VInductDecl} {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    (hgen : gen.WF env) (ordC : H.ctorEnv.Ordered) :
    GenerationEnv gen H.ctorEnv := by
  obtain ⟨hleTC, hctorLookup, -⟩ :=
    ctorFold_spec gen.block.sourceType.ctors H.addCtors
  have hlePreT := addConst_le H.addType
  have hlePreC := hlePreT.trans hleTC
  have hfamily :
      H.ctorEnv.constants gen.block.sourceType.name =
        some gen.block.sourceType.toVConstant :=
    hleTC.constants (addConst_self H.addType)
  have hctors :
      ∀ ctor ∈ gen.block.ctorPairs,
        H.ctorEnv.constants ctor.raw.name =
          some ctor.raw.toVConstant := by
    intro ctor hctor
    apply hctorLookup ctor.raw
    rw [← gen.rawCtors_eq]
    exact List.mem_map.2 ⟨ctor, hctor, rfl⟩
  exact hgen.toGenerationEnv H.addType hlePreC hleTC ordC hfamily
    hctors

/-- Preserve ordering across the single generated recursor component. -/
private theorem addInductGeneration_recursor_ordered
    {source : VInductDecl} {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    (S : GenerationEnv gen H.ctorEnv) : H.recEnv.Ordered :=
  .const S.ord S.recursor_wf H.addRec

/-- Preserve ordering across the generated rule fold. Empty families supply
no rules, so this is again the same zero-step component fold used generally. -/
private theorem addInductGeneration_rules_ordered
    {source : VInductDecl} {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    (S : GenerationEnv gen H.recEnv) : env'.Ordered := by
  have hout :=
    S.generatedRulesFold_ordered (addConst_self H.addRec)
  simpa only [H.addRules] using hout

/-- The normalized transaction preserves environment ordering from the
semantic raw/view generation certificate. Stored constants are checked in
their exact raw syntax; the mixed recursor and rules are checked only after
all raw constants are present. -/
theorem addInductGeneration_WF {source : VInductDecl}
    {gen : source.GenerationChecked}
    (henv : env.Ordered) (hgen : gen.WF env)
    (hadd : addInductGeneration env gen = some env') :
    env'.Ordered := by
  rcases addInductGeneration_trace hadd with ⟨H⟩
  have ordT : H.typeEnv.Ordered :=
    addInductGeneration_family_ordered H henv hgen
  have ordC : H.ctorEnv.Ordered :=
    addInductGeneration_constructors_ordered H hgen ordT
  have S : GenerationEnv gen H.ctorEnv :=
    addInductGeneration_constructor_generationEnv H hgen ordC
  have ordR : H.recEnv.Ordered :=
    addInductGeneration_recursor_ordered H S
  have hleCR := addConst_le H.addRec
  have SR : GenerationEnv gen H.recEnv :=
    S.mono hleCR ordR
  exact addInductGeneration_rules_ordered H SR

/-- Recover the ordinary normalized transaction trace from the
proof-carrying public entry point.  The conclusion contains only Theory data;
the producer that established the certificate is deliberately absent. -/
theorem addInductCertified_trace {source : VInductDecl}
    {certificate : source.GenerationCertificate env}
    (hadd : addInductCertified env certificate = some env') :
    Nonempty
      (AddInductGenerationTrace env env' certificate.generation) := by
  apply addInductGeneration_trace
  simpa only [addInductCertified_eq_addInductGeneration] using hadd

/-- The proof-carrying wrapper has the same atomic success/failure behavior as
the underlying normalized transaction. -/
theorem addInductCertified_atomic {source : VInductDecl}
    (env : VEnv) (certificate : source.GenerationCertificate env) :
    addInductCertified env certificate = none ∨
      ∃ env', addInductCertified env certificate = some env' ∧
        Nonempty
          (AddInductGenerationTrace env env' certificate.generation) := by
  simpa only [addInductCertified_eq_addInductGeneration] using
    addInductGeneration_atomic env certificate.generation

/-- Ordering preservation for the public certified transaction.  Its
semantic premise is carried by the certificate rather than repeated at every
call site. -/
theorem addInductCertified_WF {source : VInductDecl}
    {certificate : source.GenerationCertificate env}
    (henv : env.Ordered)
    (hadd : addInductCertified env certificate = some env') :
    env'.Ordered := by
  apply addInductGeneration_WF henv certificate.wf
  simpa only [addInductCertified_eq_addInductGeneration] using hadd

/-- Recover the exact block-wide transaction phases through the public
proof-carrying entry point. -/
theorem addInductBlockCertified_trace {source : VInductDecl}
    {certificate : source.BlockGenerationCertificate env}
    (hadd : addInductBlockCertified env certificate = some env') :
    Nonempty
      (AddInductBlockGenerationTrace env env'
        certificate.generation) := by
  apply addInductBlockGeneration_trace
  simpa only [addInductBlockCertified_eq_addInductBlockGeneration] using hadd

/-- The public block certificate wrapper has the same atomic behavior as its
underlying block transaction. -/
theorem addInductBlockCertified_atomic {source : VInductDecl}
    (env : VEnv) (certificate : source.BlockGenerationCertificate env) :
    addInductBlockCertified env certificate = none ∨
      ∃ env', addInductBlockCertified env certificate = some env' ∧
        Nonempty
          (AddInductBlockGenerationTrace env env'
            certificate.generation) := by
  simpa only [addInductBlockCertified_eq_addInductBlockGeneration] using
    addInductBlockGeneration_atomic env certificate.generation

/-- Ordering preservation for the public proof-carrying mutual-block
transaction. -/
theorem addInductBlockCertified_WF {source : VInductDecl}
    {certificate : source.BlockGenerationCertificate env}
    (henv : env.Ordered)
    (hadd : addInductBlockCertified env certificate = some env') :
    env'.Ordered := by
  apply addInductBlockGeneration_WF henv certificate.wf
  simpa only [addInductBlockCertified_eq_addInductBlockGeneration] using hadd

#guard_named_axioms Ix.Theory.Named.VEnv.addInductBlockGeneration_trace [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductBlockGeneration_atomic [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.AddInductBlockGenerationTrace.le [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.AddInductBlockGenerationTrace.family_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.AddInductBlockGenerationTrace.ctor_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.AddInductBlockGenerationTrace.rec_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.AddInductBlockGenerationTrace.rule_mem [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductBlockGeneration_WF [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductBlockCertified_eq_addInductBlockGeneration [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductBlockCertified_trace [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductBlockCertified_atomic [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductBlockCertified_WF [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductGeneration_trace [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductGeneration_atomic [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.AddInductGenerationTrace.le [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.AddInductGenerationTrace.family_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.AddInductGenerationTrace.ctor_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.AddInductGenerationTrace.rec_lookup [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.AddInductGenerationTrace.rule_mem [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductGeneration_WF [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductCertified_eq_addInductGeneration [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductCertified_trace [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductCertified_atomic [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInductCertified_WF [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInduct_eq_addInductBlockGeneration [propext, Classical.choice, Quot.sound]

/-- Elimination of a successful `addInduct` transaction into its stable
consumer-facing postcondition. -/
theorem addInduct_success (hadd : addInduct env decl = some env') :
    AddInductSuccess env env' decl := by
  unfold addInduct at hadd
  obtain ⟨generation, hgeneration, hgen⟩ :=
    Option.bind_eq_some_iff.1 hadd
  rcases addInductBlockGeneration_trace hgen with ⟨H⟩
  refine {
    generation := ⟨generation, hgeneration⟩
    accepted := by simp [stage3, hgeneration]
    le := H.le
    type_fresh := ?_
    type_lookup := ?_
    ctor_fresh := ?_
    ctor_lookup := ?_
    rec_fresh := ?_
    rec_lookup := ?_
    rule_mem := ?_
  }
  · intro ty hty
    exact H.family_fresh hty
  · intro ty hty
    exact H.family_lookup hty
  · intro ty hty c hc
    apply H.ctor_fresh
    simp only [VInductDecl.blockConstructorConstants, List.mem_flatMap]
    exact ⟨ty, hty, hc⟩
  · intro ty hty c hc
    apply H.ctor_lookup
    simp only [VInductDecl.blockConstructorConstants, List.mem_flatMap]
    exact ⟨ty, hty, hc⟩
  · intro generation' hgeneration' recursor hrecursor
    have heq : generation = generation' :=
      Option.some.inj (hgeneration.symm.trans hgeneration')
    exact H.rec_fresh (by simpa [heq] using hrecursor)
  · intro generation' hgeneration' recursor hrecursor
    have heq : generation = generation' :=
      Option.some.inj (hgeneration.symm.trans hgeneration')
    exact H.rec_lookup (by simpa [heq] using hrecursor)
  · intro generation' hgeneration' df hdf
    have heq : generation = generation' :=
      Option.some.inj (hgeneration.symm.trans hgeneration')
    exact H.rule_mem (by simpa [heq] using hdf)

/-- Successful inductive addition is monotone. -/
theorem addInduct_le (hadd : addInduct env decl = some env') : env ≤ env' :=
  (addInduct_success hadd).le

/-- Successful environment extension exposes the exact block descriptor that
drove generation, so consumers never need to re-run acceptance analysis. -/
theorem addInduct_generation (hadd : addInduct env decl = some env') :
    ∃ generation, decl.identityBlockGeneration? = some generation :=
  (addInduct_success hadd).generation

theorem addInduct_type_fresh (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) : env.constants ty.name = none :=
  (addInduct_success hadd).type_fresh ty hty

theorem addInduct_type_lookup (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) : env'.constants ty.name = some ty.toVConstant :=
  (addInduct_success hadd).type_lookup ty hty

theorem addInduct_ctor_fresh (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) (hc : c ∈ ty.ctors) : env.constants c.name = none :=
  (addInduct_success hadd).ctor_fresh ty hty c hc

theorem addInduct_ctor_lookup (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) (hc : c ∈ ty.ctors) :
    env'.constants c.name = some c.toVConstant :=
  (addInduct_success hadd).ctor_lookup ty hty c hc

theorem addInduct_rec_fresh (hadd : addInduct env decl = some env')
    {generation : decl.BlockGenerationChecked}
    (hgeneration : decl.identityBlockGeneration? = some generation)
    {recursor : VConstVal} (hrecursor : recursor ∈ generation.recursors) :
    env.constants recursor.name = none :=
  (addInduct_success hadd).rec_fresh generation hgeneration recursor hrecursor

theorem addInduct_rec_lookup (hadd : addInduct env decl = some env')
    {generation : decl.BlockGenerationChecked}
    (hgeneration : decl.identityBlockGeneration? = some generation)
    {recursor : VConstVal} (hrecursor : recursor ∈ generation.recursors) :
    env'.constants recursor.name = some recursor.toVConstant :=
  (addInduct_success hadd).rec_lookup generation hgeneration recursor hrecursor

theorem addInduct_rule_mem (hadd : addInduct env decl = some env')
    {generation : decl.BlockGenerationChecked}
    (hgeneration : decl.identityBlockGeneration? = some generation)
    (hdf : df ∈ generation.generatedRules) :
    env'.defeqs df :=
  (addInduct_success hadd).rule_mem generation hgeneration df hdf

/-- `addInduct` is an all-or-nothing transaction: every evaluation either
returns no environment or returns an environment satisfying the complete
success contract. -/
theorem addInduct_atomic :
    addInduct env decl = none ∨
      ∃ env', addInduct env decl = some env' ∧ AddInductSuccess env env' decl := by
  cases hadd : addInduct env decl with
  | none => exact .inl rfl
  | some env' => exact .inr ⟨env', rfl, addInduct_success hadd⟩

/-- The Stage-3 guard is an exact early-rejection condition. -/
theorem addInduct_eq_none_of_stage3_false (h : decl.stage3 = false) :
    addInduct env decl = none := by
  have hgeneration : decl.identityBlockGeneration? = none :=
    identityBlockGeneration?_eq_none_iff.2 h
  simp [addInduct, hgeneration]

/-- A pre-existing type name rejects the transaction before any generated
object is observable. -/
theorem addInduct_eq_none_of_type_present (hty : ty ∈ decl.types)
    (hcontains : env.contains ty.name) : addInduct env decl = none := by
  cases hadd : addInduct env decl with
  | none => rfl
  | some env' =>
    have hfresh := (addInduct_success hadd).type_fresh ty hty
    obtain ⟨ci, hci⟩ := hcontains
    rw [hci] at hfresh
    contradiction

/-- A pre-existing constructor name rejects the complete transaction. The
proof is stated through the stable success certificate, not the position of
the constructor in the internal `foldlM`. -/
theorem addInduct_eq_none_of_ctor_present (hty : ty ∈ decl.types)
    (hctor : ctor ∈ ty.ctors) (hcontains : env.contains ctor.name) :
    addInduct env decl = none := by
  cases hadd : addInduct env decl with
  | none => rfl
  | some env' =>
    have hfresh := (addInduct_success hadd).ctor_fresh ty hty ctor hctor
    obtain ⟨ci, hci⟩ := hcontains
    rw [hci] at hfresh
    contradiction

/-- A pre-existing generated recursor name likewise rejects the complete
transaction. -/
theorem addInduct_eq_none_of_rec_present
    {generation : decl.BlockGenerationChecked}
    (hgeneration : decl.identityBlockGeneration? = some generation)
    (hrecursor : recursor ∈ generation.recursors)
    (hcontains : env.contains recursor.name) : addInduct env decl = none := by
  cases hadd : addInduct env decl with
  | none => rfl
  | some env' =>
    have success := addInduct_success hadd
    have hfresh := success.rec_fresh generation hgeneration recursor hrecursor
    obtain ⟨ci, hci⟩ := hcontains
    rw [hci] at hfresh
    contradiction

theorem addInduct_WF {generation : decl.BlockGenerationChecked}
    {blockEnv : VEnv} (henv : Ordered env)
    (hgeneration : decl.identityBlockGeneration? = some generation)
    (hgen : generation.WF env blockEnv)
    (hadd : addInduct env decl = some env') : Ordered env' := by
  unfold addInduct at hadd
  rw [hgeneration] at hadd
  exact addInductBlockGeneration_WF henv hgen hadd

end VEnv

/- Mixed raw/view generation must stay within Lean's standard logical
baseline. Guard each proof-critical boundary separately so a dependency change
identifies the first affected layer. -/
#guard_named_axioms Ix.Theory.Named.VInductDecl.Checked.WF.identityGeneration [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.minor_isType [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.minorTypes_onTel [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.familyApp_transport [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.recType_isType [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.recursor_wf [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.ruleCall_hasType [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.rule_WF [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.generatedRules_WF [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.GenerationEnv.generatedRulesFold_ordered [propext, Classical.choice, Quot.sound]

/- The generalized recursive-Pi artifact path must remain within the same
standard logical baseline as the public preservation theorem. These guards
make every proof-critical boundary independently auditable. -/
#guard_named_axioms Ix.Theory.Named.VInductDecl.Stage3Env.recTypeRec_isType [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Stage3Env.recConstRec_wf [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Stage3Env.ruleCallRec_hasType [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Stage3Env.minorAppRec_hasType [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Stage3Env.recRuleAppRec_hasType [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.Stage3Env.ruleRec_WF [propext, Classical.choice, Quot.sound]

/- The indexed-inductive preservation proof stays within Lean's standard
logical axiom baseline. Keep this guard adjacent to the theorem so a new
dependency fails during ordinary module compilation. -/
#guard_named_axioms Ix.Theory.Named.VEnv.addInduct_success [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInduct_generation [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInduct_eq_none_of_ctor_present [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInduct_eq_none_of_rec_present [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.addInduct_WF [propext, Classical.choice, Quot.sound]
