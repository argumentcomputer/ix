/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Kernel.Verify.Audit.AxiomAudit
import Ix.Theory.Named.Typing.InductivePatternWF

open Ix.Theory (VLevel)

/-!
# Structure projections

This module is the consumer-neutral projection boundary.  A projection is
not determined by a structure name and field number alone: universe
instantiations, parameters, the constructor telescope, and the generated
recursor/iota package all affect its meaning.  `VStructureView` retains that
data from the same checked artifact used by inductive generation.

Projection terms are encoded with the generated recursor.  Earlier
projections occur in the motive of a dependent later projection, so one view
determines both the projected term and its dependent result type.  No
projection-function name map or unconstrained metadata witness is involved.
-/

namespace Ix.Theory.Named

open VInductDecl

/-- Instantiate an outermost-first argument list at a fixed offset.

The `k` variables below the substituted telescope remain bound.  Each
argument is lifted past them before it replaces the then-outermost variable.
This is the operation needed to specialize constructor parameters while
retaining the preceding dependent fields. -/
def VExpr.instRevAt : VExpr → List VExpr → Nat → VExpr
  | e, [], _ => e
  | e, a :: as, k => instRevAt (e.inst a (k + as.length)) as k

theorem VExpr.instRevAt_zero (e : VExpr) (args : List VExpr) :
    e.instRevAt args 0 = e.instRev args := by
  induction args generalizing e with
  | nil => rfl
  | cons arg args ih =>
      simp only [VExpr.instRevAt, VExpr.instRev]
      simpa using ih (e := e.inst arg args.length)

private theorem VExpr.instRevAt_closedN (args : List VExpr)
    {C : VExpr} {k : Nat} (hC : C.ClosedN k) :
    C.instRevAt args k = C := by
  induction args generalizing C with
  | nil => rfl
  | cons arg args ih =>
      simp only [VExpr.instRevAt]
      rw [hC.instN_eq (by omega)]
      exact ih hC

private theorem VExpr.instRev_forallE_projection
    (A B : VExpr) (args : List VExpr) :
    VExpr.instRev (.forallE A B) args =
      .forallE (VExpr.instRev A args)
        (VExpr.instRevAt B args 1) := by
  induction args generalizing A B with
  | nil => rfl
  | cons arg args ih =>
      simp only [VExpr.instRev, VExpr.inst]
      rw [ih]
      congr 1
      simp only [VExpr.instRevAt]
      rw [show 1 + args.length = args.length + 1 by omega]

private theorem VExpr.instRevAt_forallE_projection
    (A B : VExpr) (args : List VExpr) (k : Nat) :
    VExpr.instRevAt (.forallE A B) args k =
      .forallE (VExpr.instRevAt A args k)
        (VExpr.instRevAt B args (k + 1)) := by
  induction args generalizing A B with
  | nil => rfl
  | cons arg args ih =>
      simp only [VExpr.instRevAt, VExpr.inst]
      rw [ih]
      congr 1
      rw [show k + args.length + 1 = k + 1 + args.length by omega]

private theorem VExpr.instRevAt_forallN_projection
    (As : List VExpr) (B : VExpr) (args : List VExpr) (k : Nat) :
    VExpr.instRevAt (VExpr.forallN As B) args k =
      VExpr.forallN
        (As.zipIdx k |>.map fun x => x.1.instRevAt args x.2)
        (B.instRevAt args (k + As.length)) := by
  induction As generalizing k with
  | nil => rfl
  | cons A As ih =>
      simp only [VExpr.forallN, VExpr.instRevAt_forallE_projection,
        List.zipIdx, List.map_cons, List.length_cons]
      rw [ih]
      rw [show k + 1 + As.length = k + (As.length + 1) by omega]

theorem VExpr.instRev_forallN_projection
    (As : List VExpr) (B : VExpr) (args : List VExpr) :
    VExpr.instRev (VExpr.forallN As B) args =
      VExpr.forallN
        (As.zipIdx.map fun x => x.1.instRevAt args x.2)
        (B.instRevAt args As.length) := by
  cases As with
  | nil => simp [VExpr.forallN, VExpr.instRevAt_zero]
  | cons A As =>
      simp only [VExpr.forallN, VExpr.instRev_forallE_projection,
        List.zipIdx, List.map_cons, List.length_cons]
      rw [VExpr.instRevAt_forallN_projection]
      rw [VExpr.instRevAt_zero]
      congr 2
      rw [Nat.add_comm]

/-- Consume a syntactic prefix of dependent `forall` binders, instantiating
them outermost-first. -/
def VExpr.consumeForalls? : VExpr → List VExpr → Option VExpr
  | e, [] => some e
  | .forallE _ body, arg :: args => consumeForalls? (body.inst arg) args
  | _, _ :: _ => none

theorem VExpr.consumeForalls?_append (e : VExpr)
    (left right : List VExpr) :
    e.consumeForalls? (left ++ right) =
      (e.consumeForalls? left).bind fun cursor =>
        cursor.consumeForalls? right := by
  induction left generalizing e with
  | nil => rfl
  | cons arg left ih =>
      cases e <;> simp [VExpr.consumeForalls?, ih]

theorem VExpr.instTelN_getElem? (arg : VExpr) (fields : List VExpr)
    (k i : Nat) :
    (VExpr.instTelN arg fields k)[i]? =
      fields[i]?.map fun field => field.inst arg (k + i) := by
  induction fields generalizing k i with
  | nil => simp [VExpr.instTelN]
  | cons field fields ih =>
      cases i with
      | zero => simp [VExpr.instTelN]
      | succ i =>
          simp only [VExpr.instTelN, List.getElem?_cons_succ]
          simpa only [Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (k + 1) i

/-- Consuming `args` from a telescope exposes the next original binder with
exactly those arguments substituted. -/
theorem VExpr.consumeForalls?_forallN_domain
    (fields : List VExpr) (result : VExpr) (args : List VExpr)
    (hlen : args.length < fields.length) :
    ∃ field body,
      fields[args.length]? = some field ∧
      VExpr.consumeForalls? (VExpr.forallN fields result) args =
        some (.forallE (field.instRevAt args 0) body) := by
  induction args generalizing fields result with
  | nil =>
      cases fields with
      | nil => simp at hlen
      | cons field fields =>
          exact ⟨field, VExpr.forallN fields result, rfl, rfl⟩
  | cons arg args ih =>
      cases fields with
      | nil => simp at hlen
      | cons field fields =>
          have hlen' : args.length <
              (VExpr.instTelN arg fields 0).length := by
            simpa [VExpr.instTelN_length] using hlen
          obtain ⟨field', body, hfield', hconsume⟩ :=
            ih (VExpr.instTelN arg fields 0)
              (result.inst arg fields.length) hlen'
          rw [VExpr.instTelN_getElem?] at hfield'
          obtain ⟨original, horiginal, rfl⟩ := Option.map_eq_some_iff.1 hfield'
          refine ⟨original, body, by simpa using horiginal, ?_⟩
          simp only [VExpr.forallN, VExpr.consumeForalls?,
            VExpr.instN_forallN]
          simp only [Nat.zero_add]
          simpa only [VExpr.instRevAt, Nat.zero_add] using hconsume

@[simp] theorem VExpr.instL_instRevAt (e : VExpr) (as : List VExpr)
    (k : Nat) :
    (e.instRevAt as k).instL ls =
      (e.instL ls).instRevAt (as.map (VExpr.instL ls)) k := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih =>
      simp only [VExpr.instRevAt, List.map_cons]
      simpa only [VExpr.instL_instN, List.length_map] using
        ih (e := e.inst a (k + as.length))

private theorem VExpr.instL_lamN_projection (ls : List VLevel) :
    ∀ (As : List VExpr) (e : VExpr),
      (VExpr.lamN As e).instL ls =
        VExpr.lamN (As.map (VExpr.instL ls)) (e.instL ls)
  | [], _ => rfl
  | _ :: As, e => by
      simp only [VExpr.lamN, VExpr.instL, List.map_cons]
      rw [VExpr.instL_lamN_projection ls As e]

private theorem VExpr.liftN_lamN_projection (n : Nat) :
    ∀ (As : List VExpr) (e : VExpr) (k : Nat),
      (VExpr.lamN As e).liftN n k =
        VExpr.lamN (VExpr.liftTelN n As k)
          (e.liftN n (k + As.length))
  | [], _, _ => rfl
  | _ :: As, e, k => by
      simp only [VExpr.lamN, VExpr.liftN, VExpr.liftTelN,
        List.length_cons]
      rw [VExpr.liftN_lamN_projection n As e (k + 1)]
      rw [show k + 1 + As.length = k + (As.length + 1) by omega]

private theorem VExpr.instN_lamN_projection (a : VExpr) :
    ∀ (As : List VExpr) (e : VExpr) (k : Nat),
      (VExpr.lamN As e).inst a k =
        VExpr.lamN (VExpr.instTelN a As k)
          (e.inst a (k + As.length))
  | [], _, _ => rfl
  | _ :: As, e, k => by
      simp only [VExpr.lamN, VExpr.inst, VExpr.instTelN,
        List.length_cons]
      rw [VExpr.instN_lamN_projection a As e (k + 1)]
      rw [show k + 1 + As.length = k + (As.length + 1) by omega]

private theorem VExpr.liftN_lift_projection (e : VExpr) (n k : Nat) :
    e.lift.liftN n (k + 1) = (e.liftN n k).lift :=
  (VExpr.lift_liftN' e k).symm

private theorem VExpr.liftN_liftAt_projection
    (e : VExpr) (n k i : Nat) :
    (e.liftN 1 i).liftN n (k + 1 + i) =
      (e.liftN n (k + i)).liftN 1 i := by
  symm
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    VExpr.liftN_liftN_comm e 1 n i (k + i) (by omega)

private theorem VExpr.liftTelN_liftAt_projection (As : List VExpr)
    (n k i : Nat) :
    VExpr.liftTelN n (VExpr.liftTelN 1 As i) (k + 1 + i) =
      VExpr.liftTelN 1 (VExpr.liftTelN n As (k + i)) i := by
  induction As generalizing i with
  | nil => rfl
  | cons A As ih =>
      simp only [VExpr.liftTelN]
      rw [VExpr.liftN_liftAt_projection A n k i]
      congr 1
      simpa only [Nat.add_assoc] using ih (i + 1)

private theorem VExpr.liftTelN_lift_projection (As : List VExpr)
    (n k : Nat) :
    VExpr.liftTelN n (VExpr.liftTelN 1 As 0) (k + 1) =
      VExpr.liftTelN 1 (VExpr.liftTelN n As k) 0 := by
  simpa using VExpr.liftTelN_liftAt_projection As n k 0

private theorem VExpr.instN_liftAt_projection
    (e a : VExpr) (k i : Nat) :
    (e.liftN 1 i).inst a (k + 1 + i) =
      (e.inst a (k + i)).liftN 1 i := by
  symm
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    VExpr.liftN_instN_lo 1 e a (k + i) i (by omega)

private theorem VExpr.instTelN_liftAt_projection (As : List VExpr)
    (a : VExpr) (k i : Nat) :
    VExpr.instTelN a (VExpr.liftTelN 1 As i) (k + 1 + i) =
      VExpr.liftTelN 1 (VExpr.instTelN a As (k + i)) i := by
  induction As generalizing i with
  | nil => rfl
  | cons A As ih =>
      simp only [VExpr.liftTelN, VExpr.instTelN]
      rw [VExpr.instN_liftAt_projection A a k i]
      congr 1
      simpa only [Nat.add_assoc] using ih (i + 1)

private theorem VExpr.instTelN_lift_projection (As : List VExpr)
    (a : VExpr) (k : Nat) :
    VExpr.instTelN a (VExpr.liftTelN 1 As 0) (k + 1) =
      VExpr.liftTelN 1 (VExpr.instTelN a As k) 0 := by
  simpa using VExpr.instTelN_liftAt_projection As a k 0

private theorem VExpr.instN_instRevAt_lift_projection
    (e : VExpr) (args : List VExpr) (a : VExpr) (i : Nat) :
    ((e.liftN 1 i).instRevAt args (i + 1)).inst a i =
      e.instRevAt args i := by
  induction args generalizing e with
  | nil => exact VExpr.inst_liftN1 e a i
  | cons arg args ih =>
      simp only [VExpr.instRevAt]
      rw [show i + 1 + args.length = args.length + 1 + i by omega,
        VExpr.instN_liftAt_projection e arg args.length i]
      simpa only [Nat.add_comm] using
        ih (e := e.inst arg (args.length + i))

private theorem VExpr.instTelN_instRevAt_lift_projection
    (fields : List VExpr) (args : List VExpr) (a : VExpr)
    (start : Nat) :
    VExpr.instTelN a
        ((VExpr.liftTelN 1 fields start).zipIdx (start + 1) |>.map
          fun x => x.1.instRevAt args x.2)
        start =
      (fields.zipIdx start |>.map
        fun x => x.1.instRevAt args x.2) := by
  induction fields generalizing start with
  | nil => rfl
  | cons field fields ih =>
      simp only [VExpr.liftTelN, List.zipIdx, List.map_cons,
        VExpr.instTelN]
      rw [VExpr.instN_instRevAt_lift_projection]
      congr 1
      simpa only [Nat.add_assoc] using ih (start + 1)

private theorem VExpr.inst_liftN_top (e a : VExpr) (n : Nat) :
    (e.liftN (n + 1)).inst a n = e.liftN n := by
  rw [← VExpr.liftN'_liftN' (e := e) (n1 := n) (n2 := 1)
    (k1 := 0) (k2 := n) (Nat.zero_le _) (by omega)]
  exact VExpr.inst_liftN (e.liftN n) a

private theorem VExpr.instRevAt_liftN_len (args : List VExpr)
    (e : VExpr) (k : Nat) :
    (e.liftN (k + args.length)).instRevAt args k = e.liftN k := by
  induction args with
  | nil => rfl
  | cons arg args ih =>
      simp only [List.length_cons, VExpr.instRevAt]
      rw [show k + (args.length + 1) = (k + args.length) + 1 by omega,
        VExpr.inst_liftN_top]
      exact ih

private theorem VExpr.instRevAt_bvar_lt_cons (args : List VExpr)
    (arg : VExpr) (k i : Nat) (hi : i < k + args.length) :
    (VExpr.bvar i).instRevAt (arg :: args) k =
      (VExpr.bvar i).instRevAt args k := by
  simp only [VExpr.instRevAt]
  congr 1
  simp [VExpr.inst, VExpr.instVar, hi]

private theorem VExpr.map_instRevAt_bvarRevRange
    (args : List VExpr) (k : Nat) :
    (VExpr.bvarRevRange k args.length).map
        (fun e => e.instRevAt args k) =
      args.map (VExpr.liftN k) := by
  induction args with
  | nil => rfl
  | cons arg args ih =>
      simp only [List.length_cons, VExpr.bvarRevRange,
        List.map_cons]
      congr 1
      · simp only [VExpr.instRevAt]
        rw [show (VExpr.bvar (k + args.length)).inst arg
              (k + args.length) = arg.liftN (k + args.length) by
            simp [VExpr.inst, VExpr.instVar]]
        exact VExpr.instRevAt_liftN_len args arg k
      · rw [← ih]
        apply List.map_congr_left
        intro e he
        obtain ⟨i, rfl, _, hi⟩ := VExpr.mem_bvarRevRange he
        exact VExpr.instRevAt_bvar_lt_cons args arg k i (by omega)

private theorem VExpr.instRevAt_appN_projection
    (f : VExpr) (es : List VExpr) (args : List VExpr) (k : Nat) :
    (VExpr.appN f es).instRevAt args k =
      VExpr.appN (f.instRevAt args k)
        (es.map fun e => e.instRevAt args k) := by
  induction args generalizing f es with
  | nil => simp [VExpr.instRevAt, List.map_id']
  | cons arg args ih =>
      simp only [VExpr.instRevAt, VExpr.instN_appN]
      rw [ih]
      simp only [List.map_map, Function.comp_def]

private theorem VExpr.map_instRevAt_closedN (args es : List VExpr)
    (k : Nat) (hclosed : ∀ e ∈ es, e.ClosedN k) :
    es.map (fun e => e.instRevAt args k) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons]
      rw [VExpr.instRevAt_closedN args (hclosed e (.head _))]
      congr 1
      exact ih (fun e he => hclosed e (.tail _ he))

private theorem VExpr.map_instN_closedN (a : VExpr) (es : List VExpr)
    (k : Nat) (hclosed : ∀ e ∈ es, e.ClosedN k) :
    es.map (fun e => e.inst a k) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons]
      rw [(hclosed e (.head _)).instN_eq (Nat.le_refl _)]
      congr 1
      exact ih (fun e he => hclosed e (.tail _ he))

private theorem VExpr.map_instN_liftN_top
    (es : List VExpr) (a : VExpr) (n : Nat) :
    (es.map (VExpr.liftN (n + 1))).map
        (fun e => e.inst a n) =
      es.map (VExpr.liftN n) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  exact VExpr.inst_liftN_top e a n

private theorem VExpr.projectionMinorBody_shape
    (constructorName : Name) (levels : List VLevel)
    (params : List VExpr) (m : Nat) (typeFn : VExpr) :
    ((VExpr.appN (.bvar m)
          [VExpr.appN (.const constructorName levels)
            (VExpr.bvarRevRange (m + 1) params.length ++
              VExpr.bvarRevRange 0 m)]).instRevAt params (m + 1)).inst
        typeFn m =
      .app (typeFn.liftN m)
        (VExpr.appN (.const constructorName levels)
          (params.map (VExpr.liftN m) ++
            VExpr.bvarRevRange 0 m)) := by
  have hmotiveR : (VExpr.bvar m).instRevAt params (m + 1) =
      .bvar m := VExpr.instRevAt_closedN params (by
        exact Nat.lt_succ_self m)
  have hconstR : (VExpr.const constructorName levels).instRevAt
      params (m + 1) = .const constructorName levels :=
    VExpr.instRevAt_closedN params (by trivial)
  have hfieldsR := VExpr.map_instRevAt_closedN params
    (VExpr.bvarRevRange 0 m) (m + 1)
    (bvarRevRange_closedN m 0 (m + 1) (by omega))
  have hmotiveI : (VExpr.bvar m).inst typeFn m =
      typeFn.liftN m := by simp [VExpr.inst, VExpr.instVar]
  have hconstI : (VExpr.const constructorName levels).inst typeFn m =
      .const constructorName levels := by rfl
  have hparamsI := VExpr.map_instN_liftN_top params typeFn m
  have hfieldsI := VExpr.map_instN_closedN typeFn
    (VExpr.bvarRevRange 0 m) m
    (bvarRevRange_closedN m 0 m (by omega))
  rw [VExpr.instRevAt_appN_projection, hmotiveR]
  simp only [List.map_singleton]
  rw [VExpr.instRevAt_appN_projection, hconstR, List.map_append,
    VExpr.map_instRevAt_bvarRevRange, hfieldsR]
  rw [VExpr.instN_appN, hmotiveI]
  simp only [List.map_singleton]
  rw [VExpr.instN_appN, hconstI, List.map_append,
    hparamsI, hfieldsI]
  rfl

private theorem VExpr.projectionMajorTail_shape
    (familyName : Name) (levels : List VLevel)
    (params : List VExpr) (typeFn : VExpr) :
    (((VExpr.forallE
          (VExpr.appN (.const familyName levels)
            (VExpr.bvarRevRange 2 params.length))
          (.app (.appN (.bvar 2) []) (.bvar 0))).instRevAt
        params 2).inst typeFn 1) =
      VExpr.forallE
        (VExpr.appN (.const familyName levels)
          (params.map (VExpr.liftN 1)))
        (.app (typeFn.liftN 2) (.bvar 0)) := by
  have hconstR : (VExpr.const familyName levels).instRevAt
      params 2 = .const familyName levels :=
    VExpr.instRevAt_closedN params (by trivial)
  have hbodyR :
      (VExpr.app (VExpr.appN (.bvar 2) []) (.bvar 0)).instRevAt
          params 3 =
        VExpr.app (VExpr.appN (.bvar 2) []) (.bvar 0) :=
    VExpr.instRevAt_closedN params (by
      change 2 < 3 ∧ 0 < 3
      omega)
  rw [VExpr.instRevAt_forallE_projection,
    VExpr.instRevAt_appN_projection, hconstR,
    VExpr.map_instRevAt_bvarRevRange, hbodyR]
  simp only [VExpr.inst]
  congr 1
  · rw [VExpr.instN_appN]
    have hconstI : (VExpr.const familyName levels).inst typeFn 1 =
        .const familyName levels := by rfl
    rw [hconstI, VExpr.map_instN_liftN_top]

theorem VExpr.liftN_instRevAt (e : VExpr) (as : List VExpr)
    (i k n : Nat) :
    (e.instRevAt as i).liftN n (k + i) =
      (e.liftN n (k + i + as.length)).instRevAt
        (as.map fun a => a.liftN n k) i := by
  induction as generalizing e with
  | nil => simp [VExpr.instRevAt]
  | cons a as ih =>
      simp only [VExpr.instRevAt, List.map_cons]
      rw [ih]
      simp only [List.length_cons, List.length_map]
      rw [show k + i + as.length = k + (i + as.length) by omega,
        VExpr.liftN_instN_hi]
      congr 3 <;> omega

theorem VExpr.instN_instRevAt (e : VExpr) (as : List VExpr)
    (i k : Nat) (a : VExpr) :
    (e.instRevAt as i).inst a (k + i) =
      (e.inst a (k + i + as.length)).instRevAt
        (as.map fun arg => arg.inst a k) i := by
  induction as generalizing e with
  | nil => simp [VExpr.instRevAt]
  | cons arg as ih =>
      simp only [VExpr.instRevAt, List.map_cons]
      rw [ih]
      simp only [List.length_cons, List.length_map]
      rw [show k + i + as.length = k + (i + as.length) by omega,
        VExpr.inst_inst_hi]
      congr 3 <;> omega

/-- A telescope whose entries have the exact retained sort levels. -/
inductive VEnv.OnSortTel (env : VEnv) (U : Nat) :
    List VExpr → List VExpr → List VLevel → Prop where
  | nil : OnSortTel env U Γ [] []
  | cons :
      env.HasType U Γ A (.sort u) →
      OnSortTel env U (A :: Γ) As us →
      OnSortTel env U Γ (A :: As) (u :: us)

private theorem onCtx_levelWFProjection {env : VEnv} {U : Nat} :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) →
      OnCtx Γ fun _ A => A.LevelWF U
  | [], _ => trivial
  | _ :: _, ⟨hΓ, ⟨_, hA⟩⟩ =>
      let hΓ' := onCtx_levelWFProjection hΓ
      ⟨hΓ', (hA.levelWF hΓ').1⟩

/-- Every retained sort selected from a checked sort telescope is a
well-formed universe at the ambient universe bound. -/
theorem VEnv.OnSortTel.sortWF {env : VEnv} {U : Nat}
    : ∀ {Γ : List VExpr} {As : List VExpr} {us : List VLevel},
      OnCtx Γ (env.IsType U) → env.OnSortTel U Γ As us →
      ∀ {i : Nat} {u : VLevel}, us[i]? = some u → u.WF U
  | _, [], [], _, .nil, _, _, h => by simp at h
  | _, _ :: _, _ :: _, hΓ, .cons hA hT, 0, _, h => by
      injection h with h
      subst h
      exact (hA.levelWF (onCtx_levelWFProjection hΓ)).2.2
  | Γ, A :: As, u₀ :: us, hΓ, .cons hA hT, i + 1, u, h => by
      exact VEnv.OnSortTel.sortWF (env := env) (U := U)
        (Γ := A :: Γ) (As := As) (us := us)
        ⟨hΓ, ⟨u₀, hA⟩⟩ hT (by simpa using h)

private theorem VEnv.OnTel.monoProjection {env env' : VEnv}
    (henv : env ≤ env') (H : env.OnTel U Γ As) : env'.OnTel U Γ As := by
  induction As generalizing Γ with
  | nil => trivial
  | cons _ _ ih =>
      exact ⟨H.1.mono henv, ih H.2⟩

theorem VEnv.OnSortTel.mono {env env' : VEnv} (henv : env ≤ env')
    (H : env.OnSortTel U Γ As us) : env'.OnSortTel U Γ As us := by
  induction H with
  | nil => exact .nil
  | cons hA _ ih => exact .cons (hA.mono henv) ih

/-- Forget the retained sort labels, preserving the underlying telescope
well-formedness judgment. -/
theorem VEnv.OnSortTel.toOnTel {env : VEnv} :
    ∀ {U : Nat} {Γ As : List VExpr} {us : List VLevel},
      env.OnSortTel U Γ As us → env.OnTel U Γ As
  | _, _, [], [], .nil => trivial
  | _, _, _ :: _, _ :: _, .cons hA hT =>
      ⟨⟨_, hA⟩, VEnv.OnSortTel.toOnTel hT⟩

theorem VEnv.OnSortTel.instL {env : VEnv} {U U' : Nat}
    (hlevels : ∀ level ∈ levels, level.WF U') :
    ∀ {Γ As us}, env.OnSortTel U Γ As us →
      env.OnSortTel U' (Γ.map (VExpr.instL levels))
        (As.map (VExpr.instL levels))
        (us.map (VLevel.inst levels))
  | _, [], [], .nil => .nil
  | _, _ :: _, _ :: _, .cons hA hT =>
      .cons (hA.instL hlevels) (VEnv.OnSortTel.instL hlevels hT)

theorem VEnv.OnSortTel.weakN {env : VEnv} (henv : env.Ordered)
    {U n k : Nat} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ') :
    ∀ {As us}, env.OnSortTel U Γ As us →
      env.OnSortTel U Γ' (VExpr.liftTelN n As k) us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hA hT =>
      .cons (hA.weakN henv W)
        (VEnv.OnSortTel.weakN henv W.succ hT)

private theorem VEnv.OnSortTel.instN {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ₀ : List VExpr} {e₀ A₀ : VExpr}
    (h₀ : env.HasType U Γ₀ e₀ A₀) :
    ∀ {As : List VExpr} {us : List VLevel} {k : Nat}
      {Γ Γ' : List VExpr},
      Ctx.InstN Γ₀ e₀ A₀ k Γ Γ' →
      env.OnSortTel U Γ As us →
      env.OnSortTel U Γ' (VExpr.instTelN e₀ As k) us
  | [], [], _, _, _, _, .nil => .nil
  | _ :: _, _ :: _, _, _, _, W, .cons hA hT =>
      .cons (hA.instN henv W h₀)
        (VEnv.OnSortTel.instN henv h₀ W.succ hT)

private theorem VExpr.instRevAt_instTelN_cons
    (fields : List VExpr) (a : VExpr) (as : List VExpr) :
    ((VExpr.instTelN a fields as.length).zipIdx.map fun (field, i) =>
        VExpr.instRevAt field as i) =
      (fields.zipIdx.map fun (field, i) =>
        VExpr.instRevAt field (a :: as) i) := by
  suffices ∀ (start k : Nat), k = as.length + start →
      ((VExpr.instTelN a fields k).zipIdx start |>.map
          fun (field, i) => VExpr.instRevAt field as i) =
        (fields.zipIdx start |>.map fun (field, i) =>
          VExpr.instRevAt field (a :: as) i) by
    simpa using this 0 as.length (by omega)
  intro start k hk
  induction fields generalizing start k with
  | nil => rfl
  | cons field fields ih =>
      simp only [VExpr.instTelN, List.zipIdx, List.map_cons,
        VExpr.instRevAt]
      rw [hk]
      congr 1
      · congr 2 <;> omega
      · exact ih (start + 1) (as.length + start + 1) (by omega)

theorem VExpr.instRevAt_map_instL_zipIdx
    (fields : List VExpr) (levels : List VLevel)
    (params : List VExpr) (start : Nat := 0) :
    ((fields.map (VExpr.instL levels)).zipIdx start |>.map
        fun (field, i) => VExpr.instRevAt field params i) =
      (fields.zipIdx start |>.map fun (field, i) =>
        VExpr.instRevAt (field.instL levels) params i) := by
  induction fields generalizing start with
  | nil => rfl
  | cons field fields ih =>
      simp only [List.map_cons, List.zipIdx]
      congr 1
      exact ih (start + 1)

private theorem VEnv.OnSortTel.instRevParams {env : VEnv}
    (henv : env.Ordered) {U : Nat} :
    ∀ {Γ params args fields sorts resultLevel},
      env.SpineWF U Γ (VExpr.forallN params (.sort resultLevel))
        args (.sort resultLevel) →
      args.length = params.length →
      env.OnSortTel U (params.reverse ++ Γ) fields sorts →
      env.OnSortTel U Γ
        (fields.zipIdx.map fun (field, i) =>
          VExpr.instRevAt field args i) sorts
  | _, [], [], fields, sorts, _, hspine, _, hfields => by
      simpa [VExpr.instRevAt] using hfields
  | _, [], _ :: _, _, _, _, _, hlen, _ => by simp at hlen
  | Γ, param :: params, arg :: args, fields, sorts, resultLevel,
      .cons harg hrest, hlen, hfields => by
      have hparams : args.length = params.length := by simpa using hlen
      have W := Ctx.InstN.consTel (Γ₀ := Γ) (e₀ := arg)
        (A₀ := param) params (.zero)
      have hfields' : env.OnSortTel U
          ((VExpr.instTelN arg params 0).reverse ++ Γ)
          (VExpr.instTelN arg fields params.length) sorts := by
        apply VEnv.OnSortTel.instN henv harg W
        simpa [List.append_assoc] using hfields
      have hrest' : env.SpineWF U Γ
          (VExpr.forallN (VExpr.instTelN arg params 0)
            (.sort resultLevel)) args (.sort resultLevel) := by
        simpa [VExpr.instN_forallN, VExpr.inst] using hrest
      have hout := VEnv.OnSortTel.instRevParams henv
        hrest' (by simpa [VExpr.instTelN_length] using hparams) hfields'
      rw [← hparams, VExpr.instRevAt_instTelN_cons] at hout
      exact hout

/-- Extend a well-formed ambient context by a well-formed telescope. -/
theorem VEnv.OnTel.toOnCtx {env : VEnv} {U : Nat} :
    ∀ {As Γ}, env.OnTel U Γ As → OnCtx Γ (env.IsType U) →
      OnCtx (As.reverse ++ Γ) (env.IsType U)
  | [], _, _, hΓ => by simpa using hΓ
  | A :: As, Γ, ⟨hA, hAs⟩, hΓ => by
      simpa [List.append_assoc] using
        VEnv.OnTel.toOnCtx hAs (Γ := A :: Γ) ⟨hΓ, hA⟩

private theorem VEnv.OnSortTel.closedAt {env : VEnv} {U : Nat}
    (henv : env.Ordered) :
    ∀ {As us Γ}, env.OnSortTel U Γ As us → CtxClosed Γ →
      ∀ {i : Nat} {field : VExpr}, As[i]? = some field →
        field.ClosedN (Γ.length + i)
  | _, _, _, .nil, _, i, _, h => by simp at h
  | _ :: _, _ :: _, Γ, .cons hA hAs, hΓ, 0, _, h => by
      simp only [List.getElem?_cons_zero] at h
      cases h
      simpa using hA.closedN henv hΓ
  | A :: As, _ :: _, Γ, .cons hA hAs, hΓ, i + 1, field, h => by
      simp only [List.getElem?_cons_succ] at h
      have hclosed : A.ClosedN Γ.length := hA.closedN henv hΓ
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        VEnv.OnSortTel.closedAt henv hAs ⟨hΓ, hclosed⟩ h

private theorem VEnv.OnTel.liftTelN_eq {env : VEnv} {U : Nat}
    (henv : env.Ordered) :
    ∀ {As Γ}, env.OnTel U Γ As → CtxClosed Γ → ∀ n,
      VExpr.liftTelN n As Γ.length = As
  | [], _, _, _, _ => rfl
  | A :: As, Γ, ⟨hA, hAs⟩, hΓ, n => by
      obtain ⟨_, hA⟩ := hA
      have hclosed : A.ClosedN Γ.length := hA.closedN henv hΓ
      simp only [VExpr.liftTelN, hclosed.liftN_eq (Nat.le_refl _)]
      simpa using VEnv.OnTel.liftTelN_eq henv hAs ⟨hΓ, hclosed⟩ n

private theorem VEnv.OnSortTel.liftTelN_eq {env : VEnv} {U : Nat}
    (henv : env.Ordered) :
    ∀ {As us Γ}, env.OnSortTel U Γ As us → CtxClosed Γ → ∀ n,
      VExpr.liftTelN n As Γ.length = As
  | [], [], _, .nil, _, _ => rfl
  | A :: As, _ :: us, Γ, .cons hA hAs, hΓ, n => by
      have hclosed : A.ClosedN Γ.length := hA.closedN henv hΓ
      simp only [VExpr.liftTelN, hclosed.liftN_eq (Nat.le_refl _)]
      simpa using VEnv.OnSortTel.liftTelN_eq henv hAs ⟨hΓ, hclosed⟩ n

/-- The checked, generated description of a nonrecursive structure.

`generation` supplies the exact family, constructor, recursor, and iota rule
artifacts.  The shape fields restrict that general one-family artifact to the
kernel class on which `.proj` is meaningful: no indices, exactly one
constructor, and no recursive constructor arguments.  `fieldSorts` records
the motive universe required by each projection; `WF` below ties every entry
to the corresponding dependent constructor field type. -/
structure VStructureView where
  source : VInductDecl
  generation : source.GenerationChecked
  constructor : NormalizedCtor
  constructor_eq : generation.block.ctorPairs = [constructor]
  raw_indices_eq : generation.block.rawIndices = []
  checked_indices_eq : generation.block.checked.indices = []
  recursive_eq : constructor.view.recursive = []
  fieldSorts : List VLevel
  fieldSorts_length :
    fieldSorts.length = (constructor.rawFields source.nparams).length

namespace VStructureView

abbrev name (view : VStructureView) : Name :=
  view.generation.block.sourceType.name

abbrev constructorName (view : VStructureView) : Name :=
  view.constructor.raw.name

def recursorName (view : VStructureView) : Name :=
  .str view.name "rec"

abbrev uvars (view : VStructureView) : Nat := view.source.uvars

abbrev nparams (view : VStructureView) : Nat := view.source.nparams

abbrev familyType (view : VStructureView) : VExpr :=
  view.generation.block.sourceType.type

def constructorParams (view : VStructureView) : List VExpr :=
  VExpr.telN view.nparams view.constructor.raw.type

def fields (view : VStructureView) : List VExpr :=
  view.constructor.rawFields view.nparams

/-- The instantiated structure type `S.{levels} params`. -/
def structureType (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) : VExpr :=
  VExpr.appN (.const view.name levels) params

/-- Specialize declaration universes and constructor parameters, retaining
the preceding field binders of each dependent field. -/
def specializedFields (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) : List VExpr :=
  view.fields.zipIdx.map fun (field, i) =>
    VExpr.instRevAt (field.instL levels) params i

private theorem specializedFieldsAux_liftN
    (rawFields : List VExpr) (levels : List VLevel)
    (params : List VExpr) (p start n k : Nat)
    (hparams : params.length = p)
    (hclosed : ∀ (j : Nat) (field : VExpr),
      rawFields[j]? = some field →
        field.ClosedN (p + start + j)) :
    (rawFields.zipIdx start |>.map fun (field, i) =>
      VExpr.instRevAt (field.instL levels)
        (params.map fun param => param.liftN n k) i) =
    VExpr.liftTelN n
      (rawFields.zipIdx start |>.map fun (field, i) =>
        VExpr.instRevAt (field.instL levels) params i)
      (k + start) := by
  induction rawFields generalizing start with
  | nil => rfl
  | cons field rawFields ih =>
      have hfield : (field.instL levels).ClosedN (p + start + 0) :=
        VExpr.ClosedN.instL (ls := levels) (hclosed 0 field (by rfl))
      have hrawLift :
          (field.instL levels).liftN n
              (k + start + params.length) = field.instL levels :=
        hfield.liftN_eq (by rw [hparams]; omega)
      have hhead := VExpr.liftN_instRevAt
        (field.instL levels) params start k n
      rw [hrawLift] at hhead
      have htail := ih (start := start + 1)
        (fun j tailField htailField => by
          have := hclosed (j + 1) tailField (by simpa using htailField)
          simpa only [Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using this)
      simp only [List.zipIdx, List.map_cons, VExpr.liftTelN]
      rw [← hhead]
      exact congrArg
        (List.cons (VExpr.liftN n
          ((field.instL levels).instRevAt params start) (k + start)))
        (by simpa only [Nat.add_assoc] using htail)

private theorem specializedFieldsAux_instN
    (rawFields : List VExpr) (levels : List VLevel)
    (params : List VExpr) (p start k : Nat) (a : VExpr)
    (hparams : params.length = p)
    (hclosed : ∀ (j : Nat) (field : VExpr),
      rawFields[j]? = some field →
        field.ClosedN (p + start + j)) :
    (rawFields.zipIdx start |>.map fun (field, i) =>
      VExpr.instRevAt (field.instL levels)
        (params.map fun param => param.inst a k) i) =
    VExpr.instTelN a
      (rawFields.zipIdx start |>.map fun (field, i) =>
        VExpr.instRevAt (field.instL levels) params i)
      (k + start) := by
  induction rawFields generalizing start with
  | nil => rfl
  | cons field rawFields ih =>
      have hfield : (field.instL levels).ClosedN (p + start + 0) :=
        VExpr.ClosedN.instL (ls := levels) (hclosed 0 field (by rfl))
      have hrawInst :
          (field.instL levels).inst a
              (k + start + params.length) = field.instL levels :=
        hfield.instN_eq (by rw [hparams]; omega)
      have hhead := VExpr.instN_instRevAt
        (field.instL levels) params start k a
      rw [hrawInst] at hhead
      have htail := ih (start := start + 1)
        (fun j tailField htailField => by
          have := hclosed (j + 1) tailField (by simpa using htailField)
          simpa only [Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using this)
      simp only [List.zipIdx, List.map_cons, VExpr.instTelN]
      rw [← hhead]
      exact congrArg
        (List.cons (VExpr.inst
          ((field.instL levels).instRevAt params start) a (k + start)))
        (by simpa only [Nat.add_assoc] using htail)

/-- Universe arguments supplied to the generated recursor for a projection
whose result type inhabits `Sort fieldSort`. -/
def projectionLevels (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) : List VLevel :=
  match view.generation.elimination with
  | .large => fieldSort :: levels
  | .small => levels

/-- The two expressions generated for one field.  `typeFn` is the dependent
field type as a function of the structure value; `projector` is a recursor
program implementing the projection. -/
structure ProjectionCode where
  fieldSort : VLevel
  typeFn : VExpr
  minor : VExpr
  projector : VExpr

@[ext] theorem ProjectionCode.ext {left right : ProjectionCode}
    (fieldSort : left.fieldSort = right.fieldSort)
    (typeFn : left.typeFn = right.typeFn)
    (minor : left.minor = right.minor)
    (projector : left.projector = right.projector) : left = right := by
  cases left
  cases right
  simp_all

def ProjectionCode.liftN (code : ProjectionCode)
    (n k : Nat) : ProjectionCode where
  fieldSort := code.fieldSort
  typeFn := code.typeFn.liftN n k
  minor := code.minor.liftN n k
  projector := code.projector.liftN n k

def ProjectionCode.instN (code : ProjectionCode)
    (a : VExpr) (k : Nat) : ProjectionCode where
  fieldSort := code.fieldSort
  typeFn := code.typeFn.inst a k
  minor := code.minor.inst a k
  projector := code.projector.inst a k

def ProjectionCode.instL (code : ProjectionCode)
    (ls : List VLevel) : ProjectionCode where
  fieldSort := code.fieldSort.inst ls
  typeFn := code.typeFn.instL ls
  minor := code.minor.instL ls
  projector := code.projector.instL ls

/-- The constructor-headed major used by a projection minor after all fields
have been introduced. -/
def projectionConstructorApp (view : VStructureView)
    (levels : List VLevel) (params fields : List VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params.map (VExpr.liftN fields.length) ++
      VExpr.bvarRevRange 0 fields.length)

/-- The one-constructor, nonrecursive minor premise expected by the generated
recursor after parameters and a projection motive have been supplied. -/
def projectionMinorType (view : VStructureView)
    (levels : List VLevel) (params fields : List VExpr)
    (typeFn : VExpr) : VExpr :=
  VExpr.forallN fields
    (.app (typeFn.liftN fields.length)
      (view.projectionConstructorApp levels params fields))

@[simp] theorem projectionLevels_instL (view : VStructureView)
    (fieldSort : VLevel) (levels ls : List VLevel) :
    (view.projectionLevels fieldSort levels).map (VLevel.inst ls) =
      view.projectionLevels (fieldSort.inst ls)
        (levels.map (VLevel.inst ls)) := by
  unfold projectionLevels
  split <;> rfl

@[simp] theorem structureType_instL (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.structureType levels params).instL ls =
      view.structureType (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [structureType, VExpr.instL_appN, VExpr.instL]

@[simp] theorem structureType_liftN (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (n k : Nat) :
    (view.structureType levels params).liftN n k =
      view.structureType levels
        (params.map fun param => param.liftN n k) := by
  simp [structureType, VExpr.liftN_appN, VExpr.liftN]

@[simp] theorem structureType_instN (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (a : VExpr) (k : Nat) :
    (view.structureType levels params).inst a k =
      view.structureType levels
        (params.map fun param => param.inst a k) := by
  simp [structureType, VExpr.instN_appN, VExpr.inst]

@[simp] theorem specializedFields_instL (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.specializedFields levels params).map (VExpr.instL ls) =
      view.specializedFields (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [specializedFields, VExpr.instL_instRevAt, VExpr.instL_instL, Function.comp_def]

private def projectionCode (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (i : Nat)
    (previous : List ProjectionCode) : ProjectionCode :=
  let previousAtMajor := previous.map fun code =>
    .app code.projector.lift (.bvar 0)
  let motiveBody := VExpr.instRevAt
    (field.liftN 1 i) previousAtMajor 0
  let typeFn := .lam structType motiveBody
  let minor := VExpr.lamN allFields
    (.bvar (allFields.length - 1 - i))
  let recursor := .const view.recursorName
    (view.projectionLevels fieldSort levels)
  let projector := .lam structType <| VExpr.appN recursor <|
    params.map (VExpr.liftN 1) ++
      [typeFn.lift, minor.lift, .bvar 0]
  { fieldSort, typeFn, minor, projector }

private theorem projectionCode_liftN (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (i : Nat)
    (previous : List ProjectionCode) (n k : Nat)
    (hprevious : previous.length = i)
    (hi : i < allFields.length) :
    (projectionCode view levels params allFields structType field
      fieldSort i previous).liftN n k =
    projectionCode view levels
      (params.map fun param => param.liftN n k)
      (VExpr.liftTelN n allFields k)
      (structType.liftN n k) (field.liftN n (k + i)) fieldSort i
      (previous.map fun code => code.liftN n k) := by
  have hfieldLift :
      (field.liftN 1 i).liftN n (k + 1 + i) =
        (field.liftN n (k + i)).liftN 1 i :=
    VExpr.liftN_liftAt_projection field n k i
  have hpreviousLift :
      (previous.map fun code =>
        VExpr.app code.projector.lift (.bvar 0)).map
          (fun (e : VExpr) => e.liftN n (k + 1)) =
      (previous.map fun code => code.liftN n k).map fun code =>
        VExpr.app code.projector.lift (.bvar 0) := by
    simp [ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_lift_projection, List.map_map,
      Function.comp_def]
  have hmotive :
      ((field.liftN 1 i).instRevAt
          (previous.map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0).liftN n (k + 1) =
      ((field.liftN n (k + i)).liftN 1 i).instRevAt
          ((previous.map fun code => code.liftN n k).map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0 := by
    rw [VExpr.liftN_instRevAt]
    rw [List.length_map, hprevious, hfieldLift, hpreviousLift]
  have hminorBody :
      VExpr.liftN n (.bvar (allFields.length - 1 - i))
          (k + allFields.length) =
        .bvar (allFields.length - 1 - i) := by
    simp only [VExpr.liftN]
    rw [liftVar_lt]
    omega
  have hminorVar :
      liftVar n (allFields.length - 1 - i)
          (k + allFields.length) = allFields.length - 1 - i := by
    rw [liftVar_lt]
    omega
  have hminorNestedVar :
      liftVar n (liftVar 1 (allFields.length - 1 - i)
          allFields.length) (k + 1 + allFields.length) =
        liftVar 1 (allFields.length - 1 - i) allFields.length := by
    have hinner : liftVar 1 (allFields.length - 1 - i)
        allFields.length = allFields.length - 1 - i :=
      liftVar_lt (by omega)
    rw [hinner, liftVar_lt (by omega)]
  have hmotiveLift :
      (((field.liftN 1 i).instRevAt
          (previous.map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0).liftN 1 1).liftN
          n (k + 1 + 1) =
      (((field.liftN n (k + i)).liftN 1 i).instRevAt
          ((previous.map fun code => code.liftN n k).map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0).liftN 1 1 := by
    rw [VExpr.liftN_liftAt_projection]
    exact congrArg (fun e => e.liftN 1 1) hmotive
  apply ProjectionCode.ext
  · rfl
  · simp [projectionCode, ProjectionCode.liftN, VExpr.liftN,
      hmotive]
  · simp [projectionCode, ProjectionCode.liftN,
      VExpr.liftN_lamN_projection, VExpr.liftTelN_length,
      hminorBody]
  · simp [projectionCode, ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_appN, VExpr.liftN_lamN_projection,
      VExpr.liftTelN_length, VExpr.liftN_lift_projection,
      VExpr.liftTelN_lift_projection, List.map_append,
      List.map_map, Function.comp_def, hmotive, hmotiveLift,
      hminorNestedVar]

private theorem projectionCode_instN (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (i : Nat)
    (previous : List ProjectionCode) (a : VExpr) (k : Nat)
    (hprevious : previous.length = i)
    (hi : i < allFields.length) :
    (projectionCode view levels params allFields structType field
      fieldSort i previous).instN a k =
    projectionCode view levels
      (params.map fun param => param.inst a k)
      (VExpr.instTelN a allFields k)
      (structType.inst a k) (field.inst a (k + i)) fieldSort i
      (previous.map fun code => code.instN a k) := by
  have hfieldInst :
      (field.liftN 1 i).inst a (k + 1 + i) =
        (field.inst a (k + i)).liftN 1 i :=
    VExpr.instN_liftAt_projection field a k i
  have hpreviousInst :
      (previous.map fun code =>
        VExpr.app code.projector.lift (.bvar 0)).map
          (fun (e : VExpr) => e.inst a (k + 1)) =
      (previous.map fun code => code.instN a k).map fun code =>
        VExpr.app code.projector.lift (.bvar 0) := by
    simp [ProjectionCode.instN, VExpr.inst, VExpr.instVar,
      ← VExpr.lift_instN_lo, List.map_map, Function.comp_def]
  have hmotive :
      ((field.liftN 1 i).instRevAt
          (previous.map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0).inst a (k + 1) =
      ((field.inst a (k + i)).liftN 1 i).instRevAt
          ((previous.map fun code => code.instN a k).map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0 := by
    rw [VExpr.instN_instRevAt]
    rw [List.length_map, hprevious, hfieldInst, hpreviousInst]
  have hminorVar :
      VExpr.instVar (allFields.length - 1 - i) a
          (k + allFields.length) =
        .bvar (allFields.length - 1 - i) := by
    simp [VExpr.instVar, show
      allFields.length - 1 - i < k + allFields.length by omega]
  apply ProjectionCode.ext
  · rfl
  · simp [projectionCode, ProjectionCode.instN, VExpr.inst, hmotive]
  · simp [projectionCode, ProjectionCode.instN, VExpr.inst,
      VExpr.instN_lamN_projection, VExpr.instTelN_length,
      hminorVar]
  · simp [projectionCode, ProjectionCode.instN, VExpr.inst, VExpr.instN_appN,
      VExpr.instN_lamN_projection, VExpr.instTelN_length, ← VExpr.lift_instN_lo, List.map_append,
      List.map_map, Function.comp_def, hmotive, hminorVar]

private def projectionCodes.go (view : VStructureView)
    (levels : List VLevel) (params : List VExpr)
    (allFields : List VExpr) (structType : VExpr) :
    List VExpr → List VLevel → Nat → List ProjectionCode →
      List ProjectionCode
  | field :: fields, fieldSort :: fieldSorts, i, previous =>
      let code := projectionCode view levels params allFields structType
        field fieldSort i previous
      code :: projectionCodes.go view levels params allFields structType
        fields fieldSorts (i + 1) (previous ++ [code])
  | _, _, _, _ => []

private theorem projectionCodes.go_instN (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (fields : List VExpr)
    (fieldSorts : List VLevel) (i : Nat)
    (previous : List ProjectionCode) (a : VExpr) (k : Nat)
    (hprevious : previous.length = i)
    (hfields : i + fields.length = allFields.length) :
    (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous).map
      (fun code => code.instN a k) =
    projectionCodes.go view levels
      (params.map fun param => param.inst a k)
      (VExpr.instTelN a allFields k) (structType.inst a k)
      (VExpr.instTelN a fields (k + i)) fieldSorts i
      (previous.map fun code => code.instN a k) := by
  induction fields generalizing fieldSorts i previous with
  | nil =>
      cases fieldSorts <;> simp [projectionCodes.go, VExpr.instTelN]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [projectionCodes.go]
      | cons fieldSort fieldSorts =>
          have hi : i < allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          have hcode := projectionCode_instN view levels params allFields
            structType field fieldSort i previous a k hprevious hi
          simp only [projectionCodes.go, List.map_cons,
            VExpr.instTelN]
          rw [hcode]
          congr 1
          have hprevious' :
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort i previous]).length = i + 1 := by
            simp [hprevious]
          have hfields' : i + 1 + fields.length = allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          simpa only [List.map_append, List.map_singleton,
            hcode, Nat.add_assoc] using
              ih fieldSorts (i + 1)
                (previous ++ [projectionCode view levels params allFields
                  structType field fieldSort i previous])
                hprevious' hfields'

private theorem projectionCode_instL (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (i : Nat)
    (previous : List ProjectionCode) (ls : List VLevel) :
    (projectionCode view levels params allFields structType field
      fieldSort i previous).instL ls =
    projectionCode view
      (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls))
      (allFields.map (VExpr.instL ls))
      (structType.instL ls) (field.instL ls) (fieldSort.inst ls) i
      (previous.map fun code => code.instL ls) := by
  simp [projectionCode, ProjectionCode.instL, VExpr.instL,
    VExpr.instL_instRevAt, VExpr.instL_lamN_projection,
    VExpr.instL_appN, VExpr.instL_liftN,
    List.map_append, List.map_map, Function.comp_def]

private theorem projectionCodes.go_instL (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (fields : List VExpr)
    (fieldSorts : List VLevel) (i : Nat)
    (previous : List ProjectionCode) (ls : List VLevel) :
    (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous).map
      (fun code => code.instL ls) =
    projectionCodes.go view
      (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls))
      (allFields.map (VExpr.instL ls))
      (structType.instL ls)
      (fields.map (VExpr.instL ls))
      (fieldSorts.map (VLevel.inst ls)) i
      (previous.map fun code => code.instL ls) := by
  induction fields generalizing fieldSorts i previous with
  | nil => simp [projectionCodes.go]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [projectionCodes.go]
      | cons fieldSort fieldSorts =>
          simp only [projectionCodes.go, List.map_cons,
            projectionCode_instL]
          congr 1
          simpa only [List.map_append, List.map_singleton,
            projectionCode_instL] using
            ih fieldSorts (i + 1)
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort i previous])

private theorem projectionCodes.go_liftN (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (fields : List VExpr)
    (fieldSorts : List VLevel) (i : Nat)
    (previous : List ProjectionCode) (n k : Nat)
    (hprevious : previous.length = i)
    (hfields : i + fields.length = allFields.length) :
    (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous).map
      (fun code => code.liftN n k) =
    projectionCodes.go view levels
      (params.map fun param => param.liftN n k)
      (VExpr.liftTelN n allFields k) (structType.liftN n k)
      (VExpr.liftTelN n fields (k + i)) fieldSorts i
      (previous.map fun code => code.liftN n k) := by
  induction fields generalizing fieldSorts i previous with
  | nil =>
      cases fieldSorts <;> simp [projectionCodes.go, VExpr.liftTelN]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [projectionCodes.go]
      | cons fieldSort fieldSorts =>
          have hi : i < allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          have hcode := projectionCode_liftN view levels params allFields
            structType field fieldSort i previous n k hprevious hi
          simp only [projectionCodes.go, List.map_cons,
            VExpr.liftTelN]
          rw [hcode]
          congr 1
          have hprevious' :
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort i previous]).length = i + 1 := by
            simp [hprevious]
          have hfields' : i + 1 + fields.length = allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          simpa only [List.map_append, List.map_singleton,
            hcode, Nat.add_assoc] using
              ih fieldSorts (i + 1)
                (previous ++ [projectionCode view levels params allFields
                  structType field fieldSort i previous])
                hprevious' hfields'

/-- All field projections, in constructor-field order. -/
def projectionCodes (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) : List ProjectionCode :=
  let fields := view.specializedFields levels params
  projectionCodes.go view levels params fields
    (view.structureType levels params) fields
      (view.fieldSorts.map (VLevel.inst levels)) 0 []

private theorem projectionCodes.go_length (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) :
    ∀ (fields : List VExpr) (fieldSorts : List VLevel)
      (i : Nat) (previous : List ProjectionCode),
      fields.length = fieldSorts.length →
      (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous).length = fields.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | field :: fields, fieldSort :: fieldSorts, i, previous, h => by
      simp only [List.length_cons] at h ⊢
      simp only [projectionCodes.go, List.length_cons]
      exact congrArg Nat.succ <|
        projectionCodes.go_length view levels params allFields structType
          fields fieldSorts (i + 1)
          (previous ++ [projectionCode view levels params allFields
            structType field fieldSort i previous]) (Nat.succ.inj h)

@[simp] theorem projectionCodes_length (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) :
    (view.projectionCodes levels params).length =
      (view.specializedFields levels params).length := by
  apply projectionCodes.go_length
  simp [VStructureView.specializedFields, VStructureView.fields,
    view.fieldSorts_length]

/-- Semantic arguments substituted while walking to a later dependent
projection field. -/
def projectionArgs (view : VStructureView) (levels : List VLevel)
    (params : List VExpr) (count : Nat) (major : VExpr) : List VExpr :=
  (view.projectionCodes levels params).take count |>.map fun code =>
    .app code.projector major

/-- Rebuild a structure value from all of its canonical generated
projections.  This is syntax only: `ProgramsWF.projectionArgsSpine` below
supplies the rule-independent typing evidence, while any equality between
this term and `major` remains an explicit definitional-equality capability. -/
def etaRebuild (view : VStructureView) (levels : List VLevel)
    (params : List VExpr) (major : VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params ++ view.projectionArgs levels params
      (view.specializedFields levels params).length major)

@[simp] theorem projectionArgs_length (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr) (hcount : count ≤
      (view.projectionCodes levels params).length) :
    (view.projectionArgs levels params count major).length = count := by
  simp only [projectionArgs, List.length_map, List.length_take]
  exact Nat.min_eq_left hcount

theorem projectionArgs_succ (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr) {code : ProjectionCode}
    (hcode : (view.projectionCodes levels params)[count]? = some code) :
    view.projectionArgs levels params (count + 1) major =
      view.projectionArgs levels params count major ++
        [.app code.projector major] := by
  simp only [projectionArgs, List.take_add_one, hcode, Option.toList_some,
    List.map_append, List.map_singleton]

private theorem projectionCodes.go_get?_typeFn (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) :
    ∀ {fields : List VExpr} {fieldSorts : List VLevel}
      {i : Nat} {previous : List ProjectionCode} {j : Nat}
      {code : ProjectionCode},
      (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous)[j]? = some code →
      ∃ field,
        fields[j]? = some field ∧
        code.typeFn = .lam structType
          ((field.liftN 1 (i + j)).instRevAt
            ((previous ++
              (projectionCodes.go view levels params allFields structType
                fields fieldSorts i previous).take j).map fun prior =>
                .app prior.projector.lift (.bvar 0)) 0) := by
  intro fields
  induction fields with
  | nil =>
      intro fieldSorts i previous j code h
      cases fieldSorts <;> simp [projectionCodes.go] at h
  | cons field fields ih =>
      intro fieldSorts i previous j code h
      cases fieldSorts with
      | nil => simp [projectionCodes.go] at h
      | cons fieldSort fieldSorts =>
          let head := projectionCode view levels params allFields structType
            field fieldSort i previous
          cases j with
          | zero =>
              change some head = some code at h
              injection h with hcode
              subst code
              refine ⟨field, rfl, ?_⟩
              simp [head, projectionCode]
          | succ j =>
              simp only [projectionCodes.go, List.getElem?_cons_succ] at h
              obtain ⟨tailField, htailField, htypeFn⟩ :=
                ih (fieldSorts := fieldSorts) (i := i + 1)
                  (previous := previous ++ [head]) h
              refine ⟨tailField, by simpa using htailField, ?_⟩
              have hpref :
                  previous ++
                    (projectionCodes.go view levels params allFields structType
                      (field :: fields) (fieldSort :: fieldSorts) i previous).take
                        (j + 1) =
                    (previous ++ [head]) ++
                      (projectionCodes.go view levels params allFields structType
                        fields fieldSorts (i + 1)
                          (previous ++ [head])).take j := by
                simp [head, projectionCodes.go, List.append_assoc]
              rw [hpref]
              simpa only [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using htypeFn

/-- The generated type function at field `idx` is the corresponding
specialized constructor field with all earlier generated projectors
substituted at the major premise. -/
theorem projectionCodes_get?_typeFn (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) {idx : Nat}
    {code : ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code) :
    ∃ field,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params)
        ((field.liftN 1 idx).instRevAt
          ((view.projectionCodes levels params).take idx |>.map fun prior =>
            .app prior.projector.lift (.bvar 0)) 0) := by
  unfold projectionCodes at hcode ⊢
  simpa using projectionCodes.go_get?_typeFn view levels params
    (view.specializedFields levels params)
    (view.structureType levels params) hcode

private theorem projectionCodes.go_get?_program_shape
    (view : VStructureView) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr) :
    ∀ {fields : List VExpr} {fieldSorts : List VLevel}
      {i : Nat} {previous : List ProjectionCode} {j : Nat}
      {code : ProjectionCode},
      (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous)[j]? = some code →
      ∃ fieldSort,
        fieldSorts[j]? = some fieldSort ∧
          code.fieldSort = fieldSort ∧
          code.minor = VExpr.lamN allFields
            (.bvar (allFields.length - 1 - (i + j))) ∧
          code.projector = .lam structType
            (VExpr.appN
              (.const view.recursorName
                (view.projectionLevels code.fieldSort levels))
              (params.map (VExpr.liftN 1) ++
                [code.typeFn.lift, code.minor.lift, .bvar 0])) := by
  intro fields
  induction fields with
  | nil =>
      intro fieldSorts i previous j code h
      cases fieldSorts <;> simp [projectionCodes.go] at h
  | cons field fields ih =>
      intro fieldSorts i previous j code h
      cases fieldSorts with
      | nil => simp [projectionCodes.go] at h
      | cons fieldSort fieldSorts =>
          let head := projectionCode view levels params allFields structType
            field fieldSort i previous
          cases j with
          | zero =>
              change some head = some code at h
              injection h with hcode
              subst code
              simp [head, projectionCode]
          | succ j =>
              simp only [projectionCodes.go, List.getElem?_cons_succ] at h
              have hout := ih (fieldSorts := fieldSorts) (i := i + 1)
                (previous := previous ++ [head]) h
              simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hout

/-- A selected projection code retains the exact selecting minor and
recursor program emitted by `projectionCodes`. -/
theorem projectionCodes_get?_program_shape (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) {idx : Nat}
    {code : ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code) :
    ∃ fieldSort,
      (view.fieldSorts.map (VLevel.inst levels))[idx]? = some fieldSort ∧
        code.fieldSort = fieldSort ∧
        code.minor = VExpr.lamN (view.specializedFields levels params)
          (.bvar ((view.specializedFields levels params).length - 1 - idx)) ∧
        code.projector = .lam (view.structureType levels params)
          (VExpr.appN
            (.const view.recursorName
              (view.projectionLevels code.fieldSort levels))
            (params.map (VExpr.liftN 1) ++
              [code.typeFn.lift, code.minor.lift, .bvar 0])) := by
  unfold projectionCodes at hcode
  simpa using projectionCodes.go_get?_program_shape view levels params
    (view.specializedFields levels params)
    (view.structureType levels params) hcode

/-- Applying a generated projection's type function to its major premise
substitutes that major into every earlier generated projector. -/
theorem projectionCodes_get?_typeFn_beta (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) {idx : Nat}
    {code : ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (major : VExpr) :
    ∃ field typeBody,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params) typeBody ∧
      typeBody.inst major =
        field.instRevAt
          ((view.projectionCodes levels params).take idx |>.map fun prior =>
            .app prior.projector major) 0 := by
  obtain ⟨field, hfield, htypeFn⟩ :=
    view.projectionCodes_get?_typeFn levels params hcode
  let codes := view.projectionCodes levels params
  have hidx : idx < codes.length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  have htake : (codes.take idx).length = idx := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
  have htake' :
      ((view.projectionCodes levels params).take idx).length = idx := by
    simpa [codes] using htake
  refine ⟨field, _, hfield, htypeFn, ?_⟩
  rw [VExpr.instN_instRevAt]
  rw [List.length_map, htake']
  simp only [Nat.zero_add, VExpr.inst_liftN1]
  congr 1
  induction (view.projectionCodes levels params).take idx with
  | nil => rfl
  | cons prior previous ih =>
      simp only [List.map_cons]
      rw [ih]
      simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero]

@[simp] theorem projectionCodes_instL (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.projectionCodes levels params).map
        (fun code => code.instL ls) =
      view.projectionCodes (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [projectionCodes, projectionCodes.go_instL,
    VLevel.inst_inst, List.map_map, Function.comp_def]

/-- The dependent result type of projection `idx`, applied to `major`. -/
def projectionType? (view : VStructureView)
    (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major : VExpr) : Option VExpr := do
  let code ← (view.projectionCodes levels params)[idx]?
  return .app code.typeFn major

/-- The recursor encoding of projection `idx`, applied to `major`. -/
def project? (view : VStructureView)
    (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major : VExpr) : Option VExpr := do
  let code ← (view.projectionCodes levels params)[idx]?
  return .app code.projector major

/-- A proof-carrying boundary for the programs generated by
`projectionCodes`.  Generation fixes the program syntax, while this
certificate records the remaining semantic fact needed by consumers: every
selected projector is well typed at every well-formed instantiation.

This is intentionally separate from `VStructureView.WF`.  The latter is the
certificate produced by ordinary inductive generation; accepting primitive
projection syntax is a later capability boundary and must not silently add a
structure-eta rule to Theory's definitional equality. -/
def ProgramsWF (view : VStructureView) (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat} {code : ProjectionCode},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))

/-- A certified projector is typed by the exact constructor-telescope domain
exposed after substituting all earlier projections. -/
theorem ProgramsWF.projector_hasType_field
    {view : VStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat} {code : ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params)) :
    ∃ field typeBody,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params) typeBody ∧
      env.HasType U Γ (.app code.projector major)
        (field.instRevAt (view.projectionArgs levels params idx major) 0) := by
  obtain ⟨field, typeBody, hfield, htypeFn, htypeBody⟩ :=
    view.projectionCodes_get?_typeFn_beta levels params hcode major
  have hprojector := self hΓ hlevels hlevelsLength hparamsLength
    hparamsSpine hcode
  have happ : env.HasType U Γ (.app code.projector major)
      (.app code.typeFn major) := by
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using
      hprojector.app hmajor
  rw [htypeFn] at happ
  obtain ⟨sortLevel, hredexType⟩ := happ.isType henv hΓ
  obtain ⟨A, B, hlam, harg⟩ := hredexType.app_inv henv hΓ
  obtain ⟨⟨_, hstructType⟩, _, hbodyType⟩ :=
    hlam.lam_inv henv hΓ
  have hfunTypeEq := hlam.uniqU henv hΓ
    (hstructType.lam hbodyType)
  obtain ⟨⟨_, hdomainEq⟩, _⟩ :=
    hfunTypeEq.forallE_inv henv hΓ
  have harg' := harg.defeqU_r henv hΓ ⟨_, hdomainEq⟩
  have hbeta : env.IsDefEqU U Γ
      (.app (.lam (view.structureType levels params) typeBody) major)
      (typeBody.inst major) :=
    ⟨_, VEnv.IsDefEq.beta hbodyType harg'⟩
  have hout := happ.defeqU_r henv hΓ hbeta
  rw [htypeBody] at hout
  refine ⟨field, typeBody, hfield, htypeFn, ?_⟩
  simpa [projectionArgs] using hout

private theorem ProgramsWF.projectionArgsSpineAux
    {view : VStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (tailResult : VExpr) :
    ∀ {count : Nat},
      count ≤ (view.specializedFields levels params).length →
      ∃ cursor,
        VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params count major) = some cursor ∧
          env.SpineWF U Γ
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params count major) cursor := by
  intro count hcount
  induction count with
  | zero =>
      exact ⟨_, rfl, .nil⟩
  | succ count ih =>
      have hcountLt : count <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : count <
          (view.projectionCodes levels params).length := by
        simpa using hcountLt
      let code := (view.projectionCodes levels params)[count]
      have hcode :
          (view.projectionCodes levels params)[count]? = some code :=
        List.getElem?_eq_getElem hcodeIdx
      have hargsLength :
          (view.projectionArgs levels params count major).length = count :=
        view.projectionArgs_length levels params count major
          (Nat.le_of_lt hcodeIdx)
      obtain ⟨cursor, hconsume, hspine⟩ :=
        ih (Nat.le_of_lt hcountLt)
      obtain ⟨field, semanticBody, hfield, hconsumeDomain⟩ :=
        VExpr.consumeForalls?_forallN_domain
          (view.specializedFields levels params) tailResult
          (view.projectionArgs levels params count major)
          (by simpa [hargsLength] using hcountLt)
      have hcursorShape : cursor =
          .forallE
            (field.instRevAt
              (view.projectionArgs levels params count major) 0)
            semanticBody :=
        Option.some.inj (hconsume.symm.trans hconsumeDomain)
      subst cursor
      obtain ⟨field', _, hfield', _, hprojectorField⟩ :=
        self.projector_hasType_field henv hΓ hlevels hlevelsLength
          hparamsLength hparamsSpine hcode hmajor
      have hfieldEq : field' = field :=
        Option.some.inj
          (hfield'.symm.trans (by simpa [hargsLength] using hfield))
      subst field'
      refine ⟨semanticBody.inst (.app code.projector major), ?_, ?_⟩
      · rw [view.projectionArgs_succ levels params count major hcode]
        rw [VExpr.consumeForalls?_append, hconsumeDomain]
        rfl
      · rw [view.projectionArgs_succ levels params count major hcode]
        exact hspine.snoc hprojectorField

/-- All canonical generated projections of a well-typed major form a single
well-typed dependent constructor-field spine.  This theorem deliberately
stops at typing: it does not assert structure eta. -/
theorem ProgramsWF.projectionArgsSpine
    {view : VStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (tailResult : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.projectionArgs levels params
        (view.specializedFields levels params).length major)
      (VExpr.instRev tailResult
        (view.projectionArgs levels params
          (view.specializedFields levels params).length major)) := by
  obtain ⟨_, _, hspine⟩ := self.projectionArgsSpineAux henv hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hmajor tailResult
    (Nat.le_refl _)
  apply hspine.retarget
  · exact view.projectionArgs_length levels params
      (view.specializedFields levels params).length major (by simp)

/-- Applying the complete canonical projection spine to a constructor prefix
is well typed.  The constructor-prefix premise is kept explicit so this
lemma remains independent of any proposed structure-eta equality rule. -/
theorem ProgramsWF.etaRebuild_hasType_of_constructorPrefix
    {view : VStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (hconstructorPrefix : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) params)
      (VExpr.forallN (view.specializedFields levels params)
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length))) :
    env.HasType U Γ (view.etaRebuild levels params major)
      (view.structureType levels params) := by
  have hfields := self.projectionArgsSpine henv hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hmajor
    ((view.structureType levels params).liftN
      (view.specializedFields levels params).length)
  have hrebuild := hfields.hasType_appN hconstructorPrefix
  let args := view.projectionArgs levels params
    (view.specializedFields levels params).length major
  have hargsLength :
      args.length = (view.specializedFields levels params).length :=
    view.projectionArgs_length levels params
      (view.specializedFields levels params).length major (by simp)
  have hlift :
      (view.structureType levels params).liftN
          (view.specializedFields levels params).length =
        (view.structureType levels params).liftN args.length :=
    congrArg (view.structureType levels params).liftN hargsLength.symm
  have hresult :
      VExpr.instRev
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length)
        args =
        view.structureType levels params := by
    calc
      _ = VExpr.instRev
          ((view.structureType levels params).liftN args.length) args :=
        congrArg (VExpr.instRev · args) hlift
      _ = view.structureType levels params :=
        VExpr.instRev_liftN_len args _
  rw [hresult] at hrebuild
  simpa [etaRebuild, VExpr.appN_append] using hrebuild

/-- Exact registration of the checked structure artifact in a Theory
environment.  These are concrete lookups and generated iota rules, not an
oracle supplied by a projection consumer. -/
structure Registered (view : VStructureView) (env : VEnv) : Prop where
  family : env.constants view.name =
    some view.generation.block.sourceType.toVConstant
  constructor : env.constants view.constructorName =
    some view.constructor.raw.toVConstant
  recursor : env.constants view.recursorName =
    some view.generation.recursor
  rules : ∀ rule ∈ view.generation.generatedRules, env.defeqs rule

/-- The semantic fragment of `GenerationEnv` that remains monotone under an
arbitrary environment extension.  Ordering is supplied by the structural-law
caller; exact constant/rule registration is carried separately by
`Registered`. -/
structure GenerationSemantics (view : VStructureView) (env : VEnv) : Prop where
  checked : view.generation.block.checked.WF env
  familyTelescope :
    env.TelDefEq view.uvars []
      (view.generation.block.rawParams ++
        view.generation.block.rawIndices)
      (view.generation.block.checked.params ++
        view.generation.block.checked.indices)
  familyResult :
    env.IsDefEq view.uvars
      (view.generation.block.rawParams ++
        view.generation.block.rawIndices).reverse
      view.generation.block.rawResult
      (.sort view.generation.block.checked.resultLevel)
      (.sort (.succ view.generation.block.checked.resultLevel))
  constructor : view.constructor.WF view.generation.block env

/-- Semantic well-formedness of one structure view in its registered
environment.  The retained sort list is checked against the exact raw
dependent field telescope. -/
structure WF (view : VStructureView) (env : VEnv) : Prop
    extends VStructureView.Registered view env where
  generationSemantics : VStructureView.GenerationSemantics view env
  parameters : env.OnTel view.uvars []
    view.generation.block.checked.params
  parameters_length :
    view.generation.block.checked.params.length = view.nparams
  fieldTelescope : env.OnSortTel view.uvars
    view.generation.block.checked.params.reverse
      view.fields view.fieldSorts
  smallFields : view.generation.elimination = .small →
    ∀ level ∈ view.fieldSorts, level = .zero

theorem WF.rule_mem (self : VStructureView.WF view env) {df : VDefEq}
    (h : df ∈ VInductDecl.GenerationChecked.generatedRules view.generation) :
    VEnv.defeqs env df :=
  self.rules df h

/-- The semantic capability required by structure-eta consumers.

`VStructureView.WF` and `ProgramsWF` account for the registered structure
artifact and the typing of its generated projectors.  This property records
only the additional equality that those rule-independent certificates do not
derive: rebuilding every canonical projection is definitionally equal to the
original major premise.  Keeping it as an explicit environment capability
prevents checker verification from silently extending `VEnv.IsDefEq`. -/
def _root_.Ix.Theory.Named.VEnv.HasStructureEta (env : VEnv) : Prop :=
  ∀ (view : VStructureView), view.WF env → view.ProgramsWF env →
    ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {major : VExpr},
      OnCtx Γ (env.IsType U) →
      (∀ level ∈ levels, level.WF U) →
      levels.length = view.uvars →
      params.length = view.nparams →
      (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) →
      env.HasType U Γ major (view.structureType levels params) →
      env.IsDefEq U Γ (view.etaRebuild levels params major) major
        (view.structureType levels params)

theorem Registered.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VStructureView.Registered view env) :
    VStructureView.Registered view env' where
  family := henv.1 self.family
  constructor := henv.1 self.constructor
  recursor := henv.1 self.recursor
  rules := fun rule hrule => henv.2 (self.rules rule hrule)

theorem GenerationSemantics.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VStructureView.GenerationSemantics view env) :
    VStructureView.GenerationSemantics view env' where
  checked := self.checked.mono henv
  familyTelescope := self.familyTelescope.mono henv
  familyResult := self.familyResult.mono henv
  constructor := self.constructor.mono henv

/-- Recover the monotone semantic fragment of a generated structure from the
ordinary generation certificate and the exact successful transaction trace. -/
theorem GenerationSemantics.ofGenerationTrace {pre env : VEnv}
    (hgen : view.generation.WF pre)
    (trace : VEnv.AddInductGenerationTrace pre env view.generation) :
    VStructureView.GenerationSemantics view env := by
  have htypeFinal : trace.typeEnv ≤ env := by
    have hctors :=
      (ctorFold_spec view.generation.block.sourceType.ctors
        trace.addCtors).1
    have hrec := VEnv.addConst_le trace.addRec
    have hrules : trace.recEnv ≤ env := by
      simpa only [trace.addRules] using
        (rulesFold_spec view.generation.generatedRules trace.recEnv).1
    exact hctors.trans (hrec.trans hrules)
  have hpreFinal := trace.le
  refine {
    checked := hgen.blockWF.2.mono hpreFinal
    familyTelescope := hgen.familyTel.mono hpreFinal
    familyResult := hgen.familyResult.mono hpreFinal
    constructor := ?_ }
  have hconstructor :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  exact (hgen.ctors trace.typeEnv trace.addType view.constructor
    hconstructor).mono htypeFinal

theorem WF.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VStructureView.WF view env) : VStructureView.WF view env' where
  toRegistered := self.toRegistered.mono henv
  generationSemantics := self.generationSemantics.mono henv
  parameters := self.parameters.monoProjection henv
  parameters_length := self.parameters_length
  fieldTelescope := self.fieldTelescope.mono henv
  smallFields := self.smallFields

/-- Reassemble the standard generated-artifact invariant when an ordered
environment is available. -/
theorem WF.toGenerationEnv (self : VStructureView.WF view env)
    (henv : env.Ordered) :
    VInductDecl.GenerationEnv view.generation env where
  ord := henv
  checked := self.generationSemantics.checked
  familyTel := self.generationSemantics.familyTelescope
  familyResult := self.generationSemantics.familyResult
  ctorWF := by
    intro ctor hctor
    rw [view.constructor_eq] at hctor
    simp only [List.mem_singleton] at hctor
    subst ctor
    exact self.generationSemantics.constructor
  familyConst := self.family
  ctorConst := by
    intro ctor hctor
    rw [view.constructor_eq] at hctor
    simp only [List.mem_singleton] at hctor
    subst ctor
    exact self.constructor

theorem WF.field_closed (self : VStructureView.WF view env)
    (henv : env.Ordered) {i : Nat} {field : VExpr}
    (hfield : view.fields[i]? = some field) :
    field.ClosedN (view.nparams + i) := by
  have hparamsCtx : OnCtx
      view.generation.block.checked.params.reverse
      (env.IsType view.uvars) :=
    by simpa using VEnv.OnTel.toOnCtx self.parameters (by trivial)
  have hclosed := VEnv.OnSortTel.closedAt henv self.fieldTelescope
    (VEnv.CtxWF.closed henv hparamsCtx) hfield
  simpa [self.parameters_length] using hclosed

theorem WF.specializedFields_liftN
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    view.specializedFields levels
        (params.map fun param => param.liftN n k) =
      VExpr.liftTelN n (view.specializedFields levels params) k := by
  simpa [specializedFields] using
    specializedFieldsAux_liftN view.fields levels params view.nparams
      0 n k hparams
      (fun j field hfield => by
        simpa using self.field_closed henv hfield)

theorem WF.specializedFields_instN
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    view.specializedFields levels
        (params.map fun param => param.inst a k) =
      VExpr.instTelN a (view.specializedFields levels params) k := by
  simpa [specializedFields] using
    specializedFieldsAux_instN view.fields levels params view.nparams
      0 k a hparams
      (fun j field hfield => by
        simpa using self.field_closed henv hfield)

private theorem projectionLevels_length (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = view.uvars) :
    (view.projectionLevels fieldSort levels).length =
      view.generation.recUvars := by
  unfold projectionLevels
  cases h : view.generation.elimination <;>
    simp [VInductDecl.GenerationChecked.recUvars,
      VInductDecl.ElimMode.recUvars, h, hlevels]

private theorem projectionLevels_wf (view : VStructureView)
    {U : Nat} (fieldSort : VLevel) (levels : List VLevel)
    (hfieldSort : fieldSort.WF U)
    (hlevels : ∀ level ∈ levels, level.WF U) :
    ∀ level ∈ view.projectionLevels fieldSort levels, level.WF U := by
  unfold projectionLevels
  cases view.generation.elimination <;> simp_all

private theorem sourceLevels_projectionLevels (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = view.uvars) :
    view.generation.sourceLevels.map
        (VLevel.inst (view.projectionLevels fieldSort levels)) = levels := by
  unfold VInductDecl.GenerationChecked.sourceLevels
  unfold VInductDecl.ElimMode.sourceLevels projectionLevels
  cases h : view.generation.elimination
  ·
    change (VLevel.params' view.uvars 1).map
      (VLevel.inst (fieldSort :: levels)) = levels
    have hshift :
        (VLevel.params' view.uvars 1).map
            (VLevel.inst (fieldSort :: levels)) =
          (VLevel.params view.uvars).map (VLevel.inst levels) := by
      simp [VLevel.params', VLevel.params, List.map_map,
        Function.comp_def, VLevel.inst,
        List.getD_eq_getElem?_getD]
    rw [hshift]
    exact VLevel.inst_map_id hlevels
  ·
    change (VLevel.params' view.uvars 0).map
      (VLevel.inst levels) = levels
    have hzero : VLevel.params' view.uvars 0 =
        VLevel.params view.uvars := by
      simp [VLevel.params', VLevel.params]
    rw [hzero]
    exact VLevel.inst_map_id hlevels

private theorem motiveLevel_projectionLevels (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) :
    view.generation.motiveLevel.inst
        (view.projectionLevels fieldSort levels) =
      match view.generation.elimination with
      | .large => fieldSort
      | .small => .zero := by
  unfold VInductDecl.GenerationChecked.motiveLevel
  unfold VInductDecl.ElimMode.motiveLevel projectionLevels
  cases view.generation.elimination <;> rfl

private theorem WF.motiveLevel_projectionLevels
    (self : VStructureView.WF view env)
    (fieldSort : VLevel) (hfieldSort : fieldSort ∈ view.fieldSorts)
    (levels : List VLevel) :
    view.generation.motiveLevel.inst
        (view.projectionLevels (fieldSort.inst levels) levels) =
      fieldSort.inst levels := by
  rw [VStructureView.motiveLevel_projectionLevels]
  cases hmode : view.generation.elimination with
  | large => rfl
  | small =>
      rw [self.smallFields hmode fieldSort hfieldSort]
      rfl

@[simp] theorem WF.projectionCodes_liftN
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    (view.projectionCodes levels params).map
        (fun code => code.liftN n k) =
      view.projectionCodes levels
        (params.map fun param => param.liftN n k) := by
  unfold projectionCodes
  rw [self.specializedFields_liftN henv levels params hparams n k]
  rw [← structureType_liftN]
  apply projectionCodes.go_liftN
  · rfl
  · simp

@[simp] theorem WF.projectionCodes_instN
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    (view.projectionCodes levels params).map
        (fun code => code.instN a k) =
      view.projectionCodes levels
        (params.map fun param => param.inst a k) := by
  unfold projectionCodes
  rw [self.specializedFields_instN henv levels params hparams a k]
  rw [← structureType_instN]
  apply projectionCodes.go_instN
  · rfl
  · simp

/-- The exact lower-layer structure-eta descriptor generated by a checked
structure view.  Its projector syntax is the deterministic projector program
list already certified by the view; the proof fields are only the three
syntactic naturality laws required by Theory transport. -/
def WF.toStructEta (self : VStructureView.WF view env)
    (henv : env.Ordered) : VStructEta where
  uvars := view.uvars
  nparams := view.nparams
  nfields := view.fields.length
  familyName := view.name
  familyType := view.familyType
  constructorName := view.constructorName
  projectors := fun levels params =>
    (view.projectionCodes levels params).map (·.projector)
  projectors_length := by
    intro levels params _ _
    simp [VStructureView.specializedFields, VStructureView.fields]
  projectors_liftN := by
    intro levels params n k hparams
    have h := self.projectionCodes_liftN henv levels params hparams n k
    simpa [List.map_map, ProjectionCode.liftN, Function.comp_def] using
      congrArg (List.map (·.projector)) h
  projectors_instN := by
    intro levels params a k hparams
    have h := self.projectionCodes_instN henv levels params hparams a k
    simpa [List.map_map, ProjectionCode.instN, Function.comp_def] using
      congrArg (List.map (·.projector)) h
  projectors_instL := by
    intro levels params ls
    have h := projectionCodes_instL view levels params ls
    simpa [List.map_map, ProjectionCode.instL, Function.comp_def] using
      congrArg (List.map (·.projector)) h

@[simp] theorem WF.toStructEta_structureType
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr) :
    (self.toStructEta henv).structureType levels params =
      view.structureType levels params := rfl

@[simp] theorem WF.toStructEta_rebuild
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr) (major : VExpr) :
    (self.toStructEta henv).rebuild levels params major =
      view.etaRebuild levels params major := by
  simp only [VStructEta.rebuild, VStructEta.projectionArgs, WF.toStructEta,
    VStructureView.etaRebuild, VStructureView.projectionArgs]
  rw [← view.projectionCodes_length levels params, List.take_length]
  simp [List.map_map, Function.comp_def]

end VStructureView

namespace VEnv

/-- Registered checked views supply the former semantic structure-eta
capability.  The registry contributes only membership; subject reduction is
recovered from the ordered environment, and the equality itself is the
primitive `IsDefEq.structEta` step. -/
theorem hasStructureEta_of_registry (henv : env.Ordered)
    (registered : ∀ (view : VStructureView)
      (hview : view.WF env) (_ : view.ProgramsWF env),
      env.structEtas (hview.toStructEta henv)) :
    env.HasStructureEta := by
  intro view hview programs U Γ levels params major hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hmajor
  let rule := hview.toStructEta henv
  have hregistered : env.structEtas rule := registered view hview programs
  have hruleWF : rule.WF env := henv.structEtaWF hregistered
  obtain ⟨resultLevel, hparamsSpine⟩ := hparamsSpine
  have hrebuild := hruleWF.rebuild_hasType VEnv.LE.rfl hΓ hlevels
    hlevelsLength hparamsLength ⟨resultLevel, hparamsSpine⟩ hmajor
  have heta := IsDefEq.structEta hregistered hlevels hlevelsLength
    hparamsLength hparamsSpine hmajor hrebuild
  simpa [rule] using heta

private theorem SpineWF.monoProjection {env env' : VEnv}
    (henv : env ≤ env') :
    ∀ {A es B}, env.SpineWF U Γ A es B → env'.SpineWF U Γ A es B
  | _, _, _, h => h.mono henv

/-- The view-facing direction of `TelDefEq.spine_sort`: arguments checked
against the retained raw telescope also consume its definitionally equal
view telescope. -/
theorem TelDefEq.spine_sort_view
    {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Γ As As' es l}, env.TelDefEq U Γ As As' →
      env.SpineWF U Γ (VExpr.forallN As (.sort l)) es (.sort l) →
      es.length = As.length →
      env.SpineWF U Γ (VExpr.forallN As' (.sort l)) es (.sort l)
  | _, [], [], [], _, _, hspine, _ => by simpa using hspine
  | _, [], [], _ :: _, _, _, _, hlen => by simp at hlen
  | Γ, A :: As, A' :: As', e :: es, l, ⟨⟨_, hA⟩, hT⟩,
      .cons he hrest, hlen => by
    have heView : env.HasType U Γ e A' := hA.defeq he
    have hTinst := TelDefEq.instN henv he (.zero) hT
    have hrest' : env.SpineWF U Γ
        (VExpr.forallN (VExpr.instTelN e As 0) (.sort l))
        es (.sort l) := by
      simpa [VExpr.instN_forallN, VExpr.inst] using hrest
    have hlen' : es.length = As.length := by simpa using hlen
    have hlenInst :
        es.length = (VExpr.instTelN e As 0).length := by
      rw [VExpr.instTelN_length]
      exact hlen'
    have hout := TelDefEq.spine_sort_view henv
      hTinst hrest' hlenInst
    refine .cons heView ?_
    simpa [VExpr.instN_forallN, VExpr.inst] using hout

/-- Parameters accepted by the structure family also consume the stored raw
constructor parameter prefix.  This is the semantic bridge used by the
kernel projection checker before it traverses the constructor fields. -/
theorem _root_.Ix.Theory.Named.VStructureView.WF.constructorParamsSpine
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (target : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels))
        target) params (VExpr.instRev target params) := by
  let S := self.toGenerationEnv henv
  obtain ⟨resultLevel, hspine⟩ := paramsSpine
  have hrawLength :
      view.generation.block.rawParams.length = view.nparams :=
    view.generation.shape.1
  have hspineShape : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (view.generation.block.rawResult.instL levels))
      params (.sort resultLevel) := by
    simpa [VStructureView.familyType,
      VInductDecl.NormalizedChecked.rawType_eq,
      view.raw_indices_eq, VExpr.instL_forallN,
      VExpr.forallN] using hspine
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) := by
    have hout := hspineShape.retarget
      (by simpa [hrawLength] using hparamsLength) (.sort .zero)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hfamilyDefEq := S.rawParams_defeq.instL hlevels
  have hrawLift : VExpr.liftTelN Γ.length
      (view.generation.block.rawParams.map (VExpr.instL levels)) 0 =
      view.generation.block.rawParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hfamilyDefEq.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hfamilyDefEq.view_onTel henv) (by trivial) Γ.length
  have hfamilyDefEqΓ := hfamilyDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift, hcheckedLift] at hfamilyDefEqΓ
  simp only [List.append_nil] at hfamilyDefEqΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) :=
    TelDefEq.spine_sort_view henv hfamilyDefEqΓ hparamsRaw
      (by simpa [hrawLength] using hparamsLength)
  have hconstructorMem :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hconstructorShape :=
    view.generation.shape.2.2.2.2.2 view.constructor hconstructorMem
  have hconstructorDefEq₀ :=
    ((S.ctorWF view.constructor hconstructorMem).declaredTel.take
      view.nparams).instL hlevels
  have hconstructorDefEq : env.TelDefEq U []
      (view.constructorParams.map (VExpr.instL levels))
      (view.generation.block.checked.params.map (VExpr.instL levels)) := by
    simpa [VStructureView.constructorParams,
      VInductDecl.NormalizedCtor.declaredBinders,
      VInductDecl.NormalizedCtor.viewBinders,
      hconstructorShape.2.2.1, self.parameters_length] using
        hconstructorDefEq₀
  have hconstructorRawLift : VExpr.liftTelN Γ.length
      (view.constructorParams.map (VExpr.instL levels)) 0 =
      view.constructorParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hconstructorDefEq.raw_onTel (by trivial) Γ.length
  have hconstructorCheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) :=
    hcheckedLift
  have hconstructorDefEqΓ := hconstructorDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hconstructorRawLift, hconstructorCheckedLift] at hconstructorDefEqΓ
  simp only [List.append_nil] at hconstructorDefEqΓ
  have hout := TelDefEq.spine_sort henv hconstructorDefEqΓ hparamsChecked
    (by simpa [VStructureView.constructorParams] using
      hparamsLength.trans hconstructorShape.2.2.1.symm)
  exact hout.retarget
    (by simpa [VStructureView.constructorParams] using
      hparamsLength.trans hconstructorShape.2.2.1.symm) target

/-- Recover the structure-family parameter spine from the corresponding
constructor-parameter prefix.  This is the converse consumer bridge needed
when a checker recognizes a fully applied constructor before it knows the
family application carried by its result type. -/
theorem _root_.Ix.Theory.Named.VStructureView.WF.familyParamsSpine_of_constructor
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    {target cursor : VExpr}
    (constructorSpine : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) target)
      params cursor)
    (resultLevel : VLevel)
    (hresult : view.generation.block.rawResult = .sort resultLevel) :
    env.SpineWF U Γ (view.familyType.instL levels) params
      (.sort (resultLevel.inst levels)) := by
  let S := self.toGenerationEnv henv
  have hrawLength :
      view.generation.block.rawParams.length = view.nparams :=
    view.generation.shape.1
  have hconstructorMem :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hconstructorShape :=
    view.generation.shape.2.2.2.2.2 view.constructor hconstructorMem
  have hconstructorLength : params.length =
      (view.constructorParams.map (VExpr.instL levels)).length := by
    simpa [VStructureView.constructorParams] using
      hparamsLength.trans hconstructorShape.2.2.1.symm
  have hparamsConstructor : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) (.sort .zero))
      params (.sort .zero) := by
    have hout := constructorSpine.retarget hconstructorLength (.sort .zero)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hfamilyDefEq := S.rawParams_defeq.instL hlevels
  have hrawLift : VExpr.liftTelN Γ.length
      (view.generation.block.rawParams.map (VExpr.instL levels)) 0 =
      view.generation.block.rawParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hfamilyDefEq.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hfamilyDefEq.view_onTel henv) (by trivial) Γ.length
  have hfamilyDefEqΓ := hfamilyDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift, hcheckedLift] at hfamilyDefEqΓ
  simp only [List.append_nil] at hfamilyDefEqΓ
  have hconstructorDefEq₀ :=
    ((S.ctorWF view.constructor hconstructorMem).declaredTel.take
      view.nparams).instL hlevels
  have hconstructorDefEq : env.TelDefEq U []
      (view.constructorParams.map (VExpr.instL levels))
      (view.generation.block.checked.params.map (VExpr.instL levels)) := by
    simpa [VStructureView.constructorParams,
      VInductDecl.NormalizedCtor.declaredBinders,
      VInductDecl.NormalizedCtor.viewBinders,
      hconstructorShape.2.2.1, self.parameters_length] using
        hconstructorDefEq₀
  have hconstructorRawLift : VExpr.liftTelN Γ.length
      (view.constructorParams.map (VExpr.instL levels)) 0 =
      view.constructorParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hconstructorDefEq.raw_onTel (by trivial) Γ.length
  have hconstructorDefEqΓ := hconstructorDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hconstructorRawLift, hcheckedLift] at hconstructorDefEqΓ
  simp only [List.append_nil] at hconstructorDefEqΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort_view henv hconstructorDefEqΓ
      hparamsConstructor hconstructorLength
  have hrawParamsLength : params.length =
      (view.generation.block.rawParams.map (VExpr.instL levels)).length := by
    simpa [hrawLength] using hparamsLength
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort henv hfamilyDefEqΓ hparamsChecked
      hrawParamsLength
  have hout := hparamsRaw.retarget hrawParamsLength
    (.sort (resultLevel.inst levels))
  rw [VExpr.instRev_closedN params (by trivial)] at hout
  simpa [VStructureView.familyType,
    VInductDecl.NormalizedChecked.rawType_eq,
    view.raw_indices_eq, hresult, VExpr.instL_forallN,
    VExpr.forallN, VExpr.instL] using hout

theorem _root_.Ix.Theory.Named.VStructureView.WF.specializedFields_onSortTel
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.OnSortTel U Γ (view.specializedFields levels params)
      (view.fieldSorts.map (VLevel.inst levels)) := by
  let S := self.toGenerationEnv henv
  obtain ⟨resultLevel, hspine⟩ := paramsSpine
  have hrawLength :
      view.generation.block.rawParams.length = view.nparams :=
    view.generation.shape.1
  have hspineShape : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (view.generation.block.rawResult.instL levels))
      params (.sort resultLevel) := by
    simpa [VStructureView.familyType,
      VInductDecl.NormalizedChecked.rawType_eq,
      view.raw_indices_eq, VExpr.instL_forallN,
      VExpr.forallN] using hspine
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (.sort resultLevel)) params (.sort resultLevel) := by
    have hout := hspineShape.retarget
      (by simpa [hrawLength] using hparamsLength)
      (.sort resultLevel)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hrawChecked := S.rawParams_defeq.instL hlevels
  have hrawLift := VEnv.OnTel.liftTelN_eq henv
    hrawChecked.raw_onTel (by trivial) Γ.length
  have hcheckedLift := VEnv.OnTel.liftTelN_eq henv
    (hrawChecked.view_onTel henv) (by trivial) Γ.length
  have hrawLift' : VExpr.liftTelN Γ.length
      (view.generation.block.rawParams.map (VExpr.instL levels)) 0 =
      view.generation.block.rawParams.map (VExpr.instL levels) := by
    simpa using hrawLift
  have hcheckedLift' : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using hcheckedLift
  have hrawCheckedΓ := hrawChecked.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift', hcheckedLift'] at hrawCheckedΓ
  simp only [List.append_nil] at hrawCheckedΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map
          (VExpr.instL levels)) (.sort resultLevel))
      params (.sort resultLevel) := by
    exact TelDefEq.spine_sort_view henv hrawCheckedΓ hparamsRaw
      (by simpa [hrawLength] using hparamsLength)
  have hfields := self.fieldTelescope.instL hlevels
  have hcheckedParams := self.parameters.instL hlevels
  have Wparams := Ctx.LiftN.consTel
    (view.generation.block.checked.params.map (VExpr.instL levels))
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hcheckedLift'] at Wparams
  have hcheckedCtx : OnCtx
      (view.generation.block.checked.params.reverse.map
        (VExpr.instL levels)) (env.IsType U) := by
    simpa [List.map_reverse] using
      VEnv.OnTel.toOnCtx hcheckedParams (by trivial)
  have hfieldLift := VEnv.OnSortTel.liftTelN_eq henv hfields
    (VEnv.CtxWF.closed henv hcheckedCtx) Γ.length
  have hfieldsΓ := VEnv.OnSortTel.weakN henv
    (by simpa [List.map_reverse] using Wparams) hfields
  simp only [List.length_reverse, List.length_map] at hfieldLift
  rw [hfieldLift] at hfieldsΓ
  have hspecialized := VEnv.OnSortTel.instRevParams henv
    hparamsChecked (by simpa [self.parameters_length] using hparamsLength)
    (by simpa [List.map_reverse] using hfieldsΓ)
  rw [VExpr.instRevAt_map_instL_zipIdx] at hspecialized
  simpa [VStructureView.specializedFields] using hspecialized

private theorem _root_.Ix.Theory.Named.VStructureView.WF.generationParamsSpine
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel) :
    env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.paramsTel.map
          (VExpr.instL
            (view.projectionLevels fieldSort levels)))
        (.sort fieldSort)) params (.sort fieldSort) := by
  let S := self.toGenerationEnv henv
  obtain ⟨resultLevel, hspine⟩ := paramsSpine
  have hrawLength :
      view.generation.block.rawParams.length = view.nparams :=
    view.generation.shape.1
  have hspineShape : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (view.generation.block.rawResult.instL levels))
      params (.sort resultLevel) := by
    simpa [VStructureView.familyType,
      VInductDecl.NormalizedChecked.rawType_eq,
      view.raw_indices_eq, VExpr.instL_forallN,
      VExpr.forallN] using hspine
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (.sort fieldSort)) params (.sort fieldSort) := by
    have hout := hspineShape.retarget
      (by simpa [hrawLength] using hparamsLength) (.sort fieldSort)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hrawChecked := S.rawParams_defeq.instL hlevels
  have hrawLift : VExpr.liftTelN Γ.length
      (view.generation.block.rawParams.map (VExpr.instL levels)) 0 =
      view.generation.block.rawParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hrawChecked.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hrawChecked.view_onTel henv) (by trivial) Γ.length
  have hrawCheckedΓ := hrawChecked.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift, hcheckedLift] at hrawCheckedΓ
  simp only [List.append_nil] at hrawCheckedΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map
          (VExpr.instL levels)) (.sort fieldSort))
      params (.sort fieldSort) :=
    TelDefEq.spine_sort_view henv hrawCheckedΓ hparamsRaw
      (by simpa [hrawLength] using hparamsLength)
  have hgenerationChecked := S.generationParams_defeq.instL hlevels
  have hgenerationLift : VExpr.liftTelN Γ.length
      (view.generation.block.generationParams.map
        (VExpr.instL levels)) 0 =
      view.generation.block.generationParams.map
        (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hgenerationChecked.raw_onTel (by trivial) Γ.length
  have hcheckedLift₂ : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map
        (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map
        (VExpr.instL levels) := hcheckedLift
  have hgenerationCheckedΓ := hgenerationChecked.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hgenerationLift, hcheckedLift₂] at hgenerationCheckedΓ
  simp only [List.append_nil] at hgenerationCheckedΓ
  have hparamsGeneration := TelDefEq.spine_sort henv
    hgenerationCheckedΓ hparamsChecked
    (by simpa [S.generationParams_length] using hparamsLength)
  have hsource := VStructureView.sourceLevels_projectionLevels
    view fieldSort levels
    hlevelsLength
  have hparamsTel :
      view.generation.paramsTel.map
          (VExpr.instL (view.projectionLevels fieldSort levels)) =
        view.generation.block.generationParams.map
          (VExpr.instL levels) := by
    simp [VInductDecl.GenerationChecked.paramsTel,
      List.map_map, Function.comp_def, VExpr.instL_instL, hsource]
  rw [hparamsTel]
  exact hparamsGeneration

theorem _root_.Ix.Theory.Named.VStructureView.WF.recursorProjection_hasType
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel)
    (hfieldSort : fieldSort.WF U)
    (hmotiveLevel :
      view.generation.motiveLevel.inst
          (view.projectionLevels fieldSort levels) = fieldSort)
    (_structIsType : env.IsType U Γ
      (view.structureType levels params))
    {typeFn minor major : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (minorType : env.HasType U Γ minor
      (view.projectionMinorType levels params
        (view.specializedFields levels params) typeFn))
    (majorType : env.HasType U Γ major
      (view.structureType levels params)) :
    env.HasType U Γ
      (VExpr.appN (.const view.recursorName
        (view.projectionLevels fieldSort levels))
        (params ++ [typeFn, minor, major]))
      (.app typeFn major) := by
  let gen := view.generation
  let S := self.toGenerationEnv henv
  let pLevels := view.projectionLevels fieldSort levels
  let k := gen.block.ctorPairs.length
  let ni := gen.idxTel.length
  let recRest : VExpr :=
    VExpr.forallN gen.minorTypes <|
      VExpr.forallN (VExpr.liftTelN (k + 1) gen.idxTel 0) <|
        .forallE
          (VExpr.appN (.const gen.block.sourceType.name gen.sourceLevels)
            (VExpr.bvarRevRange (ni + k + 1) view.nparams ++
              VExpr.bvarRevRange 0 ni))
          (.app
            (VExpr.appN (.bvar (ni + k + 1))
              (VExpr.bvarRevRange 1 ni))
            (.bvar 0))
  let recTail : VExpr := .forallE gen.motiveType recRest
  have hrec : env.HasType U Γ
      (.const view.recursorName pLevels)
      ((VExpr.forallN gen.paramsTel recTail).instL pLevels) := by
    have hout := VEnv.HasType.const (Γ := Γ) self.recursor
      (VStructureView.projectionLevels_wf view fieldSort levels
        hfieldSort hlevels)
      (VStructureView.projectionLevels_length view fieldSort levels
        hlevelsLength)
    simpa [gen, pLevels, recTail, recRest, k, ni,
      VStructureView.recursorName,
      VInductDecl.GenerationChecked.recursor,
      VInductDecl.GenerationChecked.recType] using hout
  have hparams := self.generationParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine fieldSort
  have hparamsTelLength : params.length =
      (gen.paramsTel.map (VExpr.instL pLevels)).length := by
    simp [gen, VInductDecl.GenerationChecked.paramsTel,
      S.generationParams_length, hparamsLength]
  have hparamsFull := hparams.retarget hparamsTelLength
    (recTail.instL pLevels)
  have hparamsFull' : env.SpineWF U Γ
      ((VExpr.forallN gen.paramsTel recTail).instL pLevels)
      params (VExpr.instRev (recTail.instL pLevels) params) := by
    simpa [VExpr.instL_forallN] using hparamsFull
  have hmotiveShape :
      VExpr.instRev (recTail.instL pLevels) params =
        .forallE
          (.forallE (view.structureType levels params) (.sort fieldSort))
          (VExpr.instRevAt (recRest.instL pLevels) params 1) := by
    change VExpr.instRev
      (.forallE (gen.motiveType.instL pLevels)
        (recRest.instL pLevels)) params = _
    have hconst : VExpr.instRev
        (.const view.generation.block.sourceType.name levels) params =
        .const view.generation.block.sourceType.name levels :=
      VExpr.instRev_closedN params (by trivial)
    have hrange :
        (VExpr.bvarRevRange 0 view.source.nparams).map
            (VExpr.instRev · params) = params := by
      have hparamsLength' : params.length = view.source.nparams :=
        hparamsLength
      rw [← hparamsLength']
      exact VExpr.map_instRev_bvarRevRange params
    have hrangeL :
        (VExpr.bvarRevRange 0 view.source.nparams).map
            (fun x => (x.instL pLevels).instRev params) = params := by
      calc
        _ = ((VExpr.bvarRevRange 0 view.source.nparams).map
              (VExpr.instL pLevels)).map (VExpr.instRev · params) := by
            rw [List.map_map]
            rfl
        _ = params := by
          rw [VExpr.bvarRevRange_map_instL]
          exact hrange
    have hsort :
        (VExpr.sort fieldSort).instRevAt params 1 =
          .sort fieldSort :=
      VExpr.instRevAt_closedN params (by trivial)
    rw [VExpr.instRev_forallE_projection]
    congr 1
    simp [gen, pLevels,
      VInductDecl.GenerationChecked.motiveType,
      VInductDecl.GenerationChecked.idxTel,
      view.raw_indices_eq, VExpr.forallN, VExpr.bvarRevRange,
      VExpr.instL, VExpr.instL_appN,
      VExpr.instRev_forallE_projection,
      VExpr.instRev_appN, Function.comp_def,
      hconst, hrangeL, hsort, hmotiveLevel,
      VStructureView.structureType,
      VStructureView.sourceLevels_projectionLevels view fieldSort levels
        hlevelsLength]
  rw [hmotiveShape] at hparamsFull'
  have hwithMotive := hparamsFull'.snoc typeFnType
  have hconstructorMem :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    rw [S.viewResultIndices_length hconstructorMem]
    simp [view.checked_indices_eq]
  have hminorShape :
      ((VExpr.instRevAt (recRest.instL pLevels) params 1).inst typeFn) =
        .forallE (view.projectionMinorType levels params
            (view.specializedFields levels params) typeFn)
          (.forallE (view.structureType levels params).lift
            (.app (typeFn.liftN 2) (.bvar 0))) := by
    simp [gen, pLevels, recRest, k, ni, VInductDecl.GenerationChecked.minorTypes,
      VInductDecl.GenerationChecked.minorTypesAux, VInductDecl.GenerationChecked.minorType,
      VInductDecl.GenerationChecked.idxTel, VInductDecl.NormalizedCtor.fieldsR,
      VInductDecl.NormalizedCtor.recArgsR, VInductDecl.NormalizedCtor.resultIndicesR,
      VInductDecl.ihsFromRecArgs, VStructureView.projectionMinorType,
      VStructureView.projectionConstructorApp, view.constructor_eq, view.raw_indices_eq,
      hresultIndices, view.recursive_eq, VExpr.instL_forallN, VExpr.instL_appN,
      VExpr.liftTelN_instL, VExpr.instL_instL, VExpr.instN_forallN, VExpr.instTelN,
      VExpr.instRevAt_forallN_projection, List.map_append, VExpr.bvarRevRange, List.map_append,
      List.map_map, Function.comp_def,
      VStructureView.sourceLevels_projectionLevels view fieldSort levels hlevelsLength]
    change VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · have hfieldTel :=
        VExpr.instTelN_instRevAt_lift_projection
          ((view.constructor.rawFields view.source.nparams).map
            (VExpr.instL levels)) params typeFn 0
      rw [VExpr.instRevAt_map_instL_zipIdx] at hfieldTel
      have hfieldTel' :
          VExpr.instTelN typeFn
              ((VExpr.liftTelN 1
                  ((view.constructor.rawFields view.source.nparams).map
                    (VExpr.instL levels)) 0).zipIdx 1 |>.map
                fun x => x.1.instRevAt params x.2) 0 =
            view.specializedFields levels params := by
        simpa [VStructureView.specializedFields,
          VStructureView.fields] using hfieldTel
      rw [hfieldTel']
      congr 1
      have hsourceLevels :=
        VStructureView.sourceLevels_projectionLevels view fieldSort levels
          hlevelsLength
      change
        (VLevel.params' view.source.uvars
            view.generation.elimination.offset).map
              (VLevel.inst pLevels) = levels at hsourceLevels
      have hliftedLength :
          (VExpr.liftTelN 1
              ((view.constructor.rawFields view.source.nparams).map
                (VExpr.instL levels)) 0).length =
            (view.constructor.rawFields view.source.nparams).length := by
        rw [VExpr.liftTelN_length]
        simp
      have hspecializedLength :
          (view.specializedFields levels params).length =
            (view.constructor.rawFields view.source.nparams).length := by
        simp [VStructureView.specializedFields,
          VStructureView.fields]
      simp only [VExpr.forallN, VExpr.instL, VExpr.bvarRevRange_map_instL, hliftedLength,
        hspecializedLength]
      rw [hsourceLevels]
      have hbody :=
        VExpr.projectionMinorBody_shape view.constructorName levels
          params (view.constructor.rawFields view.source.nparams).length
          typeFn
      rw [hparamsLength] at hbody
      simpa only [Nat.add_comm] using hbody
    · have hsourceLevels :=
        VStructureView.sourceLevels_projectionLevels view fieldSort levels
          hlevelsLength
      change
        (VLevel.params' view.source.uvars
            view.generation.elimination.offset).map
              (VLevel.inst pLevels) = levels at hsourceLevels
      simp only [VExpr.forallN, VExpr.liftTelN, List.zipIdx_nil, List.map_nil, VExpr.instTelN,
        VExpr.instL, VExpr.instL_appN, VExpr.bvarRevRange_map_instL, VExpr.instL]
      rw [hsourceLevels]
      simpa [gen, hparamsLength, VStructureView.structureType] using
        (VExpr.projectionMajorTail_shape view.name levels params typeFn)
  rw [hminorShape] at hwithMotive
  have hwithMinor := hwithMotive.snoc minorType
  have hwithMajor : env.SpineWF U Γ
      ((VExpr.forallN gen.paramsTel recTail).instL pLevels)
      (params ++ [typeFn, minor, major]) (.app typeFn major) := by
    have majorType' : env.HasType U Γ major
        ((view.structureType levels params).lift.inst minor) := by
      rw [VExpr.inst_lift]
      exact majorType
    have hout := hwithMinor.snoc majorType'
    have htypeFnMinor :
        (typeFn.liftN 2).inst minor 1 = typeFn.lift := by
      rw [← VExpr.liftN_liftN typeFn 1 1,
        VExpr.instN_liftAt_projection, VExpr.inst_lift]
    have hminorVar : VExpr.instVar 0 minor 1 = .bvar 0 := by
      simp [VExpr.instVar]
    have hresult :
        (((typeFn.liftN 2).app (.bvar 0)).inst minor 1).inst major =
          typeFn.app major := by
      simp only [VExpr.inst]
      rw [htypeFnMinor, VExpr.inst_lift]
      rw [hminorVar]
      simp only [VExpr.inst]
      rw [VExpr.instVar_zero]
    rw [hresult] at hout
    simpa [List.append_assoc] using hout
  exact hwithMajor.hasType_appN hrec

theorem SpineWF.instNProjection {env : VEnv} {U k : Nat}
    {Γ₀ Γ₁ Γ : List VExpr} {e₀ A₀ : VExpr}
    (henv : env.Ordered)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀) :
    ∀ {es : List VExpr} {A B : VExpr}, env.SpineWF U Γ₁ A es B →
      env.SpineWF U Γ (A.inst e₀ k)
        (es.map fun e => e.inst e₀ k) (B.inst e₀ k)
  | _, _, _, h => h.instN henv W h₀

/-- A generated projector computes on the matching generated constructor
once the registered rule's capture spine has been checked.  This is the
exact iota layer; constructor-head and parameter-prefix alignment are kept
outside this theorem. -/
theorem _root_.Ix.Theory.Named.VStructureView.WF.projector_constructor_exact
    (self : VStructureView.WF view env) (henv : env.WF)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {levels : List VLevel} (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {idx : Nat} {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {fields : List VExpr} (hfieldsLength :
      fields.length = (view.specializedFields levels params).length)
    {field : VExpr} (hfield : fields[idx]? = some field)
    (hctorType : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) (params ++ fields))
      (view.structureType levels params))
    (hfieldsSpine : env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) (.sort .zero))
      fields (.sort .zero))
    {B : VExpr}
    (hcaps : env.SpineWF U Γ
      ((view.generation.rule 0 view.constructor).type.instL
        (view.projectionLevels code.fieldSort levels))
      (params ++ [code.typeFn, code.minor] ++ fields) B) :
    env.IsDefEqU U Γ
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels) (params ++ fields)))
      field := by
  obtain ⟨fieldSort, hfieldSort, hcodeSort, hminorShape,
      hprojectorShape⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength hparamsSpine
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  let pLevels := view.projectionLevels code.fieldSort levels
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    VStructureView.projectionLevels_wf view code.fieldSort levels
      hfieldSortWF hlevels
  have hpLevelsLength : pLevels.length = view.generation.recUvars :=
    VStructureView.projectionLevels_length view code.fieldSort levels
      hlevelsLength
  have hruleMem : view.generation.rule 0 view.constructor ∈
      view.generation.generatedRules := by
    simp [VInductDecl.GenerationChecked.generatedRules,
      view.constructor_eq]
  have hregistered := self.rule_mem hruleMem
  have hruleWF := henv.ordered.defEqWF hregistered
  rw [hprojectorShape] at hprojector
  obtain ⟨_, ⟨projectorBodyType, hprojectorBody⟩⟩ :=
    hprojector.lam_inv henv.ordered hΓ
  have hprojectorBeta := VEnv.IsDefEq.beta hprojectorBody hctorType
  have hprojectorToRule : env.IsDefEqU U Γ
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels) (params ++ fields)))
      (VExpr.appN (.const view.recursorName pLevels)
        (params ++ [code.typeFn, code.minor,
          VExpr.appN (.const view.constructorName levels)
            (params ++ fields)])) := by
    refine ⟨projectorBodyType.inst
      (VExpr.appN (.const view.constructorName levels) (params ++ fields)), ?_⟩
    rw [hprojectorShape]
    simpa [pLevels, VExpr.inst, VExpr.instN_appN, VExpr.inst_lift,
      VExpr.instVar_zero,
      List.map_append, List.map_map, Function.comp_def] using
        hprojectorBeta
  let gen := view.generation
  let Bs := view.constructor.fieldsR view.source.uvars view.source.nparams
    gen.elimination
  let m := Bs.length
  let rs := view.constructor.recArgsR view.source.uvars gen.elimination
  let binders := gen.paramsTel ++ gen.motiveType :: gen.minorTypes ++
    VExpr.liftTelN (gen.block.ctorPairs.length + 1) Bs 0
  let recBase := VExpr.appN
    (.const (.str gen.block.sourceType.name "rec") gen.recLevels)
    (VExpr.bvarRevRange m (view.source.nparams +
      gen.block.ctorPairs.length + 1))
  let idxR := view.constructor.resultIndicesR view.source.uvars
    gen.elimination |>.map fun expression =>
      expression.liftN (gen.block.ctorPairs.length + 1) m
  let ctorApp := VExpr.appN
    (.const view.constructor.raw.name gen.sourceLevels)
    (VExpr.bvarRevRange (m + gen.block.ctorPairs.length + 1)
        view.source.nparams ++ VExpr.bvarRevRange 0 m)
  let ihs := rs.map fun recursive =>
    recursive.ruleCall m gen.block.ctorPairs.length recBase
  let lhsBody := VExpr.appN recBase (idxR ++ [ctorApp])
  let rhsBody := VExpr.appN
    (.bvar (gen.block.ctorPairs.length - 1 - 0 + m))
    (VExpr.bvarRevRange 0 m ++ ihs)
  let typeBody := VExpr.appN
    (.bvar (gen.block.ctorPairs.length + m)) (idxR ++ [ctorApp])
  have hlhs₀ := hruleWF.1
  change env.HasType gen.recUvars [] (VExpr.lamN binders lhsBody)
    (VExpr.forallN binders typeBody) at hlhs₀
  have hrhs₀ := hruleWF.2
  change env.HasType gen.recUvars [] (VExpr.lamN binders rhsBody)
    (VExpr.forallN binders typeBody) at hrhs₀
  have hlhs : env.HasType U Γ
      ((VExpr.lamN binders lhsBody).instL pLevels)
      ((VExpr.forallN binders typeBody).instL pLevels) :=
    (hlhs₀.instL hpLevelsWF).weak0 henv.ordered
  have hrhs : env.HasType U Γ
      ((VExpr.lamN binders rhsBody).instL pLevels)
      ((VExpr.forallN binders typeBody).instL pLevels) :=
    (hrhs₀.instL hpLevelsWF).weak0 henv.ordered
  rw [VExpr.instL_lamN, VExpr.instL_forallN] at hlhs hrhs
  have hcaps' : env.SpineWF U Γ
      (VExpr.forallN (binders.map (VExpr.instL pLevels))
        (typeBody.instL pLevels))
      (params ++ [code.typeFn, code.minor] ++ fields) B := by
    change env.SpineWF U Γ
      ((VExpr.forallN binders typeBody).instL pLevels)
      (params ++ [code.typeFn, code.minor] ++ fields) B at hcaps
    simpa only [VExpr.instL_forallN] using hcaps
  let S := self.toGenerationEnv henv.ordered
  have hparamsTelLength : gen.paramsTel.length = view.nparams := by
    simp [gen, VInductDecl.GenerationChecked.paramsTel,
      S.generationParams_length]
  have hspecializedLength :
      (view.specializedFields levels params).length =
        (view.constructor.rawFields view.nparams).length := by
    simp [VStructureView.specializedFields, VStructureView.fields]
  have hBsLength : Bs.length =
      (view.constructor.rawFields view.nparams).length := by
    simpa [Bs] using
      (VInductDecl.NormalizedCtor.fieldsR_length
        (source := view.source) view.constructor
        (mode := gen.elimination))
  have hcapturesLength :
      (params ++ [code.typeFn, code.minor] ++ fields).length =
        (binders.map (VExpr.instL pLevels)).length := by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map, VExpr.liftTelN_length, binders]
    rw [hparamsLength, hfieldsLength, hspecializedLength,
      hparamsTelLength, gen.minorTypes_length, view.constructor_eq,
      hBsLength]
    simp
  obtain ⟨hlhsTel, lhsType, hlhsBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hlhs
  obtain ⟨hrhsTel, rhsType, hrhsBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hrhs
  have hlhsSpine := hcaps'.retarget hcapturesLength lhsType
  have hrhsSpine := hcaps'.retarget hcapturesLength rhsType
  have hcollapseL := VEnv.IsDefEq.appN_lamN henv.ordered
    hlhsTel hlhsBody hlhsSpine hcapturesLength
  have hcollapseR := VEnv.IsDefEq.appN_lamN henv.ordered
    hrhsTel hrhsBody hrhsSpine hcapturesLength
  have hregisteredRule : env.IsDefEq U Γ
      ((view.generation.rule 0 view.constructor).lhs.instL pLevels)
      ((view.generation.rule 0 view.constructor).rhs.instL pLevels)
      ((view.generation.rule 0 view.constructor).type.instL pLevels) :=
    .extra hregistered hpLevelsWF hpLevelsLength
  have happlied := VEnv.IsDefEq.appN_congr hregisteredRule hcaps
  rw [show (view.generation.rule 0 view.constructor).lhs =
      VExpr.lamN binders lhsBody from rfl,
    show (view.generation.rule 0 view.constructor).rhs =
      VExpr.lamN binders rhsBody from rfl,
    VExpr.instL_lamN] at happlied
  simp only [VExpr.instL_lamN] at happlied
  have hiotaBodies : env.IsDefEqU U Γ
      (VExpr.instRev (lhsBody.instL pLevels)
        (params ++ [code.typeFn, code.minor] ++ fields))
      (VExpr.instRev (rhsBody.instL pLevels)
        (params ++ [code.typeFn, code.minor] ++ fields)) :=
    VEnv.IsDefEqU.trans henv hΓ ⟨_, hcollapseL.symm⟩
      (VEnv.IsDefEqU.trans henv hΓ ⟨_, happlied⟩ ⟨_, hcollapseR⟩)
  have hconstructorMem : view.constructor ∈
      view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    rw [S.viewResultIndices_length hconstructorMem]
    simp [view.checked_indices_eq]
  have hfieldsLengthRaw : fields.length = m := by
    exact hfieldsLength.trans (hspecializedLength.trans hBsLength.symm)
  have hprefixLength :
      (params ++ [code.typeFn, code.minor]).length = view.nparams + 2 := by
    simp [hparamsLength]
  have hcapturesLength' :
      (params ++ [code.typeFn, code.minor] ++ fields).length =
        view.nparams + 2 + m := by
    simp [hparamsLength, hfieldsLengthRaw]
    omega
  have hsegCommon :
      (VExpr.bvarRevRange m (view.nparams + 2)).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) =
        params ++ [code.typeFn, code.minor] := by
    have h := VExpr.map_instRev_bvarRevRange_seg
      (params ++ [code.typeFn, code.minor] ++ fields)
      (view.nparams + 2) m (by rw [hcapturesLength']; omega)
    rw [← hparamsLength] at h ⊢
    rw [show (params ++ [code.typeFn, code.minor] ++ fields).length -
        m - (params.length + 2) = 0 by
          simp only [List.length_append, List.length_cons, List.length_nil]
          rw [hfieldsLengthRaw]
          omega,
      List.drop_zero] at h
    rw [List.take_append,
      show params.length + 2 =
        (params ++ [code.typeFn, code.minor]).length by simp,
      List.take_length] at h
    simpa using h
  have hsegParams :
      (VExpr.bvarRevRange (m + 2) view.nparams).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) = params := by
    have h := VExpr.map_instRev_bvarRevRange_seg
      (params ++ [code.typeFn, code.minor] ++ fields)
      view.nparams (m + 2) (by rw [hcapturesLength']; omega)
    rw [← hparamsLength] at h ⊢
    rw [show (params ++ [code.typeFn, code.minor] ++ fields).length -
        (m + 2) - params.length = 0 by
          simp only [List.length_append, List.length_cons, List.length_nil]
          rw [hfieldsLengthRaw]
          omega,
      List.drop_zero] at h
    simpa using h
  have hsegFields :
      (VExpr.bvarRevRange 0 m).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) = fields := by
    have h := VExpr.map_instRev_bvarRevRange_seg
      (params ++ [code.typeFn, code.minor] ++ fields) m 0
      (by rw [hcapturesLength']; omega)
    rw [show (params ++ [code.typeFn, code.minor] ++ fields).length -
        0 - m = view.nparams + 2 by rw [hcapturesLength']; omega,
      show view.nparams + 2 =
        (params ++ [code.typeFn, code.minor]).length by
          exact hprefixLength.symm,
      List.drop_left] at h
    have htake : fields.take m = fields :=
      List.take_of_length_le (Nat.le_of_eq hfieldsLengthRaw)
    rw [htake] at h
    exact h
  have hsourceLevels := VStructureView.sourceLevels_projectionLevels
    view code.fieldSort levels hlevelsLength
  have hrecLevels : gen.recLevels.map (VLevel.inst pLevels) = pLevels := by
    exact VLevel.inst_map_id hpLevelsLength
  have hrecConst :
      VExpr.instRev
          ((.const (.str gen.block.sourceType.name "rec") gen.recLevels :
            VExpr).instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        .const view.recursorName pLevels := by
    rw [VExpr.instRev_closedN _ (by trivial)]
    simp only [VExpr.instL]
    rw [hrecLevels]
    rfl
  have hsegCommonL :
      (VExpr.bvarRevRange m (view.nparams + 2)).map
          (fun expression => VExpr.instRev (expression.instL pLevels)
            (params ++ [code.typeFn, code.minor] ++ fields)) =
        params ++ [code.typeFn, code.minor] := by
    calc
      _ = ((VExpr.bvarRevRange m (view.nparams + 2)).map
            (VExpr.instL pLevels)).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) := by
          rw [List.map_map]
          exact List.map_congr_left fun _ _ => rfl
      _ = _ := by
        rw [VExpr.bvarRevRange_map_instL]
        exact hsegCommon
  have hsegParamsL :
      (VExpr.bvarRevRange (m + 2) view.nparams).map
          (fun expression => VExpr.instRev (expression.instL pLevels)
            (params ++ [code.typeFn, code.minor] ++ fields)) = params := by
    calc
      _ = ((VExpr.bvarRevRange (m + 2) view.nparams).map
            (VExpr.instL pLevels)).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) := by
          rw [List.map_map]
          exact List.map_congr_left fun _ _ => rfl
      _ = _ := by
        rw [VExpr.bvarRevRange_map_instL]
        exact hsegParams
  have hsegFieldsL :
      (VExpr.bvarRevRange 0 m).map
          (fun expression => VExpr.instRev (expression.instL pLevels)
            (params ++ [code.typeFn, code.minor] ++ fields)) = fields := by
    calc
      _ = ((VExpr.bvarRevRange 0 m).map
            (VExpr.instL pLevels)).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) := by
          rw [List.map_map]
          exact List.map_congr_left fun _ _ => rfl
      _ = _ := by
        rw [VExpr.bvarRevRange_map_instL]
        exact hsegFields
  have hidxRNil : idxR = [] := by
    simp [idxR, VInductDecl.NormalizedCtor.resultIndicesR,
      hresultIndices]
  have hrecBaseShape :
      VExpr.instRev (recBase.instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        VExpr.appN (.const view.recursorName pLevels)
          (params ++ [code.typeFn, code.minor]) := by
    rw [show recBase = VExpr.appN
        (.const (.str gen.block.sourceType.name "rec") gen.recLevels)
        (VExpr.bvarRevRange m (view.nparams + 2)) by
          unfold recBase
          rw [view.constructor_eq]
          rfl,
      VExpr.instL_appN, VExpr.instRev_appN, hrecConst]
    rw [List.map_map]
    exact congrArg (VExpr.appN (.const view.recursorName pLevels))
      hsegCommonL
  have hctorShape :
      VExpr.instRev (ctorApp.instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        VExpr.appN (.const view.constructorName levels)
          (params ++ fields) := by
    rw [show ctorApp = VExpr.appN
        (.const view.constructorName gen.sourceLevels)
        (VExpr.bvarRevRange (m + 2) view.nparams ++
          VExpr.bvarRevRange 0 m) by
          unfold ctorApp
          rw [view.constructor_eq]
          rfl,
      VExpr.instL_appN, VExpr.instRev_appN]
    rw [VExpr.instRev_closedN _ (by trivial)]
    simp only [VExpr.instL]
    rw [hsourceLevels]
    simp only [List.map_append, List.map_map, Function.comp_def]
    rw [hsegParamsL, hsegFieldsL]
  have hleftShape :
      VExpr.instRev (lhsBody.instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        VExpr.appN (.const view.recursorName pLevels)
          (params ++ [code.typeFn, code.minor,
            VExpr.appN (.const view.constructorName levels)
              (params ++ fields)]) := by
    rw [show lhsBody = VExpr.appN recBase (idxR ++ [ctorApp]) by
          rfl,
      VExpr.instL_appN, VExpr.instRev_appN, hrecBaseShape, hidxRNil,
      List.nil_append]
    simp only [List.map_cons, List.map_nil, hctorShape]
    rw [← VExpr.appN_append]
    simp only [List.append_assoc]
    rfl
  have hminorCapture :
      VExpr.instRev (.bvar m)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        code.minor := by
    have h := VExpr.map_instRev_bvarRevRange_seg
      (params ++ [code.typeFn, code.minor] ++ fields) 1 m
      (by rw [hcapturesLength']; omega)
    rw [show (params ++ [code.typeFn, code.minor] ++ fields).length -
        m - 1 = params.length + 1 by
          rw [hcapturesLength', hparamsLength]
          omega] at h
    simpa [VExpr.bvarRevRange] using h
  have hrightBodyShape :
      rhsBody = VExpr.appN (.bvar m) (VExpr.bvarRevRange 0 m) := by
    simp [rhsBody, ihs, rs, gen,
      VInductDecl.NormalizedCtor.recArgsR, view.recursive_eq,
      view.constructor_eq]
  have hrightShape :
      VExpr.instRev (rhsBody.instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        VExpr.appN code.minor fields := by
    rw [hrightBodyShape, VExpr.instL_appN,
      VExpr.bvarRevRange_map_instL, VExpr.instRev_appN]
    simp only [VExpr.instL]
    rw [hminorCapture, hsegFields]
  rw [hleftShape, hrightShape] at hiotaBodies
  obtain ⟨selectedType, hselectedType, -⟩ :=
    view.projectionCodes_get?_typeFn levels params hcode
  have hidxLt : idx < (view.specializedFields levels params).length :=
    (List.getElem?_eq_some_iff.1 hselectedType).1
  let q := (view.specializedFields levels params).length - 1 - idx
  have hqLt : q < (view.specializedFields levels params).length := by
    simp only [q]
    omega
  have hselectedReverse :
      (view.specializedFields levels params).reverse[q]? =
        some selectedType := by
    rw [List.getElem?_reverse hqLt,
      show (view.specializedFields levels params).length - 1 - q = idx by
        simp only [q]
        omega,
      hselectedType]
  have hselectedCtx :
      ((view.specializedFields levels params).reverse ++ Γ)[q]? =
        some selectedType := by
    rw [List.getElem?_append_left (by simpa using hqLt),
      hselectedReverse]
  have hminorBodyType : env.HasType U
      ((view.specializedFields levels params).reverse ++ Γ)
      (.bvar q) (selectedType.liftN (q + 1)) :=
    .bvar (Lookup.of_getElem? hselectedCtx)
  have hminorSpine := hfieldsSpine.retarget hfieldsLength
    (selectedType.liftN (q + 1))
  have hminorBetaRaw := VEnv.IsDefEq.appN_lamN henv.ordered
    hsortTel.toOnTel hminorBodyType hminorSpine hfieldsLength
  have hfieldInst : VExpr.instRev (.bvar q) fields = field := by
    have h := VExpr.map_instRev_bvarRevRange_seg fields 1 q
      (by rw [hfieldsLength]; exact Nat.add_one_le_iff.2 hqLt)
    rw [show fields.length - q - 1 = idx by
      rw [hfieldsLength]
      simp only [q]
      omega] at h
    obtain ⟨hidxFields, hfieldGet⟩ :=
      List.getElem?_eq_some_iff.1 hfield
    rw [List.drop_eq_getElem_cons hidxFields, hfieldGet,
      List.take_succ_cons] at h
    simpa [VExpr.bvarRevRange] using h
  have hminorBeta : env.IsDefEqU U Γ
      (VExpr.appN code.minor fields) field := by
    refine ⟨VExpr.instRev (selectedType.liftN (q + 1)) fields, ?_⟩
    rw [hminorShape]
    simpa only [hfieldInst] using hminorBetaRaw
  exact VEnv.IsDefEqU.trans henv hΓ hprojectorToRule
    (VEnv.IsDefEqU.trans henv hΓ hiotaBodies hminorBeta)

/-- Environment-indexed projection semantics.

The universe and parameter spines are explicit.  The major premise must have
the exact instantiated structure type, and the result is the unique program
computed by the registered view. -/
structure TrProj (env : VEnv) (U : Nat) (Γ : List VExpr)
    (view : VStructureView) (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major result : VExpr) : Prop where
  viewWF : VStructureView.WF view env
  levelsWF : ∀ level ∈ levels, level.WF U
  levels_length : levels.length = view.uvars
  params_length : params.length = view.nparams
  paramsSpine : ∃ resultLevel,
    env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)
  majorType : env.HasType U Γ major (view.structureType levels params)
  program : ∃ code : VStructureView.ProjectionCode,
    (view.projectionCodes levels params)[idx]? = some code ∧
      result = .app code.projector major ∧
      env.HasType U Γ code.projector
        (.forallE (view.structureType levels params)
          (.app code.typeFn.lift (.bvar 0)))

/-- The projection-specific output of registered constructor-head inversion.

This package performs no iota computation.  It only aligns a constructor
normal form and one selected runtime argument with the canonical registered
view, and supplies the typed spines needed by
`projector_constructor_exact`. -/
structure ProjectionConstructorAlignment (env : VEnv) (U : Nat)
    (Γ : List VExpr) (view : VStructureView) (levels : List VLevel)
    (params : List VExpr) (idx : Nat)
    (code : VStructureView.ProjectionCode)
    (runtimeConstructorName : Name) (runtimeMajor runtimeField : VExpr) where
  constructor_name_eq : runtimeConstructorName = view.constructorName
  fields : List VExpr
  field : VExpr
  fields_length :
    fields.length = (view.specializedFields levels params).length
  field_get : fields[idx]? = some field
  constructorType : env.HasType U Γ
    (VExpr.appN (.const view.constructorName levels) (params ++ fields))
    (view.structureType levels params)
  fieldsSpine : env.SpineWF U Γ
    (VExpr.forallN (view.specializedFields levels params) (.sort .zero))
    fields (.sort .zero)
  captures : ∃ B, env.SpineWF U Γ
    ((view.generation.rule 0 view.constructor).type.instL
      (view.projectionLevels code.fieldSort levels))
    (params ++ [code.typeFn, code.minor] ++ fields) B
  major_eq : env.IsDefEqU U Γ runtimeMajor
    (VExpr.appN (.const view.constructorName levels) (params ++ fields))
  field_eq : env.IsDefEqU U Γ runtimeField field

/-- Consume registered-head alignment with the separately proved exact iota
theorem.  This keeps the transitional injectivity boundary from hiding the
projection computation itself. -/
theorem TrProj.projector_constructor_aligned
    (self : VEnv.TrProj env U Γ view levels params idx major result)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {runtimeMajor runtimeField : VExpr}
    {runtimeConstructorName : Name}
    (alignment : ProjectionConstructorAlignment env U Γ view levels params idx
      code runtimeConstructorName runtimeMajor runtimeField) :
    env.IsDefEqU U Γ (.app code.projector runtimeMajor) runtimeField := by
  have hmajorEq := alignment.major_eq.of_r henv hΓ
    alignment.constructorType
  have hmajorCongr : env.IsDefEqU U Γ
      (.app code.projector runtimeMajor)
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels)
          (params ++ alignment.fields))) :=
    ⟨_, hprojector.appDF hmajorEq⟩
  obtain ⟨captureType, hcaptures⟩ := alignment.captures
  have hiota := self.viewWF.projector_constructor_exact henv hΓ
    self.levelsWF self.levels_length self.params_length self.paramsSpine
    hcode hprojector alignment.fields_length alignment.field_get
    alignment.constructorType alignment.fieldsSpine hcaptures
  exact VEnv.IsDefEqU.trans henv hΓ hmajorCongr
    (VEnv.IsDefEqU.trans henv hΓ hiota alignment.field_eq.symm)

theorem TrProj.project_eq
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VStructureView.project? view levels params idx major = some result := by
  obtain ⟨code, hcode, rfl, -⟩ := self.program
  simp [VStructureView.project?, hcode]

theorem TrProj.type_eq
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    ∃ code : VStructureView.ProjectionCode,
      VStructureView.projectionType? view levels params idx major =
        some (VExpr.app code.typeFn major) := by
  obtain ⟨code, hcode, _, -⟩ := self.program
  exact ⟨code, by simp [VStructureView.projectionType?, hcode]⟩

/-- A fixed checked view, universe/parameter instantiation, field index, and
major determine the projection result syntactically. -/
theorem TrProj.result_eq
    (self : VEnv.TrProj env U Γ view levels params idx major result)
    (other : VEnv.TrProj env U Γ view levels params idx major result') :
    result = result' :=
  Option.some.inj (self.project_eq.symm.trans other.project_eq)

/-- Projection evidence is stable when the registered environment is
extended without changing any existing constants or reduction rules. -/
theorem TrProj.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VEnv.TrProj env' U Γ view levels params idx major result where
  viewWF := self.viewWF.mono henv
  levelsWF := self.levelsWF
  levels_length := self.levels_length
  params_length := self.params_length
  paramsSpine := self.paramsSpine.imp fun _ h => h.monoProjection henv
  majorType := self.majorType.mono henv
  program := self.program.imp fun _ ⟨hcode, hresult, htype⟩ =>
    ⟨hcode, hresult, htype.mono henv⟩

/-- Weakening acts pointwise on the explicit parameters, major, and computed
projection program. -/
theorem TrProj.weakN (henv : env.Ordered)
    (W : Ctx.LiftN n k Γ Γ')
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VEnv.TrProj env U Γ' view levels
      (params.map fun param => param.liftN n k) idx
      (major.liftN n k) (result.liftN n k) := by
  refine {
    viewWF := self.viewWF
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.weakN henv W
    program := ?_ }
  · have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
      simpa using (henv.closedC self.viewWF.family).instL
    obtain ⟨resultLevel, hspine⟩ := self.paramsSpine
    refine ⟨resultLevel, ?_⟩
    have hspine' := hspine.weakN henv W
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at hspine'
    simpa [VExpr.liftN] using hspine'
  · obtain ⟨code, hcode, rfl, htype⟩ := self.program
    refine ⟨code.liftN n k, ?_, rfl, ?_⟩
    rw [← self.viewWF.projectionCodes_liftN henv levels params
      self.params_length n k]
    simp only [List.getElem?_map, hcode, Option.map_some]
    simpa [VStructureView.ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_lift_projection] using htype.weakN henv W

/-- General context lifting, derived one inserted binder at a time from
`weakN`. -/
theorem TrProj.weak' (henv : env.Ordered)
    (W : Ctx.Lift' l Γ Γ')
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VEnv.TrProj env U Γ' view levels
      (params.map fun param => param.lift' l) idx
      (major.lift' l) (result.lift' l) := by
  generalize hdepth : l.depth = depth
  induction depth generalizing l Γ' with
  | zero =>
      have hctx := W.depth_zero hdepth
      subst Γ'
      simpa [VExpr.lift'_depth_zero (l := l) hdepth] using self
  | succ depth ih =>
      obtain ⟨tail, k, rfl, rfl⟩ := Lift.depth_succ hdepth
      obtain ⟨Γ₁, W₁, W₂⟩ := W.of_cons_skip
      have h := (ih W₁ Lift.depth_consN).weakN henv W₂
      rw [Lift.consN_skip_eq]
      have hlift : ∀ e : VExpr,
          e.lift' ((tail.consN k).comp
              (Lift.refl.skip.consN k)) =
            (e.lift' (tail.consN k)).liftN 1 k := by
        intro e
        rw [VExpr.lift'_comp, ← Lift.skipN_one,
          VExpr.lift'_consN_skipN]
      have hparams :
          params.map (fun param => param.lift' ((tail.consN k).comp
              (Lift.refl.skip.consN k))) =
            (params.map fun param => param.lift' (tail.consN k)).map
              (fun param => param.liftN 1 k) := by
        rw [List.map_map]
        exact List.map_congr_left fun param _ => hlift param
      rw [hparams, hlift major, hlift result]
      exact h

/-- Substitution acts pointwise on the explicit parameters, major, and
computed projection program. -/
theorem TrProj.instN (henv : env.Ordered)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀)
    (self : VEnv.TrProj env U Γ₁ view levels params idx major result) :
    VEnv.TrProj env U Γ view levels
      (params.map fun param => param.inst e₀ k) idx
      (major.inst e₀ k) (result.inst e₀ k) := by
  refine {
    viewWF := self.viewWF
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.instN henv W h₀
    program := ?_ }
  · have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
      simpa using (henv.closedC self.viewWF.family).instL
    obtain ⟨resultLevel, hspine⟩ := self.paramsSpine
    refine ⟨resultLevel, ?_⟩
    have hspine' := hspine.instNProjection henv W h₀
    rw [hfamilyClosed.instN_eq (Nat.zero_le _)] at hspine'
    simpa [VExpr.inst] using hspine'
  · obtain ⟨code, hcode, rfl, htype⟩ := self.program
    refine ⟨code.instN e₀ k, ?_, rfl, ?_⟩
    rw [← self.viewWF.projectionCodes_instN henv levels params
      self.params_length e₀ k]
    simp only [List.getElem?_map, hcode, Option.map_some]
    simpa [VStructureView.ProjectionCode.instN, VExpr.inst,
      ← VExpr.lift_instN_lo] using htype.instN henv W h₀

/-- Transport projection evidence to a definitionally equal context and a
new major already checked against the same instantiated structure type. -/
theorem TrProj.defeqDFC (henv : env.Ordered)
    (hΓ : env.IsDefEqCtx U Γ₀ Γ₁ Γ₂)
    (majorType' : env.HasType U Γ₂ major'
      (view.structureType levels params))
    (self : VEnv.TrProj env U Γ₁ view levels params idx major result) :
    ∃ result', VEnv.TrProj env U Γ₂ view levels params idx major' result' := by
  obtain ⟨code, hcode, -, htype⟩ := self.program
  refine ⟨.app code.projector major', {
    viewWF := self.viewWF
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := self.params_length
    paramsSpine := self.paramsSpine.imp fun _ h => h.defeqDFC henv hΓ
    majorType := majorType'
    program := ⟨code, hcode, rfl,
      htype.defeqDFC henv hΓ⟩ }⟩

/-- Universe instantiation acts pointwise on the explicit structure
universes and parameters, and on the recursor program they determine. -/
theorem TrProj.instL {ls : List VLevel}
    (hls : ∀ level ∈ ls, level.WF U')
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VEnv.TrProj env U' (Γ.map (VExpr.instL ls)) view
      (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls)) idx
      (major.instL ls) (result.instL ls) := by
  refine {
    viewWF := self.viewWF
    levelsWF := ?_
    levels_length := by simpa using self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.instL hls
    program := ?_ }
  · intro level hlevel
    obtain ⟨sourceLevel, hsourceLevel, rfl⟩ := List.mem_map.1 hlevel
    exact VLevel.WF.inst hls
  · obtain ⟨resultLevel, hspine⟩ := self.paramsSpine
    refine ⟨resultLevel.inst ls, ?_⟩
    simpa [VExpr.instL, VExpr.instL_instL] using hspine.instL hls
  · obtain ⟨code, hcode, rfl, htype⟩ := self.program
    refine ⟨code.instL ls, ?_, ?_, ?_⟩
    · rw [← VStructureView.projectionCodes_instL]
      simp only [List.getElem?_map, hcode, Option.map_some]
    · rfl
    · simpa [VStructureView.ProjectionCode.instL, VExpr.instL,
        VExpr.instL_liftN] using htype.instL hls

/-- The registered-structure constant-head inversion boundary.

The four conclusions are the projection-specific eliminators supplied by
constant-head injectivity: a type assigned to a syntactically weakened major
recovers an instantiation below the inserted context; definitionally equal
majors recover the same registered view/instantiation strongly enough for the
generated projector programs to be definitionally equal; a runtime
constructor head recovers the registered constructor name; and that head plus
one selected argument is aligned with the registered constructor and field.
The last conclusion deliberately provides only typed alignment—the iota step
remains the proved `projector_constructor_exact` theorem.

Its eventual proof uses `IsDefEqU.weakN_iff` together with injectivity of
registered inductive heads.  Keeping the boundary in Theory makes the
remaining inversion and injectivity dependencies explicit instead of leaving Verify's
structural laws as local holes. -/
structure RegisteredStructureHeadInversion (env : VEnv) : Prop where
  weak'_inv :
    ∀ {U : Nat} {Γ Γ' : List VExpr} {view : VStructureView}
      {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {major result : VExpr} {lift : Lift},
      OnCtx Γ' (env.IsType U) →
      Ctx.Lift' lift Γ Γ' →
      env.TrProj U Γ' view levels params idx (major.lift' lift) result →
      ∃ params' result',
        env.TrProj U Γ view levels params' idx major result'
  unique :
    ∀ {U : Nat} {Γ₁ Γ₂ : List VExpr}
      {view₁ view₂ : VStructureView}
      {levels₁ levels₂ : List VLevel} {params₁ params₂ : List VExpr}
      {idx : Nat} {major₁ major₂ result₁ result₂ : VExpr},
      env.IsDefEqCtx U [] Γ₁ Γ₂ →
      env.TrProj U Γ₁ view₁ levels₁ params₁ idx major₁ result₁ →
      env.TrProj U Γ₂ view₂ levels₂ params₂ idx major₂ result₂ →
      env.IsDefEqU U Γ₁ major₁ major₂ →
      env.IsDefEqU U Γ₁ result₁ result₂
  constructor_name_inv :
    ∀ {U : Nat} {Γ : List VExpr} {view : VStructureView}
      {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {major result runtimeMajor : VExpr}
      {constructorName : Name} {constructorLevels : List VLevel}
      {constructorArgs : List VExpr},
      OnCtx Γ (env.IsType U) →
      env.TrProj U Γ view levels params idx major result →
      runtimeMajor = VExpr.appN
        (.const constructorName constructorLevels) constructorArgs →
      env.IsDefEqU U Γ runtimeMajor major →
      constructorName = view.constructorName
  constructor_inv :
    ∀ {U : Nat} {Γ : List VExpr} {view : VStructureView}
      {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {major result : VExpr} {code : VStructureView.ProjectionCode}
      {runtimeMajor runtimeField : VExpr}
      {constructorName : Name} {constructorLevels : List VLevel}
      {constructorArgs : List VExpr},
      OnCtx Γ (env.IsType U) →
      env.TrProj U Γ view levels params idx major result →
      (view.projectionCodes levels params)[idx]? = some code →
      runtimeMajor = VExpr.appN
        (.const constructorName constructorLevels) constructorArgs →
      constructorArgs[view.nparams + idx]? = some runtimeField →
      env.IsDefEqU U Γ runtimeMajor major →
      Nonempty (ProjectionConstructorAlignment env U Γ view levels params idx
        code constructorName runtimeMajor runtimeField)

set_option warn.sorry false in
/-- Registered-head inversion statement. The constant-head inversion proof
remains unfinished. Projection structural laws consume this interface and
inherit its `sorryAx` dependency until that proof is supplied. -/
theorem WF.registeredStructureHeadInversion
    (self : VEnv.WF env) : RegisteredStructureHeadInversion env := by
  sorry

#guard_named_axioms Ix.Theory.Named.VEnv.WF.registeredStructureHeadInversion [propext, sorryAx, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.TrProj.result_eq [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.TrProj.mono [propext, Quot.sound]

end VEnv

end Ix.Theory.Named
