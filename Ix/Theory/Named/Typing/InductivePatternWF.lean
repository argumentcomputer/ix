/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Typing.InductivePattern
import Ix.Theory.Named.Typing.UniqueTyping

open Ix.Theory (VLevel)

/-! # Pattern soundness for generated iota rules

Typed β-collapse: applying a lambda tower to a
well-typed argument spine is definitionally equal to the iterated
instantiation of its body (`IsDefEq.appN_lamN`), applications are
congruent along spines (`IsDefEq.appN_congr`, `IsDefEq.appN_defEq` over
`SpineDefEq`), and a matched pattern's captures are exactly the spine
arguments (`varN_matches_paths`). `pat_wf` then proves that a successful
match whose checks hold is definitionally equal to its RHS template — by
applying the registered `addInduct` rule tower to the captured arguments
and β-collapsing both readings. -/

namespace Ix.Theory.Named

open VExpr

namespace VExpr

/-- Instantiation pushes under a lambda telescope, mirroring
`instN_forallN`. -/
theorem instN_lamN (a : VExpr) : ∀ (tel : List VExpr) (X : VExpr) (k : Nat),
    (lamN tel X).inst a k = lamN (instTelN a tel k) (X.inst a (k + tel.length))
  | [], _, _ => rfl
  | A :: tel, X, k => by
    show VExpr.lam _ _ = VExpr.lam _ _
    rw [instN_lamN a tel X (k+1),
      show k+1+tel.length = k+(tel.length+1) from by omega]
    rfl

/-- Universe instantiation pushes under a lambda telescope. -/
theorem instL_lamN (ls : List VLevel) : ∀ (As : List VExpr) (e : VExpr),
    (lamN As e).instL ls = lamN (As.map (instL ls)) (e.instL ls)
  | [], _ => rfl
  | A :: As, e => by
    show VExpr.lam _ _ = VExpr.lam _ _
    rw [instL_lamN ls As e]

end VExpr

/-- Matching a constant `varN` tower captures exactly the spine arguments:
the `varNPaths` read back the argument list. -/
theorem Pattern.varN_matches_paths {c : Name} {m1 : List VLevel} :
    ∀ (n : Nat) (as : List VExpr) {f : VExpr} {m2},
      (Pattern.varN (.const c) n).Matches (VExpr.appN f as) m1 m2 →
      as.length = n →
      (Pattern.varNPaths (.const c) n).map m2 = as := by
  intro n
  induction n with
  | zero =>
    intro as f m2 H hlen
    obtain rfl : as = [] := List.length_eq_zero_iff.1 hlen
    rfl
  | succ n ih =>
    intro as f m2 H hlen
    have hne : as ≠ [] := by rintro rfl; simp at hlen
    obtain ⟨as', a, rfl⟩ : ∃ as' a, as = as' ++ [a] :=
      ⟨as.dropLast, as.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    rw [VExpr.appN_append] at H
    have has : as'.length = n := by simpa using hlen
    cases H with
    | var h =>
      show ((Pattern.varNPaths (.const c) n).map some ++ [none]).map _ =
        as' ++ [a]
      rw [List.map_append, List.map_map]
      exact congrArg (· ++ [a]) (ih as' h has)

/-- Applying an RHS template spine computes to the applied template
values. -/
theorem Pattern.RHS.appN_apply {p : Pattern} (m1 : List VLevel)
    (m2 : p.Path → VExpr) :
    ∀ (f : p.RHS) (as : List (p.RHS)),
      (Pattern.RHS.appN f as).apply m1 m2 =
        VExpr.appN (f.apply m1 m2) (as.map (Pattern.RHS.apply m1 m2))
  | _, [] => rfl
  | f, a :: as => by
    show (Pattern.RHS.appN (.app f a) as).apply m1 m2 = _
    rw [Pattern.RHS.appN_apply m1 m2 (.app f a) as]
    rfl

/-- A `HeadConstN` spine names its argument list. -/
theorem HeadConstN.exists_appN {c : Name} {ls : List VLevel} :
    ∀ {n : Nat} {e : VExpr}, HeadConstN c ls n e →
      ∃ as : List VExpr, e = VExpr.appN (.const c ls) as ∧ as.length = n
  | _, _, .const => ⟨[], rfl, rfl⟩
  | _, _, .app (a := a) h =>
    let ⟨as, he, hl⟩ := h.exists_appN
    ⟨as ++ [a], by rw [VExpr.appN_append, ← he]; rfl, by simp [hl]⟩

namespace VExpr

/-- The value of a bound variable under iterated instantiation: the spine
argument at its reverse position. -/
theorem instRev_bvar_lt : ∀ (es : List VExpr) {i : Nat} (h : i < es.length),
    instRev (.bvar i) es = es[es.length - 1 - i]'(by omega)
  | e :: es, i, h => by
    rcases Nat.lt_or_ge i es.length with h' | h'
    · rw [show instRev (.bvar i) (e :: es) = instRev (.bvar i) es from
        instRev_bvar_lt_cons es e h', instRev_bvar_lt es h']
      simp only [show (e :: es).length - 1 - i = (es.length - 1 - i) + 1 from by
        simp only [List.length_cons]; omega, List.getElem_cons_succ]
    · obtain rfl : i = es.length := by
        simp only [List.length_cons] at h; omega
      show instRev (instVar es.length e es.length) es = _
      rw [show instVar es.length e es.length = liftN es.length e from by
        simp [instVar]]
      rw [instRev_liftN_len]
      simp only [show (e :: es).length - 1 - es.length = 0 from by
        simp only [List.length_cons]; omega, List.getElem_cons_zero]

/-- Iterated instantiation of a reverse bound-variable segment reads back
the corresponding spine segment. -/
theorem map_instRev_bvarRevRange_seg (es : List VExpr) :
    ∀ (q off : Nat), off + q ≤ es.length →
    (bvarRevRange off q).map (instRev · es) =
      (es.drop (es.length - off - q)).take q := by
  intro q
  induction q with
  | zero => intro off h; simp [VExpr.bvarRevRange]
  | succ q ih =>
    intro off h
    show instRev (.bvar (off + q)) es :: (bvarRevRange off q).map (instRev · es) = _
    rw [instRev_bvar_lt es (by omega), ih off (by omega)]
    have hd : es.length - off - (q + 1) < es.length := by omega
    simp only [show es.length - 1 - (off + q) = es.length - off - (q + 1) from by
      omega, show es.length - off - q = (es.length - off - (q + 1)) + 1 from by
      omega]
    rw [List.drop_eq_getElem_cons hd, List.take_succ_cons]

end VExpr

/-! ## Typed β-collapse of applied telescopes -/

/-- Instantiating below a reversed telescope, mirroring
`Ctx.LiftN.consTel`. -/
theorem Ctx.InstN.consTel {Γ₀ : List VExpr} {e₀ A₀ : VExpr} :
    ∀ (As : List VExpr) {k : Nat} {Γ Γ' : List VExpr},
      Ctx.InstN Γ₀ e₀ A₀ k Γ Γ' →
      Ctx.InstN Γ₀ e₀ A₀ (As.length + k) (As.reverse ++ Γ)
        ((VExpr.instTelN e₀ As k).reverse ++ Γ')
  | [], k, Γ, Γ', W => by simpa [VExpr.instTelN] using W
  | A :: As, k, Γ, Γ', W => by
    have h := Ctx.InstN.consTel As (Ctx.InstN.succ (A := A) W)
    rw [show As.length + (k+1) = (A :: As).length + k from by simp; omega] at h
    simpa [VExpr.instTelN, List.append_assoc] using h

/-- Instantiating a telescope's context. -/
theorem VEnv.OnTel.instN {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} (h₀ : env.HasType U Γ₀ e₀ A₀) :
    ∀ {As : List VExpr} {k : Nat} {Γ Γ' : List VExpr},
      Ctx.InstN Γ₀ e₀ A₀ k Γ Γ' → VEnv.OnTel env U Γ As →
      VEnv.OnTel env U Γ' (VExpr.instTelN e₀ As k)
  | [], _, _, _, _, _ => trivial
  | _ :: _, _, _, _, W, ⟨⟨u, hA⟩, hT⟩ =>
    ⟨⟨u, hA.instN henv W h₀⟩, VEnv.OnTel.instN henv h₀ W.succ hT⟩

/-- Pointwise defeq of two application spines against a peeled pi type. -/
inductive VEnv.SpineDefEq (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → List VExpr → List VExpr → VExpr → Prop where
  | nil : VEnv.SpineDefEq env U Γ A [] [] A
  | cons : env.IsDefEq U Γ a a' A₁ →
      VEnv.SpineDefEq env U Γ (A₂.inst a) es es' B →
      VEnv.SpineDefEq env U Γ (.forallE A₁ A₂) (a :: es) (a' :: es') B

/-- Iterated application congruence along a pointwise defeq spine. -/
theorem VEnv.IsDefEq.appN_defEq {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {es es' : List VExpr} {F B X Y : VExpr},
      env.IsDefEq U Γ X Y F → VEnv.SpineDefEq env U Γ F es es' B →
      env.IsDefEq U Γ (VExpr.appN X es) (VExpr.appN Y es') B
  | [], _, _, _, _, _, h, .nil => h
  | a :: _, a' :: _, _, _, X, Y, h, .cons ha hrest =>
    VEnv.IsDefEq.appN_defEq (X := X.app a) (Y := Y.app a') (h.appDF ha) hrest

/-- A well-typed spine is a reflexive defeq spine. -/
theorem VEnv.SpineWF.toSpineDefEq {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {es : List VExpr} {F B : VExpr}, env.SpineWF U Γ F es B →
      VEnv.SpineDefEq env U Γ F es es B
  | [], _, _, .nil => .nil
  | _ :: _, _, _, .cons ha hrest => .cons ha hrest.toSpineDefEq

/-- Iterated application congruence in the function position. -/
theorem VEnv.IsDefEq.appN_congr {env : VEnv} {U : Nat} {Γ : List VExpr}
    {es : List VExpr} {F B X Y : VExpr}
    (h : env.IsDefEq U Γ X Y F) (hs : env.SpineWF U Γ F es B) :
    env.IsDefEq U Γ (VExpr.appN X es) (VExpr.appN Y es) B :=
  h.appN_defEq hs.toSpineDefEq

/-- A registered equation remains available after environment growth.

This is the primitive transport operation for consumer-certified extension
rules: `VEnv.LE` transports registration, while the core `.extra` constructor
still requires the exact universe instantiation side conditions. -/
theorem VEnv.LE.extra {env env' : VEnv} (henv : env ≤ env') {U : Nat}
    {Γ : List VExpr} {df : VDefEq} {ls : List VLevel}
    (hreg : env.defeqs df) (hlevels : ∀ l ∈ ls, l.WF U)
    (hlevelsLength : ls.length = df.uvars) :
    env'.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls)
      (df.type.instL ls) :=
  .extra (henv.defeqs hreg) hlevels hlevelsLength

/-- Transport a registered equation through environment growth and then
apply it to a well-typed spine. This is the beta-tower consumer boundary:
registration supplies only the tower equality; application congruence and
spine typing remain explicit proof obligations. -/
theorem VEnv.LE.extra_appN {env env' : VEnv} (henv : env ≤ env') {U : Nat}
    {Γ : List VExpr} {df : VDefEq} {ls : List VLevel} {args : List VExpr}
    {B : VExpr} (hreg : env.defeqs df)
    (hlevels : ∀ l ∈ ls, l.WF U) (hlevelsLength : ls.length = df.uvars)
    (hspine : env.SpineWF U Γ (df.type.instL ls) args B) :
    env'.IsDefEq U Γ
      (VExpr.appN (df.lhs.instL ls) args)
      (VExpr.appN (df.rhs.instL ls) args) B :=
  (henv.extra hreg hlevels hlevelsLength).appN_congr (hspine.mono henv)

/-- The symmetric applied transport is derived, not a second trusted
extension direction. -/
theorem VEnv.LE.extra_appN_symm {env env' : VEnv} (henv : env ≤ env')
    {U : Nat} {Γ : List VExpr} {df : VDefEq} {ls : List VLevel}
    {args : List VExpr} {B : VExpr} (hreg : env.defeqs df)
    (hlevels : ∀ l ∈ ls, l.WF U) (hlevelsLength : ls.length = df.uvars)
    (hspine : env.SpineWF U Γ (df.type.instL ls) args B) :
    env'.IsDefEq U Γ
      (VExpr.appN (df.rhs.instL ls) args)
      (VExpr.appN (df.lhs.instL ls) args) B :=
  (henv.extra_appN hreg hlevels hlevelsLength hspine).symm

/-- Applying a lambda telescope to a full well-typed spine collapses to the
iterated instantiation of its body. -/
theorem VEnv.IsDefEq.appN_lamN {env : VEnv} (henv : env.Ordered) {U : Nat} :
    ∀ {As : List VExpr} {Γ : List VExpr} {body T B : VExpr} {es : List VExpr},
      VEnv.OnTel env U Γ As →
      env.HasType U (As.reverse ++ Γ) body T →
      env.SpineWF U Γ (VExpr.forallN As T) es B →
      es.length = As.length →
      env.IsDefEq U Γ (VExpr.appN (VExpr.lamN As body) es)
        (VExpr.instRev body es) B
  | [], Γ, body, T, B, es, _, hb, hs, hlen => by
    obtain rfl : es = [] := List.length_eq_zero_iff.1 hlen
    obtain rfl : T = B := hs.nil_inv
    exact hb
  | A :: As, Γ, body, T, B, e :: es, ⟨⟨u, hA⟩, hT⟩, hb,
      .cons he hrest, hlen => by
    have hb' : env.HasType U (As.reverse ++ (A :: Γ)) body T := by
      simpa [List.append_assoc] using hb
    have hlam : env.HasType U (A :: Γ) (VExpr.lamN As body)
        (VExpr.forallN As T) := VEnv.HasType.lamN hT hb'
    have hbeta := VEnv.IsDefEq.beta hlam he
    rw [VExpr.instN_lamN, Nat.zero_add] at hbeta
    have hlen2 : es.length = As.length := by simpa using hlen
    have hT' : VEnv.OnTel env U Γ (VExpr.instTelN e As 0) :=
      VEnv.OnTel.instN henv he .zero hT
    have hb'' : env.HasType U ((VExpr.instTelN e As 0).reverse ++ Γ)
        (body.inst e As.length) (T.inst e As.length) := by
      have W := Ctx.InstN.consTel (Γ₀ := Γ) (e₀ := e) (A₀ := A) As .zero
      have := hb'.instN henv W he
      simpa using this
    have hrest' : env.SpineWF U Γ
        (VExpr.forallN (VExpr.instTelN e As 0) (T.inst e As.length)) es B := by
      rw [VExpr.instN_forallN] at hrest
      simpa using hrest
    have hlen' : es.length = (VExpr.instTelN e As 0).length := by
      rw [VExpr.instTelN_length]; exact hlen2
    have IH := VEnv.IsDefEq.appN_lamN henv hT' hb'' hrest' hlen'
    have hstep := VEnv.IsDefEq.appN_congr hbeta hrest
    show env.IsDefEq U Γ
      (VExpr.appN ((VExpr.lam A (VExpr.lamN As body)).app e) es)
      (VExpr.instRev (body.inst e es.length) es) B
    rw [hlen2]
    exact hstep.trans IH

/-- Instantiate a terminal definitional equality through a saturated telescope spine. -/
theorem VEnv.SpineWF.instRev_defeq
    {env : VEnv} (henv : env.Ordered) {U : Nat} {Γ : List VExpr} :
    ∀ {As : List VExpr} {C C' T : VExpr} {es : List VExpr} {B : VExpr},
      env.SpineWF U Γ (VExpr.forallN As C) es B →
      es.length = As.length →
      env.IsDefEq U (As.reverse ++ Γ) C C' T →
      env.IsDefEq U Γ (VExpr.instRev C es) (VExpr.instRev C' es)
        (VExpr.instRev T es)
  | [], C, C', T, [], B, hspine, _, hterminal => by
      simpa [VExpr.instRev] using hterminal
  | [], _, _, _, _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, _, _, _, [], _, _, hlen, _ => by simp at hlen
  | A :: As, C, C', T, e :: es, B,
      .cons he hrest, hlen, hterminal => by
      have hlen' : es.length = As.length := by simpa using hlen
      have W := Ctx.InstN.consTel (Γ₀ := Γ) (e₀ := e) (A₀ := A) As .zero
      have hterminal₀ : env.IsDefEq U (As.reverse ++ A :: Γ) C C' T := by
        simpa [List.reverse_cons, List.append_assoc] using hterminal
      have hterminal' := hterminal₀.instN henv he W
      have hrest' : env.SpineWF U Γ
          (VExpr.forallN (VExpr.instTelN e As 0)
            (C.inst e As.length)) es B := by
        rw [VExpr.instN_forallN] at hrest
        simpa using hrest
      have hout := VEnv.SpineWF.instRev_defeq henv hrest'
        (by simpa [VExpr.instTelN_length] using hlen') hterminal'
      simpa [VExpr.instRev, hlen'] using hout

/-- Iterated inversion of a lambda tower's typing: the telescope is
well-formed and the body is typed under it. -/
theorem VEnv.HasType.lamN_wf {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {As : List VExpr} {Γ : List VExpr} {body V : VExpr},
      OnCtx Γ (env.IsType U) →
      env.HasType U Γ (VExpr.lamN As body) V →
      VEnv.OnTel env U Γ As ∧
        ∃ T₀, env.HasType U (As.reverse ++ Γ) body T₀
  | [], Γ, body, V, _, H => ⟨trivial, V, H⟩
  | A :: As, Γ, body, V, hΓ, H => by
    obtain ⟨⟨u, hA⟩, W, hrest⟩ := VEnv.HasType.lam_inv henv hΓ H
    obtain ⟨hT, T₀, hbody⟩ :=
      VEnv.HasType.lamN_wf henv (As := As) (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hrest
    exact ⟨⟨⟨u, hA⟩, hT⟩, T₀, by simpa [List.append_assoc] using hbody⟩

/-- The levels of a `HeadConstN` spine are unique. -/
theorem HeadConstN.levels_uniq {c : Name} :
    ∀ {n : Nat} {e : VExpr} {ls ls' : List VLevel},
      HeadConstN c ls n e → HeadConstN c ls' n e → ls = ls'
  | _, _, _, _, .const, .const => rfl
  | _, _, _, _, .app h, .app h' => h.levels_uniq h'

/-- Zip a well-typed spine with pointwise defeqs into a defeq spine.
Reflexive entries need no defeq evidence. -/
theorem VEnv.SpineWF.defEq_of_pointwise {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {es es' : List VExpr} {F B : VExpr},
      env.SpineWF U Γ F es B →
      List.Forall₂ (fun a a' => a = a' ∨ env.IsDefEqU U Γ a a') es es' →
      VEnv.SpineDefEq env U Γ F es es' B
  | [], [], _, _, .nil, .nil => .nil
  | _ :: _, _ :: _, _, _, .cons he hrest, .cons hd htl => by
    refine .cons ?_ (hrest.defEq_of_pointwise henv hΓ htl)
    rcases hd with rfl | hd
    · exact he
    · exact VEnv.IsDefEqU.of_l henv hΓ hd he

/-- Unfold the `OK` predicate through a folded list of defeq checks. -/
theorem Pattern.Check.OK.of_foldr {p : Pattern} {α : Type _}
    {df : VExpr → VExpr → Prop} {m1 : List VLevel} {m2 : p.Path → VExpr}
    (f g : α → p.RHS) :
    ∀ {xs : List α} {rest : p.Check},
      ((xs.foldr (fun x acc => Pattern.Check.defeq (f x) (g x) acc)
        rest).OK df m1 m2) →
      (∀ x ∈ xs, df ((f x).apply m1 m2) ((g x).apply m1 m2)) ∧
        rest.OK df m1 m2
  | [], _, h => ⟨nofun, h⟩
  | _ :: xs, rest, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h3, h4⟩ := Pattern.Check.OK.of_foldr f g (xs := xs) h2
    refine ⟨fun x hx => ?_, h4⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact h3 x hx

/-- Build a pointwise relation between two mapped lists from their zip. -/
private theorem forall₂_zip_map {α β : Type _} (F : α → VExpr) (G : β → VExpr)
    (R : VExpr → VExpr → Prop) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (∀ p ∈ xs.zip ys, R (F p.1) (G p.2)) →
      List.Forall₂ R (xs.map F) (ys.map G)
  | [], [], _, _ => .nil
  | x :: xs, y :: ys, hlen, hall =>
    .cons (hall (x, y) (.head _))
      (forall₂_zip_map F G R xs ys (by simpa using hlen)
        fun p hp => hall p (.tail _ hp))
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

/-- Universe instantiation fixes a reverse bound-variable range. -/
theorem VExpr.bvarRevRange_map_instL (ls : List VLevel) :
    ∀ (off m : Nat),
      (VExpr.bvarRevRange off m).map (VExpr.instL ls) =
        VExpr.bvarRevRange off m
  | _, 0 => rfl
  | off, m+1 => by
    simp only [VExpr.bvarRevRange, List.map_cons, VExpr.instL,
      VExpr.bvarRevRange_map_instL ls off m]

/-- A well-formed telescope extends a well-formed context. -/
theorem VEnv.OnTel.onCtx {env : VEnv} {U : Nat} :
    ∀ {As Γ : List VExpr}, OnCtx Γ (env.IsType U) →
      VEnv.OnTel env U Γ As → OnCtx (As.reverse ++ Γ) (env.IsType U)
  | [], _, hΓ, _ => hΓ
  | A :: As, Γ, hΓ, ⟨hA, hT⟩ => by
    simpa [List.append_assoc] using
      VEnv.OnTel.onCtx (As := As) (Γ := A :: Γ) ⟨hΓ, hA⟩ hT

/-- Every argument of a well-typed application spine is well-typed. -/
theorem VEnv.HasType.appN_args_wf {env : VEnv} (henv : env.WF) {U : Nat}
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (n : Nat) (es : List VExpr), es.length = n → ∀ {f B : VExpr},
      env.HasType U Γ (VExpr.appN f es) B →
      ∀ e ∈ es, ∃ T, env.HasType U Γ e T := by
  intro n
  induction n with
  | zero =>
    intro es hlen f B H e he
    obtain rfl := List.length_eq_zero_iff.1 hlen
    cases he
  | succ n ih =>
    intro es hlen f B H e he
    have hne : es ≠ [] := by rintro rfl; simp at hlen
    obtain ⟨es', a, rfl⟩ : ∃ es' a, es = es' ++ [a] :=
      ⟨es.dropLast, es.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    rw [VExpr.appN_append] at H
    have H' : env.HasType U Γ ((VExpr.appN f es').app a) B := H
    obtain ⟨A₁, B₁, hf, ha⟩ := H'.app_inv henv hΓ
    rcases List.mem_append.1 he with he' | he'
    · exact ih es' (by simpa using hlen) hf e he'
    · obtain rfl : e = a := by simpa using he'
      exact ⟨A₁, ha⟩

/-- Iterated inversion of a pi tower's typing: the telescope is well formed
and the body is typed under it. -/
theorem VEnv.HasType.forallN_wf {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {As : List VExpr} {Γ : List VExpr} {body V : VExpr},
      env.HasType U Γ (VExpr.forallN As body) V →
      VEnv.OnTel env U Γ As ∧ ∃ V', env.HasType U (As.reverse ++ Γ) body V'
  | [], _, _, V, H => ⟨trivial, V, H⟩
  | A :: As, Γ, body, V, H => by
    obtain ⟨⟨u, hA⟩, v, hB⟩ := VEnv.HasType.forallE_inv henv H
    obtain ⟨hT, V', hbody⟩ := VEnv.HasType.forallN_wf henv (As := As) hB
    exact ⟨⟨⟨u, hA⟩, hT⟩, V', by simpa [List.append_assoc] using hbody⟩

private theorem forall₂_refl_or {R : VExpr → VExpr → Prop} :
    ∀ (l : List VExpr), List.Forall₂ (fun a a' => a = a' ∨ R a a') l l
  | [] => .nil
  | _ :: l => .cons (Or.inl rfl) (forall₂_refl_or l)

private theorem forall₂_append {R : VExpr → VExpr → Prop} :
    ∀ {l₁ l₂ l₁' l₂' : List VExpr}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R l₁' l₂' → List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂')
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons hd htl, h => .cons hd (forall₂_append htl h)

namespace VInductDecl

namespace BlockGenerationChecked

variable {source : VInductDecl} (gen : source.BlockGenerationChecked)

/-! ## Named shapes of one generated rule -/

theorem rule_type (i : Nat) (c : NormalizedBlockCtor) :
    (gen.rule i c).type =
      VExpr.forallN (gen.ruleBinders c)
        (VExpr.appN
          (.bvar (gen.familyCount - 1 - c.owner + gen.minorCount +
            gen.ruleFieldCount c))
          (gen.ruleIdx c ++ [gen.ruleCtorApp c])) := rfl

theorem rule_uvars (i : Nat) (c : NormalizedBlockCtor) :
    (gen.rule i c).uvars = gen.recUvars := rfl

theorem paramsTel_length : gen.paramsTel.length = source.nparams := by
  show ((generationParams gen.block.rawParams gen.block.checked.params).map
    (VExpr.instL gen.sourceLevels)).length = _
  rw [List.length_map]
  exact (generationParams_length_of_eq gen.shape.2.1).trans gen.shape.1

theorem ruleBinders_length (c : NormalizedBlockCtor) :
    (gen.ruleBinders c).length =
      source.nparams + gen.familyCount + gen.minorCount +
        gen.ruleFieldCount c := by
  simp only [ruleBinders, List.length_append, gen.paramsTel_length,
    motiveTypes, gen.motiveTypesAux_length, minorTypes,
    gen.minorTypesAux_length, VExpr.liftTelN_length, ruleFieldCount]
  try omega

/-- The instantiated left body as one flattened application spine. -/
theorem ruleLhsBody_instL (c : NormalizedBlockCtor) {m1 : List VLevel}
    (hlen1 : m1.length = gen.recUvars) :
    (gen.ruleLhsBody c).instL m1 =
      VExpr.appN (.const (gen.ruleRecName c) m1)
        (VExpr.bvarRevRange (gen.ruleFieldCount c)
            (source.nparams + gen.familyCount + gen.minorCount) ++
          (gen.ruleIdx c).map (VExpr.instL m1) ++
          [(gen.ruleCtorApp c).instL m1]) := by
  show (VExpr.appN
      (VExpr.appN (.const (gen.ruleRecName c) gen.recLevels)
        (VExpr.bvarRevRange (gen.ruleFieldCount c)
          (source.nparams + gen.familyCount + gen.minorCount)))
      (gen.ruleIdx c ++ [gen.ruleCtorApp c])).instL m1 = _
  rw [← VExpr.appN_append, VExpr.instL_appN]
  show VExpr.appN (.const (gen.ruleRecName c)
      (gen.recLevels.map (VLevel.inst m1))) _ = _
  rw [show gen.recLevels.map (VLevel.inst m1) = m1 from
    VLevel.inst_map_id hlen1]
  rw [List.map_append, List.map_append, VExpr.bvarRevRange_map_instL,
    List.append_assoc]
  rfl

/-- The instantiated major premise of the rule body. -/
theorem ruleCtorApp_instL (c : NormalizedBlockCtor) (m1 : List VLevel) :
    (gen.ruleCtorApp c).instL m1 =
      VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1)))
        (VExpr.bvarRevRange
            (gen.ruleFieldCount c + (gen.familyCount + gen.minorCount))
            source.nparams ++
          VExpr.bvarRevRange 0 (gen.ruleFieldCount c)) := by
  show (VExpr.appN (.const c.ctor.raw.name gen.sourceLevels) _).instL m1 = _
  rw [VExpr.instL_appN, List.map_append, VExpr.bvarRevRange_map_instL,
    VExpr.bvarRevRange_map_instL]
  rfl

/-- The captured template values are exactly the shared prefix of the
recursor spine and the field suffix of the major premise. -/
private theorem captureArgs_apply {c : NormalizedBlockCtor} {m1 : List VLevel}
    {g1 : Pattern.Path
      (Pattern.varN (.const (gen.ruleRecName c)) (gen.ruleMajorArity c)) → VExpr}
    {g2 : Pattern.Path
      (Pattern.varN (.const c.ctor.raw.name) (gen.ruleArgArity c)) → VExpr}
    {fArgs aArgs : List VExpr}
    (hg1 : (Pattern.varNPaths (.const (gen.ruleRecName c))
      (gen.ruleMajorArity c)).map g1 = fArgs)
    (hg2 : (Pattern.varNPaths (.const c.ctor.raw.name)
      (gen.ruleArgArity c)).map g2 = aArgs) :
    (gen.captureArgs c).map
      (Pattern.RHS.apply (p := (gen.rulePattern c).toPattern) m1
        (Sum.elim g1 g2)) =
      fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        aArgs.drop source.nparams := by
  rw [captureArgs, List.map_append, List.map_map, List.map_map]
  show List.map g1 (List.take
      (source.nparams + gen.familyCount + gen.minorCount)
      (Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c))) ++
    List.map g2 (List.drop source.nparams
      (Pattern.varNPaths (.const c.ctor.raw.name)
        (gen.ruleArgArity c))) = _
  rw [List.map_take, List.map_drop, hg1, hg2]

/-- Pattern soundness for one certified block (`pat_wf`): a successful match
of a rule's pattern whose checks hold is definitionally equal to the
instantiated RHS template, derived from the rule defeq registered by
`addInduct` via typed β-collapse. The redex arrives decomposed into its
recursor and constructor spines with spine-form typing, and the major
premise's levels pinned to the rule's source levels; both are exactly what
a verified reduction site holds. -/
theorem pat_wf {env : VEnv} (henv : env.WF) {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hcl : gen.RuleClosure)
    {i : Nat} {c : NormalizedBlockCtor} (h : gen.ruleEntry i c)
    (hreg : env.defeqs (gen.rule i c))
    (hwf : (gen.rule i c).WF env)
    {m1 : List VLevel} {m2}
    (hm1 : ∀ l ∈ m1, l.WF univs) (hlen1 : m1.length = gen.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length = gen.ruleMajorArity c)
    (hNlen : aArgs.length = gen.ruleArgArity c)
    (hm : ((gen.rulePattern c).toPattern).Matches
      (.app (VExpr.appN (.const (gen.ruleRecName c) m1) fArgs)
        (VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1))) aArgs)) m1 m2)
    (hck : (gen.ruleCheck hcl (List.mem_of_getElem? h)).OK
      (env.IsDefEqU univs Γ) m1 m2)
    {Frec Ae : VExpr}
    (hehead : env.HasType univs Γ (.const (gen.ruleRecName c) m1) Frec)
    (hespine : env.SpineWF univs Γ Frec
      (fArgs ++ [VExpr.appN (.const c.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst m1))) aArgs]) Ae)
    {Fctor Actor : VExpr}
    (hctorhead : env.HasType univs Γ
      (.const c.ctor.raw.name (gen.sourceLevels.map (VLevel.inst m1))) Fctor)
    (hctorspine : env.SpineWF univs Γ Fctor aArgs Actor)
    {B : VExpr}
    (hcaps : env.SpineWF univs Γ ((gen.rule i c).type.instL m1)
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        aArgs.drop source.nparams) B) :
    env.IsDefEqU univs Γ
      (.app (VExpr.appN (.const (gen.ruleRecName c) m1) fArgs)
        (VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1))) aArgs))
      ((gen.ruleRHS hcl h).apply m1 m2) := by
  have henvo := henv.ordered
  have hc := List.mem_of_getElem? h
  cases hm with
  | @app _ _ _ g1 _ _ f2 g2 h1 h2 =>
  -- canonical captures
  have hg1 : (Pattern.varNPaths (.const (gen.ruleRecName c))
      (gen.ruleMajorArity c)).map g1 = fArgs :=
    Pattern.varN_matches_paths _ fArgs h1 hMlen
  have hg2 : (Pattern.varNPaths (.const c.ctor.raw.name)
      (gen.ruleArgArity c)).map g2 = aArgs :=
    Pattern.varN_matches_paths _ aArgs h2 hNlen
  have hcapsVals := gen.captureArgs_apply (m1 := m1) hg1 hg2
  -- length bookkeeping
  have hcommon_le : source.nparams + gen.familyCount + gen.minorCount ≤
      gen.ruleMajorArity c := Nat.le_add_right _ _
  have hnp_le : source.nparams ≤ gen.ruleArgArity c := Nat.le_add_right _ _
  have htakelen : (fArgs.take (source.nparams + gen.familyCount +
      gen.minorCount)).length =
      source.nparams + gen.familyCount + gen.minorCount := by
    rw [List.length_take, hMlen]; omega
  have hdroplen : (aArgs.drop source.nparams).length =
      gen.ruleFieldCount c := by
    rw [List.length_drop, hNlen]
    show gen.ruleArgArity c - source.nparams = _
    simp only [ruleArgArity]; omega
  have hcapslen : (fArgs.take (source.nparams + gen.familyCount +
      gen.minorCount) ++ aArgs.drop source.nparams).length =
      ((gen.ruleBinders c).map (VExpr.instL m1)).length := by
    rw [List.length_append, htakelen, hdroplen, List.length_map,
      gen.ruleBinders_length]
  -- tower shapes
  have htype' : (gen.rule i c).type.instL m1 =
      VExpr.forallN ((gen.ruleBinders c).map (VExpr.instL m1))
        ((VExpr.appN
          (.bvar (gen.familyCount - 1 - c.owner + gen.minorCount +
            gen.ruleFieldCount c))
          (gen.ruleIdx c ++ [gen.ruleCtorApp c])).instL m1) := by
    rw [gen.rule_type, VExpr.instL_forallN]
  have hlhs' : (gen.rule i c).lhs.instL m1 =
      VExpr.lamN ((gen.ruleBinders c).map (VExpr.instL m1))
        ((gen.ruleLhsBody c).instL m1) := by
    rw [gen.rule_lhs, VExpr.instL_lamN]
  -- tower typing at the working context
  have hlhsT : env.HasType univs Γ
      (VExpr.lamN ((gen.ruleBinders c).map (VExpr.instL m1))
        ((gen.ruleLhsBody c).instL m1))
      ((gen.rule i c).type.instL m1) := by
    rw [← hlhs']
    exact (hwf.1.instL hm1).weak0 henvo
  obtain ⟨hTel, T₀, hbody⟩ := VEnv.HasType.lamN_wf henvo hΓ hlhsT
  -- β-collapse of the applied left tower
  have hcapsF : env.SpineWF univs Γ
      (VExpr.forallN ((gen.ruleBinders c).map (VExpr.instL m1))
        ((VExpr.appN
          (.bvar (gen.familyCount - 1 - c.owner + gen.minorCount +
            gen.ruleFieldCount c))
          (gen.ruleIdx c ++ [gen.ruleCtorApp c])).instL m1))
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        aArgs.drop source.nparams) B := htype' ▸ hcaps
  have hretT0 := (VEnv.SpineWF.retarget hcapsF hcapslen) T₀
  have hcollapseL := VEnv.IsDefEq.appN_lamN henvo hTel hbody hretT0 hcapslen
  -- the registered defeq, applied
  have hex : env.IsDefEq univs Γ ((gen.rule i c).lhs.instL m1)
      ((gen.rule i c).rhs.instL m1) ((gen.rule i c).type.instL m1) :=
    .extra hreg hm1 hlen1
  rw [hlhs'] at hex
  have happlied := VEnv.IsDefEq.appN_congr hex hcaps
  -- conclusion-side template computation
  have hRHS : Pattern.RHS.apply (p := (gen.rulePattern c).toPattern) m1
      (Sum.elim g1 g2) (gen.ruleRHS hcl h) =
      VExpr.appN ((gen.rule i c).rhs.instL m1)
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams) := by
    rw [ruleRHS]
    simp only [Pattern.RHS.appN_apply, hcapsVals]
    rfl
  -- typing of the rule type's index spine
  obtain ⟨u₀, htypeT⟩ := hlhsT.isType henvo hΓ
  rw [htype'] at htypeT
  obtain ⟨-, V', htypeBody⟩ := VEnv.HasType.forallN_wf henvo htypeT
  have hCtxTel : OnCtx (((gen.ruleBinders c).map (VExpr.instL m1)).reverse ++ Γ)
      (env.IsType univs) := VEnv.OnTel.onCtx hΓ hTel
  rw [show ((VExpr.appN
      (.bvar (gen.familyCount - 1 - c.owner + gen.minorCount +
        gen.ruleFieldCount c))
      (gen.ruleIdx c ++ [gen.ruleCtorApp c])).instL m1) =
    VExpr.appN (.bvar (gen.familyCount - 1 - c.owner + gen.minorCount +
        gen.ruleFieldCount c))
      ((gen.ruleIdx c ++ [gen.ruleCtorApp c]).map (VExpr.instL m1)) from by
      rw [VExpr.instL_appN]; rfl] at htypeBody
  have hargsWF := VEnv.HasType.appN_args_wf henv hCtxTel _ _ rfl htypeBody
  -- check extraction
  unfold ruleCheck at hck
  obtain ⟨hparams, hidxOK⟩ := Pattern.Check.OK.of_foldr _ _ hck
  obtain ⟨hidxs, -⟩ := Pattern.Check.OK.of_foldr _ _ hidxOK
  -- per-index tower collapse and check composition
  have hidxLink : ∀ x ∈ (gen.ruleIdx c).attach.zip
      ((Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).drop
        (source.nparams + gen.familyCount + gen.minorCount)),
      env.IsDefEqU univs Γ (Sum.elim g1 g2 (Sum.inl x.2))
        (VExpr.instRev (x.1.1.instL m1)
          (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
            aArgs.drop source.nparams)) := by
    intro x hx
    have hfact := hidxs x hx
    simp only [Pattern.RHS.appN_apply, hcapsVals] at hfact
    have htower : Pattern.RHS.apply (p := (gen.rulePattern c).toPattern) m1
        (Sum.elim g1 g2)
        (.fixed (VExpr.lamN (gen.ruleBinders c) x.1.1)
          (hcl.idxTower_closed hc x.1.1 x.1.2)) =
        VExpr.lamN ((gen.ruleBinders c).map (VExpr.instL m1))
          (x.1.1.instL m1) := by
      show (VExpr.lamN (gen.ruleBinders c) x.1.1).instL m1 = _
      rw [VExpr.instL_lamN]
    rw [htower] at hfact
    obtain ⟨Tx, hTx⟩ := hargsWF (x.1.1.instL m1)
      (by
        rw [List.map_append]
        exact List.mem_append.2 (.inl (List.mem_map_of_mem x.1.2)))
    have hretTx := (VEnv.SpineWF.retarget hcapsF hcapslen) Tx
    have hcollapseX := VEnv.IsDefEq.appN_lamN henvo hTel hTx hretTx hcapslen
    exact VEnv.IsDefEqU.trans henv hΓ hfact ⟨_, hcollapseX⟩
  -- major premise: constructor spine against its rebuilt form
  have hparamsF₂ : List.Forall₂
      (fun a a' => a = a' ∨ env.IsDefEqU univs Γ a a')
      aArgs
      (fArgs.take source.nparams ++ aArgs.drop source.nparams) := by
    have hb := forall₂_zip_map (α := Pattern.Path
        (Pattern.varN (.const c.ctor.raw.name) (gen.ruleArgArity c)))
      (β := Pattern.Path
        (Pattern.varN (.const (gen.ruleRecName c)) (gen.ruleMajorArity c)))
      g2 g1 (fun a a' => a = a' ∨ env.IsDefEqU univs Γ a a')
      ((Pattern.varNPaths (.const c.ctor.raw.name)
        (gen.ruleArgArity c)).take source.nparams)
      ((Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).take source.nparams)
      (by
        rw [List.length_take, List.length_take,
          Pattern.varNPaths_length, Pattern.varNPaths_length]
        omega)
      (fun p hp => Or.inr (hparams p hp))
    rw [List.map_take, List.map_take, hg1, hg2] at hb
    have hall := forall₂_append hb
      (forall₂_refl_or (R := env.IsDefEqU univs Γ)
        (aArgs.drop source.nparams))
    rwa [List.take_append_drop] at hall
  have hmajorLink : env.IsDefEqU univs Γ
      (VExpr.appN (.const c.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst m1))) aArgs)
      (VExpr.appN (.const c.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst m1)))
        (fArgs.take source.nparams ++ aArgs.drop source.nparams)) :=
    ⟨_, VEnv.IsDefEq.appN_defEq hctorhead
      (VEnv.SpineWF.defEq_of_pointwise henv hΓ hctorspine hparamsF₂)⟩
  -- the collapsed left spine, computed
  have hL : (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
      aArgs.drop source.nparams).length =
      gen.ruleFieldCount c +
        (source.nparams + gen.familyCount + gen.minorCount) := by
    rw [List.length_append, htakelen, hdroplen]; omega
  have hcapsTake : (fArgs.take (source.nparams + gen.familyCount +
      gen.minorCount) ++ aArgs.drop source.nparams).take
      (source.nparams + gen.familyCount + gen.minorCount) =
      fArgs.take (source.nparams + gen.familyCount + gen.minorCount) := by
    rw [List.take_append_of_le_length (by omega : _ ≤ (fArgs.take
      (source.nparams + gen.familyCount + gen.minorCount)).length)]
    exact List.take_of_length_le (Nat.le_of_eq htakelen)
  have hcapsTakeNp : (fArgs.take (source.nparams + gen.familyCount +
      gen.minorCount) ++ aArgs.drop source.nparams).take source.nparams =
      fArgs.take source.nparams := by
    rw [List.take_append_of_le_length (by omega : _ ≤ (fArgs.take
      (source.nparams + gen.familyCount + gen.minorCount)).length)]
    rw [List.take_take]
    congr 1
    omega
  have hcapsDrop : (fArgs.take (source.nparams + gen.familyCount +
      gen.minorCount) ++ aArgs.drop source.nparams).drop
      (source.nparams + gen.familyCount + gen.minorCount) =
      aArgs.drop source.nparams := by
    have hdl := List.drop_left (l₁ := fArgs.take (source.nparams + gen.familyCount + gen.minorCount)) (l₂ := aArgs.drop source.nparams)
    rwa [htakelen] at hdl
  have hsegNp : (VExpr.bvarRevRange
      (gen.ruleFieldCount c + (gen.familyCount + gen.minorCount))
      source.nparams).map (VExpr.instRev ·
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams)) = fArgs.take source.nparams := by
    rw [VExpr.map_instRev_bvarRevRange_seg _ source.nparams _ (by omega)]
    rw [show (fArgs.take (source.nparams + gen.familyCount +
        gen.minorCount) ++ aArgs.drop source.nparams).length -
        (gen.ruleFieldCount c + (gen.familyCount + gen.minorCount)) -
        source.nparams = 0 from by omega, List.drop_zero]
    exact hcapsTakeNp
  have hsegFld : (VExpr.bvarRevRange 0 (gen.ruleFieldCount c)).map
      (VExpr.instRev ·
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams)) = aArgs.drop source.nparams := by
    rw [VExpr.map_instRev_bvarRevRange_seg _ (gen.ruleFieldCount c) 0
      (by omega)]
    rw [show (fArgs.take (source.nparams + gen.familyCount +
        gen.minorCount) ++ aArgs.drop source.nparams).length - 0 -
        gen.ruleFieldCount c =
        source.nparams + gen.familyCount + gen.minorCount from by omega]
    rw [hcapsDrop]
    exact List.take_of_length_le (Nat.le_of_eq hdroplen)
  have hsegCommon : (VExpr.bvarRevRange (gen.ruleFieldCount c)
      (source.nparams + gen.familyCount + gen.minorCount)).map
      (VExpr.instRev ·
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams)) =
      fArgs.take (source.nparams + gen.familyCount + gen.minorCount) := by
    rw [VExpr.map_instRev_bvarRevRange_seg _
      (source.nparams + gen.familyCount + gen.minorCount)
      (gen.ruleFieldCount c) (by omega)]
    rw [show (fArgs.take (source.nparams + gen.familyCount +
        gen.minorCount) ++ aArgs.drop source.nparams).length -
        gen.ruleFieldCount c -
        (source.nparams + gen.familyCount + gen.minorCount) = 0 from by
        omega, List.drop_zero]
    exact hcapsTake
  have hctorImg : VExpr.instRev ((gen.ruleCtorApp c).instL m1)
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        aArgs.drop source.nparams) =
      VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1)))
        (fArgs.take source.nparams ++ aArgs.drop source.nparams) := by
    rw [gen.ruleCtorApp_instL, VExpr.instRev_appN,
      VExpr.instRev_closedN (C := .const c.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst m1))) _ trivial, List.map_append,
      hsegNp, hsegFld]
  have hcollapsedEq : VExpr.instRev ((gen.ruleLhsBody c).instL m1)
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        aArgs.drop source.nparams) =
      VExpr.appN (.const (gen.ruleRecName c) m1)
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          ((gen.ruleIdx c).map (fun x => VExpr.instRev (x.instL m1)
            (fArgs.take (source.nparams + gen.familyCount +
              gen.minorCount) ++ aArgs.drop source.nparams)) ++
          [VExpr.appN (.const c.ctor.raw.name
              (gen.sourceLevels.map (VLevel.inst m1)))
            (fArgs.take source.nparams ++ aArgs.drop source.nparams)])) := by
    rw [gen.ruleLhsBody_instL c hlen1, VExpr.instRev_appN,
      VExpr.instRev_closedN (C := .const (gen.ruleRecName c) m1) _ trivial,
      List.map_append, List.map_append, hsegCommon, List.map_map]
    rw [show ((gen.ruleCtorApp c).instL m1 ::
        ([] : List VExpr)).map (VExpr.instRev ·
          (fArgs.take (source.nparams + gen.familyCount +
            gen.minorCount) ++ aArgs.drop source.nparams)) =
        [VExpr.instRev ((gen.ruleCtorApp c).instL m1)
          (fArgs.take (source.nparams + gen.familyCount +
            gen.minorCount) ++ aArgs.drop source.nparams)] from rfl]
    rw [hctorImg]
    simp only [Function.comp_def]
    rw [List.append_assoc]
  -- pointwise defeq between the redex spine and the collapsed spine
  have hidxF₂ : List.Forall₂ (fun a a' => a = a' ∨ env.IsDefEqU univs Γ a a')
      (fArgs.drop (source.nparams + gen.familyCount + gen.minorCount))
      ((gen.ruleIdx c).map (fun x => VExpr.instRev (x.instL m1)
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams))) := by
    have hb := forall₂_zip_map
      (α := {x // x ∈ gen.ruleIdx c})
      (β := Pattern.Path (Pattern.varN (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)))
      (fun s => VExpr.instRev (s.1.instL m1)
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams))
      (fun p => Sum.elim g1 g2 (Sum.inl p))
      (fun t v => v = t ∨ env.IsDefEqU univs Γ v t)
      (gen.ruleIdx c).attach
      ((Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).drop
        (source.nparams + gen.familyCount + gen.minorCount))
      (by
        rw [List.length_attach, List.length_drop, Pattern.varNPaths_length]
        show (gen.ruleIdx c).length = gen.ruleMajorArity c - _
        simp only [ruleIdx, ruleMajorArity, List.length_map]
        omega)
      (fun p hp => Or.inr (hidxLink p hp))
    have hflip := List.Forall₂.flip hb
    have hmapG : ((Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).drop
        (source.nparams + gen.familyCount + gen.minorCount)).map
        (fun p => Sum.elim g1 g2 (Sum.inl p)) =
        fArgs.drop (source.nparams + gen.familyCount + gen.minorCount) := by
      show ((Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).drop
        (source.nparams + gen.familyCount + gen.minorCount)).map g1 = _
      rw [List.map_drop, hg1]
    have hmapF : ((gen.ruleIdx c).attach).map
        (fun s => VExpr.instRev (s.1.instL m1)
          (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
            aArgs.drop source.nparams)) =
        (gen.ruleIdx c).map (fun x => VExpr.instRev (x.instL m1)
          (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
            aArgs.drop source.nparams)) := by
      exact List.attach_map_val
        (f := fun x : VExpr => VExpr.instRev (x.instL m1)
          (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
            aArgs.drop source.nparams)) ..
    rw [hmapG, hmapF] at hflip
    exact hflip
  have hbigF₂ : List.Forall₂ (fun a a' => a = a' ∨ env.IsDefEqU univs Γ a a')
      (fArgs ++ [VExpr.appN (.const c.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst m1))) aArgs])
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        ((gen.ruleIdx c).map (fun x => VExpr.instRev (x.instL m1)
          (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
            aArgs.drop source.nparams)) ++
        [VExpr.appN (.const c.ctor.raw.name
            (gen.sourceLevels.map (VLevel.inst m1)))
          (fArgs.take source.nparams ++ aArgs.drop source.nparams)])) := by
    have hres := forall₂_append
      (forall₂_refl_or (R := env.IsDefEqU univs Γ)
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount)))
      (forall₂_append hidxF₂ (.cons (Or.inr hmajorLink) .nil))
    rwa [← List.append_assoc, List.take_append_drop] at hres
  -- the redex is defeq to the collapsed left spine
  have hE := VEnv.IsDefEq.appN_defEq hehead
    (VEnv.SpineWF.defEq_of_pointwise henv hΓ hespine hbigF₂)
  rw [← hcollapsedEq, VExpr.appN_append] at hE
  -- assemble
  rw [hRHS]
  exact VEnv.IsDefEqU.trans henv hΓ ⟨_, hE⟩
    (VEnv.IsDefEqU.trans henv hΓ ⟨_, hcollapseL.symm⟩ ⟨_, happlied⟩)

end BlockGenerationChecked

end VInductDecl

end Ix.Theory.Named

/-! ## Axiom closures

The typed β-collapse layer is sorry-free. `pat_wf` composes typed defeqs
through `IsDefEqU.of_l`/`IsDefEqU.trans` and therefore carries exactly the
transitional unique-typing closure the Church–Rosser development itself
carries. The `sorryAx` dependency remains until the underlying inversion
and unique-typing proofs are complete. -/

#guard_named_axioms Ix.Theory.Named.VEnv.IsDefEq.appN_lamN [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VEnv.IsDefEq.appN_defEq [propext]

#guard_named_axioms Ix.Theory.Named.VEnv.LE.extra [propext]

#guard_named_axioms Ix.Theory.Named.VEnv.LE.extra_appN [propext]

#guard_named_axioms Ix.Theory.Named.VEnv.LE.extra_appN_symm [propext]

#guard_named_axioms Ix.Theory.Named.Pattern.varN_matches_paths [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VInductDecl.BlockGenerationChecked.pat_wf [
  propext,
  sorryAx,
  Classical.choice,
  Quot.sound]
