module

public import IxC.Kernel.Verify.Frontend.InModelRename

@[expose] public section

/-!
# The in-model generator under a renaming injective on a scope (parametricity, step 3)

`Frontend.InModel.generate` compares keys (`find? (·.1 == n)`, `contains`, `==` on
terms) and reads its context at the keys it meets. Under a renaming `f` injective
on a scope `P` (`InjOn`), every comparison between good keys or terms gives the
same answer on the renamed side (`Key.map_beq`, `Expr.mapKeys_beq`), so the
generator takes the same branches and its records are the renamed ones, as long as
the context agrees at the good keys and holds good values there.

This module has the vocabulary: `ExRel` (two runs agree up to their error
messages, whose text names keys), its combinators for the generator's `do`
blocks, the constant table's agreement on a scope (`TblOn`), and the syntactic
inferer and the sort ceiling under it, with the goodness of what they return.
-/

namespace Ix.Kernel.Frontend.InModel

open Ix.Kernel

variable {md md' : Mode}

/-! ## Runs that agree up to their error messages -/

/-- **Two runs agree up to their error messages**: both fail, or both succeed
with related results. -/
def ExRel {ε ε' α β : Type} (R : α → β → Prop) : Except ε α → Except ε' β → Prop
  | .error _, .error _ => True
  | .ok a, .ok b => R a b
  | _, _ => False

/-- **Elementwise related lists.** -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → ListRel R as bs →
      ListRel R (a :: as) (b :: bs)

/-- Related loop steps: both continue or both stop, at related states. -/
def StepRel {α β : Type} (R : α → β → Prop) : ForInStep α → ForInStep β → Prop
  | .yield a, .yield b => R a b
  | .done a, .done b => R a b
  | _, _ => False

namespace ExRel

variable {ε ε' α β γ δ : Type} {R : α → β → Prop}

theorem ok' {a : α} {b : β} (h : R a b) : ExRel R (.ok a : Except ε α) (.ok b : Except ε' β) := h

theorem pure' {a : α} {b : β} (h : R a b) : ExRel R (pure a : Except ε α) (pure b : Except ε' β) := h

theorem error' {e : ε} {e' : ε'} : ExRel R (.error e : Except ε α) (.error e' : Except ε' β) :=
  trivial

theorem throw' {e : ε} {e' : ε'} :
    ExRel R (throw (m := Except ε) e : Except ε α) (throw (m := Except ε') e' : Except ε' β) :=
  trivial

theorem mono {R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b) :
    ∀ {x : Except ε α} {x' : Except ε' β}, ExRel R x x' → ExRel R' x x'
  | .error _, .error _, _ => trivial
  | .ok _, .ok _, h => hR _ _ h
  | .ok _, .error _, h => h.elim
  | .error _, .ok _, h => h.elim

theorem bind {S : γ → δ → Prop} {x : Except ε γ} {x' : Except ε' δ} {g : γ → Except ε α}
    {g' : δ → Except ε' β} (hx : ExRel S x x') (hg : ∀ a b, S a b → ExRel R (g a) (g' b)) :
    ExRel R (x >>= g) (x' >>= g') := by
  cases x <;> cases x' <;> first | exact hx.elim | exact trivial | exact hg _ _ hx

theorem map {S : γ → δ → Prop} {x : Except ε γ} {x' : Except ε' δ} {g : γ → α} {g' : δ → β}
    (hx : ExRel S x x') (hg : ∀ a b, S a b → R (g a) (g' b)) :
    ExRel R (g <$> x) (g' <$> x') := by
  cases x <;> cases x' <;> first | exact hx.elim | exact trivial | exact hg _ _ hx

/-- A run related to its renaming by a function is that function's image,
up to the error message. -/
theorem toOption_eq {g : α → β} {x : Except ε α} {x' : Except ε' β}
    (h : ExRel (fun a b => b = g a) x x') : x'.toOption = x.toOption.map g := by
  cases x <;> cases x' <;> first | exact h.elim | rfl | (subst h; rfl)

/-- The same branch on both sides. -/
theorem ite {c c' : Prop} [Decidable c] [Decidable c'] (hc : c ↔ c') {x y : Except ε α}
    {x' y' : Except ε' β} (hx : c → ExRel R x x') (hy : ¬ c → ExRel R y y') :
    ExRel R (if c then x else y) (if c' then x' else y') := by
  by_cases h : c
  · rw [if_pos h, if_pos (hc.mp h)]; exact hx h
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]; exact hy h

/-- A guard with the same verdict on both sides (`unless c do throw …`). -/
theorem guard {c c' : Bool} (hc : c = c') {e : ε} {e' : ε'} :
    ExRel (fun (_ : Unit) (_ : Unit) => True)
      (if c then pure () else throw e : Except ε Unit)
      (if c' then pure () else throw e' : Except ε' Unit) := by
  subst hc; cases c <;> trivial

/-- **A loop over related lists** from related states, each step related. -/
theorem forIn_list {Q : γ → δ → Prop} :
    ∀ {l : List γ} {l' : List δ}, ListRel Q l l' →
    ∀ {i : α} {i' : β} {f : γ → α → Except ε (ForInStep α)} {f' : δ → β → Except ε' (ForInStep β)},
      R i i' → (∀ x x' r r', Q x x' → R r r' → ExRel (StepRel R) (f x r) (f' x' r')) →
      ExRel R (forIn l i f) (forIn l' i' f')
  | [], [], .nil, _, _, _, _, hi, _ => hi
  | x :: xs, x' :: xs', .cons hq hl, i, i', f, f', hi, hf => by
    rw [List.forIn_cons, List.forIn_cons]
    refine bind (hf x x' i i' hq hi) fun a b hab => ?_
    cases a <;> cases b
    · exact hab
    · exact hab.elim
    · exact hab.elim
    · exact forIn_list hl hab hf

/-- A loop over one list on both sides. -/
theorem forIn_same {l : List γ} {i : α} {i' : β} {f : γ → α → Except ε (ForInStep α)}
    {f' : γ → β → Except ε' (ForInStep β)} (hi : R i i')
    (hf : ∀ x r r', x ∈ l → R r r' → ExRel (StepRel R) (f x r) (f' x r')) :
    ExRel R (forIn l i f) (forIn l i' f') := by
  have hl : ListRel (fun x y => x = y ∧ x ∈ l) l l := by
    have : ∀ l₀ : List γ, (∀ x ∈ l₀, x ∈ l) → ListRel (fun x y => x = y ∧ x ∈ l) l₀ l₀ := by
      intro l₀ h
      induction l₀ with
      | nil => exact .nil
      | cons a as ih =>
        exact .cons ⟨rfl, h a List.mem_cons_self⟩ (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact this l fun _ h => h
  exact forIn_list hl hi fun x x' r r' hq hr => by obtain ⟨rfl, hx⟩ := hq; exact hf x r r' hx hr

/-- **`mapM` over related lists**: related results, elementwise. -/
theorem mapM {Q : γ → δ → Prop} {f : γ → Except ε α} {f' : δ → Except ε' β} :
    ∀ {l : List γ} {l' : List δ}, ListRel Q l l' →
      (∀ x x', Q x x' → ExRel R (f x) (f' x')) →
      ExRel (ListRel R) (l.mapM f) (l'.mapM f')
  | [], [], .nil, _ => ListRel.nil
  | x :: xs, x' :: xs', .cons hq hl, hf => by
    rw [List.mapM_cons, List.mapM_cons]
    refine bind (hf x x' hq) fun a b hab => ?_
    refine bind (mapM hl hf) fun as bs habs => ?_
    exact ListRel.cons hab habs

/-- `mapM` over one list on both sides. -/
theorem mapM_same {f : γ → Except ε α} {f' : γ → Except ε' β} {l : List γ}
    (hf : ∀ x, x ∈ l → ExRel R (f x) (f' x)) :
    ExRel (ListRel R) (l.mapM f) (l.mapM f') := by
  have hl : ListRel (fun x y => x = y ∧ x ∈ l) l l := by
    have : ∀ l₀ : List γ, (∀ x ∈ l₀, x ∈ l) → ListRel (fun x y => x = y ∧ x ∈ l) l₀ l₀ := by
      intro l₀ h
      induction l₀ with
      | nil => exact .nil
      | cons a as ih =>
        exact .cons ⟨rfl, h a List.mem_cons_self⟩ (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact this l fun _ h => h
  exact mapM hl fun x x' hq => by obtain ⟨rfl, hx⟩ := hq; exact hf x hx

end ExRel

/-- Elementwise related lists, one the other's image, are the image. -/
theorem forall₂_map_eq {α β : Type} {g : α → β} {G : α → Prop} :
    ∀ {l : List α} {l' : List β}, ListRel (fun a b => b = g a ∧ G a) l l' →
      l' = l.map g ∧ ∀ a ∈ l, G a
  | [], [], .nil => ⟨rfl, fun _ h => nomatch h⟩
  | a :: as, b :: bs, .cons ⟨hb, ha⟩ h => by
    obtain ⟨h1, h2⟩ := forall₂_map_eq h
    refine ⟨by rw [hb, h1]; rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact h2 x hx

/-! ## The constant table on a scope -/

section Table

variable (P : KeyScope md) (f : md.Id → md'.Id)

/-- **The constant table agrees on the scope**: at a renamed good key, the
renamed declared type; the declared type at a good key is good. -/
structure TblOn (tbl : ConstTable md) (tbl' : ConstTable md') : Prop where
  agree : ∀ k : Key md, k.Good P → tbl' (k.map f) = (tbl k).map fun p => (p.1, p.2.mapKeys f)
  good : ∀ k : Key md, k.Good P → ∀ p, tbl k = some p → p.2.Good P

end Table

variable {P : KeyScope md} {f : md.Id → md'.Id}

theorem betaHeadF_good (fuel : Nat) :
    ∀ {e r : Expr md}, e.Good P → betaHeadF fuel e = some r → r.Good P := by
  induction fuel with
  | zero => intro e r _ h; exact nomatch h
  | succ fuel ih =>
    intro e r he h
    cases e with
    | app g a =>
      simp only [betaHeadF] at h
      obtain ⟨hg, ha⟩ := he
      cases hgb : betaHeadF fuel g with
      | none => rw [hgb] at h; exact nomatch h
      | some g' =>
        rw [hgb] at h
        have hg' := ih hg hgb
        cases g' with
        | lam d b m => exact ih (Expr.Good.instantiate1 hg'.2 ha 0) h
        | _ => cases h; exact ⟨hg', ha⟩
    | _ => cases h; exact he

theorem betaHeadE_good {e r : Expr md} (he : e.Good P) (h : betaHeadE e = .ok r) : r.Good P := by
  unfold betaHeadE at h
  cases hb : betaHeadF inferFuel e with
  | none => rw [hb] at h; exact nomatch h
  | some r' => rw [hb] at h; cases h; exact betaHeadF_good _ he hb

/-- What an inferer returns is good. -/
def ResGood (P : KeyScope md) (r : Except String (Option (Expr md))) : Prop :=
  ∀ t, r = .ok (some t) → t.Good P

theorem inferTyF_sortOfF_mapKeysOn (hP : P.Pre) {tbl : ConstTable md} {tbl' : ConstTable md'}
    (htbl : TblOn P f tbl tbl') (fuel : Nat) :
    (∀ (ctx : List (Expr md)) (e : Expr md), Expr.GoodList P ctx → e.Good P →
      inferTyF tbl' fuel (ctx.map (Expr.mapKeys f)) (e.mapKeys f) =
        (inferTyF tbl fuel ctx e).map (Option.map (Expr.mapKeys f)) ∧
      ResGood P (inferTyF tbl fuel ctx e)) ∧
    (∀ (ctx : List (Expr md)) (e : Expr md), Expr.GoodList P ctx → e.Good P →
      sortOfF tbl' fuel (ctx.map (Expr.mapKeys f)) (e.mapKeys f) = sortOfF tbl fuel ctx e) := by
  induction fuel with
  | zero => exact ⟨fun _ _ _ _ => ⟨rfl, fun _ h => nomatch h⟩, fun _ _ _ _ => rfl⟩
  | succ fuel ih =>
    obtain ⟨ihI, ihS⟩ := ih
    refine ⟨fun ctx e hctx he => ?_, fun ctx e hctx he => ?_⟩
    · cases e with
      | bvar i =>
        refine ⟨?_, ?_⟩
        · simp only [Expr.mapKeys, inferTyF, List.getElem?_map]
          cases ctx[i]? <;> simp [Except.map, Expr.mapKeys_liftLooseBVars]
        · intro t ht
          simp only [inferTyF, Except.ok.injEq] at ht
          cases hi : ctx[i]? with
          | none => rw [hi] at ht; exact nomatch ht
          | some c =>
            rw [hi] at ht
            cases ht
            exact Expr.Good.liftLooseBVars (hctx c (List.mem_of_getElem? hi)) _ _
      | sort u =>
        exact ⟨rfl, fun t ht => by cases ht; trivial⟩
      | const n us =>
        refine ⟨?_, ?_⟩
        · simp only [Expr.mapKeys, inferTyF, htbl.agree n he]
          cases tbl n with
          | none => rfl
          | some p =>
            obtain ⟨lps, ty⟩ := p
            simp only [Option.map_some, Option.bind_some]
            split <;> simp [Except.map, Expr.mapKeys_instantiateLevelParams]
        · intro t ht
          simp only [inferTyF, Except.ok.injEq] at ht
          cases hn : tbl n with
          | none => rw [hn] at ht; exact nomatch ht
          | some p =>
            obtain ⟨lps, ty⟩ := p
            rw [hn] at ht
            simp only [Option.bind_some] at ht
            split at ht
            · cases ht
              exact Expr.Good.instantiateLevelParams (htbl.good n he _ hn) _ _
            · exact nomatch ht
      | app g a =>
        obtain ⟨hg, ha⟩ := he
        obtain ⟨ihg, hgg⟩ := ihI ctx g hctx hg
        refine ⟨?_, ?_⟩
        · simp only [Expr.mapKeys, inferTyF, ihg]
          cases hgr : inferTyF tbl fuel ctx g with
          | error err => rfl
          | ok r =>
            cases r with
            | none => rfl
            | some ft =>
              simp only [Except.map, Option.map_some, bind, Except.bind, betaHeadF_mapKeys]
              cases betaHeadF fuel ft with
              | none => rfl
              | some t =>
                cases t <;> simp [Expr.mapKeys, pure, Except.pure, Expr.mapKeys_instantiate1]
        · intro t ht
          simp only [inferTyF, bind, Except.bind] at ht
          cases hgr : inferTyF tbl fuel ctx g with
          | error err => rw [hgr] at ht; exact nomatch ht
          | ok r =>
            rw [hgr] at ht
            cases r with
            | none => exact nomatch ht
            | some ft =>
              have hft := hgg ft hgr
              simp only at ht
              cases hb : betaHeadF fuel ft with
              | none => rw [hb] at ht; exact nomatch ht
              | some t' =>
                rw [hb] at ht
                have ht' := betaHeadF_good fuel hft hb
                cases t' with
                | forallE d b m =>
                  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at ht
                  subst ht
                  exact Expr.Good.instantiate1 ht'.2 ha 0
                | _ => exact nomatch ht
      | lam d b m =>
        obtain ⟨hd, hb⟩ := he
        obtain ⟨ihb, hbg⟩ := ihI (d :: ctx) b (by simp [Expr.GoodList] at hctx ⊢; exact ⟨hd, hctx⟩) hb
        simp only [List.map_cons] at ihb
        refine ⟨?_, ?_⟩
        · simp only [Expr.mapKeys, inferTyF, ihb]
          cases inferTyF tbl fuel (d :: ctx) b with
          | error err => rfl
          | ok r => cases r <;> rfl
        · intro t ht
          simp only [inferTyF, bind, Except.bind] at ht
          cases hbr : inferTyF tbl fuel (d :: ctx) b with
          | error err => rw [hbr] at ht; exact nomatch ht
          | ok r =>
            rw [hbr] at ht
            cases r with
            | none => exact nomatch ht
            | some bt =>
              simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at ht
              subst ht
              exact ⟨hd, hbg bt hbr⟩
      | forallE d b m =>
        obtain ⟨hd, hb⟩ := he
        have hb' := ihS (d :: ctx) b (by simp [Expr.GoodList] at hctx ⊢; exact ⟨hd, hctx⟩) hb
        simp only [List.map_cons] at hb'
        refine ⟨?_, ?_⟩
        · simp only [Expr.mapKeys, inferTyF, ihS ctx d hctx hd, hb']
          cases sortOfF tbl fuel ctx d with
          | error err => rfl
          | ok r =>
            cases r with
            | none => rfl
            | some u =>
              simp only [bind, Except.bind]
              cases sortOfF tbl fuel (d :: ctx) b with
              | error err => rfl
              | ok r => cases r <;> rfl
        · intro t ht
          simp only [inferTyF, bind, Except.bind] at ht
          cases hs : sortOfF tbl fuel ctx d with
          | error err => rw [hs] at ht; exact nomatch ht
          | ok r =>
            rw [hs] at ht
            cases r with
            | none => exact nomatch ht
            | some u =>
              simp only at ht
              cases hs2 : sortOfF tbl fuel (d :: ctx) b with
              | error err => rw [hs2] at ht; exact nomatch ht
              | ok r =>
                rw [hs2] at ht
                cases r with
                | none => exact nomatch ht
                | some v =>
                  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at ht
                  subst ht
                  trivial
      | letE t v b l =>
        obtain ⟨ht, hv, hb⟩ := he
        obtain ⟨ih1, ih2⟩ := ihI ctx (b.instantiate1 v) hctx (Expr.Good.instantiate1 hb hv 0)
        refine ⟨?_, ?_⟩
        · simp only [Expr.mapKeys, inferTyF, ← Expr.mapKeys_instantiate1, ih1]
        · intro t' ht'
          simp only [inferTyF] at ht'
          exact ih2 t' ht'
      | lit l =>
        cases l with
        | natVal n =>
          exact ⟨rfl, fun t ht => by
            simp only [inferTyF, Except.ok.injEq, Option.some.injEq] at ht
            subst ht; exact hP _ (by decide)⟩
        | strVal s =>
          exact ⟨rfl, fun t ht => by
            simp only [inferTyF, Except.ok.injEq, Option.some.injEq] at ht
            subst ht; exact he _ (by decide)⟩
      | fvar i t => exact ⟨rfl, fun _ ht => nomatch ht⟩
      | proj s i x => exact ⟨rfl, fun _ ht => nomatch ht⟩
    · obtain ⟨ihe, -⟩ := ihI ctx e hctx he
      simp only [sortOfF, ihe]
      cases inferTyF tbl fuel ctx e with
      | error err => rfl
      | ok r =>
        cases r with
        | none => rfl
        | some t =>
          simp only [Except.map, Option.map_some, bind, Except.bind, betaHeadF_mapKeys]
          cases betaHeadF fuel t with
          | none => rfl
          | some t' => cases t' <;> rfl

theorem inferTy_mapKeysOn (hP : P.Pre) {tbl : ConstTable md} {tbl' : ConstTable md'}
    (htbl : TblOn P f tbl tbl') {ctx : List (Expr md)} {e : Expr md} (hctx : Expr.GoodList P ctx)
    (he : e.Good P) :
    inferTy tbl' (ctx.map (Expr.mapKeys f)) (e.mapKeys f) =
      (inferTy tbl ctx e).map (Option.map (Expr.mapKeys f)) :=
  ((inferTyF_sortOfF_mapKeysOn hP htbl inferFuel).1 ctx e hctx he).1

theorem inferTy_good (hP : P.Pre) {tbl : ConstTable md} {tbl' : ConstTable md'}
    (htbl : TblOn P f tbl tbl') {ctx : List (Expr md)} {e : Expr md} (hctx : Expr.GoodList P ctx)
    (he : e.Good P) : ResGood P (inferTy tbl ctx e) :=
  ((inferTyF_sortOfF_mapKeysOn hP htbl inferFuel).1 ctx e hctx he).2

theorem sortOf_mapKeysOn (hP : P.Pre) {tbl : ConstTable md} {tbl' : ConstTable md'}
    (htbl : TblOn P f tbl tbl') {ctx : List (Expr md)} {e : Expr md} (hctx : Expr.GoodList P ctx)
    (he : e.Good P) :
    sortOf tbl' (ctx.map (Expr.mapKeys f)) (e.mapKeys f) = sortOf tbl ctx e :=
  (inferTyF_sortOfF_mapKeysOn hP htbl inferFuel).2 ctx e hctx he

theorem sortCeil_mapKeysOn (hP : P.Pre) {tbl : ConstTable md} {tbl' : ConstTable md'}
    (htbl : TblOn P f tbl tbl') (fuel : Nat) : ∀ (ctx : List (Expr md)) (d : Expr md),
      Expr.GoodList P ctx → d.Good P →
      sortCeil tbl' fuel (ctx.map (Expr.mapKeys f)) (d.mapKeys f) = sortCeil tbl fuel ctx d := by
  induction fuel with
  | zero => intro ctx d _ _; rfl
  | succ fuel ih =>
    intro ctx d hctx hd
    have byHead : ∀ d' : Expr md, d'.Good P →
        ceilByHead tbl' fuel (ctx.map (Expr.mapKeys f)) (d'.mapKeys f) =
        ceilByHead tbl fuel ctx d' := fun d' hd' => by
      have hfn := Expr.Good.getAppFn hd'
      simp only [ceilByHead, ← Expr.mapKeys_getAppFn, inferTy_mapKeysOn hP htbl hctx hfn]
      have hg := inferTy_good hP htbl hctx hfn
      cases hr : inferTy tbl ctx d'.getAppFn with
      | error err => rfl
      | ok r =>
        cases r with
        | none => rfl
        | some g =>
          simp only [Except.map, Option.map_some, bind, Except.bind]
          exact ih ctx g hctx (hg g hr)
    simp only [sortCeil, inferTy_mapKeysOn hP htbl hctx hd]
    have hg := inferTy_good hP htbl hctx hd
    cases hr : inferTy tbl ctx d with
    | error err => rfl
    | ok r =>
      cases r with
      | some t =>
        have ht := hg t hr
        simp only [Except.map, Option.map_some, bind, Except.bind, betaHeadE_mapKeys]
        cases hb : betaHeadE t with
        | error err => rfl
        | ok t' =>
          have h := ih ctx t' hctx (betaHeadE_good ht hb)
          cases t' <;> first | rfl | exact h
      | none =>
        simp only [Except.map, Option.map_none, bind, Except.bind, betaHeadE_mapKeys]
        cases hb : betaHeadE d with
        | error err => rfl
        | ok d' =>
          have hd' := betaHeadE_good hd hb
          have hh := byHead d' hd'
          cases d' with
          | forallE dom body m =>
            have hb2 := ih (dom :: ctx) body
              (by simp [Expr.GoodList] at hctx ⊢; exact ⟨hd'.1, hctx⟩) hd'.2
            simp only [List.map_cons] at hb2
            simp only [Expr.mapKeys, ih ctx dom hctx hd'.1, hb2]
          | letE t v b l =>
            simp only [Expr.mapKeys, ← Expr.mapKeys_instantiate1,
              ih ctx _ hctx (Expr.Good.instantiate1 hd'.2.2 hd'.2.1 0)]
          | _ => exact hh

theorem idxSort_mapKeysOn (hP : P.Pre) {tbl : ConstTable md} {tbl' : ConstTable md'}
    (htbl : TblOn P f tbl tbl') {ctx : List (Expr md)} {e : Expr md} (hctx : Expr.GoodList P ctx)
    (he : e.Good P) :
    idxSort tbl' (ctx.map (Expr.mapKeys f)) (e.mapKeys f) = idxSort tbl ctx e :=
  sortCeil_mapKeysOn hP htbl 128 ctx e hctx he

end Ix.Kernel.Frontend.InModel
