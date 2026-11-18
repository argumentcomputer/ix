import IxVMRefinement.Binding.FamilyReconStore
import IxC.Kernel.Semantics.Inductives.WrapRel

/-! # Full consumption: the other declared type a family check accepts

A family check compares each recursor's declared type `ty` with the block's reconstruction `R` at
its position (`KernelCheck::canonical_rules_at_pos`): `ty` is `R` (`kexpr_struct_eq`), or `ty` is
`R` with the wrappers at its binder domains fully consumed (`wrap_rel(1, R, ty)`), and the record
takes one of the two at all its members (the form state). A group's validation refuses the second
(`rc_validates_group`), so the family records the binding checks are in `RFormS`; a record the
typing claim checks may be in either. The rules are compared under the λs of the declared type
in both cases (`compare_rules`, `rule_lam_doms`), as `MemberRecon` states them.

This module models `wrap_rel` at `sm = 1`, mirroring the circuit (`KernelCheck.lean`, functions
`wrap_rel`, `wrap_binder`, `wrap_dom`, `consume_wrapper`, `lam_first_arity`):

* `wrapAt t E` (`get_ci`'s definition arm at a constant's address, `convert_definition`): the
  arity of the stored definition's value as a wrapper `λ x₁ … xₖ, x₁` whose λs all carry the datum
  `never` (`lam_first_arity`; IxC's `lamFirstArity`). `none` where the load fails.
* `appHead`, `consumeOf`, **`consumeAt`** (`consume_wrapper`, `collect_spine`): a wrapper applied
  to exactly its arity leaves its first argument; `some none` where no wrapper is consumed.
* `Consumes` (the loop of `wrap_dom` at `sm = 1`): the wrappers at a domain's head consumed one at
  a time, as long as one is.
* **`FullCons W g d`** (`wrap_rel(1, g, d) = 1`): the generated term `g` and the declared term `d`
  have one shape, node for node (a `let` only against a `let`, nothing expanded); the leaves are
  related as `kexpr_struct_eq` relates them (levels up to semantic equality); binder data by their
  zero-ness (`pw_eq`); and at every binder domain the generated domain's wrappers are consumed
  until none is left, the rest then related to the declared domain. Consumption is forced: unlike
  IxC's `WrapRel`, a domain does not keep a wrapper it can lose.
* `FullCons.mono`, `wrapAt_mono`: a store holding the first's records and blobs answers the same.
* `FullCons.congr_left`, `FullCons.congr_right`: up to the semantic equality of levels on either
  side (`ExprLvEq`).
* `exprLvEq_wrapRel`, `FullCons.toWrapRel`, **`wrapRel_of_recon`**: IxC's `WrapRel` wherever IxC's
  environment has the store's wrappers: a type equal to the reconstruction up to levels is above
  a type that is the reconstruction or its full consumption.
* **`RecordRecon t E B rb`**: the form-agnostic record-level form, `RecordReconWith` at "the
  reconstruction or its full consumption"; `RecordReconWith.mono`, `RFormS.toRecordRecon`,
  `RecordRecon.grow`.

Fidelity points (for the observations of `wrap_rel`, `wrap_dom` and `consume_wrapper`):
`lam_first_arity` tests a λ's datum against `Succ(Zero)` syntactically and the model tests its
zero-ness for `never`; on a converted value the two agree, since `binder_level` gives `Succ(Zero)`
exactly at a `Never` node and the other nodes give a level that can be zero. The model reads the
value canonically (`defnAt`, `loadedAt`), with the data of the record's binder blocks: the raw
reader gives every λ the datum `never`, so over it every `λ x₁ … xₖ, x₁` would count as a
wrapper. `get_ci`'s `Defn` arm
is the definition kind of any safety (`convert_definition`), `defnAt`'s `some (some _)`. A key with
no address (`keyAddr` answers `none`) names no wrapper; the circuit's terms hold addresses. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Core (KExpr KLevel KKey ExprLvEq LvEq LvEqList)

set_option linter.unusedVariables false

/-! ## Wrappers and their consumption -/

/-- **The wrapper arity `get_ci` gives at a constant**: at the key's address, the stored
definition's value, in the canonical reading, as `λ x₁ … xₖ, x₁` with every λ's datum `never`
(`lam_first_arity`), or `some none` at a constant of another kind (or no wrapper value); `none`
where the load fails. The level parameters are not read. -/
noncomputable def wrapAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (w : KKey) :
    Option (Option Nat) :=
  match keyAddr t w with
  | none => some none
  | some a =>
    match defnAt t E a with
    | none => none
    | some none => some none
    | some (some (_, v)) => some (Ix.Kernel.Semantics.lamFirstArity v 0)

/-- The constant at the head of an application spine (`collect_spine`'s head), if it is one. -/
def appHead (e : KExpr) : Option KKey :=
  match Ix.Kernel.Expr.getAppFn e with
  | .const w _ => some w
  | _ => none

/-- `consume_wrapper` over the head constant and the arguments: a wrapper applied to exactly its
arity leaves its first argument (`some (some a)`); `some none` where nothing is consumed; `none`
where the load of the head constant fails. -/
def consumeOf (W : KKey → Option (Option Nat)) : Option KKey → List KExpr → Option (Option KExpr)
  | none, _ => some none
  | some _, [] => some none
  | some w, a :: rest => (W w).map fun k => if k = some (rest.length + 1) then some a else none

/-- **`consume_wrapper`**: one wrapper consumed at the head of `t`, under the wrapper readings
`W`. -/
def consumeAt (W : KKey → Option (Option Nat)) (t : KExpr) : Option (Option KExpr) :=
  consumeOf W (appHead t) (Ix.Kernel.Expr.getAppArgs t)

/-- **The loop of `wrap_dom` at `sm = 1`**: `c` is `t` with the wrappers at its head consumed, one
at a time. -/
inductive Consumes (W : KKey → Option (Option Nat)) : KExpr → KExpr → Prop
  | refl (t : KExpr) : Consumes W t t
  | step {t a c : KExpr} : consumeAt W t = some (some a) → Consumes W a c → Consumes W t c

/-! ## `wrap_rel` at full consumption -/

/-- **`wrap_rel(1, g, d) = 1`** under the wrapper readings `W`: `g` and `d` have one shape; a
`let` is related only to a `let`, part by part; an application, a projection (same structure and
index) part by part; a binder by the zero-ness of its datum (`pw_eq`), its body, and its domain:
the generated domain's wrappers consumed until none is left (`Consumes`, then `consumeAt` answers
that nothing is consumed), the rest related to the declared domain (`wrap_dom`); any other node as
`kexpr_struct_eq` relates it (levels up to semantic equality). -/
inductive FullCons (W : KKey → Option (Option Nat)) : KExpr → KExpr → Prop
  | bvar (i : Nat) : FullCons W (.bvar i) (.bvar i)
  | fvar {i : Nat} {t t' : KExpr} : ExprLvEq t t' → FullCons W (.fvar i t) (.fvar i t')
  | sort {u v : KLevel} : LvEq u v → FullCons W (.sort u) (.sort v)
  | const {n : KKey} {us vs : List KLevel} :
      LvEqList us vs → FullCons W (.const n us) (.const n vs)
  | lit (l : Ix.Kernel.Literal) : FullCons W (.lit l) (.lit l)
  | app {f a f' a' : KExpr} :
      FullCons W f f' → FullCons W a a' → FullCons W (.app f a) (.app f' a')
  | lam {t c b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → Consumes W t c → consumeAt W c = some none → FullCons W c t' →
      FullCons W b b' → FullCons W (.lam t b m) (.lam t' b' m')
  | forallE {t c b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → Consumes W t c → consumeAt W c = some none → FullCons W c t' →
      FullCons W b b' → FullCons W (.forallE t b m) (.forallE t' b' m')
  | letE {t v b t' v' b' : KExpr} {l l' : Ix.Kernel.LetMeta} :
      FullCons W t t' → FullCons W v v' → FullCons W b b' →
      FullCons W (.letE t v b l) (.letE t' v' b' l')
  | proj {s : KKey} {i : Nat} {e e' : KExpr} :
      FullCons W e e' → FullCons W (.proj s i e) (.proj s i e')

/-! ## Readings that answer more -/

section Mono

variable {W W' : KKey → Option (Option Nat)}

theorem consumeOf_mono (hW : ∀ w x, W w = some x → W' w = some x) :
    ∀ (hd : Option KKey) (l : List KExpr) {x : Option KExpr},
      consumeOf W hd l = some x → consumeOf W' hd l = some x
  | none, _, _, h => h
  | some _, [], _, h => h
  | some w, a :: rest, x, h => by
    simp only [consumeOf] at h ⊢
    cases hw : W w with
    | none => rw [hw] at h; simp at h
    | some k => rw [hW w k hw]; rw [hw] at h; exact h

theorem consumeAt_mono (hW : ∀ w x, W w = some x → W' w = some x) {t : KExpr}
    {x : Option KExpr} (h : consumeAt W t = some x) : consumeAt W' t = some x :=
  consumeOf_mono hW (appHead t) (Ix.Kernel.Expr.getAppArgs t) h

theorem Consumes.mono (hW : ∀ w x, W w = some x → W' w = some x) {t c : KExpr}
    (h : Consumes W t c) : Consumes W' t c := by
  induction h with
  | refl t => exact .refl t
  | step hc _ ih => exact .step (consumeAt_mono hW hc) ih

/-- **Full consumption under readings that answer more**: every consumption it reads is answered
the same. -/
theorem FullCons.mono (hW : ∀ w x, W w = some x → W' w = some x) {g d : KExpr}
    (h : FullCons W g d) : FullCons W' g d := by
  induction h with
  | bvar i => exact .bvar i
  | fvar ht => exact .fvar ht
  | sort hu => exact .sort hu
  | const hus => exact .const hus
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hcs hstop _ _ ihdom ihb =>
    exact .lam hpw (hcs.mono hW) (consumeAt_mono hW hstop) ihdom ihb
  | forallE hpw hcs hstop _ _ ihdom ihb =>
    exact .forallE hpw (hcs.mono hW) (consumeAt_mono hW hstop) ihdom ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ih => exact .proj ih

end Mono

/-- **A store holding the records and blobs of `E` gives the same wrapper arities wherever `E`
gives one.** -/
theorem wrapAt_mono {t : Ix.Kernel.RoleTable} {E E' : Ixon.Env}
    (hle : ∀ y c, recordOf E y = some c → recordOf E' y = some c)
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b) :
    ∀ w x, wrapAt t E w = some x → wrapAt t E' w = some x := by
  intro w x h
  unfold wrapAt at h ⊢
  cases hk : keyAddr t w with
  | none => simp only [hk] at h ⊢; exact h
  | some a =>
    simp only [hk] at h ⊢
    cases hd : defnAt t E a with
    | none => simp [hd] at h
    | some y =>
      rw [defnAt_mono (Ok := fun _ => True) (fun y c _ hy => hle y c hy)
        (fun _ _ _ _ => trivial) hblob trivial hd]
      rw [hd] at h
      exact h

/-- A wrapper arity of the store is a definition's value of that arity at the key's address. -/
theorem wrapAt_inv {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {w : KKey} {n : Nat}
    (h : wrapAt t E w = some (some n)) :
    ∃ a nl v, keyAddr t w = some a ∧ defnAt t E a = some (some (nl, v)) ∧
      Ix.Kernel.Semantics.lamFirstArity v 0 = some n := by
  unfold wrapAt at h
  cases hk : keyAddr t w with
  | none => simp [hk] at h
  | some a =>
    simp only [hk] at h
    cases hd : defnAt t E a with
    | none => simp [hd] at h
    | some y =>
      cases y with
      | none => simp [hd] at h
      | some p =>
        obtain ⟨nl, v⟩ := p
        simp only [hd, Option.some.injEq] at h
        exact ⟨a, nl, v, by first | exact hk | rfl, hd, h⟩

/-! ## Up to the semantic equality of levels -/

theorem forall2_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {m₁ : List α} {m₂ : List β},
      List.Forall₂ R l₁ l₂ → List.Forall₂ R m₁ m₂ → List.Forall₂ R (l₁ ++ m₁) (l₂ ++ m₂)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hr hs, h => .cons hr (forall2_append hs h)

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp only [List.length_cons, forall2_length hs]

/-- Terms equal up to levels have the same head constant. -/
theorem appHead_congr {t₁ t : KExpr} (h : ExprLvEq t₁ t) : appHead t₁ = appHead t := by
  induction h with
  | bvar => rfl
  | fvar _ _ => rfl
  | sort _ => rfl
  | const _ => rfl
  | app _ _ ihf _ => exact ihf
  | lam _ _ _ _ => rfl
  | forallE _ _ _ _ => rfl
  | letE _ _ _ _ _ _ => rfl
  | lit => rfl
  | proj _ _ => rfl

/-- Terms equal up to levels have arguments equal up to levels, position by position. -/
theorem getAppArgs_congr {t₁ t : KExpr} (h : ExprLvEq t₁ t) :
    List.Forall₂ ExprLvEq (Ix.Kernel.Expr.getAppArgs t₁) (Ix.Kernel.Expr.getAppArgs t) := by
  induction h with
  | app _ ha ihf _ =>
    simp only [Ix.Kernel.Expr.getAppArgs]
    exact forall2_append ihf (.cons ha .nil)
  | bvar => exact .nil
  | fvar _ _ => exact .nil
  | sort _ => exact .nil
  | const _ => exact .nil
  | lam _ _ _ _ => exact .nil
  | forallE _ _ _ _ => exact .nil
  | letE _ _ _ _ _ _ => exact .nil
  | lit => exact .nil
  | proj _ _ => exact .nil

theorem consumeOf_congr {W : KKey → Option (Option Nat)} (hd : Option KKey) {l₁ l : List KExpr}
    (hA : List.Forall₂ ExprLvEq l₁ l) {x : Option KExpr} (hx : consumeOf W hd l = some x) :
    ∃ x₁, consumeOf W hd l₁ = some x₁ ∧ (x = none → x₁ = none) ∧
      ∀ a, x = some a → ∃ a₁, x₁ = some a₁ ∧ ExprLvEq a₁ a := by
  cases hA with
  | nil => exact ⟨x, hx, id, fun a ha => ⟨a, ha, ExprLvEq.refl a⟩⟩
  | @cons a₁ a₀ r₁ r₀ ha hr =>
    cases hd with
    | none =>
      simp only [consumeOf, Option.some.injEq] at hx
      subst hx
      exact ⟨none, rfl, fun _ => rfl, fun a h => by cases h⟩
    | some w =>
      have hlen : r₁.length = r₀.length := forall2_length hr
      cases hw : W w with
      | none => simp [consumeOf, hw] at hx
      | some k =>
        simp only [consumeOf, hw, Option.map_some, Option.some.injEq] at hx
        subst hx
        refine ⟨if k = some (r₁.length + 1) then some a₁ else none, ?_, ?_, ?_⟩
        · simp only [consumeOf, hw, Option.map_some]
        · rw [hlen]
          intro h
          by_cases hk : k = some (r₀.length + 1)
          · rw [ite_eq_left hk] at h; cases h
          · rw [ite_eq_right hk]
        · rw [hlen]
          intro a h
          by_cases hk : k = some (r₀.length + 1)
          · rw [ite_eq_left hk] at h
            rw [ite_eq_left hk]
            cases h
            exact ⟨a₁, rfl, ha⟩
          · rw [ite_eq_right hk] at h; cases h

/-- **`consume_wrapper` up to levels**: terms equal up to levels consume alike, to terms equal up
to levels. -/
theorem consumeAt_congr {W : KKey → Option (Option Nat)} {t₁ t : KExpr} (h : ExprLvEq t₁ t)
    {x : Option KExpr} (hx : consumeAt W t = some x) :
    ∃ x₁, consumeAt W t₁ = some x₁ ∧ (x = none → x₁ = none) ∧
      ∀ a, x = some a → ∃ a₁, x₁ = some a₁ ∧ ExprLvEq a₁ a := by
  have e : consumeAt W t₁ = consumeOf W (appHead t) (Ix.Kernel.Expr.getAppArgs t₁) := by
    show consumeOf W (appHead t₁) _ = _
    rw [appHead_congr h]
  rw [e]
  exact consumeOf_congr (appHead t) (getAppArgs_congr h) hx

theorem Consumes.congr {W : KKey → Option (Option Nat)} {t c : KExpr} (h : Consumes W t c) :
    ∀ {t₁ : KExpr}, ExprLvEq t₁ t → ∃ c₁, Consumes W t₁ c₁ ∧ ExprLvEq c₁ c := by
  induction h with
  | refl t => intro t₁ ht; exact ⟨t₁, .refl t₁, ht⟩
  | step hc _ ih =>
    intro t₁ ht
    obtain ⟨x₁, hx₁, -, hsome⟩ := consumeAt_congr ht hc
    obtain ⟨a₁, rfl, ha⟩ := hsome _ rfl
    obtain ⟨c₁, hc₁, hcc⟩ := ih ha
    exact ⟨c₁, .step hx₁ hc₁, hcc⟩

/-- **Full consumption from a generated term equal up to levels.** -/
theorem FullCons.congr_left {W : KKey → Option (Option Nat)} {g d : KExpr}
    (h : FullCons W g d) : ∀ {g₁ : KExpr}, ExprLvEq g₁ g → FullCons W g₁ d := by
  induction h with
  | bvar i => intro g₁ hg; cases hg; exact .bvar i
  | fvar ht => intro g₁ hg; cases hg with | fvar h1 => exact .fvar (h1.trans ht)
  | sort hu => intro g₁ hg; cases hg with | sort h1 => exact .sort (h1.trans hu)
  | const hus => intro g₁ hg; cases hg with | const h1 => exact .const (h1.trans hus)
  | lit l => intro g₁ hg; cases hg; exact .lit l
  | app _ _ ihf iha =>
    intro g₁ hg
    cases hg with | app hf ha => exact .app (ihf hf) (iha ha)
  | lam hpw hcs hstop _ _ ihdom ihb =>
    intro g₁ hg
    cases hg with
    | lam ht hb =>
      obtain ⟨c₁, hcs₁, hcc⟩ := hcs.congr ht
      obtain ⟨x₁, hx₁, hnone, -⟩ := consumeAt_congr hcc hstop
      obtain rfl := hnone rfl
      exact .lam hpw hcs₁ hx₁ (ihdom hcc) (ihb hb)
  | forallE hpw hcs hstop _ _ ihdom ihb =>
    intro g₁ hg
    cases hg with
    | forallE ht hb =>
      obtain ⟨c₁, hcs₁, hcc⟩ := hcs.congr ht
      obtain ⟨x₁, hx₁, hnone, -⟩ := consumeAt_congr hcc hstop
      obtain rfl := hnone rfl
      exact .forallE hpw hcs₁ hx₁ (ihdom hcc) (ihb hb)
  | letE _ _ _ iht ihv ihb =>
    intro g₁ hg
    cases hg with | letE ht hv hb => exact .letE (iht ht) (ihv hv) (ihb hb)
  | proj _ ih => intro g₁ hg; cases hg with | proj h1 => exact .proj (ih h1)

/-- **Full consumption to a declared term equal up to levels.** -/
theorem FullCons.congr_right {W : KKey → Option (Option Nat)} {g d : KExpr}
    (h : FullCons W g d) : ∀ {d₁ : KExpr}, ExprLvEq d d₁ → FullCons W g d₁ := by
  induction h with
  | bvar i => intro d₁ hd; cases hd; exact .bvar i
  | fvar ht => intro d₁ hd; cases hd with | fvar h1 => exact .fvar (ht.trans h1)
  | sort hu => intro d₁ hd; cases hd with | sort h1 => exact .sort (hu.trans h1)
  | const hus => intro d₁ hd; cases hd with | const h1 => exact .const (hus.trans h1)
  | lit l => intro d₁ hd; cases hd; exact .lit l
  | app _ _ ihf iha =>
    intro d₁ hd
    cases hd with | app hf ha => exact .app (ihf hf) (iha ha)
  | lam hpw hcs hstop _ _ ihdom ihb =>
    intro d₁ hd
    cases hd with | lam ht hb => exact .lam hpw hcs hstop (ihdom ht) (ihb hb)
  | forallE hpw hcs hstop _ _ ihdom ihb =>
    intro d₁ hd
    cases hd with | forallE ht hb => exact .forallE hpw hcs hstop (ihdom ht) (ihb hb)
  | letE _ _ _ iht ihv ihb =>
    intro d₁ hd
    cases hd with | letE ht hv hb => exact .letE (iht ht) (ihv hv) (ihb hb)
  | proj _ ih => intro d₁ hd; cases hd with | proj h1 => exact .proj (ih h1)

/-! ## IxC's `WrapRel` -/

theorem wrapLevels_of_lvEqList :
    ∀ {us vs : List KLevel}, LvEqList us vs →
      Ix.Kernel.Semantics.Forall₂
        (fun u v : KLevel => ∀ φ : Ix.Kernel.LevelParam → Nat, u.eval φ = v.eval φ) us vs
  | [], [], _ => .nil
  | [], _ :: _, h => False.elim (h fun _ => 0)
  | _ :: _, [], h => False.elim (h fun _ => 0)
  | _ :: _, _ :: _, h => .cons (fun φ => (h φ).1) (wrapLevels_of_lvEqList fun φ => (h φ).2)

/-- **Terms equal up to levels are related by IxC's `WrapRel`.** -/
theorem exprLvEq_wrapRel (find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)) {g d : KExpr}
    (h : ExprLvEq g d) : Ix.Kernel.Semantics.WrapRel find? g d := by
  induction h with
  | bvar => exact .bvar _
  | fvar _ ih => exact .fvar ih
  | sort hu => exact .sort hu
  | const hus => exact .const (wrapLevels_of_lvEqList hus)
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ iht ihb => exact .lam rfl (.keep iht) ihb
  | forallE _ _ iht ihb => exact .forallE rfl (.keep iht) ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | lit => exact .lit _
  | proj _ ih => exact .proj ih

theorem appHead_some {e : KExpr} {w : KKey} (h : appHead e = some w) :
    ∃ us, Ix.Kernel.Expr.getAppFn e = .const w us := by
  unfold appHead at h
  cases hf : Ix.Kernel.Expr.getAppFn e with
  | const w' us =>
    rw [hf] at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨us, rfl⟩
  | _ => rw [hf] at h; simp at h

section WrapRel

variable {W : KKey → Option (Option Nat)} {find? : KKey → Option (Ix.Kernel.ConstantInfo .anon)}

/-- **A consumption of the store is one of IxC's environment** where the environment has the
store's wrappers. -/
theorem consumeAt_wrapper
    (hW : ∀ w n, W w = some (some n) → Ix.Kernel.Semantics.wrapperArity find? w = some n)
    {t a : KExpr} (h : consumeAt W t = some (some a)) :
    Ix.Kernel.Semantics.consumeWrapper find? t = some a := by
  have hc : consumeOf W (appHead t) (Ix.Kernel.Expr.getAppArgs t) = some (some a) := h
  cases hd : appHead t with
  | none => rw [hd] at hc; simp [consumeOf] at hc
  | some w =>
    rw [hd] at hc
    obtain ⟨us, hfn⟩ := appHead_some hd
    cases hl : Ix.Kernel.Expr.getAppArgs t with
    | nil => rw [hl] at hc; simp [consumeOf] at hc
    | cons a' rest =>
      rw [hl] at hc
      simp only [consumeOf] at hc
      cases hw : W w with
      | none => rw [hw] at hc; simp at hc
      | some k =>
        rw [hw] at hc
        simp only [Option.map_some, Option.some.injEq] at hc
        by_cases hk : k = some (rest.length + 1)
        · rw [ite_eq_left hk] at hc
          simp only [Option.some.injEq] at hc
          subst hc
          subst hk
          have hA := hW w _ hw
          simp [Ix.Kernel.Semantics.consumeWrapper, hfn, hl, hA]
        · rw [ite_eq_right hk] at hc
          cases hc

theorem Consumes.toWrapDom
    (hW : ∀ w n, W w = some (some n) → Ix.Kernel.Semantics.wrapperArity find? w = some n)
    {t c : KExpr} (h : Consumes W t c) :
    ∀ {t' : KExpr}, Ix.Kernel.Semantics.WrapRel find? c t' →
      Ix.Kernel.Semantics.WrapDom find? t t' := by
  induction h with
  | refl _ => intro t' hr; exact .keep hr
  | step hc _ ih => intro t' hr; exact .consume (consumeAt_wrapper hW hc) (ih hr)

/-- **Full consumption is IxC's `WrapRel`** where IxC's environment has the store's wrappers: the
consumed wrappers are consumed by `WrapDom.consume`, the rest kept. -/
theorem FullCons.toWrapRel
    (hW : ∀ w n, W w = some (some n) → Ix.Kernel.Semantics.wrapperArity find? w = some n)
    {g d : KExpr} (h : FullCons W g d) : Ix.Kernel.Semantics.WrapRel find? g d := by
  induction h with
  | bvar i => exact .bvar i
  | fvar ht => exact .fvar (exprLvEq_wrapRel find? ht)
  | sort hu => exact .sort hu
  | const hus => exact .const (wrapLevels_of_lvEqList hus)
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hcs _ _ _ ihdom ihb => exact .lam hpw (hcs.toWrapDom hW ihdom) ihb
  | forallE hpw hcs _ _ _ ihdom ihb => exact .forallE hpw (hcs.toWrapDom hW ihdom) ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ih => exact .proj ih

/-- **The reconstruction above the reconstruction or its full consumption**: a type equal to the
reconstruction `R` up to levels is above (IxC's `WrapRel`) a type that is `R` up to levels or `R`
fully consumed, where IxC's environment has the store's wrappers. At a canonical record in
`RFormS` and a record in `RecordRecon`, member by member, this is the type part of the twin seam's
`CanonAbove`. -/
theorem wrapRel_of_recon
    (hW : ∀ w n, W w = some (some n) → Ix.Kernel.Semantics.wrapperArity find? w = some n)
    {tyC tyW R : KExpr} (hC : ExprLvEq tyC R) (hR : ExprLvEq tyW R ∨ FullCons W R tyW) :
    Ix.Kernel.Semantics.WrapRel find? tyC tyW := by
  rcases hR with h | h
  · exact exprLvEq_wrapRel find? (hC.trans h.symm)
  · exact (h.congr_left hC).toWrapRel hW

end WrapRel

/-! ## The form-agnostic record-level form -/

theorem MemberRecon.mono {T T' : KExpr → KExpr → Prop} (hT : ∀ a b, T a b → T' a b)
    {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {rb : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} {es : List FlatEntry} {off fuel k : Nat} {r : Ixon.Recursor}
    (h : MemberRecon T t E rb crb rs es off fuel k r) :
    MemberRecon T' t E rb crb rs es off fuel k r := by
  obtain ⟨ty, R, bodies, cbk, hty, hR, hrel, hb, hcb, hrules⟩ := h
  exact ⟨ty, R, bodies, cbk, hty, hR, hT _ _ hrel, hb, hcb, hrules⟩

theorem RecordReconWith.mono {T T' : KExpr → KExpr → Prop} (hT : ∀ a b, T a b → T' a b)
    {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B rb : _root_.Address}
    (h : RecordReconWith T t E B rb) : RecordReconWith T' t E B rb := by
  obtain ⟨crb, rs, es, off, fuel, hrb, hrs, hRF, hBD, hM⟩ := h
  exact ⟨crb, rs, es, off, fuel, hrb, hrs, hRF, hBD, fun k r hr => MemberRecon.mono hT (hM k r hr)⟩

/-- **The form-agnostic record-level form** (`check_recs` with its form state, under any role
context): the record `rb` of the block `B` in the store `E` is the block's family over the
flattened family derived from the block, and every recursor's declared type is, at its position,
the reconstruction up to levels or the reconstruction fully consumed (`wrap_rel(1, ·, ·)`), each
rule following the reconstructed body under the λs of the declared type. The circuit's form state
gives more (one of the two at all members); this is what the twin seam compares member by
member. -/
def RecordRecon (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B rb : _root_.Address) : Prop :=
  RecordReconWith (fun ty R => ExprLvEq ty R ∨ FullCons (wrapAt t E) R ty) t E B rb

/-- **A record in the reconstruction's form is in the form-agnostic one.** -/
theorem RFormS.toRecordRecon {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B rb : _root_.Address}
    (h : RFormS t E B rb) : RecordRecon t E B rb :=
  RecordReconWith.mono (fun _ _ h => Or.inl h) h

/-- **The form-agnostic form passes to a store that holds the first's records and blobs.** -/
theorem RecordRecon.grow {t : Ix.Kernel.RoleTable} {E E' : Ixon.Env}
    (hle : ∀ y c, recordOf E y = some c → recordOf E' y = some c)
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {B rb : _root_.Address} (h : RecordRecon t E B rb) : RecordRecon t E' B rb := by
  obtain ⟨crb, rs, es, off, fuel, hrb, hrs, hRF, hBD, hM⟩ := h
  exact ⟨crb, rs, es, off, fuel, hle _ _ hrb, hrs, hRF.of_blobs hblob,
    blockDerivedFlat_grow hle hblob hBD,
    fun k r hr => MemberRecon.mono
      (fun _ _ h => h.imp_right (FullCons.mono (wrapAt_mono hle hblob)))
      (memberRecon_transport (reconOfStore_le hle hblob) (ReconView.closedOn_true _) hblob
        (fun e _ => ⟨trivial, fun _ _ _ _ _ _ => trivial⟩) (hM k r hr))⟩

end IxVM.Refinement.Binding.FamilyRecon
