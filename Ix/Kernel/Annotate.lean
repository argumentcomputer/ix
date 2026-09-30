/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer

/-! # The annotation pass

Raw terms carry no binder regimes. `annotate` computes them bottom up: each
`lam`/`forallE` gets the zero condition of its inferred codomain sort, using
the certified `inferA` and `whnf` on the already annotated subterms. The pass
proves that its output erases to the exact supplied term (`annotate_erase`).
Its binder regimes are validated by `inferA` when the declaration is
checked; structural fidelity does not establish their semantic correctness.

Nested inference and normalization failures retain their causes. In
particular, running out of fuel below a binder remains exhaustion, and
unsuccessful conversion remains an unresolved search. -/

namespace Ix.Kernel

open Model Certified

universe u v

variable {β : Type u} [DecidableEq β]

/-- Carry the binder annotations of `ann` back onto `raw`, where `ann`
annotates `raw` with some variables replaced by terms: every non-variable node
of `raw` has the same constructor in `ann`, and every variable of `raw` is kept
as it is. -/
def transferAnnotations : VExpr β → AExpr β → Option (AExpr β)
  | .bvar i, _ => some (.bvar i)
  | .sort l, _ => some (.sort l)
  | .const r ls, _ => some (.const r ls)
  | .natLit r n, _ => some (.natLit r n)
  | .app f a, .app f' a' => return .app (← transferAnnotations f f') (← transferAnnotations a a')
  | .lam D b, .lam p D' b' =>
    return .lam p (← transferAnnotations D D') (← transferAnnotations b b')
  | .forallE D B, .forallE p D' B' =>
    return .forallE p (← transferAnnotations D D') (← transferAnnotations B B')
  | .letE t v b, .letE t' v' b' =>
    return .letE (← transferAnnotations t t') (← transferAnnotations v v') (← transferAnnotations b b')
  | .proj r i x, .proj _ _ x' => return .proj r i (← transferAnnotations x x')
  | _, _ => none

omit [DecidableEq β] in
theorem transferAnnotations_erase : ∀ {raw : VExpr β} {ann a : AExpr β},
    transferAnnotations raw ann = some a → a.erase = raw
  | .bvar _, _, _, h | .sort _, _, _, h | .const _ _, _, _, h | .natLit _ _, _, _, h => by
    simp only [transferAnnotations, Option.some.injEq] at h; subst h; rfl
  | .app f x, .app f' x', a, h => by
    simp only [transferAnnotations, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨f₁, hf, x₁, hx, rfl⟩ := h
    simp only [AExpr.erase, transferAnnotations_erase hf, transferAnnotations_erase hx]
  | .lam D b, .lam p D' b', a, h => by
    simp only [transferAnnotations, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨D₁, hD, b₁, hb, rfl⟩ := h
    simp only [AExpr.erase, transferAnnotations_erase hD, transferAnnotations_erase hb]
  | .forallE D B, .forallE p D' B', a, h => by
    simp only [transferAnnotations, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨D₁, hD, B₁, hB, rfl⟩ := h
    simp only [AExpr.erase, transferAnnotations_erase hD, transferAnnotations_erase hB]
  | .letE t v b, .letE t' v' b', a, h => by
    simp only [transferAnnotations, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨t₁, ht, v₁, hv, b₁, hb, rfl⟩ := h
    simp only [AExpr.erase, transferAnnotations_erase ht, transferAnnotations_erase hv,
      transferAnnotations_erase hb]
  | .proj r i x, .proj _ _ x', a, h => by
    simp only [transferAnnotations, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨x₁, hx, rfl⟩ := h
    simp only [AExpr.erase, transferAnnotations_erase hx]
  | .app _ _, .bvar _, _, h | .app _ _, .sort _, _, h | .app _ _, .const _ _, _, h
  | .app _ _, .lam _ _ _, _, h | .app _ _, .forallE _ _ _, _, h | .app _ _, .letE _ _ _, _, h
  | .app _ _, .proj _ _ _, _, h | .app _ _, .natLit _ _, _, h => by simp [transferAnnotations] at h
  | .lam _ _, .bvar _, _, h | .lam _ _, .sort _, _, h | .lam _ _, .const _ _, _, h
  | .lam _ _, .app _ _, _, h | .lam _ _, .forallE _ _ _, _, h | .lam _ _, .letE _ _ _, _, h
  | .lam _ _, .proj _ _ _, _, h | .lam _ _, .natLit _ _, _, h => by simp [transferAnnotations] at h
  | .forallE _ _, .bvar _, _, h | .forallE _ _, .sort _, _, h | .forallE _ _, .const _ _, _, h
  | .forallE _ _, .app _ _, _, h | .forallE _ _, .lam _ _ _, _, h | .forallE _ _, .letE _ _ _, _, h
  | .forallE _ _, .proj _ _ _, _, h | .forallE _ _, .natLit _ _, _, h => by simp [transferAnnotations] at h
  | .letE _ _ _, .bvar _, _, h | .letE _ _ _, .sort _, _, h | .letE _ _ _, .const _ _, _, h
  | .letE _ _ _, .app _ _, _, h | .letE _ _ _, .lam _ _ _, _, h | .letE _ _ _, .forallE _ _ _, _, h
  | .letE _ _ _, .proj _ _ _, _, h | .letE _ _ _, .natLit _ _, _, h => by simp [transferAnnotations] at h
  | .proj _ _ _, .bvar _, _, h | .proj _ _ _, .sort _, _, h | .proj _ _ _, .const _ _, _, h
  | .proj _ _ _, .app _ _, _, h | .proj _ _ _, .lam _ _ _, _, h | .proj _ _ _, .forallE _ _ _, _, h
  | .proj _ _ _, .letE _ _ _, _, h | .proj _ _ _, .natLit _ _, _, h => by simp [transferAnnotations] at h

/-! ## Reading binder conditions without inference

A binder's condition is the zero condition of a sort that inference would
compute. These readers return it where the syntax already determines it
exactly: a Pi's own (validated) annotation, since `zeroCondition (imax u v) =
zeroCondition v`; a sort, never a proposition's sort; a constant family whose
type telescope ends in a sort after its arguments; and a local variable whose
type is a sort. Anything else is `none` and `annotate` infers. Annotations are
proposals: `inferA` validates every one against the sort it computes. -/

/-- The rest of a type telescope after `n` Pi binders, if it has that many. -/
def telescopeAfter : AExpr β → Nat → Option (AExpr β)
  | e, 0 => some e
  | .forallE _ _ B, n + 1 => telescopeAfter B n
  | _, _ + 1 => none

/-- The zero condition of a constant family's sort after `n` arguments. -/
def familyCondition (entries : Environment β) (d : ConstRef β) (ls : List VLevel) (n : Nat) :
    Option PropWhen :=
  match entries d with
  | some entry =>
    match telescopeAfter entry.type n with
    | some (.sort l) => some (zeroCondition (l.inst ls))
    | _ => none
  | none => none

/-- The zero condition of the sort of the type `T`. `locals` is the context
`T`'s variables refer to, when it is known. -/
def typeCondition (entries : Environment β) (locals : Option (Context β)) (T : AExpr β) :
    Option PropWhen :=
  match T with
  | .forallE p _ _ => some p
  | .sort _ => some .never
  | .bvar i =>
    match locals.bind (·[i]?) with
    | some (.sort l) => some (zeroCondition l)
    | _ => none
  | _ =>
    match spine T [] with
    | (.const d ls, args) => familyCondition entries d ls args.length
    | _ => none

/-- The zero condition of the sort of the type of the term `e`, at `Γ`. -/
def termCondition (entries : Environment β) (Γ : Context β) (e : AExpr β) : Option PropWhen :=
  match e with
  | .lam p _ _ => some p
  | .forallE .. | .sort _ => some .never
  | .bvar i =>
    match Γ[i]? with
    | some A => typeCondition entries (some Γ) A
    | none => none
  | _ =>
    match spine e [] with
    | (.const c ls, args) =>
      match entries c with
      | some entry =>
        match telescopeAfter entry.type args.length with
        -- The rest's variables are the telescope's binders, not `Γ`'s.
        | some rest => typeCondition entries none (rest.instL ls)
        | none => none
      | none => none
    | _ => none

/-- Compute binder annotations. -/
def annotate : Nat → (entries : Environment β) → (Γ : Context β) → VExpr β →
    Search (AExpr β)
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, entries, Γ, e =>
    match e with
    | .bvar i => .ok (.bvar i)
    | .sort l => .ok (.sort l)
    | .const r ls => .ok (.const r ls)
    | .natLit r n => .ok (.natLit r n)
    | .app f a => do
      let f' ← annotate fuel entries Γ f
      let a' ← annotate fuel entries Γ a
      return .app f' a'
    | .proj r i x => do
      let x' ← annotate fuel entries Γ x
      return .proj r i x'
    | .lam D b => do
      let D' ← annotate fuel entries Γ D
      let Γ' := Γ.push D'
      let b' ← annotate fuel entries Γ' b
      match termCondition entries Γ' b' with
      | some p => return .lam p D' b'
      | none =>
        let ⟨B, _⟩ ← inferA.{u,v} fuel entries Γ' b'
        let ⟨SB, hSB⟩ ← inferA.{u,v} fuel entries Γ' B
        let ⟨lB, _⟩ ← sortOf (whnf.{u,v} fuel entries Γ' SB) hSB
        return .lam (zeroCondition lB) D' b'
    | .forallE D B => do
      let D' ← annotate fuel entries Γ D
      let Γ' := Γ.push D'
      let B' ← annotate fuel entries Γ' B
      match typeCondition entries (some Γ') B' with
      | some p => return .forallE p D' B'
      | none =>
        let ⟨SB, hSB⟩ ← inferA.{u,v} fuel entries Γ' B'
        let ⟨lB, _⟩ ← sortOf (whnf.{u,v} fuel entries Γ' SB) hSB
        return .forallE (zeroCondition lB) D' B'
    | .letE t v b => do
      let t' ← annotate fuel entries Γ t
      let v' ← annotate fuel entries Γ v
      -- With the let variable opaque; failing that, annotate the body with the
      -- value substituted and carry its binder annotations back. Annotations
      -- are proposals that inference validates, so either route is sound.
      let b' ← Search.orElse (annotate fuel entries (Γ.push t') b) fun _ => do
        let substituted ← annotate fuel entries Γ (b.inst v)
        Search.ofOption (transferAnnotations b substituted)
          (.unresolved "the let body's annotations did not transfer")
      return .letE t' v' b'

private theorem search_orElse_eq_ok {α : Type u} {x : Search α} {f : Unit → Search α} {b : α}
    (h : Search.orElse x f = .ok b) : x = .ok b ∨ f () = .ok b := by
  unfold Search.orElse at h
  split at h
  · exact .inl (by simp_all)
  · split at h
    · exact .inr (by simp_all)
    · cases h

private theorem search_bind_eq_ok {α γ : Type u} {x : Search α} {f : α → Search γ} {b : γ}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Every successful annotation preserves the exact raw expression. This
does not assert scope or the validity of its binder conditions. -/
theorem annotate_erase {fuel : Nat} {entries : Environment β} {Γ : Context β}
    {raw : VExpr β} {a : AExpr β} (h : annotate.{u,v} fuel entries Γ raw = .ok a) :
    a.erase = raw := by
  induction fuel generalizing Γ raw a with
  | zero => cases h
  | succ fuel ih =>
    cases raw with
    | bvar _ | sort _ | const _ _ | natLit _ _ => cases h; rfl
    | app f x =>
      obtain ⟨f', hf, h⟩ := search_bind_eq_ok h
      obtain ⟨x', hx, h⟩ := search_bind_eq_ok h
      cases h
      simp only [AExpr.erase, ih hf, ih hx]
    | proj r i x =>
      obtain ⟨x', hx, h⟩ := search_bind_eq_ok h
      cases h
      simp only [AExpr.erase, ih hx]
    | lam D b =>
      obtain ⟨D', hD, h⟩ := search_bind_eq_ok h
      obtain ⟨b', hb, h⟩ := search_bind_eq_ok h
      split at h
      · cases h
        simp only [AExpr.erase, ih hD, ih hb]
      · obtain ⟨⟨B, _⟩, _, h⟩ := search_bind_eq_ok h
        obtain ⟨⟨SB, _⟩, _, h⟩ := search_bind_eq_ok h
        obtain ⟨⟨l, _⟩, _, h⟩ := search_bind_eq_ok h
        cases h
        simp only [AExpr.erase, ih hD, ih hb]
    | forallE D B =>
      obtain ⟨D', hD, h⟩ := search_bind_eq_ok h
      obtain ⟨B', hB, h⟩ := search_bind_eq_ok h
      split at h
      · cases h
        simp only [AExpr.erase, ih hD, ih hB]
      · obtain ⟨⟨SB, _⟩, _, h⟩ := search_bind_eq_ok h
        obtain ⟨⟨l, _⟩, _, h⟩ := search_bind_eq_ok h
        cases h
        simp only [AExpr.erase, ih hD, ih hB]
    | letE t v b =>
      obtain ⟨t', ht, h⟩ := search_bind_eq_ok h
      obtain ⟨v', hv, h⟩ := search_bind_eq_ok h
      obtain ⟨b', hb, h⟩ := search_bind_eq_ok h
      cases h
      have hb' : b'.erase = b := by
        rcases search_orElse_eq_ok hb with hb | hb
        · exact ih hb
        · obtain ⟨_, -, hb⟩ := search_bind_eq_ok hb
          simp only [Search.ofOption] at hb
          split at hb
          · cases hb; exact transferAnnotations_erase ‹_›
          · cases hb
      simp only [AExpr.erase, ih ht, ih hv, hb']

/-- Package an exact annotation with its separately checked scope, reusing
the model's reading interface. Binder-condition scope is included in `hs`. -/
def annotationReading {fuel : Nat} {entries : Environment β} {Γ : Context β}
    {raw : VExpr β} {a : AExpr β} {universes depth : Nat}
    (h : annotate.{u,v} fuel entries Γ raw = .ok a) (hs : a.Scope universes depth) :
    Model.Reading universes depth raw := ⟨a, annotate_erase h, hs⟩

/-- Exact reading transfers the raw reference list without discarding
annotation-condition scope, which is a separate obligation. -/
theorem annotate_references {fuel : Nat} {entries : Environment β} {Γ : Context β}
    {raw : VExpr β} {a : AExpr β} (h : annotate.{u,v} fuel entries Γ raw = .ok a) :
    a.references = raw.refs := by
  rw [← annotate_erase h, AExpr.refs_erase]

theorem annotate_raw_scope {fuel : Nat} {entries : Environment β} {Γ : Context β}
    {raw : VExpr β} {a : AExpr β} {universes depth : Nat}
    (h : annotate.{u,v} fuel entries Γ raw = .ok a) (hs : a.Scope universes depth) :
    raw.LevelWF universes ∧ raw.ClosedN depth := by
  rw [← annotate_erase h]
  exact hs.erase

end Ix.Kernel
