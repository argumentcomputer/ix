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

Binder pushes retain each type at its introduction depth. Local reads lift
only the requested type; inference fallbacks materialize the exact model
context. This keeps structural annotation linear on binder towers.

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

/-- Annotation keeps new binder types in the context in which they were
written. A push is constant time; reading a variable lifts just its type. -/
structure AnnotationContext (β : Type u) where
  base : Context β
  pending : List (AExpr β) := []

namespace AnnotationContext

omit [DecidableEq β] in
private theorem liftN_zero (A : AExpr β) (cutoff : Nat) : A.liftN 0 cutoff = A := by
  induction A generalizing cutoff <;> simp_all [AExpr.liftN, liftVar]

omit [DecidableEq β] in
private theorem liftN_one (A : AExpr β) (depth cutoff : Nat) :
    (A.liftN depth cutoff).liftN 1 cutoff = A.liftN (depth + 1) cutoff := by
  induction A generalizing cutoff with
  | bvar index =>
    simp only [AExpr.liftN, liftVar, AExpr.bvar.injEq]
    split <;> (try split) <;> omega
  | _ => simp_all [AExpr.liftN]

def push (A : AExpr β) (Γ : AnnotationContext β) : AnnotationContext β :=
  { Γ with pending := A :: Γ.pending }

private def liftBase (base : Context β) : Nat → Context β
  | 0 => base
  | n + 1 => base.map (AExpr.liftN (n + 1) ·)

omit [DecidableEq β] in
private theorem liftBase_eq_map (base : Context β) (n : Nat) :
    liftBase base n = base.map (AExpr.liftN n ·) := by
  cases n <;> simp [liftBase, liftN_zero]

private def materialize (base : Context β) : List (AExpr β) → Nat → Context β
  | [], depth => liftBase base depth
  | A :: rest, depth => A.liftN (depth + 1) :: materialize base rest (depth + 1)

/-- The exact model context, with every pending shift applied once. -/
def toContext (Γ : AnnotationContext β) : Context β :=
  materialize Γ.base Γ.pending 0

private def lookupAt (base : Context β) : List (AExpr β) → Nat → Nat → Option (AExpr β)
  | [], 0, index => base[index]?
  | [], depth + 1, index => (base[index]?).map (AExpr.liftN (depth + 1) ·)
  | A :: _, depth, 0 => some (A.liftN (depth + 1))
  | _ :: rest, depth, index + 1 => lookupAt base rest (depth + 1) index

def lookup (Γ : AnnotationContext β) (index : Nat) : Option (AExpr β) :=
  lookupAt Γ.base Γ.pending 0 index

omit [DecidableEq β] in
private theorem materialize_succ (base : Context β) (pending : List (AExpr β)) (depth : Nat) :
    materialize base pending (depth + 1) =
      (materialize base pending depth).map (AExpr.liftN 1 ·) := by
  induction pending generalizing depth with
  | nil =>
    simp only [materialize, liftBase_eq_map, List.map_map, Function.comp_def]
    congr 1
    funext A
    exact (liftN_one A depth 0).symm
  | cons A rest ih =>
    simp only [materialize, List.map_cons, ih, List.cons.injEq]
    constructor
    · exact (liftN_one A (depth + 1) 0).symm
    · trivial

omit [DecidableEq β] in
@[simp] theorem toContext_base (Γ : Context β) : (⟨Γ, []⟩ : AnnotationContext β).toContext = Γ := rfl

omit [DecidableEq β] in
/-- Delaying binder shifts preserves the context used by certified inference. -/
@[simp] theorem toContext_push (Γ : AnnotationContext β) (A : AExpr β) :
    (Γ.push A).toContext = Γ.toContext.push A := by
  simp only [push, toContext, materialize, Context.push]
  rw [materialize_succ]

omit [DecidableEq β] in
private theorem lookupAt_eq_getElem? (base : Context β) (pending : List (AExpr β))
    (depth index : Nat) :
    lookupAt base pending depth index = (materialize base pending depth)[index]? := by
  induction pending generalizing depth index with
  | nil => cases depth <;> simp [lookupAt, materialize, liftBase, List.getElem?_map]
  | cons A rest ih => cases index <;> simp [lookupAt, materialize, ih]

omit [DecidableEq β] in
/-- A variable read agrees with the full model context at every index,
including out-of-scope indices. -/
@[simp] theorem lookup_eq_getElem? (Γ : AnnotationContext β) (index : Nat) :
    Γ.lookup index = Γ.toContext[index]? :=
  lookupAt_eq_getElem? Γ.base Γ.pending 0 index

end AnnotationContext

/-! ## Reading binder conditions without inference

A binder's condition is the zero condition of a sort that inference would
compute. These readers return it where the syntax already determines it
exactly: a Pi's own (validated) annotation, since `zeroCondition (imax u v) =
zeroCondition v`; a sort, never a proposition's sort; a constant family whose
type telescope ends in a sort after its arguments; and a local variable whose
type is a sort. For a constant application, the last consumed Pi annotation
already describes its result type's sort, even when that type is a telescope
variable. Anything else is `none` and `annotate` infers. Annotations are
proposals: `inferA` validates every one against the sort it computes. -/

/-- The rest of a type telescope after `n` Pi binders, if it has that many. -/
def telescopeAfter : AExpr β → Nat → Option (AExpr β)
  | e, 0 => some e
  | .forallE _ _ B, n + 1 => telescopeAfter B n
  | _, _ + 1 => none

/-- The last consumed Pi's codomain condition after a positive number of
arguments. Term substitution preserves that condition; only the constant's
universe arguments need instantiation. Hidden Pis and overapplication fall
back to inference. -/
def telescopeCodomainCondition : AExpr β → Nat → Option PropWhen
  | .forallE p _ _, 1 => some p
  | .forallE _ _ B, n + 2 => telescopeCodomainCondition B (n + 1)
  | _, _ => none

/-- The zero condition of a constant family's sort after `n` arguments. -/
def familyCondition (entries : Environment β) (d : ConstRef β) (ls : List VLevel) (n : Nat) :
    Option PropWhen :=
  match entries d with
  | some entry =>
    match telescopeAfter entry.type n with
    | some (.sort l) => some (zeroCondition (l.inst ls))
    | _ => none
  | none => none

/-- The zero condition of the sort of the type `T`, using a local-type reader. -/
private def typeConditionWith (entries : Environment β) (lookup : Nat → Option (AExpr β))
    (T : AExpr β) : Option PropWhen :=
  match T with
  | .forallE p _ _ => some p
  | .sort _ => some .never
  | .bvar i =>
    match lookup i with
    | some (.sort l) => some (zeroCondition l)
    | _ => none
  | _ =>
    match spine T [] with
    | (.const d ls, args) => familyCondition entries d ls args.length
    | _ => none

/-- Read a type's condition using an optional full model context. -/
def typeCondition (entries : Environment β) (locals : Option (Context β)) (T : AExpr β) :
    Option PropWhen :=
  typeConditionWith entries (fun i => locals.bind (·[i]?)) T

/-- The zero condition of the sort of the type of the term `e`, using a local-type reader. -/
private def termConditionWith (entries : Environment β) (lookup : Nat → Option (AExpr β))
    (e : AExpr β) : Option PropWhen :=
  match e with
  | .lam p _ _ => some p
  | .forallE .. | .sort _ => some .never
  | .bvar i =>
    match lookup i with
    | some A => typeConditionWith entries lookup A
    | none => none
  | _ =>
    match spine e [] with
    | (.const c ls, args) =>
      match entries c with
      | some entry =>
        match args.length with
        | 0 => typeConditionWith entries (fun _ => none) (entry.type.instL ls)
        | n + 1 => (telescopeCodomainCondition entry.type (n + 1)).map (instCondition ls)
      | none => none
    | _ => none

/-- Read a term's condition in a full model context. -/
def termCondition (entries : Environment β) (Γ : Context β) (e : AExpr β) : Option PropWhen :=
  termConditionWith entries (fun i => Γ[i]?) e

/-- Compute binder annotations, delaying context shifts until a local is
read or the certified inference fallback needs the full model context. -/
private def annotateCore : Nat → (entries : Environment β) → (Γ : AnnotationContext β) → VExpr β →
    Search (AExpr β)
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, entries, Γ, e =>
    match e with
    | .bvar i => .ok (.bvar i)
    | .sort l => .ok (.sort l)
    | .const r ls => .ok (.const r ls)
    | .natLit r n => .ok (.natLit r n)
    | .app f a => do
      let f' ← annotateCore fuel entries Γ f
      let a' ← annotateCore fuel entries Γ a
      return .app f' a'
    | .proj r i x => do
      let x' ← annotateCore fuel entries Γ x
      return .proj r i x'
    | .lam D b => do
      let D' ← annotateCore fuel entries Γ D
      let Γ' := Γ.push D'
      let b' ← annotateCore fuel entries Γ' b
      match termConditionWith entries Γ'.lookup b' with
      | some p => return .lam p D' b'
      | none =>
        let Γ' := Γ'.toContext
        let ⟨B, _⟩ ← inferA.{u,v} fuel entries Γ' b'
        let ⟨SB, hSB⟩ ← inferA.{u,v} fuel entries Γ' B
        let ⟨lB, _⟩ ← sortOf (whnf.{u,v} fuel entries Γ' SB) hSB
        return .lam (zeroCondition lB) D' b'
    | .forallE D B => do
      let D' ← annotateCore fuel entries Γ D
      let Γ' := Γ.push D'
      let B' ← annotateCore fuel entries Γ' B
      match typeConditionWith entries Γ'.lookup B' with
      | some p => return .forallE p D' B'
      | none =>
        let Γ' := Γ'.toContext
        let ⟨SB, hSB⟩ ← inferA.{u,v} fuel entries Γ' B'
        let ⟨lB, _⟩ ← sortOf (whnf.{u,v} fuel entries Γ' SB) hSB
        return .forallE (zeroCondition lB) D' B'
    | .letE t v b => do
      let t' ← annotateCore fuel entries Γ t
      let v' ← annotateCore fuel entries Γ v
      -- With the let variable opaque; failing that, annotate the body with the
      -- value substituted and carry its binder annotations back. Annotations
      -- are proposals that inference validates, so either route is sound.
      let b' ← Search.orElse (annotateCore fuel entries (Γ.push t') b) fun _ => do
        let substituted ← annotateCore fuel entries Γ (b.inst v)
        Search.ofOption (transferAnnotations b substituted)
          (.unresolved "the let body's annotations did not transfer")
      return .letE t' v' b'

/-- Compute binder annotations, preserving the supplied model context. -/
def annotate (fuel : Nat) (entries : Environment β) (Γ : Context β) (e : VExpr β) :
    Search (AExpr β) :=
  annotateCore.{u,v} fuel entries ⟨Γ, []⟩ e

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
private theorem annotateCore_erase {fuel : Nat} {entries : Environment β} {Γ : AnnotationContext β}
    {raw : VExpr β} {a : AExpr β} (h : annotateCore.{u,v} fuel entries Γ raw = .ok a) :
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

/-- Every successful annotation erases to the exact supplied raw expression. -/
theorem annotate_erase {fuel : Nat} {entries : Environment β} {Γ : Context β}
    {raw : VExpr β} {a : AExpr β} (h : annotate.{u,v} fuel entries Γ raw = .ok a) :
    a.erase = raw :=
  annotateCore_erase h

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
