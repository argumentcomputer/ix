import IxVMRefinement.Assembly.TypingRecLateMajorKey
import IxVMRefinement.StatementRel.ReaderReads
import IxVMRefinement.Obs.KernelCheck
import IxC.Kernel.Semantics.Inductives.WrapRelFacts
import IxC.Kernel.Verify.Inductives.FixRec

/-! # The family key of the reading of a late recursor's type

`RecReads` asks for the key heading the family of the reading `tyP` of a recursor record's type
(`familyKey rc tyP`): `params` literal `∀`s, then the first motive, a literal `∀`-telescope whose
last binder's domain is headed by a constant. Three facts give it.

* **The motive's domain is let-free and literal.** The member check's `check_rec_header_lets`
  peels `params` literal `Forall` cells of the record's converted type and asserts that the next
  `Forall` cell's domain (the first motive's) contains no `Let` cell (`expr_has_let`). The raw
  heap syntax of the converted type is the reading with binder data replaced (`RawShape`), so the
  reading has `params` literal `∀`s and then a `∀` whose domain is let-free
  (`rec_motive_letFree_reading`).
* **Two readings differ in level names only** (`KeyShape`, `exprReader_keyShape`): the reading
  under the recursor's level parameters has the same constructors, keys and bound variables as
  the positional one.
* **The declared motive ends at the family.** The generated recursor type's motive is
  `∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ`; `WrapRel` relates it to an annotation of the declared type, consuming
  wrapper definitions only on the generated side, and the family `T`, stored as an inductive
  type, is no wrapper. So the annotation's motive is a `∀`-telescope ending in a sort whose last
  domain is headed by `T`. An annotation of a let-free term has its shape (`keyShape_of_annotates`),
  so the declared motive's last domain is headed by `T` too (`familyKey_of_wrapRel`).
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Cert.ReaderUnits (throw_ok)

/-! ## Key shape: equal up to levels, binder data and free-variable annotations -/

/-- Two terms of one key shape: the same constructor at every node, `let`s included, the same
keys and bound variables, up to levels, binder data, `let` data and free-variable annotations. -/
inductive KeyShape : Ix.Kernel.Expr .anon → Ix.Kernel.Expr .anon → Prop
  | bvar (i : Nat) : KeyShape (.bvar i) (.bvar i)
  | fvar (i : Nat) (x y : Ix.Kernel.Expr .anon) : KeyShape (.fvar i x) (.fvar i y)
  | sort (l l' : Ix.Kernel.Level) : KeyShape (.sort l) (.sort l')
  | const (k : Ix.Kernel.Key .anon) (us us' : List Ix.Kernel.Level) :
      KeyShape (.const k us) (.const k us')
  | lit (l : Ix.Kernel.Literal) : KeyShape (.lit l) (.lit l)
  | app {f g a b : Ix.Kernel.Expr .anon} :
      KeyShape f g → KeyShape a b → KeyShape (.app f a) (.app g b)
  | lam {t t' b b' : Ix.Kernel.Expr .anon} {m m' : Ix.Kernel.BinderMeta} :
      KeyShape t t' → KeyShape b b' → KeyShape (.lam t b m) (.lam t' b' m')
  | forallE {t t' b b' : Ix.Kernel.Expr .anon} {m m' : Ix.Kernel.BinderMeta} :
      KeyShape t t' → KeyShape b b' → KeyShape (.forallE t b m) (.forallE t' b' m')
  | letE {t t' v v' b b' : Ix.Kernel.Expr .anon} {l l' : Ix.Kernel.LetMeta} :
      KeyShape t t' → KeyShape v v' → KeyShape b b' →
        KeyShape (.letE t v b l) (.letE t' v' b' l')
  | proj {s : Ix.Kernel.Key .anon} {i : Nat} {e e' : Ix.Kernel.Expr .anon} :
      KeyShape e e' → KeyShape (.proj s i e) (.proj s i e')

theorem KeyShape.refl : ∀ e : Ix.Kernel.Expr .anon, KeyShape e e
  | .bvar i => .bvar i
  | .fvar i x => .fvar i x x
  | .sort l => .sort l l
  | .const k us => .const k us us
  | .lit l => .lit l
  | .app f a => .app (KeyShape.refl f) (KeyShape.refl a)
  | .lam t b _ => .lam (KeyShape.refl t) (KeyShape.refl b)
  | .forallE t b _ => .forallE (KeyShape.refl t) (KeyShape.refl b)
  | .letE t v b _ => .letE (KeyShape.refl t) (KeyShape.refl v) (KeyShape.refl b)
  | .proj _ _ e => .proj (KeyShape.refl e)

theorem KeyShape.symm {a b : Ix.Kernel.Expr .anon} (h : KeyShape a b) : KeyShape b a := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i x y => exact .fvar i y x
  | sort l l' => exact .sort l' l
  | const k us us' => exact .const k us' us
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ih => exact .proj ih

/-- One raw shape is one key shape. -/
theorem KeyShape.of_rawShape {a b : Ix.Kernel.Expr .anon} (h : RawShape a b) : KeyShape a b := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i x y => exact .fvar i x y
  | sort l => exact .sort l l
  | const k us => exact .const k us us
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ih => exact .proj ih

/-- The heads of two terms of one key shape have one key shape. -/
theorem KeyShape.getAppFn {a b : Ix.Kernel.Expr .anon} (h : KeyShape a b) :
    KeyShape a.getAppFn b.getAppFn := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i x y => exact .fvar i x y
  | sort l l' => exact .sort l l'
  | const k us us' => exact .const k us us'
  | lit l => exact .lit l
  | app _ _ ihf _ => exact ihf
  | lam ht hb _ _ => exact .lam ht hb
  | forallE ht hb _ _ => exact .forallE ht hb
  | letE ht hv hb _ _ _ => exact .letE ht hv hb
  | proj he _ => exact .proj he

/-- Two terms of one key shape have one head key. -/
theorem headKey_eq_of_keyShape {a b : Ix.Kernel.Expr .anon} (h : KeyShape a b) :
    headKey a = headKey b := by
  unfold headKey
  have hg := h.getAppFn
  generalize a.getAppFn = x at hg ⊢
  generalize b.getAppFn = y at hg ⊢
  cases hg <;> rfl

/-- Two terms of one key shape strip the same number of `∀`s, to bodies of one key shape. -/
theorem keyShape_stripPis : ∀ (n : Nat) {a b : Ix.Kernel.Expr .anon}, KeyShape a b →
    (a.stripPis n = none ∧ b.stripPis n = none) ∨
      ∃ bs body bs' body', a.stripPis n = some (bs, body) ∧ b.stripPis n = some (bs', body') ∧
        KeyShape body body' := by
  intro n
  induction n with
  | zero =>
    intro a b h
    exact Or.inr ⟨[], a, [], b, rfl, rfl, h⟩
  | succ k ih =>
    intro a b h
    cases h with
    | @forallE t t' b₁ b₁' m m' ht hb =>
      rcases ih hb with ⟨h1, h2⟩ | ⟨bs, body, bs', body', h1, h2, h3⟩
      · left
        simp [Ix.Kernel.Expr.stripPis, h1, h2]
      · right
        exact ⟨(t, m) :: bs, body, (t', m') :: bs', body',
          by simp [Ix.Kernel.Expr.stripPis, h1], by simp [Ix.Kernel.Expr.stripPis, h2], h3⟩
    | bvar => exact Or.inl ⟨rfl, rfl⟩
    | fvar => exact Or.inl ⟨rfl, rfl⟩
    | sort => exact Or.inl ⟨rfl, rfl⟩
    | const => exact Or.inl ⟨rfl, rfl⟩
    | lit => exact Or.inl ⟨rfl, rfl⟩
    | app => exact Or.inl ⟨rfl, rfl⟩
    | lam => exact Or.inl ⟨rfl, rfl⟩
    | letE => exact Or.inl ⟨rfl, rfl⟩
    | proj => exact Or.inl ⟨rfl, rfl⟩

/-- A term of the key shape of a let-free term is let-free. -/
theorem letFree_keyShape {a b : Ix.Kernel.Expr .anon} (h : KeyShape a b) :
    Ix.Kernel.Semantics.letFree a = true → Ix.Kernel.Semantics.letFree b = true := by
  induction h with
  | bvar | fvar | sort | const | lit => intro _; rfl
  | app _ _ ihf iha =>
    intro hl
    simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true] at hl ⊢
    exact ⟨ihf hl.1, iha hl.2⟩
  | lam _ _ iht ihb =>
    intro hl
    simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true] at hl ⊢
    exact ⟨iht hl.1, ihb hl.2⟩
  | forallE _ _ iht ihb =>
    intro hl
    simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true] at hl ⊢
    exact ⟨iht hl.1, ihb hl.2⟩
  | letE => intro hl; simp [Ix.Kernel.Semantics.letFree] at hl
  | proj _ ih =>
    intro hl
    simp only [Ix.Kernel.Semantics.letFree] at hl ⊢
    exact ih hl

/-! ## Annotations of let-free terms -/

/-- An annotation is let-free. -/
theorem letFree_of_annotates {E T : Ix.Kernel.Expr .anon} (h : Annotates E T) :
    Ix.Kernel.Semantics.letFree E = true := by
  induction h with
  | bvar => rfl
  | fvar _ _ => rfl
  | sort => rfl
  | const => rfl
  | lit => rfl
  | app _ _ ihf iha =>
    simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true]
    exact ⟨ihf, iha⟩
  | lam _ _ iht ihb =>
    simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true]
    exact ⟨iht, ihb⟩
  | forallE _ _ iht ihb =>
    simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true]
    exact ⟨iht, ihb⟩
  | proj _ ih =>
    simp only [Ix.Kernel.Semantics.letFree]
    exact ih
  | letE _ ih => exact ih

/-- **An annotation of a let-free term has its key shape**: no `let` is expanded. -/
theorem keyShape_of_annotates {E T : Ix.Kernel.Expr .anon} (h : Annotates E T) :
    Ix.Kernel.Semantics.letFree T = true → KeyShape E T := by
  induction h with
  | bvar => intro _; exact .bvar _
  | fvar _ _ => intro _; exact .fvar _ _ _
  | sort => intro _; exact .sort _ _
  | const => intro _; exact .const _ _ _
  | lit => intro _; exact .lit _
  | app _ _ ihf iha =>
    intro hl
    simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true] at hl
    exact .app (ihf hl.1) (iha hl.2)
  | lam _ _ iht ihb =>
    intro hl
    simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true] at hl
    exact .lam (iht hl.1) (ihb hl.2)
  | forallE _ _ iht ihb =>
    intro hl
    simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true] at hl
    exact .forallE (iht hl.1) (ihb hl.2)
  | proj _ ih =>
    intro hl
    simp only [Ix.Kernel.Semantics.letFree] at hl
    exact .proj (ih hl)
  | letE _ _ => intro hl; simp [Ix.Kernel.Semantics.letFree] at hl

/-! ## The last binder of a telescope -/

/-- A term that is a `∀`. -/
abbrev IsForall (e : Ix.Kernel.Expr .anon) : Prop :=
  ∃ (d b : Ix.Kernel.Expr .anon) (m : Ix.Kernel.BinderMeta), e = .forallE d b m

theorem keyShape_isForall {a b : Ix.Kernel.Expr .anon} (h : KeyShape a b) :
    IsForall a ↔ IsForall b := by
  cases h with
  | forallE _ _ => exact ⟨fun _ => ⟨_, _, _, rfl⟩, fun _ => ⟨_, _, _, rfl⟩⟩
  | _ =>
    constructor
    · rintro ⟨_, _, _, he⟩
      cases he
    · rintro ⟨_, _, _, he⟩
      cases he

theorem lastBinderDom_forallE_of_isForall {d b : Ix.Kernel.Expr .anon}
    {m : Ix.Kernel.BinderMeta} (hb : IsForall b) :
    lastBinderDom (.forallE d b m) = lastBinderDom b := by
  obtain ⟨x, y, z, rfl⟩ := hb
  rfl

theorem lastBinderDom_forallE_of_not {d b : Ix.Kernel.Expr .anon} {m : Ix.Kernel.BinderMeta}
    (hb : ¬ IsForall b) : lastBinderDom (.forallE d b m) = some d := by
  cases b with
  | forallE x y z => exact (hb ⟨x, y, z, rfl⟩).elim
  | _ => rfl

/-- **The last binder's domain moves along a key shape.** -/
theorem lastBinderDom_keyShape {a b : Ix.Kernel.Expr .anon} (h : KeyShape a b) :
    ∀ {d : Ix.Kernel.Expr .anon}, lastBinderDom a = some d →
      ∃ d', lastBinderDom b = some d' ∧ KeyShape d d' := by
  induction h with
  | @forallE t t' b₁ b₁' m m' ht hb iht ihb =>
    intro d hd
    by_cases hf : IsForall b₁
    · rw [lastBinderDom_forallE_of_isForall hf] at hd
      rw [lastBinderDom_forallE_of_isForall ((keyShape_isForall hb).mp hf)]
      exact ihb hd
    · rw [lastBinderDom_forallE_of_not hf] at hd
      rw [lastBinderDom_forallE_of_not (fun h' => hf ((keyShape_isForall hb).mpr h'))]
      cases hd
      exact ⟨t', rfl, ht⟩
  | _ =>
    intro d hd
    simp [lastBinderDom] at hd

theorem isForall_of_stripPis {d b : Ix.Kernel.Expr .anon} {m : Ix.Kernel.BinderMeta}
    {bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)} :
    ∀ (k : Nat) {e : Ix.Kernel.Expr .anon}, e.stripPis k = some (bs, .forallE d b m) →
      IsForall e
  | 0, e, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨d, b, m, h.2⟩
  | k + 1, e, h => by
    obtain ⟨t, r, m', bs0, he, -⟩ := Ix.Kernel.Semantics.stripPis_succ_inv h
    exact ⟨t, r, m', he⟩

/-- A telescope that strips to a last `∀` over a non-`∀` body has that `∀`'s domain as its last
binder's domain. -/
theorem lastBinderDom_of_stripPis {d b : Ix.Kernel.Expr .anon} {m : Ix.Kernel.BinderMeta}
    (hb : ¬ IsForall b) :
    ∀ (k : Nat) {e : Ix.Kernel.Expr .anon}
      {bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)},
      e.stripPis k = some (bs, .forallE d b m) → lastBinderDom e = some d
  | 0, e, bs, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
    exact lastBinderDom_forallE_of_not hb
  | k + 1, e, bs, h => by
    obtain ⟨t, r, m', bs0, rfl, hr⟩ := Ix.Kernel.Semantics.stripPis_succ_inv h
    rw [lastBinderDom_forallE_of_isForall (isForall_of_stripPis k hr)]
    exact lastBinderDom_of_stripPis hb k hr

/-! ## The generated side of `WrapRel` -/

/-- A `∀` heads no wrapper. -/
theorem consumeWrapper_of_isForall {find? : Ix.Kernel.Key .anon → Option (ConstantInfo .anon)}
    {e : Ix.Kernel.Expr .anon} (he : IsForall e) :
    Ix.Kernel.Semantics.consumeWrapper find? e = none := by
  obtain ⟨d, b, m, rfl⟩ := he
  first
    | rfl
    | simp [Ix.Kernel.Semantics.consumeWrapper, Ix.Kernel.Expr.getAppFn,
        Ix.Kernel.Expr.getAppArgs]

theorem KeyShape.forallE_inv {t b e : Ix.Kernel.Expr .anon} {m : Ix.Kernel.BinderMeta}
    (h : KeyShape (.forallE t b m) e) :
    ∃ (t' b' : Ix.Kernel.Expr .anon) (m' : Ix.Kernel.BinderMeta), e = .forallE t' b' m' ∧
      KeyShape t t' ∧ KeyShape b b' := by
  cases h with
  | forallE ht hb => exact ⟨_, _, _, rfl, ht, hb⟩

theorem wrapT_forallE_inv {find? : Ix.Kernel.Key .anon → Option (ConstantInfo .anon)}
    {t b e : Ix.Kernel.Expr .anon} {m : Ix.Kernel.BinderMeta}
    (h : Ix.Kernel.Semantics.WrapT find? (.forallE t b m) e) :
    ∃ (a t' b' : Ix.Kernel.Expr .anon) (m' : Ix.Kernel.BinderMeta), e = .forallE t' b' m' ∧
      Ix.Kernel.Semantics.ConsumeStar find? t a ∧ Ix.Kernel.Semantics.WrapT find? a t' ∧
      Ix.Kernel.Semantics.WrapT find? b b' := by
  cases h with
  | forallE _ hcs hWd hWb => exact ⟨_, _, _, _, rfl, hcs, hWd, hWb⟩

theorem wrapT_sort_inv {find? : Ix.Kernel.Key .anon → Option (ConstantInfo .anon)}
    {l : Ix.Kernel.Level} {e : Ix.Kernel.Expr .anon}
    (h : Ix.Kernel.Semantics.WrapT find? (.sort l) e) : ∃ v, e = .sort v := by
  cases h with
  | sort _ => exact ⟨_, rfl⟩

/-- A term related to one headed by a constant is headed by that constant. -/
theorem wrapT_getAppFn_const {find? : Ix.Kernel.Key .anon → Option (ConstantInfo .anon)}
    {g d : Ix.Kernel.Expr .anon} (h : Ix.Kernel.Semantics.WrapT find? g d) :
    ∀ {k : Ix.Kernel.Key .anon} {us : List Ix.Kernel.Level},
      g.getAppFn = .const k us → ∃ vs, d.getAppFn = .const k vs := by
  induction h with
  | @const n us₀ vs₀ _ =>
    intro k us hk
    have hk' : (Ix.Kernel.Expr.const n us₀ : Ix.Kernel.Expr .anon) = .const k us := hk
    injection hk' with h1 _
    subst h1
    exact ⟨vs₀, rfl⟩
  | app _ _ ihf _ => intro k us hk; exact ihf hk
  | _ => intro k us hk; simp only [Ix.Kernel.Expr.getAppFn, reduceCtorEq] at hk

/-- **The family key, from the declared/generated relation.** A reading `tyP` with `params`
literal `∀`s followed by a `∀` with a let-free domain, of the key shape of a reading `ty`,
an annotation `tyC` of `ty` related by `WrapRel` to a generated recursor type `recTy`
(`structRecTyR` at the family `T`, stored as an inductive type): the family key of `tyP` is
`T`. -/
theorem familyKey_of_wrapRel {rc : Ixon.Recursor}
    {find? : Ix.Kernel.Key .anon → Option (ConstantInfo .anon)}
    {tyP ty tyC recTy tty : Ix.Kernel.Expr .anon} {T : Ix.Kernel.Key .anon}
    {lps : List Ix.Kernel.LevelParam} {elim : Ix.Kernel.LevelParam} {large : Bool} {nIdx : Nat}
    {ctors : List (Ix.Kernel.Key .anon × Nat × Ix.Kernel.Expr .anon × List Nat)}
    {bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)} {D B : Ix.Kernel.Expr .anon}
    {m : Ix.Kernel.BinderMeta}
    (hshape : KeyShape tyP ty)
    (hstrip : tyP.stripPis rc.params.toNat = some (bs, .forallE D B m))
    (hD : Ix.Kernel.Semantics.letFree D = true)
    (hann : Annotates tyC ty)
    (hgen : Ix.Kernel.structRecTyR T lps elim large rc.params.toNat nIdx tty ctors = some recTy)
    (hwrap : Ix.Kernel.Semantics.WrapRel find? recTy tyC)
    (hT : ∃ cv caps, find? T = some (.indInfo cv caps)) :
    familyKey rc tyP = some T := by
  -- the generated side: the motive `∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ`, related to the annotation's
  have hW := hwrap.toWrapT (letFree_of_annotates hann)
  obtain ⟨_tbs, itele, motiveTy, _major, minors, -, hmot, -, -, hr⟩ :=
    Ix.Kernel.structRecTyR_unfold hgen
  obtain ⟨bs1, h1⟩ := Ix.Kernel.Semantics.stripPis_replacePisPw _ _ _ hr
  obtain ⟨bs1', body1', h1', hW1⟩ := Ix.Kernel.Semantics.WrapT.stripPis _ hW h1
  unfold Ix.Kernel.structMotiveTyI at hmot
  obtain ⟨bs2, h2⟩ := Ix.Kernel.Semantics.stripPis_replacePisPw _ _ _ hmot
  obtain ⟨a, dC, bC, m₂, rfl, hcs, hWd, -⟩ := wrapT_forallE_inv hW1
  have ha := Ix.Kernel.Semantics.ConsumeStar.eq_of_none hcs
    (consumeWrapper_of_isForall (isForall_of_stripPis _ h2))
  subst ha
  obtain ⟨bs2', body2', h2', hW2⟩ := Ix.Kernel.Semantics.WrapT.stripPis _ hWd h2
  obtain ⟨a2, famC, sC, m₃, rfl, hcs2, hWf, hWs⟩ := wrapT_forallE_inv hW2
  have ha2 := Ix.Kernel.Semantics.ConsumeStar.eq_of_none hcs2
    (Ix.Kernel.Semantics.consumeWrapper_structFamI hT)
  subst ha2
  obtain ⟨vs, hhead⟩ := wrapT_getAppFn_const hWf Ix.Kernel.Semantics.structFamI_getAppFn
  obtain ⟨v, rfl⟩ := wrapT_sort_inv hWs
  -- the annotation's motive and its last domain
  have hbdC : binderDom rc.params.toNat tyC = some dC := by
    unfold binderDom
    rw [h1'] <;> rfl
  have hlast : lastBinderDom dC = some famC :=
    lastBinderDom_of_stripPis (by rintro ⟨_, _, _, he⟩; cases he) _ h2'
  have hkC : headKey famC = some T := by
    unfold headKey
    rw [hhead] <;> rfl
  -- the reading under the recursor's level parameters
  obtain ⟨bsT, bodyT, hT1, hT2⟩ : ∃ bsT bodyT, ty.stripPis rc.params.toNat = some (bsT, bodyT) ∧
      KeyShape (.forallE D B m) bodyT := by
    rcases keyShape_stripPis rc.params.toNat hshape with
      ⟨hn, -⟩ | ⟨bsa, bodya, bsb, bodyb, ha', hb', hab⟩
    · rw [hstrip] at hn
      cases hn
    · rw [hstrip] at ha'
      simp only [Option.some.injEq, Prod.mk.injEq] at ha'
      obtain ⟨-, rfl⟩ := ha'
      exact ⟨bsb, bodyb, hb', hab⟩
  obtain ⟨D', B', m', rfl, hDD, -⟩ := KeyShape.forallE_inv hT2
  have hbdT : binderDom rc.params.toNat ty = some D' := by
    unfold binderDom
    rw [hT1] <;> rfl
  obtain ⟨d'', hbdC', hann''⟩ := binderDom_annotates hbdT hann
  have hdd : dC = d'' := Option.some.inj (hbdC.symm.trans hbdC')
  rw [← hdd] at hann''
  have hks : KeyShape dC D' := keyShape_of_annotates hann'' (letFree_keyShape hDD hD)
  obtain ⟨X', hX', hfX'⟩ := lastBinderDom_keyShape hks hlast
  obtain ⟨X, hX, hXX⟩ := lastBinderDom_keyShape hDD.symm hX'
  have hkX : headKey X = some T :=
    (headKey_eq_of_keyShape hXX).symm.trans ((headKey_eq_of_keyShape hfX').symm.trans hkC)
  have hbdP : binderDom rc.params.toNat tyP = some D := by
    unfold binderDom
    rw [hstrip] <;> rfl
  unfold familyKey
  rw [hbdP]
  show (lastBinderDom D).bind headKey = some T
  rw [hX]
  exact hkX

/-! ## Two readings of one expression under two level namings -/

section Reading

variable {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
  {u₁ u₂ : Array Ix.Kernel.Reader.CLevel}
  {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName .anon))}

private theorem ecx_keyAt_same {i : UInt64} {k₁ k₂ : Ix.Kernel.Reader.CName .anon}
    (h1 : (⟨cx, src, u₁, self⟩ : Ix.Kernel.Reader.ECx .anon).keyAt i = .ok k₁)
    (h2 : (⟨cx, src, u₂, self⟩ : Ix.Kernel.Reader.ECx .anon).keyAt i = .ok k₂) : k₁ = k₂ := by
  have e : (⟨cx, src, u₁, self⟩ : Ix.Kernel.Reader.ECx .anon).keyAt i =
      (⟨cx, src, u₂, self⟩ : Ix.Kernel.Reader.ECx .anon).keyAt i := rfl
  rw [e, h2] at h1
  exact (Except.ok.inj h1).symm

/-- **One expression converted under two universe tables**: the two conversions have one key
shape, when the sharing tables' converted entries do. -/
theorem convExpr_keyShape
    {tbl₁ tbl₂ : Array (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CExpr .anon))}
    (htbl : ∀ (i : Nat) (x y : Ix.Kernel.Reader.CExpr .anon), tbl₁[i]? = some (Except.ok x) →
      tbl₂[i]? = some (Except.ok y) → KeyShape x y) :
    ∀ (e : Ixon.Expr) (x y : Ix.Kernel.Reader.CExpr .anon),
      Ix.Kernel.Reader.convExpr (⟨cx, src, u₁, self⟩ : Ix.Kernel.Reader.ECx .anon) tbl₁ e =
        .ok x →
      Ix.Kernel.Reader.convExpr (⟨cx, src, u₂, self⟩ : Ix.Kernel.Reader.ECx .anon) tbl₂ e =
        .ok y →
      KeyShape x y := by
  intro e
  induction e with
  | sort i =>
    intro x y h1 h2
    simp only [Ix.Kernel.Reader.convExpr] at h1 h2
    obtain ⟨l1, -, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨l2, -, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    cases h1
    cases h2
    exact .sort _ _
  | var i =>
    intro x y h1 h2
    have hq : Ix.Kernel.Reader.convExpr (⟨cx, src, u₁, self⟩ : Ix.Kernel.Reader.ECx .anon) tbl₁
        (.var i) =
        Ix.Kernel.Reader.convExpr (⟨cx, src, u₂, self⟩ : Ix.Kernel.Reader.ECx .anon) tbl₂
          (.var i) := by
      (simp only [Ix.Kernel.Reader.convExpr]) <;> rfl
    rw [hq, h2] at h1
    cases h1
    exact KeyShape.refl _
  | ref i us =>
    intro x y h1 h2
    simp only [Ix.Kernel.Reader.convExpr] at h1 h2
    obtain ⟨k1, hk1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨l1, -, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨k2, hk2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    obtain ⟨l2, -, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    have hk : k1 = k2 := ecx_keyAt_same hk1 hk2
    cases h1
    cases h2
    subst hk
    exact .const _ _ _
  | recur i us =>
    intro x y h1 h2
    cases hs : self i.toNat with
    | none =>
      simp only [Ix.Kernel.Reader.convExpr, hs] at h1
      exact (throw_ok h1).elim
    | some mk =>
      simp only [Ix.Kernel.Reader.convExpr, hs] at h1 h2
      obtain ⟨k1, hk1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
      obtain ⟨l1, -, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
      obtain ⟨k2, hk2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
      obtain ⟨l2, -, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
      have hk : k1 = k2 := Except.ok.inj (hk1.symm.trans hk2)
      cases h1
      cases h2
      subst hk
      exact .const _ _ _
  | prj i field val ih =>
    intro x y h1 h2
    simp only [Ix.Kernel.Reader.convExpr] at h1 h2
    obtain ⟨k1, hk1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨v1, hv1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨k2, hk2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    obtain ⟨v2, hv2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    have hk : k1 = k2 := ecx_keyAt_same hk1 hk2
    cases h1
    cases h2
    subst hk
    exact .proj (ih v1 v2 hv1 hv2)
  | str i =>
    intro x y h1 h2
    have hq : Ix.Kernel.Reader.convExpr (⟨cx, src, u₁, self⟩ : Ix.Kernel.Reader.ECx .anon) tbl₁
        (.str i) =
        Ix.Kernel.Reader.convExpr (⟨cx, src, u₂, self⟩ : Ix.Kernel.Reader.ECx .anon) tbl₂
          (.str i) := by
      (simp only [Ix.Kernel.Reader.convExpr]) <;> rfl
    rw [hq, h2] at h1
    cases h1
    exact KeyShape.refl _
  | nat i =>
    intro x y h1 h2
    have hq : Ix.Kernel.Reader.convExpr (⟨cx, src, u₁, self⟩ : Ix.Kernel.Reader.ECx .anon) tbl₁
        (.nat i) =
        Ix.Kernel.Reader.convExpr (⟨cx, src, u₂, self⟩ : Ix.Kernel.Reader.ECx .anon) tbl₂
          (.nat i) := by
      (simp only [Ix.Kernel.Reader.convExpr]) <;> rfl
    rw [hq, h2] at h1
    cases h1
    exact KeyShape.refl _
  | app f a ihf iha =>
    intro x y h1 h2
    simp only [Ix.Kernel.Reader.convExpr] at h1 h2
    obtain ⟨f1, hf1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨a1, ha1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨f2, hf2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    obtain ⟨a2, ha2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    cases h1
    cases h2
    exact .app (ihf f1 f2 hf1 hf2) (iha a1 a2 ha1 ha2)
  | lam ty b iht ihb =>
    intro x y h1 h2
    simp only [Ix.Kernel.Reader.convExpr] at h1 h2
    obtain ⟨t1, ht1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨b1, hb1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨t2, ht2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    obtain ⟨b2, hb2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    cases h1
    cases h2
    exact .lam (iht t1 t2 ht1 ht2) (ihb b1 b2 hb1 hb2)
  | all ty b iht ihb =>
    intro x y h1 h2
    simp only [Ix.Kernel.Reader.convExpr] at h1 h2
    obtain ⟨t1, ht1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨b1, hb1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨t2, ht2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    obtain ⟨b2, hb2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    cases h1
    cases h2
    exact .forallE (iht t1 t2 ht1 ht2) (ihb b1 b2 hb1 hb2)
  | letE nonDep mode ty val b iht ihv ihb =>
    intro x y h1 h2
    simp only [Ix.Kernel.Reader.convExpr] at h1 h2
    obtain ⟨t1, ht1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨v1, hv1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨b1, hb1, h1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h1
    obtain ⟨t2, ht2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    obtain ⟨v2, hv2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    obtain ⟨b2, hb2, h2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h2
    cases h1
    cases h2
    exact .letE (iht t1 t2 ht1 ht2) (ihv v1 v2 hv1 hv2) (ihb b1 b2 hb1 hb2)
  | share i =>
    intro x y h1 h2
    cases ht1 : tbl₁[i.toNat]? with
    | none =>
      simp only [Ix.Kernel.Reader.convExpr, ht1] at h1
      exact (throw_ok h1).elim
    | some r1 =>
      cases ht2 : tbl₂[i.toNat]? with
      | none =>
        simp only [Ix.Kernel.Reader.convExpr, ht2] at h2
        exact (throw_ok h2).elim
      | some r2 =>
        simp only [Ix.Kernel.Reader.convExpr, ht1] at h1
        simp only [Ix.Kernel.Reader.convExpr, ht2] at h2
        subst h1
        subst h2
        exact htbl _ _ _ ht1 ht2

/-- The sharing tables, entry by entry. -/
theorem buildShareTblGo_keyShape :
    ∀ (es : List Ixon.Expr) (acc₁ acc₂ : Array (Ix.Kernel.Reader.ReadM
        (Ix.Kernel.Reader.CExpr .anon))),
      acc₁.size = acc₂.size →
      (∀ (i : Nat) (x y : Ix.Kernel.Reader.CExpr .anon), acc₁[i]? = some (Except.ok x) →
        acc₂[i]? = some (Except.ok y) → KeyShape x y) →
      ∀ (i : Nat) (x y : Ix.Kernel.Reader.CExpr .anon),
        (L1.buildShareTblGo (⟨cx, src, u₁, self⟩ : Ix.Kernel.Reader.ECx .anon) acc₁ es)[i]? =
          some (Except.ok x) →
        (L1.buildShareTblGo (⟨cx, src, u₂, self⟩ : Ix.Kernel.Reader.ECx .anon) acc₂ es)[i]? =
          some (Except.ok y) →
        KeyShape x y := by
  intro es
  induction es with
  | nil =>
    intro acc₁ acc₂ _ hacc
    exact hacc
  | cons e es ih =>
    intro acc₁ acc₂ hsz hacc
    simp only [L1.buildShareTblGo]
    apply ih
    · simp [hsz]
    · intro i x y h1 h2
      rw [Array.getElem?_push] at h1 h2
      by_cases hsize : i = acc₁.size
      · rw [ite_eq_left hsize] at h1
        rw [ite_eq_left (hsize.trans hsz)] at h2
        exact convExpr_keyShape hacc e x y (Option.some.inj h1) (Option.some.inj h2)
      · rw [ite_eq_right hsize] at h1
        rw [ite_eq_right (fun h => hsize (h.trans hsz.symm))] at h2
        exact hacc i x y h1 h2

end Reading

/-- **Two readings of one expression under two level namings have one key shape.** -/
theorem exprReader_keyShape {t : Ix.Kernel.RoleTable} {blob : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {p₁ p₂ : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))} {e : Ixon.Expr}
    {a b : Ix.Kernel.Expr .anon}
    (h1 : (exprReader t blob src p₁ self).read e = .ok a)
    (h2 : (exprReader t blob src p₂ self).read e = .ok b) : KeyShape a b := by
  unfold exprReader at h1 h2
  obtain ⟨hecx₁, htbl₁⟩ := L1.memberReader_mk'_eq (readCtx t blob) src p₁ self
  obtain ⟨hecx₂, htbl₂⟩ := L1.memberReader_mk'_eq (readCtx t blob) src p₂ self
  unfold Ix.Kernel.Reader.MemberReader.read at h1 h2
  rw [hecx₁, htbl₁] at h1
  rw [hecx₂, htbl₂] at h2
  exact convExpr_keyShape
    (buildShareTblGo_keyShape src.sharing.toList #[] #[] rfl (fun i x y hi => by simp at hi))
    e a b h1 h2

/-! ## The header's let check on the raw heap syntax -/

/-- `expr_has_let` at a cell that is none of `Let`, `App`, `Lam`, `Forall`, `Proj` keeps the heap. -/
theorem expr_has_let_leaf {h : Heap F} {addr : Nat} {c : String} {xs : List (SourceValue F)}
    (cell : h[addr]? = some (.construct Core.kexprEnum c xs))
    (hLet : c ≠ "Let") (hApp : c ≠ "App") (hLam : c ≠ "Lam") (hFor : c ≠ "Forall")
    (hProj : c ≠ "Proj") {r : SourceValue F} {h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelCheck::expr_has_let" [.ptr (.enum Core.kexprEnum) addr] h r h'
      calls) :
    h' = h := by
  match Obs.«KernelCheck::expr_has_let».obs ev with
  | .Let (ld12 := ld) .. => exact (hLet (Core.load_cell cell ld).1).elim
  | .App_n1 (ld12 := ld) .. => exact (hApp (Core.load_cell cell ld).1).elim
  | .App_other (ld12 := ld) .. => exact (hApp (Core.load_cell cell ld).1).elim
  | .Lam_n1 (ld12 := ld) .. => exact (hLam (Core.load_cell cell ld).1).elim
  | .Lam_other (ld12 := ld) .. => exact (hLam (Core.load_cell cell ld).1).elim
  | .Forall_n1 (ld12 := ld) .. => exact (hFor (Core.load_cell cell ld).1).elim
  | .Forall_other (ld12 := ld) .. => exact (hFor (Core.load_cell cell ld).1).elim
  | .Proj (ld12 := ld) .. => exact (hProj (Core.load_cell cell ld).1).elim
  | .other (he295 := hh) .. => exact hh

/-- **`expr_has_let` on the raw heap syntax**: it keeps the heap, and an answer other than `1`
means the raw term contains no `let`. -/
theorem expr_has_let_rawTm {κ : _root_.Address → Core.KKey} {d : Nat} {Γ : Nat → Core.KExpr}
    {h : Heap F} {k : Nat} {R E : Core.KExpr} {x : SourceValue F}
    (rep : Decl.RawTm κ d Γ h k R E x) :
    ∀ {r : SourceValue F} {h' : Heap F} {calls : List (Call F)},
      ObsFn Obs.W "KernelCheck::expr_has_let" [x] h r h' calls →
      h' = h ∧ (r ≠ .field 1 → Ix.Kernel.Semantics.letFree R = true) := by
  induction rep with
  | bvarLocal cell _ _ =>
    intro r h' calls ev
    exact ⟨expr_has_let_leaf cell (by decide) (by decide) (by decide) (by decide) (by decide) ev,
      fun _ => rfl⟩
  | bvarFree cell _ _ _ =>
    intro r h' calls ev
    exact ⟨expr_has_let_leaf cell (by decide) (by decide) (by decide) (by decide) (by decide) ev,
      fun _ => rfl⟩
  | sort cell _ _ =>
    intro r h' calls ev
    exact ⟨expr_has_let_leaf cell (by decide) (by decide) (by decide) (by decide) (by decide) ev,
      fun _ => rfl⟩
  | const cell _ _ _ =>
    intro r h' calls ev
    exact ⟨expr_has_let_leaf cell (by decide) (by decide) (by decide) (by decide) (by decide) ev,
      fun _ => rfl⟩
  | litNat cell _ _ =>
    intro r h' calls ev
    exact ⟨expr_has_let_leaf cell (by decide) (by decide) (by decide) (by decide) (by decide) ev,
      fun _ => rfl⟩
  | litStr cell _ _ =>
    intro r h' calls ev
    exact ⟨expr_has_let_leaf cell (by decide) (by decide) (by decide) (by decide) (by decide) ev,
      fun _ => rfl⟩
  | app cell rf ra ihf iha =>
    intro r h' calls ev
    match Obs.«KernelCheck::expr_has_let».obs ev with
    | .Let (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .App_n1 (ld12 := ld) (ev72 := evf) (he85 := hr) (he86 := hh) .. =>
      obtain ⟨-, hxs⟩ := Core.load_cell cell ld
      injection hxs with e1 hxs
      injection hxs with e2 hxs
      subst e1 e2
      exact ⟨hh.trans (ihf evf).1, fun hne => (hne hr).elim⟩
    | .App_other (ld12 := ld) (ev72 := evf) (hne88 := hnf) (ev97 := eva) .. =>
      obtain ⟨-, hxs⟩ := Core.load_cell cell ld
      injection hxs with e1 hxs
      injection hxs with e2 hxs
      subst e1 e2
      obtain ⟨hm, hf⟩ := ihf evf
      subst hm
      obtain ⟨hh, ha⟩ := iha eva
      refine ⟨hh, fun hne => ?_⟩
      simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true]
      exact ⟨hf hnf, ha hne⟩
    | .Lam_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Lam_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Forall_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Forall_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Proj (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .other (ld12 := ld) (hne107 := hne) .. =>
      rw [Core.loadValue_enum_cell cell] at ld
      exact (hne _ (by rfl) (Except.ok.inj ld).symm).elim
  | lam cell rt rb _ iht ihb =>
    intro r h' calls ev
    match Obs.«KernelCheck::expr_has_let».obs ev with
    | .Let (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .App_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .App_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Lam_n1 (ld12 := ld) (ev144 := evd) (he157 := hr) (he158 := hh) .. =>
      obtain ⟨-, hxs⟩ := Core.load_cell cell ld
      injection hxs with e1 hxs
      injection hxs with e2 hxs
      subst e1 e2
      exact ⟨hh.trans (iht evd).1, fun hne => (hne hr).elim⟩
    | .Lam_other (ld12 := ld) (ev144 := evd) (hne160 := hnd) (ev169 := evb) .. =>
      obtain ⟨-, hxs⟩ := Core.load_cell cell ld
      injection hxs with e1 hxs
      injection hxs with e2 hxs
      subst e1 e2
      obtain ⟨hm, hd⟩ := iht evd
      subst hm
      obtain ⟨hh, hb⟩ := ihb evb
      refine ⟨hh, fun hne => ?_⟩
      simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true]
      exact ⟨hd hnd, hb hne⟩
    | .Forall_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Forall_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Proj (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .other (ld12 := ld) (hne179 := hne) .. =>
      rw [Core.loadValue_enum_cell cell] at ld
      exact (hne _ (by rfl) (Except.ok.inj ld).symm).elim
  | forallE cell rt rb _ iht ihb =>
    intro r h' calls ev
    match Obs.«KernelCheck::expr_has_let».obs ev with
    | .Let (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .App_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .App_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Lam_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Lam_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Forall_n1 (ld12 := ld) (ev216 := evd) (he229 := hr) (he230 := hh) .. =>
      obtain ⟨-, hxs⟩ := Core.load_cell cell ld
      injection hxs with e1 hxs
      injection hxs with e2 hxs
      subst e1 e2
      exact ⟨hh.trans (iht evd).1, fun hne => (hne hr).elim⟩
    | .Forall_other (ld12 := ld) (ev216 := evd) (hne232 := hnd) (ev241 := evb) .. =>
      obtain ⟨-, hxs⟩ := Core.load_cell cell ld
      injection hxs with e1 hxs
      injection hxs with e2 hxs
      subst e1 e2
      obtain ⟨hm, hd⟩ := iht evd
      subst hm
      obtain ⟨hh, hb⟩ := ihb evb
      refine ⟨hh, fun hne => ?_⟩
      simp only [Ix.Kernel.Semantics.letFree, Bool.and_eq_true]
      exact ⟨hd hnd, hb hne⟩
    | .Proj (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .other (ld12 := ld) (hne251 := hne) .. =>
      rw [Core.loadValue_enum_cell cell] at ld
      exact (hne _ (by rfl) (Except.ok.inj ld).symm).elim
  | letE cell _ _ _ _ _ _ =>
    intro r h' calls ev
    match Obs.«KernelCheck::expr_has_let».obs ev with
    | .Let (he38 := hr) (he39 := hh) .. => exact ⟨hh, fun hne => (hne hr).elim⟩
    | .App_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .App_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Lam_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Lam_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Forall_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Forall_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Proj (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .other (ld12 := ld) (hne41 := hne) .. =>
      rw [Core.loadValue_enum_cell cell] at ld
      exact (hne _ (by rfl) (Except.ok.inj ld).symm).elim
  | proj cell _ re ihe =>
    intro r h' calls ev
    match Obs.«KernelCheck::expr_has_let».obs ev with
    | .Let (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .App_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .App_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Lam_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Lam_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Forall_n1 (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Forall_other (ld12 := ld) .. => exact (Core.load_cell_ne cell ld (by decide)).elim
    | .Proj (ld12 := ld) (ev280 := evx) .. =>
      obtain ⟨-, hxs⟩ := Core.load_cell cell ld
      injection hxs with e1 hxs
      injection hxs with e2 hxs
      injection hxs with e3 hxs
      subst e3
      obtain ⟨hh, hx⟩ := ihe evx
      refine ⟨hh, fun hne => ?_⟩
      simp only [Ix.Kernel.Semantics.letFree]
      exact hx hne
    | .other (ld12 := ld) (hne290 := hne) .. =>
      rw [Core.loadValue_enum_cell cell] at ld
      exact (hne _ (by rfl) (Except.ok.inj ld).symm).elim

/-- **`doms_have_let` at a nonzero count, answering `0`**: the raw term is a `∀` whose domain
contains no `let`. -/
theorem doms_have_let_rawTm_head {κ : _root_.Address → Core.KKey} {d : Nat}
    {Γ : Nat → Core.KExpr} {h : Heap F} {k : Nat} {R E : Core.KExpr} {x : SourceValue F}
    {n : F} {hit rest : SourceValue F} {h' : Heap F} {calls : List (Call F)}
    (rep : Decl.RawTm κ d Γ h k R E x) (hn : n ≠ 0)
    (ev : ObsFn Obs.W "KernelCheck::doms_have_let" [x, .field n] h (.tuple [hit, rest]) h'
      calls)
    (hhit : hit = .field 0) :
    ∃ (Rd Rb : Core.KExpr) (mR : Ix.Kernel.BinderMeta), R = .forallE Rd Rb mR ∧
      Ix.Kernel.Semantics.letFree Rd = true := by
  match Obs.«KernelCheck::doms_have_let».obs ev with
  | .n0 (hv14 := hv) .. => exact (hn (Value.field.inj hv)).elim
  | .other_n1 (he152 := hr) .. =>
    subst hhit
    injection hr with hr'
    injection hr' with h0 _
    exact absurd (Value.field.inj h0) zero_ne_one
  | .other_other (ld49 := ld) (ev83 := evRec) (ev135 := evLet) (hne168 := hne) .. =>
    obtain ⟨Rt, Rb, mR, T, B, ℓ, rfl, -, hRt, -, -⟩ := rep.forallE_of_load ld
    exact ⟨Rt, Rb, mR, rfl,
      (expr_has_let_rawTm (Decl.RawTm.mono evRec.heap_extends hRt) evLet).2 hne⟩

/-- **The header's let check on the raw heap syntax**: past `n_p` literal `∀`s of the raw term
comes a literal `∀` (the first motive) whose domain contains no `let`. -/
theorem rec_header_lets_rawTm {κ : _root_.Address → Core.KKey} {d : Nat}
    {Γ : Nat → Core.KExpr} {h : Heap F} {R E : Core.KExpr} {x_ty : SourceValue F}
    {np nmot nmin ni : F} {r : SourceValue F} {h' : Heap F} {calls : List (Call F)}
    (rep : Decl.RawTm κ d Γ h 0 R E x_ty) (hmot : nmot ≠ 0)
    (ev : ObsFn Obs.W "KernelCheck::check_rec_header_lets"
      [x_ty, .field np, .field nmot, .field nmin, .field ni] h r h' calls) :
    ∃ (rbs : List (Core.KExpr × Ix.Kernel.BinderMeta)) (Rd Rb : Core.KExpr)
      (mR : Ix.Kernel.BinderMeta),
      R.stripPis (ZMod.val np) = some (rbs, .forallE Rd Rb mR) ∧
      Ix.Kernel.Semantics.letFree Rd = true := by
  match Obs.«KernelCheck::check_rec_header_lets».obs ev with
  | .run (ev28 := evPeel) (ev14 := evDoms) (heq91 := hlet) .. =>
    obtain ⟨hh, rbs, rbody, ebody, hstrip, hbody⟩ :=
      peel_n_foralls_rawTm_val (ZMod.val np) rfl rep evPeel
    subst hh
    obtain ⟨Rd, Rb, mR, rfl, hlf⟩ := doms_have_let_rawTm_head hbody hmot evDoms hlet
    exact ⟨rbs, Rd, Rb, mR, hstrip, hlf⟩

/-- **The member check runs the header's let check** on the record's type and counts, at a
heap after the check's own. -/
theorem native_rec_member_lets
    {rc address levels type parameters indices motives minors rules k unsafeFlag block position
      result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_recursor_member"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], address]
      heap result final calls) :
    ∃ (letsHeap letsAfter : Heap F) (letsResult : SourceValue F) (letsCalls : List (Call F)),
      Heap.Extends heap letsHeap ∧
      ObsFn Obs.W "KernelCheck::check_rec_header_lets" [type, parameters, motives, minors, indices]
        letsHeap letsResult letsAfter letsCalls := by
  match Obs.«KernelCheck::check_recursor_member».obs observed with
  | .run (hv15 := input) (ev85 := scan) (ev142 := load) (ev233 := route) (ev278 := muts₁)
      (ev292 := muts₂) (ev314 := sameBlock) (heq357 := notAux) (ev382 := lenRun)
      (ev412 := peelRun) (ev477 := scopeRun) (sg671 := seg) (ev685 := kRun)
      (ev751 := shapeRun) (ev781 := letsRun) .. =>
    injection input with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    match seg with
    | .n1 (hv533 := isAux) .. =>
      exact absurd (Value.field.inj (isAux.symm.trans notAux)) one_ne_zero
    | .other (ev604 := spineRun) .. =>
      exact ⟨_, _, _, _,
        scan.heap_extends.trans (load.heap_extends.trans (route.heap_extends.trans
          (muts₁.heap_extends.trans (muts₂.heap_extends.trans (sameBlock.heap_extends.trans
            (lenRun.heap_extends.trans (peelRun.heap_extends.trans
              (scopeRun.heap_extends.trans (spineRun.heap_extends.trans
                (kRun.heap_extends.trans shapeRun.heap_extends)))))))))),
        letsRun⟩

/-! ## The motive's domain in the reading -/

/-- **The reading of a late recursor's type has a literal, let-free first motive.** At a
standalone recursor record `A` (`c.info = .recr rc`, one motive) checked on the native arm, the
reading `tyP` of `rc.typ` (positional level parameters) has `params` literal `∀`s and then a
literal `∀` whose domain contains no `let`.

The member check's `check_rec_header_lets` runs on the converted type in the heap, whose raw
syntax `R'` (`RawConvExpr.toRawTmCExactTrace`, at the type's binder plan) is the reading with
binder data replaced; the check finds the literal shape and the let-free domain in `R'`, hence
in the reading. -/
theorem rec_motive_letFree_reading {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    {lim : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hmot : rc.motives.toNat = 1) :
    ∃ tyP, (exprReader t (fun x => E₀.blobs.get? x) c id (soloSelf t A)).read rc.typ = .ok tyP ∧
      ∃ (bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)) (D B : Ix.Kernel.Expr .anon)
        (m : Ix.Kernel.BinderMeta),
        tyP.stripPis rc.params.toNat = some (bs, .forallE D B m) ∧
        Ix.Kernel.Semantics.letFree D = true := by
  have hgood : Core.Good ⟨E, default, t, lim⟩ calls := hst.good default lim
  have hbound : Bounded calls := hgood.2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, -, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk, hfr⟩ := hnat
  obtain ⟨a', ha'_ref, haA⟩ := ha_pre
  subst haA
  obtain ⟨rawBytes, c', hh, hba, hex, -, hres'⟩ :=
    L1.get_ci_block_trace_spec (hgood.sub hsub_ld).2 ha'_ref ev_ld
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hex
  subst c'
  unfold L1.GetCIBlockTraceResult at hres'
  rw [hinfo] at hres'
  obtain ⟨blobs, tree, v, hhp, built, hldv, htr⟩ := hres'
  rw [hld] at hldv
  obtain ⟨hlvls, hp56, hi56, hm56, hmi56, -, tyPtr, rulesPtr, blkPtr, bR, planT, -, -, hv,
    rty, -, hplanT, -⟩ := htr
  subst hv
  injection hldv with hv'
  injection hv' with _ _ hfields
  simp only [List.cons.injEq, and_true] at hfields
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfields
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨tyP, htyP⟩ := LoadedReads.exprReader_read_ok (t := t)
    (blob := fun x => E₀.blobs.get? x) ht (param := id) (self := soloSelf t (Core.ixAddr a'))
    rty (fun i x hx => by simp at hx) hblob
  obtain ⟨sB, sA, mH, sR, sCs, mCs, hextS, evS, hmemS, hextM, evM, hsubM⟩ :=
    check_const_rec_route ev_chk
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := soloSelf t (Core.ixAddr a'))
    hbound hlvls rty hextS htyP evS (hsub_chk _ hmemS)
  have hrd : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E₀.blobs.get? x)) c
      (Ix.Kernel.Reader.recParam (List.range rc.lvls.toNat))
      (soloSelf t (Core.ixAddr a'))).read rc.typ = .ok tyP := by
    rw [Assembly.recParam_range]
    exact htyP
  -- the raw heap syntax of the converted type, and the reading with binder data replaced
  obtain ⟨R', E₂, -, hraw, -, htrace⟩ := rty.toRawTmCExactTrace (κ := Core.keyOf t)
    (ps := List.range rc.lvls.toNat) (by simp) (by simpa using hlvls)
    (LoadedReads.readCtx_keyAt_inv ht _) (fun i x m k hx => by simp at hx) hblob hrd hlbb hdef
  have hshape : RawShape tyP R' := rawShape_of_rawTrace tyP (htrace planT hplanT [])
  have hraw0 := hraw 0 (fun _ => .sort .zero)
  simp only [Decl.posOf_range] at hraw0
  have hrawM := Decl.RawTm.mono hextM hraw0.toRawTm
  -- the header's let check on it
  obtain ⟨lH, lA, lR, lCs, hextL, evL⟩ := native_rec_member_lets evM
  have hrawL := Decl.RawTm.mono hextL hrawM
  have hmotF : ((rc.motives.toNat : Nat) : F) ≠ 0 := by
    rw [hmot, Nat.cast_one]
    exact one_ne_zero
  obtain ⟨rbs, Rd, Rb, mR, hstrip, hlf⟩ := rec_header_lets_rawTm hrawL hmotF evL
  have hval : ZMod.val ((rc.params.toNat : Nat) : F) = rc.params.toNat :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hstripN : R'.stripPis rc.params.toNat = some (rbs, .forallE Rd Rb mR) := by
    rw [← hval]
    exact hstrip
  -- back to the reading
  rcases rawShape_stripPis rc.params.toNat hshape with
    ⟨-, h2⟩ | ⟨bs, body, bs', body', h1, h2, h3⟩
  · rw [hstripN] at h2
    cases h2
  · rw [hstripN] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    cases h3 with
    | @forallE D _ B _ m _ hD _ =>
      exact ⟨tyP, htyP, bs, D, B, m, h1,
        letFree_keyShape (KeyShape.of_rawShape hD).symm hlf⟩

end IxVM.Refinement.Typing
