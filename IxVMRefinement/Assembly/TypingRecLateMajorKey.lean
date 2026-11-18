import IxVMRefinement.Assembly.TypingRecLateReads
import IxVMRefinement.L1.AnnotationCorrespondence
import IxVMRefinement.Decl.NativeRec
import IxVMRefinement.Obs.KernelCheck
/-! # The major key of the reading of a late recursor's type

`RecReads` asks for the key heading the major premise of the reading `tyP` of a recursor
record's type itself (`majorKey rc tyP`): `params + motives + minors + indices` literal `∀`s,
then a literal `∀` whose domain's application head is a constant. `RecMajorTie` gives it only for
an annotation of `tyP`, which reduces `let`s. The circuit's route supplies the literal shape: its
`rec_to_parent_addr` peels literal `Forall` cells of the record's converted type (`peel_n_foralls`
has no other arm), loads the next `Forall` and finds a literal `Const` at the head of its domain.

* `RawShape`, `rawShape_of_rawTrace`, `majorKey_eq_of_rawShape`: the raw heap syntax `R'` of the
  converted type is the reading with binder data replaced (`L1.applyRawBinderTrace`), so the two
  have one major key;
* `peel_n_foralls_rawTm_val`, `rec_to_parent_addr_rawTm_major`: the route's scan on the raw heap
  syntax, at any field count;
* `majorKey_of_annotates`: an annotation of a term with a major key has that major key;
* `rec_major_key_reading`: the reading of the record's type has the tied parent's key as its
  major key.
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

/-! ## Raw shape: the trace changes binder data only -/

/-- Two terms of one raw shape: the same constructor at every node, `let`s included, up to
binder data, `let` data and free-variable annotations. -/
inductive RawShape : Ix.Kernel.Expr .anon → Ix.Kernel.Expr .anon → Prop
  | bvar (i : Nat) : RawShape (.bvar i) (.bvar i)
  | fvar (i : Nat) (x y : Ix.Kernel.Expr .anon) : RawShape (.fvar i x) (.fvar i y)
  | sort (l : Ix.Kernel.Level) : RawShape (.sort l) (.sort l)
  | const (k : Ix.Kernel.Key .anon) (us : List Ix.Kernel.Level) :
      RawShape (.const k us) (.const k us)
  | lit (l : Ix.Kernel.Literal) : RawShape (.lit l) (.lit l)
  | app {f g a b : Ix.Kernel.Expr .anon} :
      RawShape f g → RawShape a b → RawShape (.app f a) (.app g b)
  | lam {t t' b b' : Ix.Kernel.Expr .anon} {m m' : Ix.Kernel.BinderMeta} :
      RawShape t t' → RawShape b b' → RawShape (.lam t b m) (.lam t' b' m')
  | forallE {t t' b b' : Ix.Kernel.Expr .anon} {m m' : Ix.Kernel.BinderMeta} :
      RawShape t t' → RawShape b b' → RawShape (.forallE t b m) (.forallE t' b' m')
  | letE {t t' v v' b b' : Ix.Kernel.Expr .anon} {l l' : Ix.Kernel.LetMeta} :
      RawShape t t' → RawShape v v' → RawShape b b' →
        RawShape (.letE t v b l) (.letE t' v' b' l')
  | proj {s : Ix.Kernel.Key .anon} {i : Nat} {e e' : Ix.Kernel.Expr .anon} :
      RawShape e e' → RawShape (.proj s i e) (.proj s i e')

/-- **The raw trace keeps the shape**: `L1.applyRawBinderTrace` rebuilds a term node for node,
keeping `let` cells, changing only binder data. -/
theorem rawShape_of_rawTrace {md : Core.KLevel → Ix.Kernel.BinderMeta} :
    ∀ (e : Core.KExpr) {ls : List Core.KLevel} {R : Core.KExpr} {ls' : List Core.KLevel},
      L1.applyRawBinderTrace md e ls = some (R, ls') → RawShape e R := by
  intro e
  induction e with
  | bvar i =>
    intro ls R ls' h
    simp only [L1.applyRawBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hR, -⟩ := h
    subst hR
    exact .bvar i
  | fvar i ty ih =>
    intro ls R ls' h
    simp only [L1.applyRawBinderTrace] at h
    rcases h1 : L1.applyRawBinderTrace md ty ls with _ | ⟨ty', l1⟩
    · simp [h1] at h
    · simp [h1] at h
      obtain ⟨hR, -⟩ := h
      subst hR
      exact .fvar i ty ty'
  | sort u =>
    intro ls R ls' h
    simp only [L1.applyRawBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hR, -⟩ := h
    subst hR
    exact .sort u
  | const k us =>
    intro ls R ls' h
    simp only [L1.applyRawBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hR, -⟩ := h
    subst hR
    exact .const k us
  | app f a ihf iha =>
    intro ls R ls' h
    simp only [L1.applyRawBinderTrace] at h
    rcases h1 : L1.applyRawBinderTrace md f ls with _ | ⟨f', l1⟩
    · simp [h1] at h
    · rcases h2 : L1.applyRawBinderTrace md a l1 with _ | ⟨a', l2⟩
      · simp [h1, h2] at h
      · simp [h1, h2] at h
        obtain ⟨hR, -⟩ := h
        subst hR
        exact .app (ihf h1) (iha h2)
  | lam ty b m iht ihb =>
    intro ls R ls' h
    cases ls with
    | nil => simp [L1.applyRawBinderTrace] at h
    | cons lv rest =>
      simp only [L1.applyRawBinderTrace] at h
      rcases h1 : L1.applyRawBinderTrace md ty rest with _ | ⟨ty', l1⟩
      · simp [h1] at h
      · rcases h2 : L1.applyRawBinderTrace md b l1 with _ | ⟨b', l2⟩
        · simp [h1, h2] at h
        · simp [h1, h2] at h
          obtain ⟨hR, -⟩ := h
          subst hR
          exact .lam (iht h1) (ihb h2)
  | forallE ty b m iht ihb =>
    intro ls R ls' h
    cases ls with
    | nil => simp [L1.applyRawBinderTrace] at h
    | cons lv rest =>
      simp only [L1.applyRawBinderTrace] at h
      rcases h1 : L1.applyRawBinderTrace md ty rest with _ | ⟨ty', l1⟩
      · simp [h1] at h
      · rcases h2 : L1.applyRawBinderTrace md b l1 with _ | ⟨b', l2⟩
        · simp [h1, h2] at h
        · simp [h1, h2] at h
          obtain ⟨hR, -⟩ := h
          subst hR
          exact .forallE (iht h1) (ihb h2)
  | letE ty v b l iht ihv ihb =>
    intro ls R ls' h
    simp only [L1.applyRawBinderTrace] at h
    rcases h1 : L1.applyRawBinderTrace md ty ls with _ | ⟨ty', l1⟩
    · simp [h1] at h
    · rcases h2 : L1.applyRawBinderTrace md v l1 with _ | ⟨v', l2⟩
      · simp [h1, h2] at h
      · rcases h3 : L1.applyRawBinderTrace md b l2 with _ | ⟨b', l3⟩
        · simp [h1, h2, h3] at h
        · simp [h1, h2, h3] at h
          obtain ⟨hR, -⟩ := h
          subst hR
          exact .letE (iht h1) (ihv h2) (ihb h3)
  | lit l =>
    intro ls R ls' h
    simp only [L1.applyRawBinderTrace, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hR, -⟩ := h
    subst hR
    exact .lit l
  | proj s i e ih =>
    intro ls R ls' h
    simp only [L1.applyRawBinderTrace] at h
    rcases h1 : L1.applyRawBinderTrace md e ls with _ | ⟨e', l1⟩
    · simp [h1] at h
    · simp [h1] at h
      obtain ⟨hR, -⟩ := h
      subst hR
      exact .proj (ih h1)

/-- The heads of two terms of one raw shape have one raw shape. -/
theorem RawShape.getAppFn {a b : Ix.Kernel.Expr .anon} (h : RawShape a b) :
    RawShape a.getAppFn b.getAppFn := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i x y => exact .fvar i x y
  | sort l => exact .sort l
  | const k us => exact .const k us
  | lit l => exact .lit l
  | app _ _ ihf _ => exact ihf
  | lam ht hb _ _ => exact .lam ht hb
  | forallE ht hb _ _ => exact .forallE ht hb
  | letE ht hv hb _ _ _ => exact .letE ht hv hb
  | proj he _ => exact .proj he

/-- Two terms of one raw shape have one head key. -/
theorem headKey_eq_of_rawShape {a b : Ix.Kernel.Expr .anon} (h : RawShape a b) :
    headKey a = headKey b := by
  unfold headKey
  have hg := h.getAppFn
  generalize a.getAppFn = x at hg ⊢
  generalize b.getAppFn = y at hg ⊢
  cases hg <;> rfl

/-- Two terms of one raw shape strip the same number of `∀`s, to bodies of one raw shape. -/
theorem rawShape_stripPis : ∀ (n : Nat) {a b : Ix.Kernel.Expr .anon}, RawShape a b →
    (a.stripPis n = none ∧ b.stripPis n = none) ∨
      ∃ bs body bs' body', a.stripPis n = some (bs, body) ∧ b.stripPis n = some (bs', body') ∧
        RawShape body body' := by
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

/-- Two terms of one raw shape have one major key. -/
theorem majorKey_eq_of_rawShape {rc : Ixon.Recursor} {a b : Ix.Kernel.Expr .anon}
    (h : RawShape a b) : majorKey rc a = majorKey rc b := by
  unfold majorKey binderDom
  rcases rawShape_stripPis (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat) h with ⟨h1, h2⟩ | ⟨bs, body, bs', body', h1, h2, h3⟩
  · rw [h1, h2]
  · rw [h1, h2]
    cases h3 with
    | forallE hd _ => exact headKey_eq_of_rawShape hd
    | bvar => rfl
    | fvar => rfl
    | sort => rfl
    | const => rfl
    | lit => rfl
    | app => rfl
    | lam => rfl
    | letE => rfl
    | proj => rfl

/-! ## An annotation keeps a major key -/

/-- An annotation of a term headed by a constant is headed by that constant. -/
theorem annotates_getAppFn_const {E T : Ix.Kernel.Expr .anon} (h : Annotates E T) :
    ∀ {k : Ix.Kernel.Key .anon} {us : List Ix.Kernel.Level},
      T.getAppFn = .const k us → E.getAppFn = .const k us := by
  induction h with
  | const => intro k us hk; exact hk
  | app _ _ ihf _ => intro k us hk; exact ihf hk
  | _ => intro k us hk; simp only [Ix.Kernel.Expr.getAppFn, reduceCtorEq] at hk

/-- An annotation of a term with a head key has that head key. -/
theorem headKey_annotates {E T : Ix.Kernel.Expr .anon} {k : Ix.Kernel.Key .anon}
    (h : Annotates E T) (hT : headKey T = some k) : headKey E = some k := by
  unfold headKey at hT ⊢
  cases hg : T.getAppFn with
  | const k₀ us₀ =>
    rw [hg] at hT
    rw [annotates_getAppFn_const h hg]
    exact hT
  | _ => rw [hg] at hT; simp at hT

/-- An annotation of a term beginning with `n` literal `∀`s begins with `n` literal `∀`s, its
body an annotation of the term's body. -/
theorem annotates_stripPis : ∀ (n : Nat) {E T : Ix.Kernel.Expr .anon}
    {bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)} {body : Ix.Kernel.Expr .anon},
    Annotates E T → T.stripPis n = some (bs, body) →
    ∃ bs' body', E.stripPis n = some (bs', body') ∧ Annotates body' body := by
  intro n
  induction n with
  | zero =>
    intro E T bs body h hs
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact ⟨[], E, rfl, h⟩
  | succ n ih =>
    intro E T bs body h hs
    cases h with
    | @forallE ty' ty b' b m' m hd hb =>
      simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs₀, body₀⟩, hs₀, heq⟩ := hs
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      obtain ⟨bs', body', h1, h2⟩ := ih hb hs₀
      exact ⟨(ty', m') :: bs', body', by simp [Ix.Kernel.Expr.stripPis, h1], h2⟩
    | _ => simp [Ix.Kernel.Expr.stripPis] at hs

/-- An annotation of a term with the domain of binder `n` has the domain of binder `n`, an
annotation of the term's. -/
theorem binderDom_annotates {n : Nat} {E T d : Ix.Kernel.Expr .anon}
    (hT : binderDom n T = some d) (h : Annotates E T) :
    ∃ d', binderDom n E = some d' ∧ Annotates d' d := by
  unfold binderDom at hT ⊢
  cases hs : T.stripPis n with
  | none => rw [hs] at hT; simp at hT
  | some p =>
    obtain ⟨bs, body⟩ := p
    rw [hs] at hT
    obtain ⟨bs', body', h1, h2⟩ := annotates_stripPis n h hs
    rw [h1]
    cases h2 with
    | @forallE dd' dd b' b m' m hd hb =>
      have hdd : dd = d := by simpa using hT
      subst hdd
      exact ⟨dd', rfl, hd⟩
    | _ => simp at hT

/-- **An annotation keeps a major key**: an annotation of a term with a major key has that
major key. -/
theorem majorKey_of_annotates {rc : Ixon.Recursor} {E T : Ix.Kernel.Expr .anon}
    {k : Ix.Kernel.Key .anon} (hT : majorKey rc T = some k) (h : Annotates E T) :
    majorKey rc E = some k := by
  unfold majorKey at hT ⊢
  cases hb : binderDom (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat) T with
  | none => rw [hb] at hT; simp at hT
  | some d =>
    rw [hb] at hT
    obtain ⟨d', hb', hd⟩ := binderDom_annotates hb h
    rw [hb']
    exact headKey_annotates hd hT

/-! ## The route's scan on the raw heap syntax -/

private theorem getAppFn_mkAppN_raw : ∀ (As : List Core.KExpr) (f : Core.KExpr),
    (Ix.Kernel.Expr.mkAppN f As).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: As, f => by
    show (Ix.Kernel.Expr.mkAppN (.app f a) As).getAppFn = f.getAppFn
    rw [getAppFn_mkAppN_raw As (.app f a)]
    rfl

/-- A raw heap term at a `Const` cell is a constant. -/
theorem rawTm_const_of_load {κ : _root_.Address → Core.KKey} {d : Nat}
    {Γ : Nat → Core.KExpr} {h : Heap F} {k : Nat} {R E : Core.KExpr}
    {pe ap lsp : SourceValue F}
    (rep : Decl.RawTm κ d Γ h k R E pe)
    (ld : loadValue h pe = .ok (.construct Core.kexprEnum "Const" [ap, lsp])) :
    ∃ a us, R = .const (κ (Core.ixAddr a)) us := by
  cases rep with
  | const cell ra rls eq => exact ⟨_, _, rfl⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | app cell _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact (Core.load_cell_ne cell ld (by decide)).elim

/-- **`peel_n_foralls` on the raw heap syntax, at any field count**: it peels `ZMod.val n`
literal `∀`s of the raw term. -/
theorem peel_n_foralls_rawTm_val {κ : _root_.Address → Core.KKey} {d : Nat}
    {Γ : Nat → Core.KExpr} :
    ∀ (m : Nat) {n : F} {x_e r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
      {k : Nat} {R E : Core.KExpr},
      ZMod.val n = m →
      Decl.RawTm κ d Γ h k R E x_e →
      ObsFn Obs.W "KernelCheck::peel_n_foralls" [x_e, .field n] h r h' calls →
      h' = h ∧ ∃ (rbs : List (Core.KExpr × Ix.Kernel.BinderMeta)) (rbody ebody : Core.KExpr),
        R.stripPis m = some (rbs, rbody) ∧ Decl.RawTm κ d Γ h (k + m) rbody ebody r := by
  intro m
  induction m with
  | zero =>
    intro n x_e r h h' calls k R E hval hR ev
    have hn0 : n = 0 := (ZMod.val_eq_zero n).mp hval
    subst hn0
    cases Obs.«KernelCheck::peel_n_foralls».obs ev with
    | n0 _ hr hh _ =>
      subst hr hh
      exact ⟨rfl, [], R, E, rfl, by simpa using hR⟩
    | other _ _ _ _ _ hne19 _ _ _ _ =>
      exact (hne19 rfl).elim
  | succ m ih =>
    intro n x_e r h h' calls k R E hval hR ev
    have hn0 : n ≠ 0 := by
      intro e; subst e; simp at hval
    cases Obs.«KernelCheck::peel_n_foralls».obs ev with
    | n0 hv14 _ _ _ =>
      exact (hn0 (Value.field.inj hv14)).elim
    | other w42 x_body w43 cs62 v66 _ ld34 op87 ev64 _ =>
      obtain ⟨Rt, Rb, mR, T0, B0, ℓ, rfl, rfl, -, hB0, -⟩ := hR.forallE_of_load ld34
      have hv66 : v66 = .field (n - 1) := by
        simp only [evalBinOp, Except.ok.injEq] at op87
        exact op87.symm
      subst hv66
      have hval' : ZMod.val (n - 1) = m := by
        have hs := IxVM.Refinement.Lib.val_sub_one hn0
        omega
      obtain ⟨rfl, rbs, rbody, ebody, hstrip, hB⟩ := ih hval' hB0 ev64
      refine ⟨rfl, (Rt, mR) :: rbs, rbody, ebody, ?_, ?_⟩
      · simp [Ix.Kernel.Expr.stripPis, hstrip]
      · rwa [show k + (m + 1) = k + 1 + m by omega]

/-- **The route's scan on the raw heap syntax**: `rec_to_parent_addr` at counts `p, m, mi, i`
finds `ZMod.val (p + m + mi + i)` literal `∀`s of the raw term, then a literal `∀` whose domain
is headed by a constant. -/
theorem rec_to_parent_addr_rawTm_major {κ : _root_.Address → Core.KKey} {d : Nat}
    {Γ : Nat → Core.KExpr} {R E : Core.KExpr} {x_ty r : SourceValue F} {p m mi i : F}
    {h h' : Heap F} {calls : List (Call F)}
    (hR : Decl.RawTm κ d Γ h 0 R E x_ty)
    (ev : ObsFn Obs.W "KernelCheck::rec_to_parent_addr"
      [x_ty, .field p, .field m, .field mi, .field i] h r h' calls) :
    ∃ (rbs : List (Core.KExpr × Ix.Kernel.BinderMeta)) (Rd Rb : Core.KExpr)
      (mR : Ix.Kernel.BinderMeta) (a : Bytes.Address) (us : List Core.KLevel),
      R.stripPis (ZMod.val (p + m + mi + i)) = some (rbs, .forallE Rd Rb mR) ∧
      Rd.getAppFn = .const (κ (Core.ixAddr a)) us := by
  obtain ⟨v1, x9, x17, v37, m38, cs48, x_major_ty, w86, w87, m104, cs115, x_head, w132, x_caddr,
    w162, op32, op24, op16, ev50, ld78, ev117, ld154, -, -, -⟩ :=
    Obs.«KernelCheck::rec_to_parent_addr».obs ev
  have hx17 : x17 = .field (p + m) := by
    simp only [evalBinOp, Except.ok.injEq] at op32; exact op32.symm
  subst hx17
  have hx9 : x9 = .field (p + m + mi) := by
    simp only [evalBinOp, Except.ok.injEq] at op24; exact op24.symm
  subst hx9
  have hv1 : v1 = .field (p + m + mi + i) := by
    simp only [evalBinOp, Except.ok.injEq] at op16; exact op16.symm
  subst hv1
  obtain ⟨hheap, rbs, rbody, ebody, hstrip, hbody⟩ :=
    peel_n_foralls_rawTm_val (ZMod.val (p + m + mi + i)) rfl hR ev50
  subst hheap
  obtain ⟨Rt, Rb, mR, T, B, ℓ, rfl, -, hRt, -, -⟩ := hbody.forallE_of_load ld78
  obtain ⟨hd, sp, Rh, Eh, Ras, Eas, htup, hRh, -, -, hRt_eq, -, -⟩ :=
    Decl.collect_spine_rawTm_spec hRt ev117
  injection htup with h1
  simp only [List.cons.injEq, and_true] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨a, us, rfl⟩ := rawTm_const_of_load hRh ld154
  refine ⟨rbs, Rt, Rb, mR, a, us, hstrip, ?_⟩
  rw [hRt_eq, getAppFn_mkAppN_raw] <;> rfl

/-! ## The major key of the reading -/

/-- **The reading of a late recursor's type has the tied parent's key as its major key.** At a
standalone recursor record `A` (`c.info = .recr rc`) checked on the native arm, with the parent
`P` tied to the record (`RecMajorTie`: an annotation of the reading `tyP` of `rc.typ` has
`keyOf t P` as its major key), the reading itself has `params + motives + minors + indices`
literal `∀`s and then a literal `∀` whose domain is headed by `keyOf t P`.

The route's scan (`rec_to_parent_addr`) runs on the converted type in the heap, whose raw syntax
`R'` (`RawConvExpr.toRawTmCExactTrace`, at the type's binder plan) is the reading with binder
data replaced; the scan finds the literal shape in `R'`, hence in the reading, and an
annotation of the reading has the reading's major key. -/
theorem rec_major_key_reading {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    {lim : Option Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) {P : _root_.Address}
    (htie : RecMajorTie t E₀ A c rc P) :
    ∃ tyP, (exprReader t (fun x => E₀.blobs.get? x) c id (soloSelf t A)).read rc.typ = .ok tyP ∧
      majorKey rc tyP = some (keyOf t P) := by
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
  obtain ⟨tyP, E'', htyP, hann', hmajP⟩ := htie
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
  -- the route's scan on it
  obtain ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls, routeCalls,
    nl, pty, np, ni, nc, pu, blk, idx, lenHeap, lenAfter, kHeap, kAfter, canonHeap, len, kTarget,
    lenCalls, kCalls, canonCalls, _canonResult, _canonFinal, evScan, -⟩ :=
    native_rec_member_full evM
  obtain ⟨rbs, Rd, Rb, mR, a, us, hstrip, hhead⟩ := rec_to_parent_addr_rawTm_major hrawM evScan
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F) +
      (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hstripN : R'.stripPis (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat) = some (rbs, .forallE Rd Rb mR) := by
    rw [← hsum]
    exact hstrip
  have hb : binderDom (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat) R' = some Rd := by
    unfold binderDom
    rw [hstripN] <;> rfl
  have hk : headKey Rd = some (Core.keyOf t (Core.ixAddr a)) := by
    unfold headKey
    rw [hhead] <;> rfl
  have hmajR : majorKey rc R' = some (Core.keyOf t (Core.ixAddr a)) := by
    unfold majorKey
    rw [hb] <;> exact hk
  have hmajT : majorKey rc tyP = some (Core.keyOf t (Core.ixAddr a)) :=
    (majorKey_eq_of_rawShape (rc := rc) hshape).trans hmajR
  have hmajE : majorKey rc E'' = some (Core.keyOf t (Core.ixAddr a)) :=
    majorKey_of_annotates hmajT hann'
  exact ⟨tyP, htyP, hmajT.trans (hmajE.symm.trans hmajP)⟩

end IxVM.Refinement.Typing
