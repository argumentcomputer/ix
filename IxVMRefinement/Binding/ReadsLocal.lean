import IxVMRefinement.Binding.ReadsAgree
import IxVMRefinement.StatementRel.ReaderReads
import IxVMRefinement.Core.Open

/-! # A reading over a store is a reading over a sub-store closed under used references

`Reads t E₀ x ci₀` reads the store at `x`, at the block of `x`'s record (a projection's
`MemberAt`, a constructor's block) and, for a recursor, at the inductive projection records whose
keys head its family and its major premise (`IndKeyAt`), with their blocks. Every key a reading
converts is the key of a reference the record uses or of its own block's members
(`read_keys`: `Ix.Kernel.Reader.convExpr` makes constants only from the reference table and
`recur`), and the role table's keys are injective. So over a sub-store `R` of `E₀` that is closed
under used references and owners (`UsedClosed`), holds `x`, and holds `E₀`'s blobs, the reading
is one over `R` (`reads_of_closed_sub`).
-/

namespace IxVM.Refinement.Binding

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open IxVM.Refinement.ReaderReads
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (throw_ok)

/-- **`k` is the key of a constant or of a projection in `e`.** -/
inductive KeyIn (k : Key .anon) : Expr .anon → Prop
  | const (us : List Level) : KeyIn k (.const k us)
  | proj (i : Nat) (e : Expr .anon) : KeyIn k (.proj k i e)
  | projBody {n : Key .anon} {i : Nat} {e : Expr .anon} : KeyIn k e → KeyIn k (.proj n i e)
  | fvarTy {idx : Nat} {ty : Expr .anon} : KeyIn k ty → KeyIn k (.fvar idx ty)
  | appFn {f a : Expr .anon} : KeyIn k f → KeyIn k (.app f a)
  | appArg {f a : Expr .anon} : KeyIn k a → KeyIn k (.app f a)
  | lamTy {t b : Expr .anon} {m : BinderMeta} : KeyIn k t → KeyIn k (.lam t b m)
  | lamBody {t b : Expr .anon} {m : BinderMeta} : KeyIn k b → KeyIn k (.lam t b m)
  | allTy {t b : Expr .anon} {m : BinderMeta} : KeyIn k t → KeyIn k (.forallE t b m)
  | allBody {t b : Expr .anon} {m : BinderMeta} : KeyIn k b → KeyIn k (.forallE t b m)
  | letTy {t v b : Expr .anon} {l : LetMeta} : KeyIn k t → KeyIn k (.letE t v b l)
  | letVal {t v b : Expr .anon} {l : LetMeta} : KeyIn k v → KeyIn k (.letE t v b l)
  | letBody {t v b : Expr .anon} {l : LetMeta} : KeyIn k b → KeyIn k (.letE t v b l)

/-! ## Every key a conversion makes comes from the reference table or `recur` -/

section Keys

variable {P : Key .anon → Prop} {ecx : ECx .anon} {S : Nat → Prop}

theorem convExpr_keys
    (hkey : ∀ (i : UInt64) (k : Key .anon), S i.toNat → ecx.keyAt i = .ok k → P k)
    (hself : ∀ (i : Nat) (k : Key .anon), ecx.self i = some (Except.ok k) → P k)
    {tbl : Array (ReadM (CExpr .anon))}
    (htbl : ∀ (i : Nat) (v : CExpr .anon), tbl[i]? = some (Except.ok v) →
      ∀ k, KeyIn k v → P k) :
    ∀ (e : Ixon.Expr), (∀ i ∈ exprRefIdxs e, S i) → ∀ (v : CExpr .anon),
      convExpr ecx tbl e = .ok v → ∀ k, KeyIn k v → P k := by
  intro e
  induction e with
  | sort i =>
    intro _ v h k hk
    simp only [convExpr] at h
    obtain ⟨l, -, h⟩ := except_bind_ok.mp h
    cases Except.ok.inj h
    cases hk
  | var i =>
    intro _ v h k hk
    simp only [convExpr, Expr.mkBvar] at h
    cases Except.ok.inj h
    cases hk
  | ref i us =>
    intro hS v h k hk
    simp only [convExpr] at h
    obtain ⟨k', hk', h⟩ := except_bind_ok.mp h
    obtain ⟨ls, -, h⟩ := except_bind_ok.mp h
    cases Except.ok.inj h
    cases hk
    exact hkey i _ (hS _ (by simp [exprRefIdxs])) hk'
  | recur i us =>
    intro _ v h k hk
    cases hs : ecx.self i.toNat with
    | none =>
      simp only [convExpr, hs] at h
      exact (throw_ok h).elim
    | some m =>
      cases m with
      | error er =>
        simp [convExpr, hs, bind, Except.bind] at h
      | ok k' =>
        simp only [convExpr, hs] at h
        obtain ⟨k'', hk'', h⟩ := except_bind_ok.mp h
        cases hk''
        obtain ⟨ls, -, h⟩ := except_bind_ok.mp h
        cases Except.ok.inj h
        cases hk
        exact hself _ _ hs
  | prj i field val ih =>
    intro hS v h k hk
    simp only [convExpr] at h
    obtain ⟨k', hk', h⟩ := except_bind_ok.mp h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    cases Except.ok.inj h
    cases hk with
    | proj => exact hkey i _ (hS _ (by simp [exprRefIdxs])) hk'
    | projBody hb =>
      exact ih (fun j hj => hS j (by simp [exprRefIdxs, hj])) x hx k hb
  | str i =>
    intro _ v h k hk
    simp only [convExpr] at h
    obtain ⟨bytes, -, h⟩ := except_bind_ok.mp h
    cases hs : String.fromUTF8? bytes with
    | none =>
      simp only [hs] at h
      exact (throw_ok h).elim
    | some s =>
      simp only [hs] at h
      cases Except.ok.inj h
      cases hk
  | nat i =>
    intro _ v h k hk
    simp only [convExpr] at h
    obtain ⟨n, -, h⟩ := except_bind_ok.mp h
    cases Except.ok.inj h
    cases hk
  | app f a ihf iha =>
    intro hS v h k hk
    simp only [convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    cases Except.ok.inj h
    cases hk with
    | appFn hb => exact ihf (fun j hj => hS j (by simp [exprRefIdxs, hj])) x hx k hb
    | appArg hb => exact iha (fun j hj => hS j (by simp [exprRefIdxs, hj])) y hy k hb
  | lam ty b iht ihb =>
    intro hS v h k hk
    simp only [convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    cases Except.ok.inj h
    cases hk with
    | lamTy hb => exact iht (fun j hj => hS j (by simp [exprRefIdxs, hj])) x hx k hb
    | lamBody hb => exact ihb (fun j hj => hS j (by simp [exprRefIdxs, hj])) y hy k hb
  | all ty b iht ihb =>
    intro hS v h k hk
    simp only [convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    cases Except.ok.inj h
    cases hk with
    | allTy hb => exact iht (fun j hj => hS j (by simp [exprRefIdxs, hj])) x hx k hb
    | allBody hb => exact ihb (fun j hj => hS j (by simp [exprRefIdxs, hj])) y hy k hb
  | letE nonDep mode ty val b iht ihv ihb =>
    intro hS v h k hk
    simp only [convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    obtain ⟨z, hz, h⟩ := except_bind_ok.mp h
    cases Except.ok.inj h
    cases hk with
    | letTy hb => exact iht (fun j hj => hS j (by simp [exprRefIdxs, hj])) x hx k hb
    | letVal hb => exact ihv (fun j hj => hS j (by simp [exprRefIdxs, hj])) y hy k hb
    | letBody hb => exact ihb (fun j hj => hS j (by simp [exprRefIdxs, hj])) z hz k hb
  | share i =>
    intro _ v h k hk
    cases ht : tbl[i.toNat]? with
    | none =>
      simp only [convExpr, ht] at h
      exact (throw_ok h).elim
    | some r =>
      simp only [convExpr, ht] at h
      subst h
      exact htbl _ _ ht k hk

theorem buildShareTblGo_keys
    (hkey : ∀ (i : UInt64) (k : Key .anon), S i.toNat → ecx.keyAt i = .ok k → P k)
    (hself : ∀ (i : Nat) (k : Key .anon), ecx.self i = some (Except.ok k) → P k) :
    ∀ (es : List Ixon.Expr) (acc : Array (ReadM (CExpr .anon))),
      (∀ e ∈ es, ∀ i ∈ exprRefIdxs e, S i) →
      (∀ (i : Nat) (v : CExpr .anon), acc[i]? = some (Except.ok v) → ∀ k, KeyIn k v → P k) →
      ∀ (i : Nat) (v : CExpr .anon), (L1.buildShareTblGo ecx acc es)[i]? = some (Except.ok v) →
        ∀ k, KeyIn k v → P k := by
  intro es
  induction es with
  | nil =>
    intro acc _ hacc
    exact hacc
  | cons e es ih =>
    intro acc hes hacc
    simp only [L1.buildShareTblGo]
    apply ih _ (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    intro i v hi
    rw [Array.getElem?_push] at hi
    by_cases hsize : i = acc.size
    · rw [if_pos hsize] at hi
      exact convExpr_keys hkey hself hacc e (hes e List.mem_cons_self) v (Option.some.inj hi)
    · rw [if_neg hsize] at hi
      exact hacc i v hi

end Keys

/-- **Every key a reading over a record converts is the key of a reference the record uses, or a
`recur` key**: over the reading context of `Reads`, the keys are the role table's (`keyOf`). -/
theorem read_keys {t : RoleTable} (checked : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant} {param : Nat → LevelParam}
    {self : Nat → Option (ReadM (CName .anon))} {P : Key .anon → Prop}
    (href : ∀ i ∈ usedRefIdxs src, ∀ a, src.refs[i]? = some a → P (keyOf t a))
    (hself : ∀ (i : Nat) (k : Key .anon), self i = some (Except.ok k) → P k)
    {e : Ixon.Expr} (he : ∀ i ∈ exprRefIdxs e, i ∈ usedRefIdxs src) {v : CExpr .anon}
    (h : (exprReader t blob src param self).read e = .ok v) : ∀ k, KeyIn k v → P k := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq (readCtx t blob) src param self
  unfold exprReader MemberReader.read at h
  rw [hecx, htbl] at h
  have hkey : ∀ (i : UInt64) (k : Key .anon), i.toNat ∈ usedRefIdxs src →
      (⟨readCtx t blob, src, src.univs.map (convUniv param), self⟩ : ECx .anon).keyAt i =
        .ok k → P k := by
    intro i k hi hk
    simp only [ECx.keyAt] at hk
    cases hr : src.refs[i.toNat]? with
    | none =>
      simp only [hr] at hk
      exact (throw_ok hk).elim
    | some a =>
      simp only [hr, readCtx_keyAt checked] at hk
      cases Except.ok.inj hk
      exact href _ hi a hr
  have hsh : ∀ e' ∈ src.sharing.toList, ∀ i ∈ exprRefIdxs e', i ∈ usedRefIdxs src := by
    intro e' he' i hi
    unfold usedRefIdxs
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨e', he', hi⟩)
  exact convExpr_keys (S := fun i => i ∈ usedRefIdxs src) hkey hself
    (buildShareTblGo_keys (S := fun i => i ∈ usedRefIdxs src) hkey hself src.sharing.toList #[]
      hsh (fun i v hi => by simp at hi)) e he v h

/-! ## The keys a recursor reading looks up are keys of its type -/

theorem keyIn_getAppFn {k : Key .anon} : ∀ {e : Expr .anon}, KeyIn k e.getAppFn → KeyIn k e
  | .app f _, h => .appFn (keyIn_getAppFn (e := f) h)
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .lam _ _ _, h
  | .forallE _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h => h

theorem keyIn_of_headKey {e : Expr .anon} {k : Key .anon} (h : headKey e = some k) :
    KeyIn k e := by
  unfold headKey at h
  apply keyIn_getAppFn
  revert h
  cases e.getAppFn with
  | const k' us =>
    intro h
    cases h
    exact .const us
  | _ => intro h; cases h

theorem keyIn_of_stripPis {k : Key .anon} :
    ∀ (n : Nat) {ty e : Expr .anon} {bs : List (Expr .anon × BinderMeta)},
      ty.stripPis n = some (bs, e) → KeyIn k e → KeyIn k ty
  | 0, ty, e, bs, h, hk => by
    simp only [Expr.stripPis] at h
    cases h
    exact hk
  | n + 1, ty, e, bs, h, hk => by
    cases ty with
    | forallE d b m =>
      simp only [Expr.stripPis] at h
      cases hb : b.stripPis n with
      | none => simp [hb] at h
      | some p =>
        obtain ⟨bs', e'⟩ := p
        simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact .allBody (keyIn_of_stripPis n hb hk)
    | _ => simp [Expr.stripPis] at h

theorem keyIn_of_binderDom {k : Key .anon} {n : Nat} {ty d : Expr .anon}
    (h : binderDom n ty = some d) (hk : KeyIn k d) : KeyIn k ty := by
  unfold binderDom at h
  cases hs : ty.stripPis n with
  | none => simp [hs] at h
  | some p =>
    obtain ⟨bs, e⟩ := p
    rw [hs] at h
    cases e with
    | forallE d' b m =>
      have hd : d' = d := by simpa using h
      subst hd
      exact keyIn_of_stripPis n hs (.allTy hk)
    | _ => simp at h

theorem keyIn_of_lastBinderDom {k : Key .anon} :
    ∀ {m d : Expr .anon}, lastBinderDom m = some d → KeyIn k d → KeyIn k m
  | .forallE d₀ (.forallE d₁ b₁ m₁) mt, d, h, hk =>
    .allBody (keyIn_of_lastBinderDom (m := .forallE d₁ b₁ m₁) (by simpa [lastBinderDom] using h) hk)
  | .forallE d₀ (.bvar _) mt, d, h, hk | .forallE d₀ (.fvar _ _) mt, d, h, hk
  | .forallE d₀ (.sort _) mt, d, h, hk | .forallE d₀ (.const _ _) mt, d, h, hk
  | .forallE d₀ (.app _ _) mt, d, h, hk | .forallE d₀ (.lam _ _ _) mt, d, h, hk
  | .forallE d₀ (.letE _ _ _ _) mt, d, h, hk | .forallE d₀ (.lit _) mt, d, h, hk
  | .forallE d₀ (.proj _ _ _) mt, d, h, hk => by
    simp only [lastBinderDom, Option.some.injEq] at h
    subst h
    exact .allTy hk
  | .bvar _, d, h, _ | .fvar _ _, d, h, _ | .sort _, d, h, _ | .const _ _, d, h, _
  | .app _ _, d, h, _ | .lam _ _ _, d, h, _ | .letE _ _ _ _, d, h, _ | .lit _, d, h, _
  | .proj _ _ _, d, h, _ => by simp [lastBinderDom] at h

theorem keyIn_of_familyKey {rc : Ixon.Recursor} {ty : Expr .anon} {k : Key .anon}
    (h : familyKey rc ty = some k) : KeyIn k ty := by
  unfold familyKey at h
  cases hb : binderDom rc.params.toNat ty with
  | none => simp [hb] at h
  | some motive =>
    rw [hb] at h
    cases hl : lastBinderDom motive with
    | none => simp [hl] at h
    | some d =>
      simp [hl] at h
      exact keyIn_of_binderDom hb (keyIn_of_lastBinderDom hl (keyIn_of_headKey h))

theorem keyIn_of_majorKey {rc : Ixon.Recursor} {ty : Expr .anon} {k : Key .anon}
    (h : majorKey rc ty = some k) : KeyIn k ty := by
  unfold majorKey at h
  cases hb : binderDom (rc.params.toNat + rc.motives.toNat + rc.minors.toNat +
      rc.indices.toNat) ty with
  | none => simp [hb] at h
  | some d =>
    simp [hb] at h
    exact keyIn_of_binderDom hb (keyIn_of_headKey h)

/-! ## Readings over a used-closed sub-store -/

private theorem forall₂_imp_local {α β : Type} {R S : α → β → Prop}
    (H : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h rest => .cons (H _ _ h) (forall₂_imp_local H rest)

section Sub

variable {t : RoleTable} {E₀ R : Ixon.Env}

private theorem held_eq (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c)
    {y : _root_.Address} (hy : (recordOf R y).isSome = true) :
    recordOf R y = recordOf E₀ y := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hy
  rw [hc, hsub y c hc]

private theorem memberAt_sub (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c)
    {a : _root_.Address} {c : Ixon.Constant} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {m : Ixon.MutConst}
    (hB : (recordOf R B).isSome = true) (h : MemberAt (recordOf E₀) a c B cb ms i m) :
    MemberAt (recordOf R) a c B cb ms i m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold MemberAt
  exact ⟨(held_eq hsub hB).trans h1, h2, h3, h4, h5, h6⟩

/-- An inductive key the reading finds, at a held address: the projection record and its block
are held. -/
private theorem indKeyAt_sub (hwf : t.wf = true)
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    {k : Key .anon} {B : _root_.Address} {i : Nat} {ind : Ixon.Inductive}
    (hk : ∃ y, (recordOf R y).isSome = true ∧ k = keyOf t y)
    (h : IndKeyAt t (recordOf E₀) k B i ind) : IndKeyAt t (recordOf R) k B i ind := by
  obtain ⟨a, c, p, cb, ms, hka, hca, hpi, hB, hi, hm⟩ := h
  obtain ⟨y, hy, hky⟩ := hk
  have hay : a = y := IxVM.Refinement.Core.keyOf_inj hwf (hka.symm.trans hky)
  subst hay
  have hcaR : recordOf R a = some c := (held_eq hsub hy).trans hca
  have hown : (recordOf R (Ix.Cert.ownerOf a c)).isSome = true := (hcl.1 a c hcaR).1
  have hownB : Ix.Cert.ownerOf a c = B := by
    simp only [Ix.Cert.ownerOf, hpi]
    exact hB.symm
  rw [hownB] at hown
  unfold IndKeyAt
  exact ⟨a, c, p, cb, ms, hka, hcaR, hpi, hB, hi, memberAt_sub hsub hown hm⟩

/-- A recursor reading over `E₀` from a held source record whose references and `recur` keys
are held is a reading over `R`. -/
private theorem recReads_sub (checked : t.check = .ok ()) (hwf : t.wf = true)
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    {blob blob' : _root_.Address → Option ByteArray}
    (hb : ∀ x b, blob x = some b → blob' x = some b) {src : Ixon.Constant}
    {self : Nat → Option (ReadM (CName .anon))} {name : Key .anon} {rc : Ixon.Recursor}
    {ci₀ : ConstantInfo .anon}
    (href : ∀ i ∈ usedRefIdxs src, ∀ a, src.refs[i]? = some a → (recordOf R a).isSome = true)
    (hself : ∀ (i : Nat) (k : Key .anon), self i = some (Except.ok k) →
      ∃ y, (recordOf R y).isSome = true ∧ k = keyOf t y)
    (hty : ∀ i ∈ exprRefIdxs rc.typ, i ∈ usedRefIdxs src)
    (h : RecReads t (recordOf E₀) blob src self name rc ci₀) :
    RecReads t (recordOf R) blob' src self name rc ci₀ := by
  obtain ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10⟩ := h
  have hkeys := read_keys checked (P := fun k => ∃ y, (recordOf R y).isSome = true ∧ k = keyOf t y)
    (fun j hj a ha => ⟨a, href j hj a ha, rfl⟩) hself hty h1
  unfold RecReads
  exact ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, exprReader_mono hb h1, h2,
    indKeyAt_sub hwf hsub hcl (hkeys kF (keyIn_of_familyKey h2)) h3, h4,
    indKeyAt_sub hwf hsub hcl (hkeys kM (keyIn_of_majorKey h4)) h5, h6, exprReader_mono hb h7,
    h8, forall₂_imp_local (fun _ _ hr => ruleReads_mono hb hr) h9, h10⟩

/-- **A reading over `E₀` at an address a used-closed sub-store holds is a reading over the
sub-store**, which holds `E₀`'s blobs: the reading looks up the record, its block, and for a
recursor the inductive projections whose keys head its family and major premise, which are keys
of references the record (or its block) uses (`read_keys`), with their blocks. -/
theorem reads_of_closed_sub (checked : t.check = .ok ()) (hwf : t.wf = true)
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → R.blobs.get? y = some b)
    {x : _root_.Address} (hx : (recordOf R x).isSome = true) {ci₀ : ConstantInfo .anon}
    (h : Reads t E₀ x ci₀) : Reads t R x ci₀ := by
  unfold Reads ReadsIn at h ⊢
  obtain ⟨c, hc, h⟩ := h
  have hcR : recordOf R x = some c := (held_eq hsub hx).trans hc
  have hrefs : ∀ i ∈ usedRefIdxs c, ∀ a, c.refs[i]? = some a → (recordOf R a).isSome = true :=
    fun i hi a ha => (hcl.1 x c hcR).2 i hi a ha
  have hownR : (recordOf R (Ix.Cert.ownerOf x c)).isSome = true := (hcl.1 x c hcR).1
  refine Exists.intro c (And.intro hcR ?_)
  generalize hci : c.info = info at h ⊢
  have hblock : ∀ B, Ix.Cert.ownerOf x c = B → (recordOf R B).isSome = true := by
    intro B hB
    rw [← hB]
    exact hownR
  cases info with
  | defn d =>
    obtain ⟨h1, h2⟩ := h
    exact And.intro h1 (defnReads_mono hblob h2)
  | axio ax =>
    obtain ⟨h1, h2⟩ := h
    exact And.intro h1 (axiomReads_mono hblob h2)
  | quot q => exact quotReads_mono hblob h
  | recr rc =>
    obtain ⟨h1, h2⟩ := h
    refine And.intro h1 (recReads_sub checked hwf hsub hcl hblob hrefs ?_ ?_ h2)
    · intro i k hs
      unfold soloSelf at hs
      split at hs
      · cases Except.ok.inj (Option.some.inj hs)
        exact ⟨x, hx, rfl⟩
      · cases hs
    · intro i hi
      simp [usedRefIdxs, hci, hi]
  | dPrj p =>
    have hB := hblock p.block (by simp only [Ix.Cert.ownerOf, hci])
    obtain ⟨cb, ms, d, hm, hr⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro d
      (And.intro (memberAt_sub hsub hB hm) (defnReads_mono hblob hr))))
  | iPrj p =>
    have hB := hblock p.block (by simp only [Ix.Cert.ownerOf, hci])
    obtain ⟨cb, ms, ind, hm, hr⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro ind
      (And.intro (memberAt_sub hsub hB hm) (indReads_mono hblob hr))))
  | cPrj p =>
    have hB := hblock p.block (by simp only [Ix.Cert.ownerOf, hci])
    obtain ⟨cb, ms, ind, ct, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro ind (Exists.intro ct
      (And.intro ((held_eq hsub hB).trans h1) (And.intro h2 (And.intro h3 (And.intro h4
        (And.intro h5 (And.intro h6 (And.intro h7 (And.intro h8
          (ctorReads_mono hblob h9))))))))))))
  | rPrj p =>
    have hB := hblock p.block (by simp only [Ix.Cert.ownerOf, hci])
    obtain ⟨cb, ms, rc, hm, hr⟩ := h
    have hmR := memberAt_sub hsub hB hm
    obtain ⟨hcbR, hcbi, hmi, -, -, -⟩ := hmR
    refine Exists.intro cb (Exists.intro ms (Exists.intro rc (And.intro
      (memberAt_sub hsub hB hm) (recReads_sub checked hwf hsub hcl hblob ?_ ?_ ?_ hr))))
    · exact fun i hi a ha => (hcl.1 p.block cb hcbR).2 i hi a ha
    · intro i k hs
      unfold blockSelf at hs
      cases hmi' : ms[i]? with
      | none =>
        rw [hmi'] at hs
        cases hs
      | some m =>
        rw [hmi'] at hs
        cases Except.ok.inj (Option.some.inj hs)
        exact ⟨_, Option.isSome_iff_exists.mpr
          ⟨_, (hcl.2 p.block cb ms hcbR hcbi i m hmi').1⟩, rfl⟩
    · intro i hi
      have hmem : Ixon.MutConst.recr rc ∈ ms.toList :=
        List.mem_of_getElem? (show ms.toList[p.idx.toNat]? = some (.recr rc) by
          rw [Array.getElem?_toList]; exact hmi)
      simp only [usedRefIdxs, hcbi]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.recr rc, hmem, by simp [mutRefIdxs, hi]⟩)
  | muts ms => exact False.elim h

end Sub

end IxVM.Refinement.Binding
