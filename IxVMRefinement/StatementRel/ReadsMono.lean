import IxVMRefinement.StatementRel.ReaderReads
import Ix.IxVM.Consistency.TableValid

/-! # `ReadsIn` is monotone in the store and the blobs

A reading over a store of records and blobs is a reading over any store that holds at least
those records and blobs (`ReadsIn.mono`). So a reading over the records a run loaded, or over
a witness's records, is a reading over "the run's records, and behind them the witness's"
(`ReadsIn.over_run`, `ReadsIn.over_witness`), the store `ConsistentReadOver` speaks of. The
second needs the two stores to agree where both hold a record or a blob; the collision
alternative of the statements is what gives that.
-/

namespace IxVM.Refinement.ReaderReads

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency

/-- The reading context's key of an address does not depend on its blobs. -/
theorem readCtx_keyAt_blob (t : RoleTable) (blob blob' : _root_.Address → Option ByteArray)
    (a : _root_.Address) : (readCtx t blob).keyAt a = (readCtx t blob').keyAt a := rfl

section Mono

variable {t : RoleTable} {store store' : Store}
  {blob blob' : _root_.Address → Option ByteArray}

/-- **Expression reading is monotone in the blobs.** -/
theorem exprReader_mono (hb : ∀ x b, blob x = some b → blob' x = some b)
    {src : Ixon.Constant} {param : Nat → LevelParam}
    {self : Nat → Option (ReadM (CName .anon))} {e : Ixon.Expr} {v : CExpr .anon}
    (h : (exprReader t blob src param self).read e = .ok v) :
    (exprReader t blob' src param self).read e = .ok v :=
  read_le (cx₁ := readCtx t blob) (cx₂ := readCtx t blob')
    (fun a _ hk => (readCtx_keyAt_blob t blob blob' a).symm.trans hk) hb
    (fun _ _ hs => hs) h

private theorem forall₂_imp {α β : Type} {R S : α → β → Prop} (H : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h rest => .cons (H _ _ h) (forall₂_imp H rest)

theorem memberAt_mono (hs : ∀ x c, store x = some c → store' x = some c)
    {a : _root_.Address} {c : Ixon.Constant} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {m : Ixon.MutConst}
    (h : MemberAt store a c B cb ms i m) : MemberAt store' a c B cb ms i m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold MemberAt
  exact ⟨hs _ _ h1, h2, h3, h4, h5, h6⟩

theorem indKeyAt_mono (hs : ∀ x c, store x = some c → store' x = some c)
    {k : Key .anon} {B : _root_.Address} {i : Nat} {ind : Ixon.Inductive}
    (h : IndKeyAt t store k B i ind) : IndKeyAt t store' k B i ind := by
  obtain ⟨a, c, p, cb, ms, h1, h2, h3, h4, h5, h6⟩ := h
  unfold IndKeyAt
  exact ⟨a, c, p, cb, ms, h1, hs _ _ h2, h3, h4, h5, memberAt_mono hs h6⟩

variable {src : Ixon.Constant} {param : Nat → LevelParam}
  {self : Nat → Option (ReadM (CName .anon))} {name : Key .anon}
  {ci₀ : ConstantInfo .anon}

theorem defnReads_mono (hb : ∀ x b, blob x = some b → blob' x = some b) {d : Ixon.Definition}
    (h : DefnReads (exprReader t blob src param self) name d ci₀) :
    DefnReads (exprReader t blob' src param self) name d ci₀ := by
  obtain ⟨ty, value, h1, h2, h3⟩ := h
  unfold DefnReads
  exact ⟨ty, value, exprReader_mono hb h1, exprReader_mono hb h2, h3⟩

theorem axiomReads_mono (hb : ∀ x b, blob x = some b → blob' x = some b) {ax : Ixon.Axiom}
    (h : AxiomReads (exprReader t blob src param self) name ax ci₀) :
    AxiomReads (exprReader t blob' src param self) name ax ci₀ := by
  obtain ⟨h0, ty, h1, h2⟩ := h
  unfold AxiomReads
  exact ⟨h0, ty, exprReader_mono hb h1, h2⟩

theorem quotReads_mono (hb : ∀ x b, blob x = some b → blob' x = some b) {q : Ixon.Quotient}
    (h : QuotReads (exprReader t blob src param self) name q ci₀) :
    QuotReads (exprReader t blob' src param self) name q ci₀ := by
  obtain ⟨ty, h1, h2, h3⟩ := h
  unfold QuotReads
  exact ⟨ty, exprReader_mono hb h1, h2, h3⟩

theorem indReads_mono (hb : ∀ x b, blob x = some b → blob' x = some b) {ind : Ixon.Inductive}
    (h : IndReads (exprReader t blob src param self) name ind ci₀) :
    IndReads (exprReader t blob' src param self) name ind ci₀ := by
  obtain ⟨ty, caps, h1, h2⟩ := h
  unfold IndReads
  exact ⟨ty, caps, exprReader_mono hb h1, h2⟩

theorem ctorReads_mono (hb : ∀ x b, blob x = some b → blob' x = some b)
    {ct : Ixon.Constructor}
    (h : CtorReads (exprReader t blob src param self) name ct ci₀) :
    CtorReads (exprReader t blob' src param self) name ct ci₀ := by
  obtain ⟨ty, h1, h2⟩ := h
  unfold CtorReads
  exact ⟨ty, exprReader_mono hb h1, h2⟩

theorem ruleReads_mono (hb : ∀ x b, blob x = some b → blob' x = some b)
    {Bm : _root_.Address} {im : Nat} {ru : Ixon.RecursorRule × Nat} {rl : RecRule .anon}
    (h : RuleReads t (exprReader t blob src param self) Bm im ru rl) :
    RuleReads t (exprReader t blob' src param self) Bm im ru rl := by
  obtain ⟨rhs, h1, h2⟩ := h
  unfold RuleReads
  exact ⟨rhs, exprReader_mono hb h1, h2⟩

theorem recReads_mono (hs : ∀ x c, store x = some c → store' x = some c)
    (hb : ∀ x b, blob x = some b → blob' x = some b) {rc : Ixon.Recursor}
    (h : RecReads t store blob src self name rc ci₀) :
    RecReads t store' blob' src self name rc ci₀ := by
  obtain ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10⟩ := h
  unfold RecReads
  exact ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, exprReader_mono hb h1, h2,
    indKeyAt_mono hs h3, h4, indKeyAt_mono hs h5, h6, exprReader_mono hb h7, h8,
    forall₂_imp (fun _ _ hr => ruleReads_mono hb hr) h9, h10⟩

end Mono

/-- **`ReadsIn` is monotone in the store and the blobs**: a reading over a store is a
reading over any store that holds at least its records and its blobs. -/
theorem _root_.IxVM.Consistency.ReadsIn.mono {t : RoleTable} {store store' : Store}
    {blob blob' : _root_.Address → Option ByteArray}
    (hs : ∀ x c, store x = some c → store' x = some c)
    (hb : ∀ x b, blob x = some b → blob' x = some b) {a : _root_.Address}
    {ci₀ : ConstantInfo .anon} (h : ReadsIn t store blob a ci₀) :
    ReadsIn t store' blob' a ci₀ := by
  obtain ⟨c, hc, h⟩ := h
  refine Exists.intro c (And.intro (hs _ _ hc) ?_)
  generalize c.info = info at h ⊢
  cases info with
  | defn d =>
    obtain ⟨h1, h2⟩ := h
    exact And.intro h1 (defnReads_mono hb h2)
  | axio ax =>
    obtain ⟨h1, h2⟩ := h
    exact And.intro h1 (axiomReads_mono hb h2)
  | quot q => exact quotReads_mono hb h
  | recr rc =>
    obtain ⟨h1, h2⟩ := h
    exact And.intro h1 (recReads_mono hs hb h2)
  | dPrj p =>
    obtain ⟨cb, ms, d, hm, hr⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro d
      (And.intro (memberAt_mono hs hm) (defnReads_mono hb hr))))
  | iPrj p =>
    obtain ⟨cb, ms, ind, hm, hr⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro ind
      (And.intro (memberAt_mono hs hm) (indReads_mono hb hr))))
  | cPrj p =>
    obtain ⟨cb, ms, ind, ct, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro ind (Exists.intro ct
      (And.intro (hs _ _ h1) (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h5
        (And.intro h6 (And.intro h7 (And.intro h8 (ctorReads_mono hb h9))))))))))))
  | rPrj p =>
    obtain ⟨cb, ms, rc, hm, hr⟩ := h
    exact Exists.intro cb (Exists.intro ms (Exists.intro rc
      (And.intro (memberAt_mono hs hm) (recReads_mono hs hb hr))))
  | muts ms => exact False.elim h

/-! ## Into the run's records with the witness's behind them -/

/-- A record the run's environment holds is the record of the joint store. -/
theorem storeOver_left {E₀ R : Ixon.Env} {x : _root_.Address} {c : Ixon.Constant}
    (h : recordOf E₀ x = some c) : storeOver E₀ R x = some c :=
  (congrArg (fun (o : Option Ixon.Constant) => o.orElse fun _ => recordOf R x) h).trans rfl

/-- A blob the run's environment holds is the blob of the joint store. -/
theorem blobOver_left {E₀ R : Ixon.Env} {x : _root_.Address} {b : ByteArray}
    (h : E₀.blobs.get? x = some b) : blobOver E₀ R x = some b :=
  (congrArg (fun (o : Option ByteArray) => o.orElse fun _ => R.blobs.get? x) h).trans rfl

/-- A record of the witness's store is the record of the joint store, when the run's
environment holds nothing else there. -/
theorem storeOver_right {E₀ R : Ixon.Env}
    (hagree : ∀ x c c', recordOf E₀ x = some c → recordOf R x = some c' → c = c')
    {x : _root_.Address} {c : Ixon.Constant} (h : recordOf R x = some c) :
    storeOver E₀ R x = some c := by
  cases h0 : recordOf E₀ x with
  | none =>
    exact (congrArg (fun (o : Option Ixon.Constant) => o.orElse fun _ => recordOf R x)
      h0).trans h
  | some c₀ =>
    have e : c₀ = c := hagree x c₀ c h0 h
    subst e
    exact storeOver_left h0

/-- A blob of the witness's store is the blob of the joint store, when the run's environment
holds nothing else there. -/
theorem blobOver_right {E₀ R : Ixon.Env}
    (hagree : ∀ x b b', E₀.blobs.get? x = some b → R.blobs.get? x = some b' → b = b')
    {x : _root_.Address} {b : ByteArray} (h : R.blobs.get? x = some b) :
    blobOver E₀ R x = some b := by
  cases h0 : E₀.blobs.get? x with
  | none =>
    exact (congrArg (fun (o : Option ByteArray) => o.orElse fun _ => R.blobs.get? x)
      h0).trans h
  | some b₀ =>
    have e : b₀ = b := hagree x b₀ b h0 h
    subst e
    exact blobOver_left h0

/-- **A reading over the run's records is a reading over the joint store.** -/
theorem _root_.IxVM.Consistency.ReadsIn.over_run {t : RoleTable} {E₀ R : Ixon.Env}
    {a : _root_.Address} {ci₀ : ConstantInfo .anon} (h : Reads t E₀ a ci₀) :
    ReadsIn t (storeOver E₀ R) (blobOver E₀ R) a ci₀ :=
  IxVM.Consistency.ReadsIn.mono (store := recordOf E₀) (blob := fun x => E₀.blobs.get? x)
    (fun _ _ hx => storeOver_left hx) (fun _ _ hx => blobOver_left hx) h

/-- **A reading over the witness's records is a reading over the joint store**, when the two
stores agree wherever both hold a record or a blob. -/
theorem _root_.IxVM.Consistency.ReadsIn.over_witness {t : RoleTable} {E₀ R : Ixon.Env}
    (hrec : ∀ x c c', recordOf E₀ x = some c → recordOf R x = some c' → c = c')
    (hblob : ∀ x b b', E₀.blobs.get? x = some b → R.blobs.get? x = some b' → b = b')
    {a : _root_.Address} {ci₀ : ConstantInfo .anon} (h : Reads t R a ci₀) :
    ReadsIn t (storeOver E₀ R) (blobOver E₀ R) a ci₀ :=
  IxVM.Consistency.ReadsIn.mono (store := recordOf R) (blob := fun x => R.blobs.get? x)
    (fun _ _ hx => storeOver_right hrec hx) (fun _ _ hx => blobOver_right hblob hx) h

end IxVM.Refinement.ReaderReads
