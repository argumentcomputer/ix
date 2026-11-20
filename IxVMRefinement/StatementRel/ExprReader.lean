import IxVMRefinement.StatementRel.ReaderReads

/-! # A proof-returning reader of record expressions

`readCheck` converts an expression of a record as the kernel reader does
(`Ix.Kernel.Reader.MemberReader.read`) and returns the converted term with the proof that
the reader converts to it. It is evaluated on closed records: the reader's own lookups of
keys, universe levels and `recur` targets, which go through hash maps and BLAKE3 addresses,
are replaced by pure functions (`Oracle`) that are proved to agree with them.

Covered: `var`, `sort`, `ref`, `recur`, `app`, `lam`, `all`, `share`. Not covered (the check
returns nothing): `prj`, `str`, `nat`, `letE`.
-/

namespace IxVM.Refinement.ExprReader

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open Ix.CompileCert.Loop (except_bind_ok)

/-! ## Conversion, constructor by constructor -/

section Conv

variable {ecx : ECx .anon} {tbl : Array (ReadM (CExpr .anon))}

theorem level_ok {i : UInt64} {l : CLevel} (h : ecx.univs[i.toNat]? = some l) :
    ecx.level i = pure l := by
  simp only [ECx.level, h]

theorem keyAt_ok {i : UInt64} {a : _root_.Address} {k : CName .anon}
    (hr : ecx.src.refs[i.toNat]? = some a) (hk : ecx.cx.keyAt a = .ok k) :
    ecx.keyAt i = .ok k := by
  simp only [ECx.keyAt, hr]
  exact hk

theorem mapM_nil_ok {f : UInt64 → ReadM CLevel} :
    ([] : List UInt64).mapM f = (Except.ok [] : ReadM (List CLevel)) :=
  List.mapM_nil

theorem mapM_cons_ok {f : UInt64 → ReadM CLevel} {u : UInt64} {us : List UInt64} {l : CLevel}
    {ls : List CLevel} (h : f u = .ok l) (hs : us.mapM f = .ok ls) :
    (u :: us).mapM f = .ok (l :: ls) := by
  rw [List.mapM_cons]
  exact except_bind_ok.mpr ⟨l, h, except_bind_ok.mpr ⟨ls, hs, rfl⟩⟩

theorem conv_mkBvar {i : UInt64} :
    convExpr ecx tbl (.var i) = pure (Expr.mkBvar i.toNat) := by
  simp only [convExpr]

/-- A variable converts to the plain `bvar` node. The reader builds it through the pooled
constructor `Expr.mkBvar`, which is the same value; the plain node is what an evaluation in
the Lean kernel can afford (the pool is a table of 4096 nodes). -/
theorem conv_var {i : UInt64} :
    convExpr ecx tbl (.var i) = .ok (.bvar i.toNat) := by
  have h := conv_mkBvar (ecx := ecx) (tbl := tbl) (i := i)
  rw [Expr.mkBvar_eq] at h
  exact h

theorem conv_sort {i : UInt64} {l : CLevel} (hl : ecx.level i = .ok l) :
    convExpr ecx tbl (.sort i) = .ok (.sort l) := by
  simp only [convExpr]
  exact except_bind_ok.mpr ⟨l, hl, rfl⟩

theorem conv_ref {i : UInt64} {us : Array UInt64} {a : _root_.Address} {k : CName .anon}
    {ls : List CLevel} (hr : ecx.src.refs[i.toNat]? = some a) (hk : ecx.cx.keyAt a = .ok k)
    (hl : us.toList.mapM ecx.level = .ok ls) :
    convExpr ecx tbl (.ref i us) = .ok (.const k ls) := by
  simp only [convExpr]
  exact except_bind_ok.mpr ⟨k, keyAt_ok hr hk, except_bind_ok.mpr ⟨ls, hl, rfl⟩⟩

theorem conv_recur {i : UInt64} {us : Array UInt64} {k : CName .anon} {ls : List CLevel}
    (hs : ecx.self i.toNat = some (Except.ok k)) (hl : us.toList.mapM ecx.level = .ok ls) :
    convExpr ecx tbl (.recur i us) = .ok (.const k ls) := by
  simp only [convExpr, hs]
  exact except_bind_ok.mpr ⟨k, rfl, except_bind_ok.mpr ⟨ls, hl, rfl⟩⟩

theorem conv_app {f a : Ixon.Expr} {x y : CExpr .anon} (hf : convExpr ecx tbl f = .ok x)
    (ha : convExpr ecx tbl a = .ok y) : convExpr ecx tbl (.app f a) = .ok (.app x y) := by
  simp only [convExpr]
  exact except_bind_ok.mpr ⟨x, hf, except_bind_ok.mpr ⟨y, ha, rfl⟩⟩

theorem conv_lam {t b : Ixon.Expr} {x y : CExpr .anon} (ht : convExpr ecx tbl t = .ok x)
    (hb : convExpr ecx tbl b = .ok y) :
    convExpr ecx tbl (.lam t b) = .ok (.lam x y BinderMeta.leanNever) := by
  simp only [convExpr]
  exact except_bind_ok.mpr ⟨x, ht, except_bind_ok.mpr ⟨y, hb, rfl⟩⟩

theorem conv_all {t b : Ixon.Expr} {x y : CExpr .anon} (ht : convExpr ecx tbl t = .ok x)
    (hb : convExpr ecx tbl b = .ok y) :
    convExpr ecx tbl (.all t b) = .ok (.forallE x y BinderMeta.leanNever) := by
  simp only [convExpr]
  exact except_bind_ok.mpr ⟨x, ht, except_bind_ok.mpr ⟨y, hb, rfl⟩⟩

theorem conv_share {i : UInt64} {v : CExpr .anon} (h : tbl[i.toNat]? = some (Except.ok v)) :
    convExpr ecx tbl (.share i) = .ok v := by
  simp only [convExpr, h]

end Conv

/-! ## The pure lookups -/

/-- **Pure stand-ins for the reader's lookups** in the expression context `ecx`: the
universe table, the key of an address, and the key `recur k` resolves to, each proved to
agree with the reader's. -/
structure Oracle (ecx : ECx .anon) where
  univs : List CLevel
  key : _root_.Address → Key .anon
  selfKey : Nat → Option (Key .anon)
  huniv : ∀ (i : Nat) (l : CLevel), univs[i]? = some l → ecx.univs[i]? = some l
  hkey : ∀ a, ecx.cx.keyAt a = .ok (key a)
  hself : ∀ (k : Nat) (kk : Key .anon), selfKey k = some kk → ecx.self k = some (Except.ok kk)

section Check

variable {ecx : ECx .anon}

/-- One universe level, with the proof that the reader reads it. -/
def levelCheck (o : Oracle ecx) (u : UInt64) : Option { l : CLevel // ecx.level u = .ok l } :=
  match h : o.univs[u.toNat]? with
  | some l => some ⟨l, level_ok (o.huniv _ _ h)⟩
  | none => none

/-- A list of universe levels, with the proof that the reader reads them. -/
def levelsCheck (o : Oracle ecx) :
    (us : List UInt64) → Option { ls : List CLevel // us.mapM ecx.level = .ok ls }
  | [] => some ⟨[], mapM_nil_ok⟩
  | u :: us =>
    match levelCheck o u, levelsCheck o us with
    | some l, some ls => some ⟨l.1 :: ls.1, mapM_cons_ok l.2 ls.2⟩
    | _, _ => none

/-- **One expression, with the proof that the reader converts to it**, against a sharing
table `tbl` whose first entries are known to be the terms `vs`. -/
def convCheck (o : Oracle ecx) (tbl : Array (ReadM (CExpr .anon))) (vs : Array (CExpr .anon))
    (hsh : ∀ (i : Nat) (v : CExpr .anon), vs[i]? = some v → tbl[i]? = some (Except.ok v)) :
    (e : Ixon.Expr) → Option { v : CExpr .anon // convExpr ecx tbl e = .ok v }
  | .var i => some ⟨.bvar i.toNat, conv_var⟩
  | .sort i =>
    match levelCheck o i with
    | some l => some ⟨.sort l.1, conv_sort l.2⟩
    | none => none
  | .ref i us =>
    match h : ecx.src.refs[i.toNat]? with
    | some a =>
      match levelsCheck o us.toList with
      | some ls => some ⟨.const (o.key a) ls.1, conv_ref h (o.hkey a) ls.2⟩
      | none => none
    | none => none
  | .recur i us =>
    match h : o.selfKey i.toNat with
    | some k =>
      match levelsCheck o us.toList with
      | some ls => some ⟨.const k ls.1, conv_recur (o.hself _ _ h) ls.2⟩
      | none => none
    | none => none
  | .app f a =>
    match convCheck o tbl vs hsh f, convCheck o tbl vs hsh a with
    | some x, some y => some ⟨.app x.1 y.1, conv_app x.2 y.2⟩
    | _, _ => none
  | .lam t b =>
    match convCheck o tbl vs hsh t, convCheck o tbl vs hsh b with
    | some x, some y => some ⟨.lam x.1 y.1 BinderMeta.leanNever, conv_lam x.2 y.2⟩
    | _, _ => none
  | .all t b =>
    match convCheck o tbl vs hsh t, convCheck o tbl vs hsh b with
    | some x, some y => some ⟨.forallE x.1 y.1 BinderMeta.leanNever, conv_all x.2 y.2⟩
    | _, _ => none
  | .share i =>
    match h : vs[i.toNat]? with
    | some v => some ⟨v, conv_share (hsh _ _ h)⟩
    | none => none
  | _ => none

/-! ## The sharing table -/

/-- **The terms `vs` are the record's first shared subterms**, as the reader converts them:
entry `i` against the table of the entries before it. -/
def ShareOk (ecx : ECx .anon) (sharing : List Ixon.Expr) (vs : Array (CExpr .anon)) : Prop :=
  ∀ (i : Nat) (v : CExpr .anon), vs[i]? = some v →
    i < vs.size ∧ ∃ s, sharing[i]? = some s ∧
      convExpr ecx (Ingress.buildShareTbl ecx (sharing.take i)) s = .ok v

theorem shareOk_empty {sharing : List Ixon.Expr} : ShareOk ecx sharing #[] := by
  intro i v h
  rw [Array.getElem?_eq_none (Nat.zero_le i)] at h
  cases h

theorem shareOk_push {sharing : List Ixon.Expr} {vs : Array (CExpr .anon)} {s : Ixon.Expr}
    {v : CExpr .anon} (h : ShareOk ecx sharing vs) (hs : sharing[vs.size]? = some s)
    (hv : convExpr ecx (Ingress.buildShareTbl ecx (sharing.take vs.size)) s = .ok v) :
    ShareOk ecx sharing (vs.push v) := by
  intro i w hi
  rw [Array.getElem?_push] at hi
  by_cases hsize : i = vs.size
  · rw [ite_eq_left hsize] at hi
    have hw : v = w := Option.some.inj hi
    rw [hsize, ← hw]
    exact ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, s, hs, hv⟩
  · rw [ite_eq_right hsize] at hi
    obtain ⟨hlt, s', hs', hv'⟩ := h i w hi
    exact ⟨by rw [Array.size_push]; exact Nat.lt_succ_of_lt hlt, s', hs', hv'⟩

/-- The known entries, in the table of the entries read so far. -/
theorem shareOk_tbl {sharing : List Ixon.Expr} {vs : Array (CExpr .anon)}
    (h : ShareOk ecx sharing vs) : ∀ (i : Nat) (v : CExpr .anon), vs[i]? = some v →
      (Ingress.buildShareTbl ecx (sharing.take vs.size))[i]? = some (Except.ok v) := by
  intro i v hi
  obtain ⟨hlt, s, hs, hv⟩ := h i v hi
  rw [Ingress.buildShareTbl_take_getElem? ecx sharing hlt hs, hv]

/-- The known entries, in the record's whole table. -/
theorem shareOk_final {sharing : List Ixon.Expr} {vs : Array (CExpr .anon)}
    (h : ShareOk ecx sharing vs) : ∀ (i : Nat) (v : CExpr .anon), vs[i]? = some v →
      (Ingress.buildShareTbl ecx sharing)[i]? = some (Except.ok v) := by
  intro i v hi
  obtain ⟨-, s, hs, hv⟩ := h i v hi
  have hlen : i < sharing.length := (List.getElem?_eq_some_iff.mp hs).1
  have h2 := Ingress.buildShareTbl_take_getElem? ecx sharing hlen hs
  rw [List.take_length] at h2
  rw [h2, hv]

/-- The record's shared subterms, read in order, as far as `k` more entries. -/
def sharesGo (o : Oracle ecx) (sharing : List Ixon.Expr) :
    (k : Nat) → (vs : Array (CExpr .anon)) → ShareOk ecx sharing vs →
      Option { ws : Array (CExpr .anon) // ShareOk ecx sharing ws }
  | 0, vs, h => some ⟨vs, h⟩
  | k + 1, vs, h =>
    match hs : sharing[vs.size]? with
    | none => some ⟨vs, h⟩
    | some s =>
      match convCheck o (Ingress.buildShareTbl ecx (sharing.take vs.size)) vs (shareOk_tbl h) s with
      | some r => sharesGo o sharing k (vs.push r.1) (shareOk_push h hs r.2)
      | none => none

/-- **The record's shared subterms**, with the proof that they are what the reader's table
holds. -/
def sharesCheck (o : Oracle ecx) (sharing : List Ixon.Expr) :
    Option { ws : Array (CExpr .anon) // ShareOk ecx sharing ws } :=
  sharesGo o sharing sharing.length #[] shareOk_empty

end Check

/-! ## The member reader -/

theorem read_of_conv {cx : Ctx .anon} {src : Ixon.Constant} {param : Nat → LevelParam}
    {self : Nat → Option (ReadM (CName .anon))} {e : Ixon.Expr} {v : CExpr .anon}
    (h : convExpr (⟨cx, src, src.univs.map (convUniv param), self⟩ : ECx .anon)
      (Ingress.buildShareTbl ⟨cx, src, src.univs.map (convUniv param), self⟩ src.sharing.toList) e =
        .ok v) :
    (MemberReader.mk' cx src param self).read e = .ok v := by
  obtain ⟨hecx, htbl⟩ := Ingress.memberReader_mk'_eq cx src param self
  unfold MemberReader.read
  rw [hecx, htbl]
  exact h

/-- **One expression of a record, with the proof that the member reader reads it**, given
the record's shared subterms. -/
def readCheck {cx : Ctx .anon} {src : Ixon.Constant} {param : Nat → LevelParam}
    {self : Nat → Option (ReadM (CName .anon))}
    (o : Oracle (⟨cx, src, src.univs.map (convUniv param), self⟩ : ECx .anon))
    (sh : { ws : Array (CExpr .anon) //
      ShareOk ⟨cx, src, src.univs.map (convUniv param), self⟩ src.sharing.toList ws })
    (e : Ixon.Expr) :
    Option { v : CExpr .anon // (MemberReader.mk' cx src param self).read e = .ok v } :=
  match convCheck o (Ingress.buildShareTbl _ src.sharing.toList) sh.1 (shareOk_final sh.2) e with
  | some r => some ⟨r.1, read_of_conv r.2⟩
  | none => none

/-- The universe table of a record, as a list, is the reader's. -/
theorem univs_getElem? (us : Array Ixon.Univ) (f : Ixon.Univ → CLevel) (i : Nat) :
    (us.map f)[i]? = (us.toList.map f)[i]? := by
  simp

/-- **The lookups of the reading context of `Reads`**, for the record `src`: keys by
`keyOf t`, universe levels from the record's table, and `recur` by `selfKey`, which must
agree with `self`. -/
def oracleOf {t : RoleTable} (checked : t.check = .ok ())
    (blob : _root_.Address → Option ByteArray) (src : Ixon.Constant)
    (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName .anon)))
    (selfKey : Nat → Option (Key .anon))
    (hself : ∀ (k : Nat) (kk : Key .anon), selfKey k = some kk →
      self k = some (Except.ok kk)) :
    Oracle (⟨readCtx t blob, src, src.univs.map (convUniv param), self⟩ : ECx .anon) where
  univs := src.univs.toList.map (convUniv param)
  key := keyOf t
  selfKey := selfKey
  huniv := fun i _ h => (univs_getElem? src.univs (convUniv param) i).trans h
  hkey := fun a => readCtx_keyAt checked blob a
  hself := hself

end IxVM.Refinement.ExprReader
