import IxVMRefinement.StatementRel.ReadsMono
import IxVMRefinement.StatementRel.StoreInhabit

/-! # A record without literals reads alike under any blobs

`Reads` threads a store's blobs through the expression reader (`exprReader`), which looks one up
only at a string or natural-number literal (`Ix.Kernel.Reader.convExpr`'s `str` and `nat` arms,
through `ECx.blobAt`). So an expression with no literal, read against a sharing table with no
literal, reads alike under any two blob functions (`exprReader_litFree`); and a reading over a
store none of whose records has a literal in its expressions or its sharing table is a reading
over the same store under any other blobs (`readsIn_litFree`).

The 24 committed basis rows have no literal (`basisRows_litFree`, decided over the rows), so a
reading over the basis store is one under any blobs (`basisStore_litFree`).
-/

namespace IxVM.Refinement.Binding

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open IxVM.Refinement.StoreInhabit (basisStore basisRows)
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (throw_ok)

/-! ## Expressions and records without literals -/

/-- **No literal in the expression**: no `str` and no `nat` node. -/
def exprLitFree : Ixon.Expr → Bool
  | .sort _ => true
  | .var _ => true
  | .ref _ _ => true
  | .recur _ _ => true
  | .prj _ _ v => exprLitFree v
  | .str _ => false
  | .nat _ => false
  | .app f a => exprLitFree f && exprLitFree a
  | .lam t b => exprLitFree t && exprLitFree b
  | .all t b => exprLitFree t && exprLitFree b
  | .letE _ _ t v b => exprLitFree t && exprLitFree v && exprLitFree b
  | .share _ => true

/-- **No literal in a member of a block**: in its type, a definition's value, an inductive's
constructors' types and a recursor's rules' right-hand sides. -/
def mutLitFree : Ixon.MutConst → Bool
  | .defn d => exprLitFree d.typ && exprLitFree d.value
  | .indc ind => exprLitFree ind.typ && ind.ctors.toList.all fun ct => exprLitFree ct.typ
  | .recr rc => exprLitFree rc.typ && rc.rules.toList.all fun ru => exprLitFree ru.rhs

/-- **No literal in what a record declares**: its own expressions, or its members'. A projection
record holds no expression. -/
def infoLitFree : Ixon.ConstantInfo → Bool
  | .defn d => exprLitFree d.typ && exprLitFree d.value
  | .recr rc => exprLitFree rc.typ && rc.rules.toList.all fun ru => exprLitFree ru.rhs
  | .axio ax => exprLitFree ax.typ
  | .quot q => exprLitFree q.typ
  | .cPrj _ => true
  | .rPrj _ => true
  | .iPrj _ => true
  | .dPrj _ => true
  | .muts ms => ms.toList.all mutLitFree

/-- **No literal in the record**: in its sharing table and in what it declares. -/
def recordLitFree (c : Ixon.Constant) : Bool :=
  c.sharing.toList.all exprLitFree && infoLitFree c.info

/-! ## Expression conversion without literals, in a context with the same keys -/

section Transfer

variable {cx₁ cx₂ : Ctx .anon} {src : Ixon.Constant} {univs : Array CLevel}
  {self₁ self₂ : Nat → Option (ReadM (CName .anon))}

private theorem ecx_keyAt_le' (hkey : ∀ a k, cx₁.keyAt a = .ok k → cx₂.keyAt a = .ok k)
    {i : UInt64} {k : CName .anon}
    (h : (⟨cx₁, src, univs, self₁⟩ : ECx .anon).keyAt i = .ok k) :
    (⟨cx₂, src, univs, self₂⟩ : ECx .anon).keyAt i = .ok k := by
  simp only [ECx.keyAt] at h ⊢
  cases hr : src.refs[i.toNat]? with
  | none =>
    simp only [hr] at h
    exact (throw_ok h).elim
  | some a =>
    simp only [hr] at h ⊢
    exact hkey a k h

/-- **An expression without literals, in a context that answers at least the keys the first
answers**: its conversion does not look up a blob. -/
theorem convExpr_litFree (hkey : ∀ a k, cx₁.keyAt a = .ok k → cx₂.keyAt a = .ok k)
    (hself : ∀ (i : Nat) (k : CName .anon), self₁ i = some (Except.ok k) →
      self₂ i = some (Except.ok k))
    {tbl₁ tbl₂ : Array (ReadM (CExpr .anon))}
    (htbl : ∀ (i : Nat) (v : CExpr .anon), tbl₁[i]? = some (Except.ok v) →
      tbl₂[i]? = some (Except.ok v)) :
    ∀ (e : Ixon.Expr), exprLitFree e = true → ∀ (v : CExpr .anon),
      convExpr (⟨cx₁, src, univs, self₁⟩ : ECx .anon) tbl₁ e = .ok v →
      convExpr (⟨cx₂, src, univs, self₂⟩ : ECx .anon) tbl₂ e = .ok v := by
  intro e
  induction e with
  | sort i =>
    intro _ v h
    simp only [convExpr] at h ⊢
    exact h
  | var i =>
    intro _ v h
    simp only [convExpr] at h ⊢
    exact h
  | ref i us =>
    intro _ v h
    simp only [convExpr] at h ⊢
    obtain ⟨k, hk, hrest⟩ := except_bind_ok.mp h
    rw [ecx_keyAt_le' (self₂ := self₂) hkey hk]
    exact hrest
  | recur i us =>
    intro _ v h
    cases hs : self₁ i.toNat with
    | none =>
      simp only [convExpr, hs] at h
      exact (throw_ok h).elim
    | some m =>
      cases m with
      | error er =>
        simp [convExpr, hs, bind, Except.bind] at h
      | ok k =>
        simp only [convExpr, hs] at h
        simp only [convExpr, hself _ _ hs]
        exact h
  | prj i field val ih =>
    intro hl v h
    simp only [exprLitFree] at hl
    simp only [convExpr] at h ⊢
    obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    rw [ecx_keyAt_le' (self₂ := self₂) hkey hk, ih hl x hx]
    exact h
  | str i =>
    intro hl
    simp [exprLitFree] at hl
  | nat i =>
    intro hl
    simp [exprLitFree] at hl
  | app f a ihf iha =>
    intro hl v h
    simp only [exprLitFree, Bool.and_eq_true] at hl
    simp only [convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    rw [ihf hl.1 x hx, iha hl.2 y hy]
    exact h
  | lam ty b iht ihb =>
    intro hl v h
    simp only [exprLitFree, Bool.and_eq_true] at hl
    simp only [convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    rw [iht hl.1 x hx, ihb hl.2 y hy]
    exact h
  | all ty b iht ihb =>
    intro hl v h
    simp only [exprLitFree, Bool.and_eq_true] at hl
    simp only [convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    rw [iht hl.1 x hx, ihb hl.2 y hy]
    exact h
  | letE nonDep mode ty val b iht ihv ihb =>
    intro hl v h
    simp only [exprLitFree, Bool.and_eq_true] at hl
    obtain ⟨⟨hlt, hlv⟩, hlb⟩ := hl
    simp only [convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    obtain ⟨z, hz, h⟩ := except_bind_ok.mp h
    rw [iht hlt x hx, ihv hlv y hy, ihb hlb z hz]
    exact h
  | share i =>
    intro _ v h
    cases ht : tbl₁[i.toNat]? with
    | none =>
      simp only [convExpr, ht] at h
      exact (throw_ok h).elim
    | some r =>
      simp only [convExpr, ht] at h
      subst h
      simp only [convExpr, htbl _ _ ht]

/-- The sharing table without literals, entry by entry. -/
theorem buildShareTblGo_litFree (hkey : ∀ a k, cx₁.keyAt a = .ok k → cx₂.keyAt a = .ok k)
    (hself : ∀ (i : Nat) (k : CName .anon), self₁ i = some (Except.ok k) →
      self₂ i = some (Except.ok k)) :
    ∀ (es : List Ixon.Expr), (∀ e ∈ es, exprLitFree e = true) →
      ∀ (acc₁ acc₂ : Array (ReadM (CExpr .anon))),
      acc₁.size = acc₂.size →
      (∀ (i : Nat) (v : CExpr .anon), acc₁[i]? = some (Except.ok v) →
        acc₂[i]? = some (Except.ok v)) →
      ∀ (i : Nat) (v : CExpr .anon),
        (Ingress.buildShareTblGo (⟨cx₁, src, univs, self₁⟩ : ECx .anon) acc₁ es)[i]? =
          some (Except.ok v) →
        (Ingress.buildShareTblGo (⟨cx₂, src, univs, self₂⟩ : ECx .anon) acc₂ es)[i]? =
          some (Except.ok v) := by
  intro es
  induction es with
  | nil =>
    intro _ acc₁ acc₂ _ hacc
    exact hacc
  | cons e es ih =>
    intro hes acc₁ acc₂ hsz hacc
    simp only [Ingress.buildShareTblGo]
    apply ih (fun x hx => hes x (List.mem_cons_of_mem _ hx))
    · simp [hsz]
    · intro i v hi
      rw [Array.getElem?_push] at hi ⊢
      by_cases hsize : i = acc₁.size
      · rw [ite_eq_left hsize] at hi
        rw [ite_eq_left (hsize.trans hsz),
          convExpr_litFree hkey hself hacc e (hes e List.mem_cons_self) v (Option.some.inj hi)]
      · rw [ite_eq_right hsize] at hi
        rw [ite_eq_right (fun h => hsize (h.trans hsz.symm))]
        exact hacc i v hi

end Transfer

/-- **A member reader without literals reads alike in a context with the same keys**, whatever
its blobs. -/
theorem read_litFree {cx₁ cx₂ : Ctx .anon} {src : Ixon.Constant}
    {self₁ self₂ : Nat → Option (ReadM (CName .anon))}
    (hkey : ∀ a k, cx₁.keyAt a = .ok k → cx₂.keyAt a = .ok k)
    (hself : ∀ (i : Nat) (k : CName .anon), self₁ i = some (Except.ok k) →
      self₂ i = some (Except.ok k))
    (hsh : src.sharing.toList.all exprLitFree = true)
    {param : Nat → LevelParam} {e : Ixon.Expr} (he : exprLitFree e = true) {v : CExpr .anon}
    (h : (MemberReader.mk' cx₁ src param self₁).read e = .ok v) :
    (MemberReader.mk' cx₂ src param self₂).read e = .ok v := by
  obtain ⟨hecx₁, htbl₁⟩ := Ingress.memberReader_mk'_eq cx₁ src param self₁
  obtain ⟨hecx₂, htbl₂⟩ := Ingress.memberReader_mk'_eq cx₂ src param self₂
  unfold MemberReader.read at h ⊢
  rw [hecx₁, htbl₁] at h
  rw [hecx₂, htbl₂]
  exact convExpr_litFree hkey hself
    (buildShareTblGo_litFree hkey hself src.sharing.toList (List.all_eq_true.mp hsh) #[] #[] rfl
      (fun i v hi => by simp at hi)) e he v h

/-- **The expression reader of `Reads` without literals reads alike under any blobs.** -/
theorem exprReader_litFree {t : RoleTable} {blob blob' : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {param : Nat → LevelParam} {self : Nat → Option (ReadM (CName .anon))}
    (hsh : src.sharing.toList.all exprLitFree = true) {e : Ixon.Expr}
    (he : exprLitFree e = true) {v : CExpr .anon}
    (h : (exprReader t blob src param self).read e = .ok v) :
    (exprReader t blob' src param self).read e = .ok v :=
  read_litFree (cx₁ := readCtx t blob) (cx₂ := readCtx t blob')
    (fun a _ hk => (ReaderReads.readCtx_keyAt_blob t blob blob' a).symm.trans hk)
    (fun _ _ hs => hs) hsh he h

/-! ## What a record without literals declares, under any blobs -/

private theorem forall₂_imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, (∀ a ∈ l₁, ∀ b, R a b → S a b) →
      List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, _, .nil => .nil
  | _, _, H, .cons h rest =>
    .cons (H _ List.mem_cons_self _ h)
      (forall₂_imp_mem (fun a ha b hr => H a (List.mem_cons_of_mem _ ha) b hr) rest)

section Reads

variable {t : RoleTable} {store : Store} {blob blob' : _root_.Address → Option ByteArray}
  {src : Ixon.Constant} {param : Nat → LevelParam} {self : Nat → Option (ReadM (CName .anon))}
  {name : Key .anon} {ci₀ : ConstantInfo .anon}

theorem defnReads_litFree (hsh : src.sharing.toList.all exprLitFree = true)
    {d : Ixon.Definition} (hty : exprLitFree d.typ = true) (hval : exprLitFree d.value = true)
    (h : DefnReads (exprReader t blob src param self) name d ci₀) :
    DefnReads (exprReader t blob' src param self) name d ci₀ := by
  obtain ⟨ty, value, h1, h2, h3⟩ := h
  unfold DefnReads
  exact ⟨ty, value, exprReader_litFree hsh hty h1, exprReader_litFree hsh hval h2, h3⟩

theorem axiomReads_litFree (hsh : src.sharing.toList.all exprLitFree = true) {ax : Ixon.Axiom}
    (hty : exprLitFree ax.typ = true)
    (h : AxiomReads (exprReader t blob src param self) name ax ci₀) :
    AxiomReads (exprReader t blob' src param self) name ax ci₀ := by
  obtain ⟨h0, ty, h1, h2⟩ := h
  unfold AxiomReads
  exact ⟨h0, ty, exprReader_litFree hsh hty h1, h2⟩

theorem quotReads_litFree (hsh : src.sharing.toList.all exprLitFree = true) {q : Ixon.Quotient}
    (hty : exprLitFree q.typ = true)
    (h : QuotReads (exprReader t blob src param self) name q ci₀) :
    QuotReads (exprReader t blob' src param self) name q ci₀ := by
  obtain ⟨ty, h1, h2, h3⟩ := h
  unfold QuotReads
  exact ⟨ty, exprReader_litFree hsh hty h1, h2, h3⟩

theorem indReads_litFree (hsh : src.sharing.toList.all exprLitFree = true)
    {ind : Ixon.Inductive} (hty : exprLitFree ind.typ = true)
    (h : IndReads (exprReader t blob src param self) name ind ci₀) :
    IndReads (exprReader t blob' src param self) name ind ci₀ := by
  obtain ⟨ty, caps, h1, h2⟩ := h
  unfold IndReads
  exact ⟨ty, caps, exprReader_litFree hsh hty h1, h2⟩

theorem ctorReads_litFree (hsh : src.sharing.toList.all exprLitFree = true)
    {ct : Ixon.Constructor} (hty : exprLitFree ct.typ = true)
    (h : CtorReads (exprReader t blob src param self) name ct ci₀) :
    CtorReads (exprReader t blob' src param self) name ct ci₀ := by
  obtain ⟨ty, h1, h2⟩ := h
  unfold CtorReads
  exact ⟨ty, exprReader_litFree hsh hty h1, h2⟩

theorem ruleReads_litFree (hsh : src.sharing.toList.all exprLitFree = true)
    {Bm : _root_.Address} {im : Nat} {ru : Ixon.RecursorRule × Nat} {rl : RecRule .anon}
    (hrhs : exprLitFree ru.1.rhs = true)
    (h : RuleReads t (exprReader t blob src param self) Bm im ru rl) :
    RuleReads t (exprReader t blob' src param self) Bm im ru rl := by
  obtain ⟨rhs, h1, h2⟩ := h
  unfold RuleReads
  exact ⟨rhs, exprReader_litFree hsh hrhs h1, h2⟩

theorem recReads_litFree (hsh : src.sharing.toList.all exprLitFree = true)
    {rc : Ixon.Recursor} (hty : exprLitFree rc.typ = true)
    (hrules : (rc.rules.toList.all fun ru => exprLitFree ru.rhs) = true)
    (h : RecReads t store blob src self name rc ci₀) :
    RecReads t store blob' src self name rc ci₀ := by
  obtain ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10⟩ := h
  unfold RecReads
  exact ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, ps, rules, exprReader_litFree hsh hty h1, h2,
    h3, h4, h5, h6, exprReader_litFree hsh hty h7, h8,
    forall₂_imp_mem (fun p hp _ hr => ruleReads_litFree hsh
      (List.all_eq_true.mp hrules p.1 (List.fst_mem_of_mem_zipIdx hp)) hr) h9, h10⟩

/-- A member of a block of a store without literals has none, nor has the block's sharing
table. -/
theorem member_litFree (hlf : ∀ y c, store y = some c → recordLitFree c = true)
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat}
    {m : Ixon.MutConst} (hB : store B = some cb) (hms : cb.info = .muts ms)
    (hm : ms[i]? = some m) :
    cb.sharing.toList.all exprLitFree = true ∧ mutLitFree m = true := by
  have h := hlf B cb hB
  unfold recordLitFree at h
  rw [hms] at h
  simp only [infoLitFree, Bool.and_eq_true] at h
  exact ⟨h.1, List.all_eq_true.mp h.2 m (Array.mem_def.mp (Array.mem_of_getElem? hm))⟩

theorem memberAt_litFree (hlf : ∀ y c, store y = some c → recordLitFree c = true)
    {a : _root_.Address} {c : Ixon.Constant} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {m : Ixon.MutConst}
    (hm : MemberAt store a c B cb ms i m) :
    cb.sharing.toList.all exprLitFree = true ∧ mutLitFree m = true := by
  obtain ⟨hB, hms, hmi, -⟩ := hm
  exact member_litFree hlf hB hms hmi

end Reads

/-- **A reading over a store without literals is a reading under any blobs**: every expression it
reads is one of a record of the store, read against that record's sharing table. -/
theorem readsIn_litFree {t : RoleTable} {store : Store}
    {blob blob' : _root_.Address → Option ByteArray}
    (hlf : ∀ y c, store y = some c → recordLitFree c = true) {a : _root_.Address}
    {ci₀ : ConstantInfo .anon} (h : ReadsIn t store blob a ci₀) : ReadsIn t store blob' a ci₀ := by
  obtain ⟨c, hc, h⟩ := h
  refine Exists.intro c (And.intro hc ?_)
  have hrec := hlf a c hc
  unfold recordLitFree at hrec
  simp only [Bool.and_eq_true] at hrec
  obtain ⟨hsh, hinfo⟩ := hrec
  generalize c.info = info at h hinfo ⊢
  cases info with
  | defn d =>
    obtain ⟨h1, h2⟩ := h
    simp only [infoLitFree, Bool.and_eq_true] at hinfo
    exact And.intro h1 (defnReads_litFree hsh hinfo.1 hinfo.2 h2)
  | axio ax =>
    obtain ⟨h1, h2⟩ := h
    simp only [infoLitFree] at hinfo
    exact And.intro h1 (axiomReads_litFree hsh hinfo h2)
  | quot q =>
    simp only [infoLitFree] at hinfo
    exact quotReads_litFree hsh hinfo h
  | recr rc =>
    obtain ⟨h1, h2⟩ := h
    simp only [infoLitFree, Bool.and_eq_true] at hinfo
    exact And.intro h1 (recReads_litFree hsh hinfo.1 hinfo.2 h2)
  | dPrj p =>
    obtain ⟨cb, ms, d, hm, hr⟩ := h
    obtain ⟨hsh', hmf⟩ := memberAt_litFree hlf hm
    simp only [mutLitFree, Bool.and_eq_true] at hmf
    exact Exists.intro cb (Exists.intro ms (Exists.intro d
      (And.intro hm (defnReads_litFree hsh' hmf.1 hmf.2 hr))))
  | iPrj p =>
    obtain ⟨cb, ms, ind, hm, hr⟩ := h
    obtain ⟨hsh', hmf⟩ := memberAt_litFree hlf hm
    simp only [mutLitFree, Bool.and_eq_true] at hmf
    exact Exists.intro cb (Exists.intro ms (Exists.intro ind
      (And.intro hm (indReads_litFree hsh' hmf.1 hr))))
  | cPrj p =>
    obtain ⟨cb, ms, ind, ct, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    obtain ⟨hsh', hmf⟩ := member_litFree hlf h1 h2 h3
    simp only [mutLitFree, Bool.and_eq_true] at hmf
    have hct : exprLitFree ct.typ = true :=
      List.all_eq_true.mp hmf.2 ct (Array.mem_def.mp (Array.mem_of_getElem? h4))
    exact Exists.intro cb (Exists.intro ms (Exists.intro ind (Exists.intro ct
      (And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4
        (And.intro h5 (And.intro h6 (And.intro h7 (And.intro h8
          (ctorReads_litFree hsh' hct h9))))))))))))
  | rPrj p =>
    obtain ⟨cb, ms, rc, hm, hr⟩ := h
    obtain ⟨hsh', hmf⟩ := memberAt_litFree hlf hm
    simp only [mutLitFree, Bool.and_eq_true] at hmf
    exact Exists.intro cb (Exists.intro ms (Exists.intro rc
      (And.intro hm (recReads_litFree hsh' hmf.1 hmf.2 hr))))
  | muts ms => exact False.elim h

/-! ## The basis rows -/

set_option maxRecDepth 100000 in
/-- **No literal in the 24 committed basis rows** (decided over the rows). -/
theorem basisRows_litFree : basisRows.all (fun e => recordLitFree e.2) = true := by
  decide +kernel

/-- **No literal in a record of the basis store.** -/
theorem basisStore_litFree {y : _root_.Address} {c : Ixon.Constant}
    (h : recordOf basisStore y = some c) : recordLitFree c = true :=
  List.all_eq_true.mp basisRows_litFree (y, c) (StoreInhabit.store_record_inv h)

end IxVM.Refinement.Binding
