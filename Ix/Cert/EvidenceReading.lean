import Ix.RoleEvidence
import Ix.LeanIngress.Collapse
import IxC.Kernel.Verify.Rename.Basic

/-! # Source's evidence bundle, read as the Ixon reader reads it

Quotient Source's evidence bundle (`Ix.RoleEvidence.Bundle`) holds the role table's own
evidence records, with a name for each address they cite. Read by name
(`Bundle.conv`) and renamed onto an artifact's keys (onto the fiber representatives,
then to addresses), a record's expression is the Ixon reader's reading of the same
record (`Ix.Kernel.Reader.convExpr`), wherever each name the record cites renames to the
key the reader gives the cited address and each cited blob reads alike (`conv_read`).
The sharing tables of the two readings correspond entry by entry (`sharing_read`). -/

namespace Ix.Cert.EvidenceReading

open Ix.Kernel Ix.Kernel.Reader Ix.RoleEvidence

/-- **The renaming of a Source key onto an artifact's**: onto its fiber's representative
(`Ix.LeanIngress.Key.subst`), then to an address (`Key.map`). -/
def renameKey (ρ : Ix.LeanIngress.FiberMap) (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon) (k : Ix.Kernel.Key .source) :
    Ix.Kernel.Key .anon :=
  (Ix.LeanIngress.Key.subst ρ k).map f

/-- **The renaming of a Source term onto an artifact's keys**, as `renameKey` renames
its keys. -/
def renameExpr (ρ : Ix.LeanIngress.FiberMap) (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon) (e : Ix.Kernel.Expr .source) :
    Ix.Kernel.Expr .anon :=
  (Ix.LeanIngress.Expr.substKeys ρ e).mapKeys f

section
variable {ρ : Ix.LeanIngress.FiberMap} {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon}

@[simp] theorem renameExpr_bvar (i : Nat) : renameExpr ρ f (.bvar i) = .bvar i := rfl
@[simp] theorem renameExpr_sort (u : Ix.Kernel.Level) : renameExpr ρ f (.sort u) = .sort u := rfl
@[simp] theorem renameExpr_const (k : Ix.Kernel.Key .source) (us : List Ix.Kernel.Level) :
    renameExpr ρ f (.const k us) = .const (renameKey ρ f k) us := rfl
@[simp] theorem renameExpr_app (a b : Ix.Kernel.Expr .source) :
    renameExpr ρ f (.app a b) = .app (renameExpr ρ f a) (renameExpr ρ f b) := rfl
@[simp] theorem renameExpr_lam (t b : Ix.Kernel.Expr .source) (m : Ix.Kernel.BinderMeta) :
    renameExpr ρ f (.lam t b m) = .lam (renameExpr ρ f t) (renameExpr ρ f b) m := rfl
@[simp] theorem renameExpr_forallE (t b : Ix.Kernel.Expr .source) (m : Ix.Kernel.BinderMeta) :
    renameExpr ρ f (.forallE t b m) = .forallE (renameExpr ρ f t) (renameExpr ρ f b) m := rfl
@[simp] theorem renameExpr_letE (t v b : Ix.Kernel.Expr .source) (l : Ix.Kernel.LetMeta) :
    renameExpr ρ f (.letE t v b l) = .letE (renameExpr ρ f t) (renameExpr ρ f v) (renameExpr ρ f b) l := rfl
@[simp] theorem renameExpr_lit (l : Ix.Kernel.Literal) : renameExpr ρ f (.lit l) = .lit l := rfl
@[simp] theorem renameExpr_proj (s : Ix.Kernel.Key .source) (i : Nat) (e : Ix.Kernel.Expr .source) :
    renameExpr ρ f (.proj s i e) = .proj (renameKey ρ f s) i (renameExpr ρ f e) := rfl

end

/-- A universe index the bundle reads, the reader reads alike over the same table. -/
theorem level_read {univs : Array CLevel} {e : ECx .anon} (hu : e.univs = univs) {i : UInt64} {l : CLevel}
    (h : Bundle.conv.level univs i = .ok l) : e.level i = .ok l := by
  unfold Bundle.conv.level at h
  unfold ECx.level
  rw [hu]
  split at h
  · rename_i l' hl
    cases h
    simp [hl, pure, Except.pure]
  · cases h

/-- Universe indices the bundle reads, the reader reads alike over the same table. -/
theorem levels_read {univs : Array CLevel} {e : ECx .anon} (hu : e.univs = univs) :
    ∀ (us : List UInt64) (ls : List CLevel),
      us.mapM (Bundle.conv.level univs) = .ok ls → us.mapM e.level = .ok ls
  | [], ls, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h ⊢
    exact h
  | u :: us, ls, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h ⊢
    cases hu1 : Bundle.conv.level univs u with
    | error err => rw [hu1] at h; cases h
    | ok l =>
      rw [hu1] at h
      rw [level_read hu hu1]
      simp only at h ⊢
      cases hus : us.mapM (Bundle.conv.level univs) with
      | error err => rw [hus] at h; cases h
      | ok ls' =>
        rw [hus] at h
        rw [levels_read hu us ls' hus]
        simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
        exact h

/-- **One expression of a record, read by name and by the Ixon reader.** Where each
reference the bundle reads names a key that renames to the reader's key of the same
reference (`hkey`), each literal reads the same blob (`hblob`), the universe tables agree
(`hu`) and the sharing entries correspond (`htbl`), an expression the bundle reads, the
reader reads as its renaming. -/
theorem conv_read {ρ : Ix.LeanIngress.FiberMap} {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon}
    {b : Bundle} {c : Ixon.Constant} {univs : Array CLevel} {tblB : Array (Except String (Ix.Kernel.Expr .source))}
    {e : ECx .anon} {tblR : Array (ReadM (Ix.Kernel.Expr .anon))}
    (hu : e.univs = univs)
    (hkey : ∀ i k, b.keyAt c i = .ok k → e.keyAt i = .ok (renameKey ρ f k))
    (hblob : ∀ i bs, b.blobAt c i = .ok bs → e.blobAt i = .ok bs)
    (htbl : ∀ (i : Nat) p, tblB[i]? = some (.ok p) → tblR[i]? = some (.ok (renameExpr ρ f p))) :
    ∀ (x : Ixon.Expr) (p : Ix.Kernel.Expr .source), b.conv c univs tblB x = .ok p →
      convExpr e tblR x = .ok (renameExpr ρ f p) := by
  intro x
  induction x with
  | var i =>
    intro p h
    simp only [Bundle.conv, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [convExpr, pure, Except.pure]
  | sort i =>
    intro p h
    simp only [Bundle.conv, bind, Except.bind, pure, Except.pure] at h
    cases hl : Bundle.conv.level univs i with
    | error err => rw [hl] at h; cases h
    | ok l =>
      rw [hl] at h
      cases h
      simp [convExpr, level_read hu hl, bind, Except.bind, pure, Except.pure]
  | ref i us =>
    intro p h
    simp only [Bundle.conv, bind, Except.bind, pure, Except.pure] at h
    cases hk : b.keyAt c i with
    | error err => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h
      cases hl : us.toList.mapM (Bundle.conv.level univs) with
      | error err => rw [hl] at h; cases h
      | ok ls =>
        rw [hl] at h
        cases h
        simp [convExpr, ECx.levels, hkey i k hk, levels_read hu _ _ hl, bind, Except.bind, pure, Except.pure]
  | recur i us =>
    intro p h
    simp [Bundle.conv, throw, throwThe, MonadExceptOf.throw] at h
  | prj i field v ih =>
    intro p h
    simp only [Bundle.conv, bind, Except.bind, pure, Except.pure] at h
    cases hk : b.keyAt c i with
    | error err => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h
      cases hv : b.conv c univs tblB v with
      | error err => rw [hv] at h; cases h
      | ok pv =>
        rw [hv] at h
        cases h
        simp [convExpr, hkey i k hk, ih pv hv, bind, Except.bind, pure, Except.pure]
  | str i =>
    intro p h
    simp only [Bundle.conv, bind, Except.bind, pure, Except.pure] at h
    cases hb : b.blobAt c i with
    | error err => rw [hb] at h; cases h
    | ok bs =>
      rw [hb] at h
      cases hs : String.fromUTF8? bs with
      | none => simp [hs, throw, throwThe, MonadExceptOf.throw] at h
      | some s =>
        simp only [hs, Except.ok.injEq] at h
        subst h
        simp [convExpr, hblob i bs hb, hs, bind, Except.bind, pure, Except.pure]
  | nat i =>
    intro p h
    simp only [Bundle.conv, bind, Except.bind, pure, Except.pure] at h
    cases hb : b.blobAt c i with
    | error err => rw [hb] at h; cases h
    | ok bs =>
      rw [hb] at h
      cases h
      simp [convExpr, hblob i bs hb, bind, Except.bind, pure, Except.pure]
  | app a d iha ihd =>
    intro p h
    simp only [Bundle.conv, bind, Except.bind, pure, Except.pure] at h
    cases ha : b.conv c univs tblB a with
    | error err => rw [ha] at h; cases h
    | ok pa =>
      rw [ha] at h
      cases hd : b.conv c univs tblB d with
      | error err => rw [hd] at h; cases h
      | ok pd =>
        rw [hd] at h
        cases h
        simp [convExpr, iha pa ha, ihd pd hd, bind, Except.bind, pure, Except.pure]
  | lam ct t bd iht ihb =>
    intro p h
    simp only [Bundle.conv, bind, Except.bind, pure, Except.pure] at h
    cases ht : b.conv c univs tblB t with
    | error err => rw [ht] at h; cases h
    | ok pt =>
      rw [ht] at h
      cases hb : b.conv c univs tblB bd with
      | error err => rw [hb] at h; cases h
      | ok pb =>
        rw [hb] at h
        cases h
        simp [convExpr, iht pt ht, ihb pb hb, bind, Except.bind, pure, Except.pure]
  | all ct r t bd iht ihb =>
    intro p h
    simp only [Bundle.conv, bind, Except.bind, pure, Except.pure] at h
    cases ht : b.conv c univs tblB t with
    | error err => rw [ht] at h; cases h
    | ok pt =>
      rw [ht] at h
      cases hb : b.conv c univs tblB bd with
      | error err => rw [hb] at h; cases h
      | ok pb =>
        rw [hb] at h
        cases h
        simp [convExpr, iht pt ht, ihb pb hb, bind, Except.bind, pure, Except.pure]
  | letE ct t v bd iht ihv ihb =>
    intro p h
    simp only [Bundle.conv, bind, Except.bind, pure, Except.pure] at h
    cases ht : b.conv c univs tblB t with
    | error err => rw [ht] at h; cases h
    | ok pt =>
      rw [ht] at h
      cases hv : b.conv c univs tblB v with
      | error err => rw [hv] at h; cases h
      | ok pv =>
        rw [hv] at h
        cases hb : b.conv c univs tblB bd with
        | error err => rw [hb] at h; cases h
        | ok pb =>
          rw [hb] at h
          cases h
          simp [convExpr, iht pt ht, ihv pv hv, ihb pb hb, bind, Except.bind, pure, Except.pure]
  | share i =>
    intro p h
    simp only [Bundle.conv] at h
    split at h
    · rename_i r hr
      subst h
      simp [convExpr, htbl i.toNat p hr]
    · cases h

/-! ## Sharing tables and whole records -/

/-- The bundle's sharing table of record `c` (`Bundle.proofOf`'s loop): each entry read
against the entries before it. -/
def tableB (b : Bundle) (c : Ixon.Constant) (univs : Array CLevel) : Array (Except String (Ix.Kernel.Expr .source)) :=
  c.sharing.foldl (fun t e => t.push (b.conv c univs t e)) (Array.mkEmpty c.sharing.size)

/-- The reader's member reader of record `c` at the identity level parameters and the
member map `self` (as `evidenceValue?` builds it). -/
abbrev readerOf (cx : Ctx .anon) (c : Ixon.Constant) (self : Nat → Option (ReadM (CName .anon))) :
    MemberReader .anon :=
  MemberReader.mk' cx c id self

/-- **The two sharing tables correspond**: same size, and an entry the bundle reads, the
reader reads as its renaming. -/
def TableRel (ρ : Ix.LeanIngress.FiberMap) (f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon)
    (tB : Array (Except String (Ix.Kernel.Expr .source))) (tR : Array (ReadM (Ix.Kernel.Expr .anon))) : Prop :=
  tB.size = tR.size ∧ ∀ (i : Nat) p, tB[i]? = some (.ok p) → tR[i]? = some (.ok (renameExpr ρ f p))

theorem readerOf_ecx (cx : Ctx .anon) (c : Ixon.Constant) (self : Nat → Option (ReadM (CName .anon))) :
    (readerOf cx c self).ecx = ⟨cx, c, c.univs.map (convUniv id), self⟩ := by
  simp [readerOf, MemberReader.mk', Id.run]
  rfl

theorem readerOf_tbl (cx : Ctx .anon) (c : Ixon.Constant) (self : Nat → Option (ReadM (CName .anon))) :
    (readerOf cx c self).tbl = c.sharing.foldl
      (fun t e => t.push (convExpr ⟨cx, c, c.univs.map (convUniv id), self⟩ t e)) (Array.mkEmpty c.sharing.size) := by
  simp [readerOf, MemberReader.mk', Id.run]
  rfl

theorem tableRel_foldl {ρ : Ix.LeanIngress.FiberMap} {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon}
    {b : Bundle} {c : Ixon.Constant} {univs : Array CLevel} {e : ECx .anon}
    (hu : e.univs = univs)
    (hkey : ∀ i k, b.keyAt c i = .ok k → e.keyAt i = .ok (renameKey ρ f k))
    (hblob : ∀ i bs, b.blobAt c i = .ok bs → e.blobAt i = .ok bs) :
    ∀ (l : List Ixon.Expr) (tB : Array (Except String (Ix.Kernel.Expr .source))) (tR : Array (ReadM (Ix.Kernel.Expr .anon))),
      TableRel ρ f tB tR →
      TableRel ρ f (l.foldl (fun t x => t.push (b.conv c univs t x)) tB)
        (l.foldl (fun t x => t.push (convExpr e t x)) tR)
  | [], _, _, h => h
  | x :: l, tB, tR, ⟨hs, hr⟩ => by
    simp only [List.foldl_cons]
    refine tableRel_foldl hu hkey hblob l _ _ ⟨by simp [hs], ?_⟩
    intro i p hi
    rw [Array.getElem?_push] at hi ⊢
    by_cases hix : i = tB.size
    · subst hix
      simp only [↓reduceIte, Option.some.injEq] at hi
      simp only [← hs, ↓reduceIte, Option.some.injEq]
      exact conv_read hu hkey hblob hr x p hi
    · have hiR : i ≠ tR.size := by rw [← hs]; exact hix
      simp only [hix, hiR, ↓reduceIte] at hi ⊢
      exact hr i p hi

/-- **The sharing tables of one record correspond.** -/
theorem tableRel_of {ρ : Ix.LeanIngress.FiberMap} {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon}
    {b : Bundle} {c : Ixon.Constant} {cx : Ctx .anon} {self : Nat → Option (ReadM (CName .anon))}
    (hkey : ∀ i k, b.keyAt c i = .ok k →
      (ECx.keyAt ⟨cx, c, c.univs.map (convUniv id), self⟩ i) = .ok (renameKey ρ f k))
    (hblob : ∀ i bs, b.blobAt c i = .ok bs → ECx.blobAt ⟨cx, c, c.univs.map (convUniv id), self⟩ i = .ok bs) :
    TableRel ρ f (tableB b c (c.univs.map (convUniv id))) (readerOf cx c self).tbl := by
  rw [readerOf_tbl, tableB, ← Array.foldl_toList, ← Array.foldl_toList]
  exact tableRel_foldl rfl hkey hblob _ _ _ ⟨by simp, by simp⟩

/-- **A record's expression, read by name and by the reader**: where the references and
blobs agree, an expression of the record the bundle reads against its own sharing table,
the reader's member reader reads as its renaming. -/
theorem read_of_conv {ρ : Ix.LeanIngress.FiberMap} {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon}
    {b : Bundle} {c : Ixon.Constant} {cx : Ctx .anon} {self : Nat → Option (ReadM (CName .anon))}
    (hkey : ∀ i k, b.keyAt c i = .ok k →
      (ECx.keyAt ⟨cx, c, c.univs.map (convUniv id), self⟩ i) = .ok (renameKey ρ f k))
    (hblob : ∀ i bs, b.blobAt c i = .ok bs → ECx.blobAt ⟨cx, c, c.univs.map (convUniv id), self⟩ i = .ok bs)
    {x : Ixon.Expr} {p : Ix.Kernel.Expr .source}
    (h : b.conv c (c.univs.map (convUniv id)) (tableB b c (c.univs.map (convUniv id))) x = .ok p) :
    (readerOf cx c self).read x = .ok (renameExpr ρ f p) := by
  have rel := tableRel_of (ρ := ρ) (f := f) hkey hblob
  unfold MemberReader.read
  rw [readerOf_ecx]
  exact conv_read rfl hkey hblob rel.2 x p h

/-- `Bundle.proofOf`, unfolded: a theorem record's value against its sharing table. -/
theorem proofOf_eq {b : Bundle} {c : Ixon.Constant} {d : Ixon.Definition} (hc : c.info = .defn d)
    (hk : d.kind = .thm) :
    b.proofOf c = b.conv c (c.univs.map (convUniv id)) (tableB b c (c.univs.map (convUniv id))) d.value := by
  unfold Bundle.proofOf tableB
  rw [hc]
  have hb : (d.kind == .thm) = true := by rw [hk]; decide
  simp [hb]


/-- **A theorem record's statement, read by name**, as `Bundle.proofOf` reads its value:
against the record's sharing table, its universes as level parameters. -/
def typeOf (b : Bundle) (c : Ixon.Constant) : Except String (Ix.Kernel.Expr .source) :=
  match c.info with
  | .defn d => b.conv c (c.univs.map (convUniv id)) (tableB b c (c.univs.map (convUniv id))) d.typ
  | _ => .error "not a definition record"

/-- A reference the bundle reads by name, the reader reads by the key the name renames to,
where every named reference of the record does. -/
theorem keyAt_of_refs {ρ : Ix.LeanIngress.FiberMap} {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon}
    {b : Bundle} {c : Ixon.Constant} {cx : Ctx .anon} {univs : Array CLevel}
    {self : Nat → Option (ReadM (CName .anon))}
    (h : ∀ x n, x ∈ c.refs → b.names[x]? = some n →
      cx.keyAt x = .ok (renameKey ρ f (ofLeanName n))) :
    ∀ i k, b.keyAt c i = .ok k → (ECx.keyAt ⟨cx, c, univs, self⟩ i) = .ok (renameKey ρ f k) := by
  intro i k hk
  unfold Bundle.keyAt at hk
  cases hx : c.refs[i.toNat]? with
  | none => simp [hx, throw, throwThe, MonadExceptOf.throw] at hk
  | some x =>
    cases hn : b.names[x]? with
    | none => simp [hx, hn, throw, throwThe, MonadExceptOf.throw] at hk
    | some n =>
      simp only [hx, hn, pure, Except.pure, Except.ok.injEq] at hk
      subst hk
      have hmem : x ∈ c.refs := Array.mem_of_getElem? hx
      simp only [ECx.keyAt, hx]
      exact h x n hmem hn

/-- A literal the bundle reads, the reader reads alike, where every blob of the record
does. -/
theorem blobAt_of_refs {b : Bundle} {c : Ixon.Constant} {cx : Ctx .anon} {univs : Array CLevel}
    {self : Nat → Option (ReadM (CName .anon))}
    (h : ∀ x bs, x ∈ c.refs → b.blobs[x]? = some bs → cx.blob x = some bs) :
    ∀ i bs, b.blobAt c i = .ok bs → (ECx.blobAt ⟨cx, c, univs, self⟩ i) = .ok bs := by
  intro i bs hb
  unfold Bundle.blobAt at hb
  cases hx : c.refs[i.toNat]? with
  | none => simp [hx, throw, throwThe, MonadExceptOf.throw] at hb
  | some x =>
    cases hn : b.blobs[x]? with
    | none => simp [hx, hn, throw, throwThe, MonadExceptOf.throw] at hb
    | some bs' =>
      simp only [hx, hn, pure, Except.pure, Except.ok.injEq] at hb
      subst hb
      have hmem : x ∈ c.refs := Array.mem_of_getElem? hx
      simp [ECx.blobAt, hx, h x bs' hmem hn, pure, Except.pure]

/-- The member key of a singleton definition record reads. -/
theorem memberKey_singleton {cx : Ctx .anon} {a : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hstore : cx.store a = some c) (hc : c.info = .defn d) :
    ∃ k, cx.memberKey (.member a 0) = .ok k := by
  unfold Ctx.memberKey
  cases hr : cx.roles.names[ConstRef.member a 0]? with
  | some k => exact ⟨k, rfl⟩
  | none =>
    have hsing : singletonAt cx.store (.member a 0) = some a := by
      simp [singletonAt, hstore, hc, bind, Option.bind]
    have haddr : ∃ a', cx.addressOf (.member a 0) = .ok a' := by
      unfold Ctx.addressOf
      cases cx.keys.address[ConstRef.member a 0]? with
      | some a' => exact ⟨a', rfl⟩
      | none => exact ⟨a, by simp [hsing, pure, Except.pure]⟩
    obtain ⟨a', ha'⟩ := haddr
    simp only [ha', bind, Except.bind]
    cases cx.keys.byAddress[a']? with
    | some k => exact ⟨k, rfl⟩
    | none => exact ⟨.id a', by simp [Mode.addressId?, pure, Except.pure]⟩

/-- The value a lambda telescope ends in, renamed, is the renamed end. -/
theorem lamBody_rename {ρ : Ix.LeanIngress.FiberMap} {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon} :
    ∀ e : Ix.Kernel.Expr .source,
      Ix.Kernel.Frontend.lamBody (renameExpr ρ f e) = renameExpr ρ f (Ix.Kernel.Frontend.lamBody e)
  | .lam t b m => by
    simp only [renameExpr_lam, Ix.Kernel.Frontend.lamBody]
    exact lamBody_rename b
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .forallE _ _ _ | .letE _ _ _ _
  | .lit _ | .proj _ _ _ => by
    simp [renameExpr, Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.mapKeys, Ix.Kernel.Frontend.lamBody]

/-- **A term that does not end in a projection of its last binder is not rewritten**
(`projRewrite`), renamed or not. -/
theorem projRewrite_none {ρ : Ix.LeanIngress.FiberMap} {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon}
    {p : Ix.Kernel.Expr .source}
    (hp : ∀ s i, Ix.Kernel.Frontend.lamBody p ≠ .proj s i (.bvar 0)) (st : State .anon)
    (cv : CVal .anon) : projRewrite st cv (renameExpr ρ f p) = none := by
  unfold projRewrite
  rw [lamBody_rename]
  generalize hl : Ix.Kernel.Frontend.lamBody p = l at hp
  cases l with
  | proj s i e =>
    cases e with
    | bvar j =>
      cases j with
      | zero => exact absurd rfl (hp s i)
      | succ j => simp [renameExpr, Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.mapKeys]
    | _ => simp [renameExpr, Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.mapKeys]
  | _ => simp [renameExpr, Ix.LeanIngress.Expr.substKeys, Ix.Kernel.Expr.mapKeys]

/-- **The reader resolves a bundle record as the bundle reads it.** In a context whose
store holds the theorem record `c` at `a`, where every name the record cites renames to
the reader's key of the cited address and every cited blob reads alike, a record whose
value and statement the bundle reads, and whose value does not end in a projection of its
last binder, is resolved (`evidenceValue?`) to its value as the bundle reads it, renamed. -/
theorem evidenceValue_of_bundle {ρ : Ix.LeanIngress.FiberMap}
    {f : Ix.Kernel.Mode.Id .source → Ix.Kernel.Mode.Id .anon}
    {cx : Ctx .anon} {st : State .anon} {a : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    {b : Bundle} {p T : Ix.Kernel.Expr .source}
    (hstore : cx.store a = some c) (hc : c.info = .defn d) (hthm : d.kind = .thm)
    (hkey : ∀ x n, x ∈ c.refs → b.names[x]? = some n →
      cx.keyAt x = .ok (renameKey ρ f (ofLeanName n)))
    (hblob : ∀ x bs, x ∈ c.refs → b.blobs[x]? = some bs → cx.blob x = some bs)
    (hp : b.proofOf c = .ok p) (hT : typeOf b c = .ok T)
    (hproj : ∀ s i, Ix.Kernel.Frontend.lamBody p ≠ .proj s i (.bvar 0)) :
    ∃ k, evidenceValue? cx st a = some (k, renameExpr ρ f p) := by
  have hres : resolve cx.store a = some (.member a 0) := by
    simp [resolve, resolveSource, hstore, hc, bind, Option.bind]
  obtain ⟨k, hk⟩ := memberKey_singleton hstore hc
  let self : Nat → Option (ReadM (CName .anon)) :=
    fun j => if j == 0 then some (cx.memberKey (.member a 0)) else none
  have hkey' := keyAt_of_refs (univs := c.univs.map (convUniv id)) (self := self) (ρ := ρ) (f := f) hkey
  have hblob' := blobAt_of_refs (univs := c.univs.map (convUniv id)) (self := self) (b := b) hblob
  rw [proofOf_eq hc hthm] at hp
  have hT' : b.conv c (c.univs.map (convUniv id)) (tableB b c (c.univs.map (convUniv id))) d.typ = .ok T := by
    simpa [typeOf, hc] using hT
  have rv := read_of_conv (cx := cx) (self := self) hkey' hblob' hp
  have rt := read_of_conv (cx := cx) (self := self) hkey' hblob' hT'
  refine ⟨k, ?_⟩
  have hnone := projRewrite_none (ρ := ρ) (f := f) hproj st
    ⟨k, List.range d.lvls.toNat, renameExpr ρ f T⟩
  have hk2 : (d.kind == .thm) = true := by rw [hthm]; decide
  simp only [evidenceValue?, hres, hstore, hc, bind, Option.bind, ↓reduceIte, hk2]
  unfold readDefinition lowerDefinition
  simp only [readerOf] at rv rt
  have rv2 : (MemberReader.mk' cx c id fun j => if j = 0 then some (Except.ok k) else none).read d.value =
      .ok (renameExpr ρ f p) := by simpa [self, hk] using rv
  have rt2 : (MemberReader.mk' cx c id fun j => if j = 0 then some (Except.ok k) else none).read d.typ =
      .ok (renameExpr ρ f T) := by simpa [self, hk] using rt
  simp [hk, rt2, rv2, hnone, safetyDeclineOf, hthm, bind, Except.bind, pure, Except.pure]

end Ix.Cert.EvidenceReading

/-- info: 'Ix.Cert.EvidenceReading.evidenceValue_of_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.EvidenceReading.evidenceValue_of_bundle
