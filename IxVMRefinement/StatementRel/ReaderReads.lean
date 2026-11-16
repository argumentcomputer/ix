import IxVMRefinement.Assembly.NativeFormerReader
import IxVMRefinement.L1.ConvertExpr
import Ix.IxVM.Consistency.ReadsKeys

/-! # What the kernel's reader reads is a `Reads`

The easy direction between the per-record relation `IxVM.Consistency.ReadsIn` and the
kernel's executable reader: where the reader succeeds on a record, each constant its
declarations install is the `ReadsIn` of the record's constant address, over the reader's own
store and blobs.

* `read_le`: the reader's expression conversion is monotone in its context. If a second
  context answers every key and blob the first answers, and every `recur` the first resolves,
  an expression the first converts converts to the same term in the second.
* `read_reads`: so a conversion in a reader context whose keys are the role table's
  (`keyOf`) is a conversion in the reading context of `Reads`.
* `reads_of_readRecord_defn`, `reads_of_readRecord_axio`: standalone definition, theorem,
  opaque and axiom records.
* `reads_of_readInductiveBare`: the type and constructor constants of an inductive block.

The hypotheses name what the reader's context must satisfy: its keys are the table's
(`hkeys`, and `hname`, `hmember`, `hctor` for the keys of declared constants), and no
projection rewrite applies (`hrw`; `Reads` declares the record's own value). The constants
of a block are read at their projection records' addresses, where the store holds those
records.
-/

namespace IxVM.Refinement.ReaderReads

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open IxVM.Refinement.Assembly
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (throw_ok)

/-! ## Expression conversion is monotone in the context -/

section Transfer

variable {cx₁ cx₂ : Ctx .anon} {src : Ixon.Constant} {univs : Array CLevel}
  {self₁ self₂ : Nat → Option (ReadM (CName .anon))}

private theorem ecx_keyAt_le (hkey : ∀ a k, cx₁.keyAt a = .ok k → cx₂.keyAt a = .ok k)
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

private theorem ecx_blobAt_eq (hblob : cx₁.blob = cx₂.blob) (i : UInt64) :
    (⟨cx₂, src, univs, self₂⟩ : ECx .anon).blobAt i =
      (⟨cx₁, src, univs, self₁⟩ : ECx .anon).blobAt i := by
  simp only [ECx.blobAt, hblob]

private theorem ecx_natAt_eq (hblob : cx₁.blob = cx₂.blob) (i : UInt64) :
    (⟨cx₂, src, univs, self₂⟩ : ECx .anon).natAt i =
      (⟨cx₁, src, univs, self₁⟩ : ECx .anon).natAt i := by
  simp only [ECx.natAt, ecx_blobAt_eq (self₁ := self₁) (self₂ := self₂) hblob i]

/-- **One expression, in a context that answers at least as much.** -/
theorem convExpr_le (hkey : ∀ a k, cx₁.keyAt a = .ok k → cx₂.keyAt a = .ok k)
    (hblob : cx₁.blob = cx₂.blob)
    (hself : ∀ i k, self₁ i = some (.ok k) → self₂ i = some (.ok k))
    {tbl₁ tbl₂ : Array (ReadM (CExpr .anon))}
    (htbl : ∀ i v, tbl₁[i]? = some (.ok v) → tbl₂[i]? = some (.ok v)) :
    ∀ (e : Ixon.Expr) (v : CExpr .anon),
      convExpr (⟨cx₁, src, univs, self₁⟩ : ECx .anon) tbl₁ e = .ok v →
      convExpr (⟨cx₂, src, univs, self₂⟩ : ECx .anon) tbl₂ e = .ok v := by
  intro e
  induction e with
  | sort i =>
    intro v h
    simp only [convExpr] at h ⊢
    exact h
  | var i =>
    intro v h
    simp only [convExpr] at h ⊢
    exact h
  | ref i us =>
    intro v h
    simp only [convExpr] at h ⊢
    obtain ⟨k, hk, hrest⟩ := except_bind_ok.mp h
    rw [ecx_keyAt_le (self₂ := self₂) hkey hk]
    exact hrest
  | recur i us =>
    intro v h
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
    intro v h
    simp only [convExpr] at h ⊢
    obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    rw [ecx_keyAt_le (self₂ := self₂) hkey hk, ih x hx]
    exact h
  | str i =>
    intro v h
    simp only [convExpr] at h ⊢
    rw [ecx_blobAt_eq (self₁ := self₁) (self₂ := self₂) hblob i]
    exact h
  | nat i =>
    intro v h
    simp only [convExpr] at h ⊢
    rw [ecx_natAt_eq (self₁ := self₁) (self₂ := self₂) hblob i]
    exact h
  | app f a ihf iha =>
    intro v h
    simp only [convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    rw [ihf x hx, iha y hy]
    exact h
  | lam ty b iht ihb =>
    intro v h
    simp only [convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    rw [iht x hx, ihb y hy]
    exact h
  | all ty b iht ihb =>
    intro v h
    simp only [convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    rw [iht x hx, ihb y hy]
    exact h
  | letE nonDep mode ty val b iht ihv ihb =>
    intro v h
    simp only [convExpr] at h ⊢
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    obtain ⟨z, hz, h⟩ := except_bind_ok.mp h
    rw [iht x hx, ihv y hy, ihb z hz]
    exact h
  | share i =>
    intro v h
    cases ht : tbl₁[i.toNat]? with
    | none =>
      simp only [convExpr, ht] at h
      exact (throw_ok h).elim
    | some r =>
      simp only [convExpr, ht] at h
      subst h
      simp only [convExpr, htbl _ _ ht]

/-- The sharing table, entry by entry. -/
theorem buildShareTblGo_le (hkey : ∀ a k, cx₁.keyAt a = .ok k → cx₂.keyAt a = .ok k)
    (hblob : cx₁.blob = cx₂.blob)
    (hself : ∀ i k, self₁ i = some (.ok k) → self₂ i = some (.ok k)) :
    ∀ (es : List Ixon.Expr) (acc₁ acc₂ : Array (ReadM (CExpr .anon))),
      acc₁.size = acc₂.size →
      (∀ i v, acc₁[i]? = some (.ok v) → acc₂[i]? = some (.ok v)) →
      ∀ i v,
        (L1.buildShareTblGo (⟨cx₁, src, univs, self₁⟩ : ECx .anon) acc₁ es)[i]? = some (.ok v) →
        (L1.buildShareTblGo (⟨cx₂, src, univs, self₂⟩ : ECx .anon) acc₂ es)[i]? =
          some (.ok v) := by
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
    · intro i v hi
      rw [Array.getElem?_push] at hi ⊢
      by_cases hsize : i = acc₁.size
      · rw [if_pos hsize] at hi
        rw [if_pos (hsize.trans hsz),
          convExpr_le hkey hblob hself hacc e v (Option.some.inj hi)]
      · rw [if_neg hsize] at hi
        rw [if_neg (fun h => hsize (h.trans hsz.symm))]
        exact hacc i v hi

end Transfer

/-- **The kernel reader's expression conversion is monotone in its context**: a member
reader over a context that answers every key the first answers, with the same blobs and
every `recur` the first resolves, converts what the first converts, to the same term. -/
theorem read_le {cx₁ cx₂ : Ctx .anon} {src : Ixon.Constant}
    {self₁ self₂ : Nat → Option (ReadM (CName .anon))}
    (hkey : ∀ a k, cx₁.keyAt a = .ok k → cx₂.keyAt a = .ok k)
    (hblob : cx₁.blob = cx₂.blob)
    (hself : ∀ i k, self₁ i = some (.ok k) → self₂ i = some (.ok k))
    {param : Nat → LevelParam} {e : Ixon.Expr} {v : CExpr .anon}
    (h : (MemberReader.mk' cx₁ src param self₁).read e = .ok v) :
    (MemberReader.mk' cx₂ src param self₂).read e = .ok v := by
  obtain ⟨hecx₁, htbl₁⟩ := L1.memberReader_mk'_eq cx₁ src param self₁
  obtain ⟨hecx₂, htbl₂⟩ := L1.memberReader_mk'_eq cx₂ src param self₂
  unfold MemberReader.read at h ⊢
  rw [hecx₁, htbl₁] at h
  rw [hecx₂, htbl₂]
  exact convExpr_le hkey hblob hself
    (buildShareTblGo_le hkey hblob hself src.sharing.toList #[] #[] rfl
      (fun i v hi => by simp at hi)) e v h

/-- **A conversion in a reader context whose keys are the role table's is a conversion in
the reading context of `Reads`**, over the reader's own blobs. -/
theorem read_reads {t : RoleTable} (checked : t.check = .ok ()) {cx : Ctx .anon}
    (hkeys : ∀ a k, cx.keyAt a = .ok k → k = keyOf t a) {src : Ixon.Constant}
    {param : Nat → LevelParam} {self self' : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i k, self i = some (.ok k) → self' i = some (.ok k))
    {e : Ixon.Expr} {v : CExpr .anon}
    (h : (MemberReader.mk' cx src param self).read e = .ok v) :
    (exprReader t cx.blob src param self').read e = .ok v :=
  read_le (cx₂ := readCtx t cx.blob)
    (fun a k hk => by rw [hkeys a k hk]; exact readCtx_keyAt checked cx.blob a) rfl hself h

/-! ## Standalone records -/

/-- A definition the reader reads passes its safety policy. -/
theorem readDefinition_safe {cx : Ctx .anon} {st : State .anon} {heights : CName .anon → Nat}
    {ref : ConstRef _root_.Address} {lps : List LevelParam} {mr : MemberReader .anon}
    {d : Ixon.Definition} {decl : CDecl .anon} {rwd : Bool}
    (h : readDefinition cx st heights ref lps mr d = .ok (decl, rwd)) :
    safetyDeclineOf d.kind d.safety = none := by
  unfold readDefinition lowerDefinition at h
  cases hk : cx.memberKey ref with
  | error e => simp [hk, bind, Except.bind] at h
  | ok key =>
    cases ht : mr.read d.typ with
    | error e => simp [hk, ht, bind, Except.bind] at h
    | ok ty =>
      cases hv : mr.read d.value with
      | error e => simp [hk, ht, hv, bind, Except.bind] at h
      | ok value =>
        simp only [hk, ht, hv, bind, Except.bind] at h
        cases hs : safetyDeclineOf d.kind d.safety with
        | some why => simp [hs, declined, throw, throwThe, MonadExceptOf.throw] at h
        | none => rfl

/-- A standalone definition record the reader reads is in Lean's logic. -/
theorem readRecord_defn_safe {cx : Ctx .anon} {st : State .anon} {a : _root_.Address}
    {c : Ixon.Constant} {d : Ixon.Definition} {r : Read .anon} (hc : c.info = .defn d)
    (h : readRecord cx st a c = .ok r) : safetyDecline d = none := by
  unfold readRecord at h
  rw [hc] at h
  dsimp only at h
  obtain ⟨⟨decl, rwd⟩, hd, -⟩ := except_bind_ok.mp h
  exact readDefinition_safe hd

/-- **A standalone definition, theorem or opaque record**: where the reader reads it with no
projection rewrite, the constant its declaration installs is the `ReadsIn` of the record's
address. -/
theorem reads_of_readRecord_defn {t : RoleTable} (checked : t.check = .ok ()) {cx : Ctx .anon}
    {st : State .anon} {a : _root_.Address} {c : Ixon.Constant} {r : Read .anon}
    {d : Ixon.Definition}
    (hkeys : ∀ x k, cx.keyAt x = .ok k → k = keyOf t x)
    (hname : ∀ k, cx.memberKey (.member a 0) = .ok k → k = keyOf t a)
    (hstore : cx.store a = some c)
    (hrw : ∀ cv value, projRewrite st cv value = none)
    (hc : c.info = .defn d) (h : readRecord cx st a c = .ok r) :
    ∀ decl ∈ r.decls.toList, ∀ ci₀ ∈ installs decl, ReadsIn t cx.store cx.blob a ci₀ := by
  have hsafe := readRecord_defn_safe hc h
  have hl : InLogic c := by
    unfold InLogic
    rw [hc]
    exact hsafe
  obtain ⟨decl, hread, hdecls⟩ := readRecord_singleton (by rw [hc]; rfl) h
  intro decl' hdecl' ci₀ hci
  rw [hdecls] at hdecl'
  have hdd : decl' = decl := by simpa using hdecl'
  subst hdd
  have hself : ∀ i k,
      (if (i == 0) = true then some (cx.memberKey (.member a 0)) else none) =
        some (Except.ok k) → soloSelf t a i = some (Except.ok k) := by
    intro i k hi
    unfold soloSelf
    by_cases h0 : (i == 0) = true
    · rw [if_pos h0] at hi ⊢
      have hk := hname k (Option.some.inj hi)
      subst hk
      rfl
    · rw [if_neg h0] at hi
      cases hi
  cases hread with
  | axio info _ _ _ =>
    rw [hc] at info
    cases info
  | quot info _ _ =>
    rw [hc] at info
    cases info
  | defn info keyed type body kind =>
    rw [hc] at info
    have hdd := Ixon.ConstantInfo.defn.inj info
    subst hdd
    have hk := hname _ keyed
    subst hk
    have hty := read_reads checked hkeys hself type
    have hval := read_reads checked hkeys hself body
    rw [hrw] at kind
    generalize hkd : d.kind = kd at kind
    cases kind with
    | defn hint =>
      have hci' := List.mem_singleton.mp hci
      have hr : DefnReads (exprReader t cx.blob c id (soloSelf t a)) (keyOf t a) d ci₀ := by
        unfold DefnReads
        refine ⟨_, _, hty, hval, ?_⟩
        rw [hkd]
        exact ⟨hint, hci'⟩
      exact ReadsIn.of_defn hstore hc hl hr
    | thm =>
      have hci' := List.mem_singleton.mp hci
      have hr : DefnReads (exprReader t cx.blob c id (soloSelf t a)) (keyOf t a) d ci₀ := by
        unfold DefnReads
        refine ⟨_, _, hty, hval, ?_⟩
        rw [hkd]
        exact hci'
      exact ReadsIn.of_defn hstore hc hl hr
    | opaq =>
      have hci' := List.mem_singleton.mp hci
      have hr : DefnReads (exprReader t cx.blob c id (soloSelf t a)) (keyOf t a) d ci₀ := by
        unfold DefnReads
        refine ⟨_, _, hty, hval, ?_⟩
        rw [hkd]
        exact hci'
      exact ReadsIn.of_defn hstore hc hl hr

/-- **A standalone axiom record**: where the reader reads it, the constant its declaration
installs (none, at the key of `Quot.sound` or of an inert role) is the `ReadsIn` of the
record's address. -/
theorem reads_of_readRecord_axio {t : RoleTable} (checked : t.check = .ok ()) {cx : Ctx .anon}
    {st : State .anon} {a : _root_.Address} {c : Ixon.Constant} {r : Read .anon}
    {ax : Ixon.Axiom}
    (hkeys : ∀ x k, cx.keyAt x = .ok k → k = keyOf t x)
    (hname : ∀ k, cx.memberKey (.member a 0) = .ok k → k = keyOf t a)
    (hstore : cx.store a = some c)
    (hc : c.info = .axio ax) (h : readRecord cx st a c = .ok r) :
    ∀ decl ∈ r.decls.toList, ∀ ci₀ ∈ installs decl, ReadsIn t cx.store cx.blob a ci₀ := by
  obtain ⟨decl, hread, hdecls⟩ := readRecord_singleton (by rw [hc]; rfl) h
  intro decl' hdecl' ci₀ hci
  rw [hdecls] at hdecl'
  have hdd : decl' = decl := by simpa using hdecl'
  subst hdd
  cases hread with
  | defn info _ _ _ _ =>
    rw [hc] at info
    cases info
  | quot info _ _ =>
    rw [hc] at info
    cases info
  | axio info safe keyed type =>
    rw [hc] at info
    have hdd := Ixon.ConstantInfo.axio.inj info
    subst hdd
    have hk := hname _ keyed
    subst hk
    have hl : InLogic c := by
      unfold InLogic
      rw [hc]
      exact safe
    have hty := read_reads checked hkeys (self' := fun _ => none)
      (fun i k hi => by cases hi) type
    by_cases hq : keyOf t a = Ix.Kernel.quotSoundName ∨ inertKey (keyOf t a) = true
    · simp only [installs, if_pos hq] at hci
      cases hci
    · simp only [installs, if_neg hq] at hci
      have hci' := List.mem_singleton.mp hci
      have hinert : inertKey (keyOf t a) = false := by
        cases hb : inertKey (keyOf t a) with
        | false => rfl
        | true => exact absurd (Or.inr hb) hq
      have hr : AxiomReads (exprReader t cx.blob c id (fun _ => none)) (keyOf t a) ax ci₀ := by
        unfold AxiomReads
        exact ⟨hinert, _, hty, hci'⟩
      exact ReadsIn.of_axio hstore hc hl hr

/-! ## Inductive blocks -/

private theorem forall₂_right_mem {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) {b : β} (hb : b ∈ m) : ∃ a, a ∈ l ∧ R a b := by
  induction h with
  | nil => cases hb
  | cons hab _ ih =>
    rcases List.mem_cons.mp hb with e | hb'
    · rw [e]
      exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih hb'
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- **The type and constructor constants of an inductive block**: where the reader reads the
block at `owner` (its bare lowering), the block's declaration lists the types' constants,
then the constructors', then the recursors'. Each type constant is the `ReadsIn` of its
member's address, and each constructor constant of its constructor's address, where the store
holds that address's projection record. -/
theorem reads_of_readInductiveBare {t : RoleTable} (checked : t.check = .ok ())
    {cx : Ctx .anon} {owner : _root_.Address} {source : Ixon.Constant}
    {members : Array Ixon.MutConst} {result : Read .anon}
    (hkeys : ∀ x k, cx.keyAt x = .ok k → k = keyOf t x)
    (hmember : ∀ i m k, members[i]? = some m → cx.memberKey (.member owner i) = .ok k →
      k = keyOf t (memberAddr owner i m))
    (hctor : ∀ i j k, cx.memberKey (.ctor owner i j) = .ok k → k = keyOf t (ctorAddr owner i j))
    (hstore : cx.store owner = some source) (hinfo : source.info = .muts members)
    (hlogic : InLogic source)
    (hboundI : ∀ i m, members[i]? = some m → i < UInt64.size)
    (hboundJ : ∀ i ind j ct, members[i]? = some (.indc ind) → ind.ctors[j]? = some ct →
      j < UInt64.size)
    (read : readInductiveBare cx owner source members = .ok result) :
    ∃ (types ctors : List (ConstantVal .anon × Nat × Nat)) (recs : List (ConstantInfo .anon))
      (nP : Nat),
      result.decls = #[.indDecl ((types.map fun x => .indInfo x.1 {}) ++
        (ctors.map fun x => .ctorInfo x.1 x.2.1 x.2.2) ++ recs) nP] ∧
      (∀ row ∈ types, ∃ i ind, members[i]? = some (.indc ind) ∧
        (cx.store (memberAddr owner i (.indc ind)) =
            some (memberProjection owner i (.indc ind)) →
          ReadsIn t cx.store cx.blob (memberAddr owner i (.indc ind)) (.indInfo row.1 {}))) ∧
      (∀ row ∈ ctors, ∃ i j,
        (cx.store (ctorAddr owner i j) = some (constructorProjection owner i j) →
          ReadsIn t cx.store cx.blob (ctorAddr owner i j)
            (.ctorInfo row.1 row.2.1 row.2.2))) := by
  obtain ⟨shape, block, -, lowered, formers, ctorFrames⟩ := readInductiveBare_native_frames read
  obtain ⟨-, hdecls, -⟩ := lowerInductiveBare_spec lowered
  have hself : ∀ i k,
      (if i < members.size then some (cx.memberKey (.member owner i)) else none) =
        some (Except.ok k) → blockSelf t owner members i = some (Except.ok k) := by
    intro i k hi
    by_cases hlt : i < members.size
    · rw [if_pos hlt] at hi
      have hm : members[i]? = some members[i] := by simp
      have hk := hmember i _ k hm (Option.some.inj hi)
      subst hk
      unfold blockSelf
      rw [hm]
      rfl
    · rw [if_neg hlt] at hi
      cases hi
  have hentry : ∀ entry : Nat × Ixon.Inductive,
      entry ∈ (shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
        | some (.indc ind) => some (i, ind)
        | _ => none)).toList → members[entry.1]? = some (.indc entry.2) := by
    intro entry hmem
    rw [Array.toList_filterMap] at hmem
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hmem
    dsimp only at hi
    cases hm : members[i]? with
    | none =>
      rw [hm] at hi
      cases hi
    | some m =>
      rw [hm] at hi
      cases m with
      | indc ind =>
        have he : (i, ind) = entry := Option.some.inj hi
        rw [← he]
        exact hm
      | defn d => cases hi
      | recr rc => cases hi
  refine ⟨block.types.toList, block.ctors.toList, _, block.numParams, hdecls, ?_, ?_⟩
  · intro row hrow
    obtain ⟨entry, hmem, hname, htype, hlps, -, -⟩ := forall₂_right_mem formers hrow
    have hm := hentry entry hmem
    refine ⟨entry.1, entry.2, hm, fun hproj => ?_⟩
    obtain ⟨⟨name, lps, ty⟩, nP, nI⟩ := row
    have hk : name = keyOf t (memberAddr owner entry.1 (.indc entry.2)) :=
      hmember _ _ _ hm hname
    have hl : lps = List.range entry.2.lvls.toNat := hlps
    subst hk
    subst hl
    have hty := read_reads checked hkeys hself htype
    have hr : IndReads (exprReader t cx.blob source id (blockSelf t owner members))
        (keyOf t (memberAddr owner entry.1 (.indc entry.2))) entry.2
        (.indInfo ⟨keyOf t (memberAddr owner entry.1 (.indc entry.2)),
          List.range entry.2.lvls.toNat, ty⟩ {}) := by
      unfold IndReads
      exact ⟨ty, {}, hty, rfl⟩
    exact ReadsIn.of_ind (hboundI _ _ hm) hstore hinfo hm hlogic hproj hr
  · intro row hrow
    obtain ⟨slot, hslot, ⟨hname, htype, hlps, hP, hF⟩, hcidx, -⟩ :=
      forall₂_right_mem ctorFrames hrow
    unfold nativeCtorSlots at hslot
    obtain ⟨entry, hmem, hslot'⟩ := List.mem_flatMap.mp hslot
    obtain ⟨⟨ct, j⟩, hcj, hsl⟩ := List.mem_map.mp hslot'
    subst hsl
    rw [Array.toList_zipIdx] at hcj
    have hct : entry.2.ctors[j]? = some ct := by
      simpa using List.mem_zipIdx_iff_getElem?.mp hcj
    have hm := hentry entry hmem
    refine ⟨entry.1, j, fun hproj => ?_⟩
    obtain ⟨⟨name, lps, ty⟩, nP, nF⟩ := row
    have hk : name = keyOf t (ctorAddr owner entry.1 j) := hctor _ _ _ hname
    have hl : lps = List.range ct.lvls.toNat := hlps
    have hp : nP = ct.params.toNat := hP
    have hf : nF = ct.fields.toNat := hF
    subst hk
    subst hl
    subst hp
    subst hf
    have hty := read_reads checked hkeys hself htype
    have hr : CtorReads (exprReader t cx.blob source id (blockSelf t owner members))
        (keyOf t (ctorAddr owner entry.1 j)) ct
        (.ctorInfo ⟨keyOf t (ctorAddr owner entry.1 j), List.range ct.lvls.toNat, ty⟩
          ct.params.toNat ct.fields.toNat) := by
      unfold CtorReads
      exact ⟨ty, hty, rfl⟩
    exact ReadsIn.of_ctor (hboundI _ _ hm) (hboundJ _ _ _ _ hm hct) hstore hinfo hm hct hcidx
      hlogic hproj hr

end IxVM.Refinement.ReaderReads
