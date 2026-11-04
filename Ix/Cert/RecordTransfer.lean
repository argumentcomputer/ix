import IxC.Kernel.Ixon.ReaderSpec

/-! # A singleton record read in a larger context

The reader reads a definition, axiom or quotient record against its context only at the
record's own references (`Ctx.keyAt`, and the literal blobs `Ctx.blob` finds there), at the
record's own member reference (`Ctx.memberKey`) and at its hint (`Ctx.hint`). So a reading
that succeeds in one context succeeds alike in any context that reads those references
alike wherever the first does (`RefsLe`) and agrees at the member reference
(`readRecord_le`). The compile-side reading theorems run in a context aligned with the
compile environment; this moves their readings to the reading context of a closure. -/

namespace Ix.Cert.RecordTransfer

open Ix.Kernel Ix.Kernel.Reader

variable {md : Mode}

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {v : β}
    (h : (x >>= f) = .ok v) : ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **The second context reads the record's references as the first does**, wherever the
first reads them: keys and literal blobs. -/
structure RefsLe (src : Ixon.Constant) (cx cx' : Ctx md) : Prop where
  keyAt : ∀ a ∈ src.refs, ∀ k, cx.keyAt a = .ok k → cx'.keyAt a = .ok k
  blob : ∀ a ∈ src.refs, ∀ b, cx.blob a = some b → cx'.blob a = some b

/-- Two sharing tables: every entry the first reads, the second reads alike. -/
def TblLe (tbl tbl' : Array (ReadM (CExpr md))) : Prop :=
  tbl.size = tbl'.size ∧ ∀ (i : Nat) (v : CExpr md), tbl[i]? = some (Except.ok v) → tbl'[i]? = some (Except.ok v)

theorem TblLe.push {tbl tbl' : Array (ReadM (CExpr md))} (h : TblLe tbl tbl')
    {x x' : ReadM (CExpr md)} (hx : ∀ v, x = .ok v → x' = .ok v) :
    TblLe (tbl.push x) (tbl'.push x') := by
  refine ⟨by simp [h.1], fun i v hi => ?_⟩
  rw [Array.getElem?_push] at hi ⊢
  rw [← h.1]
  by_cases hi' : i = tbl.size
  · simp only [hi', ↓reduceIte] at hi ⊢
    cases hi
    rw [hx v rfl]
  · simp only [hi', ↓reduceIte] at hi ⊢
    exact h.2 i v hi

section Expr

variable {cx cx' : Ctx md} {src : Ixon.Constant} (h : RefsLe src cx cx')
  (univs : Array CLevel) (self : Nat → Option (ReadM (CName md)))

include h in
theorem keyAt_le (i : UInt64) {k : CName md}
    (hk : ECx.keyAt ⟨cx, src, univs, self⟩ i = .ok k) : ECx.keyAt ⟨cx', src, univs, self⟩ i = .ok k := by
  unfold ECx.keyAt at hk ⊢
  cases ha : src.refs[i.toNat]? with
  | none => simp only [ha] at hk; cases hk
  | some a =>
    simp only [ha] at hk ⊢
    exact h.keyAt a (Array.mem_of_getElem? ha) k hk

include h in
theorem blobAt_le (i : UInt64) {b : ByteArray}
    (hb : ECx.blobAt ⟨cx, src, univs, self⟩ i = .ok b) : ECx.blobAt ⟨cx', src, univs, self⟩ i = .ok b := by
  unfold ECx.blobAt at hb ⊢
  cases ha : src.refs[i.toNat]? with
  | none => simp only [ha] at hb; cases hb
  | some a =>
    simp only [ha] at hb ⊢
    cases hblob : cx.blob a with
    | none => simp only [hblob] at hb; cases hb
    | some bytes =>
      simp only [hblob] at hb
      rw [h.blob a (Array.mem_of_getElem? ha) bytes hblob]
      exact hb

include h in
/-- **An expression read in the first context reads alike in the second.** -/
theorem convExpr_le {tbl tbl' : Array (ReadM (CExpr md))} (ht : TblLe tbl tbl') :
    ∀ (x : Ixon.Expr) (v : CExpr md), convExpr ⟨cx, src, univs, self⟩ tbl x = .ok v →
      convExpr ⟨cx', src, univs, self⟩ tbl' x = .ok v := by
  intro x
  induction x with
  | var i => intro v hv; exact hv
  | sort i => intro v hv; exact hv
  | recur i us => intro v hv; exact hv
  | ref i us =>
    intro v hv
    simp only [convExpr] at hv ⊢
    obtain ⟨k, hk, hv⟩ := bind_ok hv
    rw [keyAt_le h univs self i hk]
    exact hv
  | prj i field x ih =>
    intro v hv
    simp only [convExpr] at hv ⊢
    obtain ⟨k, hk, hv⟩ := bind_ok hv
    obtain ⟨w, hw, hv⟩ := bind_ok hv
    rw [keyAt_le h univs self i hk, ih w hw]
    exact hv
  | str i =>
    intro v hv
    simp only [convExpr] at hv ⊢
    obtain ⟨b, hb, hv⟩ := bind_ok hv
    rw [blobAt_le h univs self i hb]
    exact hv
  | nat i =>
    intro v hv
    simp only [convExpr] at hv ⊢
    obtain ⟨b, hb, hv⟩ := bind_ok hv
    rw [blobAt_le h univs self i hb]
    exact hv
  | app f a ihf iha =>
    intro v hv
    simp only [convExpr] at hv ⊢
    obtain ⟨w, hw, hv⟩ := bind_ok hv
    obtain ⟨u, hu, hv⟩ := bind_ok hv
    rw [ihf w hw, iha u hu]
    exact hv
  | lam c t b iht ihb =>
    intro v hv
    simp only [convExpr] at hv ⊢
    obtain ⟨w, hw, hv⟩ := bind_ok hv
    obtain ⟨u, hu, hv⟩ := bind_ok hv
    rw [iht w hw, ihb u hu]
    exact hv
  | all c r t b iht ihb =>
    intro v hv
    simp only [convExpr] at hv ⊢
    obtain ⟨w, hw, hv⟩ := bind_ok hv
    obtain ⟨u, hu, hv⟩ := bind_ok hv
    rw [iht w hw, ihb u hu]
    exact hv
  | letE c t x b iht ihx ihb =>
    intro v hv
    simp only [convExpr] at hv ⊢
    obtain ⟨w, hw, hv⟩ := bind_ok hv
    obtain ⟨u, hu, hv⟩ := bind_ok hv
    obtain ⟨z, hz, hv⟩ := bind_ok hv
    rw [iht w hw, ihx u hu, ihb z hz]
    exact hv
  | share i =>
    intro v hv
    simp only [convExpr] at hv ⊢
    cases hi : tbl[i.toNat]? with
    | none => simp only [hi] at hv; cases hv
    | some r =>
      simp only [hi] at hv
      subst hv
      rw [ht.2 _ _ hi]

end Expr

/-- The sharing table of a member reader, as a fold. -/
def tblFold (e : ECx md) (l : List Ixon.Expr) (tbl : Array (ReadM (CExpr md))) :
    Array (ReadM (CExpr md)) :=
  l.foldl (fun tbl entry => tbl.push (convExpr e tbl entry)) tbl

theorem mk'_eq (cx : Ctx md) (src : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) :
    MemberReader.mk' cx src param self =
      ⟨⟨cx, src, src.univs.map (convUniv param), self⟩,
        tblFold ⟨cx, src, src.univs.map (convUniv param), self⟩ src.sharing.toList
          (Array.mkEmpty src.sharing.size)⟩ := by
  simp only [MemberReader.mk', Id.run, tblFold, Array.forIn_pure_yield_eq_foldl, ← Array.foldl_toList]
  rfl

theorem tblFold_le {cx cx' : Ctx md} {src : Ixon.Constant} (h : RefsLe src cx cx')
    (univs : Array CLevel) (self : Nat → Option (ReadM (CName md))) :
    ∀ (l : List Ixon.Expr) {tbl tbl' : Array (ReadM (CExpr md))}, TblLe tbl tbl' →
      TblLe (tblFold ⟨cx, src, univs, self⟩ l tbl) (tblFold ⟨cx', src, univs, self⟩ l tbl')
  | [], _, _, ht => ht
  | x :: l, _, _, ht => by
    simp only [tblFold, List.foldl_cons]
    exact tblFold_le h univs self l (ht.push (convExpr_le h univs self ht x))

/-- **A member reader's readings carry over** to the second context. -/
theorem read_le {cx cx' : Ctx md} {src : Ixon.Constant} (h : RefsLe src cx cx')
    (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md))) (x : Ixon.Expr)
    {v : CExpr md} (hv : (MemberReader.mk' cx src param self).read x = .ok v) :
    (MemberReader.mk' cx' src param self).read x = .ok v := by
  rw [mk'_eq] at hv ⊢
  exact convExpr_le h _ self (tblFold_le h _ self _ ⟨rfl, fun _ _ h => h⟩) x v hv

/-- **A singleton record read in one context reads alike in another** that reads its
references alike wherever the first does and agrees at its member reference. -/
theorem readRecord_le {cx cx' : Ctx md} {st : State md} {owner : Address} {c : Ixon.Constant}
    (h : RefsLe c cx cx')
    (hkey : cx'.memberKey (.member owner 0) = cx.memberKey (.member owner 0))
    (hhint : cx'.hint (.member owner 0) = cx.hint (.member owner 0))
    (single : isSingleton c.info = true)
    {r : Read md} (hr : readRecord cx st owner c = .ok r) : readRecord cx' st owner c = .ok r := by
  cases hc : c.info with
  | defn d =>
    unfold readRecord at hr ⊢
    rw [hc] at hr ⊢
    simp only at hr ⊢
    obtain ⟨p, hp, hr⟩ := bind_ok hr
    unfold readDefinition at hp ⊢
    obtain ⟨name, hname, hp⟩ := bind_ok hp
    obtain ⟨ty, hty, hp⟩ := bind_ok hp
    obtain ⟨value, hvalue, hp⟩ := bind_ok hp
    rw [hkey, hname]
    rw [hname] at hty hvalue
    try simp only [bind, Except.bind]
    rw [read_le h id _ d.typ hty, read_le h id _ d.value hvalue, hhint]
    dsimp only
    rw [hp]
    exact hr
  | axio a =>
    unfold readRecord at hr ⊢
    rw [hc] at hr ⊢
    simp only at hr ⊢
    cases hu : a.isUnsafe
    · simp only [hu] at hr ⊢
      obtain ⟨name, hname, hr⟩ := bind_ok hr
      obtain ⟨ty, hty, hr⟩ := bind_ok hr
      rw [hkey, hname]
      try simp only [bind, Except.bind]
      rw [read_le h id _ a.typ hty]
      exact hr
    · simp only [hu] at hr; cases hr
  | quot q =>
    unfold readRecord at hr ⊢
    rw [hc] at hr ⊢
    simp only at hr ⊢
    obtain ⟨name, hname, hr⟩ := bind_ok hr
    obtain ⟨ty, hty, hr⟩ := bind_ok hr
    rw [hkey, hname]
    try simp only [bind, Except.bind]
    rw [read_le h id _ q.typ hty]
    exact hr
  | _ => rw [hc] at single; simp [isSingleton] at single

/--
info: 'Ix.Cert.RecordTransfer.readRecord_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms readRecord_le

end Ix.Cert.RecordTransfer
