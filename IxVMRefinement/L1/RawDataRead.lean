import IxVMRefinement.L1.RawDataDet

/-! # Scope-free agreement of raw conversion with the serialized expression reader

The reader and actual converted heap expose the same metadata-erased raw syntax, including
lets. No typing, variable closure or universe-parameter coverage premise is used.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open Ix.Kernel (Expr)

private theorem except_bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem val_cast_u56 {n : Nat} (h : n < 72057594037927936) :
    (n : F).val = n := ZMod.val_natCast_of_lt (by omega)

private theorem levels_read {ecx : Ix.Kernel.Reader.ECx .anon} {univs : List Ixon.Univ}
    (hunivs : ecx.univs = univs.toArray.map (Ix.Kernel.Reader.convUniv id))
    {idxs : Array UInt64} {levels : List KLevel}
    (read : idxs.toList.mapM (fun i => univs[i.toNat]?.map (Ix.Kernel.Reader.convUniv id)) =
      some levels) : ecx.levels idxs = .ok levels := by
  unfold Ix.Kernel.Reader.ECx.levels
  have go : ∀ (us : List UInt64) (ls : List KLevel),
      us.mapM (fun i => univs[i.toNat]?.map (Ix.Kernel.Reader.convUniv id)) = some ls →
      us.mapM ecx.level = .ok ls := by
    intro us
    induction us with
    | nil => intro ls eq; cases eq; rfl
    | cons u rest ih =>
      intro ls eq
      simp only [List.mapM_cons, Option.bind_eq_bind] at eq
      obtain ⟨head, headRead, later⟩ := Option.bind_eq_some_iff.mp eq
      obtain ⟨tail, tailRead, result⟩ := Option.bind_eq_some_iff.mp later
      have same := Option.some.inj result
      cases same
      obtain ⟨univ, univRead, rfl⟩ := Option.map_eq_some_iff.mp headRead
      have stored : ecx.univs[u.toNat]? = some (Ix.Kernel.Reader.convUniv id univ) := by
        rw [hunivs, Array.getElem?_map, List.getElem?_toArray, univRead]
        rfl
      have headValue : ecx.level u = .ok (Ix.Kernel.Reader.convUniv id univ) := by
        simp [Ix.Kernel.Reader.ECx.level, stored, pure, Except.pure]
      simp [List.mapM_cons, headValue, ih tail tailRead, bind, Except.bind, pure, Except.pure]
  exact go idxs.toList levels read

/-- Actual conversion agrees with the reader as physical data at every sharing-table bound. -/
theorem RawConvExpr.toRawData {κ : _root_.Address → KKey}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {ecx : Ix.Kernel.Reader.ECx .anon}
    (hrefs : ecx.src.refs.toList = refs)
    (hunivs : ecx.univs = univs.toArray.map (Ix.Kernel.Reader.convUniv id))
    (keyed : ∀ a k, ecx.cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → ecx.self i = some m → m = .ok k → k = κ a)
    (blobAgreement : ∀ a bs, (a, bs) ∈ blobs → ecx.cx.blob a = some bs)
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {p : SourceValue F}
    (converted : RawConvExpr refs recurAddrs univs sharing blobs h bound e p) :
    ∀ {n : Nat} {reader : KExpr}, n ≤ sharing.length → min bound sharing.length ≤ n →
      Ix.Kernel.Reader.convExpr ecx (buildShareTbl ecx (sharing.take n)) e = .ok reader →
      RawDataExpr κ h reader.eraseMeta p := by
  induction converted with
  | @var bound addr idx small cell =>
    intro n reader _ _ read
    simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq,
      Expr.mkBvar_eq] at read
    subst read
    have value := val_cast_u56 small
    rw [show (.bvar idx.toNat : KExpr).eraseMeta = .bvar idx.toNat from rfl, ← value]
    exact .bvar cell
  | @sort bound addr idx univ lp _ univRead level cell =>
    intro n reader _ _ read
    simp only [Ix.Kernel.Reader.convExpr] at read
    obtain ⟨u, levelRead, result⟩ := except_bind_eq_ok read
    injection result with same; subst same
    have stored : ecx.univs[idx.toNat]? = some (Ix.Kernel.Reader.convUniv id univ) := by
      rw [hunivs, Array.getElem?_map, List.getElem?_toArray, univRead]; rfl
    unfold Ix.Kernel.Reader.ECx.level at levelRead
    rw [stored] at levelRead
    injection levelRead with same
    cases same
    exact .sort cell level
  | @ref bound addr idx args a bytes ap params levels _ refRead addressEq address levelsRead levelsRep cell =>
    intro n reader _ _ read
    simp only [Ix.Kernel.Reader.convExpr] at read
    obtain ⟨key, keyRead, later⟩ := except_bind_eq_ok read
    obtain ⟨ls, readLevels, result⟩ := except_bind_eq_ok later
    injection result with same; subst same
    have keyEq : key = κ a := by
      unfold Ix.Kernel.Reader.ECx.keyAt at keyRead
      have stored : ecx.src.refs[idx.toNat]? = some a := by
        rw [← Array.getElem?_toList, hrefs, refRead]
      rw [stored] at keyRead
      exact keyed a key keyRead
    have levelsEq : ls = levels := Except.ok.inj (readLevels.symm.trans (levels_read hunivs levelsRead))
    subst keyEq levelsEq
    rw [← addressEq]
    exact .const cell address levelsRep
  | @recur bound addr idx args a bytes ap params levels _ recurRead addressEq address levelsRead levelsRep cell =>
    intro n reader _ _ read
    simp only [Ix.Kernel.Reader.convExpr] at read
    cases selfRead : ecx.self idx.toNat with
    | none => simp [selfRead, Ix.Kernel.Reader.malformed, throw, Except.error] at read
    | some action =>
      simp only [selfRead] at read
      obtain ⟨key, keyRead, later⟩ := except_bind_eq_ok read
      obtain ⟨ls, readLevels, result⟩ := except_bind_eq_ok later
      injection result with same; subst same
      have keyEq := selfKeyed idx.toNat a action key recurRead selfRead keyRead
      have levelsEq : ls = levels := Except.ok.inj (readLevels.symm.trans (levels_read hunivs levelsRead))
      subst keyEq levelsEq
      rw [← addressEq]
      exact .const cell address levelsRep
  | @prj bound addr tidx fidx inner a bytes ap ip _ indexSmall refRead addressEq address _ cell ih =>
    intro n reader tableBound sharingBound read
    simp only [Ix.Kernel.Reader.convExpr] at read
    obtain ⟨key, keyRead, later⟩ := except_bind_eq_ok read
    obtain ⟨child, childRead, result⟩ := except_bind_eq_ok later
    injection result with same; subst same
    have keyEq : key = κ a := by
      unfold Ix.Kernel.Reader.ECx.keyAt at keyRead
      have stored : ecx.src.refs[tidx.toNat]? = some a := by
        rw [← Array.getElem?_toList, hrefs, refRead]
      rw [stored] at keyRead
      exact keyed a key keyRead
    subst keyEq
    have indexValue := val_cast_u56 indexSmall
    change RawDataExpr κ h (.proj (κ a) fidx.toNat child.eraseMeta) _
    rw [← addressEq, ← indexValue]
    exact .proj cell address (ih tableBound sharingBound childRead)
  | @str bound addr idx a bytes string bp _ refRead member represented stringBytes cell =>
    intro n reader _ _ read
    simp only [Ix.Kernel.Reader.convExpr] at read
    obtain ⟨data, blobRead, result⟩ := except_bind_eq_ok read
    have sameBlob : data = ⟨bytes.toArray⟩ := by
      unfold Ix.Kernel.Reader.ECx.blobAt at blobRead
      have stored : ecx.src.refs[idx.toNat]? = some a := by
        rw [← Array.getElem?_toList, hrefs, refRead]
      rw [stored, blobAgreement a _ member] at blobRead
      injection blobRead with equal
      exact equal.symm
    subst sameBlob
    have stringRead : String.fromUTF8? ⟨bytes.toArray⟩ = some string := stringBytes
    rw [stringRead] at result
    injection result with same; subst same
    exact .litStr cell represented stringBytes
  | @nat bound addr idx a bytes limbs lp _ refRead member canonical represented _ value cell =>
    intro n reader _ _ read
    simp only [Ix.Kernel.Reader.convExpr] at read
    obtain ⟨number, numberRead, result⟩ := except_bind_eq_ok read
    injection result with same; subst same
    have numberEq : number = limbsVal limbs := by
      unfold Ix.Kernel.Reader.ECx.natAt Ix.Kernel.Reader.ECx.blobAt at numberRead
      have stored : ecx.src.refs[idx.toNat]? = some a := by
        rw [← Array.getElem?_toList, hrefs, refRead]
      rw [stored, blobAgreement a _ member] at numberRead
      simp only [bind, Except.bind, canonical, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at numberRead
      exact numberRead.symm.trans value.symm
    subst numberEq
    exact .litNat cell represented
  | @app bound addr f arg fp ap _ _ cell ihf iha =>
    intro n reader tableBound sharingBound read
    simp only [Ix.Kernel.Reader.convExpr] at read
    obtain ⟨func, funcRead, later⟩ := except_bind_eq_ok read
    obtain ⟨arg, argRead, result⟩ := except_bind_eq_ok later
    injection result with same; subst same
    exact .app cell (ihf tableBound sharingBound funcRead) (iha tableBound sharingBound argRead)
  | @lam bound addr ty body tp bp lp level _ _ _ cell iht ihb =>
    intro n reader tableBound sharingBound read
    simp only [Ix.Kernel.Reader.convExpr] at read
    obtain ⟨dom, domRead, later⟩ := except_bind_eq_ok read
    obtain ⟨body, bodyRead, result⟩ := except_bind_eq_ok later
    injection result with same; subst same
    exact .lam cell (iht tableBound sharingBound domRead) (ihb tableBound sharingBound bodyRead)
  | @all bound addr ty body tp bp lp level _ _ _ cell iht ihb =>
    intro n reader tableBound sharingBound read
    simp only [Ix.Kernel.Reader.convExpr] at read
    obtain ⟨dom, domRead, later⟩ := except_bind_eq_ok read
    obtain ⟨body, bodyRead, result⟩ := except_bind_eq_ok later
    injection result with same; subst same
    exact .forallE cell (iht tableBound sharingBound domRead) (ihb tableBound sharingBound bodyRead)
  | @letE bound addr nd md ty val body tp vp bp _ _ _ cell iht ihv ihb =>
    intro n reader tableBound sharingBound read
    simp only [Ix.Kernel.Reader.convExpr] at read
    obtain ⟨type, typeRead, second⟩ := except_bind_eq_ok read
    obtain ⟨value, valueRead, third⟩ := except_bind_eq_ok second
    obtain ⟨body, bodyRead, result⟩ := except_bind_eq_ok third
    injection result with same; subst same
    exact .letE cell (iht tableBound sharingBound typeRead) (ihv tableBound sharingBound valueRead)
      (ihb tableBound sharingBound bodyRead)
  | @share bound idx expr p small shared _ ih =>
    intro n reader tableBound sharingBound read
    have inSharing : idx.toNat < sharing.length := (List.getElem?_eq_some_iff.mp shared).1
    have inTable : idx.toNat < n := by omega
    simp only [Ix.Kernel.Reader.convExpr] at read
    rw [buildShareTbl_take_getElem? ecx sharing inTable shared] at read
    exact ih (Nat.le_of_lt inSharing) (Nat.min_le_left _ _) read

/-- The actual root conversion has exactly the unannotated reader's raw data. -/
theorem RawConvExpr.memberReader_rawData {κ : _root_.Address → KKey}
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobAgreement : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {e : Ixon.Expr} {p : SourceValue F} {reader : KExpr}
    (converted : RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e p)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read e = .ok reader) :
    RawDataExpr κ h reader.eraseMeta p := by
  obtain ⟨context, table⟩ := memberReader_mk'_eq cx src id self
  unfold Ix.Kernel.Reader.MemberReader.read at read
  rw [context, table, ← List.take_length (l := src.sharing.toList)] at read
  exact converted.toRawData rfl (by simp) keyed selfKeyed blobAgreement
    (Nat.le_refl _) (Nat.min_le_right _ _) read

end IxVM.Refinement.L1
