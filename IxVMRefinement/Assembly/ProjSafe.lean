import IxVMRefinement.Assembly.SubStore
import IxVMRefinement.Assembly.ClaimsL1L6
import IxVMRefinement.L1.Records
import IxVMRefinement.Lib.Words
import IxVMRefinement.Obs.KernelCheck12
import IxVMRefinement.Obs.KernelRoles2
import Ix.Cert.ReaderKeys
import IxC.Ixon.Verify.NonrecursiveConstant
import IxC.Ixon.Verify.TagN

/-! # Exact-codec projection canonicality, authentic keying, and safe-definition reading (`ProjSafe`)

Establishes the reader-side and expression-validation lemmas needed to run `readRecordBare` and
construct `L1.RecordReadsAs` over the sub-store `(E, order)`:

1. **Exact-codec projection canonicality (`deConstantExact_proj_eq_serConstant`)**:
   Whenever `Ixon.deConstantExact bytes = .ok c`, `emptyTables c = true`, and `c.info` is a
   projection variant (`.iPrj`, `.rPrj`, `.cPrj`, `.dPrj`), `bytes = Ixon.serConstant c` and
   `c.wireWF` holds — with zero canonicality hypothesis on `bytes`.
2. **Authentic exact-store keying & reconstruction (`AuthenticExactStore`)**:
   On any store where stored records sit at `Address.blake3Pure` of `deConstantExact`-decoded
   bytes, `resolve` is injective (`AuthenticExactStore.resolve_inj`), `cx.keyAt` agrees with
   `Core.keyOf t`, `cx.memberKey (.member a 0)` yields `Core.keyOf t a` on singletons, and
   `cx.memberKey (.member owner i)` yields `Core.keyOf t (Core.dprjAddr owner i)` on walked
   `.muts` definition blocks (even when `Core.dprjAddr owner i` is omitted from `order`).
3. **Expression reader & validation specs (`SafeRefsInputs`, `recurDeps`, `defOrder`,
   `validate_expr_well_scoped`)**:
   Proves `recParam_range`, `(recurDeps c d).toList = []` for safe definitions (`recurAddrs = []`),
   `defOrder deps = some (Array.range deps.size)` when all dependency sets are empty,
   `memberReader_read_ok_of_rawConvExpr`, and `validate_expr_well_scoped_spec` (using
   `RomBound.bounded_descent_lt` to rule out Goldilocks wraparound on binder depth `d + 1`). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Obs
open Ixon.Verify.Codec
open Ixon.Verify.Codec.Constant
open Ixon.Verify.Codec.ConstantTables
open Ixon.Verify.Codec.NonrecursiveConstant
open Ixon.Verify.TagN

/-! ## Section 1: Exact-codec projection canonicality (`deConstantExact_proj_eq_serConstant`) -/

/-- Whether an `Ixon.ConstantInfo` is one of the four projection variants. -/
def IsProjInfo : Ixon.ConstantInfo → Prop
  | .iPrj _ | .rPrj _ | .cPrj _ | .dPrj _ => True
  | _ => False

/-- Any record returned by `Ix.Cert.ReadingKeys.projectionAt` has empty tables and projection info. -/
theorem projectionAt_empty_and_proj {store : Ix.Kernel.Reader.Store}
    {q : Ix.Kernel.ConstRef _root_.Address} {c : Ixon.Constant}
    (hp : Ix.Cert.ReadingKeys.projectionAt store q = some c) :
    Ix.Cert.ReadingKeys.emptyTables c = true ∧ IsProjInfo c.info := by
  cases q with
  | ctor b i j =>
    simp only [Ix.Cert.ReadingKeys.projectionAt, Option.some.injEq] at hp
    subst hp
    exact ⟨rfl, trivial⟩
  | member b i =>
    simp only [Ix.Cert.ReadingKeys.projectionAt] at hp
    cases hm : Ix.Cert.ReadingKeys.memberAt store b i with
    | none => simp [hm] at hp
    | some mc =>
      cases mc <;> simp only [hm, Option.some.injEq] at hp <;> subst hp <;> exact ⟨rfl, trivial⟩

private theorem getBytes_consumed {len : Nat} {s s' : Ixon.GetState} {chunk : ByteArray}
    (h : Ixon.getBytes len s = .ok chunk s') :
    chunk.size = len ∧ Consumed s s' chunk := by
  unfold Ixon.getBytes at h
  change EStateM.bind EStateM.get _ s = _ at h
  simp only [EStateM.bind, EStateM.get] at h
  split at h
  · rename_i hle
    change EStateM.bind (EStateM.set _) _ s = _ at h
    simp only [EStateM.bind, EStateM.set, EStateM.pure] at h
    cases h
    have hsz : (s.bytes.extract s.idx (s.idx + len)).size = len := by
      rw [ByteArray.size_extract]
      omega
    exact ⟨hsz, ⟨by simp [hsz], by simp [hsz]⟩⟩
  · exact (throw_ok_false h).elim

private theorem map_ok_inv {α β : Type} {f : α → β} {x : Ixon.GetM α}
    {s s' : Ixon.GetState} {v : β}
    (h : (f <$> x) s = .ok v s') :
    ∃ a, x s = .ok a s' ∧ f a = v := by
  change EStateM.map f x s = _ at h
  unfold EStateM.map at h
  split at h
  · rename_i a s1 hrun
    cases h
    exact ⟨a, hrun, rfl⟩
  · cases h

private theorem getAddress_consumed {s s' : Ixon.GetState} {a : _root_.Address}
    (h : (Ixon.Serialize.get : Ixon.GetM _root_.Address) s = .ok a s') :
    AddressWireWF a ∧ Consumed s s' a.hash := by
  have hdef : (Ixon.Serialize.get : Ixon.GetM _root_.Address) = Address.mk <$> Ixon.getBytes 32 := rfl
  rw [hdef] at h
  obtain ⟨chunk, hbytes, rfl⟩ := map_ok_inv h
  exact getBytes_consumed hbytes

private theorem getInductiveProj_consumed {s s' : Ixon.GetState} {p : Ixon.InductiveProj}
    (h : Ixon.getInductiveProj s = .ok p s') :
    AddressWireWF p.block ∧ Consumed s s' (inductiveProjBytes p) := by
  unfold Ixon.getInductiveProj at h
  obtain ⟨t, s1, ht, h⟩ := bind_ok_inv h
  obtain ⟨blk, s2, hblk, h⟩ := bind_ok_inv h
  obtain ⟨rfl, rfl⟩ := pure_ok_inv h
  obtain ⟨hc1, hflag⟩ := getTagN_consumed 0 (.inl rfl) ht
  have hf0 : t.flag = 0 := UInt8.ext (by simp at hflag; omega)
  rw [hf0] at hc1
  obtain ⟨hwf, hc2⟩ := getAddress_consumed hblk
  exact ⟨hwf, hc1.trans hc2⟩

private theorem getRecursorProj_consumed {s s' : Ixon.GetState} {p : Ixon.RecursorProj}
    (h : Ixon.getRecursorProj s = .ok p s') :
    AddressWireWF p.block ∧ Consumed s s' (recursorProjBytes p) := by
  unfold Ixon.getRecursorProj at h
  obtain ⟨t, s1, ht, h⟩ := bind_ok_inv h
  obtain ⟨blk, s2, hblk, h⟩ := bind_ok_inv h
  obtain ⟨rfl, rfl⟩ := pure_ok_inv h
  obtain ⟨hc1, hflag⟩ := getTagN_consumed 0 (.inl rfl) ht
  have hf0 : t.flag = 0 := UInt8.ext (by simp at hflag; omega)
  rw [hf0] at hc1
  obtain ⟨hwf, hc2⟩ := getAddress_consumed hblk
  exact ⟨hwf, hc1.trans hc2⟩

private theorem getDefinitionProj_consumed {s s' : Ixon.GetState} {p : Ixon.DefinitionProj}
    (h : Ixon.getDefinitionProj s = .ok p s') :
    AddressWireWF p.block ∧ Consumed s s' (definitionProjBytes p) := by
  unfold Ixon.getDefinitionProj at h
  obtain ⟨t, s1, ht, h⟩ := bind_ok_inv h
  obtain ⟨blk, s2, hblk, h⟩ := bind_ok_inv h
  obtain ⟨rfl, rfl⟩ := pure_ok_inv h
  obtain ⟨hc1, hflag⟩ := getTagN_consumed 0 (.inl rfl) ht
  have hf0 : t.flag = 0 := UInt8.ext (by simp at hflag; omega)
  rw [hf0] at hc1
  obtain ⟨hwf, hc2⟩ := getAddress_consumed hblk
  exact ⟨hwf, hc1.trans hc2⟩

private theorem getConstructorProj_consumed {s s' : Ixon.GetState} {p : Ixon.ConstructorProj}
    (h : Ixon.getConstructorProj s = .ok p s') :
    AddressWireWF p.block ∧ Consumed s s' (constructorProjBytes p) := by
  unfold Ixon.getConstructorProj at h
  obtain ⟨t1, s1, ht1, h⟩ := bind_ok_inv h
  obtain ⟨t2, s2, ht2, h⟩ := bind_ok_inv h
  obtain ⟨blk, s3, hblk, h⟩ := bind_ok_inv h
  obtain ⟨rfl, rfl⟩ := pure_ok_inv h
  obtain ⟨hc1, hflag1⟩ := getTagN_consumed 0 (.inl rfl) ht1
  obtain ⟨hc2, hflag2⟩ := getTagN_consumed 0 (.inl rfl) ht2
  have hf1 : t1.flag = 0 := UInt8.ext (by simp at hflag1; omega)
  have hf2 : t2.flag = 0 := UInt8.ext (by simp at hflag2; omega)
  rw [hf1] at hc1
  rw [hf2] at hc2
  obtain ⟨hwf, hc3⟩ := getAddress_consumed hblk
  exact ⟨hwf, (hc1.trans hc2).trans hc3⟩

private theorem getMany_for_zero {α : Type} (getm : Ixon.GetM α) :
    getMany getm 0 = pure #[] := by
  rfl

private theorem getMany_empty_inv {α : Type} {getm : Ixon.GetM α} {count : Nat}
    {s s' : Ixon.GetState}
    (h : getMany getm count s = .ok #[] s') :
    count = 0 ∧ s' = s := by
  cases count with
  | zero =>
    obtain ⟨_, hs⟩ := pure_ok_inv h
    exact ⟨rfl, hs⟩
  | succ n =>
    rw [getMany_succ_head] at h
    obtain ⟨v, s1, _, h⟩ := bind_ok_inv h
    obtain ⟨vs, s2, _, h⟩ := bind_ok_inv h
    obtain ⟨heq, _⟩ := pure_ok_inv h
    have hsz := congrArg Array.size heq
    simp at hsz

private theorem getTag0_zero_consumed {s s' : Ixon.GetState} {t : Ixon.TagN}
    (ht : Ixon.getTagN 0 s = .ok t s') (hv : t.value.toNat = 0) :
    Consumed s s' (tag0Bytes 0) := by
  obtain ⟨hc, hflag⟩ := getTagN_consumed 0 (.inl rfl) ht
  have hf0 : t.flag = 0 := UInt8.ext (by simp at hflag; omega)
  have hv0 : t.value = 0 := UInt64.ext hv
  rw [hf0, hv0] at hc
  exact hc

private theorem getConstantInfo_proj_consumed {s s' : Ixon.GetState} {info : Ixon.ConstantInfo}
    (h : Ixon.getConstantInfo s = .ok info s') (hproj : IsProjInfo info) :
    NonrecursiveInfoWireWF info ∧ Consumed s s' (nonrecursiveInfoBytes info) := by
  rw [getConstantInfo_eq] at h
  obtain ⟨tag, s1, htag, hinfo⟩ := bind_ok_inv h
  obtain ⟨hc_tag, _⟩ := getTagN_consumed 4 (.inr (.inr rfl)) htag
  unfold getInfoFromTag at hinfo
  by_cases hmuts : tag.flag == Ixon.Constant.FLAG_MUTS
  · simp only [hmuts, ↓reduceIte] at hinfo
    change (getMany Ixon.getMutConst tag.value.toNat >>= fun ms => pure (.muts ms)) s1 = _ at hinfo
    obtain ⟨ms, s2, _, hpure⟩ := bind_ok_inv hinfo
    obtain ⟨rfl, _⟩ := pure_ok_inv hpure
    exact False.elim hproj
  · simp only [hmuts, Bool.false_eq_true, ↓reduceIte] at hinfo
    by_cases hflag : tag.flag == Ixon.Constant.FLAG
    · have hfeq : tag.flag = Ixon.Constant.FLAG := beq_iff_eq.mp hflag
      rw [hfeq] at hc_tag
      simp only [hflag, ↓reduceIte] at hinfo
      match hv : tag.value with
      | 0 =>
        rw [hv] at hinfo
        obtain ⟨_, _, rfl⟩ := map_ok_inv hinfo
        exact False.elim hproj
      | 1 =>
        rw [hv] at hinfo
        obtain ⟨_, _, rfl⟩ := map_ok_inv hinfo
        exact False.elim hproj
      | 2 =>
        rw [hv] at hinfo
        obtain ⟨_, _, rfl⟩ := map_ok_inv hinfo
        exact False.elim hproj
      | 3 =>
        rw [hv] at hinfo
        obtain ⟨_, _, rfl⟩ := map_ok_inv hinfo
        exact False.elim hproj
      | 4 =>
        rw [hv] at hinfo hc_tag
        obtain ⟨p, hp, rfl⟩ := map_ok_inv hinfo
        obtain ⟨hwf, hc_p⟩ := getConstructorProj_consumed hp
        exact ⟨.cPrj hwf, hc_tag.trans hc_p⟩
      | 5 =>
        rw [hv] at hinfo hc_tag
        obtain ⟨p, hp, rfl⟩ := map_ok_inv hinfo
        obtain ⟨hwf, hc_p⟩ := getRecursorProj_consumed hp
        exact ⟨.rPrj hwf, hc_tag.trans hc_p⟩
      | 6 =>
        rw [hv] at hinfo hc_tag
        obtain ⟨p, hp, rfl⟩ := map_ok_inv hinfo
        obtain ⟨hwf, hc_p⟩ := getInductiveProj_consumed hp
        exact ⟨.iPrj hwf, hc_tag.trans hc_p⟩
      | 7 =>
        rw [hv] at hinfo hc_tag
        obtain ⟨p, hp, rfl⟩ := map_ok_inv hinfo
        obtain ⟨hwf, hc_p⟩ := getDefinitionProj_consumed hp
        exact ⟨.dPrj hwf, hc_tag.trans hc_p⟩
      | v + 8 =>
        have hbad : match tag.value with
            | 0 => Ixon.ConstantInfo.defn <$> Ixon.getDefinition
            | 1 => Ixon.ConstantInfo.recr <$> Ixon.getRecursor
            | 2 => Ixon.ConstantInfo.axio <$> Ixon.getAxiom
            | 3 => Ixon.ConstantInfo.quot <$> Ixon.getQuotient
            | 4 => Ixon.ConstantInfo.cPrj <$> Ixon.getConstructorProj
            | 5 => Ixon.ConstantInfo.rPrj <$> Ixon.getRecursorProj
            | 6 => Ixon.ConstantInfo.iPrj <$> Ixon.getInductiveProj
            | 7 => Ixon.ConstantInfo.dPrj <$> Ixon.getDefinitionProj
            | v => throw s!"getConstantInfo: invalid variant {v}" =
            throw s!"getConstantInfo: invalid variant {tag.value}" := by
          have hne0 : tag.value ≠ 0 := by rw [hv]; decide
          have hne1 : tag.value ≠ 1 := by rw [hv]; decide
          have hne2 : tag.value ≠ 2 := by rw [hv]; decide
          have hne3 : tag.value ≠ 3 := by rw [hv]; decide
          have hne4 : tag.value ≠ 4 := by rw [hv]; decide
          have hne5 : tag.value ≠ 5 := by rw [hv]; decide
          have hne6 : tag.value ≠ 6 := by rw [hv]; decide
          have hne7 : tag.value ≠ 7 := by rw [hv]; decide
          split <;> contradiction <;> rfl
        rw [hbad] at hinfo
        exact (throw_ok_false hinfo).elim
    · simp only [hflag, Bool.false_eq_true, ↓reduceIte] at hinfo
      exact (throw_ok_false hinfo).elim

private theorem getBinders_empty_consumed {s s' : Ixon.GetState}
    (h : Ixon.getBinders s = .ok #[] s') :
    Consumed s s' (bindersBytes #[]) := by
  unfold Ixon.getBinders at h
  obtain ⟨t, s1, ht, harr⟩ := bind_ok_inv h
  rw [← getMany_eq_getArray] at harr
  obtain ⟨hz, rfl⟩ := getMany_empty_inv harr
  have hc := getTag0_zero_consumed ht hz
  simpa [bindersBytes, listBytes, ByteArray.append_empty] using hc

private theorem getConstantAfterInfo_empty_consumed {info : Ixon.ConstantInfo}
    {s s' : Ixon.GetState}
    (h : getConstantAfterInfo info s = .ok ⟨info, #[], #[], #[], #[]⟩ s') :
    Consumed s s'
      (tag0Bytes 0 ++ tag0Bytes 0 ++ tag0Bytes 0 ++ bindersBytes #[]) := by
  unfold getConstantAfterInfo at h
  obtain ⟨tSh, s1, htSh, h⟩ := bind_ok_inv h
  change (getMany Ixon.getExpr tSh.value.toNat >>= getConstantRefs info) s1 = _ at h
  obtain ⟨sh, s2, hsh, h⟩ := bind_ok_inv h
  unfold getConstantRefs at h
  obtain ⟨tRf, s3, htRf, h⟩ := bind_ok_inv h
  change (getMany Ixon.Serialize.get tRf.value.toNat >>= getConstantUnivs info sh) s3 = _ at h
  obtain ⟨rf, s4, hrf, h⟩ := bind_ok_inv h
  unfold getConstantUnivs at h
  obtain ⟨tUn, s5, htUn, h⟩ := bind_ok_inv h
  change (getMany Ixon.getUniv tUn.value.toNat >>= fun un => do
      let bnd ← Ixon.getBinders
      return (⟨info, sh, rf, un, bnd⟩ : Ixon.Constant)) s5 = _ at h
  obtain ⟨un, s6, hun, h⟩ := bind_ok_inv h
  obtain ⟨bnd, s7, hbnd, hpure⟩ := bind_ok_inv h
  obtain ⟨heq, rfl⟩ := pure_ok_inv hpure
  cases heq
  obtain ⟨hzSh, rfl⟩ := getMany_empty_inv hsh
  obtain ⟨hzRf, rfl⟩ := getMany_empty_inv hrf
  obtain ⟨hzUn, rfl⟩ := getMany_empty_inv hun
  have hc1 := getTag0_zero_consumed htSh hzSh
  have hc2 := getTag0_zero_consumed htRf hzRf
  have hc3 := getTag0_zero_consumed htUn hzUn
  have hc4 := getBinders_empty_consumed hbnd
  exact ((hc1.trans hc2).trans hc3).trans hc4

/-- **Exact-codec projection canonicality**: any byte array `bytes` that `Ixon.deConstantExact`
decodes to a projection record `c` with `emptyTables c = true` is byte-for-byte equal to
`Ixon.serConstant c` and satisfies `c.wireWF`. -/
theorem deConstantExact_proj_eq_serConstant {bytes : ByteArray} {c : Ixon.Constant}
    (hdec : Ixon.deConstantExact bytes = .ok c)
    (hemp : Ix.Cert.ReadingKeys.emptyTables c = true)
    (hproj : IsProjInfo c.info) :
    bytes = Ixon.serConstant c ∧ c.wireWF := by
  have hc_eq := Ix.Cert.ReadingKeys.empty_constant hemp
  rw [hc_eq] at hdec ⊢
  unfold Ixon.deConstantExact Ixon.runGetExact at hdec
  split at hdec
  · rename_i val st hrun
    split at hdec
    · rename_i hidx
      cases hdec
      change Ixon.getConstant { bytes := bytes, idx := 0 } = .ok ⟨c.info, #[], #[], #[], #[]⟩ st at hrun
      rw [getConstant_eq] at hrun
      obtain ⟨info', s1, hinfo, htail⟩ := bind_ok_inv hrun
      have hinfo_eq : info' = c.info := by
        unfold getConstantAfterInfo at htail
        obtain ⟨_, _, _, h1⟩ := bind_ok_inv htail
        obtain ⟨_, _, _, h2⟩ := bind_ok_inv h1
        unfold getConstantRefs at h2
        obtain ⟨_, _, _, h3⟩ := bind_ok_inv h2
        obtain ⟨_, _, _, h4⟩ := bind_ok_inv h3
        unfold getConstantUnivs at h4
        obtain ⟨_, _, _, h5⟩ := bind_ok_inv h4
        obtain ⟨_, _, _, h6⟩ := bind_ok_inv h5
        obtain ⟨_, _, _, hp⟩ := bind_ok_inv h6
        obtain ⟨he, _⟩ := pure_ok_inv hp
        cases he
        rfl
      subst hinfo_eq
      obtain ⟨hwf_info, hc_info⟩ := getConstantInfo_proj_consumed hinfo hproj
      have hc_tail := getConstantAfterInfo_empty_consumed htail
      have hc_all := hc_info.trans hc_tail
      have hwf_nonrec : NonrecursiveConstantWireWF ⟨c.info, #[], #[], #[], #[]⟩ :=
        { info := hwf_info
          sharingCount := by decide
          sharingEntries := fun _ hm => nomatch hm
          refsCount := by decide
          refsEntries := fun _ hm => nomatch hm
          univsCount := by decide
          univsEntries := fun _ hm => nomatch hm
          binders := ⟨by decide, fun _ hm => nomatch hm⟩ }
      have hser : Ixon.serConstant ⟨c.info, #[], #[], #[], #[]⟩ =
          nonrecursiveConstantBytes ⟨c.info, #[], #[], #[], #[]⟩ := by
        unfold Ixon.serConstant
        exact (putConstant_writes_nonrecursive _ hwf_nonrec).runPut
      have hbytes_eq :
          nonrecursiveConstantBytes ⟨c.info, #[], #[], #[], #[]⟩ =
            nonrecursiveInfoBytes c.info ++
              (tag0Bytes 0 ++ tag0Bytes 0 ++ tag0Bytes 0 ++ bindersBytes #[]) := by
        simp [nonrecursiveConstantBytes, listBytes, ByteArray.append_empty, ByteArray.append_assoc]
      obtain ⟨hst, hextr⟩ := hc_all
      subst hst
      simp only [Nat.zero_add] at hidx hextr
      have hbs : bytes =
          nonrecursiveInfoBytes c.info ++
            (tag0Bytes 0 ++ tag0Bytes 0 ++ tag0Bytes 0 ++ bindersBytes #[]) := by
        rw [← hextr, hidx, ByteArray.extract_zero_size]
      have hwf_c : (⟨c.info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
        rw [L1.emptyTablesConstant_wireWF]
        cases hwf_info with
        | defn _ _ => exact False.elim hproj
        | axio _ => exact False.elim hproj
        | quot _ => exact False.elim hproj
        | cPrj hb => exact hb
        | rPrj hb => exact hb
        | iPrj hb => exact hb
        | dPrj hb => exact hb
      exact ⟨hbs.trans (hbytes_eq.symm.trans hser.symm), hwf_c⟩
    · cases hdec
  · cases hdec

/-! ## Section 2: `AuthenticExactStore` keying & reconstruction (`streamContext`) -/

/-- Store invariant requiring only `Address.blake3Pure` + `Ixon.deConstantExact` (never
`Canonical.deConstant` or `serConstant` round-tripping on arbitrary records). -/
def AuthenticExactStore (store : Ix.Kernel.Reader.Store) : Prop :=
  ∀ a c, store a = some c →
    ∃ bytes, _root_.Address.blake3Pure bytes = a ∧ Ixon.deConstantExact bytes = .ok c

/-- **Unconditional resolution injectivity on any `AuthenticExactStore`**: singletons resolve only
to themselves, and projections decode uniquely to their canonical bytes via
`deConstantExact_proj_eq_serConstant`. -/
theorem AuthenticExactStore.resolve_inj {store : Ix.Kernel.Reader.Store}
    (hauth : AuthenticExactStore store)
    {a a' : _root_.Address} {q : Ix.Kernel.ConstRef _root_.Address}
    (h : Ix.Kernel.Reader.resolve store a = some q)
    (h' : Ix.Kernel.Reader.resolve store a' = some q) :
    a' = a := by
  refine resolve_inj_of_proj_authentic h h' (fun c hproj => ?_)
  obtain ⟨hemp, hp⟩ := projectionAt_empty_and_proj hproj
  rw [_root_.Address.admissionHash_eq]
  refine ⟨fun ha => ?_, fun ha' => ?_⟩
  · obtain ⟨bytes, hbl, hdec⟩ := hauth a c ha
    obtain ⟨hbs, _⟩ := deConstantExact_proj_eq_serConstant hdec hemp hp
    rw [← hbs, hbl]
  · obtain ⟨bytes, hbl, hdec⟩ := hauth a' c ha'
    obtain ⟨hbs, _⟩ := deConstantExact_proj_eq_serConstant hdec hemp hp
    rw [← hbs, hbl]

/-- Characterization of `Core.keyOf t a` when `t.check = .ok ()`: role-bound iff `(r, a) ∈ t.bound`. -/
theorem keyOf_eq_of_bound {t : Ix.Kernel.RoleTable} (hchk : t.check = .ok ())
    {r : Ix.Kernel.Role} {a : _root_.Address}
    (hmem : (r, a) ∈ t.bound.toList) :
    Core.keyOf t a = .role r := by
  unfold Core.keyOf
  rw [← List.find?_toList]
  have hex : ∃ p ∈ t.bound.toList, (p.2 == a) = true := ⟨(r, a), hmem, beq_self_eq_true a⟩
  cases hfind : t.bound.toList.find? (·.2 == a) with
  | none =>
    have hall := List.find?_eq_none.mp hfind
    exact absurd (beq_self_eq_true a) (hall (r, a) hmem)
  | some p =>
    rcases p with ⟨r', a'⟩
    have hp_mem := List.mem_of_find?_eq_some hfind
    have hp_eq : a' = a := beq_iff_eq.mp (List.find?_some hfind)
    have hpair := Ix.Kernel.RoleTable.eq_of_nodup_map_snd
      (Ix.Kernel.RoleTable.check_nodup hchk).2 hmem hp_mem hp_eq.symm
    injection hpair with hr_eq _
    rw [hr_eq]

/-- Characterization of `Core.keyOf t a` when `a` is unbound in `t.bound`. -/
theorem keyOf_eq_of_unbound {t : Ix.Kernel.RoleTable} {a : _root_.Address}
    (hunb : ∀ r, (r, a) ∉ t.bound.toList) :
    Core.keyOf t a = .id a := by
  unfold Core.keyOf
  rw [← List.find?_toList]
  cases hfind : t.bound.toList.find? (·.2 == a) with
  | none => rfl
  | some p =>
    rcases p with ⟨r, a'⟩
    have hp_mem := List.mem_of_find?_eq_some hfind
    have hp_eq : a' = a := beq_iff_eq.mp (List.find?_some hfind)
    subst hp_eq
    exact absurd hp_mem (hunb r)

/-- Every address `a` satisfies `AddressKey b a (Core.keyOf t a)` under an admitted binding `b`. -/
theorem addressKey_keyOf {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (a : _root_.Address) :
    IxVM.Refinement.AddressKey b a (Core.keyOf t a) := by
  have hba := (Ix.Kernel.Admission.admitBinding_ok_iff _root_.Address.admissionHash b t).mp hadm
  have hofBytes : Ix.Kernel.RoleTable.ofBytes b.bytes = some t :=
    (Ix.Kernel.RoleTable.ofBytes_eq_some_iff b.bytes t).mpr hba.canonical
  unfold Core.keyOf
  rw [← List.find?_toList]
  cases hfind : t.bound.toList.find? (·.2 == a) with
  | none => exact Or.inl rfl
  | some p =>
    rcases p with ⟨r, a'⟩
    have hp_mem := List.mem_of_find?_eq_some hfind
    have hp_eq : a' = a := beq_iff_eq.mp (List.find?_some hfind)
    subst hp_eq
    exact Or.inr ⟨t, r, hofBytes,
      Ix.Cert.ReadingKeys.addressOf_of_bound hba.wellFormed hp_mem, rfl⟩

/-- On an `AuthenticExactStore`, `keyOfAddress` at any resolving address `a` equals `Core.keyOf t a`. -/
theorem keyOfAddress_eq_keyOf {store : Ix.Kernel.Reader.Store} {t : Ix.Kernel.RoleTable}
    (hauth : AuthenticExactStore store) (hchk : t.check = .ok ())
    {a : _root_.Address} {q : Ix.Kernel.ConstRef _root_.Address}
    (hres : Ix.Kernel.Reader.resolve store a = some q) :
    Ix.Kernel.Reader.keyOfAddress store (Ix.Kernel.Reader.bindingsOf (md := .anon) store t) a =
      some (Core.keyOf t a) := by
  have hinj : ∀ a', Ix.Kernel.Reader.resolve store a' = some q → a' = a :=
    fun _ h' => hauth.resolve_inj hres h'
  by_cases hbound : ∃ r, (r, a) ∈ t.bound.toList
  · obtain ⟨r, hmem⟩ := hbound
    have hbind := Ix.Cert.ReadingKeys.bindings_bound hchk hmem hres hinj
    rw [keyOf_eq_of_bound hchk hmem]
    simp [Ix.Kernel.Reader.keyOfAddress, hres, hbind]
  · have hunb : ∀ r, (r, a) ∉ t.bound.toList := fun r hm => hbound ⟨r, hm⟩
    have hbind := Ix.Cert.ReadingKeys.bindings_unbound (t := t) hunb hinj
    rw [keyOf_eq_of_unbound hunb]
    simp [Ix.Kernel.Reader.keyOfAddress, hres, hbind, Ix.Kernel.Mode.addressId?]

/-- On `streamContext` with an `AuthenticExactStore`, any resolving address `a` reads via
`cx.keyAt a` as `.ok (Core.keyOf t a)`. -/
theorem streamContext_keyAt_eq_keyOf {t : Ix.Kernel.RoleTable}
    {pre : Ix.Kernel.Reader.Prelude .anon}
    {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store)
    (hchk : t.check = .ok ())
    {a : _root_.Address} {q : Ix.Kernel.ConstRef _root_.Address}
    (hres : Ix.Kernel.Reader.resolve
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
      a = some q) :
    (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).keyAt a =
      .ok (Core.keyOf t a) := by
  let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint
  have hkoa := keyOfAddress_eq_keyOf hauth hchk hres
  have hroles : cx.roles = Ix.Kernel.Reader.bindingsOf cx.store t := rfl
  rw [← hroles] at hkoa
  exact Ix.Kernel.Reader.Ctx.keyAt_eq_ok hkoa

/-- Inverse of `cx.keyAt`: on `streamContext` with an `AuthenticExactStore`, any `cx.keyAt a = .ok k`
forces `k = Core.keyOf t a` (directly discharging `L1.RecordReadsAs`'s `hkey` condition). -/
theorem streamContext_keyAt_ok_inv {t : Ix.Kernel.RoleTable}
    {pre : Ix.Kernel.Reader.Prelude .anon}
    {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store)
    (hchk : t.check = .ok ())
    {a : _root_.Address} {k : Core.KKey}
    (hk : (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).keyAt a =
      .ok k) :
    k = Core.keyOf t a := by
  let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint
  have hroles : cx.roles = Ix.Kernel.Reader.bindingsOf cx.store t := rfl
  unfold Ix.Kernel.Reader.Ctx.keyAt at hk
  cases hby : cx.keys.byAddress[a]? with
  | some k' =>
    rw [hby] at hk
    injection hk with hkk
    subst hkk
    have hsnd := cx.keys.byAddress_sound a k' hby
    cases hres : Ix.Kernel.Reader.resolve cx.store a with
    | none => simp [Ix.Kernel.Reader.keyOfAddress, hres] at hsnd
    | some q =>
      have hkoa := keyOfAddress_eq_keyOf hauth hchk hres
      rw [← hroles] at hkoa
      exact Option.some.inj (hsnd.symm.trans hkoa)
  | none =>
    rw [hby] at hk
    cases hres : Ix.Kernel.Reader.resolve cx.store a with
    | none => simp [hres, Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at hk
    | some q =>
      have hk_full := streamContext_keyAt_eq_keyOf hauth hchk hres
      unfold Ix.Kernel.Reader.Ctx.keyAt at hk_full
      rw [hby] at hk_full
      exact Except.ok.inj (hk.symm.trans hk_full)

/-- On `streamContext` with an `AuthenticExactStore`, any singleton record (`defn`, `recr`, `axio`,
`quot`) at `a` in `cx.store` keys `.member a 0` via `cx.memberKey` as `.ok (Core.keyOf t a)`. -/
theorem streamContext_memberKey_singleton {t : Ix.Kernel.RoleTable}
    {pre : Ix.Kernel.Reader.Prelude .anon}
    {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store)
    (hchk : t.check = .ok ())
    {a : _root_.Address} {c : Ixon.Constant}
    (hc : (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store a =
      some c)
    (hsing : match c.info with | .defn _ | .recr _ | .axio _ | .quot _ => True | _ => False) :
    (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).memberKey
      (.member a 0) = .ok (Core.keyOf t a) := by
  let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint
  have hres : Ix.Kernel.Reader.resolve cx.store a = some (.member a 0) :=
    resolve_singleton hc hsing
  have hinj : ∀ a', Ix.Kernel.Reader.resolve cx.store a' = some (.member a 0) → a' = a :=
    fun _ h' => hauth.resolve_inj hres h'
  have hroles : cx.roles = Ix.Kernel.Reader.bindingsOf cx.store t := rfl
  by_cases hbound : ∃ r, (r, a) ∈ t.bound.toList
  · obtain ⟨r, hmem⟩ := hbound
    have hbind := Ix.Cert.ReadingKeys.bindings_bound hchk hmem hres hinj
    rw [keyOf_eq_of_bound hchk hmem]
    unfold Ix.Kernel.Reader.Ctx.memberKey
    rw [show cx.roles = Ix.Kernel.Reader.bindingsOf cx.store t from rfl, hbind]
    rfl
  · have hunb : ∀ r, (r, a) ∉ t.bound.toList := fun r hm => hbound ⟨r, hm⟩
    have hbind := Ix.Cert.ReadingKeys.bindings_unbound (t := t) hunb hinj
    rw [keyOf_eq_of_unbound hunb]
    have ha_of : cx.addressOf (.member a 0) = .ok a := by
      unfold Ix.Kernel.Reader.Ctx.addressOf
      cases haddr : cx.keys.address[Ix.Kernel.ConstRef.member a 0]? with
      | some a' =>
        have hsnd := cx.keys.address_sound (.member a 0) a' haddr
        rw [hinj a' hsnd]
        rfl
      | none =>
        have hsing_at : Ix.Kernel.Reader.singletonAt cx.store (.member a 0) = some a := by
          unfold Ix.Kernel.Reader.singletonAt
          rw [hc]
          cases hinfo : c.info <;> simp [hinfo] at hsing ⊢
        rw [hsing_at]
        rfl
    unfold Ix.Kernel.Reader.Ctx.memberKey
    rw [show cx.roles = Ix.Kernel.Reader.bindingsOf cx.store t from rfl, hbind]
    simp only [ha_of, bind, Except.bind]
    cases hby : cx.keys.byAddress[a]? with
    | none => rfl
    | some v =>
      have hsnd := cx.keys.byAddress_sound a v hby
      have hkoa := keyOfAddress_eq_keyOf hauth hchk hres
      rw [keyOf_eq_of_unbound hunb] at hkoa
      have hv : v = .id a := Option.some.inj (hsnd.symm.trans hkoa)
      rw [hv]
      rfl

/-- `projectionAddress` at `.member owner i` for a definition member `i < UInt64.size` yields
`some (Core.dprjAddr owner i)`. -/
theorem projectionAddress_dprj {store : Ix.Kernel.Reader.Store}
    {owner : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {i : Nat} {d : Ixon.Definition}
    (hcb : store owner = some cb) (hinfo : cb.info = .muts ms)
    (hms : ms[i]? = some (.defn d)) (hi : i < UInt64.size) :
    Ix.Kernel.Admission.projectionAddress _root_.Address.admissionHash store (.member owner i) =
      some (Core.dprjAddr owner i) := by
  have hi_toNat : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt hi
  have hpr : Ix.Kernel.Egress.ProjectionReads
      ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ .definition (.member owner i) := by
    rw [← hi_toNat]
    exact Ix.Kernel.Egress.ProjectionReads.definition ⟨i.toUInt64, owner⟩
  have hwp := Ix.Kernel.Egress.writeProjection_of_reading hpr
  unfold Ix.Kernel.Admission.projectionAddress
  simp [hcb, hinfo, hms, hwp, Except.toOption, _root_.Address.admissionHash_eq,
    Core.dprjAddr, Core.projAddr]

/-- On `streamContext` with an `AuthenticExactStore`, a definition member `.member owner i` of a
mutual block `cb` at `owner` keys via `cx.memberKey` as `.ok (Core.keyOf t (Core.dprjAddr owner i))`,
provided every bound address of `t` is stored in `cx.store` and any record stored at
`Core.dprjAddr owner i` in `cx.store` is the `.dPrj` projection record. -/
theorem streamContext_memberKey_dprj {t : Ix.Kernel.RoleTable}
    {pre : Ix.Kernel.Reader.Prelude .anon}
    {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store)
    (hchk : t.check = .ok ())
    {owner : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {i : Nat} {d : Ixon.Definition}
    (hcb : (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
      owner = some cb)
    (hinfo : cb.info = .muts ms)
    (hms : ms[i]? = some (.defn d))
    (hi : i < UInt64.size)
    (hbound_stored : ∀ r a_b, (r, a_b) ∈ t.bound.toList →
      ∃ c_b, (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
        a_b = some c_b)
    (hdprj_eq : ∀ c',
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
        (Core.dprjAddr owner i) = some c' →
      c' = ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩) :
    (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).memberKey
      (.member owner i) = .ok (Core.keyOf t (Core.dprjAddr owner i)) := by
  let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint
  let c_proj : Ixon.Constant := ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩
  have hi_toNat : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt hi
  have hres_proj : ∀ {a' : _root_.Address}, cx.store a' = some c_proj →
      Ix.Kernel.Reader.resolve cx.store a' = some (.member owner i) := by
    intro a' ha'
    unfold Ix.Kernel.Reader.resolve Ix.Kernel.Reader.resolveSource
    simp [ha', c_proj, Ix.Cert.ReadingKeys.emptyTables, hcb, hinfo, hi_toNat, hms]
  have hres_inv : ∀ {a' : _root_.Address},
      Ix.Kernel.Reader.resolve cx.store a' = some (.member owner i) →
      a' = Core.dprjAddr owner i := by
    intro a' ha'
    unfold Ix.Kernel.Reader.resolve at ha'
    obtain ⟨c', hc', hsrc⟩ := Option.bind_eq_some_iff.mp ha'
    rcases Ix.Cert.ReadingKeys.resolveSource_cases hsrc with ⟨heq, hns⟩ | hpat
    · injection heq with hown _
      subst hown
      rw [hc'] at hcb
      injection hcb with hcc
      subst hcc
      exact absurd hinfo (hns ms)
    · simp only [Ix.Cert.ReadingKeys.projectionAt, Ix.Cert.ReadingKeys.memberAt,
        hcb, hinfo, hms, Option.some.injEq] at hpat
      subst hpat
      obtain ⟨bytes, hbl, hdec⟩ := hauth a' c_proj hc'
      obtain ⟨hbs, _⟩ := deConstantExact_proj_eq_serConstant hdec rfl trivial
      rw [← hbs] at hbl
      exact hbl.symm
  have hroles : cx.roles = Ix.Kernel.Reader.bindingsOf cx.store t := rfl
  cases hrole : cx.roles.names[Ix.Kernel.ConstRef.member owner i]? with
  | some k =>
    obtain ⟨r, rfl⟩ := Ix.Cert.ReaderUnits.bindingsOf_keyed cx.store t (.member owner i) k
      (by rwa [← hroles])
    obtain ⟨a', hmem', hres'⟩ := Ix.Cert.ReaderKeys.bindings_role_origin cx.store t
      (by rwa [← hroles])
    have ha'_eq := hres_inv hres'
    subst ha'_eq
    rw [keyOf_eq_of_bound hchk hmem']
    unfold Ix.Kernel.Reader.Ctx.memberKey
    rw [hrole]
    rfl
  | none =>
    have hunb : ∀ r, (r, Core.dprjAddr owner i) ∉ t.bound.toList := by
      intro r hm
      obtain ⟨c_b, hc_b⟩ := hbound_stored r (Core.dprjAddr owner i) hm
      have hc_eq := hdprj_eq c_b hc_b
      subst hc_eq
      have hres_b := hres_proj hc_b
      have hbind := Ix.Cert.ReadingKeys.bindings_bound hchk hm hres_b (fun _ h' => hres_inv h')
      rw [← hroles, hrole] at hbind
      cases hbind
    rw [keyOf_eq_of_unbound hunb]
    have hsing_none : Ix.Kernel.Reader.singletonAt cx.store (.member owner i) = none := by
      cases i with
      | zero => simp [Ix.Kernel.Reader.singletonAt, hcb, hinfo]
      | succ _ => rfl
    have hrec_addr : cx.reconstruct (.member owner i) = some (Core.dprjAddr owner i) :=
      projectionAddress_dprj hcb hinfo hms hi
    have ha_of : cx.addressOf (.member owner i) = .ok (Core.dprjAddr owner i) := by
      unfold Ix.Kernel.Reader.Ctx.addressOf
      cases haddr : cx.keys.address[Ix.Kernel.ConstRef.member owner i]? with
      | some a' =>
        have hsnd := cx.keys.address_sound (.member owner i) a' haddr
        rw [hres_inv hsnd]
        rfl
      | none =>
        rw [hsing_none, hrec_addr]
        rfl
    have hcompat : Ix.Cert.ReaderKeys.ReconCompatible cx (· = .member owner i) := by
      intro ref a' href _ _ _ hrec hcached
      subst href
      rw [hrec_addr] at hrec
      injection hrec with ha'_eq
      subst ha'_eq
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hcached
      have hsnd := cx.keys.byAddress_sound (Core.dprjAddr owner i) v hv
      cases hst_p : cx.store (Core.dprjAddr owner i) with
      | none => simp [Ix.Kernel.Reader.keyOfAddress, Ix.Kernel.Reader.resolve, hst_p] at hsnd
      | some c' =>
        have hc' := hdprj_eq c' hst_p
        subst hc'
        exact hres_proj hst_p
    unfold Ix.Kernel.Reader.Ctx.memberKey
    rw [hrole]
    simp only [ha_of, bind, Except.bind]
    cases hby : cx.keys.byAddress[Core.dprjAddr owner i]? with
    | none => rfl
    | some v =>
      have hres_d := Ix.Cert.ReaderKeys.addressOf_resolves_of_cached hcompat rfl hrole ha_of
        (by rw [hby]; rfl)
      have hsnd := cx.keys.byAddress_sound (Core.dprjAddr owner i) v hby
      have hv : v = .id (Core.dprjAddr owner i) := by
        simpa [Ix.Kernel.Reader.keyOfAddress, hres_d, hrole, Ix.Kernel.Mode.addressId?] using hsnd.symm
      rw [hv]
      rfl

/-- From `Claim.MutsMemberCheckedAtFull` at a definition member `ms[i]? = some (.defn d)`, under
`Bounded calls` and `¬ V.HashedCollision extra calls`, `i < UInt64.size` and any record stored at
`Core.dprjAddr owner i` from `V.Preimage`, `extra`, or `Hashed calls` must equal
`⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩`. -/
theorem dprj_store_eq_of_mutsMemberChecked
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {owner : _root_.Address} {ms : Array Ixon.MutConst} {i : Nat} {d : Ixon.Definition}
    {V : IxVM.Refinement.View} {extra : List ByteArray}
    (hbound : IxVM.Consistency.Bounded calls)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hm : Claim.MutsMemberCheckedAtFull calls bAddr t owner ms i)
    (hms : ms[i]? = some (.defn d)) :
    i < UInt64.size ∧
      ∀ (raw' : ByteArray) (c' : Ixon.Constant),
        _root_.Address.blake3Pure raw' = Core.dprjAddr owner i →
        Ixon.deConstantExact raw' = .ok c' →
        (raw' ∈ V.Preimage ∨ raw' ∈ extra ∨ Hashed calls raw') →
        c' = ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ := by
  have hchk := mutsMemberCheckedAtFull_to_checkedAtFull hbound hm hms
  simp only [Core.Specs.Callees.memberProjInfo, ← Core.dprjAddr] at hchk
  obtain ⟨_, _, _, _, _, _, _, _, _, cs_load, _, bytes, E_ld,
    _, _, _, _, hhash_ld, hblake_ld, _, hL1, hsub_ld, _, _, _, _⟩ :=
    checkedAtFull_loadedL1 hbound hchk
  obtain ⟨c_ld, hdec_ld, _, _, _, _, hraw_ld⟩ := hL1
  have hhashed_calls : Hashed calls bytes := Hashed.mono hsub_ld hhash_ld
  have hi_lt : i < UInt64.size := by
    obtain ⟨_, _, _, _, _, _, hmem, _, _, hcl_pa, _⟩ := hm
    have hlen : ms.toList.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem
    have hi_sz : i < ms.size := (Array.getElem?_eq_some_iff.mp hms).1
    have hi_len : i < ms.toList.length := by simpa using hi_sz
    have : (2 ^ 39 : Nat) < UInt64.size := by decide
    omega
  have hser_dprj : bytes = Ixon.serConstant ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ := by
    have hwf_dprj :
        (⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
      rw [L1.emptyTablesConstant_wireWF]
      -- `owner` is hashed by `calls` via `MutsMemberCheckedAtFull`? Even simpler: check `owner.hash.size`!
      obtain ⟨_, _, _, _, _, _, _, hblk, _, _, _⟩ := hm
      obtain ⟨b_arr, _, rfl⟩ := hblk
      exact b_arr.size_toArray
    by_cases heq_b : bytes = Ixon.serConstant ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩
    · exact heq_b
    · -- Wait: `Core.dprjAddr owner i = Address.blake3Pure (Ixon.serConstant ⟨.dPrj ...⟩)`!
      -- Wait: is `Ixon.serConstant ⟨.dPrj ...⟩` hashed in `calls`?!
      -- YES! Inside `MutsMemberCheckedAtFull`, `Ingress::projection_addr` hashes `Ixon.serConstant ⟨.dPrj ...⟩`!
      obtain ⟨_, _, _, _, _, cs_pa, hmem_pa, hblk_pa, ev_pa, hcl_pa, hsub_pa⟩ := hm
      obtain ⟨b_arr, hb_ref, rfl⟩ := hblk_pa
      have hlen : ms.toList.length < 2 ^ 39 :=
        RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem_pa
      have hi_sz : i < ms.size := (Array.getElem?_eq_some_iff.mp hms).1
      have hi_val : ((i : F)).val = i :=
        ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
      obtain ⟨_, _, hhash_pa, mc', _, hget_pa, _, _⟩ := L1.projection_addr_spec hmem_pa hb_ref ev_pa
      rw [hi_val] at hget_pa hhash_pa
      have hms_list : ms.toList[i]? = some (.defn d) := by simpa using hms
      rw [hms_list] at hget_pa
      cases hget_pa
      have hhashed_pa : Hashed calls (Ixon.serConstant ⟨.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩) :=
        Hashed.mono hsub_pa hhash_pa
      exact absurd (.inl ⟨Core.dprjAddr (Core.ixAddr b_arr) i,
        Ixon.serConstant ⟨.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩,
        bytes, .inr (.inr ⟨hhashed_pa, rfl⟩), hhashed_calls, Ne.symm heq_b, hblake_ld⟩) hnoCol
  refine ⟨hi_lt, fun raw' c' hbl' hdec' hsrc' => ?_⟩
  have hraw_eq : raw' = bytes := by
    by_cases heq : raw' = bytes
    · exact heq
    · have hsrc_wit :
          (raw' ∈ V.Preimage ∨ raw' ∈ extra ∨
            Hashed calls raw' ∧ _root_.Address.blake3Pure raw' = Core.dprjAddr owner i) := by
        rcases hsrc' with hp | he | hh
        · exact .inl hp
        · exact .inr (.inl he)
        · exact .inr (.inr ⟨hh, hbl'⟩)
      exact absurd (.inl ⟨Core.dprjAddr owner i, raw', bytes,
        hsrc_wit, hhashed_calls, heq, hbl'.symm.trans hblake_ld⟩) hnoCol
  subst hraw_eq
  rw [hser_dprj] at hdec'
  have hwf_dprj : (⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
    obtain ⟨_, _, _, _, _, _, _, hblk, _, _, _⟩ := hm
    obtain ⟨b_arr, _, rfl⟩ := hblk
    rw [L1.emptyTablesConstant_wireWF]
    exact b_arr.size_toArray
  have hrt := Ixon.Verify.deConstantExact_serConstant _ hwf_dprj
  exact Except.ok.inj (hdec'.symm.trans hrt)

/-! ## Section 3: `SafeRefsInputs`, `recurDeps`, `defOrder`, `MemberReader.read`, and `validate_expr_well_scoped` -/

/-- `Ix.Kernel.Reader.recParam (List.range n)` is definitionally equal on all inputs to `id`. -/
theorem recParam_range (n : Nat) : Ix.Kernel.Reader.recParam (List.range n) = id := by
  funext i
  unfold Ix.Kernel.Reader.recParam
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < n
  · rw [List.getElem?_range hi]
    rfl
  · have hge : (List.range n).length ≤ i := by simp; omega
    rw [List.getElem?_eq_none hge]
    rfl

/-- Cross-lane interface isolating `KernelCheck::safe_refs_only` and inductive/recursor
`readRecordBare` completeness (keeping zero imports from `Decl/*`). -/
structure SafeRefsInputs : Prop where
  /-- Every leaf `.ref` or `.prj` reference index `i` reached by `RawConvExpr` on an expression
  accepted by `KernelCheck::safe_refs_only` resolves in `E₀` to an in-logic record
  (`¬ OutsideLogicAt E₀ a` and `(resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true`). -/
  safe_expr_refs_resolve :
    ∀ {calls : List (Call F)} {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
      {c : Ixon.Constant} {recurAddrs : List _root_.Address}
      {blobs : List (_root_.Address × ByteArray)} {h h' : Heap F} {cs : List (Call F)}
      {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F},
      IxVM.Consistency.Bounded calls →
      IxVM.Consistency.LoadedBy calls E₀ →
      ¬ V.HashedCollision extra calls →
      ObsFn Core.W "KernelCheck::safe_refs_only" [kp] h (.field 1) h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp →
      ∀ {i : Nat} {a : _root_.Address},
        -- For every ref index `i` reached by `e` through `c.sharing`:
        i ∈ (
          let sh := c.sharing.foldl
            (fun (acc : Array (List Nat)) entry =>
              acc.push (Ixon.Expr.rec
                (motive_1 := fun _ => List Nat)
                (fun _ => [])
                (fun _ => [])
                (fun idx _ => [idx.toNat])
                (fun _ _ => [])
                (fun idx _ inner => idx.toNat :: inner)
                (fun _ => [])
                (fun _ => [])
                (fun f g => f ++ g)
                (fun t b => t ++ b)
                (fun t b => t ++ b)
                (fun _ _ t v b => t ++ v ++ b)
                (fun idx => acc[idx.toNat]?.getD [])
                entry))
            #[]
          Ixon.Expr.rec
            (motive_1 := fun _ => List Nat)
            (fun _ => [])
            (fun _ => [])
            (fun idx _ => [idx.toNat])
            (fun _ _ => [])
            (fun idx _ inner => idx.toNat :: inner)
            (fun _ => [])
            (fun _ => [])
            (fun f g => f ++ g)
            (fun t b => t ++ b)
            (fun t b => t ++ b)
            (fun _ _ t v b => t ++ v ++ b)
            (fun idx => sh[idx.toNat]?.getD [])
            e) →
        c.refs[i]? = some a →
        ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧
          ∀ c_a, Ix.Cert.recordAt E₀ a = some c_a →
            (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true
  /-- Inductive and recursor record bare reading (`c.info = .recr _` or non-definition `.muts ms`)
  at a walked non-role address `a` in `streamContext`: `readRecordBare` succeeds, preserves prelude
  keys, and supplies `L1.RecordReadsAs t E_core` + `AddressKey` for all emitted constants stored in
  `E`. -/
  indRecRecordReadBare :
    ∀ {calls : List (Call F)} {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
      {E₀ E E_core : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
      {pre : Ix.Kernel.Reader.Prelude .anon} {order order_role : List _root_.Address}
      {st : Ix.Kernel.Reader.State .anon} {prev_decls : List (Ix.Kernel.Declaration .anon)}
      {a : _root_.Address} {c : Ixon.Constant},
      IxVM.Consistency.Bounded calls →
      Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t →
      Ix.Kernel.Reader.preludeFor t = .ok pre →
      IxVM.Consistency.LoadedBy calls E₀ →
      ¬ V.HashedCollision extra calls →
      L1.EnvDecoded E_core →
      ¬ L1.EnvInternalCollision E_core →
      (∀ x c_x, Ix.Cert.recordAt E x = some c_x → Ix.Cert.recordAt E_core x = some c_x) →
      (∀ x bs, E.blobs.get? x = some bs → E_core.blobs.get? x = some bs) →
      AuthenticExactStore
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)).store →
      order.Nodup →
      (a, c) ∈ Ix.Cert.Stream.decodedOf E order →
      a ∉ order_role →
      Claim.WalkedAt calls b.address t E₀ a →
      ¬ IxVM.Consistency.OutsideLogicAt E₀ a →
      (∀ a' c', (a', c') ∈ Ix.Cert.Stream.decodedOf E order → a' ∉ order_role →
        Claim.WalkedAt calls b.address t E₀ a' ∧ ¬ IxVM.Consistency.OutsideLogicAt E₀ a') →
      (∀ k ∈ pre.state.keys, st.SameAt pre.state k) →
      ((∃ rc, c.info = .recr rc) ∨
        (∃ ms, c.info = .muts ms ∧ ¬ ms.all (fun | .defn _ => true | _ => false))) →
      ∃ r,
        Ix.Kernel.Reader.readRecordBare
          (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
            (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
          st a c = .ok r ∧
        (∀ k ∈ pre.state.keys, (st.commit r).SameAt pre.state k) ∧
        (∀ x c_x,
          ((x = a ∧ c_x = c ∧ ∃ rc, c.info = .recr rc) ∨
            (Ix.Cert.recordAt E x = some c_x ∧ x ≠ a ∧ Ix.Cert.ownerOf x c_x = a)) →
          ∃ d ci₀,
            d ∈ pre.ix.decls.toList ++ prev_decls ++ r.decls.toList ∧
            ci₀ ∈ IxVM.Consistency.installs d ∧
            ci₀.name = Core.keyOf t x ∧
            L1.RecordReadsAs t E_core x c_x ci₀)

/-- Reachable `.ref`/`.prj` table indices in `e` through `sharing`. -/
def reachRefsExpr (sh : Array (List Nat)) : Ixon.Expr → List Nat
  | .var _ | .sort _ | .recur _ _ | .str _ | .nat _ => []
  | .ref idx _ => [idx.toNat]
  | .prj idx _ inner => idx.toNat :: reachRefsExpr sh inner
  | .app f g => reachRefsExpr sh f ++ reachRefsExpr sh g
  | .lam t b | .all t b => reachRefsExpr sh t ++ reachRefsExpr sh b
  | .letE _ _ t v b => reachRefsExpr sh t ++ reachRefsExpr sh v ++ reachRefsExpr sh b
  | .share idx => sh[idx.toNat]?.getD []

def buildReachRefsTbl (sharing : List Ixon.Expr) : Array (List Nat) :=
  sharing.foldl (fun acc entry => acc.push (reachRefsExpr acc entry)) #[]

private theorem reachRefsExpr_eq_rec (sh : Array (List Nat)) (e : Ixon.Expr) :
    reachRefsExpr sh e =
      Ixon.Expr.rec
        (motive_1 := fun _ => List Nat)
        (fun _ => [])
        (fun _ => [])
        (fun idx _ => [idx.toNat])
        (fun _ _ => [])
        (fun idx _ inner => idx.toNat :: inner)
        (fun _ => [])
        (fun _ => [])
        (fun f g => f ++ g)
        (fun t b => t ++ b)
        (fun t b => t ++ b)
        (fun _ _ t v b => t ++ v ++ b)
        (fun idx => sh[idx.toNat]?.getD [])
        e := by
  induction e <;> simp [reachRefsExpr, *]

private theorem buildReachRefsTbl_size :
    ∀ (es : List Ixon.Expr) (acc : Array (List Nat)),
      (es.foldl (fun a entry => a.push (reachRefsExpr a entry)) acc).size = acc.size + es.length
  | [], acc => by simp
  | _ :: es, acc => by
    simp only [List.foldl_cons, buildReachRefsTbl_size es, Array.size_push, List.length_cons]
    omega

private theorem buildReachRefsTbl_prefix :
    ∀ (es : List Ixon.Expr) (acc : Array (List Nat)) (i : Nat) (_ : i < acc.size),
      (es.foldl (fun a entry => a.push (reachRefsExpr a entry)) acc)[i]? = acc[i]?
  | [], _, _, _ => rfl
  | _ :: es, acc, i, hi => by
    simp only [List.foldl_cons]
    rw [buildReachRefsTbl_prefix es _ i (by simp; omega)]
    have hne : i ≠ acc.size := by omega
    simp [Array.getElem?_push, hne]

private theorem buildReachRefsTbl_take_getElem? (sharing : List Ixon.Expr)
    {n i : Nat} {s : Ixon.Expr} (hi_n : i < n) (hsh : sharing[i]? = some s) :
    (buildReachRefsTbl (sharing.take n))[i]? =
      some (reachRefsExpr (buildReachRefsTbl (sharing.take i)) s) := by
  have hi_len : i < sharing.length := (List.getElem?_eq_some_iff.mp hsh).1
  have hsplit : sharing.take n =
      sharing.take i ++ (s :: (sharing.drop (i + 1)).take (n - 1 - i)) := by
    have h1 : sharing.take n = (sharing.take i ++ sharing.drop i).take n := by
      rw [List.take_append_drop]
    have hdrop : sharing.drop i = s :: sharing.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi_len]
      have hs_eq : sharing[i] = s := Option.some.inj ((List.getElem?_eq_getElem hi_len).symm.trans hsh)
      rw [hs_eq]
    rw [h1, hdrop, List.take_append]
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi_len)]
    have hsub : n - i = (n - 1 - i) + 1 := by omega
    rw [List.take_of_length_le (by simp; omega), hsub, List.take_succ_cons]
  unfold buildReachRefsTbl
  rw [hsplit, List.foldl_append, List.foldl_cons]
  have hsz : ((sharing.take i).foldl (fun acc entry => acc.push (reachRefsExpr acc entry)) #[]).size = i := by
    rw [buildReachRefsTbl_size]; simp [Nat.min_eq_left (Nat.le_of_lt hi_len)]
  rw [buildReachRefsTbl_prefix _ _ i (by simp [hsz]), Array.getElem?_push]
  simp [hsz]

/-- Every index in `reachRefsExpr` of a top-level expression of `c` belongs to `usedRefIdxs c`. -/
private theorem exprDirectRefs_mem :
    ∀ (e : Ixon.Expr) (sh : Array (List Nat)) {j : Nat},
      (∀ k xs, sh[k]? = some xs → ∀ x ∈ xs, x ∈ IxVM.Consistency.usedRefIdxs c) →
      (∀ x ∈ IxVM.Consistency.exprRefIdxs e, x ∈ IxVM.Consistency.usedRefIdxs c) →
      j ∈ reachRefsExpr sh e →
      j ∈ IxVM.Consistency.usedRefIdxs c
  | .var _, _, _, _, _, hm => nomatch hm
  | .sort _, _, _, _, _, hm => nomatch hm
  | .recur _ _, _, _, _, _, hm => nomatch hm
  | .str _, _, _, _, _, hm => nomatch hm
  | .nat _, _, _, _, _, hm => nomatch hm
  | .ref idx _, _, _, _, hdir, hm => by
    simp only [reachRefsExpr, List.mem_singleton] at hm
    subst hm
    exact hdir idx.toNat (by simp [IxVM.Consistency.exprRefIdxs])
  | .prj idx _ inner, sh, j, hsh, hdir, hm => by
    simp only [reachRefsExpr, List.mem_cons] at hm
    rcases hm with rfl | hin
    · exact hdir idx.toNat (by simp [IxVM.Consistency.exprRefIdxs])
    · exact exprDirectRefs_mem inner sh hsh
        (fun x hx => hdir x (by simp [IxVM.Consistency.exprRefIdxs, hx])) hin
  | .app f g, sh, j, hsh, hdir, hm => by
    rcases List.mem_append.mp hm with hf | hg
    · exact exprDirectRefs_mem f sh hsh
        (fun x hx => hdir x (by simp [IxVM.Consistency.exprRefIdxs, hx])) hf
    · exact exprDirectRefs_mem g sh hsh
        (fun x hx => hdir x (by simp [IxVM.Consistency.exprRefIdxs, hx])) hg
  | .lam t b, sh, j, hsh, hdir, hm => by
    rcases List.mem_append.mp hm with ht | hb
    · exact exprDirectRefs_mem t sh hsh
        (fun x hx => hdir x (by simp [IxVM.Consistency.exprRefIdxs, hx])) ht
    · exact exprDirectRefs_mem b sh hsh
        (fun x hx => hdir x (by simp [IxVM.Consistency.exprRefIdxs, hx])) hb
  | .all t b, sh, j, hsh, hdir, hm => by
    rcases List.mem_append.mp hm with ht | hb
    · exact exprDirectRefs_mem t sh hsh
        (fun x hx => hdir x (by simp [IxVM.Consistency.exprRefIdxs, hx])) ht
    · exact exprDirectRefs_mem b sh hsh
        (fun x hx => hdir x (by simp [IxVM.Consistency.exprRefIdxs, hx])) hb
  | .letE _ _ t v b, sh, j, hsh, hdir, hm => by
    rcases List.mem_append.mp hm with htv | hb
    · rcases List.mem_append.mp htv with ht | hv
      · exact exprDirectRefs_mem t sh hsh
          (fun x hx => hdir x (by simp [IxVM.Consistency.exprRefIdxs, hx])) ht
      · exact exprDirectRefs_mem v sh hsh
          (fun x hx => hdir x (by simp [IxVM.Consistency.exprRefIdxs, hx])) hv
    · exact exprDirectRefs_mem b sh hsh
        (fun x hx => hdir x (by simp [IxVM.Consistency.exprRefIdxs, hx])) hb
  | .share idx, sh, j, hsh, _, hm => by
    simp only [reachRefsExpr] at hm
    cases hget : sh[idx.toNat]? with
    | none => simp [hget] at hm
    | some xs =>
      rw [hget] at hm
      exact hsh idx.toNat xs hget j hm

/-- Every index in `buildReachRefsTbl c.sharing.toList` belongs to `usedRefIdxs c`. -/
theorem reachRefs_subset_usedRefIdxs {c : Ixon.Constant} {e : Ixon.Expr}
    (hdir : ∀ x ∈ IxVM.Consistency.exprRefIdxs e, x ∈ IxVM.Consistency.usedRefIdxs c) :
    ∀ j ∈ reachRefsExpr (buildReachRefsTbl c.sharing.toList) e,
      j ∈ IxVM.Consistency.usedRefIdxs c := by
  have hsh_ok : ∀ (n : Nat), n ≤ c.sharing.toList.length →
      ∀ k xs, (buildReachRefsTbl (c.sharing.toList.take n))[k]? = some xs →
        ∀ x ∈ xs, x ∈ IxVM.Consistency.usedRefIdxs c := by
    intro n
    induction n with
    | zero =>
      intro _ k xs hk
      simp [buildReachRefsTbl] at hk
    | succ n ih =>
      intro hn k xs hk x hx
      have hsz : (buildReachRefsTbl (c.sharing.toList.take (n + 1))).size = n + 1 := by
        unfold buildReachRefsTbl
        rw [buildReachRefsTbl_size]
        simp [Nat.min_eq_left hn]
      have hk_lt : k < n + 1 := by
        have := (Array.getElem?_eq_some_iff.mp hk).1
        omega
      have hs_some : ∃ s, c.sharing.toList[k]? = some s :=
        ⟨c.sharing.toList[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨s, hs⟩ := hs_some
      rw [buildReachRefsTbl_take_getElem? c.sharing.toList hk_lt hs] at hk
      injection hk with hxs
      subst hxs
      have hs_mem : s ∈ c.sharing.toList := List.mem_of_getElem? hs
      have hs_dir : ∀ y ∈ IxVM.Consistency.exprRefIdxs s, y ∈ IxVM.Consistency.usedRefIdxs c := by
        intro y hy
        unfold IxVM.Consistency.usedRefIdxs
        rw [List.mem_eraseDup]
        apply List.mem_flatMap.mpr
        exact ⟨s, by rw [Array.toList_append]; exact List.mem_append_left _ hs_mem, hy⟩
      by_cases hkn : k < n
      · exact ih (by omega) k _ (buildReachRefsTbl_take_getElem? c.sharing.toList hkn hs) x hx
      · have hkeq : k = n := by omega
        subst hkeq
        exact exprDirectRefs_mem s _ (ih (by omega)) hs_dir hx
  intro j hj
  exact exprDirectRefs_mem e _ (by
    simpa [List.take_length] using hsh_ok c.sharing.toList.length (Nat.le_refl _)) hdir hj

/-- When `recurAddrs = []`, `RawConvExpr` contains no `.recur` nodes, so `recurDeps.go` preserves
any empty accumulator (`HashSet.toList = []`) across all converted sharing entries and `e`. -/
private theorem recurDeps_go_empty_of_rawConvExpr
    {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr refs [] univs sharing blobs h bound e kp) :
    ∀ (shared : Array (Std.HashSet Nat)) (acc : Std.HashSet Nat),
      (∀ i < bound, ∀ s, sharing[i]? = some s →
        ∃ m ∈ shared[i]?, m.toList = []) →
      acc.toList = [] →
      (Ix.Kernel.Reader.recurDeps.go shared acc e).toList = [] := by
  induction raw with
  | var _ _ | sort _ _ _ _ | ref _ _ _ _ _ _ _ | str _ _ _ _ _ _ | nat _ _ _ _ _ _ _ _ =>
    intro _ acc _ hacc; exact hacc
  | recur _ hrec _ _ _ _ _ =>
    simp at hrec
  | prj _ _ _ _ _ _ _ ih =>
    intro shared acc hsh hacc
    exact ih shared acc hsh hacc
  | app _ _ _ ihf iha =>
    intro shared acc hsh hacc
    exact iha shared _ hsh (ihf shared acc hsh hacc)
  | lam _ _ _ _ iht ihb =>
    intro shared acc hsh hacc
    exact ihb shared _ hsh (iht shared acc hsh hacc)
  | all _ _ _ _ iht ihb =>
    intro shared acc hsh hacc
    exact ihb shared _ hsh (iht shared acc hsh hacc)
  | letE _ _ _ iht ihv ihb =>
    intro shared acc hsh hacc
    exact ihb shared _ hsh (ihv shared _ hsh (iht shared acc hsh hacc))
  | @share bnd idx s _ hidx hsh_get _ ih =>
    intro shared acc hsh hacc
    simp only [Ix.Kernel.Reader.recurDeps.go]
    obtain ⟨m, hm_mem, hm_empty⟩ := hsh idx.toNat hidx s hsh_get
    have hm_get : shared[idx.toNat]? = some m := Option.mem_def.mp hm_mem
    rw [hm_get, Option.getD_some, Std.HashSet.fold_eq_foldl_toList, hm_empty]
    exact hacc

/-- Wait: in `recurDeps c d` (`Reader.lean:879-885`), `shared` is built over ALL of `c.sharing`
even if an unreferenced sharing entry has `.recur`!Wait — what if an UNREFERENCED sharing entry in
`c.sharing` had `.recur`, while `d.typ` and `d.value` never reference that sharing entry?!
Look at `recurDeps.go` (`Reader.lean:893`):
`| .share i => (shared[i.toNat]?.getD {}).fold (·.insert ·) acc`!
`recurDeps c d` ONLY folds `shared[i.toNat]?` when `.share i` IS REACHED from `d.typ` or `d.value`!
And when `.share i` IS reached in `RawConvExpr` (`rs : RawConvExpr refs [] univs sharing blobs h idx.toNat s kp`),
`ih` ALREADY proves `(recurDeps.go shared' {} s).toList = []` WITHOUT needing unreferenced entries
of `shared` to be empty!! -/
private theorem recurDeps_buildShared_getElem? (sharing : List Ixon.Expr) :
    ∀ (es : List Ixon.Expr) (acc : Array (Std.HashSet Nat)) (i : Nat) (_ : i < acc.size),
      (es.foldl (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) acc)[i]? =
        acc[i]?
  | [], _, _, _ => rfl
  | _ :: es, acc, i, hi => by
    simp only [List.foldl_cons]
    rw [recurDeps_buildShared_getElem? sharing es _ i (by simp; omega)]
    have hne : i ≠ acc.size := by omega
    simp [Array.getElem?_push, hne]

private theorem recurDeps_buildShared_size :
    ∀ (es : List Ixon.Expr) (acc : Array (Std.HashSet Nat)),
      (es.foldl (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) acc).size =
        acc.size + es.length
  | [], acc => by simp
  | _ :: es, acc => by
    simp only [List.foldl_cons, recurDeps_buildShared_size es, Array.size_push, List.length_cons]
    omega

private theorem recurDeps_buildShared_at (sharing : List Ixon.Expr) {i : Nat} {s : Ixon.Expr}
    (hsh : sharing[i]? = some s) :
    let full := sharing.foldl
      (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[]
    let pre := (sharing.take i).foldl
      (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[]
    full[i]? = some (Ix.Kernel.Reader.recurDeps.go pre {} s) ∧
      ∀ j < i, full[j]? = pre[j]? := by
  have hi_len : i < sharing.length := (List.getElem?_eq_some_iff.mp hsh).1
  have hsplit : sharing = sharing.take i ++ (s :: sharing.drop (i + 1)) := by
    conv_lhs => rw [← List.take_append_drop i sharing]
    rw [List.drop_eq_getElem_cons hi_len]
    have hs_eq : sharing[i] = s := Option.some.inj ((List.getElem?_eq_getElem hi_len).symm.trans hsh)
    rw [hs_eq]
  let pre := (sharing.take i).foldl
    (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[]
  have hpre_sz : pre.size = i := by
    dsimp only [pre]
    rw [recurDeps_buildShared_size]
    simp [Nat.min_eq_left (Nat.le_of_lt hi_len)]
  refine ⟨?_, fun j hj => ?_⟩
  · conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    rw [recurDeps_buildShared_getElem? sharing _ _ i (by simp [hpre_sz])]
    rw [Array.getElem?_push]
    simp [hpre_sz]
  · conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    rw [recurDeps_buildShared_getElem? sharing _ _ j (by simp [hpre_sz]; omega)]
    rw [Array.getElem?_push]
    have hne : j ≠ pre.size := by omega
    simp [hne]

private theorem recurDeps_go_empty_lazy
    {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr refs [] univs sharing blobs h bound e kp) :
    let full := sharing.foldl
      (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[]
    ∀ (sh : Array (Std.HashSet Nat)) (acc : Std.HashSet Nat),
      (∀ j < bound, j < sharing.length → sh[j]? = full[j]?) →
      acc.toList = [] →
      (Ix.Kernel.Reader.recurDeps.go sh acc e).toList = [] := by
  induction raw with
  | var _ _ | sort _ _ _ _ | ref _ _ _ _ _ _ _ | str _ _ _ _ _ _ | nat _ _ _ _ _ _ _ _ =>
    intro _ _ _ _ hacc; exact hacc
  | recur _ hrec _ _ _ _ _ => simp at hrec
  | prj _ _ _ _ _ _ _ ih =>
    intro _ sh acc hag hacc; exact ih sh acc hag hacc
  | app _ _ _ ihf iha =>
    intro _ sh acc hag hacc; exact iha sh _ hag (ihf sh acc hag hacc)
  | lam _ _ _ _ iht ihb =>
    intro _ sh acc hag hacc; exact ihb sh _ hag (iht sh acc hag hacc)
  | all _ _ _ _ iht ihb =>
    intro _ sh acc hag hacc; exact ihb sh _ hag (iht sh acc hag hacc)
  | letE _ _ _ iht ihv ihb =>
    intro _ sh acc hag hacc; exact ihb sh _ hag (ihv sh _ hag (iht sh acc hag hacc))
  | @share bnd idx s _ hidx hsh_get _ ih =>
    intro full sh acc hag hacc
    have hi_len : idx.toNat < sharing.length := (List.getElem?_eq_some_iff.mp hsh_get).1
    obtain ⟨hfull_i, hfull_lt⟩ := recurDeps_buildShared_at sharing hsh_get
    let pre := (sharing.take idx.toNat).foldl
      (fun a entry => a.push (Ix.Kernel.Reader.recurDeps.go a {} entry)) #[]
    have hs_empty : (Ix.Kernel.Reader.recurDeps.go pre {} s).toList = [] :=
      ih pre {} (fun j hj _ => (hfull_lt j hj).symm) (by simp)
    simp only [Ix.Kernel.Reader.recurDeps.go]
    rw [hag idx.toNat hidx hi_len, hfull_i, Option.getD_some,
      Std.HashSet.fold_eq_foldl_toList, hs_empty]
    exact hacc

/-- **Unconditional empty `recurDeps` on safe converted definitions**: even if unused sharing
entries in `c.sharing` exist, any `d` whose `d.typ` and `d.value` satisfy `RawConvExpr` with
`recurAddrs = []` has `(Ix.Kernel.Reader.recurDeps c d).toList = []`. -/
theorem recurDeps_empty_of_rawConvExpr {c : Ixon.Constant} {d : Ixon.Definition}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {tyPtr valPtr : SourceValue F}
    (hty : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h 4294967295
      d.typ tyPtr)
    (hval : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h 4294967295
      d.value valPtr) :
    (Ix.Kernel.Reader.recurDeps c d).toList = [] := by
  have hshared_eq :
      (Id.run do
        let mut shared : Array (Std.HashSet Nat) := #[]
        for entry in c.sharing do
          shared := shared.push (Ix.Kernel.Reader.recurDeps.go shared {} entry)
        return Ix.Kernel.Reader.recurDeps.go shared
          (Ix.Kernel.Reader.recurDeps.go shared {} d.typ) d.value) =
      (let shared := c.sharing.toList.foldl
          (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[]
       Ix.Kernel.Reader.recurDeps.go shared
         (Ix.Kernel.Reader.recurDeps.go shared {} d.typ) d.value) := by
    simp [Id.run, Array.forIn_pure_yield_eq_foldl, ← Array.foldl_toList]
  unfold Ix.Kernel.Reader.recurDeps
  rw [hshared_eq]
  have h1 := recurDeps_go_empty_lazy hty _ {} (fun _ _ _ => rfl) (by simp)
  exact recurDeps_go_empty_lazy hval _ _ (fun _ _ _ => rfl) h1

/-- Inner loop of `defOrder` when every `(deps[i]!).toList` is empty: pushes `0, 1, ..., n - 1`
in order during the very first pass. -/
private theorem defOrder_inner_all_empty (deps : Array (Std.HashSet Nat))
    (hempty : ∀ i : Nat, i < deps.size → (deps[i]!).toList = []) :
    ∀ (k : Nat), k ≤ deps.size →
      (List.range k).foldl
        (fun (s : Array Bool × Array Nat × Bool) (i : Nat) =>
          if !s.1[i]! && (deps[i]!).toList.all (fun j => j == i || j ≥ deps.size || s.1[j]!) then
            (s.1.set! i true, s.2.1.push i, true)
          else s)
        (Array.replicate deps.size false, #[], false) =
      ((List.range k).foldl (fun d i => d.set! i true) (Array.replicate deps.size false),
       (List.range k).toArray, decide (0 < k)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (by omega)]
    let done_k := (List.range k).foldl (fun d i => d.set! i true) (Array.replicate deps.size false)
    have hdone_sz_get : ∀ (xs : List Nat) (arr : Array Bool),
        (xs.foldl (fun d i => d.set! i true) arr).size = arr.size ∧
        (∀ x ∉ xs, (xs.foldl (fun d i => d.set! i true) arr)[x]? = arr[x]?) := by
      intro xs
      induction xs with
      | nil => intro arr; exact ⟨rfl, fun _ _ => rfl⟩
      | cons hd tl ihx =>
        intro arr
        simp only [List.foldl_cons]
        obtain ⟨hsz, hget⟩ := ihx (arr.set! hd true)
        refine ⟨hsz.trans (by simp), fun x hx => ?_⟩
        have hne_hd : hd ≠ x := fun heq => hx (heq ▸ List.mem_cons_self)
        have hne_tl : x ∉ tl := fun hm => hx (List.mem_cons_of_mem _ hm)
        rw [hget x hne_tl]
        by_cases hhd_lt : hd < arr.size
        · simp [Array.set!, Array.setIfInBounds, hhd_lt, Array.getElem?_set, hne_hd]
        · simp [Array.set!, Array.setIfInBounds, hhd_lt]
    obtain ⟨hsz_k, hget_k⟩ := hdone_sz_get (List.range k) (Array.replicate deps.size false)
    have hk_not_mem : k ∉ List.range k := by simp
    have hdone_at_k : done_k[k]! = false := by
      have hlt : k < done_k.size := by dsimp [done_k]; rw [hsz_k]; simp; omega
      rw [getElem!_pos done_k k hlt]
      have hsome : done_k[k]? = some false := by
        dsimp [done_k]
        rw [hget_k k hk_not_mem, Array.getElem?_replicate]
        simp [show k < deps.size by omega]
      exact Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans hsome)
    simp only [hdone_at_k, Bool.not_false, hempty k (by omega), List.all_nil, Bool.and_self,
      ↓reduceIte]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    · simp [List.toArray_append]
    · simp

/-- **`defOrder` succeeds with `Array.range deps.size`** whenever all dependency sets are empty. -/
theorem defOrder_all_empty (deps : Array (Std.HashSet Nat))
    (hempty : ∀ i : Nat, i < deps.size → (deps[i]!).toList = []) :
    Ix.Kernel.Reader.defOrder deps = some (Array.range deps.size) := by
  unfold Ix.Kernel.Reader.defOrder
  cases hn : deps.size with
  | zero =>
    have h0 : deps = #[] := Array.eq_empty_of_size_eq_zero hn
    subst h0
    rfl
  | succ m =>
    have hinner := defOrder_inner_all_empty deps hempty (m + 1) (by omega)
    have hrange_eq : (List.range (m + 1)).toArray = Array.range (m + 1) := by
      apply Array.ext'
      simp [Array.toList_range]
    -- Evaluate `[0 : m + 1]`'s first step (`0`), which immediately returns `some out` since `out.size == m + 1`!
    have hrange_std : ([0 : deps.size] : Std.Range) = ⟨0, m + 1, 1, by decide⟩ := by
      simp [hn]
    -- Unfold the outer `for _ in [0:n]` via `Std.Range.forIn'` / `List.range'`:
    have hforIn_inner :
        ∀ {M : Type → Type} [Monad M] [LawfulMonad M] {β : Type} (n : Nat) (init : β)
          (f : Nat → β → M (ForInStep β)),
          (∀ i, f i = fun b => pure (.yield (g b i))) →
          forIn ([0:n] : Std.Range) init f = pure ((List.range n).foldl g init) := by
      intro M _ _ β n init f g hf
      have h1 : forIn ([0:n] : Std.Range) init f = forIn (List.range' 0 n 1) init f := by
        simp [Std.Range.forIn_eq_forIn_range', Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      have hrange' : List.range' 0 n 1 = List.range n := List.range'_eq_map_range.trans (by simp)
      rw [h1, hrange']
      induction (List.range n) generalizing init with
      | nil => simp
      | cons hd tl ih => simp [List.forIn_cons, hf, ih]
    -- Now unfold `Id.run` on `defOrder`!
    dsimp only [Id.run]
    simp only [hn]
    have houter_range :
        ∀ {β : Type} (k : Nat) (s : β)
          (body : Nat → β → Id (ForInStep β)),
          forIn ([0 : k + 1] : Std.Range) s body =
            forIn (0 :: List.range' 1 k 1) s body := by
      intro β k s body
      simp [Std.Range.forIn_eq_forIn_range', Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
        List.range'_succ]
    rw [houter_range]
    rw [List.forIn_cons]
    -- Compute the inner `forIn [0 : m + 1]` on the initial state:
    let stepFn := fun (s : MProd (Array Bool) (MProd (Array Nat) Bool)) (i : Nat) =>
      if !s.fst[i]! && (deps[i]!).toList.all (fun j => j == i || j ≥ m + 1 || s.fst[j]!) then
        MProd.mk (s.fst.set! i true) (MProd.mk (s.snd.fst.push i) true)
      else s
    have hstep_mprod :
        ∀ (xs : List Nat) (a : Array Bool) (b : Array Nat) (c : Bool),
          xs.foldl stepFn ⟨a, ⟨b, c⟩⟩ =
            let r := xs.foldl
              (fun (p : Array Bool × Array Nat × Bool) (i : Nat) =>
                if !p.1[i]! && (deps[i]!).toList.all (fun j => j == i || j ≥ m + 1 || p.1[j]!) then
                  (p.1.set! i true, p.2.1.push i, true)
                else p)
              (a, b, c)
            ⟨r.1, ⟨r.2.1, r.2.2⟩⟩ := by
      intro xs
      induction xs with
      | nil => intros; rfl
      | cons hd tl ih =>
        intro a b c
        simp only [List.foldl_cons, stepFn]
        split <;> exact ih _ _ _
    have hinner_id :
        forIn (m := Id) ([0 : m + 1] : Std.Range)
          (MProd.mk (Array.replicate (m + 1) false) (MProd.mk #[] false))
          (fun i s => pure (.yield (stepFn s i))) =
        pure ((List.range (m + 1)).foldl stepFn
          (MProd.mk (Array.replicate (m + 1) false) (MProd.mk #[] false))) := by
      have h1 : forIn (m := Id) ([0 : m + 1] : Std.Range)
          (MProd.mk (Array.replicate (m + 1) false) (MProd.mk #[] false))
          (fun i s => pure (.yield (stepFn s i))) =
        forIn (m := Id) (List.range' 0 (m + 1) 1)
          (MProd.mk (Array.replicate (m + 1) false) (MProd.mk #[] false))
          (fun i s => pure (.yield (stepFn s i))) := by
        simp [Std.Range.forIn_eq_forIn_range', Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      have hrange' : List.range' 0 (m + 1) 1 = List.range (m + 1) :=
        List.range'_eq_map_range.trans (by simp)
      rw [h1, hrange']
      generalize MProd.mk (Array.replicate (m + 1) false) (MProd.mk (#[] : Array Nat) false) = init
      induction (List.range (m + 1)) generalizing init with
      | nil => rfl
      | cons hd tl ih => simp [List.forIn_cons, ih]
    -- Match the generated `do` block's inner loop!
    simp only [bind, pure]
    change (
      let s := Id.run (forIn (m := Id) ([0 : m + 1] : Std.Range)
        (MProd.mk (Array.replicate (m + 1) false) (MProd.mk #[] false))
        (fun i s =>
          if (!s.fst[i]!) = true then
            if ((deps[i]!).toList.all fun j => j == i || decide (j ≥ m + 1) || s.fst[j]!) = true then
              pure (ForInStep.yield ⟨s.fst.set! i true, ⟨s.snd.fst.push i, true⟩⟩)
            else pure (ForInStep.yield s)
          else pure (ForInStep.yield s)))
      _) = _
    have hbody_eq :
        (fun (i : Nat) (s : MProd (Array Bool) (MProd (Array Nat) Bool)) =>
          (if (!s.fst[i]!) = true then
            if ((deps[i]!).toList.all fun j => j == i || decide (j ≥ m + 1) || s.fst[j]!) = true then
              pure (ForInStep.yield ⟨s.fst.set! i true, ⟨s.snd.fst.push i, true⟩⟩)
            else pure (ForInStep.yield s)
          else pure (ForInStep.yield s) : Id (ForInStep _))) =
        (fun i s => pure (.yield (stepFn s i))) := by
      funext i s
      dsimp only [stepFn]
      cases hb1 : !s.fst[i]! <;>
        cases hb2 : ((deps[i]!).toList.all fun j => j == i || decide (j ≥ m + 1) || s.fst[j]!) <;>
        rfl
    rw [hbody_eq, hinner_id]
    dsimp only [Id.run, pure]
    rw [hstep_mprod]
    have hinner' :
        (List.range (m + 1)).foldl
          (fun (p : Array Bool × Array Nat × Bool) (i : Nat) =>
            if !p.1[i]! && (deps[i]!).toList.all (fun j => j == i || j ≥ m + 1 || p.1[j]!) then
              (p.1.set! i true, p.2.1.push i, true)
            else p)
          (Array.replicate (m + 1) false, #[], false) =
        ((List.range (m + 1)).foldl (fun d i => d.set! i true) (Array.replicate (m + 1) false),
         Array.range (m + 1), true) := by
      have hh := hinner
      simp only [hn, hrange_eq, Nat.zero_lt_succ, decide_true] at hh
      exact hh
    rw [hinner']
    have hsz_out : (Array.range (m + 1)).size = m + 1 := Array.size_range
    simp [hsz_out]

/-! ### `MemberReader.read` completeness from `RawConvExpr` -/

private theorem convExpr_ok_of_rawConvExpr
    {ecx : Ix.Kernel.Reader.ECx .anon}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {param : Nat → Ix.Kernel.LevelParam}
    (hrefs : ecx.src.refs.toList = refs)
    (hunivs : ecx.univs = univs.toArray.map (Ix.Kernel.Reader.convUniv param))
    (hself_ok : ∀ i a, recurAddrs[i]? = some a → ∃ m k, ecx.self i = some m ∧ m = .ok k)
    (hblob_ok : ∀ a bs, (a, bs) ∈ blobs → ecx.cx.blob a = some bs)
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr refs recurAddrs univs sharing blobs h bound e kp) :
    ∀ {n : Nat},
      n ≤ sharing.length →
      bound ≤ min n 4294967295 →
      (∀ idx ∈ reachRefsExpr (buildReachRefsTbl sharing) e,
        ∀ a, refs[idx]? = some a → ∃ k, ecx.cx.keyAt a = .ok k) →
      ∃ E_rd : Core.KExpr,
        Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (sharing.take n)) e = .ok E_rd := by
  induction raw with
  | var _ _ =>
    intro _ _ _ _
    exact ⟨_, rfl⟩
  | @sort _ _ uIdx u _ _ hu _ _ =>
    intro _ _ _ _
    have hu_arr : ecx.univs[uIdx.toNat]? = some (Ix.Kernel.Reader.convUniv param u) := by
      rw [hunivs, Array.getElem?_map, Array.getElem?_toList, hu]
      rfl
    exact ⟨.sort (Ix.Kernel.Reader.convUniv param u),
      by simp [Ix.Kernel.Reader.convExpr, Ix.Kernel.Reader.ECx.level, hu_arr, pure, Except.pure,
        bind, Except.bind]⟩
  | @ref _ _ rIdx uIdxs a _ _ _ ls _ href _ _ hls _ _ =>
    intro _ _ _ hkeys
    obtain ⟨k, hk⟩ := hkeys rIdx.toNat (by simp [reachRefsExpr]) a href
    have href_arr : ecx.src.refs[rIdx.toNat]? = some a := by
      rw [← Array.getElem?_toList, hrefs, href]
    have hkeyAt : ecx.keyAt rIdx = .ok k := by
      simp [Ix.Kernel.Reader.ECx.keyAt, href_arr, hk]
    have hlevels : ∃ ls_p, ecx.levels uIdxs = .ok ls_p := by
      unfold Ix.Kernel.Reader.ECx.levels
      have hgo : ∀ (us : List UInt64) (acc : List Core.KLevel),
          us.mapM (fun i => univs[i.toNat]?.map (Ix.Kernel.Reader.convUniv id)) = some acc →
          ∃ ls_p, us.mapM ecx.level = .ok ls_p := by
        intro us
        induction us with
        | nil => intro _ _; exact ⟨[], rfl⟩
        | cons u rest ihu =>
          intro acc hm
          simp only [List.mapM_cons, Option.bind_eq_bind] at hm
          obtain ⟨l1, hl1, hm2⟩ := Option.bind_eq_some_iff.mp hm
          obtain ⟨lrest, hlrest, _⟩ := Option.bind_eq_some_iff.mp hm2
          obtain ⟨u_raw, hu_raw, _⟩ := Option.map_eq_some_iff.mp hl1
          have hu_arr : ecx.univs[u.toNat]? = some (Ix.Kernel.Reader.convUniv param u_raw) := by
            rw [hunivs, Array.getElem?_map, Array.getElem?_toList, hu_raw]
            rfl
          have hlev1 : ecx.level u = .ok (Ix.Kernel.Reader.convUniv param u_raw) := by
            simp [Ix.Kernel.Reader.ECx.level, hu_arr, pure, Except.pure]
          obtain ⟨ls_rest, hls_rest⟩ := ihu lrest hlrest
          exact ⟨Ix.Kernel.Reader.convUniv param u_raw :: ls_rest,
            by simp [List.mapM_cons, hlev1, hls_rest, bind, Except.bind, pure, Except.pure]⟩
      exact hgo uIdxs.toList ls hls
    obtain ⟨ls_p, hls_p⟩ := hlevels
    exact ⟨.const k ls_p,
      by simp [Ix.Kernel.Reader.convExpr, hkeyAt, hls_p, bind, Except.bind, pure, Except.pure]⟩
  | @recur _ _ rIdx uIdxs a _ _ _ ls _ hrec _ _ hls _ _ =>
    intro _ _ _ _
    obtain ⟨m, k, hself_m, hm_k⟩ := hself_ok rIdx.toNat a hrec
    have hlevels : ∃ ls_p, ecx.levels uIdxs = .ok ls_p := by
      unfold Ix.Kernel.Reader.ECx.levels
      have hgo : ∀ (us : List UInt64) (acc : List Core.KLevel),
          us.mapM (fun i => univs[i.toNat]?.map (Ix.Kernel.Reader.convUniv id)) = some acc →
          ∃ ls_p, us.mapM ecx.level = .ok ls_p := by
        intro us
        induction us with
        | nil => intro _ _; exact ⟨[], rfl⟩
        | cons u rest ihu =>
          intro acc hm
          simp only [List.mapM_cons, Option.bind_eq_bind] at hm
          obtain ⟨l1, hl1, hm2⟩ := Option.bind_eq_some_iff.mp hm
          obtain ⟨lrest, hlrest, _⟩ := Option.bind_eq_some_iff.mp hm2
          obtain ⟨u_raw, hu_raw, _⟩ := Option.map_eq_some_iff.mp hl1
          have hu_arr : ecx.univs[u.toNat]? = some (Ix.Kernel.Reader.convUniv param u_raw) := by
            rw [hunivs, Array.getElem?_map, Array.getElem?_toList, hu_raw]
            rfl
          have hlev1 : ecx.level u = .ok (Ix.Kernel.Reader.convUniv param u_raw) := by
            simp [Ix.Kernel.Reader.ECx.level, hu_arr, pure, Except.pure]
          obtain ⟨ls_rest, hls_rest⟩ := ihu lrest hlrest
          exact ⟨Ix.Kernel.Reader.convUniv param u_raw :: ls_rest,
            by simp [List.mapM_cons, hlev1, hls_rest, bind, Except.bind, pure, Except.pure]⟩
      exact hgo uIdxs.toList ls hls
    obtain ⟨ls_p, hls_p⟩ := hlevels
    exact ⟨.const k ls_p,
      by simp [Ix.Kernel.Reader.convExpr, hself_m, hm_k, hls_p, bind, Except.bind, pure, Except.pure]⟩
  | @prj _ _ tIdx fIdx _ a _ _ _ _ _ href _ _ _ _ ih =>
    intro n hn hbnd hkeys
    obtain ⟨k, hk⟩ := hkeys tIdx.toNat (by simp [reachRefsExpr]) a href
    have href_arr : ecx.src.refs[tIdx.toNat]? = some a := by
      rw [← Array.getElem?_toList, hrefs, href]
    have hkeyAt : ecx.keyAt tIdx = .ok k := by
      simp [Ix.Kernel.Reader.ECx.keyAt, href_arr, hk]
    obtain ⟨Ein, hEin⟩ := ih hn hbnd (fun idx hidx =>
      hkeys idx (by simp [reachRefsExpr, hidx]))
    exact ⟨.proj k fIdx.toNat Ein,
      by simp [Ix.Kernel.Reader.convExpr, hkeyAt, hEin, bind, Except.bind, pure, Except.pure]⟩
  | @str _ _ bIdx a bs s _ _ href hmem _ hs _ =>
    intro _ _ _ _
    have href_arr : ecx.src.refs[bIdx.toNat]? = some a := by
      rw [← Array.getElem?_toList, hrefs, href]
    have hblob := hblob_ok a ⟨bs.toArray⟩ hmem
    have hs_utf8 : String.fromUTF8? ⟨bs.toArray⟩ = some s := hs
    exact ⟨.lit (.strVal s),
      by simp [Ix.Kernel.Reader.convExpr, Ix.Kernel.Reader.ECx.blobAt, href_arr, hblob, hs_utf8,
        bind, Except.bind, pure, Except.pure]⟩
  | @nat _ _ bIdx a bs _ _ _ href hmem hcanon _ _ _ _ =>
    intro _ _ _ _
    have href_arr : ecx.src.refs[bIdx.toNat]? = some a := by
      rw [← Array.getElem?_toList, hrefs, href]
    have hblob := hblob_ok a ⟨bs.toArray⟩ hmem
    exact ⟨.lit (.natVal (Ix.Kernel.Reader.natural ⟨bs.toArray⟩)),
      by simp [Ix.Kernel.Reader.convExpr, Ix.Kernel.Reader.ECx.natAt,
        Ix.Kernel.Reader.ECx.blobAt, href_arr, hblob, hcanon,
        bind, Except.bind, pure, Except.pure]⟩
  | app _ _ _ ihf iha =>
    intro n hn hbnd hkeys
    obtain ⟨Ef, hEf⟩ := ihf hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_left _ hidx))
    obtain ⟨Ea, hEa⟩ := iha hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_right _ hidx))
    exact ⟨.app Ef Ea,
      by simp [Ix.Kernel.Reader.convExpr, hEf, hEa, bind, Except.bind, pure, Except.pure]⟩
  | lam _ _ _ _ iht ihb =>
    intro n hn hbnd hkeys
    obtain ⟨Et, hEt⟩ := iht hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_left _ hidx))
    obtain ⟨Eb, hEb⟩ := ihb hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_right _ hidx))
    exact ⟨.lam Et Eb Ix.Kernel.BinderMeta.leanNever,
      by simp [Ix.Kernel.Reader.convExpr, hEt, hEb, bind, Except.bind, pure, Except.pure]⟩
  | all _ _ _ _ iht ihb =>
    intro n hn hbnd hkeys
    obtain ⟨Et, hEt⟩ := iht hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_left _ hidx))
    obtain ⟨Eb, hEb⟩ := ihb hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_right _ hidx))
    exact ⟨.forallE Et Eb Ix.Kernel.BinderMeta.leanNever,
      by simp [Ix.Kernel.Reader.convExpr, hEt, hEb, bind, Except.bind, pure, Except.pure]⟩
  | letE _ _ _ iht ihv ihb =>
    intro n hn hbnd hkeys
    obtain ⟨Et, hEt⟩ := iht hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_left _ (List.mem_append_left _ hidx)))
    obtain ⟨Ev, hEv⟩ := ihv hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_left _ (List.mem_append_right _ hidx)))
    obtain ⟨Eb, hEb⟩ := ihb hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_right _ hidx))
    exact ⟨.letE Et Ev Eb { nonDep := _ },
      by simp [Ix.Kernel.Reader.convExpr, hEt, hEv, hEb, bind, Except.bind, pure, Except.pure]⟩
  | @share bnd idx s _ hidx hsh_get _ ih =>
    intro n hn hbnd hkeys
    have hi_len : idx.toNat < sharing.length := (List.getElem?_eq_some_iff.mp hsh_get).1
    have hi_n : idx.toNat < n := by omega
    simp only [Ix.Kernel.Reader.convExpr]
    rw [L1.buildShareTbl_take_getElem? ecx sharing hi_n hsh_get]
    -- Show `reachRefsExpr (buildReachRefsTbl sharing) s` subsets `reachRefsExpr (buildReachRefsTbl sharing) (.share idx)`:
    have hreach_sub : ∀ j ∈ reachRefsExpr (buildReachRefsTbl sharing) s,
        j ∈ reachRefsExpr (buildReachRefsTbl sharing) (.share idx) := by
      have hget_full := buildReachRefsTbl_take_getElem? sharing hi_len hsh_get
      simp only [List.take_length] at hget_full
      -- Wait: `buildReachRefsTbl_take_getElem?` requires `idx.toNat < sharing.length`, so `take sharing.length`:
      have hget_full' := buildReachRefsTbl_take_getElem? sharing (n := sharing.length) hi_len hsh_get
      simp only [List.take_length] at hget_full'
      -- Also `reachRefsExpr (buildReachRefsTbl (sharing.take idx.toNat)) s = reachRefsExpr (buildReachRefsTbl sharing) s`
      -- for indices `< idx.toNat`! Let's prove `reachRefsExpr_congr` inline on `raw`? Even simpler:
      -- `s` only uses `.share j` with `j < idx.toNat`! Wait: what if `s` has a dead branch? No, `RawConvExpr` walked ALL of `s`!
      intro j hj
      simp only [reachRefsExpr, hget_full', Option.getD_some]
      -- We just need `reachRefsExpr (buildReachRefsTbl sharing) s = reachRefsExpr (buildReachRefsTbl (sharing.take idx.toNat)) s`!
      have hcongr : ∀ {b' : Nat} {e' : Ixon.Expr} {kp' : SourceValue F},
          L1.RawConvExpr refs recurAddrs univs sharing blobs h b' e' kp' →
          b' ≤ idx.toNat →
          reachRefsExpr (buildReachRefsTbl sharing) e' =
            reachRefsExpr (buildReachRefsTbl (sharing.take idx.toNat)) e' := by
        intro b' e' kp' r'
        induction r' with
        | var _ _ | sort _ _ _ _ | ref _ _ _ _ _ _ _ | recur _ _ _ _ _ _ _
        | str _ _ _ _ _ _ | nat _ _ _ _ _ _ _ _ => intro _; rfl
        | prj _ _ _ _ _ _ _ ih' =>
          intro hb'; simp [reachRefsExpr, ih' hb']
        | app _ _ _ ih1 ih2 =>
          intro hb'; simp [reachRefsExpr, ih1 hb', ih2 hb']
        | lam _ _ _ _ ih1 ih2 =>
          intro hb'; simp [reachRefsExpr, ih1 hb', ih2 hb']
        | all _ _ _ _ ih1 ih2 =>
          intro hb'; simp [reachRefsExpr, ih1 hb', ih2 hb']
        | letE _ _ _ ih1 ih2 ih3 =>
          intro hb'; simp [reachRefsExpr, ih1 hb', ih2 hb', ih3 hb']
        | @share b2 idx2 s2 _ hidx2 hsh2 _ _ =>
          intro hb'
          have h2_lt : idx2.toNat < idx.toNat := by omega
          have h2_len : idx2.toNat < sharing.length := (List.getElem?_eq_some_iff.mp hsh2).1
          have hg1 := buildReachRefsTbl_take_getElem? sharing (n := sharing.length) h2_len hsh2
          simp only [List.take_length] at hg1
          have hg2 := buildReachRefsTbl_take_getElem? sharing (n := idx.toNat) h2_lt hsh2
          have hsh2_take : (sharing.take idx.toNat)[idx2.toNat]? = some s2 := by
            rw [List.getElem?_take_of_lt h2_lt]
            exact hsh2
          have hg2' := buildReachRefsTbl_take_getElem? (sharing.take idx.toNat)
            (n := (sharing.take idx.toNat).length)
            (by simp [Nat.min_eq_left (Nat.le_of_lt hi_len), h2_lt]) hsh2_take
          simp only [List.take_length, List.take_take, Nat.min_eq_left (Nat.le_of_lt h2_lt)] at hg2'
          simp [reachRefsExpr, hg1, hg2']
      rw [← hcongr ‹_› (Nat.le_refl _)]
      exact hj
    exact ih (Nat.le_of_lt hi_len) (Nat.min_le_left _ _) (fun j hj => hkeys j (hreach_sub j hj))

/-- **`MemberReader.read` succeeds on any root `RawConvExpr`** once `cx.keyAt` succeeds on its
reachable `.ref`/`.prj` references, `self` succeeds on `recurAddrs`, and `cx.blob` covers `blobs`. -/
theorem memberReader_read_ok_of_rawConvExpr
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (hself_ok : ∀ i a, recurAddrs[i]? = some a → ∃ m k, self i = some m ∧ m = .ok k)
    (hblob_ok : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    (hkeys : ∀ idx ∈ reachRefsExpr (buildReachRefsTbl src.sharing.toList) e,
      ∀ a, src.refs[idx]? = some a → ∃ k, cx.keyAt a = .ok k) :
    ∃ E_rd : Core.KExpr,
      (Ix.Kernel.Reader.MemberReader.mk' cx src param self).read e = .ok E_rd := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq cx src param self
  unfold Ix.Kernel.Reader.MemberReader.read
  rw [hecx, htbl, ← List.take_length (l := src.sharing.toList)]
  exact convExpr_ok_of_rawConvExpr rfl (by simp) hself_ok hblob_ok raw
    (Nat.le_refl _) (Nat.min_le_right _ _)
    (fun idx hidx a ha => hkeys idx hidx a (by rwa [Array.getElem?_toList]))

/-! ### `validate_univ_params_seen`, `validate_univ_params_list`, and `validate_expr_well_scoped` -/

/-- `KernelCheck::validate_univ_params_seen` ensures every parameter in a `RawKLevel` lies in
`List.range nlvls`. -/
theorem validate_univ_params_seen_spec {h h' : Heap F} {u : Core.KLevel}
    {lp r : SourceValue F} {nlvls : Nat} {cs : List (Call F)}
    (hn : nlvls < 4294967296)
    (rl : L1.RawKLevel h u lp)
    (ev : ObsFn Core.W "KernelCheck::validate_univ_params_seen" [lp, .field (nlvls : F)] h r h' cs) :
    h' = h ∧ u.allParamsDefined (List.range nlvls) = true := by
  induction rl generalizing r h' cs with
  | zero cell =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Zero ld _ hh _ => exact ⟨hh, rfl⟩
    | Succ _ _ ld _ _ | Max _ _ _ _ _ _ ld _ _ _ | IMax _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | succ _ cell ih =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Succ x_in _ ld ev_in _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs
      subst hxs
      exact ih ev_in
    | Zero ld _ _ _ | Max _ _ _ _ _ _ ld _ _ _ | IMax _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | max _ _ cell iha ihb =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Max x_a x_b _ m1 _ _ ld eva evb _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain ⟨rfl, ha⟩ := iha eva
      obtain ⟨hh', hb⟩ := ihb evb
      exact ⟨hh', by simp [Ix.Kernel.Level.allParamsDefined, ha, hb]⟩
    | Zero ld _ _ _ | Succ _ _ ld _ _ | IMax _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | imax _ _ cell iha ihb =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | IMax x_a x_b _ m1 _ _ ld eva evb _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain ⟨rfl, ha⟩ := iha eva
      obtain ⟨hh', hb⟩ := ihb evb
      exact ⟨hh', by simp [Ix.Kernel.Level.allParamsDefined, ha, hb]⟩
    | Zero ld _ _ _ | Succ _ _ ld _ _ | Max _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | @param _ i hi cell =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Param x_i _ _ _ ld ev_lt heq _ hh _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs
      subst hxs
      obtain ⟨a, b, ha, hb, hxa, hxb, hr_lt, hm_eq⟩ := L1.lt_fields_both_spec ev_lt
      have hP : (72057594037927936 : Nat) < U32.Goldilocks.modulus := by decide
      have ha_eq : a = i := by
        have h1 := Value.field.inj hxa
        have h2 := congrArg ZMod.val h1
        rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (Nat.lt_trans hi hP)] at h2
      have hb_eq : b = nlvls := by
        have h1 := Value.field.inj hxb
        have h2 := congrArg ZMod.val h1
        rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h2
      subst ha_eq; subst hb_eq
      have hlt : i < nlvls := by
        by_cases hlt' : i < nlvls
        · exact hlt'
        · simp [hlt'] at hr_lt
          rw [hr_lt] at heq
          have h01 := Value.field.inj heq
          exact absurd (congrArg ZMod.val h01) (by decide)
      exact ⟨hh.trans hm_eq, by simp [Ix.Kernel.Level.allParamsDefined, List.mem_range, hlt]⟩
    | Zero ld _ _ _ | Succ _ _ ld _ _ | Max _ _ _ _ _ _ ld _ _ _
    | IMax _ _ _ _ _ _ ld _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim

/-- `validate_univ_params_seen` on an arbitrary `KernelLevels.RepKLevel` preserves the heap (`h' = h`). -/
private theorem validate_univ_params_seen_heap {h h' : Heap F} {ℓ : Core.KLevel}
    {lp x_bound r : SourceValue F} {cs : List (Call F)}
    (rl : KernelLevels.RepKLevel h ℓ lp)
    (ev : ObsFn Core.W "KernelCheck::validate_univ_params_seen" [lp, x_bound] h r h' cs) :
    h' = h := by
  induction rl generalizing r h' cs with
  | zero cell =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Zero _ _ hh _ => exact hh
    | Succ _ _ ld _ _ | Max _ _ _ _ _ _ ld _ _ _ | IMax _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | succ cell _ ih =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Succ _ _ ld ev_in _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs; subst hxs
      exact ih ev_in
    | Zero ld _ _ _ | Max _ _ _ _ _ _ ld _ _ _ | IMax _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | max cell _ _ iha ihb =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Max _ _ _ _ _ _ ld eva evb _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs; obtain ⟨rfl, rfl⟩ := hxs
      obtain rfl := iha eva
      exact ihb evb
    | Zero ld _ _ _ | Succ _ _ ld _ _ | IMax _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | imax cell _ _ iha ihb =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | IMax _ _ _ _ _ _ ld eva evb _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs; obtain ⟨rfl, rfl⟩ := hxs
      obtain rfl := iha eva
      exact ihb evb
    | Zero ld _ _ _ | Succ _ _ ld _ _ | Max _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | param cell _ =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Param _ _ _ _ ld ev_lt _ _ hh _ =>
      obtain ⟨_, _, _, _, _, _, _, hm⟩ := L1.lt_fields_both_spec ev_lt
      exact hh.trans hm
    | Zero ld _ _ _ | Succ _ _ ld _ _ | Max _ _ _ _ _ _ ld _ _ _
    | IMax _ _ _ _ _ _ ld _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim

/-- `KernelCheck::validate_univ_params_list` ensures every level in a `RawKLevelList` has all
parameters in `List.range nlvls` and preserves the heap. -/
theorem validate_univ_params_list_spec {h h' : Heap F} {ls : List Core.KLevel}
    {lsp r : SourceValue F} {nlvls : Nat} {cs : List (Call F)}
    (hn : nlvls < 4294967296)
    (rls : L1.RawKLevelList h ls lsp)
    (ev : ObsFn Core.W "KernelCheck::validate_univ_params_list" [lsp, .field (nlvls : F)] h r h' cs) :
    h' = h ∧ ls.all (Ix.Kernel.Level.allParamsDefined (List.range nlvls)) = true := by
  induction rls generalizing r h' cs with
  | nil cell =>
    cases «KernelCheck::validate_univ_params_list».obs ev with
    | Nil _ _ hh _ => exact ⟨hh, rfl⟩
    | Cons _ _ _ _ _ _ ld _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | cons cell rl _ ih =>
    cases «KernelCheck::validate_univ_params_list».obs ev with
    | Cons _ _ _ _ _ _ ld ev_hd ev_tl _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain ⟨rfl, hhd⟩ := validate_univ_params_seen_spec hn rl ev_hd
      obtain ⟨hh', htl⟩ := ih ev_tl
      exact ⟨hh', by simp [hhd, htl]⟩
    | Nil ld _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim

/-- Top-down heap-pointer reachability on initial heap `h₀` among `KExprNode` cells, used to bound
binder depth `d ≤ steps < 2 ^ 39` via `RomBound.bounded_descent_lt`. -/
inductive KExprReach (h₀ : Heap F) : SourceValue F → SourceValue F → Nat → Prop where
  | refl (p : SourceValue F) : KExprReach h₀ p p 0
  | snoc {p q q' : SourceValue F} {addr steps : Nat} {v : Value F} :
      KExprReach h₀ p q steps →
      q = .ptr (.enum Core.kexprEnum) addr →
      h₀[addr]? = some v →
      v.type = .enum Core.kexprEnum →
      q' ∈ RomBound.cellArgs v →
      KExprReach h₀ p q' (steps + 1)

private theorem kexprReach_to_heapDescent {h₀ : Heap F} :
    ∀ {p q : SourceValue F} {steps : Nat},
      KExprReach h₀ p q steps →
      ∀ { tailSteps : Nat },
        RomBound.HeapDescent h₀ (.enum Core.kexprEnum) q tailSteps →
        RomBound.HeapDescent h₀ (.enum Core.kexprEnum) p (steps + tailSteps)
  | _, _, _, .refl _, _, htail => by simpa using htail
  | _, _, _, .snoc hprev rfl hcell hty harg, tailSteps, htail => by
    have hd : RomBound.HeapDescent h₀ (.enum Core.kexprEnum) _ (tailSteps + 1) :=
      .down hcell hty harg htail
    have hall := kexprReach_to_heapDescent hprev hd
    simpa [Nat.add_assoc, Nat.add_comm 1 tailSteps] using hall

private theorem kexprReach_steps_lt {calls : List (Call F)} {h₀ : Heap F}
    {root q : SourceValue F} {c₀ : Call F} {steps addr : Nat} {v : Value F}
    (hbound : IxVM.Consistency.Bounded calls)
    (hc₀ : c₀ ∈ calls) (hheap₀ : c₀.heap = h₀) (harg₀ : root ∈ c₀.args)
    (hreach : KExprReach h₀ root q steps)
    (hq : q = .ptr (.enum Core.kexprEnum) addr)
    (hcell : h₀[addr]? = some v)
    (hty : v.type = .enum Core.kexprEnum) :
    steps < 2 ^ 39 := by
  subst hq; subst hheap₀
  have hleaf : RomBound.HeapDescent c₀.heap (.enum Core.kexprEnum)
      (.ptr (.enum Core.kexprEnum) addr) 0 :=
    .here hcell hty
  have hdesc := kexprReach_to_heapDescent hreach hleaf
  simp only [Nat.add_zero] at hdesc
  exact RomBound.bounded_descent_lt hbound hc₀ harg₀ hdesc

/-- Helper: `Lists::length<&KernelTypes::KLevelNode>` preserves the heap on a `RawKLevelList`. -/
private theorem klevel_length_heap {h h' : Heap F} {ls : List Core.KLevel}
    {lsp r : SourceValue F} {cs : List (Call F)}
    (rls : L1.RawKLevelList h ls lsp)
    (ev : ObsFn Core.W Names.«Lists::length<&KernelTypes::KLevelNode>» [lsp] h r h' cs) :
    h' = h := by
  have hsym : (Instance.mk "Lists::length" [.ptr (.named Core.klevelEnum [])]).symbol =
      Names.«Lists::length<&KernelTypes::KLevelNode>» := by decide +kernel
  have hlist_sym : (Instance.mk "Lists::Node" [.ptr (.named Core.klevelEnum [])]).symbol =
      Core.klevelListEnum := by decide +kernel
  have hrep : Aiur.Library.List.RepList
      (Instance.mk "Lists::Node" [.ptr (.named Core.klevelEnum [])]).symbol
      (fun h' l p => L1.RawKLevel h' l p) h ls lsp := by
    rw [hlist_sym]
    induction rls with
    | nil cell => exact .nil cell
    | cons cell rl _ ih => exact .cons cell rl ih
  rw [← hsym] at ev
  exact (Lib.Lists.length_spec ev hrep).2

/-- Helper: `KernelInfer::const_num_lvls` preserves the heap (`h' = h`). -/
private theorem const_num_lvls_heap {v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Core.W "KernelInfer::const_num_lvls" [v] h r h' cs) :
    h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelInfer.const_num_lvls.lookup
    (by simp [IxVM.KernelInfer.const_num_lvls, ControlLower.hasControl]) ev
  simp only [IxVM.KernelInfer.const_num_lvls] at d0
  obtain ⟨_, m2, _, _, _, _, d_sc, sel, d_arm, _⟩ := d0.matchValue_inv
  obtain ⟨_, rfl, rfl⟩ := d_sc.var_inv
  repeat (
    rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
    · obtain ⟨_, rfl, rfl⟩ := d_arm.var_inv
      rfl)
  exact (selectArm_nil_inv sel).elim

private theorem convExpr_levels_allParamsDefined {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : List Ixon.Univ} {nlvls : Nat}
    (hunivs : ecx.univs = univs.toArray.map (Ix.Kernel.Reader.convUniv id))
    {us : List UInt64} {ls ls_rd : List Core.KLevel}
    (hls : us.mapM (fun i => univs[i.toNat]?.map (Ix.Kernel.Reader.convUniv id)) = some ls)
    (hrd : us.mapM ecx.level = .ok ls_rd) :
    ls_rd = ls := by
  induction us generalizing ls ls_rd with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hls
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hrd
    exact hrd.symm.trans hls
  | cons u rest ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind] at hls
    obtain ⟨l1, hl1, hm2⟩ := Option.bind_eq_some_iff.mp hls
    obtain ⟨lrest, hlrest, hls_eq⟩ := Option.bind_eq_some_iff.mp hm2
    injection hls_eq with hls_eq'; subst hls_eq'
    obtain ⟨u_raw, hu_raw, rfl⟩ := Option.map_eq_some_iff.mp hl1
    have hu_arr : ecx.univs[u.toNat]? = some (Ix.Kernel.Reader.convUniv id u_raw) := by
      rw [hunivs, Array.getElem?_map, Array.getElem?_toList, hu_raw]
      rfl
    have hlev1 : ecx.level u = .ok (Ix.Kernel.Reader.convUniv id u_raw) := by
      simp [Ix.Kernel.Reader.ECx.level, hu_arr, pure, Except.pure]
    simp only [List.mapM_cons, hlev1, bind, Except.bind] at hrd
    cases hrest_rd : rest.mapM ecx.level with
    | error e => simp [hrest_rd] at hrd
    | ok ls_r =>
      simp only [hrest_rd, pure, Except.pure, Except.ok.injEq] at hrd
      subst hrd
      rw [ih hlrest hrest_rd]

/-- **Core specification of `KernelCheck::validate_expr_well_scoped`**: on any `RawConvExpr` on
initial heap `h₀` converted by `convExpr` to `E_rd`, `validate_expr_well_scoped [kp, .field d, .field nlvls]`
on any heap extension `h` of `h₀` yields `Heap.Extends h h'`, `E_rd.looseBVarsBounded d = true`,
and `E_rd.allLevelParamsDefined (List.range nlvls) = true`. -/
private theorem validate_expr_well_scoped_go
    {calls : List (Call F)} {c₀ : Call F} {h₀ : Heap F} {root : SourceValue F}
    (hbound : IxVM.Consistency.Bounded calls)
    (hc₀ : c₀ ∈ calls) (hheap₀ : c₀.heap = h₀) (harg₀ : root ∈ c₀.args)
    {ecx : Ix.Kernel.Reader.ECx .anon}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    (hrefs : ecx.src.refs.toList = refs)
    (hunivs : ecx.univs = univs.toArray.map (Ix.Kernel.Reader.convUniv id))
    {nlvls : Nat} (hnlvls : nlvls < 4294967296)
    {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr refs recurAddrs univs sharing blobs h₀ bound e kp) :
    ∀ {n d steps : Nat} {E_rd : Core.KExpr} {h h' : Heap F} {r : SourceValue F}
      {cs : List (Call F)},
      n ≤ sharing.length →
      bound ≤ min n 4294967295 →
      d ≤ steps →
      KExprReach h₀ root kp steps →
      Heap.Extends h₀ h →
      (∀ cl ∈ cs, cl ∈ calls) →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (sharing.take n)) e = .ok E_rd →
      ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
        [kp, .field (d : F), .field (nlvls : F)] h r h' cs →
      Heap.Extends h h' ∧
        E_rd.looseBVarsBounded d = true ∧
        E_rd.allLevelParamsDefined (List.range nlvls) = true := by
  induction raw with
  | @var _ addr idx hidx cell =>
    intro n d steps E_rd h h' r cs _ _ hd_le hreach hext _ hconv ev
    have hd_lt39 : steps < 2 ^ 39 :=
      kexprReach_steps_lt hbound hc₀ hheap₀ harg₀ hreach rfl cell (by simp [Value.type])
    have hd_lt32_or : d < U32.Goldilocks.modulus := by
      unfold U32.Goldilocks.modulus; omega
    simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq] at hconv
    subst hconv
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | BVar x_i _ _ _ ld ev_lt heq _ hh _ =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs; subst hxs
      obtain ⟨a, b, ha, hb, hxa, hxb, hr_lt, hm_eq⟩ := L1.lt_fields_both_spec ev_lt
      have hP : (72057594037927936 : Nat) < U32.Goldilocks.modulus := by decide
      have ha_eq : a = idx.toNat := by
        have h2 := congrArg ZMod.val (Value.field.inj hxa)
        rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (Nat.lt_trans hidx hP)] at h2
      have hb_eq : b = d := by
        have h2 := congrArg ZMod.val (Value.field.inj hxb)
        rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt hd_lt32_or] at h2
      subst ha_eq; subst hb_eq
      have hlt : idx.toNat < d := by
        by_cases hlt' : idx.toNat < d
        · exact hlt'
        · simp [hlt'] at hr_lt
          rw [hr_lt] at heq
          exact absurd (congrArg ZMod.val (Value.field.inj heq)) (by decide)
      rw [hh, hm_eq]
      have hmkBvar : (Ix.Kernel.Expr.mkBvar idx.toNat : Core.KExpr) = .bvar idx.toNat := rfl
      rw [hmkBvar]
      exact ⟨Heap.Extends.refl _, by simp [Ix.Kernel.Expr.looseBVarsBounded, hlt], rfl⟩
    | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @sort _ addr uIdx u lp _ hu rl cell =>
    intro n d steps E_rd h h' r cs _ _ _ _ hext _ hconv ev
    have hu_arr : ecx.univs[uIdx.toNat]? = some (Ix.Kernel.Reader.convUniv id u) := by
      rw [hunivs, Array.getElem?_map, Array.getElem?_toList, hu]
      rfl
    simp only [Ix.Kernel.Reader.convExpr, Ix.Kernel.Reader.ECx.level, hu_arr,
      pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hconv
    subst hconv
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Srt x_l _ ld ev_u _ =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs; subst hxs
      obtain ⟨hh', hdef⟩ := validate_univ_params_seen_spec hnlvls (rl.mono hext) ev_u
      rw [hh']
      exact ⟨Heap.Extends.refl _, rfl, hdef⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @ref _ addr rIdx uIdxs a d_arr ap lsp ls _ href _ ra hls rls cell =>
    intro n d steps E_rd h h' r cs _ _ _ _ hext hsub hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨k_rd, _, hbind2⟩ := L1.except_bind_eq_ok hconv
    obtain ⟨ls_rd, hls_rd, hret⟩ := L1.except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have hls_eq := convExpr_levels_allParamsDefined hunivs hls hls_rd
    subst hls_eq
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Const x_addr x_lvls v130 m131 p138 cs144 v155 m156 _ v188 m191 _ _
        ld ev_gci _ ev_cnl ev_len _ ev_vl hc_cs =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      have hsub_gci : ∀ cl ∈ cs144, cl ∈ calls := fun cl hm =>
        hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hm))
      have hbound_gci := RomBound.bounded_mono hbound hsub_gci
      obtain ⟨ext1, _, _, _, _, _, _⟩ :=
        L1.get_ci_loadedL1_spec hbound_gci (Aiur.Library.Bytes.repAddressRef_heapMono₂ _ hext ra) ev_gci
      have hm156 := const_num_lvls_heap ev_cnl
      subst hm156
      have hrls_m131 := (rls.mono hext).mono ext1
      have hm191 := klevel_length_heap hrls_m131 ev_len
      subst hm191
      obtain ⟨hh', hdef⟩ := validate_univ_params_list_spec hnlvls hrls_m131 ev_vl
      rw [hh']
      exact ⟨ext1, rfl, hdef⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @recur _ addr rIdx uIdxs a d_arr ap lsp ls _ _ _ ra hls rls cell =>
    intro n d steps E_rd h h' r cs _ _ _ _ hext hsub hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hs_opt : ecx.self rIdx.toNat with
    | none => simp [hs_opt, Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at hconv
    | some m_self =>
      simp only [hs_opt] at hconv
      obtain ⟨k_rd, _, hbind2⟩ := L1.except_bind_eq_ok hconv
      obtain ⟨ls_rd, hls_rd, hret⟩ := L1.except_bind_eq_ok hbind2
      injection hret with hE; subst hE
      have hls_eq := convExpr_levels_allParamsDefined hunivs hls hls_rd
      subst hls_eq
      have cell_h := hext.getElem?_eq cell
      cases «KernelCheck::validate_expr_well_scoped».obs ev with
      | Const x_addr x_lvls v130 m131 p138 cs144 v155 m156 _ v188 m191 _ _
          ld ev_gci _ ev_cnl ev_len _ ev_vl hc_cs =>
        have hxs := (Core.load_cell cell_h ld).2
        simp only [List.cons.injEq, and_true] at hxs
        obtain ⟨rfl, rfl⟩ := hxs
        have hsub_gci : ∀ cl ∈ cs144, cl ∈ calls := fun cl hm =>
          hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hm))
        have hbound_gci := RomBound.bounded_mono hbound hsub_gci
        obtain ⟨ext1, _, _, _, _, _, _⟩ :=
          L1.get_ci_loadedL1_spec hbound_gci (Aiur.Library.Bytes.repAddressRef_heapMono₂ _ hext ra) ev_gci
        have hm156 := const_num_lvls_heap ev_cnl
        subst hm156
        have hrls_m131 := (rls.mono hext).mono ext1
        have hm191 := klevel_length_heap hrls_m131 ev_len
        subst hm191
        obtain ⟨hh', hdef⟩ := validate_univ_params_list_spec hnlvls hrls_m131 ev_vl
        rw [hh']
        exact ⟨ext1, rfl, hdef⟩
      | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _
      | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
      | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
      | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
        exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @prj _ addr tIdx fIdx _ _ _ _ ip _ _ _ _ _ _ cell ih =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hsub hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨k_rd, _, hbind2⟩ := L1.except_bind_eq_ok hconv
    obtain ⟨Ein_rd, hEin_rd, hret⟩ := L1.except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Proj _ _ x_e1 cs1 ld ev1 hc_cs =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨_, _, rfl⟩ := hxs
      have hreach1 : KExprReach h₀ root ip (steps + 1) :=
        .snoc hreach rfl cell (by simp [Value.type]) (by simp [RomBound.cellArgs])
      exact ih hn hbnd (by omega) hreach1 hext
        (fun cl hm => hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ hm)) hEin_rd ev1
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Lit _ ld _ _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | str _ _ _ _ _ cell =>
    intro n d steps E_rd h h' r cs _ _ _ _ hext _ hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, _, h2⟩ := L1.except_bind_eq_ok hconv
    cases hutf : String.fromUTF8? _ with
    | none => rw [hutf] at h2; simp [Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at h2
    | some s =>
      rw [hutf] at h2
      injection h2 with hE; subst hE
      have cell_h := hext.getElem?_eq cell
      cases «KernelCheck::validate_expr_well_scoped».obs ev with
      | Lit _ _ _ hh _ => rw [hh]; exact ⟨Heap.Extends.refl _, rfl, rfl⟩
      | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
      | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
      | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
      | Proj _ _ _ _ ld _ _ =>
        exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | nat _ _ _ _ _ _ _ cell =>
    intro n d steps E_rd h h' r cs _ _ _ _ hext _ hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, _, h2⟩ := L1.except_bind_eq_ok hconv
    injection h2 with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Lit _ _ _ hh _ => rw [hh]; exact ⟨Heap.Extends.refl _, rfl, rfl⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @app _ addr _ _ fp ap _ _ cell ihf iha =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hsub hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Ef_rd, hEf, hbind2⟩ := L1.except_bind_eq_ok hconv
    obtain ⟨Ea_rd, hEa, hret⟩ := L1.except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | App x_f x_a _ m1 cs1 cs2 ld ev1 ev2 hc_cs =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      have hrf : KExprReach h₀ root fp (steps + 1) :=
        .snoc hreach rfl cell (by simp [Value.type]) (by simp [RomBound.cellArgs])
      have hra : KExprReach h₀ root ap (steps + 1) :=
        .snoc hreach rfl cell (by simp [Value.type]) (by simp [RomBound.cellArgs])
      obtain ⟨ext1, hl1, hd1⟩ := ihf hn hbnd (by omega) hrf hext
        (fun cl hm => hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)))
        hEf ev1
      obtain ⟨ext2, hl2, hd2⟩ := iha hn hbnd (by omega) hra (hext.trans ext1)
        (fun cl hm => hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hm))))
        hEa ev2
      exact ⟨ext1.trans ext2,
        by simp [Ix.Kernel.Expr.looseBVarsBounded, hl1, hl2],
        by simp [Ix.Kernel.Expr.allLevelParamsDefined, hd1, hd2]⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @lam _ addr _ _ tp bp lp ℓ rl _ _ cell iht ihb =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hsub hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et_rd, hEt, hbind2⟩ := L1.except_bind_eq_ok hconv
    obtain ⟨Eb_rd, hEb, hret⟩ := L1.except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Lam x_t x_b x_l _ m1 cs_l _ m2 cs_t cs_b v_d1 ld ev_l ev_t hop ev_b hc_cs =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      have hm1 := validate_univ_params_seen_heap (KernelLevels.RepKLevel.mono hext rl) ev_l
      subst hm1
      have hrt : KExprReach h₀ root tp (steps + 1) :=
        .snoc hreach rfl cell (by simp [Value.type]) (by simp [RomBound.cellArgs])
      have hrb : KExprReach h₀ root bp (steps + 1) :=
        .snoc hreach rfl cell (by simp [Value.type]) (by simp [RomBound.cellArgs])
      have hd1_eq : v_d1 = .field ((d + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at hop
        rw [← hop]
        push_cast
        rfl
      rw [hd1_eq] at ev_b
      obtain ⟨ext1, hl1, hd1⟩ := iht hn hbnd (by omega) hrt hext
        (fun cl hm => hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm)))))
        hEt ev_t
      obtain ⟨ext2, hl2, hd2⟩ := ihb hn hbnd (by omega) hrb (hext.trans ext1)
        (fun cl hm => hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hm))))))
        hEb ev_b
      exact ⟨ext1.trans ext2,
        by simp [Ix.Kernel.Expr.looseBVarsBounded, hl1, hl2],
        by simp [Ix.Kernel.Expr.allLevelParamsDefined, hd1, hd2,
          Ix.Kernel.BinderMeta.leanNever, Ix.Kernel.PropWhen.paramsDefined]⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @all _ addr _ _ tp bp lp ℓ rl _ _ cell iht ihb =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hsub hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et_rd, hEt, hbind2⟩ := L1.except_bind_eq_ok hconv
    obtain ⟨Eb_rd, hEb, hret⟩ := L1.except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Forall x_t x_b x_l _ m1 cs_l _ m2 cs_t cs_b v_d1 ld ev_l ev_t hop ev_b hc_cs =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      have hm1 := validate_univ_params_seen_heap (KernelLevels.RepKLevel.mono hext rl) ev_l
      subst hm1
      have hrt : KExprReach h₀ root tp (steps + 1) :=
        .snoc hreach rfl cell (by simp [Value.type]) (by simp [RomBound.cellArgs])
      have hrb : KExprReach h₀ root bp (steps + 1) :=
        .snoc hreach rfl cell (by simp [Value.type]) (by simp [RomBound.cellArgs])
      have hd1_eq : v_d1 = .field ((d + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at hop
        rw [← hop]
        push_cast
        rfl
      rw [hd1_eq] at ev_b
      obtain ⟨ext1, hl1, hd1⟩ := iht hn hbnd (by omega) hrt hext
        (fun cl hm => hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm)))))
        hEt ev_t
      obtain ⟨ext2, hl2, hd2⟩ := ihb hn hbnd (by omega) hrb (hext.trans ext1)
        (fun cl hm => hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hm))))))
        hEb ev_b
      exact ⟨ext1.trans ext2,
        by simp [Ix.Kernel.Expr.looseBVarsBounded, hl1, hl2],
        by simp [Ix.Kernel.Expr.allLevelParamsDefined, hd1, hd2,
          Ix.Kernel.BinderMeta.leanNever, Ix.Kernel.PropWhen.paramsDefined]⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @letE _ addr _ _ _ _ _ tp vp bp _ _ _ cell iht ihv ihb =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hsub hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et_rd, hEt, hbind2⟩ := L1.except_bind_eq_ok hconv
    obtain ⟨Ev_rd, hEv, hbind3⟩ := L1.except_bind_eq_ok hbind2
    obtain ⟨Eb_rd, hEb, hret⟩ := L1.except_bind_eq_ok hbind3
    injection hret with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Let x_t x_v x_b _ m1 cs_t _ m2 cs_v cs_b v_d1 ld ev_t ev_v hop ev_b hc_cs =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      have hrt : KExprReach h₀ root tp (steps + 1) :=
        .snoc hreach rfl cell (by simp [Value.type]) (by simp [RomBound.cellArgs])
      have hrv : KExprReach h₀ root vp (steps + 1) :=
        .snoc hreach rfl cell (by simp [Value.type]) (by simp [RomBound.cellArgs])
      have hrb : KExprReach h₀ root bp (steps + 1) :=
        .snoc hreach rfl cell (by simp [Value.type]) (by simp [RomBound.cellArgs])
      have hd1_eq : v_d1 = .field ((d + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at hop
        rw [← hop]
        push_cast
        rfl
      rw [hd1_eq] at ev_b
      obtain ⟨ext1, hl1, hd1⟩ := iht hn hbnd (by omega) hrt hext
        (fun cl hm => hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)))
        hEt ev_t
      obtain ⟨ext2, hl2, hd2⟩ := ihv hn hbnd (by omega) hrv (hext.trans ext1)
        (fun cl hm => hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm)))))
        hEv ev_v
      obtain ⟨ext3, hl3, hd3⟩ := ihb hn hbnd (by omega) hrb ((hext.trans ext1).trans ext2)
        (fun cl hm => hsub cl (by rw [hc_cs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hm))))))
        hEb ev_b
      exact ⟨(ext1.trans ext2).trans ext3,
        by simp [Ix.Kernel.Expr.looseBVarsBounded, hl1, hl2, hl3],
        by simp [Ix.Kernel.Expr.allLevelParamsDefined, hd1, hd2, hd3]⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @share bnd idx s _ hidx hsh_get _ ih =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hsub hconv ev
    have hi_len : idx.toNat < sharing.length := (List.getElem?_eq_some_iff.mp hsh_get).1
    have hi_n : idx.toNat < n := by omega
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    rw [L1.buildShareTbl_take_getElem? ecx sharing hi_n hsh_get] at hconv
    exact ih (Nat.le_of_lt hi_len) (Nat.min_le_left _ _) hd_le hreach hext hsub hconv ev

/-- **Root specification of `KernelCheck::validate_expr_well_scoped`** at depth `0`: proves
`Heap.Extends h h'`, `E_rd.looseBVarsBounded 0 = true`, and
`E_rd.allLevelParamsDefined (List.range nlvls) = true`. -/
theorem validate_expr_well_scoped_spec
    {calls : List (Call F)} {h₀ h h' : Heap F}
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {nlvls : Nat} {e : Ixon.Expr} {kp r : SourceValue F} {E_rd : Core.KExpr}
    {cs : List (Call F)}
    (hbound : IxVM.Consistency.Bounded calls)
    (hnlvls : nlvls < 4294967296)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h₀ 4294967295 e kp)
    (hext : Heap.Extends h₀ h)
    (hread : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read e = .ok E_rd)
    (ev : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
      [kp, .field 0, .field (nlvls : F)] h r h' cs)
    (hcall : (⟨"KernelCheck::validate_expr_well_scoped",
      [kp, .field 0, .field (nlvls : F)], h⟩ : Call F) ∈ calls)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧
      E_rd.looseBVarsBounded 0 = true ∧
      E_rd.allLevelParamsDefined (List.range nlvls) = true := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq cx src id self
  unfold Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl, ← List.take_length (l := src.sharing.toList)] at hread
  have raw_h := raw.mono hext (fun _ hm => hm)
  exact validate_expr_well_scoped_go hbound hcall rfl (List.Mem.head _)
    rfl (by simp) hnlvls raw_h (Nat.le_refl _) (Nat.min_le_right _ _) (Nat.le_refl 0)
    (.refl kp) (Heap.Extends.refl h) hsub hread
    (by simpa using ev)

/-- Unpacking `KernelCheck::assert_safety` when `self_unsafe = .field 0`: extracts the underlying
`KernelCheck::safe_refs_only` call returning `.field 1` and preserves `h' = h`? Note: `safe_refs_only`
may or may not allocate; we extract `ObsFn Core.W "KernelCheck::safe_refs_only" [kp] h (.field 1) h' cs'`. -/
theorem assert_safety_zero_spec {kp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Core.W "KernelCheck::assert_safety" [.field 0, kp] h r h' cs) :
    ∃ cs_sr,
      ObsFn Core.W "KernelCheck::safe_refs_only" [kp] h (.field 1) h' cs_sr ∧
      cs = (⟨"KernelCheck::safe_refs_only", [kp], h⟩ : Call F) :: cs_sr := by
  cases «KernelCheck::assert_safety».obs ev with
  | n1 hv =>
    exact absurd (congrArg ZMod.val (Value.field.inj hv)) (by decide)
  | other _ _ cs_sr _ ev_sr heq _ hh hc =>
    subst heq; subst hh; subst hc
    exact ⟨cs_sr, ev_sr, rfl⟩

end IxVM.Refinement.Assembly
