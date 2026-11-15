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

set_option maxHeartbeats 800000
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
    Ix.Kernel.Reader.emptyTables c = true ∧ IsProjInfo c.info := by
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
    simp only [EStateM.bind, EStateM.set] at h
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

private theorem uint8_eq_zero_of_lt_one {x : UInt8} (h : x.toNat < 2 ^ 0) : x = 0 :=
  UInt8.ext (by simpa using h)

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
  have hf0 : t.flag = 0 := uint8_eq_zero_of_lt_one hflag
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
  have hf0 : t.flag = 0 := uint8_eq_zero_of_lt_one hflag
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
  have hf0 : t.flag = 0 := uint8_eq_zero_of_lt_one hflag
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
  have hf1 : t1.flag = 0 := uint8_eq_zero_of_lt_one hflag1
  have hf2 : t2.flag = 0 := uint8_eq_zero_of_lt_one hflag2
  rw [hf1] at hc1
  rw [hf2] at hc2
  obtain ⟨hwf, hc3⟩ := getAddress_consumed hblk
  exact ⟨hwf, (hc1.trans hc2).trans hc3⟩

private theorem getMany_empty_inv {α : Type} {getm : Ixon.GetM α} {count : Nat}
    {s s' : Ixon.GetState}
    (h : getMany getm count s = EStateM.Result.ok #[] s') :
    count = 0 ∧ s' = s := by
  cases count with
  | zero =>
    have h0 : getMany getm 0 = pure #[] := by simp [getMany]
    rw [h0] at h
    obtain ⟨_, hs⟩ := pure_ok_inv h
    exact ⟨rfl, hs⟩
  | succ n =>
    rw [getMany_succ_head] at h
    obtain ⟨v, _, _, h1⟩ := bind_ok_inv h
    obtain ⟨vs, _, _, hpure⟩ := bind_ok_inv h1
    obtain ⟨heq, _⟩ := pure_ok_inv hpure
    have hsz := congrArg Array.size heq
    simp at hsz

private theorem getTag0_zero_consumed {s s' : Ixon.GetState} {t : Ixon.TagN}
    (ht : Ixon.getTagN 0 s = .ok t s') (hv : t.value.toNat = 0) :
    Consumed s s' (tag0Bytes 0) := by
  obtain ⟨hc, hflag⟩ := getTagN_consumed 0 (.inl rfl) ht
  have hf0 : t.flag = 0 := uint8_eq_zero_of_lt_one hflag
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
    obtain ⟨ms, s2, _, hpure⟩ := bind_ok_inv hinfo
    obtain ⟨rfl, _⟩ := pure_ok_inv hpure
    exact False.elim hproj
  · simp only [hmuts, Bool.false_eq_true, ↓reduceIte] at hinfo
    by_cases hflag : tag.flag == Ixon.Constant.FLAG
    · have hfeq : tag.flag = Ixon.Constant.FLAG := beq_iff_eq.mp hflag
      rw [hfeq] at hc_tag
      simp only [hflag, ↓reduceIte] at hinfo
      match hv : tag.value.toNat with
      | 0 =>
        have hveq : tag.value = 0 := UInt64.ext hv
        rw [hveq] at hinfo
        obtain ⟨_, _, rfl⟩ := map_ok_inv hinfo
        exact False.elim hproj
      | 1 =>
        have hveq : tag.value = 1 := UInt64.ext hv
        rw [hveq] at hinfo
        obtain ⟨_, _, rfl⟩ := map_ok_inv hinfo
        exact False.elim hproj
      | 2 =>
        have hveq : tag.value = 2 := UInt64.ext hv
        rw [hveq] at hinfo
        obtain ⟨_, _, rfl⟩ := map_ok_inv hinfo
        exact False.elim hproj
      | 3 =>
        have hveq : tag.value = 3 := UInt64.ext hv
        rw [hveq] at hinfo
        obtain ⟨_, _, rfl⟩ := map_ok_inv hinfo
        exact False.elim hproj
      | 4 =>
        have hveq : tag.value = 4 := UInt64.ext hv
        rw [hveq] at hinfo hc_tag
        obtain ⟨p, hp, rfl⟩ := map_ok_inv hinfo
        obtain ⟨hwf, hc_p⟩ := getConstructorProj_consumed hp
        exact ⟨.cPrj hwf, hc_tag.trans hc_p⟩
      | 5 =>
        have hveq : tag.value = 5 := UInt64.ext hv
        rw [hveq] at hinfo hc_tag
        obtain ⟨p, hp, rfl⟩ := map_ok_inv hinfo
        obtain ⟨hwf, hc_p⟩ := getRecursorProj_consumed hp
        exact ⟨.rPrj hwf, hc_tag.trans hc_p⟩
      | 6 =>
        have hveq : tag.value = 6 := UInt64.ext hv
        rw [hveq] at hinfo hc_tag
        obtain ⟨p, hp, rfl⟩ := map_ok_inv hinfo
        obtain ⟨hwf, hc_p⟩ := getInductiveProj_consumed hp
        exact ⟨.iPrj hwf, hc_tag.trans hc_p⟩
      | 7 =>
        have hveq : tag.value = 7 := UInt64.ext hv
        rw [hveq] at hinfo hc_tag
        obtain ⟨p, hp, rfl⟩ := map_ok_inv hinfo
        obtain ⟨hwf, hc_p⟩ := getDefinitionProj_consumed hp
        exact ⟨.dPrj hwf, hc_tag.trans hc_p⟩
      | n + 8 =>
        have hbad : (match tag.value with
            | 0 => Ixon.ConstantInfo.defn <$> Ixon.getDefinition
            | 1 => Ixon.ConstantInfo.recr <$> Ixon.getRecursor
            | 2 => Ixon.ConstantInfo.axio <$> Ixon.getAxiom
            | 3 => Ixon.ConstantInfo.quot <$> Ixon.getQuotient
            | 4 => Ixon.ConstantInfo.cPrj <$> Ixon.getConstructorProj
            | 5 => Ixon.ConstantInfo.rPrj <$> Ixon.getRecursorProj
            | 6 => Ixon.ConstantInfo.iPrj <$> Ixon.getInductiveProj
            | 7 => Ixon.ConstantInfo.dPrj <$> Ixon.getDefinitionProj
            | v => throw s!"getConstantInfo: invalid variant {v}" : Ixon.GetM Ixon.ConstantInfo) =
            throw s!"getConstantInfo: invalid variant {tag.value}" := by
          have hne0 : tag.value ≠ 0 := by intro he; rw [he] at hv; simp at hv
          have hne1 : tag.value ≠ 1 := by intro he; rw [he] at hv; simp at hv
          have hne2 : tag.value ≠ 2 := by intro he; rw [he] at hv; simp at hv
          have hne3 : tag.value ≠ 3 := by intro he; rw [he] at hv; simp at hv
          have hne4 : tag.value ≠ 4 := by intro he; rw [he] at hv; simp at hv
          have hne5 : tag.value ≠ 5 := by intro he; rw [he] at hv; simp at hv
          have hne6 : tag.value ≠ 6 := by intro he; rw [he] at hv; simp at hv
          have hne7 : tag.value ≠ 7 := by intro he; rw [he] at hv; simp at hv
          split <;> first | contradiction | rfl
        exact (throw_ok_false ((congrFun hbad s1).symm.trans hinfo)).elim
    · simp only [hflag, Bool.false_eq_true, ↓reduceIte] at hinfo
      exact (throw_ok_false hinfo).elim

private theorem getBinders_empty_consumed {s s' : Ixon.GetState}
    (h : Ixon.getBinders s = .ok #[] s') :
    Consumed s s' (bindersBytes #[]) := by
  unfold Ixon.getBinders at h
  obtain ⟨t, s1, ht, harr⟩ := bind_ok_inv h
  have harr_eq : Ixon.getArray Ixon.getBinderBlock t.value.toNat =
      getMany Ixon.getBinderBlock t.value.toNat := rfl
  rw [harr_eq] at harr
  obtain ⟨hz, rfl⟩ := getMany_empty_inv harr
  have hc := getTag0_zero_consumed ht hz
  simpa [bindersBytes, listBytes, ByteArray.append_empty] using hc

private theorem getConstantAfterInfo_empty_consumed {info : Ixon.ConstantInfo}
    {s s' : Ixon.GetState}
    (h : getConstantAfterInfo info s = .ok ⟨info, #[], #[], #[], #[]⟩ s') :
    Consumed s s'
      (tag0Bytes 0 ++ tag0Bytes 0 ++ tag0Bytes 0 ++ bindersBytes #[]) := by
  have heq1 : getConstantAfterInfo info = (do
      let t ← Ixon.getTagN 0
      let sh ← getMany Ixon.getExpr t.value.toNat
      getConstantRefs info sh) := by
    simp [getConstantAfterInfo, getMany]
  rw [heq1] at h
  obtain ⟨tSh, s1, htSh, h⟩ := bind_ok_inv h
  obtain ⟨sh, s2, hforSh, h⟩ := bind_ok_inv h
  have heq2 : getConstantRefs info sh = (do
      let t ← Ixon.getTagN 0
      let rf ← getMany Ixon.Serialize.get t.value.toNat
      getConstantUnivs info sh rf) := by
    simp [getConstantRefs, getMany]
  rw [heq2] at h
  obtain ⟨tRf, s3, htRf, h⟩ := bind_ok_inv h
  obtain ⟨rf, s4, hforRf, h⟩ := bind_ok_inv h
  have heq3 : getConstantUnivs info sh rf = (do
      let t ← Ixon.getTagN 0
      let un ← getMany Ixon.getUniv t.value.toNat
      let bnd ← Ixon.getBinders
      return ⟨info, sh, rf, un, bnd⟩) := by
    simp [getConstantUnivs, getMany]
  rw [heq3] at h
  obtain ⟨tUn, s5, htUn, h⟩ := bind_ok_inv h
  obtain ⟨un, s6, hforUn, h⟩ := bind_ok_inv h
  obtain ⟨bnd, s7, hbnd, hpure⟩ := bind_ok_inv h
  obtain ⟨heq, rfl⟩ := pure_ok_inv hpure
  cases heq
  obtain ⟨hzSh, rfl⟩ := getMany_empty_inv hforSh
  obtain ⟨hzRf, rfl⟩ := getMany_empty_inv hforRf
  obtain ⟨hzUn, rfl⟩ := getMany_empty_inv hforUn
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
    (hemp : Ix.Kernel.Reader.emptyTables c = true)
    (hproj : IsProjInfo c.info) :
    bytes = Ixon.serConstant c ∧ c.wireWF := by
  have hc_eq := Ix.Cert.ReadingKeys.empty_constant hemp
  rcases c with ⟨info₀, _, _, _, _⟩
  dsimp only at hc_eq hproj
  rw [hc_eq] at hdec ⊢
  unfold Ixon.deConstantExact Ixon.runGetExact at hdec
  split at hdec
  · rename_i val st hrun
    split at hdec
    · rename_i hidx
      cases hdec
      change Ixon.getConstant { bytes := bytes, idx := 0 } = .ok ⟨info₀, #[], #[], #[], #[]⟩ st at hrun
      rw [getConstant_eq] at hrun
      obtain ⟨info', s1, hinfo, htail⟩ := bind_ok_inv hrun
      have hinfo_eq : info' = info₀ := by
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
      subst info'
      obtain ⟨hwf_info, hc_info⟩ := getConstantInfo_proj_consumed hinfo hproj
      have hc_tail := getConstantAfterInfo_empty_consumed htail
      have hc_all := hc_info.trans hc_tail
      have hwf_nonrec : NonrecursiveConstantWireWF ⟨info₀, #[], #[], #[], #[]⟩ :=
        { info := hwf_info
          sharingCount := by dsimp only [ArrayCountWF]; decide
          sharingEntries := fun _ hm => nomatch hm
          refsCount := by dsimp only [ArrayCountWF]; decide
          refsEntries := fun _ hm => nomatch hm
          univsCount := by dsimp only [ArrayCountWF]; decide
          univsEntries := fun _ hm => nomatch hm
          binders := Ixon.bindersWireWF_empty }
      have hser : Ixon.serConstant ⟨info₀, #[], #[], #[], #[]⟩ =
          nonrecursiveConstantBytes ⟨info₀, #[], #[], #[], #[]⟩ := by
        unfold Ixon.serConstant
        exact (putConstant_writes_nonrecursive _ hwf_nonrec).runPut
      have hbytes_eq :
          nonrecursiveConstantBytes ⟨info₀, #[], #[], #[], #[]⟩ =
            nonrecursiveInfoBytes info₀ ++
              (tag0Bytes 0 ++ tag0Bytes 0 ++ tag0Bytes 0 ++ bindersBytes #[]) := by
        simp [nonrecursiveConstantBytes, listBytes, ByteArray.append_empty, ByteArray.append_assoc]
      obtain ⟨hst, hextr⟩ := hc_all
      subst hst
      simp only [Nat.zero_add] at hidx hextr
      have hbs : bytes =
          nonrecursiveInfoBytes info₀ ++
            (tag0Bytes 0 ++ tag0Bytes 0 ++ tag0Bytes 0 ++ bindersBytes #[]) := by
        rw [← hextr, hidx, ByteArray.extract_zero_size]
      have hwf_c : (⟨info₀, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
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

private theorem list_find?_pred {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {x : α}, xs.find? p = some x → p x = true
  | [], _, h => by cases h
  | hd :: tl, x, h => by
    simp only [List.find?] at h
    cases hp : p hd
    · rw [hp] at h
      exact list_find?_pred h
    · rw [hp] at h
      injection h with hxeq
      subst hxeq
      exact hp

/-- Characterization of `Core.keyOf t a` when `t.check = .ok ()`: role-bound iff `(r, a) ∈ t.bound`. -/
theorem keyOf_eq_of_bound {t : Ix.Kernel.RoleTable} (hchk : t.check = .ok ())
    {r : Ix.Kernel.Role} {a : _root_.Address}
    (hmem : (r, a) ∈ t.bound.toList) :
    Core.keyOf t a = .role r := by
  unfold Core.keyOf
  cases hfind : t.bound.find? (·.2 == a) with
  | none =>
    have hall := Array.find?_eq_none.mp hfind
    exact absurd (beq_self_eq_true a) (hall (r, a) (Array.mem_toList_iff.mp hmem))
  | some p =>
    rcases p with ⟨r', a'⟩
    have hp_mem : (r', a') ∈ t.bound.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)
    have hp_beq : (r', a').2 == a :=
      list_find?_pred (xs := t.bound.toList) (by rwa [Array.find?_toList])
    have hp_eq : a' = a := beq_iff_eq.mp hp_beq
    have hpair := Ix.Kernel.RoleTable.eq_of_nodup_map_snd
      (Ix.Kernel.RoleTable.check_nodup hchk).2 hmem hp_mem hp_eq.symm
    injection hpair with hr_eq _
    rw [hr_eq]

/-- Characterization of `Core.keyOf t a` when `a` is unbound in `t.bound`. -/
theorem keyOf_eq_of_unbound {t : Ix.Kernel.RoleTable} {a : _root_.Address}
    (hunb : ∀ r, (r, a) ∉ t.bound.toList) :
    Core.keyOf t a = .id a := by
  unfold Core.keyOf
  cases hfind : t.bound.find? (·.2 == a) with
  | none => rfl
  | some p =>
    rcases p with ⟨r, a'⟩
    have hp_mem : (r, a') ∈ t.bound.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)
    have hp_beq : (r, a').2 == a :=
      list_find?_pred (xs := t.bound.toList) (by rwa [Array.find?_toList])
    have hp_eq : a' = a := beq_iff_eq.mp hp_beq
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
  cases hfind : t.bound.find? (·.2 == a) with
  | none => exact Or.inl rfl
  | some p =>
    rcases p with ⟨r, a'⟩
    have hp_mem : (r, a') ∈ t.bound.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)
    have hp_beq : (r, a').2 == a :=
      list_find?_pred (xs := t.bound.toList) (by rwa [Array.find?_toList])
    have hp_eq : a' = a := beq_iff_eq.mp hp_beq
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
  exact Ix.Kernel.Reader.Ctx.keyAt_eq_ok.mpr hkoa

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
  change cx.keyAt a = .ok k at hk
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
    | none =>
      rw [hres] at hk
      cases hk
    | some q =>
      have hk_full : cx.keyAt a = .ok (Core.keyOf t a) :=
        streamContext_keyAt_eq_keyOf hauth hchk hres
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
  change cx.store a = some c at hc
  change cx.memberKey (.member a 0) = .ok (Core.keyOf t a)
  have hres : Ix.Kernel.Reader.resolve cx.store a = some (.member a 0) :=
    resolve_singleton hc hsing
  have hinj : ∀ a', Ix.Kernel.Reader.resolve cx.store a' = some (.member a 0) → a' = a :=
    fun _ h' => hauth.resolve_inj hres h'
  by_cases hbound : ∃ r, (r, a) ∈ t.bound.toList
  · obtain ⟨r, hmem⟩ := hbound
    have hrole : cx.roles.names[Ix.Kernel.ConstRef.member a 0]? = some (.role r) :=
      Ix.Cert.ReadingKeys.bindings_bound hchk hmem hres hinj
    rw [keyOf_eq_of_bound hchk hmem]
    unfold Ix.Kernel.Reader.Ctx.memberKey
    rw [hrole]
    rfl
  · have hunb : ∀ r, (r, a) ∉ t.bound.toList := fun r hm => hbound ⟨r, hm⟩
    have hrole : cx.roles.names[Ix.Kernel.ConstRef.member a 0]? = none :=
      Ix.Cert.ReadingKeys.bindings_unbound (t := t) hunb hinj
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
          simp only [Ix.Kernel.Reader.singletonAt, hc, bind, Option.bind]
          cases hinfo : c.info <;> simp [hinfo] at hsing ⊢
        rw [hsing_at]
        rfl
    unfold Ix.Kernel.Reader.Ctx.memberKey
    rw [hrole, ha_of]
    simp only [bind, Except.bind]
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
  have hpr₀ := Ix.Kernel.Egress.ProjectionReads.definition ⟨i.toUInt64, owner⟩
  have hpr : Ix.Kernel.Egress.ProjectionReads
      ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ .definition (.member owner i) := by
    simpa only [hi_toNat] using hpr₀
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
  change cx.store owner = some cb at hcb
  change cx.memberKey (.member owner i) = .ok (Core.keyOf t (Core.dprjAddr owner i))
  let c_proj : Ixon.Constant := ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩
  have hi_toNat : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt hi
  have hres_proj : ∀ {a' : _root_.Address}, cx.store a' = some c_proj →
      Ix.Kernel.Reader.resolve cx.store a' = some (.member owner i) := by
    intro a' ha'
    unfold Ix.Kernel.Reader.resolve Ix.Kernel.Reader.resolveSource
    simp [ha', c_proj, Ix.Kernel.Reader.emptyTables, hcb, hinfo, hi_toNat, hms]
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
        bind, Option.bind, hcb, hinfo, hms, Option.some.injEq] at hpat
      rcases hpat with rfl
      obtain ⟨bytes, hbl, hdec⟩ := hauth a' c_proj hc'
      obtain ⟨hbs, _⟩ := deConstantExact_proj_eq_serConstant hdec rfl trivial
      rw [hbs] at hbl
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
    rw [hrole, ha_of]
    simp only [bind, Except.bind]
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

set_option maxHeartbeats 3200000 in
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
        (V.Preimage (Core.dprjAddr owner i) raw' ∨ raw' ∈ extra ∨ Hashed calls raw') →
        c' = ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ := by
  have hchk : Claim.CheckedAtFull calls bAddr t (Core.dprjAddr owner i) := by
    have h0 := mutsMemberCheckedAtFull_to_checkedAtFull hbound hm hms
    simpa only [Core.Specs.Callees.memberProjInfo, Core.dprjAddr] using h0
  obtain ⟨_, _, _, _, _, _, _, _, _, cs_load, _, bytes, E_ld,
    _, _, _, _, hhash_ld, hblake_ld, _, hL1, hsub_ld, _, _, _, _⟩ :=
    checkedAtFull_loadedL1 hbound hchk
  obtain ⟨c_ld, hdec_ld, _, _, _, _, _⟩ := hL1
  have hhashed_calls : Hashed calls bytes := Core.hashed_mono hsub_ld hhash_ld
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, cs_pa, _, _,
    hmem_pa, hblk_pa, ev_pa, hcl_pa, hsub_pa, _, _, _, _, _, _, _, _, _⟩ := hm
  obtain ⟨b_arr, hb_ref, rfl⟩ := hblk_pa
  have hlen : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem_pa
  have hi_sz : i < ms.size := (Array.getElem?_eq_some_iff.mp hms).1
  have hi_len : i < ms.toList.length := by simpa using hi_sz
  have hi_lt : i < UInt64.size := by
    have : (2 ^ 39 : Nat) < UInt64.size := by decide
    omega
  have hwf_dprj :
      (⟨.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
    rw [L1.emptyTablesConstant_wireWF]
    show (Core.ixAddr b_arr).hash.size = 32
    exact b_arr.size_toArray
  have hser_dprj :
      bytes = Ixon.serConstant ⟨.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩ := by
    by_cases heq_b : bytes = Ixon.serConstant ⟨.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩
    · exact heq_b
    · have hi_val : ((i : F)).val = i :=
        ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
      obtain ⟨v1, m2, cs12, v31, m32, cs42, v198, m199, cs201,
        m231, m244, m257, m270, v282, m283, cs293, m306, cs321,
        ev14, ev44, sg206, hm239, hm252, hm265, hm278, hm314, ev295, ev323, hc332⟩ :=
        «Ingress::projection_addr».obs ev_pa
      obtain ⟨hm2, _, mc', hget_pa, hmc⟩ := L1.muts_member_at_spec hmem_pa ev14
      subst m2
      rw [hi_val] at hget_pa
      have hms_list : ms.toList[i]? = some (.defn d) := by simpa using hms
      rw [hms_list] at hget_pa
      cases hget_pa
      obtain ⟨ni, hni, hxi, hv31, hm32⟩ := Lib.u64_from_field_spec ev44
      subst m32
      have hni_eq : ni = i := by
        have hv := congrArg ZMod.val (Value.field.inj hxi).symm
        rwa [ZMod.val_natCast_of_lt (Nat.lt_trans hni (by decide)), hi_val] at hv
      subst ni
      rw [hv31] at sg206
      have e1 : Heap.Extends m199 m231 := by rw [hm239]; exact Heap.Extends.snoc _ _
      have e2 : Heap.Extends m231 m244 := by rw [hm252]; exact Heap.Extends.snoc _ _
      have e3 : Heap.Extends m244 m257 := by rw [hm265]; exact Heap.Extends.snoc _ _
      have e4 : Heap.Extends m257 m270 := by rw [hm278]; exact Heap.Extends.snoc _ _
      have e5 : Heap.Extends m270 m306 := by rw [hm314]; exact Heap.Extends.snoc _ _
      have c1 : m306[m199.length]? = some (.construct Core.Specs.Callees.ixExprListEnum "Nil" []) :=
        (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm239]; simp)
      have c2 : m306[m231.length]? = some (.construct Core.addrListEnum "Nil" []) :=
        (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm252]; simp)
      have c3 : m306[m244.length]? = some (.construct Core.Specs.Callees.ixUnivListEnum "Nil" []) :=
        (e4.trans e5).getElem?_eq (by rw [hm265]; simp)
      have c4 : m306[m257.length]? = some (.construct Core.Specs.Callees.ixBinderListEnum "Nil" []) :=
        e5.getElem?_eq (by rw [hm278]; simp)
      have c5 : m306[m270.length]? = some (.construct Core.byteListEnum "Nil" []) := by
        rw [hm314]; simp
      have hrepi : Aiur.Library.RepU64 m306 i.toUInt64 (TagN.u64Value i) := by
        have e := Lib.repU64_ofNatLT m306 (m := i)
          (Nat.lt_trans hi_len (Nat.lt_trans hlen (by decide)))
        rwa [UInt64.ofNatLT_eq_ofNat] at e
      obtain ⟨dv, rfl⟩ := hmc
      have hinfo_rep :
          Core.Specs.Callees.ProjInfoRep m306 (.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩) v198 := by
        cases sg206 with
        | Defn _ _ hv1 hm1 _ =>
          have E_ext : Heap.Extends _ m306 := by
            rw [← hm1]; exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
          rw [hv1]
          exact ⟨TagN.u64Value i, _, b_arr, rfl, hrepi,
            Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy E_ext hb_ref, rfl⟩
        | Indc _ _ hv67 _ _ _ =>
          simp only [Core.Specs.Callees.mutCtor] at hv67
          injection hv67 with _ hc _
          exact absurd hc (by decide)
        | Recr _ _ _ hv67 _ _ _ =>
          simp only [Core.Specs.Callees.mutCtor] at hv67
          injection hv67 with _ hc _
          exact absurd hc (by decide)
      have hbytes := Core.put_constant_step ⟨{}, .empty, t, none⟩ ev295 _ _
        (.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩) [] rfl
        ⟨_, _, _, _, _, rfl, hinfo_rep,
          Aiur.RepLinkedList.nil c1, Aiur.RepLinkedList.nil c2,
          Aiur.RepLinkedList.nil c3, Aiur.RepLinkedList.nil c4⟩
        (Aiur.RepLinkedList.nil c5)
      rw [List.append_nil] at hbytes
      have hstream : L1.Stream m283
          (Ixon.serConstant ⟨.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩).data.toList
          v282 := hbytes
      have hcall_b3 := (L1.bytes_to_addr_spec hstream ev323).2.2
      have hcall_pa : (⟨"Blake3::hash", [v282], m283⟩ : Call F) ∈ cs_pa := by
        rw [hc332]; simp [hcall_b3]
      have hhash_pa :
          Hashed cs_pa (Ixon.serConstant ⟨.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩) :=
        ⟨_, hcall_pa, rfl, v282, rfl, hstream⟩
      have hhashed_pa :
          Hashed calls (Ixon.serConstant ⟨.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩) :=
        Core.hashed_mono hsub_pa hhash_pa
      exact absurd (.inl ⟨Core.dprjAddr (Core.ixAddr b_arr) i,
        Ixon.serConstant ⟨.dPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩,
        bytes, .inr (.inr ⟨hhashed_pa, rfl⟩), hhashed_calls, heq_b, hblake_ld⟩) hnoCol
  refine ⟨hi_lt, fun raw' c' hbl' hdec' hsrc' => ?_⟩
  have hraw_eq : raw' = bytes := by
    by_cases heq : raw' = bytes
    · exact heq
    · have hsrc_wit :
          (V.Preimage (Core.dprjAddr (Core.ixAddr b_arr) i) raw' ∨
            (raw' ∈ extra ∧ _root_.Address.blake3Pure raw' = Core.dprjAddr (Core.ixAddr b_arr) i) ∨
            (Hashed calls raw' ∧ _root_.Address.blake3Pure raw' = Core.dprjAddr (Core.ixAddr b_arr) i)) := by
        rcases hsrc' with hp | he | hh
        · exact .inl hp
        · exact .inr (.inl ⟨he, hbl'⟩)
        · exact .inr (.inr ⟨hh, hbl'⟩)
      exact absurd (.inl ⟨Core.dprjAddr (Core.ixAddr b_arr) i, raw', bytes,
        hsrc_wit, hhashed_calls, Ne.symm heq, hblake_ld⟩) hnoCol
  subst hraw_eq
  rw [hser_dprj] at hdec'
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

/-- Cross-lane interface isolating `KernelCheck::safe_refs_only`, role-prefix bare stream transfer,
and inductive/recursor `readRecordBare` completeness (keeping zero imports from `RoleVal/*` or
`Decl/*`). -/
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
        i ∈ reachRefsExpr (buildReachRefsTbl c.sharing.toList) e →
        c.refs[i]? = some a →
        ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧
          ∀ c_a, Ix.Cert.recordAt E₀ a = some c_a →
            (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true
  /-- Role-prefix bare reading on `subEnvRole`: `order.filter (· ∈ order_role) = order_role`,
  `StreamReadBare` reads `decodedOf E order_role` to `decls_role` while preserving prelude keys,
  and every non-block constant in `order_role` satisfies `L1.RecordReadsAs t E_core`. -/
  rolePrefixStreamReadBare :
    ∀ {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
      {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
      {E₀ E E_role E_core : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
      {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
      {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
      {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
      {seeds : List _root_.Address},
      TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role →
      IxVM.Consistency.LoadedBy calls E₀ →
      ¬ V.HashedCollision extra calls →
      L1.EnvDecoded E_core →
      ¬ L1.EnvInternalCollision E_core →
      (∀ x c_x, Ix.Cert.recordAt E x = some c_x → Ix.Cert.recordAt E_core x = some c_x) →
      (∀ x bs, E.blobs.get? x = some bs → E_core.blobs.get? x = some bs) →
      (∀ a ∈ order_role, Ix.Cert.recordAt E a = Ix.Cert.recordAt E_role a ∧
        E.consts.contains a = true) →
      (∀ a bytes, (a, bytes) ∈ Ix.Cert.blobsOf E_role order_role →
        E.blobs.get? a = some bytes) →
      IxVM.Consistency.UsedClosureOrderAt t E
        (fun a => a ∈ seeds ∨ IxVM.Refinement.BindingSeeds t a) order →
      order = order.filter (· ∈ order_role) ++ order.filter (· ∉ order_role) →
      (∀ a b', a ∈ order.filter (· ∈ order_role) → b' ∈ order.filter (· ∈ order_role) →
        order.idxOf a < order.idxOf b' → order_role.idxOf a < order_role.idxOf b') →
      AuthenticExactStore
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)).store →
      order.filter (· ∈ order_role) = order_role ∧
        (∀ (decls_w : Array (Ix.Kernel.Declaration .anon)),
          (∀ d ∈ decls_w.toList, ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role) →
          (Ix.Kernel.Frontend.preparePrelude pre.ix (decls_role ++ decls_w)).toList =
            (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList ++ decls_w.toList) ∧
        ∃ st_r,
          StreamReadBare
            (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
              (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
            pre.state (Ix.Cert.Stream.decodedOf E order_role) st_r decls_role ∧
          (∀ k ∈ pre.state.keys, st_r.SameAt pre.state k) ∧
          (∀ x c_x, x ∈ order_role → Ix.Cert.recordAt E x = some c_x →
            ((∃ d_x, c_x.info = .defn d_x) ∨ (∃ ax, c_x.info = .axio ax) ∨
              (∃ qt, c_x.info = .quot qt) ∨ (∃ rc, c_x.info = .recr rc) ∨
              Ix.Cert.ownerOf x c_x ≠ x) →
            ∃ d ci₀,
              d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList ∧
              ci₀ ∈ IxVM.Consistency.installs d ∧
              ci₀.name = Core.keyOf t x ∧
              L1.RecordReadsAs t E_core x c_x ci₀)
  /-- Inductive and recursor record bare reading (`c.info = .recr _` or non-definition `.muts ms`)
  at a walked non-role address `a` in `streamContext`: `readRecordBare` succeeds, preserves prelude
  keys, and supplies `L1.RecordReadsAs t E_core` for all emitted constants stored in `E`. -/
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
      WkAll calls b.address t E₀ a →
      ¬ IxVM.Consistency.OutsideLogicAt E₀ a →
      (∀ a' c', (a', c') ∈ Ix.Cert.Stream.decodedOf E order → a' ∉ order_role →
        WkAll calls b.address t E₀ a' ∧ ¬ IxVM.Consistency.OutsideLogicAt E₀ a') →
      (∀ k ∈ pre.state.keys, st.SameAt pre.state k) →
      ((∃ rc, c.info = .recr rc) ∨
        (∃ ms, c.info = .muts ms ∧ ¬ ms.all (fun | .defn _ => true | _ => false))) →
      ∃ r,
        Ix.Kernel.Reader.readRecordBare
          (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
            (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
          st a c = .ok r ∧
        (∀ k ∈ pre.state.keys, (st.commit r).SameAt pre.state k) ∧
        (∀ d ∈ r.decls.toList,
          (∃ block nP, d = .indDecl block nP) ∧
          ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role) ∧
        (∀ x c_x,
          ((x = a ∧ c_x = c ∧ ∃ rc, c.info = .recr rc) ∨
            (Ix.Cert.recordAt E x = some c_x ∧ x ≠ a ∧ Ix.Cert.ownerOf x c_x = a)) →
          ∃ d ci₀,
            d ∈ pre.ix.decls.toList ++ prev_decls ++ r.decls.toList ∧
            ci₀ ∈ IxVM.Consistency.installs d ∧
            ci₀.name = Core.keyOf t x ∧
            L1.RecordReadsAs t E_core x c_x ci₀)

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
private theorem exprDirectRefs_mem {c : Ixon.Constant} :
    ∀ (e : Ixon.Expr) (sh : Array (List Nat)) {j : Nat},
      (∀ (k : Nat) xs, sh[k]? = some xs → ∀ x ∈ xs, x ∈ IxVM.Consistency.usedRefIdxs c) →
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
      ∀ (k : Nat) xs, (buildReachRefsTbl (c.sharing.toList.take n))[k]? = some xs →
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
        simp only [Array.size_empty, Nat.zero_add, List.length_take]
        omega
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
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs_mem, hy⟩)
      by_cases hkn : k < n
      · exact ih (by omega) k _ (buildReachRefsTbl_take_getElem? c.sharing.toList hkn hs) x hx
      · have hkeq : k = n := by omega
        subst hkeq
        exact exprDirectRefs_mem s _ (ih (by omega)) hs_dir hx
  intro j hj
  have hfull := hsh_ok c.sharing.toList.length (Nat.le_refl _)
  rw [List.take_length] at hfull
  exact exprDirectRefs_mem e _ hfull hdir hj

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
    (sharing.foldl
      (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[])[i]? =
      some (Ix.Kernel.Reader.recurDeps.go
        ((sharing.take i).foldl
          (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[]) {} s) ∧
      ∀ j < i,
        (sharing.foldl
          (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[])[j]? =
        ((sharing.take i).foldl
          (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[])[j]? := by
  have hi_len : i < sharing.length := (List.getElem?_eq_some_iff.mp hsh).1
  have hsplit : sharing = sharing.take i ++ (s :: sharing.drop (i + 1)) := by
    conv_lhs => rw [← List.take_append_drop i sharing]
    rw [List.drop_eq_getElem_cons hi_len]
    have hs_eq : sharing[i] = s := Option.some.inj ((List.getElem?_eq_getElem hi_len).symm.trans hsh)
    rw [hs_eq]
  have hpre_sz :
      ((sharing.take i).foldl
        (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[]).size = i := by
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
    have hne : j ≠ ((sharing.take i).foldl
        (fun sh entry => sh.push (Ix.Kernel.Reader.recurDeps.go sh {} entry)) #[]).size := by
      omega
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
  | letE _ _ _ _ iht ihv ihb =>
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
    dsimp only [Id.run]
    rw [← Array.forIn_toList, List.forIn_pure_yield_eq_foldl]
    rfl
  unfold Ix.Kernel.Reader.recurDeps
  rw [hshared_eq]
  have h1 := recurDeps_go_empty_lazy hty _ {} (fun _ _ _ => rfl) (by simp)
  exact recurDeps_go_empty_lazy hval _ _ (fun _ _ _ => rfl) h1

/-- Inner loop of `defOrder` when every `(deps[i]!).toList` is empty: pushes `0, 1, ..., n - 1`
in order during the very first pass. -/
private theorem defOrder_inner_all_empty (deps : Array (Std.HashSet Nat)) (n : Nat)
    (hn : n = deps.size)
    (hempty : ∀ i : Nat, i < deps.size → (deps[i]!).toList = []) :
    ∀ (k : Nat), k ≤ deps.size →
      (List.range k).foldl
        (fun (s : Array Bool × Array Nat × Bool) (i : Nat) =>
          if (!s.1[i]! && (deps[i]!).toList.all (fun j => j == i || decide (j ≥ n) || s.1[j]!)) = true then
            (s.1.set! i true, s.2.1.push i, true)
          else s)
        (Array.replicate n false, #[], false) =
      ((List.range k).foldl (fun d i => d.set! i true) (Array.replicate n false),
       (List.range k).toArray, decide (0 < k)) := by
  subst hn
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (by omega)]
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
        · simp [Array.set!, Array.setIfInBounds, hhd_lt, hne_hd]
        · simp [Array.set!, Array.setIfInBounds, hhd_lt]
    obtain ⟨hsz_k, hget_k⟩ := hdone_sz_get (List.range k) (Array.replicate deps.size false)
    have hk_not_mem : k ∉ List.range k := by simp
    have hdone_at_k :
        ((List.range k).foldl (fun d i => d.set! i true) (Array.replicate deps.size false))[k]! =
          false := by
      have hlt :
          k < ((List.range k).foldl (fun d i => d.set! i true) (Array.replicate deps.size false)).size := by
        rw [hsz_k]; simp; omega
      rw [getElem!_pos _ k hlt]
      have hsome :
          ((List.range k).foldl (fun d i => d.set! i true) (Array.replicate deps.size false))[k]? =
            some false := by
        rw [hget_k k hk_not_mem, Array.getElem?_replicate]
        simp [show k < deps.size by omega]
      exact Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans hsome)
    have hcond :
        (!((List.range k).foldl (fun d i => d.set! i true) (Array.replicate deps.size false))[k]! &&
          (deps[k]!).toList.all (fun j =>
            j == k || decide (j ≥ deps.size) ||
              ((List.range k).foldl (fun d i => d.set! i true) (Array.replicate deps.size false))[j]!)) =
          true := by
      rw [hdone_at_k, hempty k (by omega)]
      rfl
    simp only [hcond, ↓reduceIte]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    · apply Array.ext'; simp
    · simp

private theorem forIn_id_ite_yield {α β : Type} (xs : List α) (init : β)
    (cond : β → α → Bool) (step : β → α → β) :
    forIn (m := Id) xs init
      (fun a b => if cond b a = true then pure (.yield (step b a)) else pure (.yield b)) =
    pure (xs.foldl (fun b a => if cond b a then step b a else b) init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.forIn_cons, List.foldl_cons]
    cases cond init hd <;> simp [ih]

/-- **`defOrder` succeeds with `Array.range deps.size`** whenever all dependency sets are empty. -/
theorem defOrder_all_empty (deps : Array (Std.HashSet Nat))
    (hempty : ∀ i : Nat, i < deps.size → (deps[i]!).toList = []) :
    Ix.Kernel.Reader.defOrder deps = some (Array.range deps.size) := by
  unfold Ix.Kernel.Reader.defOrder
  dsimp only
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : [:deps.size].size = deps.size := by simp [Std.Legacy.Range.size]
  rw [hsize]
  cases hn : deps.size with
  | zero =>
    have h0 : Array.range 0 = #[] := by apply Array.ext'; simp [Array.toList_range]
    rw [h0]
    simp [List.range', pure, bind]
  | succ m =>
    have hrange_eq : (List.range (m + 1)).toArray = Array.range (m + 1) := by
      apply Array.ext'
      simp [Array.toList_range]
    have hrange' : List.range' 0 (m + 1) = List.range (m + 1) :=
      List.range'_eq_map_range.trans (by simp)
    have hrange1 : (0 :: List.range' (0 + 1) m) = List.range (m + 1) := by
      rw [← List.range'_succ]
      exact hrange'
    have hinner := defOrder_inner_all_empty deps (m + 1) hn.symm hempty (m + 1) (by omega)
    rw [List.range'_succ, List.forIn_cons, hrange1]
    dsimp only
    rw [forIn_id_ite_yield (List.range (m + 1)) (Array.replicate (m + 1) false, #[], false)
      (fun s i => !s.1[i]! && (deps[i]!).toList.all (fun j => j == i || decide (j ≥ m + 1) || s.1[j]!))
      (fun s i => (s.1.set! i true, s.2.1.push i, true))]
    rw [hinner, hrange_eq]
    simp [Array.size_range, pure, bind]

/-! ### `MemberReader.read` completeness from `RawConvExpr` -/

private theorem except_bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

set_option maxHeartbeats 3200000 in
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
      (bound ≤ n ∨ n = sharing.length) →
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
      rw [hunivs, Array.getElem?_map, List.getElem?_toArray, hu]
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
            rw [hunivs, Array.getElem?_map, List.getElem?_toArray, hu_raw]
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
            rw [hunivs, Array.getElem?_map, List.getElem?_toArray, hu_raw]
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
  | @letE _ _ nd _ _ _ _ _ _ _ _ _ _ _ iht ihv ihb =>
    intro n hn hbnd hkeys
    obtain ⟨Et, hEt⟩ := iht hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_left _ (List.mem_append_left _ hidx)))
    obtain ⟨Ev, hEv⟩ := ihv hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_left _ (List.mem_append_right _ hidx)))
    obtain ⟨Eb, hEb⟩ := ihb hn hbnd (fun idx hidx =>
      hkeys idx (List.mem_append_right _ hidx))
    exact ⟨.letE Et Ev Eb { nonDep := nd },
      by simp [Ix.Kernel.Reader.convExpr, hEt, hEv, hEb, bind, Except.bind, pure, Except.pure]⟩
  | @share bnd idx s _ hidx hsh_get rs ih =>
    intro n hn hbnd hkeys
    have hi_len : idx.toNat < sharing.length := (List.getElem?_eq_some_iff.mp hsh_get).1
    have hi_n : idx.toNat < n := by rcases hbnd with hb | rfl <;> omega
    simp only [Ix.Kernel.Reader.convExpr]
    rw [L1.buildShareTbl_take_getElem? ecx sharing hi_n hsh_get]
    have hreach_sub : ∀ j ∈ reachRefsExpr (buildReachRefsTbl sharing) s,
        j ∈ reachRefsExpr (buildReachRefsTbl sharing) (.share idx) := by
      have hget_full := buildReachRefsTbl_take_getElem? sharing (n := sharing.length) hi_len hsh_get
      simp only [List.take_length] at hget_full
      intro j hj
      simp only [reachRefsExpr, hget_full, Option.getD_some]
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
        | letE _ _ _ _ ih1 ih2 ih3 =>
          intro hb'; simp [reachRefsExpr, ih1 hb', ih2 hb', ih3 hb']
        | @share b2 idx2 s2 _ hidx2 hsh2 _ _ =>
          intro hb'
          have h2_lt : idx2.toNat < idx.toNat := by omega
          have h2_len : idx2.toNat < sharing.length := (List.getElem?_eq_some_iff.mp hsh2).1
          have hg1 := buildReachRefsTbl_take_getElem? sharing (n := sharing.length) h2_len hsh2
          simp only [List.take_length] at hg1
          have hg2 := buildReachRefsTbl_take_getElem? sharing (n := idx.toNat) h2_lt hsh2
          simp [reachRefsExpr, hg1, hg2]
      rw [← hcongr rs (Nat.le_refl _)]
      exact hj
    exact ih (Nat.le_of_lt hi_len) (Or.inl (Nat.le_refl _))
      (fun j hj => hkeys j (hreach_sub j hj))

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
  exact convExpr_ok_of_rawConvExpr (param := param) rfl (by simp) hself_ok hblob_ok raw
    (Nat.le_refl _) (Or.inr rfl)
    (fun idx hidx a ha => by
      dsimp only at ha
      rw [Array.getElem?_toList] at ha
      exact hkeys idx hidx a ha)

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
    | Zero _ _ hh _ => exact ⟨hh, rfl⟩
    | Succ _ _ ld _ _ | Max _ _ _ _ _ _ ld _ _ _ | IMax _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | succ cell _ ih =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Succ _ _ ld ev_in _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs
      subst hxs
      exact ih ev_in
    | Zero ld _ _ _ | Max _ _ _ _ _ _ ld _ _ _ | IMax _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | max cell _ _ iha ihb =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Max _ _ _ _ _ _ ld eva evb _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain ⟨rfl, ha⟩ := iha eva
      obtain ⟨hh', hb⟩ := ihb evb
      exact ⟨hh', by simp [Ix.Kernel.Level.allParamsDefined, ha, hb]⟩
    | Zero ld _ _ _ | Succ _ _ ld _ _ | IMax _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | imax cell _ _ iha ihb =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | IMax _ _ _ _ _ _ ld eva evb _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain ⟨rfl, ha⟩ := iha eva
      obtain ⟨hh', hb⟩ := ihb evb
      exact ⟨hh', by simp [Ix.Kernel.Level.allParamsDefined, ha, hb]⟩
    | Zero ld _ _ _ | Succ _ _ ld _ _ | Max _ _ _ _ _ _ ld _ _ _
    | Param _ _ _ _ ld _ _ _ _ _ =>
      exact (Core.load_cell_ne cell ld (by decide)).elim
  | @param i _ hi cell =>
    cases «KernelCheck::validate_univ_params_seen».obs ev with
    | Param _ _ _ _ ld ev_lt heq _ hh _ =>
      have hxs := (Core.load_cell cell ld).2
      simp only [List.cons.injEq, and_true] at hxs
      subst hxs
      obtain ⟨a, b, ha, hb, hxa, hxb, hr_lt, hm_eq⟩ := L1.lt_fields_both_spec ev_lt
      have hP : (72057594037927936 : Nat) < Aiur.Library.U32.Goldilocks.modulus := by decide
      have ha_eq : a = i := by
        have h2 := congrArg ZMod.val (Value.field.inj hxa).symm
        rwa [ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega),
          ZMod.val_natCast_of_lt (Nat.lt_trans hi hP)] at h2
      have hb_eq : b = nlvls := by
        have h2 := congrArg ZMod.val (Value.field.inj hxb).symm
        rwa [ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega),
          ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)] at h2
      rw [ha_eq, hb_eq] at hr_lt
      have hlt : i < nlvls := by
        by_cases hlt' : i < nlvls
        · exact hlt'
        · simp [hlt'] at hr_lt
          rw [hr_lt] at heq
          have h01 := Value.field.inj heq
          exact absurd (congrArg ZMod.val h01) (by decide)
      exact ⟨hh.trans hm_eq, by simp [Ix.Kernel.Level.allParamsDefined, List.mem_range]; exact hlt⟩
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
  | snoc {p q q' : SourceValue F} {addr steps : Nat} {v : SourceValue F} :
      KExprReach h₀ p q steps →
      q = .ptr (.enum Core.kexprEnum) addr →
      h₀[addr]? = some v →
      v.type = .enum Core.kexprEnum →
      q' ∈ RomBound.cellArgs v →
      KExprReach h₀ p q' (steps + 1)

private theorem kexprReach_to_heapDescent {h₀ : Heap F}
    {p q : SourceValue F} {steps : Nat}
    (hreach : KExprReach h₀ p q steps) :
    ∀ {tailSteps : Nat},
      RomBound.HeapDescent h₀ (.enum Core.kexprEnum) q tailSteps →
      RomBound.HeapDescent h₀ (.enum Core.kexprEnum) p (steps + tailSteps) := by
  induction hreach with
  | refl =>
    intro tailSteps htail
    simpa using htail
  | snoc _ hq hcell hty harg ih =>
    intro tailSteps htail
    subst hq
    have hd : RomBound.HeapDescent h₀ (.enum Core.kexprEnum) _ (tailSteps + 1) :=
      .down hcell hty harg htail
    have hall := ih hd
    simpa [Nat.add_assoc, Nat.add_comm 1 tailSteps] using hall

private theorem kexprReach_steps_lt {calls : List (Call F)} {h₀ : Heap F}
    {root q : SourceValue F} {c₀ : Call F} {steps addr : Nat} {v : SourceValue F}
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

private theorem convExpr_levels_allParamsDefined {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : List Ixon.Univ}
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
      rw [hunivs, Array.getElem?_map, List.getElem?_toArray, hu_raw]
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

set_option maxHeartbeats 4800000 in
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
    (hunivs : ecx.univs = univs.toArray.map (Ix.Kernel.Reader.convUniv id))
    {nlvls : Nat} (hnlvls : nlvls < 4294967296)
    {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr refs recurAddrs univs sharing blobs h₀ bound e kp) :
    ∀ {n d steps : Nat} {E_rd : Core.KExpr} {h h' : Heap F} {r : SourceValue F}
      {cs : List (Call F)},
      n ≤ sharing.length →
      (bound ≤ n ∨ n = sharing.length) →
      d ≤ steps →
      KExprReach h₀ root kp steps →
      Heap.Extends h₀ h →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (sharing.take n)) e = .ok E_rd →
      ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
        [kp, .field (d : F), .field (nlvls : F)] h r h' cs →
      Heap.Extends h h' ∧
        E_rd.looseBVarsBounded d = true ∧
        E_rd.allLevelParamsDefined (List.range nlvls) = true := by
  induction raw with
  | @var _ addr idx hidx cell =>
    intro n d steps E_rd h h' r cs _ _ hd_le hreach hext hconv ev
    have hd_lt39 : steps < 2 ^ 39 :=
      kexprReach_steps_lt hbound hc₀ hheap₀ harg₀ hreach rfl cell (by simp)
    have hd_lt32_or : d < Aiur.Library.U32.Goldilocks.modulus := by
      unfold Aiur.Library.U32.Goldilocks.modulus; omega
    simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq] at hconv
    subst hconv
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | BVar _ _ _ _ ld ev_lt heq _ hh _ =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs; subst hxs
      obtain ⟨a, b, ha, hb, hxa, hxb, hr_lt, hm_eq⟩ := L1.lt_fields_both_spec ev_lt
      have hP : (72057594037927936 : Nat) < Aiur.Library.U32.Goldilocks.modulus := by decide
      have ha_eq : a = idx.toNat := by
        have h2 := congrArg ZMod.val (Value.field.inj hxa).symm
        rwa [ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega),
          ZMod.val_natCast_of_lt (Nat.lt_trans hidx hP)] at h2
      have hb_eq : b = d := by
        have h2 := congrArg ZMod.val (Value.field.inj hxb).symm
        rwa [ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega),
          ZMod.val_natCast_of_lt hd_lt32_or] at h2
      subst ha_eq
      rw [hb_eq] at hr_lt
      have hlt : idx.toNat < d := by
        by_cases hlt' : idx.toNat < d
        · exact hlt'
        · simp [hlt'] at hr_lt
          rw [hr_lt] at heq
          exact absurd (congrArg ZMod.val (Value.field.inj heq)) (by decide)
      rw [hh, hm_eq, Ix.Kernel.Expr.mkBvar_eq]
      exact ⟨Heap.Extends.refl _, by simp [Ix.Kernel.Expr.looseBVarsBounded]; exact hlt, rfl⟩
    | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @sort _ addr uIdx u lp _ hu rl cell =>
    intro n d steps E_rd h h' r cs _ _ _ _ hext hconv ev
    have hu_arr : ecx.univs[uIdx.toNat]? = some (Ix.Kernel.Reader.convUniv id u) := by
      rw [hunivs, Array.getElem?_map, List.getElem?_toArray, hu]
      rfl
    simp only [Ix.Kernel.Reader.convExpr, Ix.Kernel.Reader.ECx.level, hu_arr,
      pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hconv
    subst hconv
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Srt _ _ ld ev_u _ =>
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
  | @ref _ addr rIdx uIdxs a d_arr ap lsp ls _ _ _ _ hls rls cell =>
    intro n d steps E_rd h h' r cs _ _ _ _ hext hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, _, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨ls_rd, hls_rd, hret⟩ := except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have hls_eq := convExpr_levels_allParamsDefined hunivs hls hls_rd
    subst hls_eq
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld ev_gci _ ev_cnl ev_len _ ev_vl _ =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      have ext1 := (ev_gci.heap_extends.trans ev_cnl.heap_extends).trans ev_len.heap_extends
      have hrls_m191 := (rls.mono hext).mono ext1
      obtain ⟨hh', hdef⟩ := validate_univ_params_list_spec hnlvls hrls_m191 ev_vl
      rw [hh']
      exact ⟨ext1, rfl, hdef⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @recur _ addr rIdx uIdxs a d_arr ap lsp ls _ _ _ _ hls rls cell =>
    intro n d steps E_rd h h' r cs _ _ _ _ hext hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hs_opt : ecx.self rIdx.toNat with
    | none => simp [hs_opt, Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at hconv
    | some _ =>
      simp only [hs_opt] at hconv
      obtain ⟨_, _, hbind2⟩ := except_bind_eq_ok hconv
      obtain ⟨ls_rd, hls_rd, hret⟩ := except_bind_eq_ok hbind2
      injection hret with hE; subst hE
      have hls_eq := convExpr_levels_allParamsDefined hunivs hls hls_rd
      subst hls_eq
      have cell_h := hext.getElem?_eq cell
      cases «KernelCheck::validate_expr_well_scoped».obs ev with
      | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld ev_gci _ ev_cnl ev_len _ ev_vl _ =>
        have hxs := (Core.load_cell cell_h ld).2
        simp only [List.cons.injEq, and_true] at hxs
        obtain ⟨rfl, rfl⟩ := hxs
        have ext1 := (ev_gci.heap_extends.trans ev_cnl.heap_extends).trans ev_len.heap_extends
        have hrls_m191 := (rls.mono hext).mono ext1
        obtain ⟨hh', hdef⟩ := validate_univ_params_list_spec hnlvls hrls_m191 ev_vl
        rw [hh']
        exact ⟨ext1, rfl, hdef⟩
      | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _
      | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
      | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
      | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
        exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @prj _ addr tIdx fIdx _ _ _ _ ip _ _ _ _ _ _ cell ih =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, _, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨Ein_rd, hEin_rd, hret⟩ := except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Proj _ _ _ _ ld ev1 _ =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨_, _, rfl⟩ := hxs
      have hreach1 : KExprReach h₀ root ip (steps + 1) :=
        .snoc hreach rfl cell (by simp) (by simp [RomBound.cellArgs])
      obtain ⟨ext1, hl1, hd1⟩ := ih hn hbnd (by omega) hreach1 hext hEin_rd ev1
      exact ⟨ext1,
        by simp [Ix.Kernel.Expr.looseBVarsBounded, hl1],
        by simp [Ix.Kernel.Expr.allLevelParamsDefined, hd1]⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Lit _ ld _ _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | str _ _ _ _ _ cell =>
    intro n d steps E_rd h h' r cs _ _ _ _ hext hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, _, h2⟩ := except_bind_eq_ok hconv
    cases hutf : String.fromUTF8? _ with
    | none => rw [hutf] at h2; simp [Ix.Kernel.Reader.malformed, throw, throwThe, MonadExceptOf.throw] at h2
    | some _ =>
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
    intro n d steps E_rd h h' r cs _ _ _ _ hext hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, _, h2⟩ := except_bind_eq_ok hconv
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
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Ef_rd, hEf, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨Ea_rd, hEa, hret⟩ := except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | App _ _ _ _ _ _ ld ev1 ev2 _ =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      have hrf : KExprReach h₀ root fp (steps + 1) :=
        .snoc hreach rfl cell (by simp) (by simp [RomBound.cellArgs])
      have hra : KExprReach h₀ root ap (steps + 1) :=
        .snoc hreach rfl cell (by simp) (by simp [RomBound.cellArgs])
      obtain ⟨ext1, hl1, hd1⟩ := ihf hn hbnd (by omega) hrf hext hEf ev1
      obtain ⟨ext2, hl2, hd2⟩ := iha hn hbnd (by omega) hra (hext.trans ext1) hEa ev2
      exact ⟨ext1.trans ext2,
        by simp [Ix.Kernel.Expr.looseBVarsBounded, hl1, hl2],
        by simp [Ix.Kernel.Expr.allLevelParamsDefined, hd1, hd2]⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @lam _ addr _ _ tp bp _ _ _ _ _ cell iht ihb =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et_rd, hEt, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨Eb_rd, hEb, hret⟩ := except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Lam _ _ _ _ _ _ _ _ _ _ v_d1 ld ev_l ev_t hop ev_b _ =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      have ext_l := ev_l.heap_extends
      have hrt : KExprReach h₀ root tp (steps + 1) :=
        .snoc hreach rfl cell (by simp) (by simp [RomBound.cellArgs])
      have hrb : KExprReach h₀ root bp (steps + 1) :=
        .snoc hreach rfl cell (by simp) (by simp [RomBound.cellArgs])
      have hd1_eq : v_d1 = .field ((d + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at hop
        rw [← hop]
        push_cast
        rfl
      rw [hd1_eq] at ev_b
      obtain ⟨ext1, hl1, hd1⟩ := iht hn hbnd (by omega) hrt (hext.trans ext_l) hEt ev_t
      obtain ⟨ext2, hl2, hd2⟩ := ihb hn hbnd (by omega) hrb ((hext.trans ext_l).trans ext1) hEb ev_b
      exact ⟨(ext_l.trans ext1).trans ext2,
        by simp [Ix.Kernel.Expr.looseBVarsBounded, hl1, hl2],
        by simp [Ix.Kernel.Expr.allLevelParamsDefined, hd1, hd2,
          Ix.Kernel.BinderMeta.leanNever]⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @all _ addr _ _ tp bp _ _ _ _ _ cell iht ihb =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et_rd, hEt, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨Eb_rd, hEb, hret⟩ := except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Forall _ _ _ _ _ _ _ _ _ _ v_d1 ld ev_l ev_t hop ev_b _ =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      have ext_l := ev_l.heap_extends
      have hrt : KExprReach h₀ root tp (steps + 1) :=
        .snoc hreach rfl cell (by simp) (by simp [RomBound.cellArgs])
      have hrb : KExprReach h₀ root bp (steps + 1) :=
        .snoc hreach rfl cell (by simp) (by simp [RomBound.cellArgs])
      have hd1_eq : v_d1 = .field ((d + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at hop
        rw [← hop]
        push_cast
        rfl
      rw [hd1_eq] at ev_b
      obtain ⟨ext1, hl1, hd1⟩ := iht hn hbnd (by omega) hrt (hext.trans ext_l) hEt ev_t
      obtain ⟨ext2, hl2, hd2⟩ := ihb hn hbnd (by omega) hrb ((hext.trans ext_l).trans ext1) hEb ev_b
      exact ⟨(ext_l.trans ext1).trans ext2,
        by simp [Ix.Kernel.Expr.looseBVarsBounded, hl1, hl2],
        by simp [Ix.Kernel.Expr.allLevelParamsDefined, hd1, hd2,
          Ix.Kernel.BinderMeta.leanNever]⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @letE _ addr _ _ _ _ _ tp vp bp _ _ _ cell iht ihv ihb =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hconv ev
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et_rd, hEt, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨Ev_rd, hEv, hbind3⟩ := except_bind_eq_ok hbind2
    obtain ⟨Eb_rd, hEb, hret⟩ := except_bind_eq_ok hbind3
    injection hret with hE; subst hE
    have cell_h := hext.getElem?_eq cell
    cases «KernelCheck::validate_expr_well_scoped».obs ev with
    | Let _ _ _ _ _ _ _ _ _ _ v_d1 ld ev_t ev_v hop ev_b _ =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      have hrt : KExprReach h₀ root tp (steps + 1) :=
        .snoc hreach rfl cell (by simp) (by simp [RomBound.cellArgs])
      have hrv : KExprReach h₀ root vp (steps + 1) :=
        .snoc hreach rfl cell (by simp) (by simp [RomBound.cellArgs])
      have hrb : KExprReach h₀ root bp (steps + 1) :=
        .snoc hreach rfl cell (by simp) (by simp [RomBound.cellArgs])
      have hd1_eq : v_d1 = .field ((d + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at hop
        rw [← hop]
        push_cast
        rfl
      rw [hd1_eq] at ev_b
      obtain ⟨ext1, hl1, hd1⟩ := iht hn hbnd (by omega) hrt hext hEt ev_t
      obtain ⟨ext2, hl2, hd2⟩ := ihv hn hbnd (by omega) hrv (hext.trans ext1) hEv ev_v
      obtain ⟨ext3, hl3, hd3⟩ := ihb hn hbnd (by omega) hrb ((hext.trans ext1).trans ext2) hEb ev_b
      exact ⟨(ext1.trans ext2).trans ext3,
        by simp [Ix.Kernel.Expr.looseBVarsBounded, hl1, hl2, hl3],
        by simp [Ix.Kernel.Expr.allLevelParamsDefined, hd1, hd2, hd3]⟩
    | BVar _ _ _ _ ld _ _ _ _ _ | Srt _ _ ld _ _ | Const _ _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ _
    | App _ _ _ _ _ _ ld _ _ _ | Lam _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Forall _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @share bnd idx s _ hidx hsh_get _ ih =>
    intro n d steps E_rd h h' r cs hn hbnd hd_le hreach hext hconv ev
    have hi_len : idx.toNat < sharing.length := (List.getElem?_eq_some_iff.mp hsh_get).1
    have hi_n : idx.toNat < n := by rcases hbnd with hb | rfl <;> omega
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    rw [L1.buildShareTbl_take_getElem? ecx sharing hi_n hsh_get] at hconv
    exact ih (Nat.le_of_lt hi_len) (Or.inl (Nat.le_refl _))
      hd_le hreach hext hconv ev

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
      [kp, .field 0, .field (nlvls : F)], h⟩ : Call F) ∈ calls) :
    Heap.Extends h h' ∧
      E_rd.looseBVarsBounded 0 = true ∧
      E_rd.allLevelParamsDefined (List.range nlvls) = true := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq cx src id self
  unfold Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl, ← List.take_length (l := src.sharing.toList)] at hread
  have raw_h := raw.mono hext (fun _ hm => hm)
  exact validate_expr_well_scoped_go hbound hcall rfl (List.Mem.head _)
    (by simp) hnlvls raw_h (Nat.le_refl _) (Or.inr rfl)
    (Nat.le_refl 0) (.refl kp) (Heap.Extends.refl h) hread (by simpa using ev)

/-- Unpacking `KernelCheck::assert_safety` when `self_unsafe = .field 0`: extracts the underlying
`KernelCheck::safe_refs_only` call returning `.field 1`. -/
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
