import Ix.Compile.Verify.ConstantCodec

/-!
# Proof-visible v2 constant side-table codec

This slice lifts the verified expression, universe, and core constant-info
codecs through the production sharing, reference, and universe table loops.
It records the format's two necessary side-table conditions explicitly:
array lengths survive the `Nat → UInt64 → Nat` wire-count conversion, and
serialized addresses contain exactly 32 bytes.
-/

namespace Ix.Compile.Verify.Codec.Ixon.ConstantTables

open Ix
open Ix.Compile.Verify.Codec

theorem putBytes_writes (bytes : ByteArray) :
    Writes (Ixon.putBytes bytes) bytes := by
  intro before
  simp only [Ixon.putBytes, StateT.run]
  change StateT.modifyGet _ before = _
  simp [StateT.modifyGet]
  rfl

theorem middle_extract (before bytes after : ByteArray) :
    (before ++ bytes ++ after).extract before.size
      (before.size + bytes.size) = bytes := by
  calc
    (before ++ bytes ++ after).extract before.size
        (before.size + bytes.size) =
      (bytes ++ after).extract 0 bytes.size := by
        rw [show before ++ bytes ++ after = before ++ (bytes ++ after) by
          simp [ByteArray.append_assoc]]
        simpa using (ByteArray.extract_append_size_add
          (a := before) (b := bytes ++ after) (i := 0) (j := bytes.size))
    _ = bytes := ByteArray.extract_append_eq_left rfl

theorem getBytes_reads (bytes : ByteArray) :
    Reads (Ixon.getBytes bytes.size) bytes bytes := by
  intro before after
  unfold Ixon.getBytes
  change (EStateM.bind EStateM.get _) ({
    idx := before.size
    bytes := before ++ bytes ++ after
  } : Ixon.GetState) = _
  simp only [EStateM.bind, EStateM.get]
  rw [if_pos (by simp [ByteArray.size_append])]
  change (EStateM.bind (EStateM.set _) _) _ = _
  simp only [EStateM.bind, EStateM.set]
  change (EStateM.pure _) _ = _
  simp only [EStateM.pure, EStateM.Result.ok.injEq]
  constructor
  · exact middle_extract before bytes after
  · simp

def getMany (getm : Ixon.GetM α) (count : Nat) : Ixon.GetM (Array α) := do
  let mut values := #[]
  for _ in [0:count] do
    values := values.push (← getm)
  return values

theorem getMany_succ_head (getm : Ixon.GetM α) (n : Nat) :
    getMany getm (n + 1) = do
      let value ← getm
      let values ← getMany getm n
      return #[value] ++ values := by
  have ranges (start : Nat) :
      List.mapM (fun _ => getm) (List.range' start n) =
        List.mapM (fun _ => getm) (List.range' 0 n) := by
    induction n generalizing start with
    | zero => simp
    | succ n ih => simp [List.range'_succ, ih]
  simp [getMany, List.range'_succ, ranges]

def listBytes (encode : α → ByteArray) : List α → ByteArray
  | [] => ByteArray.empty
  | value :: values => encode value ++ listBytes encode values

def putMany (putm : α → Ixon.PutM Unit) (values : List α) :
    Ixon.PutM Unit :=
  values.foldlM (fun _ value => putm value) ()

theorem putMany_writes (putm : α → Ixon.PutM Unit)
    (encode : α → ByteArray) (valid : α → Prop) (values : List α)
    (hvalid : ∀ value, value ∈ values → valid value)
    (hwrite : ∀ value, valid value → Writes (putm value) (encode value)) :
    Writes (putMany putm values) (listBytes encode values) := by
  induction values with
  | nil =>
    intro before
    simp only [putMany, List.foldlM_nil, listBytes,
      ByteArray.append_empty]
    rfl
  | cons value values ih =>
    have hhead := hvalid value (by simp)
    have htail : ∀ tail, tail ∈ values → valid tail := by
      intro tail hmem
      exact hvalid tail (by simp [hmem])
    simpa only [putMany, List.foldlM_cons, listBytes] using
      (hwrite _ hhead).bind (ih htail)

theorem arrayPut_eq_putMany (putm : α → Ixon.PutM Unit)
    (values : Array α) :
    (do for value in values do putm value) =
      putMany putm values.toList := by
  rw [← Array.forIn_toList]
  simp [putMany]

theorem arrayPut_writes (putm : α → Ixon.PutM Unit)
    (encode : α → ByteArray) (valid : α → Prop) (values : Array α)
    (hvalid : ∀ value, value ∈ values.toList → valid value)
    (hwrite : ∀ value, valid value → Writes (putm value) (encode value)) :
    Writes (do for value in values do putm value)
      (listBytes encode values.toList) := by
  rw [arrayPut_eq_putMany]
  exact putMany_writes putm encode valid values.toList hvalid hwrite

theorem getMany_reads (getm : Ixon.GetM α) (encode : α → ByteArray)
    (values : List α)
    (h : ∀ value, value ∈ values → Reads getm (encode value) value) :
    Reads (getMany getm values.length) (listBytes encode values)
      values.toArray := by
  induction values with
  | nil => simpa [getMany, listBytes] using Reads.pure (#[] : Array α)
  | cons value values ih =>
    have hhead := h value (by simp)
    have htail := ih (by
      intro tail hmem
      exact h tail (by simp [hmem]))
    have hreturn := Reads.pure (#[value] ++ values.toArray)
    have hafterTail := Reads.bind
      (next := fun tail : Array α =>
        (pure (#[value] ++ tail) : Ixon.GetM (Array α)))
      htail hreturn
    have hall := Reads.bind
      (next := fun head : α => do
        let tail ← getMany getm values.length
        return #[head] ++ tail)
      hhead hafterTail
    change Reads (getMany getm (values.length + 1))
      (listBytes encode (value :: values)) (value :: values).toArray
    rw [getMany_succ_head]
    simpa [listBytes] using hall

/-- An address is in the production wire domain exactly when its payload has
    the 32 bytes consumed by the decoder. -/
def AddressWireWF (address : Address) : Prop :=
  address.hash.size = 32

theorem putAddress_writes (address : Address) :
    Writes (Ixon.Serialize.put address) address.hash := by
  change Writes (Ixon.putBytes address.hash) address.hash
  exact putBytes_writes address.hash

theorem getAddress_reads (address : Address) (h : AddressWireWF address) :
    Reads (Ixon.Serialize.get : Ixon.GetM Address) address.hash address := by
  change Reads (Address.mk <$> Ixon.getBytes 32) address.hash address
  rw [← h]
  simpa using
    Ix.Compile.Verify.Codec.Ixon.Constant.reads_map Address.mk
      (getBytes_reads address.hash)

/-- An array count survives the production `Nat → UInt64 → Nat` conversion. -/
def ArrayCountWF (values : Array α) : Prop :=
  values.size < UInt64.size

theorem arrayCount_decode (values : Array α) (h : ArrayCountWF values) :
    values.size.toUInt64.toNat = values.size := by
  unfold ArrayCountWF at h
  change (UInt64.ofNat values.size).toNat = values.size
  exact UInt64.toNat_ofNat_of_lt h

theorem putExprArray_writes (values : Array Ixon.Expr)
    (h : ∀ value, value ∈ values.toList →
      Ixon.Expr.wireWF value) :
    Writes (do for value in values do Ixon.putExpr value)
      (listBytes Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode values.toList) := by
  exact arrayPut_writes Ixon.putExpr
    Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode
    Ixon.Expr.wireWF values h
    Ix.Compile.Verify.Codec.Ixon.Expr.putExpr_writes_spine

theorem getExprArray_reads (values : Array Ixon.Expr)
    (h : ∀ value, value ∈ values.toList →
      Ixon.Expr.wireWF value) :
    Reads (getMany Ixon.getExpr values.size)
      (listBytes Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode values.toList)
      values := by
  have hall : ∀ value, value ∈ values.toList →
      Ixon.Expr.wireWF value := by
    exact h
  simpa using getMany_reads Ixon.getExpr
    Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode values.toList
    (fun value hmem =>
      Ix.Compile.Verify.Codec.Ixon.Expr.getExpr_reads_spine value
        (hall value hmem))

theorem putAddressArray_writes (values : Array Address)
    (h : ∀ value, value ∈ values.toList → AddressWireWF value) :
    Writes (do for value in values do Ixon.Serialize.put value)
      (listBytes Address.hash values.toList) := by
  exact arrayPut_writes Ixon.Serialize.put Address.hash AddressWireWF
    values h (fun value _ => putAddress_writes value)

theorem getAddressArray_reads (values : Array Address)
    (h : ∀ value, value ∈ values.toList → AddressWireWF value) :
    Reads (getMany (Ixon.Serialize.get : Ixon.GetM Address) values.size)
      (listBytes Address.hash values.toList) values := by
  have hall : ∀ value, value ∈ values.toList → AddressWireWF value := by
    exact h
  simpa using getMany_reads (Ixon.Serialize.get : Ixon.GetM Address)
    Address.hash values.toList
    (fun value hmem => getAddress_reads value (hall value hmem))

theorem putUnivArray_writes (values : Array Ixon.Univ)
    (h : ∀ value, value ∈ values.toList →
      Ix.Compile.Verify.Codec.Ixon.Univ.WireWF value) :
    Writes (do for value in values do Ixon.putUniv value)
      (listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode values.toList) := by
  exact arrayPut_writes Ixon.putUniv
    Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode
    Ix.Compile.Verify.Codec.Ixon.Univ.WireWF values h
    Ix.Compile.Verify.Codec.Ixon.Univ.putUniv_writes

theorem getUnivArray_reads (values : Array Ixon.Univ)
    (h : ∀ value, value ∈ values.toList →
      Ix.Compile.Verify.Codec.Ixon.Univ.WireWF value) :
    Reads (getMany Ixon.getUniv values.size)
      (listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode values.toList)
      values := by
  have hall : ∀ value, value ∈ values.toList →
      Ix.Compile.Verify.Codec.Ixon.Univ.WireWF value := by
    exact h
  simpa using getMany_reads Ixon.getUniv
    Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode values.toList
    (fun value hmem =>
      Ix.Compile.Verify.Codec.Ixon.Univ.getUniv_reads value
        (hall value hmem))

open Ix.Compile.Verify.Codec.Ixon.Constant

/-- Full wire domain for definition/axiom constants with arbitrary side
    tables. -/
structure CoreConstantWireWF (constant : Ixon.Constant) : Prop where
  info : CoreInfoWireWF constant.info
  sharingCount : ArrayCountWF constant.sharing
  sharingEntries : ∀ value, value ∈ constant.sharing.toList →
    Ixon.Expr.wireWF value
  refsCount : ArrayCountWF constant.refs
  refsEntries : ∀ value, value ∈ constant.refs.toList → AddressWireWF value
  univsCount : ArrayCountWF constant.univs
  univsEntries : ∀ value, value ∈ constant.univs.toList →
    Ix.Compile.Verify.Codec.Ixon.Univ.WireWF value

def constantBytes (constant : Ixon.Constant) : ByteArray :=
  infoBytes constant.info ++
    tag0Bytes constant.sharing.size.toUInt64 ++
      listBytes Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode
        constant.sharing.toList ++
        tag0Bytes constant.refs.size.toUInt64 ++
          listBytes Address.hash constant.refs.toList ++
            tag0Bytes constant.univs.size.toUInt64 ++
              listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode
                constant.univs.toList

theorem putConstant_writes_core (constant : Ixon.Constant)
    (h : CoreConstantWireWF constant) :
    Writes (Ixon.putConstant constant) (constantBytes constant) := by
  have hwrite := (putConstantInfo_writes_core constant.info h.info).bind
    ((putTag0_writes constant.sharing.size.toUInt64).bind
      ((putExprArray_writes constant.sharing h.sharingEntries).bind
        ((putTag0_writes constant.refs.size.toUInt64).bind
          ((putAddressArray_writes constant.refs h.refsEntries).bind
            ((putTag0_writes constant.univs.size.toUInt64).bind
              (putUnivArray_writes constant.univs h.univsEntries))))))
  simpa [Ixon.putConstant, constantBytes, ByteArray.append_assoc] using hwrite

theorem getConstantUnivs_reads_core (info : Ixon.ConstantInfo)
    (sharing : Array Ixon.Expr) (refs : Array Address)
    (univs : Array Ixon.Univ) (hcount : ArrayCountWF univs)
    (hentries : ∀ value, value ∈ univs.toList →
      Ix.Compile.Verify.Codec.Ixon.Univ.WireWF value) :
    Reads (getConstantUnivs info sharing refs)
      (tag0Bytes univs.size.toUInt64 ++
        listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode univs.toList)
      ⟨info, sharing, refs, univs⟩ := by
  have htag := getTag0_reads univs.size.toUInt64
  have hdecode := arrayCount_decode univs hcount
  have hvalues := getUnivArray_reads univs hentries
  have hreturn := Reads.pure (⟨info, sharing, refs, univs⟩ : Ixon.Constant)
  have hafterValues := Reads.bind
    (next := fun decoded : Array Ixon.Univ =>
      (pure (⟨info, sharing, refs, decoded⟩ : Ixon.Constant) :
        Ixon.GetM Ixon.Constant))
    hvalues hreturn
  have htail : Reads
      (do
        let mut decoded : Array Ixon.Univ := #[]
        for _ in [0:univs.size.toUInt64.toNat] do
          decoded := decoded.push (← Ixon.getUniv)
        return (⟨info, sharing, refs, decoded⟩ : Ixon.Constant))
      (listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode univs.toList)
      ⟨info, sharing, refs, univs⟩ := by
    simpa [getMany, hdecode] using hafterValues
  have hall := Reads.bind
    (next := fun count : Ixon.Tag0 => do
      let mut decoded : Array Ixon.Univ := #[]
      for _ in [0:count.size.toNat] do
        decoded := decoded.push (← Ixon.getUniv)
      return (⟨info, sharing, refs, decoded⟩ : Ixon.Constant))
    htag htail
  simpa [getConstantUnivs] using hall

theorem getConstantRefs_reads_core (info : Ixon.ConstantInfo)
    (sharing : Array Ixon.Expr) (refs : Array Address)
    (univs : Array Ixon.Univ) (hrefCount : ArrayCountWF refs)
    (hrefEntries : ∀ value, value ∈ refs.toList → AddressWireWF value)
    (hunivCount : ArrayCountWF univs)
    (hunivEntries : ∀ value, value ∈ univs.toList →
      Ix.Compile.Verify.Codec.Ixon.Univ.WireWF value) :
    Reads (getConstantRefs info sharing)
      (tag0Bytes refs.size.toUInt64 ++ listBytes Address.hash refs.toList ++
        tag0Bytes univs.size.toUInt64 ++
          listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode univs.toList)
      ⟨info, sharing, refs, univs⟩ := by
  have htag := getTag0_reads refs.size.toUInt64
  have hdecode := arrayCount_decode refs hrefCount
  have hvalues := getAddressArray_reads refs hrefEntries
  have hunivs := getConstantUnivs_reads_core info sharing refs univs
    hunivCount hunivEntries
  have hafterValues := Reads.bind
    (next := fun decoded : Array Address =>
      getConstantUnivs info sharing decoded)
    hvalues hunivs
  have htail : Reads
      (do
        let mut decoded : Array Address := #[]
        for _ in [0:refs.size.toUInt64.toNat] do
          decoded := decoded.push (← Ixon.Serialize.get)
        getConstantUnivs info sharing decoded)
      (listBytes Address.hash refs.toList ++
        tag0Bytes univs.size.toUInt64 ++
          listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode univs.toList)
      ⟨info, sharing, refs, univs⟩ := by
    simpa [getMany, hdecode, ByteArray.append_assoc] using hafterValues
  have hall := Reads.bind
    (next := fun count : Ixon.Tag0 => do
      let mut decoded : Array Address := #[]
      for _ in [0:count.size.toNat] do
        decoded := decoded.push (← Ixon.Serialize.get)
      getConstantUnivs info sharing decoded)
    htag htail
  simpa [getConstantRefs, ByteArray.append_assoc] using hall

theorem getConstantAfterInfo_reads_core (info : Ixon.ConstantInfo)
    (sharing : Array Ixon.Expr) (refs : Array Address)
    (univs : Array Ixon.Univ) (hsharingCount : ArrayCountWF sharing)
    (hsharingEntries : ∀ value, value ∈ sharing.toList →
      Ixon.Expr.wireWF value)
    (hrefCount : ArrayCountWF refs)
    (hrefEntries : ∀ value, value ∈ refs.toList → AddressWireWF value)
    (hunivCount : ArrayCountWF univs)
    (hunivEntries : ∀ value, value ∈ univs.toList →
      Ix.Compile.Verify.Codec.Ixon.Univ.WireWF value) :
    Reads (getConstantAfterInfo info)
      (tag0Bytes sharing.size.toUInt64 ++
        listBytes Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode sharing.toList ++
          tag0Bytes refs.size.toUInt64 ++ listBytes Address.hash refs.toList ++
            tag0Bytes univs.size.toUInt64 ++
              listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode univs.toList)
      ⟨info, sharing, refs, univs⟩ := by
  have htag := getTag0_reads sharing.size.toUInt64
  have hdecode := arrayCount_decode sharing hsharingCount
  have hvalues := getExprArray_reads sharing hsharingEntries
  have hrefs := getConstantRefs_reads_core info sharing refs univs hrefCount
    hrefEntries hunivCount hunivEntries
  have hafterValues := Reads.bind
    (next := fun decoded : Array Ixon.Expr => getConstantRefs info decoded)
    hvalues hrefs
  have htail : Reads
      (do
        let mut decoded : Array Ixon.Expr := #[]
        for _ in [0:sharing.size.toUInt64.toNat] do
          decoded := decoded.push (← Ixon.getExpr)
        getConstantRefs info decoded)
      (listBytes Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode sharing.toList ++
        tag0Bytes refs.size.toUInt64 ++ listBytes Address.hash refs.toList ++
          tag0Bytes univs.size.toUInt64 ++
            listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode univs.toList)
      ⟨info, sharing, refs, univs⟩ := by
    simpa [getMany, hdecode, ByteArray.append_assoc] using hafterValues
  have hall := Reads.bind
    (next := fun count : Ixon.Tag0 => do
      let mut decoded : Array Ixon.Expr := #[]
      for _ in [0:count.size.toNat] do
        decoded := decoded.push (← Ixon.getExpr)
      getConstantRefs info decoded)
    htag htail
  simpa [getConstantAfterInfo, ByteArray.append_assoc] using hall

theorem getConstant_reads_core (constant : Ixon.Constant)
    (h : CoreConstantWireWF constant) :
    Reads Ixon.getConstant (constantBytes constant) constant := by
  have hinfo := getConstantInfo_reads_core constant.info h.info
  have htail := getConstantAfterInfo_reads_core constant.info
    constant.sharing constant.refs constant.univs h.sharingCount
    h.sharingEntries h.refsCount h.refsEntries h.univsCount h.univsEntries
  have hall := Reads.bind (next := getConstantAfterInfo) hinfo htail
  rw [getConstant_eq]
  simpa [constantBytes, ByteArray.append_assoc] using hall

/-- Top-level production constant codec round trip for definition and axiom
    payloads with arbitrary well-formed side tables. -/
theorem deConstant_serConstant_core (constant : Ixon.Constant)
    (h : CoreConstantWireWF constant) :
    Ixon.deConstant (Ixon.serConstant constant) = .ok constant := by
  unfold Ixon.serConstant
  rw [(putConstant_writes_core constant h).runPut]
  unfold Ixon.deConstant Ixon.runGet
  have hread := getConstant_reads_core constant h
    ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getConstant { bytes := constantBytes constant } = _
    at hread
  rw [hread]

end Ix.Compile.Verify.Codec.Ixon.ConstantTables

namespace Ix.Compile.Verify

abbrev ConstantAddressWireWF : Address → Prop :=
  Codec.Ixon.ConstantTables.AddressWireWF

abbrev ConstantArrayCountWF {α : Type} : Array α → Prop :=
  Codec.Ixon.ConstantTables.ArrayCountWF

abbrev CoreConstantWireWF : Ixon.Constant → Prop :=
  Codec.Ixon.ConstantTables.CoreConstantWireWF

/-- Production top-level constant round trip for core declaration payloads
    and arbitrary wire-representable sharing/reference/universe tables. -/
theorem deConstant_serConstant_core (constant : Ixon.Constant)
    (h : CoreConstantWireWF constant) :
    Ixon.deConstant (Ixon.serConstant constant) = .ok constant :=
  Codec.Ixon.ConstantTables.deConstant_serConstant_core constant h

end Ix.Compile.Verify
