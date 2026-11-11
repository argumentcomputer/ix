/-
Extracted from Ix/Compile/Verify/ConstantTablesCodec.lean at Ix revision
b067697b9d97552c6f52b2f72c892f84e4c7170f,
and the Ixon v4 (TagN) changes to that file at Ix revision
22afee6d9245bd5f974ad59019affed034d84615.
-/

import IxC.Ixon.Verify.Constant

/-!
# Proof-visible v2 constant side-table codec

This slice lifts the verified expression, universe, and core constant-info
codecs through the production sharing, reference, and universe table loops.
It records the format's two necessary side-table conditions explicitly:
array lengths survive the `Nat → UInt64 → Nat` wire-count conversion, and
serialized addresses contain exactly 32 bytes.
-/

namespace Ixon.Verify.Codec.ConstantTables

open Ix
open Ixon.Verify.Codec

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
  rw [ite_eq_left (by simp [ByteArray.size_append])]
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
    Ixon.Verify.Codec.Constant.reads_map Address.mk
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
      (listBytes Ixon.Verify.Codec.Expr.spineWireEncode values.toList) := by
  exact arrayPut_writes Ixon.putExpr
    Ixon.Verify.Codec.Expr.spineWireEncode
    Ixon.Expr.wireWF values h
    Ixon.Verify.Codec.Expr.putExpr_writes_spine

theorem getExprArray_reads (values : Array Ixon.Expr)
    (h : ∀ value, value ∈ values.toList →
      Ixon.Expr.wireWF value) :
    Reads (getMany Ixon.getExpr values.size)
      (listBytes Ixon.Verify.Codec.Expr.spineWireEncode values.toList)
      values := by
  have hall : ∀ value, value ∈ values.toList →
      Ixon.Expr.wireWF value := by
    exact h
  simpa using getMany_reads Ixon.getExpr
    Ixon.Verify.Codec.Expr.spineWireEncode values.toList
    (fun value hmem =>
      Ixon.Verify.Codec.Expr.getExpr_reads_spine value
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
      Ixon.Verify.Codec.Univ.WireWF value) :
    Writes (do for value in values do Ixon.putUniv value)
      (listBytes Ixon.Verify.Codec.Univ.wireEncode values.toList) := by
  exact arrayPut_writes Ixon.putUniv
    Ixon.Verify.Codec.Univ.wireEncode
    Ixon.Verify.Codec.Univ.WireWF values h
    Ixon.Verify.Codec.Univ.putUniv_writes

theorem getUnivArray_reads (values : Array Ixon.Univ)
    (h : ∀ value, value ∈ values.toList →
      Ixon.Verify.Codec.Univ.WireWF value) :
    Reads (getMany Ixon.getUniv values.size)
      (listBytes Ixon.Verify.Codec.Univ.wireEncode values.toList)
      values := by
  have hall : ∀ value, value ∈ values.toList →
      Ixon.Verify.Codec.Univ.WireWF value := by
    exact h
  simpa using getMany_reads Ixon.getUniv
    Ixon.Verify.Codec.Univ.wireEncode values.toList
    (fun value hmem =>
      Ixon.Verify.Codec.Univ.getUniv_reads value
        (hall value hmem))

/-! ## The binder-data section -/

theorem getMany_eq_getArray (getm : Ixon.GetM α) (count : Nat) :
    getMany getm count = Ixon.getArray getm count := rfl

/-- Run a reader, then return a function of its value. -/
theorem reads_bind_pure {getm : Ixon.GetM α} {bytes : ByteArray} {value : α}
    (f : α → β) (h : Reads getm bytes value) :
    Reads (getm >>= fun a => pure (f a)) bytes (f value) := by
  intro before after
  change (EStateM.bind getm _) _ = _
  rw [EStateM.bind, h before after]
  rfl

def binderNodeBytes : Ixon.BinderNode → ByteArray
  | .never => [0].toByteArray
  | .zero => [1].toByteArray
  | .ifAllZero params => [2].toByteArray ++
      (tag0Bytes params.size.toUInt64 ++
        Ixon.Verify.Codec.Expr.tag0ListBytes params.toList)
  | .share variant => [3].toByteArray ++ tag0Bytes variant
  | .undecided => [4].toByteArray

def binderBlockBytes (block : Ixon.BinderBlock) : ByteArray :=
  [if block.shared then 1 else 0].toByteArray ++ tag0Bytes block.index ++
    tag0Bytes block.variant ++ tag0Bytes block.nodes.size.toUInt64 ++
      listBytes binderNodeBytes block.nodes.toList

def bindersBytes (blocks : Array Ixon.BinderBlock) : ByteArray :=
  tag0Bytes blocks.size.toUInt64 ++ listBytes binderBlockBytes blocks.toList

theorem putBinderNode_writes (node : Ixon.BinderNode) :
    Writes (Ixon.putBinderNode node) (binderNodeBytes node) := by
  cases node with
  | never => exact putU8_writes 0
  | zero => exact putU8_writes 1
  | ifAllZero params =>
    have hwrite := (putU8_writes 2).bind
      ((putTag0_writes params.size.toUInt64).bind
        (Ixon.Verify.Codec.Expr.arrayPutTag0_writes params))
    simpa [Ixon.putBinderNode, binderNodeBytes] using hwrite
  | share variant =>
    have hwrite := (putU8_writes 3).bind (putTag0_writes variant)
    simpa [Ixon.putBinderNode, binderNodeBytes] using hwrite
  | undecided => exact putU8_writes 4

theorem getBinderNode_reads (node : Ixon.BinderNode) (h : node.wireWF) :
    Reads Ixon.getBinderNode (binderNodeBytes node) node := by
  cases node with
  | never =>
    show Reads Ixon.getBinderNode [0].toByteArray .never
    intro before after
    change (EStateM.bind Ixon.getU8 _) _ = _
    rw [EStateM.bind, getU8_reads 0 before after]
    rfl
  | zero =>
    show Reads Ixon.getBinderNode [1].toByteArray .zero
    intro before after
    change (EStateM.bind Ixon.getU8 _) _ = _
    rw [EStateM.bind, getU8_reads 1 before after]
    rfl
  | undecided =>
    show Reads Ixon.getBinderNode [4].toByteArray .undecided
    intro before after
    change (EStateM.bind Ixon.getU8 _) _ = _
    rw [EStateM.bind, getU8_reads 4 before after]
    rfl
  | share variant =>
    show Reads Ixon.getBinderNode ([3].toByteArray ++ tag0Bytes variant) (.share variant)
    unfold Ixon.getBinderNode
    exact Reads.bind (getU8_reads 3)
      (reads_bind_pure (fun t : Ixon.TagN => Ixon.BinderNode.share t.value)
        (getTag0_reads variant))
  | ifAllZero params =>
    have hcount : params.size.toUInt64.toNat = params.size := by
      change (UInt64.ofNat params.size).toNat = params.size
      exact UInt64.toNat_ofNat_of_lt h
    have hreturn : Reads
        (pure (Ixon.BinderNode.ifAllZero params.toList.toArray) :
          Ixon.GetM Ixon.BinderNode)
        ByteArray.empty (.ifAllZero params) := by
      simpa using Reads.pure (Ixon.BinderNode.ifAllZero params)
    have hvalues := Reads.bind
      (next := fun decoded : List UInt64 =>
        (pure (Ixon.BinderNode.ifAllZero decoded.toArray) :
          Ixon.GetM Ixon.BinderNode))
      (Ixon.Verify.Codec.Expr.getTagN0Values_reads params.toList) hreturn
    have hparams : Reads
        (do
          let decoded ← Ixon.getTagN0Values params.size.toUInt64.toNat
          return Ixon.BinderNode.ifAllZero decoded.toArray)
        (Ixon.Verify.Codec.Expr.tag0ListBytes params.toList) (.ifAllZero params) := by
      rw [hcount]
      simpa using hvalues
    have hcountRead := Reads.bind
      (next := fun count : Ixon.TagN => do
        let decoded ← Ixon.getTagN0Values count.value.toNat
        return Ixon.BinderNode.ifAllZero decoded.toArray)
      (getTag0_reads params.size.toUInt64) hparams
    show Reads Ixon.getBinderNode
      ([2].toByteArray ++ (tag0Bytes params.size.toUInt64 ++
        Ixon.Verify.Codec.Expr.tag0ListBytes params.toList)) (.ifAllZero params)
    unfold Ixon.getBinderNode
    exact Reads.bind (getU8_reads 2) hcountRead

theorem putBinderBlock_writes (block : Ixon.BinderBlock) :
    Writes (Ixon.putBinderBlock block) (binderBlockBytes block) := by
  have hwrite := (putU8_writes (if block.shared then 1 else 0)).bind
    ((putTag0_writes block.index).bind
      ((putTag0_writes block.variant).bind
        ((putTag0_writes block.nodes.size.toUInt64).bind
          (arrayPut_writes Ixon.putBinderNode binderNodeBytes (fun _ => True)
            block.nodes (fun _ _ => trivial) (fun node _ => putBinderNode_writes node)))))
  simpa [Ixon.putBinderBlock, binderBlockBytes, ByteArray.append_assoc] using hwrite

theorem getBinderBlock_reads (block : Ixon.BinderBlock) (h : block.wireWF) :
    Reads Ixon.getBinderBlock (binderBlockBytes block) block := by
  have hcount := arrayCount_decode block.nodes h.1
  have hnodes : Reads (Ixon.getArray Ixon.getBinderNode block.nodes.size)
      (listBytes binderNodeBytes block.nodes.toList) block.nodes := by
    have hread := getMany_reads Ixon.getBinderNode binderNodeBytes block.nodes.toList
      (fun node hmem => getBinderNode_reads node (h.2 node (Array.mem_toList_iff.mp hmem)))
    simpa [getMany_eq_getArray] using hread
  have hafterNodes := Reads.bind
    (next := fun nodes : Array Ixon.BinderNode =>
      (pure ({ block with nodes } : Ixon.BinderBlock) : Ixon.GetM Ixon.BinderBlock))
    hnodes (Reads.pure block)
  have hnodesTail : Reads
      (do
        let nodes ← Ixon.getArray Ixon.getBinderNode block.nodes.size.toUInt64.toNat
        return ({ block with nodes } : Ixon.BinderBlock))
      (listBytes binderNodeBytes block.nodes.toList) block := by
    rw [hcount]
    simpa using hafterNodes
  have hafterCount := Reads.bind
    (next := fun count : Ixon.TagN => do
      let nodes ← Ixon.getArray Ixon.getBinderNode count.value.toNat
      return ({ block with nodes } : Ixon.BinderBlock))
    (getTag0_reads block.nodes.size.toUInt64) hnodesTail
  have hafterVariant := Reads.bind
    (next := fun variant : Ixon.TagN => do
      let count := (← Ixon.getTagN 0).value.toNat
      let nodes ← Ixon.getArray Ixon.getBinderNode count
      return ({ block with variant := variant.value, nodes } : Ixon.BinderBlock))
    (getTag0_reads block.variant) hafterCount
  have hafterIndex := Reads.bind
    (next := fun index : Ixon.TagN => do
      let variant := (← Ixon.getTagN 0).value
      let count := (← Ixon.getTagN 0).value.toNat
      let nodes ← Ixon.getArray Ixon.getBinderNode count
      return ({ block with index := index.value, variant, nodes } : Ixon.BinderBlock))
    (getTag0_reads block.index) hafterVariant
  have hall := Reads.bind
    (next := fun shared : Bool => do
      let index := (← Ixon.getTagN 0).value
      let variant := (← Ixon.getTagN 0).value
      let count := (← Ixon.getTagN 0).value.toNat
      let nodes ← Ixon.getArray Ixon.getBinderNode count
      return (⟨shared, index, variant, nodes⟩ : Ixon.BinderBlock))
    (Ixon.Verify.Codec.Constant.getBool_reads block.shared) hafterIndex
  simpa [Ixon.getBinderBlock, binderBlockBytes, ByteArray.append_assoc] using hall

theorem putBinders_writes (blocks : Array Ixon.BinderBlock) :
    Writes (Ixon.putBinders blocks) (bindersBytes blocks) := by
  have hwrite := (putTag0_writes blocks.size.toUInt64).bind
    (arrayPut_writes Ixon.putBinderBlock binderBlockBytes (fun _ => True)
      blocks (fun _ _ => trivial) (fun block _ => putBinderBlock_writes block))
  simpa [Ixon.putBinders, bindersBytes] using hwrite

theorem getBinders_reads (blocks : Array Ixon.BinderBlock) (h : Ixon.bindersWireWF blocks) :
    Reads Ixon.getBinders (bindersBytes blocks) blocks := by
  have hcount := arrayCount_decode blocks h.1
  have hblocks : Reads (Ixon.getArray Ixon.getBinderBlock blocks.size.toUInt64.toNat)
      (listBytes binderBlockBytes blocks.toList) blocks := by
    rw [hcount]
    have hread := getMany_reads Ixon.getBinderBlock binderBlockBytes blocks.toList
      (fun block hmem => getBinderBlock_reads block (h.2 block (Array.mem_toList_iff.mp hmem)))
    simpa [getMany_eq_getArray] using hread
  have hall := Reads.bind
    (next := fun count : Ixon.TagN => Ixon.getArray Ixon.getBinderBlock count.value.toNat)
    (getTag0_reads blocks.size.toUInt64) hblocks
  simpa [Ixon.getBinders, bindersBytes] using hall

open Ixon.Verify.Codec.Constant

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
    Ixon.Verify.Codec.Univ.WireWF value
  binders : Ixon.bindersWireWF constant.binders

def constantBytes (constant : Ixon.Constant) : ByteArray :=
  infoBytes constant.info ++
    tag0Bytes constant.sharing.size.toUInt64 ++
      listBytes Ixon.Verify.Codec.Expr.spineWireEncode
        constant.sharing.toList ++
        tag0Bytes constant.refs.size.toUInt64 ++
          listBytes Address.hash constant.refs.toList ++
            tag0Bytes constant.univs.size.toUInt64 ++
              listBytes Ixon.Verify.Codec.Univ.wireEncode
                constant.univs.toList ++
                bindersBytes constant.binders

theorem putConstant_writes_core (constant : Ixon.Constant)
    (h : CoreConstantWireWF constant) :
    Writes (Ixon.putConstant constant) (constantBytes constant) := by
  have hwrite := (putConstantInfo_writes_core constant.info h.info).bind
    ((putTag0_writes constant.sharing.size.toUInt64).bind
      ((putExprArray_writes constant.sharing h.sharingEntries).bind
        ((putTag0_writes constant.refs.size.toUInt64).bind
          ((putAddressArray_writes constant.refs h.refsEntries).bind
            ((putTag0_writes constant.univs.size.toUInt64).bind
              ((putUnivArray_writes constant.univs h.univsEntries).bind
                (putBinders_writes constant.binders)))))))
  simpa [Ixon.putConstant, constantBytes, ByteArray.append_assoc] using hwrite

theorem getConstantUnivs_reads_core (info : Ixon.ConstantInfo)
    (sharing : Array Ixon.Expr) (refs : Array Address)
    (univs : Array Ixon.Univ) (binders : Array Ixon.BinderBlock)
    (hcount : ArrayCountWF univs)
    (hentries : ∀ value, value ∈ univs.toList →
      Ixon.Verify.Codec.Univ.WireWF value)
    (hbinders : Ixon.bindersWireWF binders) :
    Reads (getConstantUnivs info sharing refs)
      (tag0Bytes univs.size.toUInt64 ++
        listBytes Ixon.Verify.Codec.Univ.wireEncode univs.toList ++
          bindersBytes binders)
      ⟨info, sharing, refs, univs, binders⟩ := by
  have htag := getTag0_reads univs.size.toUInt64
  have hdecode := arrayCount_decode univs hcount
  have hvalues := getUnivArray_reads univs hentries
  have hreturn := Reads.pure (⟨info, sharing, refs, univs, binders⟩ : Ixon.Constant)
  have hafterBinders := Reads.bind
    (next := fun decoded : Array Ixon.BinderBlock =>
      (pure (⟨info, sharing, refs, univs, decoded⟩ : Ixon.Constant) :
        Ixon.GetM Ixon.Constant))
    (getBinders_reads binders hbinders) hreturn
  have hafterValues := Reads.bind
    (next := fun decoded : Array Ixon.Univ => do
      let decodedBinders ← Ixon.getBinders
      return (⟨info, sharing, refs, decoded, decodedBinders⟩ : Ixon.Constant))
    hvalues hafterBinders
  have htail : Reads
      (do
        let mut decoded : Array Ixon.Univ := #[]
        for _ in [0:univs.size.toUInt64.toNat] do
          decoded := decoded.push (← Ixon.getUniv)
        let decodedBinders ← Ixon.getBinders
        return (⟨info, sharing, refs, decoded, decodedBinders⟩ : Ixon.Constant))
      (listBytes Ixon.Verify.Codec.Univ.wireEncode univs.toList ++
        bindersBytes binders)
      ⟨info, sharing, refs, univs, binders⟩ := by
    simpa [getMany, hdecode] using hafterValues
  have hall := Reads.bind
    (next := fun count : Ixon.TagN => do
      let mut decoded : Array Ixon.Univ := #[]
      for _ in [0:count.value.toNat] do
        decoded := decoded.push (← Ixon.getUniv)
      let decodedBinders ← Ixon.getBinders
      return (⟨info, sharing, refs, decoded, decodedBinders⟩ : Ixon.Constant))
    htag htail
  simpa [getConstantUnivs, ByteArray.append_assoc] using hall

theorem getConstantRefs_reads_core (info : Ixon.ConstantInfo)
    (sharing : Array Ixon.Expr) (refs : Array Address)
    (univs : Array Ixon.Univ) (binders : Array Ixon.BinderBlock)
    (hrefCount : ArrayCountWF refs)
    (hrefEntries : ∀ value, value ∈ refs.toList → AddressWireWF value)
    (hunivCount : ArrayCountWF univs)
    (hunivEntries : ∀ value, value ∈ univs.toList →
      Ixon.Verify.Codec.Univ.WireWF value)
    (hbinders : Ixon.bindersWireWF binders) :
    Reads (getConstantRefs info sharing)
      (tag0Bytes refs.size.toUInt64 ++ listBytes Address.hash refs.toList ++
        tag0Bytes univs.size.toUInt64 ++
          listBytes Ixon.Verify.Codec.Univ.wireEncode univs.toList ++
            bindersBytes binders)
      ⟨info, sharing, refs, univs, binders⟩ := by
  have htag := getTag0_reads refs.size.toUInt64
  have hdecode := arrayCount_decode refs hrefCount
  have hvalues := getAddressArray_reads refs hrefEntries
  have hunivs := getConstantUnivs_reads_core info sharing refs univs binders
    hunivCount hunivEntries hbinders
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
          listBytes Ixon.Verify.Codec.Univ.wireEncode univs.toList ++
            bindersBytes binders)
      ⟨info, sharing, refs, univs, binders⟩ := by
    simpa [getMany, hdecode, ByteArray.append_assoc] using hafterValues
  have hall := Reads.bind
    (next := fun count : Ixon.TagN => do
      let mut decoded : Array Address := #[]
      for _ in [0:count.value.toNat] do
        decoded := decoded.push (← Ixon.Serialize.get)
      getConstantUnivs info sharing decoded)
    htag htail
  simpa [getConstantRefs, ByteArray.append_assoc] using hall

theorem getConstantAfterInfo_reads_core (info : Ixon.ConstantInfo)
    (sharing : Array Ixon.Expr) (refs : Array Address)
    (univs : Array Ixon.Univ) (binders : Array Ixon.BinderBlock)
    (hsharingCount : ArrayCountWF sharing)
    (hsharingEntries : ∀ value, value ∈ sharing.toList →
      Ixon.Expr.wireWF value)
    (hrefCount : ArrayCountWF refs)
    (hrefEntries : ∀ value, value ∈ refs.toList → AddressWireWF value)
    (hunivCount : ArrayCountWF univs)
    (hunivEntries : ∀ value, value ∈ univs.toList →
      Ixon.Verify.Codec.Univ.WireWF value)
    (hbinders : Ixon.bindersWireWF binders) :
    Reads (getConstantAfterInfo info)
      (tag0Bytes sharing.size.toUInt64 ++
        listBytes Ixon.Verify.Codec.Expr.spineWireEncode sharing.toList ++
          tag0Bytes refs.size.toUInt64 ++ listBytes Address.hash refs.toList ++
            tag0Bytes univs.size.toUInt64 ++
              listBytes Ixon.Verify.Codec.Univ.wireEncode univs.toList ++
                bindersBytes binders)
      ⟨info, sharing, refs, univs, binders⟩ := by
  have htag := getTag0_reads sharing.size.toUInt64
  have hdecode := arrayCount_decode sharing hsharingCount
  have hvalues := getExprArray_reads sharing hsharingEntries
  have hrefs := getConstantRefs_reads_core info sharing refs univs binders hrefCount
    hrefEntries hunivCount hunivEntries hbinders
  have hafterValues := Reads.bind
    (next := fun decoded : Array Ixon.Expr => getConstantRefs info decoded)
    hvalues hrefs
  have htail : Reads
      (do
        let mut decoded : Array Ixon.Expr := #[]
        for _ in [0:sharing.size.toUInt64.toNat] do
          decoded := decoded.push (← Ixon.getExpr)
        getConstantRefs info decoded)
      (listBytes Ixon.Verify.Codec.Expr.spineWireEncode sharing.toList ++
        tag0Bytes refs.size.toUInt64 ++ listBytes Address.hash refs.toList ++
          tag0Bytes univs.size.toUInt64 ++
            listBytes Ixon.Verify.Codec.Univ.wireEncode univs.toList ++
              bindersBytes binders)
      ⟨info, sharing, refs, univs, binders⟩ := by
    simpa [getMany, hdecode, ByteArray.append_assoc] using hafterValues
  have hall := Reads.bind
    (next := fun count : Ixon.TagN => do
      let mut decoded : Array Ixon.Expr := #[]
      for _ in [0:count.value.toNat] do
        decoded := decoded.push (← Ixon.getExpr)
      getConstantRefs info decoded)
    htag htail
  simpa [getConstantAfterInfo, ByteArray.append_assoc] using hall

theorem getConstant_reads_core (constant : Ixon.Constant)
    (h : CoreConstantWireWF constant) :
    Reads Ixon.getConstant (constantBytes constant) constant := by
  have hinfo := getConstantInfo_reads_core constant.info h.info
  have htail := getConstantAfterInfo_reads_core constant.info
    constant.sharing constant.refs constant.univs constant.binders h.sharingCount
    h.sharingEntries h.refsCount h.refsEntries h.univsCount h.univsEntries h.binders
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

end Ixon.Verify.Codec.ConstantTables

namespace Ixon.Verify

abbrev ConstantAddressWireWF : Address → Prop :=
  Codec.ConstantTables.AddressWireWF

abbrev ConstantArrayCountWF {α : Type} : Array α → Prop :=
  Codec.ConstantTables.ArrayCountWF

abbrev CoreConstantWireWF : Ixon.Constant → Prop :=
  Codec.ConstantTables.CoreConstantWireWF

/-- Production top-level constant round trip for core declaration payloads
    and arbitrary wire-representable sharing/reference/universe tables. -/
theorem deConstant_serConstant_core (constant : Ixon.Constant)
    (h : CoreConstantWireWF constant) :
    Ixon.deConstant (Ixon.serConstant constant) = .ok constant :=
  Codec.ConstantTables.deConstant_serConstant_core constant h

end Ixon.Verify
