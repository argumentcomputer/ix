import Ix.Compile.Verify.ConstantTablesCodec

/-!
# Proof-visible nonrecursive constant-info codec

This slice extends the verified definition/axiom constant codec across
quotient declarations and all four projection records.  Together these are
the production `ConstantInfo` variants without recursively encoded payload
arrays.  Projection block addresses expose their required 32-byte wire
invariant; every expression payload may use an arbitrary canonical wire-sized
application, lambda, or forall spine.  The final theorem retains arbitrary
well-formed top-level sharing,
reference, and universe tables.
-/

namespace Ix.Compile.Verify.Codec.Ixon.NonrecursiveConstant

open Ix
open Ix.Compile.Verify.Codec
open Ix.Compile.Verify.Codec.Ixon.Constant
open Ix.Compile.Verify.Codec.Ixon.ConstantTables

def quotKindByte : QuotKind → UInt8
  | .type => 0
  | .ctor => 1
  | .lift => 2
  | .ind => 3

def quotientBytes (quotient : Ixon.Quotient) : ByteArray :=
  [quotKindByte quotient.kind].toByteArray ++
    tag0Bytes quotient.lvls ++
      Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode quotient.typ

theorem putQuotient_writes (quotient : Ixon.Quotient)
    (htyp : Ixon.Expr.wireWF quotient.typ) :
    Writes (Ixon.putQuotient quotient) (quotientBytes quotient) := by
  rcases quotient with ⟨kind, lvls, typ⟩
  cases kind with
  | type => simpa [Ixon.putQuotient, quotientBytes, quotKindByte,
      ByteArray.append_assoc] using
      (putU8_writes 0).bind ((putTag0_writes lvls).bind
        (Ix.Compile.Verify.Codec.Ixon.Expr.putExpr_writes_spine typ htyp))
  | ctor => simpa [Ixon.putQuotient, quotientBytes, quotKindByte,
      ByteArray.append_assoc] using
      (putU8_writes 1).bind ((putTag0_writes lvls).bind
        (Ix.Compile.Verify.Codec.Ixon.Expr.putExpr_writes_spine typ htyp))
  | lift => simpa [Ixon.putQuotient, quotientBytes, quotKindByte,
      ByteArray.append_assoc] using
      (putU8_writes 2).bind ((putTag0_writes lvls).bind
        (Ix.Compile.Verify.Codec.Ixon.Expr.putExpr_writes_spine typ htyp))
  | ind => simpa [Ixon.putQuotient, quotientBytes, quotKindByte,
      ByteArray.append_assoc] using
      (putU8_writes 3).bind ((putTag0_writes lvls).bind
        (Ix.Compile.Verify.Codec.Ixon.Expr.putExpr_writes_spine typ htyp))

def decodeQuotKind (value : UInt8) : Ixon.GetM QuotKind :=
  match value with
  | 0 => pure .type
  | 1 => pure .ctor
  | 2 => pure .lift
  | 3 => pure .ind
  | value => throw s!"invalid QuotKind tag {value}"

theorem decodeQuotKind_reads (kind : QuotKind) :
    Reads (decodeQuotKind (quotKindByte kind)) ByteArray.empty kind := by
  cases kind with
  | type => simpa [decodeQuotKind, quotKindByte] using
      Reads.pure QuotKind.type
  | ctor => simpa [decodeQuotKind, quotKindByte] using
      Reads.pure QuotKind.ctor
  | lift => simpa [decodeQuotKind, quotKindByte] using
      Reads.pure QuotKind.lift
  | ind => simpa [decodeQuotKind, quotKindByte] using
      Reads.pure QuotKind.ind

theorem getQuotient_reads (quotient : Ixon.Quotient)
    (htyp : Ixon.Expr.wireWF quotient.typ) :
    Reads Ixon.getQuotient (quotientBytes quotient) quotient := by
  rcases quotient with ⟨kind, lvls, typ⟩
  have hpayload (decodedKind : QuotKind) : Reads
      (do
        let decodedLvls := (← Ixon.getTag0).size
        let decodedTyp ← Ixon.getExpr
        return (⟨decodedKind, decodedLvls, decodedTyp⟩ : Ixon.Quotient))
      (tag0Bytes lvls ++
        Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode typ)
      ⟨decodedKind, lvls, typ⟩ := by
    have hlvls := getTag0_reads lvls
    have htypRead := Ix.Compile.Verify.Codec.Ixon.Expr.getExpr_reads_spine
      typ htyp
    have hreturn := Reads.pure (⟨decodedKind, lvls, typ⟩ : Ixon.Quotient)
    have hafterTyp := Reads.bind
      (next := fun decodedTyp : Ixon.Expr =>
        (pure (⟨decodedKind, lvls, decodedTyp⟩ : Ixon.Quotient) :
          Ixon.GetM Ixon.Quotient))
      htypRead hreturn
    have hafterTyp' : Reads
        (do
          let decodedTyp ← Ixon.getExpr
          return (⟨decodedKind, lvls, decodedTyp⟩ : Ixon.Quotient))
        (Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode typ)
        ⟨decodedKind, lvls, typ⟩ := by
      simpa using hafterTyp
    exact Reads.bind
      (next := fun decodedLvls : Ixon.Tag0 => do
        let decodedTyp ← Ixon.getExpr
        return (⟨decodedKind, decodedLvls.size, decodedTyp⟩ : Ixon.Quotient))
      hlvls hafterTyp'
  let next := fun encoded : UInt8 => do
      let decodedKind : QuotKind ← match encoded with
        | 0 => pure .type
        | 1 => pure .ctor
        | 2 => pure .lift
        | 3 => pure .ind
        | _ => throw s!"invalid QuotKind tag {encoded}"
      let lvls := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      return (⟨decodedKind, lvls, typ⟩ : Ixon.Quotient)
  have hget : Ixon.getQuotient = (Ixon.getU8 >>= next) := by
    rfl
  rw [hget]
  cases kind with
  | type =>
    have hall := Reads.bind (next := next) (getU8_reads 0) (by
      simpa [next] using hpayload QuotKind.type)
    simpa [quotientBytes, quotKindByte,
      ByteArray.append_assoc] using hall
  | ctor =>
    have hall := Reads.bind (next := next) (getU8_reads 1) (by
      simpa [next] using hpayload QuotKind.ctor)
    simpa [quotientBytes, quotKindByte,
      ByteArray.append_assoc] using hall
  | lift =>
    have hall := Reads.bind (next := next) (getU8_reads 2) (by
      simpa [next] using hpayload QuotKind.lift)
    simpa [quotientBytes, quotKindByte,
      ByteArray.append_assoc] using hall
  | ind =>
    have hall := Reads.bind (next := next) (getU8_reads 3) (by
      simpa [next] using hpayload QuotKind.ind)
    simpa [quotientBytes, quotKindByte,
      ByteArray.append_assoc] using hall

def inductiveProjBytes (projection : Ixon.InductiveProj) : ByteArray :=
  tag0Bytes projection.idx ++ projection.block.hash

def constructorProjBytes (projection : Ixon.ConstructorProj) : ByteArray :=
  tag0Bytes projection.idx ++ tag0Bytes projection.cidx ++
    projection.block.hash

def recursorProjBytes (projection : Ixon.RecursorProj) : ByteArray :=
  tag0Bytes projection.idx ++ projection.block.hash

def definitionProjBytes (projection : Ixon.DefinitionProj) : ByteArray :=
  tag0Bytes projection.idx ++ projection.block.hash

theorem putInductiveProj_writes (projection : Ixon.InductiveProj) :
    Writes (Ixon.putInductiveProj projection)
      (inductiveProjBytes projection) := by
  simpa [Ixon.putInductiveProj, inductiveProjBytes] using
    (putTag0_writes projection.idx).bind
      (putAddress_writes projection.block)

theorem getInductiveProj_reads (projection : Ixon.InductiveProj)
    (hblock : AddressWireWF projection.block) :
    Reads Ixon.getInductiveProj (inductiveProjBytes projection) projection := by
  have hidx := getTag0_reads projection.idx
  have hblockRead := getAddress_reads projection.block hblock
  have hreturn := Reads.pure projection
  have hafterBlock := Reads.bind
    (next := fun block : Address =>
      (pure ({ projection with block } : Ixon.InductiveProj) :
        Ixon.GetM Ixon.InductiveProj))
    hblockRead hreturn
  have hall := Reads.bind
    (next := fun idx : Ixon.Tag0 => do
      let block ← (Ixon.Serialize.get : Ixon.GetM Address)
      return (⟨idx.size, block⟩ : Ixon.InductiveProj))
    hidx hafterBlock
  simpa [Ixon.getInductiveProj, inductiveProjBytes] using hall

theorem putConstructorProj_writes (projection : Ixon.ConstructorProj) :
    Writes (Ixon.putConstructorProj projection)
      (constructorProjBytes projection) := by
  simpa [Ixon.putConstructorProj, constructorProjBytes,
    ByteArray.append_assoc] using
    (putTag0_writes projection.idx).bind
      ((putTag0_writes projection.cidx).bind
        (putAddress_writes projection.block))

theorem getConstructorProj_reads (projection : Ixon.ConstructorProj)
    (hblock : AddressWireWF projection.block) :
    Reads Ixon.getConstructorProj (constructorProjBytes projection)
      projection := by
  have hidx := getTag0_reads projection.idx
  have hcidx := getTag0_reads projection.cidx
  have hblockRead := getAddress_reads projection.block hblock
  have hreturn := Reads.pure projection
  have hafterBlock := Reads.bind
    (next := fun block : Address =>
      (pure ({ projection with block } : Ixon.ConstructorProj) :
        Ixon.GetM Ixon.ConstructorProj))
    hblockRead hreturn
  have hafterCidx := Reads.bind
    (next := fun cidx : Ixon.Tag0 => do
      let block ← (Ixon.Serialize.get : Ixon.GetM Address)
      return ({ projection with cidx := cidx.size, block } :
        Ixon.ConstructorProj))
    hcidx hafterBlock
  have hall := Reads.bind
    (next := fun idx : Ixon.Tag0 => do
      let cidx := (← Ixon.getTag0).size
      let block ← (Ixon.Serialize.get : Ixon.GetM Address)
      return (⟨idx.size, cidx, block⟩ : Ixon.ConstructorProj))
    hidx hafterCidx
  simpa [Ixon.getConstructorProj, constructorProjBytes,
    ByteArray.append_assoc] using hall

theorem putRecursorProj_writes (projection : Ixon.RecursorProj) :
    Writes (Ixon.putRecursorProj projection)
      (recursorProjBytes projection) := by
  simpa [Ixon.putRecursorProj, recursorProjBytes] using
    (putTag0_writes projection.idx).bind
      (putAddress_writes projection.block)

theorem getRecursorProj_reads (projection : Ixon.RecursorProj)
    (hblock : AddressWireWF projection.block) :
    Reads Ixon.getRecursorProj (recursorProjBytes projection) projection := by
  have hidx := getTag0_reads projection.idx
  have hblockRead := getAddress_reads projection.block hblock
  have hreturn := Reads.pure projection
  have hafterBlock := Reads.bind
    (next := fun block : Address =>
      (pure ({ projection with block } : Ixon.RecursorProj) :
        Ixon.GetM Ixon.RecursorProj))
    hblockRead hreturn
  have hall := Reads.bind
    (next := fun idx : Ixon.Tag0 => do
      let block ← (Ixon.Serialize.get : Ixon.GetM Address)
      return (⟨idx.size, block⟩ : Ixon.RecursorProj))
    hidx hafterBlock
  simpa [Ixon.getRecursorProj, recursorProjBytes] using hall

theorem putDefinitionProj_writes (projection : Ixon.DefinitionProj) :
    Writes (Ixon.putDefinitionProj projection)
      (definitionProjBytes projection) := by
  simpa [Ixon.putDefinitionProj, definitionProjBytes] using
    (putTag0_writes projection.idx).bind
      (putAddress_writes projection.block)

theorem getDefinitionProj_reads (projection : Ixon.DefinitionProj)
    (hblock : AddressWireWF projection.block) :
    Reads Ixon.getDefinitionProj (definitionProjBytes projection) projection := by
  have hidx := getTag0_reads projection.idx
  have hblockRead := getAddress_reads projection.block hblock
  have hreturn := Reads.pure projection
  have hafterBlock := Reads.bind
    (next := fun block : Address =>
      (pure ({ projection with block } : Ixon.DefinitionProj) :
        Ixon.GetM Ixon.DefinitionProj))
    hblockRead hreturn
  have hall := Reads.bind
    (next := fun idx : Ixon.Tag0 => do
      let block ← (Ixon.Serialize.get : Ixon.GetM Address)
      return (⟨idx.size, block⟩ : Ixon.DefinitionProj))
    hidx hafterBlock
  simpa [Ixon.getDefinitionProj, definitionProjBytes] using hall

inductive NonrecursiveInfoWireWF : Ixon.ConstantInfo → Prop where
  | defn {definition : Ixon.Definition} :
      Ixon.Expr.wireWF definition.typ →
      Ixon.Expr.wireWF definition.value →
      NonrecursiveInfoWireWF (.defn definition)
  | axio {axiomInfo : Ixon.Axiom} :
      Ixon.Expr.wireWF axiomInfo.typ →
      NonrecursiveInfoWireWF (.axio axiomInfo)
  | quot {quotient : Ixon.Quotient} :
      Ixon.Expr.wireWF quotient.typ →
      NonrecursiveInfoWireWF (.quot quotient)
  | cPrj {projection : Ixon.ConstructorProj} :
      AddressWireWF projection.block →
      NonrecursiveInfoWireWF (.cPrj projection)
  | rPrj {projection : Ixon.RecursorProj} :
      AddressWireWF projection.block →
      NonrecursiveInfoWireWF (.rPrj projection)
  | iPrj {projection : Ixon.InductiveProj} :
      AddressWireWF projection.block →
      NonrecursiveInfoWireWF (.iPrj projection)
  | dPrj {projection : Ixon.DefinitionProj} :
      AddressWireWF projection.block →
      NonrecursiveInfoWireWF (.dPrj projection)

def nonrecursiveInfoBytes : Ixon.ConstantInfo → ByteArray
  | .defn definition =>
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DEFN ++
        definitionBytes definition
  | .axio axiomInfo =>
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_AXIO ++
        axiomBytes axiomInfo
  | .quot quotient =>
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_QUOT ++
        quotientBytes quotient
  | .cPrj projection =>
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_CPRJ ++
        constructorProjBytes projection
  | .rPrj projection =>
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_RPRJ ++
        recursorProjBytes projection
  | .iPrj projection =>
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ ++
        inductiveProjBytes projection
  | .dPrj projection =>
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DPRJ ++
        definitionProjBytes projection
  | _ => ByteArray.empty

theorem putConstantInfo_writes_nonrecursive (info : Ixon.ConstantInfo)
    (h : NonrecursiveInfoWireWF info) :
    Writes (Ixon.putConstantInfo info) (nonrecursiveInfoBytes info) := by
  cases h with
  | defn htyp hvalue =>
    simpa [nonrecursiveInfoBytes, infoBytes] using
      putConstantInfo_writes_core _ (.defn htyp hvalue)
  | axio htyp =>
    simpa [nonrecursiveInfoBytes, infoBytes] using
      putConstantInfo_writes_core _ (.axio htyp)
  | quot htyp =>
    simpa [Ixon.putConstantInfo, nonrecursiveInfoBytes, seqRight_eq_bind] using
      (putTag4_writes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_QUOT).bind
        (putQuotient_writes _ htyp)
  | cPrj hblock =>
    simpa [Ixon.putConstantInfo, nonrecursiveInfoBytes, seqRight_eq_bind] using
      (putTag4_writes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_CPRJ).bind
        (putConstructorProj_writes _)
  | rPrj hblock =>
    simpa [Ixon.putConstantInfo, nonrecursiveInfoBytes, seqRight_eq_bind] using
      (putTag4_writes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_RPRJ).bind
        (putRecursorProj_writes _)
  | iPrj hblock =>
    simpa [Ixon.putConstantInfo, nonrecursiveInfoBytes, seqRight_eq_bind] using
      (putTag4_writes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ).bind
        (putInductiveProj_writes _)
  | dPrj hblock =>
    simpa [Ixon.putConstantInfo, nonrecursiveInfoBytes, seqRight_eq_bind] using
      (putTag4_writes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DPRJ).bind
        (putDefinitionProj_writes _)

theorem getConstantInfo_reads_variant (variant : UInt64)
    (getm : Ixon.GetM α) (bytes : ByteArray) (value : α)
    (wrap : α → Ixon.ConstantInfo)
    (hdispatch :
      getInfoFromTag ⟨Ixon.Constant.FLAG, variant⟩ = wrap <$> getm)
    (hread : Reads getm bytes value) :
    Reads Ixon.getConstantInfo
      (tag4Bytes Ixon.Constant.FLAG variant ++ bytes) (wrap value) := by
  have htag := getTag4_reads Ixon.Constant.FLAG variant (by decide)
  have htail : Reads
      (getInfoFromTag ⟨Ixon.Constant.FLAG, variant⟩)
      bytes (wrap value) := by
    rw [hdispatch]
    exact reads_map wrap hread
  have hall := Reads.bind (next := getInfoFromTag) htag htail
  rw [getConstantInfo_eq]
  exact hall

theorem getConstantInfo_reads_nonrecursive (info : Ixon.ConstantInfo)
    (h : NonrecursiveInfoWireWF info) :
    Reads Ixon.getConstantInfo (nonrecursiveInfoBytes info) info := by
  cases h with
  | defn htyp hvalue =>
    simpa [nonrecursiveInfoBytes, infoBytes] using
      getConstantInfo_reads_core _ (.defn htyp hvalue)
  | axio htyp =>
    simpa [nonrecursiveInfoBytes, infoBytes] using
      getConstantInfo_reads_core _ (.axio htyp)
  | @quot quotient htyp =>
    apply getConstantInfo_reads_variant
      Ixon.ConstantInfo.CONST_QUOT Ixon.getQuotient
      (quotientBytes quotient) quotient Ixon.ConstantInfo.quot
    · simp [getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
        Ixon.ConstantInfo.CONST_QUOT]
    · exact getQuotient_reads quotient htyp
  | @cPrj projection hblock =>
    apply getConstantInfo_reads_variant
      Ixon.ConstantInfo.CONST_CPRJ Ixon.getConstructorProj
      (constructorProjBytes projection) projection Ixon.ConstantInfo.cPrj
    · simp [getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
        Ixon.ConstantInfo.CONST_CPRJ]
    · exact getConstructorProj_reads projection hblock
  | @rPrj projection hblock =>
    apply getConstantInfo_reads_variant
      Ixon.ConstantInfo.CONST_RPRJ Ixon.getRecursorProj
      (recursorProjBytes projection) projection Ixon.ConstantInfo.rPrj
    · simp [getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
        Ixon.ConstantInfo.CONST_RPRJ]
    · exact getRecursorProj_reads projection hblock
  | @iPrj projection hblock =>
    apply getConstantInfo_reads_variant
      Ixon.ConstantInfo.CONST_IPRJ Ixon.getInductiveProj
      (inductiveProjBytes projection) projection Ixon.ConstantInfo.iPrj
    · simp [getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
        Ixon.ConstantInfo.CONST_IPRJ]
    · exact getInductiveProj_reads projection hblock
  | @dPrj projection hblock =>
    apply getConstantInfo_reads_variant
      Ixon.ConstantInfo.CONST_DPRJ Ixon.getDefinitionProj
      (definitionProjBytes projection) projection Ixon.ConstantInfo.dPrj
    · simp [getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
        Ixon.ConstantInfo.CONST_DPRJ]
    · exact getDefinitionProj_reads projection hblock

structure NonrecursiveConstantWireWF (constant : Ixon.Constant) : Prop where
  info : NonrecursiveInfoWireWF constant.info
  sharingCount : ArrayCountWF constant.sharing
  sharingEntries : ∀ value, value ∈ constant.sharing.toList →
    Ixon.Expr.wireWF value
  refsCount : ArrayCountWF constant.refs
  refsEntries : ∀ value, value ∈ constant.refs.toList → AddressWireWF value
  univsCount : ArrayCountWF constant.univs
  univsEntries : ∀ value, value ∈ constant.univs.toList →
    Ix.Compile.Verify.Codec.Ixon.Univ.WireWF value

def nonrecursiveConstantBytes (constant : Ixon.Constant) : ByteArray :=
  nonrecursiveInfoBytes constant.info ++
    tag0Bytes constant.sharing.size.toUInt64 ++
      listBytes Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode
        constant.sharing.toList ++
        tag0Bytes constant.refs.size.toUInt64 ++
          listBytes Address.hash constant.refs.toList ++
            tag0Bytes constant.univs.size.toUInt64 ++
              listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode
                constant.univs.toList

theorem putConstant_writes_nonrecursive (constant : Ixon.Constant)
    (h : NonrecursiveConstantWireWF constant) :
    Writes (Ixon.putConstant constant) (nonrecursiveConstantBytes constant) := by
  have hwrite :=
    (putConstantInfo_writes_nonrecursive constant.info h.info).bind
      ((putTag0_writes constant.sharing.size.toUInt64).bind
        ((putExprArray_writes constant.sharing h.sharingEntries).bind
          ((putTag0_writes constant.refs.size.toUInt64).bind
            ((putAddressArray_writes constant.refs h.refsEntries).bind
              ((putTag0_writes constant.univs.size.toUInt64).bind
                (putUnivArray_writes constant.univs h.univsEntries))))))
  simpa [Ixon.putConstant, nonrecursiveConstantBytes,
    ByteArray.append_assoc] using hwrite

theorem getConstant_reads_nonrecursive (constant : Ixon.Constant)
    (h : NonrecursiveConstantWireWF constant) :
    Reads Ixon.getConstant (nonrecursiveConstantBytes constant) constant := by
  have hinfo := getConstantInfo_reads_nonrecursive constant.info h.info
  have htail := getConstantAfterInfo_reads_core constant.info
    constant.sharing constant.refs constant.univs h.sharingCount
    h.sharingEntries h.refsCount h.refsEntries h.univsCount h.univsEntries
  have hall := Reads.bind (next := getConstantAfterInfo) hinfo htail
  rw [getConstant_eq]
  simpa [nonrecursiveConstantBytes, ByteArray.append_assoc] using hall

theorem deConstant_serConstant_nonrecursive (constant : Ixon.Constant)
    (h : NonrecursiveConstantWireWF constant) :
    Ixon.deConstant (Ixon.serConstant constant) = .ok constant := by
  unfold Ixon.serConstant
  rw [(putConstant_writes_nonrecursive constant h).runPut]
  unfold Ixon.deConstant Ixon.runGet
  have hread := getConstant_reads_nonrecursive constant h
    ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getConstant
    { bytes := nonrecursiveConstantBytes constant } = _ at hread
  rw [hread]

end Ix.Compile.Verify.Codec.Ixon.NonrecursiveConstant

namespace Ix.Compile.Verify

abbrev NonrecursiveConstantInfoWireWF : Ixon.ConstantInfo → Prop :=
  Codec.Ixon.NonrecursiveConstant.NonrecursiveInfoWireWF

abbrev NonrecursiveConstantWireWF : Ixon.Constant → Prop :=
  Codec.Ixon.NonrecursiveConstant.NonrecursiveConstantWireWF

theorem definitionNonrecursiveConstantInfoWireWF
    (definition : Ixon.Definition)
    (htyp : ExprWireWF definition.typ)
    (hvalue : ExprWireWF definition.value) :
    NonrecursiveConstantInfoWireWF (.defn definition) :=
  .defn htyp hvalue

theorem axiomNonrecursiveConstantInfoWireWF (axiomInfo : Ixon.Axiom)
    (htyp : ExprWireWF axiomInfo.typ) :
    NonrecursiveConstantInfoWireWF (.axio axiomInfo) :=
  .axio htyp

theorem quotientConstantInfoWireWF (quotient : Ixon.Quotient)
    (htyp : ExprWireWF quotient.typ) :
    NonrecursiveConstantInfoWireWF (.quot quotient) :=
  .quot htyp

theorem constructorProjConstantInfoWireWF
    (projection : Ixon.ConstructorProj)
    (hblock : ConstantAddressWireWF projection.block) :
    NonrecursiveConstantInfoWireWF (.cPrj projection) :=
  .cPrj hblock

theorem recursorProjConstantInfoWireWF (projection : Ixon.RecursorProj)
    (hblock : ConstantAddressWireWF projection.block) :
    NonrecursiveConstantInfoWireWF (.rPrj projection) :=
  .rPrj hblock

theorem inductiveProjConstantInfoWireWF (projection : Ixon.InductiveProj)
    (hblock : ConstantAddressWireWF projection.block) :
    NonrecursiveConstantInfoWireWF (.iPrj projection) :=
  .iPrj hblock

theorem definitionProjConstantInfoWireWF (projection : Ixon.DefinitionProj)
    (hblock : ConstantAddressWireWF projection.block) :
    NonrecursiveConstantInfoWireWF (.dPrj projection) :=
  .dPrj hblock

/-- Production top-level round trip for definitions, axioms, quotients, and
    all projection records with arbitrary wire-representable side tables. -/
theorem deConstant_serConstant_nonrecursive (constant : Ixon.Constant)
    (h : NonrecursiveConstantWireWF constant) :
    Ixon.deConstant (Ixon.serConstant constant) = .ok constant :=
  Codec.Ixon.NonrecursiveConstant.deConstant_serConstant_nonrecursive
    constant h

end Ix.Compile.Verify
