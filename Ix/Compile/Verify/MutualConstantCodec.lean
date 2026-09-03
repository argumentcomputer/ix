import Ix.Compile.Verify.RecursorConstantCodec

/-!
# Proof-visible mutual constant codec

This final constant-codec slice verifies constructors, inductive declarations,
the three `MutConst` member tags, and the counted `.muts` block.  Together with
the preceding standalone codecs, `ConstantInfoWireWF` now covers every
production variant.  The top-level theorem composes that complete payload
domain with arbitrary well-formed sharing, reference, and universe tables.
-/

namespace Ix.Compile.Verify.Codec.Ixon.MutualConstant

open Ix
open Ix.Compile.Verify.Codec
open Ix.Compile.Verify.Codec.Ixon.Constant
open Ix.Compile.Verify.Codec.Ixon.ConstantTables
open Ix.Compile.Verify.Codec.Ixon.NonrecursiveConstant
open Ix.Compile.Verify.Codec.Ixon.RecursorConstant

def constructorBytes (constructor : Ixon.Constructor) : ByteArray :=
  [if constructor.isUnsafe then 1 else 0].toByteArray ++
    tag0Bytes constructor.lvls ++ tag0Bytes constructor.cidx ++
      tag0Bytes constructor.params ++ tag0Bytes constructor.fields ++
        Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode constructor.typ

def ConstructorWireWF (constructor : Ixon.Constructor) : Prop :=
  Ixon.Expr.wireWF constructor.typ

theorem putConstructor_writes (constructor : Ixon.Constructor)
    (h : ConstructorWireWF constructor) :
    Writes (Ixon.putConstructor constructor) (constructorBytes constructor) := by
  have hwrite :=
    (putU8_writes (if constructor.isUnsafe then 1 else 0)).bind
      ((putTag0_writes constructor.lvls).bind
        ((putTag0_writes constructor.cidx).bind
          ((putTag0_writes constructor.params).bind
            ((putTag0_writes constructor.fields).bind
              (Ix.Compile.Verify.Codec.Ixon.Expr.putExpr_writes_spine
                constructor.typ h)))))
  simpa [Ixon.putConstructor, constructorBytes,
    ByteArray.append_assoc] using hwrite

theorem getConstructor_reads (constructor : Ixon.Constructor)
    (h : ConstructorWireWF constructor) :
    Reads Ixon.getConstructor (constructorBytes constructor) constructor := by
  have hbool := getU8_reads (if constructor.isUnsafe then 1 else 0)
  have hdecode :
      (((if constructor.isUnsafe then 1 else 0) : UInt8) != 0) =
        constructor.isUnsafe := by
    cases constructor.isUnsafe <;> decide
  have hlvls := getTag0_reads constructor.lvls
  have hcidx := getTag0_reads constructor.cidx
  have hparams := getTag0_reads constructor.params
  have hfields := getTag0_reads constructor.fields
  have htyp := Ix.Compile.Verify.Codec.Ixon.Expr.getExpr_reads_spine
    constructor.typ h
  have hreturn := Reads.pure constructor
  have hafterTyp := Reads.bind
    (next := fun typ : Ixon.Expr =>
      (pure ({ constructor with typ } : Ixon.Constructor) :
        Ixon.GetM Ixon.Constructor))
    htyp hreturn
  have hafterFields := Reads.bind
    (next := fun fields : Ixon.Tag0 => do
      let typ ← Ixon.getExpr
      return ({ constructor with fields := fields.size, typ } :
        Ixon.Constructor))
    hfields hafterTyp
  have hafterParams := Reads.bind
    (next := fun params : Ixon.Tag0 => do
      let fields := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      return ({ constructor with params := params.size, fields, typ } :
        Ixon.Constructor))
    hparams hafterFields
  have hafterCidx := Reads.bind
    (next := fun cidx : Ixon.Tag0 => do
      let params := (← Ixon.getTag0).size
      let fields := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      return ({ constructor with cidx := cidx.size, params, fields, typ } :
        Ixon.Constructor))
    hcidx hafterParams
  have hafterLvls := Reads.bind
    (next := fun lvls : Ixon.Tag0 => do
      let cidx := (← Ixon.getTag0).size
      let params := (← Ixon.getTag0).size
      let fields := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      return (⟨constructor.isUnsafe, lvls.size, cidx, params, fields, typ⟩ :
        Ixon.Constructor))
    hlvls hafterCidx
  have hall := Reads.bind
    (next := fun encodedUnsafe : UInt8 => do
      let isUnsafe := encodedUnsafe != 0
      let lvls := (← Ixon.getTag0).size
      let cidx := (← Ixon.getTag0).size
      let params := (← Ixon.getTag0).size
      let fields := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      return (⟨isUnsafe, lvls, cidx, params, fields, typ⟩ :
        Ixon.Constructor))
    hbool (by simpa [hdecode] using hafterLvls)
  simpa [Ixon.getConstructor, constructorBytes,
    ByteArray.append_assoc] using hall

theorem putConstructorArray_writes (constructors : Array Ixon.Constructor)
    (h : ∀ constructor, constructor ∈ constructors.toList →
      ConstructorWireWF constructor) :
    Writes (do for constructor in constructors do Ixon.putConstructor constructor)
      (listBytes constructorBytes constructors.toList) := by
  exact arrayPut_writes Ixon.putConstructor constructorBytes
    ConstructorWireWF constructors h putConstructor_writes

theorem getConstructorArray_reads (constructors : Array Ixon.Constructor)
    (h : ∀ constructor, constructor ∈ constructors.toList →
      ConstructorWireWF constructor) :
    Reads (getMany Ixon.getConstructor constructors.size)
      (listBytes constructorBytes constructors.toList) constructors := by
  simpa using getMany_reads Ixon.getConstructor constructorBytes
    constructors.toList
    (fun constructor hmem => getConstructor_reads constructor
      (h constructor hmem))

def inductiveFlags (inductiveInfo : Ixon.Inductive) : UInt8 :=
  Ixon.packBools [inductiveInfo.isUnsafe]

theorem unpackInductiveFlags_pack (isUnsafe : Bool) :
    let bools := Ixon.unpackBools 1 (Ixon.packBools [isUnsafe])
    bools[0]! = isUnsafe := by
  cases isUnsafe <;> decide

def inductiveBytes (inductiveInfo : Ixon.Inductive) : ByteArray :=
  [inductiveFlags inductiveInfo].toByteArray ++
    tag0Bytes inductiveInfo.lvls ++ tag0Bytes inductiveInfo.params ++
      tag0Bytes inductiveInfo.indices ++
        Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode inductiveInfo.typ ++
          tag0Bytes inductiveInfo.ctors.size.toUInt64 ++
            listBytes constructorBytes inductiveInfo.ctors.toList

structure InductiveWireWF (inductiveInfo : Ixon.Inductive) : Prop where
  typ : Ixon.Expr.wireWF inductiveInfo.typ
  constructorsCount : ArrayCountWF inductiveInfo.ctors
  constructors : ∀ constructor, constructor ∈ inductiveInfo.ctors.toList →
    ConstructorWireWF constructor

theorem putInductive_writes (inductiveInfo : Ixon.Inductive)
    (h : InductiveWireWF inductiveInfo) :
    Writes (Ixon.putInductive inductiveInfo) (inductiveBytes inductiveInfo) := by
  have hwrite := (putU8_writes (inductiveFlags inductiveInfo)).bind
    ((putTag0_writes inductiveInfo.lvls).bind
      ((putTag0_writes inductiveInfo.params).bind
        ((putTag0_writes inductiveInfo.indices).bind
          ((Ix.Compile.Verify.Codec.Ixon.Expr.putExpr_writes_spine
            inductiveInfo.typ h.typ).bind
            ((putTag0_writes inductiveInfo.ctors.size.toUInt64).bind
              (putConstructorArray_writes inductiveInfo.ctors
                h.constructors))))))
  simpa [Ixon.putInductive, inductiveFlags, inductiveBytes,
    ByteArray.append_assoc] using hwrite

def getInductiveConstructors (isUnsafe : Bool) (lvls params indices : UInt64)
    (typ : Ixon.Expr) : Ixon.GetM Ixon.Inductive := do
  let count := (← Ixon.getTag0).size.toNat
  let mut constructors : Array Ixon.Constructor := #[]
  for _ in [0:count] do
    constructors := constructors.push (← Ixon.getConstructor)
  return ⟨isUnsafe, lvls, params, indices, typ, constructors⟩

def getInductiveAfterFlags (isUnsafe : Bool) : Ixon.GetM Ixon.Inductive := do
  let lvls := (← Ixon.getTag0).size
  let params := (← Ixon.getTag0).size
  let indices := (← Ixon.getTag0).size
  let typ ← Ixon.getExpr
  getInductiveConstructors isUnsafe lvls params indices typ

def getInductiveFromFlags (flags : UInt8) : Ixon.GetM Ixon.Inductive :=
  let bools := Ixon.unpackBools 1 flags
  getInductiveAfterFlags bools[0]!

theorem getInductive_eq :
    Ixon.getInductive = (Ixon.getU8 >>= getInductiveFromFlags) := by
  rfl

theorem getInductiveConstructors_reads (inductiveInfo : Ixon.Inductive)
    (h : InductiveWireWF inductiveInfo) :
    Reads
      (getInductiveConstructors inductiveInfo.isUnsafe inductiveInfo.lvls
        inductiveInfo.params inductiveInfo.indices inductiveInfo.typ)
      (tag0Bytes inductiveInfo.ctors.size.toUInt64 ++
        listBytes constructorBytes inductiveInfo.ctors.toList)
      inductiveInfo := by
  have htag := getTag0_reads inductiveInfo.ctors.size.toUInt64
  have hdecode := arrayCount_decode inductiveInfo.ctors h.constructorsCount
  have hconstructors :=
    getConstructorArray_reads inductiveInfo.ctors h.constructors
  have hreturn := Reads.pure inductiveInfo
  have hafterConstructors := Reads.bind
    (next := fun constructors : Array Ixon.Constructor =>
      (pure ({ inductiveInfo with ctors := constructors } : Ixon.Inductive) :
        Ixon.GetM Ixon.Inductive))
    hconstructors hreturn
  have htail : Reads
      (do
        let mut constructors : Array Ixon.Constructor := #[]
        for _ in [0:inductiveInfo.ctors.size.toUInt64.toNat] do
          constructors := constructors.push (← Ixon.getConstructor)
        return ({ inductiveInfo with ctors := constructors } : Ixon.Inductive))
      (listBytes constructorBytes inductiveInfo.ctors.toList)
      inductiveInfo := by
    simpa [getMany, hdecode] using hafterConstructors
  have hall := Reads.bind
    (next := fun count : Ixon.Tag0 => do
      let mut constructors : Array Ixon.Constructor := #[]
      for _ in [0:count.size.toNat] do
        constructors := constructors.push (← Ixon.getConstructor)
      return ({ inductiveInfo with ctors := constructors } : Ixon.Inductive))
    htag htail
  simpa [getInductiveConstructors] using hall

theorem getInductiveAfterFlags_reads (inductiveInfo : Ixon.Inductive)
    (h : InductiveWireWF inductiveInfo) :
    Reads (getInductiveAfterFlags inductiveInfo.isUnsafe)
      (tag0Bytes inductiveInfo.lvls ++ tag0Bytes inductiveInfo.params ++
        tag0Bytes inductiveInfo.indices ++
          Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode inductiveInfo.typ ++
            tag0Bytes inductiveInfo.ctors.size.toUInt64 ++
              listBytes constructorBytes inductiveInfo.ctors.toList)
      inductiveInfo := by
  have hlvls := getTag0_reads inductiveInfo.lvls
  have hparams := getTag0_reads inductiveInfo.params
  have hindices := getTag0_reads inductiveInfo.indices
  have htyp := Ix.Compile.Verify.Codec.Ixon.Expr.getExpr_reads_spine
    inductiveInfo.typ h.typ
  have hconstructors := getInductiveConstructors_reads inductiveInfo h
  have hafterTyp := Reads.bind
    (next := fun typ : Ixon.Expr =>
      getInductiveConstructors inductiveInfo.isUnsafe inductiveInfo.lvls
        inductiveInfo.params inductiveInfo.indices typ)
    htyp hconstructors
  have hafterIndices := Reads.bind
    (next := fun indices : Ixon.Tag0 => do
      let typ ← Ixon.getExpr
      getInductiveConstructors inductiveInfo.isUnsafe inductiveInfo.lvls
        inductiveInfo.params indices.size typ)
    hindices hafterTyp
  have hafterParams := Reads.bind
    (next := fun params : Ixon.Tag0 => do
      let indices := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      getInductiveConstructors inductiveInfo.isUnsafe inductiveInfo.lvls
        params.size indices typ)
    hparams hafterIndices
  have hall := Reads.bind
    (next := fun lvls : Ixon.Tag0 => do
      let params := (← Ixon.getTag0).size
      let indices := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      getInductiveConstructors inductiveInfo.isUnsafe lvls.size params indices
        typ)
    hlvls hafterParams
  simpa [getInductiveAfterFlags, ByteArray.append_assoc] using hall

theorem getInductive_reads (inductiveInfo : Ixon.Inductive)
    (h : InductiveWireWF inductiveInfo) :
    Reads Ixon.getInductive (inductiveBytes inductiveInfo) inductiveInfo := by
  have hflags := getU8_reads (inductiveFlags inductiveInfo)
  have hdecode := unpackInductiveFlags_pack inductiveInfo.isUnsafe
  have htail := getInductiveAfterFlags_reads inductiveInfo h
  have htail' : Reads (getInductiveFromFlags (inductiveFlags inductiveInfo))
      (tag0Bytes inductiveInfo.lvls ++ tag0Bytes inductiveInfo.params ++
        tag0Bytes inductiveInfo.indices ++
          Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode inductiveInfo.typ ++
            tag0Bytes inductiveInfo.ctors.size.toUInt64 ++
              listBytes constructorBytes inductiveInfo.ctors.toList)
      inductiveInfo := by
    simpa [getInductiveFromFlags, inductiveFlags, hdecode] using htail
  have hall := Reads.bind (next := getInductiveFromFlags) hflags htail'
  rw [getInductive_eq]
  simpa [inductiveBytes, ByteArray.append_assoc] using hall

inductive MutConstWireWF : Ixon.MutConst → Prop where
  | defn {definition : Ixon.Definition} :
      Ixon.Expr.wireWF definition.typ →
      Ixon.Expr.wireWF definition.value →
      MutConstWireWF (.defn definition)
  | indc {inductiveInfo : Ixon.Inductive} :
      InductiveWireWF inductiveInfo → MutConstWireWF (.indc inductiveInfo)
  | recr {recursor : Ixon.Recursor} :
      RecursorWireWF recursor → MutConstWireWF (.recr recursor)

def mutConstBytes : Ixon.MutConst → ByteArray
  | .defn definition => [0].toByteArray ++ definitionBytes definition
  | .indc inductiveInfo => [1].toByteArray ++ inductiveBytes inductiveInfo
  | .recr recursor => [2].toByteArray ++ recursorBytes recursor

theorem putMutConst_writes (member : Ixon.MutConst)
    (h : MutConstWireWF member) :
    Writes (Ixon.putMutConst member) (mutConstBytes member) := by
  cases h with
  | defn htyp hvalue =>
    simpa [Ixon.putMutConst, mutConstBytes, seqRight_eq_bind] using
      (putU8_writes 0).bind (putDefinition_writes _ htyp hvalue)
  | indc hinductive =>
    simpa [Ixon.putMutConst, mutConstBytes, seqRight_eq_bind] using
      (putU8_writes 1).bind (putInductive_writes _ hinductive)
  | recr hrecursor =>
    simpa [Ixon.putMutConst, mutConstBytes, seqRight_eq_bind] using
      (putU8_writes 2).bind (putRecursor_writes _ hrecursor)

def getMutConstFromTag (tag : UInt8) : Ixon.GetM Ixon.MutConst :=
  match tag with
  | 0 => Ixon.MutConst.defn <$> Ixon.getDefinition
  | 1 => Ixon.MutConst.indc <$> Ixon.getInductive
  | 2 => Ixon.MutConst.recr <$> Ixon.getRecursor
  | tag => throw s!"getMutConst: invalid tag {tag}"

theorem getMutConst_eq :
    Ixon.getMutConst = (Ixon.getU8 >>= getMutConstFromTag) := by
  rfl

theorem getMutConst_reads_variant (tag : UInt8) (getm : Ixon.GetM α)
    (bytes : ByteArray) (value : α) (wrap : α → Ixon.MutConst)
    (hdispatch : getMutConstFromTag tag = wrap <$> getm)
    (hread : Reads getm bytes value) :
    Reads Ixon.getMutConst ([tag].toByteArray ++ bytes) (wrap value) := by
  have htag := getU8_reads tag
  have htail : Reads (getMutConstFromTag tag) bytes (wrap value) := by
    rw [hdispatch]
    exact reads_map wrap hread
  have hall := Reads.bind (next := getMutConstFromTag) htag htail
  rw [getMutConst_eq]
  exact hall

theorem getMutConst_reads (member : Ixon.MutConst)
    (h : MutConstWireWF member) :
    Reads Ixon.getMutConst (mutConstBytes member) member := by
  cases h with
  | @defn definition htyp hvalue =>
    apply getMutConst_reads_variant 0 Ixon.getDefinition
      (definitionBytes definition) definition Ixon.MutConst.defn
    · rfl
    · exact getDefinition_reads definition htyp hvalue
  | @indc inductiveInfo hinductive =>
    apply getMutConst_reads_variant 1 Ixon.getInductive
      (inductiveBytes inductiveInfo) inductiveInfo Ixon.MutConst.indc
    · rfl
    · exact getInductive_reads inductiveInfo hinductive
  | @recr recursor hrecursor =>
    apply getMutConst_reads_variant 2 Ixon.getRecursor
      (recursorBytes recursor) recursor Ixon.MutConst.recr
    · rfl
    · exact getRecursor_reads recursor hrecursor

theorem putMutConstArray_writes (members : Array Ixon.MutConst)
    (h : ∀ member, member ∈ members.toList → MutConstWireWF member) :
    Writes (do for member in members do Ixon.putMutConst member)
      (listBytes mutConstBytes members.toList) := by
  exact arrayPut_writes Ixon.putMutConst mutConstBytes MutConstWireWF
    members h putMutConst_writes

theorem getMutConstArray_reads (members : Array Ixon.MutConst)
    (h : ∀ member, member ∈ members.toList → MutConstWireWF member) :
    Reads (getMany Ixon.getMutConst members.size)
      (listBytes mutConstBytes members.toList) members := by
  simpa using getMany_reads Ixon.getMutConst mutConstBytes members.toList
    (fun member hmem => getMutConst_reads member (h member hmem))

inductive ConstantInfoWireWF : Ixon.ConstantInfo → Prop where
  | standalone {info : Ixon.ConstantInfo} :
      StandaloneInfoWireWF info → ConstantInfoWireWF info
  | muts {members : Array Ixon.MutConst} :
      ArrayCountWF members →
      (∀ member, member ∈ members.toList → MutConstWireWF member) →
      ConstantInfoWireWF (.muts members)

def constantInfoBytes : Ixon.ConstantInfo → ByteArray
  | .muts members =>
      tag4Bytes Ixon.Constant.FLAG_MUTS members.size.toUInt64 ++
        listBytes mutConstBytes members.toList
  | info => standaloneInfoBytes info

theorem putConstantInfo_writes (info : Ixon.ConstantInfo)
    (h : ConstantInfoWireWF info) :
    Writes (Ixon.putConstantInfo info) (constantInfoBytes info) := by
  cases h with
  | @standalone info hbase =>
    have hwrite := putConstantInfo_writes_standalone info hbase
    cases hbase with
    | nonrecursive hnonrecursive =>
      cases hnonrecursive <;>
        simpa [constantInfoBytes, standaloneInfoBytes,
          nonrecursiveInfoBytes] using hwrite
    | recr hrecursor =>
      simpa [constantInfoBytes, standaloneInfoBytes] using hwrite
  | @muts members hcount hmembers =>
    have hwrite :=
      (putTag4_writes Ixon.Constant.FLAG_MUTS members.size.toUInt64).bind
        (putMutConstArray_writes members hmembers)
    simpa [Ixon.putConstantInfo, constantInfoBytes,
      ByteArray.append_assoc] using hwrite

theorem getConstantInfo_reads (info : Ixon.ConstantInfo)
    (h : ConstantInfoWireWF info) :
    Reads Ixon.getConstantInfo (constantInfoBytes info) info := by
  cases h with
  | @standalone info hbase =>
    have hread := getConstantInfo_reads_standalone info hbase
    cases hbase with
    | nonrecursive hnonrecursive =>
      cases hnonrecursive <;>
        simpa [constantInfoBytes, standaloneInfoBytes,
          nonrecursiveInfoBytes] using hread
    | recr hrecursor =>
      simpa [constantInfoBytes, standaloneInfoBytes] using hread
  | @muts members hcount hmembers =>
    have htag := getTag4_reads Ixon.Constant.FLAG_MUTS
      members.size.toUInt64 (by decide)
    have hdecode := arrayCount_decode members hcount
    have hmembersRead := getMutConstArray_reads members hmembers
    have hreturn := Reads.pure (Ixon.ConstantInfo.muts members)
    have hafterMembers := Reads.bind
      (next := fun decoded : Array Ixon.MutConst =>
        (pure (Ixon.ConstantInfo.muts decoded) : Ixon.GetM Ixon.ConstantInfo))
      hmembersRead hreturn
    have htail : Reads
        (getInfoFromTag
          ⟨Ixon.Constant.FLAG_MUTS, members.size.toUInt64⟩)
        (listBytes mutConstBytes members.toList)
        (.muts members) := by
      simpa [getInfoFromTag, Ixon.Constant.FLAG_MUTS, Ixon.Constant.FLAG,
        getMany, hdecode] using hafterMembers
    have hall := Reads.bind (next := getInfoFromTag) htag htail
    rw [getConstantInfo_eq]
    simpa [constantInfoBytes] using hall

structure ConstantWireWF (constant : Ixon.Constant) : Prop where
  info : ConstantInfoWireWF constant.info
  sharingCount : ArrayCountWF constant.sharing
  sharingEntries : ∀ value, value ∈ constant.sharing.toList →
    Ixon.Expr.wireWF value
  refsCount : ArrayCountWF constant.refs
  refsEntries : ∀ value, value ∈ constant.refs.toList → AddressWireWF value
  univsCount : ArrayCountWF constant.univs
  univsEntries : ∀ value, value ∈ constant.univs.toList →
    Ix.Compile.Verify.Codec.Ixon.Univ.WireWF value

theorem recursorWireWF_of_catalog (recursor : Ixon.Recursor)
    (h : recursor.wireWF) : RecursorWireWF recursor := by
  refine {
    typ := h.1
    rulesCount := h.2.1
    rules := ?_
  }
  intro rule hmem
  exact h.2.2 rule (by simpa using hmem)

theorem constructorWireWF_of_catalog (constructor : Ixon.Constructor)
    (h : constructor.wireWF) : ConstructorWireWF constructor :=
  h

theorem inductiveWireWF_of_catalog (inductiveInfo : Ixon.Inductive)
    (h : inductiveInfo.wireWF) : InductiveWireWF inductiveInfo := by
  refine {
    typ := h.1
    constructorsCount := h.2.1
    constructors := ?_
  }
  intro constructor hmem
  exact constructorWireWF_of_catalog constructor
    (h.2.2 constructor (by simpa using hmem))

theorem mutConstWireWF_of_catalog (member : Ixon.MutConst)
    (h : member.wireWF) : MutConstWireWF member := by
  cases member with
  | defn definition =>
    exact .defn h.1 h.2
  | indc inductiveInfo =>
    exact .indc (inductiveWireWF_of_catalog inductiveInfo h)
  | recr recursor =>
    exact .recr (recursorWireWF_of_catalog recursor h)

theorem constantInfoWireWF_of_catalog (info : Ixon.ConstantInfo)
    (h : info.wireWF) : ConstantInfoWireWF info := by
  cases info with
  | defn definition =>
    exact .standalone (.nonrecursive (.defn h.1 h.2))
  | recr recursor =>
    exact .standalone (.recr (recursorWireWF_of_catalog recursor h))
  | axio axiomInfo =>
    exact .standalone (.nonrecursive (.axio h))
  | quot quotient =>
    exact .standalone (.nonrecursive (.quot h))
  | cPrj projection =>
    exact .standalone (.nonrecursive (.cPrj h))
  | rPrj projection =>
    exact .standalone (.nonrecursive (.rPrj h))
  | iPrj projection =>
    exact .standalone (.nonrecursive (.iPrj h))
  | dPrj projection =>
    exact .standalone (.nonrecursive (.dPrj h))
  | muts members =>
    refine .muts h.1 ?_
    intro member hmem
    exact mutConstWireWF_of_catalog member
      (h.2 member (by simpa using hmem))

/-- The catalog's public wire invariant is exactly strong enough to construct
the proof object consumed by the compositional codec development. -/
theorem constantWireWF_of_catalog (constant : Ixon.Constant)
    (h : constant.wireWF) : ConstantWireWF constant := by
  rcases h with
    ⟨hinfo, hsharingCount, hsharing, hrefsCount, hrefs,
      hunivsCount, hunivs⟩
  refine {
    info := constantInfoWireWF_of_catalog constant.info hinfo
    sharingCount := hsharingCount
    sharingEntries := ?_
    refsCount := hrefsCount
    refsEntries := ?_
    univsCount := hunivsCount
    univsEntries := ?_
  }
  · intro value hmem
    exact hsharing value (by simpa using hmem)
  · intro value hmem
    exact hrefs value (by simpa [AddressWireWF] using hmem)
  · intro value hmem
    exact hunivs value (by simpa using hmem)

theorem recursorWireWF_to_catalog {recursor : Ixon.Recursor}
    (h : RecursorWireWF recursor) : recursor.wireWF := by
  refine ⟨h.typ, h.rulesCount, ?_⟩
  intro rule hmem
  exact h.rules rule (by simpa using hmem)

theorem inductiveWireWF_to_catalog {inductiveInfo : Ixon.Inductive}
    (h : InductiveWireWF inductiveInfo) : inductiveInfo.wireWF := by
  refine ⟨h.typ, h.constructorsCount, ?_⟩
  intro constructor hmem
  exact h.constructors constructor (by simpa using hmem)

theorem mutConstWireWF_to_catalog {member : Ixon.MutConst}
    (h : MutConstWireWF member) : member.wireWF := by
  cases h with
  | defn htyp hvalue => exact ⟨htyp, hvalue⟩
  | indc hinductive => exact inductiveWireWF_to_catalog hinductive
  | recr hrecursor => exact recursorWireWF_to_catalog hrecursor

theorem constantInfoWireWF_to_catalog {info : Ixon.ConstantInfo}
    (h : ConstantInfoWireWF info) : info.wireWF := by
  cases h with
  | standalone hstandalone =>
    cases hstandalone with
    | nonrecursive hnonrecursive =>
      cases hnonrecursive with
      | defn htyp hvalue => exact ⟨htyp, hvalue⟩
      | axio htyp => exact htyp
      | quot htyp => exact htyp
      | cPrj hblock => exact hblock
      | rPrj hblock => exact hblock
      | iPrj hblock => exact hblock
      | dPrj hblock => exact hblock
    | recr hrecursor => exact recursorWireWF_to_catalog hrecursor
  | muts hcount hmembers =>
    refine ⟨hcount, ?_⟩
    intro member hmem
    exact mutConstWireWF_to_catalog
      (hmembers member (by simpa using hmem))

theorem constantWireWF_to_catalog {constant : Ixon.Constant}
    (h : ConstantWireWF constant) : constant.wireWF := by
  refine ⟨constantInfoWireWF_to_catalog h.info, h.sharingCount, ?_,
    h.refsCount, ?_, h.univsCount, ?_⟩
  · intro value hmem
    exact h.sharingEntries value (by simpa using hmem)
  · intro value hmem
    exact h.refsEntries value (by simpa [AddressWireWF] using hmem)
  · intro value hmem
    exact h.univsEntries value (by simpa using hmem)

theorem constantWireWF_iff_catalog (constant : Ixon.Constant) :
    ConstantWireWF constant ↔ constant.wireWF :=
  ⟨constantWireWF_to_catalog, constantWireWF_of_catalog constant⟩

def constantBytes (constant : Ixon.Constant) : ByteArray :=
  constantInfoBytes constant.info ++
    tag0Bytes constant.sharing.size.toUInt64 ++
      listBytes Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode
        constant.sharing.toList ++
        tag0Bytes constant.refs.size.toUInt64 ++
          listBytes Address.hash constant.refs.toList ++
            tag0Bytes constant.univs.size.toUInt64 ++
              listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode
                constant.univs.toList

theorem putConstant_writes (constant : Ixon.Constant)
    (h : ConstantWireWF constant) :
    Writes (Ixon.putConstant constant) (constantBytes constant) := by
  have hwrite := (putConstantInfo_writes constant.info h.info).bind
    ((putTag0_writes constant.sharing.size.toUInt64).bind
      ((putExprArray_writes constant.sharing h.sharingEntries).bind
        ((putTag0_writes constant.refs.size.toUInt64).bind
          ((putAddressArray_writes constant.refs h.refsEntries).bind
            ((putTag0_writes constant.univs.size.toUInt64).bind
              (putUnivArray_writes constant.univs h.univsEntries))))))
  simpa [Ixon.putConstant, constantBytes, ByteArray.append_assoc] using hwrite

theorem getConstant_reads (constant : Ixon.Constant)
    (h : ConstantWireWF constant) :
    Reads Ixon.getConstant (constantBytes constant) constant := by
  have hinfo := getConstantInfo_reads constant.info h.info
  have htail := getConstantAfterInfo_reads_core constant.info
    constant.sharing constant.refs constant.univs h.sharingCount
    h.sharingEntries h.refsCount h.refsEntries h.univsCount h.univsEntries
  have hall := Reads.bind (next := getConstantAfterInfo) hinfo htail
  rw [getConstant_eq]
  simpa [constantBytes, ByteArray.append_assoc] using hall

theorem deConstant_serConstant (constant : Ixon.Constant)
    (h : ConstantWireWF constant) :
    Ixon.deConstant (Ixon.serConstant constant) = .ok constant := by
  unfold Ixon.serConstant
  rw [(putConstant_writes constant h).runPut]
  unfold Ixon.deConstant Ixon.runGet
  have hread := getConstant_reads constant h ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getConstant { bytes := constantBytes constant } = _
    at hread
  rw [hread]

end Ix.Compile.Verify.Codec.Ixon.MutualConstant

namespace Ix.Compile.Verify

abbrev ConstructorWireWF : Ixon.Constructor → Prop :=
  Codec.Ixon.MutualConstant.ConstructorWireWF

abbrev InductiveWireWF : Ixon.Inductive → Prop :=
  Codec.Ixon.MutualConstant.InductiveWireWF

abbrev MutConstWireWF : Ixon.MutConst → Prop :=
  Codec.Ixon.MutualConstant.MutConstWireWF

abbrev ConstantInfoWireWF : Ixon.ConstantInfo → Prop :=
  Codec.Ixon.MutualConstant.ConstantInfoWireWF

abbrev ConstantWireWF : Ixon.Constant → Prop := Ixon.Constant.wireWF

theorem definitionMutConstWireWF (definition : Ixon.Definition)
    (htyp : ExprWireWF definition.typ)
    (hvalue : ExprWireWF definition.value) :
    MutConstWireWF (.defn definition) :=
  .defn htyp hvalue

theorem inductiveMutConstWireWF (inductiveInfo : Ixon.Inductive)
    (h : InductiveWireWF inductiveInfo) :
    MutConstWireWF (.indc inductiveInfo) :=
  .indc h

theorem recursorMutConstWireWF (recursor : Ixon.Recursor)
    (h : RecursorWireWF recursor) :
    MutConstWireWF (.recr recursor) :=
  .recr h

theorem constantInfoWireWF_of_standalone {info : Ixon.ConstantInfo}
    (h : StandaloneConstantInfoWireWF info) :
    ConstantInfoWireWF info :=
  .standalone h

theorem mutualConstantInfoWireWF (members : Array Ixon.MutConst)
    (hcount : ConstantArrayCountWF members)
    (hmembers : ∀ member, member ∈ members.toList → MutConstWireWF member) :
    ConstantInfoWireWF (.muts members) :=
  .muts hcount hmembers

/-- The public catalog invariant and the codec's compositional proof domain
    describe the same constants. -/
theorem constantWireWF_iff_codec (constant : Ixon.Constant) :
    ConstantWireWF constant ↔
      Codec.Ixon.MutualConstant.ConstantWireWF constant :=
  (Codec.Ixon.MutualConstant.constantWireWF_iff_catalog constant).symm

/-- Production serializer/decoder round trip for every `ConstantInfo` variant,
    arbitrary canonical expression spines, and arbitrary wire-representable
    top-level side tables. -/
theorem deConstant_serConstant (constant : Ixon.Constant)
    (h : ConstantWireWF constant) :
    Ixon.deConstant (Ixon.serConstant constant) = .ok constant :=
  Codec.Ixon.MutualConstant.deConstant_serConstant constant
    (Codec.Ixon.MutualConstant.constantWireWF_of_catalog constant h)

end Ix.Compile.Verify
