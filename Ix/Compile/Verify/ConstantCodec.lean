import Ix.Compile.Verify.ExprSpineCodec

/-!
# Proof-visible v2 core constant codec

This slice composes the verified arbitrary-spine expression codec through
production definition and axiom payloads, their `ConstantInfo` tags, and a
top-level `Constant` whose sharing, reference, and universe side tables are
empty.  The byte model is explicit at every layer, so the final theorem
relates the actual `serConstant` and `deConstant` entry points without an
assumed serialization law.
-/

namespace Ix.Compile.Verify.Codec.Ixon.Constant

open Ix

def definitionBytes (definition : Ixon.Definition) : ByteArray :=
  [Ixon.packDefKindSafety definition.kind definition.safety].toByteArray ++
    tag0Bytes definition.lvls ++
      Expr.spineWireEncode definition.typ ++ Expr.spineWireEncode definition.value

def axiomBytes (axiomInfo : Ixon.Axiom) : ByteArray :=
  [if axiomInfo.isUnsafe then 1 else 0].toByteArray ++
    tag0Bytes axiomInfo.lvls ++ Expr.spineWireEncode axiomInfo.typ

theorem unpackDefKindSafety_pack (kind : DefKind)
    (safety : DefinitionSafety) :
    Ixon.unpackDefKindSafety (Ixon.packDefKindSafety kind safety) =
      (kind, safety) := by
  cases kind <;> cases safety <;> decide

theorem putDefinition_writes (definition : Ixon.Definition)
    (htyp : Ixon.Expr.wireWF definition.typ)
    (hvalue : Ixon.Expr.wireWF definition.value) :
    Writes (Ixon.putDefinition definition) (definitionBytes definition) := by
  have hwrite :=
    (putU8_writes (Ixon.packDefKindSafety definition.kind definition.safety)).bind
      ((putTag0_writes definition.lvls).bind
        ((Expr.putExpr_writes_spine definition.typ htyp).bind
          (Expr.putExpr_writes_spine definition.value hvalue)))
  simpa [Ixon.putDefinition, definitionBytes, ByteArray.append_assoc] using
    hwrite

theorem putAxiom_writes (axiomInfo : Ixon.Axiom)
    (htyp : Ixon.Expr.wireWF axiomInfo.typ) :
    Writes (Ixon.putAxiom axiomInfo) (axiomBytes axiomInfo) := by
  have hwrite :=
    (putU8_writes (if axiomInfo.isUnsafe then 1 else 0)).bind
      ((putTag0_writes axiomInfo.lvls).bind
        (Expr.putExpr_writes_spine axiomInfo.typ htyp))
  simpa [Ixon.putAxiom, axiomBytes, ByteArray.append_assoc] using hwrite

theorem getDefinition_reads (definition : Ixon.Definition)
    (htyp : Ixon.Expr.wireWF definition.typ)
    (hvalue : Ixon.Expr.wireWF definition.value) :
    Reads Ixon.getDefinition (definitionBytes definition) definition := by
  have hkind :=
    getU8_reads (Ixon.packDefKindSafety definition.kind definition.safety)
  have hlvls := getTag0_reads definition.lvls
  have htypRead := Expr.getExpr_reads_spine definition.typ htyp
  have hvalueRead := Expr.getExpr_reads_spine definition.value hvalue
  have hreturn := Reads.pure definition
  have hafterValue := Reads.bind
    (next := fun value : Ixon.Expr =>
      (pure ({ definition with value } : Ixon.Definition) :
        Ixon.GetM Ixon.Definition))
    hvalueRead hreturn
  have hafterTyp := Reads.bind
    (next := fun typ : Ixon.Expr => do
      let value ← Ixon.getExpr
      return ({ definition with typ, value } : Ixon.Definition))
    htypRead hafterValue
  have hafterLvls := Reads.bind
    (next := fun lvls : Ixon.Tag0 => do
      let typ ← Ixon.getExpr
      let value ← Ixon.getExpr
      return ({ definition with lvls := lvls.size, typ, value } :
        Ixon.Definition))
    hlvls hafterTyp
  have hafterLvls' : Reads
      (match Ixon.unpackDefKindSafety
          (Ixon.packDefKindSafety definition.kind definition.safety) with
        | (kind, safety) => do
          let lvls := (← Ixon.getTag0).size
          let typ ← Ixon.getExpr
          let value ← Ixon.getExpr
          return (⟨kind, safety, lvls, typ, value⟩ : Ixon.Definition))
      (tag0Bytes definition.lvls ++ Expr.spineWireEncode definition.typ ++
        Expr.spineWireEncode definition.value)
      definition := by
    rw [unpackDefKindSafety_pack]
    simpa [ByteArray.append_assoc] using hafterLvls
  have hall := Reads.bind
    (next := fun packed : UInt8 => do
      let (kind, safety) := Ixon.unpackDefKindSafety packed
      let lvls := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      let value ← Ixon.getExpr
      return (⟨kind, safety, lvls, typ, value⟩ : Ixon.Definition))
    hkind hafterLvls'
  simpa [Ixon.getDefinition, definitionBytes, unpackDefKindSafety_pack,
    ByteArray.append_assoc] using hall

theorem getAxiom_reads (axiomInfo : Ixon.Axiom)
    (htyp : Ixon.Expr.wireWF axiomInfo.typ) :
    Reads Ixon.getAxiom (axiomBytes axiomInfo) axiomInfo := by
  have hbool := getU8_reads (if axiomInfo.isUnsafe then 1 else 0)
  have hlvls := getTag0_reads axiomInfo.lvls
  have htypRead := Expr.getExpr_reads_spine axiomInfo.typ htyp
  have hreturn := Reads.pure axiomInfo
  have hafterTyp := Reads.bind
    (next := fun typ : Ixon.Expr =>
      (pure ({ axiomInfo with typ } : Ixon.Axiom) : Ixon.GetM Ixon.Axiom))
    htypRead hreturn
  have hafterLvls := Reads.bind
    (next := fun lvls : Ixon.Tag0 => do
      let typ ← Ixon.getExpr
      return ({ axiomInfo with lvls := lvls.size, typ } : Ixon.Axiom))
    hlvls hafterTyp
  have hdecodeUnsafe :
      (((if axiomInfo.isUnsafe then 1 else 0) : UInt8) != 0) =
        axiomInfo.isUnsafe := by
    cases axiomInfo.isUnsafe <;> decide
  have hafterLvls' : Reads
      (do
        let lvls := (← Ixon.getTag0).size
        let typ ← Ixon.getExpr
        return (⟨(((if axiomInfo.isUnsafe then 1 else 0) : UInt8) != 0),
          lvls, typ⟩ : Ixon.Axiom))
      (tag0Bytes axiomInfo.lvls ++ Expr.spineWireEncode axiomInfo.typ)
      axiomInfo := by
    simp only [hdecodeUnsafe]
    simpa using hafterLvls
  have hall := Reads.bind
    (next := fun encodedUnsafe : UInt8 => do
      let isUnsafe := encodedUnsafe != 0
      let lvls := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      return (⟨isUnsafe, lvls, typ⟩ : Ixon.Axiom))
    hbool hafterLvls'
  simpa [Ixon.getAxiom, axiomBytes, ByteArray.append_assoc] using hall

theorem runGet_runPut_definition (definition : Ixon.Definition)
    (htyp : Ixon.Expr.wireWF definition.typ)
    (hvalue : Ixon.Expr.wireWF definition.value) :
    Ixon.runGet Ixon.getDefinition (Ixon.runPut (Ixon.putDefinition definition)) =
      .ok definition := by
  rw [(putDefinition_writes definition htyp hvalue).runPut]
  unfold Ixon.runGet
  have hread := getDefinition_reads definition htyp hvalue
    ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getDefinition { bytes := definitionBytes definition } = _
    at hread
  rw [hread]

theorem runGet_runPut_axiom (axiomInfo : Ixon.Axiom)
    (htyp : Ixon.Expr.wireWF axiomInfo.typ) :
    Ixon.runGet Ixon.getAxiom (Ixon.runPut (Ixon.putAxiom axiomInfo)) =
      .ok axiomInfo := by
  rw [(putAxiom_writes axiomInfo htyp).runPut]
  unfold Ixon.runGet
  have hread := getAxiom_reads axiomInfo htyp
    ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getAxiom { bytes := axiomBytes axiomInfo } = _ at hread
  rw [hread]

inductive CoreInfoWireWF : Ixon.ConstantInfo → Prop where
  | defn {definition : Ixon.Definition} :
      Ixon.Expr.wireWF definition.typ →
      Ixon.Expr.wireWF definition.value →
      CoreInfoWireWF (.defn definition)
  | axio {axiomInfo : Ixon.Axiom} :
      Ixon.Expr.wireWF axiomInfo.typ →
      CoreInfoWireWF (.axio axiomInfo)

def infoBytes : Ixon.ConstantInfo → ByteArray
  | .defn definition =>
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DEFN ++
        definitionBytes definition
  | .axio axiomInfo =>
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_AXIO ++
        axiomBytes axiomInfo
  | _ => ByteArray.empty

theorem reads_map {getm : Ixon.GetM α} {bytes : ByteArray} {value : α}
    (f : α → β) (h : Reads getm bytes value) :
    Reads (f <$> getm) bytes (f value) := by
  intro before after
  rw [map_eq_pure_bind]
  change (EStateM.bind getm (fun value => pure (f value))) _ = _
  rw [EStateM.bind, h]
  rfl

def getInfoFromTag (tag : Ixon.Tag4) : Ixon.GetM Ixon.ConstantInfo := do
  if tag.flag == Ixon.Constant.FLAG_MUTS then
    let mut ms := #[]
    for _ in [0:tag.size.toNat] do
      ms := ms.push (← Ixon.getMutConst)
    return Ixon.ConstantInfo.muts ms
  else if tag.flag == Ixon.Constant.FLAG then
    match tag.size with
    | 0 => Ixon.ConstantInfo.defn <$> Ixon.getDefinition
    | 1 => Ixon.ConstantInfo.recr <$> Ixon.getRecursor
    | 2 => Ixon.ConstantInfo.axio <$> Ixon.getAxiom
    | 3 => Ixon.ConstantInfo.quot <$> Ixon.getQuotient
    | 4 => Ixon.ConstantInfo.cPrj <$> Ixon.getConstructorProj
    | 5 => Ixon.ConstantInfo.rPrj <$> Ixon.getRecursorProj
    | 6 => Ixon.ConstantInfo.iPrj <$> Ixon.getInductiveProj
    | 7 => Ixon.ConstantInfo.dPrj <$> Ixon.getDefinitionProj
    | v => throw s!"getConstantInfo: invalid variant {v}"
  else
    throw s!"getConstantInfo: invalid flag {tag.flag}"

theorem getConstantInfo_eq :
    Ixon.getConstantInfo = (Ixon.getTag4 >>= getInfoFromTag) := by
  rfl

theorem putConstantInfo_writes_core (info : Ixon.ConstantInfo)
    (h : CoreInfoWireWF info) :
    Writes (Ixon.putConstantInfo info) (infoBytes info) := by
  cases h with
  | defn htyp hvalue =>
    have hwrite :=
      (putTag4_writes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DEFN).bind
        (putDefinition_writes _ htyp hvalue)
    simpa [Ixon.putConstantInfo, infoBytes, seqRight_eq_bind] using hwrite
  | axio htyp =>
    have hwrite :=
      (putTag4_writes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_AXIO).bind
        (putAxiom_writes _ htyp)
    simpa [Ixon.putConstantInfo, infoBytes, seqRight_eq_bind] using hwrite

theorem getConstantInfo_reads_core (info : Ixon.ConstantInfo)
    (h : CoreInfoWireWF info) :
    Reads Ixon.getConstantInfo (infoBytes info) info := by
  cases h with
  | @defn definition htyp hvalue =>
    have htag := getTag4_reads Ixon.Constant.FLAG
      Ixon.ConstantInfo.CONST_DEFN (by decide)
    have hdefinition := getDefinition_reads definition htyp hvalue
    have htail : Reads
        (getInfoFromTag
          ⟨Ixon.Constant.FLAG, Ixon.ConstantInfo.CONST_DEFN⟩)
        (definitionBytes definition) (.defn definition) := by
      simpa [getInfoFromTag, Ixon.Constant.FLAG,
        Ixon.Constant.FLAG_MUTS, Ixon.ConstantInfo.CONST_DEFN] using
          reads_map Ixon.ConstantInfo.defn hdefinition
    have hall := Reads.bind (next := getInfoFromTag) htag htail
    rw [getConstantInfo_eq]
    simpa [infoBytes] using hall
  | @axio axiomInfo htyp =>
    have htag := getTag4_reads Ixon.Constant.FLAG
      Ixon.ConstantInfo.CONST_AXIO (by decide)
    have haxiom := getAxiom_reads axiomInfo htyp
    have htail : Reads
        (getInfoFromTag
          ⟨Ixon.Constant.FLAG, Ixon.ConstantInfo.CONST_AXIO⟩)
        (axiomBytes axiomInfo) (.axio axiomInfo) := by
      simpa [getInfoFromTag, Ixon.Constant.FLAG,
        Ixon.Constant.FLAG_MUTS, Ixon.ConstantInfo.CONST_AXIO] using
          reads_map Ixon.ConstantInfo.axio haxiom
    have hall := Reads.bind (next := getInfoFromTag) htag htail
    rw [getConstantInfo_eq]
    simpa [infoBytes] using hall

theorem runGet_runPut_constantInfo_core (info : Ixon.ConstantInfo)
    (h : CoreInfoWireWF info) :
    Ixon.runGet Ixon.getConstantInfo (Ixon.runPut (Ixon.putConstantInfo info)) =
      .ok info := by
  rw [(putConstantInfo_writes_core info h).runPut]
  unfold Ixon.runGet
  have hread := getConstantInfo_reads_core info h
    ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getConstantInfo { bytes := infoBytes info } = _ at hread
  rw [hread]

def emptyConstant (info : Ixon.ConstantInfo) : Ixon.Constant :=
  ⟨info, #[], #[], #[]⟩

def emptyConstantBytes (info : Ixon.ConstantInfo) : ByteArray :=
  infoBytes info ++ tag0Bytes 0 ++ tag0Bytes 0 ++ tag0Bytes 0

def getConstantUnivs (info : Ixon.ConstantInfo)
    (sharing : Array Ixon.Expr) (refs : Array Address) :
    Ixon.GetM Ixon.Constant := do
  let numUnivs := (← Ixon.getTag0).size.toNat
  let mut univs : Array Ixon.Univ := #[]
  for _ in [0:numUnivs] do
    univs := univs.push (← Ixon.getUniv)
  return ⟨info, sharing, refs, univs⟩

def getConstantRefs (info : Ixon.ConstantInfo)
    (sharing : Array Ixon.Expr) : Ixon.GetM Ixon.Constant := do
  let numRefs := (← Ixon.getTag0).size.toNat
  let mut refs : Array Address := #[]
  for _ in [0:numRefs] do
    refs := refs.push (← Ixon.Serialize.get)
  getConstantUnivs info sharing refs

def getConstantAfterInfo (info : Ixon.ConstantInfo) :
    Ixon.GetM Ixon.Constant := do
  let numSharing := (← Ixon.getTag0).size.toNat
  let mut sharing : Array Ixon.Expr := #[]
  for _ in [0:numSharing] do
    sharing := sharing.push (← Ixon.getExpr)
  getConstantRefs info sharing

theorem getConstant_eq :
    Ixon.getConstant = (Ixon.getConstantInfo >>= getConstantAfterInfo) := by
  rfl

theorem putConstant_writes_core_empty (info : Ixon.ConstantInfo)
    (h : CoreInfoWireWF info) :
    Writes (Ixon.putConstant (emptyConstant info))
      (emptyConstantBytes info) := by
  have hwrite := (putConstantInfo_writes_core info h).bind
    ((putTag0_writes 0).bind
      ((putTag0_writes 0).bind (putTag0_writes 0)))
  simpa [Ixon.putConstant, emptyConstant, emptyConstantBytes,
    ByteArray.append_assoc] using hwrite

theorem getConstant_reads_core_empty (info : Ixon.ConstantInfo)
    (h : CoreInfoWireWF info) :
    Reads Ixon.getConstant (emptyConstantBytes info) (emptyConstant info) := by
  have hinfo := getConstantInfo_reads_core info h
  have hzero := getTag0_reads 0
  have hreturn := Reads.pure (emptyConstant info)
  have hunivsTail : Reads
      (do
        let mut univs : Array Ixon.Univ := #[]
        for _ in [0:0] do
          univs := univs.push (← Ixon.getUniv)
        return (⟨info, #[], #[], univs⟩ : Ixon.Constant))
      ByteArray.empty (emptyConstant info) := by
    simpa [emptyConstant] using hreturn
  have hunivs := Reads.bind
    (next := fun count : Ixon.Tag0 => do
      let mut univs : Array Ixon.Univ := #[]
      for _ in [0:count.size.toNat] do
        univs := univs.push (← Ixon.getUniv)
      return (⟨info, #[], #[], univs⟩ : Ixon.Constant))
    hzero hunivsTail
  have hunivs' : Reads (getConstantUnivs info #[] #[])
      (tag0Bytes 0) (emptyConstant info) := by
    simpa [getConstantUnivs] using hunivs
  have hrefsTail : Reads
      (do
        let mut refs : Array Address := #[]
        for _ in [0:0] do
          refs := refs.push (← Ixon.Serialize.get)
        getConstantUnivs info #[] refs)
      (tag0Bytes 0) (emptyConstant info) := by
    simpa using hunivs'
  have hrefs := Reads.bind
    (next := fun count : Ixon.Tag0 => do
      let mut refs : Array Address := #[]
      for _ in [0:count.size.toNat] do
        refs := refs.push (← Ixon.Serialize.get)
      getConstantUnivs info #[] refs)
    hzero hrefsTail
  have hrefs' : Reads (getConstantRefs info #[])
      (tag0Bytes 0 ++ tag0Bytes 0) (emptyConstant info) := by
    simpa [getConstantRefs] using hrefs
  have hsharingTail : Reads
      (do
        let mut sharing : Array Ixon.Expr := #[]
        for _ in [0:0] do
          sharing := sharing.push (← Ixon.getExpr)
        getConstantRefs info sharing)
      (tag0Bytes 0 ++ tag0Bytes 0) (emptyConstant info) := by
    simpa using hrefs'
  have hsharing := Reads.bind
    (next := fun count : Ixon.Tag0 => do
      let mut sharing : Array Ixon.Expr := #[]
      for _ in [0:count.size.toNat] do
        sharing := sharing.push (← Ixon.getExpr)
      getConstantRefs info sharing)
    hzero hsharingTail
  have htail : Reads (getConstantAfterInfo info)
      (tag0Bytes 0 ++ tag0Bytes 0 ++ tag0Bytes 0)
      (emptyConstant info) := by
    simpa [getConstantAfterInfo, ByteArray.append_assoc] using hsharing
  have hall := Reads.bind (next := getConstantAfterInfo) hinfo htail
  rw [getConstant_eq]
  simpa [emptyConstantBytes, ByteArray.append_assoc] using hall

theorem deConstant_serConstant_core_empty (info : Ixon.ConstantInfo)
    (h : CoreInfoWireWF info) :
    Ixon.deConstant (Ixon.serConstant (emptyConstant info)) =
      .ok (emptyConstant info) := by
  unfold Ixon.serConstant
  rw [(putConstant_writes_core_empty info h).runPut]
  unfold Ixon.deConstant Ixon.runGet
  have hread := getConstant_reads_core_empty info h
    ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getConstant { bytes := emptyConstantBytes info } = _
    at hread
  rw [hread]

end Ix.Compile.Verify.Codec.Ixon.Constant

namespace Ix.Compile.Verify

abbrev CoreConstantInfoWireWF : Ixon.ConstantInfo → Prop :=
  Codec.Ixon.Constant.CoreInfoWireWF

abbrev emptyCoreConstant : Ixon.ConstantInfo → Ixon.Constant :=
  Codec.Ixon.Constant.emptyConstant

theorem definitionCoreInfoWireWF (definition : Ixon.Definition)
    (htyp : ExprWireWF definition.typ)
    (hvalue : ExprWireWF definition.value) :
    CoreConstantInfoWireWF (.defn definition) :=
  .defn htyp hvalue

theorem axiomCoreInfoWireWF (axiomInfo : Ixon.Axiom)
    (htyp : ExprWireWF axiomInfo.typ) :
    CoreConstantInfoWireWF (.axio axiomInfo) :=
  .axio htyp

/-- Top-level constant codec round trip for definitions and axioms with
    empty sharing/reference/universe side tables. -/
theorem deConstant_serConstant_core_empty (info : Ixon.ConstantInfo)
    (h : CoreConstantInfoWireWF info) :
    Ixon.deConstant (Ixon.serConstant (emptyCoreConstant info)) =
      .ok (emptyCoreConstant info) :=
  Codec.Ixon.Constant.deConstant_serConstant_core_empty info h

end Ix.Compile.Verify
