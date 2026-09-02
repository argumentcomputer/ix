import Ix.Compile.Verify.NonrecursiveConstantCodec

/-!
# Proof-visible recursor constant codec

This slice verifies production `RecursorRule` arrays and `Recursor` payloads,
including packed Boolean flags, all five numeric arity fields, the recursor
type, and the losslessly counted rule table.  Lifting the payload through the
`.recr` `ConstantInfo` discriminant closes every standalone constant variant;
the final theorem retains arbitrary well-formed top-level side tables.
-/

namespace Ix.Compile.Verify.Codec.Ixon.RecursorConstant

open Ix
open Ix.Compile.Verify.Codec
open Ix.Compile.Verify.Codec.Ixon.Constant
open Ix.Compile.Verify.Codec.Ixon.ConstantTables
open Ix.Compile.Verify.Codec.Ixon.NonrecursiveConstant

def recursorRuleBytes (rule : Ixon.RecursorRule) : ByteArray :=
  tag0Bytes rule.fields ++
    Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode rule.rhs

def RecursorRuleWireWF (rule : Ixon.RecursorRule) : Prop :=
  Ixon.Expr.wireWF rule.rhs

theorem putRecursorRule_writes (rule : Ixon.RecursorRule)
    (h : RecursorRuleWireWF rule) :
    Writes (Ixon.putRecursorRule rule) (recursorRuleBytes rule) := by
  simpa [Ixon.putRecursorRule, recursorRuleBytes] using
    (putTag0_writes rule.fields).bind
      (Ix.Compile.Verify.Codec.Ixon.Expr.putExpr_writes_spine rule.rhs h)

theorem getRecursorRule_reads (rule : Ixon.RecursorRule)
    (h : RecursorRuleWireWF rule) :
    Reads Ixon.getRecursorRule (recursorRuleBytes rule) rule := by
  have hfields := getTag0_reads rule.fields
  have hrhs := Ix.Compile.Verify.Codec.Ixon.Expr.getExpr_reads_spine rule.rhs h
  have hreturn := Reads.pure rule
  have hafterRhs := Reads.bind
    (next := fun rhs : Ixon.Expr =>
      (pure ({ rule with rhs } : Ixon.RecursorRule) :
        Ixon.GetM Ixon.RecursorRule))
    hrhs hreturn
  have hall := Reads.bind
    (next := fun fields : Ixon.Tag0 => do
      let rhs ← Ixon.getExpr
      return (⟨fields.size, rhs⟩ : Ixon.RecursorRule))
    hfields hafterRhs
  simpa [Ixon.getRecursorRule, recursorRuleBytes] using hall

theorem putRecursorRuleArray_writes (rules : Array Ixon.RecursorRule)
    (h : ∀ rule, rule ∈ rules.toList → RecursorRuleWireWF rule) :
    Writes (do for rule in rules do Ixon.putRecursorRule rule)
      (listBytes recursorRuleBytes rules.toList) := by
  exact arrayPut_writes Ixon.putRecursorRule recursorRuleBytes
    RecursorRuleWireWF rules h putRecursorRule_writes

theorem getRecursorRuleArray_reads (rules : Array Ixon.RecursorRule)
    (h : ∀ rule, rule ∈ rules.toList → RecursorRuleWireWF rule) :
    Reads (getMany Ixon.getRecursorRule rules.size)
      (listBytes recursorRuleBytes rules.toList) rules := by
  simpa using getMany_reads Ixon.getRecursorRule recursorRuleBytes rules.toList
    (fun rule hmem => getRecursorRule_reads rule (h rule hmem))

def recursorFlags (recursor : Ixon.Recursor) : UInt8 :=
  Ixon.packBools [recursor.k, recursor.isUnsafe]

theorem unpackRecursorFlags_pack (k isUnsafe : Bool) :
    let bools := Ixon.unpackBools 2 (Ixon.packBools [k, isUnsafe])
    bools[0]! = k ∧ bools[1]! = isUnsafe := by
  cases k <;> cases isUnsafe <;> decide

def recursorBytes (recursor : Ixon.Recursor) : ByteArray :=
  [recursorFlags recursor].toByteArray ++
    tag0Bytes recursor.lvls ++ tag0Bytes recursor.params ++
      tag0Bytes recursor.indices ++ tag0Bytes recursor.motives ++
        tag0Bytes recursor.minors ++
          Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode recursor.typ ++
            tag0Bytes recursor.rules.size.toUInt64 ++
              listBytes recursorRuleBytes recursor.rules.toList

structure RecursorWireWF (recursor : Ixon.Recursor) : Prop where
  typ : Ixon.Expr.wireWF recursor.typ
  rulesCount : ArrayCountWF recursor.rules
  rules : ∀ rule, rule ∈ recursor.rules.toList → RecursorRuleWireWF rule

theorem putRecursor_writes (recursor : Ixon.Recursor)
    (h : RecursorWireWF recursor) :
    Writes (Ixon.putRecursor recursor) (recursorBytes recursor) := by
  have hwrite := (putU8_writes (recursorFlags recursor)).bind
    ((putTag0_writes recursor.lvls).bind
      ((putTag0_writes recursor.params).bind
        ((putTag0_writes recursor.indices).bind
          ((putTag0_writes recursor.motives).bind
            ((putTag0_writes recursor.minors).bind
              ((Ix.Compile.Verify.Codec.Ixon.Expr.putExpr_writes_spine
                recursor.typ h.typ).bind
                ((putTag0_writes recursor.rules.size.toUInt64).bind
                  (putRecursorRuleArray_writes recursor.rules h.rules))))))))
  simpa [Ixon.putRecursor, recursorFlags, recursorBytes,
    ByteArray.append_assoc] using hwrite

def getRecursorRules (k isUnsafe : Bool) (lvls params indices motives minors : UInt64)
    (typ : Ixon.Expr) : Ixon.GetM Ixon.Recursor := do
  let count := (← Ixon.getTag0).size.toNat
  let mut rules : Array Ixon.RecursorRule := #[]
  for _ in [0:count] do
    rules := rules.push (← Ixon.getRecursorRule)
  return ⟨k, isUnsafe, lvls, params, indices, motives, minors, typ, rules⟩

def getRecursorAfterFlags (k isUnsafe : Bool) : Ixon.GetM Ixon.Recursor := do
  let lvls := (← Ixon.getTag0).size
  let params := (← Ixon.getTag0).size
  let indices := (← Ixon.getTag0).size
  let motives := (← Ixon.getTag0).size
  let minors := (← Ixon.getTag0).size
  let typ ← Ixon.getExpr
  getRecursorRules k isUnsafe lvls params indices motives minors typ

def getRecursorFromFlags (flags : UInt8) : Ixon.GetM Ixon.Recursor :=
  let bools := Ixon.unpackBools 2 flags
  getRecursorAfterFlags bools[0]! bools[1]!

theorem getRecursor_eq :
    Ixon.getRecursor = (Ixon.getU8 >>= getRecursorFromFlags) := by
  rfl

theorem getRecursorRules_reads (recursor : Ixon.Recursor)
    (h : RecursorWireWF recursor) :
    Reads
      (getRecursorRules recursor.k recursor.isUnsafe recursor.lvls
        recursor.params recursor.indices recursor.motives recursor.minors
        recursor.typ)
      (tag0Bytes recursor.rules.size.toUInt64 ++
        listBytes recursorRuleBytes recursor.rules.toList)
      recursor := by
  have htag := getTag0_reads recursor.rules.size.toUInt64
  have hdecode := arrayCount_decode recursor.rules h.rulesCount
  have hrules := getRecursorRuleArray_reads recursor.rules h.rules
  have hreturn := Reads.pure recursor
  have hafterRules := Reads.bind
    (next := fun rules : Array Ixon.RecursorRule =>
      (pure ({ recursor with rules } : Ixon.Recursor) :
        Ixon.GetM Ixon.Recursor))
    hrules hreturn
  have htail : Reads
      (do
        let mut rules : Array Ixon.RecursorRule := #[]
        for _ in [0:recursor.rules.size.toUInt64.toNat] do
          rules := rules.push (← Ixon.getRecursorRule)
        return ({ recursor with rules } : Ixon.Recursor))
      (listBytes recursorRuleBytes recursor.rules.toList) recursor := by
    simpa [getMany, hdecode] using hafterRules
  have hall := Reads.bind
    (next := fun count : Ixon.Tag0 => do
      let mut rules : Array Ixon.RecursorRule := #[]
      for _ in [0:count.size.toNat] do
        rules := rules.push (← Ixon.getRecursorRule)
      return ({ recursor with rules } : Ixon.Recursor))
    htag htail
  simpa [getRecursorRules] using hall

theorem getRecursorAfterFlags_reads (recursor : Ixon.Recursor)
    (h : RecursorWireWF recursor) :
    Reads (getRecursorAfterFlags recursor.k recursor.isUnsafe)
      (tag0Bytes recursor.lvls ++ tag0Bytes recursor.params ++
        tag0Bytes recursor.indices ++ tag0Bytes recursor.motives ++
          tag0Bytes recursor.minors ++
            Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode recursor.typ ++
              tag0Bytes recursor.rules.size.toUInt64 ++
                listBytes recursorRuleBytes recursor.rules.toList)
      recursor := by
  have hlvls := getTag0_reads recursor.lvls
  have hparams := getTag0_reads recursor.params
  have hindices := getTag0_reads recursor.indices
  have hmotives := getTag0_reads recursor.motives
  have hminors := getTag0_reads recursor.minors
  have htyp := Ix.Compile.Verify.Codec.Ixon.Expr.getExpr_reads_spine
    recursor.typ h.typ
  have hrules := getRecursorRules_reads recursor h
  have hafterTyp := Reads.bind
    (next := fun typ : Ixon.Expr =>
      getRecursorRules recursor.k recursor.isUnsafe recursor.lvls
        recursor.params recursor.indices recursor.motives recursor.minors typ)
    htyp hrules
  have hafterMinors := Reads.bind
    (next := fun minors : Ixon.Tag0 => do
      let typ ← Ixon.getExpr
      getRecursorRules recursor.k recursor.isUnsafe recursor.lvls
        recursor.params recursor.indices recursor.motives minors.size typ)
    hminors hafterTyp
  have hafterMotives := Reads.bind
    (next := fun motives : Ixon.Tag0 => do
      let minors := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      getRecursorRules recursor.k recursor.isUnsafe recursor.lvls
        recursor.params recursor.indices motives.size minors typ)
    hmotives hafterMinors
  have hafterIndices := Reads.bind
    (next := fun indices : Ixon.Tag0 => do
      let motives := (← Ixon.getTag0).size
      let minors := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      getRecursorRules recursor.k recursor.isUnsafe recursor.lvls
        recursor.params indices.size motives minors typ)
    hindices hafterMotives
  have hafterParams := Reads.bind
    (next := fun params : Ixon.Tag0 => do
      let indices := (← Ixon.getTag0).size
      let motives := (← Ixon.getTag0).size
      let minors := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      getRecursorRules recursor.k recursor.isUnsafe recursor.lvls
        params.size indices motives minors typ)
    hparams hafterIndices
  have hall := Reads.bind
    (next := fun lvls : Ixon.Tag0 => do
      let params := (← Ixon.getTag0).size
      let indices := (← Ixon.getTag0).size
      let motives := (← Ixon.getTag0).size
      let minors := (← Ixon.getTag0).size
      let typ ← Ixon.getExpr
      getRecursorRules recursor.k recursor.isUnsafe lvls.size params indices
        motives minors typ)
    hlvls hafterParams
  simpa [getRecursorAfterFlags, ByteArray.append_assoc] using hall

theorem getRecursor_reads (recursor : Ixon.Recursor)
    (h : RecursorWireWF recursor) :
    Reads Ixon.getRecursor (recursorBytes recursor) recursor := by
  have hflags := getU8_reads (recursorFlags recursor)
  have hdecode := unpackRecursorFlags_pack recursor.k recursor.isUnsafe
  have htail := getRecursorAfterFlags_reads recursor h
  have htail' : Reads (getRecursorFromFlags (recursorFlags recursor))
      (tag0Bytes recursor.lvls ++ tag0Bytes recursor.params ++
        tag0Bytes recursor.indices ++ tag0Bytes recursor.motives ++
          tag0Bytes recursor.minors ++
            Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode recursor.typ ++
              tag0Bytes recursor.rules.size.toUInt64 ++
                listBytes recursorRuleBytes recursor.rules.toList)
      recursor := by
    simpa [getRecursorFromFlags, recursorFlags, hdecode.1, hdecode.2] using htail
  have hall := Reads.bind (next := getRecursorFromFlags) hflags htail'
  rw [getRecursor_eq]
  simpa [recursorBytes, ByteArray.append_assoc] using hall

inductive StandaloneInfoWireWF : Ixon.ConstantInfo → Prop where
  | nonrecursive {info : Ixon.ConstantInfo} :
      NonrecursiveInfoWireWF info → StandaloneInfoWireWF info
  | recr {recursor : Ixon.Recursor} :
      RecursorWireWF recursor → StandaloneInfoWireWF (.recr recursor)

def standaloneInfoBytes : Ixon.ConstantInfo → ByteArray
  | .recr recursor =>
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_RECR ++
        recursorBytes recursor
  | info => nonrecursiveInfoBytes info

theorem putConstantInfo_writes_standalone (info : Ixon.ConstantInfo)
    (h : StandaloneInfoWireWF info) :
    Writes (Ixon.putConstantInfo info) (standaloneInfoBytes info) := by
  cases h with
  | @nonrecursive info hbase =>
    have hwrite := putConstantInfo_writes_nonrecursive info hbase
    cases hbase <;>
      simpa [standaloneInfoBytes, nonrecursiveInfoBytes] using hwrite
  | recr hrecursor =>
    simpa [Ixon.putConstantInfo, standaloneInfoBytes, seqRight_eq_bind] using
      (putTag4_writes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_RECR).bind
        (putRecursor_writes _ hrecursor)

theorem getConstantInfo_reads_standalone (info : Ixon.ConstantInfo)
    (h : StandaloneInfoWireWF info) :
    Reads Ixon.getConstantInfo (standaloneInfoBytes info) info := by
  cases h with
  | @nonrecursive info hbase =>
    have hread := getConstantInfo_reads_nonrecursive info hbase
    cases hbase <;>
      simpa [standaloneInfoBytes, nonrecursiveInfoBytes] using hread
  | @recr recursor hrecursor =>
    apply getConstantInfo_reads_variant
      Ixon.ConstantInfo.CONST_RECR Ixon.getRecursor
      (recursorBytes recursor) recursor Ixon.ConstantInfo.recr
    · simp [getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
        Ixon.ConstantInfo.CONST_RECR]
    · exact getRecursor_reads recursor hrecursor

structure StandaloneConstantWireWF (constant : Ixon.Constant) : Prop where
  info : StandaloneInfoWireWF constant.info
  sharingCount : ArrayCountWF constant.sharing
  sharingEntries : ∀ value, value ∈ constant.sharing.toList →
    Ixon.Expr.wireWF value
  refsCount : ArrayCountWF constant.refs
  refsEntries : ∀ value, value ∈ constant.refs.toList → AddressWireWF value
  univsCount : ArrayCountWF constant.univs
  univsEntries : ∀ value, value ∈ constant.univs.toList →
    Ix.Compile.Verify.Codec.Ixon.Univ.WireWF value

def standaloneConstantBytes (constant : Ixon.Constant) : ByteArray :=
  standaloneInfoBytes constant.info ++
    tag0Bytes constant.sharing.size.toUInt64 ++
      listBytes Ix.Compile.Verify.Codec.Ixon.Expr.spineWireEncode
        constant.sharing.toList ++
        tag0Bytes constant.refs.size.toUInt64 ++
          listBytes Address.hash constant.refs.toList ++
            tag0Bytes constant.univs.size.toUInt64 ++
              listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode
                constant.univs.toList

theorem putConstant_writes_standalone (constant : Ixon.Constant)
    (h : StandaloneConstantWireWF constant) :
    Writes (Ixon.putConstant constant) (standaloneConstantBytes constant) := by
  have hwrite := (putConstantInfo_writes_standalone constant.info h.info).bind
    ((putTag0_writes constant.sharing.size.toUInt64).bind
      ((putExprArray_writes constant.sharing h.sharingEntries).bind
        ((putTag0_writes constant.refs.size.toUInt64).bind
          ((putAddressArray_writes constant.refs h.refsEntries).bind
            ((putTag0_writes constant.univs.size.toUInt64).bind
              (putUnivArray_writes constant.univs h.univsEntries))))))
  simpa [Ixon.putConstant, standaloneConstantBytes,
    ByteArray.append_assoc] using hwrite

theorem getConstant_reads_standalone (constant : Ixon.Constant)
    (h : StandaloneConstantWireWF constant) :
    Reads Ixon.getConstant (standaloneConstantBytes constant) constant := by
  have hinfo := getConstantInfo_reads_standalone constant.info h.info
  have htail := getConstantAfterInfo_reads_core constant.info
    constant.sharing constant.refs constant.univs h.sharingCount
    h.sharingEntries h.refsCount h.refsEntries h.univsCount h.univsEntries
  have hall := Reads.bind (next := getConstantAfterInfo) hinfo htail
  rw [getConstant_eq]
  simpa [standaloneConstantBytes, ByteArray.append_assoc] using hall

theorem deConstant_serConstant_standalone (constant : Ixon.Constant)
    (h : StandaloneConstantWireWF constant) :
    Ixon.deConstant (Ixon.serConstant constant) = .ok constant := by
  unfold Ixon.serConstant
  rw [(putConstant_writes_standalone constant h).runPut]
  unfold Ixon.deConstant Ixon.runGet
  have hread := getConstant_reads_standalone constant h
    ByteArray.empty ByteArray.empty
  simp only [ByteArray.empty_append, ByteArray.append_empty,
    ByteArray.size_empty, Nat.zero_add] at hread
  change EStateM.run Ixon.getConstant
    { bytes := standaloneConstantBytes constant } = _ at hread
  rw [hread]

end Ix.Compile.Verify.Codec.Ixon.RecursorConstant

namespace Ix.Compile.Verify

abbrev RecursorRuleWireWF : Ixon.RecursorRule → Prop :=
  Codec.Ixon.RecursorConstant.RecursorRuleWireWF

abbrev RecursorWireWF : Ixon.Recursor → Prop :=
  Codec.Ixon.RecursorConstant.RecursorWireWF

abbrev StandaloneConstantInfoWireWF : Ixon.ConstantInfo → Prop :=
  Codec.Ixon.RecursorConstant.StandaloneInfoWireWF

abbrev StandaloneConstantWireWF : Ixon.Constant → Prop :=
  Codec.Ixon.RecursorConstant.StandaloneConstantWireWF

theorem standaloneConstantInfoWireWF_of_nonrecursive {info : Ixon.ConstantInfo}
    (h : NonrecursiveConstantInfoWireWF info) :
    StandaloneConstantInfoWireWF info :=
  .nonrecursive h

theorem recursorConstantInfoWireWF (recursor : Ixon.Recursor)
    (h : RecursorWireWF recursor) :
    StandaloneConstantInfoWireWF (.recr recursor) :=
  .recr h

/-- Production top-level round trip for every non-mutual `ConstantInfo`
    variant with arbitrary wire-representable side tables. -/
theorem deConstant_serConstant_standalone (constant : Ixon.Constant)
    (h : StandaloneConstantWireWF constant) :
    Ixon.deConstant (Ixon.serConstant constant) = .ok constant :=
  Codec.Ixon.RecursorConstant.deConstant_serConstant_standalone constant h

end Ix.Compile.Verify
