import Batteries.Data.RBMap.Basic
import Ix.Aiur.Constraints
import Ix.SmallMap

namespace Aiur.Circuit

abbrev B64_MULT_GEN : UInt128 := 508773776270040456

open Archon Binius

structure AiurChannels where
  func : ChannelId
  add : ChannelId
  mul : ChannelId
  mem : SmallMap Nat ChannelId

inductive CachedOracleKey
  | const : UInt128 → CachedOracleKey
  | lc : ArithExpr → TowerField → CachedOracleKey
  deriving Ord

structure SynthState where
  circuitModule : CircuitModule
  cachedOracles : Batteries.RBMap CachedOracleKey OracleIdx compare

@[inline] def SynthState.init (circuitModule : CircuitModule) : SynthState :=
  ⟨circuitModule, default⟩

abbrev SynthM := StateM SynthState

@[inline] def synthesizeM (circuitModuleId : USize) (f : SynthM α) : CircuitModule :=
  let (_, stt) := f.run $ .init (CircuitModule.new circuitModuleId)
  stt.circuitModule

@[inline] def flush (direction : FlushDirection) (channelId : ChannelId)
    (selector : OracleIdx) (args : @& Array OracleIdx) (multiplicity : UInt64) : SynthM Unit :=
  modify fun stt =>
    let circuitModule := stt.circuitModule.flush direction channelId selector
      args multiplicity
    { stt with circuitModule }

@[inline] def send (channelId : ChannelId) (args : @& Array OracleIdx) : SynthM Unit :=
  flush .push channelId CircuitModule.selector args 1

@[inline] def recv (channelId : ChannelId) (args : @& Array OracleIdx) : SynthM Unit :=
  flush .pull channelId CircuitModule.selector args 1

@[inline] def assertZero (name : @& String) (expr : @& ArithExpr) : SynthM Unit :=
  modify fun stt =>
    { stt with circuitModule := stt.circuitModule.assertZero name #[] expr }

def addCommitted (name : @& String) (tf : TowerField) : SynthM OracleIdx :=
  modifyGet fun stt =>
    let (o, circuitModule) := stt.circuitModule.addCommitted name tf
    (o, { stt with circuitModule })

def addTransparent (name : @& String) (transparent : Transparent) : SynthM OracleIdx :=
  modifyGet fun stt =>
    let (o, circuitModule) := stt.circuitModule.addTransparent name transparent
    (o, { stt with circuitModule })

def addLinearCombination (name : @& String) (offset : @& UInt128)
    (inner : @& Array (OracleIdx × UInt128)) : SynthM OracleIdx :=
  modifyGet fun stt =>
    let (o, circuitModule) := stt.circuitModule.addLinearCombination name offset inner
    (o, { stt with circuitModule })

def addPacked (name : @& String) (inner : OracleIdx) (logDegree : USize) : SynthM OracleIdx :=
  modifyGet fun stt =>
    let (o, circuitModule) := stt.circuitModule.addPacked name inner logDegree
    (o, { stt with circuitModule })

def addShifted (name : @& String) (inner : OracleIdx) (shiftOffset : UInt32)
    (blockBits : USize) (shiftVariant : ShiftVariant) : SynthM OracleIdx :=
  modifyGet fun stt =>
    let (o, circuitModule) := stt.circuitModule.addShifted name inner shiftOffset
      blockBits shiftVariant
    (o, { stt with circuitModule })

def addProjected (name : @& String) (inner : OracleIdx) (mask : UInt64)
    (unprojectedSize startIndex : USize) : SynthM OracleIdx :=
  modifyGet fun stt =>
    let (o, circuitModule) := stt.circuitModule.addProjected name inner mask
      unprojectedSize startIndex
    (o, { stt with circuitModule })

@[inline] def cacheConstAux (value : UInt128) (stt : SynthState) : OracleIdx × SynthState :=
  let (o, circuitModule) := stt.circuitModule.addTransparent
    s!"cached-const-{value}" (.const value)
  let cachedOracles := stt.cachedOracles.insert (.const value) o
  (o, ⟨circuitModule, cachedOracles⟩)

def cacheConst (value : UInt128) : SynthM OracleIdx :=
  modifyGet fun stt => match stt.cachedOracles.find? (.const value) with
  | some o => (o, stt)
  | none => cacheConstAux value stt

def cacheLc (expr : ArithExpr) (tf : TowerField) : SynthM OracleIdx :=
  let key := .lc expr tf
  modifyGet fun stt => match stt.cachedOracles.find? key with
  | some o => (o, stt)
  | none => if let .const value := expr then cacheConstAux value stt else
    let (summands, offset) := accSummandsAndOffset expr #[] 0
    let inner := summands.map (·, 1)
    let (o, circuitModule) := stt.circuitModule.addLinearCombination
      s!"cached-lc-{expr}-{tf}" offset inner
    let cachedOracles := stt.cachedOracles.insert key o
    (o, ⟨circuitModule, cachedOracles⟩)
where
  accSummandsAndOffset expr summands (offset : UInt128) := match expr with
    | .const c => (summands, addUInt128InBinaryField offset c tf)
    | .oracle o => (summands.push o, offset)
    | .add a b =>
      let (summands', offset') := accSummandsAndOffset a summands offset
      accSummandsAndOffset b summands' offset'
    | _ => unreachable!

def provide (channelId : ChannelId) (multiplicity : OracleIdx)
    (args : Array OracleIdx) : SynthM Unit := do
  let ones ← cacheConst 1
  send channelId (args.push ones)
  recv channelId (args.push multiplicity)

def require (channelId : ChannelId) (prevIdx : OracleIdx) (args : Array OracleIdx)
    (sel : OracleIdx) : SynthM Unit := do
  let idx ← addLinearCombination s!"index-{channelId.toUSize}" 0 #[(prevIdx, B64_MULT_GEN)]
  flush .pull channelId sel (args.push prevIdx) 1
  flush .push channelId sel (args.push idx) 1

def synthesizeFunction (funcIdx : Nat) (function : Bytecode.Function)
    (layout : Layout) (aiurChannels : AiurChannels) : SynthM Unit := do
  let columns ← modifyGet fun stt =>
    let (cs, circuitModule) := Columns.ofLayout stt.circuitModule layout
    (cs, { stt with circuitModule })
  let constraints := buildFuncionConstraints function layout columns
  assertZero "topmost" (constraints.topmostSelector - CircuitModule.selector)
  let funcIdxOracle ← cacheConst (.ofNatWrap funcIdx)
  provide aiurChannels.func constraints.multiplicity (constraints.io.push funcIdxOracle)
  constraints.uniqueConstraints.zipIdx.forM fun (expr, i) =>
    assertZero s!"unique constraint {i}" expr
  constraints.sharedConstraints.zipIdx.forM fun (expr, i) =>
    assertZero s!"shared constraint {i}" expr
  constraints.sends.forM fun (channel, sel, args) => do
    let sel ← cacheLc sel .b1
    let args ← args.mapM (cacheLc · .b64)
    match channel with
    | .add => flush .push aiurChannels.add sel args 1
    | .mul => flush .push aiurChannels.mul sel args 1
    | _ => unreachable!
  constraints.requires.forM fun (channel, sel, prevIdx, args) => do
    let sel ← cacheLc sel .b1
    let args ← args.mapM (cacheLc · .b64)
    match channel with
    | .func funcIdx =>
      let idx ← cacheConst (.ofNatWrap funcIdx.toNat)
      require aiurChannels.func prevIdx (args.push idx) sel
    | .mem width =>
      let channelId := aiurChannels.mem.get width |>.get!
      require channelId prevIdx args sel
    | _ => unreachable!

def synthesizeAdd (channelId : ChannelId) : SynthM Unit := do
  let xin ← addCommitted "add-xin" .b1
  let yin ← addCommitted "add-yin" .b1
  let zout ← addCommitted "add-zout" .b1
  let cout ← addCommitted "add-cout" .b1
  let cin ← addShifted "add-cin" cout 1 TowerField.b64.logDegree .logicalLeft
  let xinPacked ← addPacked "add-xin-packed" xin TowerField.b64.logDegree
  let yinPacked ← addPacked "add-yin-packed" yin TowerField.b64.logDegree
  let zoutPacked ← addPacked "add-zout-packed" zout TowerField.b64.logDegree
  let mask := 0b111111
  let coutProjected ← addProjected "add-cout-projected" cout mask 64 0
  assertZero "add-sum" $ xin + yin + cin - zout
  assertZero "add-carry" $ (xin + cin) * (yin + cin) + cin - cout
  recv channelId #[xinPacked, yinPacked, zoutPacked, coutProjected]

def synthesizeMul (channelId : ChannelId) : SynthM Unit :=
  sorry

def synthesizeMemory (channelId : ChannelId) (width : Nat) : SynthM Unit := do
  let address ← addTransparent s!"mem-{width}-address" .incremental
  let values ← Array.range width |>.mapM (addCommitted s!"mem-{width}-value-{·}" .b64)
  let multiplicipy ← addCommitted s!"mem-{width}-multiplicity" .b64
  let args := values.push address
  provide channelId multiplicipy args

structure AiurCircuitModules where
  funcs : Array CircuitModule
  add : CircuitModule
  mul : CircuitModule
  -- If we don't need these widths, we can change to `Array CircuitModule` later
  mem : SmallMap Nat CircuitModule

def synthesize (toplevel : Bytecode.Toplevel) : AiurCircuitModules :=
  let channelAllocator := ChannelAllocator.init
  let (funcChannel, channelAllocator) := channelAllocator.next
  let (addChannel, channelAllocator) := channelAllocator.next
  let (mulChannel, channelAllocator) := channelAllocator.next
  let (memChannels, _) := toplevel.memWidths.foldl (init := (default, channelAllocator))
    fun (map, channelAllocator) width =>
      let (channelId, channelAllocator) := channelAllocator.next
      (map.insert width channelId, channelAllocator)
  let aiurChannels := AiurChannels.mk funcChannel addChannel mulChannel memChannels
  let funcsModules := toplevel.functions.zip toplevel.layouts |>.zipIdx.map
    fun ((function, layout), functionIdx) => synthesizeM functionIdx.toUSize
      (synthesizeFunction functionIdx function layout aiurChannels)
  let numFunctions := toplevel.functions.size.toUSize
  let addModule := synthesizeM (numFunctions + 1) (synthesizeAdd addChannel)
  let mulModule := synthesizeM (numFunctions + 2) (synthesizeMul mulChannel)
  let memIdStart := numFunctions + 3
  let memModules := memChannels.pairs.zipIdx.map
    fun ((width, channelId), memIdx) =>
      let circuitModule := synthesizeM (memIdStart + memIdx.toUSize)
        (synthesizeMemory channelId width)
      (width, circuitModule)
  ⟨funcsModules, addModule, mulModule, ⟨memModules⟩⟩

end Aiur.Circuit
