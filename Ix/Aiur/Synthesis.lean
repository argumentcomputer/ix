import Batteries.Data.RBMap.Basic
import Ix.Aiur.Constraints
import Ix.SmallMap

namespace Aiur.Circuit

abbrev B64_MULT_GEN : UInt128 := 508773776270040456
abbrev B128_MULT_GEN : UInt128 := 61857528091874184034011775247790689018

open Archon Binius

structure AiurChannels where
  func : Array ChannelId
  add : ChannelId
  mul : ChannelId
  mem : SmallMap Nat ChannelId
  gad : Array ChannelId

inductive CachedOracleKey
  | const : UInt128 → CachedOracleKey
  | lc : ArithExpr → CachedOracleKey
  deriving Ord

structure SynthState where
  circuitModule : CircuitModule
  cachedOracles : Batteries.RBMap CachedOracleKey OracleIdx compare

@[inline] def SynthState.init (circuitModule : CircuitModule) : SynthState :=
  ⟨circuitModule, default⟩

abbrev SynthM := StateM SynthState

@[inline] def synthesizeM (circuitModuleId : USize) (f : SynthM α) : (CircuitModule × α) :=
  let (a, stt) := f.run $ .init (CircuitModule.new circuitModuleId)
  (stt.circuitModule.freezeOracles, a)

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

@[inline] def assertDynamicExp (expBits : @& Array OracleIdx) (result base : OracleIdx) :
    SynthM Unit :=
  modify fun stt =>
    { stt with circuitModule := stt.circuitModule.assertDynamicExp expBits result base }

@[inline] def assertStaticExp (expBits : @& Array OracleIdx) (result : OracleIdx)
    (base : @& UInt128) (baseTF : TowerField): SynthM Unit :=
  modify fun stt =>
    { stt with circuitModule := stt.circuitModule.assertStaticExp expBits result base baseTF }

def addCommitted (name : @& String) (tf : TowerField) (relativeHeight : RelativeHeight) :
    SynthM OracleIdx :=
  modifyGet fun stt =>
    let (o, circuitModule) := stt.circuitModule.addCommitted name tf relativeHeight
    (o, { stt with circuitModule })

def addTransparent (name : @& String) (transparent : Transparent) (relativeHeight : RelativeHeight) :
    SynthM OracleIdx :=
  modifyGet fun stt =>
    let (o, circuitModule) := stt.circuitModule.addTransparent name transparent relativeHeight
    (o, { stt with circuitModule })

def addLinearCombination (name : @& String) (offset : @& UInt128)
    (inner : @& Array (OracleIdx × UInt128)) (relativeHeight : RelativeHeight) : SynthM OracleIdx :=
  modifyGet fun stt =>
    let (o, circuitModule) := stt.circuitModule.addLinearCombination name offset inner relativeHeight
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

def addProjected (name : @& String) (inner : OracleIdx) (selection : UInt64)
    (chunkSize : USize) : SynthM OracleIdx :=
  modifyGet fun stt =>
    let (o, circuitModule) := stt.circuitModule.addProjected name inner selection chunkSize
    (o, { stt with circuitModule })

def cacheConst (value : UInt128) : SynthM OracleIdx :=
  modifyGet fun stt => match stt.cachedOracles.find? (.const value) with
  | some o => (o, stt)
  | none =>
    let (o, circuitModule) := stt.circuitModule.addTransparent
      s!"cached-const-{value}" (.const value) .base
    let cachedOracles := stt.cachedOracles.insert (.const value) o
    (o, ⟨circuitModule, cachedOracles⟩)

def cacheLc (expr : ArithExpr) : SynthM OracleIdx :=
  let key := .lc expr
  modifyGet fun stt => match stt.cachedOracles.find? key with
  | some o => (o, stt)
  | none =>
    let (summands, offset) := accSummandsAndOffset expr #[] 0
    let inner := summands.map (·, 1)
    let (o, circuitModule) := stt.circuitModule.addLinearCombination
      s!"cached-lc-{expr}" offset inner .base
    let cachedOracles := stt.cachedOracles.insert key o
    (o, ⟨circuitModule, cachedOracles⟩)
where
  accSummandsAndOffset expr summands (offset : UInt128) := match expr with
    | .const c => (summands, addUInt128InBinaryField offset c)
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
  let idx ← addLinearCombination s!"index-{channelId.toUSize}" 0 #[(prevIdx, B64_MULT_GEN)] .base
  flush .pull channelId sel (args.push prevIdx) 1
  flush .push channelId sel (args.push idx) 1

def synthesizeFunction (funcIdx : FuncIdx) (function : Bytecode.Function)
    (layout : Layout) (aiurChannels : AiurChannels) : SynthM Columns := do
  let columns ← modifyGet fun stt =>
    let (cs, circuitModule) := Columns.ofLayout stt.circuitModule layout
    (cs, { stt with circuitModule })
  let constraints := buildFuncionConstraints function layout columns
  assertZero "func-topmost" (constraints.topmostSelector - CircuitModule.selector)
  let funcChannel := aiurChannels.func[funcIdx]!
  provide funcChannel constraints.multiplicity constraints.io
  constraints.uniqueConstraints.zipIdx.forM fun (expr, i) =>
    assertZero s!"func-unique-constraint-{i}" expr
  constraints.sharedConstraints.zipIdx.forM fun (expr, i) =>
    assertZero s!"func-shared-constraint-{i}" expr
  constraints.recvs.forM fun (channel, sel, args) => do
    let sel ← cacheLc sel
    let args ← args.mapM cacheLc
    match channel with
    | .add => flush .pull aiurChannels.add sel args 1
    | .mul => flush .pull aiurChannels.mul sel args 1
    | _ => unreachable!
  constraints.requires.forM fun (channel, sel, prevIdx, values) => do
    let sel ← cacheLc sel
    let values ← values.mapM cacheLc
    match channel with
    | .func funcIdx =>
      let funcChannel := aiurChannels.func[funcIdx]!
      require funcChannel prevIdx values sel
    | .mem width =>
      let channelId := aiurChannels.mem.get width |>.get!
      require channelId prevIdx values sel
    | .gadget gadgetIdx =>
      let gadgetChannel := aiurChannels.gad[gadgetIdx]!
      require gadgetChannel prevIdx values sel
    | _ => unreachable!
  pure columns

structure AddColumns where
  xin : OracleIdx
  yin : OracleIdx
  zout : OracleIdx
  cout : OracleIdx

def synthesizeAdd (channelId : ChannelId) : SynthM AddColumns := do
  let xin ← addCommitted "add-xin" .b1 (.mul2 6)
  let yin ← addCommitted "add-yin" .b1 (.mul2 6)
  let zout ← addCommitted "add-zout" .b1 (.mul2 6)
  let cout ← addCommitted "add-cout" .b1 (.mul2 6)
  let cin ← addShifted "add-cin" cout 1 TowerField.b64.logDegree .logicalLeft
  let xinPacked ← addPacked "add-xin-packed" xin TowerField.b64.logDegree
  let yinPacked ← addPacked "add-yin-packed" yin TowerField.b64.logDegree
  let zoutPacked ← addPacked "add-zout-packed" zout TowerField.b64.logDegree
  let coutProjected ← addProjected "add-cout-projected" cout 63 64
  assertZero "add-sum" $ xin + yin + cin - zout
  assertZero "add-carry" $ (xin + cin) * (yin + cin) + cin - cout
  send channelId #[xinPacked, yinPacked, zoutPacked, coutProjected]
  pure { xin, yin, zout, cout }

structure MulColumns where
  xin : OracleIdx
  yin : OracleIdx
  zout : OracleIdx
  xinBits : Array OracleIdx
  yinBits : Array OracleIdx
  zoutBits : Array OracleIdx
  xinExpResult : OracleIdx
  yinExpResult : OracleIdx
  zoutLowExpResult : OracleIdx
  zoutHighExpResult : OracleIdx

def B128GenPow2To64 : UInt128 :=
  let outSize := 64
  outSize.fold (init := B128_MULT_GEN)
    fun _ _ g => mulUInt128InBinaryField g g

def synthesizeMul (channelId : ChannelId) : SynthM MulColumns := do
  let xin ← addCommitted "mul-xin" .b64 .base
  let yin ← addCommitted "mul-yin" .b64 .base
  let zout ← addCommitted "mul-zout" .b64 .base
  let xinBits ← Array.range 64 |>.mapM (addCommitted s!"mul-xin-bit-{·}" .b1 .base)
  let yinBits ← Array.range 64 |>.mapM (addCommitted s!"mul-yin-bit-{·}" .b1 .base)
  bitDecomposition "mul-bit-decomposition-xin" xinBits xin
  bitDecomposition "mul-bit-decomposition-yin" yinBits yin
  let (xinExpResult, yinExpResult, zoutLowExpResult, zoutHighExpResult, zoutBits)
    ← mul xinBits yinBits
  let zoutLow := zoutBits.extract (stop := 64)
  bitDecomposition "mul-bit-decomposition-zout" zoutLow zout
  send channelId #[xin, yin, zout]
  pure {
    xin,
    yin,
    zout,
    xinBits,
    yinBits,
    zoutBits,
    xinExpResult,
    yinExpResult,
    zoutLowExpResult,
    zoutHighExpResult, }
where
  bitDecomposition name bits word :=
    let (expr, _) := bits.foldl (init := (.oracle word, (1 : UInt64)))
      fun (expr, coeff) bit => (expr - (.const (.ofLoHi coeff 0)) * bit, coeff <<< 1)
    assertZero name expr
  mul xinBits yinBits := do
    let outSize : Nat := 64
    let xinExpResult ← addCommitted "mul-xin-exp-result" .b128 .base
    let yinExpResult ← addCommitted "mul-yin-exp-result" .b128 .base
    let zoutLowExpResult ← addCommitted "mul-zout-low-exp-result" .b128 .base
    let zoutHighExpResult ← addCommitted "mul-zout-high-exp-result" .b128 .base
    let zoutBits ← Array.range (2 * outSize) |>.mapM (addCommitted s!"mul-zout-bit-{·}" .b1 .base)

    let xin0 := xinBits[0]!
    let yin0 := yinBits[0]!
    let zout0 := zoutBits[0]!
    assertZero "mul-bit0" $ xin0 * yin0 - zout0

    let yin := yinExpResult
    let low := zoutLowExpResult
    let high := zoutHighExpResult
    assertZero "mul-yin-zout-low-high" $ low * high - yin

    let zoutLow := zoutBits.extract (stop := outSize)
    let zoutHigh := zoutBits.extract (start := outSize)

    assertStaticExp xinBits xinExpResult B128_MULT_GEN .b128
    assertDynamicExp yinBits yinExpResult xinExpResult
    assertStaticExp zoutLow zoutLowExpResult B128_MULT_GEN .b128
    assertStaticExp zoutHigh zoutHighExpResult B128GenPow2To64 .b128

    pure (xinExpResult, yinExpResult, zoutLowExpResult, zoutHighExpResult, zoutBits)

structure MemoryColumns where
  values : Array OracleIdx
  multiplicity : OracleIdx

def synthesizeMemory (channelId : ChannelId) (width : Nat) : SynthM MemoryColumns := do
  let address ← addTransparent s!"mem-{width}-address" .incremental .base
  let values ← Array.range width |>.mapM (addCommitted s!"mem-{width}-value-{·}" .b64 .base)
  let multiplicity ← addCommitted s!"mem-{width}-multiplicity" .b64 .base
  let args := #[address] ++ values
  provide channelId multiplicity args
  pure { values, multiplicity }

structure AiurCircuits where
  funcs : Array (CircuitModule × Columns)
  add : CircuitModule × AddColumns
  mul : CircuitModule × MulColumns
  mem : Array (CircuitModule × MemoryColumns)
  gad : Array (CircuitModule × Array OracleIdx)

def AiurCircuits.circuitModules (self : AiurCircuits) : Array CircuitModule :=
  self.funcs.map (·.fst)
    ++ #[self.add.fst, self.mul.fst]
    ++ self.mem.map (·.fst)
    ++ self.gad.map (·.fst)

def synthesize (toplevel : Bytecode.Toplevel) : AiurCircuits × Array ChannelId :=
  let (funcChannels, channelAllocator) := ChannelAllocator.init.nextN toplevel.functions.size
  let (addChannel, channelAllocator) := channelAllocator.next
  let (mulChannel, channelAllocator) := channelAllocator.next
  let (memChannels, channelAllocator) := channelAllocator.nextN toplevel.memWidths.size
  let (gadgetChannels, _) := channelAllocator.nextN toplevel.gadgets.size
  let memChannelsMap := ⟨toplevel.memWidths.zip memChannels⟩
  let aiurChannels := ⟨funcChannels, addChannel, mulChannel, memChannelsMap, gadgetChannels⟩
  let funcsModules := toplevel.functions.zip toplevel.layouts |>.zipIdx.map
    fun ((function, layout), functionIdx) => synthesizeM functionIdx.toUSize
      (synthesizeFunction functionIdx function layout aiurChannels)
  let numFunctions := toplevel.functions.size.toUSize
  let addModule := synthesizeM numFunctions (synthesizeAdd addChannel)
  let mulModule := synthesizeM (numFunctions + 1) (synthesizeMul mulChannel)
  let memIdStart := numFunctions + 2
  let memModules := memChannelsMap.pairs.zipIdx.map
    fun ((width, channelId), memIdx) =>
      synthesizeM (memIdStart + memIdx.toUSize) (synthesizeMemory channelId width)
  let gadgetIdStart := memIdStart + memModules.size.toUSize
  let gadgetsModules := toplevel.gadgets.zip gadgetChannels |>.zipIdx.map
    fun ((gadget, channelId), gadgetIdx) =>
      let circuitModule := CircuitModule.new $ gadgetIdStart + gadgetIdx.toUSize
      let (circuitModule, oracles) := gadget.synthesize channelId circuitModule
      (circuitModule.freezeOracles, oracles)
  (⟨funcsModules, addModule, mulModule, memModules, gadgetsModules⟩, aiurChannels.func)

end Aiur.Circuit
