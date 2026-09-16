import Compilatrix.Ixon.V3.Const

namespace Compilatrix.Ixon.V3

/-- Each counted field has an inclusive 4096-entry limit and must fit
the remaining input before allocation. -/
def getArrayN (getOne : GetM α) (count : Nat) : GetM (Array α) := do
  let mut result := #[]
  for _ in [:count] do result := result.push (← getOne)
  return result

def getCountedArray (getOne : GetM α) : GetM (Array α) := do
  let count ← checkedCount (← getTag0).size 4096
  getArrayN getOne count

def getDefinition : GetM Definition :=
  (fun raw =>
    ⟨raw.1.1, raw.1.2, raw.2.1.size, raw.2.2.1, raw.2.2.2⟩) <$>
    getPairM getDefinitionMode
      (getPairM getTag0 (getPairM getExpr getExpr))

def getRecursorRule : GetM RecursorRule :=
  (fun raw => ⟨raw.1.size, raw.2⟩) <$> getPairM getTag0 getExpr

def getRecursor : GetM Recursor :=
  (fun raw =>
    ⟨raw.1.1, raw.1.2, raw.2.1.size, raw.2.2.1.size,
      raw.2.2.2.1.size, raw.2.2.2.2.1.size, raw.2.2.2.2.2.1.size,
      raw.2.2.2.2.2.2.1, raw.2.2.2.2.2.2.2⟩) <$>
    getPairM getRecursorMode
      (getPairM getTag0
        (getPairM getTag0
          (getPairM getTag0
            (getPairM getTag0
              (getPairM getTag0
                (getPairM getExpr (getCountedArray getRecursorRule)))))))

def getAxiom : GetM Axiom :=
  (fun raw => ⟨raw.1, raw.2.1.size, raw.2.2⟩) <$>
    getPairM (getStrictBool "getAxiom") (getPairM getTag0 getExpr)

def getQuotient : GetM Quotient :=
  (fun raw => ⟨raw.1, raw.2.1.size, raw.2.2⟩) <$>
    getPairM getQuotKind (getPairM getTag0 getExpr)

def getConstructor : GetM Constructor :=
  (fun raw =>
    ⟨raw.1, raw.2.1.size, raw.2.2.1.size, raw.2.2.2.1.size,
      raw.2.2.2.2.1.size, raw.2.2.2.2.2⟩) <$>
    getPairM (getStrictBool "getConstructor")
      (getPairM getTag0
        (getPairM getTag0 (getPairM getTag0 (getPairM getTag0 getExpr))))

def getInductive : GetM Inductive :=
  (fun raw =>
    ⟨raw.1, raw.2.1.size, raw.2.2.1.size, raw.2.2.2.1.size,
      raw.2.2.2.2.1, raw.2.2.2.2.2⟩) <$>
    getPairM (getStrictBool "getInductive")
      (getPairM getTag0
        (getPairM getTag0
          (getPairM getTag0
            (getPairM getExpr (getCountedArray getConstructor)))))

def getInductiveProj : GetM InductiveProj :=
  (fun raw => ⟨raw.1.size, raw.2⟩) <$>
    getPairM getTag0 Serialize.get

def getConstructorProj : GetM ConstructorProj :=
  (fun raw => ⟨raw.1.size, raw.2.1.size, raw.2.2⟩) <$>
    getPairM getTag0 (getPairM getTag0 Serialize.get)

def getRecursorProj : GetM RecursorProj :=
  (fun raw => ⟨raw.1.size, raw.2⟩) <$>
    getPairM getTag0 Serialize.get

def getDefinitionProj : GetM DefinitionProj :=
  (fun raw => ⟨raw.1.size, raw.2⟩) <$>
    getPairM getTag0 Serialize.get

def getMutConstTag (tag : UInt8) : GetM MutConst := do
  match tag with
  | 0 => .defn <$> getDefinition
  | 1 => .indc <$> getInductive
  | 2 => .recr <$> getRecursor
  | t => throw s!"getMutConst: invalid tag {t}"

def getMutConst : GetM MutConst := do
  getMutConstTag (← getU8)

def getConstantInfoVariant (variant : UInt64) : GetM ConstantInfo := do
  if variant == ConstantInfo.CONST_DEFN then .defn <$> getDefinition
  else if variant == ConstantInfo.CONST_RECR then .recr <$> getRecursor
  else if variant == ConstantInfo.CONST_AXIO then .axio <$> getAxiom
  else if variant == ConstantInfo.CONST_QUOT then .quot <$> getQuotient
  else if variant == ConstantInfo.CONST_CPRJ then .cPrj <$> getConstructorProj
  else if variant == ConstantInfo.CONST_RPRJ then .rPrj <$> getRecursorProj
  else if variant == ConstantInfo.CONST_IPRJ then .iPrj <$> getInductiveProj
  else if variant == ConstantInfo.CONST_DPRJ then .dPrj <$> getDefinitionProj
  else throw s!"getConstantInfo: invalid variant {variant}"

def getConstantInfoTag (tag : Tag4) : GetM ConstantInfo := do
  if tag.flag == Constant.FLAG_MUTS then
    return .muts (← getArrayN getMutConst (← checkedCount tag.size 4096))
  else if tag.flag == Constant.FLAG then
    getConstantInfoVariant tag.size
  else
    throw s!"getConstantInfo: invalid flag {tag.flag}"

def getConstantInfo : GetM ConstantInfo := do
  getConstantInfoTag (← getTag4)

instance : Serialize ConstantInfo where
  put := putConstantInfo
  get := getConstantInfo

def getConstant : GetM Constant := do
  let info ← getConstantInfo
  let sharing ← getCountedArray getExpr
  let refs ← getCountedArray (Serialize.get : GetM Address)
  let univs ← getCountedArray (do return (← getUnivFuel 256).value)
  return ⟨info, sharing, refs, univs⟩

instance : Serialize Constant where
  put := putConstant
  get := getConstant

structure DecodedConstant (bytes : ByteArray) where
  value : Constant
  canonical : constantBytes value = bytes

def decodeConstant (bytes : ByteArray) (maxBytes : Nat := 1024 * 1024) :
    Except String (DecodedConstant bytes) := do
  if bytes.size > maxBytes then throw "ixon-v3: constant byte budget exceeded"
  let value ← runGet getConstant bytes
  if canonical : constantBytes value = bytes then return ⟨value, canonical⟩
  else throw "ixon-v3: noncanonical constant"

end Compilatrix.Ixon.V3
