import CompilatrixTests.Support
import Compilatrix.Ixon.Sharing
import Compilatrix.Ixon.DecodeCheck
import Compilatrix.Ixon.Merkle
import Compilatrix.Ixon.CatalogIO
import Compilatrix.Coverage.StdContact

namespace CompilatrixTests

open Compilatrix.Ixon

namespace IxRebaseline

def sourceTree : String := "c09cfe3df1ee6ff92009672cc9077b4b7e2db63a"
def wireFormat : String := "ixon-v2"

def sampleAxiomBytes : ByteArray := ByteArray.mk #[210, 0, 1, 3, 0, 0, 1, 0]

def sampleAxiomAddress : List Nat :=
  [175, 190, 20, 2, 194, 88, 190, 182, 79, 114, 28, 108, 112, 136,
   43, 71, 254, 192, 235, 145, 134, 231, 227, 179, 11, 181, 74, 208,
   29, 62, 109, 135]

def goldenV2Bytes : ByteArray := ByteArray.mk #[
  208, 1, 128, 128, 148, 0, 0, 5, 8, 31, 2, 8, 32, 7, 8, 128,
  3, 132, 0, 0, 1, 8, 31, 2, 8, 32, 3, 8, 128, 120, 8, 40,
  8, 0, 0, 1, 2, 3, 4, 0, 1, 2, 19, 18, 17, 16, 176, 176,
  80, 9, 0, 1, 1, 114, 49, 0, 4, 65, 0, 16, 16, 1, 171, 171,
  171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171,
  171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171,
  171, 171, 5, 0, 1, 0, 64, 192, 1, 193, 128, 194, 64, 0, 195, 225,
  0, 1]

def goldenV2Address : List Nat :=
  [238, 16, 204, 23, 76, 138, 70, 122, 24, 3, 187, 143, 106, 4,
   178, 63, 183, 235, 146, 24, 170, 118, 219, 68, 149, 59, 34, 171,
   73, 90, 205, 116]

structure SharingCapture where
  name : String
  input : ByteArray
  output : ByteArray

def sharingCaptures : List SharingCapture := [
  { name := "simple"
    input := ByteArray.mk #[1, 148, 7, 32, 0, 7, 32, 0, 7, 32, 0, 7, 32, 0, 1]
    output := ByteArray.mk #[1, 148, 7, 176, 7, 176, 7, 176, 7, 176, 1, 1, 32, 0] },
  { name := "content-hash"
    input := ByteArray.mk #[3, 145, 7, 32, 0, 0, 145, 7, 32, 0, 1,
      145, 7, 32, 0, 2]
    output := ByteArray.mk #[3, 145, 7, 176, 0, 145, 7, 176, 1,
      145, 7, 176, 2, 1, 32, 0] },
  { name := "recursor"
    input := ByteArray.mk #[4, 149, 7, 145, 7, 32, 0, 1, 7, 113, 17, 32,
      1, 7, 113, 18, 32, 2, 7, 113, 19, 32, 3, 7, 32, 0, 113, 17, 16,
      17, 18, 19]
    output := ByteArray.mk #[4, 149, 7, 145, 7, 32, 0, 1, 7, 113, 17,
      32, 1, 7, 113, 18, 32, 2, 7, 113, 19, 32, 3, 7, 32, 0, 113, 17,
      16, 17, 18, 19, 0] },
  { name := "forall-imp-sharing"
    input := ByteArray.mk #[2, 146, 7, 19, 7, 113, 18, 17, 113, 18, 16,
      146, 7, 19, 7, 113, 18, 16, 113, 18, 17]
    output := ByteArray.mk #[2, 146, 7, 19, 7, 176, 177, 146, 7, 19, 7,
      177, 176, 2, 113, 18, 17, 113, 18, 16] },
  { name := "forall-imp-real"
    input := ByteArray.mk #[2, 150, 7, 0, 7, 145, 7, 16, 1, 7, 145, 7,
      17, 1, 7, 146, 7, 18, 7, 113, 18, 16, 113, 18, 17, 7, 145, 7, 19,
      113, 19, 16, 7, 20, 113, 19, 16, 134, 3, 0, 3, 145, 7, 16, 1, 3,
      145, 7, 17, 1, 3, 146, 7, 18, 7, 113, 18, 16, 113, 18, 17, 3, 145,
      7, 19, 113, 19, 16, 3, 20, 114, 18, 16, 113, 17, 16]
    output := ByteArray.mk #[2, 150, 7, 0, 7, 183, 7, 179, 7, 182, 7,
      178, 7, 20, 177, 134, 3, 0, 3, 183, 3, 179, 3, 182, 3, 178, 3, 20,
      113, 180, 113, 17, 16, 8, 113, 18, 17, 113, 19, 16, 145, 7, 19,
      177, 145, 7, 17, 1, 113, 18, 16, 145, 7, 180, 176, 145, 7, 18,
      181, 145, 7, 16, 1] },
  { name := "flip"
    input := ByteArray.mk #[2, 150, 7, 0, 7, 1, 7, 2, 7, 146, 7, 18, 7,
      18, 18, 7, 18, 7, 20, 19, 134, 3, 0, 3, 1, 3, 2, 3, 146, 7, 18,
      7, 18, 18, 3, 18, 3, 20, 114, 18, 16, 17]
    output := ByteArray.mk #[2, 150, 7, 0, 7, 1, 7, 2, 7, 177, 7, 18, 7,
      20, 19, 134, 3, 0, 3, 1, 3, 2, 3, 177, 3, 18, 3, 20, 114, 18, 16,
      17, 2, 145, 7, 18, 18, 145, 7, 18, 176] }
]

def sharingCapture? (name : String) : Option SharingCapture :=
  sharingCaptures.find? fun capture => capture.name == name

end IxRebaseline

namespace SharingPolicy

def all (domain body : Expr) : Expr :=
  .all .many .shared domain body

def lam (domain body : Expr) : Expr :=
  .lam .many domain body

def simple : Array Expr :=
  let t := Expr.ref 0 #[]
  let e1 := all t (.sort 1)
  let e2 := all t e1
  let e3 := all t e2
  #[all t e3]

def contentHash : Array Expr := #[
  all (.ref 0 #[]) (.sort 0),
  all (.ref 0 #[]) (.sort 1),
  all (.ref 0 #[]) (.sort 2)]

def recursor : Array Expr :=
  let tRef := Expr.ref 0 #[]
  let target := all tRef (.app (.var 1) (.var 0))
  let withMinor3 := all (.app (.var 3) (.ref 3 #[])) target
  let withMinor2 := all (.app (.var 2) (.ref 2 #[])) withMinor3
  let withMinor1 := all (.app (.var 1) (.ref 1 #[])) withMinor2
  let motiveType := all tRef (.sort 1)
  #[all motiveType withMinor1, .var 1, .var 2, .var 3]

def forallImpReal : Array Expr :=
  let typ := all (.sort 0)
    (all (all (.var 0) (.sort 1))
      (all (all (.var 1) (.sort 1))
        (all
          (all (.var 2)
            (all (.app (.var 2) (.var 0))
                 (.app (.var 2) (.var 1))))
          (all
            (all (.var 3) (.app (.var 3) (.var 0)))
            (all (.var 4) (.app (.var 3) (.var 0)))))))
  let value := lam (.sort 0)
    (lam (all (.var 0) (.sort 1))
      (lam (all (.var 1) (.sort 1))
        (lam
          (all (.var 2)
            (all (.app (.var 2) (.var 0))
                 (.app (.var 2) (.var 1))))
          (lam
            (all (.var 3) (.app (.var 3) (.var 0)))
            (lam (.var 4)
              (.app
                (.app (.var 2) (.var 0))
                (.app (.var 1) (.var 0))))))))
  #[typ, value]

def forallImpSharing : Array Expr :=
  let app21 := Expr.app (.var 2) (.var 1)
  let app20 := Expr.app (.var 2) (.var 0)
  let e1 := all app21 app20
  let e2 := all app20 app21
  #[all (.var 3) e1, all (.var 3) e2]

def flipCase : Array Expr :=
  let innerAll := all (.var 2) (.var 2)
  let funcType := all (.var 2) innerAll
  let resultType := all (.var 2) (all (.var 4) (.var 3))
  let typ := all (.sort 0)
    (all (.sort 1)
      (all (.sort 2) (all funcType resultType)))
  let body := Expr.app (.app (.var 2) (.var 0)) (.var 1)
  let value := lam (.sort 0)
    (lam (.sort 1)
      (lam (.sort 2)
        (lam funcType
          (lam (.var 2) (lam (.var 4) body)))))
  #[typ, value]

def simpleOutput : Sharing.Compression :=
  { bodies := #[all (.share 0)
      (all (.share 0) (all (.share 0) (all (.share 0) (.sort 1))))]
    table := #[.ref 0 #[]] }

def contentHashOutput : Sharing.Compression :=
  { bodies := #[
      all (.share 0) (.sort 0),
      all (.share 0) (.sort 1),
      all (.share 0) (.sort 2)]
    table := #[.ref 0 #[]] }

def recursorOutput : Sharing.Compression :=
  { bodies := recursor, table := #[] }

def forallImpSharingOutput : Sharing.Compression :=
  { bodies := #[
      all (.var 3) (all (.share 0) (.share 1)),
      all (.var 3) (all (.share 1) (.share 0))]
    table := #[
      .app (.var 2) (.var 1),
      .app (.var 2) (.var 0)] }

/-- Exact eight-entry output captured from ix's v2 compressor at
`Sharing.ixParityRevision`. The local exact-byte audit intentionally does not
retain this nested table. -/
def ixForallImpRealOutput : Sharing.Compression :=
  { bodies := #[
      all (.sort 0)
        (all (.share 7)
          (all (.share 3)
            (all (.share 6)
              (all (.share 2) (all (.var 4) (.share 1)))))),
      lam (.sort 0)
        (lam (.share 7)
          (lam (.share 3)
            (lam (.share 6)
              (lam (.share 2)
                (lam (.var 4)
                  (.app (.share 4) (.app (.var 1) (.var 0))))))))]
    table := #[
      .app (.var 2) (.var 1),
      .app (.var 3) (.var 0),
      all (.var 3) (.share 1),
      all (.var 1) (.sort 1),
      .app (.var 2) (.var 0),
      all (.share 4) (.share 0),
      all (.var 2) (.share 5),
      all (.var 0) (.sort 1)] }

/-- Audited v2 output for `forall_imp`: three stale nested entries disappear,
and the surviving mode-bearing representatives have v2 Merkle order. -/
def v2ForallImpRealOutput : Sharing.Compression :=
  { bodies := #[
      all (.sort 0)
        (all (.share 4)
          (all (.share 2)
            (all (.share 3)
              (all (.share 1) (all (.var 4) (.share 0)))))),
      lam (.sort 0)
        (lam (.share 4)
          (lam (.share 2)
            (lam (.share 3)
              (lam (.share 1)
                (lam (.var 4)
                  (.app (.app (.var 2) (.var 0))
                    (.app (.var 1) (.var 0))))))))]
    table := #[
      .app (.var 3) (.var 0),
      all (.var 3) (.share 0),
      all (.var 1) (.sort 1),
      all (.var 2)
        (all (.app (.var 2) (.var 0)) (.app (.var 2) (.var 1))),
      all (.var 0) (.sort 1)] }

/-- Exact two-entry output captured from ix's v2 compressor at
`Sharing.ixParityRevision`. -/
def ixFlipOutput : Sharing.Compression :=
  { bodies := #[
      all (.sort 0)
        (all (.sort 1)
          (all (.sort 2)
            (all (.share 1)
              (all (.var 2) (all (.var 4) (.var 3)))))),
      lam (.sort 0)
        (lam (.sort 1)
          (lam (.sort 2)
            (lam (.share 1)
              (lam (.var 2)
                (lam (.var 4)
                  (.app (.app (.var 2) (.var 0)) (.var 1)))))))]
    table := #[
      all (.var 2) (.var 2),
      all (.var 2) (.share 0)] }

/-- V2 keeps only the maximal two-binder telescope; sharing its inner suffix
would split the canonical `all` run. -/
def v2FlipOutput : Sharing.Compression :=
  { bodies := #[
      all (.sort 0)
        (all (.sort 1)
          (all (.sort 2)
            (all (.share 0)
              (all (.var 2) (all (.var 4) (.var 3)))))),
      lam (.sort 0)
        (lam (.sort 1)
          (lam (.sort 2)
            (lam (.share 0)
              (lam (.var 2)
                (lam (.var 4)
                  (.app (.app (.var 2) (.var 0)) (.var 1)))))))]
    table := #[all (.var 2) (all (.var 2) (.var 2))] }

inductive Relation where
  | exactParity
  | intentionalV2Delta
  deriving BEq, Repr

structure Case where
  name : String
  input : Array Expr
  ixOutput : Sharing.Compression
  v2Output : Sharing.Compression
  relation : Relation

def cases : Array Case := #[
  ⟨"simple", simple, simpleOutput, simpleOutput, .exactParity⟩,
  ⟨"content-hash", contentHash, contentHashOutput, contentHashOutput,
    .exactParity⟩,
  ⟨"recursor", recursor, recursorOutput, recursorOutput, .exactParity⟩,
  ⟨"forall-imp-sharing", forallImpSharing, forallImpSharingOutput,
    forallImpSharingOutput, .exactParity⟩,
  ⟨"forall-imp-real", forallImpReal, ixForallImpRealOutput,
    v2ForallImpRealOutput, .intentionalV2Delta⟩,
  ⟨"flip", flipCase, ixFlipOutput, v2FlipOutput, .intentionalV2Delta⟩]

def putExprArray (exprs : Array Expr) : PutM Unit := do
  putTag0 ⟨exprs.size.toUInt64⟩
  for e in exprs do putExpr e

def putCompression (c : Sharing.Compression) : PutM Unit := do
  putExprArray c.bodies
  putExprArray c.table

/-- Canonically framed transcript of the inputs, pinned ix vectors, intended
v2 vectors, and parity/delta classification. -/
def transcript : ByteArray := runPut do
  putTag0 ⟨cases.size.toUInt64⟩
  for c in cases do
    putU8 (match c.relation with | .exactParity => 0 | .intentionalV2Delta => 1)
    putExprArray c.input
    putCompression c.ixOutput
    putCompression c.v2Output

def fingerprint : Address := .blake3 transcript

/-- `19aa227e6be89cbabef37366bdc3a48fcf1d8f856892054511ae6b6fcf1db4ce`.
Bump only after reviewing both the pinned ix vector and the intended v2
output for every case. -/
def expectedFingerprint : List Nat :=
  [25, 170, 34, 126, 107, 232, 156, 186,
   190, 243, 115, 102, 189, 195, 164, 143,
   207, 29, 143, 133, 104, 146, 5, 69,
   17, 174, 107, 111, 207, 29, 180, 206]

end SharingPolicy

namespace DecodeCheckFixtures

open DecodeCheck

def address : Address := Address.replicate 0x5a

def axiomConstant (lvls : UInt64) (typ : Expr) (refs : Array Address := #[])
    (univs : Array Univ := #[]) (sharing : Array Expr := #[]) : Constant :=
  { info := .axio { isUnsafe := false, lvls, typ }
    sharing, refs, univs }

def validAxiom : Constant :=
  axiomConstant 1 (.app (.ref 0 #[0]) (.sort 0)) #[address] #[.var 0]

def validShared : Constant :=
  axiomConstant 0 (.app (.share 0) (.share 0)) #[] #[] #[.var 0]

def validUniverse : Constant :=
  axiomConstant 1 (.sort 0) #[]
    #[.imax (.succ (.var 0)) (.max .zero (.var 0))]

def validDefinition : Constant :=
  { info := .defn
      { kind := .thm, safety := .safe, lvls := 0
        typ := .all .many .shared (.var 0) (.var 0)
        value := .lam .many (.var 0)
          (.letE false (.var 0) (.var 0) (.var 0)) }
    sharing := #[], refs := #[], univs := #[] }

def validMutualRecur : Constant :=
  { info := .muts #[.defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .var 0, value := .recur 0 #[] }]
    sharing := #[], refs := #[], univs := #[] }

def invalidMutualRecur : Constant :=
  { validMutualRecur with info := .muts #[.defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .var 0, value := .recur 1 #[] }] }

def recursor (typ : Expr) (rules : Array RecursorRule) : Constant :=
  { info := .recr
      { k := false, isUnsafe := false, lvls := 0
        params := 0, indices := 0, motives := 0, minors := 0
        typ, rules }
    sharing := #[], refs := #[], univs := #[] }

def validRecursor : Constant :=
  recursor
    (.all .many .shared (.var 0) (.var 0))
    #[{ fields := 1, rhs := .lam .many (.var 0) (.var 0) }]

def invalidRecursorType : Constant := recursor (.var 0) #[]

def invalidRecursorRule : Constant :=
  recursor
    (.all .many .shared (.var 0) (.var 0))
    #[{ fields := 1, rhs := .var 0 }]

def allN : Nat → Expr → Expr
  | 0, body => body
  | count + 1, body => .all .many .shared (.var 0) (allN count body)

def lamN : Nat → Expr → Expr
  | 0, body => body
  | count + 1, body => .lam .many (.var 0) (lamN count body)

def validRichRecursor : Constant :=
  { info := .recr
      { k := true, isUnsafe := true, lvls := 0
        params := 1, indices := 2, motives := 3, minors := 4
        typ := allN 11 (.var 0)
        rules := #[{ fields := 5, rhs := lamN 13 (.var 0) }] }
    sharing := #[], refs := #[], univs := #[] }

def validInductiveBlock : Constant :=
  { info := .muts #[.indc
      { isUnsafe := true, lvls := 0, params := 2, indices := 3
        typ := .var 0
        ctors := #[
          { isUnsafe := false, lvls := 0, cidx := 7, params := 2,
            fields := 5, typ := .recur 0 #[] }] }]
    sharing := #[], refs := #[], univs := #[] }

def validQuotient : Constant :=
  { info := .quot { kind := .ind, lvls := 0, typ := .var 0 }
    sharing := #[], refs := #[], univs := #[] }

def validProjections : Array Constant := #[
  { info := .cPrj { idx := 1, cidx := 2, block := address }
    sharing := #[], refs := #[], univs := #[] },
  { info := .rPrj { idx := 3, block := address }
    sharing := #[], refs := #[], univs := #[] },
  { info := .iPrj { idx := 4, block := address }
    sharing := #[], refs := #[], univs := #[] },
  { info := .dPrj { idx := 5, block := address }
    sharing := #[], refs := #[], univs := #[] }
]

/-- A positive corpus spanning every constant-info variant exercised by the
checked decoder.  The fuzz harness mutates the exact encodings of these
values, so it always contains successful inputs as well as malformed ones. -/
def validConstants : Array Constant := #[
  validAxiom,
  validShared,
  validUniverse,
  validDefinition,
  validMutualRecur,
  validRecursor,
  validRichRecursor,
  validInductiveBlock,
  validQuotient
] ++ validProjections

structure Case where
  name : String
  constant : Constant
  expected : Except Error Constant

def axiomSite : Site := ⟨none, .axiomType⟩

def cases : Array Case := #[
  ⟨"last valid ref/universe index", validAxiom, .ok validAxiom⟩,
  ⟨"sharing is checked before inlining", validShared, .ok validShared⟩,
  ⟨"recursive universe forms", validUniverse, .ok validUniverse⟩,
  ⟨"definition and let forms", validDefinition, .ok validDefinition⟩,
  ⟨"last valid mutual self index", validMutualRecur, .ok validMutualRecur⟩,
  ⟨"valid recursor slicing counts", validRecursor, .ok validRecursor⟩,
  ⟨"distinct recursor metadata fields", validRichRecursor,
    .ok validRichRecursor⟩,
  ⟨"inductive/constructor metadata", validInductiveBlock,
    .ok validInductiveBlock⟩,
  ⟨"quotient variant", validQuotient, .ok validQuotient⟩,
  ⟨"constant ref index", axiomConstant 0 (.ref 1 #[]) #[address],
    .error (.refIndex axiomSite .constant 1 1)⟩,
  ⟨"string ref index", axiomConstant 0 (.str 1) #[address],
    .error (.refIndex axiomSite .string 1 1)⟩,
  ⟨"natural ref index", axiomConstant 0 (.nat 1) #[address],
    .error (.refIndex axiomSite .natural 1 1)⟩,
  ⟨"projection type-ref index", axiomConstant 0 (.prj 1 0 (.var 0)) #[address],
    .error (.refIndex axiomSite .projectionType 1 1)⟩,
  ⟨"sort universe index", axiomConstant 0 (.sort 1) #[] #[.zero],
    .error (.universeIndex axiomSite 1 1)⟩,
  ⟨"reference universe-argument index", axiomConstant 0 (.ref 0 #[1])
      #[address] #[.zero],
    .error (.universeIndex axiomSite 1 1)⟩,
  ⟨"universe variable scope", axiomConstant 1 (.sort 0) #[] #[.var 1],
    .error (.universeVariable axiomSite 1 1)⟩,
  ⟨"mutual self index", invalidMutualRecur,
    .error (.recurIndex ⟨some 0, .definitionValue⟩ 1 1)⟩,
  ⟨"recursor type arity", invalidRecursorType,
    .error (.recursorTypeArity ⟨none, .recursorType⟩ 1 0)⟩,
  ⟨"recursor rule arity", invalidRecursorRule,
    .error (.recursorRuleArity ⟨none, .recursorRule 0⟩ 1 0)⟩
]

def allCases : Array Case := cases ++ validProjections.map fun constant =>
  ⟨"projection variant", constant, .ok constant⟩

def resultEq : Except Error Constant → Except Error Constant → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

def hostileAppCountBytes (count : Nat) : ByteArray := runPut do
  putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩
  putU8 0
  putTag0 ⟨0⟩
  putTag4 ⟨Expr.FLAG_APP, count.toUInt64⟩

def hostileExpressionDepthBytes (depth : Nat) : ByteArray := runPut do
  putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩
  putU8 0
  putTag0 ⟨0⟩
  for _ in [:depth] do
    putTag4 ⟨Expr.FLAG_PRJ, 0⟩
    putTag0 ⟨0⟩

def hostileReferenceCountBytes (count : Nat) : ByteArray := runPut do
  putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩
  putU8 0
  putTag0 ⟨0⟩
  putTag4 ⟨Expr.FLAG_VAR, 0⟩
  putTag0 ⟨0⟩
  putTag0 ⟨count.toUInt64⟩

def hostileUniverseDepthBytes (depth : Nat) : ByteArray := runPut do
  putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩
  putU8 0
  putTag0 ⟨0⟩
  putTag4 ⟨Expr.FLAG_SORT, 0⟩
  putTag0 ⟨0⟩
  putTag0 ⟨0⟩
  putTag0 ⟨1⟩
  for _ in [:depth] do
    putTag2 ⟨Univ.FLAG_MAX, 0⟩

structure ResourceCase where
  name : String
  bytes : ByteArray
  expected : Error

def resourceCases : Array ResourceCase :=
  let limits := DecodeCheck.defaultLimits
  let tooLong := limits.maxSequenceLength + 1
  #[
    ⟨"flat application count",
      hostileAppCountBytes tooLong,
      .sequenceTooLong .applicationSpine tooLong limits.maxSequenceLength⟩,
    ⟨"flat reference-table count",
      hostileReferenceCountBytes tooLong,
      .sequenceTooLong .references tooLong limits.maxSequenceLength⟩,
    ⟨"expression nesting",
      hostileExpressionDepthBytes limits.maxExpressionDepth,
      .expressionDepth limits.maxExpressionDepth⟩,
    ⟨"universe nesting",
      hostileUniverseDepthBytes limits.maxUniverseDepth,
      .universeDepth limits.maxUniverseDepth⟩
  ]

end DecodeCheckFixtures

namespace DecodeFuzz

inductive Outcome where
  | rejected
  | accepted
  | roundTripFailure
deriving BEq

def classify (bytes : ByteArray) : Outcome :=
  match DecodeCheck.decodeChecked bytes with
  | .error _ => .rejected
  | .ok constant =>
    if ser constant != bytes then
      .roundTripFailure
    else
      match DecodeCheck.encodeChecked constant with
      | .ok encoded =>
        if encoded == bytes then .accepted else .roundTripFailure
      | .error _ => .roundTripFailure

/-- Original bytes, every strict prefix, every single-byte low-bit flip, and
two trailing-byte mutations. -/
def mutations (bytes : ByteArray) : Array ByteArray :=
  let prefixes := (Array.range bytes.size).map fun size =>
    bytes.extract 0 size
  let flips := (Array.range bytes.size).map fun index =>
    bytes.set! index (bytes.get! index ^^^ (1 : UInt8))
  #[bytes] ++ prefixes ++ flips ++ #[bytes.push 0, bytes.push 0xff]

def nextState (state : UInt64) : UInt64 :=
  state * 6364136223846793005 + 1442695040888963407

def randomBytes (seed : UInt64) (size : Nat) : ByteArray × UInt64 := Id.run do
  let mut state := seed
  let mut bytes : ByteArray := ByteArray.empty
  for _ in [:size] do
    state := nextState state
    bytes := bytes.push state.toUInt8
  return (bytes, state)

def randomCaseCount : Nat := 4096
def maxRandomBytes : Nat := 256

end DecodeFuzz

namespace WorkBudgetFixtures

/-- A tiny valid backward sharing chain whose stored size is linear while its
fully inlined body size doubles at each table entry. -/
def doublingTable (steps : Nat) : Array Expr := Id.run do
  let mut table : Array Expr := #[.sort 0]
  for _ in [:steps] do
    let previous := table.size - 1
    table := table.push (.app (.share previous.toUInt64)
      (.share previous.toUInt64))
  return table

def doublingBodies (table : Array Expr) : Array Expr :=
  let final := table.size - 1
  #[.app (.share final.toUInt64) (.share final.toUInt64)]

end WorkBudgetFixtures

namespace MerkleFixture

/-! Independent ix artifact capture: the 19 member env roots and stored
`members_root` from `Palomar.ix/palomar.ixc/manifest` on 2026-08-25.  Keeping
the leaves as well as the result prevents a local manifest writer and reader
from masking the same Merkle drift. -/

def memberRoots : Array Address := #[
  Address.ofFn fun i => (#[34, 234, 228, 113, 117, 211, 236, 250, 12, 20, 221, 253, 121, 13, 252, 195, 27, 240, 149, 55, 73, 7, 144, 92, 155, 122, 46, 147, 113, 226, 5, 97])[i.val]!,
  Address.ofFn fun i => (#[116, 97, 231, 128, 84, 148, 77, 83, 202, 126, 202, 150, 124, 0, 176, 235, 222, 183, 166, 224, 113, 238, 25, 56, 13, 65, 96, 181, 182, 57, 119, 229])[i.val]!,
  Address.ofFn fun i => (#[178, 247, 193, 242, 219, 45, 196, 228, 122, 118, 69, 100, 245, 136, 74, 92, 136, 86, 221, 152, 221, 79, 234, 103, 78, 74, 238, 176, 138, 27, 92, 106])[i.val]!,
  Address.ofFn fun i => (#[197, 210, 150, 170, 96, 111, 211, 193, 207, 253, 183, 138, 222, 220, 222, 247, 164, 30, 184, 199, 158, 0, 192, 87, 18, 208, 78, 245, 30, 161, 4, 208])[i.val]!,
  Address.ofFn fun i => (#[113, 24, 108, 74, 6, 70, 166, 135, 172, 152, 118, 176, 59, 121, 135, 128, 234, 238, 153, 16, 145, 9, 141, 42, 37, 45, 197, 2, 254, 60, 76, 14])[i.val]!,
  Address.ofFn fun i => (#[67, 233, 29, 165, 155, 181, 250, 65, 95, 83, 213, 85, 21, 66, 190, 24, 249, 255, 96, 99, 118, 74, 59, 235, 185, 33, 23, 128, 50, 60, 161, 23])[i.val]!,
  Address.ofFn fun i => (#[214, 146, 214, 62, 98, 89, 36, 231, 71, 40, 100, 222, 168, 79, 138, 76, 235, 220, 215, 112, 83, 235, 245, 15, 114, 217, 214, 181, 22, 81, 143, 80])[i.val]!,
  Address.ofFn fun i => (#[234, 135, 20, 248, 51, 210, 152, 133, 138, 210, 227, 25, 114, 172, 242, 166, 193, 1, 80, 143, 221, 170, 160, 94, 109, 29, 140, 218, 161, 149, 55, 90])[i.val]!,
  Address.ofFn fun i => (#[15, 124, 132, 78, 214, 243, 93, 39, 51, 53, 88, 135, 122, 178, 188, 204, 21, 225, 138, 112, 175, 10, 166, 85, 198, 167, 171, 38, 142, 182, 33, 247])[i.val]!,
  Address.ofFn fun i => (#[104, 43, 172, 14, 231, 2, 233, 90, 35, 84, 74, 53, 139, 125, 192, 24, 248, 243, 12, 41, 244, 76, 41, 94, 140, 68, 19, 232, 161, 228, 72, 195])[i.val]!,
  Address.ofFn fun i => (#[210, 7, 24, 253, 31, 165, 232, 69, 246, 142, 248, 60, 244, 106, 1, 74, 111, 133, 218, 46, 12, 58, 0, 149, 147, 253, 165, 66, 191, 99, 159, 167])[i.val]!,
  Address.ofFn fun i => (#[119, 83, 141, 120, 37, 67, 242, 190, 143, 237, 20, 18, 67, 237, 49, 133, 131, 127, 229, 206, 100, 241, 62, 189, 140, 61, 199, 43, 154, 68, 243, 225])[i.val]!,
  Address.ofFn fun i => (#[183, 152, 5, 233, 133, 174, 139, 144, 196, 62, 15, 196, 222, 227, 79, 11, 5, 100, 167, 42, 171, 88, 166, 146, 212, 81, 54, 23, 35, 156, 184, 62])[i.val]!,
  Address.ofFn fun i => (#[35, 234, 146, 78, 94, 211, 112, 27, 116, 122, 186, 146, 57, 78, 196, 65, 226, 124, 96, 74, 131, 53, 150, 60, 2, 54, 157, 227, 189, 54, 194, 99])[i.val]!,
  Address.ofFn fun i => (#[180, 90, 29, 76, 86, 71, 8, 189, 92, 197, 78, 85, 64, 190, 142, 172, 202, 89, 154, 26, 98, 188, 116, 17, 20, 119, 104, 192, 53, 135, 230, 34])[i.val]!,
  Address.ofFn fun i => (#[252, 125, 42, 67, 124, 240, 172, 16, 227, 226, 107, 203, 54, 148, 155, 175, 239, 89, 88, 86, 119, 198, 5, 130, 7, 71, 92, 183, 184, 74, 227, 65])[i.val]!,
  Address.ofFn fun i => (#[219, 250, 226, 156, 208, 225, 113, 112, 219, 44, 135, 127, 76, 197, 101, 87, 228, 216, 169, 28, 38, 37, 85, 26, 48, 215, 104, 219, 144, 245, 134, 187])[i.val]!,
  Address.ofFn fun i => (#[66, 225, 49, 195, 52, 228, 129, 12, 82, 120, 164, 31, 84, 71, 0, 25, 22, 103, 200, 130, 69, 165, 23, 39, 95, 181, 243, 241, 53, 230, 47, 40])[i.val]!,
  Address.ofFn fun i => (#[149, 80, 218, 120, 189, 201, 21, 41, 23, 137, 28, 249, 223, 95, 95, 135, 137, 34, 248, 77, 249, 114, 119, 233, 44, 68, 79, 107, 71, 146, 240, 54])[i.val]!
]

def membersRoot : Address :=
  Address.ofFn fun i => (#[131, 134, 112, 180, 85, 1, 141, 183, 156,
    87, 54, 99, 118, 196, 117, 184, 37, 253, 59, 105, 99, 209, 139,
    201, 67, 197, 39, 27, 64, 28, 41, 13])[i.val]!

end MerkleFixture

namespace CatalogFixtures

private def putU16LE (value : UInt16) : PutM Unit :=
  putBytes (u64LEBytes value.toUInt64 2)

private def putU32LE (value : UInt32) : PutM Unit :=
  putBytes (u64LEBytes value.toUInt64 4)

private def putU64LE (value : UInt64) : PutM Unit :=
  putBytes (u64LEBytes value 8)

private def putAddress (address : Address) : PutM Unit :=
  putBytes address.hash

private def putString16 (value : String) : PutM Unit := do
  let bytes := value.toUTF8
  putU16LE bytes.size.toUInt16
  putBytes bytes

private def putMember (member : Catalog.Member) : PutM Unit := do
  putAddress member.envRoot
  putU64LE member.constCount
  putString16 member.label
  putString16 member.toolchain
  putString16 member.sourcePin
  putU32LE member.deps.size.toUInt32
  for dependency in member.deps do
    putU32LE dependency
  match member.preimage with
  | none => putU8 0
  | some address => putU8 1; putAddress address

/-- Test-side exact manifest writer, kept independent of the production
decoder so the loader is exercised from bytes. -/
def manifestBytes (manifest : Catalog.Manifest) : ByteArray := runPut do
  putBytes Catalog.magic
  putU32LE Catalog.version
  putU32LE (match manifest.storage with
    | .fat _ => 0
    | .chunked _ => Catalog.flagChunked)
  putAddress manifest.membersRoot
  putAddress manifest.contentRoot
  putU32LE manifest.members.size.toUInt32
  for member in manifest.members do
    putMember member
  match manifest.storage with
  | .fat pieces =>
    for piece in pieces do
      putAddress piece.fileHash
      putU64LE piece.fileBytes
  | .chunked chunks =>
    putU32LE chunks.size.toUInt32
    for chunk in chunks do
      putAddress chunk.chunkRoot
      putAddress chunk.fileHash
      putU64LE chunk.fileBytes
      putU32LE chunk.owner
  putBytes manifest.trailing

structure PieceArtifact where
  bytes : ByteArray
  envRoot : Address
  addresses : Array Address
  deriving Inhabited

/-- Minimal complete anonymous `.ixe`: the loader consumes through §3 and
retains the three empty metadata-section counts opaquely. -/
def pieceBytes (constants : Array Constant)
    (blobs : Array ByteArray := #[])
    (assumptions : Array Address := #[]) : Except String PieceArtifact := do
  let mut encodedConstants : Array (Address × ByteArray) := #[]
  for constant in constants do
    let address ← match constant.addressChecked with
      | .ok address => pure address
      | .error error => throw s!"unaddressable fixture: {repr error}"
    encodedConstants := encodedConstants.push (address, ser constant)
  encodedConstants := encodedConstants.qsort fun left right =>
    Merkle.addressLT left.1 right.1
  let mut encodedBlobs : Array (Address × ByteArray) := #[]
  for bytes in blobs do
    encodedBlobs := encodedBlobs.push (Address.blake3 bytes, bytes)
  encodedBlobs := encodedBlobs.qsort fun left right =>
    Merkle.addressLT left.1 right.1
  let assumptions := Merkle.dedupSorted (Merkle.sortAddresses assumptions)
  let addresses := encodedConstants.map (·.1)
  let envRoot := Merkle.rootCanonical addresses
  let bytes := runPut do
    putTag4 ⟨Catalog.envFlag, Catalog.envVersion⟩
    putAddress envRoot
    putU8 0
    putTag0 ⟨assumptions.size.toUInt64⟩
    for address in assumptions do putAddress address
    putTag0 ⟨encodedBlobs.size.toUInt64⟩
    for (address, payload) in encodedBlobs do
      putAddress address
      putTag0 ⟨payload.size.toUInt64⟩
      putBytes payload
    putTag0 ⟨encodedConstants.size.toUInt64⟩
    for (address, payload) in encodedConstants do
      putAddress address
      putTag0 ⟨payload.size.toUInt64⟩
      putBytes payload
    putTag0 ⟨0⟩
    -- Empty §4 names, §5 named entries, and §6 comms.  These are opaque to
    -- the anonymous loader but make the fixture a complete `.ixe`.
    putTag0 ⟨0⟩
    putTag0 ⟨0⟩
    putTag0 ⟨0⟩
  return ⟨bytes, envRoot, addresses⟩

def member (label : String) (piece : PieceArtifact)
    (deps : Array UInt32 := #[]) : Catalog.Member :=
  { envRoot := piece.envRoot
    constCount := piece.addresses.size.toUInt64
    label
    toolchain := "lean-4.33.0"
    sourcePin := "catalog-fixture"
    deps
    preimage := none }

def fatManifest (members : Array Catalog.Member)
    (pieces : Array PieceArtifact) : Catalog.Manifest :=
  let allAddresses := pieces.foldl
    (fun addresses piece => addresses.append piece.addresses) #[]
  { membersRoot := Catalog.membersRootOf members
    contentRoot := Merkle.rootCanonical allAddresses
    members
    storage := .fat (pieces.map fun piece =>
      { fileHash := Address.blake3 piece.bytes
        fileBytes := piece.bytes.size.toUInt64 }) }

def chunkedManifest (members : Array Catalog.Member)
    (pieces : Array PieceArtifact) (owners : Array UInt32) :
    Catalog.Manifest :=
  let allAddresses := pieces.foldl
    (fun addresses piece => addresses.append piece.addresses) #[]
  { membersRoot := Catalog.membersRootOf members
    contentRoot := Merkle.rootCanonical allAddresses
    members
    storage := .chunked (pieces.zip owners |>.map fun (piece, owner) =>
      { chunkRoot := piece.envRoot
        fileHash := Address.blake3 piece.bytes
        fileBytes := piece.bytes.size.toUInt64
        owner }) }

def axiomFixture (isUnsafe : Bool) : Constant :=
  { info := .axio { isUnsafe, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[.zero] }

def block (constructorOrdinal : UInt64 := 0) : Constant :=
  { info := .muts #[.indc
      { isUnsafe := false, lvls := 0, params := 0, indices := 0
        typ := .sort 0
        ctors := #[
          { isUnsafe := false, lvls := 0, cidx := constructorOrdinal
            params := 0, fields := 0, typ := .sort 0 }] }]
    sharing := #[], refs := #[], univs := #[.zero] }

def inductiveProjection (blockAddress : Address) (index : UInt64 := 0) :
    Constant :=
  { info := .iPrj { idx := index, block := blockAddress }
    sharing := #[], refs := #[], univs := #[] }

def constructorProjection (blockAddress : Address) (index : UInt64 := 0)
    (ctorIndex : UInt64 := 0) : Constant :=
  { info := .cPrj
      { idx := index
        cidx := ctorIndex
        block := blockAddress }
    sharing := #[], refs := #[], univs := #[] }

structure Input where
  manifest : Catalog.Manifest
  manifestBytes : ByteArray
  pieces : Array PieceArtifact

def inputOf (manifest : Catalog.Manifest) (pieces : Array PieceArtifact) :
    Input :=
  ⟨manifest, manifestBytes manifest, pieces⟩

def validFatInput : Except String Input := do
  let blockConstant := block
  let blockAddress ← match blockConstant.addressChecked with
    | .ok address => pure address
    | .error error => throw s!"block address: {repr error}"
  let sharedAxiom := axiomFixture false
  let pieceA ← pieceBytes #[sharedAxiom, blockConstant,
    inductiveProjection blockAddress,
    constructorProjection blockAddress]
  let pieceB ← pieceBytes #[sharedAxiom, axiomFixture true]
  let members := #[member "Core" pieceA,
    member "Extra" pieceB #[0]]
  let pieces := #[pieceA, pieceB]
  return inputOf (fatManifest members pieces) pieces

def invalidMemberInput : Except String Input := do
  let blockConstant := block
  let blockAddress ← match blockConstant.addressChecked with
    | .ok address => pure address
    | .error error => throw s!"block address: {repr error}"
  let piece ← pieceBytes #[blockConstant,
    inductiveProjection blockAddress 1]
  let pieces := #[piece]
  let members := #[member "BadMember" piece]
  return inputOf (fatManifest members pieces) pieces

def invalidOrdinalInput : Except String Input := do
  let piece ← pieceBytes #[block 7]
  let pieces := #[piece]
  let members := #[member "BadOrdinal" piece]
  return inputOf (fatManifest members pieces) pieces

def duplicateChunkInput : Except String Input := do
  let piece ← pieceBytes #[axiomFixture false]
  let pieces := #[piece, piece]
  let members := #[member "Chunked" piece]
  let manifest := chunkedManifest members pieces #[0, 0]
  return inputOf manifest pieces

def replaceFatBytes (manifest : Catalog.Manifest) (index : Nat)
    (bytes : ByteArray) : Catalog.Manifest :=
  match manifest.storage with
  | .fat rows =>
    let replacement : Catalog.FatPiece :=
      { fileHash := Address.blake3 bytes
        fileBytes := bytes.size.toUInt64 }
    { manifest with storage := .fat (rows.set! index replacement) }
  | .chunked _ => manifest

end CatalogFixtures

end CompilatrixTests
