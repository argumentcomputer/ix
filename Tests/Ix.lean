import LSpec
import Ix.Ixon
import Ix.Ixon.Metadata
import Ix.Address
import Ix.Ixon.Serialize
import Ix.Ixon.Univ
import Ix.Claim
import Ix.TransportM
import LSpec.SlimCheck.Gen
import LSpec
import Blake3

import Tests.Common
import Tests.Ix.Common
import Tests.Ix.Ixon
import Tests.Ix.IR

open LSpec
open SlimCheck
open SlimCheck.Gen

def serde [Ixon.Serialize A] [BEq A] (x: A) : Bool :=
  match Ixon.runGet Ixon.Serialize.get (Ixon.runPut <| Ixon.Serialize.put x) with
  | .ok (y : A) => x == y
  | _ => false

open Ix.TransportM

def transportUniv (univ: Ix.Level): Bool :=
  match EStateM.run (dematUniv univ) emptyDematState with
  | .ok ixon stt =>
    let remat := (ReaderT.run (rematUniv ixon) { meta := stt.meta})
    match EStateM.run remat (rematStateWithStore stt.store) with
    | .ok ix _ => univ == ix
    | .error _ _ => .false
  | .error _ _ => .false

def transportExpr (x: Ix.Expr): Bool :=
  match EStateM.run (dematExpr x) emptyDematState with
  | .ok ixon stt =>
    let remat := (ReaderT.run (rematExpr ixon) { meta := stt.meta})
    match EStateM.run remat (rematStateWithStore stt.store) with
    | .ok ix _ => x == ix
    | .error _ _ => .false
  | .error _ _ => .false

def transportConst (x: Ix.Const): Bool :=
  match EStateM.run (dematConst x) emptyDematState with
  | .ok ixon stt =>
    let remat := (ReaderT.run (rematConst ixon) { meta := stt.meta})
    match EStateM.run remat (rematStateWithStore stt.store) with
    | .ok ix _ => x == ix
    | .error _ _ => .false
  | .error _ _ => .false


--def transportExpr' (x: Ix.Expr): Except TransportError Bool :=
--  match EStateM.run (dematExpr x) emptyDematState with
--  | .ok ixon stt =>
--    let remat := (ReaderT.run (rematExpr ixon) { meta := stt.meta})
--    match EStateM.run remat emptyRematState with
--    | .ok ix _ => .ok (x == ix)
--    | .error e _ => .error e
--  | .error e _ => .error e

def ffiConst (x: Ixon.IxonConst) : Bool := 
  let bytes := (Ixon.runPut <| Ixon.Serialize.put x)
  Ixon.eqLeanRustSerialization x.ixon.toFFI bytes

def ffiExpr (x: Ixon.IxonExpr) : Bool := 
  let bytes := (Ixon.runPut <| Ixon.Serialize.put x)
  Ixon.eqLeanRustSerialization x.ixon.toFFI bytes


def myConfig : SlimCheck.Configuration where
  numInst := 10000
  maxSize := 100
  traceDiscarded := true
  traceSuccesses := true
  traceShrink := true
  traceShrinkCandidates := true

def dbg : IO UInt32 := do
   SlimCheck.Checkable.check (∀ x: Ix.Const, transportConst x) myConfig
   return 0

--def Test.Ix.unitTransport : TestSeq :=
--  testExprs.foldl (init := .done) fun tSeq x =>
--    tSeq ++ (test s!"transport {repr x}" $ Except.isOk (transportExpr' x))


def Tests.Ix.suite : List LSpec.TestSeq :=
  [
    check "metadatum serde" (∀ x : Ixon.Metadatum, serde x),
    check "metadata serde" (∀ x : Ixon.Metadata, serde x),
    check "universe serde" (∀ x : Ixon.Univ, serde x),
    check "universe transport" (∀ x : Ix.Level, transportUniv x),
    check "expr serde" (∀ x : Ixon.IxonExpr, serde x),
    check "expr transport" (∀ x : Ix.Expr, transportExpr x),
    check "expr ffi with Rust" (∀ x : Ixon.IxonExpr, ffiExpr x),
    --check "axiom serde" (∀ x : Ixon.Axiom, serde x),
    --check "recursor rule serde" (∀ x : Ixon.RecursorRule, serde x),
    --check "recursor serde" (∀ x : Ixon.Recursor, serde x),
    --check "constructor serde" (∀ x : Ixon.Constructor, serde x),
    check "claim serde" (∀ x : Claim, serde x),
    check "const ffi with Rust" (∀ x : Ixon.IxonConst, ffiConst x),
    check "const transport" (∀ x : Ix.Const, transportConst x),
  ]


def hexVal? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some (UInt8.ofNat (10 + (c.toNat - 'a'.toNat)))
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some (UInt8.ofNat (10 + (c.toNat - 'A'.toNat)))
  else
    none

/-- Parse a hexadecimal string like `0xdead_beef_cafe_0123_4567_89ab_cdef` into a `ByteArray`.
Underscores are ignored; `0x`/`0X` prefix is optional. Panics on invalid input. -/
def parseHex (x : String) : ByteArray :=
  -- drop optional 0x/0X
  let x :=
    if x.startsWith "0x" || x.startsWith "0X" then x.drop 2 else x
  -- remove underscores
  let x := String.mk (x.toList.filter (· ≠ '_'))
  -- must have an even number of hex digits
  if x.length % 2 = 1 then
    panic! "parseHex: odd number of hex digits"
  else
    let n := x.length
    let rec loop (i : Nat) (acc : ByteArray) : ByteArray :=
      if i < n then
        -- safe since ASCII: `String.get!` indexes by chars
        let c1 := x.get! ⟨i⟩
        let c2 := x.get! ⟨i+1⟩
        match hexVal? c1, hexVal? c2 with
        | some hi, some lo =>
          let b : UInt8 := (hi <<< 4) ||| lo
          loop (i + 2) (acc.push b)
        | _, _ =>
          panic! s!"parseHex: invalid hex at positions {i}..{i+1}"
      else
        acc
    loop 0 ByteArray.empty

/-- Print a `ByteArray` as a lowercase hex string with a `0x` prefix. -/
def printHex (ba : ByteArray) : String :=
  let hexdigits := "0123456789abcdef"
  let rec go (i : Nat) (acc : String) : String :=
    if h : i < ba.size then
      let b := ba.get! i
      let hi := (b.toNat / 16)
      let lo := (b.toNat % 16)
      let acc := acc.push (hexdigits.get! ⟨hi⟩)
      let acc := acc.push (hexdigits.get! ⟨lo⟩)
      go (i + 1) acc
    else acc
  "0x" ++ go 0 ""

def serde_is [Ixon.Serialize A] [BEq A] (x: A) (expect: String): Bool := Id.run do
  let expected := parseHex expect
  let bytes := Ixon.runPut (Ixon.Serialize.put x)
  if bytes == expected then
    match Ixon.runGet Ixon.Serialize.get bytes with
    | .ok (y : A) => x == y
    | _ => false
  else false

def test_serde [Ixon.Serialize A] [BEq A] [Repr A] (x: A) (expect: String): LSpec.TestSeq :=
  let expected := parseHex expect
  let bytes := Ixon.runPut (Ixon.Serialize.put x)
  let res := if bytes == expected then
    match Ixon.runGet Ixon.Serialize.get bytes with
    | .ok (y : A) => x == y
    | _ => false
    else false
  test s!"serde {repr x} <-> {expect}" res

open Ixon


-- TODO
def bad : Ixon := Ixon.meta <| .mk [
  (0, [Metadatum.name `d, .link default, .hints (.regular 576554452), .link default]),
  (1, [.info .instImplicit, .info .instImplicit, .info .strictImplicit]),
  (2, [.all [.mkNum .anonymous 165851424810452359], .info .default]),
  (3, []),
  (4, []),
  (5, [.hints .opaque]),
  (6, [.name <| .mkNum .anonymous 871843802607008850]),
  ]

--#eval printHex <| runPut <| Serialize.put bad
--"0xe0a78100a400a1716402af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32620302d4855d2202af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32628101a30103010301028102a204a1a1880887c551fdfd384d0201008103a08104a08105a103008106a100a18808523c04ba5169190c"

--#eval runGet (@Serialize.get Ixon _) (runPut (Serialize.put bad))


def Tests.Ixon.units : List LSpec.TestSeq :=
  [
    test_serde (Ixon.vari 0x0) "0x00",
    test_serde (Ixon.vari 0x7) "0x07",
    test_serde (Ixon.vari 0x8) "0x0808",
    test_serde (Ixon.vari 0xFF) "0x08FF",
    test_serde (Ixon.vari 0x0100) "0x090001",
    test_serde (Ixon.vari 0x0100) "0x090001",
    test_serde (Ixon.vari 0xFFFF) "0x09FFFF",
    test_serde (Ixon.vari 0x010000) "0x0A000001",
    test_serde (Ixon.vari 0xFFFFFF) "0x0AFFFFFF",
    test_serde (Ixon.vari 0x01000000) "0x0B00000001",
    test_serde (Ixon.vari 0xFFFFFFFF) "0x0BFFFFFFFF",
    test_serde (Ixon.vari 0x0100000000) "0x0C0000000001",
    test_serde (Ixon.vari 0xFFFFFFFFFF) "0x0CFFFFFFFFFF",
    test_serde (Ixon.vari 0x010000000000) "0x0D000000000001",
    test_serde (Ixon.vari 0xFFFFFFFFFFFF) "0x0DFFFFFFFFFFFF",
    test_serde (Ixon.vari 0x01000000000000) "0x0E00000000000001",
    test_serde (Ixon.vari 0xFFFFFFFFFFFFFF) "0x0EFFFFFFFFFFFFFF",
    test_serde (Ixon.vari 0x0100000000000000) "0x0F0000000000000001",
    test_serde (Ixon.vari 0xFFFFFFFFFFFFFFFF) "0x0FFFFFFFFFFFFFFFFF",
    test_serde (Ixon.sort <| .const 0x0) "0x9000",
    test_serde (Ixon.sort <| .const 0x1F) "0x901F",
    test_serde (Ixon.sort <| .const 0x20) "0x902020",
    test_serde (Ixon.sort <| .const 0xFF) "0x9020FF",
    test_serde (Ixon.sort <| .const 0x0100) "0x90210001",
    test_serde (Ixon.sort <| .const 0xFFFF) "0x9021FFFF",
    test_serde (Ixon.sort <| .const 0x010000) "0x9022000001",
    test_serde (Ixon.sort <| .const 0xFFFFFF) "0x9022FFFFFF",
    test_serde (Ixon.sort <| .const 0x01000000) "0x902300000001",
    test_serde (Ixon.sort <| .const 0xFFFFFFFF) "0x9023FFFFFFFF",
    test_serde (Ixon.sort <| .const 0x0100000000) "0x90240000000001",
    test_serde (Ixon.sort <| .const 0xFFFFFFFFFF) "0x9024FFFFFFFFFF",
    test_serde (Ixon.sort <| .const 0x010000000000) "0x9025000000000001",
    test_serde (Ixon.sort <| .const 0xFFFFFFFFFFFF) "0x9025FFFFFFFFFFFF",
    test_serde (Ixon.sort <| .const 0x01000000000000) "0x902600000000000001",
    test_serde (Ixon.sort <| .const 0xFFFFFFFFFFFFFF) "0x9026FFFFFFFFFFFFFF",
    test_serde (Ixon.sort <| .const 0x0100000000000000) "0x90270000000000000001",
    test_serde (Ixon.sort <| .const 0xFFFFFFFFFFFFFFFF) "0x9027FFFFFFFFFFFFFFFF",
    test_serde (Ixon.sort <| .var 0x0) "0x9040",
    test_serde (Ixon.sort <| .var 0x1F) "0x905F",
    test_serde (Ixon.sort <| .var 0x20) "0x906020",
    test_serde (Ixon.sort <| .var 0xFF) "0x9060FF",
    test_serde (Ixon.sort <| .var 0x0100) "0x90610001",
    test_serde (Ixon.sort <| .var 0xFFFFFFFFFFFFFFFF) "0x9067FFFFFFFFFFFFFFFF",
    test_serde (Ixon.sort <| .add 0x0 (.const 0x0)) "0x908000",
    test_serde (Ixon.sort <| .add 0x0 (.var 0x0)) "0x908040",
    test_serde (Ixon.sort <| .add 0x1F (.var 0x0)) "0x909F40",
    test_serde (Ixon.sort <| .add 0x20 (.var 0x0)) "0x90A02040",
    test_serde (Ixon.sort <| .add 0xFF (.var 0x0)) "0x90A0FF40",
    test_serde (Ixon.sort <| .add 0xFFFF_FFFF_FFFF_FFFF (.var 0x0)) "0x90A7FFFFFFFFFFFFFFFF40",
    test_serde (Ixon.sort <| .max (.var 0x0) (.var 0x0)) "0x90C04040",
    test_serde (Ixon.sort <| .max (.var 0x0) (.var 0x1)) "0x90C04041",
    test_serde (Ixon.sort <| .max (.var 0x1) (.var 0x0)) "0x90C04140",
    test_serde (Ixon.sort <| .max (.var 0x1) (.var 0x1)) "0x90C04141",
    test_serde (Ixon.sort <| .imax (.var 0x0) (.var 0x0)) "0x90C14040",
    test_serde (Ixon.sort <| .imax (.var 0x0) (.var 0x1)) "0x90C14041",
    test_serde (Ixon.sort <| .imax (.var 0x1) (.var 0x0)) "0x90C14140",
    test_serde (Ixon.sort <| .imax (.var 0x1) (.var 0x1)) "0x90C14141",
    test_serde (Ixon.sort <| .imax (.var 0x1) (.var 0x1)) "0x90C14141",
    test_serde (Ixon.refr (default) []) "0x10af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.refr (default) [.var 0x0]) "0x11af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f326240",
    test_serde (Ixon.recr 0x0 [.var 0x0]) "0x20A140",
    test_serde (Ixon.recr 0x0 [.var 0x0, .var 0x1]) "0x20A24041",
    test_serde (Ixon.apps (Ixon.vari 0x0) (Ixon.vari 0x1) []) "0x300001",
    test_serde (Ixon.apps (Ixon.vari 0x0) (Ixon.vari 0x1) [Ixon.vari 0x2]) "0x31000102",
    test_serde (Ixon.apps (Ixon.vari 0x0) (Ixon.vari 0x1)
      [
        Ixon.vari 0x2, Ixon.vari 0x3, Ixon.vari 0x4, Ixon.vari 0x5,
        Ixon.vari 0x6, Ixon.vari 0x7, Ixon.vari 0x8, Ixon.vari 0x9,
      ]) "0x3808000102030405060708080809",
    test_serde (Ixon.lams [Ixon.vari 0x0] (Ixon.vari 0x1)) "0x410001",
    test_serde (Ixon.lams
      [
        Ixon.vari 0x0, Ixon.vari 0x1, Ixon.vari 0x2, Ixon.vari 0x3, 
        Ixon.vari 0x4, Ixon.vari 0x5, Ixon.vari 0x6, Ixon.vari 0x7,
      ] (Ixon.vari 0x8)) "0x480800010203040506070808",
    test_serde (Ixon.alls [Ixon.vari 0x0] (Ixon.vari 0x1)) "0x510001",
    test_serde (Ixon.alls
      [
        Ixon.vari 0x0, Ixon.vari 0x1, Ixon.vari 0x2, Ixon.vari 0x3, 
        Ixon.vari 0x4, Ixon.vari 0x5, Ixon.vari 0x6, Ixon.vari 0x7,
      ] (Ixon.vari 0x8)) "0x580800010203040506070808",
    test_serde (Ixon.proj (default) 0x0 (Ixon.vari 0x0)) "0x60af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f326200",
    test_serde (Ixon.proj (default) 0x8 (Ixon.vari 0x0)) "0x6808af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f326200",
    test_serde (Ixon.strl "") "0x70",
    test_serde (Ixon.strl "foobar") "0x76666f6f626172",
    test_serde (Ixon.natl 0x0) "0x8100",
    test_serde (Ixon.natl 0xFF) "0x81FF",
    test_serde (Ixon.natl 0x100) "0x820001",
    test_serde (Ixon.letE true (Ixon.vari 0x0) (Ixon.vari 0x1) (Ixon.vari 0x2)) "0x91000102",
    test_serde (Ixon.list []) "0xA0",
    test_serde (Ixon.list [Ixon.vari 0x0, Ixon.vari 0x1, Ixon.vari 0x2]) "0xA3000102",
    test_serde (Ixon.defn (.mk .definition .unsafe 0 (default) (default))) "0xB000008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.defn (.mk .opaque .safe 1 default default)) "0xB001018101af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.axio ⟨true, 0, default⟩) "0xB1018100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.quot ⟨.type, 0, default⟩) "0xB2008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.cprj ⟨0, 0, default⟩) "0xB381008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.rprj ⟨0, 0, default⟩) "0xB481008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.iprj ⟨0, default⟩) "0xB58100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.dprj ⟨0, default⟩) "0xB68100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.inds []) "0xC0",
    test_serde (Ixon.inds [⟨false, false, false, 0, 0, 0, 0, default, [], []⟩]) "0xC1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A0A0",
    test_serde (Ixon.inds [⟨false, false, false, 0, 0, 0, 0, default, [⟨false, 0,0,0,0, default⟩], [⟨false, false, 0,0,0,0,0,default, [⟨0, default⟩]⟩]⟩]) "0xC1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A1008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A10081008100810081008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262A18100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.defs []) "0xD0",
    test_serde (Ixon.defs [⟨.definition, .unsafe, 0, default, default⟩]) "0xD100008100af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.meta ⟨[]⟩) "0xE0A0",
    test_serde (Ixon.meta ⟨[(0, [])]⟩) "0xE0A18100A0",
    test_serde (Ixon.meta ⟨[(0, [.name .anonymous])]⟩) "0xE0A18100A100A0",
    test_serde (Ixon.meta ⟨[(0, [.name `a])]⟩) "0xE0A18100A100A17161",
    test_serde (Ixon.meta ⟨[(0, [.name `a.b])]⟩) "0xE0A18100A100A271617162",
    test_serde (Ixon.meta ⟨[(0, [.name `a.b.c])]⟩) "0xE0A18100A100A3716171627163",
    test_serde (Ixon.meta ⟨[(0, [.name (.mkNum .anonymous 165851424810452359)])]⟩) "0xE0A18100A100A1880887C551FDFD384D02",
    test_serde (Ixon.meta ⟨[(0, [Metadatum.name `d, .link default, .hints (.regular 576554452), .link default])]⟩) "0xe0a18100a400a1716402af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32620302d4855d2202af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    test_serde (Ixon.meta ⟨[(0, [.hints (.regular 42)])]⟩) "0xe0a18100a103022a000000",
    test_serde bad "0xe0a78100a400a1716402af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32620302d4855d2202af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f32628101a30103010301028102a204a1a1880887c551fdfd384d0201008103a08104a08105a103008106a100a18808523c04ba5169190c"
  ]


