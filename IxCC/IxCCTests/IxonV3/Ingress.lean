import IxCC.Ixon.V3.Env
import IxCC.Ixon.V3.Keys
import IxCC.Ixon.V3.Support
import IxCC.Src.Ingress
import IxCC.Tools.Check
import IxCCTests.IxonV3.Builder
import IxCCTests.Support.Bound

/-! # Ixon v5 wire, N6 reject-parity, R5 binder-data ingress, and N2 datum cross-check tests

Self-contained verification suite for Lane W (`R4`, `N6`, `R5`, `N2`, `N7`):
- `wireFormatId == "ixon-v5"` and 0..255 sweeps of every v5 mode-code bijection;
- every vector of `fixtures/ixon-v4/expressions.txt` (v5) with truncation and trailing-byte checks;
- every record / noncanonical / canonical-rule / env-accept / tampered-record row of
  `fixtures/ixon-v4/reject-parity.txt` plus explicit hand-built N6 cases (`lvls = 2^32`,
  node tags 5/6/7, input code 7, share with mode bits, `let` header ≥ 16, assertion bit 7,
  alloc code 3, theorem assertions, constructor flags/field modes, non-canonical `Nat` blobs);
- R5 binder-data section reader (`Src.Ingress`): completeness/canonicity enforcement,
  mutual-block `ConstantInfo.binderRoots` alignment across inductives/constructors/defs/recursors,
  walking through `.share` in leading `lam` and `all` telescopes, `(index, variant)` share cache
  separation, and `letE` mode roundtrips;
- N2 stored zero-ness datum fail-closed cross-check (`checkStoredDatum`, `checkStoredDatumStrict`,
  `checkBinderDatumAt`, `checkTermBinderData`). -/

namespace IxCCTests.IxonV3.Ingress

open IxCC IxCC.Ixon IxCC.Ixon.V3 IxCC.Src IxCC.Src.Ingress
open IxCCTests.IxonV3.Builder

private def require (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError s!"ixon-v5: {msg}")

private def hex (s : String) : IO ByteArray :=
  IO.ofExcept (IxCC.Tools.Check.unhex s)

private def dataLines (file : System.FilePath) : IO (List String) := do
  return (← IO.FS.readFile file).splitOn "\n" |>.filter fun line =>
    !line.isEmpty && !line.startsWith "#"

/-- Parse `reject-parity.txt` byte tokens: hex string or `XX*N`. -/
private def parseTokens (tokens : List String) : IO ByteArray := do
  let mut out := ByteArray.empty
  for tok in tokens do
    if tok.isEmpty then continue
    match tok.splitOn "*" with
    | [byteHex, countStr] =>
      let b ← hex byteHex
      require (b.size == 1) s!"invalid repeat token {tok}"
      let some n := countStr.toNat? | throw (IO.userError s!"invalid repeat count {tok}")
      out := out ++ ByteArray.mk (Array.replicate n b[0]!)
    | [_] =>
      out := out ++ (← hex tok)
    | _ => throw (IO.userError s!"invalid token {tok}")
  return out

/-! ## 1. Mode code bijections and v5 expression vectors -/

def testModesAndExprs (root : System.FilePath) : IO Nat := do
  let mut n := 0
  require (V3.wireFormatId == "ixon-v5") s!"expected wireFormatId ixon-v5, got {V3.wireFormatId}"
  n := n + 1
  -- All 0..255 sweeps of every v5 mode code bijection
  for code in [:256] do
    let u8 := code.toUInt8
    let u64 := code.toUInt64
    let bm := BinderMode.ofCode? u8
    require (bm.isSome == (code < 7)) s!"BinderMode.ofCode? {code}"
    if let some m := bm then require (m.toCode.toNat == code) s!"BinderMode roundtrip {code}"
    let rm := ResultMode.ofCode? u8
    require (rm.isSome == (code < 4)) s!"ResultMode.ofCode? {code}"
    if let some m := rm then require (m.toCode.toNat == code) s!"ResultMode roundtrip {code}"
    let am := AllMode.ofCode? u8
    require (am.isSome == (code < 32 && (code &&& 7) < 7)) s!"AllMode.ofCode? {code}"
    if let some m := am then require (m.toCode.toNat == code) s!"AllMode roundtrip {code}"
    let lm := LetMode.ofCode? u8
    require (lm.isSome == (code < 8)) s!"LetMode.ofCode? {code}"
    if let some m := lm then require (m.toCode.toNat == code) s!"LetMode roundtrip {code}"
    let lh := LetMode.ofHeader? u64
    require (lh.isSome == (code < 16)) s!"LetMode.ofHeader? {code}"
    if let some (nd, m) := lh then
      require ((LetMode.header nd m).toNat == code) s!"LetMode header roundtrip {code}"
    let fm := FieldMode.ofCode? u8
    require (fm.isSome == (code < 2)) s!"FieldMode.ofCode? {code}"
    if let some m := fm then require (m.toCode.toNat == code) s!"FieldMode roundtrip {code}"
    let aa := AllocAssert.ofCode? u8
    require (aa.isSome == (code < 3)) s!"AllocAssert.ofCode? {code}"
    if let some a := aa then require (a.toCode.toNat == code) s!"AllocAssert roundtrip {code}"
    let da := DefAsserts.ofCode? u8
    require (da.isSome == (code < 8 && (code &&& 3) < 3)) s!"DefAsserts.ofCode? {code}"
    if let some a := da then require (a.toCode.toNat == code) s!"DefAsserts roundtrip {code}"
    n := n + 8
  -- All v5 expression fixture vectors (roundtrip, every prefix truncation, trailing byte)
  for line in ← dataLines (root / "expressions.txt") do
    let [label, encoded] := line.splitOn " "
      | throw (IO.userError s!"invalid expression fixture row: {line}")
    let bs ← hex encoded
    let decoded ← IO.ofExcept (decodeExpr bs)
    require (exprBytes decoded.value == bs) s!"expression bytes differ: {label}"
    n := n + 1
    for len in [:bs.size] do
      require ((decodeExpr (bs.extract 0 len)).toOption.isNone)
        s!"accepted truncated expression: {label}/{len}"
      n := n + 1
    require ((decodeExpr (bs.push 0)).toOption.isNone) s!"accepted trailing byte: {label}"
    n := n + 1
  -- Depth, count, and reserved let header on expressions
  let huge := _root_.Ixon.runPut (_root_.Ixon.putTagN 4 8 (UInt64.ofNat (UInt64.size - 1)))
  require ((decodeExpr huge).toOption.isNone) "accepted impossible telescope count"
  require ((decodeExpr (← hex "a808001110")).toOption.isNone) "accepted let header 16"
  require ((decodeExpr (← hex "a809001110")).toOption.isNone) "accepted let header 17"
  let bounded : V3.Expr := .lam (.sort 0) (.var 0)
  require ((decodeExpr (exprBytes bounded) (depth := 2)).toOption.isSome)
    "rejected expression at exact depth bound"
  let nested : V3.Expr := .lam (.sort 0) bounded
  require ((decodeExpr (exprBytes nested) (depth := 2)).toOption.isNone)
    "telescope bypassed semantic expression depth"
  let oversizedLevels := _root_.Ixon.runPut (_root_.Ixon.putTagN 4 2 4097) ++
    _root_.Ixon.runPut (_root_.Ixon.putTagN 0 0 0) ++ ByteArray.mk (Array.replicate 4097 0)
  require ((decodeExpr oversizedLevels).toOption.isNone) "universe arguments bypassed count bound"
  n := n + 6
  return n

/-! ## 2. N6 must-refuse cases (`reject-parity.txt` + explicit hand-built checks) -/

def testN6RejectParity (root : System.FilePath) : IO Nat := do
  let mut n := 0
  -- All record / noncanonical / canonical-rule / env-accept / env tampered-record rows
  for line in ← dataLines (root / "reject-parity.txt") do
    let parts := line.splitOn " " |>.filter (!·.isEmpty)
    match parts with
    | kind :: name :: tokens =>
      let bs ← parseTokens tokens
      match kind with
      | "record-accept" | "canonical-rule-accept" =>
        let dec ← IO.ofExcept (decodeConstant bs)
        require (constantBytes dec.value == bs) s!"reject-parity {kind}/{name}: roundtrip"
        n := n + 1
      | "record" | "noncanonical" | "canonical-rule" =>
        require ((decodeConstant bs).toOption.isNone)
          s!"reject-parity {kind}/{name}: decoder accepted invalid record"
        n := n + 1
      | "env-accept" =>
        let _ ← IO.ofExcept (decodeAnonymousEnv bs)
        n := n + 1
      | "env" =>
        if name == "tampered-record" then
          require ((decodeAnonymousEnv bs).toOption.isNone)
            s!"reject-parity env/{name}: accepted tampered record"
          n := n + 1
      | _ => pure ()
    | _ => pure ()
  -- Explicit lvls >= 2^32 refusal and lvls = 2^32 - 1 control
  let axTooMany : V3.Constant :=
    ⟨.axio ⟨false, (2 ^ 32 : Nat).toUInt64, .sort 0⟩, #[], #[], #[.zero], #[]⟩
  let axMaxOk : V3.Constant :=
    ⟨.axio ⟨false, (2 ^ 32 - 1 : Nat).toUInt64, .sort 0⟩, #[], #[], #[.zero], #[]⟩
  require ((decodeConstant (constantBytes axTooMany)).toOption.isNone)
    "N6: accepted record with lvls = 2^32"
  require ((decodeConstant (constantBytes axMaxOk)).toOption.isSome)
    "N6: rejected control record with lvls = 2^32 - 1"
  -- Explicit binder node tags 5, 6, 7 and share with mode bits 0x0B / 0x1B / 0xFF
  -- Base moded-definition from reject-parity.txt (node byte at index 18)
  let baseDef ← hex "D00100910000810010000001000200000001200001000100"
  require ((decodeConstant baseDef).toOption.isSome) "N6: base moded-definition control failed"
  for badByte in ([0x05, 0x06, 0x07, 0x38, 0x0B, 0x1B, 0xFF] : List UInt8) do
    let tampered := baseDef.set! 18 badByte
    require ((decodeConstant tampered).toOption.isNone)
      s!"N6: accepted illegal binder node byte 0x{Nat.toDigits 16 badByte.toNat |> String.ofList}"
    n := n + 1
  -- Explicit constructor fieldModes roundtrip
  let ctorListedBytes ← hex "C10100000000000102000000020001000000010000"
  let ctorDec ← IO.ofExcept (decodeConstant ctorListedBytes)
  match ctorDec.value.info with
  | .muts #[.indc ind] =>
    match ind.ctors[0]? with
    | some c =>
      require (c.fieldMode 0 == .inherited && c.fieldMode 1 == .shared && c.fieldMode 2 == .inherited)
        "N6: constructor fieldMode mismatch"
    | none => throw (IO.userError "N6: missing constructor")
  | _ => throw (IO.userError "N6: unexpected constant info for constructor-field-modes")
  -- Non-canonical Nat literal blobs refused by decodeNatBlob AND end-to-end Src.Ingress
  for badBlob in ([ByteArray.empty, ⟨#[0, 0]⟩, ⟨#[5, 0]⟩, ⟨#[0, 1, 0]⟩] : List ByteArray) do
    require (!V3.canonicalNatBytes badBlob) s!"N6: canonicalNatBytes accepted {badBlob.data.toList}"
    require ((V3.decodeNatBlob badBlob).toOption.isNone)
      s!"N6: decodeNatBlob accepted {badBlob.data.toList}"
    let (env0, ax) := Builder.base
    let (env1, blobAddr) := storeBlob env0 badBlob
    let natDef : V3.Constant :=
      ⟨.defn ⟨.defn, .safe, {}, 0, .ref 0 #[], .nat 1⟩, #[], #[ax, blobAddr], #[], #[]⟩
    let (env2, defAddr) := store env1 natDef
    let decodedEnv ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes env2))
    require ((Src.Ingress.readAll decodedEnv #[defAddr]).toOption.isNone)
      s!"N6: Src.Ingress accepted non-canonical Nat blob {badBlob.data.toList}"
    n := n + 3
  -- Canonical Nat literal blobs accepted end-to-end through Src.Ingress
  for val in ([0, 1, 5, 255, 256, 65535, 2 ^ 130 + 513] : List Nat) do
    let goodBlob := canonicalNatBlob val
    require (V3.canonicalNatBytes goodBlob) s!"N6: canonicalNatBytes rejected {val}"
    require ((V3.decodeNatBlob goodBlob).toOption == some val) s!"N6: decodeNatBlob mismatch for {val}"
    let (env0, ax) := Builder.base
    let (env1, blobAddr) := storeBlob env0 goodBlob
    let natDef : V3.Constant :=
      ⟨.defn ⟨.defn, .safe, {}, 0, .ref 0 #[], .nat 1⟩, #[], #[ax, blobAddr], #[], #[]⟩
    let (env2, defAddr) := store env1 natDef
    let decodedEnv ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes env2))
    let prog ← IO.ofExcept (Src.Ingress.readAll decodedEnv #[defAddr])
    let some cId := prog.lookup defAddr | throw (IO.userError s!"N6: missing nat def {val}")
    match prog.decl? cId with
    | some (.defn _ _ _ _ (.natLit m)) =>
      require (m == val) s!"N6: ingested Nat literal {m} != {val}"
    | _ => throw (IO.userError s!"N6: expected natLit for {val}")
    n := n + 3
  return n + 4

/-! ## 3. R5 binder-data section reader: completeness, muts, leading `.share`, `(index, variant)` cache -/

def testR5Ingress : IO Nat := do
  let mut n := 0
  let (env0, ax) := Builder.base

  -- 3a. Completeness refusals: missing section, partial section, unsafe with non-undecided node
  let idNoBinders : V3.Constant :=
    ⟨.defn ⟨.defn, .safe, {}, 0, arrow (.ref 0 #[]) (.ref 0 #[]),
      lambda (.ref 0 #[]) (.var 0)⟩, #[], #[ax], #[], #[]⟩
  require (!idNoBinders.bindersComplete) "R5: empty binders passed bindersComplete"
  let (envBad1, aBad1) := storeRaw env0 idNoBinders
  let decBad1 ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes envBad1))
  require ((Src.Ingress.readAll decBad1 #[aBad1]).toOption.isNone)
    "R5: ingress accepted incomplete binder section (empty)"
  -- Only root 0 present, root 1 missing
  let idHalf : V3.Constant :=
    { idNoBinders with binders := #[{ shared := false, index := 0, variant := 0, nodes := #[.never {}] }] }
  require (!idHalf.bindersComplete) "R5: half binders passed bindersComplete"
  let (envBad2, aBad2) := storeRaw env0 idHalf
  let decBad2 ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes envBad2))
  require ((Src.Ingress.readAll decBad2 #[aBad2]).toOption.isNone)
    "R5: ingress accepted incomplete binder section (missing value block)"
  -- Unsafe defn with `.never` instead of `.undecided` refused; `.undecided` accepted
  let unsafeBad : V3.Constant :=
    ⟨.defn ⟨.defn, .unsaf, {}, 0, arrow (.ref 0 #[]) (.ref 0 #[]),
      lambda (.ref 0 #[]) (.var 0)⟩, #[], #[ax], #[],
      #[{ shared := false, index := 0, variant := 0, nodes := #[.never {}] },
        { shared := false, index := 1, variant := 0, nodes := #[.never {}] }]⟩
  require (!unsafeBad.bindersComplete) "R5: unsafe constant with .never passed bindersComplete"
  let (envUBad, aUBad) := storeRaw env0 unsafeBad
  let decUBad ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes envUBad))
  require ((Src.Ingress.readAll decUBad #[aUBad]).toOption.isNone)
    "R5: ingress accepted unsafe constant with non-undecided binder node"
  let unsafeGood : V3.Constant :=
    completeBinders ⟨.defn ⟨.defn, .unsaf, {}, 0, arrow (.ref 0 #[]) (.ref 0 #[]),
      lambda (.ref 0 #[]) (.var 0)⟩, #[], #[ax], #[], #[]⟩
  require unsafeGood.bindersComplete "R5: completeBinders failed on unsafe constant"
  let (envUGood, aUGood) := store env0 unsafeGood
  let decUGood ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes envUGood))
  let _ ← IO.ofExcept (Src.Ingress.readAll decUGood #[aUGood])
  -- Direct readConsts also refuses incomplete records bypassing decodeRead
  require ((Src.Ingress.readConsts decBad1 #[{ address := aBad1, constant := idNoBinders, proofs := true }] #[aBad1]).toOption.isNone)
    "R5: readConsts accepted incomplete binder section directly"
  n := n + 9

  -- 3b. Mutual block (`muts`) root index alignment across indc + 2 ctors + defn + recr + 2 rules
  -- Roots in `ConstantInfo.binderRoots`:
  --   0: ind.typ (0 binders: .sort 0)
  --   1: ctor0.typ (1 binder: arrow (.ref 0 #[]) (.recur 0 #[]))
  --   2: ctor1.typ (2 binders: arrow (.ref 0 #[]) (arrow (.recur 0 #[]) (.recur 0 #[])))
  --   3: defn.typ (1 binder: arrow (.recur 0 #[]) (.recur 0 #[]))
  --   4: defn.value (1 binder: lambda (.recur 0 #[]) (.var 0))
  --   5: recr.typ (4 binders: motive, m0, m1, major — with motive = arrow (.recur 0 #[]) (.sort 0))
  --   6: rule0.rhs (1 binder: lambda (.ref 0 #[]) (.var 0))
  --   7: rule1.rhs (1 binder: lambda (.ref 0 #[]) (.var 0))
  let mCtor0 : AllMode := { input := .erased, result := .shared }
  let mCtor1a : AllMode := { input := .unique, result := .borrowed }
  let mCtor1b : AllMode := { input := .borrowed, result := .unique }
  let mDefTy : AllMode := { input := .once, result := .uniqueBorrowed }
  let mDefVal : AllMode := { input := .onceBorrowed, result := .borrowed }
  let mRecMajor : AllMode := { input := .uniqueBorrowed, result := .unique }
  let mRule0 : AllMode := { input := .unique, result := .shared }
  let mRule1 : AllMode := { input := .erased, result := .unique }
  let indC0 : V3.Constructor := ⟨false, 2, 0, 0, 1, .inherited, arrow (.ref 0 #[]) (.recur 0 #[])⟩
  let indC1 : V3.Constructor :=
    ⟨false, 2, 1, 0, 2, .inherited, arrow (.ref 0 #[]) (arrow (.recur 0 #[]) (.recur 0 #[]))⟩
  let indM : V3.Inductive := ⟨false, 2, 0, 0, .sort 0, #[indC0, indC1]⟩
  let defM : V3.Definition :=
    ⟨.defn, .safe, {}, 2, arrow (.recur 0 #[]) (.recur 0 #[]), lambda (.recur 0 #[]) (.var 0)⟩
  let recTy : V3.Expr :=
    arrow (arrow (.recur 0 #[]) (.sort 0))
      (arrow (.ref 0 #[]) (arrow (.ref 0 #[]) (arrow (.recur 0 #[]) (.ref 0 #[]))))
  let recM : V3.Recursor :=
    ⟨false, false, 2, 0, 0, 1, 2, recTy,
      #[⟨1, lambda (.ref 0 #[]) (.var 0)⟩, ⟨2, lambda (.ref 0 #[]) (.var 0)⟩]⟩
  let mutRaw : V3.Constant :=
    ⟨.muts #[.indc indM, .defn defM, .recr recM], #[], #[ax], #[.succ .zero], #[]⟩
  let mutComplete := completeBindersWith mutRaw fun pos =>
    match pos.shared, pos.index.toNat, pos.ordinal with
    | false, 1, 0 => .zero mCtor0
    | false, 2, 0 => .ifAllZero #[0] mCtor1a
    | false, 2, 1 => .ifAllZero #[0, 1] mCtor1b
    | false, 3, 0 => .never mDefTy
    | false, 4, 0 => .ifAllZero #[1] mDefVal
    -- root 5 (recTy): ord 0 motive, ord 1 inner arrow of motive, ord 2 m0, ord 3 m1, ord 4 major
    | false, 5, 4 => .zero mRecMajor
    | false, 6, 0 => .never mRule0
    | false, 7, 0 => .zero mRule1
    | _, _, _ => .never {}
  require mutComplete.bindersComplete "R5: muts constant not bindersComplete"
  let (envMut, blkAddr) := block env0 mutComplete
  let decMut ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes envMut))
  let progMut ← IO.ofExcept (Src.Ingress.readAll decMut #[defnProjAddr blkAddr 1])
  let checkCtor := fun (cidx : UInt64) (pred : Term → Bool) (lbl : String) => do
    let some cid := progMut.lookup (ctorProjAddr blkAddr 0 cidx)
      | throw (IO.userError s!"R5 muts: missing {lbl}")
    match progMut.decl? cid with
    | some (.ctor _ _ _ _ _ _ ty) => require (pred ty) s!"R5 muts: {lbl} mismatch"
    | _ => throw (IO.userError s!"R5 muts: expected ctor for {lbl}")
  checkCtor 0 (fun
    | .pi b _ _ => b.mode == mCtor0 && b.propWhen == .always
    | _ => false) "ctor 0"
  checkCtor 1 (fun
    | .pi b0 _ (.pi b1 _ _) =>
      b0.mode == mCtor1a && b0.propWhen == .allZero [0] &&
      b1.mode == mCtor1b && b1.propWhen == .allZero [0, 1]
    | _ => false) "ctor 1"
  let some dCid := progMut.lookup (defnProjAddr blkAddr 1) | throw (IO.userError "R5 muts: missing defn")
  match progMut.decl? dCid with
  | some (.defn _ _ _ (.pi bt _ _) (.lam bv _ _)) =>
    require (bt.mode == mDefTy && bt.propWhen == .never)
      "R5 muts: defn type mode/datum mismatch"
    require (bv.mode == mDefVal && bv.propWhen == .allZero [1])
      "R5 muts: defn value mode/datum mismatch"
  | _ => throw (IO.userError "R5 muts: unexpected defn shape")
  let some rCid := progMut.lookup (recrProjAddr blkAddr 2) | throw (IO.userError "R5 muts: missing recr")
  match progMut.decl? rCid with
  | some (.recr _ _ _ _ _ _ _ _ [r0, r1] (.pi _ _ (.pi _ _ (.pi _ _ (.pi bm _ _))))) =>
    require (bm.mode == mRecMajor && bm.propWhen == .always)
      "R5 muts: recr major mode/datum mismatch"
    match r0.rhs, r1.rhs with
    | .lam b0 _ _, .lam b1 _ _ =>
      require (b0.mode == mRule0 && b0.propWhen == .never) "R5 muts: rule 0 mismatch"
      require (b1.mode == mRule1 && b1.propWhen == .always) "R5 muts: rule 1 mismatch"
    | _, _ => throw (IO.userError "R5 muts: unexpected rule rhs shape")
  | _ => throw (IO.userError "R5 muts: unexpected recr shape")
  n := n + 8

  -- 3c. Walking through `.share` in leading `lam` and `all` telescopes (incl. nested `.share` & HO domain)
  -- sharing[0] = lam (.ref 0 #[]) (.var 0)
  -- sharing[1] = lam (.ref 0 #[]) (.share 0)
  -- sharing[2] = all (.ref 0 #[]) (.ref 0 #[])
  -- typ = all (arrow (.ref 0 #[]) (.ref 0 #[])) (all (.ref 0 #[]) (.share 2))
  -- val = lam (arrow (.ref 0 #[]) (.ref 0 #[])) (.share 1)
  let hoDom : V3.Expr := arrow (.ref 0 #[]) (.ref 0 #[])
  let telTyp : V3.Expr := arrow hoDom (arrow (.ref 0 #[]) (.share 2))
  let telVal : V3.Expr := lambda hoDom (.share 1)
  let mT0 : AllMode := { input := .erased, result := .shared }
  let mTDom : AllMode := { input := .borrowed, result := .shared }
  let mT1 : AllMode := { input := .unique, result := .borrowed }
  let mT2 : AllMode := { input := .once, result := .unique }
  let mV0 : AllMode := { input := .unique, result := .shared }
  let mVDom : AllMode := { input := .onceBorrowed, result := .shared }
  let mV1 : AllMode := { input := .borrowed, result := .unique }
  let mV2 : AllMode := { input := .erased, result := .uniqueBorrowed }
  let telRaw : V3.Constant :=
    ⟨.defn ⟨.defn, .safe, {}, 1, telTyp, telVal⟩,
      #[lambda (.ref 0 #[]) (.var 0), lambda (.ref 0 #[]) (.share 0), arrow (.ref 0 #[]) (.ref 0 #[])],
      #[ax], #[], #[]⟩
  let telConst := completeBindersWith telRaw fun pos =>
    match pos.shared, pos.index.toNat, pos.variant.toNat, pos.ordinal with
    | false, 0, 0, 0 => .never mT0
    | false, 0, 0, 1 => .never mTDom
    | false, 0, 0, 2 => .zero mT1
    | true, 2, 0, 0 => .ifAllZero #[0] mT2
    | false, 1, 0, 0 => .never mV0
    | false, 1, 0, 1 => .never mVDom
    | true, 1, 0, 0 => .zero mV1
    | true, 0, 0, 0 => .ifAllZero #[0] mV2
    | _, _, _, _ => .never {}
  require telConst.bindersComplete "R5: leading-share telescope constant not bindersComplete"
  let (allBs, allBody) ← IO.ofExcept (leadingAllBinders telConst 0 telTyp)
  require (allBs.size == 3 && allBody == .ref 0 #[]) s!"R5: leadingAllBinders got {allBs.size} binders"
  require (allBs[0]!.1 == ⟨false, 0, 0, 0⟩ && allBs[0]!.2.1 == .never mT0) "R5: leading all 0"
  require (allBs[1]!.1 == ⟨false, 0, 0, 2⟩ && allBs[1]!.2.1 == .zero mT1) "R5: leading all 1"
  require (allBs[2]!.1 == ⟨true, 2, 0, 0⟩ && allBs[2]!.2.1 == .ifAllZero #[0] mT2)
    "R5: leading all 2 (through .share)"
  let (lamBs, lamBody) ← IO.ofExcept (leadingLamBinders telConst 1 telVal)
  require (lamBs.size == 3 && lamBody == .var 0) s!"R5: leadingLamBinders got {lamBs.size} binders"
  require (lamBs[0]!.1 == ⟨false, 1, 0, 0⟩ && lamBs[0]!.2.1 == .never mV0) "R5: leading lam 0"
  require (lamBs[1]!.1 == ⟨true, 1, 0, 0⟩ && lamBs[1]!.2.1 == .zero mV1)
    "R5: leading lam 1 (through .share 1)"
  require (lamBs[2]!.1 == ⟨true, 0, 0, 0⟩ && lamBs[2]!.2.1 == .ifAllZero #[0] mV2)
    "R5: leading lam 2 (through nested .share 0)"
  let (envTel, aTel) := store env0 telConst
  let decTel ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes envTel))
  let progTel ← IO.ofExcept (Src.Ingress.readAll decTel #[aTel])
  let some telId := progTel.lookup aTel | throw (IO.userError "R5: missing telescope def")
  match progTel.decl? telId with
  | some (.defn _ _ _
      (.pi bt0 (.pi btd _ _) (.pi bt1 _ (.pi bt2 _ _)))
      (.lam bv0 (.pi bvd _ _) (.lam bv1 _ (.lam bv2 _ _)))) =>
    require (bt0.mode == mT0 && btd.mode == mTDom &&
             bt1.mode == mT1 && bt1.propWhen == .always &&
             bt2.mode == mT2 && bt2.propWhen == .allZero [0])
      "R5: converted leading all telescope mismatch"
    require (bv0.mode == mV0 && bvd.mode == mVDom &&
             bv1.mode == mV1 && bv1.propWhen == .always &&
             bv2.mode == mV2 && bv2.propWhen == .allZero [0])
      "R5: converted leading lam telescope mismatch"
  | _ => throw (IO.userError "R5: unexpected converted telescope term")
  n := n + 11

  -- 3d. Share cache keyed by `(index, variant)`: same sharing[0] referenced with variant 0 and 1,
  -- plus binder-free sharing[1] referenced twice without consuming binder nodes
  let mVar0 : AllMode := AllMode.erased
  let mVar1 : AllMode := { input := .unique, result := .borrowed }
  let shareRaw : V3.Constant :=
    ⟨.defn ⟨.defn, .safe, {}, 0, arrow (.share 1) (.share 1), .app (.share 0) (.share 0)⟩,
      #[lambda (.ref 0 #[]) (.var 0), .ref 0 #[]], #[ax], #[], #[]⟩
  let shareConst := completeBindersWith shareRaw
    (fun pos =>
      match pos.shared, pos.index.toNat, pos.variant.toNat, pos.ordinal with
      | true, 0, 0, 0 => .never mVar0
      | true, 0, 1, 0 => .zero mVar1
      | _, _, _, _ => .never {})
    (fun pos =>
      if !pos.shared && pos.index == 1 then
        if pos.ordinal == 0 then some 0 else some 1
      else none)
  require shareConst.bindersComplete "R5: multi-variant share constant not bindersComplete"
  let (envSh, aSh) := store env0 shareConst
  let decSh ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes envSh))
  let progSh ← IO.ofExcept (Src.Ingress.readAll decSh #[aSh])
  let some shId := progSh.lookup aSh | throw (IO.userError "R5: missing share def")
  match progSh.decl? shId with
  | some (.defn _ _ _ (.pi _ (.const c0 []) (.const c1 []))
      (.app (.lam b0 _ _) (.lam b1 _ _) _ _)) =>
    require (c0 == c1) "R5: binder-free share mismatch"
    require (b0.mode == mVar0 && b0.propWhen == .never)
      "R5: share variant 0 mode/datum mismatch"
    require (b1.mode == mVar1 && b1.propWhen == .always)
      "R5: share variant 1 reused variant 0 cache entry!"
  | _ => throw (IO.userError "R5: unexpected multi-variant share term")
  n := n + 4

  -- 3e. All `letE` modes through wire + Src.Ingress
  for (nd, lm) in ([
      (false, LetMode.value .many), (true, .value .many),
      (false, .value .unique), (true, .value .erased),
      (false, .value .onceBorrowed), (false, .borrow), (true, .borrow)
    ] : List (Bool × LetMode)) do
    let letC : V3.Constant :=
      ⟨.defn ⟨.defn, .safe, {}, 0, .ref 0 #[],
        .letE nd lm (.ref 0 #[]) (.ref 0 #[]) (.var 0)⟩, #[], #[ax], #[], #[]⟩
    let (envL, aL) := store env0 letC
    let decL ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes envL))
    let progL ← IO.ofExcept (Src.Ingress.readAll decL #[aL])
    let some lId := progL.lookup aL | throw (IO.userError "R5: missing let def")
    match progL.decl? lId with
    | some (.defn _ _ _ _ (.letE nd' lm' _ _ _ _)) =>
      require (nd' == nd && lm' == lm) s!"R5: letE mode mismatch ({nd}, {repr lm})"
    | _ => throw (IO.userError "R5: expected letE")
    n := n + 1

  -- 3f. `Builder.identity` and `Support.Bound.simpleBlock`/`simpleRecursor` roundtrip cleanly
  let idC := Builder.identity ax
  require idC.bindersComplete "R5: Builder.identity not bindersComplete"
  let (envId, aId) := store env0 idC
  let decId ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes envId))
  let _ ← IO.ofExcept (Src.Ingress.readAll decId #[aId])
  let treeBlk := IxCCTests.Support.Bound.simpleBlock #[#[], #[.self, .self]]
  let (envT1, blkA) := block env0 treeBlk
  let treeRec := IxCCTests.Support.Bound.simpleRecursor blkA #[#[], #[.self, .self]]
  let (envT2, recA) := store envT1 treeRec
  let decT ← IO.ofExcept (decodeAnonymousEnv (Builder.bytes envT2))
  let progT ← IO.ofExcept (Src.Ingress.readAll decT #[recA])
  require ((progT.lookup recA).isSome && (progT.lookup (indcProjAddr blkA 0)).isSome &&
           (progT.lookup (ctorProjAddr blkA 0 0)).isSome &&
           (progT.lookup (ctorProjAddr blkA 0 1)).isSome)
    "R5: Support.Bound simpleBlock/simpleRecursor ingress failed"
  n := n + 3

  return n

/-! ## 4. N2 stored zero-ness datum fail-closed cross-check -/

def testN2StoredDatum : IO Nat := do
  let mut n := 0
  let p0 : BinderPos := ⟨false, 0, 0, 0⟩
  -- Agreement (including reordered / duplicate parameter lists)
  require (checkStoredDatum p0 (some .never) .never).isOk "N2: never vs never"
  require (checkStoredDatum p0 (some .always) .always).isOk "N2: always vs always"
  require (checkStoredDatum p0 (some (.allZero [0, 2])) (.allZero [2, 0, 2])).isOk
    "N2: reordered/dup allZero params"
  -- Advisory undecided passes checkStoredDatum, fails checkStoredDatumStrict
  require (checkStoredDatum p0 none .never).isOk "N2: undecided advisory never"
  require (checkStoredDatum p0 none .always).isOk "N2: undecided advisory always"
  require (checkStoredDatumStrict p0 none .never).toOption.isNone
    "N2: strict check accepted undecided"
  -- Fail-closed on every disagreement
  require (checkStoredDatum p0 (some .never) .always).toOption.isNone "N2: never vs always"
  require (checkStoredDatum p0 (some .never) (.allZero [0])).toOption.isNone "N2: never vs allZero"
  require (checkStoredDatum p0 (some .always) .never).toOption.isNone "N2: always vs never"
  require (checkStoredDatum p0 (some .always) (.allZero [0])).toOption.isNone "N2: always vs allZero"
  require (checkStoredDatum p0 (some (.allZero [0])) (.allZero [1])).toOption.isNone
    "N2: allZero [0] vs [1]"
  require (checkStoredDatum p0 (some (.allZero [0, 1])) (.allZero [0])).toOption.isNone
    "N2: allZero [0,1] vs [0]"
  n := n + 12

  -- Whole-term cross-check across multi-variant shared subterms & skipIrr
  let (_, ax) := Builder.base
  let shareExpr : V3.Expr := .app (.share 0) (.share 0)
  let shareRaw : V3.Constant :=
    ⟨.defn ⟨.defn, .safe, {}, 0, .ref 0 #[], shareExpr⟩,
      #[lambda (.ref 0 #[]) (.var 0)], #[ax], #[], #[]⟩
  let shareConst := completeBindersWith shareRaw
    (fun pos =>
      match pos.shared, pos.index.toNat, pos.variant.toNat, pos.ordinal with
      | true, 0, 0, 0 => .never AllMode.erased
      | true, 0, 1, 0 => .zero AllMode.unique
      | _, _, _, _ => .never {})
    (fun pos => if !pos.shared && pos.index == 1 && pos.ordinal == 1 then some 1 else some 0)
  require shareConst.bindersComplete "N2: multi-variant test record incomplete"
  -- Single-position lookup checks
  require (checkBinderDatumAt shareConst ⟨true, 0, 0, 0⟩ .never).isOk "N2: pos (true,0,0,0) ok"
  require (checkBinderDatumAt shareConst ⟨true, 0, 1, 0⟩ .always).isOk "N2: pos (true,0,1,0) ok"
  require (checkBinderDatumAt shareConst ⟨true, 0, 1, 0⟩ .never).toOption.isNone
    "N2: pos (true,0,1,0) disagreement accepted"
  require (checkBinderDatumAt shareConst ⟨false, 1, 0, 0⟩ .never).toOption.isNone
    "N2: share node accepted as binder datum"
  require (checkBinderDatumAt shareConst ⟨true, 0, 9, 0⟩ .never).toOption.isNone
    "N2: missing pos accepted"
  -- Whole-term checks: agreeing term passes, tampered variant 1 fails closed
  let goodTerm : Term :=
    .app (.lam { mode := AllMode.erased, propWhen := .never } (.const 0 []) (.var 0))
         (.lam { mode := AllMode.unique, propWhen := .always } (.const 0 []) (.var 0))
         .strict .rel
  let badTerm : Term :=
    .app (.lam { mode := AllMode.erased, propWhen := .never } (.const 0 []) (.var 0))
         (.lam { mode := AllMode.unique, propWhen := .never } (.const 0 []) (.var 0))
         .strict .rel
  require (checkTermBinderData shareConst 1 shareExpr goodTerm).isOk
    "N2: checkTermBinderData rejected agreeing shared term"
  require (checkTermBinderData shareConst 1 shareExpr badTerm).toOption.isNone
    "N2: checkTermBinderData accepted disagreeing shared variant 1"
  -- Irrelevant argument skipped when skipIrr = true, caught when skipIrr = false
  let irrArgTerm : Term :=
    .app (.lam { mode := AllMode.erased, propWhen := .never } (.const 0 []) (.var 0))
         (.lam { mode := AllMode.unique, propWhen := .never } (.const 0 []) (.var 0))
         .strict .type
  require (checkTermBinderData shareConst 1 shareExpr irrArgTerm (skipIrr := true)).isOk
    "N2: skipIrr = true did not skip type-irrelevant argument"
  require (checkTermBinderData shareConst 1 shareExpr irrArgTerm (skipIrr := false)).toOption.isNone
    "N2: skipIrr = false did not catch disagreement inside irrelevant argument"
  -- Undecided stored datum: advisory passes, strict fails closed
  let undecConst := completeBindersWith shareRaw (fun _ => .undecided {})
  require (checkTermBinderData undecConst 1 shareExpr goodTerm (allowUndecided := true)).isOk
    "N2: allowUndecided = true rejected undecided datum"
  require (checkTermBinderData undecConst 1 shareExpr goodTerm (allowUndecided := false)).toOption.isNone
    "N2: allowUndecided = false accepted undecided datum"
  n := n + 12

  return n

def run (root : System.FilePath) : IO Nat := do
  let n1 ← testModesAndExprs root
  let n2 ← testN6RejectParity root
  let n3 ← testR5Ingress
  let n4 ← testN2StoredDatum
  let total := n1 + n2 + n3 + n4
  IO.println s!"ixon-v5-ingress-ok: {total} assertions (modes/exprs={n1}, N6={n2}, R5={n3}, N2={n4})"
  return total

end IxCCTests.IxonV3.Ingress
