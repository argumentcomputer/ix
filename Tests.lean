import Compilatrix

/-!
Runtime test executable: everything that must *execute* FFI (blake3)
lives here, compiled and linked against the static lib — elaboration-
time `#guard`s can't run FFI (no dynlib in the interpreter). Run by the
flake's `tests` check; prints `tests-ok` on success.
-/

open Compilatrix.Ixon

/-- The universal BLAKE3 empty-input test vector:
`af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262`. -/
def expectedEmptyBlake3 : List Nat :=
  [0xaf, 0x13, 0x49, 0xb9, 0xf5, 0xf9, 0xa1, 0xa6,
   0xa0, 0x40, 0x4d, 0xea, 0x36, 0xdc, 0xc9, 0x49,
   0x9b, 0xcb, 0x25, 0xc9, 0xad, 0xc1, 0x12, 0xb7,
   0xcc, 0x9a, 0x93, 0xca, 0xe4, 0x1f, 0x32, 0x62]

/-- Golden address of the sample axiom below. Deliberately
format-freezing: any change to the Ixon v2 canonical encoding breaks
this — bump it only with an intentional format roll. -/
def expectedSampleAxiomAddr : List Nat :=
  [175, 190, 20, 2, 194, 88, 190, 182, 79, 114, 28, 108, 112, 136,
   43, 71, 254, 192, 235, 145, 134, 231, 227, 179, 11, 181, 74, 208,
   29, 62, 109, 135]

/-- Golden layer-2 address of `goldenV2` (the 110-byte format-freezing
fixture in `Const.lean`):
`ee10cc174c8a467a1803bb8f6a04b23fb7eb9218aa76db44953b22ab495acd74`.
Like `expectedSampleAxiomAddr`, this freezes the canonical encoding
*and* the layer-2 sharing acceptance of the fixture — bump only with
an intentional format roll. -/
def expectedGoldenV2Addr : List Nat :=
  [238, 16, 204, 23, 76, 138, 70, 122, 24, 3, 187, 143, 106, 4,
   178, 63, 183, 235, 146, 24, 170, 118, 219, 68, 149, 59, 34, 171,
   73, 90, 205, 116]

def hashNats (a : Address) : List Nat :=
  a.hash.data.toList.map (fun (b : UInt8) => b.toNat)

/-! The six structural cases in ix's pinned Lean/Rust sharing parity suite,
translated mechanically to Ixon v2's `.many`/`.shared` Lean fragment. -/

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

/-- Mechanical `.many`/`.shared` translation of ix's eight-entry v1 output.
The v2 exact-byte audit intentionally does not retain this nested table. -/
def ixForallImpRealOutput : Sharing.Compression :=
  { bodies := #[
      all (.sort 0)
        (all (.share 6)
          (all (.share 7)
            (all (.share 5)
              (all (.share 4) (all (.var 4) (.share 3)))))),
      lam (.sort 0)
        (lam (.share 6)
          (lam (.share 7)
            (lam (.share 5)
              (lam (.share 4)
                (lam (.var 4)
                  (.app (.share 1) (.app (.var 1) (.var 0))))))))]
    table := #[
      .app (.var 2) (.var 1),
      .app (.var 2) (.var 0),
      all (.share 1) (.share 0),
      .app (.var 3) (.var 0),
      all (.var 3) (.share 3),
      all (.var 2) (.share 2),
      all (.var 0) (.sort 1),
      all (.var 1) (.sort 1)] }

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

/-- Mechanical v2-mode annotation of ix's two-entry `flip` output. -/
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

/-- `8c712eab0db958befe94bda3a40998debe172243dd5771f62d0cd915074f5097`.
Bump only after reviewing both the pinned ix vector and the intended v2
output for every case. -/
def expectedFingerprint : List Nat :=
  [140, 113, 46, 171, 13, 185, 88, 190,
   254, 148, 189, 163, 164, 9, 152, 222,
   190, 23, 34, 67, 221, 87, 113, 246,
   45, 12, 217, 21, 7, 79, 80, 151]

end SharingPolicy

def main : IO UInt32 := do
  let mut ok := true

  let overlongTrimmed : ByteArray := ⟨Array.replicate 9 0⟩
  match runGet (getU64TrimmedLE 9) overlongTrimmed with
  | .error message =>
    if message != "getU64TrimmedLE: byte length 9 exceeds 8" then
      IO.eprintln s!"FAIL: unexpected overlong u64 error: {message}"
      ok := false
  | .ok value =>
    IO.eprintln s!"FAIL: accepted a nine-byte trimmed u64 as {value}"
    ok := false

  if Sharing.compressorPolicyId != "compilatrix/ixon-v2-sharing/1" then
    IO.eprintln s!"FAIL: unexpected compressor policy id {Sharing.compressorPolicyId}"
    ok := false
  if Sharing.ixParityRevision !=
      "c98bb74106017e518c705b2567f022e89f732393" then
    IO.eprintln s!"FAIL: unexpected ix parity revision {Sharing.ixParityRevision}"
    ok := false
  if hashNats SharingPolicy.fingerprint != SharingPolicy.expectedFingerprint then
    IO.eprintln s!"FAIL: sharing policy fingerprint changed: {hashNats SharingPolicy.fingerprint}"
    ok := false

  for c in SharingPolicy.cases do
    let actual := Sharing.compressUnchecked c.input
    if actual != c.v2Output then
      IO.eprintln s!"FAIL: v2 policy vector changed for {c.name}: {repr actual}"
      ok := false
    if c.ixOutput.expanded != c.input then
      IO.eprintln s!"FAIL: transcribed ix vector does not recover {c.name}"
      ok := false
    if c.v2Output.expanded != c.input then
      IO.eprintln s!"FAIL: pinned v2 vector does not recover {c.name}"
      ok := false
    match c.relation with
    | .exactParity =>
      if c.ixOutput != c.v2Output || actual != c.ixOutput then
        IO.eprintln s!"FAIL: common-case ix parity changed for {c.name}"
        ok := false
    | .intentionalV2Delta =>
      if c.ixOutput == c.v2Output then
        IO.eprintln s!"FAIL: declared v2 delta collapsed for {c.name}"
        ok := false
    if Sharing.compress? c.input != some c.v2Output then
      IO.eprintln s!"FAIL: checked compressor diverged from policy vector for {c.name}"
      ok := false
    if !Sharing.layer1WF c.v2Output.table c.v2Output.bodies ||
        !Sharing.deletionLocalOptimal c.v2Output ||
        !Sharing.allEntriesPay c.v2Output ||
        !Sharing.canonical c.v2Output.bodies c.v2Output.table then
      IO.eprintln s!"FAIL: pinned v2 vector violates compressor postconditions for {c.name}"
      ok := false

  let empty := Address.blake3 (ByteArray.mk #[])
  if empty.hash.size != 32 then
    IO.eprintln s!"FAIL: hash size = {empty.hash.size}"
    ok := false
  if hashNats empty != expectedEmptyBlake3 then
    IO.eprintln s!"FAIL: blake3(empty) = {hashNats empty}"
    IO.eprintln s!"      expected       {expectedEmptyBlake3}"
    ok := false

  if !(Address.blake3 (ByteArray.mk #[1, 2, 3])
      == Address.blake3 (ByteArray.mk #[1, 2, 3])) then
    IO.eprintln "FAIL: blake3 nondeterministic"
    ok := false
  if Address.blake3 (ByteArray.mk #[1, 2, 3])
      == Address.blake3 (ByteArray.mk #[1, 2, 4]) then
    IO.eprintln "FAIL: blake3 input-insensitive"
    ok := false

  if Sharing.exprHash (.lam .many (.sort 0) (.var 0)) ==
      Sharing.exprHash (.lam .linear (.sort 0) (.var 0)) then
    IO.eprintln "FAIL: sharing Merkle hash omitted the v2 lambda mode"
    ok := false

  let repeated : Expr := .ref 17 #[0, 1, 2]
  let repeatedInput : Array Expr := #[repeated, repeated, repeated]
  match Sharing.compress? repeatedInput with
  | none =>
    IO.eprintln "FAIL: compressor rejected share-free repeated input"
    ok := false
  | some out =>
    let expectedBodies : Array Expr := #[.share 0, .share 0, .share 0]
    let expectedTable : Array Expr := #[repeated]
    if out.bodies != expectedBodies || out.table != expectedTable then
      IO.eprintln s!"FAIL: unexpected canonical compression {repr out}"
      ok := false
    if out.bodies.map (Sharing.inlineExpr out.table) != repeatedInput then
      IO.eprintln "FAIL: inlining compressed roots did not recover input"
      ok := false
    if !Sharing.deletionLocalOptimal out || !Sharing.allEntriesPay out then
      IO.eprintln "FAIL: compressor output failed the exact deletion audit"
      ok := false
    if !Sharing.canonical out.bodies out.table then
      IO.eprintln "FAIL: compressor output was not a recompression fixpoint"
      ok := false

  -- Both the lambda and its repeated domain are initially profitable. Once
  -- the lambda is shared, the domain occurs only once in residual syntax, so
  -- the exact audit must remove that stale nested candidate.
  let nestedLeaf : Expr := .ref 23 #[0, 1, 2]
  let nested : Expr := .lam .many nestedLeaf (.var 0)
  let nestedInput : Array Expr := #[nested, nested, nested]
  match Sharing.compress? nestedInput with
  | none =>
    IO.eprintln "FAIL: compressor rejected nested repeated input"
    ok := false
  | some out =>
    if out.table != #[nested] || out.bodies != #[.share 0, .share 0, .share 0] then
      IO.eprintln s!"FAIL: exact audit retained a stale nested candidate {repr out}"
      ok := false
    if out.bodies.map (Sharing.inlineExpr out.table) != nestedInput then
      IO.eprintln "FAIL: audited nested compression did not inline to input"
      ok := false
    if !Sharing.deletionLocalOptimal out || !Sharing.allEntriesPay out ||
        !Sharing.canonical out.bodies out.table then
      IO.eprintln "FAIL: audited nested compression failed its postconditions"
      ok := false

  let compressionCorpus : Array (Array Expr) := #[
    #[],
    repeatedInput,
    nestedInput,
    #[.sort 0, .var 0, .nat 0],
    #[.ref 130 #[0, 129], .ref 130 #[0, 129], .ref 130 #[0, 129]],
    #[.lam .many (.ref 9 #[0]) (.var 0),
      .lam .many (.ref 9 #[0]) (.var 0),
      .lam .linear (.ref 9 #[0]) (.var 0)],
    #[.letE false (.sort 0) repeated (.app (.var 0) repeated),
      .letE false (.sort 0) repeated (.app (.var 0) repeated)],
    #[.prj 0 1 repeated, .prj 0 1 repeated, .prj 0 1 repeated],
    #[.app (.app (.ref 3 #[]) repeated) repeated,
      .app (.app (.ref 3 #[]) repeated) repeated]
  ]
  for input in compressionCorpus do
    match Sharing.compress? input with
    | none =>
      IO.eprintln s!"FAIL: compressor rejected corpus input {repr input}"
      ok := false
    | some out =>
      let heuristic := Sharing.compressUnchecked input
      if !Sharing.layer1WF heuristic.table heuristic.bodies ||
          !Sharing.allEntriesPay heuristic then
        IO.eprintln s!"FAIL: raw heuristic violated its corpus invariants {repr heuristic}"
        ok := false
      if out != heuristic then
        IO.eprintln s!"FAIL: certified fallback unexpectedly activated {repr input}"
        ok := false
      if Sharing.compress? input != some out then
        IO.eprintln "FAIL: compressor was nondeterministic"
        ok := false
      if !Sharing.layer1WF out.table out.bodies then
        IO.eprintln s!"FAIL: compressor emitted a non-layer-1 table {repr out}"
        ok := false
      if out.bodies.map (Sharing.inlineExpr out.table) != input then
        IO.eprintln s!"FAIL: corpus compression did not inline to input {repr out}"
        ok := false
      if !Sharing.deletionLocalOptimal out || !Sharing.allEntriesPay out then
        IO.eprintln s!"FAIL: corpus compression retained a non-paying entry {repr out}"
        ok := false
      if !Sharing.canonical out.bodies out.table then
        IO.eprintln s!"FAIL: corpus output was not canonical {repr out}"
        ok := false

  let c : Constant :=
    { info := .axio { isUnsafe := false, lvls := 1, typ := .sort 3 }
      sharing := #[], refs := #[], univs := #[.zero] }
  match c.address? with
  | none =>
    IO.eprintln "FAIL: well-formed sample axiom was not addressable"
    ok := false
  | some address =>
    if hashNats address != expectedSampleAxiomAddr then
      IO.eprintln s!"FAIL: addr(sampleAxiom) = {hashNats address}"
      IO.eprintln s!"      expected           {expectedSampleAxiomAddr}"
      ok := false

  match goldenV2.address? with
  | none =>
    IO.eprintln "FAIL: goldenV2 fixture was not layer-2 addressable"
    ok := false
  | some address =>
    if hashNats address != expectedGoldenV2Addr then
      IO.eprintln s!"FAIL: addr(goldenV2) = {hashNats address}"
      IO.eprintln s!"      expected        {expectedGoldenV2Addr}"
      ok := false

  let merelyLayer1 : Constant :=
    { info := .axio
        { isUnsafe := false, lvls := 0
          typ := .app (.share 0) (.share 0) }
      sharing := #[.sort 0], refs := #[], univs := #[] }
  if !merelyLayer1.sharingWF then
    IO.eprintln "FAIL: noncanonical identity fixture was not layer-1 valid"
    ok := false
  if merelyLayer1.canonicalSharing then
    IO.eprintln "FAIL: redundant small sharing table passed layer 2"
    ok := false
  if merelyLayer1.address?.isSome then
    IO.eprintln "FAIL: merely layer-1 constant crossed the address boundary"
    ok := false

  if ok then
    IO.println "tests-ok"
    return 0
  else
    return 1
