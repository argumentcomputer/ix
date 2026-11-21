import IxAIVerify.Spec

/-!
# The public statement of a compressed `aiurExec` root

Ix's compression pipeline turns an aggregate root (a STARK proof, its verifying key and its claim)
into one gnark PLONK proof over BN254 whose only public inputs are the two little-endian 128-bit
halves of a 32-byte statement. This module computes that statement from what a consumer expects,
without reading the certificate or any file of the prover. The derivation is Ix's:

1. The root statement (`stark_verifier::compress_wrap::Statement`):
   `S_root = BLAKE3("ix/compress-wrap/v1\0" ‖ BLAKE3(root key) ‖ BLAKE3(claims_bytes(root claims)))`,
   where `claims_bytes` is `u64(#claims) ‖ (u64(#words) ‖ u64(word)…)…`, little-endian.
2. The wrapper (`CompressWrap::verify_root`) proves the claim `[1, 0] ‖ 0⁸ ‖ words(S_root)`: the
   call tag and entry of the wrapper (`WrapPolicy::claim_prefix`), eight reserved zeros and
   `S_root` as eight little-endian `u32` words (`stark_verifier::digest_words`).
3. CompressGL, the narrow stage and the terminal carry one statement, `WrapPolicy::statement_for`:
   `S = BLAKE3("ix/compress-wrap/v1\0" ‖ BLAKE3(wrapper key) ‖ BLAKE3(claims_bytes([wrapper claim])))`.
   Its two halves are the PLONK circuit's public inputs (`final_program::statement_arguments`).

The `aiurExec` root claim (`AiurExec::aiur_exec`, fork `ix-aiurexec`) is 18 words,
`[1, entry] ‖ words(BLAKE3(identity)) ‖ words(BLAKE3(output))`:

* identity (80 bytes): `BLAKE3(program key) ‖ u64(program entry) ‖ BLAKE3(aggregator key) ‖
  u64(aggregator entry)`;
* output (104 bytes): `u64(count) ‖ BLAKE3(enc m₀) ‖ BLAKE3(enc mₙ) ‖ data root`, with `enc` each
  word modulo the Goldilocks prime as a little-endian `u64`.

The data root depends on the program the root aggregates (`ExecShape`). The keys and entries come
from recompiling the approved packages (`aiur_exec_check` prints them); everything else here comes
from the specification, the expected model and, for one `train_tree` execution, the intermediate
models it hashed.
-/

namespace IxAIVerify.Compression

open IxAI IxAIVerify

/-- `n mod 2⁶⁴` as eight little-endian bytes. -/
def u64le (n : Nat) : ByteArray :=
  ⟨(List.range 8).toArray.map fun i => ((n >>> (8 * i)) % 256).toUInt8⟩

/-- A signed word as the circuit's Goldilocks field element. -/
def fieldWord (v : Int) : Nat := (v % goldilocks).toNat

/-- Words as the aggregator hashes them: each field element as a little-endian `u64`. The
specification; `encWords` computes the same bytes into one buffer. -/
def encWordsSpec (vs : List Int) : ByteArray :=
  vs.foldl (fun b v => b ++ u64le (fieldWord v)) ByteArray.empty

/-- `encWordsSpec`, written into one preallocated buffer (`IxAIVerifyTest` checks the equality). -/
def encWords (vs : List Int) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (8 * vs.length)
  for v in vs do
    let n := fieldWord v
    for i in [0:8] do b := b.push ((n >>> (8 * i)) % 256).toUInt8
  return b

/-- A digest as eight little-endian `u32` words. -/
def digestWords (d : Digest) : List Nat :=
  (List.range 8).map fun i =>
    (List.range 4).foldl (fun acc j => acc + (d.bytes.get! (4 * i + j)).toNat <<< (8 * j)) 0

/-- `stark_verifier::claims_bytes`: the claim count, then each claim's length and words. -/
def claimsBytes (claims : List (List Nat)) : ByteArray :=
  claims.foldl (fun b c => c.foldl (fun b w => b ++ u64le w) (b ++ u64le c.length)) (u64le claims.length)

def statementDomain : ByteArray := "ix/compress-wrap/v1".toUTF8.push 0

/-- `compress_wrap::Statement` of a key and its claims, as one digest. -/
def wrapStatement (key : Digest) (claims : List (List Nat)) : Digest :=
  blake3 (statementDomain ++ key.bytes ++ (blake3 (claimsBytes claims)).bytes)

/-- What a consumer pins about the compression pipeline before training: the BLAKE3 of the
terminal PLONK verifying key (which fixes the terminal circuit, the stages it embeds and the KZG
setup points the verification equation uses) and the BLAKE3 of the wrapper key the statement names
(`m16384w64-v3.layout.json`'s `key_blake3`). -/
structure Pin where
  plonkKey : Digest
  wrapKey : Digest
  deriving BEq, Repr

/-- The call tag and entry index of `CompressWrap::verify_root` in the wrapper's claim. -/
def wrapClaimPrefix : List Nat := [1, 0]

/-- The terminal statement of a root with key digest `rootKey` and the one claim `rootClaim`,
through the wrapper whose key has digest `wrapKey`. -/
def terminalStatement (wrapKey rootKey : Digest) (rootClaim : List Nat) : Digest :=
  let root := wrapStatement rootKey [rootClaim]
  wrapStatement wrapKey [wrapClaimPrefix ++ List.replicate 8 0 ++ digestWords root]

/-- The little-endian `u64` at byte `off`. -/
def readU64 (b : ByteArray) (off : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc + (b.get! (off + i)).toNat <<< (8 * i)) 0

/-- The claims of a `claims_bytes` file (`root-claims.bin`), each word a canonical Goldilocks
element. `none` unless the bytes are exactly `claimsBytes` of what is returned, so the statement
built from the result hashes the same bytes the file holds. -/
def decodeClaims (b : ByteArray) : Option (List (List Nat)) := do
  guard (b.size % 8 == 0)
  let ws := (List.range (b.size / 8)).map fun i => readU64 b (8 * i)
  let n :: rest := ws | none
  let claims ← go n rest
  guard (claims.all (·.all (· < goldilocks.toNat)))
  guard ((claimsBytes claims).data == b.data)
  pure claims
where
  go : Nat → List Nat → Option (List (List Nat))
    | 0, [] => some []
    | 0, _ :: _ => none
    | _ + 1, [] => none
    | k + 1, len :: ws =>
      if ws.length < len then none else do
        pure (ws.take len :: (← go k (ws.drop len)))

/-- The PLONK public inputs: the statement's two little-endian 128-bit halves. -/
def statementLimbs (s : Digest) : Nat × Nat :=
  let le := fun (lo : Nat) => (List.range 16).foldr (fun j acc => acc * 256 + (s.bytes.get! (lo + j)).toNat) 0
  (le 0, le 16)

/-! ## The `aiurExec` root claim -/

/-- The recompiled keys an `aiurExec` root names: the aggregator's (the root key) and the
aggregated program's, each by BLAKE3 with its entry index. -/
structure ExecKeys where
  aggregator : Digest
  aggregatorEntry : Nat
  program : Digest
  programEntry : Nat
  deriving BEq, Repr

def execIdentity (k : ExecKeys) : ByteArray :=
  k.program.bytes ++ u64le k.programEntry ++ k.aggregator.bytes ++ u64le k.aggregatorEntry

def execOutput (count : Nat) (m0 mn : List Int) (data : Digest) : ByteArray :=
  u64le count ++ (blake3 (encWords m0)).bytes ++ (blake3 (encWords mn)).bytes ++ data.bytes

def execRootClaim (aggregatorEntry : Nat) (identity output : Digest) : List Nat :=
  [1, aggregatorEntry] ++ digestWords identity ++ digestWords output

/-- An inner node of the aggregation's data tree. -/
def execNode (l r : Digest) : Digest := blake3 (ByteArray.mk #[1] ++ l.bytes ++ r.bytes)

/-- One level of the aggregation's data tree: adjacent nodes joined, an odd last node carried. -/
def execLevel : List Digest → List Digest
  | l :: r :: rest => execNode l r :: execLevel rest
  | rest => rest

/-- The aggregation's data root over the executions' leaves, level by level. -/
def execDataRoot (leaves : List Digest) : Digest :=
  go leaves leaves.length
where
  go (level : List Digest) : Nat → Digest
    | 0 => level.headD default
    | fuel + 1 => match level with
      | [d] => d
      | _ => go (execLevel level) fuel

/-- Words as `FixedTree` hashes them: the two little-endian bytes of `v + 32768`. -/
def enc16 (vs : List Int) : Option ByteArray :=
  vs.foldlM (init := ByteArray.empty) fun b v =>
    let u := v + 32768
    if 0 ≤ u ∧ u < 65536 then some ((b.push (u.toNat % 256).toUInt8).push (u.toNat / 256).toUInt8)
    else none

/-- `FixedTree::range`'s root: the first `⌊n/2⌋` leaves and the rest, joined by BLAKE3 of the two
children. -/
def treeRoot (leaves : List Digest) : Digest :=
  go leaves leaves.length
where
  go (ls : List Digest) : Nat → Digest
    | 0 => ls.headD default
    | fuel + 1 => match ls with
      | [d] => d
      | _ =>
        let k := ls.length / 2
        blake3 ((go (ls.take k) fuel).bytes ++ (go (ls.drop k) fuel).bytes)

/-- The program an `aiurExec` root aggregates, which fixes its data root.
* `steps`: one `Fixed::step` execution per batch; leaf `H(enc(xs ‖ ts ‖ lr))`.
* `blocks n`: one `Fixed::train_block` execution per `n` consecutive batches; leaf
  `H(enc(lr ‖ xs ‖ ts))` over the block's batches.
* `tree models`: one `FixedTree::train_tree` execution of every batch; its data is
  `lr ‖ R`, `R` the BLAKE3 tree over leaves `H(enc16(mᵢ₊₁) ‖ enc16(xsᵢ) ‖ enc16(tsᵢ))`, with
  `models` the model after each step. -/
inductive ExecShape where
  | steps
  | blocks (n : Nat)
  | tree (models : List (List Int))

def ExecShape.label : ExecShape → String
  | .steps => "Fixed::step executions"
  | .blocks n => s!"Fixed::train_block executions of {n} steps"
  | .tree _ => "one FixedTree::train_tree execution"

/-- The number of executions and the data root, for batches given as `(xs, ts)` words. -/
def execData (shape : ExecShape) (lr : Int) (batches : List (List Int × List Int)) :
    Except String (Nat × Digest) := do
  if batches.isEmpty then throw "no batches"
  match shape with
  | .steps =>
    return (batches.length, execDataRoot (batches.map fun (x, t) => blake3 (encWords (x ++ t ++ [lr]))))
  | .blocks n =>
    unless n > 0 && batches.length % n == 0 do
      throw s!"{batches.length} batches are not whole blocks of {n}"
    let blocks := (List.range (batches.length / n)).map fun i => (batches.drop (i * n)).take n
    return (blocks.length, execDataRoot (blocks.map fun b =>
      blake3 (encWords ([lr] ++ (b.map (·.1)).flatten ++ (b.map (·.2)).flatten))))
  | .tree models =>
    unless models.length == batches.length do
      throw s!"{models.length} intermediate models for {batches.length} steps"
    let leaves ← (models.zip batches).mapM fun (m, x, t) =>
      match enc16 m, enc16 x, enc16 t with
      | some a, some b, some c => pure (blake3 (a ++ b ++ c))
      | _, _, _ => throw "a word outside 16 bits in a tree leaf"
    let r := treeRoot leaves
    return (1, blake3 (encWords (lr :: r.bytes.toList.map fun b => (b.toNat : Int))))

/-- The terminal statement of an `aiurExec` root that chains `batches` from `m0` to `mn` through
the keys `keys`, compressed through the wrapper key `wrapKey`. -/
def execStatement (wrapKey : Digest) (keys : ExecKeys) (shape : ExecShape) (lr : Int)
    (m0 mn : List Int) (batches : List (List Int × List Int)) : Except String Digest := do
  let (count, data) ← execData shape lr batches
  let out := blake3 (execOutput count m0 mn data)
  let claim := execRootClaim keys.aggregatorEntry (blake3 (execIdentity keys)) out
  return terminalStatement wrapKey keys.aggregator claim

/-- `key: aggregator|program BLAKE3 entry N`, as `aiur_exec_check` prints the keys it recompiled. -/
def parseKeyLine (role : String) (out : String) : Option (Digest × Nat) :=
  (out.splitOn "\n").findSome? fun l =>
    match words l with
    | ["key:", r, d, "entry", n] =>
      if r == role then do pure (← Digest.ofHex? d, ← n.toNat?) else none
    | _ => none

def parseExecKeys (out : String) : Option ExecKeys := do
  let (a, ae) ← parseKeyLine "aggregator" out
  let (p, pe) ← parseKeyLine "program" out
  pure { aggregator := a, aggregatorEntry := ae, program := p, programEntry := pe }

end IxAIVerify.Compression
