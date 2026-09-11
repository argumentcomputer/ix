import Ix.Compiler.Tools.UniqueCheck

namespace Benchmarks.Compiler

open Lean Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck

def workload : String := "native-reverse/1"
def datasetMagic : String := "CPBN001\n"
def scheduleMagic : String := "CPBS001\n"
def baseSeed : UInt64 := 0x6a09e667f3bcc909
def chunkSize : Nat := 4096
def primaryLimit : Nat := 2^30

def word? (value : Nat) : Option UInt64 :=
  if value < UInt64.size then some value.toUInt64 else none

structure Input where
  id : Nat
  length : Nat
  pattern : Nat
  domain : Nat
  seed : UInt64
  values : Array UInt64
  deriving Inhabited

def Input.name (input : Input) : String :=
  s!"n{input.length}-p{input.pattern}"

def patternName (pattern : Nat) : String :=
  (#[("zero" : String), "repeated", "ascending", "descending", "alternating", "random",
    "2^63-1", "2^63", "2^64-1"])[pattern]!

def domainName (domain : Nat) : String :=
  (#[("primary" : String), "stress-2^63-1", "stress-2^63", "stress-2^64-1"])[domain]!

def nextRandom (state : UInt64) : UInt64 :=
  let state := state ^^^ (state >>> 12)
  let state := state ^^^ (state <<< 25)
  state ^^^ (state >>> 27)

def input (length pattern : Nat) : Input := Id.run do
  let seed := baseSeed ^^^ ((length.toUInt64 + 1) * 0x9e3779b97f4a7c15)
  let mut state := seed
  let mut values := #[]
  for index in [:length] do
    state := nextRandom state
    let value : UInt64 := match pattern with
      | 0 => 0
      | 1 => 17
      | 2 => index.toUInt64
      | 3 => (length - index - 1).toUInt64
      | 4 => if index % 2 == 0 then 0 else (primaryLimit - 1).toUInt64
      | 5 => (state * 0x2545f4914f6cdd1d) &&& (primaryLimit - 1).toUInt64
      | 6 => 0x7fffffffffffffff
      | 7 => 0x8000000000000000
      | _ => 0xffffffffffffffff
    values := values.push value
  return { id := length * 9 + pattern, length, pattern
           domain := if pattern < 6 then 0 else pattern - 5
           seed, values }

def inputs : Array Input := Id.run do
  let mut cases := #[]
  for length in [:65] do
    for pattern in [:9] do cases := cases.push (input length pattern)
  return cases

/-- Each list contributes a word-sized, order- and payload-sensitive digest.
All arithmetic wraps modulo 2^64. Full correctness compares every value. -/
def listDigest (values : Array UInt64) : UInt64 :=
  values.foldl (fun hash value => (hash ^^^ value) * 0x100000001b3) 0xcbf29ce484222325

def Input.expectedDigest (input : Input) : UInt64 := listDigest input.values.reverse

def wordBytes (value : UInt64) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for index in [:8] do bytes := bytes.push (value >>> (8 * index).toUInt64).toUInt8
  return bytes

def Input.bytes (input : Input) : ByteArray := Id.run do
  let mut bytes := wordBytes input.length.toUInt64 ++ wordBytes input.pattern.toUInt64 ++
    wordBytes input.domain.toUInt64 ++ wordBytes input.seed
  for index in [:64] do bytes := bytes ++ wordBytes (input.values[index]?.getD 0)
  return bytes

def datasetBytes : ByteArray :=
  inputs.foldl (fun bytes input => bytes ++ input.bytes)
    (datasetMagic.toUTF8 ++ wordBytes inputs.size.toUInt64)

def Input.json (input : Input) : Json :=
  Json.mkObj [
    ("id", toJson input.id), ("name", toJson input.name), ("length", toJson input.length),
    ("pattern", toJson (patternName input.pattern)), ("domain", toJson (domainName input.domain)),
    ("seed", toJson input.seed.toNat), ("values", toJson (input.values.map UInt64.toNat)),
    ("expected", toJson (input.values.reverse.map UInt64.toNat)),
    ("expected_digest", toJson input.expectedDigest.toNat)]

structure TimingCase where
  length : Nat
  domain : Nat
  profile : Nat
  deriving BEq, Repr, Inhabited

def TimingCase.profileName (row : TimingCase) : String :=
  if row.profile == 0 then "entry+handoff" else "lifecycle"

def TimingCase.name (row : TimingCase) : String :=
  s!"{domainName row.domain}-n{row.length}-{row.profileName}"

def TimingCase.inputIds (row : TimingCase) : Array Nat :=
  if row.domain == 0 then (List.range 6).toArray.map (row.length * 9 + ·)
  else #[row.length * 9 + row.domain + 5]

def timingCases : Array TimingCase := Id.run do
  let mut rows := #[]
  for profile in [:2] do
    for length in [0, 1, 2, 4, 8, 16, 32, 48, 63, 64] do
      rows := rows.push { length, domain := 0, profile }
    for domain in [1, 2, 3] do
      for length in [1, 16, 64] do rows := rows.push { length, domain, profile }
  return rows

def TimingCase.json (row : TimingCase) : Json :=
  Json.mkObj [("name", toJson row.name), ("length", toJson row.length),
    ("domain", toJson (domainName row.domain)), ("profile", toJson row.profileName),
    ("input_ids", toJson row.inputIds), ("capacity", toJson (row.length + 2))]

def datasetJson : Json :=
  Json.mkObj [
    ("format", toJson "compilatrix/benchmark-datasets/1"), ("workload", toJson workload),
    ("generator", toJson "xorshift64star-patterns/1"), ("seed", toJson baseSeed.toNat),
    ("binary", toJson "datasets.bin"), ("binary_bytes", toJson datasetBytes.size),
    ("binary_blake3", toJson (digest datasetBytes)),
    ("cases", toJson (inputs.map Input.json)), ("timing_cases", toJson (timingCases.map TimingCase.json))]

def checkData : IO Unit := do
  need (inputs.size == 585 && datasetBytes.size == 318256 && timingCases.size == 38)
    "benchmark dataset inventory drifted"
  need (word? UInt64.size == none && word? (UInt64.size + 1) == none &&
      (word? (UInt64.size - 1)).map UInt64.toNat == some (UInt64.size - 1))
    "benchmark Word admission wrapped a Nat"
  let mut capacityCases := 0
  for index in [:inputs.size] do
    let input := inputs[index]!
    need (input.id == index && input.length ≤ 64 && input.values.size == input.length && input.bytes.size == 544)
      "benchmark input shape disagrees"
    if input.domain == 0 then
      need (input.values.all (fun word => word.toNat < primaryLimit)) "primary input needs boxing outside the common range"
    capacityCases := capacityCases + (65 - input.length)
  need (capacityCases == 19305) "benchmark capacity inventory drifted"

def writeDatasets (output : System.FilePath) : IO Unit := do
  checkData
  need (!(← output.pathExists)) "benchmark datasets require a fresh output directory"
  IO.FS.createDirAll output
  IO.FS.writeBinFile (output / "datasets.bin") datasetBytes
  IO.FS.writeFile (output / "datasets.json") (datasetJson.pretty 120 ++ "\n")

end Benchmarks.Compiler
