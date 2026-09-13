/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.DomainAccumulator
import Ix.Aiur.Proofs.Quotient
import Tests.Aiur.EmissionReader

/-! Native domain selectors for every supported logarithm, complete small
cosets, and the quotient arithmetic with both accepting and rejecting cases.
The native domain methods are called directly; quotient fixtures reproduce
the verifier's private iterator expression using native basis and field APIs.
-/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader
open ProofCodec (Extension)

namespace AiurTests.Domain

private def readExtension : Reader Extension := do return ⟨← readField, ← readField⟩

private def readSelectors : Reader (NativeAIR.Domain.Selectors Extension) := do
  return ⟨← readExtension, ← readExtension, ← readExtension, ← readExtension⟩

private def readVector : Reader (List Extension) := do readList (← readCount) readExtension

private def readDomain (bits : Nat) : Reader NativeAIR.Domain.Subgroup := do
  unless (← readNat) == bits do throw "domain logarithm order differs"
  let some domain := NativeAIR.Domain.ofLogSize bits | throw "unsupported domain logarithm"
  return domain

private def readDomains : Reader (Nat × Nat × Nat) := do
  let header := "Aiur trace domains v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "domain snapshot version differs"
  unless (← readNat) == 33 do throw "incomplete domain inventory"
  let mut rows := 0
  let mut accepted := 0
  let mut rejected := 0
  for bits in [:33] do
    let domain ← readDomain bits
    let n := NativeAIR.Domain.size domain
    unless (← readNat) == n do throw "native domain size differs"
    unless (← readField) == NativeAIR.Domain.generator domain do throw "native domain generator differs"
    unless (← readField) == NativeAIR.Domain.lastPoint domain do throw "native last point differs"
    unless (← readField) == NativeAIR.Domain.normalizer domain do throw "native normalizer differs"
    unless (← readField) == (NativeAIR.Domain.normalizer domain).inverse do throw "native inverse normalizer differs"
    let indices := (List.range (min n 16) ++ [n / 2, n - 1, n - 2] ++
      (List.range 16).map fun seed => seed * 0x0a3751c9 % n).mergeSort (· ≤ ·) |>.eraseDups
    unless (← readNat) == indices.length do throw "incomplete domain row samples"
    for index in indices do
      unless (← readNat) == index do throw "native row index differs"
      let fin : Fin n ← if bounded : index < n then pure ⟨index, bounded⟩ else throw "native row index out of bounds"
      let point := NativeAIR.Domain.point domain fin
      unless (← readField) == point do throw "native row point differs"
      unless (← readExtension) == Extension.ofBase (point * NativeAIR.Domain.generator domain) do
        throw "native next point differs"
      unless NativeAIR.Domain.selectors domain (Extension.ofBase point) == none do throw "trace row pole accepted"
      rows := rows + 1
    unless (← readNat) == 64 do throw "incomplete selector assignments"
    for _ in [:64] do
      let point ← readExtension
      unless (← readExtension) == NativeAIR.Domain.vanishing domain point do throw "native vanishing polynomial differs"
      let defined ← readBool
      let expected ← if defined then some <$> readSelectors else pure none
      unless NativeAIR.Domain.selectors domain point == expected do throw "native point selectors differ"
      if defined then accepted := accepted + 1 else rejected := rejected + 1
  unless (← readNat) == 9 do throw "incomplete bulk selector domains"
  for bits in [:9] do
    let domain ← readDomain bits
    let n := NativeAIR.Domain.size domain
    unless (← readNat) == n do throw "bulk selector count differs"
    for _ in [:n] do
      let point ← readField
      let expected ← readSelectors
      unless NativeAIR.Domain.selectors domain (Extension.ofBase point) == some expected do
        throw "native bulk selectors differ"
  for invalid in [33, 64, 255, 256, 2^64 - 1] do
    unless (NativeAIR.Domain.ofLogSize invalid).isNone do throw "invalid domain logarithm accepted"
  return (rows, accepted, rejected)

private def readQuotients : Reader (Nat × Nat) := do
  let header := "Aiur quotient arithmetic v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "quotient snapshot version differs"
  unless (← readNat) == 704 do throw "incomplete quotient inventory"
  let mut accepted := 0
  let mut rejected := 0
  for bits in [0, 1, 2, 4, 8, 16, 31, 32] do
    for count in [0, 1, 2, 3, 4, 7, 8, 9, 16, 31, 32] do
      for seed in [:8] do
        let domain ← readDomain bits
        unless (← readNat) == count && (← readNat) == seed do throw "quotient assignment order differs"
        let point ← readExtension
        let alpha ← readExtension
        let constraints ← readVector
        let row ← readVector
        unless constraints.length == count && row.length == 2 * count do throw "quotient case dimensions differ"
        unless (← readExtension) == Quotient.composition alpha constraints do throw "native constraint fold differs"
        let expected ← readExtension
        unless Quotient.evaluate domain point row == some expected do throw "native quotient recombination differs"
        let expectedAcceptance ← readBool
        unless Quotient.check domain point alpha constraints row == some expectedAcceptance do
          throw "native out-of-domain arithmetic check differs"
        unless Quotient.check domain point alpha constraints (row ++ [0]) == none do throw "odd quotient row accepted"
        unless Quotient.check domain 1 alpha constraints row == none do throw "first-row pole accepted"
        unless Quotient.check domain (Extension.ofBase (NativeAIR.Domain.lastPoint domain)) alpha constraints row == none do
          throw "last-row pole accepted"
        if expectedAcceptance then
          accepted := accepted + 1
          if let first :: rest := row then
            unless Quotient.check domain point alpha constraints ((first + 1) :: rest) == some false do
              throw "altered quotient coordinate accepted"
        else rejected := rejected + 1
  return (accepted, rejected)

private def runReader (reader : Reader α) (path : System.FilePath) : IO α := do
  let bytes ← IO.FS.readBinFile path
  match reader.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok (value, (_, cursor)) =>
    unless cursor == bytes.size do throw (IO.userError "domain snapshot has trailing bytes")
    return value

def run (domains quotients : System.FilePath) : IO Unit := do
  let (rows, accepted, rejected) ← runReader readDomains domains
  IO.println s!"domains: 33 generators, {rows} row samples, {accepted} defined/{rejected} rejected selectors and 511 bulk points match"
  let (accepted, rejected) ← runReader readQuotients quotients
  IO.println s!"quotients: {accepted} accepted/{rejected} rejected native arithmetic cases, malformed rows, poles and alterations match"

end AiurTests.Domain

def main (args : List String) : IO Unit := do
  match args with
  | [domains, quotients] => AiurTests.Domain.run domains quotients
  | _ => throw (IO.userError "expected native domain and quotient snapshots")
