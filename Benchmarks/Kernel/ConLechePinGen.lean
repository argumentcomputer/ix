/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.ConLecheStep

/-! # The pin table and the Ixon prelude, from the compiled Init (untrusted)

Generates `Ix/Kernel/ConLeche/PinData.lean` from a compiled `.ixe`
(`.lake/census/initstd.ixe`):

1. **The names.** Con-leche's pinned names, and only those: the basis
   (`reservedBasisNames`), the prelude's `And` and `Bool`, the structural and
   pin-certified Nat operations, the string-literal support, the standard and
   compiler-trust axioms (with `Iff`, `Nonempty`, `True`), `sorryAx`.
   Recursor names (`T.rec`, `T.rec_k`) are not pinned: the reader derives
   them. The constants the committed JSON Nat-operation pins mention are
   *not* pinned: Ixon content-addresses alpha-equivalent constants to one
   record (`HAdd`/`HMul`/`HDiv` and their instances are one block), so names
   those pins spell apart cannot all be given (the generator reports which
   collapse). Instead the pins are renamed into the reader's names
   (`renames`, step 3).
2. **Candidates.** Each name is looked up in the environment's `named`
   metadata (this host tool is the only place metadata is read), and its
   address resolved to a `ConstRef Address` exactly as the reader resolves
   references.
3. **Renaming and verification by con-leche.** Each name the committed
   Nat-operation pins mention is mapped to the reader's name of the constant
   it compiles to (`renames`). The prelude records are read under the
   candidate table, and the dependency closure of every pinned constant is
   read and checked record by record (`ConLecheStep.censusLoop`, the
   census's own step) with the renamed pins. The run fails unless every
   pinned constant's record is accepted (a basis block matches its pin up to
   `canon`, the literal-support constants have their exact types, the
   structural Nat operations are certified by their recurrences and the
   pin-certified ones by their pins and certificates), both literal
   capabilities hold in the final environment, and every recursor the
   prelude names gets its derived name.
4. **Output.** The table, sorted by name, the level names, the renaming,
   and the prelude's records (the twelve declarations of con-leche's
   prelude, with their projection and recursor records), as canonical
   bytes.

Usage: `conleche-pin-gen <input.ixe> <PinData.lean> [closure.jsonl]`. -/

namespace Benchmarks.Kernel.ConLechePinGen

open Ix.Kernel (ConstRef)
open Ix.Kernel.ConLecheReader
open Benchmarks.Kernel.ConLecheStep

def fixedNames : List CName :=
  ConLeche.reservedBasisNames ++
  [ConLeche.andName, ConLeche.andIntroName, ConLeche.boolName, ConLeche.boolFalseName,
   ConLeche.boolTrueName] ++
  ConLeche.natOpNames ++ ConLeche.natDivModNames ++
  [ConLeche.stringName, ConLeche.stringOfListName, ConLeche.listName, ConLeche.listNilName,
   ConLeche.listConsName, ConLeche.charName, ConLeche.charOfNatName] ++
  [ConLeche.propextName, ConLeche.choiceName, ConLeche.iffName, ConLeche.iffIntroName,
   ConLeche.nonemptyName, ConLeche.nonemptyIntroName] ++
  [ConLeche.trueName, ConLeche.trueIntroName, ConLeche.trustCompilerName,
   ConLeche.reduceNatName, ConLeche.reduceBoolName, ConLeche.ofReduceNatName,
   ConLeche.ofReduceBoolName, ConLeche.sorryAxName]

/-- The constants the committed Nat-operation pins mention. -/
def pinClosureNames : List CName := Id.run do
  let mut seen : Std.HashSet ConLeche.Expr := {}
  let mut acc : Array CName := #[]
  for ps in ConLeche.natOpPinSets do
    let exprs := [ps.divPin, ps.modPin, ps.gcdPin, ps.landPin, ps.lorPin, ps.xorPin,
      ps.shiftLeftPin, ps.shiftRightPin] ++ ps.divProofs ++ ps.modProofs ++ ps.gcdProofs ++
      ps.landProofs ++ ps.lorProofs ++ ps.xorProofs ++ ps.shiftLeftProofs ++ ps.shiftRightProofs
    for e in exprs do
      let (seen', acc') := ConLeche.Frontend.usedConstsGo seen acc e
      seen := seen'
      acc := acc'
  return acc.toList

/-- The prelude's declarations, in con-leche's prelude order
(`pins/<toolchain>.prelude.ndjson`): each group's names. -/
def preludeGroups : List (List CName) :=
  [[ConLeche.eqName, ConLeche.eqReflName, ConLeche.eqName.str "rec"],
   [ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName, ConLeche.natName.str "rec"],
   [ConLeche.punitName, ConLeche.punitUnitName, ConLeche.punitRecName],
   [ConLeche.emptyName, ConLeche.emptyName.str "rec"],
   [ConLeche.falseName, ConLeche.falseName.str "rec"],
   [ConLeche.quotName], [ConLeche.quotMkName], [ConLeche.quotLiftName], [ConLeche.quotIndName],
   [ConLeche.quotSoundName],
   [ConLeche.andName, ConLeche.andIntroName, ConLeche.andName.str "rec"],
   [ConLeche.boolName, ConLeche.boolFalseName, ConLeche.boolTrueName, ConLeche.boolName.str "rec"]]

def toLeanName : CName → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (toLeanName p) s
  | .num p n => .num (toLeanName p) n

def isRecursorName : CName → Bool
  | .str _ s => s == "rec" || s.startsWith "rec_"
  | _ => false

def components : CName → List (String ⊕ Nat)
  | .anonymous => []
  | .str p s => components p ++ [.inl s]
  | .num p n => components p ++ [.inr n]

def componentLit : String ⊕ Nat → String
  | .inl s => s!".inl {s.quote}"
  | .inr n => s!".inr {n}"

def ixToC : Ix.Name → CName
  | .anonymous _ => .anonymous
  | .str p s _ => .str (ixToC p) s
  | .num p n _ => .num (ixToC p) n

/-- The level-parameter names a constant's metadata records. -/
def metaLevels (env : Ixon.Env) (named : Ixon.Named) : Option (List CName) := do
  let addrs := match named.constMeta.info with
    | .defn _ lvls .. | .axio _ lvls .. | .quot _ lvls .. | .indc _ lvls .. | .ctor _ lvls ..
    | .recr _ lvls .. => lvls
    | _ => #[]
  addrs.toList.mapM fun a => ixToC <$> env.names[a]?

def refFields : ConstRef Address → String × Nat × Nat
  | .member b i => (toString b, i, 0)
  | .ctor b i c => (toString b, i, c + 1)

def sha256 (path : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #["--", path.toString] }
  return (out.stdout.splitOn " ").headD ""

def run (args : List String) : IO UInt32 := do
  let parsed : Option (String × String × Option String) := match args with
    | [i, o] => some (i, o, none)
    | [i, o, r] => some (i, o, some r)
    | _ => none
  let some (input, output, rowsOut) := parsed
    | IO.eprintln "usage: conleche-pin-gen <input.ixe> <PinData.lean> [closure.jsonl]"; return 2
  let started ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile input))
  let mut store : ConLecheStep.RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  IO.eprintln s!"pin-gen: {store.size} records loaded in {(← IO.monoMsNow) - started} ms"
  let lookup : Ix.Kernel.ConLecheReader.Store := (store[·]?)
  -- 1-2: names and candidates
  let wanted := (fixedNames ++ preludeGroups.flatten).eraseDups
  -- the JSON pins' own names: how many collapse onto one Ixon constant
  let mut closureRefs : Std.HashMap (ConstRef Address) (Array CName) := {}
  let mut closureMissing := 0
  for n in pinClosureNames.eraseDups do
    if isRecursorName n then continue
    let some named := env.named[Ix.Name.fromLeanName (toLeanName n)]?
      | closureMissing := closureMissing + 1; continue
    let some c := store[named.addr]? | continue
    let some ref := resolveSource (store[·]?) named.addr c | continue
    closureRefs := closureRefs.insert ref ((closureRefs.getD ref #[]).push n)
  let collapsed := closureRefs.toList.filter (·.2.size > 1)
  IO.eprintln s!"pin-gen: the JSON Nat-op pins name {pinClosureNames.eraseDups.length} constants; \
    {closureMissing} are absent from this corpus (other toolchains'), and {collapsed.length} Ixon \
    constants carry several of their names: {collapsed.map (·.2.toList)}"
  let mut pins : Array Pin := #[]
  let mut missing : Array CName := #[]
  let mut recNames : Array CName := #[]
  let mut addrOf : Std.HashMap CName Address := {}
  for n in wanted do
    let some named := env.named[Ix.Name.fromLeanName (toLeanName n)]?
      | missing := missing.push n; continue
    addrOf := addrOf.insert n named.addr
    if isRecursorName n then recNames := recNames.push n; continue
    let some c := store[named.addr]? | missing := missing.push n; continue
    let some ref := resolveSource lookup named.addr c | missing := missing.push n; continue
    pins := pins.push ⟨ref, n⟩
  -- the pin dumps of other toolchains mention constants this corpus does not
  -- have; only con-leche's own pinned names and the prelude must resolve
  let required := missing.filter fun n => fixedNames.contains n || preludeGroups.flatten.contains n
  unless missing.isEmpty do
    IO.eprintln s!"pin-gen: names without a resolvable record (other toolchains' pins): {missing.toList}"
  unless required.isEmpty do
    IO.eprintln s!"pin-gen: required names without a resolvable record: {required.toList}"
    return 1
  -- aliases: two names on one reference keep the first and are reported
  let mut byRef : Std.HashMap (ConstRef Address) CName := {}
  let mut kept : Array Pin := #[]
  for p in pins do
    if let some other := byRef[p.ref]? then
      IO.eprintln s!"pin-gen: alias: {p.name} and {other} are the same constant; keeping {other}"
    else
      byRef := byRef.insert p.ref p.name
      kept := kept.push p
  let pinnedNames ← IO.ofExcept (pinMap kept)
  -- level-parameter names: every pinned constant's, and the recursors' of
  -- every pinned inductive (`matchesPin` compares them by name)
  let mut levels : Std.HashMap (ConstRef Address) (List CName) := {}
  for p in kept do
    let some named := env.named[Ix.Name.fromLeanName (toLeanName p.name)]? | continue
    if let some ns := metaLevels env named then levels := levels.insert p.ref ns
    if (inductiveAt lookup p.ref).isSome then
      for r in (List.range 8).map (fun k => if k == 0 then p.name.str "rec" else p.name.str s!"rec_{k}") do
        let some rn := env.named[Ix.Name.fromLeanName (toLeanName r)]? | continue
        let some rc := store[rn.addr]? | continue
        let some rref := resolveSource lookup rn.addr rc | continue
        if let some ns := metaLevels env rn then levels := levels.insert rref ns
  let pinned : Pins := { names := pinnedNames, levels }
  IO.eprintln s!"pin-gen: {kept.size} pins, {levels.size} level lists, {recNames.size} derived recursor names"
  -- the prelude records, in prelude order
  let mut preludeAddrs : Array Address := #[]
  for group in preludeGroups do
    for n in group do
      let a := addrOf.getD n default
      let some c := store[a]? | IO.eprintln s!"pin-gen: no prelude record for {n}"; return 1
      for x in #[owner a c, a] do
        unless preludeAddrs.contains x do preludeAddrs := preludeAddrs.push x
  let preRecords : Array (Address × Ixon.Constant) := preludeAddrs.filterMap fun a =>
    (store[a]?).map (a, ·)
  -- canonical bytes round-trip through the decoder the prelude loader uses
  for (a, c) in preRecords do
    let bytes := Ixon.serConstant c
    match Ixon.Canonical.deConstant preludeMaxBytes preludeMaxUnivNodes bytes with
    | .ok c' => unless c' == c do IO.eprintln s!"pin-gen: prelude record {a} does not round-trip"; return 1
    | .error e => IO.eprintln s!"pin-gen: prelude record {a}: {e}"; return 1
  let pre ← match readPrelude pinned preRecords with
    | .ok p => pure p
    | .error e => IO.eprintln s!"pin-gen: prelude: {e}"; return 1
  IO.eprintln s!"pin-gen: prelude: {preRecords.size} records, {pre.ix.decls.size} declarations: \
    {pre.ix.decls.toList.map ConLeche.Frontend.preludeKey}"
  -- 3: verification by con-leche over the pinned constants' closure
  let s := setup store (env.blobs[·]?) pinned pre (Hints.ofStore store env.anonHints).lookup
  for n in recNames do
    let a := addrOf.getD n default
    let some c := store[a]? | continue
    let some ref := resolveSource lookup a c | continue
    unless s.cx.nameOf ref == n do
      IO.eprintln s!"pin-gen: recursor {n} is named {s.cx.nameOf ref} by the reader"
      return 1
  -- the JSON pins' names in the reader's key space
  let mut renames : Array (CName × CName) := #[]
  for n in pinClosureNames.eraseDups do
    let some named := env.named[Ix.Name.fromLeanName (toLeanName n)]? | continue
    let some c := store[named.addr]? | continue
    let some ref := resolveSource lookup named.addr c | continue
    let m := s.cx.nameOf ref
    if m != n then renames := renames.push (n, m)
  let renameMap : Std.HashMap CName CName := renames.foldl (fun m (a, b) => m.insert a b) {}
  let natPins := renamePins renameMap
  IO.eprintln s!"pin-gen: {renames.size} of the pins' names renamed into the reader's names"
  let roots := (preRecords.map (·.1)) ++ (kept.map (·.ref.block))
  let ordered := closure s.store s.extra roots
  IO.eprintln s!"pin-gen: checking the closure, {ordered.size} records"
  let rows ← IO.mkRef (#[] : Array Row)
  let names := reportNames env s.store
  let out ← censusLoop s natPins (names.getD · #[]) ordered {}
    (emit := fun row => rows.modify (·.push row))
  let rows ← rows.get
  if let some path := rowsOut then
    IO.FS.writeFile path (String.intercalate "\n" (rows.toList.map (·.json.compress)) ++ "\n")
  IO.eprintln s!"pin-gen: closure checked in {(← IO.monoMsNow) - started} ms: {out.counts.toList}"
  let outcomeOf : Std.HashMap Address (String × String) :=
    rows.foldl (fun m r => m.insert r.address (r.outcome, r.reason)) {}
  -- every pinned constant's record must be accepted, and both literal
  -- capabilities must hold in the final environment
  let mut bad := 0
  for p in kept do
    let verdict := outcomeOf[p.ref.block]?
    match verdict with
    | some ("accept", _) => pure ()
    | _ =>
      let (o, reason) := verdict.getD ("unchecked", "")
      IO.eprintln s!"pin-gen: pinned {p.name}: {o}: {reason}"
      bad := bad + 1
  let fe := out.checker.fe
  let nat := ConLeche.natLitSupportedF fe
  let str := ConLeche.strLitSupportedF fe
  IO.eprintln s!"pin-gen: Nat literals {nat}, String literals {str}"
  unless bad == 0 && nat && str do return 1
  -- 4: output
  let sorted := kept.qsort (fun a b => toString a.name < toString b.name)
  let pinLines := sorted.toList.map fun p =>
    let (b, i, c) := refFields p.ref
    s!"  ([{", ".intercalate ((components p.name).map componentLit)}], {b.quote}, {i}, {c})"
  let levelLines := (levels.toArray.qsort (fun a b => toString (refFields a.1) < toString (refFields b.1))).toList.map
    fun (r, ns) =>
      let (b, i, c) := refFields r
      s!"  ({b.quote}, {i}, {c}, [{", ".intercalate (ns.map fun n => s!"[{", ".intercalate ((components n).map componentLit)}]")}])"
  let renameLines := (renames.qsort (fun a b => toString a.1 < toString b.1)).toList.map fun (a, b) =>
    s!"  ([{", ".intercalate ((components a).map componentLit)}],\n   [{", ".intercalate ((components b).map componentLit)}])"
  let preLines := preRecords.toList.map fun (a, c) =>
    s!"  ({(toString a).quote},\n   {(hexOfBytes (Ixon.serConstant c)).quote})"
  let digest ← sha256 input
  let text := s!"/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

/-! # Pinned names and prelude records (generated)

GENERATED by `lake exe conleche-pin-gen {System.FilePath.fileName input |>.getD input} <this file>`
(`Benchmarks/Kernel/ConLechePinGen.lean`); do not edit. Every pinned
constant's record, and the literal capabilities, were checked by con-leche's
verified fold through the Ixon reader when this file was generated; see
`Ix/Kernel/ConLeche/Reader.lean` for what the table may affect (coverage,
never soundness). Source: sha256 {digest}.

`pins`: (name components, block address, member, constructor + 1 or 0).
`levels`: (block address, member, constructor + 1 or 0, level-parameter
names), for the pinned constants and their recursors.
`renames`: (a Lean name the committed Nat-operation pins mention, the
reader's name of the constant it compiles to), where they differ.
`prelude`: (record address, canonical record bytes), in con-leche's prelude
order. -/

namespace Ix.Kernel.ConLecheReader.PinData

def source : String := {s!"sha256:{digest}".quote}

def pins : Array (List (String ⊕ Nat) × String × Nat × Nat) := #[
{",\n".intercalate pinLines}]

def levels : Array (String × Nat × Nat × List (List (String ⊕ Nat))) := #[
{",\n".intercalate levelLines}]

def renames : Array (List (String ⊕ Nat) × List (String ⊕ Nat)) := #[
{",\n".intercalate renameLines}]

def prelude : Array (String × String) := #[
{",\n".intercalate preLines}]

end Ix.Kernel.ConLecheReader.PinData
"
  IO.FS.writeFile output text
  IO.eprintln s!"pin-gen: wrote {output}: {sorted.size} pins, {preRecords.size} prelude records"
  return 0

end Benchmarks.Kernel.ConLechePinGen

def main (args : List String) : IO UInt32 := Benchmarks.Kernel.ConLechePinGen.run args
