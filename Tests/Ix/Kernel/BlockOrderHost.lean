import Tests.Ix.Kernel.BlockOrder
import Lean.Data.Json

/-! Canonical block order against Rust (`kernel-order`): for each case, the
classes `Ixon.BlockOrder.canonicalClasses` computes and the Rust kernel's
(`rs_kernel_canonical_classes`), one JSON row per case. -/

open Ix.Kernel Ixon.BlockOrder Tests.Ix.Kernel.BlockOrder
open Tests.Ix.Kernel.IxonFixtures (address)

namespace Tests.Ix.Kernel.BlockOrderHost

@[extern "rs_kernel_canonical_classes"]
opaque rustClasses : @& Address → @& Ixon.Constant → @& Array (Address × ByteArray) → String

structure Case where
  label : String
  source : Ixon.Constant
  blobs : Ingress.Blobs := []

def expressionCases : List Case :=
  let expressions : List Ixon.Expr := [
    .var 0, .var 1, .sort 0, .sort 1,
    .ref 0 #[], .ref 1 #[], .ref 0 #[1], .ref 0 #[0, 0],
    .app (.var 0) (.var 1), .app (.var 0) (.var 2),
    .lam .many (.sort 0) (.var 0), .lam .linear (.sort 0) (.var 0),
    .all .many .shared (.sort 0) (.var 0),
    .letE (.lean false) (.sort 0) (.var 0) (.var 1), .letE (.lean true) (.sort 0) (.var 0) (.var 1),
    .nat 0, .nat 1, .str 0, .str 1,
    .prj 0 0 (.var 0), .prj 0 1 (.var 0), .prj 1 0 (.var 0), .share 0,
    -- `let`s whose order against 13 or 14 depends on where the nondependency
    -- bit is compared: a smaller body with the other bit, a larger value, a
    -- larger type
    .letE (.lean true) (.sort 0) (.var 0) (.var 0), .letE (.lean false) (.sort 0) (.var 1) (.var 1),
    .letE (.lean false) (.sort 1) (.var 0) (.var 1)]
  let blobs : Ingress.Blobs := [(address 1, "z".toUTF8), (address 2, "ab".toUTF8)]
  expressions.zipIdx.flatMap fun (x, i) =>
    expressions.zipIdx.map fun (y, j) =>
      { label := s!"expression-{i}-{j}", blobs, source :=
        { record #[defn x, defn y] with refs := #[address 1, address 2], sharing := #[.var 1] } }

def recursor : Ixon.Recursor := ⟨false, false, 0, 0, 0, 0, 0, .sort 0, #[]⟩

def payloadCases : List Case :=
  let definition : Ixon.Definition := ⟨.defn, .safe, 0, .sort 0, .var 0⟩
  let members := [
    .defn definition, .defn { definition with kind := .opaq },
    .defn { definition with kind := .thm }, .defn { definition with safety := .unsaf },
    .defn { definition with lvls := 1 },
    indc 0, indc 1, .indc ⟨true, 0, 0, 0, .sort 0, #[]⟩,
    .indc ⟨false, 1, 0, 0, .sort 0, #[]⟩, .indc ⟨false, 0, 0, 1, .sort 0, #[]⟩,
    indc 0 #[ctor 0 0], indc 0 #[ctor 0 1], indc 0 #[ctor 0 0, ctor 1 0],
    .recr recursor, .recr { recursor with lvls := 1 },
    .recr { recursor with params := 1 }, .recr { recursor with indices := 1 },
    .recr { recursor with motives := 1 }, .recr { recursor with minors := 1 },
    .recr { recursor with k := true }, .recr { recursor with isUnsafe := true },
    .recr { recursor with rules := #[⟨0, .var 0⟩] },
    .recr { recursor with rules := #[⟨1, .var 0⟩] },
    .recr { recursor with rules := #[⟨0, .var 1⟩] }]
  members.zipIdx.flatMap fun (x, i) => members.zipIdx.map fun (y, j) =>
    { label := s!"payload-{i}-{j}", source := record #[x, y] }

/-- Since ix #637 the native oracle's ingress rejects cyclic *safe* definition
blocks before ordering them. Ordering is independent of a shared safety flag,
so the recursive cases use partial definitions, whose policy is unchanged. -/
def asPartial (source : Ixon.Constant) : Ixon.Constant :=
  match source.info with
  | .muts members => { source with info := .muts (members.map fun
      | .defn definition => .defn { definition with safety := .part }
      | member => member) }
  | _ => source

def cases : List Case := [
  ⟨"empty", record #[], []⟩, ⟨"singleton", record #[indc 0], []⟩,
  ⟨"sorted", simple, []⟩, ⟨"permuted", reversed, []⟩, ⟨"duplicate", duplicate, []⟩,
  ⟨"weak", asPartial weak, []⟩, ⟨"weak-permuted", asPartial weakPermuted, []⟩,
  ⟨"self-alpha", asPartial alphaSelf, []⟩, ⟨"cycle-alpha", asPartial alphaCycle, []⟩,
  ⟨"constructor-offsets", ctorBlock, []⟩,
  ⟨"unreduced-levels", { unreduced with info := .muts #[defn (.sort 0), defn (.sort 1)] }, []⟩,
  ⟨"ref-recur-alias", asPartial
    { localAliases with info := .muts #[defn (.ref 0 #[]), defn (.recur 1 #[])] }, []⟩,
  -- members that differ only in a `let`'s nondependency bit: two classes
  ⟨"nondep-let-have", letHave, []⟩, ⟨"nondep-have-let", haveLet, []⟩, ⟨"nondep-same-bit", letLet, []⟩,
  ⟨"nondep-left-right", leftRight, []⟩, ⟨"nondep-right-left", rightLeft, []⟩]
  ++ expressionCases ++ payloadCases

def run (test : Case) : IO Bool := do
  let actual := classes test.source test.blobs
  let expected := rustClasses owner test.source test.blobs.toArray
  let verdict := accepts test.source test.blobs
  let rendered := match actual with
    | .ok groups => "{\"classes\":" ++ (Lean.toJson groups).compress ++
      ",\"accepted\":" ++ (if verdict then "true" else "false") ++ "}"
    | .error reason => s!"error:{reprStr reason}"
  let passed := rendered == expected
  IO.println (Lean.Json.mkObj [
    ("case", Lean.toJson test.label), ("passed", Lean.toJson passed),
    ("lean", Lean.toJson rendered), ("rust", Lean.toJson expected),
    ("owner", Lean.toJson (toString owner)), ("ixonHex", Lean.toJson (hexOfBytes (Ixon.serConstant test.source))),
    ("blobs", Lean.toJson (test.blobs.map fun (key, bytes) =>
      Lean.Json.mkObj [("address", Lean.toJson (toString key)), ("hex", Lean.toJson (hexOfBytes bytes))]))]).compress
  unless passed do IO.eprintln s!"{test.label}: Lean {rendered}; Rust {expected}"
  return passed

def main : IO UInt32 := do
  let mut failed := 0
  for test in cases do
    unless ← run test do failed := failed + 1
  IO.eprintln s!"Canonical block order: {cases.length - failed}/{cases.length} Rust comparisons passed."
  return if failed == 0 then 0 else 1

end Tests.Ix.Kernel.BlockOrderHost

def main : IO UInt32 := Tests.Ix.Kernel.BlockOrderHost.main
