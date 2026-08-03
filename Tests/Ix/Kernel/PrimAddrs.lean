/-
  Guards the kernel's hardcoded primitive addresses against the
  canonical table.

  The Aiur kernel hardcodes ~77 primitive constant addresses as 32-byte
  literals (`fn nat_add_addr() -> Addr { store([0xd6u8, ...]) }`) so
  reduction can recognize `Nat.add` etc. by address alone. Those bytes
  are the kernel's entire notion of "this Const IS the primitive whose
  semantics I am about to substitute", so a single wrong byte is a
  soundness-relevant defect: the kernel either fails to recognize a
  primitive (incompleteness) or — worse — recognizes the WRONG constant
  and applies native semantics to it.

  Such a defect is invisible to the FFT-pinned suite and to the arena
  fixtures: a corrupted literal simply never matches, so well-typed
  targets still check and ill-typed ones still fail. One shipped for
  months (`bool_false_addr`, last 8 bytes wrong) and only surfaced when
  a new reduction path finally tried to emit `Bool.false`.

  This test closes that class. It reads the byte arrays out of the
  ELABORATED toplevel — not the source text — and compares each against
  the address computed at test runtime from `Ix.Tc.PrimAddrs`, which is
  the same table the host-side closure walker and ingress verifier use.
  Any drift between the two sources of truth fails here.

  Coverage is by construction: every `fn <name>() -> Addr` in the
  toplevel whose body is a 32-byte literal must resolve to a canonical
  address, and the test reports the count so a silent drop to zero
  (e.g. an AST shape change) cannot pass unnoticed.
-/
import Ix.Meta
import Ix.Aiur.Compiler
import Ix.IxVM
import Ix.IxVM.Toplevel
import Ix.Tc.Primitive
import LSpec

open LSpec

namespace Tests.Ix.Kernel.PrimAddrs

/-- Read a 32-byte address literal out of an elaborated function body.
    Recognizes exactly the shape the addr helpers use:
    `store([b0u8, …, b31u8])`. Anything else → `none` (the function is
    not an address constant). -/
private def addrLiteralOf (body : Aiur.Source.Term) : Option Address :=
  match body with
  | .store (.array elts) | .array elts =>
    if elts.size != 32 then none else Id.run do
      let mut bytes : Array UInt8 := Array.mkEmpty 32
      for e in elts do
        match e with
        | .u8Lit n => bytes := bytes.push (UInt8.ofNat n)
        | _ => return none
      return some ⟨⟨bytes⟩⟩
  | _ => none

/-- Every `fn <name>() -> Addr`-shaped constant in the toplevel, paired
    with the address its literal encodes. -/
private def collectAddrFns (t : Aiur.Source.Toplevel) :
    Array (String × Address) := Id.run do
  let mut out : Array (String × Address) := #[]
  for f in t.functions do
    if !f.inputs.isEmpty then continue
    if let some a := addrLiteralOf f.body then
      out := out.push (f.name.toName.toString, a)
  return out

/-- The canonical address set, computed at test runtime from the Lean
    parity table + reserved markers — the same source the host closure
    walker (`Ix.Tc.primAddrSet`) consults. -/
private def canonical : Std.HashMap Address String := Id.run do
  let mut m : Std.HashMap Address String := {}
  for (name, a) in Ix.Tc.PrimAddrs.leanParityTable do
    m := m.insert a name
  for (name, a) in Ix.Tc.PrimAddrs.reservedMarkerAddrs do
    m := m.insert a name
  return m

/-- Fold a name to a comparison key: drop namespace separators and
    underscores, lowercase. `nat_add_addr` and `Nat.add` both become
    `natadd`. -/
private def normKey (s : String) : String :=
  ((s.replace "_" "").replace "." "").toLower

private def dropSuffix (s suf : String) : String :=
  if s.endsWith suf then (s.dropEnd suf.length).toString else s

/-- The addr function's key: last namespace component, with the
    dispatch-site suffix (`_dec`/`_io`/`_iota` — several primitives have
    one addr function per call site), the `_addr` marker, and a trailing
    `_type`/`_ty` removed, then normalized. `str` is spelled out, since
    the kernel abbreviates `String`. -/
private def fnKey (fnName : String) : String :=
  let base := (fnName.splitOn ".").getLast!
  let base := ["_dec", "_io", "_iota"].foldl dropSuffix base
  let base := dropSuffix base "_addr"
  let base := ["_type", "_ty"].foldl dropSuffix base
  let k := normKey base
  if k == "str" || (k.startsWith "str" && !k.startsWith "string")
  then "string" ++ k.drop 3 else k

/-- Addr functions whose name does not follow `snake_case` of the Lean
    constant even after the normalizations above. Maps the function's key
    to the constant it must resolve to; anything absent is required to
    match by normalized name. -/
private def nameExceptions : Std.HashMap String String := .ofList [
  ("quotctor", "Quot.mk"),
  ("quotlift", "Quot.lift"),
  ("quotind", "Quot.ind")
]

def suite : List TestSeq := Id.run do
  let some toplevel := (IxVM.ixVMFull).toOption
    | [test "IxVM toplevel builds" false]
  let fns := collectAddrFns toplevel
  let mut tests : TestSeq :=
    -- Guard against the extractor silently matching nothing (e.g. an
    -- AST shape change): the kernel is known to carry dozens of these.
    test s!"found {fns.size} address literals (expect ≥ 60)" (fns.size ≥ 60)
  for (fnName, addr) in fns do
    match canonical[addr]? with
    | some canonName =>
      -- Assert the function resolves to the constant its NAME claims.
      -- Membership alone is not enough: this map is keyed by address, so
      -- a table where `nat_add_addr` held `Nat.mul`'s bytes would still
      -- find a canonical entry and pass. That permutation is precisely
      -- the defect this suite exists to catch — the kernel would apply
      -- one primitive's native semantics under another's name.
      -- The addr function may spell the constant fully (`nat_add_addr` ↔
      -- `Nat.add`) or only its final component (`reduce_bool_addr` ↔
      -- `Lean.reduceBool`); both are accepted, anything else must be
      -- declared in `nameExceptions`.
      let k := fnKey fnName
      let ok : Bool := match nameExceptions[k]? with
        | some want => canonName == want
        | none => k == normKey canonName || k == fnKey canonName
      tests := tests ++ test s!"{fnName} = {canonName}" ok
    | none =>
      -- A named address constant that matches no canonical address is
      -- the defect this test exists for: the kernel will never
      -- recognize the primitive it thinks it encodes. Report the bytes.
      -- (Sentinel fillers must be written inline, not as named addr
      -- functions — see the zero-Addr tuple returns in Whnf/DefEq.)
      tests := tests ++
        test s!"{fnName}: {addr} not in canonical primitive table" false
  return [tests]

end Tests.Ix.Kernel.PrimAddrs
