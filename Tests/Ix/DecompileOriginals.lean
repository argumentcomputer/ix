module
public import Ix.DecompileDriver
public import LSpec
public section

namespace Tests.DecompileOriginals

open Ix.DecompileM Ixon

private def check (label : String) (ok : Bool) : Except String Unit :=
  unless ok do throw label

private def rejects (env : Ixon.Env) (name : Ix.Name) (message : String) : Bool :=
  let (_, errors, _) := decompileEnvFull env {}
  errors.any fun (n, e) => n == name && e.contains name.pretty && e.contains message

/-- Constructed artifacts isolate the reader from compiler capture/retention.
    The argument comes from IO so native hashes run only with this suite. -/
private def originalChecks (suffix : Nat) : Except String Unit := do
  let n := fun s => Ix.Name.mkStr (Ix.Name.mkStr Ix.Name.mkAnon s!"OR{suffix}") s
  let dep := n "dependency"
  let ns := #[n "plain", n "alias", Ix.Name.mkStr (n "I") "rec"]
  let ax : Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero]⟩
  let axOrig := { ax with univs := #[.succ .zero] }
  let depAddr := Address.blake3 (serConstant ax)
  let depOrigAddr := Address.blake3 (serConstant axOrig)
  let d : Definition := ⟨.defn, .safe, 0, .sort 0, .ref 0 #[]⟩
  let original : Constant := ⟨.defn d, #[], #[depAddr], #[.zero]⟩
  let canonical := { original with info := .defn { d with value := .sort 0 } }
  let oa := Address.blake3 (serConstant original)
  let ca := Address.blake3 (serConstant canonical)
  let mkMeta := fun (name : Ix.Name) => ({ info := .defn name.getHash #[] #[] #[] ⟨#[.leaf]⟩ 0 0 } : ConstantMeta)
  let depMeta : ConstantMeta := { info := .axio dep.getHash #[] ⟨#[.leaf]⟩ 0 }
  let mut base := ({} : Ixon.Env)
    |>.storeConst depAddr ax |>.storeConst depOrigAddr axOrig
    |>.storeConst ca canonical |>.storeConst oa original
  base := base.registerName dep {
    addr := depAddr, constMeta := depMeta,
    original := some (depOrigAddr, depMeta) }
  for name in ns do
    base := base.registerName name {
      addr := ca, constMeta := .empty,
      original := some (oa, mkMeta name), hints := some .abbrev }
  for name in ns.push dep do
    base := { base with names := RawEnv.addNameComponents base.names name }
  let verify := fun (env : Ixon.Env) (hints : Array Lean.ReducibilityHints) => do
    let (out, errors, _) := decompileEnvFull env {}
    check s!"original read: {errors}" (errors.isEmpty && out.size == 4)
    for i in [:ns.size] do
      let some (.defnInfo v) := out[ns[i]!]?
        | throw s!"missing definition {ns[i]!}"
      check "source value and per-name hints"
        (v.value == Ix.Expr.mkConst dep #[] && v.hints == hints[i]!)
    let some ci := out[dep]? | throw "dependency missing"
    check "original dependency metadata/address" (ci.getCnst.type == Ix.Expr.mkSort (Ix.Level.mkSucc Ix.Level.mkZero))
  let v4 ← serEnv base
  check "empty original tables retain v4" (v4.data[0]? == some 0xE4)
  verify (← deEnv v4) #[.abbrev, .abbrev, .abbrev]
  let env5 := { base with
    consts := (base.consts.erase oa).erase depOrigAddr,
    originals := ({} : Std.HashMap Address LazyConstant)
      |>.insert oa (LazyConstant.ofConstant original)
      |>.insert depOrigAddr (LazyConstant.ofConstant axOrig),
    originalHintOverrides := ({} : Std.HashMap Ix.Name (Option Lean.ReducibilityHints))
      |>.insert ns[0]! (some (.regular 17)) |>.insert ns[1]! none }
  let expected := #[Lean.ReducibilityHints.regular 17, .opaque, .abbrev]
  let v5 ← serEnv env5
  check "original data selects v5" (v5.data[0]? == some 0xE5)
  let lazy ← deEnvVerifiedLazy v5
  for env in [env5, ← deEnv v5, ← lazy.materializeAll] do
    verify env expected
    check "ordinary checker lookup excludes originals" ((env.getConst? oa).isNone)
    check "reference resolution remains canonical"
      ((originalView env).addrToName[depAddr]? == some dep &&
       (originalView env).addrToName[depOrigAddr]? == none)
  -- A cached value cannot replace validated raw bytes.
  verify { env5 with
    originals := env5.originals.insert oa
      { LazyConstant.ofConstant original with cache := some canonical } } expected
  check "missing original is a named error"
    (rejects { env5 with originals := env5.originals.erase oa } ns[0]! "missing constant/original")
  check "aux suffix does not omit a required original"
    (rejects { env5 with originals := env5.originals.erase oa } ns[2]! "missing constant/original")
  let legacyMissing := { env5 with originals := {}, originalHintOverrides := {} }
  check "legacy v4 missing originals requests recompilation"
    (rejects (← deEnv (← serEnv legacyMissing)) ns[0]! "recompile")
  check "original hash mismatch is named"
    (rejects { env5 with
      originals := env5.originals.insert oa (LazyConstant.ofConstant canonical) } ns[0]! "hash mismatch")
  check "canonical-store hash mismatch is named"
    (rejects { base with
      consts := base.consts.insert oa (LazyConstant.ofConstant canonical) } ns[0]! "hash mismatch")
  check "overlapping stores compare exact bytes"
    (rejects { env5 with
      consts := env5.consts.insert oa (LazyConstant.ofConstant canonical) } ns[0]! "conflicting original bytes")
  let block : Constant := ⟨.muts #[.defn { d with typ := .share 0 }],
    #[.sort 0], #[depAddr], #[.zero]⟩
  let ba := Address.blake3 (serConstant block)
  let proj := fun addr => (⟨.dPrj ⟨0, addr⟩, #[], #[], #[]⟩ : Constant)
  let pa := Address.blake3 (serConstant (proj ba))
  let mut projected := { env5 with
    originals := (env5.originals.erase oa)
      |>.insert ba (LazyConstant.ofConstant block) |>.insert pa (LazyConstant.ofConstant (proj ba)) }
  for name in ns do
    projected := { projected with
      named := projected.named.insert name { projected.named[name]! with original := some (pa, mkMeta name) } }
  verify (← deEnv (← serEnv projected)) expected
  verify { projected with
    consts := projected.consts.insert ba (LazyConstant.ofConstant block),
    originals := projected.originals.erase ba } expected
  verify { projected with
    consts := projected.consts.insert pa (LazyConstant.ofConstant (proj ba)),
    originals := projected.originals.erase pa } expected
  check "missing original block is named"
    (rejects { projected with originals := projected.originals.erase ba } ns[0]! "missing constant/original")
  check "tampered original block is named"
    (rejects { projected with
      originals := projected.originals.insert ba (LazyConstant.ofConstant canonical) } ns[0]! "hash mismatch")
  let wrong := proj depAddr
  let wa := Address.blake3 (serConstant wrong)
  let wrongEnv := { projected with
    originals := projected.originals.insert wa (LazyConstant.ofConstant wrong),
    named := projected.named.insert ns[0]!
      { projected.named[ns[0]!]! with original := some (wa, mkMeta ns[0]!) } }
  check "wrong projection block is named" (rejects wrongEnv ns[0]! "not a mutual block")

/-- Constructor metadata is selected from its own original entry, even when
    emitted as part of the inductive; flags use only decoded declarations. -/
private def constructorChecks (suffix : Nat) : Except String Unit := do
  let ind := Ix.Name.mkStr Ix.Name.mkAnon s!"OI{suffix}"
  let ctor := Ix.Name.mkStr ind "mk"
  let binder := Ix.Name.mkStr ind "sourceBinder"
  let indMeta : ConstantMeta := {
    info := .indc ind.getHash #[] #[ctor.getHash] #[ind.getHash] #[ind.getHash] ⟨#[.leaf]⟩ 0 }
  let ctorMeta : ConstantMeta := {
    info := .ctor ctor.getHash #[] ind.getHash ⟨#[.leaf, .binder binder.getHash .default 0 0]⟩ 1 }
  let c : Constructor := ⟨false, 0, 0, 0, 1, .leanAll (.ref 0 #[]) (.ref 0 #[])⟩
  let block : Constant := ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 0, #[c]⟩],
    #[], #[ind.getHash], #[.succ .zero]⟩
  let ba := Address.blake3 (serConstant block)
  let ip : Constant := ⟨.iPrj ⟨0, ba⟩, #[], #[], #[]⟩
  let cp : Constant := ⟨.cPrj ⟨0, 0, ba⟩, #[], #[], #[]⟩
  let ia := Address.blake3 (serConstant ip)
  let ca := Address.blake3 (serConstant cp)
  let mut env : Ixon.Env := { addrToName := ({} : Std.HashMap Address Ix.Name).insert ind.getHash ind }
  for name in #[ind, ctor, binder] do
    env := { env with names := RawEnv.addNameComponents env.names name }
  for (name, addr, md) in #[(ind, ia, indMeta), (ctor, ca, ctorMeta)] do
    env := { env with
      named := env.named.insert name
        { addr := ind.getHash, constMeta := .empty, original := some (addr, md) } }
  for (addr, cnst) in #[(ba, block), (ia, ip), (ca, cp)] do
    env := { env with originals := env.originals.insert addr (LazyConstant.ofConstant cnst) }
  let (out, errs, _) := decompileEnvFull env {}
  check s!"constructor original read: {errs}" (errs.isEmpty && out.size == 2)
  let some (.inductInfo iv) := out[ind]? | throw "inductive missing"
  check "Pass 1.5 recomputes flags" (iv.isRec && !iv.isReflexive && iv.numNested == 0)
  let view := originalView env
  let entries ← decompileOne { ixonEnv := view } view ind view.named[ind]!
  let expected := Ix.Expr.mkForallE binder (Ix.Expr.mkConst ind #[]) (Ix.Expr.mkConst ind #[]) .default
  check "parent inductive uses original constructor metadata"
    (entries.any fun (name, ci) => name == ctor && ci.getCnst.type == expected)
  check "constructor projection reads its own source metadata"
    ((out[ctor]?).any fun ci => ci.getCnst.type == expected)
  check "missing constructor original is named"
    (rejects { env with originals := env.originals.erase ca } ctor "missing constant/original")

def suite : LSpec.TestSeq :=
  .individualIO "original records: checked kernel-free decompile" none (do
    let seed ← IO.mkRef 0
    let seed ← seed.get
    let result := do originalChecks seed; constructorChecks seed
    match result with
    | .ok () => return (true, 0, 0, none)
    | .error err => return (false, 0, 0, some err)) .done

end Tests.DecompileOriginals
