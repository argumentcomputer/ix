module

public import LSpec
public import Ix.Tc
public import Ix.CompileM
public import Ix.Meta
public import Ix.Common
public import Tests.Ix.Tc.AnonDiff
public import Tests.Ix.Tc.IxonFixtures

/-!
Meta-mode ingress tests (`tc-unit` entries + `tc-ingress-meta` ignored).

Pure fixtures (tc-unit):
- metadata lands in the kernel types (constant names, level params, binder
  names/infos, mdata layers, call-site head names);
- anon/meta ADDRESS PARITY: metadata is never hashed, so the meta ingress
  of a constant must produce byte-identical `ty`/`val` addresses to the
  anon ingress of the same env;
- negatives: `ref` (and `prj`) without an arena name are HARD errors;
  `lam` without one soft-falls-back to a synthetic `_s{n}` name.

FFI closures (`tc-ingress-meta`, ignored): Rust-compile seed closures,
parse with the pure full reader (`Ixon.deEnv`), meta-ingress every work
item, and check per-named-entry address parity against the anon ingress
of the same env. Whole-env meta scale is exercised by the R3 roundtrip.
-/

namespace Tests.Tc.IngressMeta

open LSpec
open Ix.Tc

public section

/-- Run a meta ingress action on an empty kernel env. -/
def runIngressMeta (x : IngressMetaM α) : Except IngressErr (α × MetaEnv) :=
  match x.run {} with
  | .ok a env => .ok (a, env)
  | .error e _ => .error e

/-- Register `name → (addr, cm)` and all of the name's components (plus any
    extra metadata-referenced names) in the env. -/
def withNamed (env : Ixon.Env) (name : Ix.Name) (addr : Address)
    (cm : Ixon.ConstantMeta) (extraNames : List Ix.Name := []) : Ixon.Env :=
  let names := extraNames.foldl (init := env.names)
    Ixon.RawEnv.addNameComponents
  let names := Ixon.RawEnv.addNameComponents names name
  { env with names } |>.registerName name { addr, constMeta := cm }

/-- Meta-ingress the full work list of `env` into a fresh kernel env. -/
def ingressAllMeta (env : Ixon.Env) : Except IngressErr MetaEnv := do
  let work := buildMetaWork env
  let ((), kenv) ← runIngressMeta do
    for item in work do
      ingressMetaWorkItem env item
  return kenv

/-! ### Fixtures -/

def nA : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "A"
def nU : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "u"
def nId : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "idA"
def nX : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "x"
def nKey : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "key"

open Tests.Tc.Fixtures in
/-- Axiom `A : Sort 1` with `.axio` metadata: name `A`, one level param
    `u`, leaf arena. -/
def envMetaAxiom : Ixon.Env × Address := Id.run do
  let (env, aAddr) := envA
  let cm : Ixon.ConstantMeta := .new
    (.axio nA.getHash #[nU.getHash] ⟨#[.leaf]⟩ 0)
  let env := withNamed env nA aAddr cm (extraNames := [nU])
  return (env, aAddr)

open Tests.Tc.Fixtures in
/-- Definition `idA : A → A := fun (x : A) => x` with full arena metadata:
    binder name `x` (implicit), and an mdata layer on the value root. -/
def envMetaDefn : Ixon.Env × Address × Address := Id.run do
  let (env, aAddr) := envA
  -- Value `fun (x : @A) => x`; type `@A → @A` (ref 0 = aAddr).
  let c : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0, .all (.ref 0 #[]) (.ref 0 #[]),
      .lam (.ref 0 #[]) (.var 0)⟩,
     #[], #[aAddr], #[]⟩
  let (env, dAddr) := storeConst env c
  -- Arena (bottom-up): [0] leaf (A ref of ty domain — refs are hard, so
  -- use .ref nodes), [1] ref A (ty domain), [2] ref A (ty codomain),
  -- [3] binder x (ty binder), [4] ref A (val domain), [5] leaf (var x),
  -- [6] binder x implicit (val lam), [7] mdata wrapper on the lam.
  let mdataKV : Ixon.KVMap := #[(nKey.getHash, .ofBool true)]
  let arena : Ixon.ExprMetaArena := ⟨#[
    .leaf,                                    -- 0 (spare)
    .ref nA.getHash,                          -- 1: ty domain ref
    .ref nA.getHash,                          -- 2: ty codomain ref
    .binder nX.getHash .default 1 2,          -- 3: ty forall binder
    .ref nA.getHash,                          -- 4: val domain ref
    .leaf,                                    -- 5: val body (var x)
    .binder nX.getHash .implicit 4 5,         -- 6: val lam binder
    .mdata #[mdataKV] 6                       -- 7: mdata over the lam
  ]⟩
  let cm : Ixon.ConstantMeta := .new
    (.defn nId.getHash #[] #[nId.getHash] #[] arena 3 7)
  let env := withNamed env nId dAddr cm (extraNames := [nX, nKey])
  let env := withNamed env nA aAddr
    (.new (.axio nA.getHash #[] ⟨#[.leaf]⟩ 0))
  return (env, dAddr, aAddr)

/-! ### Unit tests (pure, `tc-unit`) -/

def metaAxiomChecks : Bool × Bool × Bool := Id.run do
  let (env, aAddr) := envMetaAxiom
  match ingressAllMeta env with
  | .error _ => return (false, false, false)
  | .ok kenv =>
    match kenv.get? ⟨aAddr, nA⟩ with
    | some (.axio name levelParams _ _ _) =>
      -- Address parity with the anon ingress of the same env.
      let anonOk := Id.run do
        match Tests.Tc.Fixtures.runIngress
            (ingressAnonAddrShallow env aAddr) with
        | .ok (_, aenv) =>
          match aenv.get? ⟨aAddr, ()⟩, kenv.get? ⟨aAddr, nA⟩ with
          | some ac, some mc => return ac.ty.addr == mc.ty.addr
          | _, _ => return false
        | .error _ => return false
      return (name == nA, levelParams == #[nU], anonOk)
    | _ => return (false, false, false)

def metaDefnChecks : Bool × Bool × Bool × Bool := Id.run do
  let (env, dAddr, _) := envMetaDefn
  match ingressAllMeta env with
  | .error _ => return (false, false, false, false)
  | .ok kenv =>
    match kenv.get? ⟨dAddr, nId⟩ with
    | some (.defn name _ _ _ _ _ ty val leanAll _) =>
      -- Value is `lam x^{implicit} => x` with one mdata layer on the lam.
      let valOk := match val with
        | .lam n bi _ body info =>
          n == nX && bi == .implicit &&
          info.mdata.size == 1 &&
          (match body with
            | .var 0 vn _ => vn == nX
            | _ => false)
        | _ => false
      -- Type binder resolved from the arena.
      let tyOk := match ty with
        | .all n bi _ _ _ => n == nX && bi == .default
        | _ => false
      let allOk := leanAll.map (·.name) == #[nId]
      return (name == nId, valOk, tyOk, allOk)
    | _ => return (false, false, false, false)

/-- Anon/meta value+type address parity for the defn fixture. -/
def metaDefnAddrParity : Bool := Id.run do
  let (env, dAddr, _) := envMetaDefn
  match ingressAllMeta env,
        Tests.Tc.Fixtures.runIngress (ingressAnonAddrShallow env dAddr) with
  | .ok kenv, .ok (_, aenv) =>
    match kenv.get? ⟨dAddr, nId⟩, aenv.get? ⟨dAddr, ()⟩ with
    | some (.defn (ty := mty) (val := mval) ..),
      some (.defn (ty := aty) (val := aval) ..) =>
      return mty.addr == aty.addr && mval.addr == aval.addr
    | _, _ => return false
  | _, _ => return false

open Tests.Tc.Fixtures in
/-- `ref` without an arena `.ref` node is a hard error. -/
def metaRefMissingArenaCaught : Bool := Id.run do
  let (env, aAddr) := envA
  let c : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 0 #[]⟩, #[], #[aAddr], #[]⟩
  let (env, dAddr) := storeConst env c
  -- Empty arena: the Ref lookup lands on `.leaf`.
  let cm : Ixon.ConstantMeta := .new (.defn nId.getHash #[] #[] #[] ⟨#[]⟩ 0 0)
  let env := withNamed env nId dAddr cm
  match ingressAllMeta env with
  | .error e => return (e.splitOn "has no metadata name").length > 1
  | .ok _ => return false

open Tests.Tc.Fixtures in
/-- `lam` without an arena binder soft-falls-back to a synthetic name. -/
def metaLamSynthFallback : Bool := Id.run do
  let (env, aAddr) := envA
  let c : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .lam (.ref 0 #[]) (.var 0)⟩,
     #[], #[aAddr], #[]⟩
  let (env, dAddr) := storeConst env c
  -- Type root must still resolve: give the type a `.ref` node; leave the
  -- value's lam without a binder node (root 0 = the ty ref — wrong shape
  -- for a lam, exercising the soft fallback).
  let arena : Ixon.ExprMetaArena := ⟨#[.ref nA.getHash]⟩
  let cm : Ixon.ConstantMeta := .new (.defn nId.getHash #[] #[] #[] arena 0 0)
  let env := withNamed env nId dAddr cm
  match ingressAllMeta env with
  | .error _ => return false
  | .ok kenv =>
    match kenv.get? ⟨dAddr, nId⟩ with
    | some (.defn (val := .lam n _ _ _ _) ..) =>
      return n == Ix.Name.mkStr Ix.Name.mkAnon "_s0"
    | _ => return false

open Tests.Tc.Fixtures in
/-- A `callSite` arena node distributes canonical-arg metadata and names
    the head from the call-site's `name` field. -/
def metaCallSiteFixture : Bool := Id.run do
  let (env, aAddr) := envA
  -- f : A → A (reuse idA-shaped constant under a different name source),
  -- g : A := @f @A-axiom? Keep it minimal: value `(@f x…)` needs a bound
  -- var — use `fun (x : A) => f x` with a callSite over the `f x` spine.
  let f : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0, .all (.ref 0 #[]) (.ref 0 #[]),
      .lam (.ref 0 #[]) (.var 0)⟩, #[], #[aAddr], #[]⟩
  let (env, fAddr) := storeConst env f
  let nF := Ix.Name.mkStr Ix.Name.mkAnon "f"
  let g : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[],
      .lam (.ref 0 #[]) (.app (.ref 1 #[]) (.var 0))⟩,
     #[], #[aAddr, fAddr], #[]⟩
  let (env, gAddr) := storeConst env g
  let nG := Ix.Name.mkStr Ix.Name.mkAnon "g"
  -- Arena: [0] ref A (g ty), [1] ref A (lam domain), [2] leaf (var),
  -- [3] callSite f #[kept 0 2] canonMeta=[2], [4] binder x over (1, 3).
  let arena : Ixon.ExprMetaArena := ⟨#[
    .ref nA.getHash,
    .ref nA.getHash,
    .leaf,
    .callSite nF.getHash #[.kept 0 2] #[2] none,
    .binder nX.getHash .default 1 3
  ]⟩
  let cm : Ixon.ConstantMeta := .new (.defn nG.getHash #[] #[] #[] arena 0 4)
  let env := withNamed env nG gAddr cm (extraNames := [nX, nF])
  let env := withNamed env nF fAddr
    (.new (.defn nF.getHash #[] #[] #[]
      ⟨#[.ref nA.getHash, .ref nA.getHash, .binder nX.getHash .default 0 1,
         .ref nA.getHash, .leaf, .binder nX.getHash .default 3 4]⟩ 2 5))
  let env := withNamed env nA aAddr
    (.new (.axio nA.getHash #[] ⟨#[.leaf]⟩ 0))
  match ingressAllMeta env with
  | .error _ => return false
  | .ok kenv =>
    match kenv.get? ⟨gAddr, nG⟩ with
    | some (.defn (val := .lam _ _ _ (.app fk _ _) _) ..) =>
      match fk with
      | .const id _ _ => return id.name == nF && id.addr == fAddr
      | _ => return false
    | _ => return false

def unitTests : List TestSeq :=
  let (axName, axLvls, axParity) := metaAxiomChecks
  let (dName, dVal, dTy, dAll) := metaDefnChecks
  [ test "meta axiom: name resolved" axName
    ++ test "meta axiom: level params resolved" axLvls
    ++ test "meta axiom: anon/meta ty address parity" axParity
    ++ test "meta defn: name resolved" dName
    ++ test "meta defn: binder name/info + mdata on value" dVal
    ++ test "meta defn: type binder from arena" dTy
    ++ test "meta defn: leanAll resolved" dAll
    ++ test "meta defn: anon/meta ty+val address parity" metaDefnAddrParity
    ++ test "meta negative: ref without arena name is a hard error"
        metaRefMissingArenaCaught
    ++ test "meta soft fallback: lam without arena gets synth name"
        metaLamSynthFallback
    ++ test "meta callSite: head named from call-site" metaCallSiteFixture ]

/-! ### Rust-compiled closures (`tc-ingress-meta`, ignored) -/

/-- Compile a seed closure, parse with the PURE full reader, ingress in
    both modes, and check per-named-entry ty/val address parity. Returns
    `(namedChecked, firstErr?)`. -/
def closureParity (leanEnv : Lean.Environment) (label : String)
    (seeds : List Lean.Name) : IO (Nat × Option String) := do
  let consts := Tests.Tc.AnonDiff.closureOf leanEnv seeds
  if consts.isEmpty then
    return (0, some s!"empty closure for {seeds}")
  let dir ← IO.FS.createTempDir
  let path := dir / s!"tc-ingress-meta-{label}.ixe"
  let _ ← Ix.CompileM.rsCompileEnvBytesFFI consts path.toString
  let bytes ← IO.FS.readBinFile path
  IO.FS.removeDirAll dir
  match Ixon.deEnv bytes with
  | .error e => return (0, some s!"pure deEnv failed: {e}")
  | .ok ixonEnv =>
    -- Meta ingress of the whole env.
    let kenv ← match ingressAllMeta ixonEnv with
      | .error e => return (0, some s!"meta ingress failed: {e}")
      | .ok kenv => pure kenv
    -- Anon ingress of the whole env.
    let aenv ← match Tests.Tc.Fixtures.runIngress (do
        match buildAnonWork ixonEnv with
        | .error e => throw e
        | .ok work =>
          for item in work do
            match item with
            | .standalone addr =>
              let _ ← ingressAnonAddrShallow ixonEnv addr
            | .block blockAddr _ _ =>
              let _ ← ingressAnonAddrShallow ixonEnv blockAddr) with
      | .error e => return (0, some s!"anon ingress failed: {e}")
      | .ok (_, aenv) => pure aenv
    let mut checked := 0
    let mut firstErr : Option String := none
    for (name, named) in ixonEnv.named do
      match kenv.get? ⟨named.addr, name⟩ with
      | none =>
        -- Aux-original-bearing entries whose constants are absent are
        -- skipped by ingress; only flag when the anon side has it.
        if (aenv.get? ⟨named.addr, ()⟩).isSome && firstErr.isNone then
          firstErr := some s!"{name}: in anon env but not meta env"
      | some mc =>
        match aenv.get? ⟨named.addr, ()⟩ with
        | none =>
          if firstErr.isNone then
            firstErr := some s!"{name}: in meta env but not anon env"
        | some ac =>
          checked := checked + 1
          if mc.ty.addr != ac.ty.addr && firstErr.isNone then
            firstErr := some s!"{name}: ty address mismatch \
                                (meta {mc.ty.addr} vs anon {ac.ty.addr})"
    return (checked, firstErr)

def suite : List TestSeq :=
  (Tests.Tc.AnonDiff.seedSets ++
    [("inductives-recursors",
      [`Nat.rec, `List.rec, `Acc.rec, `Prod.rec, `PSigma.rec])]).map
    fun (label, seeds) =>
      .individualIO s!"anon/meta ingress parity: {label}" none (do
        let env ← get_env!
        let (checked, err?) ← closureParity env label seeds
        return (err?.isNone, checked, 0, err?)) .done

end

end Tests.Tc.IngressMeta
