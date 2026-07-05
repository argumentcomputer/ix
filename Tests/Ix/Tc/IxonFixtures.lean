module

public import LSpec
public import Ix.Tc

/-!
Hand-built `Ixon.Env` fixtures for `Ix.Tc` ingress tests (no FFI, no
compiler): constants stored at `blake3 (serConstant c)`, mutual blocks stored
together with all their projection constants (mirroring what the compiler
emits), plus ingress negative cases (index OOB, missing blob, missing
projection, integrity violation).

The accept tests assert exact kernel node addresses computed independently
via the `Ix.Tc` smart constructors — a pure-Lean end-to-end check of the
index-resolution + Blake3 pipeline.
-/

namespace Tests.Tc.Fixtures

open LSpec
open Ix.Tc

/-! ### Builders -/

/-- Store a constant at its content address (`blake3 (serConstant c)`). -/
def storeConst (env : Ixon.Env) (c : Ixon.Constant) : Ixon.Env × Address :=
  let addr := Address.blake3 (Ixon.serConstant c)
  (env.storeConst addr c, addr)

/-- Store a Muts block *and* all of its projection constants (member DPrj /
    IPrj / RPrj plus one CPrj per constructor), as the compiler does. -/
def storeMutsWithProjs (env : Ixon.Env) (block : Ixon.Constant) :
    Ixon.Env × Address := Id.run do
  let (env, blockAddr) := storeConst env block
  let mut env := env
  let .muts members := block.info | return (env, blockAddr)
  for h : i in [0:members.size] do
    let idx := i.toUInt64
    match members[i] with
    | .defn _ =>
      env := (storeConst env ⟨.dPrj ⟨idx, blockAddr⟩, #[], #[], #[]⟩).1
    | .recr _ =>
      env := (storeConst env ⟨.rPrj ⟨idx, blockAddr⟩, #[], #[], #[]⟩).1
    | .indc ind =>
      env := (storeConst env ⟨.iPrj ⟨idx, blockAddr⟩, #[], #[], #[]⟩).1
      for cidx in [0:ind.ctors.size] do
        env := (storeConst env
          ⟨.cPrj ⟨idx, cidx.toUInt64, blockAddr⟩, #[], #[], #[]⟩).1
  return (env, blockAddr)

/-- Run an ingress action on an empty kernel env. -/
def runIngress (x : IngressM α) : Except IngressErr (α × AnonEnv) :=
  match x.run {} with
  | .ok a env => .ok (a, env)
  | .error e _ => .error e

def sort1U : Ixon.Univ := .succ .zero

/-! ### Fixtures -/

/-- `A : Sort 1` (axiom). -/
def axiomA : Ixon.Constant :=
  ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[sort1U]⟩

/-- Environment with just `A`. -/
def envA : Ixon.Env × Address := storeConst {} axiomA

/-- `idA : A → A := fun a => a`, referencing `A` via refs[0]. -/
def defnIdA (aAddr : Address) : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 0,
    .all (.ref 0 #[]) (.ref 0 #[]),
    .lam (.ref 0 #[]) (.var 0)⟩,
   #[], #[aAddr], #[]⟩

/-- Environment: `A`, `idA`. -/
def envIdA : Ixon.Env × Address × Address :=
  let (env, aAddr) := envA
  let (env, idAddr) := storeConst env (defnIdA aAddr)
  (env, aAddr, idAddr)

/-- `lit42 : A := 42` (nat literal; blob stored). Value never typechecks —
    ingress only. -/
def envNatLit : Ixon.Env × Address × Address := Id.run do
  let (env, aAddr) := envA
  let (env, blobAddr) := env.storeBlob ⟨(42 : Nat).toBytesLE⟩
  let c : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .nat 1⟩, #[], #[aAddr, blobAddr], #[]⟩
  let (env, cAddr) := storeConst env c
  return (env, cAddr, blobAddr)

/-- `lit : A := "hi"` (string literal; blob stored). -/
def envStrLit : Ixon.Env × Address × Address := Id.run do
  let (env, aAddr) := envA
  let (env, blobAddr) := env.storeBlob "hi".toUTF8
  let c : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .str 1⟩, #[], #[aAddr, blobAddr], #[]⟩
  let (env, cAddr) := storeConst env c
  return (env, cAddr, blobAddr)

/-- `dup : A := (fun a => a) ((fun a => a) x)`-ish shape exercising `share`
    twice: value `app (share 0) (share 0)`, sharing `[lam (ref 0) (var 0)]`. -/
def envShare : Ixon.Env × Address := Id.run do
  let (env, aAddr) := envA
  let c : Ixon.Constant :=
    ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .app (.share 0) (.share 0)⟩,
     #[.lam (.ref 0 #[]) (.var 0)], #[aAddr], #[]⟩
  let (env, cAddr) := storeConst env c
  return (env, cAddr)

/-- Two mutually-referencing definitions via `recur`. -/
def envMutualDefs : Ixon.Env × Address := Id.run do
  let (env, aAddr) := envA
  let f : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .ref 0 #[], .recur 1 #[]⟩
  let g : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .ref 0 #[], .recur 0 #[]⟩
  let block : Ixon.Constant := ⟨.muts #[f, g], #[], #[aAddr], #[]⟩
  let (env, blockAddr) := storeMutsWithProjs env block
  return (env, blockAddr)

/-- A one-inductive block `B : Sort 1` with `mk : B` (ctor type is
    `recur 0`). -/
def envInductive : Ixon.Env × Address := Id.run do
  let ind : Ixon.Inductive :=
    ⟨false, 0, 0, 0, .sort 0, #[⟨false, 0, 0, 0, 0, .recur 0 #[]⟩]⟩
  let block : Ixon.Constant := ⟨.muts #[.indc ind], #[], #[], #[sort1U]⟩
  storeMutsWithProjs {} block

/-! ### Accept tests (exact node-address expectations) -/

def sort1K : KExpr .anon := .mkSort (.mkSucc .mkZero)

def acceptTests : TestSeq :=
  test "axiom ingresses with exact ty address"
    ((match runIngress (ingressAnonAddrShallow envA.1 envA.2) with
      | .ok (true, kenv) =>
        match kenv.get? ⟨envA.2, ()⟩ with
        | some (.axio _ _ false 0 ty) => ty.addr == sort1K.addr
        | _ => false
      | _ => false : Bool))
  ++ test "defn ingresses with exact ty/val addresses"
    ((let (env, aAddr, idAddr) := envIdA
      match runIngress (ingressAnonAddrShallow env idAddr) with
      | .ok (true, kenv) =>
        match kenv.get? ⟨idAddr, ()⟩ with
        | some (.defn (ty := ty) (val := val) (hints := hints) ..) =>
          let aRef : KExpr .anon := .mkConst ⟨aAddr, ()⟩ #[]
          ty.addr == (KExpr.mkAll () () aRef aRef).addr
            && val.addr == (KExpr.mkLam () () aRef (.mkVar 0 ())).addr
            && hints == .regular 0
        | _ => false
      | _ => false : Bool))
  ++ test "anonHints override reaches the defn"
    ((let (env, aAddr, idAddr) := envIdA
      let env := { env with
        anonHints := env.anonHints.insert idAddr (.regular 7) }
      match runIngress (ingressAnonAddrShallow env idAddr) with
      | .ok (_, kenv) =>
        match kenv.get? ⟨idAddr, ()⟩ with
        | some (.defn (hints := hints) ..) => hints == .regular 7
        | _ => false
      | _ => false : Bool))
  ++ test "nat literal decodes with blob address payload"
    ((let (env, cAddr, blobAddr) := envNatLit
      match runIngress (ingressAnonAddrShallow env cAddr) with
      | .ok (_, kenv) =>
        match kenv.get? ⟨cAddr, ()⟩ with
        | some (.defn (val := val) ..) =>
          val.addr == (KExpr.mkNat (m := .anon) 42 blobAddr).addr
            && blobAddr == KExpr.natBlob 42
        | _ => false
      | _ => false : Bool))
  ++ test "str literal decodes with blob address payload"
    ((let (env, cAddr, blobAddr) := envStrLit
      match runIngress (ingressAnonAddrShallow env cAddr) with
      | .ok (_, kenv) =>
        match kenv.get? ⟨cAddr, ()⟩ with
        | some (.defn (val := val) ..) =>
          val.addr == (KExpr.mkStr (m := .anon) "hi" blobAddr).addr
            && blobAddr == KExpr.strBlob "hi"
        | _ => false
      | _ => false : Bool))
  ++ test "share expands transparently (both occurrences)"
    ((let (env, cAddr) := envShare
      match runIngress (ingressAnonAddrShallow env cAddr) with
      | .ok (_, kenv) =>
        match kenv.get? ⟨cAddr, ()⟩ with
        | some (.defn (val := val) ..) =>
          let aRef : KExpr .anon :=
            .mkConst ⟨(storeConst {} axiomA).2, ()⟩ #[]
          let lam := KExpr.mkLam () () aRef (.mkVar 0 ())
          val.addr == (KExpr.mkApp lam lam).addr
        | _ => false
      | _ => false : Bool))
  ++ test "mutual defs resolve recur to sibling projections"
    ((let (env, blockAddr) := envMutualDefs
      let fAddr := defnProjAddr blockAddr 0
      let gAddr := defnProjAddr blockAddr 1
      match runIngress (ingressAnonAddrShallow env fAddr) with
      | .ok (_, kenv) =>
        (match kenv.get? ⟨fAddr, ()⟩ with
          | some (.defn (val := val) (block := b) ..) =>
            val.addr == (KExpr.mkConst (m := .anon) ⟨gAddr, ()⟩ #[]).addr
              && b.addr == blockAddr
          | _ => false)
        && (match kenv.get? ⟨gAddr, ()⟩ with
          | some (.defn (val := val) ..) =>
            val.addr == (KExpr.mkConst (m := .anon) ⟨fAddr, ()⟩ #[]).addr
          | _ => false)
        && (kenv.getBlock? ⟨blockAddr, ()⟩ |>.any (·.size == 2))
      | _ => false : Bool))
  ++ test "inductive block registers ind + ctor under projection addrs"
    ((let (env, blockAddr) := envInductive
      let bAddr := indcProjAddr blockAddr 0
      let mkAddr := ctorProjAddr blockAddr 0 0
      match runIngress (ingressAnonAddrShallow env bAddr) with
      | .ok (_, kenv) =>
        (match kenv.get? ⟨bAddr, ()⟩ with
          | some (.indc (ty := ty) (ctors := cs) ..) =>
            ty.addr == sort1K.addr
              && cs.size == 1 && cs[0]!.addr == mkAddr
          | _ => false)
        && (match kenv.get? ⟨mkAddr, ()⟩ with
          | some (.ctor (induct := ind) (ty := ty) ..) =>
            ind.addr == bAddr
              && ty.addr == (KExpr.mkConst (m := .anon) ⟨bAddr, ()⟩ #[]).addr
          | _ => false)
        -- flat block order: [ind, ctor]
        && (kenv.getBlock? ⟨blockAddr, ()⟩
            |>.any fun ms => ms.map (·.addr) == #[bAddr, mkAddr])
      | _ => false : Bool))
  ++ test "buildAnonWork enumerates fixtures correctly"
    ((let (env, blockAddr) := envInductive
      let (env, _) := storeConst env axiomA
      match buildAnonWork env with
      | .ok work =>
        work.size == 2  -- one standalone (A), one block; projections skipped
          && work.any (fun i => match i with
              | .standalone _ => true | _ => false)
          && work.any (fun i => match i with
              | .block b p ts =>
                b == blockAddr && p == indcProjAddr blockAddr 0
                  && ts == #[indcProjAddr blockAddr 0, ctorProjAddr blockAddr 0 0]
              | _ => false)
      | .error _ => false : Bool))
  ++ test "ingressAll covers everything and faulting dedups blocks"
    ((let (env, blockAddr) := envInductive
      match runIngress (do
        let work ← ingressAll env
        -- Re-faulting a projection of an already-ingressed block hits dedup.
        let again ← ingressAnonAddrShallow env (ctorProjAddr blockAddr 0 0)
        return (work.size, again)) with
      | .ok ((1, true), kenv) => kenv.size == 2
      | _ => false : Bool))

/-! ### Negative tests -/

def failsWith (r : Except IngressErr (Bool × AnonEnv)) (frag : String) : Bool :=
  match r with
  | .error e => (e.splitOn frag).length > 1
  | .ok _ => false

def rejectTests : TestSeq :=
  test "share index OOB"
    (let (env, aAddr) := envA
     let c : Ixon.Constant :=
       ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .share 5⟩, #[], #[aAddr], #[]⟩
     let (env, cAddr) := storeConst env c
     failsWith (runIngress (ingressAnonAddrShallow env cAddr))
       "invalid Share index 5")
  ++ test "ref index OOB"
    (let c : Ixon.Constant :=
       ⟨.axio ⟨false, 0, .ref 3 #[]⟩, #[], #[], #[]⟩
     let (env, cAddr) := storeConst {} c
     failsWith (runIngress (ingressAnonAddrShallow env cAddr))
       "invalid Ref index 3")
  ++ test "recur index OOB in standalone"
    (let (env, aAddr) := envA
     let c : Ixon.Constant :=
       ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .recur 1 #[]⟩, #[], #[aAddr], #[]⟩
     let (env, cAddr) := storeConst env c
     failsWith (runIngress (ingressAnonAddrShallow env cAddr))
       "invalid Rec index 1")
  ++ test "sort univ index OOB"
    (let c : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 2⟩, #[], #[], #[]⟩
     let (env, cAddr) := storeConst {} c
     failsWith (runIngress (ingressAnonAddrShallow env cAddr))
       "invalid universe index 2")
  ++ test "missing nat blob"
    (let (env, aAddr) := envA
     let c : Ixon.Constant :=
       ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .nat 0⟩, #[], #[aAddr], #[]⟩
     let (env, cAddr) := storeConst env c
     failsWith (runIngress (ingressAnonAddrShallow env cAddr))
       "missing Nat blob")
  ++ test "missing projection constant"
    -- Store the block WITHOUT its projection constants.
    (let (env, aAddr) := envA
     let f : Ixon.MutConst := .defn ⟨.defn, .safe, 0, .ref 0 #[], .recur 0 #[]⟩
     let block : Ixon.Constant := ⟨.muts #[f], #[], #[aAddr], #[]⟩
     let (env, blockAddr) := storeConst env block
     failsWith (runIngress (ingressAnonAddrShallow env blockAddr))
       "not present in env")
  ++ test "integrity violation (bytes stored under wrong address)"
    (let wrongAddr := Address.blake3 "wrong".toUTF8
     let base : Ixon.Env := {}
     let env := { base with
       consts := base.consts.insert wrongAddr (.ofConstant axiomA) }
     failsWith (runIngress (ingressAnonAddrShallow env wrongAddr))
       "fails integrity check")
  ++ test "guardReserved rejects marker addresses"
    ((match (guardReserved #[(⟨PrimAddrs.canonical.eagerReduce, ()⟩,
        .axio () () false 0 (.mkSort .mkZero))]).run {} with
      | .error e _ => (e.splitOn "reserved kernel marker").length > 1
      | .ok _ _ => false : Bool))
  ++ test "peekTag classifies fixture constants"
    ((let (env, blockAddr) := envInductive
      let tags := env.consts.toList.filterMap fun (_, lc) => lc.peekTag.toOption
      tags.length == 3  -- muts + iPrj + cPrj
        && (env.consts[blockAddr]?.bind (·.peekTag.toOption)) == some .muts
      : Bool))

public def suite : List TestSeq := [acceptTests, rejectTests]

end Tests.Tc.Fixtures
