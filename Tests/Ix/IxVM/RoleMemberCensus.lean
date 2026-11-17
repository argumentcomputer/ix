import Ix.Ixon
import Ix.Address.Admission
import IxC.Kernel.Admission

/-! # Roles bound at the constants of mutual and nested inductive blocks

`ixvm-role-member-census` (manual, `IX_ROLE_IXE`): for every role the default role table binds
(`Ix.Kernel.Admission.defaultBinding`, admitted by `admitBinding` under `Address.admissionHash`),
the record a compiled environment holds at the bound address, its kind and, for a projection
record or a block record, its block with the block's member and inductive counts and the route
the circuit gives the block (`KernelModeled::block_is_modeled`). For a recursor, the block of its
first motive's carrier (`KernelModeled::rec_family_block`) and that block's route. For a
projection record, whether the bound address is the block's constant address the projection
names (the member's or the constructor's projection address, recomputed).

The route is computed as the circuit computes it, on the record's own expressions with sharing
followed (the converted term inlines every sharing entry): a reference is the address in the
record's reference table, a member reference (`recur`) the projection address of that member
(`Ingress::build_recur_addrs`). `block_is_modeled` answers 0 at a record that is no block or a
block without an inductive, 1 at two or more inductives, and `ctors_nested` at one: it peels
exactly the constructor's parameter count of leading binders (`KernelCheck::peel_n_foralls`; a
run fails where fewer exist), tests the rest for a mention of a member (`KernelWhnf::se_mentions`)
and only then scans it (`nested_scan`): at an application whose head is a constant outside the
block and some argument of which mentions a member, the head's record decides
(`addr_is_inductive`: `Ingress::get_ci` reads an inductive there). A head that is no constant is
scanned itself; the arguments are scanned after the head.

Over every inductive block of the environment it also tests whether a bound address is one of
the block's constant addresses, and counts the blocks by route.
-/

namespace Tests.Ix.IxVM.RoleMemberCensus

abbrev IE := Ixon.Expr
abbrev Store := Address → Option Ixon.Constant

/-! ## Projection addresses -/

def projRecord (info : Ixon.ConstantInfo) : Ixon.Constant := ⟨info, #[], #[], #[], #[]⟩

def memberInfo (B : Address) (i : Nat) : Ixon.MutConst → Ixon.ConstantInfo
  | .defn _ => .dPrj ⟨i.toUInt64, B⟩
  | .indc _ => .iPrj ⟨i.toUInt64, B⟩
  | .recr _ => .rPrj ⟨i.toUInt64, B⟩

def ctorInfo (B : Address) (i j : Nat) : Ixon.ConstantInfo := .cPrj ⟨i.toUInt64, j.toUInt64, B⟩

def projAddr (hash : ByteArray → Address) (info : Ixon.ConstantInfo) : Address :=
  hash (Ixon.serConstant (projRecord info))

/-- `Ingress::build_recur_addrs`: every member's projection address, in position order. -/
def recurAddrs (hash : ByteArray → Address) (B : Address) (ms : Array Ixon.MutConst) :
    Array Address := Id.run do
  let mut out : Array Address := #[]
  let mut i := 0
  for m in ms do
    out := out.push (projAddr hash (memberInfo B i m))
    i := i + 1
  return out

/-! ## The converted term, read off the record -/

/-- A sharing reference followed to a node that is none. -/
def unshare (c : Ixon.Constant) (e : IE) : IE := go (c.sharing.size + 1) e
where
  go : Nat → IE → IE
    | 0, e => e
    | n + 1, .share i =>
      match c.sharing[i.toNat]? with
      | some e' => go n e'
      | none => .share i
    | _, e => e

/-- `KernelCheck::peel_n_foralls`: exactly `n` leading binders; `none` where the circuit has no
run. -/
def peel (c : Ixon.Constant) : Nat → IE → Option IE
  | 0, e => some e
  | n + 1, e =>
    match unshare c e with
    | .all _ b => peel c n b
    | _ => none

/-- `KernelTypes::collect_spine`, sharing followed along the function position. -/
partial def spine (c : Ixon.Constant) (e : IE) (args : List IE := []) : IE × List IE :=
  match unshare c e with
  | .app f a => spine c f (a :: args)
  | h => (h, args)

structure Ctx where
  c : Ixon.Constant
  mems : Array Address

structure Memo where
  ment : Std.HashMap Nat Bool := {}
  scan : Std.HashMap Nat Bool := {}

abbrev M := StateT Memo (Except String)

instance {α : Type} : Inhabited (M α) := ⟨throw "unreachable"⟩

instance {α : Type} : Inhabited (Except String α) := ⟨.error "unreachable"⟩

def refAddr (x : Ctx) (i : UInt64) : Except String Address :=
  match x.c.refs[i.toNat]? with
  | some a => .ok a
  | none => .error s!"reference {i} outside the table"

def recurAddr (x : Ctx) (j : UInt64) : Except String Address :=
  match x.mems[j.toNat]? with
  | some a => .ok a
  | none => .error s!"member reference {j} outside the block"

/-- `KernelWhnf::se_mentions`: some constant of the term is a member's address. -/
partial def mentions (x : Ctx) (e : IE) : M Bool := do
  match e with
  | .share i =>
    match (← get).ment[i.toNat]? with
    | some b => return b
    | none =>
      let some e' := x.c.sharing[i.toNat]? | throw s!"sharing entry {i} missing"
      let b ← mentions x e'
      modify fun m => { m with ment := m.ment.insert i.toNat b }
      return b
  | .ref i _ => return x.mems.contains (← refAddr x i)
  | .recur j _ => return x.mems.contains (← recurAddr x j)
  | .app f a => if (← mentions x f) then return true else mentions x a
  | .lam t b => if (← mentions x t) then return true else mentions x b
  | .all t b => if (← mentions x t) then return true else mentions x b
  | .letE _ _ t v b =>
    if (← mentions x t) then return true
    if (← mentions x v) then return true
    mentions x b
  | .prj _ _ y => mentions x y
  | _ => return false

/-- `KernelModeled::addr_is_inductive`: whether `Ingress::get_ci` reads an inductive at `a`
(an inductive projection record at an inductive member); an error where `get_ci` has no run. -/
def addrIsInductive (store : Store) (a : Address) : Except String Bool := do
  let some c := store a | throw s!"no record at {a}"
  match c.info with
  | .iPrj p =>
    let some cb := store p.block | throw s!"no block record at {p.block}"
    match cb.info with
    | .muts ms =>
      match ms[p.idx.toNat]? with
      | some (.indc _) => return true
      | _ => throw s!"inductive projection {a} at a member that is no inductive"
    | _ => throw s!"inductive projection {a} at a record that is no block"
  | .muts _ => throw s!"a constant reference names the block record {a}"
  | _ => return false

/-- `KernelModeled::nested_scan`. -/
partial def nscan (store : Store) (x : Ctx) (e : IE) : M Bool := do
  match e with
  | .share i =>
    match (← get).scan[i.toNat]? with
    | some b => return b
    | none =>
      let some e' := x.c.sharing[i.toNat]? | throw s!"sharing entry {i} missing"
      let b ← nscan store x e'
      modify fun m => { m with scan := m.scan.insert i.toNat b }
      return b
  | .app .. =>
    let (head, args) := spine x.c e
    let headAddr? : Option (Except String Address) :=
      match head with
      | .ref i _ => some (refAddr x i)
      | .recur j _ => some (recurAddr x j)
      | _ => none
    let here ← match headAddr? with
      | some ha => do
        let h ← ha
        if x.mems.contains h then
          pure false
        else
          -- the arguments first: `addr_is_inductive` loads the head
          let m ← args.anyM (mentions x)
          if m then
            let ind ← addrIsInductive store h
            pure ind
          else
            pure false
      | none => nscan store x head
    if here then return true
    for a in args do
      if (← nscan store x a) then return true
    return false
  | .lam t b => if (← nscan store x t) then return true else nscan store x b
  | .all t b => if (← nscan store x t) then return true else nscan store x b
  | .letE _ _ t v b =>
    if (← nscan store x t) then return true
    if (← nscan store x v) then return true
    nscan store x b
  | .prj _ _ y => nscan store x y
  | _ => return false

/-- `KernelModeled::ctors_nested` at the block's one inductive: the first constructor whose type,
after its parameters, holds a nested occurrence. -/
def ctorsNested (store : Store) (cb : Ixon.Constant) (ind : Ixon.Inductive)
    (mems : Array Address) : Except String (Option Nat) := do
  let x : Ctx := ⟨cb, mems⟩
  let mut memo : Memo := {}
  let mut j := 0
  for ct in ind.ctors do
    let some body := peel cb ct.params.toNat ct.typ
      | throw s!"constructor {j}: fewer than {ct.params} leading binders"
    let step : M Bool := do
      if (← mentions x body) then nscan store x body else pure false
    let (found, memo') ← step.run memo
    memo := memo'
    if found then return some j
    j := j + 1
  return none

/-! ## The route -/

structure Route where
  members : Nat
  inductives : Nat
  modeled : Bool
  why : String

def isIndc : Ixon.MutConst → Bool
  | .indc _ => true
  | _ => false

/-- `KernelModeled::block_is_modeled` at the record `cb` stored at `B`. -/
def routeOf (store : Store) (hash : ByteArray → Address) (B : Address) (cb : Ixon.Constant) :
    Except String Route := do
  match cb.info with
  | .muts ms =>
    let n := (ms.filter isIndc).size
    if n == 0 then return ⟨ms.size, 0, false, "no-inductive"⟩
    if n ≥ 2 then return ⟨ms.size, n, true, "two-or-more-inductives"⟩
    let some ind := ms.findSome? (fun m => match m with | .indc i => some i | _ => none)
      | throw "no inductive member"
    match ← ctorsNested store cb ind (recurAddrs hash B ms) with
    | some j => return ⟨ms.size, 1, true, s!"nested-occurrence-in-constructor-{j}"⟩
    | none => return ⟨ms.size, 1, false, "one-inductive-no-nested-occurrence"⟩
  | _ => return ⟨0, 0, false, "not-a-block-record"⟩

def blockIsModeled (store : Store) (hash : ByteArray → Address) (B : Address) :
    Except String Route := do
  let some cb := store B | throw s!"no record at {B}"
  routeOf store hash B cb

partial def lastBinderDom (c : Ixon.Constant) (e : IE) : Except String IE :=
  match unshare c e with
  | .all d b =>
    match unshare c b with
    | .all .. => lastBinderDom c b
    | _ => .ok d
  | _ => .error "the first motive's type is not a binder"

/-- `KernelModeled::rec_family_block`: the block of the first motive's carrier, at a recursor
record (`none` at any other record). -/
def recFamily (store : Store) (hash : ByteArray → Address) (a : Address) :
    Except String (Option Address) := do
  let some c := store a | throw s!"no record at {a}"
  let rx? : Option (Ixon.Recursor × Ctx) ← match c.info with
    | .recr r => pure (some (r, ⟨c, #[a]⟩))
    | .rPrj p => do
      let some cb := store p.block | throw s!"no block record at {p.block}"
      match cb.info with
      | .muts ms =>
        match ms[p.idx.toNat]? with
        | some (.recr r) => pure (some (r, ⟨cb, recurAddrs hash p.block ms⟩))
        | _ => throw "recursor projection at a member that is no recursor"
      | _ => throw "recursor projection at a record that is no block"
    | _ => pure none
  let some (r, x) := rx? | return none
  let some after := peel x.c r.params.toNat r.typ
    | throw "fewer leading binders than parameters"
  match unshare x.c after with
  | .all mdom _ =>
    let carrier ← lastBinderDom x.c mdom
    let (head, _) := spine x.c carrier
    let h ← match head with
      | .ref i _ => refAddr x i
      | .recur j _ => recurAddr x j
      | _ => throw "the carrier's head is not a constant"
    let some ch := store h | throw s!"no record at the carrier's head {h}"
    match ch.info with
    | .iPrj p => return some p.block
    | _ => throw "the carrier's head is not an inductive"
  | _ => throw "no motive binder after the parameters"

/-! ## Rows -/

def recordKind (c : Ixon.Constant) : String :=
  match c.info with
  | .defn d =>
    match d.kind with
    | .defn => "defn:definition"
    | .thm => "defn:theorem"
    | .opaq => "defn:opaque"
  | .recr _ => "recr:standalone-recursor"
  | .axio _ => "axio"
  | .quot _ => "quot"
  | .iPrj _ => "iPrj"
  | .cPrj _ => "cPrj"
  | .rPrj _ => "rPrj"
  | .dPrj _ => "dPrj"
  | .muts ms =>
    let ni := (ms.filter isIndc).size
    if ni == ms.size then "muts:inductive-block" else if ni > 0 then "muts:mixed" else "muts:other"

/-- The block a projection record names, or the record's own address at a block record. -/
def blockOf (a : Address) (c : Ixon.Constant) : Option Address :=
  match c.info with
  | .iPrj p => some p.block
  | .cPrj p => some p.block
  | .rPrj p => some p.block
  | .dPrj p => some p.block
  | .muts _ => some a
  | _ => none

/-- Whether `a` is the constant address its projection record names (`ConstAddrOf B cb a`):
the member's or the constructor's projection address, recomputed under `hash`. -/
def constAddrOf (store : Store) (hash : ByteArray → Address) (a : Address) (c : Ixon.Constant) :
    String :=
  let member (B : Address) (i : Nat) : String :=
    match store B with
    | some cb =>
      match cb.info with
      | .muts ms =>
        match ms[i]? with
        | some m => if projAddr hash (memberInfo B i m) == a then s!"yes:member-{i}" else "no:address-differs"
        | none => "no:index-outside-block"
      | _ => "no:block-is-no-muts"
    | none => "no:no-block-record"
  match c.info with
  | .iPrj p => member p.block p.idx.toNat
  | .rPrj p => member p.block p.idx.toNat
  | .dPrj p => member p.block p.idx.toNat
  | .cPrj p =>
    match store p.block with
    | some cb =>
      match cb.info with
      | .muts ms =>
        match ms[p.idx.toNat]? with
        | some (.indc ind) =>
          if p.cidx.toNat < ind.ctors.size then
            if projAddr hash (ctorInfo p.block p.idx.toNat p.cidx.toNat) == a then
              s!"yes:ctor-{p.idx}-{p.cidx}"
            else "no:address-differs"
          else "no:ctor-index-outside"
        | _ => "no:member-is-no-inductive"
      | _ => "no:block-is-no-muts"
    | none => "no:no-block-record"
  | .muts _ => "no:block-record-itself"
  | _ => "no:standalone"

def unstored : List Ix.Kernel.Role :=
  [.true, .trueIntro, .sorryAx, .trustCompiler, .reduceBool, .reduceNat,
   .ofReduceBool, .ofReduceNat, .notProp, .decidable, .decidableIsTrue, .decidableIsFalse,
   .natLe, .int, .intOfNat, .intNegSucc, .intLe, .bitVec, .bitVecOfNat, .byteArray,
   .byteArrayEmpty, .ofDecideEqTrue, .ofDecideEqFalse]

def roleStr (r : Ix.Kernel.Role) : String :=
  let s := reprStr r
  ((s.splitOn ".").getLast?).getD s

/-- A dotted Lean name as an `Ix.Name` (string components only). -/
def ixNameOf (s : String) : Ix.Name :=
  s.splitOn "." |>.foldl Ix.Name.mkStr Ix.Name.mkAnon

/-- The shortest published name of each target address. -/
def namesFor (env : Ixon.Env) (targets : Std.HashSet Address) : Std.HashMap Address String :=
  Id.run do
    let mut out : Std.HashMap Address String := {}
    for (n, nm) in env.named.toArray do
      if targets.contains nm.addr then
        let s := toString n
        match out[nm.addr]? with
        | some old =>
          if s.length < old.length || (s.length == old.length && s < old) then
            out := out.insert nm.addr s
        | none => out := out.insert nm.addr s
    return out

def routeStr : Except String Route → String
  | .ok r => s!"{r.members}\t{r.inductives}\t{if r.modeled then 1 else 0}\t{r.why}"
  | .error e => s!"-\t-\terror\t{e}"

def stamp (t0 : Nat) (msg : String) : IO Unit := do
  IO.eprintln s!"[ixvm-role-member-census] {(← IO.monoMsNow) - t0} ms: {msg}"

def run : IO UInt32 := do
  let some path ← IO.getEnv "IX_ROLE_IXE"
    | IO.eprintln "[ixvm-role-member-census] set IX_ROLE_IXE to an .ixe file"; return 1
  let t0 ← IO.monoMsNow
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  stamp t0 s!"{path}: {env.consts.size} records, {env.named.size} names"
  let store : Store := fun a => (env.consts.get? a).bind (·.get?)
  -- the default binding and its admission
  let b ← IO.ofExcept Ix.Kernel.Admission.defaultBinding
  let .ok t := Ix.Kernel.Admission.admitBinding Address.admissionHash b
    | IO.eprintln "[ixvm-role-member-census] the default binding does not admit"; return 3
  IO.println s!"TABLE\tbinding\t{b.address}\tbytes\t{b.bytes.size}\tversion\t{t.version}\tbound\t{t.bound.size}\tevidence\t{t.evidence.size}\troles\t{Ix.Kernel.Role.all.length}"
  let artifactBinding := match env.roleBinding with
    | some rb => if rb.bytes == b.bytes && rb.address == b.address then "default" else s!"other:{rb.address}"
    | none => "none"
  IO.println s!"TABLE\tartifact-binding\t{artifactBinding}"
  for (r, a) in t.bound do
    IO.println s!"TABLEROW\t{r.idx}\t{roleStr r}\t{a}"
  -- names of the bound records, their blocks and the blocks' first members
  let mut targets : Std.HashSet Address := {}
  for (_, a) in t.bound do
    targets := targets.insert a
    if let some c := store a then
      if let some B := blockOf a c then
        targets := targets.insert B
        if let some cb := store B then
          if let .muts ms := cb.info then
            if let some m := ms[0]? then
              targets := targets.insert (projAddr Address.admissionHash (memberInfo B 0 m))
      if let .ok (some F) := recFamily store Address.admissionHash a then
        targets := targets.insert F
        if let some cf := store F then
          if let .muts ms := cf.info then
            if let some m := ms[0]? then
              targets := targets.insert (projAddr Address.admissionHash (memberInfo F 0 m))
  let names := namesFor env targets
  stamp t0 s!"names of {targets.size} addresses: {names.size} found"
  let blockName (B : Address) : String :=
    match names[B]? with
    | some s => s
    | none =>
      match store B with
      | some cb =>
        match cb.info with
        | .muts ms =>
          match ms[0]? with
          | some m => (names[projAddr Address.admissionHash (memberInfo B 0 m)]?).getD "?"
          | none => "?"
        | _ => "?"
      | none => "?"
  IO.println "ROWHEAD\tidx\trole\tleanName\tstored\taddress\tname\tpublishedUnderRoleName\tkind\thashOk\tblock\tblockName\tmembers\tinductives\tmodeled\twhy\tconstAddrOf\tfamily\tfamilyName\tfamMembers\tfamInductives\tfamModeled\tfamWhy"
  let mut nRows := 0
  let mut nModeledConst := 0
  let mut nModeledAny := 0
  let mut nHashBad := 0
  let mut nHashDisagree := 0
  for (r, a) in t.bound do
    nRows := nRows + 1
    let stored := if unstored.contains r then "unstored" else "stored"
    let published := match env.named[ixNameOf (toString r.leanName)]? with
      | some nm => if nm.addr == a then "yes" else s!"no:{nm.addr}"
      | none => "unpublished"
    let nm := names.getD a "?"
    match env.consts.get? a, store a with
    | some lc, some c =>
      let hashOk := Address.admissionHash lc.rawBytes == a
      unless hashOk do nHashBad := nHashBad + 1
      let kind := recordKind c
      let cao := constAddrOf store Address.admissionHash a c
      unless cao == constAddrOf store Address.blake3 a c do nHashDisagree := nHashDisagree + 1
      let (blockCols, modeled) := match blockOf a c with
        | some B =>
          let rt := blockIsModeled store Address.admissionHash B
          let m := match rt with | .ok r => r.modeled | .error _ => false
          (s!"{B}\t{blockName B}\t{routeStr rt}", m)
        | none => ("-\t-\t-\t-\t-\t-", false)
      if modeled then nModeledAny := nModeledAny + 1
      if modeled && cao.startsWith "yes" then nModeledConst := nModeledConst + 1
      let famCols := match recFamily store Address.admissionHash a with
        | .ok (some F) => s!"{F}\t{blockName F}\t{routeStr (blockIsModeled store Address.admissionHash F)}"
        | .ok none => "-\t-\t-\t-\t-\t-"
        | .error e => s!"error\t{e}\t-\t-\t-\t-"
      IO.println s!"ROW\t{r.idx}\t{roleStr r}\t{r.leanName}\t{stored}\t{a}\t{nm}\t{published}\t{kind}\t{hashOk}\t{blockCols}\t{cao}\t{famCols}"
    | _, _ =>
      IO.println s!"ROW\t{r.idx}\t{roleStr r}\t{r.leanName}\t{stored}\t{a}\t{nm}\t{published}\tmissing\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-"
  IO.println s!"SUMMARY\trows\t{nRows}\tblock-modeled\t{nModeledAny}\tconstant-address-of-a-modeled-block\t{nModeledConst}\thash-mismatch\t{nHashBad}\tpure-vs-ffi-hash-disagreements\t{nHashDisagree}"
  stamp t0 "rows done"
  -- every inductive block of the environment
  let tableAddrs : Std.HashMap Address Ix.Kernel.Role :=
    t.bound.foldl (fun m (r, a) => m.insert a r) {}
  let mut nRec := 0
  let mut nFlag := 0
  let mut nMuts := 0
  let mut nParseErr := 0
  let mut nInd := 0
  let mut nMulti := 0
  let mut nNested := 0
  let mut nPlain := 0
  let mut nRouteErr := 0
  let mut nConstAddrs := 0
  let mut hits : Array String := #[]
  let mut routeErrs : Array String := #[]
  for (B, lc) in env.consts.toArray do
    nRec := nRec + 1
    if lc.len == 0 then continue
    -- the record's first byte carries its tag's flag in the high nibble (`muts`: 0xC)
    if lc.cache.isNone && (lc.buf[lc.off]!) >>> 4 != 0xC then continue
    nFlag := nFlag + 1
    match lc.get? with
    | none => nParseErr := nParseErr + 1
    | some cb =>
      match cb.info with
      | .muts ms =>
        nMuts := nMuts + 1
        if (ms.filter isIndc).size > 0 then
          nInd := nInd + 1
          let rt := routeOf store Address.blake3 B cb
          match rt with
          | .ok r =>
            if r.inductives ≥ 2 then nMulti := nMulti + 1
            else if r.modeled then nNested := nNested + 1
            else nPlain := nPlain + 1
          | .error e =>
            nRouteErr := nRouteErr + 1
            if routeErrs.size < 20 then routeErrs := routeErrs.push s!"{B}\t{e}"
          let mems := recurAddrs Address.blake3 B ms
          let mut i := 0
          for m in ms do
            let x := mems[i]!
            nConstAddrs := nConstAddrs + 1
            if let some r := tableAddrs[x]? then
              hits := hits.push s!"{roleStr r}\t{x}\tmember-{i}\t{B}\t{routeStr rt}"
            if let .indc ind := m then
              for j in [0:ind.ctors.size] do
                let y := projAddr Address.blake3 (ctorInfo B i j)
                nConstAddrs := nConstAddrs + 1
                if let some r := tableAddrs[y]? then
                  hits := hits.push s!"{roleStr r}\t{y}\tctor-{i}-{j}\t{B}\t{routeStr rt}"
            i := i + 1
      | _ => pure ()
  stamp t0 "blocks done"
  IO.println s!"GLOBAL\trecords\t{nRec}\tmuts-flag\t{nFlag}\tparse-errors\t{nParseErr}\tmuts\t{nMuts}\tinductive-blocks\t{nInd}\ttwo-or-more\t{nMulti}\tone-nested\t{nNested}\tone-native\t{nPlain}\troute-errors\t{nRouteErr}\tconstant-addresses\t{nConstAddrs}\tbound-hits\t{hits.size}"
  for h in hits do
    IO.println s!"GLOBALHIT\t{h}"
  for e in routeErrs do
    IO.println s!"ROUTEERR\t{e}"
  return 0

end Tests.Ix.IxVM.RoleMemberCensus
