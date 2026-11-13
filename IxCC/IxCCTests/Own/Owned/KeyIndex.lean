import IxCC.Recheck.Rc.Produce

/-! # Policy selection's linear form against the list form

`Own.Plain.enrichFirContracts` (which `selectRcPolicyForSrc` and `Program.canonicalForSrc` run)
reads a key's function from `keyIndex` and merges in one pass; `enrichFirContracts_eq_list`
(`Recheck/Rc/Proof/KeyIndex.lean`) proves it equal to `enrichFirContractsList`. Tested before it
was proved, and kept: on each program given (`tests-own-owned` passes every corpus root with its
source, then `synthetic`'s programs), the definition before 2026-11-13 written out here
(`listEnrich`, the independent reference), the production list form and the definition must give
the same enriched program (every function's contracts and result) and the same policy, and the
key index must give `funList.find?`'s function for every key and every base key the
specialisation, worker and λ keys lead to. The synthetic programs cover every key constructor,
a key held by two functions (the first in id order wins), a base key no function has, nested
specialisations and workers, and contract lists shorter and longer than the parameters. -/

set_option autoImplicit false

namespace IxCCTests.Own.Owned.KeyIndex

open IxCC IxCC.Own.Plain IxCC.Ixon

/-- The list form, written out: `enrichFirContracts`'s definition before 2026-11-13. -/
def listEnrich (src : Src.Program) (P : Fir.Program) : Fir.Program :=
  { P with
    funs := P.funs.map fun f =>
      let fromProg := progKeyContracts src P f.key
      let n := f.params.length
      let contracts := (List.range n).map fun i =>
        mergeBinderContract (f.contracts.getD i {}) (fromProg.getD i {})
      let result := if f.result != .shared then f.result else progKeyResult src P f.key
      { f with contracts, result } }

/-- Two enrichments of one program agree: every function's key, arity, contracts and result. -/
def same (A B : Fir.Program) : Bool :=
  A.size == B.size && (List.range A.size).all fun f =>
    match A.fun? f, B.fun? f with
    | some x, some y => decide (x.key = y.key) && x.params.length == y.params.length &&
        x.contracts == y.contracts && x.result == y.result
    | none, none => true
    | _, _ => false

/-- The keys a function's enrichment looks up: its own, and the bases its key leads to. -/
def lookedUp : Key.GKey → List Key.GKey
  | .spec g args => .spec g args :: lookedUp g
  | .worker g keep => .worker g keep :: lookedUp g
  | .lam g path => .lam g path :: lookedUp g
  | k => [k]

def keyTag : Key.GKey → Nat
  | .const .. => 0 | .byName .. => 1 | .recStar .. => 2 | .wrapper .. => 3 | .spec .. => 4
  | .worker .. => 5 | .lam .. => 6 | .dispatch _ => 7 | .entry .. => 8

structure Tally where
  programs : Nat := 0
  functions : Nat := 0
  /-- functions by key constructor (`keyTag`) -/
  byKey : Array Nat := .replicate 9 0
  lookups : Nat := 0
  /-- lookups that find a function, and those that find none -/
  hits : Nat := 0
  misses : Nat := 0
  /-- functions whose key an earlier function also has -/
  duplicates : Nat := 0
  failures : Array String := #[]

def Tally.fail (t : Tally) (msg : String) : Tally := { t with failures := t.failures.push msg }

def checkProgram (t : Tally) (label : String) (src : Src.Program) (P : Fir.Program) : Tally := Id.run do
  let mut t := { t with programs := t.programs + 1 }
  let a := listEnrich src P
  let b := enrichFirContractsList src P
  let c := enrichFirContracts src P
  unless same a b do t := t.fail s!"{label}: enrichFirContractsList differs from the written-out list form"
  unless same a c do t := t.fail s!"{label}: enrichFirContracts differs from the list form"
  unless selectRcPolicy a == selectRcPolicyForSrc src P do
    t := t.fail s!"{label}: selectRcPolicyForSrc differs from the list form's policy"
  let ix := keyIndex P
  let fl := P.funList
  let mut seen : Array Key.GKey := #[]
  for (_, fd) in fl do
    t := { t with functions := t.functions + 1, byKey := t.byKey.modify (keyTag fd.key) (· + 1) }
    if seen.any (· = fd.key) then t := { t with duplicates := t.duplicates + 1 }
    seen := seen.push fd.key
    for k in lookedUp fd.key do
      let want := (fl.find? fun (_, g) => decide (g.key = k)).map (·.2)
      let got := ix[k]?
      t := { t with lookups := t.lookups + 1 }
      if want.isSome then t := { t with hits := t.hits + 1 } else t := { t with misses := t.misses + 1 }
      let agree := match want, got with
        | some x, some y => decide (x.key = y.key) && x.contracts == y.contracts &&
            x.result == y.result && x.params.length == y.params.length
        | none, none => true
        | _, _ => false
      unless agree do t := t.fail s!"{label}: the key index and funList.find? differ on a key"
  return t

/-! ## Synthetic programs -/

def fn (key : Key.GKey) (params : Nat) (contracts : List V3.BinderContract := [])
    (result : V3.ValueContract := .shared) : Fir.Fun :=
  let ps : List (Fir.Var × Fir.Rep) := (List.range params).map fun v => (v, .tobj)
  { (default : Fir.Fun) with key := key, params := ps, body := .trap, vars := params,
                             contracts := contracts, result := result }

def prog (fs : List Fir.Fun) : Fir.Program :=
  { funs := Src.NatMap.ofList (fs.zipIdx.map fun (f, i) => (i, f)), size := fs.length,
    exports := [0], ctors := [], known := {} }

def u : V3.BinderContract := { uses := .linear }
def b : V3.BinderContract := { value := .localShared }
def e : V3.BinderContract := V3.BinderContract.erased

/-- Every key constructor, duplicates, a missing base, nested specialisations and workers,
contract lists of every length against the arity. -/
def mixed : Fir.Program :=
  let c0 : Key.GKey := .const 0 []
  let c1 : Key.GKey := .const 1 [true]
  let sp : Key.GKey := .spec c0 [.hole 1, .glob c1, .con (.src 3) [.hole 0, .lit 7]]
  prog [
    fn c0 3 [u, b, e],
    fn c1 2 [b] .unique,
    fn c0 3 [e, e, e],                       -- c0 again: the first wins
    fn sp 2,
    fn (.worker c0 [true, false, true]) 2,
    fn (.worker sp [false, true]) 1,
    fn (.spec (.worker c0 [true, true, false]) [.hole 0, .hole 2]) 3 [u],
    fn (.lam c1 [0, 2]) 4 [] .shared,
    fn (.lam (.lam sp [1]) [0]) 1,
    fn (.const 99 []) 1,
    fn (.spec (.const 98 []) [.hole 0]) 1,   -- a base no function has
    fn (.worker (.const 97 []) [true]) 1,
    fn (.byName 0 []) 2 [b, b, b, b],         -- longer than the arity
    fn (.recStar 1 [false]) 1,
    fn (.wrapper (.ctor 2) []) 2 [e],
    fn (.wrapper (.prim .add) []) 2,
    fn (.dispatch 3) 3,
    fn (.entry c0 2) 2 [] .unique,
    fn (.entry c0 2) 2 [u, u]]                -- a duplicate whose contracts differ

/-- `n` distinct constants, then `n` specialisations and `n` workers of them. -/
def wide (n : Nat) : Fir.Program :=
  prog ((List.range n).map (fun i => fn (.const i []) 4 [u, {}, b]) ++
        (List.range n).map (fun i => fn (.spec (.const i []) [.hole 1, .hole 0]) 2) ++
        (List.range n).map (fun i => fn (.worker (.const (n - 1 - i) []) [false, true, true, true]) 3))

def synthetic (t : Tally) : Tally := Id.run do
  let mut t := checkProgram t "mixed" default mixed
  for n in [1, 7, 300] do t := checkProgram t s!"wide {n}" default (wide n)
  return t

def report (t : Tally) : List String × Tally :=
  let t := if t.programs == 0 then t.fail "policy selection: no programs" else t
  let t := if t.duplicates == 0 then t.fail "policy selection: no duplicate key" else t
  let t := if t.misses == 0 then t.fail "policy selection: no lookup that finds no function" else t
  let t := if t.byKey.any (· == 0) then t.fail s!"policy selection: a key constructor never seen ({t.byKey})" else t
  ([s!"policy selection (enrichFirContracts against the list forms): {t.programs} programs, \
      {t.functions} functions (by key constructor {t.byKey}, {t.duplicates} with a key held \
      earlier), {t.lookups} key lookups ({t.hits} found, {t.misses} found none); \
      {t.failures.size} failures"], t)

end IxCCTests.Own.Owned.KeyIndex
