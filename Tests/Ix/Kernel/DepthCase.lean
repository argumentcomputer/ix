import Ix.Ixon.Authenticated
import Ix.KernelCheck.Run
import Ix.Runtime.Thread

/-! # The cases of `kernel-depth`, run one per process (`kernel-depth-case NAME N`)

The records and entry points of each case; the test itself, which runs each
case on a 2 MiB stack in a process of its own, and what each case shows, are in
`Tests.Ix.Kernel.Depth`. A separate small executable, so that a case's process
starts in milliseconds (the test binary's own start-up takes about 20 s). -/

namespace Tests.Ix.Kernel.Depth

open Benchmarks.Kernel.CheckIxeStep

abbrev IE := _root_.Ixon.Expr
abbrev IU := _root_.Ixon.Univ

/-! ## The records -/

/-- `∀ p : Prop, p`, a closed proposition. -/
def P : IE := _root_.Ixon.Expr.leanAll (.sort 0) (.var 0)

/-- `∀ p : Prop, p → p`. -/
def Pid : IE := _root_.Ixon.Expr.leanAll (.sort 0) (_root_.Ixon.Expr.leanAll (.var 0) (.var 1))

/-- `Prop`, `Type`. -/
def univs01 : Array IU := #[.zero, .succ .zero]

def defnR (ty val : IE) (refs : Array Address) : _root_.Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, 0, ty, val⟩, #[], refs, univs01⟩

def record (c : _root_.Ixon.Constant) : Address × ByteArray :=
  let b := _root_.Ixon.serConstant c
  (Address.admissionHash b, b)

/-- `D0 : Type := Prop`, then `n` records `Dj : Type := step D(j-1)`, then
`last D_n` if given. -/
def chain (n : Nat) (step : IE → IE) (last : Option (IE → IE)) : _root_.Ix.Kernel.Admission.Records := Id.run do
  let d0 := record (defnR (.sort 1) (.sort 0) #[])
  let mut rs := #[d0]
  let mut prev := d0.1
  for _ in [0:n] do
    let dj := record (defnR (.sort 1) (step (.ref 0 #[])) #[prev])
    rs := rs.push dj
    prev := dj.1
  if let some f := last then
    rs := rs.push (record (defnR (.ref 0 #[]) (f (.ref 0 #[])) #[prev]))
  return rs.toList

/-- `delta n`: `X : D_n := P` after `Dj : Type := D(j-1)`. -/
def delta (n : Nat) : _root_.Ix.Kernel.Admission.Records := chain n id (some fun _ => P)

/-- `wide n`: `Dj : Type := Prop → D(j-1)`; nothing unfolds. -/
def wide (n : Nat) : _root_.Ix.Kernel.Admission.Records := chain n (_root_.Ixon.Expr.leanAll (.sort 0)) none

/-- A natural number's blob: its little-endian bytes, without trailing zeros
(the reader's `natural`). -/
def natBytes (n : Nat) : ByteArray := Id.run do
  let mut out : ByteArray := .empty
  let mut m := n
  while m > 0 do
    out := out.push (m % 256).toUInt8
    m := m / 256
  return out

/-- `iota n`: `X : Prop := Nat.rec.{1} (fun _ : Nat => Prop) P' (fun n ih => ih) n`
with `P' = ∀ p : Prop, p → p` and `n` a literal (a blob), then `T : X := fun p h => h`.
`Nat.rec` and `Nat` are the prelude's, at the addresses the default table binds. -/
def iota (table : _root_.Ix.Kernel.RoleTable) (n : Nat) :
    Except String (_root_.Ix.Kernel.Admission.Records × _root_.Ix.Kernel.Ingress.Blobs) := do
  let bound (r : _root_.Ix.Kernel.Role) : Except String Address :=
    match table.bound.find? (·.1 == r) with
    | some (_, a) => pure a
    | none => throw s!"the default table binds no {repr r}"
  let natRec ← bound .natRec
  let nat ← bound .nat
  let blob := natBytes n
  let blobAddr := Address.admissionHash blob
  let motive : IE := _root_.Ixon.Expr.leanLam (.ref 1 #[]) (.sort 0)
  let minor : IE := _root_.Ixon.Expr.leanLam (.ref 1 #[]) (_root_.Ixon.Expr.leanLam (.sort 0) (.var 0))
  let value : IE := .app (.app (.app (.app (.ref 0 #[1]) motive) Pid) minor) (.nat 2)
  let x := record (defnR (.sort 0) value #[natRec, nat, blobAddr])
  let t := record (defnR (.ref 0 #[]) (_root_.Ixon.Expr.leanLam (.sort 0) (_root_.Ixon.Expr.leanLam (.var 0) (.var 0))) #[x.1])
  pure ([x, t], [(blobAddr, blob)])

/-- The command line's limits (`ix check-lean`'s `artifactLimits`). -/
def limits : _root_.Ix.Kernel.Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

def hint : _root_.Ix.Kernel.ConstRef Address → Option _root_.Ix.Kernel.ReducibilityHint := fun _ => some (.regular 1)

/-! ## The record-by-record check -/

/-- An address that encodes `n` (no hashing: the loop source decodes it). -/
def addrOf (n : Nat) : Address :=
  ⟨⟨(List.range 32).toArray.map fun i => if i < 8 then ((n >>> (8 * i)) % 256).toUInt8 else 0x5a⟩⟩

def indexOf (a : Address) : Nat :=
  (List.range 8).foldr (fun i acc => acc * 256 + (a.hash.data[i]?.getD 0).toNat) 0

/-- `n` declarations `Dj : Type := Prop` and, last, `Dn : Type := Type`
(rejected): the check-lean step's records, read without a codec. -/
def stepSource (n : Nat) : LoopSource Nat .anon :=
  let decl (j : Nat) : _root_.Ix.Kernel.Declaration .anon :=
    .defnDecl ⟨.id (addrOf j), [], .sort (.succ .zero)⟩
      (.sort (if j < n then .zero else .succ .zero)) .opaque
  { view := fun _ => some { kind := "fixture", recs := #[], deps := fun _ => #[] }
    read := fun _ a => pure { decls := #[decl (indexOf a)] }
    commit := fun st _ _ => st + 1
    init := pure 0 }

/-! ## One case, in the child -/

/-- A non-tail recursion `n` deep (the control). -/
def deep : Nat → Nat
  | 0 => 0
  | n + 1 => deep n + 1

def timed (act : IO String) : IO String := do
  let t0 ← IO.monoMsNow
  let s ← act
  return s!"{s} in {(← IO.monoMsNow) - t0} ms"

def entryVerdict (r : Except _root_.Ix.Kernel.Admission.Error (_root_.Ix.Kernel.Env .anon)) : String :=
  match r with
  | .ok env => s!"accepted ({env.consts.length} constants)"
  | .error e => s!"{if e.outcome == .declined then "declined" else "rejected"}: {(toString e).take 200}"

/-- Run one case; the line it prints starts with the verdict. -/
def runOne (name : String) (n : Nat) : IO String := do
  let binding ← IO.ofExcept _root_.Ix.Kernel.Admission.defaultBinding
  match name with
  | "control" => return s!"returned {deep n}"
  | "delta" => timed do
    let rs := delta n
    IO.lazyPure fun _ => entryVerdict (_root_.Ixon.Authenticated.checkBytes binding limits rs [] hint)
  | "delta-tiered" => timed do
    let rs := delta n
    IO.lazyPure fun _ =>
      match _root_.Ixon.Authenticated.checkBytesTiered binding limits rs [] hint with
      | .ok (env, _) => s!"accepted ({env.consts.length} constants)"
      | .error e => s!"refused: {(toString e).take 200}"
  | "iota" => timed do
    let table ← IO.ofExcept _root_.Ix.Kernel.Reader.defaultTable
    let (rs, blobs) ← IO.ofExcept (iota table n)
    IO.lazyPure fun _ => entryVerdict (_root_.Ixon.Authenticated.checkBytes binding limits rs blobs hint)
  | "wide" => timed do
    let rs := wide n
    IO.lazyPure fun _ => entryVerdict (_root_.Ixon.Authenticated.checkBytes binding limits rs [] hint)
  | "step" | "step-pool" => timed do
    let cfg : RunConfig := if name == "step" then {} else { workers := some 1 }
    let report ← runRecords (stepSource n) [] (fun _ => #[])
      ((Array.range (n + 1)).map addrOf) cfg
    let accepts := report.rows.filter (·.outcome == "accept") |>.size
    let last := (report.rows.back?.map (·.outcome)).getD "none"
    return s!"{accepts} accepted, last {last}, {report.rows.size} rows"
  | _ => throw (IO.userError s!"kernel-depth: unknown case {name}")

/-- `kernel-depth-case NAME N`: run the case on a dedicated thread of
`LEAN_STACK_SIZE_KB` and print one line, `NAME N: VERDICT`. -/
def runCase (args : List String) : IO UInt32 := do
  let some kb := (← IO.getEnv "LEAN_STACK_SIZE_KB").bind String.toNat?
    | IO.eprintln "kernel-depth-case: LEAN_STACK_SIZE_KB unset"; return 2
  let [name, nStr] := args | IO.eprintln "usage: kernel-depth-case NAME N"; return 2
  let some n := nStr.toNat? | IO.eprintln s!"kernel-depth-case: bad size {nStr}"; return 2
  _root_.Ix.Runtime.setLeanThreadStackSize (USize.ofNat (kb * 1024))
  let line ← IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) (runOne name n)))
  IO.println s!"{name} {n}: {line}"
  return 0

end Tests.Ix.Kernel.Depth
