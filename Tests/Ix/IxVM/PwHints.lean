import Ix.IxVM.PwCheck
import Ix.IxVM.ClaimHarness
import Ix.Shard.Environment
import Ix.KernelCheck.Step

/-!
# The binder-data annotator (D2)

`IxVM.PwHints.annotate` writes, for every record a witness carries, the datum
of every `Lam` and `All` node and the variant of every `Share` site, keyed as
lane cx's interface (`plans/ixvmc/cx/REPORT.md`, "D2 hint interface") says.

`ixvm-pw-hints` holds the annotator to hand-made records whose data are known:
* a sharing entry `x → x` with `x` loose, used under `A : Prop` and under
  `B : Type`: the binder is `ifAllZero []` at the first, `never` at the
  second, so the entry gets two variants;
* a `let` (the kernel annotates its body as the ζ-reduct, its value on its own);
* a datum with a level parameter, `(α : Sort u) → α → α`.
Each is checked by value, by the host-side check (`IxVM.PwHints.check`:
coverage, and every aligned binder against the kernel's own annotation pass),
and by tampering: a wrong datum is a mismatch, a dropped block a missing key.
The stream encoding round-trips.

`ixvm-pw-corpus` (manual) measures the annotator on a compiled corpus:
`IX_PW_IXE` (an `.ixe`), and with `IX_PW_IXES` (its shard manifest) each
shard's claim closure as `ix check` builds it, one line per shard.
-/

namespace Tests.Ix.IxVM.PwHints

open IxVM.PwHints

private def all := Ixon.Expr.leanAll
private def lam := Ixon.Expr.leanLam

/-- `(A : Prop) → (A → A) → (B : Type) → (B → B) → Prop`, both `_ → _` the
sharing entry 0, `x → x` with `x` loose. -/
def twoSorts : Ixon.Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ :=
      all (.sort 0) (all (.share 0) (all (.sort 1) (all (.share 0) (.sort 0)))) }
    sharing := #[all (.var 0) (.var 1)], refs := #[], univs := #[.zero, .succ .zero] }

/-- `def _ : Prop → Prop := fun p => let q : Prop := p → p; q → q`. -/
def letBody : Ixon.Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0,
      typ := all (.sort 0) (.sort 0),
      value := lam (.sort 0)
        (Ixon.Expr.leanLet false (.sort 0) (all (.var 0) (.var 1)) (all (.var 0) (.var 1))) }
    sharing := #[], refs := #[], univs := #[.zero] }

/-- `(α : Sort u) → α → α`. -/
def polyId : Ixon.Constant :=
  { info := .axio { isUnsafe := false, lvls := 1, typ := all (.sort 0) (all (.var 0) (.var 1)) }
    sharing := #[], refs := #[], univs := #[.var 0] }

private def never : Node := .binder none
private def always : Node := .binder (some #[])

/-- The expected blocks of each record. -/
def expected : List (Ixon.Constant × Array Block) := [
  (twoSorts, #[⟨0, 0, 0, #[never, never, .share 0, never, never, .share 1]⟩,
               ⟨1, 0, 0, #[always]⟩, ⟨1, 0, 1, #[never]⟩]),
  (letBody, #[⟨0, 0, 0, #[never]⟩, ⟨0, 1, 0, #[never, always, always]⟩]),
  (polyId, #[⟨0, 0, 0, #[.binder (some #[0]), .binder (some #[0])]⟩])]

/-- An environment of `cs` bound to the default role table, without the
table's support records (the records name no role). -/
def envOf (cs : List Ixon.Constant) : Except String Ixon.Env := do
  let bytes ← Ix.Kernel.Reader.defaultTableBytes
  let env : Ixon.Env := { roleBinding := some { address := Address.blake3 bytes, bytes } }
  return cs.foldl (fun env c => env.storeConst (Address.blake3 (Ixon.ser c)) c) env

/-- A witness's IO with every record of `env`, without binder data. -/
def bufferOf (env : Ixon.Env) : Aiur.IOBuffer :=
  IxVM.ClaimHarness.addEntries env (fun _ => true) (IxVM.ClaimHarness.seedBinding env default)

private def ensure (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

def units : IO Unit := do
  let env ← IO.ofExcept (envOf (expected.map (·.1)))
  let io := bufferOf env
  let (io', stats) ← IO.ofExcept (annotate io env)
  IO.println s!"[ixvm-pw-hints] {stats.render}"
  ensure (stats.fallbacks == 0) "the kernel's pass failed at a binder"
  ensure (stats.extraVariants == 1) s!"expected one variant beyond 0, got {stats.extraVariants}"
  let table ← IO.ofExcept (tableOf io')
  for (c, blocks) in expected do
    let a := Address.blake3 (Ixon.ser c)
    for b in blocks do
      let got := table[(a, b.ekind, b.eidx, b.variant)]?
      ensure (got == some b.nodes)
        s!"{a} ({b.ekind}, {b.eidx}) variant {b.variant}: {repr got}, expected {repr b.nodes}"
  ensure (table.size == (expected.map (·.2.size)).sum) s!"{table.size} blocks, expected more or fewer"
  -- the encoding round-trips
  for (_, blocks) in expected do
    let back := match decode (encode blocks) with
      | .ok bs => bs == blocks
      | .error _ => false
    ensure back "the stream encoding does not round-trip"
  -- the host-side check: complete, and the kernel's
  let rep ← IO.ofExcept (check io' env)
  IO.println s!"[ixvm-pw-hints] check: {rep.render}"
  for s in rep.samples do IO.println s!"  {s}"
  ensure rep.ok "the annotated witness fails the check"
  ensure (rep.compared ≥ 10 && rep.unaligned == 1) s!"unexpected comparison counts: {rep.render}"
  -- tampering: a wrong datum is a mismatch, a missing block a missing key
  let k ← IO.ofExcept (KernelEnv.ofView (View.ofBuffer io env))
  let (tables, _) := annotateKernel k
  let polyAddr := Address.blake3 (Ixon.ser polyId)
  let twoAddr := Address.blake3 (Ixon.ser twoSorts)
  let wrong := tables.map fun (a, bs) =>
    if a == polyAddr then (a, bs.map fun b => { b with nodes := b.nodes.set! 0 never }) else (a, bs)
  let rep ← IO.ofExcept (check (seed io wrong).1 env)
  ensure (rep.mismatches ≥ 1 && rep.missing == 0) s!"a wrong datum was not caught: {rep.render}"
  let dropped := tables.map fun (a, bs) =>
    if a == twoAddr then (a, bs.filter (·.variant == 0)) else (a, bs)
  let rep ← IO.ofExcept (check (seed io dropped).1 env)
  ensure (rep.missing ≥ 1) s!"a missing block was not caught: {rep.render}"
  -- a witness without data is caught, and `withHints` leaves one with data alone
  let rep ← IO.ofExcept (check io env)
  ensure (rep.missing ≥ 1) "a witness without binder data passed the check"
  ensure (hasHints io' && !hasHints io) "hasHints"

def run : IO UInt32 := do
  try
    units
    IO.println "[ixvm-pw-hints] passed"
    return 0
  catch e =>
    IO.eprintln s!"[ixvm-pw-hints] FAILED: {e}"
    return 1

/-! ## The corpus measurement -/

private def rssKb : IO Nat := Benchmarks.Kernel.CheckIxeStep.statusKb "VmHWM:"

/-- Annotate `io` and report the time, the counts and the peak memory so far. -/
def measure (label : String) (env : Ixon.Env) (io : Aiur.IOBuffer) : IO Stats := do
  let t0 ← IO.monoMsNow
  let (_, stats) ← IO.ofExcept (annotate io env)
  let ms := (← IO.monoMsNow) - t0
  IO.println s!"PWCORPUS {label}: ms={ms} {stats.render} hwm_kb={← rssKb}"
  return stats

def corpus : IO UInt32 := do
  let some ixe ← IO.getEnv "IX_PW_IXE" | do IO.eprintln "IX_PW_IXE is not set"; return 1
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))
  let env ← IO.ofExcept (IxVM.ClaimHarness.withDefaultRoleBinding env)
  IO.println s!"PWCORPUS loaded {ixe}: {env.consts.size} records, hwm_kb={← rssKb}"
  match ← IO.getEnv "IX_PW_IXES" with
  | some ixes =>
    let shards ← match ← Ix.Shard.loadEnvAndShards ixes ixe with
      | .ok (_, shards) => pure shards
      | .error e => throw (IO.userError e)
    let mut total : Stats := {}
    let t0 ← IO.monoMsNow
    for (blocks, k) in shards.zipIdx do
      let owned := Ix.Shard.ownedConstsForBlocks env blocks
      let (_, closure, _) ← IO.ofExcept (IxVM.ClaimHarness.shardCheckEnvClaim env owned true)
      let io := IxVM.ClaimHarness.addEntries env closure.contains
        (IxVM.ClaimHarness.seedBinding env default)
      total := total.add (← measure s!"shard {k} ({owned.size} owned, {closure.size} in closure)" env io)
    IO.println s!"PWCORPUS shards total: ms={(← IO.monoMsNow) - t0} {total.render} hwm_kb={← rssKb}"
  | none => pure ()
  if (← IO.getEnv "IX_PW_WHOLE") != some "0" then
    let _ ← measure "whole environment" env (bufferOf env)
  return 0

end Tests.Ix.IxVM.PwHints
