import Aiur.Library.Field.BN254
import Aiur.Library.Field.BLS12381.Prime
import Aiur.Tiling.IxaTrace
import Aiur.Tiling.WideIxa
import Aiur.Tiling.GroupedIxa
import Aiur.Plonk.SharedSound
import Aiur.Plonk.Terminal
import Aiur.Plonk.Layout
import Aiur.Plonk.Schema
import Aiur.Plonk.Stage
import Aiur.Plonk.BetaGadget

/-!
# `plonk_export`: the terminal's sparse R1CS as an `ix-aiur-scs-v1` file

`plonk_export terminal.ixa schema.json out.ixscs [nocheck] [selector-maps] [--bn254|--bls12-381]`
builds the stage as `plonk_check_stage` does (`WideIxa.stageOf` at the
entry `Schema.entryOf` resolves from the schema's `callable`, the root table
last: `rootAir k n` with `CALL` and the entry id `k` as circuit constants, its
`n` cells the statement limbs, which are the public wires, then the outputs), decides `stageOk`, `Layout.finalOk`, `Layout.linkOkF` and
`Beta.betaOk` (unless `nocheck`), and writes `emitScsFull airs P W steps`
under the dense layout `W = Layout.wiringF …`.

The tables are `units ++ maps ++ roms ++ [root]`. By default the map tables
are the compiler's (`Grouped.sharedTablesOf`, labels `map_shared/<k>`, cells
the main count columns, rows the fixed height), each accepted by
`SharedTable.checkFast` (`= check`, `checkFast_eq`) against the stage's
claims or nothing is written; soundness is `plonk_shared_heap_sound`. With
`selector-maps` they are the per-claim-length selector tables `mapAirs`
(labels `map/<L>`, `plonk_wide_heap_sound`), which the Rust witness does not
fill.

The file holds:

* gates: `emitGates` (boundary, pool and every row's gates instantiated by
  `Layout.wireOf`; a uniform table's rows reuse row 0's lowering, equal by
  `lowerRowState_uniform`) and `Beta.gadgetGates steps`, each as
  `exportGate` (`exportGate_holds`), ordered pre-commitment first;
* the commitment list `commitList airs L.cellWire`, in its own order;
* `γ = L.poolWire gammaRef`, `β = L.poolWire betaRef`.

The pre-commitment gates are the `constraint` and `count` gates whose wires
are cells or row locals; every other gate (boundary, `β` gadget, pool,
fingerprint, `q`, running sum) is post-commitment. The file is a
permutation of `emitScsFull`'s gates: `Scs.Satisfied` does not depend on
order.

For the prover, each wire carries a hint: an input (public or cell), the
commitment challenge, a bit of another wire, or "solve gate `i`" (the first
gate, in file order, in which it is the only unsolved wire). Hints do not
affect soundness.

Layout (little-endian): magic `ixscs001`; ten `u64`: publics, outputs,
wires, gates, pre-commitment gates, commits, `γ`, `β`, coefficients,
tables; `outputs × u32` output wires; `coefficients × 32` bytes (canonical
`Fr`); `gates × 26` bytes (`a b c : u32`, `sel : u8` with bits
`sL sR sO sM`, `α β ω : u32` coefficient ids, `qC : i8`); `commits × u32`;
`wires × 9` bytes (`kind : u8`, `x y : u32`; kind 0 input, 1 solve gate `x`,
2 bit `y` of wire `x`, 3 commitment challenge, 4 free); per table a `u16`
name length, the name, `cellBase : u64`, `rows : u32`, `width : u32`.
-/

namespace Aiur.Plonk.Export

open Aiur.Plonk Aiur.Tiling Aiur.Tiling.WideStage
open Aiur.Plonk.Lower (LGate Ref)

/-- For `SharedTable.checkFast`, which equals `check` under any instance. -/
local instance {p : Nat} : Hashable (ZMod p) := ⟨fun x => hash x.val⟩

def say (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

def pushU8 (b : ByteArray) (x : Nat) : ByteArray := b.push x.toUInt8

def pushU32 (b : ByteArray) (x : Nat) : ByteArray :=
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

def pushU64 (b : ByteArray) (x : Nat) : ByteArray := pushU32 (pushU32 b (x % 2 ^ 32)) (x >>> 32)

def pushFr {p : Nat} (b : ByteArray) (x : ZMod p) : ByteArray := Id.run do
  let mut b := b
  let v := x.val
  for i in [0:32] do b := b.push (v >>> (8 * i)).toUInt8
  return b

def getU32 (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat ||| (b[i + 1]!.toNat <<< 8) ||| (b[i + 2]!.toNat <<< 16) ||| (b[i + 3]!.toNat <<< 24)

/-- A gate's exported coefficients: selector bits, coefficient ids, `qC`. -/
structure Conv where
  sel : Nat
  α : Nat
  β : Nat
  ω : Nat
  qC : Int

structure Coeffs (p : Nat) where
  idx : Std.HashMap Nat Nat := {}
  vals : Array (ZMod p) := #[]

def Coeffs.id {p : Nat} (c : Coeffs p) (x : ZMod p) : Coeffs p × Nat :=
  match c.idx[x.val]? with
  | some i => (c, i)
  | none => ({ idx := c.idx.insert x.val c.vals.size, vals := c.vals.push x }, c.vals.size)

/-- `exportGate` of the coefficients, with ids; `none` when the gate has no
`GGate` form or an operand coefficient is zero. -/
def convert {p : Nat} [Fact (Nat.Prime p)] (c : Coeffs p) (L R O M C : ZMod p) : Coeffs p × Option Conv :=
  match exportGate ⟨0, 0, 0, L, R, O, M, C⟩ with
  | none => (c, none)
  | some g =>
      if g.α == 0 || g.β == 0 || g.ω == 0 then (c, none)
      else
        let (c, ia) := c.id g.α
        let (c, ib) := c.id g.β
        let (c, io) := c.id g.ω
        let sel := (if g.sL then 1 else 0) + (if g.sR then 2 else 0) + (if g.sO then 4 else 0) + (if g.sM then 8 else 0)
        (c, some ⟨sel, ia, ib, io, g.qC⟩)

def writeGate (b : ByteArray) (a bb c : Nat) (v : Conv) : ByteArray :=
  let b := pushU32 (pushU32 (pushU32 b a) bb) c
  let b := pushU8 b v.sel
  let b := pushU32 (pushU32 (pushU32 b v.α) v.β) v.ω
  pushU8 b (if v.qC < 0 then (256 + v.qC).toNat else v.qC.toNat)

/-- Pre-commitment: a constraint or count gate over cells and row locals. -/
def isPre {F : Type} (g : LGate F) : Bool :=
  (match g.tag with | .constraint | .count => true | _ => false) &&
    [g.a, g.b, g.c].all fun x => x % 4 == 0 || x % 4 == 1

def runFor (p : Nat) [Fact (Nat.Prime p)] (args : List String) (check sharedMaps : Bool) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let pkg ← IO.ofExcept (Ixa.decodeChecked (F := ZMod p) p ZMod.val
    (← IO.FS.readBinFile args[0]!))
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile args[1]!))
  let src ← IO.ofExcept (Schema.source (F := ZMod p) j)
  let nPublicInputs ← IO.ofExcept (j.getObjValAs? Nat "public_inputs")
  let nOutputs ← IO.ofExcept (j.getObjValAs? Nat "private_outputs")
  let circuits := src.tables.filterMap fun t =>
    if pkg.chips.any (·.name == t.name) then some (t.name, t.rows) else none
  let rom := src.tables.filterMap fun t =>
    if t.name.startsWith "<ROM:" then
      some (((t.name.drop 5).takeWhile Char.isDigit).toString.toNat!, t.rows) else none
  let entry ← IO.ofExcept (Schema.entryOf pkg circuits j)
  let st ← IO.ofExcept (WideIxa.stageOf pkg { circuits, rom, entry := some entry, allMaps := true, pow2 := true })
  let claims := st.claims
  let digest := claims.foldl (fun h c => c.foldl (fun h x => mixHash h (hash x.val)) (mixHash h 7)) (0 : UInt64)
  say s!"stageOf: entry {entry}, {claims.length} claims, digest {digest}, {(← IO.monoMsNow) - t0} ms"
  let shared := if sharedMaps then (Grouped.sharedTablesOf pkg).map (·.1) else []
  for T in shared do
    unless T.checkFast claims do
      throw (IO.userError "a shared map table row is not a map claim")
  let maps := if sharedMaps then shared.map Grouped.SharedTable.air
    else mapAirsArr claims (WideIxa.mapRows claims)
  let mapLabels := if sharedMaps then (List.range maps.length).map (s!"map_shared/{·}")
    else maps.map (fun a => s!"map/{a.circuit.fixedWidth - 1}")
  say s!"maps: {maps.length} tables ({if sharedMaps then "shared" else "selector"}), {(maps.map (·.rows)).sum} rows"
  -- `request = CALL :: idOf entry :: words`: the two constants are folded
  -- into the root message, the words are the root cells.
  let entryId : ZMod p := st.request[1]!
  let nRoot := st.request.length - 2
  let airs := st.units ++ maps ++ st.roms ++ [rootAir entryId nRoot]
  let labels := st.chips.map (·.1.name) ++ mapLabels ++
    st.roms.map (fun a => s!"rom/{a.circuit.width - 1}") ++ ["root"]
  let publics := nPublicInputs
  unless st.request.length ≥ 2 && st.request[0]! == (Bridge.CALL : ZMod p) &&
      entryId == (pkg.idOf entry : ZMod p) && nRoot == publics + nOutputs do
    throw (IO.userError s!"root message has {nRoot} cells, expected {publics} + {nOutputs}")
  -- the final pool
  let mut pool : Aiur.Plonk.Lower.Pool (ZMod p) := {}
  for a in airs do
    let rows := if AirIn.uniformB a then 1 else a.rows
    for r in [0:rows] do
      pool := (AirIn.lowerRowState a r pool).pool
  let P := pool
  let poolIdx : Std.HashMap Ref Nat := P.gates.zipIdx.foldl (fun m (g, i) => m.insert g.c i) {}
  say s!"pool: {P.gates.size} gates, {(← IO.monoMsNow) - t0} ms"
  let mut bad := 0
  if check then
    unless poolClosed P do bad := bad + 1
    for (a, name) in airs.zip labels do
      let rows := if AirIn.uniformB a then 1 else a.rows
      for r in [0:rows] do
        unless AirIn.rowCheck a r P (poolIdx[·]?) do
          bad := bad + 1; say s!"{name}: rowCheck rejects row {r}"; break
    say s!"stageOk: {if bad == 0 then "true" else "false"}, {(← IO.monoMsNow) - t0} ms"
  -- the layout, as `plonk_check_stage`
  let airsA := airs.toArray
  let mut frs : Array (Array Nat) := #[]
  let mut nlocs : Array Nat := #[]
  for a in airs do
    if AirIn.uniformB a then
      let s := AirIn.lowerRowState a 0 P
      frs := frs.push #[s.sum]; nlocs := nlocs.push s.nloc
    else
      let mut fs : Array Nat := #[]
      let mut nl := 0
      for r in [0:a.rows] do
        let s := AirIn.lowerRowState a r P
        fs := fs.push s.sum; nl := max nl s.nloc
      frs := frs.push fs; nlocs := nlocs.push nl
  let tR := airsA.size - 1
  let mut cellBases : Array Nat := #[]
  let mut cur := nRoot
  for h : t in [0:airsA.size] do
    let a := airsA[t]
    if t == tR then cellBases := cellBases.push 0
    else cellBases := cellBases.push cur; cur := cur + a.rows * a.circuit.width
  let poolBase := cur
  cur := poolBase + P.next
  let mut locStarts : Array Nat := #[]
  for h : t in [0:airsA.size] do
    locStarts := locStarts.push cur
    cur := cur + airsA[t].rows * nlocs[t]!
  let init := cur
  let spare := cur + 1
  let locBase (i : Nat × Nat) : Nat := locStarts[i.1]! + i.2 * nlocs[i.1]!
  let fr (i : Nat × Nat) : Nat := let fs := frs[i.1]!; if fs.size == 1 then fs[0]! else fs.getD i.2 Aiur.Plonk.Lower.sumIn
  let mut sums : Array (Array Nat) := #[]
  let mut s := init
  for h : t in [0:airsA.size] do
    let a := airsA[t]
    if frs[t]!.size == 1 then
      let f := frs[t]!.getD 0 Aiur.Plonk.Lower.sumIn
      sums := sums.push #[s]
      if a.rows > 0 && f != Aiur.Plonk.Lower.sumIn then s := locBase (t, a.rows - 1) + f / 4
    else
      let mut ss : Array Nat := #[]
      for r in [0:a.rows] do
        ss := ss.push s
        let f := fr (t, r)
        if f != Aiur.Plonk.Lower.sumIn then s := locBase (t, r) + f / 4
      sums := sums.push ss
  let last := s
  let sumIn (i : Nat × Nat) : Nat :=
    let ss := sums[i.1]!
    if frs[i.1]!.size == 1 then
      let f := frs[i.1]!.getD 0 Aiur.Plonk.Lower.sumIn
      if i.2 == 0 || f == Aiur.Plonk.Lower.sumIn then ss.getD 0 0 else locBase (i.1, i.2 - 1) + f / 4
    else ss.getD i.2 0
  let L : Layout := ⟨(fun t => cellBases[t]!), (fun t => (airsA.getD t (defaultAir (F := ZMod p))).circuit.width), poolBase, locBase, sumIn, spare⟩
  if check then
    let fOk := Layout.finalOk airs P fr
    let lOk := L.linkOkF airs fr init last
    say s!"finalOk {fOk}, linkOkF {lOk}"
    unless fOk && lOk do bad := bad + 1
  -- the `β` gadget
  let γw := L.poolWire Aiur.Plonk.Lower.gammaRef
  let βw := L.poolWire Aiur.Plonk.Lower.betaRef
  let (steps, nWires) := Beta.betaSteps p γw βw (spare + 1)
  let bOk := Beta.betaOk steps γw βw
  say s!"β gadget: {(Beta.gadgetGates steps).length} gates, betaOk {bOk}, wires {nWires}"
  unless bOk do bad := bad + 1
  if bad != 0 then
    say "checks failed; nothing written"
    return 1
  -- gates
  let mut co : Coeffs p := {}
  let mut pre : ByteArray := ByteArray.emptyWithCapacity (1 <<< 30)
  let mut post : ByteArray := ByteArray.emptyWithCapacity (1 <<< 30)
  let mut npre := 0
  let mut npost := 0
  let mut failed := 0
  let emitPost (co : Coeffs p) (post : ByteArray) (g : Gate (ZMod p)) : Coeffs p × ByteArray × Bool :=
    match convert co g.qL g.qR g.qO g.qM g.qC with
    | (co, some v) => (co, writeGate post g.a g.b g.c v, true)
    | (co, none) => (co, post, false)
  let bInit : Gate (ZMod p) := ⟨init, init, init, 1, 0, 0, 0, 0⟩
  let (co1, post1, ok1) := emitPost co post bInit
  co := co1; post := post1; npost := npost + 1; unless ok1 do failed := failed + 1
  for g in Beta.gadgetGates steps do
    let (co1, post1, ok1) := emitPost co post g
    co := co1; post := post1; npost := npost + 1; unless ok1 do failed := failed + 1
  for g in P.gates do
    let (co1, post1, ok1) := emitPost co post (g.inst L.poolWire)
    co := co1; post := post1; npost := npost + 1; unless ok1 do failed := failed + 1
  say s!"pool and gadget written, {(← IO.monoMsNow) - t0} ms"
  let mut commits : ByteArray := ByteArray.emptyWithCapacity (1 <<< 25)
  let mut ncommit := 0
  let mut msgColsTotal := 0
  for h : t in [0:airsA.size] do
    let a := airsA[t]
    let mc := msgCols a
    let lc := Aiur.Plonk.Lower.messageColumns (AirIn.table a 0)
    unless mc.length == lc.length && mc.all (lc.contains ·) do
      say s!"{labels[t]?.getD ""}: msgCols {mc} differs from the lowering's message columns {lc}"
      bad := bad + 1
    msgColsTotal := msgColsTotal + a.rows * mc.length
    let uniform := AirIn.uniformB a
    let mut convs : Array (Option Conv × Bool) := #[]
    let mut gates0 : Array (LGate (ZMod p)) := #[]
    if uniform then
      gates0 := (AirIn.lowerRowState a 0 P).gates
      for g in gates0 do
        let (co1, v) := convert co g.L g.R g.O g.M g.C
        co := co1; convs := convs.push (v, isPre g)
    for r in [0:a.rows] do
      let i := (t, r)
      for c in mc do
        commits := pushU32 commits (L.cellWire i c); ncommit := ncommit + 1
      let gs := if uniform then gates0 else (AirIn.lowerRowState a r P).gates
      for h : k in [0:gs.size] do
        let g := gs[k]
        let (v, pr) ← if uniform then pure convs[k]! else do
          let (co1, v) := convert co g.L g.R g.O g.M g.C
          co := co1
          pure (v, isPre g)
        match v with
        | none => failed := failed + 1
        | some v =>
            let wa := L.wireOf i g.a
            let wb := L.wireOf i g.b
            let wc := L.wireOf i g.c
            if pr then pre := writeGate pre wa wb wc v; npre := npre + 1
            else post := writeGate post wa wb wc v; npost := npost + 1
  let bLast : Gate (ZMod p) := ⟨last, last, last, 1, 0, 0, 0, 0⟩
  let (co1, post1, ok1) := emitPost co post bLast
  co := co1; post := post1; npost := npost + 1; unless ok1 do failed := failed + 1
  let nGates := npre + npost
  say s!"gates: {nGates} ({npre} pre, {npost} post), {co.vals.size} coefficients, {failed} without GGate form, commits {ncommit} (= Σ rows·|msgCols| {msgColsTotal}, msgCols = the lowering's message columns in every table: {bad == 0}), {(← IO.monoMsNow) - t0} ms"
  if failed != 0 || bad != 0 then
    say "some gates have no GGate form, or the message columns differ; nothing written"
    return 1
  -- hints
  let mut kind : ByteArray := ByteArray.mk (Array.replicate nWires 255)
  let mut hx : Array UInt32 := Array.replicate nWires 0
  let mut hy : Array UInt32 := Array.replicate nWires 0
  for x in [0:poolBase] do kind := kind.set! x 0
  kind := kind.set! γw 3
  -- bit wires of the gadget: preset, defined when first read
  let mut preset : ByteArray := ByteArray.mk (Array.replicate nWires 0)
  for stp in steps do
    if let .bits x bs _ _ := stp then
      for (b, k) in bs.zipIdx do
        preset := preset.set! b 1
        hx := hx.set! b x.toUInt32
        hy := hy.set! b (bs.length - 1 - k).toUInt32
  let mut multi := 0
  let mut free := 0
  let mut gi := 0
  for part in [pre, post] do
    let n := part.size / 26
    for q in [0:n] do
      let o := 26 * q
      let a := getU32 part o
      let b := getU32 part (o + 4)
      let c := getU32 part (o + 8)
      let sel := part[o + 12]!.toNat
      for x in [a, b, c] do
        if kind[x]! == 255 && preset[x]! == 1 then kind := kind.set! x 2
      let un := ([a, b, c].filter fun x => kind[x]! == 255).eraseDups
      match un with
      | [] => pure ()
      | [u] =>
          let lin := (a == u && sel &&& 1 != 0) || (b == u && sel &&& 2 != 0) || (c == u && sel &&& 4 != 0) ||
            (sel &&& 8 != 0 && ((a == u) != (b == u)))
          if lin then kind := kind.set! u 1; hx := hx.set! u gi.toUInt32
          else kind := kind.set! u 4; free := free + 1
      | us =>
          multi := multi + 1
          for u in us do kind := kind.set! u 4
      gi := gi + 1
  let mut unused := 0
  for x in [0:nWires] do
    if kind[x]! == 255 then kind := kind.set! x 4; unused := unused + 1
  say s!"hints: {multi} gates with several unsolved wires, {free} free wires, {unused} unused wires, {(← IO.monoMsNow) - t0} ms"
  -- the file
  let path : System.FilePath := args[2]!
  let h ← IO.FS.Handle.mk path .write
  let mut hdr : ByteArray := "ixscs001".toUTF8
  for v in [publics, nOutputs, nWires, nGates, npre, ncommit, γw, βw, co.vals.size, airsA.size] do
    hdr := pushU64 hdr v
  for k in [0:nOutputs] do hdr := pushU32 hdr (L.cellWire (tR, 0) (publics + k))
  h.write hdr
  let mut cb : ByteArray := ByteArray.emptyWithCapacity (32 * co.vals.size)
  for x in co.vals do cb := pushFr cb x
  h.write cb
  h.write pre
  h.write post
  h.write commits
  let mut wt : ByteArray := ByteArray.emptyWithCapacity (9 * nWires)
  for x in [0:nWires] do
    wt := pushU32 (pushU32 (wt.push kind[x]!) hx[x]!.toNat) hy[x]!.toNat
  h.write wt
  let mut tb : ByteArray := ByteArray.empty
  for h : t in [0:airsA.size] do
    let name := (labels[t]?.getD "").toUTF8
    tb := pushU64 (pushU8 (pushU8 tb (name.size % 256)) (name.size / 256) ++ name) cellBases[t]!
    tb := pushU32 (pushU32 tb airsA[t].rows) airsA[t].circuit.width
  h.write tb
  h.flush
  let size := hdr.size + cb.size + pre.size + post.size + commits.size + wt.size + tb.size
  say s!"wrote {path}: {size} bytes; root constants CALL {Bridge.CALL}, entry id {entryId.val}; publics {publics} (root cells 0..{publics - 1}), outputs {nOutputs}, wires {nWires}, gates {nGates}, commits {ncommit}, γ {γw}, β {βw}; SCS constraints with the commitment rows: {nGates + ncommit + 1}; {(← IO.monoMsNow) - t0} ms"
  return 0

def run (args : List String) : IO UInt32 := do
  let opts := args.drop 3
  for o in opts do
    unless o == "nocheck" || o == "selector-maps" || o == "--bn254" || o == "--bls12-381" do
      throw (IO.userError s!"unknown option {o}")
  if opts.contains "--bn254" && opts.contains "--bls12-381" then
    throw (IO.userError "cannot specify both --bn254 and --bls12-381")
  let check := !opts.contains "nocheck"
  let sharedMaps := !opts.contains "selector-maps"
  if opts.contains "--bls12-381" then
    runFor Aiur.Library.Field.BLS12381.modulus args check sharedMaps
  else
    runFor Aiur.Library.Field.BN254.modulus args check sharedMaps

end Aiur.Plonk.Export

def main (args : List String) : IO UInt32 := Aiur.Plonk.Export.run args
