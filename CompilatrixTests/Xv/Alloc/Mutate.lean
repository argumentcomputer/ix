import CompilatrixTests.Xv.Alloc.Support
import CompilatrixTests.Support.Rng

/-!
# Validator mutation (05 §12 item 4)

Each mutation plants one allocation bug in an accepted allocation. The
validator must reject the mutant; if it accepts one, differential execution
must show the mutant still runs like the Xv program (an equivalent mutant),
or the validator is unsound and the run fails.

| Class | Plants |
| --- | --- |
| `swap` | two operand locations of one instruction exchanged |
| `dropEdit` | an edit removed |
| `retarget` | an edit's destination or source changed to another register |
| `earlyAlias` | an early definition (a fused `setcc`) placed on a use's register |
| `reserved` | an operand or a move destination in `rsp`, `rbp` or `r15` |
| `acrossCall` | a value copied into a caller-saved register before a call and read from it after |
| `unknownSource` | a use's register overwritten from a slot nothing was stored to (gap 1) |
| `entryCert` | block 0's certificate claims a parameter in a register the convention does not use |
| `blockCert` | a block's certificate claims a live register in an extra location |
| `tie` | a tied definition moved off its use's location |
| `fixed` | a fixed operand moved off its register |
| `slotRange` | `numSlots` below a slot the allocation uses |
| `cellMove` | a register-to-cell edit turned into a cell-to-cell one |
| `convention` | two call arguments' locations exchanged |
-/

namespace CompilatrixTests.Xv.Alloc.Mutate

open Compilatrix Compilatrix.Lir Compilatrix.Xv CompilatrixTests.Lir CompilatrixTests.Xv CompilatrixTests.Support
open Compilatrix.Xv.Alloc (Output BlockOut Edit)

abbrev G := StateM Rng

def rand {α : Type} (m : RngM α) : G α := modifyGet fun g => m.run g

def pick {α : Type} [Inhabited α] (xs : List α) : G (Option α) := do
  if xs.isEmpty then return none
  return some (← rand (RngM.pick xs.toArray))

def setAt {α : Type} (xs : List α) (i : Nat) (f : α → α) : List α :=
  xs.zipIdx.map fun (x, j) => if j == i then f x else x

def classes : List String :=
  ["swap", "dropEdit", "retarget", "earlyAlias", "reserved", "acrossCall", "unknownSource", "entryCert",
    "blockCert", "tie", "fixed", "slotRange", "cellMove", "convention"]

/-- Every instruction site `(block, index, instruction, locations)`; the body
size is the terminator. -/
def sites (f : Func VReg) (o : Output) : List (Nat × Nat × List (Operand VReg) × List Loc) :=
  (f.blocks.toList.zip o.blocks).zipIdx.flatMap fun ((b, bo), l) =>
    let body := (b.body.toList.zip bo.locs).zipIdx.map fun ((inst, ls), i) => (l, i, inst.operands, ls)
    body ++ [(l, b.body.size, b.term.operands, bo.termLocs)]

def setLocs (o : Output) (l i : Nat) (nb : Nat) (ls : List Loc) : Output :=
  { o with blocks := setAt o.blocks l fun bo =>
      if i == nb then { bo with termLocs := ls } else { bo with locs := setAt bo.locs i fun _ => ls } }

def bodySize (f : Func VReg) (l : Nat) : Nat := (f.blocks[l]?.map (·.body.size)).getD 0

/-- Insert `e` as the last edit before position `i` of block `l`. -/
def insertEdit (o : Output) (l i : Nat) (e : Edit) : Output :=
  { o with blocks := setAt o.blocks l fun bo =>
      let before := bo.edits.filter (·.1 ≤ i)
      let after := bo.edits.filter (·.1 > i)
      { bo with edits := before ++ [(i, e)] ++ after } }

def regs : List X86.GPR := scratch

/-- Plant one mutation of class `c` in function `fi`'s allocation. -/
def mutate (c : String) (env : Xl.Env) (f : Func VReg) (o : Output) : G (Option Output) := do
  let ss := sites f o
  match c with
  | "swap" =>
      let cands := ss.filter fun (_, _, _, ls) => (dedup ls).length ≥ 2
      let some (l, i, _, ls) ← pick cands | return none
      let some j ← pick (List.range ls.length) | return none
      let some k ← pick ((List.range ls.length).filter fun k => ls[k]! != ls[j]!) | return none
      let ls' := (ls.zipIdx.map fun (x, n) => if n == j then ls[k]! else if n == k then ls[j]! else x)
      return some (setLocs o l i (bodySize f l) ls')
  | "dropEdit" =>
      let cands := o.blocks.zipIdx.flatMap fun (bo, l) => (List.range bo.edits.length).map (l, ·)
      let some (l, n) ← pick cands | return none
      return some { o with blocks := setAt o.blocks l fun bo =>
        { bo with edits := bo.edits.zipIdx.filterMap fun (e, m) => if m == n then none else some e } }
  | "retarget" =>
      let cands := o.blocks.zipIdx.flatMap fun (bo, l) => (List.range bo.edits.length).map (l, ·)
      let some (l, n) ← pick cands | return none
      let some r ← pick regs | return none
      let dst ← rand (RngM.chance 50)
      return some { o with blocks := setAt o.blocks l fun bo =>
        { bo with edits := setAt bo.edits n fun (i, e) => match e with
            | .move d s => (i, if dst then .move (.reg r) s else .move d (.reg r)) } }
  | "earlyAlias" =>
      let cands := ss.filter fun (_, _, ops, _) =>
        ops.any (fun op => op.kind == .define && op.pos == .early) && ops.any (·.kind == .use)
      let some (l, i, ops, ls) ← pick cands | return none
      let some e := (ops.zipIdx.find? fun (op, _) => op.kind == .define && op.pos == .early).map (·.2) | return none
      let uses := (ops.zipIdx.filter fun (op, _) => op.kind == .use).map (·.2)
      let some u ← pick uses | return none
      return some (setLocs o l i (bodySize f l) (setAt ls e fun _ => ls[u]!))
  | "reserved" =>
      let some r ← pick [X86.GPR.rsp, .rbp, .r15] | return none
      if ← rand (RngM.chance 50) then
        let cands := ss.filter fun (_, _, _, ls) => !ls.isEmpty
        let some (l, i, _, ls) ← pick cands | return none
        let some j ← pick (List.range ls.length) | return none
        return some (setLocs o l i (bodySize f l) (setAt ls j fun _ => .reg r))
      else
        let cands := o.blocks.zipIdx.flatMap fun (bo, l) => (List.range bo.edits.length).map (l, ·)
        let some (l, n) ← pick cands | return none
        return some { o with blocks := setAt o.blocks l fun bo =>
          { bo with edits := setAt bo.edits n fun (i, e) => match e with | .move _ s => (i, .move (.reg r) s) } }
  | "acrossCall" =>
      -- A call at (l, i), then a later use in the same block at a location that survives calls.
      let calls := ss.filter fun (l, i, _, _) =>
        match f.blocks[l]?.bind (·.body[i]?) with
        | some (.call ..) => true
        | _ => false
      let some (l, i, _, _) ← pick calls | return none
      let later := ss.filter fun (l', j, ops, ls) =>
        l' == l && j > i && (ops.zip ls).any fun (op, loc) =>
          op.kind == .use && match loc with
            | .reg r => !(env.clobbers 0).contains r || calleeSaved r
            | _ => true
      let some (_, j, ops, ls) ← pick later | return none
      let some k ← pick ((ops.zip ls).zipIdx.filterMap fun ((op, loc), k) =>
          if op.kind == .use && (match loc with | .reg r => calleeSaved r | _ => true) then some k else none)
        | return none
      let src := ls[k]!
      let o := insertEdit o l i (.move (.reg .r11) src)
      return some (setLocs o l j (bodySize f l) (setAt ls k fun _ => .reg .r11))
  | "unknownSource" =>
      let cands := ss.filter fun (_, _, ops, ls) =>
        (ops.zip ls).any fun (op, loc) => op.kind == .use && !loc.isCell
      let some (l, i, ops, ls) ← pick cands | return none
      let some loc ← pick ((ops.zip ls).filterMap fun (op, loc) =>
          if op.kind == .use && !loc.isCell then some loc else none) | return none
      let o := insertEdit o l i (.move loc (.slot o.numSlots))
      return some { o with numSlots := o.numSlots + 1 }
  | "entryCert" =>
      let some p := f.params.head? | return none
      let used := (Xv.Xl.paramLoc 0) :: (List.range f.params.length).map Xv.Xl.paramLoc
      let some r ← pick (regs.filter fun r => !used.contains (.reg r)) | return none
      return some { o with blocks := setAt o.blocks 0 fun bo => { bo with cert := (.reg r, [p]) :: bo.cert } }
  | "blockCert" =>
      let cands := (o.blocks.zipIdx.filter fun (bo, l) => l != 0 && !bo.cert.isEmpty).map (·.2)
      let some l ← pick cands | return none
      let bo := o.blocks[l]!
      let some (_, vs) ← pick bo.cert | return none
      let some v := vs.head? | return none
      let taken := bo.cert.map (·.1)
      let some r ← pick (regs.filter fun r => !taken.contains (.reg r)) | return none
      return some { o with blocks := setAt o.blocks l fun bo => { bo with cert := (.reg r, [v]) :: bo.cert } }
  | "tie" =>
      let cands := ss.filter fun (_, _, ops, _) => ops.any fun op => match op.con with | .reuse _ => true | _ => false
      let some (l, i, ops, ls) ← pick cands | return none
      let some j := (ops.zipIdx.find? fun (op, _) => match op.con with | .reuse _ => true | _ => false).map (·.2)
        | return none
      let some r ← pick (regs.filter fun r => ls[j]! != .reg r) | return none
      return some (setLocs o l i (bodySize f l) (setAt ls j fun _ => .reg r))
  | "fixed" =>
      let cands := ss.filter fun (_, _, ops, _) => ops.any fun op => match op.con with | .fixed _ => true | _ => false
      let some (l, i, ops, ls) ← pick cands | return none
      let some j ← pick ((ops.zipIdx.filter fun (op, _) => match op.con with | .fixed _ => true | _ => false).map (·.2))
        | return none
      let some r ← pick (regs.filter fun r => ls[j]! != .reg r) | return none
      return some (setLocs o l i (bodySize f l) (setAt ls j fun _ => .reg r))
  | "slotRange" =>
      if o.numSlots == 0 then return none
      return some { o with numSlots := o.numSlots - 1 }
  | "cellMove" =>
      let cands := o.blocks.zipIdx.flatMap fun (bo, l) =>
        (bo.edits.zipIdx.filter fun ((_, e), _) => match e with | .move d s => d.isCell && !s.isCell).map (l, ·.2)
      let some (l, n) ← pick cands | return none
      return some { o with numSlots := o.numSlots + 1, blocks := setAt o.blocks l fun bo =>
        { bo with edits := setAt bo.edits n fun (i, e) => match e with | .move d _ => (i, .move d (.slot o.numSlots)) } }
  | "convention" =>
      let calls := ss.filter fun (l, i, _, _) =>
        match f.blocks[l]?.bind (·.body[i]?) with
        | some (.call _ args _) => args.length ≥ 2
        | _ => false
      let some (l, i, _, ls) ← pick calls | return none
      let ls' := match ls with
        | a :: b :: rest => b :: a :: rest
        | _ => ls
      return some (setLocs o l i (bodySize f l) ls')
  | _ => return none
where
  calleeSaved (r : X86.GPR) : Bool := [X86.GPR.rbx, .r12, .r13, .r14].contains r

/-- Per class: mutants planted, rejected (by code), and accepted mutants
that differential execution showed equivalent. -/
structure Stats where
  planted : Std.HashMap String Nat := {}
  rejected : Std.HashMap String Nat := {}
  equivalent : Std.HashMap String Nat := {}
  codes : Std.HashMap String Nat := {}
  deriving Inhabited

def bump (m : Std.HashMap String Nat) (k : String) (n : Nat := 1) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + n)

def Stats.add (a b : Stats) : Stats :=
  let merge (x y : Std.HashMap String Nat) := y.fold (init := x) fun acc k v => bump acc k v
  { planted := merge a.planted b.planted, rejected := merge a.rejected b.rejected
    equivalent := merge a.equivalent b.equivalent, codes := merge a.codes b.codes }

/-- Plant each class once in allocation `outs` of `q` (a random function
and site), check the validator rejects it or the mutant is equivalent. -/
def run (q : VProgram) (outs : List Output) (env : Xl.Env) (args : List Word) (seed : UInt64) :
    Except String Stats := do
  let mut stats : Stats := {}
  let mut rng := Rng.ofSeed (seed ^^^ 0x6d757461)
  for c in classes do
    let (fi, rng') := (RngM.below outs.length).run rng
    rng := rng'
    let some f := q.funcs[fi]? | continue
    let some o := outs[fi]? | continue
    let (m, rng') := (mutate c env f o).run rng
    rng := rng'
    let some o' := m | continue
    if o' == o then continue
    stats := { stats with planted := bump stats.planted c }
    let outs' := setAt outs fi fun _ => o'
    match Validate.program env q outs' with
    | .error e =>
        stats := { stats with rejected := bump stats.rejected c, codes := bump stats.codes s!"{c}:{e.code.name}" }
    | .ok () =>
        if equivalent q outs' env args seed then
          stats := { stats with equivalent := bump stats.equivalent c }
        else
          throw s!"validator accepted a {c} mutant of function {fi} that runs differently"
  return stats

end CompilatrixTests.Xv.Alloc.Mutate
