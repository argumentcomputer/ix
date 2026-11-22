import IxCC.Xv.Operands
import IxCC.Lir.Graph

/-!
# Well-formed Xv

Decidable conditions on Xv programs, checked on selection's output
and assumed by the allocator. Validator soundness does not rely on them.

1. **Shape**, as for Lir: `main` and every callee exist with matching
   arities; the entry block has no parameters and no predecessors; edges
   reach existing blocks with one argument per parameter; no critical
   edges; every block is reachable.
2. **Rows.** An `op` names a row of `Op.rows` that is linear and has no
   stack effect (`rsp` is never an operand), its `defs` and `args` bind the
   row's slots and implicit registers, each argument has a kind its slot
   accepts (register, memory, or an immediate in the slot's canonical
   form), and no written slot is an 8- or 16-bit register destination
   without a tie (such a write keeps the register's other bits, which are
   not an operand). A `jcc` producer obeys the same. A `fused` pair is a
   flags-only producer and a flag consumer, whose narrow destination
   (`setcc`) is allowed: its expansion zeroes it first.
3. **Flags** (`Inst.flagsOk`, `Term.flagsOk`): a lone row reads no flags; in
   a fused pair or a `jcc`, the producer reads none and sets every flag the
   consumer reads (`X86.FusedOk`); a fused producer writes nothing but
   flags (`Op.flagsOnly`) and its consumer is a flag consumer.
4. **Aliasing basics:** an instruction's definitions are distinct and none
   is also one of its uses.
5. **SSA:** each register is defined once and each definition dominates its
   uses, in Lir's order within a block (parameters; each instruction's uses,
   then its definitions; the terminator's uses, its definitions, then the
   edge arguments).
6. **Context stores:** no `Base.ctx` store may reach `entrySp` or
   `stackLimit` (`ctx − 64`, `ctx − 56`), as at Lir. -/

namespace IxCC.Xv

open IxCC.Lir (VReg Label FunId)

/-! ## Flags -/

def Inst.flagsOk {ρ : Type} : Inst ρ → Bool
  | .op o .. => (X86.desc o).flagsIn.isEmpty
  | .fused p _ c .. => (X86.desc p).flagsIn.isEmpty && !(X86.desc c).flagsIn.isEmpty && X86.FusedOk p c
  | _ => true

def Term.flagsOk {ρ : Type} : Term ρ → Bool
  | .jcc p _ _ c _ _ => (X86.desc p).flagsIn.isEmpty && X86.FusedOk p (X86.Op.jccRel32 c)
  | _ => true

/-! ## Rows -/

/-- A row that may appear as an Xv `op` or producer: listed, linear (not
control and not a flag consumer), with no stack traffic. -/
def rowOk (o : X86.Op) : Bool :=
  X86.Op.rows.contains o && o.linear && (X86.desc o).stack == .none

/-- Each operand has a kind its slot accepts; implicit operands are
registers by construction. -/
def Bound.kindOk {ρ : Type} : Bound ρ → Bool
  | .input s (.r _) => s.kinds.contains .reg
  | .input s (.m _) => s.kinds.contains .mem
  | .input s (.i w) => s.kinds.any (·.accepts (.imm w))
  | .output s _ | .tied s _ _ => s.kinds.contains .reg
  | .memory s _ => s.kinds.contains .mem
  | .fixedUse .. | .fixedDef .. | .fixedTied .. => true

def distinct : List VReg → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

/-- A row's operands bind and fit its slots (condition 2); a narrow
write-only register destination only where `narrowOk` (a fused consumer,
whose expansion zeroes it first). -/
def rowArgsOk (o : X86.Op) (defs : List VReg) (args : List (XArg VReg)) (narrowOk : Bool := false) : Bool :=
  match bindRow o defs args with
  | some bs => bs.all fun b => b.kindOk && (narrowOk || !b.narrowOutput)
  | none => false

def Bound.protectedStore {ρ : Type} : Bound ρ → Bool
  | .memory s m => m.hitsProtectedCtx s.width.bytes
  | _ => false

def rowStoresOk (o : X86.Op) (defs : List VReg) (args : List (XArg VReg)) : Bool :=
  match bindRow o defs args with
  | some bs => !bs.any Bound.protectedStore
  | none => true

def Inst.check (i : Inst VReg) : Except String Unit := do
  unless i.flagsOk do throw "flags: a lone row reads flags, or a fused producer does not set them"
  unless distinct i.defs do throw "definitions are not distinct"
  if i.defs.any i.uses.contains then throw "a definition is also a use"
  match i with
  | .op o defs args =>
      unless rowOk o do throw s!"row {repr o} is not a listed linear row"
      unless rowArgsOk o defs args do throw s!"operands do not fit row {repr o}"
      unless rowStoresOk o defs args do throw "store may reach the context's entrySp or stackLimit cell"
  | .fused p pargs c defs cargs =>
      unless rowOk p && p.flagsOnly && X86.Op.rows.contains c && c.consumer do
        throw s!"fused rows {repr p}, {repr c} are not a flags-only producer and a flag consumer"
      unless rowArgsOk p [] pargs do throw s!"operands do not fit producer {repr p}"
      unless rowArgsOk c defs cargs (narrowOk := true) do throw s!"operands do not fit consumer {repr c}"
      unless rowStoresOk c defs cargs do throw "store may reach the context's entrySp or stackLimit cell"
  | .move .. | .zero _ | .call .. => pure ()

def Term.check (t : Term VReg) : Except String Unit := do
  unless t.flagsOk do throw "flags: the producer does not set the flags the branch reads"
  match t with
  | .jcc p pargs defs _ _ _ =>
      unless distinct defs do throw "definitions are not distinct"
      if defs.any t.uses.contains then throw "a definition is also a use"
      unless rowOk p do throw s!"producer {repr p} is not a listed linear row"
      unless rowArgsOk p defs pargs do throw s!"operands do not fit producer {repr p}"
      unless rowStoresOk p defs pargs do throw "store may reach the context's entrySp or stackLimit cell"
  | _ => pure ()

/-! ## Functions -/

namespace Func

/-- The control-flow graph as a Lir function (edges only), for Lir's graph
analyses. -/
def skeleton {ρ : Type} (f : Func ρ) : Lir.Func :=
  { params := [], results := 0
    blocks := f.blocks.map fun b =>
      { term := match b.term.succs with
          | [t] => .jump ⟨t, []⟩
          | [t, e] => .br .eq .w64 (.imm 0) (.imm 0) ⟨t, []⟩ ⟨e, []⟩
          | _ => .trap } }

private def site (fi : FunId) (f : Func VReg) (b : Label) : String :=
  s!"function {fi}{if f.name.isEmpty then "" else s!" ({f.name})"} block {b}"

def checkShape (p : VProgram) (fi : FunId) (f : Func VReg) : Except String Unit := do
  let n := f.blocks.size
  if n == 0 then throw s!"function {fi} has no blocks"
  unless f.blocks[0]!.params.isEmpty do throw s!"{site fi f 0}: the entry block has parameters"
  let preds := f.skeleton.predCounts
  for h : b in [:n] do
    let block := f.blocks[b]
    let edges := block.term.edges
    for e in edges do
      match f.blocks[e.target]? with
      | none => throw s!"{site fi f b}: edge to missing block {e.target}"
      | some target =>
          if e.target == 0 then throw s!"{site fi f b}: edge to the entry block"
          unless e.args.length == target.params.length do
            throw s!"{site fi f b}: edge to block {e.target} passes {e.args.length} arguments for {target.params.length} parameters"
          if edges.length ≥ 2 && preds[e.target]! ≥ 2 then
            throw s!"{site fi f b}: critical edge to block {e.target}"
    for h : i in [:block.body.size] do
      let inst := block.body[i]
      match inst.check with
      | .error e => throw s!"{site fi f b} instruction {i}: {e}"
      | .ok () => pure ()
      if let .call g args rets := inst then
        match p.funcs[g]? with
        | none => throw s!"{site fi f b} instruction {i}: call to missing function {g}"
        | some callee =>
            unless args.length == callee.params.length do
              throw s!"{site fi f b} instruction {i}: call to {g} passes {args.length} arguments for {callee.params.length}"
            unless rets.length == callee.results do
              throw s!"{site fi f b} instruction {i}: call to {g} binds {rets.length} results of {callee.results}"
    match block.term.check with
    | .error e => throw s!"{site fi f b} terminator: {e}"
    | .ok () => pure ()
    match block.term with
    | .ret vs =>
        unless vs.length == f.results do throw s!"{site fi f b}: returns {vs.length} values of {f.results}"
    | .tail g args =>
        match p.funcs[g]? with
        | none => throw s!"{site fi f b}: tail call to missing function {g}"
        | some callee =>
            unless args.length == callee.params.length do
              throw s!"{site fi f b}: tail call to {g} passes {args.length} arguments for {callee.params.length}"
            unless callee.results == f.results do
              throw s!"{site fi f b}: tail call to {g} returns {callee.results} values of {f.results}"
    | _ => pure ()

def checkSsa (fi : FunId) (f : Func VReg) : Except String Unit := do
  let n := f.blocks.size
  let g := f.skeleton
  unless g.rpo.size == n do
    let reachable := g.rpoIndex
    throw s!"function {fi}: unreachable blocks {(List.range n).filter fun b => (reachable[b]!).isNone}"
  let mut defs : Std.HashMap VReg (Label × Nat) := {}
  let define (defs : Std.HashMap VReg (Label × Nat)) (x : VReg) (b pos : Nat) :
      Except String (Std.HashMap VReg (Label × Nat)) :=
    if defs.contains x then throw s!"{site fi f b}: v{x} is defined twice" else pure (defs.insert x (b, pos))
  for x in f.params do defs ← define defs x 0 0
  for h : b in [:n] do
    let block := f.blocks[b]
    for x in block.params do defs ← define defs x b 0
    for h : i in [:block.body.size] do
      for x in block.body[i].defs do defs ← define defs x b (2 * i + 2)
    for x in block.term.defs do defs ← define defs x b (2 * block.body.size + 2)
  let doms := g.dominators
  let check (b pos : Nat) (x : VReg) : Except String Unit :=
    match defs[x]? with
    | none => throw s!"{site fi f b}: v{x} is used but never defined"
    | some (db, dpos) =>
        if (db == b && dpos < pos) || (db != b && Lir.Func.dominates doms db b) then pure ()
        else throw s!"{site fi f b}: the definition of v{x} (block {db}) does not dominate its use"
  for h : b in [:n] do
    let block := f.blocks[b]
    for h : i in [:block.body.size] do
      for x in block.body[i].uses do check b (2 * i + 1) x
    for x in block.term.uses do check b (2 * block.body.size + 1) x
    for x in block.term.edgeUses do check b (2 * block.body.size + 3) x

end Func

def Program.check (p : VProgram) : Except String Unit := do
  unless p.main < p.funcs.size do throw s!"main function {p.main} is missing"
  for h : fi in [:p.funcs.size] do
    p.funcs[fi].checkShape p fi
    p.funcs[fi].checkSsa fi

def Program.wellFormed (p : VProgram) : Bool := p.check.toBool

/-- Well-formed Xv (decidable). -/
def WellFormed (p : VProgram) : Prop := p.wellFormed = true

instance (p : VProgram) : Decidable (WellFormed p) := inferInstanceAs (Decidable (_ = true))

end IxCC.Xv
