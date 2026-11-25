import IxCC.Lir.Opt.Unroll
import IxCC.Lir.WellFormed

/-!
# Directly-verified diamond if-conversion (`Lir.Opt.IfConv`)

Converts unpredictable diamond branches `b → (armT, armF) → join` (with pure total
arm bodies and zero or more `brOvf → .fail res` overflow guards, e.g. `collatz`'s
50/50 even/odd step!) into branchless `select` (`cmov`) plus a single predicated
overflow guard.

Arm-defined registers are shifted above `off = nextFreshVReg F` so speculative
execution of both arms never clobbers any register `< off` and creates zero
critical edges.

Soundness is proved directly via `Sem.Forward` in `IxCC.Lir.Proof.Opt.IfConv`
(`ifConvDiamondSite_sim : Sem.Sim Eq id`).
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func Program Word)

/-! ## Extracting straight-line / `brOvf`-guarded diamond arms -/

/-- One block in a linear diamond arm (either intermediate `brOvf` guard or final `.jump join`). -/
structure ArmStep where
  label : Label
  body : List Stmt
  ovf? : Option (Ovf × VReg × Arg × Arg × Sem.Resource)
  deriving DecidableEq, Repr, Inhabited

/-- A validated linear arm from entry label to `join` with final jump arguments `joinArgs`. -/
structure DiamondArm where
  steps : List ArmStep
  join : Label
  joinArgs : List Arg
  deriving DecidableEq, Repr, Inhabited

/-- Collect all labels visited by an arm. -/
def DiamondArm.labels (arm : DiamondArm) : List Label :=
  arm.steps.map (·.label)

/-- Collect all virtual registers defined by an arm's statements and `brOvf` results. -/
def DiamondArm.defs (arm : DiamondArm) : Src.NatSet :=
  arm.steps.foldl (init := .leaf) fun acc st =>
    let acc1 := st.body.foldl (fun s stmt => stmt.defs.foldl (fun a x => a.insert x) s) acc
    match st.ovf? with
    | some (_, x, _, _, _) => acc1.insert x
    | none => acc1

/-- Whether an arm contains any `brOvf` guards, returning the common `.fail` resource if uniform. -/
def DiamondArm.failRes? (arm : DiamondArm) : Option Sem.Resource :=
  arm.steps.findSome? fun st => st.ovf?.map fun (_, _, _, _, r) => r

/-- Check whether every statement in an arm is pure and total (never traps, reads/writes memory,
or calls), and every register in `armDefs` is defined before use inside the arm. -/
def checkArmPure (arm : DiamondArm) (armDefs : Src.NatSet) : Bool :=
  let rec go (av : Src.NatSet) : List ArmStep → Bool
    | [] => arm.joinArgs.all fun a => a.uses.all fun x => !armDefs.contains x || av.contains x
    | st :: rest =>
        if !st.body.all isHoistableStmt then false
        else match checkStmtsAvail armDefs av st.body with
        | none => false
        | some av1 =>
            match st.ovf? with
            | none => go av1 rest
            | some (_, x, oa, ob, _) =>
                if (oa.uses ++ ob.uses).all (fun u => !armDefs.contains u || av1.contains u) then
                  go (av1.insert x) rest
                else false
  go .leaf arm.steps

/-- Untrusted extractor: follow a chain of 0-param blocks starting at `start` (up to `fuel` steps)
where every intermediate block ends in `.brOvf o x a b okEdge ovfEdge` with `okEdge.args = []`
and `ovfEdge` an immediate `.fail res` edge, terminating at `.jump ⟨join, joinArgs⟩`. -/
def extractDiamondArm (F : Func) (origB minLbl : Label) : Nat → Label → Option DiamondArm
  | 0, _ => none
  | fuel + 1, l =>
      if l ≤ minLbl then none
      else match F.blocks[l]? with
      | none => none
      | some blk =>
          if !blk.params.isEmpty then none
          else match blk.term with
          | .jump e =>
              if e.target ≤ origB || l < e.target then
                some { steps := [{ label := l, body := blk.body.toList, ovf? := none }]
                       join := e.target
                       joinArgs := e.args }
              else none
          | .brOvf o x a b okEdge ovfEdge =>
              if !okEdge.args.isEmpty then none
              else match failEdgeResource? F ovfEdge with
              | none => none
              | some res =>
                  match extractDiamondArm F origB l fuel okEdge.target with
                  | none => none
                  | some tail =>
                      some { tail with
                        steps := { label := l, body := blk.body.toList, ovf? := some (o, x, a, b, res) } :: tail.steps }
          | _ => none

/-- Verify that an extracted `DiamondArm` faithfully matches `F`'s actual blocks starting at `start`,
with strictly increasing labels and clock-compatible exit (`join ≤ b ∨ last < join`), and uniform `.fail` resource `commonRes?`. -/
def verifyArmMatches (F : Func) (b start join : Label) (commonRes? : Option Sem.Resource)
    (arm : DiamondArm) : Bool :=
  let rec go (cur : Label) : List ArmStep → Bool
    | [] => false
    | [st] =>
        st.label == cur &&
        decide (join ≤ b || cur < join) &&
        st.ovf?.isNone &&
        match F.blocks[cur]? with
        | none => false
        | some blk =>
            blk.params.isEmpty &&
            blk.body.toList == st.body &&
            blk.term == .jump { target := join, args := arm.joinArgs }
    | st :: next :: rest =>
        st.label == cur &&
        decide (cur < next.label) &&
        match st.ovf?, F.blocks[cur]? with
        | some (o, x, oa, ob, res), some blk =>
            (match commonRes? with | some r0 => res == r0 | none => false) &&
            blk.params.isEmpty &&
            blk.body.toList == st.body &&
            match blk.term with
            | .brOvf o' x' oa' ob' okEdge ovfEdge =>
                o' == o && x' == x && oa' == oa && ob' == ob &&
                okEdge == { target := next.label, args := [] } &&
                failEdgeResource? F ovfEdge == some res &&
                go next.label (next :: rest)
            | _ => false
        | _, _ => false
  arm.join == join && go start arm.steps

/-- Decidable soundness check for diamond if-conversion at block `b` with arms `armT, armF`. -/
def ifConvDiamondOk (F : Func) (b : Label) (armT armF : DiamondArm) (off : VReg) : Bool :=
  match F.blocks[b]? with
  | none => false
  | some blk =>
      match blk.term with
      | .br _ _ a bArg eT eF =>
          let join := armT.join
          let n := F.blocks.size
          let commonRes? := armT.failRes?.orElse fun _ => armF.failRes?
          let armTDefs := armT.defs
          let armFDefs := armF.defs
          let tLbls := Src.NatSet.ofList armT.labels
          let fLbls := Src.NatSet.ofList armF.labels
          let bNoOverlap := !tLbls.contains b && !fLbls.contains b &&
            !tLbls.contains join && !fLbls.contains join &&
            armT.labels.all (fun l => !fLbls.contains l)
          let guaranteedList : List VReg :=
            F.params ++ blk.params ++
            blk.body.toList.flatMap (fun s => s.uses ++ s.defs) ++
            a.uses ++ bArg.uses
          let guaranteedDef : Src.NatSet := Src.NatSet.ofList guaranteedList
          let guarDisjoint : Bool :=
            guaranteedList.all fun x => !armTDefs.contains x && !armFDefs.contains x
          let armOuterUsesOk (arm : DiamondArm) (armDefs : Src.NatSet) : Bool :=
            arm.steps.all fun st =>
              st.body.all (fun s => s.uses.all fun x => armDefs.contains x || guaranteedDef.contains x) &&
              match st.ovf? with
              | none => true
              | some (_, _, oa, ob, _) =>
                  (oa.uses ++ ob.uses).all fun x => armDefs.contains x || guaranteedDef.contains x
          let diffJoinArgsOk : Bool :=
            (armT.joinArgs.zip armF.joinArgs).all fun (at_, af_) =>
              let at' := loopMapArg armTDefs off 1 at_
              let af' := loopMapArg armFDefs off 2 af_
              if at' == af' then true
              else
                at_.uses.all (fun x => armTDefs.contains x || guaranteedDef.contains x) &&
                af_.uses.all (fun x => armFDefs.contains x || guaranteedDef.contains x)
          (b != 0 || blk.params.isEmpty) &&
          decide (b < eT.target) &&
          decide (b < eF.target) &&
          decide (join < n) &&
          eT.args.isEmpty &&
          eF.args.isEmpty &&
          armT.join == armF.join &&
          armT.joinArgs.length == armF.joinArgs.length &&
          (match F.blocks[join]? with
           | some jBlk => armT.joinArgs.length == jBlk.params.length
           | none => false) &&
          bNoOverlap &&
          guarDisjoint &&
          funcRegsLt F off &&
          verifyArmMatches F b eT.target join commonRes? armT &&
          verifyArmMatches F b eF.target join commonRes? armF &&
          checkArmPure armT armTDefs &&
          checkArmPure armF armFDefs &&
          armOuterUsesOk armT armTDefs &&
          armOuterUsesOk armF armFDefs &&
          diffJoinArgsOk &&
          -- No block outside `armT` (resp. `armF`) uses `armTDefs` (resp. `armFDefs`),
          -- and no block other than `b` enters `armT` or `armF` from outside
          (List.range n).all fun u =>
            match F.blocks[u]? with
            | none => false
            | some uBlk =>
                let uUses := uBlk.body.toList.flatMap (·.uses) ++ uBlk.term.uses ++ uBlk.term.edgeUses
                let noOutsideEnter :=
                  if u == b then true
                  else uBlk.term.edges.all fun e =>
                    (tLbls.contains u || !tLbls.contains e.target) &&
                    (fLbls.contains u || !fLbls.contains e.target)
                noOutsideEnter &&
                (tLbls.contains u || uUses.all fun x => !armTDefs.contains x) &&
                (fLbls.contains u || uUses.all fun x => !armFDefs.contains x)
      | _ => false

/-! ## Emitting speculative arm statements + branchless `select` + predicated guard -/

/-- Emit a pure total limb operation computing `(x, flag)` where `flag ≠ 0 ↔ (o.eval a b).2 = true`. -/
def emitOvfLimb (o : Ovf) (x flag : VReg) (a b : Arg) : Stmt :=
  match o with
  | .addC => .limb x flag (.addCarry64 a b (.imm 0))
  | .subB => .limb x flag (.subBorrow64 a b (.imm 0))
  | .mulOvf => .limb x flag (.mulWide64 a b)

/-- Emit all statements of `arm` shifted by `shiftMul * off`, accumulating the bitwise-OR of all
`brOvf` overflow flags into a single `Arg` (`.imm 0` if the arm has no `brOvf` guards). -/
def emitSpeculativeArm (armDefs : Src.NatSet) (off shiftMul : Nat) (arm : DiamondArm)
    (flagBase : VReg) : List Stmt × Arg × VReg :=
  arm.steps.foldl (init := ([], Arg.imm 0, flagBase)) fun (acc, curFlag, nextReg) st =>
    let bodyShifted := st.body.map (loopMapStmt armDefs off shiftMul)
    match st.ovf? with
    | none => (acc ++ bodyShifted, curFlag, nextReg)
    | some (o, x, oa, ob, _) =>
        let x' := loopMapReg armDefs off shiftMul x
        let oa' := loopMapArg armDefs off shiftMul oa
        let ob' := loopMapArg armDefs off shiftMul ob
        let fReg := nextReg
        let limbSt := emitOvfLimb o x' fReg oa' ob'
        match curFlag with
        | .imm 0 =>
            (acc ++ bodyShifted ++ [limbSt], .v fReg, nextReg + 1)
        | _ =>
            let orReg := nextReg + 1
            let orSt := Stmt.assign orReg (.bin .or .w64 curFlag (.v fReg))
            (acc ++ bodyShifted ++ [limbSt, orSt], .v orReg, nextReg + 2)

/-- Build the if-converted function for validated diamond `(b, armT, armF)`. -/
def buildIfConvFunc (F : Func) (b : Label) (armT armF : DiamondArm) (off : VReg) : Func :=
  let blk := F.blocks[b]!
  match blk.term with
  | .br c w a bArg _ _ =>
      let join := armT.join
      let armTDefs := armT.defs
      let armFDefs := armF.defs
      -- Shift armT defs by `1 * off`, armF defs by `2 * off`, and allocate flags/selects at `3 * off + ...`
      let (stmtsT, flagT, fr1) := emitSpeculativeArm armTDefs off 1 armT (3 * off)
      let (stmtsF, flagF, fr2) := emitSpeculativeArm armFDefs off 2 armF fr1
      let argsT := armT.joinArgs.map (loopMapArg armTDefs off 1)
      let argsF := armF.joinArgs.map (loopMapArg armFDefs off 2)
      let (selStmts, selArgsRev, fr3) : List Stmt × List Arg × VReg :=
        (argsT.zip argsF).foldl (init := ([], [], fr2)) fun (ss, out, fr) (at_, af_) =>
          if at_ == af_ then (ss, at_ :: out, fr)
          else (ss ++ [.assign fr (.select c w a bArg at_ af_)], .v fr :: out, fr + 1)
      let selArgs := selArgsRev.reverse
      let commonRes? := armT.failRes?.orElse fun _ => armF.failRes?
      match commonRes? with
      | none =>
          -- Shape 1: pure total diamond — zero extra blocks needed!
          let blk' : Block :=
            { blk with
              body := (blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts).toArray
              term := .jump { target := join, args := selArgs } }
          { F with blocks := F.blocks.set! b blk' }
      | some res =>
          -- Shape 2: predicated `.fail res` guard + 0-stmt forward hop to `join + 1`!
          let predReg := fr3
          let predStmt := Stmt.assign predReg (.select c w a bArg flagT flagF)
          let cut := b + 1
          let n := F.blocks.size
          let hopLbl := cut
          let failLbl := n + 1
          let blk' : Block :=
            { blk with
              body := (blk.body.toList ++ stmtsT ++ stmtsF ++ selStmts ++ [predStmt]).toArray
              term := .br .ne .w64 (.v predReg) (.imm 0)
                { target := failLbl, args := [] }
                { target := hopLbl, args := [] } }
          let remapLbl (l : Label) : Label := if l < cut then l else l + 1
          let hopBlk : Block :=
            { params := []
              body := #[]
              term := .jump { target := remapLbl join, args := selArgs }
              cold := blk.cold }
          let failBlk : Block := { params := [], body := #[], term := .fail res, cold := true }
          let remapBlk (blk0 : Block) : Block :=
            { blk0 with term := blk0.term.setEdges (blk0.term.edges.map fun (e : Edge) => { e with target := remapLbl e.target }) }
          let before := (List.range b).map fun i => remapBlk F.blocks[i]!
          let after := (List.range (n - cut)).map fun d => remapBlk F.blocks[cut + d]!
          { F with blocks := (before ++ [blk', hopBlk] ++ after ++ [failBlk]).toArray }
  | _ => F

/-- Apply diamond if-conversion at `(fi, b)` if all soundness preconditions hold. -/
def ifConvDiamondSite (p : Program) (fi : FunId) (b : Label) : Option Program :=
  match p.funcs[fi]? with
  | none => none
  | some F =>
      match F.blocks[b]? with
      | none => none
      | some blk =>
          match blk.term with
          | .br _ _ _ _ eT eF =>
              match extractDiamondArm F b b 4 eT.target, extractDiamondArm F b b 4 eF.target with
              | some armT, some armF =>
                  let off := nextFreshVReg F
                  if ifConvDiamondOk F b armT armF off then
                    let F' := buildIfConvFunc F b armT armF off
                    some { p with funcs := p.funcs.set! fi F' }
                  else none
              | _, _ => none
          | _ => none

/-- Checked single-site diamond if-conversion preserving `WellFormed`. -/
def ifConvDiamondSiteChecked (p : Program) (fi : FunId) (b : Label) : Program × Bool :=
  match ifConvDiamondSite p fi b with
  | none => (p, false)
  | some q => if !p.wellFormed || q.wellFormed then (q, true) else (p, false)

/-! ## Heuristic site picker (hot small diamonds inside loops) -/

/-- Find a small pure/brOvf-guarded diamond branch inside a loop of `F` suitable for
branchless if-conversion (e.g. `collatz` even/odd step). -/
def findIfConvDiamondSite (F : Func) : Option Label :=
  let n := F.blocks.size
  if n < 4 || n > 100 then none
  else
    let inLoop : Src.NatSet := (List.range n).foldl (init := .leaf) fun acc h =>
      match classifyLoopExits F h with
      | some (nodes, _, _) => nodes.foldl (fun s x => Src.NatSet.insert s x) acc
      | none => acc
    (List.range n).findSome? fun b =>
      if !inLoop.contains b then none
      else match F.blocks[b]? with
      | none => none
      | some blk =>
          if blk.cold then none
          else match blk.term with
          | .br _ _ _ _ eT eF =>
              match extractDiamondArm F b b 4 eT.target, extractDiamondArm F b b 4 eF.target with
              | some armT, some armF =>
                  let stT := armT.steps.foldl (fun acc s => acc + s.body.length) 0
                  let stF := armF.steps.foldl (fun acc s => acc + s.body.length) 0
                  -- Keep diamonds small and non-trivial (at least 1 stmt or differing args, ≤ 10 stmts total)
                  if stT + stF ≤ 10 && armT.steps.length ≤ 3 && armF.steps.length ≤ 3 &&
                     !armT.joinArgs.isEmpty && armT.joinArgs != armF.joinArgs then
                    let off := nextFreshVReg F
                    if ifConvDiamondOk F b armT armF off then some b else none
                  else none
              | _, _ => none
          | _ => none

end IxCC.Lir.Opt
