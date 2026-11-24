import IxCC.Lir.Opt.Sym
import IxCC.Lir.Opt.Licm
import IxCC.Lir.Graph
import IxCC.Lir.WellFormed
import IxCC.Src.NatMap

/-!
# Dominator-tree GVN, algebraic simplification, division strength reduction,
memory forwarding/CSE, intra-block DSE, and DCE (untrusted optimizer)

Implements the core intra-procedural SSA optimization pipeline on `Lir.Func`:
1. **Dominator-tree preorder GVN / CSE + copy & constant propagation**
2. **Algebraic simplification** (width-safe across `w8`–`w64`, constant reassociation,
   `addr` displacement folding, `select`/`test` simplification)
3. **Constant unsigned division / modulo strength reduction** (power-of-2 shifts/masks
   at all widths + Granlund–Montgomery magic multipliers for 64-bit & 32-bit constants)
4. **Dominating branch fact & unsigned interval propagation** (folding redundant
   `br` and non-overflowing `brOvf` terminators)
5. **Intra-segment store-to-load forwarding & load CSE** across byte-disjoint stores
6. **Intra-block dead store elimination (DSE)** matching `SymMem.write`
7. **Fixpoint dead code elimination (DCE)**
8. **Order-preserving unreachable block pruning** (preserving `WellFormed` & clocks)

All passes are **untrusted** and total (no `partial`); every output is verified by
`Lir.Opt.check` + `Lir.Program.wellFormed`.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func Word sext dispWord fitsI32)

/-! ## Helpers -/

/-- Build dominator-tree child lists from `F.idoms`. -/
def domTreeChildren (F : Func) : Array (List Label) :=
  let n := F.blocks.size
  let idoms := F.idoms
  let acc := (List.range n).foldl (init := Array.replicate n ([] : List Label)) fun ch b =>
    match idoms[b]? with
    | some (some p) => if p < ch.size then ch.modify p (b :: ·) else ch
    | _ => ch
  acc.map List.reverse

/-- Signed 64-bit value of an immediate word, if it fits in signed 32-bit. -/
private def immAsSmallInt? (k : Word) : Option Int :=
  let i : Int := k.toInt64.toInt
  if fitsI32 i then some i else none

/-- Map `Ovf` to its corresponding wrapping 64-bit `BinOp`. -/
private def ovfBinOp : Ovf → BinOp
  | .addC => .add
  | .subB => .sub
  | .mulOvf => .mul

/-- Emit 64-bit Granlund–Montgomery magic-multiplier quotient sequence for `a / d` into `dst`. -/
private def emitMagicU64 (dst : VReg) (a : Arg) (mc : Magic64) (fresh : VReg) :
    List Stmt × VReg :=
  match mc with
  | .simple m s =>
      if s == 0 then
        let tLo := fresh
        ([.limb tLo dst (.mulWide64 a (.imm m))], fresh + 1)
      else
        let tLo := fresh
        let tHi := fresh + 1
        ([.limb tLo tHi (.mulWide64 a (.imm m)),
          .assign dst (.bin .shr .w64 (.v tHi) (.imm (UInt64.ofNat s)))],
         fresh + 2)
  | .addShift m' s =>
      let tLo := fresh
      let tHi := fresh + 1
      let tSub := fresh + 2
      let tHalf := fresh + 3
      if s ≤ 1 then
        ([.limb tLo tHi (.mulWide64 a (.imm m')),
          .assign tSub (.bin .sub .w64 a (.v tHi)),
          .assign tHalf (.bin .shr .w64 (.v tSub) (.imm 1)),
          .assign dst (.bin .add .w64 (.v tHalf) (.v tHi))],
         fresh + 4)
      else
        let tCore := fresh + 4
        ([.limb tLo tHi (.mulWide64 a (.imm m')),
          .assign tSub (.bin .sub .w64 a (.v tHi)),
          .assign tHalf (.bin .shr .w64 (.v tSub) (.imm 1)),
          .assign tCore (.bin .add .w64 (.v tHalf) (.v tHi)),
          .assign dst (.bin .shr .w64 (.v tCore) (.imm (UInt64.ofNat (s - 1))))],
         fresh + 5)

/-- Emit 32-bit Granlund–Montgomery magic-multiplier quotient sequence for `a / d` into `dst`. -/
private def emitMagicU32 (dst : VReg) (a : Arg) (mc : Magic32) (fresh : VReg) :
    List Stmt × VReg :=
  let tU := fresh
  let tMul := fresh + 1
  match mc with
  | .simple m s =>
      ([.assign tU (.bin .and .w64 a (.imm 0xffffffff)),
        .assign tMul (.bin .mul .w64 (.v tU) (.imm m)),
        .assign dst (.bin .shr .w64 (.v tMul) (.imm (UInt64.ofNat (32 + s))))],
       fresh + 2)
  | .addShift m' s =>
      let tHi := fresh + 2
      let tSub := fresh + 3
      let tHalf := fresh + 4
      if s ≤ 1 then
        ([.assign tU (.bin .and .w64 a (.imm 0xffffffff)),
          .assign tMul (.bin .mul .w64 (.v tU) (.imm m')),
          .assign tHi (.bin .shr .w64 (.v tMul) (.imm 32)),
          .assign tSub (.bin .sub .w64 (.v tU) (.v tHi)),
          .assign tHalf (.bin .shr .w64 (.v tSub) (.imm 1)),
          .assign dst (.bin .add .w64 (.v tHalf) (.v tHi))],
         fresh + 5)
      else
        let tCore := fresh + 5
        ([.assign tU (.bin .and .w64 a (.imm 0xffffffff)),
          .assign tMul (.bin .mul .w64 (.v tU) (.imm m')),
          .assign tHi (.bin .shr .w64 (.v tMul) (.imm 32)),
          .assign tSub (.bin .sub .w64 (.v tU) (.v tHi)),
          .assign tHalf (.bin .shr .w64 (.v tSub) (.imm 1)),
          .assign tCore (.bin .add .w64 (.v tHalf) (.v tHi)),
          .assign dst (.bin .shr .w64 (.v tCore) (.imm (UInt64.ofNat (s - 1))))],
         fresh + 6)

/-- Safe guard ensuring 32-bit magic multiplier won't normalize `mul` to `shl` or identity. -/
private def isSafeMagic32 (mc : Magic32) : Bool :=
  let m := match mc with | .simple m _ => m | .addShift m' _ => m'
  m != 0 && m != 1 && (findPow2 .w64 m).isNone

/-! ## Dominator-tree GVN scope and per-segment memory state -/

/-- Dominating scope carried down the dominator tree. -/
private structure GvnScope where
  /-- Copy & constant propagation table. -/
  copyMap : Src.NatMap Arg := .leaf
  /-- Symbolic expression of each dominating register (normalized). -/
  symMap : Src.NatMap SymExpr := .leaf
  /-- Original `Addr` for registers defined by `.addr m` (for disp-folding). -/
  addrMap : Src.NatMap Addr := .leaf
  /-- Pure GVN table: normalized mem-free `SymExpr` → dominating `VReg`. -/
  gvnMap : List (SymExpr × VReg) := []
  /-- Dominating branch facts. -/
  facts : List PFact := []

/-- Per-segment state (reset at block entry and at every `.call`). -/
private structure SegOpt where
  smem : SymMem := []
  snaps : SnapTable := SnapTable.init
  /-- Active stored `(width, caddr, arg)` entries whose slot has not been overwritten. -/
  storeVals : List (Width × Option ConstAddr × Arg) := []
  /-- Load CSE table for this segment: normalized `SymExpr.load` → `VReg`. -/
  loadMap : List (SymExpr × VReg) := []
  /-- Same-segment constant division cache: `(width, lhsExpr, dTrunc) → qReg`. -/
  divCache : List (Width × SymExpr × Word × VReg) := []

private def symOf (sc : GvnScope) (x : VReg) : SymExpr :=
  sc.symMap.getD x (.reg x)

private def lookupGvn (sc : GvnScope) (e : SymExpr) : Option VReg :=
  (sc.gvnMap.find? fun (se, _) => se == e).map (·.2)

private def lookupLoad (sg : SegOpt) (e : SymExpr) : Option VReg :=
  (sg.loadMap.find? fun (se, _) => se == e).map (·.2)

private def lookupDivCache (sg : SegOpt) (w : Width) (ea : SymExpr) (d : Word) : Option VReg :=
  (sg.divCache.find? fun (w', e', d', _) => w' == w && e' == ea && d' == d).map (·.2.2.2)

/-- Simplify a binary operation into a single `Rhs` (algebraic identities, constant folding,
power-of-2 shift/mask, `addr` displacement folding). Does NOT emit multi-stmt magic division. -/
private def simplifyBinRhs (sc : GvnScope) (o : BinOp) (w : Width) (a b : Arg) : Rhs :=
  match a, b with
  | .imm va, .imm vb =>
      match o.eval w va vb with
      | some v => .arg (.imm v)
      | none => .bin o w a b
  | _, _ =>
      -- Put constant on the right for commutative operations
      let (a, b) := match binOpIsComm o, a, b with
        | true, .imm _, .v _ => (b, a)
        | _, _, _ => (a, b)
      match o with
      | .add =>
          match w, a, b with
          | .w64, a, .imm 0 => .arg a
          | .w64, .v r, .imm k =>
              match sc.addrMap.get? r, immAsSmallInt? k with
              | some m, some ki =>
                  let d' := m.disp + ki
                  if fitsI32 d' then .addr { m with disp := d' }
                  else .bin .add .w64 a b
              | _, _ => .bin .add .w64 a b
          | _, _, _ => .bin .add w a b
      | .sub =>
          if a == b then .arg (.imm 0)
          else match w, a, b with
          | .w64, a, .imm 0 => .arg a
          | .w64, .v r, .imm k =>
              match sc.addrMap.get? r, immAsSmallInt? (0 - k) with
              | some m, some negKi =>
                  let d' := m.disp + negKi
                  if fitsI32 d' then .addr { m with disp := d' }
                  else .bin .sub .w64 a b
              | _, _ => .bin .sub .w64 a b
          | _, _, _ => .bin .sub w a b
      | .mul =>
          match a, b with
          | _, .imm 0 => .arg (.imm 0)
          | a, .imm 1 => if w == .w64 then .arg a else .bin .mul w a (.imm 1)
          | a, .imm k =>
              match findPow2 w k with
              | some sh => .bin .shl w a (.imm (UInt64.ofNat sh))
              | none => .bin .mul w a (.imm k)
          | _, _ => .bin .mul w a b
      | .and =>
          match a, b with
          | _, .imm 0 => .arg (.imm 0)
          | a, .imm k => if w == .w64 && k == w.mask then .arg a else .bin .and w a (.imm k)
          | _, _ => if w == .w64 && a == b then .arg a else .bin .and w a b
      | .or =>
          match a, b with
          | a, .imm 0 => if w == .w64 then .arg a else .bin .or w a (.imm 0)
          | _, .imm k => if w.truncate k == w.mask then .arg (.imm w.mask) else .bin .or w a (.imm k)
          | _, _ => if w == .w64 && a == b then .arg a else .bin .or w a b
      | .xor =>
          if a == b then .arg (.imm 0)
          else match w, a, b with
          | .w64, a, .imm 0 => .arg a
          | _, _, _ => .bin .xor w a b
      | .shl =>
          match a, b with
          | .imm 0, _ => .arg (.imm 0)
          | a, .imm k =>
              if w == .w64 && (k &&& Lir.shiftMask .w64) == 0 then .arg a
              else .bin .shl w a (.imm (k &&& Lir.shiftMask w))
          | _, _ => .bin .shl w a b
      | .shr =>
          match a, b with
          | .imm 0, _ => .arg (.imm 0)
          | a, .imm k =>
              if w == .w64 && (k &&& Lir.shiftMask .w64) == 0 then .arg a
              else .bin .shr w a (.imm (k &&& Lir.shiftMask w))
          | _, _ => .bin .shr w a b
      | .sar =>
          match a, b with
          | .imm 0, _ => .arg (.imm 0)
          | a, .imm k =>
              if w == .w64 && (k &&& Lir.shiftMask .w64) == 0 then .arg a
              else .bin .sar w a (.imm (k &&& Lir.shiftMask w))
          | _, _ => .bin .sar w a b
      | .udiv =>
          match a, b with
          | a, .imm k =>
              let d := w.truncate k
              if d == 1 then (if w == .w64 then .arg a else .bin .and w a (.imm w.mask))
              else match findPow2 w k with
              | some sh => .bin .shr w a (.imm (UInt64.ofNat sh))
              | none => .bin .udiv w a (.imm k)
          | _, _ => .bin .udiv w a b
      | .urem =>
          match a, b with
          | _, .imm k =>
              let d := w.truncate k
              if d == 1 then .arg (.imm 0)
              else match findPow2 w k with
              | some sh => .bin .and w a (.imm (UInt64.ofNat (2 ^ sh - 1)))
              | none => .bin .urem w a (.imm k)
          | _, _ => .bin .urem w a b

/-- Optimize one statement within a block, updating `(sc, sg, fresh)` and returning emitted stmts. -/
private def optStmt (sc : GvnScope) (sg : SegOpt) (fresh : VReg) (s : Stmt) :
    List Stmt × GvnScope × SegOpt × VReg :=
  match s with
  | .assign x r =>
      let r1 := substRhs sc.copyMap r
      match r1 with
      | .arg a =>
          let e := (argToSym (symOf sc) a).norm
          let sc' := { sc with copyMap := sc.copyMap.insert x a, symMap := sc.symMap.insert x e }
          ([.assign x (.arg a)], sc', sg, fresh)
      | .addr m =>
          let e := (addrToSym (symOf sc) m).norm
          match e with
          | .imm k =>
              let sc' := { sc with copyMap := sc.copyMap.insert x (.imm k), symMap := sc.symMap.insert x e }
              ([.assign x (.arg (.imm k))], sc', sg, fresh)
          | _ =>
              match lookupGvn sc e with
              | some prev =>
                  let sc' := { sc with copyMap := sc.copyMap.insert x (.v prev), symMap := sc.symMap.insert x e }
                  ([.assign x (.arg (.v prev))], sc', sg, fresh)
              | none =>
                  let sc' :=
                    { sc with
                      symMap := sc.symMap.insert x e
                      addrMap := sc.addrMap.insert x m
                      gvnMap := (e, x) :: sc.gvnMap }
                  ([.assign x (.addr m)], sc', sg, fresh)
      | .select c w a b t f =>
          let ea := (argToSym (symOf sc) a).norm
          let eb := (argToSym (symOf sc) b).norm
          let et := (argToSym (symOf sc) t).norm
          let ef := (argToSym (symOf sc) f).norm
          let e := (SymExpr.select c w ea eb et ef).norm
          let folded? : Option Arg :=
            if t == f then some t
            else match condFromFacts sc.facts c w ea eb with
            | some true => some t
            | some false => some f
            | none => match e with | .imm k => some (.imm k) | _ => none
          match folded? with
          | some aRes =>
              let eRes := (argToSym (symOf sc) aRes).norm
              let sc' := { sc with copyMap := sc.copyMap.insert x aRes, symMap := sc.symMap.insert x eRes }
              ([.assign x (.arg aRes)], sc', sg, fresh)
          | none =>
              match lookupGvn sc e with
              | some prev =>
                  let sc' := { sc with copyMap := sc.copyMap.insert x (.v prev), symMap := sc.symMap.insert x e }
                  ([.assign x (.arg (.v prev))], sc', sg, fresh)
              | none =>
                  let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                  ([.assign x (.select c w a b t f)], sc', sg, fresh)
      | .test c w a b =>
          let ea := (argToSym (symOf sc) a).norm
          let eb := (argToSym (symOf sc) b).norm
          let e := (SymExpr.test c w ea eb).norm
          let folded? : Option Word :=
            match condFromFacts sc.facts c w ea eb with
            | some true => some 1
            | some false => some 0
            | none => match e with | .imm k => some k | _ => none
          match folded? with
          | some k =>
              let sc' := { sc with copyMap := sc.copyMap.insert x (.imm k), symMap := sc.symMap.insert x (.imm k) }
              ([.assign x (.arg (.imm k))], sc', sg, fresh)
          | none =>
              match lookupGvn sc e with
              | some prev =>
                  let sc' := { sc with copyMap := sc.copyMap.insert x (.v prev), symMap := sc.symMap.insert x e }
                  ([.assign x (.arg (.v prev))], sc', sg, fresh)
              | none =>
                  let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                  ([.assign x (.test c w a b)], sc', sg, fresh)
      | .bsr64 a =>
          let ea := (argToSym (symOf sc) a).norm
          let e := (SymExpr.bsr64 ea).norm
          match e with
          | .imm k =>
              let sc' := { sc with copyMap := sc.copyMap.insert x (.imm k), symMap := sc.symMap.insert x e }
              ([.assign x (.arg (.imm k))], sc', sg, fresh)
          | _ =>
              match lookupGvn sc e with
              | some prev =>
                  let sc' := { sc with copyMap := sc.copyMap.insert x (.v prev), symMap := sc.symMap.insert x e }
                  ([.assign x (.arg (.v prev))], sc', sg, fresh)
              | none =>
                  let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                  ([.assign x (.bsr64 a)], sc', sg, fresh)
      | .load w ext m =>
          let addr := (addrToSym (symOf sc) m).norm
          let ca := toConstAddr (symOf sc) m
          -- 1. Try store-to-load forwarding from `sg.storeVals`
          let fwd? : Option Rhs :=
            match sg.storeVals.find? (fun (sw, sca, _) => constAddrSame w ca sw sca) with
            | some (_, _, sa) =>
                match w, ext with
                | .w64, _ => some (.arg sa)
                | _, .zero =>
                    match sa with
                    | .imm k => some (.arg (.imm (w.truncate k)))
                    | _ => some (.bin .and .w64 sa (.imm w.mask))
                | _, .sign =>
                    match sa with
                    | .imm k => some (.arg (.imm (sext w (w.truncate k))))
                    | _ => none
            | none => none
          match fwd? with
          | some (.arg sa) =>
              let e := (argToSym (symOf sc) sa).norm
              let sc' := { sc with copyMap := sc.copyMap.insert x sa, symMap := sc.symMap.insert x e }
              ([.assign x (.arg sa)], sc', sg, fresh)
          | some rhsFwd =>
              let (e, snaps') := SymMem.read sg.smem sg.snaps w ext addr ca
              let sc' := { sc with symMap := sc.symMap.insert x e.norm }
              ([.assign x rhsFwd], sc', { sg with snaps := snaps' }, fresh)
          | none =>
              -- 2. Try intra-segment Load CSE via `SymMem.read` snapshot canonicalization
              let (e, snaps') := SymMem.read sg.smem sg.snaps w ext addr ca
              let e' := e.norm
              let sg1 := { sg with snaps := snaps' }
              match lookupLoad sg1 e' with
              | some prev =>
                  let sc' := { sc with copyMap := sc.copyMap.insert x (.v prev), symMap := sc.symMap.insert x e' }
                  ([.assign x (.arg (.v prev))], sc', sg1, fresh)
              | none =>
                  let sc' := { sc with symMap := sc.symMap.insert x e' }
                  let sg2 := { sg1 with loadMap := (e', x) :: sg1.loadMap }
                  ([.assign x (.load w ext m)], sc', sg2, fresh)
      | .bin o w a b =>
          let ea := (argToSym (symOf sc) a).norm
          let eb := (argToSym (symOf sc) b).norm
          let e := mkBin o w ea eb
          -- First check constant result or GVN hit!
          match e with
          | .imm k =>
              let sc' := { sc with copyMap := sc.copyMap.insert x (.imm k), symMap := sc.symMap.insert x e }
              ([.assign x (.arg (.imm k))], sc', sg, fresh)
          | _ =>
              match lookupGvn sc e with
              | some prev =>
                  let sc' := { sc with copyMap := sc.copyMap.insert x (.v prev), symMap := sc.symMap.insert x e }
                  ([.assign x (.arg (.v prev))], sc', sg, fresh)
              | none =>
                  let rSimp := simplifyBinRhs sc o w a b
                  match rSimp with
                  | .arg aRes =>
                      let sc' := { sc with copyMap := sc.copyMap.insert x aRes, symMap := sc.symMap.insert x e }
                      ([.assign x (.arg aRes)], sc', sg, fresh)
                  | .addr mRes =>
                      let sc' :=
                        { sc with
                          symMap := sc.symMap.insert x e
                          addrMap := sc.addrMap.insert x mRes
                          gvnMap := (e, x) :: sc.gvnMap }
                      ([.assign x (.addr mRes)], sc', sg, fresh)
                  | .bin .udiv .w64 a' (.imm d) =>
                      -- Granlund–Montgomery 64-bit unsigned division strength reduction
                      match magicU64 d with
                      | some mc =>
                          let (stmts, fresh') := emitMagicU64 x a' mc fresh
                          let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                          let sg' := { sg with divCache := (.w64, ea, d, x) :: sg.divCache }
                          (stmts, sc', sg', fresh')
                      | none =>
                          let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                          ([.assign x rSimp], sc', sg, fresh)
                  | .bin .urem .w64 a' (.imm d) =>
                      -- Granlund–Montgomery 64-bit unsigned remainder: `a - q * d` (reusing `q` if cached!)
                      match magicU64 d with
                      | some mc =>
                          let (qReg, qStmts, sg1, fresh1) :=
                            match lookupDivCache sg .w64 ea d with
                            | some q => (q, [], sg, fresh)
                            | none =>
                                let q := fresh
                                let (qs, fr) := emitMagicU64 q a' mc (fresh + 1)
                                (q, qs, { sg with divCache := (.w64, ea, d, q) :: sg.divCache }, fr)
                          let tProd := fresh1
                          let remStmts : List Stmt := qStmts ++
                            [Stmt.assign tProd (.bin .mul .w64 (.v qReg) (.imm d)),
                             Stmt.assign x (.bin .sub .w64 a' (.v tProd))]
                          let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                          (remStmts, sc', sg1, fresh1 + 1)
                      | none =>
                          let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                          ([.assign x rSimp], sc', sg, fresh)
                  | .bin .udiv .w32 a' (.imm d) =>
                      let dw := X86.Width.w32.truncate d
                      match magicU32 dw with
                      | some mc =>
                          if isSafeMagic32 mc then
                            let (stmts, fresh') := emitMagicU32 x a' mc fresh
                            let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                            let sg' := { sg with divCache := (.w32, ea, dw, x) :: sg.divCache }
                            (stmts, sc', sg', fresh')
                          else
                            let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                            ([.assign x rSimp], sc', sg, fresh)
                      | none =>
                          let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                          ([.assign x rSimp], sc', sg, fresh)
                  | .bin .urem .w32 a' (.imm d) =>
                      let dw := X86.Width.w32.truncate d
                      match magicU32 dw with
                      | some mc =>
                          if isSafeMagic32 mc then
                            let (qReg, qStmts, sg1, fresh1) :=
                              match lookupDivCache sg .w32 ea dw with
                              | some q => (q, [], sg, fresh)
                              | none =>
                                  let q := fresh
                                  let (qs, fr) := emitMagicU32 q a' mc (fresh + 1)
                                  (q, qs, { sg with divCache := (.w32, ea, dw, q) :: sg.divCache }, fr)
                            let tProd := fresh1
                            let remStmts : List Stmt := qStmts ++
                              [Stmt.assign tProd (.bin .mul .w32 (.v qReg) (.imm d)),
                               Stmt.assign x (.bin .sub .w32 a' (.v tProd))]
                            let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                            (remStmts, sc', sg1, fresh1 + 1)
                          else
                            let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                            ([.assign x rSimp], sc', sg, fresh)
                      | none =>
                          let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                          ([.assign x rSimp], sc', sg, fresh)
                  | _ =>
                      let sc' := { sc with symMap := sc.symMap.insert x e, gvnMap := (e, x) :: sc.gvnMap }
                      ([.assign x rSimp], sc', sg, fresh)
  | .limb r1 r2 op =>
      let op1 := substLimb sc.copyMap op
      let (e1, e2) := match op1 with
        | .mulWide64 a b =>
            let ea := (argToSym (symOf sc) a).norm; let eb := (argToSym (symOf sc) b).norm
            (mkBin .mul .w64 ea eb, (SymExpr.mulHi ea eb).norm)
        | .divWide64 hi lo d =>
            let ehi := (argToSym (symOf sc) hi).norm
            let elo := (argToSym (symOf sc) lo).norm
            let ed := (argToSym (symOf sc) d).norm
            ((SymExpr.divQ ehi elo ed).norm, (SymExpr.divR ehi elo ed).norm)
        | .addCarry64 a b c =>
            let ea := (argToSym (symOf sc) a).norm
            let eb := (argToSym (symOf sc) b).norm
            let ec := (argToSym (symOf sc) c).norm
            ((SymExpr.addCLo ea eb ec).norm, (SymExpr.addCHi ea eb ec).norm)
        | .subBorrow64 a b c =>
            let ea := (argToSym (symOf sc) a).norm
            let eb := (argToSym (symOf sc) b).norm
            let ec := (argToSym (symOf sc) c).norm
            ((SymExpr.subBLo ea eb ec).norm, (SymExpr.subBHi ea eb ec).norm)
      -- Check if BOTH outputs are already known (constants or GVN hits)
      let res1? : Option Arg := match e1 with
        | .imm k => some (.imm k)
        | _ => (lookupGvn sc e1).map .v
      let res2? : Option Arg := match e2 with
        | .imm k => some (.imm k)
        | _ => (lookupGvn sc e2).map .v
      match res1?, res2? with
      | some a1, some a2 =>
          let sc' :=
            { sc with
              copyMap := (sc.copyMap.insert r1 a1).insert r2 a2
              symMap := (sc.symMap.insert r1 e1).insert r2 e2 }
          ([.assign r1 (.arg a1), .assign r2 (.arg a2)], sc', sg, fresh)
      | _, _ =>
          let sc' :=
            { sc with
              symMap := (sc.symMap.insert r1 e1).insert r2 e2
              gvnMap := (e2, r2) :: (e1, r1) :: sc.gvnMap }
          ([.limb r1 r2 op1], sc', sg, fresh)
  | .store w m a =>
      let m' := substAddr sc.copyMap m
      let a' := substArg sc.copyMap a
      let addr := (addrToSym (symOf sc) m').norm
      let ca := toConstAddr (symOf sc) m'
      let val := (argToSym (symOf sc) a').norm
      let smem' := SymMem.write sg.smem w addr ca val
      let storeVals' :=
        let kept := sg.storeVals.filter fun (sw, sca, _) => constAddrDisjoint w ca sw sca
        if ca.isSome then (w, ca, a') :: kept else kept
      ([.store w m' a'], sc, { sg with smem := smem', storeVals := storeVals' }, fresh)
  | .call rs f as =>
      let as' := as.map (substArg sc.copyMap)
      -- Reset per-segment memory state across `.call`!
      ([.call rs f as'], sc, {}, fresh)

/-- Optimize one block's body and terminator, returning the updated block, updated `fresh`,
and per-successor `(targetLabel, extraFacts, edgeArgs)` refinements for dominated children. -/
private def optBlock (sc : GvnScope) (fresh : VReg) (blk : Block) :
    Block × GvnScope × List (Label × Option PFact × List Arg) × VReg :=
  let (revStmts, sc1, _, fresh1) := blk.body.foldl
    (init := ([], sc, ({} : SegOpt), fresh)) fun (acc, scc, sgg, fr) stmt =>
      let (out, scc', sgg', fr') := optStmt scc sgg fr stmt
      (out.reverse ++ acc, scc', sgg', fr')
  let body1 := revStmts.reverse
  -- Optimize terminator
  let term0 := substTerm sc1.copyMap blk.term
  match term0 with
  | .jump e =>
      ({ blk with body := body1.toArray, term := .jump e }, sc1, [(e.target, none, e.args)], fresh1)
  | .br c w a b t f =>
      let ea := (argToSym (symOf sc1) a).norm
      let eb := (argToSym (symOf sc1) b).norm
      match condFromFacts sc1.facts c w ea eb with
      | some true =>
          ({ blk with body := body1.toArray, term := .jump t }, sc1, [(t.target, none, t.args)], fresh1)
      | some false =>
          ({ blk with body := body1.toArray, term := .jump f }, sc1, [(f.target, none, f.args)], fresh1)
      | none =>
          if t == f then
            ({ blk with body := body1.toArray, term := .jump t }, sc1, [(t.target, none, t.args)], fresh1)
          else
            let fT : Option PFact := if ea.isMemFree && eb.isMemFree then
              some { cond := c, width := w, lhs := ea, rhs := eb, result := true } else none
            let fF : Option PFact := if ea.isMemFree && eb.isMemFree then
              some { cond := c, width := w, lhs := ea, rhs := eb, result := false } else none
            ({ blk with body := body1.toArray, term := .br c w a b t f }, sc1,
             [(t.target, fT, t.args), (f.target, fF, f.args)], fresh1)
  | .brOvf o x a b ok ovf =>
      let ea := (argToSym (symOf sc1) a).norm
      let eb := (argToSym (symOf sc1) b).norm
      let resSym := ovfToSym o ea eb
      let emitFolded (edge : Edge) : Block × GvnScope × List (Label × Option PFact × List Arg) × VReg :=
        -- Choose best instruction to compute `x` (constant, GVN hit, `addr` disp-fold, or wrapping binop)
        let (xStmt, sc2) : Stmt × GvnScope :=
          match resSym with
          | .imm k =>
              (Stmt.assign x (.arg (.imm k)),
               { sc1 with copyMap := sc1.copyMap.insert x (.imm k), symMap := sc1.symMap.insert x resSym })
          | _ =>
              match lookupGvn sc1 resSym with
              | some prev =>
                  (Stmt.assign x (.arg (.v prev)),
                   { sc1 with copyMap := sc1.copyMap.insert x (.v prev), symMap := sc1.symMap.insert x resSym })
              | none =>
                  let rhs := simplifyBinRhs sc1 (ovfBinOp o) .w64 a b
                  match rhs with
                  | .arg aRes =>
                      (Stmt.assign x (.arg aRes),
                       { sc1 with copyMap := sc1.copyMap.insert x aRes, symMap := sc1.symMap.insert x resSym })
                  | .addr mRes =>
                      (Stmt.assign x (.addr mRes),
                       { sc1 with symMap := sc1.symMap.insert x resSym, addrMap := sc1.addrMap.insert x mRes,
                                  gvnMap := (resSym, x) :: sc1.gvnMap })
                  | _ =>
                      (Stmt.assign x rhs,
                       { sc1 with symMap := sc1.symMap.insert x resSym, gvnMap := (resSym, x) :: sc1.gvnMap })
        let edge' := substEdge sc2.copyMap edge
        ({ blk with body := (body1 ++ [xStmt]).toArray, term := .jump edge' }, sc2,
         [(edge'.target, none, edge'.args)], fresh1)
      match ovfFromFacts sc1.facts o ea eb with
      | some false => emitFolded ok
      | some true => emitFolded ovf
      | none =>
          if ok == ovf then emitFolded ok
          else
            let sc2 := { sc1 with symMap := sc1.symMap.insert x resSym, gvnMap := (resSym, x) :: sc1.gvnMap }
            ({ blk with body := body1.toArray, term := .brOvf o x a b ok ovf }, sc2,
             [(ok.target, none, ok.args), (ovf.target, none, ovf.args)], fresh1)
  | t => ({ blk with body := body1.toArray, term := t }, sc1, [], fresh1)

/-- Dominator-tree preorder GVN + algebraic simplification + div strength reduction +
branch/brOvf folding + store-to-load forwarding + load CSE. -/
def gvnPassFunc (F : Func) : Func :=
  let n := F.blocks.size
  if n == 0 then F
  else
    let children := domTreeChildren F
    let preds := F.predCounts
    let fresh0 := nextFreshVReg F
    let rec dfs (fuel : Nat) (b : Label) (sc : GvnScope) (bs : Array Block) (fresh : VReg) :
        Array Block × VReg :=
      match fuel with
      | 0 => (bs, fresh)
      | fuel + 1 =>
          match bs[b]? with
          | none => (bs, fresh)
          | some blk =>
              let (blk', sc1, edgeInfos, fresh1) := optBlock sc fresh blk
              let bs1 := bs.set! b blk'
              let kids := children[b]?.getD []
              kids.foldl (init := (bs1, fresh1)) fun (bsAcc, frAcc) ch =>
                -- Refine scope for single-predecessor dominated child `ch`
                let scChild :=
                  if preds[ch]?.getD 0 == 1 then
                    match edgeInfos.filter (fun (t, _, _) => t == ch) with
                    | [(_, fact?, eArgs)] =>
                        let scF := match fact? with
                          | some pf => { sc1 with facts := pf :: sc1.facts }
                          | none => sc1
                        match bsAcc[ch]? with
                        | some chBlk =>
                            if chBlk.params.length == eArgs.length then
                              (chBlk.params.zip eArgs).foldl (init := scF) fun s (p, a) =>
                                let ea := (argToSym (symOf sc1) a).norm
                                { s with copyMap := s.copyMap.insert p a, symMap := s.symMap.insert p ea }
                            else scF
                        | none => scF
                    | _ => sc1
                  else sc1
                dfs fuel ch scChild bsAcc frAcc
    let (bsFinal, _) := dfs (n + 1) 0 {} F.blocks fresh0
    { F with blocks := bsFinal }

/-! ## Intra-block Dead Store Elimination (DSE) -/

/-- Backward DSE over one call-free segment, given symbolic register map `symMap` before
each statement. Mirrors `SymMem.write` / `dropShadowed` / `readAux` exactly. -/
private def dseSegment (sym0 : Src.NatMap SymExpr) (stmts : List Stmt) : List Stmt :=
  -- Forward pass: attach `(stmt, ca?)` where `ca?` is the `ConstAddr` for `.load`/`.store`
  let lookup (m : Src.NatMap SymExpr) (x : VReg) : SymExpr := m.getD x (.reg x)
  let (_, annotatedRev) := stmts.foldl (init := (sym0, ([] : List (Stmt × Option (Width × Option ConstAddr)))))
    fun (m, acc) s =>
      match s with
      | .assign x (.load w _ addr) =>
          let ca := toConstAddr (lookup m) addr
          (m.insert x (.reg x), (s, some (w, ca)) :: acc)
      | .assign x r =>
          let e := match r with
            | .arg a => (argToSym (lookup m) a).norm
            | .bin o w a b => mkBin o w (argToSym (lookup m) a).norm (argToSym (lookup m) b).norm
            | .addr ad => (addrToSym (lookup m) ad).norm
            | _ => .reg x
          (m.insert x e, (s, none) :: acc)
      | .limb r1 r2 _ =>
          ((m.insert r1 (.reg r1)).insert r2 (.reg r2), (s, none) :: acc)
      | .store w addr _ =>
          let ca := toConstAddr (lookup m) addr
          (m, (s, some (w, ca)) :: acc)
      | .call .. => (m, (s, none) :: acc)
  -- Backward pass: maintain `overwritten` slots guaranteed overwritten later with no intervening may-alias
  let (_, kept) := annotatedRev.foldl (init := (([] : List (Width × Option ConstAddr)), ([] : List Stmt)))
    fun (over, acc) (s, info?) =>
      match s, info? with
      | .store w _ _, some (_, ca) =>
          if over.any (fun (ow, oca) => constAddrSame w ca ow oca) then
            -- Shadowed dead store! Drop it!
            (over, acc)
          else
            -- Keep store; drop any `over` entries that may-alias this store (cannot commute past it)
            let over1 := over.filter fun (ow, oca) => constAddrDisjoint w ca ow oca
            let over2 := if ca.isSome then (w, ca) :: over1 else over1
            (over2, s :: acc)
      | .assign _ (.load ..), some (wl, cal) =>
          -- A load makes any may-aliasing store live!
          let over1 := over.filter fun (ow, oca) => constAddrDisjoint wl cal ow oca
          (over1, s :: acc)
      | _, _ => (over, s :: acc)
  kept

/-- Run intra-block DSE across all segments of all blocks of `F`. -/
def dseFunc (F : Func) : Func :=
  let optBlk (blk : Block) : Block :=
    let rec go (cur : List Stmt) : List Stmt → List Stmt
      | [] => dseSegment .leaf cur.reverse
      | .call rs f as :: rest =>
          dseSegment .leaf cur.reverse ++ [.call rs f as] ++ go [] rest
      | s :: rest => go (s :: cur) rest
    { blk with body := (go [] blk.body.toList).toArray }
  { F with blocks := F.blocks.map optBlk }

/-! ## Fixpoint Dead Code Elimination (DCE) -/

/-- Single pass of DCE: deletes pure `.assign` and `.limb` statements whose defs are unused. -/
private def dceStep (F : Func) : Func × Bool :=
  let used0 : Src.NatSet := F.blocks.foldl (init := (Src.NatMap.leaf : Src.NatSet)) fun u blk =>
    let u1 := blk.term.uses.foldl (fun s x => s.insert x) u
    let u2 := blk.term.edgeUses.foldl (fun s x => s.insert x) u1
    blk.body.foldl (init := u2) fun s st =>
      st.uses.foldl (fun acc x => acc.insert x) s
  let (blocks', changed) := F.blocks.foldl (init := (#[], false)) fun (bs, ch) blk =>
    let (body', bch) := blk.body.foldl (init := (#[], false)) fun (acc, c) st =>
      match st with
      | .assign x _ =>
          if used0.contains x then (acc.push st, c) else (acc, true)
      | .limb r1 r2 _ =>
          if used0.contains r1 || used0.contains r2 then (acc.push st, c) else (acc, true)
      | .store .. | .call .. => (acc.push st, c)
    (bs.push { blk with body := body' }, ch || bch)
  ({ F with blocks := blocks' }, changed)

/-- Fixpoint DCE over `F`. -/
def dceFunc (F : Func) : Func :=
  let totalStmts := F.blocks.foldl (fun acc b => acc + b.body.size) 0
  let rec go : Nat → Func → Func
    | 0, cur => cur
    | fuel + 1, cur =>
        let (cur', ch) := dceStep cur
        if !ch then cur' else go fuel cur'
  go (totalStmts + 2) F

/-! ## Order-preserving unreachable block pruning -/

/-- Remove unreachable blocks while preserving the relative order of all kept blocks
(so `b1 ≤ b2 ↔ newIdx b1 ≤ newIdx b2` and all back-edge charges stay identical). -/
def pruneUnreachable (F : Func) : Func :=
  let n := F.blocks.size
  if n ≤ 1 then F
  else
    let reach := F.rpoIndex.map Option.isSome
    if reach.all id then F
    else
      let (newIdx, _) := (List.range n).foldl (init := (Array.replicate n 0, 0)) fun (arr, next) b =>
        if reach[b]! then (arr.set! b next, next + 1) else (arr, next)
      let remapEdge (e : Edge) : Edge :=
        { e with target := newIdx[e.target]?.getD e.target }
      let remapTerm (t : Term) : Term :=
        t.setEdges (t.edges.map remapEdge)
      let kept := (List.range n).filterMap fun b =>
        if reach[b]! then
          (F.blocks[b]?).map fun blk => { blk with term := remapTerm blk.term }
        else none
      { F with blocks := kept.toArray }

/-- Combined GVN + DSE + DCE + unreachable-block pruning pass on one function. -/
def gvnFunc (F : Func) : Func :=
  let F1 := gvnPassFunc F
  let F2 := pruneUnreachable F1
  let F3 := dseFunc F2
  dceFunc F3

end IxCC.Lir.Opt
