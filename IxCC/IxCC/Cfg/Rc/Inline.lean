import IxCC.Cfg.Rc.Layout

/-! # Inline RC Fast Paths (Track A2)

A pure Lir-to-Lir pass over the source functions (`f < l.sourceCount`) of the
plain-RC native program, applied right before `splitCriticalEdges`:

* **Inline `inc` (`l.incWrapper`):** 2-instruction tag-bit skip for immediates,
  single unsigned compare `< maxCount - 1` fast path incrementing `rc` in place
  with zero calls, and a cold slow check for overflow (`fail .heap`) vs static
  (immortal) cells.
* **Inline `dec` (`l.decWrapper`):** 2-instruction tag-bit skip for immediates,
  `rc == 1` (`cnt == 0`) calling `l.decProc` (`Gen.dec`) directly (bypassing
  `decrementWrapper`), static (`cnt <s 0`) skip, and inline `rc -= 1` on shared
  cells with zero calls.
* **Inline `alloc` (`l.allocWrapper i`):** inline free-list pop fast path,
  inline bump-pointer refill fallback, cold `fail .heap`, header store, and
  field stores — zero calls on every constructor allocation.

Every expanded block keeps its original chunk order (`newLabel` strictly
monotone), every internal edge is strictly forward (zero clock charge), every
fresh temporary register lies strictly above `freshBase F`, and all non-source
runtime procedures (`f ≥ l.sourceCount`) are untouched. Semantic preservation
is proved in `IxCC.Cfg.Rc.Proof.Inline`. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Inline

open IxCC.Cfg.Rc.Native

/-! ## Maximum virtual register in a Lir function -/

def maxList (xs : List Nat) (acc : Nat) : Nat :=
  xs.foldl max acc

def argMax (a : Lir.Arg) (acc : Nat) : Nat :=
  match a with
  | .v x => max acc x
  | .imm _ => acc

def argsMax (as : List Lir.Arg) (acc : Nat) : Nat :=
  as.foldl (fun m a => argMax a m) acc

def addrMax (m : Lir.Addr) (acc : Nat) : Nat :=
  let acc := match m.base with
    | some (.v x) => max acc x
    | _ => acc
  match m.index with
  | some (x, _) => max acc x
  | none => acc

def limbOpMax (op : Lir.LimbOp) (acc : Nat) : Nat :=
  match op with
  | .mulWide64 a b => argMax b (argMax a acc)
  | .divWide64 hi lo d => argMax d (argMax lo (argMax hi acc))
  | .addCarry64 a b c => argMax c (argMax b (argMax a acc))
  | .subBorrow64 a b c => argMax c (argMax b (argMax a acc))

def rhsMax (r : Lir.Rhs) (acc : Nat) : Nat :=
  match r with
  | .arg a => argMax a acc
  | .bin _ _ a b => argMax b (argMax a acc)
  | .load _ _ m => addrMax m acc
  | .addr m => addrMax m acc
  | .select _ _ a b t f => argMax f (argMax t (argMax b (argMax a acc)))
  | .test _ _ a b => argMax b (argMax a acc)
  | .bsr64 a => argMax a acc

def stmtMax (s : Lir.Stmt) (acc : Nat) : Nat :=
  match s with
  | .assign x r => rhsMax r (max acc x)
  | .limb r1 r2 op => limbOpMax op (max (max acc r1) r2)
  | .store _ m a => argMax a (addrMax m acc)
  | .call rs _ as => argsMax as (maxList rs acc)

def edgeMax (e : Lir.Edge) (acc : Nat) : Nat :=
  argsMax e.args acc

def termMax (t : Lir.Term) (acc : Nat) : Nat :=
  match t with
  | .jump e => edgeMax e acc
  | .br _ _ a b t f => edgeMax f (edgeMax t (argMax b (argMax a acc)))
  | .brOvf _ x a b ok ovf => edgeMax ovf (edgeMax ok (argMax b (argMax a (max acc x))))
  | .ret as => argsMax as acc
  | .tail _ as => argsMax as acc
  | .fail _ | .trap => acc

def blockMax (b : Lir.Block) (acc : Nat) : Nat :=
  let acc := maxList b.params acc
  let acc := b.body.toList.foldl (fun m s => stmtMax s m) acc
  termMax b.term acc

def maxVReg (F : Lir.Func) : Nat :=
  F.blocks.toList.foldl (fun m b => blockMax b m) (maxList F.params 0)

/-- Every register occurring anywhere in `F` is strictly below `freshBase F`. -/
def freshBase (F : Lir.Func) : Nat := maxVReg F + 1

/-! ## Classifying inlinable RC call statements -/

inductive RcSite where
  | inc (dst x : Lir.VReg)
  | dec (dst x : Lir.VReg)
  | alloc (dst : Lir.VReg) (ctorIdx : Nat) (layout : Rt.Rc.CellLayout) (cls : Nat) (args : List Lir.Arg)
  | reset (dst x : Lir.VReg) (ctorIdx : Nat) (layout : Rt.Rc.CellLayout) (cls : Nat) (mask : UInt64)
  | resetU (dst x : Lir.VReg) (ctorIdx : Nat) (layout : Rt.Rc.CellLayout) (cls : Nat) (mask : UInt64)
  | reuse (dst slot : Lir.VReg) (ctorIdx : Nat) (layout : Rt.Rc.CellLayout) (cls : Nat) (args : List Lir.Arg)
  | reuseU (dst slot : Lir.VReg) (ctorIdx : Nat) (layout : Rt.Rc.CellLayout) (cls : Nat) (args : List Lir.Arg)
  deriving DecidableEq, Repr

inductive RcPair where
  | fusedResetReuse (slot x dst : Lir.VReg) (idx1 : Nat) (lay1 : Rt.Rc.CellLayout) (mask : UInt64)
      (idx2 : Nat) (lay2 : Rt.Rc.CellLayout) (cls : Nat) (args : List Lir.Arg)
  | fusedResetUReuseU (slot x dst : Lir.VReg) (lay2 : Rt.Rc.CellLayout) (cls : Nat) (args : List Lir.Arg)
  deriving DecidableEq, Repr

def argsContainVReg (dst : Lir.VReg) : List Lir.Arg → Bool
  | [] => false
  | .v y :: rest => (y == dst) || argsContainVReg dst rest
  | .imm _ :: rest => argsContainVReg dst rest

/-- Field indices `j < n` whose live bit `j + 1` is `0` in tagged bitmask `mask`. -/
def deadFields (n : Nat) (mask : UInt64) : List Nat :=
  (List.range n).filter fun j => (mask &&& UInt64.ofNat (2 ^ (j + 1))) == 0

/-- Classify a Lir statement as an inlinable `inc`, `dec`, `alloc`, `reset`, or `reuse` RC site. -/
def classify (l : Layout) (s : Lir.Stmt) : Option RcSite :=
  match s with
  | .call [dst] f as =>
    if f == l.incWrapper then
      match as with
      | [.v x, .imm _] => some (.inc dst x)
      | _ => none
    else if f == l.decWrapper then
      match as with
      | [.v x] => some (.dec dst x)
      | _ => none
    else if l.allocWrapper 0 ≤ f && f < l.allocWrapper l.ctors.length then
      let idx := f - l.allocWrapper 0
      match l.ctors[idx]? with
      | some c =>
        let lay := Rt.Rc.CellLayout.ofFields c.arity c.tag
        match lay.cls? with
        | some cls =>
          if as.length == c.arity && lay.ok && !argsContainVReg dst as then
            some (.alloc dst idx lay cls as)
          else none
        | none => none
      | none => none
    else if l.resetWrapper 0 ≤ f && f < l.resetWrapper l.ctors.length then
      let idx := f - l.resetWrapper 0
      match l.ctors[idx]?, as with
      | some c, [.v x, .imm mask] =>
        let lay := Rt.Rc.CellLayout.ofFields c.arity c.tag
        match lay.cls? with
        | some cls =>
          if lay.ok && dst != x then some (.reset dst x idx lay cls mask) else none
        | none => none
      | _, _ => none
    else if l.resetUWrapper 0 ≤ f && f < l.resetUWrapper l.ctors.length then
      let idx := f - l.resetUWrapper 0
      match l.ctors[idx]?, as with
      | some c, [.v x, .imm mask] =>
        let lay := Rt.Rc.CellLayout.ofFields c.arity c.tag
        match lay.cls? with
        | some cls =>
          if lay.ok && dst != x then some (.resetU dst x idx lay cls mask) else none
        | none => none
      | _, _ => none
    else if l.reuseWrapper 0 ≤ f && f < l.reuseWrapper l.ctors.length then
      let idx := f - l.reuseWrapper 0
      match l.ctors[idx]?, as with
      | some c, .v slot :: args =>
        let lay := Rt.Rc.CellLayout.ofFields c.arity c.tag
        match lay.cls? with
        | some cls =>
          if args.length == c.arity && lay.ok && dst != slot && !argsContainVReg dst args then
            some (.reuse dst slot idx lay cls args)
          else none
        | none => none
      | _, _ => none
    else if l.reuseUWrapper 0 ≤ f && f < l.reuseUWrapper l.ctors.length then
      let idx := f - l.reuseUWrapper 0
      match l.ctors[idx]?, as with
      | some c, .v slot :: args =>
        let lay := Rt.Rc.CellLayout.ofFields c.arity c.tag
        match lay.cls? with
        | some cls =>
          if args.length == c.arity && lay.ok && dst != slot && !argsContainVReg dst args then
            some (.reuseU dst slot idx lay cls args)
          else none
        | none => none
      | _, _ => none
    else none
  | _ => none

/-- Peephole classifier for adjacent `reset`/`reuse` (or `resetU`/`reuseU`) on the same slot
with all-live fields and `lay1.nobj ≤ lay2.nobj`: fuses directly into a single `writeCell`
with zero intermediate `resetShell` stores and zero second branch. -/
def classifyPair (l : Layout) (s1 s2 : Lir.Stmt) : Option RcPair :=
  match classify l s1, classify l s2 with
  | some (.reset slot x idx1 lay1 cls1 mask), some (.reuse dst slot2 idx2 lay2 cls2 args) =>
    if slot == slot2 && cls1 == cls2 && lay1.nobj ≤ lay2.nobj &&
        (deadFields lay1.nobj mask).isEmpty &&
        dst != x && slot != x && dst != slot &&
        !argsContainVReg dst args && !argsContainVReg slot args then
      some (.fusedResetReuse slot x dst idx1 lay1 mask idx2 lay2 cls2 args)
    else none
  | some (.resetU slot x _ lay1 cls1 mask), some (.reuseU dst slot2 _ lay2 cls2 args) =>
    if slot == slot2 && cls1 == cls2 && lay1.nobj ≤ lay2.nobj &&
        (deadFields lay1.nobj mask).isEmpty &&
        dst != x && slot != x && dst != slot &&
        !argsContainVReg dst args && !argsContainVReg slot args then
      some (.fusedResetUReuseU slot x dst lay2 cls2 args)
    else none
  | _, _ => none

def siteExtra : RcSite → Nat
  | .inc .. => 5
  | .dec .. => 5
  | .alloc .. => 6
  | .reset .. => 4
  | .resetU .. => 0
  | .reuse .. => 3
  | .reuseU .. => 0

def pairExtra : RcPair → Nat
  | .fusedResetReuse .. => 4
  | .fusedResetUReuseU .. => 0

def stmtExtra (l : Layout) (s : Lir.Stmt) : Nat :=
  match classify l s with
  | none => 0
  | some site => siteExtra site

def stmtsExtra (l : Layout) : List Lir.Stmt → Nat
  | [] => 0
  | s1 :: s2 :: rest =>
    match classifyPair l s1 s2 with
    | some fp => pairExtra fp + stmtsExtra l rest
    | none => stmtExtra l s1 + stmtsExtra l (s2 :: rest)
  | [s] => stmtExtra l s

def blockExtra (l : Layout) (b : Lir.Block) : Nat :=
  stmtsExtra l b.body.toList

def siteTemps : RcSite → Nat
  | .inc .. => 2
  | .dec .. => 2
  | .alloc .. => 5
  | .reset _ _ _ lay _ mask => 2 + (deadFields lay.nobj mask).length
  | .resetU _ _ _ lay _ mask => (deadFields lay.nobj mask).length
  | .reuse .. => 1
  | .reuseU .. => 0

def pairTemps : RcPair → Nat
  | .fusedResetReuse .. => 3
  | .fusedResetUReuseU .. => 0

def stmtTemps (l : Layout) (s : Lir.Stmt) : Nat :=
  match classify l s with
  | none => 0
  | some site => siteTemps site

def stmtsTemps (l : Layout) : List Lir.Stmt → Nat
  | [] => 0
  | s1 :: s2 :: rest =>
    match classifyPair l s1 s2 with
    | some fp => pairTemps fp + stmtsTemps l rest
    | none => stmtTemps l s1 + stmtsTemps l (s2 :: rest)
  | [s] => stmtTemps l s

def blockTemps (l : Layout) (b : Lir.Block) : Nat :=
  stmtsTemps l b.body.toList

/-- New entry label of original block `i` in `F`. -/
def newLabel (l : Layout) (F : Lir.Func) (i : Nat) : Nat :=
  i + ((F.blocks.toList.map (blockExtra l)).take i).sum

/-- Relabel every outgoing edge of a terminator via `rel`. -/
def relabelEdge (rel : Lir.Label → Lir.Label) (e : Lir.Edge) : Lir.Edge :=
  { e with target := rel e.target }

def relabelTerm (rel : Lir.Label → Lir.Label) : Lir.Term → Lir.Term
  | .jump e => .jump (relabelEdge rel e)
  | .br c w a b t f => .br c w a b (relabelEdge rel t) (relabelEdge rel f)
  | .brOvf o x a b ok ovf => .brOvf o x a b (relabelEdge rel ok) (relabelEdge rel ovf)
  | .ret as => .ret as
  | .tail g as => .tail g as
  | .fail r => .fail r
  | .trap => .trap

/-! ## Expanding a single block -/

def cellAddr (x : Lir.VReg) (off : Int := 0) : Lir.Addr :=
  { base := some (.v x), disp := off }

def ctxAddr (off : Int) : Lir.Addr :=
  { base := some .ctx, disp := off }

def mkFieldStores (dst : Lir.VReg) : Nat → List Lir.Arg → List Lir.Stmt
  | _, [] => []
  | j, a :: rest =>
    .store .w64 (cellAddr dst (Int.ofNat (8 * (j + 1)))) a :: mkFieldStores dst (j + 1) rest

def mkShellStores (x : Lir.VReg) (hdr : UInt64) (n : Nat) : List Lir.Stmt :=
  .store .w64 (cellAddr x 0) (.imm hdr) ::
    (List.range n).map fun j =>
      .store .w64 (cellAddr x (Int.ofNat (8 * (j + 1)))) (.imm 1)

def mkDeadLoads (x : Lir.VReg) (baseTmp : Lir.VReg) : List Nat → List Lir.Stmt
  | [] => []
  | j :: rest =>
    .assign baseTmp (.load .w64 .zero (cellAddr x (Int.ofNat (8 * (j + 1))))) ::
      mkDeadLoads x (baseTmp + 1) rest

def mkDeadDecs (decProc : Nat) (baseTmp : Lir.VReg) : List Nat → List Lir.Stmt
  | [] => []
  | _ :: rest =>
    .call [] decProc [.v baseTmp] :: mkDeadDecs decProc (baseTmp + 1) rest

/-- Expand a single Lir statement into emitted closed blocks plus updated open-block state
`(prefixBlocks, cur', nextTmp', params', acc')`. -/
def stepSingle (l : Layout) (cold : Bool) (s : Lir.Stmt) (cur : Lir.Label) (nextTmp : Lir.VReg)
    (params : List Lir.VReg) (acc : List Lir.Stmt) :
    List Lir.Block × Lir.Label × Lir.VReg × List Lir.VReg × List Lir.Stmt :=
  match classify l s with
  | none => ([], cur, nextTmp, params, s :: acc)
  | some (.inc dst x) =>
    let t0 := nextTmp
    let t1 := nextTmp + 1
    let joinLbl := cur + 5
    let maxMinus1 := UInt64.ofNat (Rt.Rc.maxCount - 1)
    let b0 : Lir.Block :=
      { params, body := acc.reverse.toArray
        term := .br .tnz .w64 (.v x) (.imm 1) ⟨joinLbl, []⟩ ⟨cur + 1, []⟩
        cold }
    let b1 : Lir.Block :=
      { body := #[Lir.Stmt.assign t0 (.load .w32 .zero (cellAddr x 4))]
        term := .br .ult .w32 (.v t0) (.imm maxMinus1) ⟨cur + 2, []⟩ ⟨cur + 3, []⟩
        cold }
    let b2 : Lir.Block :=
      { body := #[Lir.Stmt.assign t1 (.bin .add .w32 (.v t0) (.imm 1)),
          Lir.Stmt.store .w32 (cellAddr x 4) (.v t1)]
        term := .jump ⟨joinLbl, []⟩
        cold }
    let b3 : Lir.Block :=
      { body := #[]
        term := .br .eq .w32 (.v t0) (.imm maxMinus1) ⟨cur + 4, []⟩ ⟨joinLbl, []⟩
        cold := true }
    let b4 : Lir.Block :=
      { body := #[]
        term := .fail .heap
        cold := true }
    ([b0, b1, b2, b3, b4], joinLbl, nextTmp + 2, [], [Lir.Stmt.assign dst (.arg (.imm 1))])
  | some (.dec dst x) =>
    let t0 := nextTmp
    let t1 := nextTmp + 1
    let joinLbl := cur + 5
    let b0 : Lir.Block :=
      { params, body := acc.reverse.toArray
        term := .br .tnz .w64 (.v x) (.imm 1) ⟨joinLbl, []⟩ ⟨cur + 1, []⟩
        cold }
    let b1 : Lir.Block :=
      { body := #[Lir.Stmt.assign t0 (.load .w32 .zero (cellAddr x 4))]
        term := .br .eq .w32 (.v t0) (.imm 0) ⟨cur + 2, []⟩ ⟨cur + 3, []⟩
        cold }
    let b2 : Lir.Block :=
      { body := #[Lir.Stmt.call [] l.decProc [.v x]]
        term := .jump ⟨joinLbl, []⟩
        cold }
    let b3 : Lir.Block :=
      { body := #[]
        term := .br .slt .w32 (.v t0) (.imm 0) ⟨joinLbl, []⟩ ⟨cur + 4, []⟩
        cold }
    let b4 : Lir.Block :=
      { body := #[Lir.Stmt.assign t1 (.bin .sub .w32 (.v t0) (.imm 1)),
          Lir.Stmt.store .w32 (cellAddr x 4) (.v t1)]
        term := .jump ⟨joinLbl, []⟩
        cold }
    ([b0, b1, b2, b3, b4], joinLbl, nextTmp + 2, [], [Lir.Stmt.assign dst (.arg (.imm 1))])
  | some (.alloc dst _ lay cls args) =>
    let t0 := nextTmp
    let t1 := nextTmp + 1
    let t2 := nextTmp + 2
    let t3 := nextTmp + 3
    let t4 := nextTmp + 4
    let pubLbl := cur + 6
    let headOff := Int.ofNat (8 * cls)
    let bytes := UInt64.ofNat (Rt.Rc.classBytes cls)
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    let b0 : Lir.Block :=
      { params
        body := (Lir.Stmt.assign t0 (.load .w64 .zero (ctxAddr headOff)) :: acc).reverse.toArray
        term := .br .eq .w64 (.v t0) (.imm 0) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩
        cold }
    let b1 : Lir.Block :=
      { body := #[Lir.Stmt.assign t1 (.load .w64 .zero (cellAddr t0)),
          Lir.Stmt.store .w64 (ctxAddr headOff) (.v t1)]
        term := .jump ⟨pubLbl, [.v t0]⟩
        cold }
    let b2 : Lir.Block :=
      { body := #[Lir.Stmt.assign t2 (.load .w64 .zero (ctxAddr Rt.bumpOff)),
          Lir.Stmt.assign t3 (.load .w64 .zero (ctxAddr Rt.limitOff))]
        term := .brOvf .addC t4 (.v t2) (.imm bytes) ⟨cur + 3, []⟩ ⟨cur + 5, []⟩
        cold }
    let b3 : Lir.Block :=
      { body := #[]
        term := .br .ule .w64 (.v t4) (.v t3) ⟨cur + 4, []⟩ ⟨cur + 5, []⟩
        cold }
    let b4 : Lir.Block :=
      { body := #[Lir.Stmt.store .w64 (ctxAddr Rt.bumpOff) (.v t4)]
        term := .jump ⟨pubLbl, [.v t2]⟩
        cold }
    let b5 : Lir.Block :=
      { body := #[]
        term := .fail .heap
        cold := true }
    let pubInit : List Lir.Stmt :=
      Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: mkFieldStores dst 0 args
    ([b0, b1, b2, b3, b4, b5], pubLbl, nextTmp + 5, [dst], pubInit.reverse)
  | some (.reset dst x idx lay cls mask) =>
    let t0 := nextTmp
    let tRes := nextTmp + 1
    let dead := deadFields lay.nobj mask
    let joinLbl := cur + 4
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    let hotBody : List Lir.Stmt :=
      mkDeadLoads x (nextTmp + 2) dead ++
        mkShellStores x hdr lay.nobj ++
        mkDeadDecs l.decProc (nextTmp + 2) dead
    let b0 : Lir.Block :=
      { params, body := acc.reverse.toArray
        term := .br .tnz .w64 (.v x) (.imm 1) ⟨cur + 3, []⟩ ⟨cur + 1, []⟩
        cold }
    let b1 : Lir.Block :=
      { body := #[Lir.Stmt.assign t0 (.load .w32 .zero (cellAddr x 4))]
        term := .br .eq .w32 (.v t0) (.imm 0) ⟨cur + 2, []⟩ ⟨cur + 3, []⟩
        cold }
    let b2 : Lir.Block :=
      { body := hotBody.toArray
        term := .jump ⟨joinLbl, [.v x]⟩
        cold }
    let b3 : Lir.Block :=
      { body := #[.call [tRes] (l.resetWrapper idx) [.v x, .imm mask]]
        term := .jump ⟨joinLbl, [.v tRes]⟩
        cold := true }
    ([b0, b1, b2, b3], joinLbl, nextTmp + 2 + dead.length, [dst], [])
  | some (.resetU dst x _ lay cls mask) =>
    let dead := deadFields lay.nobj mask
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    let bodyStmts : List Lir.Stmt :=
      mkDeadLoads x nextTmp dead ++
        mkShellStores x hdr lay.nobj ++
        mkDeadDecs l.decProc nextTmp dead ++
        [.assign dst (.arg (.v x))]
    ([], cur, nextTmp + dead.length, params, bodyStmts.reverse ++ acc)
  | some (.reuse dst slot idx lay cls args) =>
    let t0 := nextTmp
    let joinLbl := cur + 3
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    let b0 : Lir.Block :=
      { params, body := acc.reverse.toArray
        term := .br .tnz .w64 (.v slot) (.imm 1) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩
        cold }
    let b1 : Lir.Block :=
      { body := (.store .w64 (cellAddr slot 0) (.imm hdr) :: mkFieldStores slot 0 args).toArray
        term := .jump ⟨joinLbl, [.v slot]⟩
        cold }
    let b2 : Lir.Block :=
      { body := #[.call [t0] (l.reuseWrapper idx) (.v slot :: args)]
        term := .jump ⟨joinLbl, [.v t0]⟩
        cold := true }
    ([b0, b1, b2], joinLbl, nextTmp + 1, [dst], [])
  | some (.reuseU dst slot _ lay cls args) =>
    let hdr := Rt.Rc.dynamicHeader lay.nobj cls lay.tag 1
    let bodyStmts : List Lir.Stmt :=
      .store .w64 (cellAddr slot 0) (.imm hdr) ::
        mkFieldStores slot 0 args ++
        [.assign dst (.arg (.v slot))]
    ([], cur, nextTmp, params, bodyStmts.reverse ++ acc)

/-- Expand a fused adjacent `reset`+`reuse` pair into emitted closed blocks plus updated
open-block state. -/
def stepPair (l : Layout) (cold : Bool) (fp : RcPair) (cur : Lir.Label) (nextTmp : Lir.VReg)
    (params : List Lir.VReg) (acc : List Lir.Stmt) :
    List Lir.Block × Lir.Label × Lir.VReg × List Lir.VReg × List Lir.Stmt :=
  match fp with
  | .fusedResetUReuseU slot x dst lay2 cls args =>
    let hdr2 := Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1
    let fused : List Lir.Stmt :=
      .store .w64 (cellAddr x 0) (.imm hdr2) ::
        mkFieldStores x 0 args ++
        [.assign slot (.arg (.v x)), .assign dst (.arg (.v x))]
    ([], cur, nextTmp, params, fused.reverse ++ acc)
  | .fusedResetReuse slot x dst idx1 _ mask idx2 lay2 cls args =>
    let t0 := nextTmp
    let t1 := nextTmp + 1
    let t2 := nextTmp + 2
    let joinLbl := cur + 4
    let hdr2 := Rt.Rc.dynamicHeader lay2.nobj cls lay2.tag 1
    let b0 : Lir.Block :=
      { params, body := acc.reverse.toArray
        term := .br .tnz .w64 (.v x) (.imm 1) ⟨cur + 3, []⟩ ⟨cur + 1, []⟩
        cold }
    let b1 : Lir.Block :=
      { body := #[Lir.Stmt.assign t0 (.load .w32 .zero (cellAddr x 4))]
        term := .br .eq .w32 (.v t0) (.imm 0) ⟨cur + 2, []⟩ ⟨cur + 3, []⟩
        cold }
    let b2 : Lir.Block :=
      { body := (.store .w64 (cellAddr x 0) (.imm hdr2) :: mkFieldStores x 0 args).toArray
        term := .jump ⟨joinLbl, [.v x, .v x]⟩
        cold }
    let b3 : Lir.Block :=
      { body := #[
          .call [t1] (l.resetWrapper idx1) [.v x, .imm mask],
          .call [t2] (l.reuseWrapper idx2) (.v t1 :: args)]
        term := .jump ⟨joinLbl, [.v t1, .v t2]⟩
        cold := true }
    ([b0, b1, b2, b3], joinLbl, nextTmp + 3, [slot, dst], [])

/-- Expand a list of statements within one original block, returning the list of
emitted blocks (in label order) and the next fresh temporary register.
Invariant: `cur` is the label of the currently open block, `params` its block
parameters, `acc` its reversed statements so far, `cold` its coldness flag. -/
def expandStmts (l : Layout) (rel : Lir.Label → Lir.Label) (term : Lir.Term) (cold : Bool)
    (stmts : List Lir.Stmt) (cur : Lir.Label) (nextTmp : Lir.VReg) (params : List Lir.VReg)
    (acc : List Lir.Stmt) : List Lir.Block × Lir.VReg :=
  match stmts with
  | [] =>
    ([{ params, body := acc.reverse.toArray, term := relabelTerm rel term, cold }], nextTmp)
  | s1 :: rest =>
    match rest with
    | s2 :: rest2 =>
      match classifyPair l s1 s2 with
      | some fp =>
        let (pre, cur', nextTmp', params', acc') := stepPair l cold fp cur nextTmp params acc
        let (tail, finalTmp) := expandStmts l rel term cold rest2 cur' nextTmp' params' acc'
        (pre ++ tail, finalTmp)
      | none =>
        let (pre, cur', nextTmp', params', acc') := stepSingle l cold s1 cur nextTmp params acc
        let (tail, finalTmp) := expandStmts l rel term cold (s2 :: rest2) cur' nextTmp' params' acc'
        (pre ++ tail, finalTmp)
    | [] =>
      let (pre, cur', nextTmp', params', acc') := stepSingle l cold s1 cur nextTmp params acc
      let (tail, finalTmp) := expandStmts l rel term cold [] cur' nextTmp' params' acc'
      (pre ++ tail, finalTmp)
termination_by stmts.length

def expandBlock (l : Layout) (rel : Lir.Label → Lir.Label) (cur : Lir.Label) (nextTmp : Lir.VReg)
    (b : Lir.Block) : List Lir.Block × Lir.VReg :=
  expandStmts l rel b.term b.cold b.body.toList cur nextTmp b.params []

def expandBlocks (l : Layout) (rel : Lir.Label → Lir.Label) :
    List Lir.Block → Lir.Label → Lir.VReg → List Lir.Block
  | [], _, _ => []
  | b :: bs, cur, nextTmp =>
    let (emitted, nextTmp') := expandBlock l rel cur nextTmp b
    emitted ++ expandBlocks l rel bs (cur + 1 + blockExtra l b) nextTmp'

/-- Inline all RC fast paths in one Lir function. -/
def inlineFunc (l : Layout) (F : Lir.Func) : Lir.Func :=
  let rel := newLabel l F
  { F with blocks := (expandBlocks l rel F.blocks.toList 0 (freshBase F)).toArray }

/-- Inline RC fast paths in all source functions (`f < l.sourceCount`), leaving
every runtime wrapper and procedure (`f ≥ l.sourceCount`) unchanged. -/
def inlineProgram (l : Layout) (p : Lir.Program) : Lir.Program :=
  { p with
    funcs := p.funcs.mapIdx fun i F =>
      if i < l.sourceCount then inlineFunc l F else F }

end IxCC.Cfg.Rc.Inline
