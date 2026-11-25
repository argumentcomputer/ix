import IxCC.Cfg.Rc.Inline
import IxCC.Cfg.Rc.Prune

/-! # Inline RC & Alloc Fast Paths Inside Surviving Reset/Reuse Wrappers

Runs after `Prune.pruneUnusedReuse` on every surviving (unpruned) wrapper in
`(l.isUniqueProc, l.init + 4 + 4 * l.ctors.length)` (`resetWrapper`,
`resetUWrapper`, `reuseWrapper`, `reuseUWrapper`).

Replaces every call to:
- `l.isUniqueProc` (2-block inline `tnz` + `rc == 0` check, zero calls)
- `l.incProc` (5-block inline `inc` fast path, zero calls)
- `l.decProc` (5-block inline `dec` fast path; only calls `l.decProc` on `rc == 0`)
- `l.allocProc idx` (6-block inline free-list pop / bump-pointer + header store, zero calls)

This turns `reuseWrapper` into a 100% leaf function (zero spills/prologue) and
eliminates all 7 out-of-line leaf calls on the shared path of `resetWrapper`. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.InlineWrappers

open IxCC.Cfg.Rc.Native
open IxCC.Cfg.Rc.Inline (cellAddr ctxAddr relabelTerm freshBase)

/-! ## Wrapper call-site classification -/

inductive WrapperSite
  | isUnique (dst x : Lir.VReg)
  | inc (x : Lir.VReg)
  | dec (x : Lir.VReg)
  | alloc (dst : Lir.VReg) (idx : Nat) (lay : Rt.Rc.CellLayout) (cls : Nat)
  deriving DecidableEq, Repr

def classify (l : Layout) (s : Lir.Stmt) : Option WrapperSite :=
  match s with
  | .call [dst] g [.v x] =>
    if g == l.isUniqueProc && dst != x then
      some (.isUnique dst x)
    else
      none
  | .call [] g [.v x] =>
    if g == l.incProc then
      some (.inc x)
    else if g == l.decProc then
      some (.dec x)
    else
      none
  | .call [dst] g [] =>
    if l.incProc + 2 ≤ g && g < l.init then
      let idx := g - (l.incProc + 2)
      match l.ctors[idx]? with
      | some c =>
        let lay := Rt.Rc.CellLayout.ofFields c.arity c.tag
        if lay.ok then
          match lay.cls? with
          | some cls => some (.alloc dst idx lay cls)
          | none => none
        else
          none
      | none => none
    else
      none
  | _ => none

/-- Find the unique classified wrapper call in a block body (if there is exactly one). -/
def findUniqueSite (l : Layout) :
    List Lir.Stmt → Option (List Lir.Stmt × WrapperSite × List Lir.Stmt)
  | [] => none
  | s :: rest =>
    match classify l s with
    | some site =>
      if rest.all (fun s' => (classify l s').isNone) then
        some ([], site, rest)
      else
        none
    | none =>
      match findUniqueSite l rest with
      | some (pre, site, post) => some (s :: pre, site, post)
      | none => none

def siteExtra : WrapperSite → Nat
  | .isUnique .. => 3
  | .inc .. => 5
  | .dec .. => 5
  | .alloc .. => 6

def siteTemps : WrapperSite → Nat
  | .isUnique .. => 1
  | .inc .. => 2
  | .dec .. => 2
  | .alloc .. => 5

def sitePostOff : WrapperSite → Nat
  | .alloc .. => 1
  | _ => 0

def blockExtra (l : Layout) (b : Lir.Block) : Nat :=
  match findUniqueSite l b.body.toList with
  | none => 0
  | some (_, site, _) => siteExtra site

def blockTemps (l : Layout) (b : Lir.Block) : Nat :=
  match findUniqueSite l b.body.toList with
  | none => 0
  | some (_, site, _) => siteTemps site

/-- New entry label of original block `i` in `F`. -/
def newLabel (l : Layout) (F : Lir.Func) (i : Nat) : Nat :=
  i + ((F.blocks.toList.map (blockExtra l)).take i).sum

/-! ## Block expansion -/

def expandSite (l : Layout) (rel : Lir.Label → Lir.Label) (b : Lir.Block)
    (cur : Lir.Label) (nextTmp : Lir.VReg)
    (pre : List Lir.Stmt) (site : WrapperSite) (post : List Lir.Stmt) : List Lir.Block :=
  let term' := relabelTerm rel b.term
  match site with
  | .isUnique dst x =>
    let t0 := nextTmp
    let joinLbl := cur + 3
    let b0 : Lir.Block :=
      { params := b.params, body := pre.toArray
        term := .br .tnz .w64 (.v x) (.imm 1) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩
        cold := b.cold }
    let b1 : Lir.Block :=
      { body := #[Lir.Stmt.assign t0 (.load .w32 .zero (cellAddr x 4))]
        term := .br .eq .w32 (.v t0) (.imm 0) ⟨joinLbl, [.imm 1]⟩ ⟨cur + 2, []⟩
        cold := b.cold }
    let b2 : Lir.Block :=
      { body := #[]
        term := .jump ⟨joinLbl, [.imm 0]⟩
        cold := b.cold }
    let b3 : Lir.Block :=
      { params := [dst], body := post.toArray
        term := term'
        cold := b.cold }
    [b0, b1, b2, b3]
  | .inc x =>
    let t0 := nextTmp
    let t1 := nextTmp + 1
    let joinLbl := cur + 5
    let maxMinus1 := UInt64.ofNat (Rt.Rc.maxCount - 1)
    let b0 : Lir.Block :=
      { params := b.params, body := pre.toArray
        term := .br .tnz .w64 (.v x) (.imm 1) ⟨joinLbl, []⟩ ⟨cur + 1, []⟩
        cold := b.cold }
    let b1 : Lir.Block :=
      { body := #[Lir.Stmt.assign t0 (.load .w32 .zero (cellAddr x 4))]
        term := .br .ult .w32 (.v t0) (.imm maxMinus1) ⟨cur + 2, []⟩ ⟨cur + 3, []⟩
        cold := b.cold }
    let b2 : Lir.Block :=
      { body := #[Lir.Stmt.assign t1 (.bin .add .w32 (.v t0) (.imm 1)),
          Lir.Stmt.store .w32 (cellAddr x 4) (.v t1)]
        term := .jump ⟨joinLbl, []⟩
        cold := b.cold }
    let b3 : Lir.Block :=
      { body := #[]
        term := .br .eq .w32 (.v t0) (.imm maxMinus1) ⟨cur + 4, []⟩ ⟨joinLbl, []⟩
        cold := true }
    let b4 : Lir.Block :=
      { body := #[]
        term := .fail .heap
        cold := true }
    let b5 : Lir.Block :=
      { body := post.toArray
        term := term'
        cold := b.cold }
    [b0, b1, b2, b3, b4, b5]
  | .dec x =>
    let t0 := nextTmp
    let t1 := nextTmp + 1
    let joinLbl := cur + 5
    let b0 : Lir.Block :=
      { params := b.params, body := pre.toArray
        term := .br .tnz .w64 (.v x) (.imm 1) ⟨joinLbl, []⟩ ⟨cur + 1, []⟩
        cold := b.cold }
    let b1 : Lir.Block :=
      { body := #[Lir.Stmt.assign t0 (.load .w32 .zero (cellAddr x 4))]
        term := .br .eq .w32 (.v t0) (.imm 0) ⟨cur + 2, []⟩ ⟨cur + 3, []⟩
        cold := b.cold }
    let b2 : Lir.Block :=
      { body := #[Lir.Stmt.call [] l.decProc [.v x]]
        term := .jump ⟨joinLbl, []⟩
        cold := true }
    let b3 : Lir.Block :=
      { body := #[]
        term := .br .slt .w32 (.v t0) (.imm 0) ⟨joinLbl, []⟩ ⟨cur + 4, []⟩
        cold := b.cold }
    let b4 : Lir.Block :=
      { body := #[Lir.Stmt.assign t1 (.bin .sub .w32 (.v t0) (.imm 1)),
          Lir.Stmt.store .w32 (cellAddr x 4) (.v t1)]
        term := .jump ⟨joinLbl, []⟩
        cold := b.cold }
    let b5 : Lir.Block :=
      { body := post.toArray
        term := term'
        cold := b.cold }
    [b0, b1, b2, b3, b4, b5]
  | .alloc dst _ lay cls =>
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
      { params := b.params
        body := (pre ++ [Lir.Stmt.assign t0 (.load .w64 .zero (ctxAddr headOff))]).toArray
        term := .br .eq .w64 (.v t0) (.imm 0) ⟨cur + 2, []⟩ ⟨cur + 1, []⟩
        cold := false }
    let b1 : Lir.Block :=
      { body := #[Lir.Stmt.assign t1 (.load .w64 .zero (cellAddr t0)),
          Lir.Stmt.store .w64 (ctxAddr headOff) (.v t1)]
        term := .jump ⟨pubLbl, [.v t0]⟩
        cold := false }
    let b2 : Lir.Block :=
      { body := #[Lir.Stmt.assign t2 (.load .w64 .zero (ctxAddr Rt.bumpOff)),
          Lir.Stmt.assign t3 (.load .w64 .zero (ctxAddr Rt.limitOff))]
        term := .brOvf .addC t4 (.v t2) (.imm bytes) ⟨cur + 3, []⟩ ⟨cur + 5, []⟩
        cold := false }
    let b3 : Lir.Block :=
      { body := #[]
        term := .br .ule .w64 (.v t4) (.v t3) ⟨cur + 4, []⟩ ⟨cur + 5, []⟩
        cold := false }
    let b4 : Lir.Block :=
      { body := #[Lir.Stmt.store .w64 (ctxAddr Rt.bumpOff) (.v t4)]
        term := .jump ⟨pubLbl, [.v t2]⟩
        cold := false }
    let b5 : Lir.Block :=
      { body := #[]
        term := .fail .heap
        cold := true }
    let b6 : Lir.Block :=
      { params := [dst]
        body := (Lir.Stmt.store .w64 (cellAddr dst) (.imm hdr) :: post).toArray
        term := term'
        cold := false }
    [b0, b1, b2, b3, b4, b5, b6]

def expandBlock (l : Layout) (rel : Lir.Label → Lir.Label) (cur : Lir.Label) (nextTmp : Lir.VReg)
    (b : Lir.Block) : List Lir.Block :=
  match findUniqueSite l b.body.toList with
  | none => [{ b with term := relabelTerm rel b.term }]
  | some (pre, site, post) => expandSite l rel b cur nextTmp pre site post

def expandBlocks (l : Layout) (rel : Lir.Label → Lir.Label) :
    List Lir.Block → Lir.Label → Lir.VReg → List Lir.Block
  | [], _, _ => []
  | b :: bs, cur, nextTmp =>
    expandBlock l rel cur nextTmp b ++
      expandBlocks l rel bs (cur + 1 + blockExtra l b) (nextTmp + blockTemps l b)

/-- Inline all wrapper runtime calls inside one reuse/reset wrapper function. -/
def inlineFunc (l : Layout) (F : Lir.Func) : Lir.Func :=
  let rel := newLabel l F
  { F with blocks := (expandBlocks l rel F.blocks.toList 0 (freshBase F)).toArray }

/-- Transform every function in the reuse-wrapper slice `(l.isUniqueProc, l.init + 4 + 4 * l.ctors.length)`.
Pruned `.trap` stubs have no calls and pass through unchanged. -/
def inlineProgram (l : Layout) (p : Lir.Program) : Lir.Program :=
  { p with
    funcs := p.funcs.mapIdx fun i F =>
      if Prune.isPrunableReuse l i then inlineFunc l F else F }

end IxCC.Cfg.Rc.InlineWrappers
