import IxCC.Cfg.Rc.Syntax
import IxCC.Rt.Lower
import IxCC.Fir.Shape

/-!
# Raw 64-bit words on the reference-counted route (`Cfg.Rc.Raw`)

Design note `plans/ONE-PIPELINE.md`, sections 2.4 and 2.5 (lane `rc-raw-words`).

A register of a function is *raw* when it holds the untagged 64-bit word `n` of a `UInt64`
(`n < 2^64`) instead of the tagged immediate `2n + 1`, which exists only below `2^63`. Raw
registers have no tag operation and no `natOverflow` test, so a `UInt64` computation runs over
its whole range. The layout (`RawLayout`, on `Program.raw`) is a function of the checked shape
certificate: `infer` proposes the registers whose shape's native slot is the 64-bit raw word
(`Shape.slot σ = .raw .w64`) and demotes, until `rawOk` holds, every one that meets a position
that reads a tagged word. Nothing in it is trusted.

**What the native lowering relies on is `rawOk`**, which `Cfg.Rc.Native.lower` checks: a raw
register is read only by a 64-bit word operation, by a copy into a raw register, as the
argument of a raw parameter (of a block, a callee or a tail callee) and by the return of a
function whose result is raw; it is written only by those, by a call of a function whose result
is raw, and as a raw parameter. An exported function has no raw parameter and no raw result.
So every other construct reads and writes tagged words exactly as before, and the value a raw
register holds is always a `Nat` literal below `2^64`: a word operation's result is one, and
each flow into a raw position carries one. The soundness of the layout rests on this check and
on the primitives' meaning, not on the shape certificate.

The tables the lowering reads (`Rt.Lower.Tables.rawVar`, `rawParams`, `rawRet`) come from the
layout by `rawTables`. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open IxCC.Fir (Arg)

namespace Raw

/-- The raw flags of block `b`'s parameters in function `f` of `C` (block 0: the function's). -/
def paramsOf (L : RawLayout) (C : Cfg.Program) (f b : Nat) : List Bool :=
  match C.fun? f with
  | some fd =>
    match fd.blocks[b]? with
    | some blk => blk.params.map fun p => L.isRaw f p.1
    | none => []
  | none => []

/-- The lowering's tables with a raw layout over the program `C` it lowers. -/
def rawTables (L : RawLayout) (C : Cfg.Program) (T : Rt.Lower.Tables) : Rt.Lower.Tables :=
  { T with
    rawVar := L.isRaw
    rawParams := paramsOf L C
    rawRet := L.retRaw }

/-! ## The native flow check -/

/-- An argument may flow to a position whose raw flag is `r`: a register only when its own flag
is `r`. A literal fits either (at a raw position the lowering takes it below `2^64` and fails
with `natOverflow` otherwise); `□` and a string literal never reach a raw register (the lowering
of a raw position fails on them). -/
def argFits (R : Nat → Bool) (r : Bool) : Arg → Bool
  | .var y => R y == r
  | _ => true

/-- Arguments at positions with the given flags (a missing flag is `false`), in the order
`Rt.Lower.operandsAt` reads them. -/
def argsFit (R : Nat → Bool) : List Bool → List Arg → Bool
  | _, [] => true
  | rs, a :: as => argFits R (rs.headD false) a && argsFit R rs.tail as

/-- A binding's flows. -/
def instrOk (L : RawLayout) (C : Cfg.Program) (f : Nat) : Cfg.Instr → Bool
  | .bind _ (.fir (.prim (.word .w64 _) _)) => true
  | .bind x (.fir (.arg a)) => argFits (L.isRaw f) (L.isRaw f x) a
  | .bind x (.fir (.call g as)) =>
    argsFit (L.isRaw f) (paramsOf L C g 0) as && (L.isRaw f x == L.retRaw g)
  | .bind x rhs => !L.isRaw f x && (Cfg.Check.rhsVars rhs).all fun y => !L.isRaw f y

/-- An edge's arguments against its target block's parameters. -/
def edgeOk (L : RawLayout) (C : Cfg.Program) (f : Nat) (e : Cfg.Edge) : Bool :=
  argsFit (L.isRaw f) (paramsOf L C f e.target) e.args

/-- A terminator's flows. -/
def termOk (L : RawLayout) (C : Cfg.Program) (f : Nat) : Cfg.Term → Bool
  | .jump e => edgeOk L C f e
  | .switch x alts d => !L.isRaw f x && (alts.map (·.2) ++ d.toList).all (edgeOk L C f)
  | .ret a => argFits (L.isRaw f) (L.retRaw f) a
  | .tcall g as => argsFit (L.isRaw f) (paramsOf L C g 0) as && (L.retRaw g == L.retRaw f)
  | .trap => true

def blockOk (L : RawLayout) (C : Cfg.Program) (f : Nat) (b : Cfg.Block) : Bool :=
  b.body.all (instrOk L C f) && termOk L C f b.term

/-- An exported function has no raw parameter and no raw result. -/
def exportOk (L : RawLayout) (C : Cfg.Program) (f : Nat) : Bool :=
  (paramsOf L C f 0).all (· == false) && !L.retRaw f

/-- An instruction that touches a heap cell: an allocation of a constructor with fields, a
projection other than the `Nat` successor's, or a call of a runtime procedure past the
increment and decrement markers (`size`, `size + 1`): before consumption the reset and reuse
markers (`size + 2`, `size + 3`), after it the allocation, reset and reuse wrappers. -/
def heapInstr (C : Cfg.Program) : Cfg.Instr → Bool
  | .bind _ (.alloc c _ _) => c.arity != 0
  | .bind _ (.proj _ c _) => C.known.natSucc != some c
  | .bind _ (.fir (.call g _)) => decide (C.size + 2 ≤ g)
  | _ => false

/-- Whether the layout gives function `f` a raw register or a raw result. -/
def hasRaw (L : RawLayout) (f : Nat) : Bool := !(L.vars.getD f []).isEmpty || L.retRaw f

/-- A function with a raw register or result has no heap-cell instruction. (Raw registers in
functions that allocate are a later step: their proofs would thread the raw relation through
every heap construct.) -/
def heapFree (C : Cfg.Program) (fd : Cfg.Fun) : Bool :=
  fd.blocks.all fun b => b.body.all fun i => !heapInstr C i

/-- One function's part of the check. -/
def funOk (L : RawLayout) (C : Cfg.Program) (f : Nat) (fd : Cfg.Fun) : Bool :=
  fd.blocks.all (blockOk L C f) && (!hasRaw L f || heapFree C fd)

/-- **The native flow check of a raw layout over the program it lowers.** No function returns a
raw word yet (`rets` is empty): a result goes tagged, which is a later step. -/
def rawOk (L : RawLayout) (C : Cfg.Program) : Bool :=
  (List.range C.size).all (fun f =>
    match C.fun? f with
    | some fd => funOk L C f fd
    | none => true) &&
  C.exports.all (exportOk L C) && L.rets.isEmpty


/-- **The admission gate of this step**: the reference-counted route accepts only the empty
layout. The lowering, the flow check and the producer are in place; the physical proofs do not
yet carry raw registers through every construct (`Cfg.Rc.Proof.Physical.Bridge.RawWords` is the
relation they will carry), so a non-empty layout is refused rather than compiled unproved. -/
def emptyLayout (L : RawLayout) : Bool :=
  (match L.vars with
    | .leaf => true
    | _ => false) && L.rets.isEmpty

theorem emptyLayout_isRaw {L : RawLayout} (h : emptyLayout L = true) (f x : Nat) :
    L.isRaw f x = false := by
  unfold emptyLayout at h
  unfold RawLayout.isRaw
  split at h
  · rename_i hv
    simp [hv, Src.NatMap.getD, Src.NatMap.get?]
  · simp at h

theorem emptyLayout_retRaw {L : RawLayout} (h : emptyLayout L = true) (f : Nat) :
    L.retRaw f = false := by
  unfold emptyLayout at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  simp [RawLayout.retRaw, h.2]
/-! ## The untrusted producer -/

/-- A shape held natively as a 64-bit raw word. -/
def raw64 (σ : Shape.Shape) : Bool := σ.slot == .raw .w64

mutual
/-- The join points of a body with their parameters. -/
def joinParams : Fir.Code → List (Fir.JoinId × List Fir.Var)
  | .bind _ _ k => joinParams k
  | .jp j ps _ b k => (j, ps) :: joinParams b ++ joinParams k
  | .case _ alts d => joinParamsAlts alts ++ joinParamsOpt d
  | .jmp .. | .ret _ | .tcall .. | .trap => []
def joinParamsAlts : List Fir.Alt → List (Fir.JoinId × List Fir.Var)
  | [] => []
  | .mk _ b :: rest => joinParams b ++ joinParamsAlts rest
def joinParamsOpt : Option Fir.Code → List (Fir.JoinId × List Fir.Var)
  | none => []
  | some c => joinParams c
end

/-- The registers of one function whose shape is a 64-bit word: its variables, its parameters
and its join points' parameters by position. -/
def seedFun (fd : Fir.Fun) (fs : Fir.Shape.FunShapes) : List Nat :=
  let ps := (fd.params.zip fs.params).filterMap fun (p, σ) => if raw64 σ then some p.1 else none
  let vs := fs.vars.toList.filterMap fun (x, σ) => if raw64 σ then some x else none
  let js := (joinParams fd.body).flatMap fun (j, xs) =>
    (xs.zip (fs.join j)).filterMap fun (x, σ) => if raw64 σ then some x else none
  ps ++ vs ++ js

/-- The proposal before demotion. -/
def seed (F : Fir.Program) (sc : Fir.Shape.ShapeCert) : RawLayout :=
  { vars := Src.NatMap.ofList (F.funList.map fun (f, fd) => (f, seedFun fd (sc.fn f)))
    rets := [] }

/-- What one violated flow demotes: registers of a function, and functions whose result goes
tagged. -/
structure Demote where
  vars : List (Nat × Nat) := []
  rets : List Nat := []

def Demote.append (a b : Demote) : Demote := ⟨a.vars ++ b.vars, a.rets ++ b.rets⟩

/-- At a position with flag `r` an argument that does not fit: demote the raw side (the register
if it is raw, else the position, which is the parameter `p` when the position names one). -/
def demoteArg (P : Program) (f : Nat) (r : Bool) (param : Option (Nat × Nat)) (a : Arg) : Demote :=
  if argFits (P.raw.isRaw f) r a then {} else
    match a with
    | .var y => if P.raw.isRaw f y then { vars := [(f, y)] } else
      match param with
      | some fp => { vars := [fp] }
      | none => {}
    | _ => {}

def demoteArgs (P : Program) (f : Nat) (g : Nat) (ps : List Nat) (rs : List Bool) : List Arg → Demote
  | [] => {}
  | a :: as => (demoteArg P f (rs.headD false) ((ps.head?).map (g, ·)) a).append
      (demoteArgs P f g ps.tail rs.tail as)

/-- The parameters of block `b` of function `g`. -/
def paramNames (P : Program) (g b : Nat) : List Nat :=
  match P.base.fun? g with
  | some fd => match fd.blocks[b]? with
    | some blk => blk.params.map (·.1)
    | none => []
  | none => []

def demoteInstr (P : Program) (f : Nat) : Cfg.Instr → Demote
  | .bind _ (.fir (.prim (.word .w64 _) _)) => {}
  | .bind x (.fir (.arg a)) =>
    let r := P.raw.isRaw f x
    if argFits (P.raw.isRaw f) r a then {} else
      match a with
      | .var y => if r then { vars := [(f, x)] } else { vars := [(f, y)] }
      | _ => {}
  | .bind x (.fir (.call g as)) =>
    let d := demoteArgs P f g (paramNames P g 0) (paramsOf P.raw P.base g 0) as
    if P.raw.isRaw f x == P.raw.retRaw g then d
    else d.append (if P.raw.isRaw f x then { vars := [(f, x)] } else { rets := [g] })
  | .bind x rhs =>
    { vars := (if P.raw.isRaw f x then [(f, x)] else []) ++
        ((Cfg.Check.rhsVars rhs).filter (P.raw.isRaw f)).map (f, ·) }

def demoteTerm (P : Program) (f : Nat) : Cfg.Term → Demote
  | .jump e => demoteArgs P f f (paramNames P f e.target) (paramsOf P.raw P.base f e.target) e.args
  | .switch x alts d =>
    let es := (alts.map (·.2) ++ d.toList).foldl (fun acc e =>
      acc.append (demoteArgs P f f (paramNames P f e.target) (paramsOf P.raw P.base f e.target) e.args)) {}
    if P.raw.isRaw f x then es.append { vars := [(f, x)] } else es
  | .ret a =>
    if argFits (P.raw.isRaw f) (P.raw.retRaw f) a then {} else
      if P.raw.retRaw f then { rets := [f] } else
        match a with
        | .var y => { vars := [(f, y)] }
        | _ => {}
  | .tcall g as =>
    let d := demoteArgs P f g (paramNames P g 0) (paramsOf P.raw P.base g 0) as
    if P.raw.retRaw g == P.raw.retRaw f then d
    else d.append { rets := [if P.raw.retRaw g then g else f] }
  | .trap => {}

def demoteExport (P : Program) (f : Nat) : Demote :=
  { vars := (paramNames P f 0).filter (P.raw.isRaw f) |>.map (f, ·)
    rets := if P.raw.retRaw f then [f] else [] }

/-- A function with a heap-cell instruction loses every raw register and its raw result. -/
def demoteHeap (P : Program) (f : Nat) (fd : Cfg.Fun) : Demote :=
  if heapFree P.base fd then {} else
    { vars := (P.raw.vars.getD f []).map (f, ·), rets := if P.raw.retRaw f then [f] else [] }

def demotions (P : Program) : Demote :=
  let funs := (List.range P.base.size).foldl (fun acc f =>
    match P.base.fun? f with
    | some fd => (fd.blocks.foldl (fun acc b =>
        (b.body.foldl (fun acc i => acc.append (demoteInstr P f i)) acc).append (demoteTerm P f b.term))
          acc).append (demoteHeap P f fd)
    | none => acc) {}
  P.base.exports.foldl (fun acc f => acc.append (demoteExport P f)) funs

def removeDemoted (L : RawLayout) (d : Demote) : RawLayout :=
  { vars := d.vars.foldl (fun m (f, x) => m.insert f ((m.getD f []).filter (· != x))) L.vars
    rets := L.rets.filter fun f => !d.rets.contains f }

/-- Demote until no flow is violated (each round with a violation removes at least one entry). -/
def settle : Nat → Program → Program
  | 0, P => P
  | fuel + 1, P =>
    let d := demotions P
    if d.vars.isEmpty && d.rets.isEmpty then P else settle fuel { P with raw := removeDemoted P.raw d }

/-- **The producer**: the shape certificate's 64-bit word positions, demoted until the native
flow check holds; the empty layout if it does not settle. -/
def infer (F : Fir.Program) (sc : Fir.Shape.ShapeCert) (P : Program) : RawLayout :=
  let start := seed F sc
  let fuel := start.rets.length + (start.vars.toList.map (·.2.length)).foldl (· + ·) 0 + 1
  let settled := settle fuel { P with raw := start }
  if rawOk settled.raw settled.base then settled.raw else {}

end Raw

end IxCC.Cfg.Rc
