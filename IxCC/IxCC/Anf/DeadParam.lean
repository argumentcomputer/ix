import IxCC.Anf.Walk

/-! # P5: dead / erased parameter stripping (worker/wrapper)

Erasure keeps every binder slot and passes `□` for irrelevant arguments, so
polymorphic helpers such as `StateT.bind` (8 parameters, 4 erased) can exceed
the 7-register internal tail-call limit. After defunctionalisation (or on any
Anf program), `DeadParam.run` splits every non-root, non-dispatcher function
global with unused parameters into:

* a **worker** global (key `GKey.worker gd.key keep`) taking only the kept
  parameters (at least one, so arity > 0 is preserved), with parameter indices
  remapped and calls rewritten; and
* a **wrapper** global at the original id and arity that forwards its kept
  parameters to the worker.

Every saturated known call `call g as` across the program is rewritten directly
to `call w (filterMask keep as)`. In a `FirstOrder` program (after P8), no
function-valued `glob g` exists, so `Prune.run` immediately drops the wrapper
and dispatchers / narrowed arms tail-call the slim worker directly.

Deterministic, no certificate data. Kernel-evaluable: lists, `Src.NatMap`,
structural recursion. -/

namespace IxCC.Anf.DeadParam

/-- Keep elements of `xs` whose corresponding bit in `mask` is `true`. -/
def filterMask {α : Type} : List Bool → List α → List α
  | [], _ => []
  | _, [] => []
  | true :: bs, x :: xs => x :: filterMask bs xs
  | false :: bs, _ :: xs => filterMask bs xs

/-- Number of `true` bits in `mask`. -/
def countTrue : List Bool → Nat
  | [] => 0
  | true :: bs => countTrue bs + 1
  | false :: bs => countTrue bs

/-- Which parameters of `gd` to keep (parameter `i` at index `n - 1 - i` in
`gd.body`). At least one parameter is kept when `gd.ps` is non-empty so a
function global never turns into a 0-arity CAF. -/
def keepMask (gd : GDef) : List Bool :=
  let n := gd.ps.length
  let used := (List.range n).map fun i => decide (gd.body.occ (n - 1 - i) > 0)
  if used.any id then used
  else match n with
    | 0 => []
    | m + 1 => true :: List.replicate m false

/-- Whether `g` is split into a worker/wrapper pair, and its kept-parameter mask. -/
def candidate (P : Program) (g : GlobalId) (gd : GDef) : Option (List Bool) :=
  if P.roots.contains g || Walk.isDispatchKey gd.key || gd.ps.length ≤ 1 then none
  else
    let keep := keepMask gd
    if keep.any (!·) && keep.any id then some keep else none

/-- Map a single atom under `d` local binders, where outer indices follow
`rmask = keep.reverse`: local indices `< d` stay unchanged; kept parameter
index `idx` maps to `d + countTrue (rmask.take idx)`; dead indices never occur
in a checked body; out-of-scope indices `≥ rmask.length` stay out-of-scope
(`≥ d + countTrue rmask`). -/
def remapAtom (rmask : List Bool) (d : Nat) : Atom → Atom
  | .var j =>
    if j < d then .var j
    else
      let idx := j - d
      if idx < rmask.length then .var (d + countTrue (rmask.take idx))
      else .var (d + countTrue rmask + (idx - rmask.length))
  | a => a

def remapAtoms (rmask : List Bool) (d : Nat) : List Atom → List Atom
  | [] => []
  | a :: as => remapAtom rmask d a :: remapAtoms rmask d as

/-- Information recorded per stripped global: its worker id and kept mask. -/
abbrev Plan := Src.NatMap (GlobalId × List Bool)

mutual

/-- Remap parameter indices (when `rmask` is `some m`) and redirect known calls
according to `plan`, under `d` local binders. -/
def rewriteExp (plan : Plan) (rmask : Option (List Bool)) (d : Nat) : Exp → Exp
  | .bind c b e => .bind c (rewriteBind plan rmask d b) (rewriteExp plan rmask (d + 1) e)
  | .join n r b e => .join n r (rewriteExp plan rmask (d + n) b) (rewriteExp plan rmask d e)
  | .jump j as => .jump j (match rmask with | some m => remapAtoms m d as | none => as)
  | .case x alts dflt =>
    let x' := match rmask with | some m => remapAtom m d x | none => x
    .case x' (rewriteAlts plan rmask d alts) (rewriteOpt plan rmask d dflt)
  | .ret a => .ret (match rmask with | some m => remapAtom m d a | none => a)
  | .tick e => .tick (rewriteExp plan rmask d e)
  | .trap => .trap

def rewriteBind (plan : Plan) (rmask : Option (List Bool)) (d : Nat) : Bind → Bind
  | .atom a => .atom (match rmask with | some m => remapAtom m d a | none => a)
  | .con c as => .con c (match rmask with | some m => remapAtoms m d as | none => as)
  | .proj c i x => .proj c i (match rmask with | some m => remapAtom m d x | none => x)
  | .prim p as => .prim p (match rmask with | some m => remapAtoms m d as | none => as)
  | .glob g => .glob g
  | .call g as =>
    let as' := match rmask with | some m => remapAtoms m d as | none => as
    match plan.get? g with
    | some (w, keep) =>
      if as'.length == keep.length then .call w (filterMask keep as')
      else .call g as'
    | none => .call g as'
  | .app f as =>
    let f' := match rmask with | some m => remapAtom m d f | none => f
    let as' := match rmask with | some m => remapAtoms m d as | none => as
    .app f' as'
  | .fn ps b => .fn ps (rewriteExp plan rmask (d + ps.length) b)

def rewriteAlts (plan : Plan) (rmask : Option (List Bool)) (d : Nat) : List Alt → List Alt
  | [] => []
  | .mk k n b :: as => .mk k n (rewriteExp plan rmask (d + n) b) :: rewriteAlts plan rmask d as

def rewriteOpt (plan : Plan) (rmask : Option (List Bool)) (d : Nat) : Option Exp → Option Exp
  | none => none
  | some e => some (rewriteExp plan rmask d e)

end

/-- Parameter variables `var (n - 1), ..., var 0` filtered by `keep`. -/
def keptParamAtoms (n : Nat) (keep : List Bool) : List Atom :=
  filterMask keep ((List.range n).map fun i => .var (n - 1 - i))

/-- Wrapper body forwarding kept parameters to worker `w`. -/
def wrapperBody (w n : Nat) (keep : List Bool) : Exp :=
  .bind freshLet (.call w (keptParamAtoms n keep)) (.ret (.var 0))

/-- Plan the workers to create, in global-id order, starting at `next`. -/
def buildPlan (P : Program) : GlobalId → List (GlobalId × GDef) →
    List (GlobalId × GlobalId × GDef × List Bool)
  | _, [] => []
  | next, (g, gd) :: rest =>
    match candidate P g gd with
    | some keep => (g, next, gd, keep) :: buildPlan P (next + 1) rest
    | none => buildPlan P next rest

mutual

/-- Whether every `glob g` reference in `e` lies below `bound`. -/
def globBelow (bound : Nat) : Exp → Bool
  | .bind _ b e => globBelowBind bound b && globBelow bound e
  | .join _ _ b e => globBelow bound b && globBelow bound e
  | .jump .. | .ret _ | .trap => true
  | .case _ alts d => globBelowAlts bound alts && globBelowOpt bound d
  | .tick e => globBelow bound e

def globBelowBind (bound : Nat) : Bind → Bool
  | .glob g => decide (g < bound)
  | .fn _ b => globBelow bound b
  | _ => true

def globBelowAlts (bound : Nat) : List Alt → Bool
  | [] => true
  | .mk _ _ b :: as => globBelow bound b && globBelowAlts bound as

def globBelowOpt (bound : Nat) : Option Exp → Bool
  | none => true
  | some e => globBelow bound e

end

/-- **P5**: strip dead/erased parameters via worker/wrapper split and call
redirection. Unchanged when no global has strippable parameters. -/
def run (P : Program) : Program :=
  let entries := buildPlan P P.size P.globalList
  if entries.isEmpty || !P.globalList.all (fun (_, gd) => globBelow P.size gd.body) then P
  else
    let plan : Plan := Src.NatMap.ofList (entries.map fun (g, w, _, keep) => (g, (w, keep)))
    let oldGs := P.globalList.map fun (g, gd) =>
      match plan.get? g with
      | some (w, keep) => (g, { gd with body := wrapperBody w gd.ps.length keep })
      | none => (g, { gd with body := rewriteExp plan none 0 gd.body })
    let workers := entries.map fun (_, w, gd, keep) =>
      (w, { key := .worker gd.key keep
            ps := filterMask keep gd.ps
            result := gd.result
            body := rewriteExp plan (some keep.reverse) 0 gd.body })
    { P with globals := Src.NatMap.ofList (oldGs ++ workers), size := P.size + entries.length }

end IxCC.Anf.DeadParam
