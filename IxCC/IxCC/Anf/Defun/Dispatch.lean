import IxCC.Anf.Defun.Lift

/-! # P8, the dispatchers and the closure keys

The second half of P8 (`docs/closures-design.md`, "Dispatchers"). A
**closure source** is a global whose closures the program can build: an
escaping function global (no captures) or a lifted local function (its
captures first). For each source `s` and each `j < s.arity` the constructor
`clo s.key j` is a closure of `s` with `j` arguments supplied; its cell holds
the captures and then those arguments (`s.caps + j` fields), and it gets its
own tag, so that every dispatcher's `case` tells its keys apart by tag alone
(`Rt.switchOk`: no default arm, distinct tests).

The dispatcher of arity `m` takes the callee and `m` arguments and cases on
the callee's key, one alternative per closure key, with no default (applying
a literal, a data constructor or □ is stuck, as in `applyN`). With the cell's
fields `fs` and `r = s.arity - j` parameters still missing, the alternative

* `m = r` calls `s` on `fs ++ as` (a tail call);
* `m < r` returns the cell `clo s.key (j + m)` of `fs ++ as`;
* `m > r` calls `s` on `fs` and the first `r` arguments, then the dispatcher of
  arity `m - r` on the result and the rest (a tail call).

This is `applyN` written as code. Kernel-evaluable (D17): lists only. -/

namespace IxCC.Anf.Defun

open IxCC.Ixon

/-- A closure source. -/
structure Source where
  /-- The key the closure constructors carry (`clo key j`). -/
  key : Key.GKey
  /-- The global the dispatchers call. -/
  id : GlobalId
  /-- Captured values, the first fields of every cell and parameters of `id`. -/
  caps : Nat
  /-- The parameters after the captures (at least one). -/
  arity : Nat
  deriving Repr, Inhabited, DecidableEq

/-- The variables of `count` consecutive binders in binding order, the
first-bound at index `top`: `var top, var (top - 1), …`. -/
def downFrom (top count : Nat) : List Atom := (List.range count).map fun t => .var (top - t)

/-- The constructor-table rows of the sources' closure keys, tags from `tag`
on, in source order and by supplied arguments. -/
def rows : List Source → Nat → List Lam.CtorInfo
  | [], _ => []
  | s :: ss, tag =>
    ((List.range s.arity).map fun j => { key := .clo s.key j, tag := tag + j, arity := s.caps + j }) ++
      rows ss (tag + s.arity)

/-- An atom under one more binder. -/
def shiftVar : Atom → Atom
  | .var i => .var (i + 1)
  | a => a

/-- The body of the alternative for `clo s.key j` in the dispatcher of arity
`m`, in a program of `size` globals: the cell's `F = s.caps + j` fields are
bound innermost (field `i` at `F - 1 - i`), the dispatcher's parameters
outside them (the callee at `F + m`, argument `t` at `F + m - 1 - t`). -/
def altBody (size : Nat) (s : Source) (j m : Nat) : Exp :=
  let F := s.caps + j
  let fs := downFrom (F - 1) F
  let as := downFrom (F + m - 1) m
  let r := s.arity - j
  if m = r then .bind freshLet (.call s.id (fs ++ as)) (.ret (.var 0))
  else if m < r then .bind freshLet (.con (.clo s.key (j + m)) (fs ++ as)) (.ret (.var 0))
  else
    .bind freshLet (.call s.id (fs ++ as.take r))
      (.bind freshLet (.call (dispId size (m - r)) (.var 0 :: (as.drop r).map shiftVar)) (.ret (.var 0)))

/-- The alternatives of the dispatcher of arity `m`, one per closure key. -/
def dispAlts (size : Nat) (m : Nat) : List Source → List Alt
  | [] => []
  | s :: ss =>
    ((List.range s.arity).map fun j => Alt.mk (.clo s.key j) (s.caps + j) (altBody size s j m)) ++
      dispAlts size m ss

/-- The dispatcher of arity `m`: the callee and `m` arguments, every
parameter with the plain contract. -/
def dispatcher (size : Nat) (srcs : List Source) (m : Nat) : GDef :=
  { key := .dispatch m, ps := List.replicate (m + 1) {}
    body := .case (.var m) (dispAlts size m srcs) none }

/-- The nodes of the alternative for `clo s.key j` in the dispatcher of arity
`m` (`(altBody size s j m).nodes`, without building it). -/
def altNodes (s : Source) (j m : Nat) : Nat :=
  s.caps + j + m + (if m > s.arity - j then 6 else 3)

/-- The nodes of the dispatcher of arity `m`, without building it, stopping
once the count passes `cap` (a loop over the sources). -/
def dispNodesUpTo (cap m : Nat) : List Source → Nat → Nat
  | [], acc => acc
  | s :: ss, acc =>
    let acc := (List.range s.arity).foldl (fun n j => n + altNodes s j m) acc
    if acc > cap then acc else dispNodesUpTo cap m ss acc

end IxCC.Anf.Defun
