import Compilatrix.Src.Runtime

/-! # Src.Lazify

Sets `byName` on the arguments of saturated `lazy` spines (the first
`arity` arguments), on the minors of saturated recursor and `case` spines,
and on every IH argument of every rule `rhs` (design note 01 §4.4). A mode
matters only where its argument is relevant, so a level-conditional argument
(D18) gets its mode like any other; arguments irrelevant at every instance
are not entered. It never changes a class or a major, and it touches only
modes, so the erased program is unchanged (`Lazify.erase_eq`). It runs after
the relevance check, on the checked runtime terms.

Kernel-evaluable (D17, on the recheck path as a re-run pass): the term walk
is a mutual structural recursion over `Term`, a spine's by-name positions are
a list of intervals, and the program is read through its `NatMap`s. -/

namespace Compilatrix.Src.Lazify

/-- Argument positions of a spine of `n` arguments that become `byName`, as
half-open intervals `[lo, hi)`. -/
def byNameRanges (p : Program) (head : Term) (n : Nat) : List (Nat × Nat) :=
  match head with
  | .const c _ =>
    let lazy := match p.table.lazyOf c with
      | some a => if n ≥ a then [(0, a)] else []
      | none => []
    let elim := match p.table.resolveOf c with
      | some (.case r) =>
        match p.decl? r with
        | some (.recr _ _ _ np _ nmin ni _ _ _) =>
          if n ≥ np + 1 + ni + 1 + nmin then [(np + 1 + ni + 1, np + 1 + ni + 1 + nmin)] else []
        | _ => []
      | none =>
        match p.decl? c with
        | some (.recr _ _ _ np nmot nmin ni _ _ _) =>
          if n ≥ np + nmot + nmin + ni + 1 then [(np + nmot, np + nmot + nmin)] else []
        | _ => []
      | _ => []
    lazy ++ elim
  | _ => []

/-- Whether position `i` is in one of the intervals. -/
def inRanges (ranges : List (Nat × Nat)) (i : Nat) : Bool :=
  ranges.any fun (lo, hi) => lo ≤ i && i < hi

def newMode (ranges : List (Nat × Nat)) (i : Nat) (m : Mode) (r : Rel) : Mode :=
  if !r.alwaysIrr && inRanges ranges i then .byName else m

/-- The number of arguments of an application spine. -/
def spineLength : Term → Nat
  | .app f _ _ _ => spineLength f + 1
  | _ => 0

/-- The head of an application spine. -/
def spineHead : Term → Term
  | .app f _ _ _ => spineHead f
  | t => t

mutual

/-- Lazify the relevant positions of a term. -/
def term (p : Program) : Term → Term
  | .app f a m r =>
    let n := spineLength f + 1
    let ranges := byNameRanges p (spineHead f) n
    let i := n - 1
    .app (spine p ranges (i - 1) f) (if r.alwaysIrr then a else term p a) (newMode ranges i m r) r
  | .lam b d t => .lam b d (term p t)
  | .letE c r ty v b => .letE c r ty (if r.alwaysIrr then v else term p v) (term p b)
  | .proj s i e => .proj s i (term p e)
  | t => t
termination_by structural t => t

/-- Rebuild the rest of a spine whose outermost remaining argument has
index `i`; its head is lazified as `term` does it. -/
def spine (p : Program) (ranges : List (Nat × Nat)) (i : Nat) : Term → Term
  | .app f a m r =>
    .app (spine p ranges (i - 1) f) (if r.alwaysIrr then a else term p a)
      (newMode ranges i m r) r
  | .lam b d t => .lam b d (term p t)
  | .letE c r ty v b => .letE c r ty (if r.alwaysIrr then v else term p v) (term p b)
  | .proj s i e => .proj s i (term p e)
  | t => t
termination_by structural t => t

end

/-- Mark the IH arguments of a rule's minor application `byName`. -/
def ihs (np nmot nmin : Nat) (rule : Rule) : Rule :=
  let total := np + nmot + nmin + rule.fields
  let (binders, body) := rule.rhs.lams
  if binders.length != total then rule else
  let (head, args) := body.spine
  let args := args.mapIdx fun i (a, m, r) =>
    (a, (if i ≥ rule.fields && !r.alwaysIrr then Mode.byName else m), r)
  let body := Term.mkApps head args
  { rule with rhs := binders.foldr (fun (b, d) acc => .lam b d acc) body }

/-- Lazify one runtime term. -/
def step (p : Program) (key : TermKey) : Program :=
  match key with
  | .rule r j =>
    match p.decl? r with
    | some (.recr _ _ _ np nmot nmin _ _ rules _) =>
      match rules[j]? with
      | some rule => p.setTerm key (term p (ihs np nmot nmin rule).rhs)
      | none => p
    | _ => p
  | _ =>
    match p.termOf key with
    | some t => p.setTerm key (term p t)
    | none => p

/-- Lazify the given runtime terms, in order (structural on the list). -/
def run (p : Program) : List TermKey → Program
  | [] => p
  | key :: keys => run (step p key) keys

end Compilatrix.Src.Lazify
