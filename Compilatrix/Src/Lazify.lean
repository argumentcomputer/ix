import Compilatrix.Src.Runtime

/-! # Src.Lazify

Sets `byName` on the arguments of saturated `lazy` spines (the first
`arity` arguments), on the minors of saturated recursor and `case` spines,
and on every IH argument of every rule `rhs` (design note 01 §4.4). A mode
matters only where its argument is relevant, so a level-conditional argument
(D18) gets its mode like any other; arguments irrelevant at every instance
are not entered. It never changes a class or a major, and it touches only
modes, so the erased program is unchanged (`Lazify.erase_eq`). It runs after
the relevance check, on the checked runtime terms. -/

namespace Compilatrix.Src.Lazify

/-- Argument positions of a spine that become `byName`. -/
def byNameMask (p : Program) (head : Term) (n : Nat) : Array Bool := Id.run do
  let mut mask : Array Bool := .replicate n false
  let .const c _ := head | return mask
  if let some a := p.table.lazyOf c then
    if n ≥ a then
      for i in [0:a] do mask := mask.set! i true
  match p.table.resolveOf c with
  | some (.case r) =>
    if let some (.recr _ _ _ np _ nmin ni _ _ _) := p.decl? r then
      if n ≥ np + 1 + ni + 1 + nmin then
        for j in [0:nmin] do mask := mask.set! (np + 1 + ni + 1 + j) true
  | none =>
    if let some (.recr _ _ _ np nmot nmin ni _ _ _) := p.decl? c then
      if n ≥ np + nmot + nmin + ni + 1 then
        for j in [0:nmin] do mask := mask.set! (np + nmot + j) true
  | _ => pure ()
  return mask

def newMode (mask : Array Bool) (i : Nat) (m : Mode) (r : Rel) : Mode :=
  if !r.alwaysIrr && mask[i]?.getD false then .byName else m

mutual

/-- Lazify the relevant positions of a term. -/
def term (p : Program) : Term → Term
  | .app f a m r =>
    let (head, args) := (Term.app f a m r).spine
    let mask := byNameMask p head args.size
    let i := args.size - 1
    .app (spine p mask (i - 1) f) (if r.alwaysIrr then a else term p a) (newMode mask i m r) r
  | .lam b d t => .lam b d (term p t)
  | .letE c r ty v b => .letE c r ty (if r.alwaysIrr then v else term p v) (term p b)
  | .proj s i e => .proj s i (term p e)
  | t => t

/-- Rebuild the rest of a spine whose outermost remaining argument has
index `i`. -/
def spine (p : Program) (mask : Array Bool) (i : Nat) : Term → Term
  | .app f a m r =>
    .app (spine p mask (i - 1) f) (if r.alwaysIrr then a else term p a) (newMode mask i m r) r
  | head => term p head

end

/-- Mark the IH arguments of a rule's minor application `byName`. -/
def ihs (np nmot nmin : Nat) (rule : Rule) : Rule :=
  let total := np + nmot + nmin + rule.fields
  let (binders, body) := rule.rhs.lams
  if binders.size != total then rule else
  let (head, args) := body.spine
  let args := args.mapIdx fun i (a, m, r) =>
    (a, (if i ≥ rule.fields && !r.alwaysIrr then Mode.byName else m), r)
  let body := Term.mkApps head args
  { rule with rhs := binders.foldr (fun (b, d) acc => .lam b d acc) body }

/-- Lazify the given runtime terms. -/
def run (p : Program) (keys : Array TermKey) : Program := Id.run do
  let mut p := p
  for key in keys do
    match key with
    | .rule r j =>
      if let some (.recr _ _ _ np nmot nmin _ _ rules _) := p.decl? r then
        if let some rule := rules[j]? then
          p := p.setTerm key (term p (ihs np nmot nmin rule).rhs)
    | _ =>
      if let some t := p.termOf key then p := p.setTerm key (term p t)
  return p

end Compilatrix.Src.Lazify
