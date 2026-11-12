import IxCC.Src.Table.Check

/-! # Word entries of the unfolding table (stage W1)

A `word w op thm` entry makes the constant pinned for the operation `op` at width `w` a special
head of SrcEval (rule F6w), its meaning the stored theorem `thm`. The check (`checkWord`) asks:
words are enabled (`Config.words`); `op` is one of the width's primitive operations; the constant
is at the operation's pinned address; and `thm` is a safe, level-monomorphic theorem, read with its
proof (a proposal's theorem is a proof seed of ingress once its subject is reached; one read by
statement, `Program.byStatement`, is refused, as `checkEqn` refuses it), with a standard-axiom
closure (`checkAxiomClosure` walks the proof), whose stored statement is, syntactically
(`Term.eqv`), the one `wordEqnType` builds from the program's pinned constants:

* a binary operation: `∀ x y : Nat, op (ofNat x) (ofNat y) = ofNat (spec x y)`;
* `complement`, `neg`: `∀ x : Nat, op (ofNat x) = ofNat (spec x)`;
* a conversion to width `w'`: `∀ x : Nat, op (ofNat x) = ofNat' (spec x)`, `ofNat'` the target's;
* `toNat`: `∀ x : Nat, toNat (ofNat x) = Nat.mod x size`;
* `ofNat`, the bridge: `∀ x (h : Nat.le (Nat.succ (Nat.mod x size)) size),
  ofNat x = UIntN.ofBitVec (BitVec.ofFin bits (Fin.mk size (Nat.mod x size) h))`;

where `spec` is `WordOp.eval`'s number as a term over `Nat`'s pinned operations, on the arguments
reduced first (`Nat.mod x size`), and reduced again where `eval` reduces (`add`, `sub`, `mul`,
`shiftLeft`, `neg`). `ix compile --equations --word-equations` adds exactly these theorems
(`Ix.Compile.WordEquations`) and names each in its output's `theorems` list (kind `word`, subject
the operation), which the sidecar carries with addresses; the producer proposes the entry from
there (`Table.wordProposal`), never by searching the closure for a statement. The theorem fixes
what the pinned constant computes, so a wrong
pin cannot make a statement about the model false; the pin is what makes SrcEval's rule agree with
the constant's own body, which `tests-src` tests on Lean 4.34.1's bodies. -/

namespace IxCC.Src.Table

open IxCC.Ixon

/-- The constant at a pinned address. -/
def pinnedId (p : Program) (pin : Option Nat) : Option CId :=
  pin.bind fun n => p.lookup (Pinned.addrOfNat n)

/-- A `Nat` primitive's constant, through its pin. -/
def natOpId (p : Program) (op : PrimOp) : Option CId := pinnedId p (p.known.pins.prim? op)

/-- A word operation's constant, through its pin. -/
def wordOpId (p : Program) (w : Width) (op : WordOp) : Option CId :=
  pinnedId p (p.known.pins.wordOp? w op)

private def app (f a : Term) : Term := .app f a .strict .rel

private def app2 (f a b : Term) : Term := app (app f a) b

/-- `@Eq.{1} T a b`. -/
private def eqT (eq : CId) (T a b : Term) : Term :=
  app (app (app (.const eq [.succ .zero]) T) a) b

/-- **The statement a word entry's theorem must have** (the module docstring), over the
program's pinned constants; `none` if one of them is absent. -/
def wordEqnType (p : Program) (w : Width) (op : WordOp) : Option Term := do
  let natC ← p.known.nat
  let eqC ← p.known.eq
  let natT : Term := .const natC []
  let ofN ← wordOpId p w .ofNat
  let tyC ← pinnedId p (p.known.pins.wordTypes.lookup w)
  let nop := fun (o : PrimOp) (a b : Term) => do
    let c ← natOpId p o
    pure (app2 (.const c []) a b)
  let m : Term := .natLit w.size
  let bin := op.arity == 2
  let x : Term := if bin then .var 1 else .var 0
  let y : Term := .var 0
  let ofNx := app (.const ofN []) x
  let pi1 := fun (body : Term) => Term.pi {} {} natT body
  match op with
  | .ofNat =>
    let natLeC ← pinnedId p p.known.pins.natLe
    let succC ← p.known.natSucc
    let ctorC ← pinnedId p (p.known.pins.wordCtors.lookup w)
    let bvC ← pinnedId p p.known.pins.bitVecOfFin
    let finC ← pinnedId p p.known.pins.finMk
    let xm0 ← nop .mod (.var 0) m
    let xm1 ← nop .mod (.var 1) m
    let bound := app2 (.const natLeC []) (app (.const succC []) xm0) m
    let tower := app (.const ctorC [])
      (app2 (.const bvC []) (.natLit w.bits) (app (app2 (.const finC []) m xm1) (.var 0)))
    pure (pi1 (.pi {} {} bound (eqT eqC (.const tyC []) (app (.const ofN []) (.var 1)) tower)))
  | .toNat =>
    let k ← wordOpId p w .toNat
    let xm ← nop .mod x m
    pure (pi1 (eqT eqC natT (app (.const k []) ofNx) xm))
  | .decEq | .decLt | .decLe => none
  | _ => do
    let k ← wordOpId p w op
    let xm ← nop .mod x m
    let ym ← nop .mod y m
    let red := fun (e : Term) => nop .mod e m
    let rhs ← match op with
      | .add => do red (← nop .add xm ym)
      | .sub => do red (← nop .add (← nop .sub m ym) xm)
      | .mul => do red (← nop .mul xm ym)
      | .div => nop .div xm ym
      | .mod => nop .mod xm ym
      | .land => nop .land xm ym
      | .lor => nop .lor xm ym
      | .xor => nop .xor xm ym
      | .shiftLeft => do red (← nop .shiftLeft xm (← nop .mod ym (.natLit w.bits)))
      | .shiftRight => do nop .shiftRight xm (← nop .mod ym (.natLit w.bits))
      | .complement => nop .xor (.natLit (w.size - 1)) xm
      | .neg => do red (← nop .sub m xm)
      | .convert w' => if w.bits ≤ w'.bits then pure xm else nop .mod xm (.natLit w'.size)
      | _ => none
    let w' := op.resultWidth w
    let tyC' ← pinnedId p (p.known.pins.wordTypes.lookup w')
    let ofN' ← wordOpId p w' .ofNat
    let lhs := if bin then app2 (.const k []) ofNx (app (.const ofN []) y) else app (.const k []) ofNx
    let body := eqT eqC (.const tyC' []) lhs (app (.const ofN' []) rhs)
    pure (if bin then pi1 (pi1 body) else pi1 body)

/-- **Check `word w op thm` for constant `f`** (the module docstring). -/
def checkWord (cfg : Config) (p : Program) (f : CId) (w : Width) (op : WordOp) (thm : CId) :
    Except String Unit := do
  unless cfg.words do throw "word: fixed-width words are not enabled"
  unless (WordOp.primitives w).contains op do
    throw s!"word: {op.leanName w} is not a primitive operation"
  unless some (Pinned.addrNat (p.addr f)) == p.known.pins.wordOp? w op do
    throw "word: the address is not the pinned one"
  let some expected := wordEqnType p w op
    | throw s!"word: a constant the statement of {op.leanName w} names is absent"
  let some (.defn .thm .safe 0 ty _) := p.decl? thm
    | throw "word: the equation is not a safe level-monomorphic theorem"
  if p.byStatement.contains thm then
    throw "word: the equation was read by its statement; its proof is not in the program"
  unless ty.nodesLe maxTermNodes do throw "word: the statement exceeds the node budget"
  unless ty.eqv expected do throw s!"word: the theorem does not state {op.leanName w}'s equation"
  checkAxiomClosure p thm

end IxCC.Src.Table
