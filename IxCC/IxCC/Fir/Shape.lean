import IxCC.Fir.Semantics
import IxCC.Shape.Basic

/-!
# The shape certificate at `Fir` (`IxCC.Fir.Shape`)

Design note: `plans/ONE-PIPELINE.md`, section 2 (statement module
`IxCCDesign.OnePipeline.ShapeCert`).

**The hand-off** to a back end is `(Fir.Program, ShapeCert)` with `check P cert = true`.
`Fir`'s evaluator is unchanged, and a back end that ignores the certificate is still correct.

**What the certificate is.** One shape per variable, parameter, join parameter and result of
every function, and a data table (`DataDecl Key.CtorKey`). Untrusted inference produces it
(`IxCC.Fir.ShapeInfer`); `check` decides it.

**The specification** of the checker is the set of rules `ArgOk`, `PrimOk`, `RhsOk`, `CodeOk`,
collected in `Checked`. `check` implies `Checked` (`Fir.Proof.Shape.check_checked`), and
`Checked` implies that the certificate's facts hold of every value the evaluator produces
(`Fir.Proof.Shape.checkSound`, `codeSound`).

**Range facts are shapes.** The rules for `Nat` primitives carry bounds
(`natLt a + natLt b` is `natLt (a + b)`), so a checked `natLt b` is a validated range.

**Array primitives.** `Fir.primResult` evaluates them (`Src.ArrOp.eval` at `Fir.model`). Their
typed rules (`ArrOk`) are stated below and sound at Fir's reader (`arrEnc`,
`Fir.Proof.Shape.arrOkSound_fir`). The value judgment reads arrays through an `ArrEnc`; the
checker's soundness (`Fir.Proof.Shape.checkSound`, `codeSound`) is stated at `arrEnc`, the reader
of Fir's own values.

The checker (`check` and everything it calls) recurses structurally and uses lists and
`Src.NatMap` only, so the kernel can evaluate it (the style `IxCCTests.Recheck.Audit` checks).
-/

set_option autoImplicit false

namespace IxCC.Fir.Shape

open IxCC.Shape
open IxCC.Sem (Result)
open IxCC.Fir (Var FunId JoinId Arg Rhs Code Alt Val Env Program CtorInfo)

/-! ## The certificate -/

/-- The shapes of one function. A variable or join point the certificate does not list is
`any`. -/
structure FunShapes where
  params : List Shape := []
  ret : Shape := .any
  vars : Src.NatMap Shape := .leaf
  joins : Src.NatMap (List Shape) := .leaf
  deriving Inhabited

def FunShapes.var (fs : FunShapes) (x : Var) : Shape := fs.vars.getD x .any

def FunShapes.join (fs : FunShapes) (j : JoinId) : List Shape := fs.joins.getD j []

/-- **The shape certificate of a `Fir` program.** -/
structure ShapeCert where
  funs : Src.NatMap FunShapes := .leaf
  /-- The data table: entry `d` is `datas[d]`. -/
  datas : List (DataDecl Key.CtorKey) := []
  /-- The constructors of each enumeration. -/
  enums : List (Src.CId × List Key.CtorKey) := []
  deriving Inhabited

namespace ShapeCert

def fn (cert : ShapeCert) (f : FunId) : FunShapes := cert.funs.getD f {}

def data? (cert : ShapeCert) (d : Nat) : Option (DataDecl Key.CtorKey) := cert.datas[d]?

def enum? (cert : ShapeCert) (ind : Src.CId) : Option (List Key.CtorKey) :=
  (cert.enums.find? (·.1 == ind)).map (·.2)

/-- No entry lists a constructor twice. -/
def WF (cert : ShapeCert) : Prop :=
  ∀ d D, cert.data? d = some D →
    ∀ c fl fl', (c, fl) ∈ D.ctors → (c, fl') ∈ D.ctors → fl = fl'

end ShapeCert

/-- How `Fir.Val` holds an array: the one reader the value judgment needs. (Recommended
encoding, design note 1.4: a constructor value under a reserved key with one field per element,
so no `Val` constructor is added.) The checker's soundness is stated at Fir's reader, `arrEnc`.
-/
structure ArrEnc where
  asArr : Val → Option (List Val)

/-- **Fir's array reader**: a constructor value under the reserved key `Key.CtorKey.arr`
(`Fir.Val.asArr`, the reader of `Fir.model`). -/
def arrEnc : ArrEnc := ⟨Val.asArr⟩

/-! ## The value judgment: what a shape says of a `Fir` value -/

mutual

/-- **A `Fir` value has a shape.** -/
inductive ValOk (cert : ShapeCert) (enc : ArrEnc) : Shape → Val → Prop
  | any (v : Val) : ValOk cert enc .any v
  | irr : ValOk cert enc .irr .erased
  | nat (n : Nat) : ValOk cert enc .nat (.lit (.nat n))
  | natLt {b n : Nat} : n < b → ValOk cert enc (.natLt b) (.lit (.nat n))
  /-- a word: below erasure its tower is its number, a literal below the width's size (the
  values of `natLt (2 ^ w)`) -/
  | word {w : Src.Width} {n : Nat} : n < w.size → ValOk cert enc (.word w) (.lit (.nat n))
  | enum {ind : Src.CId} {ks : List Key.CtorKey} {c : CtorInfo} :
      cert.enum? ind = some ks → c.key ∈ ks → ValOk cert enc (.enum ind) (.ctor c [])
  /-- a constructor of the entry, its fields at the entry's shapes -/
  | data {d : Nat} {D : DataDecl Key.CtorKey} {c : CtorInfo} {fl : List Shape} {fs : List Val} :
      cert.data? d = some D → (c.key, fl) ∈ D.ctors → ValsOk cert enc fl fs →
      ValOk cert enc (.data d) (.ctor c fs)
  /-- a closure constructor (what defunctionalisation leaves of a function) -/
  | fn {σ τ : Shape} {c : CtorInfo} {fs : List Val} {g : Key.GKey} {n : Nat} :
      c.key = .clo g n → ValOk cert enc (.fn σ τ) (.ctor c fs)
  /-- both facts -/
  | inter {a b : Shape} {v : Val} :
      ValOk cert enc a v → ValOk cert enc b v → ValOk cert enc (.inter a b) v
  /-- an array, element by element, of the stated length where one is stated -/
  | arr {e : Shape} {len : Option Nat} {v : Val} {xs : List Val} :
      enc.asArr v = some xs → (∀ x, x ∈ xs → ValOk cert enc e x) →
      (∀ n, len = some n → xs.length = n) → ValOk cert enc (.arr e len) v

/-- Values have shapes, one by one. -/
inductive ValsOk (cert : ShapeCert) (enc : ArrEnc) : List Shape → List Val → Prop
  | nil : ValsOk cert enc [] []
  | cons {σ : Shape} {v : Val} {σs : List Shape} {vs : List Val} :
      ValOk cert enc σ v → ValsOk cert enc σs vs → ValsOk cert enc (σ :: σs) (v :: vs)

end

/-- Every bound variable has its shape. -/
def EnvOk (cert : ShapeCert) (enc : ArrEnc) (fs : FunShapes) (ρ : Env) : Prop :=
  ∀ x v, ρ.get? x = some v → ValOk cert enc (fs.var x) v

/-! ## The rules: the specification of the checker -/

/-- An operand supplies a value of shape `σ`. -/
inductive ArgOk (fs : FunShapes) : Arg → Shape → Prop
  | var {x : Var} {σ : Shape} : (fs.var x).le σ = true → ArgOk fs (.var x) σ
  | nat {n : Nat} {σ : Shape} : (Shape.natLt (n + 1)).le σ = true → ArgOk fs (.lit (.nat n)) σ
  | str {s : String} : ArgOk fs (.lit (.str s)) .any
  | erased {σ : Shape} : Shape.irr.le σ = true → ArgOk fs .erased σ

inductive ArgsOk (fs : FunShapes) : List Arg → List Shape → Prop
  | nil : ArgsOk fs [] []
  | cons {a : Arg} {σ : Shape} {as : List Arg} {σs : List Shape} :
      ArgOk fs a σ → ArgsOk fs as σs → ArgsOk fs (a :: as) (σ :: σs)

/-- Variables are declared at exactly their shapes (parameters, join parameters). -/
inductive ParamsOk (fs : FunShapes) : List Var → List Shape → Prop
  | nil : ParamsOk fs [] []
  | cons {x : Var} {xs : List Var} {σs : List Shape} :
      ParamsOk fs xs σs → ParamsOk fs (x :: xs) (fs.var x :: σs)

/-- The result shape of a `Nat` primitive with no bound known: a literal for the thirteen
operations that return a number; nothing for a comparison (the pinned `Bool`, of which nothing
is recorded) and for anything else. A word operation is not read here (`PrimOk.natAny` asks
`isWord = false`). -/
def natPrimResult : Lam.Prim → Shape
  | .natAdd | .natSub | .natMul | .natDiv | .natMod | .natPow | .natGcd | .natLand | .natLor
  | .natXor | .natShl | .natShr | .natPred => .nat
  | _ => .any

/-- **A primitive on operands of shapes `σs` returns a `τ`** (whenever it returns: a primitive
on an operand that is not what it reads is stuck, which asks nothing). -/
inductive PrimOk : Lam.Prim → List Shape → Shape → Prop
  /-- A word operation returns a word of its result width whatever came in
  (`Src.WordOp.eval_word_lt`, `eval3_word_lt`; an operand out of range is stuck), stated as
  `natLt (2 ^ w)`, so the range rules read its bound; the same values as `word w`
  (`ValOk.word`), into which it weakens (`Shape.le`). -/
  | word {w : Src.Width} {op : Src.WordOp} {σs : List Shape} :
      PrimOk (.word w op) σs (.natLt (op.resultWidth w).size)
  | natAny {op : Lam.Prim} {σs : List Shape} : op.isWord = false → PrimOk op σs (natPrimResult op)
  /-- the range rules: validated bounds -/
  | add {a b : Nat} {σ τ : Shape} : σ.le (.natLt a) = true → τ.le (.natLt b) = true →
      PrimOk .natAdd [σ, τ] (.natLt (a + b))
  | mul {a b : Nat} {σ τ : Shape} : σ.le (.natLt a) = true → τ.le (.natLt b) = true →
      PrimOk .natMul [σ, τ] (.natLt (a * b))
  | sub {a : Nat} {σ τ : Shape} : σ.le (.natLt a) = true → PrimOk .natSub [σ, τ] (.natLt a)
  | div {a : Nat} {σ τ : Shape} : σ.le (.natLt a) = true → PrimOk .natDiv [σ, τ] (.natLt a)
  | mod {a : Nat} {σ τ : Shape} : σ.le (.natLt a) = true → PrimOk .natMod [σ, τ] (.natLt a)
  | modBound {b : Nat} {σ τ : Shape} : 0 < b → σ.le (.natLt b) = true → τ.le (.natLt b) = true →
      PrimOk .natMod [σ, τ] (.natLt b)
  | land {a : Nat} {σ τ : Shape} : σ.le (.natLt a) = true → PrimOk .natLand [σ, τ] (.natLt a)
  | shr {a : Nat} {σ τ : Shape} : σ.le (.natLt a) = true → PrimOk .natShr [σ, τ] (.natLt a)
  | pred {a : Nat} {σ : Shape} : σ.le (.natLt a) = true → PrimOk .natPred [σ] (.natLt a)

/-! ### Array primitives (lane `prims-core`)

`ArrOk` is the statement module's (`IxCCDesign.OnePipeline.ShapeCert.ArrOk`): the twelve
operations, typed rules that keep the element shape and track a static length, each with an
untyped fallback. It is sound at Fir's reader (`Fir.Proof.Shape.arrOkSound_fir`, from
`arrOk_sound` in any model whose arrays the reader reads back), and it is a rule of `RhsOk`
(`RhsOk.arr`), decided by `arrOk` (`arrShape` beside `primShape`, and the element shape of a fresh
`empty` or `replicate` read from the target). The soundness theorems are stated at `arrEnc` (an
empty array has shape `arr e (some 0)` only for a reader that reads it). -/

/-- **An array primitive on operands of shapes `σs` returns a `τ`.** The typed rules keep the
element shape and track a static length; each has an untyped fallback, so generic code checks. -/
inductive ArrOk : Src.ArrOp → List Shape → Shape → Prop
  | empty {σ e : Shape} : ArrOk .empty [σ] (.arr e (some 0))
  | replicate {σ ν e : Shape} : ν.le e = true → ArrOk .replicate [σ, ν] (.arr e none)
  | sizeKnown {e : Shape} {n : Nat} : ArrOk .size [.arr e (some n)] (.natLt (n + 1))
  | size {σ : Shape} : ArrOk .size [σ] .nat
  | get {e τ : Shape} {n : Option Nat} : ArrOk .get [.arr e n, τ] e
  | set {e τ ν : Shape} {n : Option Nat} : ν.le e = true → ArrOk .set [.arr e n, τ, ν] (.arr e n)
  | push {e ν : Shape} {n : Option Nat} : ν.le e = true →
      ArrOk .push [.arr e n, ν] (.arr e (n.map (· + 1)))
  | pop {e : Shape} {n : Option Nat} : ArrOk .pop [.arr e n] (.arr e (n.map (· - 1)))
  | append {e : Shape} {n m : Option Nat} : ArrOk .append [.arr e n, .arr e m] (.arr e none)
  | extract {e σ τ : Shape} {n : Option Nat} : ArrOk .extract [.arr e n, σ, τ] (.arr e none)
  | copySlice {e σ τ υ : Shape} {n m : Option Nat} :
      ArrOk .copySlice [.arr e n, σ, .arr e m, τ, υ] (.arr e none)
  /-- whatever the operands, an operation that returns an array returns an array -/
  | arrAny {op : Src.ArrOp} {σs : List Shape} :
      op ≠ .size → op ≠ .get → op ≠ .toList → ArrOk op σs (.arr .any none)
  | any {op : Src.ArrOp} {σs : List Shape} : ArrOk op σs .any

/-- Whether a primitive returns a pinned `Bool` constructor (`natBeq`, `natBle`, `natBlt`). -/
def isBoolPrim : Lam.Prim → Bool
  | .natBeq | .natBle | .natBlt => true
  | _ => false

/-- Whether `ind` is an enumeration in `cert` that contains both pinned `Bool` constructors of `P`. -/
def boolEnumOk (P : Program) (cert : ShapeCert) (ind : Src.CId) : Bool :=
  match cert.enum? ind, P.known.boolTrue, P.known.boolFalse with
  | some ks, some tt, some ff => ks.contains tt && ks.contains ff
  | _, _, _ => false

/-- **A right-hand side yields a value of shape `σ`.** A call always checks its arguments: the
callee was checked under its parameters' shapes. -/
inductive RhsOk (P : Program) (cert : ShapeCert) (fs : FunShapes) : Rhs → Shape → Prop
  | arg {a : Arg} {σ : Shape} : ArgOk fs a σ → RhsOk P cert fs (.arg a) σ
  | ctorData {c : CtorInfo} {args : List Arg} {d : Nat} {D : DataDecl Key.CtorKey}
      {fl : List Shape} :
      cert.data? d = some D → (c.key, fl) ∈ D.ctors → ArgsOk fs args fl →
      RhsOk P cert fs (.ctor c args) (.data d)
  | ctorEnum {c : CtorInfo} {ind : Src.CId} {ks : List Key.CtorKey} :
      cert.enum? ind = some ks → c.key ∈ ks → RhsOk P cert fs (.ctor c []) (.enum ind)
  | ctorFn {c : CtorInfo} {args : List Arg} {g : Key.GKey} {n : Nat} {σ τ : Shape} :
      c.key = .clo g n → RhsOk P cert fs (.ctor c args) (.fn σ τ)
  | ctorAny {c : CtorInfo} {args : List Arg} : RhsOk P cert fs (.ctor c args) .any
  /-- a field of a constructor of the scrutinee's entry (another constructor is stuck) -/
  | projData {x : Var} {c : Key.CtorKey} {i d : Nat} {D : DataDecl Key.CtorKey}
      {fl : List Shape} {σ : Shape} :
      fs.var x = .data d → cert.data? d = some D → (c, fl) ∈ D.ctors → fl[i]? = some σ →
      RhsOk P cert fs (.proj x c i) σ
  /-- the predecessor a bounded `Nat` literal peels to preserves its bound -/
  | projNatLt {x : Var} {c : Key.CtorKey} {a : Nat} :
      P.known.natSucc = some c → (fs.var x).le (.natLt a) = true →
      RhsOk P cert fs (.proj x c 0) (.natLt a)
  /-- the predecessor a `Nat` literal peels to -/
  | projNat {x : Var} {c : Key.CtorKey} : P.known.natSucc = some c → (fs.var x).le .nat = true →
      RhsOk P cert fs (.proj x c 0) .nat
  | projAny {x : Var} {c : Key.CtorKey} {i : Nat} : RhsOk P cert fs (.proj x c i) .any
  | prim {op : Lam.Prim} {args : List Arg} {σs : List Shape} {τ : Shape} :
      ArgsOk fs args σs → PrimOk op σs τ → RhsOk P cert fs (.prim op args) τ
  /-- a `Nat` comparison primitive yields the pinned `Bool` enumeration when recorded in `cert` -/
  | primBool {op : Lam.Prim} {args : List Arg} {ind : Src.CId} {ks : List Key.CtorKey}
      {tt ff : Key.CtorKey} :
      isBoolPrim op = true → cert.enum? ind = some ks →
      P.known.boolTrue = some tt → P.known.boolFalse = some ff →
      tt ∈ ks → ff ∈ ks →
      RhsOk P cert fs (.prim op args) (.enum ind)
  | primAny {op : Lam.Prim} {args : List Arg} : RhsOk P cert fs (.prim op args) .any
  /-- an array primitive by its rules (`ArrOk`) -/
  | arr {op : Src.ArrOp} {args : List Arg} {σs : List Shape} {τ : Shape} :
      ArgsOk fs args σs → ArrOk op σs τ → RhsOk P cert fs (.prim (.arr op) args) τ
  | call {g : FunId} {args : List Arg} :
      ArgsOk fs args (cert.fn g).params → RhsOk P cert fs (.call g args) (cert.fn g).ret
  | weaken {r : Rhs} {σ τ : Shape} : RhsOk P cert fs r σ → σ.le τ = true → RhsOk P cert fs r τ

mutual

/-- **Code of a function checks against its shapes.** -/
inductive CodeOk (P : Program) (cert : ShapeCert) (fs : FunShapes) : Code → Prop
  | bind {x : Var} {r : Rhs} {k : Code} :
      RhsOk P cert fs r (fs.var x) → CodeOk P cert fs k → CodeOk P cert fs (.bind x r k)
  | jp {j : JoinId} {ps : List Var} {isRec : Bool} {body k : Code} :
      ParamsOk fs ps (fs.join j) → CodeOk P cert fs body → CodeOk P cert fs k →
      CodeOk P cert fs (.jp j ps isRec body k)
  | jmp {j : JoinId} {args : List Arg} : ArgsOk fs args (fs.join j) → CodeOk P cert fs (.jmp j args)
  | case {x : Var} {alts : List Alt} {d : Option Code} :
      AltsOk P cert fs alts → OptOk P cert fs d → CodeOk P cert fs (.case x alts d)
  | ret {a : Arg} : ArgOk fs a fs.ret → CodeOk P cert fs (.ret a)
  | tcall {g : FunId} {args : List Arg} :
      ArgsOk fs args (cert.fn g).params → (cert.fn g).ret.le fs.ret = true →
      CodeOk P cert fs (.tcall g args)
  | trap : CodeOk P cert fs .trap

inductive AltsOk (P : Program) (cert : ShapeCert) (fs : FunShapes) : List Alt → Prop
  | nil : AltsOk P cert fs []
  | cons {key : Key.CtorKey} {body : Code} {rest : List Alt} :
      CodeOk P cert fs body → AltsOk P cert fs rest → AltsOk P cert fs (.mk key body :: rest)

inductive OptOk (P : Program) (cert : ShapeCert) (fs : FunShapes) : Option Code → Prop
  | absent : OptOk P cert fs Option.none
  | present {c : Code} : CodeOk P cert fs c → OptOk P cert fs (Option.some c)

end

/-- **The certificate checks**: it is well formed, and every function's parameters are declared
at its parameter shapes and its body checks. This is what the Boolean checker decides. -/
structure Checked (P : Program) (cert : ShapeCert) : Prop where
  wf : cert.WF
  funs : ∀ f fd, P.fun? f = some fd →
    ParamsOk (cert.fn f) (fd.params.map (·.1)) (cert.fn f).params ∧
      CodeOk P cert (cert.fn f) fd.body

/-- **The join stack of checked code**: every entry was pushed by a checked `jp` of the
function, in an environment that had its shapes. This is the invariant a back end's simulation
carries from a function's entry (where the stack is empty) to any point of its body. -/
inductive JStackOk (P : Program) (cert : ShapeCert) (enc : ArrEnc) (fs : FunShapes) :
    List Fir.JEntry → Prop
  | nil : JStackOk P cert enc fs []
  | cons {e : Fir.JEntry} {rest : List Fir.JEntry} :
      EnvOk cert enc fs e.env → ParamsOk fs e.params (fs.join e.id) → CodeOk P cert fs e.body →
      JStackOk P cert enc fs rest → JStackOk P cert enc fs (e :: rest)

/-! ## Soundness: the statements

Proved in `IxCC.Fir.Proof.Shape` (`checkSound`, `codeSound`, `leSound`, `primOkSound`). -/

/-- The certificate's facts hold of every run of every function. -/
def ShapeSound (P : Program) (cert : ShapeCert) (enc : ArrEnc) : Prop :=
  ∀ (f : FunId) (k : Nat) (args : List Val) (v : Val), f < P.size →
    ValsOk cert enc (cert.fn f).params args → Fir.run P k f args = .ok v →
    ValOk cert enc (cert.fn f).ret v

/-- **Soundness of the shape checker.** It takes the place of `Fir.Proof.Rep.check_sound` as
the fact a back end reads, and covers what `Fir.Rep.checkWithArrays` was never proved to. -/
def CheckSound (enc : ArrEnc) : Prop :=
  ∀ (P : Program) (cert : ShapeCert), Checked P cert → ShapeSound P cert enc

/-- The same from inside a body, the form a back end's simulation uses: checked code, run in an
environment that has its shapes, returns a value of the function's result shape. (The
theorem with a join stack and its invariant is `Fir.Proof.Shape.evalSound`; this is the
instance at a function's entry.) -/
def CodeSound (enc : ArrEnc) : Prop :=
  ∀ (P : Program) (cert : ShapeCert), Checked P cert →
    ∀ (fs : FunShapes) (k : Nat) (ρ : Env) (c : Code) (v : Val),
      EnvOk cert enc fs ρ → CodeOk P cert fs c → Fir.eval P k ρ [] c = .ok v →
      ValOk cert enc fs.ret v

/-- Weakening is sound: the fact the checker's `Shape.le` decides. -/
def LeSound (enc : ArrEnc) : Prop :=
  ∀ (cert : ShapeCert) (σ τ : Shape) (v : Val), σ.le τ = true → ValOk cert enc σ v →
    ValOk cert enc τ v

/-- The rules for today's primitives are sound: `Lam.Prim.sem` on literals of the operand
shapes gives a literal of the result shape. -/
def PrimOkSound (cert : ShapeCert) (enc : ArrEnc) : Prop :=
  ∀ (P : Program) (op : Lam.Prim) (σs : List Shape) (τ : Shape) (vs : List Val) (v : Val),
    PrimOk op σs τ → ValsOk cert enc σs vs → Fir.primResult P op vs = .ok v → ValOk cert enc τ v

/-- The rules for the array primitives are sound in a value model (the statement module's
`ArrOkSound`). `Fir.model` reads no `List` value, so it is not `Lawful`; the theorem proved
(`Fir.Proof.Shape.arrOk_sound`) asks only that the model read back its arrays. -/
def ArrOkSound (cert : ShapeCert) (enc : ArrEnc) (M : Sem.ValModel Val) : Prop :=
  M.Lawful → M.asArr = enc.asArr → (M.nat = fun n => .lit (.nat n)) →
    ∀ (op : Src.ArrOp) (σs : List Shape) (τ : Shape) (vs : List Val) (v : Val),
      ArrOk op σs τ → ValsOk cert enc σs vs → op.eval M vs = .ok v → ValOk cert enc τ v

/-! ## The checker -/

/-- The shape an operand has, as far as the certificate knows. -/
def argShape (fs : FunShapes) : Arg → Shape
  | .var x => fs.var x
  | .lit (.nat n) => .natLt (n + 1)
  | .lit (.str _) => .any
  | .erased => .irr

/-- Decides `ArgOk`. -/
def argOk (fs : FunShapes) : Arg → Shape → Bool
  | .var x, σ => (fs.var x).le σ
  | .lit (.nat n), σ => (Shape.natLt (n + 1)).le σ
  | .lit (.str _), σ => σ == .any
  | .erased, σ => Shape.irr.le σ

/-- Decides `ArgsOk`. -/
def argsOk (fs : FunShapes) : List Arg → List Shape → Bool
  | [], [] => true
  | a :: as, σ :: σs => argOk fs a σ && argsOk fs as σs
  | _, _ => false

/-- Decides `ParamsOk`. -/
def paramsOk (fs : FunShapes) : List Var → List Shape → Bool
  | [], [] => true
  | x :: xs, σ :: σs => fs.var x == σ && paramsOk fs xs σs
  | _, _ => false

/-- The bounds of two bounded operands. -/
def bound2 : List Shape → Option (Nat × Nat)
  | [.natLt a, .natLt b] => some (a, b)
  | _ => none

/-- The bound of the left of two operands. -/
def boundL : List Shape → Option Nat
  | [.natLt a, _] => some a
  | _ => none

/-- The bound of one operand. -/
def bound1 : List Shape → Option Nat
  | [.natLt a] => some a
  | _ => none

/-- The best shape the rules give a primitive's result on operands of shapes `σs`
(`primShape_ok`: `PrimOk op σs (primShape op σs)`). -/
def primShape (op : Lam.Prim) (σs : List Shape) : Shape :=
  match op with
  | .word w wop => .natLt (wop.resultWidth w).size
  | .natAdd =>
    match bound2 σs with
    | some (a, b) => .natLt (a + b)
    | none => .nat
  | .natMul =>
    match bound2 σs with
    | some (a, b) => .natLt (a * b)
    | none => .nat
  | .natSub | .natDiv | .natMod | .natLand | .natShr =>
    match boundL σs with
    | some a => .natLt a
    | none => .nat
  | .natPred =>
    match bound1 σs with
    | some a => .natLt a
    | none => .nat
  | op => natPrimResult op

/-- The best shape the array rules give an array primitive's result on operands of shapes `σs`
(`arrShape_ok`: `ArrOk op σs (arrShape op σs)`): the element shape is kept and a static length
tracked where the operands allow, else the untyped fallback. -/
def arrShape (op : Src.ArrOp) (σs : List Shape) : Shape :=
  match op with
  | .empty =>
    match σs with
    | [_] => .arr .any (some 0)
    | _ => .arr .any none
  | .replicate =>
    match σs with
    | [_, ν] => .arr ν none
    | _ => .arr .any none
  | .size =>
    match σs with
    | [.arr _ (some n)] => .natLt (n + 1)
    | [_] => .nat
    | _ => .any
  | .get =>
    match σs with
    | [.arr e _, _] => e
    | _ => .any
  | .set =>
    match σs with
    | [.arr e n, _, ν] => if ν.le e then .arr e n else .arr .any none
    | _ => .arr .any none
  | .push =>
    match σs with
    | [.arr e n, ν] => if ν.le e then .arr e (n.map (· + 1)) else .arr .any none
    | _ => .arr .any none
  | .pop =>
    match σs with
    | [.arr e n] => .arr e (n.map (· - 1))
    | _ => .arr .any none
  | .append =>
    match σs with
    | [.arr e _, .arr e' _] => if e = e' then .arr e none else .arr .any none
    | _ => .arr .any none
  | .extract =>
    match σs with
    | [.arr e _, _, _] => .arr e none
    | _ => .arr .any none
  | .copySlice =>
    match σs with
    | [.arr e _, _, .arr e' _, _, _] => if e = e' then .arr e none else .arr .any none
    | _ => .arr .any none
  | .ofList => .arr .any none
  | .toList => .any

/-- Decides the array rules at a target shape: `arrShape` weakens to it, or a fresh `empty` or
`replicate` takes its element shape from it. -/
def arrOk (op : Src.ArrOp) (σs : List Shape) (τ : Shape) : Bool :=
  (arrShape op σs).le τ ||
    match op, σs, τ with
    | .empty, [_], .arr _ (some 0) => true
    | .empty, [_], .arr _ none => true
    | .replicate, [_, ν], .arr e none => ν.le e
    | _, _, _ => false

/-- Decides a primitive's rules at a target shape: an array primitive by `arrOk`, any other by
`primShape`. -/
def primRhsOk : Lam.Prim → List Shape → Shape → Bool
  | .arr op, σs, τ => arrOk op σs τ
  | op, σs, τ => (primShape op σs).le τ

/-- The fields an entry lists for a constructor. -/
def ctorFields (D : DataDecl Key.CtorKey) (c : Key.CtorKey) : Option (List Shape) :=
  (D.ctors.find? (·.1 == c)).map (·.2)

/-- A closure constructor's key. -/
def isClo : Key.CtorKey → Bool
  | .clo _ _ => true
  | .src _ => false
  | .arr => false

/-- A constructor application at a target shape. -/
def ctorOk (cert : ShapeCert) (fs : FunShapes) (c : CtorInfo) (args : List Arg) : Shape → Bool
  | .any => true
  | .data d =>
    match cert.data? d with
    | some D =>
      match ctorFields D c.key with
      | some fl => argsOk fs args fl
      | none => false
    | none => false
  | .enum ind =>
    args.isEmpty &&
      match cert.enum? ind with
      | some ks => ks.contains c.key
      | none => false
  | .fn _ _ => isClo c.key
  | _ => false

/-- The shape a projection reads, where the rules give one. -/
def projShape (P : Program) (cert : ShapeCert) (fs : FunShapes) (x : Var) (c : Key.CtorKey)
    (i : Nat) : Option Shape :=
  match fs.var x with
  | .data d =>
    match cert.data? d with
    | some D =>
      match ctorFields D c with
      | some fl => fl[i]?
      | none => none
    | none => none
  | .natLt a => if P.known.natSucc == some c && i == 0 then some (.natLt a) else none
  | .word w => if P.known.natSucc == some c && i == 0 then some (.natLt w.size) else none
  | σ => if σ.le .nat && P.known.natSucc == some c && i == 0 then some .nat else none

/-- Decides `RhsOk` at a target shape. -/
def rhsOk (P : Program) (cert : ShapeCert) (fs : FunShapes) : Rhs → Shape → Bool
  | .arg a, τ => argOk fs a τ
  | .ctor c args, τ => ctorOk cert fs c args τ
  | .proj x c i, τ =>
    τ == .any ||
      match projShape P cert fs x c i with
      | some σ => σ.le τ
      | none => false
  | .prim op args, τ =>
    τ == .any ||
      (match τ with
       | .enum ind => isBoolPrim op && boolEnumOk P cert ind
       | _ => false) ||
      primRhsOk op (args.map (argShape fs)) τ
  | .call g args, τ => argsOk fs args (cert.fn g).params && (cert.fn g).ret.le τ

mutual

/-- Decides `CodeOk`. -/
def codeOk (P : Program) (cert : ShapeCert) (fs : FunShapes) : Code → Bool
  | .bind x r k => rhsOk P cert fs r (fs.var x) && codeOk P cert fs k
  | .jp j ps _ body k =>
    paramsOk fs ps (fs.join j) && codeOk P cert fs body && codeOk P cert fs k
  | .jmp j args => argsOk fs args (fs.join j)
  | .case _ alts d => altsOk P cert fs alts && optOk P cert fs d
  | .ret a => argOk fs a fs.ret
  | .tcall g args => argsOk fs args (cert.fn g).params && (cert.fn g).ret.le fs.ret
  | .trap => true

def altsOk (P : Program) (cert : ShapeCert) (fs : FunShapes) : List Alt → Bool
  | [] => true
  | .mk _ body :: rest => codeOk P cert fs body && altsOk P cert fs rest

def optOk (P : Program) (cert : ShapeCert) (fs : FunShapes) : Option Code → Bool
  | none => true
  | some c => codeOk P cert fs c

end

/-- One function: its parameters are declared at its parameter shapes and its body checks. -/
def funOk (P : Program) (cert : ShapeCert) (f : FunId) (fd : Fir.Fun) : Bool :=
  paramsOk (cert.fn f) (fd.params.map (·.1)) (cert.fn f).params &&
    codeOk P cert (cert.fn f) fd.body

/-- No constructor is listed twice. -/
def ctorsOk : List (Key.CtorKey × List Shape) → Bool
  | [] => true
  | e :: rest => !(rest.any (·.1 == e.1)) && ctorsOk rest

/-- Decides `ShapeCert.WF`. -/
def wfOk (cert : ShapeCert) : Bool := cert.datas.all fun D => ctorsOk D.ctors

/-- **The shape checker.** Every entry of the function map is checked, whatever its index, so
no call can reach an unchecked body. -/
def check (P : Program) (cert : ShapeCert) : Bool :=
  wfOk cert && P.funs.toList.all fun e => funOk P cert e.1 e.2

end IxCC.Fir.Shape
