import CompilatrixTests.Src.Support
import Compilatrix.Src.Lazify

/-! One synthetic program per SrcEval rule (design note 01 §3.2, §10 part 1),
with stuck and trap cases, the lazy and by-name behaviours, and an
executable clock-monotonicity check on generated terms. -/

namespace CompilatrixTests.Src.Rules

open Compilatrix Compilatrix.Src Compilatrix.Ixon CompilatrixTests.Src
open Compilatrix.Sem (Result)

/-- The base program extended with the definitions the rules need. -/
structure World where
  p : Program
  b : Base
  loop : CId
  ident : CId
  thm : CId
  ax : CId
  opaq : CId
  opaqOk : CId
  unsafeDef : CId
  partialDef : CId
  viaEqn : CId
  viaCsimp : CId
  myIte : CId
  myOr : CId

def world : World := Id.run do
  let (b0, b) := base
  let mut bld := b0
  let loopId := bld.consts.size
  let (bld1, loop) := bld.add (.defn .defn .safe 0 ty (.const loopId []))
  bld := bld1
  let (bld1, ident) := bld.add (.defn .defn .safe 0 ty (lam (.var 0)))
  bld := bld1
  let (bld1, thm) := bld.add (.defn .thm .safe 0 ty (.natLit 1))
  bld := bld1
  let (bld1, ax) := bld.add (.axio true 0 ty)
  bld := bld1
  let (bld1, opaq) := bld.add (.defn .opaq .safe 0 ty (.natLit 2))
  bld := bld1
  let (bld1, opaqOk) := bld.add (.defn .opaq .safe 0 ty (.natLit 3))
  bld := { bld1 with opaqueByValue := bld1.opaqueByValue.set! opaqOk true }
  let (bld1, unsafeDef) := bld.add (.defn .defn .unsaf 0 ty (.natLit 4))
  bld := bld1
  let (bld1, partialDef) := bld.add (.defn .defn .part 0 ty (.natLit 5))
  bld := bld1
  -- A definition whose body diverges but whose eqn entry gives 6.
  let (bld1, viaEqn) := bld.add (.defn .defn .safe 0 ty (.const loop []))
  bld := { bld1 with resolve := bld1.resolve.set! viaEqn (some (.eqn thm (.natLit 6))) }
  -- A csimp redirect to `ident`.
  let (bld1, viaCsimp) := bld.add (.defn .defn .safe 0 ty (.const loop []))
  bld := { bld1 with resolve := bld1.resolve.set! viaCsimp (some (.csimp ident [] thm)) }
  -- myIte b t e := Bool.casesOn motive b e t (lazy, arity 3).
  let (bld1, myIte) := bld.add (.defn .defn .safe 0 ty (lams 3
    (appM (.const b.boolCases [.zero]) [(irrArg, .irr), (.var 2, .strict), (.var 0, .strict),
      (.var 1, .strict)])))
  bld := { bld1 with lazy := bld1.lazy.set! myIte (some 3) }
  -- myOr x y := Bool.casesOn motive x y true (lazy, arity 2).
  let (bld1, myOr) := bld.add (.defn .defn .safe 0 ty (lams 2
    (appM (.const b.boolCases [.zero]) [(irrArg, .irr), (.var 1, .strict), (.var 0, .strict),
      (.const b.btrue [], .strict)])))
  bld := { bld1 with lazy := bld1.lazy.set! myOr (some 2) }
  let p := bld.program
  -- Lazify every runtime term of the synthetic program.
  let keys := (Array.range p.size).filterMap fun c =>
    match p.decl? c with
    | some (.defn ..) => some (TermKey.value c)
    | _ => none
  let keys := keys ++ #[TermKey.eqn viaEqn, .rule b.natRec 0, .rule b.natRec 1]
  let p := Lazify.run p keys
  return { p, b, loop, ident, thm, ax, opaq, opaqOk, unsafeDef, partialDef, viaEqn, viaCsimp,
           myIte, myOr }

def ev (w : World) (k : Nat) (t : Term) (ls : Levels := []) (ρ : Env := []) : Result Value :=
  eval w.p k ls ρ t

def lit (n : Nat) : Term := .natLit n
def c (id : CId) : Term := .const id []

def expectOutcome (a : Assert) (got : Result Value) (expected : String) (msg : String) : IO Unit :=
  expect a (outcome got == expected) s!"{msg}: got {outcome got}, expected {expected}"

def expectNat (a : Assert) (got : Result Value) (n : Nat) (msg : String) : IO Unit :=
  expect a (natOf got == some n) s!"{msg}: got {outcome got}, expected lit {n}"

/-- A lazified term (as `Src.Lazify` treats runtime terms). -/
def lz (w : World) (t : Term) : Term := Lazify.term w.p t

def rules (a : Assert) : IO Unit := do
  let w := world
  let b := w.b
  -- E1: a val slot, a name slot (forcing charges), out of range.
  expectNat a (ev w 0 (.var 0) [] [.val (.lit 7)]) 7 "E1 val slot"
  expectOutcome a (ev w 0 (.var 0) [] [.name (lit 8) [] []]) "timeout" "E1 name slot charges"
  expectNat a (ev w 1 (.var 0) [] [.name (lit 8) [] []]) 8 "E1 name slot forced"
  expectOutcome a (ev w 5 (.var 3)) "stuck" "E1 out of range"
  -- E2, E3, E4.
  expectOutcome a (ev w 0 (.sort .zero)) "ok irr" "E2 sort"
  expectOutcome a (ev w 0 (.pi {} {} ty ty)) "ok irr" "E2 pi"
  expectNat a (ev w 0 (lit 42)) 42 "E3 natLit"
  expectOutcome a (ev w 0 (.strLit "s")) "ok str" "E3 strLit"
  expectOutcome a (ev w 0 (lam (.var 0))) "ok clo" "E4 lam"
  -- E5: a relevant let evaluates; an irrelevant one binds irr without evaluating.
  expectNat a (ev w 5 (.letE {nonDep := false} .rel ty (lit 3) (.var 0))) 3 "E5 relevant let"
  expectNat a (ev w 0 (.letE {nonDep := false} Rel.prf ty (c w.loop) (lit 1))) 1 "E5 irrelevant let"
  expectOutcome a (ev w 5 (.letE {nonDep := false} Rel.prf ty (lit 3) (.var 0))) "ok irr"
    "E5 irrelevant let binds irr"
  -- E6: projections.
  let pairT := app (c b.pairMk) [lit 1, lit 2]
  expectNat a (ev w 5 (.proj b.pair 1 pairT)) 2 "E6 projection"
  expectOutcome a (ev w 5 (.proj b.pair 2 pairT)) "stuck" "E6 field out of range"
  expectOutcome a (ev w 5 (.proj b.pair 0 (.sort .zero))) "stuck" "E6 projecting irr (S38)"
  expectOutcome a (ev w 5 (.proj b.pair 0 (lit 3))) "stuck" "E6 projecting a literal"
  expectOutcome a (ev w 5 (.proj b.pair 0 (.strLit "ab"))) "stuck" "E6 string subject (E9 declined)"
  -- E7: argument modes.
  expectNat a (ev w 5 (.app (lam (lit 9)) (c w.loop) .byName .rel)) 9 "E7 byName argument unevaluated"
  expectNat a (ev w 5 (appIrr (lam (lit 9)) (c w.loop))) 9 "E7 irr argument unevaluated"
  expectOutcome a (ev w 50 (.app (lam (lit 9)) (c w.loop) .strict .rel)) "timeout"
    "E7 strict argument evaluated"
  -- E5 and E7 are level-exact (D18): a proof under `allZero [0]` is `irr`
  -- at level 0 and evaluated at level 1.
  let condArg := appM (lam (lit 9)) [(c w.loop, .irrWhen (.allZero [0]))]
  expectNat a (ev w 5 condArg [0]) 9 "E7 conditional argument irr at level 0"
  expectOutcome a (ev w 50 condArg [1]) "timeout" "E7 conditional argument evaluated at level 1"
  expectOutcome a (ev w 50 condArg []) "ok lit 9" "E7 missing levels read as zero"
  let condLet := Term.letE {nonDep := false} (.proof (.allZero [0])) ty (c w.loop) (lit 1)
  expectNat a (ev w 5 condLet [0]) 1 "E5 conditional let irr at level 0"
  expectOutcome a (ev w 50 condLet [2]) "timeout" "E5 conditional let evaluated at level 2"
  -- E8: δ through the table and the declaration.
  expectNat a (ev w 5 (app (c w.ident) [lit 4])) 4 "E8 safe definition"
  expectOutcome a (ev w 0 (app (c w.ident) [lit 4])) "timeout" "E8 δ charges"
  expectOutcome a (ev w 5 (c w.thm)) "stuck" "E8 theorem"
  expectOutcome a (ev w 5 (c w.ax)) "stuck" "E8 axiom"
  expectOutcome a (ev w 5 (c w.opaq)) "stuck" "E8 opaque"
  expectNat a (ev w 5 (c w.opaqOk)) 3 "E8 opaque by value"
  expectOutcome a (ev w 5 (c w.unsafeDef)) "stuck" "E8 unsafe"
  expectOutcome a (ev w 5 (c w.partialDef)) "stuck" "E8 partial"
  expectNat a (ev w 5 (c w.viaEqn)) 6 "E8 eqn entry replaces the body"
  expectNat a (ev w 5 (app (c w.viaCsimp) [lit 5])) 5 "E8 csimp redirect"
  expectOutcome a (ev w 5 (c b.nat)) "stuck" "E8 inductive type"
  -- A1–A3.
  expectNat a (ev w 5 (app (lam (.var 0)) [lit 3])) 3 "A1 β"
  expectOutcome a (ev w 5 (app (lam (.var 0) { propWhen := .allZero [] }) [lit 3])) "stuck"
    "A1 proof-regime β is stuck"
  expectOutcome a (ev w 5 (app (lam (.var 0) { propWhen := .allZero [0] }) [lit 3]) [0]) "stuck"
    "A1 guard at level 0"
  expectNat a (ev w 5 (app (lam (.var 0) { propWhen := .allZero [0] }) [lit 3]) [1]) 3
    "A1 guard at level 1"
  expectOutcome a (ev w 5 (app (c b.add) [lit 1])) "ok pap" "A2 pap accumulation"
  expectOutcome a (ev w 5 (app (lit 3) [lit 1])) "stuck" "A3 applying a literal"
  expectOutcome a (ev w 5 (app (.sort .zero) [lit 1])) "stuck" "A3 applying irr (S38)"
  expectOutcome a (ev w 5 (app pairT [lit 1])) "stuck" "A3 applying a constructor"
  -- F1: constructors.
  expectNat a (ev w 5 (c b.zero)) 0 "F1 Nat.zero"
  expectNat a (ev w 5 (app (c b.succ) [lit 41])) 42 "F1 Nat.succ"
  expectOutcome a (ev w 5 (app (c b.succ) [.sort .zero])) "stuck" "F1 Nat.succ of irr"
  expectOutcome a (ev w 5 pairT) s!"ok con {b.pairMk}/2" "F1 constructor"
  -- F2: Nat.rec peels literals; IHs are by name.
  let sumTo := fun (n : Nat) => lz w (appM (.const b.natRec [.succ .zero])
    [(irrArg, .irr), (lit 0, .strict), (lams 2 (app (c b.add) [.var 1, .var 0]) , .strict),
     (lit n, .strict)])
  expectNat a (ev w 1000 (sumTo 10)) 45 "F2 Nat.rec on a literal"
  let unusedIh := lz w (appM (.const b.natRec [.succ .zero])
    [(irrArg, .irr), (lit 0, .strict), (lams 2 (.var 1), .strict), (lit 1000000, .strict)])
  expectNat a (ev w 6 unusedIh) 999999 "F2 unused IH costs O(1) clock"
  expectOutcome a (ev w 50 (appM (.const b.natRec [.succ .zero])
    [(irrArg, .irr), (lit 0, .strict), (lams 2 (.var 1), .strict), (pairT, .strict)])) "stuck"
    "F2 major of another inductive"
  -- F3: a subsingleton recursor reads its field from the index slot.
  expectNat a (ev w 5 (appM (.const b.isNatRec [.zero])
    [(irrArg, .irr), (lam (.var 0), .strict), (lit 11, .strict), (irrArg, .irr)])) 11
    "F3 subsingleton ι from an index"
  -- F2/F3 per profile (D18): a `subsingleton (allZero [0])` eliminator (a
  -- `PUnit.{u}.rec`) does not force its major at u = 0 and is ordinary at u = 1.
  let unitElim := fun (major : Term) (m : A) => appM (.const b.unitRec [.succ .zero, .var 0])
    [(irrArg, .irr), (lit 5, .strict), (major, m)]
  expectNat a (ev w 5 (unitElim irrArg .irr) [0]) 5 "F3 where the family is a proposition"
  expectOutcome a (ev w 5 (unitElim irrArg .irr) [1]) "stuck"
    "F2 where it is not: an irr major is stuck"
  expectNat a (ev w 5 (unitElim (c b.unitMk) .strict) [1]) 5 "F2 on the constructor at u = 1"
  -- F4: an empty recursor traps.
  expectOutcome a (ev w 5 (appM (.const b.emptyRec [.zero]) [(irrArg, .irr), (irrArg, .irr)]))
    "trap" "F4 empty recursor"
  -- F5: case.
  let natCase := fun (major : Term) => lz w (appM (.const b.natCases [.succ .zero])
    [(irrArg, .irr), (major, .strict), (lit 100, .strict), (lam (app (c b.add) [.var 0, lit 1]), .strict)])
  expectNat a (ev w 5 (natCase (lit 0))) 100 "F5 case zero"
  expectNat a (ev w 5 (natCase (lit 7))) 7 "F5 case succ"
  expectOutcome a (ev w 5 (natCase (.sort .zero))) "stuck" "F5 case on irr"
  -- F6: primitives.
  expectNat a (ev w 5 (app (c b.sub) [lit 3, lit 5])) 0 "F6 truncated sub"
  expectOutcome a (ev w 5 (app (c b.beq) [lit 3, lit 3])) s!"ok con {b.btrue}/0" "F6 beq gives Bool.true"
  expectOutcome a (ev w 5 (app (c b.add) [lit 3, .sort .zero])) "stuck" "F6 non-literal argument"
  -- F7, F8, F9: quotients.
  let mk := app (.const b.quotMk [.succ .zero]) [irrArg, irrArg, lit 20]
  expectOutcome a (ev w 5 mk) s!"ok con {b.quotMk}/1" "F7 Quot.mk"
  expectNat a (ev w 5 (appM (.const b.quotLift [.succ .zero, .succ .zero])
    [(irrArg, .irr), (irrArg, .irr), (irrArg, .irr), (lam (app (c b.add) [.var 0, lit 1]), .strict),
     (irrArg, .irr), (mk, .strict)])) 21 "F8 Quot.lift"
  expectOutcome a (ev w 5 (c b.quotInd)) "stuck" "F9 Quot.ind"
  expectOutcome a (ev w 5 (c b.quot)) "stuck" "F9 Quot"
  -- Lazy spines.
  let iteT := fun (cond : Term) (t e : Term) => lz w (app (c w.myIte) [cond, t, e])
  expectNat a (ev w 20 (iteT (c b.btrue) (lit 1) (c w.loop))) 1 "lazy ite with a diverging branch"
  expectNat a (ev w 20 (iteT (c b.bfalse) (c w.loop) (lit 2))) 2 "lazy ite, other branch"
  expectOutcome a (ev w 20 (app (c w.myIte) [c b.btrue, lit 1, c w.loop])) "timeout"
    "strict ite evaluates both branches"
  expectOutcome a (ev w 20 (lz w (app (c w.myOr) [c b.btrue, c w.loop]))) s!"ok con {b.btrue}/0"
    "Bool.or true ⊥ terminates"
  -- 10⁴ free steps run at k = 3: primitives and constructors are free.
  let deep := (List.range 10000).foldl (fun t _ => app (c b.add) [t, lit 1]) (lit 0)
  expectNat a (ev w 3 deep) 10000 "10⁴ free steps at k = 3"
  -- Readback of a constructor keeps its fields.
  match ev w 5 pairT with
  | .ok v => expect a (readbackAll w.p v == some (.ctor 0 [.nat 1, .nat 2])) "readback of a pair"
  | _ => expect a false "readback of a pair"

/-! ## Executable clock monotonicity -/

/-- A deterministic linear congruential generator. -/
structure Gen where
  seed : Nat

def Gen.next (g : Gen) (bound : Nat) : Nat × Gen :=
  let s := (g.seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  ((s >>> 33) % (max bound 1), { seed := s })

/-- A random closed term over the world's constants, with `depth` binders
in scope. -/
def genTerm (w : World) : Nat → Nat → Gen → Term × Gen
  | 0, scope, g =>
    let (k, g) := g.next 3
    if k == 0 && scope > 0 then
      let (i, g) := g.next scope
      (.var i, g)
    else
      let (n, g) := g.next 6
      (.natLit n, g)
  | fuel + 1, scope, g =>
    let (k, g) := g.next 11
    match k with
    | 0 => let (i, g) := g.next (scope + 1); (if scope > 0 then .var (i % scope) else .natLit i, g)
    | 1 => let (t, g) := genTerm w fuel (scope + 1) g; (lam t, g)
    | 2 =>
      let (f, g) := genTerm w fuel scope g
      let (x, g) := genTerm w fuel scope g
      let (m, g) := g.next 3
      (if m == 0 then .app f x .strict .rel else if m == 1 then .app f x .byName .rel
        else appIrr f x, g)
    | 3 =>
      let (x, g) := genTerm w fuel scope g
      let (y, g) := genTerm w fuel scope g
      (app (.const w.b.add []) [x, y], g)
    | 4 =>
      let (x, g) := genTerm w fuel scope g
      let (n, g) := g.next 8
      let (s, g) := genTerm w fuel (scope + 2) g
      (lz w (appM (.const w.b.natRec [.succ .zero])
        [(irrArg, .irr), (x, .strict), (lam (lam s), .strict), (.natLit n, .strict)]), g)
    | 5 =>
      let (x, g) := genTerm w fuel scope g
      let (y, g) := genTerm w fuel scope g
      (.proj w.b.pair 0 (app (.const w.b.pairMk []) [x, y]), g)
    | 6 => (.const w.loop [], g)
    | 7 =>
      let (x, g) := genTerm w fuel scope g
      let (y, g) := genTerm w fuel (scope + 1) g
      (.letE { nonDep := false } .rel ty x y, g)
    | 8 => let (x, g) := genTerm w fuel scope g; (app (.const w.ident []) [x], g)
    | 9 =>
      let (x, g) := genTerm w fuel scope g
      let (y, g) := genTerm w fuel scope g
      (lz w (app (.const w.myIte []) [.const w.b.btrue [], x, y]), g)
    | _ => let (n, g) := g.next 10; (.natLit n, g)

/-- For random terms and clocks `k ≤ k'`: a non-timeout outcome at `k` is
the outcome at `k'` (01 §6.1 `eval_mono`, executable). -/
def evalMono (a : Assert) (samples : Nat := 2000) : IO Unit := do
  let w := world
  let mut g : Gen := { seed := 20260929 }
  let mut checked := 0
  for _ in [0:samples] do
    let (t, g1) := genTerm w 5 0 g
    let (k, g2) := g1.next 12
    let (dk, g3) := g2.next 20
    g := g3
    let r := ev w k t
    let r' := ev w (k + dk) t
    if outcome r != "timeout" then
      expect a (sameOutcome w.p r r') s!"eval_mono: {outcome r} at {k} but {outcome r'} at {k + dk}"
      checked := checked + 1
  expect a (checked > samples / 4) s!"eval_mono: only {checked} non-timeout samples"

def run (a : Assert) : IO Unit := do
  rules a
  evalMono a

end CompilatrixTests.Src.Rules
