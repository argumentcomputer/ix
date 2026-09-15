import CompilatrixTests.Support.Lowering

namespace Compilatrix.IxIR1.Lower

open Compilatrix.Ixon (Address Owned Uses)
open Compilatrix.IxIR0 (Literal)

section Guards

open Compilatrix.IxIR0.Examples

/-! β, let, dup (a variable consumed twice), projection -/

#guard diffExpr (.app (.lam .many (.var 0)) (natE 4))
#guard diffExpr (.letE .many (natE 2) (.app (.ref natSucc) (.var 0)))
#guard diffExpr (.letE .many (natE 2)
  (.app (.app (.ref pairMk) (.var 0)) (.var 0)))
#guard diffExpr (.proj 0 (.app (.app (.ref pairMk) (natE 1)) (natE 2)))
#guard diffExpr (.proj 1 (.app (.app (.ref pairMk) (natE 1)) (natE 2)))
#guard diffExpr (.proj 5 (.app (.app (.ref pairMk) (natE 1)) (natE 2)))
#guard diffExpr (.app (.ref pairMk) (natE 1))   -- first-class ctor pap

-- dead binding: the inserted drop reclaims the unused 1̂
#guard diffExpr (.letE .many (natE 1) (natE 2))

-- a struct borrowed twice: released only after its last projection
#guard diffExpr (.letE .many (.app (.app (.ref pairMk) (natE 1)) (natE 2))
  (.app (.app (.ref natAddDef) (.proj 0 (.var 0))) (.proj 1 (.var 0))))

/-! Recursor ι: `case` + `callSelf`, constructor and peeled-literal
majors -/

#guard diffExpr (.app (.app (.ref natAddDef) (natE 2)) (natE 3))
#guard diffExpr (.app (.app (.ref natAddDef) (natE 0)) (natE 0))
#guard diffExpr (.app (.app (.ref natAddDef) (natE 7)) (natE 0))
#guard diffExpr (.app (.app (.ref natAddDef) (.lit (.nat 2))) (.lit (.nat 3)))
#guard diffExpr (.app (.app (.ref natAddDef) (natE 1)) (.lit (.nat 3)))

/-! List recursion, including a shared (dup'd) list argument -/

#guard diffExpr
  (.app (.app (.ref appendDef) (listE natE [1, 2])) (listE natE [3]))
#guard diffExpr
  (.app (.app (.ref appendDef) (listE natE [])) (listE natE []))
#guard diffExpr (.app (.ref lengthDef) (listE natE [5, 6, 7]))
#guard diffExpr (.letE .many (listE natE [1])
  (.app (.app (.ref appendDef) (.var 0)) (.var 0)))

/-! Externs (success and both-sides refusal) -/

#guard diffExpr
  (.app (.app (.ref natAddExt) (.lit (.nat 20))) (.lit (.nat 22)))
#guard diffExpr (.app (.app (.ref natAddExt) (natE 1)) (.lit (.nat 1)))

/-! ◻ absorption (arguments still lowered, then released), stuckness -/

#guard diffExpr (.app .erased (natE 1))
#guard diffExpr (.proj 0 .erased)
#guard diffExpr (.app (.lit (.nat 1)) (.lit (.nat 2)))

/-! Lambda lifting with a capture:
`(fun x => (fun y => add x y) 2̂) 3̂` -/

#guard diffExpr (.app (.lam .many (.app (.lam .many
  (.app (.app (.ref natAddDef) (.var 1)) (.var 0))) (natE 2))) (natE 3))

/-! Divergence: Ω exhausts fuel on both sides -/

#guard diffExpr
  (.app (.lam .many (.app (.var 0) (.var 0)))
    (.lam .many (.app (.var 0) (.var 0))))
  (runFuel := 300)

/-! The lowering rejects unknown references at compile time -/

#guard
  match lowerAll IxIR0.Examples.declList (.ref (synthAddr 999)) with
  | .error _ => true
  | .ok _ => false

/-! Target-side readback: lowered 2+3 really is 5̂ -/

#guard
  match lowerAll IxIR0.Examples.declList
      (.app (.app (.ref natAddDef) (natE 2)) (natE 3)) with
  | .ok (ds, c) =>
    (match runMain { decls := Env.ofList ds, oracle := tgtOracle } c with
     | .ok (s, v) => ((treeOfR s 1000 v).bind natT?) == some 5
     | _ => false)
  | _ => false

/-! ## Stage 2: the unique world

The same corpus expressions flip worlds by demand: `natE`/`pairMk`
spines at unique demand allocate unique. Linear/affine programs run
with **zero refcount operations** — the no-RC strategy, as counter
`#guard`s — and unique results release by deep free in the harness. -/

-- linear pair of linear nats: values agree with IxIR₀, leak-free
private def linPair : IxIR0.Expr :=
  .letE .linear (natE 2) (.letE .linear (natE 3)
    (.app (.app (.ref pairMk) (.var 1)) (.var 0)))

#guard diffExpr linPair (mainW := .unique)

-- …and with zero RC traffic: 8 unique allocations, nothing else
#guard checkLowered linPair .unique fun s _ =>
  s.allocs == 8 && s.rcops == 0 && s.frees == 0 && s.live == 8

-- a whole unique tree without lets
#guard diffExpr (.app (.app (.ref pairMk) (natE 1)) (natE 2))
  (mainW := .unique)
#guard checkLowered (.app (.app (.ref pairMk) (natE 1)) (natE 2))
  .unique fun s _ => s.allocs == 6 && s.rcops == 0 && s.live == 6

-- dead affine: dropU deep-frees the unused 2̂ (3 nodes), no RC ops
private def affDead : IxIR0.Expr := .letE .affine (natE 2) (natE 1)

#guard diffExpr affDead (mainW := .unique)
#guard checkLowered affDead .unique fun s _ =>
  s.allocs == 5 && s.frees == 3 && s.rcops == 0 && s.live == 2

/-! Static mode errors: the lowering is the operational usage check -/

-- a dead linear binding
#guard lowersErr (.letE .linear (natE 1) (natE 2)) .shared
  "unused linear binding"

-- a unique variable used twice
#guard lowersErr (.letE .linear (natE 1)
  (.app (.app (.ref pairMk) (.var 0)) (.var 0))) .unique
  "unique variable used more than once"

-- dereliction: a shared value at unique demand
#guard lowersErr (.letE .many (natE 1) (.app (.ref natSucc) (.var 0)))
  .unique "dereliction: shared value at unique demand"

-- freeze needed: a unique value at shared demand
#guard lowersErr (.letE .linear (natE 1) (.app (.ref natSucc) (.var 0)))
  .shared freezeNeededMsg

-- a unique value into a recursor (the all-`many` fragment)
#guard lowersErr (.letE .linear (natE 1)
  (.app (.app (.ref natAddDef) (.var 0)) (natE 1))) .shared
  freezeNeededMsg

-- function values live in the shared world
#guard lowersErr (.letE .linear (.lam .many (.var 0)) (.var 0)) .shared
  "function values live in the shared world (one-shot closures deferred)"

-- projection from a unique value
#guard lowersErr
  (.letE .linear (.app (.app (.ref pairMk) (natE 1)) (natE 2))
    (.proj 0 (.var 0))) .shared
  uniqueDestructuringMsg

-- shared paps cannot own a captured unique value
private def uniqueCaptureRestriction : IxIR0.Expr :=
  .letE .linear (natE 1) (.lam .many (.var 1))

#guard lowersErr uniqueCaptureRestriction .shared uniqueCaptureMsg

-- a direct recursor call demands every argument in the shared world
private def modeMonomorphicRecursorRestriction : IxIR0.Expr :=
  .letE .linear (natE 1)
    (.app
      (.app
        (.app (.ref natRec) (natE 0))
        (.lam .many (.lam .many (.app (.ref natSucc) (.var 0)))))
      (.var 0))

#guard lowersErr modeMonomorphicRecursorRestriction .shared freezeNeededMsg

-- `recSelf` exists only in recursor-rule environments.  A one-parameter
-- recursor has self arity two, so this one-argument rule call witnesses the
-- exact saturation restriction while the declaration itself is lowered.
private def underAppliedRecSelfAddr : Address := synthAddr 92

private def underAppliedRecSelfRule : IxIR0.RecRule :=
  { fields := 0, rhs := .app (.var 1) (.var 0) }

private def underAppliedRecSelfRejected : Bool :=
  match lowerAll
      (IxIR0.Examples.declList ++
        [(underAppliedRecSelfAddr,
          .recursor 1 false #[underAppliedRecSelfRule])])
      (natE 0) with
  | .error message => message == underAppliedRecSelfMsg
  | .ok _ => false

#guard underAppliedRecSelfRejected

/-- Executable coverage for the complete six-entry policy inventory.  The
individual guards above retain readable failure locations; this aggregate
guard prevents a newly listed restriction from landing without a witness. -/
private def restrictionWitness : RestrictionKind → Bool
  | kind@(.freeze) =>
    lowersErr (.letE .linear (natE 1) (.app (.ref natSucc) (.var 0)))
      .shared kind.diagnostic
  | kind@(.uniqueDestructuring) =>
    lowersErr
      (.letE .linear (.app (.app (.ref pairMk) (natE 1)) (natE 2))
        (.proj 0 (.var 0)))
      .shared kind.diagnostic
  | kind@(.sharedFunctionValues) =>
    lowersErr (.app (.lam .affine (.lit (.nat 7))) (natE 3))
      .shared kind.diagnostic
  | kind@(.uniqueCapture) =>
    lowersErr uniqueCaptureRestriction .shared kind.diagnostic
  | kind@(.modeMonomorphicRecursors) =>
    lowersErr modeMonomorphicRecursorRestriction .shared kind.diagnostic
  | .saturatedRecSelf => underAppliedRecSelfRejected

#guard RestrictionKind.all.all restrictionWitness

/-! Non-`many` function values are rejected before they can reach the
all-shared `apply` path: direct lambdas, bare known references, and
under-applied known definitions all pin the same exact diagnostic.
All-`many` partial applications remain supported. -/

#guard lowersErr
  (.app (.lam .affine (.lit (.nat 7))) (natE 3)) .shared
  nonManyPapMsg

#guard lowersErr (.ref dropFstDef) .shared nonManyPapMsg

#guard lowersErr (.app (.ref dropFstDef) (natE 1)) .shared nonManyPapMsg

#guard diffExpr (.app (.ref natAddDef) (natE 2))

/-! Declared result worlds close the old call seam: a shared result at
unique demand is rejected statically, before a mismatched `dropU` can
reach the evaluator. -/

#guard lowersErr
  (.letE .affine
    (.app (.app (.ref natAddDef) (natE 1)) (natE 1))
    (natE 0)) .shared
  "call result is shared at unique demand"

private def uniqueResultDef : Address := synthAddr 91

private def uniqueResultDecls : List (Address × IxIR0.Decl) :=
  IxIR0.Examples.declList ++
    [(uniqueResultDef, .defn .unique (natE 1))]

/-! A declared unique computed global is lowered in the unique world,
its signature survives in `FnDef`, and an unused affine caller can
deep-free the returned tree with no RC traffic. -/

#guard
  match lowerAll uniqueResultDecls
      (.letE .affine (.ref uniqueResultDef) (natE 0)) with
  | .ok (ds, c) =>
    match (Env.ofList ds) uniqueResultDef,
        runMain { decls := Env.ofList ds, oracle := tgtOracle } c with
    | some (.fn d), .ok (s, _) =>
      d.result == .unique && s.allocs == 3 && s.frees == 2 &&
        s.rcops == 0 && s.live == 1
    | _, _ => false
  | .error _ => false

#guard
  match lowerAll uniqueResultDecls (.ref uniqueResultDef) .shared with
  | .error msg =>
    msg == freezeNeededMsg
  | .ok _ => false

/-! Mixed-mode telescopes: the binder-mode signature is
outermost-first while de Bruijn vars count innermost-first, so
entries, entry drops, and `knownCall` argument worlds must agree
per-parameter. Both orders exercise declaration lowering and saturated
known calls; first-class mixed-mode lambdas are rejected above. -/

#guard diffExpr (.app (.app (.ref dropFstDef) (natE 1)) (natE 2))
#guard diffExpr (.app (.app (.ref dropSndDef) (natE 2)) (natE 1))

-- the dead affine argument (2 unique nodes) deep-frees at entry with
-- zero RC traffic; the shared result (3 nodes) survives
#guard checkLowered (.app (.app (.ref dropFstDef) (natE 1)) (natE 2))
  .shared fun s _ =>
    s.allocs == 5 && s.frees == 2 && s.rcops == 0 && s.live == 3
#guard checkLowered (.app (.app (.ref dropSndDef) (natE 2)) (natE 1))
  .shared fun s _ =>
    s.allocs == 5 && s.frees == 2 && s.rcops == 0 && s.live == 3

-- A mixed-mode lambda cannot escape into the all-shared papp/apply path.
#guard lowersErr (.lam .affine (.lam .many (.var 0))) .shared
  nonManyPapMsg

-- a dead linear binder in a mixed telescope is rejected *as such*
-- (not as a freeze error on the wrong binder)
#guard
  match lowerAll (IxIR0.Examples.declList ++
      [(synthAddr 90,
        .defn .shared (.lam .linear (.lam .many (.var 0))))])
      (natE 0) with
  | .error "unused linear binding" => true
  | _ => false

end Guards

end Compilatrix.IxIR1.Lower
