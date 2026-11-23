import IxCC.Anf.Pipeline
import IxCC.Anf.Entry
import IxCC.Anf.Defun
import IxCC.Anf.WellFormed

/-! # The closures step

The middle end's last step, after the certificate's (`Anf.Pipeline.run`) and
before `Fir.lower`, on both paths (the producer and `Recheck.run`'s replay):

```text
plain P  :=  P is first order (Anf.firstOrder) and every root takes its declared count
closures :=  P unchanged                                                   when plain
             entries (Anf.Entry) → P8 (Anf.defun) → post-P8 (runPost)      otherwise
```

`decl` lists the source roots' declared parameter counts by position. A
program with no residual closure whose roots take their declared counts is
returned as it is: its bytes do not change, and P8's input checks cannot
refuse it. Otherwise each root whose count differs gets an entry at its
declared count, P8 removes every closure, and `runPost` runs the certified
post-P8 optimization steps (known-dispatch shrinking, post-P8 inlining, P9
flow-directed dispatch narrowing, P5 dead-parameter stripping, pruning, and
the node/depth/work budget check).

When the certificate carries `post = some pc` with `E.size == pc.baseSize`,
`closures` replays `pc` directly without running any analysis or search; when
`post = none` or `Entry.run` added entries (`E.size ≠ pc.baseSize`), it
computes `producePost E.size Q8` deterministically and replays it. Errors are
rendered `code: message`, with P8's codes (`defun.*`) and `anf.entry`. -/

namespace IxCC.Anf.Pipeline

/-- Every root takes exactly its declared count. -/
def rootsAgree (decl : List Nat) (P : Program) : Bool :=
  P.roots.length == decl.length && (P.roots.zip decl).all fun (r, n) => P.arity? r == some n

/-- Nothing for the step to do: first order, every root at its declared count. -/
def plain (decl : List Nat) (P : Program) : Bool := firstOrder P && rootsAgree decl P

/-- **The closures step** (see the module note). -/
def closures (decl : List Nat) (P : Program) (post : Option PostCert := none) :
    Except String Program :=
  if plain decl P then .ok P
  else do
    let E ← (Entry.run decl P).mapError ("anf.entry: " ++ ·)
    let Q8 ← defun E
    let pc := match post with
      | some c => if E.size == c.baseSize then c else producePost E.size Q8
      | none => producePost E.size Q8
    runPost pc Q8

end IxCC.Anf.Pipeline
