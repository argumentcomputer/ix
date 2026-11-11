import IxCC.Anf.Pipeline
import IxCC.Anf.Entry
import IxCC.Anf.Defun
import IxCC.Anf.WellFormed

/-! # The closures step

The middle end's last step, after the certificate's (`Anf.Pipeline.run`) and
before `Fir.lower`, on both paths (the producer and `Recheck.run`'s replay):

```text
plain P  :=  P is first order (Anf.firstOrder) and every root takes its declared count
closures :=  P unchanged                                   when plain
             entries (Anf.Entry) → P8 (Anf.defun) → size check   otherwise
```

`decl` lists the source roots' declared parameter counts by position. A
program with no residual closure whose roots take their declared counts is
returned as it is: its bytes do not change, and P8's input checks cannot
refuse it. Otherwise each root whose count differs gets an entry at its
declared count, and P8 removes every closure; its output is
`Anf.FirstOrder`, which `Fir.lower` accepts.

Not a certificate step: deterministic, it reads no certificate data, and the
replay re-runs it. No shrink or prune follows P8: they would need
certificate data (the rounds of each global P8 adds), and they have nothing
to do until the known-dispatch rule (`docs/closures-design.md`, "Known calls
after P8") exists. Errors are rendered `code: message`, with P8's codes
(`defun.*`) and `anf.entry`. -/

namespace IxCC.Anf.Pipeline

/-- Every root takes exactly its declared count. -/
def rootsAgree (decl : List Nat) (P : Program) : Bool :=
  P.roots.length == decl.length && (P.roots.zip decl).all fun (r, n) => P.arity? r == some n

/-- Nothing for the step to do: first order, every root at its declared count. -/
def plain (decl : List Nat) (P : Program) : Bool := firstOrder P && rootsAgree decl P

/-- **The closures step** (see the module note). -/
def closures (decl : List Nat) (P : Program) : Except String Program :=
  if plain decl P then .ok P
  else do
    let E ← (Entry.run decl P).mapError ("anf.entry: " ++ ·)
    let Q ← defun E
    checkGlobalNodes Q

end IxCC.Anf.Pipeline
