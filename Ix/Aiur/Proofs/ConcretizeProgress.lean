module
public import Ix.Aiur.Proofs.Lib
public import Ix.Aiur.Compiler.Concretize
public import Ix.Aiur.Semantics.TypedInvariants

/-!
Progress proofs for `Concretize`: predicates characterizing the inputs on
which `typToConcrete` / `termToConcrete` succeed, plus the supporting
progress lemmas. Paired with `Proofs/ConcretizeSound.lean` which proves
semantic preservation.

Companion to `Ix/Aiur/Compiler/Concretize.lean`. Kept out of the
implementation file so the compiler passes can evolve without churn in
the proof layer.

Note: `Typ.MvarFree`, `Typed.Term.MvarFree`, `Pattern.Simple`, and
`Typed.Term.ConcretizeReady` — the universal source/typed shape
predicates that previously lived here — now live in
`Ix.Aiur.Semantics.TypedInvariants` (semantic shape predicates).
-/

@[expose] public section

namespace Aiur

open Source

/-! ## Progress lemma: `termToConcrete` succeeds on `ConcretizeReady` terms. -/



end Aiur

end -- @[expose] public section
