module
public import Ix.Aiur.Stages.Typed

/-!
Structural invariants on `Typed.Decls` in pairs.toList form. Moved here
from `Ix/Aiur/Proofs/CompilerProgress.lean` so upstream proof files can
import these Props without circular dependency.
-/

public section
@[expose] section

namespace Aiur

open Source

@[reducible]
def Typed.Decls.DtNameIsKey (tds : Typed.Decls) : Prop :=
  ∀ (key : Global) (dt : DataType),
    (key, Typed.Declaration.dataType dt) ∈ tds.pairs.toList → key = dt.name

@[reducible]
def Typed.Decls.CtorIsKey (tds : Typed.Decls) : Prop :=
  ∀ (key : Global) (dt : DataType) (c : Constructor),
    (key, Typed.Declaration.constructor dt c) ∈ tds.pairs.toList →
    key = dt.name.pushNamespace c.nameHead

/-- `CtorPresent`: every `.dataType dt` pair obligates each `c ∈ dt.constructors`
to have a matching `.constructor dt cc` entry keyed at
`dt.name.pushNamespace c.nameHead`. -/
@[reducible]
def Typed.Decls.CtorPresent (tds : Typed.Decls) : Prop :=
  ∀ (dtkey : Global) (dt : DataType) (c : Constructor),
    (dtkey, Typed.Declaration.dataType dt) ∈ tds.pairs.toList →
    c ∈ dt.constructors →
    ∃ cc,
      (dt.name.pushNamespace c.nameHead,
        Typed.Declaration.constructor dt cc) ∈ tds.pairs.toList

end Aiur

end -- @[expose] section
end -- public section
