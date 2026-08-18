module

public import FixtureB.Base

@[expose] public section

namespace FixtureA

/- These declarations force owner-aware rewriting. Their relocated forms must
   mention the qualified `FixtureB` names, never the unqualified source
   names. -/
def importedToken : FixtureB.Token := FixtureB.defaultToken

def importedScore : Nat := importedToken.score

theorem importedScore_eq : importedScore = 42 := rfl

end FixtureA
