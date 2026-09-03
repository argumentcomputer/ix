import Ix.Tc.Verify.Check.BlockClassification
import Ix.Tc.Verify.Check.QuotientBridge
import Ix.Tc.Verify.Check.StandaloneDriver

/-!
# Quotient checking is not a coordinated-block transaction

Production validates quotient declarations through `checkConstMember`; they
never enter `coordinatedBlockFor`.  If a quotient is nevertheless present in
a physical block array, the production classifier rejects it at the exact
member where it is observed.  The semantic catalog relation likewise has no
coordinated quotient constructor.

Quotient acceptance therefore uses the separate four-check atomic bridge; it
never acquires inductive-oracle or block-cache authority through E0.
-/

namespace Ix.Tc

namespace RecM

/-- The production router never selects a coordinated block for a quotient. -/
theorem coordinatedBlockFor_quotient
    (name : Mode.anon.F Name)
    (levelParams : Mode.anon.F (Array Name)) (kind : Ix.QuotKind)
    (levels : UInt64) (type : KExpr .anon) (methods : Methods .anon)
    (state : TcState .anon) :
    (coordinatedBlockFor (.quot name levelParams kind levels type)).run
      methods state = .ok none state := by
  rfl

/-- Axioms share the same non-coordinated routing boundary. -/
theorem coordinatedBlockFor_axiom
    (name : Mode.anon.F Name)
    (levelParams : Mode.anon.F (Array Name)) (isUnsafe : Bool)
    (levels : UInt64) (type : KExpr .anon) (methods : Methods .anon)
    (state : TcState .anon) :
    (coordinatedBlockFor (.axio name levelParams isUnsafe levels type)).run
      methods state = .ok none state := by
  rfl

end RecM

namespace RecM.BlockClassFlags

/-- Encountering a quotient in the named production census is an immediate
classifier error; no later flag combination can turn it into a block kind. -/
theorem note_quotient
    (flags : BlockClassFlags) (member : KId .anon)
    (name : Mode.anon.F Name) (levelParams : Mode.anon.F (Array Name))
    (kind : Ix.QuotKind) (levels : UInt64) (type : KExpr .anon) :
    flags.note member (.quot name levelParams kind levels type) =
      .error (.other
        s!"unsupported check block {member}: axiom/quotient member") := by
  rfl

/-- Axioms are rejected by the same production census branch. -/
theorem note_axiom
    (flags : BlockClassFlags) (member : KId .anon)
    (name : Mode.anon.F Name) (levelParams : Mode.anon.F (Array Name))
    (isUnsafe : Bool) (levels : UInt64) (type : KExpr .anon) :
    flags.note member (.axio name levelParams isUnsafe levels type) =
      .error (.other
        s!"unsupported check block {member}: axiom/quotient member") := by
  rfl

end RecM.BlockClassFlags

namespace Catalog

/-- A catalogued quotient cannot satisfy any coordinated member kind. -/
theorem quotient_not_coordinated
    {catalog : Catalog} {id block : KId .anon}
    {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)}
    {quotKind : Ix.QuotKind} {levels : UInt64} {type : KExpr .anon}
    (hcatalog : catalog id =
      some (.quot name levelParams quotKind levels type))
    (kind : CheckBlockKind) :
    ¬catalog.CoordinatedMember block kind id := by
  rintro ⟨concrete, hfound, hshape⟩
  have hconcrete : concrete =
      .quot name levelParams quotKind levels type :=
    Option.some.inj (hfound.symm.trans hcatalog)
  subst concrete
  cases kind <;>
    simp [KConst.IsMemberOfKind, KConst.IsDefinitionMemberOf,
      KConst.IsInductiveMemberOf, KConst.IsRecursorMemberOf] at hshape

end Catalog

namespace StandaloneRoute

/-- Quotient declarations take the operational standalone branch, while
their semantic acceptance remains deliberately outside K3/E0. -/
theorem quotientRoute
    (I : TcState .anon → Prop) (methods : Methods .anon)
    (name : Mode.anon.F Name) (levelParams : Mode.anon.F (Array Name))
    (kind : Ix.QuotKind) (levels : UInt64) (type : KExpr .anon) :
    StandaloneRoute I methods
      (.quot name levelParams kind levels type) := by
  intro state hI
  exact ⟨hI, rfl⟩

end StandaloneRoute

end Ix.Tc
