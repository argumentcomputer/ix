import Ix.CompileCert.Canon.SourceTelescope
import Ix.CompileCert.Canon.GeneratedTables

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

abbrev RunReach (cx : XCtx) : Name → Prop :=
  SourceReach cx.source cx.groupOf.blocks cx.sourceMembers.toList

/-- Source reads and generated queue identities are kept distinct. Once a
head is in the queue, nested discovery does not resolve it as an external. -/
def RunKnown (cx : XCtx) (st : XSt) (name : Name) : Prop :=
  RunReach cx name ∨ st.typeNames.contains name = true

def MemberScope (P : Name → Prop) (member : XMember) : Prop :=
  RefScope P member.typ ∧ ∀ ctor ∈ member.ctors, RefScope P ctor.typ

theorem MemberScope.mono {P Q : Name → Prop} {member : XMember}
    (scope : MemberScope P member) (included : ∀ n, P n → Q n) :
    MemberScope Q member :=
  ⟨scope.1.mono included, fun ctor found => (scope.2 ctor found).mono included⟩

theorem RunKnown.push {cx : XCtx} {st : XSt} {name : Name}
    (known : RunKnown cx st name) (member : XMember) :
    RunKnown cx (st.push member) name := by
  rcases known with source | queued
  · exact Or.inl source
  · exact Or.inr (NameTable.contains_insert_mono st.typeNames member.name name () queued)

theorem RunKnown.pushed (cx : XCtx) (st : XSt) (member : XMember) :
    RunKnown cx (st.push member) member.name :=
  Or.inr (NameTable.contains_insert_self st.typeNames member.name ())

/-- Internal queue scope and cache provenance; both are established from
the actual expansion initializer. This is not a public caller precondition. -/
structure ExpansionScope (cx : XCtx) (st : XSt) : Prop where
  members : ∀ member ∈ st.types, MemberScope (RunKnown cx st) member
  sourceCache : st.sourceNames? = none ∨
    st.sourceNames? = some (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames

theorem ExpansionScope.empty (cx : XCtx) : ExpansionScope cx {} := by
  constructor
  · simp
  · exact Or.inl rfl

theorem ExpansionScope.push {cx : XCtx} {st : XSt}
    (scope : ExpansionScope cx st) (member : XMember)
    (memberScope : MemberScope (RunKnown cx (st.push member)) member) :
    ExpansionScope cx (st.push member) := by
  constructor
  · intro current found
    rcases (show current ∈ st.types ∨ current = member by simpa [XSt.push] using found) with old | rfl
    · exact (scope.members current old).mono (fun _ known => known.push member)
    · exact memberScope
  · exact scope.sourceCache

theorem ExpansionScope.sourceNames {cx : XCtx} {st : XSt}
    (scope : ExpansionScope cx st) :
    st.sourceNames cx = (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames := by
  rcases scope.sourceCache with empty | full
  · simp [XSt.sourceNames,empty]
  · simp [XSt.sourceNames,full]

/-- The exact eligibility prefix derives external source reachability from
the current constructor expression. A generated head cannot pass this test. -/
theorem RefScope.externalQuery {cx : XCtx} {st : XSt} {e : Expr}
    (scope : RefScope (RunKnown cx st) e) {head : Name} {levels : Array Ix.Level}
    {hash : Address} (headEq : (Ix.Compile.Canon.getAppFnArgs e).1 = .const head levels hash)
    (outside : st.typeNames.contains head = false) : RunReach cx head := by
  have headScope := scope.getAppFnArgs.1
  rw [headEq] at headScope
  have known := headScope head (by simp [sourceExprRefs])
  rcases known with reached | queued
  · exact reached
  · rw [outside] at queued
    cases queued

/-- Actual source view resolution and actual registered group membership
connect an eligible query to every source representative opened by the step. -/
theorem RefScope.externalGroupMember {cx : XCtx} {st : XSt} {e : Expr}
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : RefScope (RunKnown cx st) e) {head : Name} {levels : Array Ix.Level}
    {hash : Address} (headEq : (Ix.Compile.Canon.getAppFnArgs e).1 = .const head levels hash)
    (outside : st.typeNames.contains head = false) {view : IndView}
    (found : cx.ind? head = some view) {cls : Array Name}
    (classMember : cls ∈ cx.groupOf view) {name : Name} (member : name ∈ cls) :
    RunReach cx name := by
  have reached := scope.externalQuery headEq outside
  apply reached.groupMember
  · simpa [lookup] using found
  · exact classMember
  · exact member

/-- Every constructor actually loaded for an opened representative has its
query spelling in the exact list used by the allocator. This is the missing
source-to-freshness bridge, without any source constructor-prefix condition. -/
theorem ExpansionScope.externalConstructor {cx : XCtx} {st : XSt}
    (scope : ExpansionScope cx st) (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    {name : Name} (reached : RunReach cx name) {view : IndView}
    (found : cx.ind? name = some view) {ctor : Name × Expr × Nat}
    (member : ctor ∈ view.ctors) :
    RunReach cx ctor.1 ∧ RefScope (RunReach cx) ctor.2.1 ∧
      keyName ctor.1 ∈ st.sourceNames cx := by
  have actual : IndView.ofConst? cx.source.get? name = some view := by simpa [lookup] using found
  obtain ⟨query,refs,protectedName⟩ := reached.viewCtor actual member
  exact ⟨query,refs,scope.sourceNames.symm ▸ protectedName⟩

end Ix.CompileCert.Canon
