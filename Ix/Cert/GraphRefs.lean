import Ix.Cert.Statement
import Ix.Cert.GraphWalk

/-! # The closure relation's references are exact

`Ix.Cert.refsOf`, the references the closure relation (`DependsOn`) and the condensation read,
runs `Ix.graphConst` from the empty memo. By `GraphWalk`, it returns exactly the mentions
(`GraphWalk.Refs`) of an axiom's or quotient constant's type and of a definition's, theorem's or
opaque's type and value (`refsOf_axiom` … `refsOf_opaque`), and every mention of any constant's
terms (`termsOf`) is one of its references (`refsOf_mentions`). -/

namespace Ix.Cert.GraphRefs

open Ix.Cert.GraphWalk (Refs)

theorem refsOf_axiom (v : Ix.AxiomVal) (n : Ix.Name) :
    (refsOf (.axiomInfo v)).contains n = true ↔ Refs n v.cnst.type :=
  GraphWalk.graphConst_axiom v { consts := {} } n

theorem refsOf_quot (v : Ix.QuotVal) (n : Ix.Name) :
    (refsOf (.quotInfo v)).contains n = true ↔ Refs n v.cnst.type :=
  GraphWalk.graphConst_quot v { consts := {} } n

/-- **A definition references exactly its type's and value's mentions.** -/
theorem refsOf_defn (v : Ix.DefinitionVal) (n : Ix.Name) :
    (refsOf (.defnInfo v)).contains n = true ↔ Refs n v.cnst.type ∨ Refs n v.value :=
  GraphWalk.graphConst_defn v { consts := {} } n

theorem refsOf_thm (v : Ix.TheoremVal) (n : Ix.Name) :
    (refsOf (.thmInfo v)).contains n = true ↔ Refs n v.cnst.type ∨ Refs n v.value :=
  GraphWalk.graphConst_thm v { consts := {} } n

theorem refsOf_opaque (v : Ix.OpaqueVal) (n : Ix.Name) :
    (refsOf (.opaqueInfo v)).contains n = true ↔ Refs n v.cnst.type ∨ Refs n v.value :=
  GraphWalk.graphConst_opaque v { consts := {} } n

/-- **Every mention of a constant's terms is one of its references** (`termsOf`), whatever its
kind. -/
theorem refsOf_mentions (ci : Ix.ConstantInfo) {n : Ix.Name} {e : Ix.Expr} (he : e ∈ termsOf ci)
    (hn : Refs n e) : (refsOf ci).contains n = true := by
  cases ci with
  | axiomInfo v =>
    rw [List.mem_singleton.mp he] at hn
    exact (refsOf_axiom v n).mpr hn
  | quotInfo v =>
    rw [List.mem_singleton.mp he] at hn
    exact (refsOf_quot v n).mpr hn
  | defnInfo v =>
    obtain rfl | rfl : e = v.cnst.type ∨ e = v.value := by simpa [termsOf] using he
    · exact (refsOf_defn v n).mpr (.inl hn)
    · exact (refsOf_defn v n).mpr (.inr hn)
  | thmInfo v =>
    obtain rfl | rfl : e = v.cnst.type ∨ e = v.value := by simpa [termsOf] using he
    · exact (refsOf_thm v n).mpr (.inl hn)
    · exact (refsOf_thm v n).mpr (.inr hn)
  | opaqueInfo v =>
    obtain rfl | rfl : e = v.cnst.type ∨ e = v.value := by simpa [termsOf] using he
    · exact (refsOf_opaque v n).mpr (.inl hn)
    · exact (refsOf_opaque v n).mpr (.inr hn)
  | inductInfo v =>
    rw [List.mem_singleton.mp he] at hn
    exact GraphWalk.graphConst_induct v { consts := {} } hn
  | ctorInfo v =>
    rw [List.mem_singleton.mp he] at hn
    exact GraphWalk.graphConst_ctor v { consts := {} } hn
  | recInfo v =>
    refine GraphWalk.graphConst_rec v { consts := {} } ?_
    rcases List.mem_cons.mp he with rfl | he
    · exact .inl hn
    · obtain ⟨rule, hr, rfl⟩ := List.mem_map.mp he
      exact .inr ⟨rule, hr, hn⟩

/--
info: 'Ix.Cert.GraphRefs.refsOf_mentions' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refsOf_mentions

end Ix.Cert.GraphRefs
