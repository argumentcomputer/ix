/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Expr
import Ix.Theory.Certified.Accept

/-!
# Semantic postcondition for kernel typing

`ModelTyping` states the postcondition that the production inference and
conversion proofs must establish in the new model. It ties both annotated
endpoints to the actual `KExpr` trees. It is not defined by checker success,
and this module does not assume that checker success establishes it.

The current producers transport existing evidence through hash equality and
interning. The consistency theorem constructs a dependency model from an
admitted environment and rules out this postcondition at the primitive False.
The remaining checker refinement must produce the postcondition for each
successful inference/declaration path.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model Theory.Model.SetTheory

universe u v
variable {β : Type u} {m : Mode}

/-- An annotated typing judgment whose two erasures read the exact kernel
term and type. This is a semantic specification, not a runtime acceptance bit. -/
def ModelTyping (resolve : Address → Option (ConstRef β))
    (entries : Model.Environment β) (context : Model.Context β)
    (term type : KExpr m) : Prop :=
  ∃ e A : AExpr β,
    readExpr? resolve term = some e.erase ∧
    readExpr? resolve type = some A.erase ∧
    TypingClaim.{u,v} entries context e A

namespace ModelTyping

/-- The sort rule applies to the exact source and production successor type. -/
theorem sort {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β}
    (level : KUniv m) (info : ExprInfo m) :
    ModelTyping.{u,v} resolve entries context (.sort level info)
      (KExpr.mkSort (KUniv.mkSucc level)) := by
  refine ⟨.sort (readLevel level), .sort (.succ (readLevel level)), rfl, ?_,
    TypingClaim.sort _⟩
  simp only [readExpr?_mkSort, readLevel_mkSucc, AExpr.erase]

/-- Reusing a hash-equal term preserves the semantic typing postcondition
under the comparison's existing address-faithfulness hypothesis. -/
theorem of_beq {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β}
    {left right type : KExpr m} (faithful : left.AddrFaithful right)
    (equal : (left == right) = true)
    (typed : ModelTyping.{u,v} resolve entries context right type) :
    ModelTyping.{u,v} resolve entries context left type := by
  obtain ⟨e, A, he, hA, typing⟩ := typed
  exact ⟨e, A, (beq_readExpr? faithful equal).trans he, hA, typing⟩

/-- Interning a typed candidate preserves its semantic typing postcondition. -/
theorem internExpr {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β}
    {table : InternTable m} {term type : KExpr m}
    (coherent : table.WF)
    (faithful : KExpr.KeyCollisionFree fun e => table.ExprSupport e ∨ e = term)
    (typed : ModelTyping.{u,v} resolve entries context term type) :
    ModelTyping.{u,v} resolve entries context (table.internExpr term).1 type := by
  obtain ⟨e, A, he, hA, typing⟩ := typed
  exact ⟨e, A, (internExpr_readExpr? coherent faithful).trans he, hA, typing⟩

/-- Interning the inferred type also preserves the semantic judgment. -/
theorem internType {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β}
    {table : InternTable m} {term type : KExpr m}
    (coherent : table.WF)
    (faithful : KExpr.KeyCollisionFree fun e => table.ExprSupport e ∨ e = type)
    (typed : ModelTyping.{u,v} resolve entries context term type) :
    ModelTyping.{u,v} resolve entries context term (table.internExpr type).1 := by
  obtain ⟨e, A, he, hA, typing⟩ := typed
  exact ⟨e, A, he, (internExpr_readExpr? coherent faithful).trans hA, typing⟩

/-- A closed kernel typing judgment at primitive False contradicts the
set-theoretic model. Dependency realizations are constructed by admission. -/
theorem no_false [DecidableEq β]
    {resolve : Address → Option (ConstRef β)}
    {signature : Certified.PrimitiveSignature β} {store : Theory.Store β}
    (admitted : Certified.AdmittedEnvironment.{u,v} signature store)
    {term type : KExpr m}
    (isFalse : readExpr? resolve type = some signature.falseExpr)
    (typed : ModelTyping.{u,v} resolve admitted.entries [] term type)
    (V : Type v) [SetTheory V] : False := by
  obtain ⟨e, A, _he, hA, typing⟩ := typed
  have erased : A.erase = signature.falseExpr := Option.some.inj (hA.symm.trans isFalse)
  have falseExpr : A = .const signature.falseType [] := AExpr.eq_const_of_erase_eq erased
  obtain ⟨constants, compatible⟩ := admitted.model V
  have member := (typing V constants compatible.realizes [] (fun _ => empty)
    (Model.Context.valid_nil constants [] (fun _ => empty))).2.2
  rw [falseExpr] at member
  simp only [interp, List.map_nil, compatible.falseValue] at member
  exact not_mem_empty _ member

end ModelTyping

/-- A successful production universe equality supplies semantic conversion
between the corresponding annotated sorts in every compatible model. -/
theorem sort_conversion {entries : Model.Environment β} {context : Model.Context β}
    {left right : KUniv m} (faithful : left.AddrFaithful right)
    (boundLeft : left.size < UInt64.size) (boundRight : right.size < UInt64.size)
    (accepted : Kernel.univEq left right = true) :
    ConversionClaim.{u,v} entries context (.sort (readLevel left)) (.sort (readLevel right)) :=
  ConversionClaim.sort (Theory.VLevel.equiv_def.mp
    (univEq_sound faithful boundLeft boundRight accepted))

end Ix.Kernel.Consistency
