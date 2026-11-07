import IxCC.Aiur.OracleEval.Op
import IxCC.Vendor.Ix.Aiur.Compiler.UnitCounter

/-! The observations needed to relate the affine analyzer to real replay.
Memory, gadgets, and advice are unconstrained here except for register count;
their full meanings remain in OracleEval. Constrained calls remain exact. -/

namespace IxCC.Aiur.CounterAnalysis

open _root_.IxCC.Vendor.Aiur (G)
open _root_.IxCC.Vendor.Aiur.Bytecode
open OracleEval (Values)

structure Call where
  function : Nat
  inputs : Values
  outputs : Values
  deriving DecidableEq, Repr

def callOf : Message → Option Call
  | .function function inputs outputs => some ⟨function, inputs, outputs⟩
  | .memory .. | .gadget .. => none

def calls (messages : List Message) : List Call := messages.filterMap callOf

theorem call_mem (messages : List Message) (function : Nat) (inputs outputs : Values) :
    ⟨function, inputs, outputs⟩ ∈ calls messages ↔ .function function inputs outputs ∈ messages := by
  simp only [calls, List.mem_filterMap]
  constructor
  · rintro ⟨message, member, equal⟩
    cases message <;> simp_all [callOf]
  · intro member
    exact ⟨.function function inputs outputs, member, rfl⟩

inductive ReadList (values : Array G) : List Nat → Values → Prop where
  | nil : ReadList values [] []
  | cons {index : Nat} {value : G} {indices : List Nat} {inputs : Values}
      (read : values[index]? = some value) (rest : ReadList values indices inputs) :
      ReadList values (index :: indices) (value :: inputs)

def Reads (values : Array G) (indices : Array Nat) (inputs : Values) : Prop :=
  ReadList values indices.toList inputs

def OutputFact (op : Op) (values : Array G) (outputs : Values) : Prop :=
  match op with
  | .const value => outputs = [value]
  | .add left right => ∃ a b, values[left]? = some a ∧ values[right]? = some b ∧ outputs = [a + b]
  | .sub left right => ∃ a b, values[left]? = some a ∧ values[right]? = some b ∧ outputs = [a - b]
  | .mul left right => ∃ a b, values[left]? = some a ∧ values[right]? = some b ∧ outputs = [a * b]
  | _ => outputs.length = UnitCounter.outputCount op

def CallFact (op : Op) (values : Array G) (outputs : Values) (before after : List Call) : Prop :=
  match op with
  | .call function indices _ false =>
      ∃ inputs, Reads values indices inputs ∧ after = ⟨function, inputs, outputs⟩ :: before
  | _ => after = before

def Effect (op : Op) (before after : OracleEval.State) : Prop :=
  ∃ outputs, after.values = before.values ++ outputs.toArray ∧
    OutputFact op before.values outputs ∧
    CallFact op before.values outputs (calls before.demandsRev) (calls after.demandsRev)

theorem bind_success {ε α β : Type} {source : Except ε α} {next : α → Except ε β} {result : β}
    (success : (source >>= next) = .ok result) :
    ∃ value, source = .ok value ∧ next value = .ok result := by
  cases source with
  | error error => cases success
  | ok value => exact ⟨value, rfl, success⟩

end IxCC.Aiur.CounterAnalysis
