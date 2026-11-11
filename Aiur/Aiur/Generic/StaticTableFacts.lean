import Aiur.Typecheck
import Aiur.ExceptFacts
import Aiur.TableUniqueness

/-! # Checking a static table program from facts about its tables

A `Generic.Source` carries `typecheck tables = .ok ()` for its static tables.
Evaluating that check on large generated tables is out of the kernel's reach
(a table of 65,536 rows costs minutes and tens of gigabytes, and the map
inputs' distinctness is quadratic). These lemmas reduce it to facts about the
tables that their generators prove: every row has the row type, and every map
input table's rows are distinct. -/

namespace Aiur

variable {F : Type}

theorem forIn_ok_of {ε α : Type} {action : α → Except ε Unit} {items : List α}
    (h : ∀ item ∈ items, action item = .ok ()) :
    (do for item in items do action item : Except ε Unit) = .ok () := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    have tail := ih (fun x hx => h x (by simp [hx]))
    simpa [List.forIn_cons, h item (by simp), bind, Except.bind, pure, Except.pure] using tail

theorem checkTable_ok_of {program : Program F} {table : Table F}
    (names : table.rowType.checkNames program.enums = .ok ())
    (free : table.rowType.pointerFree program.enums = true)
    (rows : ∀ row ∈ table.rows, row.type = table.rowType ∧ row.wellFormed program.enums = true) :
    checkTable program table = .ok () := by
  have each : ∀ entry ∈ table.rows.zipIdx, checkTableRow program table entry = .ok () := by
    intro entry member
    obtain ⟨typed, formed⟩ := rows entry.1 (List.fst_mem_of_mem_zipIdx member)
    simp [checkTableRow, typed, formed]
  unfold checkTable
  simp only [names, requirePointerFree, free, Except.mapError, if_true, bind, Except.bind, pure,
    Except.pure]
  simpa [bind, Except.bind, pure, Except.pure] using forIn_ok_of each

theorem checkMap_ok_of [DecidableEq F] {program : Program F} {map : MapDecl}
    {inputs outputs : Table F}
    (paramNames : ∀ p ∈ map.params, p.2.checkNames program.enums = .ok ())
    (resultNames : map.result.checkNames program.enums = .ok ())
    (paramsFree : (Ty.tuple (map.params.map Prod.snd)).pointerFree program.enums = true)
    (resultFree : map.result.pointerFree program.enums = true)
    (distinctParams : findDuplicate (map.params.map Prod.fst) [] = none)
    (input : program.findTable? map.input = some inputs)
    (output : program.findTable? map.output = some outputs)
    (inputType : inputs.rowType = .tuple (map.params.map Prod.snd))
    (outputType : outputs.rowType = map.result)
    (lengths : inputs.rows.length = outputs.rows.length)
    (distinct : inputs.rows.Nodup) :
    checkMap program map = .ok () := by
  have each : ∀ p ∈ map.params,
      (fun (p : String × Ty) => (p.2.checkNames program.enums).mapError CheckError.invalidDeclarations) p
        = .ok () := by
    intro p member
    simp [paramNames p member, Except.mapError]
  unfold checkMap
  have loop := forIn_ok_of each
  simp only [requirePointerFree, paramsFree, resultFree, distinctParams, input, output,
    requireType, inputType, outputType, lengths, resultNames, tableRowsNodup_eq, distinct,
    Except.mapError, bind, Except.bind, pure, Except.pure, if_true, decide_true,
    Bool.not_true, bne_self_eq_false] at loop ⊢
  simpa [bind, Except.bind, pure, Except.pure] using loop

theorem typecheck_ok_of [DecidableEq F] {program : Program F}
    (noFunctions : program.functions = [])
    (declarations : checkDeclarations program.enums = .ok ())
    (distinctMaps : findDuplicate (program.maps.map (·.name)) [] = none)
    (distinctTables : findDuplicate (program.tables.map (·.name)) [] = none)
    (tables : ∀ table ∈ program.tables, checkTable program table = .ok ())
    (maps : ∀ map ∈ program.maps, checkMap program map = .ok ()) :
    typecheck program = .ok () := by
  have tableLoop := forIn_ok_of tables
  have mapLoop := forIn_ok_of maps
  unfold typecheck checkTables
  simp only [noFunctions, declarations, List.map_nil, List.nil_append, distinctMaps,
    distinctTables, Except.mapError, bind, Except.bind, pure, Except.pure] at tableLoop mapLoop ⊢
  simp [tableLoop, mapLoop, List.forIn_nil, bind, Except.bind, pure, Except.pure]

end Aiur
