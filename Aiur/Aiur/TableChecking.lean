import Aiur.Tables

namespace Aiur

variable {F : Type}

set_option linter.unusedSimpArgs false

private theorem duplicate_none {names seen : List String}
    (checked : findDuplicate names seen = none) : names.Nodup ∧ ∀ name ∈ names, name ∉ seen := by
  induction names generalizing seen with
  | nil => simp
  | cons name names ih =>
      simp only [findDuplicate] at checked
      split at checked
      · cases checked
      · rename_i fresh
        obtain ⟨distinct, separate⟩ := ih checked
        refine ⟨List.nodup_cons.mpr ⟨?_, distinct⟩, ?_⟩
        · intro member
          exact separate name member (by simp)
        · intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact fresh
          · intro old
            exact separate value member (by simp [old])

theorem typecheck_tables [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) :
    (program.functions.map (·.name) ++ program.maps.map (·.name)).Nodup ∧
      checkTables program = .ok () := by
  unfold typecheck at checked
  obtain ⟨_, _, rest⟩ := except_bind_ok.mp checked
  cases repeated : findDuplicate (program.functions.map (·.name) ++ program.maps.map (·.name)) [] with
  | some name => simp [repeated, bind, Except.bind] at rest
  | none =>
      simp only [repeated, pure_bind] at rest
      obtain ⟨done, tables, _⟩ := except_bind_ok.mp rest
      cases done
      exact ⟨(duplicate_none repeated).1, tables⟩

theorem typecheck_table [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {table : Table F} (member : table ∈ program.tables) :
    checkTable program table = .ok () := by
  have checked := (typecheck_tables checked).2
  unfold checkTables at checked
  split at checked
  · cases checked
  · simp only [pure_bind] at checked
    obtain ⟨done, tables, _⟩ := except_bind_ok.mp checked
    cases done
    have combined := congrArg (fun r : Except CheckError PUnit =>
      r >>= fun _ => (pure () : Except CheckError Unit)) tables
    exact forIn_ok (by simpa [bind, Except.bind, pure, Except.pure] using combined) table member

theorem typecheck_map [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {map : MapDecl} (member : map ∈ program.maps) :
    checkMap program map = .ok () := by
  have checked := (typecheck_tables checked).2
  unfold checkTables at checked
  split at checked
  · cases checked
  · simp only [pure_bind] at checked
    obtain ⟨done, _, rest⟩ := except_bind_ok.mp checked
    cases done
    exact forIn_ok rest map member

theorem requirePointerFree_ok {decls : Declarations} {context : String} {type : Ty}
    (checked : requirePointerFree decls context type = .ok ()) : type.pointerFree decls = true := by
  cases free : type.pointerFree decls <;> simp_all [requirePointerFree]

theorem table_pointerFree {program : Program F} {table : Table F}
    (checked : checkTable program table = .ok ()) : table.rowType.pointerFree program.enums = true := by
  unfold checkTable at checked
  obtain ⟨_, _, rest⟩ := except_bind_ok.mp checked
  obtain ⟨done, free, _⟩ := except_bind_ok.mp rest
  cases done
  exact requirePointerFree_ok free

theorem map_pointerFree [DecidableEq F] {program : Program F} {map : MapDecl}
    (checked : checkMap program map = .ok ()) :
    (Ty.tuple (map.params.map Prod.snd)).pointerFree program.enums = true ∧
      map.result.pointerFree program.enums = true := by
  unfold checkMap at checked
  obtain ⟨_, _, rest⟩ := except_bind_ok.mp checked
  obtain ⟨_, _, rest⟩ := except_bind_ok.mp rest
  obtain ⟨done, input, rest⟩ := except_bind_ok.mp rest
  cases done
  obtain ⟨done, output, _⟩ := except_bind_ok.mp rest
  cases done
  exact ⟨requirePointerFree_ok input, requirePointerFree_ok output⟩

theorem table_row_typed {program : Program F} {table : Table F}
    (checked : checkTable program table = .ok ()) {value : Constant F} (member : value ∈ table.rows) :
    value.type = table.rowType ∧ value.wellFormed program.enums = true := by
  unfold checkTable at checked
  obtain ⟨_, _, rest⟩ := except_bind_ok.mp checked
  obtain ⟨_, _, rows⟩ := except_bind_ok.mp rest
  obtain ⟨index, bounded, same⟩ := List.mem_iff_getElem.mp member
  have accepted := forIn_ok rows (value, index) (by
    have mem := List.getElem_mem (l := table.rows.zipIdx) (n := index) (by simpa using bounded)
    simpa [List.getElem_zipIdx, same] using mem)
  by_cases typed : value.type = table.rowType
  · by_cases formed : value.wellFormed program.enums = true
    · exact ⟨typed, formed⟩
    · simp [checkTableRow, typed, formed, bind, Except.bind, pure, Except.pure] at accepted
  · simp [checkTableRow, typed, bind, Except.bind] at accepted

theorem checkMap_spec [DecidableEq F] {program : Program F} {map : MapDecl}
    (checked : checkMap program map = .ok ()) :
    ∃ inputs outputs, program.findTable? map.input = some inputs ∧
      program.findTable? map.output = some outputs ∧
      inputs.rowType = .tuple (map.params.map Prod.snd) ∧ outputs.rowType = map.result ∧
      inputs.rows.length = outputs.rows.length ∧ inputs.rows.Nodup := by
  unfold checkMap at checked
  obtain ⟨_, _, rest⟩ := except_bind_ok.mp checked
  obtain ⟨_, _, rest⟩ := except_bind_ok.mp rest
  obtain ⟨_, _, rest⟩ := except_bind_ok.mp rest
  obtain ⟨_, _, rest⟩ := except_bind_ok.mp rest
  cases duplicate : findDuplicate (map.params.map Prod.fst) [] with
  | some name => simp [duplicate, bind, Except.bind] at rest
  | none =>
    simp only [duplicate, pure_bind] at rest
    cases hi : program.findTable? map.input with
    | none => simp [hi] at rest
    | some inputs =>
      cases ho : program.findTable? map.output with
      | none => simp [hi, ho] at rest
      | some outputs =>
        simp only [hi, ho] at rest
        obtain ⟨done, inputType, rest⟩ := except_bind_ok.mp rest
        obtain ⟨done, outputType, rest⟩ := except_bind_ok.mp rest
        cases done
        by_cases sameLength : inputs.rows.length = outputs.rows.length
        · by_cases unique : inputs.rows.Nodup
          · exact ⟨inputs, outputs, rfl, rfl, (requireType_ok inputType).symm,
              (requireType_ok outputType).symm, sameLength, unique⟩
          · simp [sameLength, unique, bind, Except.bind] at rest
        · simp [sameLength, bind, Except.bind] at rest

theorem map_function_absent [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {map : MapDecl} (member : map ∈ program.maps) :
    program.findFunction? map.name = none := by
  have disjoint := (List.nodup_append.mp (typecheck_tables checked).1).2.2
  apply List.find?_eq_none.mpr
  intro fn present
  have different : fn.name ≠ map.name := fun same =>
    disjoint fn.name (List.mem_map.mpr ⟨fn, present, rfl⟩) map.name
      (List.mem_map.mpr ⟨map, member, rfl⟩) same
  simpa using different

theorem find_of_unique_key [DecidableEq β] (key : α → β) {rows : List α} {row : α}
    (unique : (rows.map key).Nodup) (member : row ∈ rows) :
    rows.find? (fun candidate => decide (key candidate = key row)) = some row := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
      have distinct := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | member
      · simp [List.find?_cons]
      · have different : key head ≠ key row := by
          intro same
          exact distinct.1 (List.mem_map.mpr ⟨row, member, same.symm⟩)
        simp [List.find?_cons, different, ih distinct.2 member]

theorem map_found_of_mem [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {map : MapDecl} (member : map ∈ program.maps) :
    program.findMap? map.name = some map := by
  have unique := (List.nodup_append.mp (typecheck_tables checked).1).2.1
  have found := find_of_unique_key MapDecl.name unique member
  simpa only [Program.findMap?, beq_eq_decide] using found

theorem mapRows_unique [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {map : MapDecl} (member : map ∈ program.maps) :
    ((program.mapRows map).map Prod.fst).Nodup := by
  obtain ⟨inputs, outputs, hi, ho, _, _, sameLength, unique⟩ :=
    checkMap_spec (typecheck_map checked member)
  simpa only [Program.mapRows, hi, ho, List.map_fst_zip (Nat.le_of_eq sameLength)] using unique

theorem mapRows_typed [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {map : MapDecl} (member : map ∈ program.maps)
    {key value : Constant F} (row : (key, value) ∈ program.mapRows map) :
    key.type = .tuple (map.params.map Prod.snd) ∧ key.wellFormed program.enums = true ∧
      value.hasType program.enums map.result = true := by
  obtain ⟨inputs, outputs, hi, ho, inputType, outputType, _, _⟩ :=
    checkMap_spec (typecheck_map checked member)
  simp only [Program.mapRows, hi, ho] at row
  have a := table_row_typed (typecheck_table checked (List.mem_of_find?_eq_some hi)) (List.of_mem_zip row).1
  have b := table_row_typed (typecheck_table checked (List.mem_of_find?_eq_some ho)) (List.of_mem_zip row).2
  exact ⟨a.1.trans inputType, a.2, by simp [Value.hasType, b.1, b.2, outputType]⟩

theorem mapEntry_mem_iff {program : Program F} {map : MapDecl} {entry : MapEntry F} :
    entry ∈ program.mapEntries map ↔ (.tuple entry.args, entry.result) ∈ program.mapRows map := by
  simp only [Program.mapEntries, List.mem_filterMap]
  constructor
  · rintro ⟨⟨key, value⟩, member, same⟩
    cases key with
    | field | construct => cases same
    | ptr _ address => exact Empty.elim address
    | tuple args => cases same; exact member
  · intro member
    exact ⟨(.tuple entry.args, entry.result), member, by cases entry; rfl⟩

/-- On checked tables, membership and executable lookup coincide. -/
theorem lookupMap_of_entry [DecidableEq F] {program : Program F}
    (checked : typecheck program = .ok ()) {map : MapDecl} (member : map ∈ program.maps)
    {entry : MapEntry F} (row : entry ∈ program.mapEntries map) :
    lookupMap program map.name (entry.args.map (Constant.toValue (Address := A))) = .ok entry.result := by
  have row := mapEntry_mem_iff.mp row
  obtain ⟨inputType, inputFormed, outputTyped⟩ := mapRows_typed checked member row
  have types : map.params.map Prod.snd = (entry.args.map (Constant.toValue (Address := A))).map Value.type := by
    simp only [Value.type, Ty.tuple.injEq] at inputType
    simpa only [List.map_map, Function.comp_def, Constant.toValue_type] using inputType.symm
  have arity : map.params.length = entry.args.length := by
    have := congrArg List.length types
    simpa using this
  have formed : ∀ arg ∈ entry.args.map (Constant.toValue (Address := A)), arg.wellFormed program.enums = true := by
    simpa [Value.wellFormed] using inputFormed
  have arguments := checked_arguments program.enums map.name map.params _ types formed
  have found := find_of_unique_key Prod.fst (mapRows_unique checked member) row
  have key : (Value.tuple (entry.args.map (Constant.toValue (Address := A)))).toConstant? =
      some (.tuple entry.args) := by
    simpa only [Constant.toValue, Value.mapAddress, show (Constant.toValue (Address := A) : Constant F → Value F A) = Value.mapAddress Empty.elim from rfl] using
      (Constant.toConstant_toValue (A := A) (.tuple entry.args))
  simp only [lookupMap, map_found_of_mem checked member, List.length_map, arity,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
  have combined := congrArg (fun r : Except EvalError Unit => r >>= fun _ =>
    (pure entry.result : Except EvalError (Constant F))) arguments
  simp only [bind_assoc, pure_bind] at combined
  simpa only [key, found, outputTyped, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    pure_bind, bind_assoc, bind, Except.bind, pure, Except.pure] using combined

end Aiur
