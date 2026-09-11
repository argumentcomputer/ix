module
public import Ix.Ixby.Aiur.ObjectsUnique
import all Ix.Aiur.Goldilocks

/-! The complete compiled constructor-declaration reader.

The certificate links the byte, identity, equality, uniqueness, and recursive
declaration readers in one bytecode toplevel. Input bytes, constructor count,
and memory capacity are explicit premises here. `ObjectsAdmission` supplies
the byte premise and preserves table capacity for a loaded declaration prefix;
`ObjectsProgramPrefix` derives the count bound from the actual program header
and composes this parser call. Whole-program admission remains open. These results concern the
Lean evaluator, not the compiler, trace, or AIR relation.
-/

namespace Ix.Ixby.AiurBackend.ObjectsDeclarations

deriving instance DecidableEq for Aiur.Bytecode.Op
deriving instance ReflBEq, LawfulBEq for Ix.Ixby.CtorId

public section
@[expose] section

open Aiur Aiur.Bytecode Aiur.Bytecode.Eval Ix.Ixby
open ObjectsRefinement ObjectsMemory ObjectsStore ObjectsTable ObjectsParser ObjectsIdentity ObjectsEquality ObjectsUnique

/-- Eleven little-endian u32 words, without losing any digest limb. -/
structure DeclarationBytes where
  a : WordBytes
  b : WordBytes
  c : WordBytes
  d : WordBytes
  e : WordBytes
  f : WordBytes
  g : WordBytes
  h : WordBytes
  member : WordBytes
  tag : WordBytes
  fields : WordBytes

def DeclarationBytes.idWords (d : DeclarationBytes) : List WordBytes :=
  [d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h, d.member, d.tag]
def DeclarationBytes.bytes (d : DeclarationBytes) : List UInt8 :=
  d.idWords.flatMap WordBytes.bytes ++ d.fields.bytes
def DeclarationBytes.raw (d : DeclarationBytes) : RawDecl :=
  ⟨⟨d.a.field, d.b.field, d.c.field, d.d.field, d.e.field, d.f.field,
    d.g.field, d.h.field, d.member.field, d.tag.field⟩, d.fields.field⟩

def DeclarationBytes.declaration (d : DeclarationBytes) : CtorDecl := {
  id := {
    block := ⟨natOfBytesLE ([d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h].flatMap WordBytes.bytes).toArray, by
      obtain ⟨id, _, same, _, _⟩ := decode_id_words d.a d.b d.c d.d d.e d.f d.g d.h d.member d.tag
      rw [← same]
      exact id.block.isLt⟩
    member := d.member.field.n
    tag := d.tag.field.n }
  fields := d.fields.field.n }

theorem declaration_bytes_length (d : DeclarationBytes) : d.bytes.length = 44 := by
  simp [DeclarationBytes.bytes, DeclarationBytes.idWords, WordBytes.bytes]

theorem declaration_decoded (d : DeclarationBytes) :
    d.raw.id.decode = some d.declaration.id := by
  obtain ⟨id, decoded, block, member, tag⟩ :=
    decode_id_words d.a d.b d.c d.d d.e d.f d.g d.h d.member d.tag
  have equal : id = d.declaration.id := by
    cases id with
    | mk blockId memberId tagId =>
      simp only [DeclarationBytes.declaration, word_field_codec] at block member tag ⊢
      cases blockId
      simp_all
  exact decoded.trans (congrArg some equal)

/-- The semantic acceptance condition: supported field counts and no repeated
full constructor name. Constructor-table length is bounded separately. -/
def Valid (decls : List DeclarationBytes) : Prop :=
  (∀ d ∈ decls, d.declaration.fields ≤ 16) ∧
    (decls.map (fun d => d.declaration.id)).Nodup

instance (decls : List DeclarationBytes) : Decidable (Valid decls) := by
  unfold Valid
  infer_instance

theorem declaration_fields (d : DeclarationBytes) : d.declaration.fields = d.fields.field.n := by
  simp only [DeclarationBytes.declaration]

theorem valid_cons (d : DeclarationBytes) (decls : List DeclarationBytes) :
    Valid (d :: decls) ↔ d.declaration.fields ≤ 16 ∧
      d.declaration.id ∉ decls.map (fun d => d.declaration.id) ∧ Valid decls := by
  simp only [Valid, List.mem_cons, forall_eq_or_imp, List.map_cons, List.nodup_cons]
  constructor
  · rintro ⟨⟨head, tail⟩, fresh, unique⟩
    exact ⟨head, fresh, tail, unique⟩
  · rintro ⟨head, fresh, tail, unique⟩
    exact ⟨⟨head, tail⟩, fresh, unique⟩

def guardOps : Array Aiur.Bytecode.Op :=
  #[.const 16, .const 1, .add 30 31, .u32LessThan 29 32, .const 1,
    .assertEq #[33] #[34] (some "IxBy constructor fields"), .const 1, .sub 1 35]
def advanceOps : Array Aiur.Bytecode.Op := #[.const 1, .sub 1 39]
def storeOps : Array Aiur.Bytecode.Op :=
  #[.const 0, .store #[41, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 29, 37]]
def uniquenessArgs : Array Nat := #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 37, 40]
def identityArgs : Array Nat := #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def headerOps (reader identity : Nat) : Array Aiur.Bytecode.Op :=
  #[.call identity #[0] 11 false] ++ inlineWordOps reader 13 12 ++ guardOps

def declarationsStep (reader identity unique self selector : Nat) : Aiur.Bytecode.Block := {
  ops := headerOps reader identity ++ (#[.call self #[20, 36] 2 false] ++ advanceOps ++
      #[.call unique uniquenessArgs 0 false] ++ storeOps),
  ctrl := .return selector #[42, 38] }

def declarationsBody (reader identity unique self zeroSelector consSelector : Nat) : Aiur.Bytecode.Block :=
  emptyTableBody zeroSelector (some (declarationsStep reader identity unique self consSelector))

/-- Certifies both branches, including every operation, call index, argument,
assertion, selector, and output. It does not merely certify the zero case. -/
def checkDeclarations (f : Aiur.Bytecode.Function)
    (reader identity unique self zeroSelector consSelector : Nat) : Bool :=
  match f.body.ctrl with
  | .match count zeros (some step) =>
    match zeros.toList with
    | [(tag, zero)] =>
      decide (f.layout.inputSize = 2 ∧ f.body.ops = #[] ∧ count = 1 ∧ tag = 0) &&
        checkReturnBlock zero (emptyTableBranch zeroSelector).ops zeroSelector #[4, 0] &&
        checkReturnBlock step (declarationsStep reader identity unique self consSelector).ops consSelector #[42, 38]
    | _ => false
  | _ => false

theorem declarations_checked (f : Aiur.Bytecode.Function)
    (reader identity unique self zeroSelector consSelector : Nat)
    (checked : checkDeclarations f reader identity unique self zeroSelector consSelector = true) :
    f.layout.inputSize = 2 ∧ f.body = declarationsBody reader identity unique self zeroSelector consSelector := by
  unfold checkDeclarations at checked
  split at checked
  · rename_i count zeros step ctrl
    split at checked
    · rename_i tag zero arms
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨basic, zeroChecked⟩, stepChecked⟩ := checked
      obtain ⟨input, ops, countEq, tagEq⟩ := of_decide_eq_true basic
      have zerosEq : zeros = #[(tag, zero)] := Array.toList_inj.mp arms
      have zeroEq := return_block_checked zero _ _ _ zeroChecked
      have stepEq := return_block_checked step _ _ _ stepChecked
      refine ⟨input, ?_⟩
      cases f with
      | mk b layout entry constrained => cases b; simp_all [declarationsBody, emptyTableBody, emptyTableBranch, declarationsStep]
    · simp at checked
  · simp at checked

/-- Callee indices are parameters because pruning relocates them. Selectors
are also explicit, despite all current production instances using 0/1. -/
structure DeclarationCode where
  reader : Nat
  identity : Nat
  comparer : Nat
  unique : Nat
  self : Nat
  byteSelector : Nat := 0
  idSelector : Nat := 0
  compareSelector : Nat := 0
  uniqueZero : Nat := 0
  uniqueCons : Nat := 1
  zeroSelector : Nat := 0
  consSelector : Nat := 1

/-- Resolved functions and checked shapes, all in the same toplevel. No
execution result is assumed for the recursive parser or its recursive callee. -/
structure CheckedCode (t : Bytecode.Toplevel) (code : DeclarationCode) where
  byteFn : Aiur.Bytecode.Function
  idFn : Aiur.Bytecode.Function
  compareFn : Aiur.Bytecode.Function
  uniqueFn : Aiur.Bytecode.Function
  parserFn : Aiur.Bytecode.Function
  byteFunction : t.functions[code.reader]? = some byteFn
  idFunction : t.functions[code.identity]? = some idFn
  compareFunction : t.functions[code.comparer]? = some compareFn
  uniqueFunction : t.functions[code.unique]? = some uniqueFn
  parserFunction : t.functions[code.self]? = some parserFn
  byteChecked : checkByteReader byteFn code.byteSelector = true
  idChecked : checkIdReader idFn code.reader code.idSelector = true
  compareChecked : checkIdEq compareFn code.compareSelector = true
  uniqueChecked : checkUnique uniqueFn code.comparer code.unique code.uniqueZero code.uniqueCons = true
  parserChecked : checkDeclarations parserFn code.reader code.identity code.unique code.self code.zeroSelector code.consSelector = true

def checkDeclarationCode (t : Bytecode.Toplevel) (code : DeclarationCode) : Bool :=
  match t.functions[code.reader]?, t.functions[code.identity]?, t.functions[code.comparer]?,
      t.functions[code.unique]?, t.functions[code.self]? with
  | some byteFn, some idFn, some compareFn, some uniqueFn, some parserFn =>
    checkByteReader byteFn code.byteSelector && checkIdReader idFn code.reader code.idSelector &&
      checkIdEq compareFn code.compareSelector &&
      checkUnique uniqueFn code.comparer code.unique code.uniqueZero code.uniqueCons &&
      checkDeclarations parserFn code.reader code.identity code.unique code.self code.zeroSelector code.consSelector
  | _, _, _, _, _ => false

theorem declaration_code_checked (t : Bytecode.Toplevel) (code : DeclarationCode)
    (checked : checkDeclarationCode t code = true) : Nonempty (CheckedCode t code) := by
  unfold checkDeclarationCode at checked
  split at checked
  · rename_i byteFn idFn compareFn uniqueFn parserFn byteFunction idFunction compareFunction uniqueFunction parserFunction
    simp only [Bool.and_eq_true] at checked
    exact ⟨⟨byteFn, idFn, compareFn, uniqueFn, parserFn, byteFunction, idFunction, compareFunction,
      uniqueFunction, parserFunction, checked.1.1.1.1, checked.1.1.1.2, checked.1.1.2, checked.1.2, checked.2⟩⟩
  · simp at checked

/-- Exact immutable store order: terminal Nil first, then Cons cells from the
last declaration to the first. The returned table remains in wire order. -/
def storeDeclarations (st : EvalState) : List DeclarationBytes → EvalState × G
  | [] => let stored := memStore st tableNil; (stored.1, G.ofNat stored.2)
  | d :: ds =>
    let tail := storeDeclarations st ds
    let stored := memStore tail.1 (d.raw.cell tail.2)
    (stored.1, G.ofNat stored.2)

theorem declaration_cell_size (d : DeclarationBytes) (tail : G) : (d.raw.cell tail).size = 13 := rfl

theorem store_declarations_map (st : EvalState) (map : Array G) (decls : List DeclarationBytes) :
    storeDeclarations { st with map } decls =
      ({ (storeDeclarations st decls).1 with map }, (storeDeclarations st decls).2) := by
  induction decls with
  | nil => simp [storeDeclarations]
  | cons d ds ih => simp [storeDeclarations, ih]

theorem store_declarations_io (st : EvalState) (decls : List DeclarationBytes) :
    (storeDeclarations st decls).1.ioBuffer = st.ioBuffer := by
  induction decls with
  | nil => exact mem_store_io st tableNil
  | cons d ds ih => simpa only [storeDeclarations, mem_store_io] using ih

theorem store_declarations_size (st : EvalState) (decls : List DeclarationBytes) :
    bucketSize (storeDeclarations st decls).1 13 ≤ bucketSize st 13 + decls.length + 1 := by
  induction decls with
  | nil => simpa [storeDeclarations, tableNil] using (mem_store_bounds st tableNil).2
  | cons d ds ih =>
    have next := (mem_store_bounds (storeDeclarations st ds).1 (d.raw.cell (storeDeclarations st ds).2)).2
    rw [declaration_cell_size] at next
    change bucketSize (memStore (storeDeclarations st ds).1 (d.raw.cell (storeDeclarations st ds).2)).1 13 ≤ _
    simp only [List.length_cons]
    omega

theorem store_declarations_preserves (st : EvalState) (decls : List DeclarationBytes)
    {width pointer : Nat} {flat : Array G} (read : memLoad st width pointer = .ok flat) :
    memLoad (storeDeclarations st decls).1 width pointer = .ok flat := by
  induction decls with
  | nil => exact mem_store_preserves st tableNil read
  | cons d ds ih => exact mem_store_preserves _ _ ih

theorem store_declarations_prefix (st : EvalState) (decls : List DeclarationBytes)
    {pointer finish : G} {bytes : List UInt8}
    (read : BytePrefix (bytecodeMemory st) pointer bytes finish) :
    BytePrefix (bytecodeMemory (storeDeclarations st decls).1) pointer bytes finish := by
  induction decls with
  | nil => exact byte_prefix_store st tableNil read
  | cons d ds ih => exact byte_prefix_store _ _ ih

theorem raw_declaration_cell_decoded (raw : RawDecl) (decl : CtorDecl) (tail : G)
    (decoded : raw.id.decode = some decl.id) (fields : raw.fields.n = decl.fields)
    (limit : decl.fields ≤ 16) :
    decodeDeclCell (raw.cell tail) = some (.cons decl tail.n) := by
  change (raw.id.decode >>= fun id => if raw.fields.n > 16 then none
    else some (DeclCell.cons ⟨id, raw.fields.n⟩ tail.n)) = _
  rw [decoded, fields]
  simp only [if_neg (Nat.not_lt.mpr limit)]
  rfl

theorem declaration_cell_decoded (d : DeclarationBytes) (tail : G)
    (fields : d.declaration.fields ≤ 16) :
    decodeDeclCell (d.raw.cell tail) = some (.cons d.declaration tail.n) := by
  have fieldsEq : d.raw.fields.n = d.declaration.fields := by
    simp only [DeclarationBytes.raw, DeclarationBytes.declaration]
  exact raw_declaration_cell_decoded d.raw d.declaration tail (declaration_decoded d) fieldsEq fields

/-- The memory relation is established by actual stores, not assumed. At most
`length + 1` cells are inserted; the capacity premise prevents pointer wrap. -/
theorem store_declarations_table (st : EvalState) (decls : List DeclarationBytes)
    (valid : Valid decls) (capacity : decls.length ≤ 16)
    (space : bucketSize st 13 + decls.length + 1 ≤ goldilocksModulus) :
    readTable (bytecodeMemory (storeDeclarations st decls).1) (storeDeclarations st decls).2.n
      decls.length = some (decls.map DeclarationBytes.declaration).toArray := by
  induction decls with
  | nil =>
    have bound := (mem_store_bounds st tableNil).1
    change (memStore st tableNil).2 ≤ bucketSize st 13 at bound
    change readTable (bytecodeMemory (memStore st tableNil).1) (G.ofNat (memStore st tableNil).2).n 0 = some #[]
    rw [field_of_nat_exact _ (by simp only [List.length_nil] at space; omega)]
    exact stored_empty_table st
  | cons d ds ih =>
    obtain ⟨fields, fresh, validTail⟩ := (valid_cons d ds).mp valid
    simp only [List.length_cons] at capacity space
    have tailRead := ih validTail (by omega) (by omega)
    have previousSize := store_declarations_size st ds
    have bound := (mem_store_bounds (storeDeclarations st ds).1 (d.raw.cell (storeDeclarations st ds).2)).1
    rw [declaration_cell_size] at bound
    have pointerBound : (memStore (storeDeclarations st ds).1 (d.raw.cell (storeDeclarations st ds).2)).2 < goldilocksModulus := by
      omega
    have read := stored_declaration_table (storeDeclarations st ds).1 (d.raw.cell (storeDeclarations st ds).2)
      (declaration_cell_size d _) d.declaration _ ds.length _ (declaration_cell_decoded d _ fields) tailRead
      (by simpa using fresh) (by simpa [objectsProfile] using capacity)
    change readTable (bytecodeMemory (memStore (storeDeclarations st ds).1 (d.raw.cell (storeDeclarations st ds).2)).1)
      (G.ofNat (memStore (storeDeclarations st ds).1 (d.raw.cell (storeDeclarations st ds).2)).2).n (ds.length + 1) = _
    rw [field_of_nat_exact _ pointerBound]
    rw [List.map_cons]
    rw [← List.singleton_append, ← List.append_toArray]
    exact read

/-- The emitted comparison uses UInt32, so the byte-derived u32 range is
essential for agreement with the natural-number field limit. -/
theorem field_u32_limit (word : G) (bounded : word.n < 2 ^ 32) :
    word.val.toUInt32 < (17 : G).val.toUInt32 ↔ word.n ≤ 16 := by
  rw [UInt32.lt_iff_toNat_lt, UInt64.toNat_toUInt32]
  change word.n % 2 ^ 32 < 17 ↔ word.n ≤ 16
  rw [Nat.mod_eq_of_lt bounded]
  omega

private theorem guard_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (size : st.map.size = 30) (word : G) (range : word.n < 2 ^ 32) (fields : st.map[29]? = some word)
    (count : Nat) (counter : st.map[1]? = some (G.ofNat (count + 1)))
    (bounded : count + 1 < goldilocksModulus) :
    runOps t fuel guardOps st 0 = if word.n ≤ 16 then
      .ok { st with map := st.map ++ #[16, 1, 17, 1, 1, 1, G.ofNat count] } else .error .assertFailed := by
  obtain ⟨_, fieldsValue⟩ := Array.getElem?_eq_some_iff.mp fields
  obtain ⟨_, counterValue⟩ := Array.getElem?_eq_some_iff.mp counter
  have added : (16 : G) + 1 = 17 := by decide
  have different : (0 : G).val ≠ (1 : G).val := by decide
  have comparison := field_u32_limit word range
  simp at comparison
  by_cases limit : word.n ≤ 16 <;>
    simp +arith [guardOps, run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdxs, readIdx,
      size, fieldsValue, counterValue, added, different, comparison, limit, field_pred count bounded,
      Array.getElem?_push, Array.getElem_push, pushMap, Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply Array.toList_inj.mp
  simp [List.append_assoc]

private theorem advance_eval (t : Bytecode.Toplevel) (fuel : Nat) (st : EvalState)
    (size : st.map.size = 39) (count : Nat) (counter : st.map[1]? = some (G.ofNat (count + 1)))
    (bounded : count + 1 < goldilocksModulus) :
    runOps t fuel advanceOps st 0 = .ok { st with map := st.map ++ #[1, G.ofNat count] } := by
  obtain ⟨_, counterValue⟩ := Array.getElem?_eq_some_iff.mp counter
  simp +arith [advanceOps, run_ops_list, Aiur.Bytecode.Eval.evalOp, readIdx, size, counterValue,
    field_pred count bounded, Array.getElem_push, pushMap,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact (Array.append_push (xs := st.map) (ys := #[1]) (a := G.ofNat count)).symm

private theorem call_pair_result (t : Bytecode.Toplevel) (fuel callee : Nat) (st : EvalState)
    (f : Aiur.Bytecode.Function) (function : t.functions[callee]? = some f)
    (args : Array Nat) (a b x y : G) (arguments : readIdxs st args = .ok #[a, b])
    (arity : f.layout.inputSize = 2) (accepted : Prop) [Decidable accepted] (after : EvalState)
    (executed : evalBlock t fuel f.body { st with map := #[a, b] } =
      if accepted then .error (.earlyReturn #[x, y] after) else .error .assertFailed) (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + 1) (.call callee args 2 unconstrained) st =
      if accepted then .ok { st with map := st.map ++ #[x, y], memory := after.memory, ioBuffer := after.ioBuffer }
      else .error .assertFailed := by
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp function
  by_cases accept : accepted <;>
    simp [Aiur.Bytecode.Eval.evalOp, arguments, bound, found, arity, executed, accept,
      appendMap, setIoBuffer, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem declarations_nonzero (t : Bytecode.Toplevel) (fuel reader identity unique self zeroSelector consSelector : Nat)
    (st : EvalState) (pointer count : G) (nonzero : count ≠ 0) :
    evalBlock t fuel (declarationsBody reader identity unique self zeroSelector consSelector)
        { st with map := #[pointer, count] } =
      evalBlock t fuel (declarationsStep reader identity unique self consSelector) { st with map := #[pointer, count] } := by
  have nonzeroVal : (0 : G).val ≠ count.val := fun equal => nonzero (Subtype.ext equal.symm)
  simp [declarationsBody, emptyTableBody, evalBlock, run_ops_list, evalCtrl, evalMatchArm, evalDefaultBlock,
    readIdx, nonzeroVal, Pure.pure, Except.pure]

private theorem run_single (t : Bytecode.Toplevel) (fuel : Nat) (op : Aiur.Bytecode.Op) (st : EvalState) :
    runOps t fuel #[op] st 0 = Aiur.Bytecode.Eval.evalOp t fuel op st := by
  simp [run_ops_list, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases Aiur.Bytecode.Eval.evalOp t fuel op st <;> rfl

/-- Only the live registers needed after reading one record. Intermediate
byte pointers remain in the actual register array but need no invented values. -/
structure HeaderRegisters (registers : Array G) (raw : RawDecl) (count : Nat) (finish : G) : Prop where
  size : registers.size = 37
  counter : registers[1]? = some (G.ofNat (count + 1))
  suffix : registers[20]? = some finish
  fields : registers[29]? = some raw.fields
  remaining : registers[36]? = some (G.ofNat count)
  identity : All₂ (fun idx value => registers[idx]? = some value) identityArgs.toList raw.id.flat.toList

/-- Actual 44-byte read and arity guard, with all registers needed by the
recursive path. Unsupported u32 arities produce an assertion failure. -/
theorem checked_declaration_header (t : Bytecode.Toplevel) (code : DeclarationCode) (checked : CheckedCode t code)
    (fuel : Nat) (st : EvalState) (d : DeclarationBytes) (count : Nat)
    (bounded : count + 1 < goldilocksModulus) (pointer finish : G)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer d.bytes finish) :
    ∃ registers, HeaderRegisters registers d.raw count finish ∧
      runOps t (fuel + 2) (headerOps code.reader code.identity) { st with map := #[pointer, G.ofNat (count + 1)] } 0 =
        if d.fields.field.n ≤ 16 then .ok { st with map := registers } else .error .assertFailed := by
  obtain ⟨middle, idRead, fieldsRead⟩ := byte_prefix_split (xs := d.idWords.flatMap WordBytes.bytes)
    (ys := d.fields.bytes) bytesRead
  let idState : EvalState := { st with map := #[pointer, G.ofNat (count + 1)] ++ (d.raw.id.flat ++ #[middle]) }
  have idValues : (d.idWords.map WordBytes.field).toArray = d.raw.id.flat := rfl
  have idRun := checked_id_reader_call t fuel code.byteSelector code.idSelector code.reader code.identity 0
    { st with map := #[pointer, G.ofNat (count + 1)] } checked.byteFn checked.idFn
    checked.byteFunction checked.idFunction checked.byteChecked checked.idChecked d.idWords rfl
    pointer middle rfl idRead false
  rw [idValues] at idRun
  change Aiur.Bytecode.Eval.evalOp t (fuel + 2) (.call code.identity #[0] 11 false)
    { st with map := #[pointer, G.ofNat (count + 1)] } = .ok idState at idRun
  have idSize : idState.map.size = 13 := by simp [idState, RawId.flat]
  obtain ⟨wordRegs, wordSize, wordFinish, wordValue, wordRun⟩ := inline_word_prefix t (fuel + 1)
    code.byteSelector code.reader 12 idState checked.byteFn checked.byteFunction checked.byteChecked
    middle finish d.fields (by simp [idState, RawId.flat]) fieldsRead
  rw [idSize] at wordRun
  let wordState : EvalState := { idState with map := idState.map ++ wordRegs }
  have size : wordState.map.size = 30 := by simp [wordState, idSize, wordSize]
  have fields : wordState.map[29]? = some d.fields.field := by
    simpa [wordState, Array.getElem?_append, idSize] using wordValue
  have counter : wordState.map[1]? = some (G.ofNat (count + 1)) := by
    simp [wordState, idState, RawId.flat, Array.getElem?_append]
  have guardRun := guard_eval t (fuel + 2) wordState size d.fields.field (word_field_bound d.fields)
    fields count counter bounded
  let registers := wordState.map ++ #[16, 1, 17, 1, 1, 1, G.ofNat count]
  refine ⟨registers, ?_, ?_⟩
  · refine ⟨by simp [registers, size], ?_, ?_, ?_, ?_, ?_⟩
    · simpa [registers, Array.getElem?_append, size] using counter
    · simpa [registers, wordState, Array.getElem?_append, size, idSize, wordSize] using wordFinish
    · simpa [registers, Array.getElem?_append, size, DeclarationBytes.raw] using fields
    · simp [registers, size]
    · simp only [identityArgs, RawId.flat]
      repeat' first | apply All₂.cons | exact All₂.nil
      all_goals simp [registers, wordState, idState, RawId.flat, Array.getElem?_append]
  · rw [headerOps, run_ops_append, run_ops_append, run_single, idRun]
    simp only [Except.bind, wordRun]
    exact guardRun

private theorem append_registers {registers extra : Array G} {indices : List Nat} {values : List G}
    (found : All₂ (fun idx value => registers[idx]? = some value) indices values) :
    All₂ (fun idx value => (registers ++ extra)[idx]? = some value) indices values := by
  induction found with
  | nil => exact .nil
  | cons head tail ih =>
    refine .cons ?_ ih
    have bound := (Array.getElem?_eq_some_iff.mp head).1
    simpa only [Array.getElem?_append, if_pos bound] using head

private theorem header_id_arguments (st : EvalState) (registers extra : Array G) (raw : RawDecl)
    (count : Nat) (finish : G) (header : HeaderRegisters registers raw count finish) :
    readIdxs { st with map := registers ++ extra } identityArgs = .ok raw.id.flat := by
  simpa only [Array.toArray_toList] using read_idxs_of_all₂ { st with map := registers ++ extra }
    identityArgs.toList raw.id.flat.toList (append_registers header.identity)

private theorem header_recursive_arguments (st : EvalState) (registers : Array G) (raw : RawDecl)
    (count : Nat) (finish : G) (header : HeaderRegisters registers raw count finish) :
    readIdxs { st with map := registers } #[20, 36] = .ok #[finish, G.ofNat count] := by
  simp [readIdxs, readIdx, header.suffix, header.remaining, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem header_unique_arguments (st : EvalState) (registers : Array G) (raw : RawDecl)
    (count : Nat) (next tail finish : G) (header : HeaderRegisters registers raw count next) :
    readIdxs { st with map := registers ++ #[tail, finish, 1, G.ofNat count] } uniquenessArgs =
      .ok (raw.id.flat ++ #[tail, G.ofNat count]) := by
  change readIdxs _ (identityArgs ++ #[37, 40]) = _
  rw [read_idxs_append, header_id_arguments st registers _ raw count next header]
  simp [readIdxs, readIdx, header.size, Array.getElem?_append, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem header_store_arguments (st : EvalState) (registers : Array G) (raw : RawDecl)
    (count : Nat) (next tail finish : G) (header : HeaderRegisters registers raw count next) :
    readIdxs { st with map := registers ++ #[tail, finish, 1, G.ofNat count, 0] }
      #[41, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 29, 37] = .ok (raw.cell tail) := by
  change readIdxs _ (#[41] ++ (identityArgs ++ #[29, 37])) = _
  rw [read_idxs_append, read_idxs_single _ _ 0 (by simp [header.size]), Except.bind,
    read_idxs_append, header_id_arguments st registers _ raw count next header]
  have fields := (Array.getElem?_eq_some_iff.mp header.fields).2
  simp [readIdxs, readIdx, header.size, fields, Array.getElem?_append, RawDecl.cell,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem eval_block_append (t : Bytecode.Toplevel) (fuel : Nat)
    (left right : Array Aiur.Bytecode.Op) (ctrl : Aiur.Bytecode.Ctrl) (st : EvalState) :
    evalBlock t fuel ⟨left ++ right, ctrl⟩ st =
      (runOps t fuel left st 0).bind (fun after => evalBlock t fuel ⟨right, ctrl⟩ after) := by
  simp only [evalBlock, run_ops_append]
  cases runOps t fuel left st 0 <;> rfl

private theorem finish_eval (t : Bytecode.Toplevel) (fuel selector : Nat) (st : EvalState)
    (registers : Array G) (raw : RawDecl) (count : Nat) (next tail finish : G)
    (header : HeaderRegisters registers raw count next) :
    ∃ after, evalBlock t fuel ⟨storeOps, .return selector #[42, 38]⟩
        { st with map := registers ++ #[tail, finish, 1, G.ofNat count] } =
      .error (.earlyReturn #[G.ofNat (memStore st (raw.cell tail)).2, finish] after) ∧
      after.memory = (memStore st (raw.cell tail)).1.memory ∧ after.ioBuffer = st.ioBuffer := by
  let ready : EvalState := { st with map := registers ++ #[tail, finish, 1, G.ofNat count, 0] }
  have constant : Aiur.Bytecode.Eval.evalOp t fuel (.const 0)
      { st with map := registers ++ #[tail, finish, 1, G.ofNat count] } = .ok ready := by
    simp only [Aiur.Bytecode.Eval.evalOp, pushMap, ready]
    rw [← Array.append_push]
    rfl
  have values := header_store_arguments st registers raw count next tail finish header
  change readIdxs ready _ = .ok (raw.cell tail) at values
  change ∃ after, evalBlock t fuel
    ⟨#[.const 0] ++ #[.store #[41, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 29, 37]], .return selector #[42, 38]⟩ _ = _ ∧ _ ∧ _
  simp only [eval_block_append, run_single, constant, Except.bind, evalBlock, run_single,
    Aiur.Bytecode.Eval.evalOp, values, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [ready, mem_store_map, pushMap, evalCtrl, readIdxs, readIdx, header.size,
    Array.getElem?_append, Bind.bind, Except.bind, Pure.pure, Except.pure,
    mem_store_io]

set_option maxHeartbeats 1000000 in
/-- Exact acceptance/rejection of a byte-derived declaration prefix. No
semantic table or uniqueness premise is assumed: the recursive parser builds
the former and checks the latter. The count and allocation bounds are explicit.
On rejection there is no returned state in the evaluator's error type. -/
theorem checked_declarations_eval (t : Bytecode.Toplevel) (code : DeclarationCode) (checked : CheckedCode t code)
    (fuel : Nat) (st : EvalState) (decls : List DeclarationBytes)
    (capacity : decls.length ≤ 16) (space : bucketSize st 13 + decls.length + 1 ≤ goldilocksModulus)
    (pointer finish : G)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer (decls.flatMap DeclarationBytes.bytes) finish) :
    ∃ after, evalBlock t (fuel + decls.length + 2) checked.parserFn.body
        { st with map := #[pointer, G.ofNat decls.length] } =
      (if Valid decls then .error (.earlyReturn #[(storeDeclarations st decls).2, finish] after)
        else .error .assertFailed) ∧
      (Valid decls → after.memory = (storeDeclarations st decls).1.memory ∧ after.ioBuffer = st.ioBuffer) := by
  induction decls generalizing st pointer with
  | nil =>
    cases bytesRead
    have zero : G.ofNat 0 = 0 := by decide
    obtain ⟨after, executed, memory, io⟩ := empty_table_eval t (fuel + 2) code.zeroSelector
      (some (declarationsStep code.reader code.identity code.unique code.self code.consSelector)) st finish
    refine ⟨after, ?_, fun _ => ⟨memory, io⟩⟩
    rw [(declarations_checked checked.parserFn _ _ _ _ _ _ checked.parserChecked).2]
    simpa [declarationsBody, Valid, storeDeclarations, zero] using executed
  | cons d ds ih =>
    simp only [List.length_cons] at capacity space ⊢
    rw [show fuel + (ds.length + 1) + 2 = fuel + ds.length + 3 by omega]
    have bounded : ds.length + 1 < goldilocksModulus := by
      change ds.length + 1 < 18446744069414584321
      omega
    rw [(declarations_checked checked.parserFn _ _ _ _ _ _ checked.parserChecked).2,
      declarations_nonzero t _ _ _ _ _ _ _ st pointer _ (field_succ_nonzero ds.length bounded)]
    simp only [List.flatMap_cons] at bytesRead
    obtain ⟨next, first, rest⟩ := byte_prefix_split bytesRead
    obtain ⟨registers, header, headerRun⟩ := checked_declaration_header t code checked
      (fuel + ds.length + 1) st d ds.length bounded pointer next first
    rw [← declaration_fields, show fuel + ds.length + 1 + 2 = fuel + ds.length + 3 by omega] at headerRun
    by_cases fields : d.declaration.fields ≤ 16
    · rw [if_pos fields] at headerRun
      obtain ⟨afterTail, tailRun, tailState⟩ := ih { st with map := registers } (by omega) (by
        change bucketSize st 13 + ds.length + 1 ≤ goldilocksModulus
        omega) next rest
      simp only [store_declarations_map] at tailRun tailState
      have tailCall := call_pair_result t (fuel + ds.length + 2) code.self { st with map := registers }
        checked.parserFn checked.parserFunction #[20, 36] next (G.ofNat ds.length)
        (storeDeclarations st ds).2 finish (header_recursive_arguments st registers d.raw ds.length next header)
        (declarations_checked checked.parserFn _ _ _ _ _ _ checked.parserChecked).1
        (Valid ds) afterTail tailRun false
      rw [show fuel + ds.length + 2 + 1 = fuel + ds.length + 3 by omega] at tailCall
      by_cases validTail : Valid ds
      · obtain ⟨tailMemory, tailIo⟩ := tailState validTail
        let called : EvalState := { (storeDeclarations st ds).1 with map := registers ++ #[(storeDeclarations st ds).2, finish] }
        have callRun : Aiur.Bytecode.Eval.evalOp t (fuel + ds.length + 3) (.call code.self #[20, 36] 2 false)
            { st with map := registers } = .ok called := by
          simpa only [if_pos validTail, tailMemory, tailIo, called, store_declarations_io] using tailCall
        have counter : called.map[1]? = some (G.ofNat (ds.length + 1)) := by
          simpa [called, Array.getElem?_append, header.size] using header.counter
        have advanceRun := advance_eval t (fuel + ds.length + 3) called (by simp [called, header.size])
          ds.length counter bounded
        let advanced : EvalState := { (storeDeclarations st ds).1 with
          map := registers ++ #[(storeDeclarations st ds).2, finish, 1, G.ofNat ds.length] }
        have advancedEq : { called with map := called.map ++ #[1, G.ofNat ds.length] } = advanced := by
          simp [called, advanced, Array.append_assoc]
        rw [advancedEq] at advanceRun
        have tailRead : readTable (bytecodeMemory advanced) (storeDeclarations st ds).2.n ds.length =
            some (ds.map DeclarationBytes.declaration).toArray := by
          simpa only [advanced, bytecode_memory_map] using store_declarations_table st ds validTail
            (by omega) (by omega)
        have uniqueRun := checked_unique_call t (fuel + 1) code.comparer code.unique code.compareSelector code.uniqueZero code.uniqueCons
          checked.compareFn checked.uniqueFn checked.compareFunction checked.uniqueFunction checked.compareChecked checked.uniqueChecked
          advanced d.raw.id d.declaration.id (declaration_decoded d) (storeDeclarations st ds).2 ds.length _ tailRead
          uniquenessArgs (header_unique_arguments (storeDeclarations st ds).1 registers d.raw ds.length next
            (storeDeclarations st ds).2 finish header) false
        rw [show fuel + 1 + ds.length + 2 = fuel + ds.length + 3 by omega] at uniqueRun
        simp only [List.map_map, Function.comp_def] at uniqueRun
        by_cases duplicate : d.declaration.id ∈ ds.map (fun d => d.declaration.id)
        · rw [if_pos duplicate] at uniqueRun
          have invalid : ¬ Valid (d :: ds) := fun valid => (valid_cons d ds).mp valid |>.2.1 duplicate
          refine ⟨st, ?_, fun valid => False.elim (invalid valid)⟩
          simp only [if_neg invalid, declarationsStep, eval_block_append, run_ops_append, run_single,
            headerRun, callRun, advanceRun, uniqueRun, Except.bind]
        · rw [if_neg duplicate] at uniqueRun
          have valid := (valid_cons d ds).mpr ⟨fields, duplicate, validTail⟩
          obtain ⟨after, finishRun, memory, io⟩ := finish_eval t (fuel + ds.length + 3) code.consSelector
            (storeDeclarations st ds).1 registers d.raw ds.length next (storeDeclarations st ds).2 finish header
          refine ⟨after, ?_, fun _ => ⟨memory, io.trans (store_declarations_io st ds)⟩⟩
          simp only [if_pos valid, declarationsStep, eval_block_append, run_ops_append, run_single,
            headerRun, callRun, advanceRun, uniqueRun, Except.bind]
          exact finishRun
      · rw [if_neg validTail] at tailCall
        have invalid : ¬ Valid (d :: ds) := fun valid => validTail ((valid_cons d ds).mp valid).2.2
        refine ⟨st, ?_, fun valid => False.elim (invalid valid)⟩
        simp only [if_neg invalid, declarationsStep, eval_block_append, run_ops_append, run_single,
          headerRun, tailCall, Except.bind]
    · rw [if_neg fields] at headerRun
      have invalid : ¬ Valid (d :: ds) := fun valid => fields ((valid_cons d ds).mp valid).1
      refine ⟨st, ?_, fun valid => False.elim (invalid valid)⟩
      simp only [if_neg invalid, declarationsStep, eval_block_append, headerRun, Except.bind]

/-- A successful parse establishes the existing semantic table relation in
forward wire order and preserves every prior readable cell and all I/O. -/
theorem checked_declarations_table (t : Bytecode.Toplevel) (code : DeclarationCode) (checked : CheckedCode t code)
    (fuel : Nat) (st : EvalState) (decls : List DeclarationBytes) (valid : Valid decls)
    (capacity : decls.length ≤ 16) (space : bucketSize st 13 + decls.length + 1 ≤ goldilocksModulus)
    (pointer finish : G)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer (decls.flatMap DeclarationBytes.bytes) finish) :
    ∃ after, evalBlock t (fuel + decls.length + 2) checked.parserFn.body
        { st with map := #[pointer, G.ofNat decls.length] } =
      .error (.earlyReturn #[(storeDeclarations st decls).2, finish] after) ∧
      readTable (bytecodeMemory after) (storeDeclarations st decls).2.n decls.length =
        some (decls.map DeclarationBytes.declaration).toArray ∧
      after.ioBuffer = st.ioBuffer ∧
      (∀ width pointer flat, memLoad st width pointer = .ok flat → memLoad after width pointer = .ok flat) := by
  obtain ⟨after, executed, state⟩ := checked_declarations_eval t code checked fuel st decls capacity space pointer finish bytesRead
  obtain ⟨memory, io⟩ := state valid
  refine ⟨after, by simpa only [if_pos valid] using executed, ?_, io, ?_⟩
  · rw [bytecode_memory_congr after (storeDeclarations st decls).1 memory]
    exact store_declarations_table st decls valid capacity space
  · intro width pointer flat read
    simpa only [memLoad, memory] using store_declarations_preserves st decls read

/-- An unsupported arity or any repeated full ID anywhere in the consumed
prefix is rejected by the actual recursive parser. -/
theorem checked_declarations_reject (t : Bytecode.Toplevel) (code : DeclarationCode) (checked : CheckedCode t code)
    (fuel : Nat) (st : EvalState) (decls : List DeclarationBytes) (invalid : ¬ Valid decls)
    (capacity : decls.length ≤ 16) (space : bucketSize st 13 + decls.length + 1 ≤ goldilocksModulus)
    (pointer finish : G)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer (decls.flatMap DeclarationBytes.bytes) finish) :
    evalBlock t (fuel + decls.length + 2) checked.parserFn.body
      { st with map := #[pointer, G.ofNat decls.length] } = .error .assertFailed := by
  obtain ⟨_, executed, _⟩ := checked_declarations_eval t code checked fuel st decls capacity space pointer finish bytesRead
  simpa only [if_neg invalid] using executed

/-- Complete Call contract. Success appends exactly the table and suffix
pointers, performs the proved stores, and keeps the caller's prior registers
and I/O. Both constraint flags have this Lean evaluator behavior only. -/
theorem checked_declarations_call (t : Bytecode.Toplevel) (code : DeclarationCode) (checked : CheckedCode t code)
    (fuel : Nat) (st : EvalState) (decls : List DeclarationBytes)
    (capacity : decls.length ≤ 16) (space : bucketSize st 13 + decls.length + 1 ≤ goldilocksModulus)
    (pointer finish : G)
    (bytesRead : BytePrefix (bytecodeMemory st) pointer (decls.flatMap DeclarationBytes.bytes) finish)
    (args : Array Nat) (arguments : readIdxs st args = .ok #[pointer, G.ofNat decls.length]) (unconstrained : Bool) :
    Aiur.Bytecode.Eval.evalOp t (fuel + decls.length + 3) (.call code.self args 2 unconstrained) st =
      if Valid decls then .ok { (storeDeclarations st decls).1 with
        map := st.map ++ #[(storeDeclarations st decls).2, finish] } else .error .assertFailed := by
  obtain ⟨after, executed, state⟩ := checked_declarations_eval t code checked fuel st decls capacity space pointer finish bytesRead
  have called := call_pair_result t (fuel + decls.length + 2) code.self st checked.parserFn checked.parserFunction
    args pointer (G.ofNat decls.length) (storeDeclarations st decls).2 finish arguments
    (declarations_checked checked.parserFn _ _ _ _ _ _ checked.parserChecked).1 (Valid decls) after executed unconstrained
  by_cases valid : Valid decls
  · obtain ⟨memory, io⟩ := state valid
    simpa only [if_pos valid, memory, io, store_declarations_io] using called
  · simpa only [if_neg valid] using called

/-- Semantic fields agree with the existing little-endian byte codec. -/
theorem declaration_codec (d : DeclarationBytes) :
    d.declaration.id.block.val = natOfBytesLE ([d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h].flatMap WordBytes.bytes).toArray ∧
      d.declaration.id.member = natOfBytesLE d.member.bytes.toArray ∧
      d.declaration.id.tag = natOfBytesLE d.tag.bytes.toArray ∧
      d.declaration.fields = natOfBytesLE d.fields.bytes.toArray := by
  simp only [DeclarationBytes.declaration, word_field_codec, and_self]

private theorem group_declaration_words (count : Nat) (words : List WordBytes) (length : words.length = 11 * count) :
    ∃ decls : List DeclarationBytes, decls.length = count ∧
      decls.flatMap (fun d => d.idWords ++ [d.fields]) = words := by
  induction count generalizing words with
  | zero =>
    have empty : words = [] := by simpa using length
    subst words
    exact ⟨[], rfl, rfl⟩
  | succ count ih =>
    match words with
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] |
        [_, _, _, _, _, _] | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] |
        [_, _, _, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _, _, _] => simp_all +arith
    | a :: b :: c :: d :: e :: f :: g :: h :: member :: tag :: fields :: rest =>
      obtain ⟨decls, countEq, wordsEq⟩ := ih rest (by simp only [List.length_cons] at length; omega)
      refine ⟨⟨a, b, c, d, e, f, g, h, member, tag, fields⟩ :: decls, by simp [countEq], ?_⟩
      simp only [List.flatMap_cons, wordsEq]
      rfl

/-- Grouping into records is not an extra wire-format restriction: every
sequence of exactly `44 * count` bytes has the representation used above. -/
theorem group_declaration_bytes (count : Nat) (bytes : List UInt8) (length : bytes.length = 44 * count) :
    ∃ decls : List DeclarationBytes, decls.length = count ∧ decls.flatMap DeclarationBytes.bytes = bytes := by
  obtain ⟨words, wordCount, wordBytes⟩ := group_word_bytes (11 * count) bytes (by omega)
  obtain ⟨decls, declCount, declWords⟩ := group_declaration_words count words wordCount
  refine ⟨decls, declCount, ?_⟩
  have expanded : (decls.flatMap (fun d => d.idWords ++ [d.fields])).flatMap WordBytes.bytes =
      decls.flatMap DeclarationBytes.bytes := by
    simp only [List.flatMap_assoc, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  rw [← expanded, declWords, wordBytes]

end
end
end Ix.Ixby.AiurBackend.ObjectsDeclarations
