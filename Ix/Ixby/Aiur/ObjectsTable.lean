module
public import Ix.Ixby.Aiur.ObjectsStore
public import Ix.Ixby.Codec

/-! Concrete constructor tables and their checked binding to a program image.

`ISCtorDecl.Mk` is tagless (eleven fields); its list cells have width thirteen.
Names retain eight little-endian u32 digest limbs plus u32 member/tag limbs.
This module checks concrete memory against the existing canonical program
decoder. It does not prove that the interpreter's parser or hash gadget
establishes that agreement, and is not a new production verification path. -/

public section
@[expose] section

namespace Ix.Ixby.AiurBackend.ObjectsTable

open ObjectsRefinement ObjectsMemory ObjectsStore

abbrev declWidth : Nat := 11
abbrev tableWidth : Nat := 13
abbrev limbBase : Nat := 2 ^ 32

/-- Exact natural packing, with no Goldilocks reduction or u32 narrowing. -/
def packLimbs : List Nat → Nat
  | [] => 0
  | limb :: rest => limb + limbBase * packLimbs rest

theorem pack_limbs_bound {limbs : List Nat}
    (bounded : ∀ limb ∈ limbs, limb < limbBase) :
    packLimbs limbs < limbBase ^ limbs.length := by
  induction limbs with
  | nil => simp [packLimbs]
  | cons limb rest ih =>
    have head := bounded limb (by simp)
    have tail := ih (fun limb mem => bounded limb (by simp [mem]))
    change limb + limbBase * packLimbs rest < limbBase ^ (rest.length + 1)
    have powered : limbBase ^ (rest.length + 1) = limbBase ^ rest.length * limbBase :=
      Nat.pow_succ _ _
    rw [powered]
    change limb < 4294967296 at head
    change packLimbs rest < 4294967296 ^ rest.length at tail
    change limb + 4294967296 * packLimbs rest < 4294967296 ^ rest.length * 4294967296
    omega

theorem pack_limbs_injective {xs ys : List Nat}
    (leftBound : ∀ limb ∈ xs, limb < limbBase) (rightBound : ∀ limb ∈ ys, limb < limbBase)
    (length : xs.length = ys.length) (packed : packLimbs xs = packLimbs ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at length
    | cons y ys =>
      have xBound := leftBound x (by simp)
      have yBound := rightBound y (by simp)
      have head : x = y := by
        have same := congrArg (· % limbBase) packed
        simpa [packLimbs, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt xBound,
          Nat.mod_eq_of_lt yBound] using same
      subst y
      have tail : packLimbs xs = packLimbs ys := by
        change x + 4294967296 * packLimbs xs = x + 4294967296 * packLimbs ys at packed
        omega
      exact congrArg (x :: ·) (ih (fun limb mem => leftBound limb (by simp [mem]))
        (fun limb mem => rightBound limb (by simp [mem])) (by simpa using length) tail)

/-- Full ten-limb semantic names. The explicit final bound makes creation of
the 256-bit digest proof-carrying, never a modular conversion. -/
def decodeId : List Aiur.G → Option CtorId
  | [a, b, c, d, e, f, g, h, member, tag] =>
    if ([a, b, c, d, e, f, g, h, member, tag].all (fun limb => limb.n < limbBase)) then
      let block := packLimbs [a.n, b.n, c.n, d.n, e.n, f.n, g.n, h.n]
      if bound : block < 2 ^ 256 then some ⟨⟨block, bound⟩, member.n, tag.n⟩ else none
    else none
  | _ => none

theorem decode_id_exact (a b c d e f g h member tag : Aiur.G) (id : CtorId)
    (decoded : decodeId [a, b, c, d, e, f, g, h, member, tag] = some id) :
    id.block.val = packLimbs [a.n, b.n, c.n, d.n, e.n, f.n, g.n, h.n] ∧
      id.member = member.n ∧ id.tag = tag.n := by
  simp only [decodeId] at decoded
  split at decoded
  · split at decoded
    · have equal := Option.some.inj decoded
      exact ⟨(congrArg (fun id : CtorId => id.block.val) equal).symm,
        (congrArg CtorId.member equal).symm, (congrArg CtorId.tag equal).symm⟩
    · simp at decoded
  · simp at decoded

inductive DeclCell where
  | nil
  | cons (declaration : CtorDecl) (tail : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

def decodeDeclCell (flat : Array Aiur.G) : Option DeclCell :=
  match flat.toList with
  | [tag, a, b, c, d, e, f, g, h, member, ctorTag, fields, tail] =>
    match tag.n with
    | 0 => do
      let id ← decodeId [a, b, c, d, e, f, g, h, member, ctorTag]
      if fields.n > objectsProfile.limits.operands then none
      else some (.cons ⟨id, fields.n⟩ tail.n)
    | 1 =>
      if [a, b, c, d, e, f, g, h, member, ctorTag, fields, tail].all (· == 1) then some .nil
      else none
    | _ => none
  | _ => none

def declarationHeap (memory : RawMemory) : Nat → Option DeclCell := fun pointer =>
  memory tableWidth pointer >>= decodeDeclCell

/-- Declaration order is preserved (unlike the reversed object-field lists).
An exact terminal Nil is required even for the empty table. -/
def readDeclarations (memory : RawMemory) : Nat → Nat → Option (List CtorDecl)
  | 0, pointer => match declarationHeap memory pointer with
    | some .nil => some []
    | _ => none
  | count + 1, pointer => match declarationHeap memory pointer with
    | some (.cons declaration tail) => (declaration :: ·) <$> readDeclarations memory count tail
    | _ => none

theorem read_declarations_length {memory : RawMemory} {count pointer : Nat} {decls : List CtorDecl}
    (read : readDeclarations memory count pointer = some decls) : decls.length = count := by
  induction count generalizing pointer decls with
  | zero =>
    cases loaded : declarationHeap memory pointer with
    | none => simp [readDeclarations, loaded] at read
    | some cell => cases cell <;> simp_all [readDeclarations]
  | succ count ih =>
    cases loaded : declarationHeap memory pointer with
    | none => simp [readDeclarations, loaded] at read
    | some cell =>
      cases cell with
      | nil => simp [readDeclarations, loaded] at read
      | cons declaration tail =>
        cases rest : readDeclarations memory count tail with
        | none => simp [readDeclarations, loaded, rest] at read
        | some values =>
          simp [readDeclarations, loaded, rest] at read
          subst decls
          simp [ih rest]

private theorem unique_of_nodup {decls : List CtorDecl} (unique : (decls.map CtorDecl.id).Nodup) :
    UniqueIds decls.toArray := by
  intro i j a b left right same
  simp only [List.getElem?_toArray] at left right
  induction decls generalizing i j with
  | nil => simp at left
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at left
      subst a
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_succ] at right
        have member := List.mem_of_getElem? right
        exact False.elim (unique.1 (List.mem_map.mpr ⟨b, member, same.symm⟩))
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at right
        subst b
        simp only [List.getElem?_cons_succ] at left
        have member := List.mem_of_getElem? left
        exact False.elim (unique.1 (List.mem_map.mpr ⟨a, member, same⟩))
      | succ j => exact congrArg Nat.succ (ih unique.2 i j left right)

def readTable (memory : RawMemory) (pointer count : Nat) : Option (Array CtorDecl) := do
  if count > objectsProfile.limits.constructors then none
  else
    let decls ← readDeclarations memory count pointer
    if (decls.map CtorDecl.id).Nodup then some decls.toArray else none

theorem read_table_sound {memory : RawMemory} {pointer count : Nat} {table : Array CtorDecl}
    (read : readTable memory pointer count = some table) :
    readDeclarations memory count pointer = some table.toList ∧ table.size = count ∧
      UniqueIds table ∧ count ≤ objectsProfile.limits.constructors := by
  unfold readTable at read
  split at read
  · simp at read
  · rename_i capacity
    obtain ⟨decls, decoded, read⟩ := Option.bind_eq_some_iff.mp read
    split at read
    · rename_i unique
      cases Option.some.inj read
      exact ⟨by simpa using decoded, by simpa using read_declarations_length decoded,
        unique_of_nodup unique, by omega⟩
    · simp at read

theorem store_preserves_declaration_cell (st : Aiur.Bytecode.Eval.EvalState) (stored : Array Aiur.G)
    {pointer : Nat} {cell : DeclCell}
    (loaded : declarationHeap (bytecodeMemory st) pointer = some cell) :
    declarationHeap (bytecodeMemory (Aiur.Bytecode.Eval.memStore st stored).1) pointer = some cell := by
  unfold declarationHeap at loaded ⊢
  obtain ⟨flat, read, decoded⟩ := Option.bind_eq_some_iff.mp loaded
  unfold bytecodeMemory at read ⊢
  cases actual : Aiur.Bytecode.Eval.memLoad st tableWidth pointer with
  | error error => simp [actual] at read
  | ok values =>
    simp only [actual, Option.some.injEq] at read
    subst flat
    simp [mem_store_preserves st stored actual, decoded]

theorem store_preserves_declarations (st : Aiur.Bytecode.Eval.EvalState) (stored : Array Aiur.G)
    {count pointer : Nat} {decls : List CtorDecl}
    (read : readDeclarations (bytecodeMemory st) count pointer = some decls) :
    readDeclarations (bytecodeMemory (Aiur.Bytecode.Eval.memStore st stored).1) count pointer =
      some decls := by
  induction count generalizing pointer decls with
  | zero =>
    cases loaded : declarationHeap (bytecodeMemory st) pointer with
    | none => simp [readDeclarations, loaded] at read
    | some cell =>
      cases cell <;> simp_all [readDeclarations, store_preserves_declaration_cell st stored loaded]
  | succ count ih =>
    cases loaded : declarationHeap (bytecodeMemory st) pointer with
    | none => simp [readDeclarations, loaded] at read
    | some cell =>
      cases cell with
      | nil => simp [readDeclarations, loaded] at read
      | cons declaration tail =>
        cases rest : readDeclarations (bytecodeMemory st) count tail with
        | none => simp [readDeclarations, loaded, rest] at read
        | some values =>
          simp [readDeclarations, loaded, rest] at read
          subst decls
          simp [readDeclarations, store_preserves_declaration_cell st stored loaded, ih rest]

theorem store_preserves_table (st : Aiur.Bytecode.Eval.EvalState) (stored : Array Aiur.G)
    {pointer count : Nat} {table : Array CtorDecl}
    (read : readTable (bytecodeMemory st) pointer count = some table) :
    readTable (bytecodeMemory (Aiur.Bytecode.Eval.memStore st stored).1) pointer count = some table := by
  unfold readTable at read ⊢
  split at read
  · simp at read
  · rename_i capacity
    obtain ⟨decls, decoded, read⟩ := Option.bind_eq_some_iff.mp read
    simpa [capacity, store_preserves_declarations st stored decoded] using read

/-- Bind a reconstructed table to an already decoded program, rather than
accepting its indices as an unrelated host-supplied constructor namespace. -/
def checkProgramTable (memory : RawMemory) (pointer count : Nat) (program : Program) : Bool :=
  match readTable memory pointer count with
  | some table => decide (table = program.constructors)
  | none => false

theorem checked_program_table {memory : RawMemory} {pointer count : Nat} {program : Program}
    (checked : checkProgramTable memory pointer count program = true) :
    readTable memory pointer count = some program.constructors ∧ UniqueIds program.constructors := by
  unfold checkProgramTable at checked
  split at checked
  · rename_i table read
    have same : table = program.constructors := of_decide_eq_true checked
    subst table
    exact ⟨read, (read_table_sound read).2.2.1⟩
  · simp at checked

/-- Diagnostic binding to the existing canonical program decoder. The bytes
must still be tied to the expected commitment by the execution/AIR proof. -/
def reconstructProgram (memory : RawMemory) (programBytes : Codec.Bytes)
    (pointer count : Nat) (flat : Array Aiur.G) (nodes : Nat) : Option (Program × Value × Nat) := do
  let decoded ← (Codec.decodeProgram objectsProfile programBytes).toOption
  if checkProgramTable memory pointer count decoded.value then
    let (value, remaining) ← reconstruct memory decoded.value.constructors flat nodes
    some (decoded.value, value, remaining)
  else none

theorem reconstruct_program_sound {memory : RawMemory} {programBytes : Codec.Bytes}
    {pointer count nodes remaining : Nat} {flat : Array Aiur.G} {program : Program} {value : Value}
    (decoded : reconstructProgram memory programBytes pointer count flat nodes =
      some (program, value, remaining)) :
    Codec.encodeProgram objectsProfile program = .ok programBytes ∧
      readTable memory pointer count = some program.constructors ∧ UniqueIds program.constructors ∧
      ∃ ref, decodeRef flat.toList = some ref ∧ Represents (typedHeap memory) program.constructors ref value := by
  unfold reconstructProgram at decoded
  obtain ⟨image, _, decoded⟩ := Option.bind_eq_some_iff.mp decoded
  split at decoded
  · rename_i tableChecked
    obtain ⟨⟨result, rest⟩, reconstructed, equal⟩ := Option.bind_eq_some_iff.mp decoded
    cases Option.some.inj equal
    obtain ⟨tableRead, unique⟩ := checked_program_table tableChecked
    exact ⟨image.canonical, tableRead, unique, reconstruct_sound reconstructed⟩
  · simp at decoded

theorem store_preserves_program_reconstruction (st : Aiur.Bytecode.Eval.EvalState)
    (stored : Array Aiur.G) {programBytes : Codec.Bytes} {pointer count nodes remaining : Nat}
    {flat : Array Aiur.G} {program : Program} {value : Value}
    (decoded : reconstructProgram (bytecodeMemory st) programBytes pointer count flat nodes =
      some (program, value, remaining)) :
    reconstructProgram (bytecodeMemory (Aiur.Bytecode.Eval.memStore st stored).1)
      programBytes pointer count flat nodes = some (program, value, remaining) := by
  unfold reconstructProgram at decoded ⊢
  obtain ⟨image, imageRead, decoded⟩ := Option.bind_eq_some_iff.mp decoded
  split at decoded
  · rename_i checked
    obtain ⟨⟨result, rest⟩, reconstructed, equal⟩ := Option.bind_eq_some_iff.mp decoded
    cases Option.some.inj equal
    have kept := store_preserves_table st stored (checked_program_table checked).1
    have checkedAfter : checkProgramTable (bytecodeMemory (Aiur.Bytecode.Eval.memStore st stored).1)
        pointer count image.value = true := by simp [checkProgramTable, kept]
    simp [imageRead, checkedAfter, store_preserves_reconstruction st stored reconstructed]
  · simp at decoded

end Ix.Ixby.AiurBackend.ObjectsTable
