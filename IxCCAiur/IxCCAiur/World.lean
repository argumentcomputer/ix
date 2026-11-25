import IxCCAiur.Backward
import Aiur.Generic.LawfulBEq

/-! # The world hypothesis, checked

`Backward.LoweredWorld P prog world` says three things about the Aiur source
a lowered program is evaluated in: `prog` is `lowerProgram P`; the `UInt64`
library's contracts hold in `world`; and every function of `prog` is bound in
`world` under `Prog::<name>` with its qualified body. `Backward` and
`Compose` take it as a hypothesis.

Here it follows from a Boolean evaluated on the prepared source
(`checkWorld`, with `loweredWorld_of_check`):

* `checkTables`: the three `UInt8` maps are tables and not functions, each
  reads the two tables it should, and the five tables have the rows the
  contracts are proved from (`Gadgets.U8TablesMatch`);
* `Gadgets.checkU64Functions`: the seventeen `UInt8`/`UInt64` functions the
  contracts are proved about are in the source with exactly the bodies the
  proofs invert, and `UInt8::BYTE_0` is the literal `0`
  (`Gadgets.U64LibraryWorld`);
* `checkFunctions`: every lowered function is in the source under its
  qualified name, without type parameters, with the same parameter names and
  with the body `Lower.qualifyExprF` predicts.

The comparisons of bodies are `==` on `Aiur.Generic.Expr`, which is equality
(`Aiur/Aiur/Generic/LawfulBEq.lean`). The driver evaluates `checkWorld` on
what `Aiur.Modules.prepare` returns before it writes a package
(`IxCCAiur.Main`), so the hypothesis is a computed fact about each program
that is proved, not an assumption about the linker and the elaborator. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.World

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Gadgets IxCC.AiurBackend.Backward

variable {F : Type} [Field F] [DecidableEq F]

/-! ## The `UInt8` tables -/

/-- `name` is not a function of the source (so a call of it is a table lookup). -/
def checkNoFunction (s : Generic.Source F) (name : String) : Bool :=
  (s.program.sourceFunction? name).isNone

/-- The static map `name` reads table `input` and answers from table `output`. -/
def checkMap (s : Generic.Source F) (name input output : String) : Bool :=
  match s.tables.findMap? name with
  | some m => decide (m.input = input) && decide (m.output = output)
  | none => false

/-- The static table `name` has exactly the rows `rows`. -/
def checkTable (s : Generic.Source F) (name : String) (rows : List (Constant F)) : Bool :=
  match s.tables.findTable? name with
  | some t => decide (t.rows = rows)
  | none => false

/-- The three `UInt8` maps and their five tables are the ones
`Gadgets.u8MapSpec_of_source` reads (`Gadgets.U8TablesMatch`). -/
def checkTables (s : Generic.Source F) : Bool :=
  checkNoFunction s "UInt8::range_pair" &&
  checkNoFunction s "UInt8::raw_xor" &&
  checkNoFunction s "UInt8::raw_sum_byte" &&
  checkMap s "UInt8::range_pair" "UInt8::pair_inputs" "UInt8::pair_units" &&
  checkMap s "UInt8::raw_xor" "UInt8::pair_inputs" "UInt8::pair_xors" &&
  checkMap s "UInt8::raw_sum_byte" "UInt8::sum_inputs" "UInt8::sum_bytes" &&
  checkTable s "UInt8::pair_inputs"
    (((List.range 256).flatMap fun a => (List.range 256).map fun b => (a, b)).map
      fun (a, b) => .tuple [.field (a : F), .field (b : F)]) &&
  checkTable s "UInt8::pair_units"
    (((List.range 256).flatMap fun a => (List.range 256).map fun b => (a, b)).map
      fun _ => .tuple []) &&
  checkTable s "UInt8::pair_xors"
    (((List.range 256).flatMap fun a => (List.range 256).map fun b => (a, b)).map
      fun (a, b) => .field ((Nat.xor a b : Nat) : F)) &&
  checkTable s "UInt8::sum_inputs"
    ((Carry.rows 256 768).map fun (n, _) => .tuple [.field (n : F)]) &&
  checkTable s "UInt8::sum_bytes"
    ((Carry.rows 256 768).map fun (_, b) => .field (b : F))

/-! ## The lowered functions -/

/-- The lowered function `g` is in the source as `Prog::<name>`, without type
parameters, with `g`'s parameter names and its qualified body. -/
def checkFunction (s : Generic.Source F) (g : Fn) : Bool :=
  match s.program.findFunction? (qualified g.name) with
  | some f => f.typeParams.isEmpty && (f.params.map Prod.fst == g.params.map Prod.fst) &&
      (f.body == qualifyExprF F g.body)
  | none => false

/-- Every function of the lowered program passes `checkFunction`. -/
def checkFunctions (s : Generic.Source F) (prog : Aiur.Generic.Program Nat) : Bool :=
  prog.functions.all (checkFunction s)

/-- The lowered functions that fail `checkFunction` (for a report; empty
exactly when `checkFunctions` holds). -/
def failing (s : Generic.Source F) (prog : Aiur.Generic.Program Nat) : List String :=
  (prog.functions.filter fun g => !checkFunction s g).map (·.name)

/-- **The world check**: the tables, the library's functions and the lowered
functions. -/
def checkWorld (s : Generic.Source F) (prog : Aiur.Generic.Program Nat) : Bool :=
  checkTables s && checkU64Functions s && checkFunctions s prog

/-! ## Soundness of the checks -/

omit [Field F] in
theorem checkNoFunction_sound {s : Generic.Source F} {name : String}
    (h : checkNoFunction s name = true) : s.program.sourceFunction? name = none :=
  Option.isNone_iff_eq_none.mp h

omit [Field F] in
theorem checkMap_sound {s : Generic.Source F} {name input output : String}
    (h : checkMap s name input output = true) :
    ∃ m, s.tables.findMap? name = some m ∧ m.input = input ∧ m.output = output := by
  unfold checkMap at h
  cases hm : s.tables.findMap? name with
  | none => rw [hm] at h; simp at h
  | some m =>
    rw [hm] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨m, rfl, h.1, h.2⟩

omit [Field F] in
theorem checkTable_sound {s : Generic.Source F} {name : String} {rows : List (Constant F)}
    (h : checkTable s name rows = true) :
    ∃ t, s.tables.findTable? name = some t ∧ t.rows = rows := by
  unfold checkTable at h
  cases ht : s.tables.findTable? name with
  | none => rw [ht] at h; simp at h
  | some t =>
    rw [ht] at h
    simp only [decide_eq_true_eq] at h
    exact ⟨t, rfl, h⟩

/-- **The table check is sound**: a source that passes it has the tables the
`UInt8` map contracts are proved from. -/
theorem u8TablesMatch_of_check {s : Generic.Source F} (h : checkTables s = true) :
    U8TablesMatch s := by
  simp only [checkTables, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact
    { noFn_range_pair := checkNoFunction_sound h1
      noFn_raw_xor := checkNoFunction_sound h2
      noFn_raw_sum_byte := checkNoFunction_sound h3
      map_range_pair := checkMap_sound h4
      map_raw_xor := checkMap_sound h5
      map_raw_sum_byte := checkMap_sound h6
      tbl_pair_inputs := checkTable_sound h7
      tbl_pair_units := checkTable_sound h8
      tbl_pair_xors := checkTable_sound h9
      tbl_sum_inputs := checkTable_sound h10
      tbl_sum_bytes := checkTable_sound h11 }

omit [Field F] in
/-- One conjunct of `Gadgets.checkU64Functions`: a function found in the
source with no type parameters, the given parameter names and the given body
is bound so in the source's world. The body comparison is `==` on
`Aiur.Generic.Expr`, which is equality (`Aiur.Generic.LawfulBEq`). -/
theorem worldHasFn_of_check (s : Generic.Source F) {name : String} {params : List String}
    {body : Aiur.Generic.Expr F} (hname : name.toList.head? ≠ some '$')
    (h : (match s.program.findFunction? name with
          | some f => f.typeParams.isEmpty && (f.params.map Prod.fst == params) && (f.body == body)
          | none => false) = true) :
    WorldHasFn s.world name params body := by
  cases hf : s.program.findFunction? name with
  | none => rw [hf] at h; simp at h
  | some f =>
    rw [hf] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    have hw := worldHasFn_of_findFunction? s hname hf h.1.1
    rw [h.1.2, h.2] at hw
    exact hw

/-- A library name does not begin with `$` (the marker of an instantiated
symbol, `Aiur.Generic.Instance.ofSymbol`). -/
local macro "library_name" : tactic => `(tactic| first | decide | simp)

/-- **The library check is sound**: a source with the `UInt8` tables that
passes `Gadgets.checkU64Functions` is a `Gadgets.U64LibraryWorld`, the
hypothesis the `UInt64` contracts are proved under. -/
theorem u64LibraryWorld_of_check (s : Generic.Source F) (tables : U8TablesMatch s)
    (h : checkU64Functions s = true) : U64LibraryWorld s.world := by
  simp only [checkU64Functions, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have byte0 : s.world.constant "UInt8::BYTE_0" .field = .ok (.literal (0 : F)) := by
    cases hc : elaborateConst s.program "UInt8::BYTE_0" .field with
    | error e => rw [hc] at h0; simp at h0
    | ok p =>
      rw [hc] at h0
      simp only [beq_iff_eq] at h0
      simp [Generic.Source.world, sourceWorld, hc, h0, Except.mapError]
  exact
    { maps := u8MapSpec_of_source s tables
      constDepth_pos := Nat.succ_pos _
      const_byte0 := byte0
      u8_to_field := worldHasFn_of_check s (by library_name) h1
      u8_from_fields := worldHasFn_of_check s (by library_name) h2
      u8_split_sum := worldHasFn_of_check s (by library_name) h3
      u8_raw_and := worldHasFn_of_check s (by library_name) h4
      u8_raw_or := worldHasFn_of_check s (by library_name) h5
      u8_and := worldHasFn_of_check s (by library_name) h6
      u8_or := worldHasFn_of_check s (by library_name) h7
      u8_xor := worldHasFn_of_check s (by library_name) h8
      u64_to_field := worldHasFn_of_check s (by library_name) h9
      u64_from_field := worldHasFn_of_check s (by library_name) h10
      u64_is_zero := worldHasFn_of_check s (by library_name) h11
      u64_sub_with_borrow := worldHasFn_of_check s (by library_name) h12
      u64_mul_column := worldHasFn_of_check s (by library_name) h13
      u64_mul := worldHasFn_of_check s (by library_name) h14
      u64_and := worldHasFn_of_check s (by library_name) h15
      u64_or := worldHasFn_of_check s (by library_name) h16
      u64_xor := worldHasFn_of_check s (by library_name) h17 }

theorem checkFunction_sound {s : Generic.Source F} {g : Fn} (h : checkFunction s g = true) :
    ∃ f, s.program.findFunction? (qualified g.name) = some f ∧ f.typeParams = [] ∧
      f.params.map Prod.fst = g.params.map Prod.fst ∧ f.body = qualifyExprF F g.body := by
  unfold checkFunction at h
  cases hf : s.program.findFunction? (qualified g.name) with
  | none => rw [hf] at h; simp at h
  | some f =>
    rw [hf] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    exact ⟨f, rfl, h.1.1, h.1.2, h.2⟩

/-- **The world check is sound.** For a program the lowering accepts, a
prepared source that passes `checkWorld` gives the world hypothesis of the
backward simulation, over any field in which natural numbers below `2^57` are
distinct. -/
theorem loweredWorld_of_check (fc : FieldCompatible F) {P : Fir.Program}
    {prog : Aiur.Generic.Program Nat} (hlow : lowerProgram P = .ok prog)
    (s : Generic.Source F) (h : checkWorld s prog = true) : LoweredWorld P prog s.world := by
  simp only [checkWorld, Bool.and_eq_true] at h
  obtain ⟨⟨htables, hlibrary⟩, hfunctions⟩ := h
  have tables := u8TablesMatch_of_check htables
  have hall : ∀ g ∈ prog.functions, checkFunction s g = true := List.all_eq_true.mp hfunctions
  exact LoweredWorld.ofSource hlow s
    (U64Contracts.ofLibraryWorld (u64LibraryWorld_of_check s tables hlibrary) fc)
    fun g hg => checkFunction_sound (hall g hg)

/-- `failing` is empty exactly when every lowered function passes (it is what
the driver prints when the check fails). -/
theorem failing_eq_nil_iff (s : Generic.Source F) (prog : Aiur.Generic.Program Nat) :
    failing s prog = [] ↔ checkFunctions s prog = true := by
  simp [failing, checkFunctions, List.filter_eq_nil_iff]

end IxCC.AiurBackend.World
