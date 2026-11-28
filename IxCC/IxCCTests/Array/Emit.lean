import IxCC.Rt.Rc.Array.Procs
import IxCC.Rt.Rc.Gen.Procs
import IxCC.Rt.Procs.Entry
import IxCC.Lir.SplitEdges
import IxCC.Lir.WellFormed
import IxCC.Backend

/-! # Compile Native Contiguous Array Runtime Procedures to an x86-64 ELF Object

Exports all 27 contiguous array / `ByteArray` / `LimbArray` runtime procedures
(plus `cx_init` and `cx_rc_alloc_2_0_1` for mixed boxed-array + constructor
release tests) through IxCC's validated x86-64 backend so `NativeControls` can
run them natively on the host Xeon inside `IxCCTests.Exe.TestShell`. -/

set_option autoImplicit false

namespace IxCCTests.Array.Emit

open IxCC
open IxCC.Rt.Rc.Array

/-- Wrap a 0-result effect procedure (`inc`, `dec`) behind a 1-result SysV export
returning `1` (matching `IxCCTests.Rt.Rc.Emit.effectWrapper`). -/
def effectWrapper (name : String) (f : Lir.FunId) : Lir.Func :=
  { name, params := [0], results := 1, conv := .sysvExport name
    blocks := #[{ body := #[.call [] f [.v 0]], term := .ret [.imm 1] }] }

/-- Full Lir program containing all 27 array runtime procedures at their exact
canonical `FunId`s (`0..26`) plus export wrappers for `inc`/`dec`, `cx_init`,
and `cx_rc_alloc_2_0_1`. -/
def program : Lir.Program :=
  let exp (f : Lir.Func) (sym : String) : Lir.Func := { f with conv := .sysvExport sym }
  { funcs := #[
      -- 0..1: 0-result internal RC entry points (wrapped at 27..28)
      IxCC.Rt.Rc.Procs.inc,
      arrDec,
      -- 2..26: 1-result array runtime procedures exported directly
      exp arrClassFor "cx_arr_class_for",
      exp arrClassWords "cx_arr_class_words",
      exp arrAllocCell "cx_arr_alloc_cell",
      exp arrEmptyCapBoxed "cx_arr_empty_boxed",
      exp arrEmptyCapLimbs "cx_arr_empty_limbs",
      exp byteArrEmptyCap "cx_byte_empty",
      exp arrSize "cx_arr_size",
      exp arrCap "cx_arr_cap",
      exp arrGet "cx_arr_get",
      exp byteArrGet "cx_byte_get",
      exp arrSetBoxed "cx_arr_set_boxed",
      exp arrSetLimbs "cx_arr_set_limbs",
      exp arrPushBoxed "cx_arr_push_boxed",
      exp arrPushLimbs "cx_arr_push_limbs",
      exp arrPopBoxed "cx_arr_pop_boxed",
      exp arrPopLimbs "cx_arr_pop_limbs",
      exp arrExtractBoxed "cx_arr_extract_boxed",
      exp arrExtractLimbs "cx_arr_extract_limbs",
      exp arrCopySliceBoxed "cx_arr_copy_slice_boxed",
      exp arrCopySliceLimbs "cx_arr_copy_slice_limbs",
      exp byteArrSet "cx_byte_set",
      exp byteArrPush "cx_byte_push",
      exp byteArrPop "cx_byte_pop",
      exp byteArrExtract "cx_byte_extract",
      exp byteArrCopySlice "cx_byte_copy_slice",
      -- 27: internal alias-safe recursive value increment (`fnIncVal`)
      arrIncValue,
      -- 28..31: effect wrappers + heap init + 2-field ctor allocator
      effectWrapper "cx_arr_inc" fnInc,
      effectWrapper "cx_arr_dec" fnDec,
      Rt.Procs.cxInit,
      { Rt.Rc.Gen.alloc ⟨2, 0, 1⟩ with conv := .sysvExport "cx_rc_alloc_2_0_1" }
    ]
    main := fnEmptyCapBoxed }

/-- Export table order passed to `IxCCTests.Exe.TestShell.writeExe`. -/
def exports : List String := [
  "cx_init",
  "cx_arr_inc",
  "cx_arr_dec",
  "cx_arr_class_for",
  "cx_arr_class_words",
  "cx_arr_alloc_cell",
  "cx_arr_empty_boxed",
  "cx_arr_empty_limbs",
  "cx_byte_empty",
  "cx_arr_size",
  "cx_arr_cap",
  "cx_arr_get",
  "cx_byte_get",
  "cx_arr_set_boxed",
  "cx_arr_set_limbs",
  "cx_arr_push_boxed",
  "cx_arr_push_limbs",
  "cx_arr_pop_boxed",
  "cx_arr_pop_limbs",
  "cx_arr_extract_boxed",
  "cx_arr_extract_limbs",
  "cx_arr_copy_slice_boxed",
  "cx_arr_copy_slice_limbs",
  "cx_byte_set",
  "cx_byte_push",
  "cx_byte_pop",
  "cx_byte_extract",
  "cx_byte_copy_slice",
  "cx_rc_alloc_2_0_1"
]

/-- Compile `program` through `splitCriticalEdges`, `p.check`, and `Backend.compile`,
returning the validated ELF64 relocatable object bytes. -/
def compileObject : Except String ByteArray := do
  let p := program.splitCriticalEdges
  p.check
  let cfg : Backend.Config :=
    { provenance := .ixir1Policy (Ixon.Address.replicate 0x41) 1 1
      reps := fun f => (p.funcs[f]?).map fun fd => fd.params.map fun _ => .word }
  let result ← (Backend.compile p cfg).mapError toString
  pure result.object

end IxCCTests.Array.Emit
