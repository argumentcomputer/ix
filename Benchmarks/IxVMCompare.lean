-- Bytecode-only, ungrouped current IxVM; compare ordinary and constrained calls.
import Ix.IxVM.Toplevel
import Ix.IxVM.FunctionGroups
import Ix.Aiur.Compiler
import Lean

open Aiur Lean

instance : ToJson Aiur.G := ⟨fun x => toJson x.n⟩
deriving instance ToJson for Bytecode.Op
deriving instance ToJson for Bytecode.Ctrl, Bytecode.Block
deriving instance ToJson for Bytecode.FunctionLayout, Bytecode.Function, Bytecode.Circuit

def transitiveEntry := ⟦
  pub fn verify_transitive(addr_bytes: [U8; 32]) {
    run_check_transitive(store(addr_bytes));
  }
⟧

def ixvmPortCases := ⟦
-- Shared semantic probes; converted lexically for the Ix comparison exporter.
fn audit_div(a: KLimbs, b: KLimbs, expected_q: KLimbs, expected_r: KLimbs) {
    let (q, r) = klimbs_div_mod(a, b);
    assert_eq!(klimbs_eq(q, expected_q), 1, "audit quotient");
    assert_eq!(klimbs_eq(r, expected_r), 1, "audit remainder");
    ()
}
pub fn check_port_cases() {
    audit_div(store(ListNode.Nil), store(ListNode.Nil), store(ListNode.Nil), store(ListNode.Nil));
    audit_div(store(ListNode.Nil), store(ListNode.Cons([u8_from_field_unsafe(7), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Nil), store(ListNode.Nil));
    audit_div(store(ListNode.Cons([u8_from_field_unsafe(25), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Nil), store(ListNode.Nil), store(ListNode.Cons([u8_from_field_unsafe(25), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))));
    audit_div(store(ListNode.Cons([u8_from_field_unsafe(25), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(7), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(3), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(4), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))));
    audit_div(store(ListNode.Cons([u8_from_field_unsafe(0), u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(255), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))));
    audit_div(store(ListNode.Cons([u8_from_field_unsafe(255), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(0), u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Nil), store(ListNode.Cons([u8_from_field_unsafe(255), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))));
    audit_div(store(ListNode.Cons([u8_from_field_unsafe(7), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Cons([u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))))), store(ListNode.Cons([u8_from_field_unsafe(1), u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(255), u8_from_field_unsafe(0), u8_from_field_unsafe(255), u8_from_field_unsafe(0), u8_from_field_unsafe(255), u8_from_field_unsafe(0), u8_from_field_unsafe(255), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(8), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))));
    audit_div(store(ListNode.Cons([u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(255)], store(ListNode.Cons([u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))))), store(ListNode.Cons([u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(254), u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))));
    audit_div(store(ListNode.Cons([u8_from_field_unsafe(123), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Cons([u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))))), store(ListNode.Cons([u8_from_field_unsafe(5), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Cons([u8_from_field_unsafe(1), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))))), store(ListNode.Cons([u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0), u8_from_field_unsafe(0)], store(ListNode.Nil))), store(ListNode.Cons([u8_from_field_unsafe(128), u8_from_field_unsafe(0), u8_from_field_unsafe(251), u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(255), u8_from_field_unsafe(255)], store(ListNode.Nil))));
    let empty = store(ListNode.Nil);
    let zero_level = store(KLevelNode.Zero);
    let prop = store(KExprNode.Srt(zero_level));
    let v0 = store(KExprNode.BVar(0));
    let v1 = store(KExprNode.BVar(1));
    let lam = store(KExprNode.Lam(prop, v0));
    let app = store(KExprNode.App(lam, prop));
    assert_eq!(k_is_def_eq(prop, prop, empty), 1, "reflexive sort");
    assert_eq!(k_is_def_eq(lam, lam, empty), 1, "reflexive lambda");
    assert_eq!(k_is_def_eq(app, prop, empty), 1, "beta reduction left");
    assert_eq!(k_is_def_eq(prop, app, empty), 1, "beta reduction right");
    assert_eq!(kexpr_struct_eq(v0, v1), 0, "distinct variables");
    assert_eq!(kexpr_struct_eq(app, app), 1, "structural reflexivity");
    assert_eq!(canon_cmp_kexpr_ctx(app, app, store(ListNode.Nil)), (1, 1), "canonical reflexivity");
    assert_eq!(level_struct_eq(zero_level, store(KLevelNode.Succ(zero_level))), 0, "distinct levels");
    assert_eq!(level_struct_eq(store(KLevelNode.Max(zero_level, zero_level)), store(KLevelNode.Max(zero_level, zero_level))), 1, "recursive level equality");
    assert_eq!(u32_less_than(0, 4294967295), 1, "u32 upper bound");
    assert_eq!(u32_less_than(4294967295, 0), 0, "u32 reverse upper bound");
    assert_eq!(u32_less_than(4294967295, 4294967295), 0, "u32 equality");
    ()
}

⟧

def auditEntries := ⟦
  pub fn verify_constant(digest: [U8; 32]) { run_check(store(digest)); }
  pub fn verify_serde(digest: [U8; 32]) {
    let (idx, len) = io_get_info(2, digest);
    let bytes = read_finite_byte_stream(2, idx, len);
    verify_bytes_against(bytes, digest);
    let (constant, rest) = get_constant(bytes);
    assert_eq!(load(rest), ListNode.Nil, "trailing serialization");
    let output = put_constant(constant, store(ListNode.Nil));
    assert_eq!(bytes, output, "serialization round trip");
  }
⟧

def save (path : String) (compiled : CompiledToplevel) (variant : String) : IO Unit := do
  let some entry := compiled.getFuncIdx `verify_transitive
    | throw <| IO.userError "missing benchmark entrypoint"
  let names := compiled.bytecode.functions.mapIdx fun i _ =>
    (compiled.nameMap.toArray.filterMap fun (name, j) =>
      if i == j then some (toString name) else none).qsort (· < ·)
  IO.FS.writeFile path (Json.mkObj [
    ("entry", toJson entry), ("entries", Json.mkObj <| ["verify_transitive", "verify_constant", "verify_serde", "check_port_cases"].filterMap fun name =>
      (compiled.getFuncIdx (Lean.Name.mkSimple name)).map fun i => (name, toJson i)), ("variant", toJson variant),
    ("functions", toJson compiled.bytecode.functions), ("names", toJson names),
    ("circuits", toJson compiled.bytecode.circuits),
    ("memory_sizes", toJson compiled.bytecode.memorySizes)]).compress
  IO.println s!"Exported {compiled.bytecode.functions.size} functions and {compiled.bytecode.circuits.size} circuits to {path}"

partial def constrainCalls (t : Source.Term) : Source.Term :=
  match t with
  | .unit => .unit
  | .var a => .var a
  | .ref a => .ref a
  | .field a => .field a
  | .tuple a => .tuple (a.map constrainCalls)
  | .array a => .array (a.map constrainCalls)
  | .ret a => .ret (constrainCalls a)
  | .let a b c => .let a (constrainCalls b) (constrainCalls c)
  | .match a b => .match (constrainCalls a) (b.map fun (p, b) => (p, constrainCalls b))
  | .app a b c => .app a (b.map constrainCalls) (if c == .unconstrained then .normal else c)
  | .add a b => .add (constrainCalls a) (constrainCalls b)
  | .sub a b => .sub (constrainCalls a) (constrainCalls b)
  | .mul a b => .mul (constrainCalls a) (constrainCalls b)
  | .eqZero a => .eqZero (constrainCalls a)
  | .proj a b => .proj (constrainCalls a) b
  | .get a b => .get (constrainCalls a) b
  | .slice a b c => .slice (constrainCalls a) b c
  | .set a b c => .set (constrainCalls a) b (constrainCalls c)
  | .store a => .store (constrainCalls a)
  | .load a => .load (constrainCalls a)
  | .ptrVal a => .ptrVal (constrainCalls a)
  | .ann a b => .ann a (constrainCalls b)
  | .assertEq a b c d => .assertEq (constrainCalls a) (constrainCalls b) c (constrainCalls d)
  | .ioGetInfo a b => .ioGetInfo (constrainCalls a) (constrainCalls b)
  | .ioSetInfo a b c d e => .ioSetInfo (constrainCalls a) (constrainCalls b) (constrainCalls c) (constrainCalls d) (constrainCalls e)
  | .ioRead a b c => .ioRead (constrainCalls a) (constrainCalls b) c
  | .ioWrite a b c => .ioWrite (constrainCalls a) (constrainCalls b) (constrainCalls c)
  | .u8BitDecomposition a => .u8BitDecomposition (constrainCalls a)
  | .u8ShiftLeft a => .u8ShiftLeft (constrainCalls a)
  | .u8ShiftRight a => .u8ShiftRight (constrainCalls a)
  | .u8Xor a b => .u8Xor (constrainCalls a) (constrainCalls b)
  | .u8Add a b => .u8Add (constrainCalls a) (constrainCalls b)
  | .u8Mul a b => .u8Mul (constrainCalls a) (constrainCalls b)
  | .u8Sub a b => .u8Sub (constrainCalls a) (constrainCalls b)
  | .u8And a b => .u8And (constrainCalls a) (constrainCalls b)
  | .u8Or a b => .u8Or (constrainCalls a) (constrainCalls b)
  | .u8LessThan a b => .u8LessThan (constrainCalls a) (constrainCalls b)
  | .u32LessThan a b => .u32LessThan (constrainCalls a) (constrainCalls b)
  | .u8XorSplit7 a b => .u8XorSplit7 (constrainCalls a) (constrainCalls b)
  | .u8XorSplit4 a b => .u8XorSplit4 (constrainCalls a) (constrainCalls b)
  | .unconstrainedU32Add a b => .unconstrainedU32Add (constrainCalls a) (constrainCalls b)
  | .unconstrainedU32Add3 a b c => .unconstrainedU32Add3 (constrainCalls a) (constrainCalls b) (constrainCalls c)
  | .u32ToField a => .u32ToField (constrainCalls a)
  | .unconstrainedBigUintDivMod a b => .unconstrainedBigUintDivMod (constrainCalls a) (constrainCalls b)
  | .unconstrainedGToBytes a => .unconstrainedGToBytes (constrainCalls a)
  | .unconstrainedGInverse a => .unconstrainedGInverse (constrainCalls a)
  | .u8Lit a => .u8Lit a
  | .u8RangeCheck a b => .u8RangeCheck (constrainCalls a) (constrainCalls b)
  | .toField a => .toField (constrainCalls a)
  | .u8FromFieldUnsafe a => .u8FromFieldUnsafe (constrainCalls a)
  | .debug a b c => .debug a (b.map constrainCalls) (constrainCalls c)

def main (args : List String) : IO Unit := do
  let [outPrefix] := args | throw <| IO.userError "usage: IxVMCompare.lean OUTPUT_PREFIX"
  let full ← IO.ofExcept <| (do
    let source ← (← IxVM.ixVMFull).merge transitiveEntry
    (← source.merge auditEntries).merge ixvmPortCases).mapError toString
  let source := full.prune [`verify_transitive]
  save (outPrefix ++ "-standard.json") (← IO.ofExcept source.compile) "standard"
  save (outPrefix ++ "-validation.json")
    (← IO.ofExcept (full.prune [`verify_transitive, `verify_constant, `verify_serde, `check_port_cases]).compile) "validation"
  let source : Source.Toplevel := { source with functions := source.functions.map fun f =>
    { f with body := constrainCalls f.body } }
  save (outPrefix ++ "-constrained.json") (← IO.ofExcept source.compile) "constrained-calls"
