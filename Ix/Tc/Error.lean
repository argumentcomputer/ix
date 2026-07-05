module

public import Ix.Tc.Expr

/-!
Mirror: crates/kernel/src/error.rs

Type checker error types. (Rust's `u64_to_usize` helper is unneeded: Lean
`Nat` conversions are total.)
-/

public section
@[expose] section

namespace Ix.Tc

inductive TcError (m : Mode) where
  | typeExpected
  | funExpected (e : KExpr m) (whnf : KExpr m)
  | appTypeMismatch (aTy : KExpr m) (dom : KExpr m) (depth : Nat)
  | declTypeMismatch
  | unknownConst (addr : Address)
  | univParamMismatch (expected : UInt64) (got : Nat)
  /-- An interior universe substitution hit `param idx` out of range for the
      supplied universe list. Distinct from `univParamMismatch` (the arity
      gate at const-infer time); this fires from `substUniv` as
      defense-in-depth against paths that reach substitution unchecked. -/
  | univParamOutOfRange (idx : UInt64) (bound : Nat)
  | varOutOfRange (idx : UInt64) (ctxLen : Nat)
  | defEqFailed
  | maxRecDepth
  | maxRecFuel
  /-- A stored mutual block fails the kernel's canonicity check: under the
      stored partition, an adjacent pair did not satisfy strict `lt`.
      `gt` means the stored order disagrees with `sortConsts`; `eq` means two
      distinct entries are alpha-equivalent (the compiler should have
      collapsed them). `pos` is the index of the pair's first member. -/
  | nonCanonicalBlock (block : Address) (pos : Nat) (ordering : Ordering)
  /-- A free variable reached a comparator that requires de-Bruijn-only
      inputs. Canonicalization runs over closed, egressed expressions before
      any binder opening; an fvar here means a kernel path leaked an open
      expression into the canonical-ordering stage. -/
  | unexpectedFVarInComparator
  | other (msg : String)

namespace TcError

def render : TcError m → String
  | .typeExpected => "type expected"
  | .funExpected e whnf => s!"function expected, got {e} (whnf: {whnf})"
  | .appTypeMismatch aTy dom depth =>
    s!"app type mismatch at depth {depth}: arg has type {aTy}, domain is {dom}"
  | .declTypeMismatch => "declaration type mismatch"
  | .unknownConst addr => s!"unknown constant {(toString addr).take 12}"
  | .univParamMismatch expected got =>
    s!"universe param count: expected {expected.toNat}, got {got}"
  | .univParamOutOfRange idx bound =>
    s!"universe Param({idx.toNat}) out of range: only {bound} universes supplied"
  | .varOutOfRange idx ctxLen =>
    s!"variable #{idx.toNat} out of range (context depth {ctxLen})"
  | .defEqFailed => "definitional equality check failed"
  | .maxRecDepth => "max recursion depth exceeded"
  | .maxRecFuel => "recursive fuel exhausted"
  | .nonCanonicalBlock block pos ordering =>
    let dir := match ordering with
      | .lt => "Less"
      | .eq => "Equal (uncollapsed alpha-equivalence)"
      | .gt => "Greater (wrong order)"
    s!"non-canonical block {(toString block).take 12}: adjacent pair at position {pos} compares {dir} (expected strict Less)"
  | .unexpectedFVarInComparator =>
    "unexpected free variable in canonical-ordering comparator: canonicalization must run before any binder opening"
  | .other s => s

instance : ToString (TcError m) := ⟨render⟩

instance : Repr (TcError m) := ⟨fun e _ => .text e.render⟩

instance : Inhabited (TcError m) := ⟨.typeExpected⟩

end TcError

end Ix.Tc

end
end
