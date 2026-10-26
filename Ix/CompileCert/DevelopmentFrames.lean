import Ix.CompileCert.FramePrimitives
import Ix.CompileCert.DevelopmentArity

/-! Placement invariants for the actual development cache. The conditional
invariant does not authorize arbitrary poisoned results from matching keys. -/
namespace Ix.CompileCert.DevelopmentFrames
open Ix (Expr)
open Ix.Compile.Image Ix.Compile.Canon
open SemanticFrames

def InstFrames (state : DevState) : Prop :=
  ∀ (bucket : UInt64) (entry : InstEntry), state.insts[bucket]? = some entry →
    Frames entry.value → Frames entry.body → Frames entry.result.1 ∧ Shell entry.body entry.result.1

theorem empty : InstFrames {} := by
  intro bucket entry found
  simp at found

theorem insert {state : DevState} (good : InstFrames state) (v e : Expr) (k : Nat)
    (result : Expr × Created) (valid : Frames result.1 ∧ Shell e result.1) :
    InstFrames { state with insts := state.insts.insert (instBucket v e k) ⟨v, e, k, result⟩ } := by
  intro bucket entry found hv he
  simp only [Std.HashMap.getElem?_insert] at found
  split at found
  · cases Option.some.inj found; exact valid
  · exact good bucket entry found hv he

theorem probe {state : DevState} (good : InstFrames state) {v e : Expr} {k : Nat}
    (hv : Frames v) (he : Frames e) {result : Expr × Created}
    (found : instProbe state v e k = some result) : Frames result.1 ∧ Shell e result.1 := by
  unfold instProbe at found
  cases hit : state.insts.get? (instBucket v e k) with
  | none => simp only [hit] at found; cases found
  | some entry =>
    simp only [hit] at found
    split at found
    · rename_i exactKeys
      simp only [Bool.and_eq_true, RawExact.exprEq_eq_true, beq_iff_eq] at exactKeys
      cases Option.some.inj found
      have valid := good _ entry hit (exactKeys.2 ▸ hv) (exactKeys.1.2 ▸ he)
      simpa only [exactKeys.1.2] using valid
    · cases found

theorem probe_fits {state : DevState} (good : InstFrames state) {v e : Expr} {k : Nat}
    (hv : Frames v) (he : Frames e) {result : Expr × Created}
    (found : instProbe state v e k = some result) (kind : Ix.SemanticContract.Kind)
    (nonLam : kind ≠ .lam) (matched : fits kind e = true) : fits kind result.1 = true :=
  FramePrimitives.fits_shell kind e result.1 nonLam (probe good hv he found).2 matched

theorem spine (e : Expr) (valid : Frames e) :
    Frames (getAppFnArgs e).1 ∧ ∀ a ∈ (getAppFnArgs e).2, Frames a := by
  induction e
  case app f a hash ih _ =>
    obtain ⟨head, args⟩ := ih valid.1
    refine ⟨head, ?_⟩
    intro x member
    simp only [getAppFnArgs, Array.mem_push] at member
    rcases member with old | rfl
    · exact args x old
    · exact valid.2
  all_goals exact ⟨valid, by simp [getAppFnArgs]⟩

theorem field {s : Ix.Name} {i : Nat} {e out : Expr} (valid : Frames e)
    (found : projCtor? s i e = some out) : Frames out := by
  rcases pair : getAppFnArgs e with ⟨head, args⟩
  have members := (spine e valid).2
  rw [pair] at members
  simp only [projCtor?, pair] at found
  split at found <;> try cases found
  split at found <;> try cases found
  exact members out (Array.mem_of_getElem? found)

end Ix.CompileCert.DevelopmentFrames
