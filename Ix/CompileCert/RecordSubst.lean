import Ix.CompileCert.RecordSourceShape
import Ix.CompileCert.CacheSound
import Ix.CompileM

open private Ix.CompileM.substRecords.record? Ix.CompileM.substRecords.go from Ix.CompileM

/-! The actual record-metadata walk. Root binder kind is retained separately
from the conditional semantic-frame relation; no raw-input erasure claim. -/
namespace Ix.CompileCert.RecordSubst
open Ix (Expr Name)
open Ix.CompileM Ix.Compile.ExactKey Ix.CompileCert.RecordSourceShape

def binderKind : Expr → Option Ix.SemanticContract.Kind
  | .lam .. => some .lam
  | .forallE .. => some .all
  | .letE .. => some .letE
  | _ => none

inductive Frames : Expr → Expr → Prop where
  | refl (e) : Frames e e
  | app {f a f' a' h h'} : Frames f f' → Frames a a' → Frames (.app f a h) (.app f' a' h')
  | lam {t b t' b' h h'} (n bi) : Frames t t' → Frames b b' →
      Frames (.lam n t b bi h) (.lam n t' b' bi h')
  | all {t b t' b' h h'} (n bi) : Frames t t' → Frames b b' →
      Frames (.forallE n t b bi h) (.forallE n t' b' bi h')
  | letE {t v b t' v' b' h h'} (n nd) : Frames t t' → Frames v v' → Frames b b' →
      Frames (.letE n t v b nd h) (.letE n t' v' b' nd h')
  | proj {e e' h h'} (n i) : Frames e e' → Frames (.proj n i e h) (.proj n i e' h')
  | mdata {e e' h h'} (data) : Frames e e' → Frames (.mdata data e h) (.mdata data e' h')
  | plain {e e' h h'} (data data') : Ix.SemanticContract.hasMetadata data = false →
      Ix.SemanticContract.hasMetadata data' = false → Frames e e' →
      Frames (.mdata data e h) (.mdata data' e' h')

def Meaning (e : Expr) (r : Expr × Bool) : Prop :=
  binderKind r.1 = binderKind e ∧ (ContractArity e → Frames e r.1)
abbrev Memo := Std.HashMap ExprKey (Expr × Bool)
def Sound (memo : Memo) : Prop := CacheSound (fun key value => Meaning key.expr value) memo
private def Valid (p : α → Prop) (action : StateM Memo α) : Prop :=
  ∀ before, Sound before → Sound (action.run before).2 ∧ p (action.run before).1

private theorem pureV {p : α → Prop} {v : α} (h : p v) : Valid p (pure v) :=
  fun _ sound => ⟨sound, h⟩
private theorem bindV {p : α → Prop} {q : β → Prop} {a : StateM Memo α} {f : α → StateM Memo β}
    (first : Valid p a) (next : ∀ v, p v → Valid q (f v)) : Valid q (a >>= f) := by
  intro before sound
  have h := first before sound
  exact next (a.run before).1 h.2 (a.run before).2 h.1
private theorem getV : Valid Sound get := fun _ sound => ⟨sound, sound⟩
private theorem insertV (e : Expr) (r : Expr × Bool) (h : Meaning e r) :
    Valid (fun _ => True) (modify fun m : Memo => m.insert e r) :=
  fun _ sound => ⟨sound.insert ⟨e⟩ r h, trivial⟩
private theorem unchanged (e : Expr) (flag : Bool) : Meaning e (e, flag) :=
  ⟨rfl, fun _ => .refl e⟩
private theorem doneV (e : Expr) (r : Expr × Bool) (h : Meaning e r) :
    Valid (Meaning e) (do let r' ← pure r; modify fun m : Memo => m.insert e r'; pure r') :=
  bindV (pureV h) (fun r' correct => bindV (insertV e r' correct) (fun _ _ => pureV correct))

theorem record_shape (records : Std.HashMap Nat (Nat × UInt64))
    {data out : Array (Name × Ix.DataValue)}
    (run : Ix.CompileM.substRecords.record? records data = some out) :
    data.size = 1 ∧ Ix.SemanticContract.hasMetadata out = false := by
  obtain ⟨xs⟩ := data
  cases xs with
  | nil => cases run
  | cons p rest =>
    cases rest with
    | cons => cases run
    | nil =>
      obtain ⟨key, value⟩ := p
      cases value <;> try cases run
      case ofNat n =>
        change (if key == Ix.Compile.Pass.inlineKey then (records.get? n).map
          (fun (s, m) => #[(Ix.Compile.Pass.inlineKey, .ofNat s),
            (Ix.Compile.Pass.inlineMetaKey, .ofNat m.toNat)]) else none) = some out at run
        split at run
        · obtain ⟨⟨slot, root⟩, _, rfl⟩ := Option.map_eq_some_iff.mp run
          refine ⟨rfl, ?_⟩
          simp [Ix.SemanticContract.hasMetadata, Ix.SemanticContract.reserved,
            Ix.SemanticContract.toLeanName, Ix.SemanticContract.key, Ix.Compile.Pass.inlineKey,
            Ix.Compile.Pass.inlineMetaKey, Ix.Compile.Pass.ixComponent, Name.mkStr, Name.mkAnon, Id.run]
          decide
        · cases run

theorem record_plain (records : Std.HashMap Nat (Nat × UInt64))
    {data out : Array (Name × Ix.DataValue)}
    (arity : Ix.SemanticContract.hasMetadata data = true → data.size = 3)
    (run : Ix.CompileM.substRecords.record? records data = some out) :
    Ix.SemanticContract.hasMetadata data = false ∧ Ix.SemanticContract.hasMetadata out = false := by
  obtain ⟨one, plain⟩ := record_shape records run
  refine ⟨?_, plain⟩
  cases h : Ix.SemanticContract.hasMetadata data
  · rfl
  · have three := arity h; omega

private theorem goV (records : Std.HashMap Nat (Nat × UInt64)) (e : Expr) :
    Valid (Meaning e) (Ix.CompileM.substRecords.go records e) := by
  induction e using (measure (fun e : Expr => sizeOf e)).wf.induction with
  | h e ih =>
    change ∀ y, sizeOf y < sizeOf e → Valid (Meaning y) (Ix.CompileM.substRecords.go records y) at ih
    rw [Ix.CompileM.substRecords.go]
    apply bindV getV
    intro memo sound
    cases found : memo.get? (ExprKey.mk e)
    ·
      cases e
      case bvar => exact doneV _ _ (unchanged _ false)
      case fvar => exact doneV _ _ (unchanged _ false)
      case mvar => exact doneV _ _ (unchanged _ false)
      case sort => exact doneV _ _ (unchanged _ false)
      case const => exact doneV _ _ (unchanged _ false)
      case lit => exact doneV _ _ (unchanged _ false)
      case app f a hash =>
        apply bindV (ih f (by simp; omega)); rintro ⟨f', cf⟩ hf
        apply bindV (ih a (by simp; omega)); rintro ⟨a', ca⟩ ha
        apply doneV; split
        · exact ⟨rfl, fun h => .app (hf.2 h.1) (ha.2 h.2)⟩
        · exact unchanged _ _
      case lam n t b bi hash =>
        apply bindV (ih t (by simp; omega)); rintro ⟨t', ct⟩ ht
        apply bindV (ih b (by simp; omega)); rintro ⟨b', cb⟩ hb
        apply doneV; split
        · exact ⟨rfl, fun h => .lam n bi (ht.2 h.1) (hb.2 h.2)⟩
        · exact unchanged _ _
      case forallE n t b bi hash =>
        apply bindV (ih t (by simp; omega)); rintro ⟨t', ct⟩ ht
        apply bindV (ih b (by simp; omega)); rintro ⟨b', cb⟩ hb
        apply doneV; split
        · exact ⟨rfl, fun h => .all n bi (ht.2 h.1) (hb.2 h.2)⟩
        · exact unchanged _ _
      case letE n t v b nd hash =>
        apply bindV (ih t (by simp; omega)); rintro ⟨t', ct⟩ ht
        apply bindV (ih v (by simp; omega)); rintro ⟨v', cv⟩ hv
        apply bindV (ih b (by simp; omega)); rintro ⟨b', cb⟩ hb
        apply doneV; split
        · exact ⟨rfl, fun h => .letE n nd (ht.2 h.1) (hv.2 h.2.1) (hb.2 h.2.2)⟩
        · exact unchanged _ _
      case proj n i x hash =>
        apply bindV (ih x (by simp; omega)); rintro ⟨x', c⟩ hx
        apply doneV; split
        · exact ⟨rfl, fun h => .proj n i (hx.2 h)⟩
        · exact unchanged _ _
      case mdata data x hash =>
        apply bindV (ih x (by simp; omega)); rintro ⟨x', c⟩ hx
        cases hit : Ix.CompileM.substRecords.record? records data
        · apply doneV; split
          · exact ⟨rfl, fun h => .mdata data (hx.2 h.2)⟩
          · exact unchanged _ _
        · rename_i out
          apply doneV
          refine ⟨rfl, fun h => ?_⟩
          obtain ⟨plain, plain'⟩ := record_plain records h.1 hit
          exact .plain data out plain plain' (hx.2 h.2)
    · rename_i r
      exact pureV (sound ⟨e⟩ r found)

/-- The actual empty memo supplies both guarantees; no cache premise. -/
theorem produced (records : Std.HashMap Nat (Nat × UInt64)) (e : Expr) :
    binderKind (substRecords records e) = binderKind e ∧
      (ContractArity e → Frames e (substRecords records e)) :=
  (goV records e {} (CacheSound.empty _)).2

end Ix.CompileCert.RecordSubst
