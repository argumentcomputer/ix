module
public import Ix.Compile.SourceGraph
public import Std.Data.HashMap.Lemmas

public section
namespace Ix.Compile.SourceGraph
namespace Literal

abbrev Bits := Bool × Bool
def tree (e : Expr) : Bits := (hasStrLit e, hasNatLit e)
def join (a b : Bits) : Bits := (a.1 || b.1, a.2 || b.2)

/-- Exact expression keys, with a checked result for every stored entry. -/
structure Memo where
  entries : Std.HashMap ExactKey.ExprKey Bits
  sound : ∀ (key : ExactKey.ExprKey) (bits : Bits), entries[key]? = some bits → bits = tree key.expr

def empty : Memo := ⟨{}, by intro key bits h; simp at h⟩
def Extends (a b : Memo) : Prop :=
  ∀ (key : ExactKey.ExprKey) (bits : Bits), a.entries[key]? = some bits → b.entries[key]? = some bits

theorem Extends.refl (m : Memo) : Extends m m := fun _ _ h => h
theorem Extends.trans {a b c : Memo} (ab : Extends a b) (bc : Extends b c) : Extends a c :=
  fun key bits h => bc key bits (ab key bits h)

def store (m : Memo) (e : Expr) (bits : Bits) (correct : bits = tree e) : Memo :=
  ⟨m.entries.insert ⟨e⟩ bits, by
    intro key value h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i same
      have eq : (⟨e⟩ : ExactKey.ExprKey) = key := eq_of_beq same
      subst key
      cases h
      exact correct
    · exact m.sound key value h⟩

theorem store_extends (m : Memo) (e : Expr) (bits : Bits) (correct : bits = tree e) :
    Extends m (store m e bits correct) := by
  intro key value h
  simp only [store, Std.HashMap.getElem?_insert, beq_iff_eq]
  split
  · rename_i same
    subst key
    rw [m.sound _ _ h, correct]
  · exact h

structure Result (before : Memo) (e : Expr) where
  bits : Bits
  correct : bits = tree e
  memo : Memo
  grows : Extends before memo
  cached : memo.entries[ExactKey.ExprKey.mk e]? = some bits

private def finish (before : Memo) (e : Expr) (work : Memo) (more : Extends before work)
    (bits : Bits) (correct : bits = tree e) : Result before e :=
  ⟨bits, correct, store work e bits correct, more.trans (store_extends work e bits correct), by simp [store]⟩

/-- The memo probe precedes every recursive descent. Proof fields erase; a
constant's terms share one memo and the exported wrapper discards it. -/
def scan (m : Memo) (e : Expr) : Result m e :=
  match hit : m.entries[ExactKey.ExprKey.mk e]? with
  | some bits => ⟨bits, m.sound _ _ hit, m, .refl m, hit⟩
  | none => match e with
    | .app f a h =>
      let x := scan m f
      let y := scan x.memo a
      finish m (.app f a h) y.memo (x.grows.trans y.grows) (join x.bits y.bits)
        (by rw [x.correct, y.correct]; rfl)
    | .lam n t b bi h =>
      let x := scan m t
      let y := scan x.memo b
      finish m (.lam n t b bi h) y.memo (x.grows.trans y.grows) (join x.bits y.bits)
        (by rw [x.correct, y.correct]; rfl)
    | .forallE n t b bi h =>
      let x := scan m t
      let y := scan x.memo b
      finish m (.forallE n t b bi h) y.memo (x.grows.trans y.grows) (join x.bits y.bits)
        (by rw [x.correct, y.correct]; rfl)
    | .letE n t v b nd h =>
      let x := scan m t
      let y := scan x.memo v
      let z := scan y.memo b
      finish m (.letE n t v b nd h) z.memo (x.grows.trans (y.grows.trans z.grows))
        (join (join x.bits y.bits) z.bits)
        (by rw [x.correct, y.correct, z.correct]; rfl)
    | .mdata d b h =>
      let x := scan m b
      finish m (.mdata d b h) x.memo x.grows x.bits
        (by simpa only [tree, hasStrLit, hasNatLit] using x.correct)
    | .proj n i b h =>
      let x := scan m b
      finish m (.proj n i b h) x.memo x.grows x.bits
        (by simpa only [tree, hasStrLit, hasNatLit] using x.correct)
    | .lit (.strVal s) h => finish m (.lit (.strVal s) h) m (.refl m) (true, false) rfl
    | .lit (.natVal n) h => finish m (.lit (.natVal n) h) m (.refl m) (false, true) rfl
    | .bvar i h => finish m (.bvar i h) m (.refl m) (false, false) rfl
    | .fvar n h => finish m (.fvar n h) m (.refl m) (false, false) rfl
    | .mvar n h => finish m (.mvar n h) m (.refl m) (false, false) rfl
    | .sort u h => finish m (.sort u h) m (.refl m) (false, false) rfl
    | .const n us h => finish m (.const n us h) m (.refl m) (false, false) rfl
termination_by structural e

theorem scan_correct (m : Memo) (e : Expr) : (scan m e).bits = tree e := (scan m e).correct
theorem scan_extends (m : Memo) (e : Expr) : Extends m (scan m e).memo := (scan m e).grows
theorem scan_cached (m : Memo) (e : Expr) : (scan m e).memo.entries[ExactKey.ExprKey.mk e]? = some (scan m e).bits :=
  (scan m e).cached
theorem scan_sound (m : Memo) (e : Expr) (key : ExactKey.ExprKey) (bits : Bits)
    (hit : (scan m e).memo.entries[key]? = some bits) : bits = tree key.expr :=
  (scan m e).memo.sound key bits hit

/-- A hit returns unchanged storage before any child is queried. -/
theorem scan_hit (m : Memo) (e : Expr) (bits : Bits) (hit : m.entries[ExactKey.ExprKey.mk e]? = some bits) :
    (scan m e).bits = bits ∧ (scan m e).memo = m := by
  have result : scan m e = ⟨bits, m.sound _ _ hit, m, .refl m, hit⟩ := by
    rw [scan]
    split
    · rename_i value found
      have same : value = bits := Option.some.inj (found.symm.trans hit)
      subst value
      rfl
    · rename_i found
      cases found.symm.trans hit
  rw [result]
  exact ⟨rfl, rfl⟩

structure TermsResult (before : Memo) (es : List Expr) where
  bits : Bits
  correct : bits = (es.any hasStrLit, es.any hasNatLit)
  memo : Memo
  grows : Extends before memo

def scanTerms (m : Memo) : (es : List Expr) → TermsResult m es
  | [] => ⟨(false, false), rfl, m, .refl m⟩
  | e :: es =>
    let x := scan m e
    let y := scanTerms x.memo es
    ⟨join x.bits y.bits, by rw [x.correct, y.correct]; rfl,
      y.memo, x.grows.trans y.grows⟩

theorem scanTerms_correct (m : Memo) (es : List Expr) :
    (scanTerms m es).bits = (es.any hasStrLit, es.any hasNatLit) := (scanTerms m es).correct
theorem scanTerms_extends (m : Memo) (es : List Expr) : Extends m (scanTerms m es).memo := (scanTerms m es).grows

end Literal

def literalUseShared (ci : ConstantInfo) : LiteralUse :=
  let bits := (Literal.scanTerms Literal.empty (terms ci)).bits
  if bits.1 then .string else if bits.2 then .nat else .none

theorem literalUseShared_eq (ci : ConstantInfo) : literalUseShared ci = literalUse ci := by
  simp only [literalUseShared, (Literal.scanTerms Literal.empty (terms ci)).correct, literalUse]

def captureUsingShared (ci : ConstantInfo) (direct : Ix.Set Name) : Node :=
  { direct, literals := literalUseShared ci, grouping := (captureUsing ci direct).grouping }

theorem captureUsingShared_eq (ci : ConstantInfo) (direct : Ix.Set Name) :
    captureUsingShared ci direct = captureUsing ci direct := by
  simp only [captureUsingShared, literalUseShared_eq, captureUsing]

def rowUsingShared (n : Name) (ci : ConstantInfo) (direct : Ix.Set Name) : Row :=
  ⟨n, captureUsingShared ci direct, keep ci⟩

theorem rowUsingShared_eq (n : Name) (ci : ConstantInfo) (direct : Ix.Set Name) :
    rowUsingShared n ci direct = rowUsing n ci direct := by
  simp only [rowUsingShared, rowUsing, captureUsingShared_eq]

end Ix.Compile.SourceGraph
