module
public import Ix.Compile.SourceInput
public import Std.Data.HashSet.Lemmas

public section
namespace Ix.Compile.SourceInput.Uses

/-- Lookup obligations of expression syntax. Family/grouping membership and
literal blob addresses are not constant-reference uses. -/
inductive Use where
  | constant (name : Ix.Name)
  | projection (owner : Ix.Name)
  | natLiteral | strLiteral
  deriving Repr, DecidableEq

def same : Use → Use → Bool
  | .constant a,.constant b | .projection a,.projection b => ExactKey.nameEq a b
  | .natLiteral,.natLiteral | .strLiteral,.strLiteral => true
  | _,_ => false
instance : BEq Use := ⟨same⟩
theorem same_iff (a b : Use) : (a == b) = true ↔ a = b := by
  change same a b = true ↔ _
  cases a <;> cases b <;> simp [same, ExactKey.nameEq_iff]
instance : LawfulBEq Use where
  eq_of_beq := (same_iff _ _).mp
  rfl := (same_iff _ _).mpr rfl
instance : Hashable Use where
  hash
    | .constant n => mixHash 0 (hash n) | .projection n => mixHash 1 (hash n)
    | .natLiteral => 2 | .strLiteral => 3
instance : LawfulHashable Use where
  hash_eq a b same := by cases (same_iff a b).mp same; rfl

abbrev Set := Std.HashSet Use
@[expose] def join (a b : Set) : Set := a.union b
@[expose] def one (u : Use) : Set := ({} : Set).insert u

/-- Structural specification. The executable below probes its exact-key
memo before descending, so shared expression DAGs are not tree-expanded. -/
@[expose] def tree : Ix.Expr → Set
  | .const n _ _ => one (.constant n)
  | .proj n _ b _ => (tree b).insert (.projection n)
  | .lit (.natVal _) _ => one .natLiteral
  | .lit (.strVal _) _ => one .strLiteral
  | .app f a _ => join (tree f) (tree a)
  | .lam _ t b _ _ | .forallE _ t b _ _ => join (tree t) (tree b)
  | .letE _ t v b _ _ => join (join (tree t) (tree v)) (tree b)
  | .mdata _ b _ => tree b
  | _ => {}

structure Memo where
  entries : Std.HashMap ExactKey.ExprKey Set
  sound : ∀ (key : ExactKey.ExprKey) (uses : Set), entries[key]? = some uses → uses = tree key.expr
def empty : Memo := ⟨{}, by intro key uses h; simp at h⟩
def Extends (a b : Memo) : Prop :=
  ∀ (key : ExactKey.ExprKey) (uses : Set), a.entries[key]? = some uses → b.entries[key]? = some uses
theorem Extends.refl (m : Memo) : Extends m m := fun _ _ h => h
theorem Extends.trans {a b c : Memo} (ab : Extends a b) (bc : Extends b c) : Extends a c :=
  fun k u h => bc k u (ab k u h)
def store (m : Memo) (e : Ix.Expr) (uses : Set) (correct : uses = tree e) : Memo :=
  ⟨m.entries.insert ⟨e⟩ uses, by
    intro key value h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i same
      have eq : (⟨e⟩ : ExactKey.ExprKey) = key := eq_of_beq same
      subst key; cases h; exact correct
    · exact m.sound key value h⟩
theorem store_extends (m : Memo) (e : Ix.Expr) (uses : Set) (correct : uses = tree e) :
    Extends m (store m e uses correct) := by
  intro key value h
  simp only [store, Std.HashMap.getElem?_insert, beq_iff_eq]
  split
  · rename_i same; subst key; rw [m.sound _ _ h, correct]
  · exact h
structure Result (before : Memo) (e : Ix.Expr) where
  uses : Set
  correct : uses = tree e
  memo : Memo
  grows : Extends before memo
private def finish (before : Memo) (e : Ix.Expr) (work : Memo) (more : Extends before work)
    (uses : Set) (correct : uses = tree e) : Result before e :=
  ⟨uses,correct,store work e uses correct,more.trans (store_extends work e uses correct)⟩

/-- A per-declaration memo with erased correctness fields. Neither stored
expression hashes nor name hashes alone justify a cache/key equality. -/
def scan (m : Memo) (e : Ix.Expr) : Result m e :=
  match hit : m.entries[ExactKey.ExprKey.mk e]? with
  | some uses => ⟨uses,m.sound _ _ hit,m,.refl m⟩
  | none => match e with
    | .app f a h =>
      let x := scan m f; let y := scan x.memo a
      finish m (.app f a h) y.memo (x.grows.trans y.grows) (join x.uses y.uses)
        (by rw [x.correct,y.correct]; rfl)
    | .lam n t b bi h =>
      let x := scan m t; let y := scan x.memo b
      finish m (.lam n t b bi h) y.memo (x.grows.trans y.grows) (join x.uses y.uses)
        (by rw [x.correct,y.correct]; rfl)
    | .forallE n t b bi h =>
      let x := scan m t; let y := scan x.memo b
      finish m (.forallE n t b bi h) y.memo (x.grows.trans y.grows) (join x.uses y.uses)
        (by rw [x.correct,y.correct]; rfl)
    | .letE n t v b nd h =>
      let x := scan m t; let y := scan x.memo v; let z := scan y.memo b
      finish m (.letE n t v b nd h) z.memo (x.grows.trans (y.grows.trans z.grows))
        (join (join x.uses y.uses) z.uses) (by rw [x.correct,y.correct,z.correct]; rfl)
    | .mdata d b h =>
      let x := scan m b
      finish m (.mdata d b h) x.memo x.grows x.uses (by simpa only [tree] using x.correct)
    | .proj n i b h =>
      let x := scan m b
      finish m (.proj n i b h) x.memo x.grows (x.uses.insert (.projection n))
        (by rw [x.correct]; rfl)
    | .const n us h => finish m (.const n us h) m (.refl m) (one (.constant n)) rfl
    | .lit (.natVal n) h => finish m (.lit (.natVal n) h) m (.refl m) (one .natLiteral) rfl
    | .lit (.strVal s) h => finish m (.lit (.strVal s) h) m (.refl m) (one .strLiteral) rfl
    | .bvar n h => finish m (.bvar n h) m (.refl m) {} rfl
    | .fvar n h => finish m (.fvar n h) m (.refl m) {} rfl
    | .mvar n h => finish m (.mvar n h) m (.refl m) {} rfl
    | .sort u h => finish m (.sort u h) m (.refl m) {} rfl
termination_by structural e

def collect (e : Ix.Expr) : Set := (scan empty e).uses
theorem collect_eq (e : Ix.Expr) : collect e = tree e := (scan empty e).correct

inductive Part where
  | header | value | rule (index : Nat)
  deriving Repr, DecidableEq

/-- Only actual expression fields. Constructor-name lists, inductive all-lists
and recursor grouping are not silently made strict prefix prerequisites. -/
@[expose] def terms (ci : Ix.ConstantInfo) : List (Part × Ix.Expr) :=
  (.header,ci.getCnst.type) :: match ci with
  | .defnInfo d => [(.value,d.value)] | .thmInfo d => [(.value,d.value)]
  | .opaqueInfo d => [(.value,d.value)]
  | .recInfo d => d.rules.toList.zipIdx.map (fun (r,i) => (.rule i,r.rhs))
  | _ => []
@[expose] def trees (xs : List (Part × Ix.Expr)) : List (Part × Set) := xs.map fun (p,e) => (p,tree e)
structure TermsResult (before : Memo) (xs : List (Part × Ix.Expr)) where
  uses : List (Part × Set)
  correct : uses = trees xs
  memo : Memo
  grows : Extends before memo
def scanTerms (m : Memo) : (xs : List (Part × Ix.Expr)) → TermsResult m xs
  | [] => ⟨[],rfl,m,.refl m⟩
  | (p,e) :: xs =>
    let x := scan m e; let y := scanTerms x.memo xs
    ⟨(p,x.uses) :: y.uses, by rw [x.correct,y.correct]; rfl, y.memo,x.grows.trans y.grows⟩
def capture (ci : Ix.ConstantInfo) : List (Part × Set) := (scanTerms empty (terms ci)).uses
theorem capture_eq (ci : Ix.ConstantInfo) : capture ci = trees (terms ci) := (scanTerms empty (terms ci)).correct

end Ix.Compile.SourceInput.Uses
namespace Ix.Compile.SourceInput
/-- Complete original lookup first; a successful result retains only compact
tagged uses, releasing the transient canonical declaration and expression memo.
This does not establish scope, universe bounds, actual reading or typing. -/
@[expose] def Carrier.captureUsesAt (s : Carrier) (name : Ix.Name) : Except Error (List (Uses.Part × Uses.Set)) :=
  (fun form => Uses.capture form.original) <$> s.valueAt name
end Ix.Compile.SourceInput

end
