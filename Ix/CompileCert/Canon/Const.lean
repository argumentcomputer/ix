import Ix.CompileCert.Canon.Expr

/-! # Pass 1's constant comparison is a total preorder at a fixed context

CS-01, ported from the donor `a9cf3607` (`Canon/Const`). The per-kind keys
(definitions: kind, level count, type, value; inductives: level, parameter,
index and constructor counts, type, constructors pairwise; constructors:
level count, index, parameters, fields, type; recursors: level, parameter,
index, motive and minor counts, `k`, type, rules), with the kind tag first
(definition < inductive < recursor).

`compareInd` and `compareCtor` run in `CmpM` (they read and fill the
strong-result cache). This module states their results without the cache,
as pure functions with the same structure (`compareCtorKeys` is the
compiler's own, `indP`, `constP`); `Cache.lean` proves that the cached
functions return exactly these values whenever the cache holds only true
results. The theorems: `compareDef_total`, `ctorP_total`, `indP_total`,
`compareRecr_total`, `constP_total`, each on the constants whose
expressions reference faithful names only (`ConstIn N`). Today's dispatch
compares two kinds by their tags (the donor's port fix C1 is the only
behaviour now, so its defect exhibit is gone). -/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Level Expr MutConst Def Ind Rec ConstructorVal RecursorVal RecursorRule)

/-! ## Leaf orders -/

instance transCmp_defKind : Std.TransCmp (compare : Ix.DefKind → Ix.DefKind → Ordering) where
  eq_swap {a b} := by cases a <;> cases b <;> rfl
  isLE_trans {a b c} := by cases a <;> cases b <;> cases c <;> decide

theorem cmp_true (o p : Ordering) : SOrder.cmp ⟨true, o⟩ ⟨true, p⟩ = ⟨true, o.then p⟩ := by
  cases o <;> rfl

/-! ## The names a constant references -/

def DefIn (N : Name → Prop) (x : Def) : Prop := ExprIn N x.type ∧ ExprIn N x.value

def IndIn (N : Name → Prop) (x : Ind) : Prop :=
  ExprIn N x.type ∧ ∀ c ∈ x.ctors.toList, ExprIn N c.cnst.type

def RecIn (N : Name → Prop) (x : RecursorVal) : Prop :=
  ExprIn N x.cnst.type ∧ ∀ r ∈ x.rules.toList, ExprIn N r.rhs

/-- Every expression of the constant references only names of `N`. -/
def ConstIn (N : Name → Prop) : MutConst → Prop
  | .defn x => DefIn N x
  | .indc x => IndIn N x
  | .recr x => RecIn N x

/-! ## Definitions -/

theorem compareDef_total (c : CmpCtx) {N : Name → Prop} (hN : Faithful N) :
    PreOn (DefIn N) (compareDef c) := by
  have E := compareExpr_total c hN
  refine ((PreOn.pureCmp (compare : Ix.DefKind → Ix.DefKind → Ordering) (fun x : Def => x.kind)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : Def => x.levelParams.size)).cmpM
      ((E.comap (fun x : Def => (x.levelParams.toList, x.type)) fun _ h => h.1).cmpM
        (E.comap (fun x : Def => (x.levelParams.toList, x.value)) fun _ h => h.2)))).congr ?_
  intro x y _ _; rfl

/-! ## Constructors -/

/-- `compareCtorKeys` on points: a constructor with its inductive's
universe-parameter list. -/
def ctorC (c : CmpCtx) (a b : List Name × ConstructorVal) : Except CmpError SOrder :=
  compareCtorKeys c a.1 b.1 a.2 b.2

theorem ctorP_total (c : CmpCtx) {N : Name → Prop} (hN : Faithful N) :
    PreOn (fun a : List Name × ConstructorVal => ExprIn N a.2.cnst.type) (ctorC c) := by
  have E := compareExpr_total c hN
  refine ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : List Name × ConstructorVal => a.2.cnst.levelParams.size)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : List Name × ConstructorVal => a.2.cidx)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : List Name × ConstructorVal => a.2.numParams)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : List Name × ConstructorVal => a.2.numFields)).cmpM
    (E.comap (fun a : List Name × ConstructorVal => (a.1, a.2.cnst.type))
      fun _ h => h))))).congr ?_
  intro x y _ _; rfl

/-! ## Inductives -/

theorem indHeader_eq (x y : Ind) : indHeader x y =
    ⟨true, (compare x.levelParams.size y.levelParams.size).then
      ((compare x.numParams y.numParams).then
        ((compare x.numIndices y.numIndices).then (compare x.ctors.size y.ctors.size)))⟩ := by
  unfold indHeader
  cases compare x.levelParams.size y.levelParams.size <;>
    cases compare x.numParams y.numParams <;>
    cases compare x.numIndices y.numIndices <;> rfl

/-- `compareInd`'s comparison without the cache: the header, then the type,
then the constructors pairwise (lexicographically, the shorter list
first). -/
def indP (c : CmpCtx) (x y : Ind) : Except CmpError SOrder :=
  lexIf (pure (indHeader x y))
    (SOrder.cmpM (compareExpr c x.levelParams.toList y.levelParams.toList x.type y.type)
      (zipCtx (ctorC c) (x.levelParams.toList, x.ctors.toList)
        (y.levelParams.toList, y.ctors.toList)))

theorem indP_total (c : CmpCtx) {N : Name → Prop} (hN : Faithful N) :
    PreOn (IndIn N) (indP c) := by
  have E := compareExpr_total c hN
  have H : TotalPre (fun x y : Ind => (pure (indHeader x y) : Except CmpError SOrder)) := by
    refine ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : Ind => x.levelParams.size)).cmpM
      ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : Ind => x.numParams)).cmpM
      ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : Ind => x.numIndices)).cmpM
      (PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : Ind => x.ctors.size))))).congr ?_
    intro x y _ _
    simp only [cmpM_pure, indHeader_eq]
  have C := (ctorP_total c hN).zipCtx
  refine ((H.mono fun _ _ => trivial).lexIf
    ((E.comap (fun x : Ind => (x.levelParams.toList, x.type)) fun _ h => h.1).cmpM
    (C.comap (fun x : Ind => (x.levelParams.toList, x.ctors.toList)) fun _ h => h.2))).congr ?_
  intro x y _ _; rfl

/-! ## Recursors -/

/-- `compareRule` on points: a rule with its recursor's universe-parameter
list. -/
def ruleC (c : CmpCtx) (a b : List Name × RecursorRule) : Except CmpError SOrder :=
  compareRule c a.1 b.1 a.2 b.2

theorem compareRule_total (c : CmpCtx) {N : Name → Prop} (hN : Faithful N) :
    PreOn (fun a : List Name × RecursorRule => ExprIn N a.2.rhs) (ruleC c) := by
  have E := compareExpr_total c hN
  refine ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : List Name × RecursorRule => a.2.nfields)).cmpM
    (E.comap (fun a : List Name × RecursorRule => (a.1, a.2.rhs)) fun _ h => h)).congr ?_
  intro x y _ _; rfl

theorem compareRecr_total (c : CmpCtx) {N : Name → Prop} (hN : Faithful N) :
    PreOn (RecIn N) (compareRecr c) := by
  have E := compareExpr_total c hN
  have R := (compareRule_total c hN).zipCtx
  let L := fun x : RecursorVal => x.cnst.levelParams.toList
  refine ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun x : RecursorVal => x.cnst.levelParams.size)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : RecursorVal => x.numParams)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : RecursorVal => x.numIndices)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : RecursorVal => x.numMotives)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : RecursorVal => x.numMinors)).cmpM
    ((PreOn.pureCmp (compare : Bool → Bool → Ordering) (fun x : RecursorVal => x.k)).cmpM
    ((E.comap (fun x : RecursorVal => (L x, x.cnst.type)) fun _ h => h.1).cmpM
      (R.comap (fun x : RecursorVal => (L x, x.rules.toList)) fun _ h => h.2)))))))).congr ?_
  intro x y _ _; rfl

/-! ## The kind dispatch -/

/-- Stand-ins built without hashing. -/
def rawDef : Def := ⟨rawName, #[], rawExpr, .defn, rawExpr, .opaque, .safe, #[]⟩
def rawInd : Ind := ⟨rawName, #[], rawExpr, 0, 0, #[], #[], 0, false, false, false⟩

def defOf : MutConst → Def
  | .defn d => d
  | _ => rawDef

def indOf : MutConst → Ind
  | .indc i => i
  | _ => rawInd

/-- A recursor value standing in for the other kinds. -/
def recDefault : RecursorVal :=
  ⟨⟨rawName, #[], rawExpr⟩, #[], 0, 0, 0, 0, #[], false, false⟩

def recOf : MutConst → RecursorVal
  | .recr r => r
  | _ => recDefault

/-- `compareConstBody` without the cache. -/
def constP (c : CmpCtx) : MutConst → MutConst → Except CmpError SOrder
  | .defn x, .defn y => compareDef c x y
  | .indc x, .indc y => indP c x y
  | .recr x, .recr y => compareRecr c x y
  | x, y => pure ⟨true, compare (kindTag x) (kindTag y)⟩

/-- **The constant comparison is a total preorder at a fixed context**, on
the constants whose expressions reference faithful names only. -/
theorem constP_total (c : CmpCtx) {N : Name → Prop} (hN : Faithful N) :
    PreOn (ConstIn N) (constP c) := by
  refine PreOn.ofTag kindTag ?_ ?_
  · intro x y _ _ h
    cases x <;> cases y <;> simp_all [kindTag, constP, pure, Except.pure]
  intro T
  match T with
  | 0 =>
    refine ((compareDef_total c hN).comap defOf fun x h => ?_).congr ?_
    · obtain ⟨hx, t⟩ := h; cases x <;> simp_all [kindTag, ConstIn, defOf]
    · intro x y ⟨_, hx⟩ ⟨_, hy⟩
      cases x <;> cases y <;> simp_all [kindTag, constP, defOf]
  | 1 =>
    refine ((indP_total c hN).comap indOf fun x h => ?_).congr ?_
    · obtain ⟨hx, t⟩ := h; cases x <;> simp_all [kindTag, ConstIn, indOf]
    · intro x y ⟨_, hx⟩ ⟨_, hy⟩
      cases x <;> cases y <;> simp_all [kindTag, constP, indOf]
  | 2 =>
    refine ((compareRecr_total c hN).comap recOf fun x h => ?_).congr ?_
    · obtain ⟨hx, t⟩ := h; cases x <;> simp_all [kindTag, ConstIn, recOf]
    · intro x y ⟨_, hx⟩ ⟨_, hy⟩
      cases x <;> cases y <;> simp_all [kindTag, constP, recOf]
  | T + 3 =>
    refine PreOn.empty fun x ⟨_, h⟩ => ?_
    cases x <;> simp [kindTag] at h

end Ix.CompileCert.Canon
