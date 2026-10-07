import Ix.CompileCert.Canon.Expr

/-!
# M7 L1: the constant comparison is a total preorder at a fixed context

The per-kind keys of design document §2.2 (definitions: kind, level count, type, value;
inductives: level, parameter, index and constructor counts, type, constructors pairwise;
constructors: level count, index, parameters, fields, type; recursors: level, parameter,
index, motive and minor counts, `k`, type, rules), and the kind tag first
(definition < inductive < recursor; the port fix C1 of §3.4).

`compareInd` and `compareCtor` run in `CmpM` (they read and fill the strong-result cache).
This module states their results without the cache, as pure functions with the same
structure (`ctorP`, `indP`, `constP`); `Cache.lean` proves that the cached functions return
exactly these values whenever the cache holds only true results. The theorems here:
`compareDef_total`, `ctorP_total`, `indP_total`, `compareRecr_total`, `constP_total`.

`constP` is the dispatch with `kindsByTag := true` (`Rules.compiler`, `portFixes := true`).
With `kindsByTag := false` (`Rules.today`, the Lean port before A2) the dispatch is not
antisymmetric: `compareConstBody_today_mixed` exhibits the defect C1 (a definition against
an inductive is `lt` both ways). No Lean input reaches it: components are kind-homogeneous.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Level Expr MutConst Def Ind Rec ConstructorVal RecursorVal RecursorRule)

/-! ## Leaf orders -/

instance transCmp_defKind : Std.TransCmp (compare : Ix.DefKind → Ix.DefKind → Ordering) where
  eq_swap {a b} := by cases a <;> cases b <;> rfl
  isLE_trans {a b c} := by cases a <;> cases b <;> cases c <;> decide

theorem cmp_true (o p : Ordering) : SOrder.cmp ⟨true, o⟩ ⟨true, p⟩ = ⟨true, o.then p⟩ := by
  cases o <;> rfl

/-! ## Definitions -/

theorem compareDef_total (c : CmpCtx) (hc : AddrCongr c.addr?) : TotalPre (compareDef c) := by
  have E := compareExpr_total c hc
  refine ((PreOn.pureCmp (compare : Ix.DefKind → Ix.DefKind → Ordering) (fun x : Def => x.kind)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : Def => x.levelParams.size)).cmpM
      ((E.comap (fun x : Def => (x.levelParams.toList, x.type)) fun _ _ => trivial).cmpM
        (E.comap (fun x : Def => (x.levelParams.toList, x.value)) fun _ _ => trivial)))).congr ?_
  intro x y _ _; rfl

/-! ## Constructors -/

/-- `compareCtor`'s comparison without the cache. -/
def ctorP (c : CmpCtx) (xl yl : List Name) (x y : ConstructorVal) : Except String SOrder :=
  SOrder.cmpM (pure ⟨true, compare x.cnst.levelParams.size y.cnst.levelParams.size⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.cidx y.cidx⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.numFields y.numFields⟩)
    (compareExpr c xl yl x.cnst.type y.cnst.type)

/-- `ctorP` on points: a constructor with its inductive's universe-parameter list. -/
def ctorC (c : CmpCtx) (a b : List Name × ConstructorVal) : Except String SOrder :=
  ctorP c a.1 b.1 a.2 b.2

theorem ctorP_total (c : CmpCtx) (hc : AddrCongr c.addr?) : TotalPre (ctorC c) := by
  have E := compareExpr_total c hc
  refine ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : List Name × ConstructorVal => a.2.cnst.levelParams.size)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : List Name × ConstructorVal => a.2.cidx)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : List Name × ConstructorVal => a.2.numParams)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : List Name × ConstructorVal => a.2.numFields)).cmpM
    (E.comap (fun a : List Name × ConstructorVal => (a.1, a.2.cnst.type))
      fun _ _ => trivial))))).congr ?_
  intro x y _ _; rfl

/-! ## Inductives -/

/-- The header of `compareInd`: level, parameter, index and constructor counts. -/
def indHdr (x y : Ind) : SOrder :=
  SOrder.cmpMany ⟨true, compare x.levelParams.size y.levelParams.size⟩
    [⟨true, compare x.numParams y.numParams⟩,
     ⟨true, compare x.numIndices y.numIndices⟩,
     ⟨true, compare x.ctors.size y.ctors.size⟩]

theorem indHdr_eq (x y : Ind) : indHdr x y =
    ⟨true, (compare x.levelParams.size y.levelParams.size).then
      ((compare x.numParams y.numParams).then
        ((compare x.numIndices y.numIndices).then (compare x.ctors.size y.ctors.size)))⟩ := by
  unfold indHdr
  cases compare x.levelParams.size y.levelParams.size <;>
    cases compare x.numParams y.numParams <;>
    cases compare x.numIndices y.numIndices <;> rfl

/-- `compareInd`'s comparison without the cache: the header, then the type, then the
constructors pairwise (lexicographically, the shorter list first). -/
def indP (c : CmpCtx) (x y : Ind) : Except String SOrder :=
  lexIf (pure (indHdr x y))
    (SOrder.cmpM (compareExpr c x.levelParams.toList y.levelParams.toList x.type y.type)
      (zipCtx (ctorC c) (x.levelParams.toList, x.ctors.toList)
        (y.levelParams.toList, y.ctors.toList)))

theorem indP_total (c : CmpCtx) (hc : AddrCongr c.addr?) : TotalPre (indP c) := by
  have E := compareExpr_total c hc
  have H : TotalPre (fun x y : Ind => (pure (indHdr x y) : Except String SOrder)) := by
    refine ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : Ind => x.levelParams.size)).cmpM
      ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : Ind => x.numParams)).cmpM
      ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : Ind => x.numIndices)).cmpM
      (PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : Ind => x.ctors.size))))).congr ?_
    intro x y _ _
    simp only [cmpM_pure, indHdr_eq]
  have C := ((ctorP_total c hc).zipCtx).mono
    (S' := fun a : List Name × List ConstructorVal => True) fun _ _ _ _ => trivial
  refine (H.lexIf ((E.comap (fun x : Ind => (x.levelParams.toList, x.type)) fun _ _ => trivial).cmpM
    (C.comap (fun x : Ind => (x.levelParams.toList, x.ctors.toList)) fun _ _ => trivial))).congr ?_
  intro x y _ _; rfl

/-! ## Recursors -/

/-- `compareRule` on points: a rule with its recursor's universe-parameter list. -/
def ruleC (c : CmpCtx) (a b : List Name × RecursorRule) : Except String SOrder :=
  compareRule c a.1 b.1 a.2 b.2

theorem compareRule_total (c : CmpCtx) (hc : AddrCongr c.addr?) : TotalPre (ruleC c) := by
  have E := compareExpr_total c hc
  refine ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : List Name × RecursorRule => a.2.nfields)).cmpM
    (E.comap (fun a : List Name × RecursorRule => (a.1, a.2.rhs)) fun _ _ => trivial)).congr ?_
  intro x y _ _; rfl

theorem compareRecr_total (c : CmpCtx) (hc : AddrCongr c.addr?) : TotalPre (compareRecr c) := by
  have E := compareExpr_total c hc
  have R := ((compareRule_total c hc).zipCtx).mono
    (S' := fun a : List Name × List RecursorRule => True) fun _ _ _ _ => trivial
  let L := fun x : RecursorVal => x.cnst.levelParams.toList
  refine ((PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun x : RecursorVal => x.cnst.levelParams.size)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : RecursorVal => x.numParams)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : RecursorVal => x.numIndices)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : RecursorVal => x.numMotives)).cmpM
    ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun x : RecursorVal => x.numMinors)).cmpM
    ((PreOn.pureCmp (compare : Bool → Bool → Ordering) (fun x : RecursorVal => x.k)).cmpM
    ((E.comap (fun x : RecursorVal => (L x, x.cnst.type)) fun _ _ => trivial).cmpM
      (R.comap (fun x : RecursorVal => (L x, x.rules.toList)) fun _ _ => trivial)))))))).congr ?_
  intro x y _ _; rfl

/-! ## The kind dispatch -/

def defOf : MutConst → Def
  | .defn d => d
  | _ => default

def indOf : MutConst → Ind
  | .indc i => i
  | _ => default

/-- A recursor value standing in for the other kinds. -/
def recDefault : RecursorVal :=
  ⟨⟨default, #[], default⟩, #[], 0, 0, 0, 0, #[], false, false⟩

def recOf : MutConst → RecursorVal
  | .recr r => r
  | _ => recDefault

/-- `compareConstBody` with `kindsByTag := true`, without the cache. -/
def constP (c : CmpCtx) : MutConst → MutConst → Except String SOrder
  | .defn x, .defn y => compareDef c x y
  | .indc x, .indc y => indP c x y
  | .recr x, .recr y => compareRecr c x y
  | x, y => pure ⟨true, compare (kindTag x) (kindTag y)⟩

theorem constP_total (c : CmpCtx) (hc : AddrCongr c.addr?) : TotalPre (constP c) := by
  refine PreOn.ofTag kindTag ?_ ?_
  · intro x y _ _ h
    cases x <;> cases y <;> simp_all [kindTag, constP, pure, Except.pure]
  intro T
  match T with
  | 0 =>
    refine ((compareDef_total c hc).comap defOf fun _ _ => trivial).congr ?_
    intro x y ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp_all [kindTag, constP, defOf]
  | 1 =>
    refine ((indP_total c hc).comap indOf fun _ _ => trivial).congr ?_
    intro x y ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp_all [kindTag, constP, indOf]
  | 2 =>
    refine ((compareRecr_total c hc).comap recOf fun _ _ => trivial).congr ?_
    intro x y ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp_all [kindTag, constP, recOf]
  | T + 3 =>
    refine PreOn.empty fun x ⟨_, h⟩ => ?_
    cases x <;> simp [kindTag] at h

/-- Defect C1 of the design document §3.4, as it stands in `Rules.today` (`portFixes :=
false`): two constants of different kinds compare `lt` in both orders, so the dispatch is
not antisymmetric. `Rules.compiler` (`portFixes := true`) compares the kind tags
(`constP`). -/
theorem compareConstBody_today_mixed (c : CmpCtx) (x : Def) (y : Ind) (st : CmpState) :
    (compareConstBody false false c (.defn x) (.indc y)).run st = .ok (⟨true, .lt⟩, st) ∧
    (compareConstBody false false c (.indc y) (.defn x)).run st = .ok (⟨true, .lt⟩, st) :=
  ⟨rfl, rfl⟩

end Ix.CompileCert.Canon
