import Ix.CompileCert.Canon.Ref

/-!
# M7 L1: the expression comparison is a total preorder at a fixed context

Design document §3.2: at a fixed context `c` (rule set's level comparison, external mode,
address map, class indices), `compareExpr c` is a lexicographic comparison of finite trees
whose leaves are totally preordered, with non-semantic `mdata` stripped on either side and
semantic-contract `mdata` a node above every other tag. Here that is a theorem
(`compareExpr_total`): on the points `(universe-parameter list, expression)`, the comparison
is oriented and transitive on its ok-domain, under `AddrCongr c.addr?` (the only hypothesis,
see `Ref.lean`).

The proof reads the comparator through its head view:

* `ehd e`: `e` with non-semantic `mdata` stripped (`none` for a metavariable or free
  variable); the comparison of two expressions is that of their heads
  (`compareExpr_strip`), and fails when either head is missing (`compareExpr_bad`);
* `etag`: bvar < sort < const < app < lam < forallE < letE < lit < proj < contract; heads of
  different tags compare by tag, strongly (`compareExpr_diff`);
* heads of one tag compare lexicographically by their parts (the `cE_*` equations), each
  part a total preorder: indices, literals and contract keys by a lawful order, levels by
  `compareLevel_total`, references by `compareRef_total`, subterms by induction on size.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Level Expr)

/-! ## Literals -/

theorem literal_compare_natVal (a b : Nat) :
    compare (Lean.Literal.natVal a) (Lean.Literal.natVal b) = compare a b := by
  show (compare a b).then .eq = _; cases compare a b <;> rfl

theorem literal_compare_strVal (a b : String) :
    compare (Lean.Literal.strVal a) (Lean.Literal.strVal b) = compare a b := by
  show (compare a b).then .eq = _; cases compare a b <;> rfl

def litTag : Lean.Literal → Nat
  | .natVal _ => 0
  | .strVal _ => 1

def litNat : Lean.Literal → Nat
  | .natVal n => n
  | _ => 0

def litStr : Lean.Literal → String
  | .strVal s => s
  | _ => ""

theorem literal_total :
    TotalPre (fun a b : Lean.Literal => (pure ⟨true, compare a b⟩ : Except Unit SOrder)) := by
  refine PreOn.ofTag litTag ?_ ?_
  · intro a b _ _ h
    cases a <;> cases b <;> simp_all [litTag] <;> rfl
  intro T
  match T with
  | 0 =>
    refine (PreOn.pureCmp (compare : Nat → Nat → Ordering) litNat).congr ?_
    intro a b ⟨_, ha⟩ ⟨_, hb⟩
    cases a <;> cases b <;> simp_all [litTag, litNat, literal_compare_natVal]
  | 1 =>
    refine (PreOn.pureCmp (compare : String → String → Ordering) litStr).congr ?_
    intro a b ⟨_, ha⟩ ⟨_, hb⟩
    cases a <;> cases b <;> simp_all [litTag, litStr, literal_compare_strVal]
  | T + 2 =>
    refine PreOn.empty fun a ⟨_, h⟩ => ?_
    cases a <;> simp [litTag] at h

instance transCmp_literal : Std.TransCmp (compare : Lean.Literal → Lean.Literal → Ordering) :=
  transCmp_of_total _ literal_total

/-! ## The head view -/

/-- `e` with non-semantic `mdata` stripped; `none` for a metavariable or free variable. -/
def ehd : Expr → Option Expr
  | .mdata d x h => if SemanticContract.hasMetadata d then some (.mdata d x h) else ehd x
  | .mvar .. | .fvar .. => none
  | e => some e

/-- A head: neither a metavariable, a free variable, nor non-semantic `mdata`. -/
def HN : Expr → Prop
  | .mvar .. | .fvar .. => False
  | .mdata d _ _ => SemanticContract.hasMetadata d = true
  | _ => True

/-- The tag order of the comparator's dispatch. -/
def etag : Expr → Nat
  | .bvar .. => 0
  | .sort .. => 1
  | .const .. => 2
  | .app .. => 3
  | .lam .. => 4
  | .forallE .. => 5
  | .letE .. => 6
  | .lit .. => 7
  | .proj .. => 8
  | .mdata .. => 9
  | .fvar .. | .mvar .. => 10

theorem ehd_spec : ∀ {e h : Expr}, ehd e = some h → HN h ∧ exprSize h ≤ exprSize e
  | .mdata d x hh, h, he => by
    unfold ehd at he
    split at he
    · cases he; exact ⟨by simpa [HN], Nat.le_refl _⟩
    · have := ehd_spec he
      exact ⟨this.1, by simp only [exprSize_mdata]; omega⟩
  | .mvar .., _, he | .fvar .., _, he => by simp [ehd] at he
  | .bvar .., _, he | .sort .., _, he | .const .., _, he | .app .., _, he | .lam .., _, he
  | .forallE .., _, he | .letE .., _, he | .lit .., _, he | .proj .., _, he => by
    simp only [ehd, Option.some.injEq] at he; subst he; exact ⟨trivial, Nat.le_refl _⟩

theorem ehd_of_HN : ∀ {e : Expr}, HN e → ehd e = some e
  | .mdata d x h, he => by simp only [HN] at he; simp [ehd, he]
  | .mvar .., he | .fvar .., he => by simp [HN] at he
  | .bvar .., _ | .sort .., _ | .const .., _ | .app .., _ | .lam .., _
  | .forallE .., _ | .letE .., _ | .lit .., _ | .proj .., _ => rfl

theorem HN_etag_lt : ∀ {e : Expr}, HN e → etag e < 10
  | .mdata .., _ => by simp [etag]
  | .mvar .., he | .fvar .., he => by simp [HN] at he
  | .bvar .., _ | .sort .., _ | .const .., _ | .app .., _ | .lam .., _
  | .forallE .., _ | .letE .., _ | .lit .., _ | .proj .., _ => by simp [etag]

/-! ## Stripping -/

/-- Not a metavariable or free variable at the top. -/
def NotVar : Expr → Prop
  | .mvar .. | .fvar .. => False
  | _ => True

theorem NotVar_of_ehd : ∀ {e h : Expr}, ehd e = some h → NotVar e
  | .mvar .., _, he | .fvar .., _, he => by simp [ehd] at he
  | .mdata .., _, _ | .bvar .., _, _ | .sort .., _, _ | .const .., _, _ | .app .., _, _
  | .lam .., _, _ | .forallE .., _, _ | .letE .., _, _ | .lit .., _, _ | .proj .., _, _ => trivial

theorem cE_mdata_left (c : CmpCtx) (xl yl : List Name) {d x h}
    (hd : SemanticContract.hasMetadata d = false) {y : Expr} (hy : NotVar y) :
    compareExpr c xl yl (.mdata d x h) y = compareExpr c xl yl x y := by
  cases y <;> simp only [NotVar] at hy <;> rw [compareExpr.eq_def] <;> simp [hd]

theorem cE_mdata_right (c : CmpCtx) (xl yl : List Name) {d y h}
    (hd : SemanticContract.hasMetadata d = false) {x : Expr} (hx : HN x) :
    compareExpr c xl yl x (.mdata d y h) = compareExpr c xl yl x y := by
  cases x <;> simp only [HN] at hx <;> rw [compareExpr.eq_def] <;> simp [hd, hx]

/-- The comparison of two expressions is that of their heads. -/
theorem compareExpr_strip_lt (c : CmpCtx) (xl yl : List Name) (n : Nat) :
    ∀ (x y : Expr), exprSize x + exprSize y < n → ∀ {hx hy : Expr}, ehd x = some hx →
      ehd y = some hy → compareExpr c xl yl x y = compareExpr c xl yl hx hy := by
  induction n with
  | zero => intro x y h; omega
  | succ n ih =>
    intro x y hs hx hy ex ey
    by_cases nx : ∃ d x' h, x = .mdata d x' h ∧ SemanticContract.hasMetadata d = false
    · obtain ⟨d, x', h, rfl, hd⟩ := nx
      have ex' : ehd x' = some hx := by simpa [ehd, hd] using ex
      rw [cE_mdata_left c xl yl hd (NotVar_of_ehd ey)]
      exact ih x' y (by simp only [exprSize_mdata] at hs; omega) ex' ey
    · have hxx : ehd x = some x := by
        cases x <;> simp_all [ehd]
      rw [hxx] at ex; cases ex
      have hHN : HN x := (ehd_spec hxx).1
      by_cases ny : ∃ d y' h, y = .mdata d y' h ∧ SemanticContract.hasMetadata d = false
      · obtain ⟨d, y', h, rfl, hd⟩ := ny
        have ey' : ehd y' = some hy := by simpa [ehd, hd] using ey
        rw [cE_mdata_right c xl yl hd hHN]
        exact ih x y' (by simp only [exprSize_mdata] at hs; omega) hxx ey'
      · have hyy : ehd y = some y := by
          cases y <;> simp_all [ehd]
        rw [hyy] at ey; cases ey; rfl

theorem compareExpr_strip (c : CmpCtx) (xl yl : List Name) (x y : Expr) {hx hy : Expr}
    (ex : ehd x = some hx) (ey : ehd y = some hy) :
    compareExpr c xl yl x y = compareExpr c xl yl hx hy :=
  compareExpr_strip_lt c xl yl _ x y (Nat.lt_succ_self _) ex ey

/-- A missing head (a metavariable or free variable under non-semantic `mdata`) fails the
comparison. -/
theorem compareExpr_bad_lt (c : CmpCtx) (xl yl : List Name) (n : Nat) :
    ∀ (x y : Expr), exprSize x + exprSize y < n → (ehd x = none ∨ ehd y = none) →
      ∀ r, compareExpr c xl yl x y ≠ .ok r := by
  induction n with
  | zero => intro x y h; omega
  | succ n ih =>
    intro x y hs h r
    by_cases vx : NotVar x
    · by_cases vy : NotVar y
      · by_cases nx : ∃ d x' hh, x = .mdata d x' hh ∧ SemanticContract.hasMetadata d = false
        · obtain ⟨d, x', hh, rfl, hd⟩ := nx
          rw [cE_mdata_left c xl yl hd vy]
          exact ih x' y (by simp only [exprSize_mdata] at hs; omega)
            (by simpa [ehd, hd] using h) r
        · have hxx : ehd x = some x := by cases x <;> simp_all [ehd, NotVar]
          have hHN : HN x := (ehd_spec hxx).1
          rw [hxx] at h
          simp only [reduceCtorEq, false_or] at h
          by_cases ny : ∃ d y' hh, y = .mdata d y' hh ∧ SemanticContract.hasMetadata d = false
          · obtain ⟨d, y', hh, rfl, hd⟩ := ny
            rw [cE_mdata_right c xl yl hd hHN]
            exact ih x y' (by simp only [exprSize_mdata] at hs; omega)
              (.inr (by simpa [ehd, hd] using h)) r
          · exfalso
            cases y <;> simp_all [ehd, NotVar]
      · cases y <;> simp [NotVar] at vy <;> rw [compareExpr.eq_def] <;>
          cases x <;> simp
    · cases x <;> simp [NotVar] at vx <;> rw [compareExpr.eq_def] <;>
        cases y <;> simp

theorem compareExpr_bad (c : CmpCtx) (xl yl : List Name) (x y : Expr)
    (h : ehd x = none ∨ ehd y = none) (r : SOrder) : compareExpr c xl yl x y ≠ .ok r :=
  compareExpr_bad_lt c xl yl _ x y (Nat.lt_succ_self _) h r

/-- Heads of different tags compare by tag, strongly. -/
theorem compareExpr_diff (c : CmpCtx) (xl yl : List Name) {x y : Expr} (hx : HN x) (hy : HN y)
    (ht : etag x ≠ etag y) :
    compareExpr c xl yl x y = .ok ⟨true, compare (etag x) (etag y)⟩ := by
  cases x <;> cases y <;> simp only [HN, etag] at hx hy ht <;>
    first
      | (exfalso; omega)
      | (rw [compareExpr.eq_def]; simp [hx, hy, pure, Except.pure]; rfl)

/-! ## Heads of one tag -/

section parts

def eBvar : Expr → Nat
  | .bvar i _ => i
  | _ => 0

def eSort : Expr → Level
  | .sort u _ => u
  | _ => default

def eConstName : Expr → Name
  | .const n _ _ | .proj n _ _ _ => n
  | _ => default

def eConstLevels : Expr → List Level
  | .const _ us _ => us.toList
  | _ => []

/-- First part: the function of an application, the type of a binder or `let`, the body of
a projection or `mdata`. -/
def e1 : Expr → Expr
  | .app f _ _ | .lam _ f _ _ _ | .forallE _ f _ _ _ | .letE _ f _ _ _ _ | .proj _ _ f _
  | .mdata _ f _ => f
  | e => e

/-- Second part: the argument of an application, the body of a binder, the value of a
`let`. -/
def e2 : Expr → Expr
  | .app _ a _ | .lam _ _ a _ _ | .forallE _ _ a _ _ | .letE _ _ a _ _ _ => a
  | e => e

/-- Third part: the body of a `let`. -/
def e3 : Expr → Expr
  | .letE _ _ _ b _ _ => b
  | e => e

def eLit : Expr → Lean.Literal
  | .lit l _ => l
  | _ => .natVal 0

def eProjIdx : Expr → Nat
  | .proj _ i _ _ => i
  | _ => 0

def eData : Expr → Array (Name × Ix.DataValue)
  | .mdata d _ _ => d
  | _ => #[]

/-- The contract key of a semantic-contract frame. -/
def eKey (e : Expr) : Nat :=
  match SemanticContract.read (eData e) with
  | .ok k => k.orderKey
  | .error _ => 0

end parts

theorem etag_eq_mdata {x : Expr} (h : etag x = 9) : ∃ d x' hh, x = .mdata d x' hh := by
  cases x <;> simp [etag] at h; exact ⟨_, _, _, rfl⟩

/-- Two semantic-contract frames: both contracts read, then the key, then the body. -/
theorem cE_contract (c : CmpCtx) (xl yl : List Name) {dx x hx dy y hy}
    (h1 : SemanticContract.hasMetadata dx = true) (h2 : SemanticContract.hasMetadata dy = true) :
    compareExpr c xl yl (.mdata dx x hx) (.mdata dy y hy) =
      (do
        let cx ← SemanticContract.read dx
        let cy ← SemanticContract.read dy
        lexIf (pure ⟨true, compare cx.orderKey cy.orderKey⟩) (compareExpr c xl yl x y)) := by
  rw [compareExpr.eq_def]; simp only [h1, h2, ↓reduceIte]; rfl

/-- An expression with its side's universe-parameter list. -/
abbrev EPt := List Name × Expr

/-- `compareExpr` on points. -/
def eC (c : CmpCtx) (a b : EPt) : Except String SOrder := compareExpr c a.1 b.1 a.2 b.2

theorem compareExpr_total (c : CmpCtx) (hc : AddrCongr c.addr?) : TotalPre (eC c) := by
  refine PreOn.ofSize (fun a => exprSize a.2) fun n ih => ?_
  refine PreOn.ofGood (fun a => (ehd a.2).isSome) ?_ ?_
  · rintro ⟨xl, x⟩ ⟨yl, y⟩ - - h r
    apply compareExpr_bad c xl yl x y
    simpa [Option.isSome_iff_ne_none] using h
  -- reduce to heads
  let H : EPt → EPt := fun a => (a.1, (ehd a.2).getD a.2)
  suffices hH : PreOn (fun a : EPt => exprSize a.2 < n + 1 ∧ HN a.2) (eC c) by
    refine (hH.comap H ?_).congr ?_
    · rintro ⟨l, x⟩ ⟨hs, hg⟩
      obtain ⟨hx, ex⟩ := Option.isSome_iff_exists.1 hg
      have hsp := ehd_spec (e := x) (h := hx) ex
      simp only [H, ex, Option.getD_some]
      exact ⟨by simp only at hs; omega, hsp.1⟩
    · rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨-, gx⟩ ⟨-, gy⟩
      obtain ⟨hx, ex⟩ := Option.isSome_iff_exists.1 gx
      obtain ⟨hy, ey⟩ := Option.isSome_iff_exists.1 gy
      simp only [H, eC, ex, ey, Option.getD_some]
      exact (compareExpr_strip c xl yl x y ex ey).symm
  refine PreOn.ofTag (fun a => etag a.2) ?_ ?_
  · rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨-, hx⟩ ⟨-, hy⟩ ht
    exact compareExpr_diff c xl yl hx hy ht
  intro T
  -- the parts of a head of tag `T` are smaller
  have h1 : ∀ a : EPt, (exprSize a.2 < n + 1 ∧ HN a.2) ∧ etag a.2 = T →
      T = 3 ∨ T = 4 ∨ T = 5 ∨ T = 6 ∨ T = 8 ∨ T = 9 → exprSize (e1 a.2) < n := by
    rintro ⟨l, x⟩ ⟨⟨hs, -⟩, ht⟩ hT
    cases x <;> simp_all [etag, e1] <;> omega
  have h2 : ∀ a : EPt, (exprSize a.2 < n + 1 ∧ HN a.2) ∧ etag a.2 = T →
      T = 3 ∨ T = 4 ∨ T = 5 ∨ T = 6 → exprSize (e2 a.2) < n := by
    rintro ⟨l, x⟩ ⟨⟨hs, -⟩, ht⟩ hT
    cases x <;> simp_all [etag, e2] <;> omega
  have h3 : ∀ a : EPt, (exprSize a.2 < n + 1 ∧ HN a.2) ∧ etag a.2 = T →
      T = 6 → exprSize (e3 a.2) < n := by
    rintro ⟨l, x⟩ ⟨⟨hs, -⟩, ht⟩ hT
    cases x <;> simp_all [etag, e3]; omega
  have P1 : ∀ {S' : EPt → Prop}, (∀ a, S' a → exprSize (e1 a.2) < n) →
      PreOn S' (fun a b => eC c (a.1, e1 a.2) (b.1, e1 b.2)) := fun hs => ih.comap _ hs
  have P2 : ∀ {S' : EPt → Prop}, (∀ a, S' a → exprSize (e2 a.2) < n) →
      PreOn S' (fun a b => eC c (a.1, e2 a.2) (b.1, e2 b.2)) := fun hs => ih.comap _ hs
  have P3 : ∀ {S' : EPt → Prop}, (∀ a, S' a → exprSize (e3 a.2) < n) →
      PreOn S' (fun a b => eC c (a.1, e3 a.2) (b.1, e3 b.2)) := fun hs => ih.comap _ hs
  match T with
  | 0 =>
    refine (PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun a : EPt => eBvar a.2)).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp only [etag] at hx hy <;> try omega
    symm; rw [eC, compareExpr.eq_def]; rfl
  | 1 =>
    refine ((compareLevel_total c.levels).comap (fun a : EPt => (a.1, eSort a.2))
      fun _ _ => trivial).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp only [etag] at hx hy <;> try omega
    symm; rw [eC, compareExpr.eq_def]; rfl
  | 2 =>
    refine (((compareLevels_total c.levels).comap (fun a : EPt => (a.1, eConstLevels a.2))
      fun _ _ => trivial).lexIf ((compareRef_total c hc).comap (fun a : EPt => eConstName a.2)
      fun _ _ => trivial)).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp only [etag] at hx hy <;> try omega
    symm; rw [eC, compareExpr.eq_def]; rfl
  | 3 =>
    refine ((P1 fun a h => h1 a h (by omega)).cmpM (P2 fun a h => h2 a h (by omega))).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp only [etag] at hx hy <;> try omega
    symm; rw [eC, compareExpr.eq_def]; rfl
  | 4 =>
    refine ((P1 fun a h => h1 a h (by omega)).cmpM (P2 fun a h => h2 a h (by omega))).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp only [etag] at hx hy <;> try omega
    symm; rw [eC, compareExpr.eq_def]; rfl
  | 5 =>
    refine ((P1 fun a h => h1 a h (by omega)).cmpM (P2 fun a h => h2 a h (by omega))).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp only [etag] at hx hy <;> try omega
    symm; rw [eC, compareExpr.eq_def]; rfl
  | 6 =>
    refine ((P1 fun a h => h1 a h (by omega)).cmpM ((P2 fun a h => h2 a h (by omega)).cmpM
      (P3 fun a h => h3 a h (by omega)))).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp only [etag] at hx hy <;> try omega
    symm; rw [eC, compareExpr.eq_def]; rfl
  | 7 =>
    refine (PreOn.pureCmp (compare : Lean.Literal → Lean.Literal → Ordering)
      (fun a : EPt => eLit a.2)).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp only [etag] at hx hy <;> try omega
    symm; rw [eC, compareExpr.eq_def]; rfl
  | 8 =>
    refine (((compareRef_total c hc).comap (fun a : EPt => eConstName a.2) fun _ _ => trivial).cmpM
      ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun a : EPt => eProjIdx a.2)).cmpM
        (P1 fun a h => h1 a h (by omega)))).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, hx⟩ ⟨_, hy⟩
    cases x <;> cases y <;> simp only [etag] at hx hy <;> try omega
    symm; rw [eC, compareExpr.eq_def]; rfl
  | 9 =>
    -- contract frames: both contracts read, then the key, then the body
    refine PreOn.ofGood (fun a => ∃ k, SemanticContract.read (eData a.2) = .ok k) ?_ ?_
    · rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨⟨_, hhx⟩, hx⟩ ⟨⟨_, hhy⟩, hy⟩ hbad r
      obtain ⟨dx, x', hx', rfl⟩ := etag_eq_mdata hx
      obtain ⟨dy, y', hy', rfl⟩ := etag_eq_mdata hy
      simp only [HN] at hhx hhy
      simp only [eData] at hbad
      simp only [eC]
      rw [cE_contract c xl yl hhx hhy]
      cases hrx : SemanticContract.read dx <;> cases hry : SemanticContract.read dy <;>
        simp_all [bind, Except.bind]
    refine ((PreOn.pureCmp (compare : Nat → Nat → Ordering) (fun a : EPt => eKey a.2)).lexIf
      (P1 fun a h => h1 a h.1 (by omega))).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨⟨⟨_, hhx⟩, hx⟩, kx, rkx⟩ ⟨⟨⟨_, hhy⟩, hy⟩, ky, rky⟩
    obtain ⟨dx, x', hx', rfl⟩ := etag_eq_mdata hx
    obtain ⟨dy, y', hy', rfl⟩ := etag_eq_mdata hy
    simp only [HN] at hhx hhy
    simp only [eData] at rkx rky
    simp only [eC, eKey, eData, e1, rkx, rky]
    rw [cE_contract c xl yl hhx hhy, rkx, rky]
    rfl
  | T + 10 =>
    refine PreOn.empty fun a ⟨⟨_, hn⟩, ht⟩ => ?_
    have := HN_etag_lt hn
    omega

end Ix.CompileCert.Canon
