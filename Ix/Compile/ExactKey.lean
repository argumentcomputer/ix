module
public import Ix.Environment
import all Init.Util

public section

namespace Ix.Compile.ExactKey

/-! Exact cache-key comparison. Stored hashes remain fields of the raw
key; equal hashes alone never justify a successful comparison. -/

deriving instance DecidableEq for Ix.Name
deriving instance DecidableEq for Ix.Level
deriving instance DecidableEq for Ix.Int
deriving instance DecidableEq for Ix.Substring
deriving instance DecidableEq for Ix.SourceInfo
deriving instance DecidableEq for Ix.SyntaxPreresolved

def arrayDec {α : Type} (a b : Array α)
    (compare : ∀ (i : Nat) (hi : i < a.size) (j : Nat) (hj : j < b.size),
      Decidable (a[i]'hi = b[j]'hj)) : Decidable (a = b) := by
  if sizes : a.size = b.size then
    letI (i : Fin a.size) : Decidable (a[i] = b[i.val]'(by omega)) :=
      compare i.val i.isLt i.val (by omega)
    if same : ∀ i : Fin a.size, a[i] = b[i.val]'(by omega) then
      exact .isTrue (Array.ext sizes (fun i hi _ => same ⟨i, hi⟩))
    else
      exact .isFalse (fun equal => same (by subst b; intro i; rfl))
  else exact .isFalse (fun equal => sizes (congrArg Array.size equal))

def syntaxDec (a b : Ix.Syntax) : Decidable (a = b) := by
  cases a <;> cases b
  all_goals try (solve | apply isFalse; intro equal; cases equal)
  case missing.missing => exact .isTrue rfl
  case node.node ai ak aa bi bk ba =>
    letI : Decidable (aa = ba) :=
      arrayDec aa ba (fun i hi j hj => syntaxDec aa[i] ba[j])
    exact decidable_of_iff (ai = bi ∧ ak = bk ∧ aa = ba) (by simp only [Ix.Syntax.node.injEq])
  case atom.atom ai av bi bv =>
    exact decidable_of_iff (ai = bi ∧ av = bv) (by simp only [Ix.Syntax.atom.injEq])
  case ident.ident ai ar av ap bi br bv bp =>
    exact decidable_of_iff (ai = bi ∧ ar = br ∧ av = bv ∧ ap = bp)
      (by simp only [Ix.Syntax.ident.injEq])
termination_by sizeOf a
decreasing_by
  simp_wf
  exact Nat.lt_trans (Array.sizeOf_lt_of_mem (Array.getElem_mem hi)) (by omega)

instance : DecidableEq Ix.Syntax := syntaxDec
deriving instance DecidableEq for Ix.DataValue
deriving instance DecidableEq for Lean.BinderInfo
deriving instance DecidableEq for Lean.Literal
deriving instance DecidableEq for Ix.Expr

@[inline] def rawLevelDec : DecidableEq Ix.Level := inferInstance
@[inline] def rawExprDec : DecidableEq Ix.Expr := inferInstance

@[inline] def ptrDec {α : Type} [DecidableEq α] (a b : α) : Decidable (a = b) :=
  withPtrEqDecEq a b (fun _ => inferInstance)

@[inline] def withAddr {α β : Type} [Subsingleton β] (a : α) (next : USize → β) : β :=
  withPtrAddr a next (fun _ _ => Subsingleton.elim _ _)

structure Entry (α : Type) where
  left : α
  right : α
  leftAddr : USize
  rightAddr : USize
  eq : left = right

abbrev Memo (α : Type) := Std.HashMap Nat (Entry α)

@[inline] def pairKey (a b : USize) : Nat :=
  ((a ^^^ (b * 0x9E3779B97F4A7C15)) &&& 0x3FFFFFFFFFFFFFFF).toNat

@[inline] def probe {α : Type} [DecidableEq α] (memo : Memo α)
    (pa pb : USize) (a b : α) : { hit : Bool // hit = true → a = b } :=
  match memo.get? (pairKey pa pb) with
  | none => ⟨false, fun bad => Bool.noConfusion bad⟩
  | some entry =>
    if entry.leftAddr == pa && entry.rightAddr == pb then
      match ptrDec entry.left a, ptrDec entry.right b with
      | .isTrue left, .isTrue right => ⟨true, fun _ => left ▸ right ▸ entry.eq⟩
      | _, _ => ⟨false, fun bad => Bool.noConfusion bad⟩
    else ⟨false, fun bad => Bool.noConfusion bad⟩

structure Result {α : Type} (a b : α) where
  decision : Decidable (a = b)
  memo : Memo α

abbrev Out {α : Type} (a b : α) := Squash (Result a b)

@[inline] def out {α : Type} {a b : α} (decision : Decidable (a = b)) (memo : Memo α) : Out a b :=
  Squash.mk ⟨decision, memo⟩

/-- Address hints only choose a candidate. Every accepted candidate carries
an equality proof and its retained objects are confirmed by identity. -/
@[inline] def enter {α : Type} [DecidableEq α] (memo : Memo α) (a b : @& α)
    (next : Memo α → Out a b) : Out a b :=
  withAddr a fun pa => withAddr b fun pb =>
    if pa == pb then out (ptrDec a b) memo else
    let hit := probe memo pa pb a b
    if accepted : hit.1 then out (.isTrue (hit.2 accepted)) memo else
    Squash.lift (next memo) fun result =>
      match result.decision with
      | .isTrue same => out (.isTrue same)
          (result.memo.insert (pairKey pa pb) ⟨a, b, pa, pb, same⟩)
      | .isFalse different => out (.isFalse different) result.memo

structure ListResult {α : Type} (a b : List α) where
  decision : Decidable (a = b)
  memo : Memo α

def listGo {α : Type} (a b : List α) (memo : Memo α)
    (compare : ∀ x, x ∈ a → ∀ y, y ∈ b → Memo α → Out x y) : Squash (ListResult a b) :=
  match a, b with
  | [], [] => Squash.mk ⟨.isTrue rfl, memo⟩
  | [], _ :: _ => Squash.mk ⟨.isFalse (by intro same; cases same), memo⟩
  | _ :: _, [] => Squash.mk ⟨.isFalse (by intro same; cases same), memo⟩
  | x :: xs, y :: ys =>
    Squash.lift (compare x (by simp) y (by simp) memo) fun head =>
      match head.decision with
      | .isFalse different =>
        Squash.mk ⟨.isFalse (fun same => different (List.cons.inj same).1), head.memo⟩
      | .isTrue sameHead =>
        Squash.lift (listGo xs ys head.memo (fun x hx y hy next =>
          compare x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) next)) fun tail =>
          Squash.mk ⟨match tail.decision with
            | .isTrue sameTail => .isTrue (by cases sameHead; cases sameTail; rfl)
            | .isFalse different => .isFalse (fun same => different (List.cons.inj same).2), tail.memo⟩

def syntaxGo (memo : Memo Ix.Syntax) (a b : @& Ix.Syntax) : Out a b :=
  match a, b with
  | .node info kind args, .node info' kind' args' =>
    if fields : (info, kind) = (info', kind') then
      Squash.lift (listGo args.toList args'.toList memo (fun x hx y _ next =>
        enter next x y fun next' => syntaxGo next' x y)) fun result =>
          out (match result.decision with
            | .isTrue sameArgs => .isTrue (by
                have equal : args = args' := Array.toList_inj.mp sameArgs
                rcases Prod.mk.inj fields with ⟨rfl, rfl⟩
                cases equal; rfl)
            | .isFalse different => .isFalse (fun same => different (by cases same; rfl))) result.memo
    else out (.isFalse (fun same => fields (by cases same; rfl))) memo
  | a', b' => out (syntaxDec a' b') memo
termination_by sizeOf a
decreasing_by
  have small := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp hx)
  simp_wf
  omega

def syntaxSharedDec (a b : Ix.Syntax) : Decidable (a = b) :=
  Squash.lift (enter {} a b fun memo => syntaxGo memo a b) (fun result => result.decision)

/-- Explicit constructor cases avoid an eagerly evaluated structural
fallback for shared syntax payloads. -/
def dataDec (a b : Ix.DataValue) : Decidable (a = b) := by
  cases a <;> cases b
  all_goals try (solve | apply isFalse; intro same; cases same)
  case ofString.ofString s t =>
    exact decidable_of_iff (s = t) (by simp only [Ix.DataValue.ofString.injEq])
  case ofBool.ofBool s t =>
    exact decidable_of_iff (s = t) (by simp only [Ix.DataValue.ofBool.injEq])
  case ofName.ofName s t =>
    exact decidable_of_iff (s = t) (by simp only [Ix.DataValue.ofName.injEq])
  case ofNat.ofNat s t =>
    exact decidable_of_iff (s = t) (by simp only [Ix.DataValue.ofNat.injEq])
  case ofInt.ofInt s t =>
    exact decidable_of_iff (s = t) (by simp only [Ix.DataValue.ofInt.injEq])
  case ofSyntax.ofSyntax s t =>
    letI : Decidable (s = t) := syntaxSharedDec s t
    exact decidable_of_iff (s = t) (by simp only [Ix.DataValue.ofSyntax.injEq])

def metadataDec (a b : Array (Ix.Name × Ix.DataValue)) : Decidable (a = b) :=
  arrayDec a b (fun i _ j _ =>
    let x := a[i]
    let y := b[j]
    letI : Decidable (x.2 = y.2) := dataDec x.2 y.2
    decidable_of_iff (x.1 = y.1 ∧ x.2 = y.2) (by
      constructor
      · rintro ⟨first, second⟩; exact Prod.ext first second
      · intro same; exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩))

def levelGo (memo : Memo Ix.Level) (a b : @& Ix.Level) : Out a b :=
  match a, b with
  | .succ x ha, .succ y hb =>
    if hashes : ha = hb then
      Squash.lift (enter memo x y fun next => levelGo next x y) fun result =>
        out (match result.decision with
          | .isTrue same => .isTrue (by cases hashes; cases same; rfl)
          | .isFalse different => .isFalse (fun same => different (by cases same; rfl))) result.memo
    else out (.isFalse (fun same => hashes (by cases same; rfl))) memo
  | .max x y ha, .max x' y' hb | .imax x y ha, .imax x' y' hb =>
    if hashes : ha = hb then
      Squash.lift (enter memo x x' fun next => levelGo next x x') fun first =>
        match first.decision with
        | .isFalse different => out (.isFalse (fun same => different (by cases same; rfl))) first.memo
        | .isTrue sameX =>
          Squash.lift (enter first.memo y y' fun next => levelGo next y y') fun second =>
            out (match second.decision with
              | .isTrue sameY => .isTrue (by cases hashes; cases sameX; cases sameY; rfl)
              | .isFalse different => .isFalse (fun same => different (by cases same; rfl))) second.memo
    else out (.isFalse (fun same => hashes (by cases same; rfl))) memo
  | a', b' => out (rawLevelDec a' b') memo
termination_by structural a

def levelDec (a b : Ix.Level) : Decidable (a = b) :=
  Squash.lift (enter {} a b fun memo => levelGo memo a b) (fun result => result.decision)

def levelEqImpl (a b : Ix.Level) : Bool :=
  withPtrEq a b (fun _ =>
    if a.getHash = b.getHash then @decide (a = b) (levelDec a b) else false)
    (fun same => by subst b; simp)

theorem levelEqImpl_eq (a b : Ix.Level) : levelEqImpl a b = decide (a = b) := by
  show (if a.getHash = b.getHash then @decide (a = b) (levelDec a b) else false) = _
  rw [Subsingleton.elim (levelDec a b) (inferInstance : Decidable (a = b))]
  by_cases same : a = b
  · subst b; simp
  · simp [same]

@[expose] def levelEq (a b : Ix.Level) : Bool := decide (a = b)

@[csimp] theorem levelEq_eq_impl : @levelEq = @levelEqImpl := by
  funext a b
  exact (levelEqImpl_eq a b).symm

theorem levelEq_iff (a b : Ix.Level) : levelEq a b = true ↔ a = b := by
  simp [levelEq]

def nameEqImpl (a b : Ix.Name) : Bool :=
  withPtrEq a b (fun _ =>
    if a.getHash = b.getHash then @decide (a = b) (ptrDec a b) else false)
    (fun same => by subst b; simp)

theorem nameEqImpl_eq (a b : Ix.Name) : nameEqImpl a b = decide (a = b) := by
  show (if a.getHash = b.getHash then @decide (a = b) (ptrDec a b) else false) = _
  rw [Subsingleton.elim (ptrDec a b) (inferInstance : Decidable (a = b))]
  by_cases same : a = b
  · subst b; simp
  · simp [same]

@[expose] def nameEq (a b : Ix.Name) : Bool := decide (a = b)

@[csimp] theorem nameEq_eq_impl : @nameEq = @nameEqImpl := by
  funext a b
  exact (nameEqImpl_eq a b).symm

theorem nameEq_iff (a b : Ix.Name) : nameEq a b = true ↔ a = b := by
  simp [nameEq]

/-- Parameter identity before conversion to positional universes. Stored
digests cannot make a different parameter capture the first matching slot. -/
def nameIndex (name : Ix.Name) (params : List Ix.Name) : Option Nat :=
  params.findIdx? (fun param => nameEq param name)

theorem paramsEq_iff (a b : List Ix.Name) : a.isEqv b nameEq = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp
  | cons a as ih =>
    cases b <;> simp [List.isEqv_cons_cons, nameEq_iff, ih]

/-- A positional universe depends on the exact source level and its complete
parameter context. Hashes select buckets but never establish identity. -/
structure UnivKey where
  level : Ix.Level
  params : List Ix.Name
  deriving DecidableEq

instance univKeyBEq : BEq UnivKey :=
  ⟨fun a b => levelEq a.level b.level && a.params.isEqv b.params nameEq⟩
instance univKeyHashable : Hashable UnivKey := ⟨fun key => hash (key.level, key.params)⟩
instance univKeyLawful : LawfulBEq UnivKey where
  eq_of_beq {a b} equal := by
    cases a with
    | mk a as =>
      cases b with
      | mk b bs =>
        change (levelEq a b && as.isEqv bs nameEq) = true at equal
        simpa only [Bool.and_eq_true, levelEq_iff, paramsEq_iff, UnivKey.mk.injEq] using equal
  rfl {a} := by
    change (levelEq a.level a.level && a.params.isEqv a.params nameEq) = true
    simp only [Bool.and_eq_true, levelEq_iff, paramsEq_iff, and_self]

def exprGo (memo : Memo Ix.Expr) (a b : @& Ix.Expr) : Out a b :=
  match a, b with
  | .sort x ha, .sort y hb =>
    letI : Decidable (x = y) := levelDec x y
    out (decidable_of_iff (x = y ∧ ha = hb) (by simp only [Ix.Expr.sort.injEq])) memo
  | .const n us ha, .const m vs hb =>
    letI : Decidable (us = vs) := arrayDec us vs (fun i _ j _ => levelDec us[i] vs[j])
    out (decidable_of_iff (n = m ∧ us = vs ∧ ha = hb) (by simp only [Ix.Expr.const.injEq])) memo
  | .app f x ha, .app g y hb =>
    if hashes : ha = hb then
      Squash.lift (enter memo f g fun next => exprGo next f g) fun first =>
        match first.decision with
        | .isFalse different => out (.isFalse (fun same => different (by cases same; rfl))) first.memo
        | .isTrue sameF =>
          Squash.lift (enter first.memo x y fun next => exprGo next x y) fun second =>
            out (match second.decision with
              | .isTrue sameX => .isTrue (by cases hashes; cases sameF; cases sameX; rfl)
              | .isFalse different => .isFalse (fun same => different (by cases same; rfl))) second.memo
    else out (.isFalse (fun same => hashes (by cases same; rfl))) memo
  | .lam n t body info ha, .lam m u other info' hb
  | .forallE n t body info ha, .forallE m u other info' hb =>
    if fields : (n, info, ha) = (m, info', hb) then
      Squash.lift (enter memo t u fun next => exprGo next t u) fun first =>
        match first.decision with
        | .isFalse different => out (.isFalse (fun same => different (by cases same; rfl))) first.memo
        | .isTrue sameT =>
          Squash.lift (enter first.memo body other fun next => exprGo next body other) fun second =>
            out (match second.decision with
              | .isTrue sameB => .isTrue (by
                  simp only [Prod.mk.injEq] at fields
                  rcases fields with ⟨rfl, rfl, rfl⟩
                  cases sameT; cases sameB; rfl)
              | .isFalse different => .isFalse (fun same => different (by cases same; rfl))) second.memo
    else out (.isFalse (fun same => fields (by cases same; rfl))) memo
  | .letE n t v body nonDep ha, .letE m u w other nonDep' hb =>
    if fields : (n, nonDep, ha) = (m, nonDep', hb) then
      Squash.lift (enter memo t u fun next => exprGo next t u) fun first =>
        match first.decision with
        | .isFalse different => out (.isFalse (fun same => different (by cases same; rfl))) first.memo
        | .isTrue sameT =>
          Squash.lift (enter first.memo v w fun next => exprGo next v w) fun second =>
            match second.decision with
            | .isFalse different => out (.isFalse (fun same => different (by cases same; rfl))) second.memo
            | .isTrue sameV =>
              Squash.lift (enter second.memo body other fun next => exprGo next body other) fun third =>
                out (match third.decision with
                  | .isTrue sameB => .isTrue (by
                      simp only [Prod.mk.injEq] at fields
                      rcases fields with ⟨rfl, rfl, rfl⟩
                      cases sameT; cases sameV; cases sameB; rfl)
                  | .isFalse different => .isFalse (fun same => different (by cases same; rfl))) third.memo
    else out (.isFalse (fun same => fields (by cases same; rfl))) memo
  | .mdata md inner ha, .mdata md' other hb =>
    letI : Decidable (md = md') := metadataDec md md'
    if fields : md = md' ∧ ha = hb then
      Squash.lift (enter memo inner other fun next => exprGo next inner other) fun result =>
        out (match result.decision with
          | .isTrue sameB => .isTrue (by
              rcases fields with ⟨rfl, rfl⟩
              cases sameB; rfl)
          | .isFalse different => .isFalse (fun same => different (by cases same; rfl))) result.memo
    else out (.isFalse (fun same => fields (by cases same; exact ⟨rfl, rfl⟩))) memo
  | .proj n index inner ha, .proj m index' other hb =>
    if fields : (n, index, ha) = (m, index', hb) then
      Squash.lift (enter memo inner other fun next => exprGo next inner other) fun result =>
        out (match result.decision with
          | .isTrue sameB => .isTrue (by
              simp only [Prod.mk.injEq] at fields
              rcases fields with ⟨rfl, rfl, rfl⟩
              cases sameB; rfl)
          | .isFalse different => .isFalse (fun same => different (by cases same; rfl))) result.memo
    else out (.isFalse (fun same => fields (by cases same; rfl))) memo
  | a', b' => out (rawExprDec a' b') memo
termination_by structural a

def exprDec (a b : Ix.Expr) : Decidable (a = b) :=
  Squash.lift (enter {} a b fun memo => exprGo memo a b) (fun result => result.decision)

/-- Pointer identity and the stored digest reject unnecessary comparisons;
successful non-identical candidates are compared as complete raw terms. -/
def exprEqImpl (a b : Ix.Expr) : Bool :=
  withPtrEq a b (fun _ =>
    if a.getHash = b.getHash then @decide (a = b) (exprDec a b) else false)
    (fun same => by subst b; simp)

theorem exprEqImpl_eq (a b : Ix.Expr) : exprEqImpl a b = decide (a = b) := by
  show (if a.getHash = b.getHash then @decide (a = b) (exprDec a b) else false) = _
  rw [Subsingleton.elim (exprDec a b) (inferInstance : Decidable (a = b))]
  by_cases same : a = b
  · subst b; simp
  · simp [same]

/-- Exact raw equality, with its proved DAG implementation used at runtime. -/
@[expose] def exprEq (a b : Ix.Expr) : Bool := decide (a = b)

theorem exprEq_eq (a b : Ix.Expr) : exprEq a b = decide (a = b) := rfl

@[csimp] theorem exprEq_eq_impl : @exprEq = @exprEqImpl := by
  funext a b
  exact (exprEqImpl_eq a b).symm

theorem exprEq_sound {a b : Ix.Expr} (equal : exprEq a b = true) : a = b := by
  rw [exprEq_eq] at equal
  exact of_decide_eq_true equal

/-- An expression-cache key. Hashes index candidates; equality includes
every retained source field, so colliding digests do not identify terms. -/
structure ExprKey where
  expr : Ix.Expr
  deriving DecidableEq

instance : Coe Ix.Expr ExprKey := ⟨ExprKey.mk⟩
instance : BEq ExprKey := ⟨fun a b => exprEq a.expr b.expr⟩
instance : Hashable ExprKey := ⟨fun key => hash key.expr⟩

instance : LawfulBEq ExprKey where
  eq_of_beq {a b} equal := by
    cases a with
    | mk a =>
      cases b with
      | mk b => exact congrArg ExprKey.mk (exprEq_sound equal)
  rfl {a} := by
    change exprEq a.expr a.expr = true
    simp [exprEq]

end Ix.Compile.ExactKey
