import Ix.Ixon.Verify.WorkTags

namespace Ixon.Verify.Work

open Ixon

/-! Expression accounting includes list cells and tuples, array materialization,
and telescope folds, in addition to byte/tag work. Collection readers retain
credit proportional to their actual successful output, never the wire's claimed
count. Failed children retain all earlier work and construct no pending suffix.

Four credits from each complete expression can pay a surrounding table or
telescope step. Sixteen units per consumed byte fund the grammar, including
noncanonical encodings and every error path. These are abstract parser units;
arithmetic bit complexity and runtime allocation behavior are not modeled.
-/

def tagN0Values : Nat → M (List UInt64)
  | 0 => pure []
  | count + 1 => do
    let head ← tagN 0
    let tail ← tagN0Values count
    charged 1 (pure (head.value :: tail))

def appArgs (recur : M Expr) : Nat → Expr → M Expr
  | 0, result => pure result
  | count + 1, result => do
    let arg ← recur
    charged 2 (appArgs recur count (.app result arg))

/-- Ixon's `checkCount` reads the cursor and consumes nothing. -/
def check (count : UInt64) (minBytes : Nat := 1) : M Unit := fun state =>
  (checkCount count minBytes state, 0)

/-- One Ixon binder contract byte. -/
def binderContract : M BinderContract := do
  let bits ← u8
  let some contract := BinderContract.ofBits? bits
    | fail s!"invalid binder contract {bits}"
  pure contract

def lamBinders (recur : M Expr) : Nat → M (List (BinderContract × Expr))
  | 0 => pure []
  | count + 1 => do
    let contract ← binderContract
    let ty ← recur
    let tail ← lamBinders recur count
    charged 2 (pure ((contract, ty) :: tail))

def allBinders (recur : M Expr) : Nat → M (List (BinderContract × ValueContract × Expr))
  | 0 => pure []
  | count + 1 => do
    let bits ← u8
    let some (contract, result) := unpackAllContract? bits
      | fail s!"getExpr: invalid forall contract {bits}"
    let ty ← recur
    let tail ← allBinders recur count
    charged 3 (pure ((contract, result, ty) :: tail))

def exprFromTag (recur : M Expr) (tag : TagN) : M Expr := do
  match tag.flag with
  | 0x0 => charged 1 (pure (.sort tag.value))
  | 0x1 => charged 1 (pure (.var tag.value))
  | 0x2 => do
    let refIdx ← tagN 0
    check tag.value
    let univIdxs ← tagN0Values tag.value.toNat
    charged (2 * univIdxs.length + 1) (pure (.ref refIdx.value univIdxs.toArray))
  | 0x3 => do
    let recIdx ← tagN 0
    check tag.value
    let univIdxs ← tagN0Values tag.value.toNat
    charged (2 * univIdxs.length + 1) (pure (.recur recIdx.value univIdxs.toArray))
  | 0x4 => do
    let typeRefIdx ← tagN 0
    let val ← recur
    charged 1 (pure (.prj typeRefIdx.value tag.value val))
  | 0x5 => charged 1 (pure (.str tag.value))
  | 0x6 => charged 1 (pure (.nat tag.value))
  | 0x7 =>
    if tag.value == 0 then fail "getExpr: empty app spine"
    else do
      check tag.value
      let base ← recur
      match base with
      | .app .. => fail "getExpr: non-canonical app base"
      | _ => appArgs recur tag.value.toNat base
  | 0x8 =>
    if tag.value == 0 then fail "getExpr: Lam with zero binders"
    else do
      check tag.value 2
      let binders ← lamBinders recur tag.value.toNat
      let body ← recur
      match body with
      | .lam .. => fail "getExpr: non-canonical lam telescope"
      | _ =>
        charged (2 * binders.length)
          (pure (binders.foldr (fun (uses, ty) result => .lam uses ty result) body))
  | 0x9 =>
    if tag.value == 0 then fail "getExpr: All with zero binders"
    else do
      check tag.value 2
      let binders ← allBinders recur tag.value.toNat
      let body ← recur
      match body with
      | .all .. => fail "getExpr: non-canonical all telescope"
      | _ =>
        charged (2 * binders.length)
          (pure (binders.foldr (fun (uses, owned, ty) result => .all uses owned ty result) body))
  | 0xA =>
    if tag.value > 3 then fail s!"getExpr: invalid let flags {tag.value}"
    else do
      let binder ← binderContract
      let some contract := LetContract.ofFlags? tag.value binder
        | fail "getExpr: invalid let flags"
      let ty ← recur
      let val ← recur
      let body ← recur
      charged 1 (pure (.letE contract ty val body))
  | 0xB => charged 1 (pure (.share tag.value))
  | f => fail s!"getExpr: invalid flag {f}"

def exprFuel : Nat → M Expr
  | 0 => fail "getExpr: recursion budget exhausted"
  | fuel + 1 => bind (tagN 4) (exprFromTag (exprFuel fuel))

def expr : M Expr := fun state => exprFuel (state.bytes.size - state.idx + 1) state

theorem tagN0Values_erases (count : Nat) : Erases (tagN0Values count) (getTagN0Values count) := by
  induction count with
  | zero => exact pure_erases []
  | succ count ih =>
    unfold tagN0Values getTagN0Values
    exact (tagN_erases 0).bind fun _ => ih.bind fun _ => (pure_erases _).charged 1

theorem appArgs_erases {recur : M Expr} {reader : GetM Expr} (same : Erases recur reader)
    (count : Nat) (base : Expr) : Erases (appArgs recur count base) (getExprAppArgs reader count base) := by
  induction count generalizing base with
  | zero => exact pure_erases base
  | succ count ih =>
    unfold appArgs getExprAppArgs
    exact same.bind fun _ => (ih _).charged 2

theorem check_erases (count : UInt64) (minBytes : Nat) :
    Erases (check count minBytes) (checkCount count minBytes) := rfl

theorem binderContract_erases : Erases binderContract getBinderContract := by
  unfold binderContract getBinderContract
  apply u8_erases.bind
  intro bits
  cases BinderContract.ofBits? bits with
  | none => exact fail_erases _
  | some contract => exact pure_erases _

theorem lamBinders_erases {recur : M Expr} {reader : GetM Expr} (same : Erases recur reader)
    (count : Nat) : Erases (lamBinders recur count) (getExprLamBinders reader count) := by
  induction count with
  | zero => exact pure_erases []
  | succ count ih =>
    unfold lamBinders getExprLamBinders
    exact binderContract_erases.bind fun _ => same.bind fun _ => ih.bind fun _ =>
      (pure_erases _).charged 2

theorem allBinders_erases {recur : M Expr} {reader : GetM Expr} (same : Erases recur reader)
    (count : Nat) : Erases (allBinders recur count) (getExprAllBinders reader count) := by
  induction count with
  | zero => exact pure_erases []
  | succ count ih =>
    unfold allBinders getExprAllBinders
    apply u8_erases.bind
    intro bits
    cases unpackAllContract? bits with
    | none => exact fail_erases _
    | some contracts => exact same.bind fun _ => ih.bind fun _ => (pure_erases _).charged 3

theorem tagN0Values_bound (count : Nat) :
    Bound (tagN0Values count) 16 0 (fun values => 2 * values.length) := by
  induction count with
  | zero => exact pure_bound 16 0 _ [] (Nat.le_refl _)
  | succ count ih =>
    unfold tagN0Values
    apply (tagN_bound 0 16 (by decide)).bind
    intro head
    apply (ih.frame 14).bind
    intro tail
    apply charged_pure_bound
    simp only [List.length_cons]
    omega

theorem appArgs_bound {recur : M Expr} (bound : Bound recur 16 0 (fun _ => 4))
    (count : Nat) (base : Expr) : Bound (appArgs recur count base) 16 0 (fun _ => 0) := by
  induction count generalizing base with
  | zero => exact pure_bound 16 0 _ base (Nat.le_refl _)
  | succ count ih =>
    unfold appArgs
    apply bound.bind
    intro arg
    exact ((ih _).charged 2).weaken (by decide) (fun _ => Nat.le_refl _)

theorem check_bound (count : UInt64) (minBytes rate credit : Nat) :
    Bound (check count minBytes) rate credit (fun _ => credit) := by
  intro start valid
  show Costs start (checkCount count minBytes start) 0 rate credit (fun _ => credit)
  unfold checkCount
  change Costs start ((EStateM.bind EStateM.get _) start) 0 rate credit _
  simp only [EStateM.bind, EStateM.get]
  split
  · exact ⟨Progress.refl start valid, by split <;> simp⟩
  · exact ⟨Progress.refl start valid, by split <;> simp⟩

theorem binderContract_bound : Bound binderContract 16 0 (fun _ => 15) := by
  unfold binderContract
  apply (u8_bound 16 (by decide)).bind
  intro bits
  cases BinderContract.ofBits? bits with
  | none => exact fail_bound _ _ _ _
  | some contract => exact pure_bound _ _ _ _ (Nat.le_refl _)

theorem lamBinders_bound {recur : M Expr} (bound : Bound recur 16 0 (fun _ => 4))
    (count : Nat) : Bound (lamBinders recur count) 16 0 (fun values => 2 * values.length) := by
  induction count with
  | zero => exact pure_bound 16 0 _ [] (Nat.le_refl _)
  | succ count ih =>
    unfold lamBinders
    apply binderContract_bound.bind
    intro contract
    apply (bound.frame 15).bind
    intro ty
    apply (ih.frame 19).bind
    intro tail
    apply charged_pure_bound
    simp only [List.length_cons]
    omega

theorem allBinders_bound {recur : M Expr} (bound : Bound recur 16 0 (fun _ => 4))
    (count : Nat) : Bound (allBinders recur count) 16 0 (fun values => 2 * values.length) := by
  induction count with
  | zero => exact pure_bound 16 0 _ [] (Nat.le_refl _)
  | succ count ih =>
    unfold allBinders
    apply (u8_bound 16 (by decide)).bind
    intro bits
    cases unpackAllContract? bits with
    | none => exact fail_bound _ _ _ _
    | some contracts =>
      apply (bound.frame 15).bind
      intro ty
      apply (ih.frame 19).bind
      intro tail
      apply charged_pure_bound
      simp only [List.length_cons]
      omega

theorem exprFromTag_erases {recur : M Expr} {reader : GetM Expr}
    (same : Erases recur reader) (tag : TagN) :
    Erases (exprFromTag recur tag) (getExprFromTag reader tag) := by
  unfold exprFromTag getExprFromTag
  split <;> simp_all only
  · exact (pure_erases _).charged 1
  · exact (pure_erases _).charged 1
  · exact (tagN_erases 0).bind fun _ => (check_erases _ _).bind fun _ =>
      (tagN0Values_erases _).bind fun _ => (pure_erases _).charged _
  · exact (tagN_erases 0).bind fun _ => (check_erases _ _).bind fun _ =>
      (tagN0Values_erases _).bind fun _ => (pure_erases _).charged _
  · exact (tagN_erases 0).bind fun _ => same.bind fun _ => (pure_erases _).charged 1
  · exact (pure_erases _).charged 1
  · exact (pure_erases _).charged 1
  · split
    · exact fail_erases _
    · apply (check_erases _ _).bind
      intro checked
      apply same.bind
      intro base
      cases base <;> first | exact fail_erases _ | exact appArgs_erases same _ _
  · split
    · exact fail_erases _
    · apply (check_erases _ _).bind
      intro checked
      apply (lamBinders_erases same _).bind
      intro binders
      apply same.bind
      intro body
      cases body <;> first | exact fail_erases _ | exact (pure_erases _).charged _
  · split
    · exact fail_erases _
    · apply (check_erases _ _).bind
      intro checked
      apply (allBinders_erases same _).bind
      intro binders
      apply same.bind
      intro body
      cases body <;> first | exact fail_erases _ | exact (pure_erases _).charged _
  · split
    · exact fail_erases _
    · apply binderContract_erases.bind
      intro binder
      cases LetContract.ofFlags? tag.value binder with
      | none => exact fail_erases _
      | some contract =>
        exact same.bind fun _ => same.bind fun _ => same.bind fun _ => (pure_erases _).charged 1
  · exact (pure_erases _).charged 1
  · exact fail_erases _

theorem exprFuel_erases (fuel : Nat) : Erases (exprFuel fuel) (getExprFuel fuel) := by
  induction fuel with
  | zero => exact fail_erases _
  | succ fuel ih => exact (tagN_erases 4).bind (exprFromTag_erases ih)

theorem expr_erases : Erases expr getExpr := by
  funext state
  exact congrFun (exprFuel_erases _) state

theorem exprFromTag_bound {recur : M Expr} (bound : Bound recur 16 0 (fun _ => 4))
    (tag : TagN) : Bound (exprFromTag recur tag) 16 14 (fun _ => 4) := by
  unfold exprFromTag
  split
  · exact charged_pure_bound _ _ _ _ _ (by decide)
  · exact charged_pure_bound _ _ _ _ _ (by decide)
  · apply ((tagN_bound 0 16 (by decide)).frame 14).bind
    intro refIdx
    apply (check_bound _ _ _ _).bind
    intro checked
    apply ((tagN0Values_bound _).frame 28).bind
    intro univIdxs
    exact charged_pure_bound _ _ _ _ _ (by omega)
  · apply ((tagN_bound 0 16 (by decide)).frame 14).bind
    intro recIdx
    apply (check_bound _ _ _ _).bind
    intro checked
    apply ((tagN0Values_bound _).frame 28).bind
    intro univIdxs
    exact charged_pure_bound _ _ _ _ _ (by omega)
  · apply ((tagN_bound 0 16 (by decide)).frame 14).bind
    intro typeRefIdx
    apply (bound.frame 28).bind
    intro val
    exact charged_pure_bound _ _ _ _ _ (by decide)
  · exact charged_pure_bound _ _ _ _ _ (by decide)
  · exact charged_pure_bound _ _ _ _ _ (by decide)
  · split
    · exact fail_bound _ _ _ _
    · apply (check_bound _ _ _ _).bind
      intro checked
      apply (bound.frame 14).bind
      intro base
      cases base <;> first
      | exact fail_bound _ _ _ _
      | exact ((appArgs_bound bound _ _).frame 18).weaken (by decide) (fun _ => by decide)
  · split
    · exact fail_bound _ _ _ _
    · apply (check_bound _ _ _ _).bind
      intro checked
      apply ((lamBinders_bound bound _).frame 14).bind
      intro binders
      apply (bound.carry (2 * binders.length + 14)).bind
      intro body
      cases body <;> first
      | exact fail_bound _ _ _ _
      | exact charged_pure_bound _ _ _ _ _ (by omega)
  · split
    · exact fail_bound _ _ _ _
    · apply (check_bound _ _ _ _).bind
      intro checked
      apply ((allBinders_bound bound _).frame 14).bind
      intro binders
      apply (bound.carry (2 * binders.length + 14)).bind
      intro body
      cases body <;> first
      | exact fail_bound _ _ _ _
      | exact charged_pure_bound _ _ _ _ _ (by omega)
  · split
    · exact fail_bound _ _ _ _
    · apply (binderContract_bound.frame 14).bind
      intro binder
      cases LetContract.ofFlags? tag.value binder with
      | none => exact fail_bound _ _ _ _
      | some contract =>
        apply ((bound.frame 25).weaken (by decide) (fun _ => Nat.le_refl _)).bind
        intro ty
        apply (bound.frame 29).bind
        intro val
        apply (bound.frame 33).bind
        intro body
        exact charged_pure_bound _ _ _ _ _ (by decide)
  · exact charged_pure_bound _ _ _ _ _ (by decide)
  · exact fail_bound _ _ _ _

theorem exprFuel_bound (fuel : Nat) : Bound (exprFuel fuel) 16 0 (fun _ => 4) := by
  induction fuel with
  | zero => exact fail_bound _ _ _ _
  | succ fuel ih => exact (tagN_bound 4 16 (by decide)).bind (exprFromTag_bound ih)

/-- Includes arbitrary nonzero valid cursors and all malformed/truncated reads.
The production reader executes no accounting state. -/
theorem expr_bound : Bound expr 16 0 (fun _ => 4) := by
  intro state valid
  exact exprFuel_bound _ state valid

end Ixon.Verify.Work
