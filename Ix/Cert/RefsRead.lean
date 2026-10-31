import Ix.Cert.Compile
import IxC.Ixon.Verify.BoundedConstant

/-! # The refs-only reader reads what the bounded decoder reads

The reference check (`Ix.Cert.referenceCycle`) reads each stored record's
`refs` table and projection block with `Ix.Cert.RecordRefs.getRefs`, which
walks the record by `Ixon.Bounded.getConstant`'s grammar without keeping its
expressions or universes. This file proves that the two agree: each `skip…`
reader is its `Ixon.get…` reader with the value forgotten (`skipExpr_eq`,
`skipUniv_eq`, `skipInfo_eq`, …), as an equation of `Ixon.GetM` programs, so
they succeed and fail together, at the same position. Hence:

* `getRefs_eq`: `getRefs` is the bounded decoder followed by the record's `refs`
  and projection block;
* `lazyRefs_eq`: a stored record's references and owner, read without its
  expressions, are those of the decoded record (`LazyConstant.get?`);
* `storedRefs_eq`: the check's `storedRefs` is the decoded record's
  (`storedRecord`) references and owner. -/

namespace Ix.Cert.RefsRead

open Ixon Ix.Cert.RecordRefs

theorem map_throw {α β : Type} (f : α → β) (e : String) :
    f <$> (throw e : GetM α) = throw e := rfl

theorem throw_bind {α β : Type} (e : String) (g : α → GetM β) :
    (throw e : GetM α) >>= g = throw e := rfl

/-! ## Expressions -/

theorem skipTagN0Values_eq (n : Nat) :
    skipTagN0Values n = (fun _ => ()) <$> getTagN0Values n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [skipTagN0Values, getTagN0Values, ih, map_bind, bind_pure_comp, Functor.map_map]

theorem skipAppArgs_eq (recur : GetM Ixon.Expr) (n : Nat) (base : Ixon.Expr) :
    skipAppArgs (head <$> recur) n (head base) = head <$> getExprAppArgs recur n base := by
  induction n generalizing base with
  | zero => simp only [skipAppArgs, getExprAppArgs, map_pure]
  | succ n ih =>
    simp only [skipAppArgs, getExprAppArgs, map_bind, bind_map_left]
    congr 1
    funext arg
    exact ih (.app base arg)

theorem skipLamBinders_eq (recur : GetM Ixon.Expr) (n : Nat) :
    skipLamBinders (head <$> recur) n = List.isEmpty <$> getExprLamBinders recur n := by
  induction n with
  | zero => simp only [skipLamBinders, getExprLamBinders, map_pure, List.isEmpty_nil]
  | succ n ih =>
    simp only [skipLamBinders, getExprLamBinders, ih, map_bind, bind_map_left, map_pure,
      List.isEmpty_cons]

theorem skipAllBinders_eq (recur : GetM Ixon.Expr) (n : Nat) :
    skipAllBinders (head <$> recur) n = List.isEmpty <$> getExprAllBinders recur n := by
  induction n with
  | zero => simp only [skipAllBinders, getExprAllBinders, map_pure, List.isEmpty_nil]
  | succ n ih =>
    simp only [skipAllBinders, getExprAllBinders, map_bind]
    congr 1
    funext bits
    cases unpackAllContract? bits with
    | none => rfl
    | some cr =>
      obtain ⟨c, r⟩ := cr
      simp only [ih, map_bind, bind_map_left, map_pure, List.isEmpty_cons]

theorem head_foldr_lam (bs : List (BinderContract × Ixon.Expr)) (body : Ixon.Expr) :
    head (bs.foldr (fun (uses, ty) result => .lam uses ty result) body) =
      if bs.isEmpty then head body else .lam := by
  cases bs <;> rfl

theorem head_foldr_all (bs : List (BinderContract × ValueContract × Ixon.Expr)) (body : Ixon.Expr) :
    head (bs.foldr (fun (uses, owned, ty) result => .all uses owned ty result) body) =
      if bs.isEmpty then head body else .all := by
  cases bs <;> rfl

theorem skipExprFromTag_eq (recur : GetM Ixon.Expr) (tag : TagN) :
    skipExprFromTag (head <$> recur) tag = head <$> getExprFromTag recur tag := by
  unfold skipExprFromTag getExprFromTag
  split
  next h => simp only [h, map_pure, head]
  next h => simp only [h, map_pure, head]
  next h =>
    simp only [h, map_bind, bind_pure_comp, Functor.map_map,
      skipTagN0Values_eq, head]
  next h =>
    simp only [h, map_bind, bind_pure_comp, Functor.map_map,
      skipTagN0Values_eq, head]
  next h =>
    simp only [h, map_bind, bind_pure_comp, Functor.map_map, head]
  next h => simp only [h, map_pure, head]
  next h => simp only [h, map_pure, head]
  next h =>
    simp only [h]
    split
    · rfl
    · simp only [map_bind, bind_map_left]
      congr 1; funext _; congr 1; funext base
      cases base <;> simp only [head, map_throw, throw_bind] <;> rw [← skipAppArgs_eq] <;> rfl
  next h =>
    simp only [h]
    split
    · rfl
    · simp only [map_bind, bind_map_left, skipLamBinders_eq]
      congr 1; funext _; congr 1; funext bs; congr 1; funext body
      cases body <;> simp only [head_foldr_lam, map_pure, map_throw, throw_bind] <;> simp only [head]
  next h =>
    simp only [h]
    split
    · rfl
    · simp only [map_bind, bind_map_left, skipAllBinders_eq]
      congr 1; funext _; congr 1; funext bs; congr 1; funext body
      cases body <;> simp only [head_foldr_all, map_pure, map_throw, throw_bind] <;> simp only [head]
  next h =>
    simp only [h]
    split
    · rfl
    · simp only [map_bind]
      congr 1; funext binder
      cases LetContract.ofFlags? _ binder with
      | none => rfl
      | some _ => simp only [map_bind, bind_map_left, bind_pure_comp, Functor.map_map,
          head]
  next h => simp only [h, map_pure, head]
  next =>
    split <;> first | rfl | (exfalso; simp_all)

theorem skipExprFuel_eq (n : Nat) : skipExprFuel n = head <$> getExprFuel n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [skipExprFuel, getExprFuel, map_bind, ih]
    congr 1; funext tag; exact skipExprFromTag_eq _ tag

/-- **`skipExpr` is `getExpr` with the expression forgotten.** -/
theorem skipExpr_eq : skipExpr = (fun _ => ()) <$> getExpr := by
  simp only [skipExpr, getExpr, map_bind, skipExprFuel_eq, bind_pure_comp,
    Functor.map_map]

/-! ## Universes -/

theorem skipUnivFromTag_eq (recur : Nat → GetM (Univ × Nat)) (budget : Nat) (tag : TagN) :
    skipUnivFromTag (fun n => Prod.snd <$> recur n) budget tag =
      Prod.snd <$> Bounded.getUnivFromTag recur budget tag := by
  unfold skipUnivFromTag Bounded.getUnivFromTag
  dsimp only
  by_cases fits : Bounded.univTagCharge tag ≤ budget
  · simp only [fits, ↓reduceIte]
    split
    next h =>
      simp only [h]
      split
      next => simp only [map_pure]
      next => simp only [bind_pure_comp, Functor.map_map]
    next h => simp only [h, map_bind, bind_map_left, bind_pure_comp, Functor.map_map]
    next h => simp only [h, map_bind, bind_map_left, bind_pure_comp, Functor.map_map]
    next h => simp only [h, map_pure]
    next => split <;> first | rfl | (exfalso; simp_all)
  · simp only [fits, ↓reduceIte, map_throw]

theorem skipUnivFuel_eq (n budget : Nat) :
    skipUnivFuel n budget = Prod.snd <$> Bounded.getUnivFuel n budget := by
  induction n generalizing budget with
  | zero => rfl
  | succ n ih =>
    have same : skipUnivFuel n = fun budget => Prod.snd <$> Bounded.getUnivFuel n budget :=
      funext ih
    simp only [skipUnivFuel, Bounded.getUnivFuel, map_bind, same]
    congr 1; funext tag; exact skipUnivFromTag_eq _ budget tag

/-- The skipping decoder keeps exactly the bounded reader's unspent budget. -/
theorem skipUniv_eq (budget : Nat) : skipUniv budget = Prod.snd <$> Bounded.getUniv budget := by
  simp only [skipUniv, Bounded.getUniv, map_bind, skipUnivFuel_eq]

theorem skipUnivArray_eq (count budget : Nat) (acc : Array Univ) :
    skipUnivArray count budget = Prod.snd <$> Bounded.getUnivArrayLoop count budget acc := by
  induction count generalizing budget acc with
  | zero => rfl
  | succ count ih =>
    simp only [skipUnivArray, Bounded.getUnivArrayLoop, skipUniv_eq, map_bind, bind_map_left]
    congr 1
    funext value
    exact ih value.2 (acc.push value.1)

/-! ## Tables and loops -/

/-- A pushing loop over a list, its value forgotten, is `skipMany`. -/
theorem forIn_push_eq {α : Type} (m : GetM α) (l : List Nat) (init : Array α) :
    (fun _ => ()) <$> forIn l init (fun _ r => (fun x => ForInStep.yield (r.push x)) <$> m) =
      skipMany ((fun _ => ()) <$> m) l.length := by
  induction l generalizing init with
  | nil => simp only [List.forIn_nil, map_pure, List.length_nil, skipMany]
  | cons a l ih =>
    simp only [List.forIn_cons, bind_map_left, List.length_cons, skipMany, map_bind, ih]

/-- `skipMany` is `Ixon.getArray` with the values forgotten. -/
theorem skipMany_eq {α : Type} (m : GetM α) (n : Nat) :
    skipMany ((fun _ => ()) <$> m) n = (fun _ => ()) <$> getArray m n := by
  unfold getArray
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', map_bind, bind_pure_comp]
  simp only [map_pure, bind_pure_comp, forIn_push_eq, List.length_range']
  simp [Std.Legacy.Range.size]

theorem range_size (n : Nat) : [:n].size = n := by simp [Std.Legacy.Range.size]

/-! ## Constant payloads -/

theorem skipDefinition_eq : skipDefinition = (fun _ => ()) <$> getDefinition := by
  unfold skipDefinition getDefinition
  simp only [skipExpr_eq, map_bind, bind_map_left, bind_pure_comp]
  congr 1; funext flags
  split <;> simp only [map_throw, throw_bind, map_bind,
    Functor.map_map]

theorem skipRecursorRule_eq : skipRecursorRule = (fun _ => ()) <$> getRecursorRule := by
  unfold skipRecursorRule getRecursorRule
  simp only [skipExpr_eq, map_bind, bind_pure_comp, Functor.map_map]

theorem skipRecursor_eq : skipRecursor = (fun _ => ()) <$> getRecursor := by
  unfold skipRecursor getRecursor
  simp only [skipExpr_eq, skipRecursorRule_eq, map_bind, bind_map_left, bind_pure_comp]
  congr 1; funext flags
  split <;> simp only [map_throw, throw_bind, map_bind,
    Functor.map_map, skipMany_eq,
    Std.Legacy.Range.forIn_eq_forIn_range', forIn_push_eq, List.length_range', range_size]

theorem skipAxiom_eq : skipAxiom = (fun _ => ()) <$> getAxiom := by
  unfold skipAxiom getAxiom
  simp only [skipExpr_eq, map_bind, bind_pure_comp, Functor.map_map]

theorem skipQuotient_eq : skipQuotient = (fun _ => ()) <$> getQuotient := by
  unfold skipQuotient getQuotient
  simp only [skipExpr_eq, map_bind, bind_pure_comp]
  congr 1; funext v
  split <;> simp only [map_throw, throw_bind, map_bind,
    Functor.map_map, pure_bind]

theorem skipConstructor_eq : skipConstructor = (fun _ => ()) <$> getConstructor := by
  unfold skipConstructor getConstructor
  simp only [skipExpr_eq, map_bind, bind_pure_comp, Functor.map_map]

theorem skipInductive_eq : skipInductive = (fun _ => ()) <$> getInductive := by
  unfold skipInductive getInductive
  simp only [skipExpr_eq, skipConstructor_eq, map_bind, bind_map_left, bind_pure_comp,
    Functor.map_map, skipMany_eq,
    Std.Legacy.Range.forIn_eq_forIn_range', forIn_push_eq, List.length_range', range_size]

theorem skipMutConst_eq : skipMutConst = (fun _ => ()) <$> getMutConst := by
  unfold skipMutConst getMutConst
  simp only [map_bind]
  congr 1; funext t
  split <;> simp only [skipDefinition_eq, skipInductive_eq, skipRecursor_eq, map_throw,
    Functor.map_map]

/-! ## Records -/

/-- A projection's block (`Ix.Cert.refOwner`'s case split), else `none`. -/
def infoBlock : Ixon.ConstantInfo → Option Address
  | .cPrj p => some p.block
  | .rPrj p => some p.block
  | .iPrj p => some p.block
  | .dPrj p => some p.block
  | _ => none

theorem refOwner_eq_infoBlock (a : Address) (c : Ixon.Constant) :
    refOwner a c = (infoBlock c.info).getD a := by
  unfold refOwner infoBlock
  cases c.info <;> rfl

/-- **`skipInfo` is `getConstantInfo`, keeping a projection's block.** -/
theorem skipInfo_eq : skipInfo = infoBlock <$> getConstantInfo := by
  unfold skipInfo getConstantInfo
  simp only [map_bind]
  congr 1; funext tag
  split
  next =>
    have h := forIn_push_eq getMutConst (List.range' 0 [:tag.value.toNat].size) #[]
    simp only [List.length_range', range_size] at h
    simp only [skipMutConst_eq, bind_pure_comp, Std.Legacy.Range.forIn_eq_forIn_range',
      Functor.map_map, range_size, ← h, infoBlock]
  next =>
    split
    next =>
      split <;> simp only [skipDefinition_eq, skipRecursor_eq, skipAxiom_eq, skipQuotient_eq,
        bind_pure_comp, Functor.map_map, map_throw]
      all_goals rename_i h; simp only [h, Functor.map_map, infoBlock]
    next => rfl

/-- **`getRefs` is the bounded decoder followed by the record's `refs` and
projection block.** -/
theorem getRefs_eq (budget : Nat) :
    getRefs budget = (fun c => (c.refs, infoBlock c.info)) <$> Bounded.getConstant budget := by
  unfold getRefs Bounded.getConstant getConstantWithUnivs Bounded.getUnivArray
  simp only [skipInfo_eq, skipExpr_eq, skipUnivArray_eq _ _ #[], skipMany_eq, map_bind, bind_map_left,
    bind_pure_comp, Functor.map_map]

theorem refsAt_eq (buf : ByteArray) (off len : Nat) (budget : Nat := loadMaxUnivNodes) :
    refsAt buf off len budget =
      (deConstantAt buf off len budget).toOption.map fun c => (c.refs, infoBlock c.info) := by
  unfold refsAt deConstantAt
  split
  · rw [getRefs_eq]
    simp only [Functor.map, EStateM.map, EStateM.run]
    cases Bounded.getConstant budget { idx := off, bytes := buf } with
    | ok a s => by_cases h : s.idx = off + len <;> simp [h, Except.toOption]
    | error e s => rfl
  · rfl

/-- **A stored record's references and owner, read without its expressions,
are those of the decoded record.** -/
theorem lazyRefs_eq (a : Address) (lc : Ixon.LazyConstant) :
    lazyRefs a lc = lc.get?.map fun c => (c.refs, refOwner a c) := by
  unfold lazyRefs Ixon.LazyConstant.get?
  cases lc.cache with
  | some c => rfl
  | none =>
    simp only [refsAt_eq]
    cases Ixon.deConstantAt lc.buf lc.off lc.len <;> simp [Except.toOption, refOwner_eq_infoBlock]

/-- **The check's `storedRefs` is the decoded record's references and owner.** -/
theorem storedRefs_eq (ixe : Ixon.Env) (a : Address) :
    storedRefs ixe a = (storedRecord ixe a).map fun c => (c.refs, refOwner a c) := by
  unfold storedRefs storedRecord
  cases ixe.consts.get? a <;> simp [lazyRefs_eq]

end Ix.Cert.RefsRead
