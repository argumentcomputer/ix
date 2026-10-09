import Ix.CompileCert.Opt.FreshOpening
import Ix.Compile.Pass.Opt.O11a

/-!
F-1 source/support bridge for the actual no-shift opening helper. Arbitrary
raw bodies, replacements, initial supplies and instance callbacks are retained.
The source-derived protection corollaries support the O2/O11a loop invariant;
they do not assume it at a final caller. O11a's actual non-FVar replacement is
shown to need no bound-variable lifting when its field comes from allocation.
This additive leaf is UNCOMPILED. Full loop/source adapters, conversion,
all-callback totality, Rust correspondence and compiler gates remain open.
-/

namespace Ix.CompileCert.Opt.FreshFVarsProof

open Ix (Name Level Expr)
open Ix.AuxGen (FreshFVars instantiate1At)
open Ix.Compile.Canon (keyName)
open Ix.CompileCert.Conv

/-- Opening has no source of free names other than the original term and its
replacement. This includes arbitrary raw, open replacements. -/
theorem tmOccurs_openAt_source (replacement t : Tm) (depth : Nat) (key : Lean.Name) :
    tmOccurs key (openAt replacement depth t) →
      tmOccurs key t ∨ tmOccurs key replacement := by
  induction t generalizing depth with
  | bvar index =>
      by_cases same : index = depth
      · intro occurs
        exact .inr (by simpa only [openAt, same, ↓reduceIte] using occurs)
      · intro occurs
        exact False.elim (by simpa only [openAt, same, ↓reduceIte, tmOccurs] using occurs)
  | fvar name => exact Or.inl
  | app f a ihf iha =>
      rintro (fromF | fromA)
      · rcases ihf depth fromF with old | added
        · exact .inl (.inl old)
        · exact .inr added
      · rcases iha depth fromA with old | added
        · exact .inl (.inr old)
        · exact .inr added
  | lam ty body iht ihb =>
      rintro (fromTy | fromBody)
      · rcases iht depth fromTy with old | added
        · exact .inl (.inl old)
        · exact .inr added
      · rcases ihb (depth + 1) fromBody with old | added
        · exact .inl (.inr old)
        · exact .inr added
  | pi ty body iht ihb =>
      rintro (fromTy | fromBody)
      · rcases iht depth fromTy with old | added
        · exact .inl (.inl old)
        · exact .inr added
      · rcases ihb (depth + 1) fromBody with old | added
        · exact .inl (.inr old)
        · exact .inr added
  | letE ty value body iht ihv ihb =>
      rintro ((fromTy | fromValue) | fromBody)
      · rcases iht depth fromTy with old | added
        · exact .inl (.inl (.inl old))
        · exact .inr added
      · rcases ihv depth fromValue with old | added
        · exact .inl (.inl (.inr old))
        · exact .inr added
      · rcases ihb (depth + 1) fromBody with old | added
        · exact .inl (.inr old)
        · exact .inr added
  | proj owner index body ih => exact ih depth
  | _ => exact False.elim

/-- The same support law for the actual executable, at every opening depth.
It concerns the FVar-bearing positions of `batchAbstractNames`, not metadata. -/
theorem instantiate1At_occurs_source (e replacement : Expr) (depth : Nat) (key : Lean.Name) :
    Occurs key (instantiate1At e replacement depth) →
      Occurs key e ∨ Occurs key replacement := by
  intro occurs
  have erased := (tmOccurs_er key _).2 occurs
  rw [er_instantiate1At] at erased
  rcases tmOccurs_openAt_source (er replacement) (er e) depth key erased with old | added
  · exact .inl ((tmOccurs_er key e).1 old)
  · exact .inr ((tmOccurs_er key replacement).1 added)

/-- An internal loop invariant, discharged from actual source protection and
allocation below. It is not an additional generator/callback premise. -/
def Protects (s : FreshFVars) (e : Expr) : Prop :=
  ∀ key, Occurs key e → key ∈ s.used

theorem protectExpr_protects (s : FreshFVars) (e : Expr) :
    Protects (s.protectExpr e) e := protectExpr_covers s e

theorem protects_mono (s t : FreshFVars) (e : Expr)
    (grows : ∀ key, key ∈ s.used → key ∈ t.used) (covered : Protects s e) :
    Protects t e := fun key occurs => grows key (covered key occurs)

theorem protects_fvar (s : FreshFVars) (name : Name) (hash : Ix.Address) :
    Protects s (.fvar name hash) ↔ keyName name ∈ s.used := by
  constructor
  · intro covered
    exact covered (keyName name) rfl
  · intro member key occurs
    change keyName name = key at occurs
    exact occurs ▸ member

/-- The local operational invariant is preserved for every replacement whose
support is protected, without any bound-variable or raw-cache restriction. -/
theorem opening_protects (s : FreshFVars) (e replacement : Expr) (depth : Nat)
    (bodyCovered : Protects s e) (replacementCovered : Protects s replacement) :
    Protects s (instantiate1At e replacement depth) := by
  intro key occurs
  rcases instantiate1At_occurs_source e replacement depth key occurs with old | added
  · exact bodyCovered key old
  · exact replacementCovered key added

/-- A fresh allocation preserves the already-established loop invariant and
protects the actual returned FVar; no invariant on the supply is required. -/
theorem fresh_open_protects_of (s : FreshFVars) (e : Expr) (pfx : String) (idx depth : Nat)
    (covered : Protects s e) :
    Protects (s.fresh pfx idx).2 (instantiate1At e (s.fresh pfx idx).1.2 depth) := by
  rw [fresh_pair_expr]
  apply opening_protects
  · exact protects_mono s _ e (fresh_grows s pfx idx) covered
  · intro key occurs
    change keyName (s.fresh pfx idx).1.1 = key at occurs
    exact occurs ▸ fresh_reserved s pfx idx

/-- The initial source protection supplies the invariant internally on every
raw body. This is the protection/opening sequence used by the source peeler. -/
theorem fresh_open_protects (s : FreshFVars) (e : Expr) (pfx : String) (idx depth : Nat) :
    let run := (s.protectExpr e).fresh pfx idx
    Protects run.2 (instantiate1At e run.1.2 depth) :=
  fresh_open_protects_of (s.protectExpr e) e pfx idx depth (protectExpr_protects s e)

/-- A subsequent allocation avoids all original and just-opened free names.
No second protection pass or caller freshness assumption is needed. -/
theorem fresh_open_next_avoids (s : FreshFVars) (e : Expr)
    (pfx qfx : String) (idx jdx depth : Nat) :
    let run := (s.protectExpr e).fresh pfx idx
    ¬ Occurs (keyName (run.2.fresh qfx jdx).1.1) (instantiate1At e run.1.2 depth) := by
  dsimp only
  intro occurs
  exact fresh_not_mem _ qfx jdx (fresh_open_protects s e pfx idx depth _ occurs)

/-- Connect the next actual allocation to the existing erased roundtrip.
Both depths and both name preferences are arbitrary, including collisions. -/
theorem fresh_open_next_roundtrip (s : FreshFVars) (e : Expr)
    (pfx qfx : String) (idx jdx firstDepth nextDepth : Nat) :
    let run := (s.protectExpr e).fresh pfx idx
    let opened := instantiate1At e run.1.2 firstDepth
    let nextName := (run.2.fresh qfx jdx).1.1
    er (Ix.AuxGen.batchAbstractNames (instantiate1At opened (Expr.mkFVar nextName) nextDepth)
      (singletonTable nextName) 1 nextDepth) = er opened := by
  dsimp only
  exact close_instantiate1At_fvar_of_fresh _ _ nextDepth
    (fresh_open_next_avoids s e pfx qfx idx jdx firstDepth)

/-- Internal substitution fact. The following actual-producer corollaries
derive the range condition, rather than requiring closed caller inputs. -/
theorem openAt_eq_inst_of_range_zero (replacement t : Tm) (depth : Nat)
    (rangeZero : Tm.range replacement = 0) :
    openAt replacement depth t = Tm.inst replacement depth t := by
  induction t generalizing depth with
  | bvar index =>
      by_cases same : index = depth
      · simp only [openAt, Tm.inst, same, ↓reduceIte]
        exact (Tm.lift_of_range_le depth 0 replacement (Nat.le_of_eq rangeZero)).symm
      · simp only [openAt, Tm.inst, same, ↓reduceIte]
  | app f a ihf iha => simp only [openAt, Tm.inst, ihf, iha]
  | lam ty body iht ihb => simp only [openAt, Tm.inst, iht, ihb]
  | pi ty body iht ihb => simp only [openAt, Tm.inst, iht, ihb]
  | letE ty value body iht ihv ihb => simp only [openAt, Tm.inst, iht, ihv, ihb]
  | proj owner index body ih => simp only [openAt, Tm.inst, ih]
  | _ => rfl

/-- Exactly the local `sz` expression constructed by O11a.sizeOfMinorWith,
with the instance callback's returned name/level and actual field operand. -/
def sizeOfReplacement (target instName : Name) (level : Level) (field : Expr) : Expr :=
  Ix.Compile.Canon.mkAppN (Expr.mkConst Ix.Compile.Pass.Opt.nSizeOf #[level])
    #[Expr.mkConst target #[], Expr.mkConst instName #[], field]

theorem sizeOfReplacement_eq (target instName : Name) (level : Level) (field : Expr) :
    sizeOfReplacement target instName level field =
      Expr.mkApp (Expr.mkApp (Expr.mkApp
        (Expr.mkConst Ix.Compile.Pass.Opt.nSizeOf #[level])
        (Expr.mkConst target #[])) (Expr.mkConst instName #[])) field := rfl

theorem er_sizeOfReplacement (target instName : Name) (level : Level) (field : Expr) :
    er (sizeOfReplacement target instName level field) =
      .app (.app (.app (.const Ix.Compile.Pass.Opt.nSizeOf #[level])
        (.const target #[])) (.const instName #[])) (er field) := by
  rw [sizeOfReplacement_eq]
  rfl

/-- Its entire free-name support is the field's, regardless of the names or
levels returned by an arbitrary instance callback. -/
theorem sizeOfReplacement_occurs (target instName : Name) (level : Level)
    (field : Expr) (key : Lean.Name) :
    Occurs key (sizeOfReplacement target instName level field) ↔ Occurs key field := by
  rw [sizeOfReplacement_eq]
  change (((False ∨ False) ∨ False) ∨ Occurs key field) ↔ Occurs key field
  simp only [false_or]

/-- The non-FVar replacement produced from any allocated FVar has no loose
bound variables. Its constants, universes and cached field address are arbitrary. -/
theorem sizeOfReplacement_range (target instName fieldName : Name) (level : Level)
    (hash : Ix.Address) :
    Tm.range (er (sizeOfReplacement target instName level (.fvar fieldName hash))) = 0 := by
  rw [er_sizeOfReplacement]
  rfl

/-- Actual O11a replacement opening agrees with substitution on every raw
body and at every depth, without a closed-body or callback validity premise. -/
theorem er_open_sizeOfReplacement (body : Expr) (target instName fieldName : Name)
    (level : Level) (hash : Ix.Address) (depth : Nat) :
    er (instantiate1At body (sizeOfReplacement target instName level (.fvar fieldName hash)) depth) =
      Tm.inst (er (sizeOfReplacement target instName level (.fvar fieldName hash))) depth (er body) := by
  rw [er_instantiate1At]
  exact openAt_eq_inst_of_range_zero _ _ depth
    (sizeOfReplacement_range target instName fieldName level hash)

/-- The replacement generated from the actual fresh output is covered by its
returned supply. No external protection or validity premise is supplied. -/
theorem fresh_sizeOfReplacement_protects (s : FreshFVars) (pfx : String) (idx : Nat)
    (target instName : Name) (level : Level) :
    Protects (s.fresh pfx idx).2
      (sizeOfReplacement target instName level (s.fresh pfx idx).1.2) := by
  intro key occurs
  have fieldOccurs := (sizeOfReplacement_occurs target instName level _ key).1 occurs
  rw [fresh_pair_expr] at fieldOccurs
  change keyName (s.fresh pfx idx).1.1 = key at fieldOccurs
  exact fieldOccurs ▸ fresh_reserved s pfx idx

/-- Whole Except correspondence for the actual callback read and replacement
construction: errors are unchanged, and every successful name/level is admitted.
This is the local O11a branch, not yet the full sizeOfMinorWith loop theorem. -/
theorem sizeOf_callback_opening (inst? : Name → Array Expr → Ix.Compile.Pass.Opt.O11aM (Name × Level))
    (target fieldName : Name) (telescope : Array Expr) (body : Expr)
    (hash : Ix.Address) (depth : Nat) :
    (inst? target telescope).map (fun answer =>
      er (instantiate1At body (sizeOfReplacement target answer.1 answer.2 (.fvar fieldName hash)) depth)) =
    (inst? target telescope).map (fun answer =>
      Tm.inst (er (sizeOfReplacement target answer.1 answer.2 (.fvar fieldName hash))) depth (er body)) := by
  cases inst? target telescope with
  | error error => rfl
  | ok answer =>
      exact congrArg Except.ok
        (er_open_sizeOfReplacement body target answer.1 fieldName answer.2 hash depth)

/-- Boundary control: a fabricated loose field does not justify the producer
corollary. The actual loop must derive its field-FVar invariant internally. -/
theorem loose_sizeOf_field_distinguishes (target instName : Name) (level : Level)
    (bodyHash fieldHash : Ix.Address) :
    er (instantiate1At (.bvar 1 bodyHash)
      (sizeOfReplacement target instName level (.bvar 0 fieldHash)) 1) ≠
    Tm.inst (er (sizeOfReplacement target instName level (.bvar 0 fieldHash))) 1
      (er (.bvar 1 bodyHash)) := by
  rw [opening_target_as_is, er_sizeOfReplacement]
  simp [er, Tm.inst, Tm.lift]

end Ix.CompileCert.Opt.FreshFVarsProof
