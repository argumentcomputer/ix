import Ix.CompileCert.Opt.FreshAbstraction
import Ix.CompileCert.Opt.AuxRuntime

/-!
The actual opening helper is structurally total with its original clauses.
It inserts the replacement without lifting; this remains its contract for
arbitrary raw replacements. The FVar specialization agrees with ordinary
substitution because an FVar has no loose bound variables. Input-derived
freshness then gives an opening/abstraction roundtrip on erased terms, without
a caller freshness or closed-input premise. Full O2/O11a loop and arbitrary
callback conversion obligations remain separate. This leaf is uncompiled.
-/

namespace Ix.CompileCert.Opt.FreshFVarsProof

open Ix (Name Expr)
open Ix.AuxGen (FreshFVars instantiate1At batchAbstractNames)
open Ix.Compile.Canon (keyName)
open Ix.CompileCert.Conv

/-- The helper's exact no-shift opening convention on kernel-relevant terms.
This deliberately differs from `Tm.inst` for a general loose replacement. -/
def openAt (replacement : Tm) : Nat → Tm → Tm
  | depth, .bvar index =>
      if index = depth then replacement
      else .bvar (if depth < index then index - 1 else index)
  | depth, .app f a => .app (openAt replacement depth f) (openAt replacement depth a)
  | depth, .lam ty body =>
      .lam (openAt replacement depth ty) (openAt replacement (depth + 1) body)
  | depth, .pi ty body =>
      .pi (openAt replacement depth ty) (openAt replacement (depth + 1) body)
  | depth, .letE ty value body =>
      .letE (openAt replacement depth ty) (openAt replacement depth value)
        (openAt replacement (depth + 1) body)
  | depth, .proj name index body => .proj name index (openAt replacement depth body)
  | _, .fvar name => .fvar name
  | _, .mvar name => .mvar name
  | _, .sort level => .sort level
  | _, .const name levels => .const name levels
  | _, .lit value => .lit value

/-- Actual executable opening, for every replacement and depth. Cached fields
and metadata are erased, not assumed to have been rebuilt canonically. -/
theorem er_instantiate1At (e replacement : Expr) (depth : Nat) :
    er (instantiate1At e replacement depth) = openAt (er replacement) depth (er e) := by
  induction e generalizing depth with
  | bvar index hash =>
      by_cases same : index = depth
      · simp [instantiate1At, openAt, er, same]
      · by_cases above : depth < index
        · simp [instantiate1At, openAt, er, same, above]
        · simp [instantiate1At, openAt, er, same, above]
  | app f a hash ihf iha =>
      simp only [instantiate1At, er_mkApp, er, openAt, ihf, iha]
  | lam name ty body info hash iht ihb =>
      simp only [instantiate1At, er_mkLam, er, openAt, iht, ihb]
  | forallE name ty body info hash iht ihb =>
      simp only [instantiate1At, er_mkForallE, er, openAt, iht, ihb]
  | letE name ty value body nd hash iht ihv ihb =>
      simp only [instantiate1At, er_mkLetE, er, openAt, iht, ihv, ihb]
  | proj name index body hash ih =>
      simp only [instantiate1At, er_mkProj, er, openAt, ih]
  | mdata data body hash ih =>
      simpa only [instantiate1At, er_mkMData, er] using ih depth
  | _ => rfl

/-- No freshness premise is needed to identify the FVar opening convention. -/
theorem openAt_fvar_eq_inst (name : Name) (t : Tm) (depth : Nat) :
    openAt (.fvar name) depth t = Tm.inst (.fvar name) depth t := by
  induction t generalizing depth with
  | bvar index => simp only [openAt, Tm.inst, Tm.lift]
  | app f a ihf iha => simp only [openAt, Tm.inst, ihf, iha]
  | lam ty body iht ihb => simp only [openAt, Tm.inst, iht, ihb]
  | pi ty body iht ihb => simp only [openAt, Tm.inst, iht, ihb]
  | letE ty value body iht ihv ihb => simp only [openAt, Tm.inst, iht, ihv, ihb]
  | proj owner index body ih => simp only [openAt, Tm.inst, ih]
  | _ => rfl

theorem er_instantiate1At_fvar (e : Expr) (name : Name) (depth : Nat) :
    er (instantiate1At e (Expr.mkFVar name) depth) = Tm.inst (.fvar name) depth (er e) := by
  rw [er_instantiate1At, er_mkFVar]
  exact openAt_fvar_eq_inst name (er e) depth

/-- Structural free-name occurrence on the same erased traversal. -/
def tmOccurs (key : Lean.Name) : Tm → Prop
  | .fvar name => keyName name = key
  | .app f a => tmOccurs key f ∨ tmOccurs key a
  | .lam ty body | .pi ty body => tmOccurs key ty ∨ tmOccurs key body
  | .letE ty value body => (tmOccurs key ty ∨ tmOccurs key value) ∨ tmOccurs key body
  | .proj _ _ body => tmOccurs key body
  | _ => False

theorem tmOccurs_er (key : Lean.Name) (e : Expr) :
    tmOccurs key (er e) ↔ Occurs key e := by
  induction e with
  | app f a hash ihf iha => simp only [er, tmOccurs, Occurs, ihf, iha]
  | lam name ty body info hash iht ihb => simp only [er, tmOccurs, Occurs, iht, ihb]
  | forallE name ty body info hash iht ihb => simp only [er, tmOccurs, Occurs, iht, ihb]
  | letE name ty value body nd hash iht ihv ihb =>
      simp only [er, tmOccurs, Occurs, iht, ihv, ihb]
  | proj name index body hash ih => exact ih
  | mdata data body hash ih => exact ih
  | _ => rfl

/-- Internal roundtrip with its precise freshness condition. The exported
producer corollary below discharges this condition from the actual operands. -/
theorem close_open_fresh (name : Name) (t : Tm) (depth : Nat)
    (fresh : ¬ tmOccurs (keyName name) t) :
    babs (singletonTable name).get? 1 depth (openAt (.fvar name) depth t) = t := by
  induction t generalizing depth with
  | bvar index =>
      by_cases same : index = depth
      · subst index
        simp [openAt, babs, singletonTable_get]
      · by_cases above : depth < index
        · have lower : depth ≤ index - 1 := by omega
          simp only [openAt, same, above, ↓reduceIte, babs, lower]
          congr 1
          omega
        · have below : ¬ depth ≤ index := by omega
          simp only [openAt, same, above, ↓reduceIte, babs, below]
  | fvar query =>
      have different : keyName name ≠ keyName query := by
        intro equal
        exact fresh equal.symm
      simp [openAt, babs, singletonTable_get, different]
  | app f a ihf iha =>
      have ff : ¬ tmOccurs (keyName name) f := fun h => fresh (.inl h)
      have fa : ¬ tmOccurs (keyName name) a := fun h => fresh (.inr h)
      simp only [openAt, babs, ihf depth ff, iha depth fa]
  | lam ty body iht ihb =>
      have ft : ¬ tmOccurs (keyName name) ty := fun h => fresh (.inl h)
      have fb : ¬ tmOccurs (keyName name) body := fun h => fresh (.inr h)
      simp only [openAt, babs, iht depth ft, ihb (depth + 1) fb]
  | pi ty body iht ihb =>
      have ft : ¬ tmOccurs (keyName name) ty := fun h => fresh (.inl h)
      have fb : ¬ tmOccurs (keyName name) body := fun h => fresh (.inr h)
      simp only [openAt, babs, iht depth ft, ihb (depth + 1) fb]
  | letE ty value body iht ihv ihb =>
      have ft : ¬ tmOccurs (keyName name) ty := fun h => fresh (.inl (.inl h))
      have fv : ¬ tmOccurs (keyName name) value := fun h => fresh (.inl (.inr h))
      have fb : ¬ tmOccurs (keyName name) body := fun h => fresh (.inr h)
      simp only [openAt, babs, iht depth ft, ihv depth fv, ihb (depth + 1) fb]
  | proj owner index body ih =>
      exact congrArg (Tm.proj owner index) (ih depth fresh)
  | _ => rfl

theorem close_instantiate1At_fvar_of_fresh (e : Expr) (name : Name) (depth : Nat)
    (fresh : ¬ Occurs (keyName name) e) :
    er (batchAbstractNames (instantiate1At e (Expr.mkFVar name) depth)
      (singletonTable name) 1 depth) = er e := by
  rw [er_batchAbstractNames, er_instantiate1At, er_mkFVar]
  exact close_open_fresh name (er e) depth fun occurs => fresh ((tmOccurs_er _ e).1 occurs)

/-- Actual allocation supplies the only freshness fact used by the roundtrip.
Every raw expression and initial supply are admitted, including open inputs. -/
theorem fresh_open_close (s : FreshFVars) (e : Expr) (pfx : String) (idx depth : Nat) :
    let chosen := ((s.protectExpr e).fresh pfx idx).1.1
    er (batchAbstractNames (instantiate1At e (Expr.mkFVar chosen) depth)
      (singletonTable chosen) 1 depth) = er e := by
  dsimp only
  exact close_instantiate1At_fvar_of_fresh e _ depth (fresh_avoids_expr s e pfx idx)

/-- The public zero-depth entry used by the actual telescope-opening callers. -/
theorem fresh_instantiate1_close (s : FreshFVars) (e : Expr) (pfx : String) (idx : Nat) :
    let chosen := ((s.protectExpr e).fresh pfx idx).1.1
    er (batchAbstractNames (Ix.AuxGen.instantiate1 e (Expr.mkFVar chosen))
      (singletonTable chosen) 1 0) = er e :=
  fresh_open_close s e pfx idx 0

/-- The actual supply returns the FVar of exactly the name it reserves. -/
theorem fresh_pair_expr (s : FreshFVars) (pfx : String) (idx : Nat) :
    (s.fresh pfx idx).1.2 = Expr.mkFVar (s.fresh pfx idx).1.1 := rfl

/-- Roundtrip plus reservation and preservation of the complete prior protected
set, using the actual StateM output pair. No supplied cache/freshness law. -/
theorem freshFVarM_open_close_state (s : FreshFVars) (e : Expr)
    (pfx : String) (idx depth : Nat) :
    let run := Ix.AuxGen.freshFVarM pfx idx (s.protectExpr e)
    er (batchAbstractNames (instantiate1At e run.1.2 depth)
      (singletonTable run.1.1) 1 depth) = er e ∧
      keyName run.1.1 ∈ run.2.used ∧
      ∀ key, key ∈ s.used → key ∈ run.2.used := by
  dsimp only [Ix.AuxGen.freshFVarM]
  refine ⟨?_, fresh_reserved (s.protectExpr e) pfx idx, ?_⟩
  · rw [fresh_pair_expr]
    exact fresh_open_close s e pfx idx depth
  · intro key member
    exact fresh_grows (s.protectExpr e) pfx idx key (protectExpr_grows s e key member)

/-- Raw target replacement retains all its fields and is not silently lifted. -/
theorem opening_target_as_is (replacement : Expr) (depth : Nat) (hash : Address) :
    instantiate1At (.bvar depth hash) replacement depth = replacement := by
  simp only [instantiate1At, beq_self_eq_true, ↓reduceIte]

/-- A raw loose replacement witnesses why the general convention must not be
equated with ordinary substitution by imposing a new closed-input domain. -/
theorem loose_replacement_distinguishes_inst (hash : Address) :
    er (instantiate1At (.bvar 1 hash) (.bvar 0 hash) 1) ≠
      Tm.inst (er (.bvar 0 hash)) 1 (er (.bvar 1 hash)) := by
  rw [opening_target_as_is]
  simp [er, Tm.inst, Tm.lift]

/-- Negative control: abstracting a pre-existing equal name does capture it. -/
theorem unprotected_name_is_captured (name : Name) (hash : Address) :
    er (batchAbstractNames (instantiate1At (.fvar name hash) (Expr.mkFVar name) 0)
      (singletonTable name) 1 0) = .bvar 0 := by
  rw [er_batchAbstractNames, er_instantiate1At]
  simp [er, openAt, babs, singletonTable_get]

/-- The actual allocator avoids that capture even on an arbitrary open raw FVar. -/
theorem protected_fvar_roundtrip (s : FreshFVars) (name : Name) (hash : Address)
    (pfx : String) (idx : Nat) :
    let e := Expr.fvar name hash
    let chosen := ((s.protectExpr e).fresh pfx idx).1.1
    er (batchAbstractNames (instantiate1At e (Expr.mkFVar chosen) 0)
      (singletonTable chosen) 1 0) = .fvar name :=
  fresh_open_close s (.fvar name hash) pfx idx 0

end Ix.CompileCert.Opt.FreshFVarsProof
