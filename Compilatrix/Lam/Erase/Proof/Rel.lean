import Compilatrix.Lam.Erase.Proof.Spec
import Compilatrix.Lam.Semantics

/-! # SrcEval and Lam values, related

The relation that erasure's simulation keeps between SrcEval's values,
slots and environments and Lam's (design note 02 §5.2, M2.2). Closures and
partial applications are included, related up to erasure's context map
(`Cx`: which Src variable lives at which Lam binder level, or is □).

* `VR v v'`: `irr` is □; a literal is a literal; a constructor is its kept
  fields under its checked key (every field dropped at every profile holds
  `irr`: *FieldsIrr*, which erasure's local S2 checks establish), the
  unboxed field, or a quotient's element; a closure is a closure whose body
  is an erasure of the Src body, under an environment so related; a partial
  application of a special head is a partially applied wrapper closure
  over related values.
* `SR s s'`: value slots are related values; a thunk is a thunk of an
  erased term; and a value may be *delayed* as a thunk of a variable bound
  to a related value (how `r⋆` receives a strict minor).
* `ER ctx ρ ρ'`: each Src variable mapped to a level holds a slot related to
  the Lam slot at that level; each mapped to □ holds `irr`.
* `Agree ls q`: SrcEval's concrete levels decide every zero condition as the
  profile does (D18).
* `MinorsOk cx ρ`: a variable bound to an `r⋆` minor that is dispatched with
  by-name IHs holds a thunk of a λ-telescope at least as long as the
  dispatch (S25), so by-name arguments only ever meet λ binders. -/

set_option autoImplicit false

namespace Compilatrix.Lam.Erase.Proof

open Compilatrix.Src (CId Head Profile Levels PropWhen Rel RecKind)

/-- Two lists related pointwise. -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

/-! ## Levels and profiles -/

/-- SrcEval's levels agree with a profile: a parameter is zero in one
exactly when it is in the other (a missing entry reads as zero in both). -/
def Agree (ls : Levels) (q : Profile) : Prop := ∀ p, q.getD p true = (ls.getD p 0 == 0)

namespace Agree

variable {ls : Levels} {q : Profile}

theorem holds (h : Agree ls q) (c : PropWhen) : c.holdsP q = c.holds ls := by
  cases c with
  | never => rfl
  | allZero ps =>
    simp only [PropWhen.holdsP, PropWhen.holds]
    congr 1
    funext p
    exact h p

theorem irr (h : Agree ls q) (r : Rel) : r.irrP q = r.irrAt ls := by
  simp only [Rel.irrP, Rel.irrAt]
  exact h.holds _

theorem allowsBeta (h : Agree ls q) (c : PropWhen) : c.allowsBeta ls = !c.holdsP q := by
  simp [PropWhen.allowsBeta, h.holds]

theorem recKind (h : Agree ls q) (k : RecKind) : k.atProfile q = k.atLevels ls := by
  cases k with
  | subsingleton w fs => simp only [RecKind.atProfile, RecKind.atLevels, h.holds]
  | _ => rfl

/-- The empty profile of `n` parameters agrees with the empty levels
(`Src.run` instantiates a root's parameters at zero). -/
theorem root (n : Nat) : Agree [] (Profile.normalize [] n) := by
  intro p
  simp only [Profile.normalize, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_nil, Option.getD_none]
  cases (List.range n)[p]? <;> rfl

private theorem getD_map_univ (us : List Ixon.Univ) (f : Ixon.Univ → Bool) (g : Ixon.Univ → Nat)
    (hfg : ∀ u, f u = (g u == 0)) (p : Nat) :
    (us.map f).getD p true = ((us.map g).getD p 0 == 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases us[p]? with
  | none => simp
  | some u => simp [hfg]

/-- A callee's normalised profile agrees with its instantiated levels, when
the reference has no more universe arguments than parameters. -/
theorem inst (h : Agree ls q) (us : List Ixon.Univ) (n : Nat) (hus : us.length ≤ n) :
    Agree (us.map (Src.evalUniv ls)) ((q.inst us).normalize n) := by
  intro p
  simp only [Profile.normalize, Profile.inst]
  by_cases hp : p < n
  · have e : ((List.range n).map fun i =>
        (us.map fun u => (Src.zeroCond u).holdsP q).getD i true).getD p true =
        (us.map fun u => (Src.zeroCond u).holdsP q).getD p true := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    rw [e]
    refine getD_map_univ us _ _ (fun u => ?_) p
    rw [h.holds, Src.zeroCond_holds]
  · have e : ((List.range n).map fun i =>
        (us.map fun u => (Src.zeroCond u).holdsP q).getD i true).getD p true = true := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    rw [e]
    have : us.length ≤ p := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none this]

end Agree

/-! ## Minors dispatched by name -/

/-- A slot whose value, once forced, is a closure of a λ-telescope of at
least `n` binders: a thunk of such a telescope, or of a variable holding
one (a forwarded minor). -/
inductive TeleSlot : Nat → Src.Slot → Prop
  | lams {n : Nat} {m : Src.Term} {ρ : Src.Env} {ls : Levels} :
      n ≤ m.lamCount → TeleSlot n (.name m ρ ls)
  | fwd {n v : Nat} {ρ : Src.Env} {ls : Levels} {s : Src.Slot} :
      ρ[v]? = some s → TeleSlot n s → TeleSlot n (.name (.var v) ρ ls)

/-- Every variable bound to a minor of an enclosing `r⋆` that is dispatched
with a by-name argument holds a `TeleSlot` of the dispatch's length. -/
def MinorsOk (cx : Cx) (ρ : Src.Env) : Prop :=
  ∀ (v l : Nat) (sig : List Mode), cx.ctx[v]? = some (some l) → cx.minors.lookup l = some sig →
    hasName sig = true →
    ∃ s, ρ[v]? = some s ∧ TeleSlot sig.length s

/-- The levels of `r⋆` minors lie below the Lam depth. -/
def MinorsLt (cx : Cx) : Prop := ∀ e ∈ cx.minors, e.1 < cx.depth

/-- An irrelevant value slot. -/
def IrrSlot (s : Src.Slot) : Prop := ∃ t ρ ls, s = .val (.irr t ρ ls)

/-! ## Values, slots and environments -/

variable (I : Input) (G : Key.GKey → GlobalId → Prop)

mutual

inductive VR : Src.Value → Val → Prop
  | lit {n : Nat} : VR (.lit n) (.lit (.nat n))
  | str {s : String} : VR (.str s) (.lit (.str s))
  | irr {t : Option Src.Term} {ρ : Src.Env} {ls : Levels} : VR (.irr t ρ ls) .box
  | quot {c : CId} {ls : Levels} {ps : List Src.Slot} {a : Src.Value} {v' : Val} {lv : Nat}
      {ty : Src.Term} :
      I.decl? c = some (.quot .ctor lv ty) → VR a v' → VR (.con c ls ps [a]) v'
  | unboxed {c : CId} {ls : Levels} {ps : List Src.Slot} {fs : List Src.Value} {a : Src.Value}
      {v' : Val} {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Src.Term} {j : Nat} :
      I.decl? c = some (.ctor sf lv ind cidx np nf ty) → fs.length = nf →
      I.unbox? ind [] = some j → fs[j]? = some a → VR a v' →
      (∀ i f, fs[i]? = some f → i ≠ j → f.isIrr = true) → VR (.con c ls ps fs) v'
  | con {c : CId} {ls : Levels} {ps : List Src.Slot} {fs : List Src.Value} {fs' : List Val}
      {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Src.Term} :
      I.decl? c = some (.ctor sf lv ind cidx np nf ty) → fs.length = nf →
      I.unbox? ind [] = none → KeptR c 0 fs fs' → VR (.con c ls ps fs) (.con (I.ctorKey c) fs')
  | clo {b : Src.Binder} {d body : Src.Term} {ρ : Src.Env} {ls : Levels} {ρ' : Env}
      {body' : Term} {cx : Cx} :
      ER cx.ctx ρ ρ' → cx.depth = ρ'.length → MinorsOk cx ρ → MinorsLt cx → Agree ls cx.prof →
      TR I G cx.bind body body' → VR (.clo b d body ρ ls) (.clos ρ' body')
  | pap {h : Head} {ls : Levels} {args : List Src.Slot} {q : Profile} {inner : Term}
      {vs : List Val} :
      WrapR I G h q (Term.lams (List.replicate (headArity I h) .strict) inner) → Agree ls q →
      args.length < headArity I h → ValsR args vs →
      VR (.pap h ls args) (.clos (vs.reverse.map .val)
        (Term.lams (List.replicate (headArity I h - 1 - args.length) .strict) inner))

/-- A constructor's fields against its kept fields, from field `i`. -/
inductive KeptR : CId → Nat → List Src.Value → List Val → Prop
  | nil {c : CId} {i : Nat} : KeptR c i [] []
  | kept {c : CId} {i : Nat} {f : Src.Value} {fs : List Src.Value} {f' : Val} {fs' : List Val} :
      I.kept c [] i = true → VR f f' → KeptR c (i + 1) fs fs' → KeptR c i (f :: fs) (f' :: fs')
  | drop {c : CId} {i : Nat} {f : Src.Value} {fs : List Src.Value} {fs' : List Val} :
      I.kept c [] i = false → f.isIrr = true → KeptR c (i + 1) fs fs' → KeptR c i (f :: fs) fs'

/-- A partial application's argument slots: values. -/
inductive ValsR : List Src.Slot → List Val → Prop
  | nil : ValsR [] []
  | cons {v : Src.Value} {v' : Val} {ss : List Src.Slot} {vs : List Val} :
      VR v v' → ValsR ss vs → ValsR (.val v :: ss) (v' :: vs)

inductive SR : Src.Slot → Slot → Prop
  | val {v : Src.Value} {v' : Val} : VR v v' → SR (.val v) (.val v')
  | name {t : Src.Term} {ρ : Src.Env} {ls : Levels} {ρ' : Env} {t' : Term} {cx : Cx} :
      TR I G cx t t' → ER cx.ctx ρ ρ' → cx.depth = ρ'.length → MinorsOk cx ρ → MinorsLt cx →
      Agree ls cx.prof → SR (.name t ρ ls) (.name ρ' t')
  /-- A value delayed as a thunk of a variable (a strict minor passed to `r⋆`). -/
  | delayed {v : Src.Value} {ρ' : Env} {i : Nat} {v' : Val} :
      ρ'[i]? = some (.val v') → VR v v' → SR (.val v) (.name ρ' (.var i))

/-- The Src environment against the whole Lam environment `ρ'`, through the
context map `ctx` (Src index ↦ Lam level, or □). -/
inductive ER : List (Option Nat) → Src.Env → Env → Prop
  | nil {ρ' : Env} : ER [] [] ρ'
  | lvl {l : Nat} {ctx : List (Option Nat)} {s : Src.Slot} {ρ : Src.Env} {s' : Slot}
      {ρ' : Env} :
      l < ρ'.length → ρ'[ρ'.length - 1 - l]? = some s' → SR s s' → ER ctx ρ ρ' →
      ER (some l :: ctx) (s :: ρ) ρ'
  | box {ctx : List (Option Nat)} {s : Src.Slot} {ρ : Src.Env} {ρ' : Env} :
      IrrSlot s → ER ctx ρ ρ' → ER (none :: ctx) (s :: ρ) ρ'

end

/-- The environment relation for a context: its map and its Lam depth. -/
structure EnvR (cx : Cx) (ρ : Src.Env) (ρ' : Env) : Prop where
  er : ER I G cx.ctx ρ ρ'
  depth : cx.depth = ρ'.length
  minors : MinorsOk cx ρ
  minorsLt : MinorsLt cx

end Compilatrix.Lam.Erase.Proof
