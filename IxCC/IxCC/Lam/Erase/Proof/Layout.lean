import IxCC.Lam.Erase.Proof.Spec
import IxCC.Src.Proof.Unfold

/-! # Erasure's input against SrcEval

Facts relating erasure's reading of a program (`Erase.Input`) to SrcEval's:
the input reads the program's own maps; constructor layouts do not
depend on the universe profile (one layout per constructor); special
heads have the arities SrcEval gives them; δ and special heads are what
`evalConst` evaluates. Also `ProgWF`, the structural well-formedness of the
Src program the simulation assumes (ingress guarantees it; erasure decides
it, `progWF_iff`). -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)
open IxCC.Src.Relevance (FieldClass Checked)
open IxCC.Sem (Result later)

/-! ## The input reads the program -/

section Input

variable (p : Src.Program) (ch : Checked)

@[simp] theorem input_decl (c : CId) : (Input.ofProgram p ch).decl? c = p.decl? c := rfl
@[simp] theorem input_resolve (c : CId) :
    (Input.ofProgram p ch).resolve.get? c = p.table.resolveOf c := rfl
@[simp] theorem input_recKind (c : CId) :
    (Input.ofProgram p ch).recKind.get? c = p.table.recKindOf c := rfl
@[simp] theorem input_known : (Input.ofProgram p ch).known = p.known := rfl
@[simp] theorem input_opaque (c : CId) :
    (Input.ofProgram p ch).isOpaqueByValue c = p.table.isOpaqueByValue c := rfl

theorem headArity_eq (h : Head) : headArity (Input.ofProgram p ch) h = p.headArity h := by
  cases h with
  | ctor c =>
    simp only [headArity, Src.Program.headArity, input_decl]
    cases p.decl? c with
    | none => rfl
    | some d => cases d <;> rfl
  | quotMk _ => rfl
  | quotLift _ => rfl
  | recr r =>
    simp only [headArity, Src.Program.headArity, input_decl]
    cases p.decl? r with
    | none => rfl
    | some d => cases d <;> rfl
  | cases c =>
    simp only [headArity, Src.Program.headArity, input_decl, input_resolve]
    cases p.table.resolveOf c with
    | none => rfl
    | some res =>
      cases res with
      | case r =>
        dsimp only
        cases p.decl? r with
        | none => rfl
        | some d => cases d <;> rfl
      | _ => rfl
  | prim _ => rfl
  | word _ _ => rfl

theorem evalConst_delta {c : CId} {b : Src.Term} (hb : (Input.ofProgram p ch).deltaBody c = some b)
    (k : Nat) (ls : Levels) :
    Src.evalConst p k ls c = later k fun k => Src.eval p k ls [] b := by
  rw [Src.evalConst_eq]
  simp only [Input.deltaBody, input_resolve, input_decl, input_opaque] at hb
  cases hr : p.table.resolveOf c with
  | some res =>
    rw [hr] at hb
    cases res with
    | csimp g vs _ => simp only [Option.some.injEq] at hb; subst hb; rfl
    | eqn _ body => simp only [Option.some.injEq] at hb; subst hb; rfl
    | prim _ => simp at hb
    | case _ => simp at hb
    | word _ _ _ => simp at hb
  | none =>
    rw [hr] at hb
    dsimp only at hb ⊢
    cases hd : p.decl? c with
    | none => rw [hd] at hb; simp at hb
    | some d =>
      rw [hd] at hb
      cases d with
      | defn kind safety _ _ v =>
        cases kind <;> cases safety <;> simp at hb
        · subst hb; rfl
        · by_cases ho : p.table.isOpaqueByValue c = true
          · simp only [ho, ite_true, Option.some.injEq] at hb; subst hb; simp [ho]
          · simp [ho] at hb
      | _ => simp at hb

theorem evalConst_head {c : CId} {h : Head} (hh : (Input.ofProgram p ch).headOf c = some h)
    (k : Nat) (ls : Levels) : Src.evalConst p k ls c = Src.headValue p k ls h := by
  rw [Src.evalConst_eq]
  simp only [Input.headOf, input_resolve, input_decl] at hh
  cases hr : p.table.resolveOf c with
  | some res =>
    rw [hr] at hh
    cases res with
    | prim op => simp only [Option.some.injEq] at hh; subst hh; rfl
    | case _ => simp only [Option.some.injEq] at hh; subst hh; rfl
    | csimp _ _ _ => simp at hh
    | eqn _ _ => simp at hh
    | word _ _ _ => simp at hh
  | none =>
    rw [hr] at hh
    dsimp only at hh ⊢
    cases hd : p.decl? c with
    | none => rw [hd] at hh; simp at hh
    | some d =>
      rw [hd] at hh
      cases d with
      | ctor => simp only [Option.some.injEq] at hh; subst hh; rfl
      | recr => simp only [Option.some.injEq] at hh; subst hh; rfl
      | quot kind _ _ =>
        cases kind <;> simp at hh <;> (subst hh; rfl)
      | _ => simp at hh

end Input

/-! ## One layout per constructor -/

theorem layout_dropP (cls : FieldClass) (q : Profile) :
    (Input.layoutClass cls).dropP q = (Input.layoutClass cls).dropP [] := by
  cases cls with
  | keep => rfl
  | type => rfl
  | proof w =>
    cases w with
    | never => rfl
    | allZero ps =>
      cases ps with
      | nil => rfl
      | cons _ _ => rfl

end IxCC.Lam.Erase.Proof

namespace IxCC.Lam.Erase.Input

open IxCC.Src (CId Profile)
open IxCC.Lam.Erase.Proof (layout_dropP)

variable (I : Input)

theorem kept_prof (c : CId) (q : Profile) (i : Nat) : I.kept c q i = I.kept c [] i := by
  simp only [kept, fields?]
  cases I.ctors.get? c with
  | none => rfl
  | some r =>
    simp only [Option.map_some]
    cases h : (r.fields.map layoutClass)[i]? with
    | none => rfl
    | some cls =>
      simp only [List.getElem?_map] at h
      cases h' : r.fields[i]? with
      | none => rw [h'] at h; simp at h
      | some cls₀ =>
        rw [h'] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp [layout_dropP]

theorem kept_fun (c : CId) (q : Profile) : I.kept c q = I.kept c [] :=
  funext (kept_prof I c q)

theorem rank_prof (c : CId) (q : Profile) (i : Nat) : I.rank c q i = I.rank c [] i := by
  simp only [rank, kept_fun]

theorem keptCount_prof (c : CId) (q : Profile) (n : Nat) :
    I.keptCount c q n = I.keptCount c [] n := by
  simp only [keptCount, rank_prof]

theorem unbox?_prof (t : CId) (q : Profile) : I.unbox? t q = I.unbox? t [] := by
  unfold unbox?
  cases I.decl? t with
  | none => rfl
  | some d =>
    cases d with
    | induct _ _ np _ ty _ =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      split
      · next k _ =>
        cases hf : I.fields? k with
        | none => rfl
        | some fields =>
          have hk : (fields.zipIdx.filter fun x => match x with | (c, _) => !c.dropP q) =
              (fields.zipIdx.filter fun x => match x with | (c, _) => !c.dropP []) := by
            apply List.filter_congr
            intro x hx
            obtain ⟨cls, i⟩ := x
            have : cls ∈ fields := List.fst_mem_of_mem_zipIdx hx
            simp only [fields?, Option.map_eq_some_iff] at hf
            obtain ⟨r, _, rfl⟩ := hf
            obtain ⟨cls₀, _, rfl⟩ := List.mem_map.1 this
            dsimp only
            rw [layout_dropP]
          simp only [Option.bind_some, hk]
      · rfl
    | _ => rfl

end IxCC.Lam.Erase.Input

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId)

/-! ## Structural well-formedness of the Src program -/

/-- What the simulation assumes of the Src program's declarations: every
constructor is listed by its inductive at its index, and every listed
constructor declares that inductive and index. Ingress (the kernel's
acceptance) ensures it; erasure decides it (`Input.progWF`, `progWF_iff`). -/
structure ProgWF (I : Input) : Prop where
  ctorIn : ∀ {c : CId} {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Src.Term},
    I.decl? c = some (.ctor sf lv ind cidx np nf ty) → (I.ctorsOf ind)[cidx]? = some c
  ctorOf : ∀ {t k : CId} {i : Nat}, (I.ctorsOf t)[i]? = some k →
    ∃ sf lv np nf ty, I.decl? k = some (.ctor sf lv t i np nf ty)
  /-- A pinned `Nat` has its two pinned constructors: `zero` (index 0, no
  parameters or fields) and `succ` (index 1, one field). -/
  natPins : ∀ {N : CId}, I.known.nat = some N → ∃ Z S, I.known.natZero = some Z ∧
    I.known.natSucc = some S ∧ (∃ sf lv ty, I.decl? Z = some (.ctor sf lv N 0 0 0 ty)) ∧
    (∃ sf lv ty, I.decl? S = some (.ctor sf lv N 1 0 1 ty))
  /-- A pinned `Nat.zero` has neither parameters nor fields. -/
  zeroPin : ∀ {Z : CId}, I.known.natZero = some Z →
    ∃ sf lv N cidx ty, I.decl? Z = some (.ctor sf lv N cidx 0 0 ty)
  /-- A pinned `Nat.succ` has no parameters and one field. -/
  succPin : ∀ {S : CId}, I.known.natSucc = some S →
    ∃ sf lv N cidx ty, I.decl? S = some (.ctor sf lv N cidx 0 1 ty)
  /-- A constructor's field classes, where annotated, are as many as its
  fields. -/
  ctorFields : ∀ {c : CId} {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Src.Term},
    I.decl? c = some (.ctor sf lv ind cidx np nf ty) → ∀ {fs : List Src.Relevance.FieldClass},
      I.fields? c = some fs → fs.length = nf
  /-- The pinned `Bool` constructors: `false` at index 0 and `true` at index
  1 of one inductive, without fields. -/
  boolFalse : ∀ {c : CId}, I.known.boolFalse = some c →
    ∃ sf lv B np ty, I.decl? c = some (.ctor sf lv B 0 np 0 ty) ∧ ∃ t, I.known.boolTrue = some t ∧
      ∃ sf' lv' np' ty', I.decl? t = some (.ctor sf' lv' B 1 np' 0 ty')
  boolTrue : ∀ {c : CId}, I.known.boolTrue = some c →
    ∃ sf lv B np ty, I.decl? c = some (.ctor sf lv B 1 np 0 ty) ∧ ∃ f, I.known.boolFalse = some f ∧
      ∃ sf' lv' np' ty', I.decl? f = some (.ctor sf' lv' B 0 np' 0 ty')
  /-- `Decidable`'s pinned constructors are constructors of an inductive
  other than those of `Bool` and `Nat`'s. -/
  decOther : ∀ {c d : CId}, (I.known.decIsFalse = some c ∨ I.known.decIsTrue = some c) →
    (I.known.boolFalse = some d ∨ I.known.boolTrue = some d ∨ I.known.natZero = some d ∨
      I.known.natSucc = some d) →
    ∀ {sf lv ind cidx np nf ty sf' lv' ind' cidx' np' nf' ty'},
      I.decl? c = some (.ctor sf lv ind cidx np nf ty) →
      I.decl? d = some (.ctor sf' lv' ind' cidx' np' nf' ty') → ind ≠ ind'
  /-- A recursor has a rule for each constructor of its inductive. -/
  recRules : ∀ {r : CId} {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term},
    I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
    (I.ctorsOf ind).length ≤ rules.length ∧ rules.length ≤ nmin
  /-- A subsingleton recursor's index fields name indices of its spine. -/
  recKindIdx : ∀ {r : CId} {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term} {w : Src.PropWhen} {srcs : List Src.FieldSrc},
    I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
    I.recKind.get? r = some (.subsingleton w srcs) → ∀ i, Src.FieldSrc.index i ∈ srcs → i < ni
  /-- A subsingleton recursor has its (only) minor. -/
  subMinor : ∀ {r : CId} {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId}
    {rules : List Src.Rule} {ty : Src.Term} {w : Src.PropWhen} {srcs : List Src.FieldSrc},
    I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
    I.recKind.get? r = some (.subsingleton w srcs) → 0 < nmin
  decIsFalse : ∀ {c : CId}, I.known.decIsFalse = some c →
    ∃ sf lv D np nf ty, I.decl? c = some (.ctor sf lv D 0 np nf ty)
  decIsTrue : ∀ {c : CId}, I.known.decIsTrue = some c →
    ∃ sf lv D np nf ty, I.decl? c = some (.ctor sf lv D 1 np nf ty)

end IxCC.Lam.Erase.Proof
