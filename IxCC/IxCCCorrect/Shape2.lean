import IxCCCorrect.Shape

/-!
# Progress by shapes, milestone M2 (`IxCCCorrect.Shape2`)

`IxCCCorrect.Shape1` (first-order `Nat` and enumeration programs) extended with
**data**:

* a shape `data d`, where `d` indexes a table of the signature (`Sig.datas`,
  `DataDecl`): one entry per instance of a data type, with its inductive, the shapes
  of its parameter slots, and each constructor with the shapes of all its fields
  (`irr` for a proof or a type). A recursive type's fields mention its own index. A
  class instance (`HAdd Nat Nat Nat`) is an entry with one constructor whose field is
  a function shape;
* **constructors** with parameters and fields as special heads (`HeadOk.ctor`, F1);
* **`case`** (F5) at data, with the inductive's parameters before the motive
  (`HeadOk.cases`, `ScrutOk.data`);
* **projections** (E6) out of a one-constructor entry (`HasShape.proj`);
* a polymorphic definition is, as a matcher was in M1, one instance per use.

The judgment never mentions a Lean type: soundness needs only that the table is used
consistently (a constructor application builds a `data d` from fields of the listed
shapes, an eliminator at `data d` hands on fields of the listed shapes).

`run_ok_vals`: a shaped root on shaped argument **values** times out or returns a
value of its result shape: SrcEval's `run` is never stuck and never traps there. It
mentions no view and no `Nat` input. `run_ok`, `neverWrong_of_shape`,
`recheck_sound_of_shape` are its specialisations to the compiler's roots.

Not here: recursors with parameters (F2 is as in M1), indices, subsingleton and
empty recursors.
-/

set_option autoImplicit false

namespace IxCC.Correct.Shape2

open IxCC.Src
open IxCC.Sem (Result Lang later later_zero later_succ)
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.Correct.Shape (arity_cases headArity_prim eval2_nat evalLits_of_length litArgs_map_lit)

/-! ## Shapes, signatures and the term judgment -/

/-- The shape of a value: a `Nat`, a value of an enumeration, something irrelevant (a
type, a proof, an erased argument), or a function. -/
inductive Shape where
  | nat
  | enum (ind : CId)
  | data (d : Nat)
  | irr
  | fn (dom cod : Shape)
  deriving DecidableEq, Repr

/-- `σ₁ → … → σₙ → τ`. -/
def arrows : List Shape → Shape → Shape
  | [], τ => τ
  | σ :: σs, τ => .fn σ (arrows σs τ)

/-- **One instance of a data type**: its inductive, the shapes of its parameter slots,
each constructor with the shapes of all its fields, in index order, and whether E6 may
project it (a structure). -/
structure DataDecl where
  ind : CId
  params : List Shape
  ctors : List (CId × List Shape)
  struct : Bool

/-- A signature: the shapes each constant has at each instantiation of its levels
(several, where it is used at several), and the constructors of each enumeration in
index order. -/
structure Sig where
  inst : CId → Levels → Shape → Prop
  enums : CId → Option (List CId)
  datas : Nat → Option DataDecl

/-- **The term judgment at levels `ls`.** An argument, a `let` and a λ are read at
`ls` as SrcEval reads them: an irrelevant argument is not looked at and its slot has
shape `irr`; a λ must be one SrcEval applies there. -/
inductive HasShape (sig : Sig) (ls : Levels) : List Shape → Term → Shape → Prop
  | var {Γ : List Shape} {i : Nat} {σ : Shape} :
      Γ[i]? = some σ → HasShape sig ls Γ (.var i) σ
  | natLit {Γ : List Shape} {n : Nat} : HasShape sig ls Γ (.natLit n) .nat
  | sort {Γ : List Shape} {u : Ixon.Univ} : HasShape sig ls Γ (.sort u) .irr
  | pi {Γ : List Shape} {b : Binder} {d c : Term} : HasShape sig ls Γ (.pi b d c) .irr
  | const {Γ : List Shape} {c : CId} {us : List Ixon.Univ} {σ : Shape} :
      sig.inst c (us.map (evalUniv ls)) σ → HasShape sig ls Γ (.const c us) σ
  | lam {Γ : List Shape} {b : Binder} {d body : Term} {σ τ : Shape} :
      b.propWhen.allowsBeta ls = true → HasShape sig ls (σ :: Γ) body τ →
      HasShape sig ls Γ (.lam b d body) (.fn σ τ)
  | app {Γ : List Shape} {f a : Term} {m : Mode} {r : Rel} {σ τ : Shape} :
      r.irrAt ls = false → HasShape sig ls Γ f (.fn σ τ) → HasShape sig ls Γ a σ →
      HasShape sig ls Γ (.app f a m r) τ
  | appIrr {Γ : List Shape} {f a : Term} {m : Mode} {r : Rel} {τ : Shape} :
      r.irrAt ls = true → HasShape sig ls Γ f (.fn .irr τ) →
      HasShape sig ls Γ (.app f a m r) τ
  | letE {Γ : List Shape} {nonDep : Bool} {lm : Ixon.V3.LetMode} {r : Rel} {ty v body : Term}
      {σ τ : Shape} :
      r.irrAt ls = false → HasShape sig ls Γ v σ → HasShape sig ls (σ :: Γ) body τ →
      HasShape sig ls Γ (.letE nonDep lm r ty v body) τ
  | letIrr {Γ : List Shape} {nonDep : Bool} {lm : Ixon.V3.LetMode} {r : Rel} {ty v body : Term}
      {τ : Shape} :
      r.irrAt ls = true → HasShape sig ls (.irr :: Γ) body τ →
      HasShape sig ls Γ (.letE nonDep lm r ty v body) τ
  /-- E6: a field of a structure's entry -/
  | proj {Γ : List Shape} {s : CId} {i : Nat} {e : Term} {d : Nat} {D : DataDecl} {c : CId}
      {fl : List Shape} {σ : Shape} :
      HasShape sig ls Γ e (.data d) → sig.datas d = some D → D.struct = true → D.ind = s →
      D.ctors = [(c, fl)] → fl[i]? = some σ → HasShape sig ls Γ (.proj s i e) σ

/-! ## Special heads -/

/-- **What F2 and F5 scrutinise**: a shape, the inductive whose recursor reads it, and
the shapes of each constructor's fields, in constructor order. An enumeration's
constructors have none; `Nat`'s are `zero` and `succ n`. (M2 adds data here.) -/
inductive ScrutOk (p : Program) (sig : Sig) : Shape → CId → Nat → List (List Shape) → Prop
  | enum {I : CId} {cs : List CId} :
      sig.enums I = some cs → ScrutOk p sig (.enum I) I 0 (cs.map fun _ => [])
  | nat {N : CId} : (some N == p.known.nat) = true → ScrutOk p sig .nat N 0 [[], [.nat]]
  | data {d : Nat} {D : DataDecl} : sig.datas d = some D →
      ScrutOk p sig (.data d) D.ind D.params.length (D.ctors.map fun e => e.2)

/-- **A special head fired on slots of shapes `σs` returns a `τ`.** One clause per
kind of head in the fragment; the program facts in each are what the firing rule
reads. -/
inductive HeadOk (p : Program) (sig : Sig) : Head → Levels → List Shape → Shape → Prop
  /-- F6 at a `Nat`-valued primitive -/
  | prim (op : PrimOp) (ls : Levels) : op.isPredicate = false →
      HeadOk p sig (.prim op) ls (List.replicate op.arity .nat) .nat
  /-- F6 at a `Bool`-valued primitive: the pinned `Bool` constructors, of an
  enumeration of the signature -/
  | pred (op : PrimOp) (ls : Levels) (B t f : CId) (cs : List CId) : op.isPredicate = true →
      p.known.boolTrue = some t → p.known.boolFalse = some f → sig.enums B = some cs →
      t ∈ cs → f ∈ cs →
      HeadOk p sig (.prim op) ls (List.replicate op.arity .nat) (.enum B)
  /-- F1 at the pinned `Nat.succ` -/
  | succ (c : CId) (ls : Levels) (s : Bool) (lv : Nat) (ind : CId) (cidx : Nat) (ty : Term) :
      p.decl? c = some (.ctor s lv ind cidx 0 1 ty) → (some c == p.known.natZero) = false →
      (some c == p.known.natSucc) = true → HeadOk p sig (.ctor c) ls [.nat] .nat
  /-- F5: a `case` entry over an ordinary recursor without parameters or indices;
  the motive is irrelevant, each minor takes its constructor's fields -/
  | cases (c r : CId) (ls : Levels) (ps : List Shape) (σ : Shape) (ind : CId)
      (flds : List (List Shape)) (τ : Shape) (s kk : Bool) (lv nmot : Nat) (rules : List Rule)
      (ty : Term) :
      p.table.resolveOf c = some (.case r) →
      p.decl? r = some (.recr s kk lv ps.length nmot flds.length 0 ind rules ty) →
      p.table.recKindOf r = some .ordinary → ScrutOk p sig σ ind ps.length flds →
      HeadOk p sig (.cases c) ls (ps ++ (.irr :: σ :: flds.map fun fl => arrows fl τ)) τ
  /-- F1 at a constructor of a data entry: its parameter slots, then its fields -/
  | ctor (c : CId) (ls : Levels) (d : Nat) (D : DataDecl) (j : Nat) (fl : List Shape) :
      sig.datas d = some D → D.ctors[j]? = some (c, fl) →
      HeadOk p sig (.ctor c) ls (D.params ++ fl) (.data d)
  /-- F2: an ordinary recursor without parameters or indices, at minors of any
  shapes `ms` under which each rule's body, in the environment F2 builds, has the
  result shape -/
  | recr (r : CId) (ls : Levels) (σ : Shape) (ind : CId) (flds : List (List Shape))
      (ms : List Shape) (τ : Shape) (s kk : Bool) (lv : Nat) (rules : List Rule) (ty : Term) :
      p.decl? r = some (.recr s kk lv 0 1 ms.length 0 ind rules ty) →
      p.table.recKindOf r = some .ordinary → ScrutOk p sig σ ind 0 flds →
      (∀ (j : Nat) (fl : List Shape), flds[j]? = some fl → ∃ (rule : Rule) (body : Term),
        rules[j]? = some rule ∧
        peelLams (1 + ms.length + fl.length) rule.rhs = some body ∧
        HasShape sig ls (fl.reverse ++ (ms.reverse ++ [.irr])) body τ) →
      HeadOk p sig (.recr r) ls (.irr :: (ms ++ [σ])) τ

/-! ## The value judgment -/

mutual

/-- **A value has a shape.** -/
inductive ValOk (p : Program) (sig : Sig) : Value → Shape → Prop
  | lit {n : Nat} : ValOk p sig (.lit n) .nat
  | enum {c : CId} {ls : Levels} {I : CId} {cs : List CId} :
      sig.enums I = some cs → c ∈ cs → ValOk p sig (.con c ls [] []) (.enum I)
  /-- a constructor value of a data entry: as many parameter slots as the entry
  says (they are not read), fields of the constructor's shapes -/
  | data {c : CId} {ls : Levels} {ps : List Slot} {fs : List Value} {d : Nat} {D : DataDecl}
      {j : Nat} {fl : List Shape} :
      sig.datas d = some D → D.ctors[j]? = some (c, fl) → ps.length = D.params.length →
      ValsOk p sig fs fl → ValOk p sig (.con c ls ps fs) (.data d)
  | irr {t : Option Term} {ρ : List Slot} {ls : Levels} : ValOk p sig (.irr t ρ ls) .irr
  /-- a closure, by its code, at its own levels -/
  | clo {b : Binder} {d body : Term} {ρ : List Slot} {ls : Levels} {Γ : List Shape}
      {σ τ : Shape} :
      b.propWhen.allowsBeta ls = true → EnvOk p sig ρ Γ → HasShape sig ls (σ :: Γ) body τ →
      ValOk p sig (.clo b d body ρ ls) (.fn σ τ)
  /-- a partial application of a special head: the arguments it has are of the first
  shapes, and it lacks at least one -/
  | pap (h : Head) (ls : Levels) (args : List Slot) (σs done rest : List Shape)
      (τ σ : Shape) :
      HeadOk p sig h ls σs τ → σs = done ++ rest → EnvOk p sig args done → rest ≠ [] →
      σ = arrows rest τ → ValOk p sig (.pap h ls args) σ

/-- **A slot has a shape**: a value's, or a thunk's by its code. -/
inductive SlotOk (p : Program) (sig : Sig) : Slot → Shape → Prop
  | val {v : Value} {σ : Shape} : ValOk p sig v σ → SlotOk p sig (.val v) σ
  | name {t : Term} {ρ : List Slot} {ls : Levels} {Γ : List Shape} {σ : Shape} :
      EnvOk p sig ρ Γ → HasShape sig ls Γ t σ → SlotOk p sig (.name t ρ ls) σ

/-- **Slots have shapes**, one by one. -/
inductive EnvOk (p : Program) (sig : Sig) : List Slot → List Shape → Prop
  | nil : EnvOk p sig [] []
  | cons {s : Slot} {ρ : List Slot} {σ : Shape} {Γ : List Shape} :
      SlotOk p sig s σ → EnvOk p sig ρ Γ → EnvOk p sig (s :: ρ) (σ :: Γ)

/-- **Values have shapes**, one by one (a constructor's fields). -/
inductive ValsOk (p : Program) (sig : Sig) : List Value → List Shape → Prop
  | nil : ValsOk p sig [] []
  | cons {v : Value} {vs : List Value} {σ : Shape} {Γ : List Shape} :
      ValOk p sig v σ → ValsOk p sig vs Γ → ValsOk p sig (v :: vs) (σ :: Γ)

end

/-- An outcome is a timeout or a value of the shape. -/
def ResOk (p : Program) (sig : Sig) (σ : Shape) (r : Result Value) : Prop :=
  r = .timeout ∨ ∃ v, r = .ok v ∧ ValOk p sig v σ

/-! ## The program against the signature -/

/-- δ of `c` evaluates the term `t`: an equation hint's body, a `csimp` target, a
safe definition's value. -/
inductive Unfolds (p : Program) : CId → Term → Prop
  | eqn {c thm : CId} {body : Term} :
      p.table.resolveOf c = some (.eqn thm body) → Unfolds p c body
  | csimp {c g thm : CId} {us : List Ixon.Univ} :
      p.table.resolveOf c = some (.csimp g us thm) → Unfolds p c (.const g us)
  | defn {c : CId} {lvls : Nat} {ty v : Term} :
      p.table.resolveOf c = none → p.decl? c = some (.defn .defn .safe lvls ty v) →
      Unfolds p c v

/-- δ of `c` is the special head `h`. -/
inductive HeadOf (p : Program) : CId → Head → Prop
  | prim {c : CId} {op : PrimOp} : p.table.resolveOf c = some (.prim op) → HeadOf p c (.prim op)
  | cases {c r : CId} : p.table.resolveOf c = some (.case r) → HeadOf p c (.cases c)
  | ctor {c : CId} {s : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Term} :
      p.table.resolveOf c = none → p.decl? c = some (.ctor s lv ind cidx np nf ty) →
      HeadOf p c (.ctor c)
  | recr {c : CId} {s kk : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Rule}
      {ty : Term} :
      p.table.resolveOf c = none →
      p.decl? c = some (.recr s kk lv np nmot nmin ni ind rules ty) → HeadOf p c (.recr c)

/-- **A constant resolves in the program as an instance says.** -/
inductive ConstOk (p : Program) (sig : Sig) : CId → Levels → Shape → Prop
  | body {c : CId} {ls : Levels} {σ : Shape} {t : Term} :
      Unfolds p c t → HasShape sig ls [] t σ → ConstOk p sig c ls σ
  | head {c : CId} {ls : Levels} {h : Head} {σs : List Shape} {τ : Shape} :
      HeadOf p c h → HeadOk p sig h ls σs τ → ConstOk p sig c ls (arrows σs τ)
  | zero {c : CId} {ls : Levels} {s : Bool} {lv : Nat} {ind : CId} {cidx : Nat} {ty : Term} :
      p.table.resolveOf c = none → p.decl? c = some (.ctor s lv ind cidx 0 0 ty) →
      (some c == p.known.natZero) = true → ConstOk p sig c ls .nat
  | enumCtor {c : CId} {ls : Levels} {I : CId} {cs : List CId} :
      p.table.resolveOf c = none → sig.enums I = some cs → c ∈ cs →
      ConstOk p sig c ls (.enum I)

/-- **The program agrees with the signature**: every instance resolves as it says, and
every enumeration's listed constructors are its constructors, in index order, without
parameters or fields, and none is a pinned `Nat` constructor. -/
structure SigOk (p : Program) (sig : Sig) : Prop where
  inst : ∀ c ls σ, sig.inst c ls σ → ConstOk p sig c ls σ
  enums : ∀ I cs, sig.enums I = some cs → ∀ i c, cs[i]? = some c →
    ∃ s lv ty, p.decl? c = some (.ctor s lv I i 0 0 ty) ∧
      (some c == p.known.natZero) = false ∧ (some c == p.known.natSucc) = false
  /-- every data entry's constructors are constructors of its inductive, at their
  indices, with the entry's parameter count and their own field count -/
  datas : ∀ d D, sig.datas d = some D → ∀ j c fl, D.ctors[j]? = some (c, fl) →
    ∃ s lv ty, p.decl? c = some (.ctor s lv D.ind j D.params.length fl.length ty) ∧
      (some c == p.known.natZero) = false ∧ (some c == p.known.natSucc) = false
  /-- an entry E6 may project is of an inductive with exactly that constructor -/
  structs : ∀ d D, sig.datas d = some D → D.struct = true → ∀ c fl, D.ctors = [(c, fl)] →
    ∃ s lv np ni ty, p.decl? D.ind = some (.induct s lv np ni ty [c])

/-! ## Small facts -/

theorem eval2_bool {op : PrimOp} (hp : op.isPredicate = true) (a b : Nat) :
    ∃ r, op.eval2 a b = .bool r := by
  cases op <;> first | exact ⟨_, rfl⟩ | cases hp

theorem getElem?_two_add {α : Type} (a b : α) (l : List α) (j : Nat) :
    (a :: b :: l)[2 + j]? = l[j]? := by
  rw [Nat.add_comm]
  rfl

theorem evalConst_unfolds {p : Program} {k : Nat} {ls : Levels} {c : CId} {t : Term}
    (h : Unfolds p c t) : evalConst p k ls c = later k fun k => eval p k ls [] t := by
  cases h with
  | eqn hres => rw [evalConst_eq, hres] <;> rfl
  | csimp hres => rw [evalConst_eq, hres] <;> rfl
  | defn hres hdecl => rw [evalConst_eq, hres, hdecl] <;> rfl

theorem evalConst_head {p : Program} {k : Nat} {ls : Levels} {c : CId} {h : Head}
    (hof : HeadOf p c h) : evalConst p k ls c = headValue p k ls h := by
  cases hof with
  | prim hres => rw [evalConst_eq, hres] <;> rfl
  | cases hres => rw [evalConst_eq, hres] <;> rfl
  | ctor hres hdecl => rw [evalConst_eq, hres, hdecl] <;> rfl
  | recr hres hdecl => rw [evalConst_eq, hres, hdecl] <;> rfl

theorem headArity_ctor (p : Program) {c : CId} {s : Bool} {lv : Nat} {ind : CId}
    {cidx np nf : Nat} {ty : Term} (hdecl : p.decl? c = some (.ctor s lv ind cidx np nf ty)) :
    p.headArity (.ctor c) = np + nf := by
  simp only [Program.headArity, hdecl]

theorem getElem?_append_add {α : Type} : ∀ (l₁ l₂ : List α) (i : Nat),
    (l₁ ++ l₂)[l₁.length + i]? = l₂[i]?
  | [], l₂, i => by
    show l₂[0 + i]? = l₂[i]?
    rw [Nat.zero_add]
  | a :: l₁, l₂, i => by
    have e : (a :: l₁).length + i = (l₁.length + i) + 1 := by
      rw [List.length_cons]
      omega
    rw [e]
    show (l₁ ++ l₂)[l₁.length + i]? = l₂[i]?
    exact getElem?_append_add l₁ l₂ i

/-- F5 at an ordinary recursor with `np` parameters and no index. -/
theorem fire_cases_ord (p : Program) (k : Nat) (ls : Levels) (c r : CId) (args : List Slot)
    {s kk : Bool} {lv np nmot nmin : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hres : p.table.resolveOf c = some (.case r))
    (hdecl : p.decl? r = some (.recr s kk lv np nmot nmin 0 ind rules ty))
    (hkind : p.table.recKindOf r = some .ordinary) :
    fire p k (.cases c) ls args = later k fun k =>
      ((force p k (args.getD (np + 1) default)).bind fun major =>
          Result.ofOption (p.selectRule ind np major)).bind fun (j, fields) =>
        (force p k (args.getD (np + 1 + 1 + j) default)).bind fun minor =>
          applyAll p k minor fields := by
  rw [fire_cases]
  simp only [hres, hdecl, hkind, Option.map_some] <;> rfl

/-- F2 at an ordinary recursor with one motive and no parameters or indices. -/
theorem fire_recr_ord (p : Program) (k : Nat) (ls : Levels) (r : CId) (args : List Slot)
    {s kk : Bool} {lv nmin : Nat} {ind : CId} {rules : List Rule} {ty : Term}
    (hdecl : p.decl? r = some (.recr s kk lv 0 1 nmin 0 ind rules ty))
    (hkind : p.table.recKindOf r = some .ordinary) :
    fire p k (.recr r) ls args = later k fun k =>
      ((force p k (args.getD (1 + nmin) default)).bind fun major =>
          Result.ofOption (p.selectRule ind 0 major)).bind fun (j, fields) =>
        match rules[j]? with
        | some rule =>
          match peelLams (args.take (1 + nmin) ++ fields).length rule.rhs with
          | some body => eval p k ls (args.take (1 + nmin) ++ fields).reverse body
          | none => .stuck
        | none => .stuck := by
  rw [fire_recr]
  simp only [hdecl, hkind, Option.map_some] <;> rfl

variable {p : Program} {sig : Sig}

/-! ## Slots against shapes -/

theorem EnvOk.get : ∀ (ρ : List Slot) (Γ : List Shape), EnvOk p sig ρ Γ →
    ∀ (i : Nat) (σ : Shape), Γ[i]? = some σ → ∃ s, ρ[i]? = some s ∧ SlotOk p sig s σ
  | [], _, h, i, σ, hi => by
    cases h
    simp at hi
  | s :: ρ, _, h, i, σ, hi => by
    cases h with
    | cons hs hρ =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨s, List.getElem?_cons_zero, hs⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi ⊢
        exact EnvOk.get ρ _ hρ i σ hi

theorem EnvOk.getD {ρ : List Slot} {Γ : List Shape} (h : EnvOk p sig ρ Γ) {i : Nat} {σ : Shape}
    (hi : Γ[i]? = some σ) : SlotOk p sig (ρ.getD i default) σ := by
  obtain ⟨s, hs, hok⟩ := EnvOk.get ρ Γ h i σ hi
  rw [List.getD_eq_getElem?_getD, hs]
  exact hok

theorem EnvOk.length : ∀ (ρ : List Slot) (Γ : List Shape), EnvOk p sig ρ Γ →
    ρ.length = Γ.length
  | [], _, h => by
    cases h
    rfl
  | s :: ρ, _, h => by
    cases h with
    | cons hs hρ => simp [EnvOk.length ρ _ hρ]

theorem EnvOk.append : ∀ (ρ₁ : List Slot) (Γ₁ : List Shape) {ρ₂ : List Slot} {Γ₂ : List Shape},
    EnvOk p sig ρ₁ Γ₁ → EnvOk p sig ρ₂ Γ₂ → EnvOk p sig (ρ₁ ++ ρ₂) (Γ₁ ++ Γ₂)
  | [], _, _, _, h₁, h₂ => by
    cases h₁
    exact h₂
  | s :: ρ₁, _, _, _, h₁, h₂ => by
    cases h₁ with
    | cons hs hρ => exact .cons hs (EnvOk.append ρ₁ _ hρ h₂)

theorem EnvOk.reverse : ∀ (ρ : List Slot) (Γ : List Shape), EnvOk p sig ρ Γ →
    EnvOk p sig ρ.reverse Γ.reverse
  | [], _, h => by
    cases h
    exact .nil
  | s :: ρ, _, h => by
    cases h with
    | cons hs hρ =>
      rw [List.reverse_cons, List.reverse_cons]
      exact EnvOk.append _ _ (EnvOk.reverse ρ _ hρ) (.cons hs .nil)

theorem EnvOk.take : ∀ (Γ₁ : List Shape) (ρ : List Slot) {Γ₂ : List Shape},
    EnvOk p sig ρ (Γ₁ ++ Γ₂) → EnvOk p sig (ρ.take Γ₁.length) Γ₁
  | [], _, _, _ => .nil
  | σ :: Γ₁, ρ, Γ₂, h => by
    have h' : EnvOk p sig ρ (σ :: (Γ₁ ++ Γ₂)) := h
    cases h' with
    | cons hs hρ => exact .cons hs (EnvOk.take Γ₁ _ hρ)

theorem EnvOk.drop : ∀ (Γ₁ : List Shape) (ρ : List Slot) {Γ₂ : List Shape},
    EnvOk p sig ρ (Γ₁ ++ Γ₂) → EnvOk p sig (ρ.drop Γ₁.length) Γ₂
  | [], _, _, h => h
  | σ :: Γ₁, ρ, Γ₂, h => by
    have h' : EnvOk p sig ρ (σ :: (Γ₁ ++ Γ₂)) := h
    cases h' with
    | cons hs hρ => exact EnvOk.drop Γ₁ _ hρ

theorem ValsOk.toEnv : ∀ (vs : List Value) (Γ : List Shape), ValsOk p sig vs Γ →
    EnvOk p sig (vs.map Slot.val) Γ
  | [], _, h => by
    cases h
    exact .nil
  | v :: vs, _, h => by
    cases h with
    | cons hv hvs => exact .cons (.val hv) (ValsOk.toEnv vs _ hvs)

theorem ValsOk.get : ∀ (vs : List Value) (Γ : List Shape), ValsOk p sig vs Γ →
    ∀ (i : Nat) (σ : Shape), Γ[i]? = some σ → ∃ v, vs[i]? = some v ∧ ValOk p sig v σ
  | [], _, h, i, σ, hi => by
    cases h
    simp at hi
  | v :: vs, _, h, i, σ, hi => by
    cases h with
    | cons hv hvs =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨v, List.getElem?_cons_zero, hv⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi ⊢
        exact ValsOk.get vs _ hvs i σ hi

theorem EnvOk.all_replicate {σ : Shape} : ∀ (n : Nat) (ρ : List Slot),
    EnvOk p sig ρ (List.replicate n σ) → ∀ s, s ∈ ρ → SlotOk p sig s σ
  | 0, ρ, h, s, hs => by
    have h' : EnvOk p sig ρ [] := h
    cases h'
    cases hs
  | n + 1, ρ, h, s, hs => by
    have h' : EnvOk p sig ρ (σ :: List.replicate n σ) := h
    cases h' with
    | cons h1 hρ =>
      rcases List.mem_cons.1 hs with rfl | hs'
      · exact h1
      · exact EnvOk.all_replicate n _ hρ s hs'

theorem envOk_lits : ∀ ns : List Nat,
    EnvOk p sig ((ns.map Value.lit).map Slot.val) (List.replicate ns.length .nat)
  | [] => .nil
  | n :: ns => by
    show EnvOk p sig (Slot.val (Value.lit n) :: (ns.map Value.lit).map Slot.val)
      (Shape.nat :: List.replicate ns.length .nat)
    exact .cons (.val .lit) (envOk_lits ns)

/-! ## Canonical forms, by inversion of the value judgment -/

/-- **Canonical forms at `nat`.** -/
theorem ValOk.nat_inv {v : Value} (h : ValOk p sig v .nat) : ∃ n, v = .lit n := by
  cases h with
  | lit => exact ⟨_, rfl⟩
  | pap h ls args σs done rest τ σ hh hσs hargs hrest hσ =>
    cases rest with
    | nil => exact absurd rfl hrest
    | cons a r => simp [arrows] at hσ

/-- **Canonical forms at an enumeration**: a listed constructor, with no parameter
and no field. -/
theorem ValOk.enum_inv {v : Value} {I : CId} (h : ValOk p sig v (.enum I)) :
    ∃ c ls cs, v = .con c ls [] [] ∧ sig.enums I = some cs ∧ c ∈ cs := by
  cases h with
  | enum hI hc => exact ⟨_, _, _, rfl, hI, hc⟩
  | pap h ls args σs done rest τ σ hh hσs hargs hrest hσ =>
    cases rest with
    | nil => exact absurd rfl hrest
    | cons a r => simp [arrows] at hσ

/-- **Canonical forms at a data entry**: one of its constructors, with the entry's
parameter count and fields of that constructor's shapes. -/
theorem ValOk.data_inv {v : Value} {d : Nat} (h : ValOk p sig v (.data d)) :
    ∃ (c : CId) (ls : Levels) (ps : List Slot) (fs : List Value) (D : DataDecl) (j : Nat)
      (fl : List Shape), v = .con c ls ps fs ∧ sig.datas d = some D ∧
      D.ctors[j]? = some (c, fl) ∧ ps.length = D.params.length ∧ ValsOk p sig fs fl := by
  cases h with
  | data hD hc hps hfs => exact ⟨_, _, _, _, _, _, _, rfl, hD, hc, hps, hfs⟩
  | pap h ls args σs done rest τ σ hh hσs hargs hrest hσ =>
    cases rest with
    | nil => exact absurd rfl hrest
    | cons a r => simp [arrows] at hσ

/-- **F2 and F5 select a rule** on a value of the scrutinised shape, and the fields
they hand on have the constructor's field shapes. -/
theorem selectRule_ok (hsig : SigOk p sig) {σ : Shape} {ind : CId} {np : Nat}
    {flds : List (List Shape)} {v : Value} (hs : ScrutOk p sig σ ind np flds)
    (hv : ValOk p sig v σ) :
    ∃ j fs fl, p.selectRule ind np v = some (j, fs) ∧ flds[j]? = some fl ∧
      EnvOk p sig fs fl := by
  cases hs with
  | @data d D hD =>
    obtain ⟨c, ls, ps, fs, D', j, fl, rfl, hD', hc, hps, hfs⟩ := hv.data_inv
    rw [hD] at hD'
    cases hD'
    obtain ⟨s, lv, ty, hdecl, -, -⟩ := hsig.datas _ _ hD j c fl hc
    refine ⟨j, fs.map Slot.val, fl, ?_, ?_, ValsOk.toEnv _ _ hfs⟩
    · simp [Program.selectRule, hdecl, hps]
    · simp [hc]
  | enum hI =>
    obtain ⟨c, ls, cs', rfl, hI', hc⟩ := hv.enum_inv
    rw [hI] at hI'
    cases hI'
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc
    obtain ⟨s, lv, ty, hdecl, -, -⟩ := hsig.enums _ _ hI i c hi
    refine ⟨i, [], [], ?_, ?_, .nil⟩
    · simp [Program.selectRule, hdecl]
    · simp [hi]
  | nat hN =>
    obtain ⟨n, rfl⟩ := hv.nat_inv
    cases n with
    | zero => exact ⟨0, [], [], by simp [Program.selectRule, hN], rfl, .nil⟩
    | succ n =>
      exact ⟨1, [.val (.lit n)], [.nat], by simp [Program.selectRule, hN], rfl,
        .cons (.val .lit) .nil⟩

/-- A special head's arity is the number of shapes it is fired on. -/
theorem HeadOk.arity (hsig : SigOk p sig) {h : Head} {ls : Levels} {σs : List Shape}
    {τ : Shape} (hh : HeadOk p sig h ls σs τ) : p.headArity h = σs.length := by
  cases hh with
  | prim op ls hp => simp [Program.headArity]
  | pred op ls B t f cs hp ht hf hB htm hfm => simp [Program.headArity]
  | succ c ls s lv ind cidx ty hdecl hz hs => simp [Program.headArity, hdecl]
  | ctor c ls d D j fl hD hc =>
    obtain ⟨s, lv, ty, hdecl, -, -⟩ := hsig.datas _ _ hD j c fl hc
    simp [Program.headArity, hdecl]
  | cases c r ls ps σ ind flds τ s kk lv nmot rules ty hres hdecl hkind hscrut =>
    simp [Program.headArity, hres, hdecl] <;> omega
  | recr r ls σ ind flds ms τ s kk lv rules ty hdecl hkind hscrut hrules =>
    simp [Program.headArity, hdecl, Decl.recArity] <;> omega

/-- Forcing slots of shape `nat` times out or returns literals. -/
theorem forceAll_nat {k : Nat}
    (hslot : ∀ (s : Slot) (σ : Shape), SlotOk p sig s σ → ResOk p sig σ (force p k s)) :
    ∀ ss : List Slot, (∀ s, s ∈ ss → SlotOk p sig s .nat) →
      forceAll p k ss = .timeout ∨
        ∃ ns : List Nat, forceAll p k ss = .ok (ns.map Value.lit) ∧ ns.length = ss.length
  | [], _ => .inr ⟨[], forceAll_nil p k, rfl⟩
  | s :: ss, h => by
    rw [forceAll_cons]
    rcases hslot s .nat (h s (List.mem_cons.2 (.inl rfl))) with hs | ⟨v, hs, hv⟩
    · rw [hs]
      exact .inl rfl
    · obtain ⟨n, rfl⟩ := hv.nat_inv
      rw [hs]
      rcases forceAll_nat hslot ss (fun s' hs' => h s' (List.mem_cons.2 (.inr hs'))) with
        ht | ⟨ns, hns, hnl⟩
      · rw [ht]
        exact .inl rfl
      · rw [hns]
        exact .inr ⟨n :: ns, rfl, by simp [hnl]⟩

/-- Forcing slots times out or returns values of their shapes. -/
theorem forceAll_ok {k : Nat}
    (hslot : ∀ (s : Slot) (σ : Shape), SlotOk p sig s σ → ResOk p sig σ (force p k s)) :
    ∀ (ss : List Slot) (Γ : List Shape), EnvOk p sig ss Γ →
      forceAll p k ss = .timeout ∨ ∃ vs, forceAll p k ss = .ok vs ∧ ValsOk p sig vs Γ
  | [], _, h => by
    cases h
    exact .inr ⟨[], forceAll_nil p k, .nil⟩
  | s :: ss, _, h => by
    cases h with
    | cons hs hss =>
      rw [forceAll_cons]
      rcases hslot s _ hs with h1 | ⟨v, h1, hv⟩
      · rw [h1]
        exact .inl rfl
      · rw [h1]
        rcases forceAll_ok hslot ss _ hss with ht | ⟨vs, hvs, hok⟩
        · rw [ht]
          exact .inl rfl
        · rw [hvs]
          exact .inr ⟨v :: vs, rfl, .cons hv hok⟩

/-- A value of shape `σ₁ → … → σₙ → τ` applied to slots of those shapes. -/
theorem applyAll_ok {k : Nat}
    (happ : ∀ (f : Value) (s : Slot) (σ τ : Shape), ValOk p sig f (.fn σ τ) → SlotOk p sig s σ →
      ResOk p sig τ (apply p k f s)) {τ : Shape} :
    ∀ (ss : List Slot) (Γ : List Shape) (f : Value), EnvOk p sig ss Γ →
      ValOk p sig f (arrows Γ τ) → ResOk p sig τ (applyAll p k f ss)
  | [], _, f, h, hf => by
    cases h
    rw [applyAll_nil]
    exact .inr ⟨f, rfl, hf⟩
  | s :: ss, _, f, h, hf => by
    cases h with
    | cons hs hss =>
      rw [applyAll_cons]
      rcases happ f s _ _ hf hs with ha | ⟨v, ha, hv⟩
      · rw [ha]
        exact .inl rfl
      · rw [ha]
        exact applyAll_ok happ ss _ v hss hv

/-! ## Soundness -/

/-- **Shape soundness at clock `k`.** -/
structure AllOk (p : Program) (sig : Sig) (k : Nat) : Prop where
  term : ∀ (ls : Levels) (ρ : Env) (Γ : List Shape) (t : Term) (σ : Shape),
    HasShape sig ls Γ t σ → EnvOk p sig ρ Γ → ResOk p sig σ (eval p k ls ρ t)
  const : ∀ (ls : Levels) (c : CId) (σ : Shape), sig.inst c ls σ →
    ResOk p sig σ (evalConst p k ls c)
  app : ∀ (f : Value) (s : Slot) (σ τ : Shape), ValOk p sig f (.fn σ τ) → SlotOk p sig s σ →
    ResOk p sig τ (apply p k f s)
  slot : ∀ (s : Slot) (σ : Shape), SlotOk p sig s σ → ResOk p sig σ (force p k s)

/-- **Shape soundness (M1)**: on a program that agrees with the signature, at every
clock, a shaped term in a shaped environment, δ of an instance, application of a
function-shaped value to a slot of its domain, and a force of a shaped slot each time
out or return a value of the shape. By strong induction on the clock; firing a
saturated special head is by cases on `HeadOk`, the charged ones (F2, F5) one clock
down. -/
theorem allOk (hsig : SigOk p sig) : ∀ k, AllOk p sig k := by
  intro k
  refine Nat.strongRecOn k fun k ih => ?_
  -- E1's force and a forced thunk
  have hslot : ∀ (s : Slot) (σ : Shape), SlotOk p sig s σ → ResOk p sig σ (force p k s) := by
    intro s σ hs
    cases hs with
    | val hv =>
      rw [force_val]
      exact .inr ⟨_, rfl, hv⟩
    | name hρ ht =>
      rw [force_name]
      cases k with
      | zero => exact .inl rfl
      | succ k => exact (ih k (Nat.lt_succ_self k)).term _ _ _ _ _ ht hρ
  -- F1, F2, F5, F6: a saturated special head
  have hfire : ∀ (h : Head) (ls : Levels) (σs : List Shape) (τ : Shape) (slots : List Slot),
      HeadOk p sig h ls σs τ → EnvOk p sig slots σs → ResOk p sig τ (fire p k h ls slots) := by
    intro h ls σs τ slots hh hslots
    cases hh with
    | prim op ls hp =>
      rw [fire_prim]
      have hall := EnvOk.all_replicate _ _ hslots
      have hlen : slots.length = op.arity := by
        rw [EnvOk.length _ _ hslots, List.length_replicate]
      rcases forceAll_nat hslot slots hall with hto | ⟨ns, hns, hnl⟩
      · rw [hto]
        exact .inl rfl
      · rw [hns]
        obtain ⟨a, b, he⟩ := evalLits_of_length (op := op) (ns := ns) (by rw [hnl, hlen])
        obtain ⟨n, hn⟩ := eval2_nat hp a b
        refine .inr ⟨.lit n, ?_, .lit⟩
        show primValue p op (ns.map Value.lit) = .ok (.lit n)
        simp only [primValue, litArgs_map_lit, he, hn]
    | pred op ls B t f cs hp ht hf hB htm hfm =>
      rw [fire_prim]
      have hall := EnvOk.all_replicate _ _ hslots
      have hlen : slots.length = op.arity := by
        rw [EnvOk.length _ _ hslots, List.length_replicate]
      rcases forceAll_nat hslot slots hall with hto | ⟨ns, hns, hnl⟩
      · rw [hto]
        exact .inl rfl
      · rw [hns]
        obtain ⟨a, b, he⟩ := evalLits_of_length (op := op) (ns := ns) (by rw [hnl, hlen])
        obtain ⟨r, hr⟩ := eval2_bool hp a b
        have hpv : primValue p op (ns.map Value.lit) = p.boolValue r := by
          simp only [primValue, litArgs_map_lit, he, hr]
        show ResOk p sig (.enum B) (primValue p op (ns.map Value.lit))
        rw [hpv]
        cases r with
        | true =>
          refine .inr ⟨.con t [] [] [], ?_, .enum hB htm⟩
          simp [Program.boolValue, ht]
        | false =>
          refine .inr ⟨.con f [] [] [], ?_, .enum hB hfm⟩
          simp [Program.boolValue, hf]
    | succ c ls s lv ind cidx ty hdecl hz hs =>
      rw [fire_ctor, hdecl]
      show ResOk p sig .nat ((forceAll p k slots).bind (ctorResult p c ls []))
      have hslots' : EnvOk p sig slots (List.replicate 1 .nat) := hslots
      have hall := EnvOk.all_replicate _ _ hslots'
      have hlen : slots.length = 1 := EnvOk.length _ _ hslots
      rcases forceAll_nat hslot slots hall with hto | ⟨ns, hns, hnl⟩
      · rw [hto]
        exact .inl rfl
      · have h1 : ns.length = 1 := hnl.trans hlen
        cases ns with
        | nil => simp at h1
        | cons n rest =>
          cases rest with
          | cons _ _ =>
            simp only [List.length_cons] at h1
            omega
          | nil =>
            rw [hns]
            refine .inr ⟨.lit (n + 1), ?_, .lit⟩
            show ctorResult p c ls [] [Value.lit n] = .ok (.lit (n + 1))
            simp [ctorResult, hz, hs]
    | ctor c ls d D j fl hD hc =>
      obtain ⟨s, lv, ty, hdecl, hz, hs⟩ := hsig.datas _ _ hD j c fl hc
      rw [fire_ctor, hdecl]
      show ResOk p sig (.data d) ((forceAll p k (slots.drop D.params.length)).bind
        (ctorResult p c ls (slots.take D.params.length)))
      have hfl := EnvOk.drop _ _ hslots
      have hpl : (slots.take D.params.length).length = D.params.length :=
        EnvOk.length _ _ (EnvOk.take _ _ hslots)
      rcases forceAll_ok hslot _ _ hfl with hto | ⟨vs, hvs, hok⟩
      · rw [hto]
        exact .inl rfl
      · rw [hvs]
        refine .inr ⟨.con c ls (slots.take D.params.length) vs, ?_, .data hD hc hpl hok⟩
        show ctorResult p c ls (slots.take D.params.length) vs = _
        simp [ctorResult, hz, hs]
    | cases c r ls ps σ ind flds τ s kk lv nmot rules ty hres hdecl hkind hscrut =>
      rw [fire_cases_ord p k ls c r slots hres hdecl hkind]
      cases k with
      | zero => exact .inl rfl
      | succ k =>
        have A := ih k (Nat.lt_succ_self k)
        simp only [later_succ]
        have hmajor : SlotOk p sig (slots.getD (ps.length + 1) default) σ := by
          refine EnvOk.getD hslots ?_
          rw [getElem?_append_add]
          rfl
        rcases A.slot _ _ hmajor with hm | ⟨v, hm, hv⟩
        · rw [hm]
          exact .inl rfl
        · rw [hm]
          obtain ⟨j, fs, fl, hsel, hfl, hfs⟩ := selectRule_ok hsig hscrut hv
          show ResOk p sig τ ((Result.ofOption (p.selectRule ind ps.length v)).bind _)
          rw [hsel]
          show ResOk p sig τ ((force p k (slots.getD (ps.length + 1 + 1 + j) default)).bind
            fun minor => applyAll p k minor fs)
          have hminor : SlotOk p sig (slots.getD (ps.length + 1 + 1 + j) default)
              (arrows fl τ) := by
            refine EnvOk.getD hslots ?_
            have e : ps.length + 1 + 1 + j = ps.length + (2 + j) := by omega
            rw [e, getElem?_append_add, getElem?_two_add, List.getElem?_map, hfl]
            rfl
          rcases A.slot _ _ hminor with hmn | ⟨mv, hmn, hmv⟩
          · rw [hmn]
            exact .inl rfl
          · rw [hmn]
            exact applyAll_ok A.app fs fl mv hfs hmv
    | recr r ls σ ind flds ms τ s kk lv rules ty hdecl hkind hscrut hrules =>
      rw [fire_recr_ord p k ls r slots hdecl hkind]
      cases k with
      | zero => exact .inl rfl
      | succ k =>
        have A := ih k (Nat.lt_succ_self k)
        simp only [later_succ]
        have hmajor : SlotOk p sig (slots.getD (1 + ms.length) default) σ := by
          refine EnvOk.getD hslots ?_
          rw [Nat.add_comm]
          simp
        rcases A.slot _ _ hmajor with hm | ⟨v, hm, hv⟩
        · rw [hm]
          exact .inl rfl
        · rw [hm]
          obtain ⟨j, fs, fl, hsel, hfl, hfs⟩ := selectRule_ok hsig hscrut hv
          obtain ⟨rule, body, hrule, hpeel, hbody⟩ := hrules j fl hfl
          have e1 : 1 + ms.length = (Shape.irr :: ms).length := by
            rw [List.length_cons, Nat.add_comm]
          have hpre : EnvOk p sig (slots.take (1 + ms.length)) (Shape.irr :: ms) := by
            rw [e1]
            have hslots' : EnvOk p sig slots ((Shape.irr :: ms) ++ [σ]) := hslots
            exact EnvOk.take _ _ hslots'
          have hall := EnvOk.append _ _ hpre hfs
          have hlen : (slots.take (1 + ms.length) ++ fs).length = 1 + ms.length + fl.length := by
            rw [EnvOk.length _ _ hall, List.length_append, List.length_cons]
            omega
          have henv := EnvOk.reverse _ _ hall
          have e2 : ((Shape.irr :: ms) ++ fl).reverse = fl.reverse ++ (ms.reverse ++ [Shape.irr]) := by
            simp
          rw [e2] at henv
          show ResOk p sig τ ((Result.ofOption (p.selectRule ind 0 v)).bind _)
          rw [hsel]
          show ResOk p sig τ
            (match rules[j]? with
            | some rule =>
              match peelLams (slots.take (1 + ms.length) ++ fs).length rule.rhs with
              | some body => eval p k ls (slots.take (1 + ms.length) ++ fs).reverse body
              | none => .stuck
            | none => .stuck)
          rw [hrule]
          show ResOk p sig τ
            (match peelLams (slots.take (1 + ms.length) ++ fs).length rule.rhs with
            | some body => eval p k ls (slots.take (1 + ms.length) ++ fs).reverse body
            | none => .stuck)
          rw [hlen, hpeel]
          exact A.term ls _ _ body τ hbody henv
  -- E8 (δ)
  have hconst : ∀ (ls : Levels) (c : CId) (σ : Shape), sig.inst c ls σ →
      ResOk p sig σ (evalConst p k ls c) := by
    intro ls c σ hc
    cases hsig.inst c ls σ hc with
    | body hu ht =>
      rw [evalConst_unfolds hu]
      cases k with
      | zero => exact .inl rfl
      | succ k => exact (ih k (Nat.lt_succ_self k)).term _ _ _ _ _ ht .nil
    | @head h σs τ hof hh =>
      rw [evalConst_head hof, headValue_eq, hh.arity hsig]
      cases σs with
      | nil => exact hfire h ls [] τ [] hh .nil
      | cons a rest =>
        exact .inr ⟨_, rfl, .pap h ls [] (a :: rest) [] (a :: rest) τ _ hh rfl .nil
          (by simp) rfl⟩
    | zero hres hdecl hz =>
      rw [evalConst_eq, hres, hdecl]
      show ResOk p sig .nat (headValue p k ls (.ctor c))
      rw [headValue_eq, headArity_ctor p hdecl]
      show ResOk p sig .nat (fire p k (.ctor c) ls [])
      rw [fire_ctor, hdecl]
      show ResOk p sig .nat ((forceAll p k []).bind (ctorResult p c ls []))
      rw [forceAll_nil]
      refine .inr ⟨.lit 0, ?_, .lit⟩
      show ctorResult p c ls [] [] = .ok (.lit 0)
      simp [ctorResult, hz]
    | @enumCtor I cs hres hI hc' =>
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc'
      obtain ⟨s, lv, ty, hdecl, hz, hs⟩ := hsig.enums _ _ hI i c hi
      rw [evalConst_eq, hres, hdecl]
      show ResOk p sig (.enum I) (headValue p k ls (.ctor c))
      rw [headValue_eq, headArity_ctor p hdecl]
      show ResOk p sig (.enum I) (fire p k (.ctor c) ls [])
      rw [fire_ctor, hdecl]
      show ResOk p sig (.enum I) ((forceAll p k []).bind (ctorResult p c ls []))
      rw [forceAll_nil]
      refine .inr ⟨.con c ls [] [], ?_, .enum hI hc'⟩
      show ctorResult p c ls [] [] = .ok (.con c ls [] [])
      simp [ctorResult, hz, hs]
  -- A1, A2
  have happ : ∀ (f : Value) (s : Slot) (σ τ : Shape), ValOk p sig f (.fn σ τ) → SlotOk p sig s σ →
      ResOk p sig τ (apply p k f s) := by
    intro f s σ τ hf hs
    cases hf with
    | clo hb hρ hbody =>
      rw [apply_clo]
      simp only [hb, ↓reduceIte]
      cases k with
      | zero => exact .inl rfl
      | succ k => exact (ih k (Nat.lt_succ_self k)).term _ _ _ _ _ hbody (.cons hs hρ)
    | pap h ls' args σs done rest τ' σ' hh hσs hargs hrest hσ =>
      cases rest with
      | nil => exact absurd rfl hrest
      | cons σ₁ rest' =>
        simp only [arrows, Shape.fn.injEq] at hσ
        obtain ⟨h1, h2⟩ := hσ
        subst h1
        subst h2
        subst hσs
        have harity := hh.arity hsig
        have hargs' : EnvOk p sig (args ++ [s]) (done ++ [σ]) :=
          EnvOk.append _ _ hargs (.cons hs .nil)
        have hL := EnvOk.length _ _ hargs'
        rw [apply_pap, harity]
        cases rest' with
        | nil =>
          have e1 : ((args ++ [s]).length == (done ++ [σ]).length) = true := beq_iff_eq.2 hL
          simp only [e1, ↓reduceIte]
          exact hfire h ls' (done ++ [σ]) τ' (args ++ [s]) hh hargs'
        | cons σ₂ rest'' =>
          have e1 : ¬ ((args ++ [s]).length == (done ++ σ :: σ₂ :: rest'').length) = true := by
            rw [beq_iff_eq, hL]
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          have e2 : (args ++ [s]).length < (done ++ σ :: σ₂ :: rest'').length := by
            rw [hL]
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          simp only [e1, e2, ↓reduceIte]
          refine .inr ⟨_, rfl, .pap h ls' (args ++ [s]) _ (done ++ [σ]) (σ₂ :: rest'') τ' _ hh ?_
            hargs' (by simp) rfl⟩
          simp
  -- E1 to E7, on the term judgment
  have hterm : ∀ (ls : Levels) (ρ : Env) (Γ : List Shape) (t : Term) (σ : Shape),
      HasShape sig ls Γ t σ → EnvOk p sig ρ Γ → ResOk p sig σ (eval p k ls ρ t) := by
    intro ls ρ Γ t σ ht
    induction ht generalizing ρ with
    | var hi =>
      intro hρ
      obtain ⟨s, hs, hok⟩ := EnvOk.get ρ _ hρ _ _ hi
      rw [eval_var_of p k ls ρ hs]
      exact hslot s _ hok
    | natLit =>
      intro _
      rw [eval_natLit]
      exact .inr ⟨_, rfl, .lit⟩
    | sort =>
      intro _
      rw [eval_sort]
      exact .inr ⟨_, rfl, .irr⟩
    | pi =>
      intro _
      rw [eval_pi]
      exact .inr ⟨_, rfl, .irr⟩
    | const hc =>
      intro _
      rw [eval_const]
      exact hconst _ _ _ hc
    | lam hb hbody _ =>
      intro hρ
      rw [eval_lam]
      exact .inr ⟨_, rfl, .clo hb hρ hbody⟩
    | @app Γ f a m r σ τ hr hf ha ihf iha =>
      intro hρ
      rw [eval_app, hr]
      rcases ihf ρ hρ with hfv | ⟨fv, hfv, hfok⟩
      · rw [hfv]
        exact .inl rfl
      · rw [hfv]
        cases m with
        | strict =>
          show ResOk p sig τ ((eval p k ls ρ a).bind fun x => apply p k fv (.val x))
          rcases iha ρ hρ with hav | ⟨av, hav, haok⟩
          · rw [hav]
            exact .inl rfl
          · rw [hav]
            exact happ fv (.val av) _ _ hfok (.val haok)
        | byName =>
          show ResOk p sig τ (apply p k fv (.name a ρ ls))
          exact happ fv (.name a ρ ls) _ _ hfok (.name hρ ha)
    | @appIrr Γ f a m r τ hr hf ihf =>
      intro hρ
      rw [eval_app, hr]
      rcases ihf ρ hρ with hfv | ⟨fv, hfv, hfok⟩
      · rw [hfv]
        exact .inl rfl
      · rw [hfv]
        show ResOk p sig τ (apply p k fv (.val (.irr (some a) ρ ls)))
        exact happ fv _ _ _ hfok (.val .irr)
    | @letE Γ nonDep lm r ty v body σ τ hr hv hbody ihv ihb =>
      intro hρ
      rw [eval_letE, hr]
      show ResOk p sig τ ((eval p k ls ρ v).bind fun x => eval p k ls (.val x :: ρ) body)
      rcases ihv ρ hρ with h1 | ⟨x, h1, hx⟩
      · rw [h1]
        exact .inl rfl
      · rw [h1]
        exact ihb _ (.cons (.val hx) hρ)
    | @letIrr Γ nonDep lm r ty v body τ hr hbody ihb =>
      intro hρ
      rw [eval_letE, hr]
      show ResOk p sig τ (eval p k ls (.val (.irr (some v) ρ ls) :: ρ) body)
      exact ihb _ (.cons (.val .irr) hρ)
    | @proj Γ s i e d D c fl σ he hD hst hind hctors hi ihe =>
      intro hρ
      rw [eval_proj]
      rcases ihe ρ hρ with h1 | ⟨v, h1, hv⟩
      · rw [h1]
        exact .inl rfl
      · rw [h1]
        show ResOk p sig σ (p.projectField s i v)
        obtain ⟨c', ls', ps, fs, D', j, fl', rfl, hD', hc', hps, hfs⟩ := hv.data_inv
        rw [hD] at hD'
        cases hD'
        obtain ⟨s', lv, np', ni', ty', hdecl⟩ := hsig.structs _ _ hD hst c fl hctors
        rw [hctors] at hc'
        cases j with
        | succ j => simp at hc'
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨hcc, hff⟩ := hc'
          subst hcc
          subst hff
          subst hind
          obtain ⟨v', hv', hvok⟩ := ValsOk.get _ _ hfs i σ hi
          refine .inr ⟨v', ?_, hvok⟩
          simp [Program.projectField, hdecl, hv', Result.ofOption]
  exact ⟨hterm, hconst, happ, hslot⟩

/-- **A shaped root on shaped argument values times out or returns a value of its
result shape**: SrcEval's `run` is never stuck and never traps on it. No view, and
no restriction of the arguments to `Nat`. -/
theorem run_ok_vals (hsig : SigOk p sig) {root : CId} (xs : List Value) (Γ : List Shape)
    {ρ : Shape} (hxs : ValsOk p sig xs Γ) (hroot : sig.inst root [] (arrows Γ ρ)) (k : Nat) :
    ResOk p sig ρ (run p k root xs) := by
  have hall := allOk hsig k
  rw [run_eq]
  rcases hall.const [] root _ hroot with hc | ⟨f, hc, hf⟩
  · rw [hc]
    exact .inl rfl
  · rw [hc]
    exact applyAll_ok hall.app _ _ f (ValsOk.toEnv _ _ hxs) hf

/-- **A shaped root on `Nat` arguments times out or returns a value of its result
shape.** -/
theorem run_ok (hsig : SigOk p sig) {root : CId} (ns : List Nat) {ρ : Shape}
    (hroot : sig.inst root [] (arrows (List.replicate ns.length .nat) ρ)) (k : Nat) :
    ResOk p sig ρ (run p k root (ns.map Value.lit)) := by
  have hall := allOk hsig k
  rw [run_eq]
  rcases hall.const [] root _ hroot with hc | ⟨f, hc, hf⟩
  · rw [hc]
    exact .inl rfl
  · rw [hc]
    exact applyAll_ok hall.app _ _ f (envOk_lits ns) hf

/-! ## The discharge -/

/-- The erasure of an enumeration value whose constructor has no universe parameter
does not depend on the levels the value carries. -/
theorem eraseVal_enum_levels (I : IxCC.Lam.Erase.Input) {c : CId} (h : I.lvls c = 0)
    (ls : Levels) :
    IxCC.Lam.Erase.eraseVal I (.con c ls [] []) = IxCC.Lam.Erase.eraseVal I (.con c [] [] []) := by
  have hq : ∀ prof : Profile, Profile.normalize prof 0 = [] := fun _ => rfl
  simp only [IxCC.Lam.Erase.eraseVal, h, hq]

/-- The view at a root read back as `Nat` (or not read back) accepts every value of
shape `nat`. -/
theorem view_nat_ok {f : Recheck.Front} {r : Nat}
    (hty : f.tys r = none ∨ f.tys r = some ({}, .nat)) (v : Value)
    (hv : ValOk f.src sig v .nat) :
    f.view r (Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, v) : Lang.Val CheckedProgram)) ≠ none := by
  obtain ⟨n, rfl⟩ := hv.nat_inv
  exact IxCC.Correct.Shape.view_lit_ne_none hty _ n

/-- The view accepts every value of an enumeration's shape if it accepts each listed
constructor, and none has a universe parameter. Both are decisions on the checker's
data: the view is a function, and there are finitely many constructors. -/
theorem view_enum_ok {f : Recheck.Front} {r : Nat} {B : CId} {cs : List CId}
    (hB : sig.enums B = some cs)
    (hcs : ∀ c, c ∈ cs → (IxCC.Lam.Erase.Input.ofProgram f.src f.checked).lvls c = 0 ∧
      f.view r (Lang.obs (S := CheckedProgram)
        ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, Value.con c [] [] []) :
          Lang.Val CheckedProgram)) ≠ none)
    (v : Value) (hv : ValOk f.src sig v (.enum B)) :
    f.view r (Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, v) : Lang.Val CheckedProgram)) ≠ none := by
  obtain ⟨c, ls, cs', rfl, hB', hc⟩ := hv.enum_inv
  rw [hB] at hB'
  cases hB'
  obtain ⟨hl, hne⟩ := hcs c hc
  have e : Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, Value.con c ls [] []) :
        Lang.Val CheckedProgram) =
      Lang.obs (S := CheckedProgram)
        ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, Value.con c [] [] []) :
          Lang.Val CheckedProgram) := by
    show (IxCC.Lam.Erase.eraseVal _ (Value.con c ls [] [])).bind IxCC.Lam.Erase.Proof.obsV =
      (IxCC.Lam.Erase.eraseVal _ (Value.con c [] [] [])).bind IxCC.Lam.Erase.Proof.obsV
    rw [eraseVal_enum_levels _ hl]
  rw [e]
  exact hne

/-- **M1: `NeverWrong` for a shaped first-order root.** If the checked source agrees
with the signature, root `r` has an instance `Nat → … → Nat → ρ` at no levels with as
many arguments as the input, and the root's view reads back every value of shape `ρ`,
then the viewed source goes wrong at no clock: `Front.GoesWrong` is false of the
input. -/
theorem neverWrong_of_shape {f : Recheck.Front} (hsig : SigOk f.src sig) {r : Nat}
    {addr : Ixon.Address} {c : CId} (hroot : f.src.roots[r]? = some (addr, c)) (ns : List Nat)
    {ρ : Shape} (hc : sig.inst c [] (arrows (List.replicate ns.length .nat) ρ))
    (hview : ∀ v, ValOk f.src sig v ρ → f.view r (Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram f.src f.checked, v) : Lang.Val CheckedProgram)) ≠ none) :
    NeverWrong f.source (r, ns) := by
  rw [neverWrong_iff]
  intro k
  have e : Lang.run f.source.prog (r, ns) k =
      IxCC.Lam.Erase.Proof.srcRun ⟨f.src, f.checked⟩ (r, ns) k := rfl
  unfold IxCC.Lam.Erase.Proof.srcRun at e
  simp only [hroot] at e
  rcases run_ok hsig ns hc k with hr | ⟨v, hr, hv⟩
  · rw [hr] at e
    constructor
    · rw [e]
      intro hw
      exact hw
    · intro v hv
      rw [e] at hv
      cases hv
  · rw [hr] at e
    constructor
    · rw [e]
      intro hw
      exact hw
    · intro v' hv'
      rw [e] at hv'
      cases hv'
      exact hview v hv

/-- **M1 at the object**: `Recheck.sound` for a shaped first-order root, with no
"source goes wrong" case. -/
theorem recheck_sound_of_shape {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a) (hsig : SigOk a.src sig) {r : Nat}
    {addr : Ixon.Address} {root : CId} (hroot : a.src.roots[r]? = some (addr, root))
    (ns : List Nat) {ρ : Shape}
    (hc : sig.inst root [] (arrows (List.replicate ns.length .nat) ρ))
    (hview : ∀ v, ValOk a.src sig v ρ → a.front.view r (Lang.obs (S := CheckedProgram)
      ((IxCC.Lam.Erase.Input.ofProgram a.src a.checked, v) : Lang.Val CheckedProgram)) ≠ none)
    (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size) (hi : a.front.Covered c (r, ns)) :
    (∀ k w, Lang.run (a.linked D) (r, ns) k = .ok w →
      ∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) (r, ns) k' = .ok v ∧
        a.front.view r (Lang.obs v) = some w) ∧
    (∀ k, ¬ (Lang.run (a.linked D) (r, ns) k).GoesWrong) :=
  recheck_sound_of_neverWrong h D hD (r, ns) hi
    (neverWrong_of_shape (f := a.front) hsig hroot ns hc hview)

end IxCC.Correct.Shape2
