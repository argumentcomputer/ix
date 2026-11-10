import IxCC.Anf.Convert
import IxCC.Anf.Proof.Mono
import IxCC.Lam.Proof.ModesOk
import IxCC.Lam.Proof.Spine
import IxCC.Sem.Dominance

/-! # ANF conversion: the value relation

The relation that ANF conversion's simulation (P1) keeps between Lam
values, slots and environments and Anf values (for the
Lam → Anf instance). Lam and Anf both use depth clocks, so a value computed
one clock down is used at the full clock; the relation on values is
therefore not clock-indexed (as in the erasure proof): a closure is
related through the *code* conversion produced for its body, under related
environments, and the simulation itself is clock-indexed (`Sem.SimUpTo`)
and proved by strong induction on the clock bound.

* `VR v w` relates *plain* values: literals, □, constructors of related
  fields, and closures whose remaining binders are strict. Every value a
  `ModesOk` term evaluates to is plain.
* `CloR tk j v w`: a Lam closure of a λ-telescope `lamsWith ps body` with
  `j` argument slots supplied, against the Anf closure of arity
  `ps.length` that conversion built for it (a local `fn` or a global's
  parameters), with `j` related arguments; `tk` are the binders' kinds
  (`name` binders hold thunks, with their dispatch signatures).
* `SlotR q s w`: a value slot holds a related plain value; a `name` slot
  is related to the thunk closure `fn [_] t'` conversion built for its term
  (`ThunkR`), whose term is well moded at the binder's signature.
* `EnvR kinds vars ρ ρt`: each Lam variable's slot against the value of its
  target operand (`Opd.val`, a level counted from the outside of `ρt`). -/

set_option autoImplicit false

namespace IxCC.Anf

/-- The value of a target operand in a target environment: a level counts
from the outside, so it keeps its value when the environment grows. -/
def Opd.val (ρ : List Val) : Opd → Option Val
  | .lvl l => if l < ρ.length then ρ[ρ.length - 1 - l]? else none
  | .lit l => some (.lit l)
  | .box => some .box

theorem Opd.val_atom {ρ : List Val} {o : Opd} {w : Val} (h : o.val ρ = some w) :
    (o.atom ρ.length).eval ρ = some w := by
  cases o with
  | lvl l =>
    simp only [Opd.val] at h
    split at h
    · simpa [Opd.atom, Atom.eval] using h
    · cases h
  | lit l => simpa [Opd.val, Opd.atom, Atom.eval] using h
  | box => simpa [Opd.val, Opd.atom, Atom.eval] using h

theorem Opd.val_append {ρ : List Val} (ext : List Val) {o : Opd} {w : Val} (h : o.val ρ = some w) :
    o.val (ext ++ ρ) = some w := by
  cases o with
  | lvl l =>
    simp only [Opd.val] at h ⊢
    split at h
    · next hl =>
      have hl' : l < (ext ++ ρ).length := by simp; omega
      rw [if_pos hl']
      rw [List.getElem?_append_right (by simp; omega)]
      have : (ext ++ ρ).length - 1 - l - ext.length = ρ.length - 1 - l := by simp; omega
      rw [this]; exact h
    · cases h
  | lit l => exact h
  | box => exact h

theorem Opd.val_suffix {ρ ρ' : List Val} (hs : ρ <:+ ρ') {o : Opd} {w : Val}
    (h : o.val ρ = some w) : o.val ρ' = some w := by
  obtain ⟨ext, rfl⟩ := hs
  exact Opd.val_append ext h

theorem Opd.val_lvl_top (ρ : List Val) (w : Val) : (Opd.lvl ρ.length).val (w :: ρ) = some w := by
  simp [Opd.val]

end IxCC.Anf

namespace IxCC.Lam

/-- Whether a variable of this kind holds a thunk. -/
def Kind.isName : Kind → Bool
  | .strict => false
  | .name _ => true

end IxCC.Lam

namespace IxCC.Anf.Convert.Proof

open IxCC.Sem (Result ClockMono SimUpTo)
open IxCC.Lam (Kind Mode)
open IxCC.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName)
open IxCC.Ixon

/-- A λ-telescope with the given binders over `body`. -/
def lamsWith : List (Mode × V3.BinderContract) → Lam.Term → Lam.Term
  | [], b => b
  | (m, c) :: ps, b => .lam m c (lamsWith ps b)

/-- A term that is not a λ (the body of a maximal telescope). -/
def NotLam : Lam.Term → Prop
  | .lam .. => False
  | _ => True

/-- Binder modes and kinds agree: `name` binders, and only they, hold
thunks. -/
def ModesAgree (ps : List (Mode × V3.BinderContract)) (tk : List Kind) : Prop :=
  ps.length = tk.length ∧
    ∀ (i : Nat) (p : Mode × V3.BinderContract) (q : Kind), ps[i]? = some p → tk[i]? = some q →
      (p.1 == Mode.name) = q.isName

variable (A : Arities) (G : Src.NatMap Lam.ModesOk.GInfo)

mutual

/-- Plain values (see the module comment). -/
inductive VR : Lam.Val → Val → Prop
  | lit {l : Lam.Lit} : VR (.lit l) (.lit l)
  | box : VR .box .box
  | con {c : Key.CtorKey} {fs : List Lam.Val} {ws : List Val} : VRs fs ws → VR (.con c fs) (.con c ws)
  | clo {tk : List Kind} {j : Nat} {v : Lam.Val} {w : Val} :
      CloR tk j v w → (∀ q ∈ tk.drop j, q = .strict) → VR v w

inductive VRs : List Lam.Val → List Val → Prop
  | nil : VRs [] []
  | cons {v : Lam.Val} {vs : List Lam.Val} {w : Val} {ws : List Val} :
      VR v w → VRs vs ws → VRs (v :: vs) (w :: ws)

/-- A Lam closure of a telescope with `j` slots supplied, against the Anf
closure conversion built for it. -/
inductive CloR : List Kind → Nat → Lam.Val → Val → Prop
  | mk {ps : List (Mode × V3.BinderContract)} {body : Lam.Term} {tk : List Kind}
      {ρ0 : Lam.Env} {k0 : List Kind} {vars0 : List VarInfo} {ρt : List Val}
      {ss : List Lam.Slot} {got : List Val} {fuel : Nat} {bt : Exp} {j : Nat} {v : Lam.Val}
      {w : Val} :
      NotLam body → ModesAgree ps tk → ss.length < ps.length →
      EnvR k0 vars0 ρ0 ρt → SlotsR tk ss got →
      conv A fuel { vars := pushParams vars0 ρt.length (ps.map (·.1 == .name)),
                    d := ρt.length + ps.length, dj := 0 } body .ret = .ok bt →
      TermOk G (tk.reverse ++ k0) body →
      j = ss.length →
      v = .clos (ss.reverse ++ ρ0) (lamsWith (ps.drop (ss.length + 1)) body) →
      w = .clos ρt ps.length bt got →
      CloR tk j v w

/-- Supplied argument slots against values, by the binders' kinds (a prefix
of `tk`). -/
inductive SlotsR : List Kind → List Lam.Slot → List Val → Prop
  | nil {tk : List Kind} : SlotsR tk [] []
  | cons {q : Kind} {tk : List Kind} {s : Lam.Slot} {ss : List Lam.Slot} {w : Val}
      {ws : List Val} : SlotR q s w → SlotsR tk ss ws → SlotsR (q :: tk) (s :: ss) (w :: ws)

inductive SlotR : Kind → Lam.Slot → Val → Prop
  | val {v : Lam.Val} {w : Val} : VR v w → SlotR .strict (.val v) w
  | name {sig : List Mode} {ρs : Lam.Env} {ts : Lam.Term} {w : Val} :
      ThunkR sig ρs ts w → SlotR (.name sig) (.name ρs ts) w

/-- A Lam thunk against the thunk closure `fn [_] t'` of its conversion. -/
inductive ThunkR : List Mode → Lam.Env → Lam.Term → Val → Prop
  | mk {sig : List Mode} {ρs : Lam.Env} {ts : Lam.Term} {k0 : List Kind} {vars0 : List VarInfo}
      {ρt : List Val} {fuel : Nat} {bt : Exp} {w : Val} :
      EnvR k0 vars0 ρs ρt →
      conv A fuel { vars := vars0, d := ρt.length + 1, dj := 0 } ts .ret = .ok bt →
      NameArgOk G k0 sig ts → w = .clos ρt 1 bt [] → ThunkR sig ρs ts w

/-- A Lam environment against a target environment, through the variables'
operands. -/
inductive EnvR : List Kind → List VarInfo → Lam.Env → List Val → Prop
  | nil {ρt : List Val} : EnvR [] [] [] ρt
  | cons {q : Kind} {ks : List Kind} {vi : VarInfo} {vars : List VarInfo} {s : Lam.Slot}
      {ρ : Lam.Env} {ρt : List Val} {w : Val} :
      vi.thunk = q.isName → vi.opd.val ρt = some w → SlotR q s w → EnvR ks vars ρ ρt →
      EnvR (q :: ks) (vi :: vars) (s :: ρ) ρt

end

end IxCC.Anf.Convert.Proof
