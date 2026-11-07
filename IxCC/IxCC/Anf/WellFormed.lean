import IxCC.Anf.Syntax

/-! # Anf well-scopedness

`Anf.WellScoped P` (design note 02 §6.2), decided by `wellScoped` with an
iff lemma. `Exp.WS S Γ Δ e` holds when every value variable of `e` is below
the value depth `Γ`; every jump targets a join point of `Δ` (the arities of
the join points in scope, innermost first) with that many arguments; `call`s
name a global of their arity (at least one); `con` arities, `case`
alternative arities and `proj` indices come from the constructor table;
primitives are saturated; the keys of a `case` are distinct; an `fn` has at
least one parameter and a body over its captured depth plus its parameters,
with no join point in scope. Jumps are in tail position by construction
(they are expressions, and `fn` bodies start with an empty join context).

A program is well scoped when every global `0 … size - 1` is present with a
body over its parameters, keys are pairwise distinct (D19), the constructor
table has distinct keys, roots are in range and the pinned keys have their
arities. `FirstOrder` (no `fn`, no `app`, no `glob` of a function global) is
what the Anf → Fir boundary accepts in Phase 1 (02 §8). -/

namespace IxCC.Anf

/-- What scoping reads from a program. -/
structure Sig where
  size : Nat
  arity? : GlobalId → Option Nat
  ctorArity? : Key.CtorKey → Option Nat

def Program.sig (P : Program) : Sig :=
  { size := P.size, arity? := P.arity?, ctorArity? := fun c => (P.ctor? c).map (·.arity) }

namespace Atom

def ws (Γ : Nat) : Atom → Bool
  | .var i => decide (i < Γ)
  | _ => true

def WS (Γ : Nat) : Atom → Prop
  | .var i => i < Γ
  | _ => True

theorem ws_iff (Γ : Nat) (a : Atom) : a.ws Γ = true ↔ a.WS Γ := by
  cases a <;> simp [ws, WS]

def wsList (Γ : Nat) : List Atom → Bool
  | [] => true
  | a :: as => a.ws Γ && wsList Γ as

def WSList (Γ : Nat) : List Atom → Prop
  | [] => True
  | a :: as => a.WS Γ ∧ WSList Γ as

theorem wsList_iff (Γ : Nat) : ∀ as : List Atom, wsList Γ as = true ↔ WSList Γ as
  | [] => by simp [wsList, WSList]
  | a :: as => by simp [wsList, WSList, ws_iff, wsList_iff Γ as]

end Atom

/-- Whether index `i` is below a constructor's arity. -/
def projOk (S : Sig) (c : Key.CtorKey) (i : Nat) : Bool :=
  match S.ctorArity? c with
  | some n => decide (i < n)
  | none => false

/-- The keys of a list of alternatives. -/
def altKeys : List Alt → List Key.CtorKey
  | [] => []
  | .mk key _ _ :: as => key :: altKeys as

mutual

def Bind.ws (S : Sig) (Γ : Nat) : Bind → Bool
  | .atom a => a.ws Γ
  | .con c as => decide (S.ctorArity? c = some as.length) && Atom.wsList Γ as
  | .proj c i x => projOk S c i && x.ws Γ
  | .prim p as => decide (as.length = p.arity) && Atom.wsList Γ as
  | .glob g => decide (g < S.size)
  | .call g as => decide (S.arity? g = some as.length) && decide (as ≠ []) && Atom.wsList Γ as
  | .app f as => f.ws Γ && decide (as ≠ []) && Atom.wsList Γ as
  | .fn ps b => decide (ps ≠ []) && Exp.ws S (Γ + ps.length) [] b

/-- Scope of an expression under value depth `Γ` and join arities `Δ`. -/
def Exp.ws (S : Sig) (Γ : Nat) (Δ : List Nat) : Exp → Bool
  | .bind _ b e => b.ws S Γ && Exp.ws S (Γ + 1) Δ e
  | .join n r b e => Exp.ws S (Γ + n) (if r then n :: Δ else Δ) b && Exp.ws S Γ (n :: Δ) e
  | .jump j as => decide (Δ[j]? = some as.length) && Atom.wsList Γ as
  | .case x alts d =>
    x.ws Γ && Exp.altsWs S Γ Δ alts && decide (altKeys alts).Nodup && Exp.optWs S Γ Δ d
  | .ret a => a.ws Γ
  | .tick e => Exp.ws S Γ Δ e
  | .trap => true

def Exp.altsWs (S : Sig) (Γ : Nat) (Δ : List Nat) : List Alt → Bool
  | [] => true
  | .mk key n b :: as =>
    decide (S.ctorArity? key = some n) && Exp.ws S (Γ + n) Δ b && Exp.altsWs S Γ Δ as

def Exp.optWs (S : Sig) (Γ : Nat) (Δ : List Nat) : Option Exp → Bool
  | none => true
  | some e => Exp.ws S Γ Δ e

end

mutual

def Bind.WS (S : Sig) (Γ : Nat) : Bind → Prop
  | .atom a => a.WS Γ
  | .con c as => S.ctorArity? c = some as.length ∧ Atom.WSList Γ as
  | .proj c i x => projOk S c i = true ∧ x.WS Γ
  | .prim p as => as.length = p.arity ∧ Atom.WSList Γ as
  | .glob g => g < S.size
  | .call g as => S.arity? g = some as.length ∧ as ≠ [] ∧ Atom.WSList Γ as
  | .app f as => f.WS Γ ∧ as ≠ [] ∧ Atom.WSList Γ as
  | .fn ps b => ps ≠ [] ∧ Exp.WS S (Γ + ps.length) [] b

/-- `WellScoped Γ Δ e` (02 §6.2). -/
def Exp.WS (S : Sig) (Γ : Nat) (Δ : List Nat) : Exp → Prop
  | .bind _ b e => b.WS S Γ ∧ Exp.WS S (Γ + 1) Δ e
  | .join n r b e => Exp.WS S (Γ + n) (if r then n :: Δ else Δ) b ∧ Exp.WS S Γ (n :: Δ) e
  | .jump j as => Δ[j]? = some as.length ∧ Atom.WSList Γ as
  | .case x alts d =>
    x.WS Γ ∧ Exp.AltsWS S Γ Δ alts ∧ (altKeys alts).Nodup ∧ Exp.OptWS S Γ Δ d
  | .ret a => a.WS Γ
  | .tick e => Exp.WS S Γ Δ e
  | .trap => True

def Exp.AltsWS (S : Sig) (Γ : Nat) (Δ : List Nat) : List Alt → Prop
  | [] => True
  | .mk key n b :: as => S.ctorArity? key = some n ∧ Exp.WS S (Γ + n) Δ b ∧ Exp.AltsWS S Γ Δ as

def Exp.OptWS (S : Sig) (Γ : Nat) (Δ : List Nat) : Option Exp → Prop
  | none => True
  | some e => Exp.WS S Γ Δ e

end

mutual

theorem Bind.ws_iff (S : Sig) : ∀ (Γ : Nat) (b : Bind), b.ws S Γ = true ↔ b.WS S Γ
  | Γ, .atom a => by simp [Bind.ws, Bind.WS, Atom.ws_iff]
  | Γ, .con c as => by simp [Bind.ws, Bind.WS, Atom.wsList_iff]
  | Γ, .proj c i x => by simp [Bind.ws, Bind.WS, Atom.ws_iff]
  | Γ, .prim p as => by simp [Bind.ws, Bind.WS, Atom.wsList_iff]
  | Γ, .glob g => by simp [Bind.ws, Bind.WS]
  | Γ, .call g as => by simp [Bind.ws, Bind.WS, Atom.wsList_iff, and_assoc]
  | Γ, .app f as => by simp [Bind.ws, Bind.WS, Atom.ws_iff, Atom.wsList_iff, and_assoc]
  | Γ, .fn ps b => by simp [Bind.ws, Bind.WS, Exp.ws_iff S (Γ + ps.length) [] b]

theorem Exp.ws_iff (S : Sig) : ∀ (Γ : Nat) (Δ : List Nat) (e : Exp), e.ws S Γ Δ = true ↔ e.WS S Γ Δ
  | Γ, Δ, .bind _ b e => by
    simp [Exp.ws, Exp.WS, Bind.ws_iff S Γ b, Exp.ws_iff S (Γ + 1) Δ e]
  | Γ, Δ, .join n r b e => by
    simp [Exp.ws, Exp.WS, Exp.ws_iff S (Γ + n) (if r then n :: Δ else Δ) b,
      Exp.ws_iff S Γ (n :: Δ) e]
  | Γ, Δ, .jump j as => by simp [Exp.ws, Exp.WS, Atom.wsList_iff]
  | Γ, Δ, .case x alts d => by
    simp [Exp.ws, Exp.WS, Atom.ws_iff, Exp.altsWs_iff S Γ Δ alts, Exp.optWs_iff S Γ Δ d,
      and_assoc]
  | Γ, Δ, .ret a => by simp [Exp.ws, Exp.WS, Atom.ws_iff]
  | Γ, Δ, .tick e => by simp only [Exp.ws, Exp.WS]; exact Exp.ws_iff S Γ Δ e
  | Γ, Δ, .trap => by simp [Exp.ws, Exp.WS]

theorem Exp.altsWs_iff (S : Sig) :
    ∀ (Γ : Nat) (Δ : List Nat) (as : List Alt), Exp.altsWs S Γ Δ as = true ↔ Exp.AltsWS S Γ Δ as
  | _, _, [] => by simp [Exp.altsWs, Exp.AltsWS]
  | Γ, Δ, .mk key n b :: as => by
    simp [Exp.altsWs, Exp.AltsWS, Exp.ws_iff S (Γ + n) Δ b, Exp.altsWs_iff S Γ Δ as, and_assoc]

theorem Exp.optWs_iff (S : Sig) :
    ∀ (Γ : Nat) (Δ : List Nat) (d : Option Exp), Exp.optWs S Γ Δ d = true ↔ Exp.OptWS S Γ Δ d
  | _, _, none => by simp [Exp.optWs, Exp.OptWS]
  | Γ, Δ, some e => by simp only [Exp.optWs, Exp.OptWS]; exact Exp.ws_iff S Γ Δ e

end

/-- The pinned keys have the arities `Nat` peeling and Boolean primitives
produce, wherever the table lists them. -/
def knownConsistent (K : Lam.Known) (S : Sig) : Bool :=
  let ok := fun (c : Option Key.CtorKey) (n : Nat) => match c with
    | some c => (S.ctorArity? c).all (· == n)
    | none => true
  ok K.natZero 0 && ok K.natSucc 1 && ok K.boolFalse 0 && ok K.boolTrue 0

/-- Decide well-scopedness of a program. -/
def wellScoped (P : Program) : Bool :=
  (List.range P.size).all (fun g => match P.global? g with
    | some gd => gd.body.ws P.sig gd.ps.length []
    | none => false) &&
  decide ((P.globalList.map (·.2.key)).Nodup) &&
  decide ((P.ctors.map (·.key)).Nodup) &&
  P.roots.all (· < P.size) &&
  knownConsistent P.known P.sig

structure WellScoped (P : Program) : Prop where
  globals : ∀ g, g < P.size → ∃ gd, P.global? g = some gd ∧ gd.body.WS P.sig gd.ps.length []
  keys : (P.globalList.map (·.2.key)).Nodup
  ctorKeys : (P.ctors.map (·.key)).Nodup
  roots : ∀ r ∈ P.roots, r < P.size
  known : knownConsistent P.known P.sig = true

theorem wellScoped_iff (P : Program) : wellScoped P = true ↔ WellScoped P := by
  constructor
  · intro h
    simp only [wellScoped, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hg, hk⟩, hc⟩, hr⟩, hkn⟩ := h
    refine ⟨fun g hlt => ?_, hk, hc, fun r hr' => by simpa using hr r hr', hkn⟩
    have := hg g hlt
    split at this
    · next gd hgd => exact ⟨gd, hgd, (Exp.ws_iff _ _ _ _).mp this⟩
    · cases this
  · intro ⟨hg, hk, hc, hr, hkn⟩
    simp only [wellScoped, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq]
    refine ⟨⟨⟨⟨fun g hlt => ?_, hk⟩, hc⟩, fun r hr' => by simpa using hr r hr'⟩, hkn⟩
    obtain ⟨gd, hgd, hws⟩ := hg g hlt
    simp [hgd, (Exp.ws_iff _ _ _ _).mpr hws]

instance (P : Program) : Decidable (WellScoped P) :=
  decidable_of_iff _ (wellScoped_iff P)

/-- The first global that is missing or not well scoped, for diagnostics. -/
def firstIllScoped (P : Program) : Option GlobalId :=
  (List.range P.size).find? fun g => match P.global? g with
    | some gd => !gd.body.ws P.sig gd.ps.length []
    | none => true

/-! ## First order (P8's output; Phase 1's Anf → Fir boundary) -/

mutual

/-- No `fn`, no `app`, no `glob` of a function global (`isFn g`). -/
def Exp.firstOrder (isFn : GlobalId → Bool) : Exp → Bool
  | .bind _ b e => Bind.firstOrder isFn b && Exp.firstOrder isFn e
  | .join _ _ b e => Exp.firstOrder isFn b && Exp.firstOrder isFn e
  | .jump .. | .ret _ | .trap => true
  | .case _ alts d => Exp.altsFirstOrder isFn alts && Exp.optFirstOrder isFn d
  | .tick e => Exp.firstOrder isFn e

def Bind.firstOrder (isFn : GlobalId → Bool) : Bind → Bool
  | .fn .. | .app .. => false
  | .glob g => !isFn g
  | _ => true

def Exp.altsFirstOrder (isFn : GlobalId → Bool) : List Alt → Bool
  | [] => true
  | .mk _ _ b :: as => Exp.firstOrder isFn b && Exp.altsFirstOrder isFn as

def Exp.optFirstOrder (isFn : GlobalId → Bool) : Option Exp → Bool
  | none => true
  | some e => Exp.firstOrder isFn e

end

def firstOrder (P : Program) : Bool :=
  let isFn := fun g => (P.arity? g).any (· > 0)
  P.globalList.all fun (_, gd) => gd.body.firstOrder isFn

/-- `Anf.FirstOrder` (02 §6.1): P8's output, and the fragment Phase 1's Fir
accepts. -/
def FirstOrder (P : Program) : Prop := firstOrder P = true

instance (P : Program) : Decidable (FirstOrder P) := inferInstanceAs (Decidable (_ = true))

end IxCC.Anf
