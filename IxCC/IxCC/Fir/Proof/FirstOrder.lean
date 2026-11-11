import IxCC.Fir.Lower
import IxCC.Fir.Proof.Lowering

/-! # `Fir.lower` declines no first-order program for closures

`Fir.Proof.lower_firstOrder`: on an `Anf.FirstOrder` program (no `fn`, no
`app`, no `glob` of a global with parameters), `Fir.lower` never refuses with
`fir.closures`; its other refusals (`malformed`, `missing`, `pins`) are about
scope, arities and pinned keys. With `Anf.Defun.Proof.run_firstOrder` this is
what lets P8's output past the Anf → Fir boundary. The decline set
(`Lower.residual`) of a first-order program is empty (`residual_empty`), and
the conversion's own `closures` cases, `app`, `fn` and the value of a
function global, are the forms `FirstOrder` excludes (`exp_noClo`).
Conversely, a program `Fir.lower` accepts is first order
(`lower_ok_firstOrder`): an empty decline set means no residual form. -/

set_option autoImplicit false

namespace IxCC.Fir.Proof

open IxCC.Fir.Lower

/-- A `closures` refusal. -/
def Error.isClosures : Lower.Error → Bool
  | .closures .. => true
  | _ => false

/-- A computation that refuses with no `closures` error. -/
def NoClo {α : Type} (x : Except Lower.Error α) : Prop := ∀ e, x = .error e → Error.isClosures e = false

theorem noClo_ok {α : Type} (a : α) : NoClo (Except.ok a : Except Lower.Error α) := by
  intro e he
  cases he

theorem noClo_pure {α : Type} (a : α) : NoClo (pure a : Except Lower.Error α) := noClo_ok a

theorem noClo_error {α : Type} {e : Lower.Error} (h : Error.isClosures e = false) :
    NoClo (Except.error e : Except Lower.Error α) := by
  intro e' he
  cases he
  exact h

theorem noClo_throw {α : Type} {e : Lower.Error} (h : Error.isClosures e = false) :
    NoClo (throw e : Except Lower.Error α) := noClo_error h

theorem noClo_bind {α β : Type} {x : Except Lower.Error α} {f : α → Except Lower.Error β}
    (hx : NoClo x) (hf : ∀ a, NoClo (f a)) : NoClo (x >>= f) := by
  intro e he
  cases hxe : x with
  | error e' =>
    rw [hxe] at he
    cases he
    exact hx _ hxe
  | ok a =>
    rw [hxe] at he
    exact hf a e he

set_option hygiene false in
/-- The steps of a conversion case: binds, results, refusals other than
`closures`, the atom conversions, the induction hypotheses `ih1`–`ih3`, and
`if`/`match` by cases, on every goal until none progresses. Unhygienic, so
that `ih1`–`ih3` are the proof's own hypotheses. -/
macro "noclo" : tactic => `(tactic| repeat (any_goals (first
  | exact noClo_pure _
  | exact noClo_ok _
  | exact noClo_throw rfl
  | exact noClo_error rfl
  | exact noClo_atoms _ _ _
  | exact noClo_atom _ _ _
  | exact noClo_atomVar _ _ _ _
  | exact ih1 _ _ _
  | exact ih2 _ _ _
  | exact ih3 _ _ _ _
  | (refine noClo_bind ?_ (fun _ => ?_))
  | split
  | (dsimp only))))

theorem noClo_atom (g : Anf.GlobalId) (ρ : List Var) (a : Anf.Atom) : NoClo (atom g ρ a) := by
  cases a <;> simp only [atom] <;> noclo

theorem noClo_atoms (g : Anf.GlobalId) (ρ : List Var) : ∀ as : List Anf.Atom, NoClo (atoms g ρ as)
  | [] => noClo_pure _
  | a :: as => by
    simp only [atoms]
    exact noClo_bind (noClo_atom g ρ a) fun _ => noClo_bind (noClo_atoms g ρ as) fun _ => noClo_pure _

theorem noClo_atomVar (g : Anf.GlobalId) (ρ : List Var) (st : St) (a : Anf.Atom) :
    NoClo (atomVar g ρ st a) := by
  cases a <;> simp only [atomVar] <;> noclo

/-- The output's `isFn`. -/
abbrev isFnOf (A : Anf.Program) (g : Anf.GlobalId) : Bool := (A.arity? g).any (· > 0)

mutual

theorem exp_noClo (A : Anf.Program) (g : Anf.GlobalId) :
    ∀ (e : Anf.Exp), Anf.Exp.firstOrder (isFnOf A) e = true →
      ∀ (ρ : List Var) (J : List JoinId) (st : St), NoClo (Lower.exp A g ρ J st e)
  | .bind c b e, hfo, ρ, J, st => by
    simp only [Anf.Exp.firstOrder, Bool.and_eq_true] at hfo
    have ih1 := exp_noClo A g e hfo.2
    cases b with
    | glob h =>
      have hcaf : ∀ hd, A.global? h = some hd → hd.ps.isEmpty = true := by
        intro hd hg
        have hf := hfo.1
        cases hps : hd.ps with
        | nil => simp
        | cons p ps => simp [Anf.Bind.firstOrder, isFnOf, Anf.Program.arity?, hg, Anf.GDef.arity, hps] at hf
      simp only [Lower.exp]
      noclo
      all_goals (exfalso; simp_all)
    | app f as => simp [Anf.Bind.firstOrder] at hfo
    | fn ps b => simp [Anf.Bind.firstOrder] at hfo
    | atom a => simp only [Lower.exp]; noclo
    | con k as => simp only [Lower.exp]; noclo
    | proj k i a => simp only [Lower.exp]; noclo
    | prim p as => simp only [Lower.exp]; noclo
    | call h as => simp only [Lower.exp]; noclo
  | .join n r b e, hfo, ρ, J, st => by
    simp only [Anf.Exp.firstOrder, Bool.and_eq_true] at hfo
    have ih1 := exp_noClo A g b hfo.1
    have ih2 := exp_noClo A g e hfo.2
    simp only [Lower.exp]
    noclo
  | .jump j as, _, ρ, J, st => by
    simp only [Lower.exp]
    noclo
  | .case x alts d, hfo, ρ, J, st => by
    simp only [Anf.Exp.firstOrder, Bool.and_eq_true] at hfo
    have ih3 := exps_noClo A g alts hfo.1
    have ih2 := opt_noClo A g d hfo.2
    simp only [Lower.exp]
    noclo
  | .ret a, _, ρ, J, st => by
    simp only [Lower.exp]
    noclo
  | .tick e, hfo, ρ, J, st => by
    simp only [Anf.Exp.firstOrder] at hfo
    simp only [Lower.exp]
    exact exp_noClo A g e hfo ρ J st
  | .trap, _, ρ, J, st => by
    simp only [Lower.exp]
    noclo

theorem exps_noClo (A : Anf.Program) (g : Anf.GlobalId) :
    ∀ (alts : List Anf.Alt), Anf.Exp.altsFirstOrder (isFnOf A) alts = true →
      ∀ (ρ : List Var) (J : List JoinId) (y : Var) (st : St), NoClo (Lower.exps A g ρ J y st alts)
  | [], _, ρ, J, y, st => by
    simp only [Lower.exps]
    noclo
  | .mk k n b :: as, hfo, ρ, J, y, st => by
    simp only [Anf.Exp.altsFirstOrder, Bool.and_eq_true] at hfo
    have ih1 := exp_noClo A g b hfo.1
    have ih3 := exps_noClo A g as hfo.2
    simp only [Lower.exps]
    noclo

theorem opt_noClo (A : Anf.Program) (g : Anf.GlobalId) :
    ∀ (d : Option Anf.Exp), Anf.Exp.optFirstOrder (isFnOf A) d = true →
      ∀ (ρ : List Var) (J : List JoinId) (st : St), NoClo (Lower.opt A g ρ J st d)
  | none, _, ρ, J, st => by
    simp only [Lower.opt]
    noclo
  | some e, hfo, ρ, J, st => by
    simp only [Anf.Exp.optFirstOrder] at hfo
    have ih1 := exp_noClo A g e hfo
    simp only [Lower.opt]
    noclo

end

theorem mem_globalList {P : Anf.Program} {g : Anf.GlobalId} {gd : Anf.GDef} :
    (g, gd) ∈ P.globalList ↔ g < P.size ∧ P.global? g = some gd := by
  unfold Anf.Program.globalList
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨g', hg', gd', hgd, rfl, rfl⟩
    exact ⟨hg', hgd⟩
  · rintro ⟨hg, hgd⟩
    exact ⟨g, hg, gd, hgd, rfl, rfl⟩

theorem functions_noClo (A : Anf.Program)
    (hfo : ∀ g gd, g < A.size → A.global? g = some gd → Anf.Exp.firstOrder (isFnOf A) gd.body = true) :
    ∀ gs : List Anf.GlobalId, (∀ g ∈ gs, g < A.size) → NoClo (Lower.functions A gs)
  | [], _ => by simp only [Lower.functions]; exact noClo_pure _
  | g :: gs, hlt => by
    have ih := functions_noClo A hfo gs fun g' hg' => hlt g' (List.mem_cons_of_mem _ hg')
    simp only [Lower.functions]
    split
    · next gd hgd =>
      have ih1 := fun ρ J st => exp_noClo A g gd.body (hfo g gd (hlt g List.mem_cons_self) hgd) ρ J st
      refine noClo_bind ?_ fun _ => noClo_bind ih fun _ => noClo_pure _
      simp only [Lower.function]
      noclo
    · exact noClo_throw rfl

mutual

theorem countExp_fo (isFn : Anf.GlobalId → Bool) :
    ∀ e : Anf.Exp, Anf.Exp.firstOrder isFn e = true →
      (countExp isFn e).fns = 0 ∧ (countExp isFn e).apps = 0 ∧ (countExp isFn e).globs = 0
  | .bind _ b e, h => by
    simp only [Anf.Exp.firstOrder, Bool.and_eq_true] at h
    obtain ⟨b1, b2, b3⟩ := countBind_fo isFn b h.1
    obtain ⟨e1, e2, e3⟩ := countExp_fo isFn e h.2
    simp only [countExp, Counts.add, b1, b2, b3, e1, e2, e3, Nat.add_zero, and_self]
  | .join _ _ b e, h => by
    simp only [Anf.Exp.firstOrder, Bool.and_eq_true] at h
    obtain ⟨b1, b2, b3⟩ := countExp_fo isFn b h.1
    obtain ⟨e1, e2, e3⟩ := countExp_fo isFn e h.2
    simp only [countExp, Counts.add, b1, b2, b3, e1, e2, e3, Nat.add_zero, and_self]
  | .jump .., _ => by simp only [countExp, and_self]
  | .case _ alts d, h => by
    simp only [Anf.Exp.firstOrder, Bool.and_eq_true] at h
    obtain ⟨b1, b2, b3⟩ := countAlts_fo isFn alts h.1
    obtain ⟨e1, e2, e3⟩ := countOpt_fo isFn d h.2
    simp only [countExp, Counts.add, b1, b2, b3, e1, e2, e3, Nat.add_zero, and_self]
  | .ret _, _ => by simp only [countExp, and_self]
  | .tick e, h => by
    simp only [Anf.Exp.firstOrder] at h
    simp only [countExp]
    exact countExp_fo isFn e h
  | .trap, _ => by simp only [countExp, and_self]

theorem countBind_fo (isFn : Anf.GlobalId → Bool) :
    ∀ b : Anf.Bind, Anf.Bind.firstOrder isFn b = true →
      (countBind isFn b).fns = 0 ∧ (countBind isFn b).apps = 0 ∧ (countBind isFn b).globs = 0
  | .glob g, h => by
    simp only [Anf.Bind.firstOrder, Bool.not_eq_true'] at h
    simp only [countBind, h, Bool.false_eq_true, ↓reduceIte, and_self]
  | .app .., h => by simp [Anf.Bind.firstOrder] at h
  | .fn .., h => by simp [Anf.Bind.firstOrder] at h
  | .atom _, _ => by simp only [countBind, and_self]
  | .con .., _ => by simp only [countBind, and_self]
  | .proj .., _ => by simp only [countBind, and_self]
  | .prim .., _ => by simp only [countBind, and_self]
  | .call .., _ => by simp only [countBind, and_self]

theorem countAlts_fo (isFn : Anf.GlobalId → Bool) :
    ∀ alts : List Anf.Alt, Anf.Exp.altsFirstOrder isFn alts = true →
      (countAlts isFn alts).fns = 0 ∧ (countAlts isFn alts).apps = 0 ∧ (countAlts isFn alts).globs = 0
  | [], _ => by simp only [countAlts, and_self]
  | .mk _ _ b :: as, h => by
    simp only [Anf.Exp.altsFirstOrder, Bool.and_eq_true] at h
    obtain ⟨b1, b2, b3⟩ := countExp_fo isFn b h.1
    obtain ⟨e1, e2, e3⟩ := countAlts_fo isFn as h.2
    simp only [countAlts, Counts.add, b1, b2, b3, e1, e2, e3, Nat.add_zero, and_self]

theorem countOpt_fo (isFn : Anf.GlobalId → Bool) :
    ∀ d : Option Anf.Exp, Anf.Exp.optFirstOrder isFn d = true →
      (countOpt isFn d).fns = 0 ∧ (countOpt isFn d).apps = 0 ∧ (countOpt isFn d).globs = 0
  | none, _ => by simp only [countOpt, and_self]
  | some e, h => by
    simp only [Anf.Exp.optFirstOrder] at h
    simp only [countOpt]
    exact countExp_fo isFn e h

end

/-- A fold that keeps the residual empty leaves it empty. -/
theorem foldl_empty {α : Type} (f : Residual → α → Residual) :
    ∀ (l : List α) (r : Residual), (r.fns = [] ∧ r.apps = [] ∧ r.globs = []) →
      (∀ r x, x ∈ l → (r.fns = [] ∧ r.apps = [] ∧ r.globs = []) →
        ((f r x).fns = [] ∧ (f r x).apps = [] ∧ (f r x).globs = [])) →
      ((l.foldl f r).fns = [] ∧ (l.foldl f r).apps = [] ∧ (l.foldl f r).globs = [])
  | [], _, hr, _ => hr
  | x :: l, r, hr, hf => by
    rw [List.foldl_cons]
    exact foldl_empty f l (f r x) (hf r x List.mem_cons_self hr) fun r' y hy => hf r' y (List.mem_cons_of_mem _ hy)

/-- The globals of a first-order program have first-order bodies. -/
theorem fo_globals {A : Anf.Program} (h : Anf.FirstOrder A) :
    ∀ g gd, (g, gd) ∈ A.globalList → Anf.Exp.firstOrder (isFnOf A) gd.body = true := by
  intro g gd hm
  unfold Anf.FirstOrder Anf.firstOrder at h
  dsimp only at h
  exact (List.all_eq_true.1 h) (g, gd) hm

theorem foldl_isEmpty {α : Type} (f : Residual → α → Residual) (l : List α)
    (hf : ∀ r x, x ∈ l → (r.fns = [] ∧ r.apps = [] ∧ r.globs = []) →
      ((f r x).fns = [] ∧ (f r x).apps = [] ∧ (f r x).globs = [])) :
    (l.foldl f {}).isEmpty = true := by
  obtain ⟨h1, h2, h3⟩ := foldl_empty f l {} ⟨rfl, rfl, rfl⟩ hf
  simp [Residual.isEmpty, h1, h2, h3]

/-- The decline set of a first-order program is empty. -/
theorem residual_empty {A : Anf.Program} (h : Anf.FirstOrder A) : (residual A).isEmpty = true := by
  have hall := fo_globals h
  unfold residual
  dsimp only
  apply foldl_isEmpty
  intro r x hx hr
  obtain ⟨g, gd⟩ := x
  obtain ⟨c1, c2, c3⟩ := countExp_fo _ gd.body (hall g gd hx)
  obtain ⟨h1, h2, h3⟩ := hr
  simp [c1, c2, c3, h1, h2, h3]

/-- **`Fir.lower` declines no first-order program for closures.** -/
theorem lower_firstOrder {A : Anf.Program} (h : Anf.FirstOrder A) :
    ∀ e, lower A = .error e → Error.isClosures e = false := by
  have hfo : ∀ g gd, g < A.size → A.global? g = some gd → Anf.Exp.firstOrder (isFnOf A) gd.body = true :=
    fun g gd hlt hgd => fo_globals h g gd (mem_globalList.2 ⟨hlt, hgd⟩)
  have hr := residual_empty h
  have hfs := functions_noClo A hfo (List.range A.size) fun g hg => List.mem_range.1 hg
  show NoClo (lower A)
  unfold lower
  noclo
  all_goals first
    | exact hfs
    | exact noClo_pure _
    | (exfalso; simp_all)

theorem lower_ne_closures {A : Anf.Program} (h : Anf.FirstOrder A) (fns apps globs : List Anf.GlobalId) :
    lower A ≠ .error (.closures fns apps globs) := fun he => by
  have := lower_firstOrder h _ he
  simp [Error.isClosures] at this

/-! ## The converse: what `Fir.lower` accepts is first order -/

mutual

theorem fo_of_countExp (isFn : Anf.GlobalId → Bool) :
    ∀ e : Anf.Exp, (countExp isFn e).fns = 0 → (countExp isFn e).apps = 0 → (countExp isFn e).globs = 0 →
      Anf.Exp.firstOrder isFn e = true
  | .bind _ b e, h1, h2, h3 => by
    simp only [countExp, Counts.add, Nat.add_eq_zero_iff] at h1 h2 h3
    simp only [Anf.Exp.firstOrder, Bool.and_eq_true]
    exact ⟨fo_of_countBind isFn b h1.1 h2.1 h3.1, fo_of_countExp isFn e h1.2 h2.2 h3.2⟩
  | .join _ _ b e, h1, h2, h3 => by
    simp only [countExp, Counts.add, Nat.add_eq_zero_iff] at h1 h2 h3
    simp only [Anf.Exp.firstOrder, Bool.and_eq_true]
    exact ⟨fo_of_countExp isFn b h1.1 h2.1 h3.1, fo_of_countExp isFn e h1.2 h2.2 h3.2⟩
  | .jump .., _, _, _ => rfl
  | .case _ alts d, h1, h2, h3 => by
    simp only [countExp, Counts.add, Nat.add_eq_zero_iff] at h1 h2 h3
    simp only [Anf.Exp.firstOrder, Bool.and_eq_true]
    exact ⟨fo_of_countAlts isFn alts h1.1 h2.1 h3.1, fo_of_countOpt isFn d h1.2 h2.2 h3.2⟩
  | .ret _, _, _, _ => rfl
  | .tick e, h1, h2, h3 => by
    simp only [countExp] at h1 h2 h3
    simp only [Anf.Exp.firstOrder]
    exact fo_of_countExp isFn e h1 h2 h3
  | .trap, _, _, _ => rfl

theorem fo_of_countBind (isFn : Anf.GlobalId → Bool) :
    ∀ b : Anf.Bind, (countBind isFn b).fns = 0 → (countBind isFn b).apps = 0 → (countBind isFn b).globs = 0 →
      Anf.Bind.firstOrder isFn b = true
  | .glob g, _, _, h3 => by
    simp only [countBind] at h3
    simp only [Anf.Bind.firstOrder]
    cases hg : isFn g <;> simp_all
  | .app .., _, h2, _ => by simp [countBind] at h2
  | .fn .., h1, _, _ => by simp [countBind, Counts.add] at h1
  | .atom _, _, _, _ => rfl
  | .con .., _, _, _ => rfl
  | .proj .., _, _, _ => rfl
  | .prim .., _, _, _ => rfl
  | .call .., _, _, _ => rfl

theorem fo_of_countAlts (isFn : Anf.GlobalId → Bool) :
    ∀ alts : List Anf.Alt, (countAlts isFn alts).fns = 0 → (countAlts isFn alts).apps = 0 →
      (countAlts isFn alts).globs = 0 → Anf.Exp.altsFirstOrder isFn alts = true
  | [], _, _, _ => rfl
  | .mk _ _ b :: as, h1, h2, h3 => by
    simp only [countAlts, Counts.add, Nat.add_eq_zero_iff] at h1 h2 h3
    simp only [Anf.Exp.altsFirstOrder, Bool.and_eq_true]
    exact ⟨fo_of_countExp isFn b h1.1 h2.1 h3.1, fo_of_countAlts isFn as h1.2 h2.2 h3.2⟩

theorem fo_of_countOpt (isFn : Anf.GlobalId → Bool) :
    ∀ d : Option Anf.Exp, (countOpt isFn d).fns = 0 → (countOpt isFn d).apps = 0 → (countOpt isFn d).globs = 0 →
      Anf.Exp.optFirstOrder isFn d = true
  | none, _, _, _ => rfl
  | some e, h1, h2, h3 => by
    simp only [countOpt] at h1 h2 h3
    simp only [Anf.Exp.optFirstOrder]
    exact fo_of_countExp isFn e h1 h2 h3

end

/-- A fold that ends with an empty residual began with one, and each step
kept it empty. -/
theorem foldl_isEmpty_inv {α : Type} (f : Residual → α → Residual) (Z : α → Prop)
    (hf : ∀ r x, (f r x).isEmpty = true → r.isEmpty = true ∧ Z x) :
    ∀ (l : List α) (r : Residual), (l.foldl f r).isEmpty = true → r.isEmpty = true ∧ ∀ x ∈ l, Z x
  | [], _, h => ⟨h, fun _ hx => nomatch hx⟩
  | x :: l, r, h => by
    rw [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := foldl_isEmpty_inv f Z hf l (f r x) h
    obtain ⟨h3, h4⟩ := hf r x h1
    exact ⟨h3, fun y hy => (List.mem_cons.1 hy).elim (fun e => e ▸ h4) (h2 y)⟩

/-- A program whose decline set is empty is first order. -/
theorem firstOrder_of_residual {A : Anf.Program} (h : (residual A).isEmpty = true) : Anf.FirstOrder A := by
  unfold residual at h
  have key := foldl_isEmpty_inv _
    (fun p : Anf.GlobalId × Anf.GDef =>
      (countExp (fun g => (A.arity? g).any (· > 0)) p.2.body).fns = 0 ∧
      (countExp (fun g => (A.arity? g).any (· > 0)) p.2.body).apps = 0 ∧
      (countExp (fun g => (A.arity? g).any (· > 0)) p.2.body).globs = 0) ?hf _ _ h
  case hf =>
    intro r x hx
    obtain ⟨g, gd⟩ := x
    simp only [Residual.isEmpty] at hx ⊢
    by_cases c1 : (countExp (fun g => (A.arity? g).any (· > 0)) gd.body).fns > 0
    · simp [c1] at hx
    by_cases c2 : (countExp (fun g => (A.arity? g).any (· > 0)) gd.body).apps > 0
    · simp [c2] at hx
    by_cases c3 : (countExp (fun g => (A.arity? g).any (· > 0)) gd.body).globs > 0
    · simp [c3] at hx
    simp only [c1, c2, c3, ↓reduceIte] at hx
    exact ⟨hx, by omega, by omega, by omega⟩
  obtain ⟨-, hall⟩ := key
  unfold Anf.FirstOrder Anf.firstOrder
  rw [List.all_eq_true]
  intro ⟨g, gd⟩ hm
  obtain ⟨h1, h2, h3⟩ := hall _ hm
  exact fo_of_countExp _ gd.body h1 h2 h3

/-- **A program `Fir.lower` accepts is first order.** -/
theorem lower_ok_firstOrder {A : Anf.Program} {F : Program} (h : lower A = .ok F) : Anf.FirstOrder A :=
  firstOrder_of_residual (lower_ok h).1

end IxCC.Fir.Proof
