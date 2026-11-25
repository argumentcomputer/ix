import IxCC.Fir.Shape
import IxCC.Fir.Proof.Unfold
import IxCC.Src.Proof.NatMap

/-!
# Soundness of the shape checker at `Fir` (`IxCC.Fir.Proof.Shape`)

Design note: `plans/ONE-PIPELINE.md`, section 2.3.

* `leSound`: weakening (`Shape.le`) is sound.
* `primOkSound`: the rules for today's primitives are sound: a word operation returns a word of
  its result width, a `Nat` operation a literal, and the range rules their bounds.
* `rhsSound`, `evalSound`: checked code, run in an environment and under a join stack that
  have their shapes, returns a value of the function's result shape.
* `checkSound`, `codeSound`: the statements of `IxCC.Fir.Shape`, from the rules (`Checked`).
* `check_checked`: the Boolean checker implies the rules; `check_sound`, `check_codeSound`:
  the two together, the form a back end reads.

Every theorem holds for every array reader (`ArrEnc`): no primitive makes an array at this
commit. The marked place for the array rules is in `IxCC.Fir.Shape`.
-/

set_option autoImplicit false

namespace IxCC.Fir.Proof.Shape

open IxCC.Shape
open IxCC.Fir
open IxCC.Fir.Shape
open IxCC.Sem (Result later)

/-! ## Outcomes -/

theorem ofOption_ok {α : Type} {o : Option α} {v : α} (h : Result.ofOption o = .ok v) :
    o = some v := by
  cases o with
  | none => cases h
  | some x => cases h; rfl

theorem bind_ok {α β : Type} {r : Result α} {f : α → Result β} {v : β}
    (h : r.bind f = .ok v) : ∃ x, r = .ok x ∧ f x = .ok v := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | timeout => cases h
  | resource _ => cases h
  | trap => cases h
  | stuck => cases h

/-! ## Weakening -/

theorem valOk_natLt_inv {cert : ShapeCert} {enc : ArrEnc} {b : Nat} {v : Val}
    (h : ValOk cert enc (.natLt b) v) : ∃ n, v = .lit (.nat n) ∧ n < b := by
  cases h with
  | natLt hn => exact ⟨_, rfl, hn⟩

theorem valOk_nat_inv {cert : ShapeCert} {enc : ArrEnc} {v : Val}
    (h : ValOk cert enc .nat v) : ∃ n, v = .lit (.nat n) := by
  cases h with
  | nat n => exact ⟨n, rfl⟩

/-- **Weakening is sound.** -/
theorem leSound (enc : ArrEnc) : LeSound enc := by
  intro cert σ
  induction σ with
  | any =>
    intro τ v hle _
    cases τ with
    | any => exact .any v
    | _ => simp [Shape.le] at hle
  | irr =>
    intro τ v hle hv
    cases τ with
    | any => exact .any v
    | irr => exact hv
    | _ => simp [Shape.le] at hle
  | nat =>
    intro τ v hle hv
    cases τ with
    | any => exact .any v
    | nat => exact hv
    | _ => simp [Shape.le] at hle
  | natLt a =>
    intro τ v hle hv
    cases τ with
    | any => exact .any v
    | nat =>
      obtain ⟨n, rfl, _⟩ := valOk_natLt_inv hv
      exact .nat n
    | natLt b =>
      simp only [Shape.le, decide_eq_true_eq] at hle
      obtain ⟨n, rfl, hn⟩ := valOk_natLt_inv hv
      exact .natLt (Nat.lt_of_lt_of_le hn hle)
    | _ => simp [Shape.le] at hle
  | enum i =>
    intro τ v hle hv
    cases τ with
    | any => exact .any v
    | enum j =>
      simp [Shape.le] at hle
      subst hle
      exact hv
    | _ => simp [Shape.le] at hle
  | data d =>
    intro τ v hle hv
    cases τ with
    | any => exact .any v
    | data d' =>
      simp [Shape.le] at hle
      subst hle
      exact hv
    | _ => simp [Shape.le] at hle
  | fn a b _ _ =>
    intro τ v hle hv
    cases τ with
    | any => exact .any v
    | fn c d =>
      simp [Shape.le] at hle
      obtain ⟨rfl, rfl⟩ := hle
      exact hv
    | _ => simp [Shape.le] at hle
  | inter a b _ _ =>
    intro τ v hle hv
    cases τ with
    | any => exact .any v
    | inter c d =>
      simp [Shape.le] at hle
      obtain ⟨rfl, rfl⟩ := hle
      exact hv
    | _ => simp [Shape.le] at hle
  | arr e n ih =>
    intro τ v hle hv
    cases τ with
    | any => exact .any v
    | arr e' n' =>
      simp only [Shape.le, Bool.and_eq_true, Bool.or_eq_true] at hle
      obtain ⟨he, hn⟩ := hle
      cases hv with
      | arr hxs hall hlen =>
        refine .arr hxs (fun x hx => ih e' x he (hall x hx)) ?_
        intro m hm
        rcases hn with hn | hn
        · rw [hm] at hn
          cases hn
        · have hnn : n' = n := by simpa using hn
          exact hlen m (hnn ▸ hm)
    | _ => simp [Shape.le] at hle

/-- A value whose shape weakens to a bound is a literal below it. -/
theorem valOk_le_natLt {cert : ShapeCert} {enc : ArrEnc} {σ : Shape} {a : Nat} {v : Val}
    (hle : σ.le (.natLt a) = true) (hv : ValOk cert enc σ v) : ∃ n, v = .lit (.nat n) ∧ n < a :=
  valOk_natLt_inv (leSound enc cert _ _ _ hle hv)

/-! ## Lists of values -/

theorem valsOk_get {cert : ShapeCert} {enc : ArrEnc} :
    ∀ (σs : List Shape) (vs : List Val), ValsOk cert enc σs vs →
      ∀ (i : Nat) (σ : Shape) (v : Val), σs[i]? = some σ → vs[i]? = some v → ValOk cert enc σ v
  | [], _, _, _, _, _, hσ, _ => by simp at hσ
  | _ :: σs, _, h, i, σ, v, hσ, hv => by
    cases h with
    | cons h1 h2 =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hσ hv
        subst hσ
        subst hv
        exact h1
      | succ i =>
        simp only [List.getElem?_cons_succ] at hσ hv
        exact valsOk_get σs _ h2 i σ v hσ hv

/-! ## Environments -/

theorem envOk_insert {cert : ShapeCert} {enc : ArrEnc} {fs : FunShapes} {ρ : Env}
    (h : EnvOk cert enc fs ρ) {x : Var} {v : Val} (hv : ValOk cert enc (fs.var x) v) :
    EnvOk cert enc fs (ρ.insert x v) := by
  intro y w hy
  rw [Src.NatMap.get?_insert] at hy
  split at hy
  · rename_i heq
    subst heq
    cases hy
    exact hv
  · exact h y w hy

theorem envOk_leaf (cert : ShapeCert) (enc : ArrEnc) (fs : FunShapes) :
    EnvOk cert enc fs .leaf := by
  intro x v h
  cases h

theorem envOk_bindAll {cert : ShapeCert} {enc : ArrEnc} {fs : FunShapes} :
    ∀ (xs : List Var) (σs : List Shape) (vs : List Val) (ρ : Env),
      EnvOk cert enc fs ρ → ParamsOk fs xs σs → ValsOk cert enc σs vs →
      EnvOk cert enc fs (Fir.bindAll ρ xs vs)
  | [], _, _, _, hρ, hp, hv => by
    cases hp
    cases hv
    exact hρ
  | x :: xs, _, _, ρ, hρ, hp, hv => by
    cases hp with
    | cons hp' =>
      cases hv with
      | cons hv1 hv2 =>
        exact envOk_bindAll xs _ _ (ρ.insert x _) (envOk_insert hρ hv1) hp' hv2

/-! ## Operands -/

theorem argSound {cert : ShapeCert} {enc : ArrEnc} {fs : FunShapes} {ρ : Env}
    (hρ : EnvOk cert enc fs ρ) {a : Arg} {σ : Shape} {v : Val} (h : ArgOk fs a σ)
    (hv : a.eval ρ = some v) : ValOk cert enc σ v := by
  cases h with
  | var hle => exact leSound enc cert _ _ _ hle (hρ _ _ hv)
  | nat hle =>
    simp only [Arg.eval, Option.some.injEq] at hv
    subst hv
    exact leSound enc cert _ _ _ hle (.natLt (Nat.lt_succ_self _))
  | str => exact .any v
  | erased hle =>
    simp only [Arg.eval, Option.some.injEq] at hv
    subst hv
    exact leSound enc cert _ _ _ hle .irr

theorem argsSound {cert : ShapeCert} {enc : ArrEnc} {fs : FunShapes} {ρ : Env}
    (hρ : EnvOk cert enc fs ρ) :
    ∀ (as : List Arg) (σs : List Shape) (vs : List Val), ArgsOk fs as σs →
      evalArgs ρ as = some vs → ValsOk cert enc σs vs
  | [], _, _, h, hv => by
    cases h
    simp only [evalArgs, Option.some.injEq] at hv
    subst hv
    exact .nil
  | a :: as, _, _, h, hv => by
    cases h with
    | cons ha has =>
      rw [evalArgs_cons] at hv
      cases hae : a.eval ρ with
      | none => rw [hae] at hv; cases hv
      | some w =>
        rw [hae] at hv
        cases hrest : evalArgs ρ as with
        | none => rw [hrest] at hv; cases hv
        | some ws =>
          rw [hrest] at hv
          simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hv
          subst hv
          exact .cons (argSound hρ ha hae) (argsSound hρ as _ ws has hrest)

/-! ## Primitives -/

/-- A successful primitive read literals and returned what `Lam.Prim.sem` says: a literal, or
a Boolean. -/
theorem primResult_ok_inv {P : Program} {op : Lam.Prim} {vs : List Val} {v : Val}
    (h : primResult P op vs = .ok v) :
    ∃ ns, natArgs vs = some ns ∧
      ((∃ n, op.sem ns = some (.nat n) ∧ v = .lit (.nat n)) ∨ ∃ b, op.sem ns = some (.bool b)) := by
  simp only [primResult] at h
  cases hns : natArgs vs with
  | none => simp [hns] at h
  | some ns =>
    simp only [hns] at h
    refine ⟨ns, rfl, ?_⟩
    cases hsem : op.sem ns with
    | none => simp [hsem] at h
    | some r =>
      simp only [hsem] at h
      cases r with
      | nat n =>
        cases h
        exact .inl ⟨n, rfl, rfl⟩
      | bool b => exact .inr ⟨b, rfl⟩

theorem sem_word (w : Src.Width) (op : Src.WordOp) (ns : List Nat) :
    (Lam.Prim.word w op).sem ns = Lam.wordSem w op ns := rfl

theorem not_or_true {x y : Bool} (h : ¬(x || y) = true) : y = false := by
  cases x <;> cases y <;> simp_all

theorem eval_word_width {w : Src.Width} {op : Src.WordOp} {a b : Nat} {w' : Src.Width} {n : Nat}
    (h : Src.WordOp.eval w op a b = .word w' n) : w' = op.resultWidth w := by
  cases op with
  | convert w'' =>
    simp only [Src.WordOp.eval] at h
    split at h <;>
      · simp only [Src.WordResult.word.injEq] at h
        exact h.1.symm
  | _ => simp [Src.WordOp.eval] at h <;> exact h.1.symm

theorem eval_nat_inv {w : Src.Width} {op : Src.WordOp} {a b n : Nat}
    (h : Src.WordOp.eval w op a b = .nat n) : op = .toNat ∧ n = a := by
  cases op with
  | convert w'' =>
    simp only [Src.WordOp.eval] at h
    split at h <;> cases h
  | toNat =>
    simp [Src.WordOp.eval] at h
    exact ⟨rfl, h.symm⟩
  | _ => simp [Src.WordOp.eval] at h

theorem eval_dec_inv {w : Src.Width} {op : Src.WordOp} {a b : Nat} {d : Bool}
    (h : Src.WordOp.eval w op a b = .dec d) : op.isDecision = true := by
  cases op with
  | convert w'' =>
    simp only [Src.WordOp.eval] at h
    split at h <;> cases h
  | decEq => rfl
  | decLt => rfl
  | decLe => rfl
  | _ => simp [Src.WordOp.eval] at h

/-- The number a one- or two-operand word operation returns is below its result width's size. -/
theorem eval_val_lt (w : Src.Width) (op : Src.WordOp) (a b : Nat) (hdec : op.isDecision = false)
    (ha : op = .ofNat ∨ a < w.size) (hb : b < w.size) :
    (op.eval w a b).val < (op.resultWidth w).size := by
  cases hr : op.eval w a b with
  | word w' n =>
    have hlt := Src.WordOp.eval_word_lt w op a b ha hb w' n hr
    have hw : w' = op.resultWidth w := eval_word_width hr
    rw [← hw]
    exact hlt
  | nat n =>
    obtain ⟨hop, hn⟩ := eval_nat_inv hr
    subst hop
    subst hn
    rcases ha with ha | ha
    · cases ha
    · exact ha
  | dec d =>
    have hd := eval_dec_inv hr
    rw [hd] at hdec
    cases hdec

theorem eval3_word {w : Src.Width} {op : Src.WordOp} {a b c : Nat} {r : Src.WordResult}
    (h : Src.WordOp.eval3 w op a b c = some r) : ∃ n, r = .word w n ∧ op.resultWidth w = w := by
  cases op with
  | divWideQ =>
    simp only [Src.WordOp.eval3] at h
    split at h
    · cases h
      exact ⟨_, rfl, rfl⟩
    · cases h
  | divWideR =>
    simp only [Src.WordOp.eval3] at h
    split at h
    · cases h
      exact ⟨_, rfl, rfl⟩
    · cases h
  | _ => first | (cases h; exact ⟨_, rfl, rfl⟩) | cases h

/-- **A word primitive returns a word of its result width**, whatever it is given. -/
theorem wordSem_lt {w : Src.Width} {op : Src.WordOp} :
    ∀ (ns : List Nat) (r : Src.PrimResult), Lam.wordSem w op ns = some r →
      ∃ n, r = .nat n ∧ n < (op.resultWidth w).size
  | [], _, h => by simp [Lam.wordSem] at h
  | [a], _, h => by
    simp only [Lam.wordSem] at h
    split at h
    · cases h
    · split at h
      · rename_i hnd hcond
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
        cases h
        exact ⟨_, rfl, eval_val_lt w op a 0 (not_or_true hnd) hcond w.size_pos⟩
      · cases h
  | [a, b], _, h => by
    simp only [Lam.wordSem] at h
    split at h
    · cases h
    · split at h
      · rename_i hnd hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        cases h
        exact ⟨_, rfl, eval_val_lt w op a b (not_or_true hnd) (.inr hcond.1) hcond.2⟩
      · cases h
  | [a, b, c], _, h => by
    simp only [Lam.wordSem] at h
    split at h
    · cases h
    · split at h
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        cases he : Src.WordOp.eval3 w op a b c with
        | none => rw [he] at h; cases h
        | some wr =>
          rw [he] at h
          cases h
          obtain ⟨n, hwr, hrw⟩ := eval3_word he
          subst hwr
          refine ⟨n, rfl, ?_⟩
          rw [hrw]
          exact Src.WordOp.eval3_word_lt w op a b c hcond.1.1 hcond.1.2 hcond.2 w n he
      · cases h
  | _ :: _ :: _ :: _ :: _, _, h => by simp [Lam.wordSem] at h

/-- A literal has the shape `natPrimResult` gives. -/
theorem natPrimResult_lit (cert : ShapeCert) (enc : ArrEnc) (op : Lam.Prim) (n : Nat) :
    ValOk cert enc (natPrimResult op) (.lit (.nat n)) := by
  cases op <;> first | exact .nat n | exact .any _

/-- Only a comparison returns a Boolean, and of a comparison nothing is recorded. -/
theorem sem_bool_any {op : Lam.Prim} {ns : List Nat} {b : Bool}
    (hsem : op.sem ns = some (.bool b)) : natPrimResult op = .any := by
  cases op <;> first
    | rfl
    | (exfalso
       rcases ns with _ | ⟨a, _ | ⟨b', _ | ⟨c, rest⟩⟩⟩ <;> cases hsem)

theorem prim2_inv {P : Program} {op : Lam.Prim} {v : Val} {n1 n2 r : Nat}
    (h : primResult P op [.lit (.nat n1), .lit (.nat n2)] = .ok v)
    (hsem : op.sem [n1, n2] = some (.nat r)) : v = .lit (.nat r) := by
  simp [primResult, natArgs, hsem] at h
  exact h.symm

theorem prim1_inv {P : Program} {op : Lam.Prim} {v : Val} {n1 r : Nat}
    (h : primResult P op [.lit (.nat n1)] = .ok v)
    (hsem : op.sem [n1] = some (.nat r)) : v = .lit (.nat r) := by
  simp [primResult, natArgs, hsem] at h
  exact h.symm

/-- Two operands, the left one below a bound. -/
theorem valsOk_left {cert : ShapeCert} {enc : ArrEnc} {σ τ : Shape} {a : Nat} {vs : List Val}
    (hσ : σ.le (.natLt a) = true) (hvs : ValsOk cert enc [σ, τ] vs) :
    ∃ n1 v2, vs = [.lit (.nat n1), v2] ∧ n1 < a ∧ ValOk cert enc τ v2 := by
  cases hvs with
  | cons h1 hrest =>
    cases hrest with
    | cons h2 hnil =>
      cases hnil
      obtain ⟨n1, rfl, hn1⟩ := valOk_le_natLt hσ h1
      exact ⟨n1, _, rfl, hn1, h2⟩

/-- Two operands, each below a bound. -/
theorem valsOk_both {cert : ShapeCert} {enc : ArrEnc} {σ τ : Shape} {a b : Nat} {vs : List Val}
    (hσ : σ.le (.natLt a) = true) (hτ : τ.le (.natLt b) = true)
    (hvs : ValsOk cert enc [σ, τ] vs) :
    ∃ n1 n2, vs = [.lit (.nat n1), .lit (.nat n2)] ∧ n1 < a ∧ n2 < b := by
  obtain ⟨n1, v2, rfl, hn1, h2⟩ := valsOk_left hσ hvs
  obtain ⟨n2, rfl, hn2⟩ := valOk_le_natLt hτ h2
  exact ⟨n1, n2, rfl, hn1, hn2⟩

/-- A primitive that returned on a literal on the left returned on two literals. -/
theorem prim_right_lit {P : Program} {op : Lam.Prim} {n1 : Nat} {v2 v : Val}
    (h : primResult P op [.lit (.nat n1), v2] = .ok v) : ∃ n2, v2 = .lit (.nat n2) := by
  obtain ⟨ns, hns, _⟩ := primResult_ok_inv h
  cases v2 with
  | lit l =>
    cases l with
    | nat n2 => exact ⟨n2, rfl⟩
    | str s => simp [natArgs] at hns
  | ctor c fs => simp [natArgs] at hns
  | erased => simp [natArgs] at hns

theorem mul_lt_mul_of_lt {a b c d : Nat} (h1 : a < c) (h2 : b < d) : a * b < c * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right b (Nat.le_of_lt h1))
    (Nat.mul_lt_mul_of_pos_left h2 (Nat.zero_lt_of_lt h1))

/-- **The rules for today's primitives are sound.** -/
theorem primOkSound (cert : ShapeCert) (enc : ArrEnc) : PrimOkSound cert enc := by
  intro P op σs τ vs v hok hvs hres
  cases hok with
  | word =>
    obtain ⟨ns, _, hsem | hsem⟩ := primResult_ok_inv hres
    · obtain ⟨n, hsem, rfl⟩ := hsem
      rw [sem_word] at hsem
      obtain ⟨m, hm, hlt⟩ := wordSem_lt ns _ hsem
      cases hm
      exact .natLt hlt
    · obtain ⟨b, hsem⟩ := hsem
      rw [sem_word] at hsem
      obtain ⟨m, hm, _⟩ := wordSem_lt ns _ hsem
      cases hm
  | natAny _ =>
    obtain ⟨ns, _, hsem | hsem⟩ := primResult_ok_inv hres
    · obtain ⟨n, _, rfl⟩ := hsem
      exact natPrimResult_lit cert enc _ n
    · obtain ⟨b, hsem⟩ := hsem
      rw [sem_bool_any hsem]
      exact .any v
  | add hσ hτ =>
    obtain ⟨n1, n2, rfl, hn1, hn2⟩ := valsOk_both hσ hτ hvs
    have hv := prim2_inv hres (r := n1 + n2) rfl
    subst hv
    exact .natLt (Nat.add_lt_add hn1 hn2)
  | mul hσ hτ =>
    obtain ⟨n1, n2, rfl, hn1, hn2⟩ := valsOk_both hσ hτ hvs
    have hv := prim2_inv hres (r := n1 * n2) rfl
    subst hv
    exact .natLt (mul_lt_mul_of_lt hn1 hn2)
  | sub hσ =>
    obtain ⟨n1, v2, rfl, hn1, _⟩ := valsOk_left hσ hvs
    obtain ⟨n2, rfl⟩ := prim_right_lit hres
    have hv := prim2_inv hres (r := n1 - n2) rfl
    subst hv
    exact .natLt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn1)
  | div hσ =>
    obtain ⟨n1, v2, rfl, hn1, _⟩ := valsOk_left hσ hvs
    obtain ⟨n2, rfl⟩ := prim_right_lit hres
    have hv := prim2_inv hres (r := if n2 == 0 then 0 else n1 / n2) rfl
    subst hv
    refine .natLt (Nat.lt_of_le_of_lt ?_ hn1)
    split
    · exact Nat.zero_le _
    · exact Nat.div_le_self _ _
  | mod hσ =>
    obtain ⟨n1, v2, rfl, hn1, _⟩ := valsOk_left hσ hvs
    obtain ⟨n2, rfl⟩ := prim_right_lit hres
    have hv := prim2_inv hres (r := if n2 == 0 then n1 else n1 % n2) rfl
    subst hv
    refine .natLt (Nat.lt_of_le_of_lt ?_ hn1)
    split
    · exact Nat.le_refl _
    · exact Nat.mod_le _ _
  | modBound _ hσ _ =>
    obtain ⟨n1, v2, rfl, hn1, _⟩ := valsOk_left hσ hvs
    obtain ⟨n2, rfl⟩ := prim_right_lit hres
    have hv := prim2_inv hres (r := if n2 == 0 then n1 else n1 % n2) rfl
    subst hv
    refine .natLt (Nat.lt_of_le_of_lt ?_ hn1)
    split
    · exact Nat.le_refl _
    · exact Nat.mod_le _ _
  | land hσ =>
    obtain ⟨n1, v2, rfl, hn1, _⟩ := valsOk_left hσ hvs
    obtain ⟨n2, rfl⟩ := prim_right_lit hres
    have hv := prim2_inv hres (r := n1 &&& n2) rfl
    subst hv
    exact .natLt (Nat.lt_of_le_of_lt Nat.and_le_left hn1)
  | shr hσ =>
    obtain ⟨n1, v2, rfl, hn1, _⟩ := valsOk_left hσ hvs
    obtain ⟨n2, rfl⟩ := prim_right_lit hres
    have hv := prim2_inv hres (r := if n1.log2 < n2 then 0 else n1 / 2 ^ n2) rfl
    subst hv
    refine .natLt (Nat.lt_of_le_of_lt ?_ hn1)
    split
    · exact Nat.zero_le _
    · exact Nat.div_le_self _ _
  | pred hσ =>
    cases hvs with
    | cons h1 hnil =>
      cases hnil
      obtain ⟨n1, rfl, hn1⟩ := valOk_le_natLt hσ h1
      have hv := prim1_inv hres (r := n1 - 1) rfl
      subst hv
      exact .natLt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn1)

/-! ## Right-hand sides -/

theorem evalRhs_ctor_ok {P : Program} {ρ : Env} {c : CtorInfo} {as : List Arg} {v : Val}
    (h : evalRhs P ρ (.ctor c as) = .ok v) : ∃ vs, evalArgs ρ as = some vs ∧ v = .ctor c vs := by
  simp only [evalRhs] at h
  cases hvs : evalArgs ρ as with
  | none => simp [hvs] at h
  | some vs =>
    simp only [hvs] at h
    by_cases hlen : vs.length = c.arity
    · rw [ite_eq_left hlen] at h
      cases h
      exact ⟨vs, rfl, rfl⟩
    · rw [ite_eq_right hlen] at h
      cases h

theorem evalRhs_proj_ok {P : Program} {ρ : Env} {x : Var} {c : Key.CtorKey} {i : Nat} {v : Val}
    (h : evalRhs P ρ (.proj x c i) = .ok v) :
    ∃ vx c' fields, ρ.get? x = some vx ∧ vx.asCtor P.known = some (c', fields) ∧ c' = c ∧
      fields[i]? = some v := by
  simp only [evalRhs] at h
  cases hx : ρ.get? x with
  | none => simp [hx] at h
  | some vx =>
    simp only [hx] at h
    cases hc : vx.asCtor P.known with
    | none => simp [hc] at h
    | some p =>
      obtain ⟨c', fields⟩ := p
      simp only [hc] at h
      by_cases hcc : c' = c
      · rw [ite_eq_left hcc] at h
        exact ⟨vx, c', fields, rfl, hc, hcc, ofOption_ok h⟩
      · rw [ite_eq_right hcc] at h
        cases h

theorem evalRhs_prim_ok {P : Program} {ρ : Env} {op : Lam.Prim} {as : List Arg} {v : Val}
    (h : evalRhs P ρ (.prim op as) = .ok v) :
    ∃ vs, evalArgs ρ as = some vs ∧ primResult P op vs = .ok v := by
  simp only [evalRhs] at h
  cases hvs : evalArgs ρ as with
  | none => simp [hvs] at h
  | some vs =>
    simp only [hvs] at h
    exact ⟨vs, rfl, h⟩

theorem asCtor_zero (K : Lam.Known) :
    Val.asCtor K (.lit (.nat 0)) = K.natZero.map (·, []) := rfl

theorem asCtor_succ (K : Lam.Known) (n : Nat) :
    Val.asCtor K (.lit (.nat (n + 1))) = K.natSucc.map (·, [.lit (.nat n)]) := rfl

/-- **A checked right-hand side yields a value of its shape** (a call is not a right-hand side
of `evalRhs`: it is stuck there, and `evalSound` treats it). -/
theorem rhsSound {P : Program} {cert : ShapeCert} {enc : ArrEnc} {fs : FunShapes} {ρ : Env}
    (hwf : cert.WF) (hρ : EnvOk cert enc fs ρ) {r : Rhs} {σ : Shape} (h : RhsOk P cert fs r σ)
    {v : Val} (hv : evalRhs P ρ r = .ok v) : ValOk cert enc σ v := by
  induction h generalizing v with
  | arg ha => exact argSound hρ ha (ofOption_ok hv)
  | ctorData hD hmem hargs =>
    obtain ⟨vs, hvs, rfl⟩ := evalRhs_ctor_ok hv
    exact .data hD hmem (argsSound hρ _ _ _ hargs hvs)
  | ctorEnum hE hmem =>
    obtain ⟨vs, hvs, rfl⟩ := evalRhs_ctor_ok hv
    simp only [evalArgs, Option.some.injEq] at hvs
    subst hvs
    exact .enum hE hmem
  | ctorFn hkey =>
    obtain ⟨vs, _, rfl⟩ := evalRhs_ctor_ok hv
    exact .fn hkey
  | ctorAny => exact .any v
  | projData hx hD hmem hi =>
    obtain ⟨vx, c', fields, hget, hctor, hcc, hfi⟩ := evalRhs_proj_ok hv
    have hvx := hρ _ _ hget
    rw [hx] at hvx
    cases hvx with
    | data hD' hmem' hfields =>
      simp only [Val.asCtor, Option.some.injEq, Prod.mk.injEq] at hctor
      obtain ⟨hk, hf⟩ := hctor
      rw [hD] at hD'
      cases hD'
      have hfl := hwf _ _ hD _ _ _ hmem (by rw [← hcc, ← hk]; exact hmem')
      rw [hfl] at hi
      rw [← hf] at hfi
      exact valsOk_get _ _ hfields _ _ _ hi hfi
  | projNat _ hle =>
    obtain ⟨vx, c', fields, hget, hctor, _, hfi⟩ := evalRhs_proj_ok hv
    obtain ⟨n, rfl⟩ := valOk_nat_inv (leSound enc cert _ _ _ hle (hρ _ _ hget))
    cases n with
    | zero =>
      rw [asCtor_zero] at hctor
      cases hz : P.known.natZero with
      | none => rw [hz] at hctor; cases hctor
      | some z =>
        rw [hz] at hctor
        cases hctor
        simp at hfi
    | succ m =>
      rw [asCtor_succ] at hctor
      cases hs : P.known.natSucc with
      | none => rw [hs] at hctor; cases hctor
      | some s =>
        rw [hs] at hctor
        cases hctor
        simp at hfi
        subst hfi
        exact .nat m
  | projAny => exact .any v
  | prim hargs hprim =>
    obtain ⟨vs, hvs, hres⟩ := evalRhs_prim_ok hv
    exact primOkSound cert enc P _ _ _ _ _ hprim (argsSound hρ _ _ _ hargs hvs) hres
  | primAny => exact .any v
  | call _ => cases hv
  | weaken _ hle ih => exact leSound enc cert _ _ _ hle (ih hv)

/-- What a checked call says: its arguments have the callee's parameter shapes, and the
callee's result has the binder's shape. -/
theorem rhsOk_call_inv (enc : ArrEnc) {P : Program} {cert : ShapeCert} {fs : FunShapes}
    {g : FunId} {as : List Arg} {τ : Shape} (h : RhsOk P cert fs (.call g as) τ) :
    ArgsOk fs as (cert.fn g).params ∧
      ∀ v, ValOk cert enc (cert.fn g).ret v → ValOk cert enc τ v := by
  generalize hr : Rhs.call g as = r at h
  induction h with
  | call hargs =>
    cases hr
    exact ⟨hargs, fun _ hv => hv⟩
  | weaken _ hle ih =>
    obtain ⟨ha, hf⟩ := ih hr
    exact ⟨ha, fun v hv => leSound enc cert _ _ _ hle (hf v hv)⟩
  | _ => cases hr

/-! ## Code -/

theorem lookupJ_ok {P : Program} {cert : ShapeCert} {enc : ArrEnc} {fs : FunShapes} :
    ∀ {j : JoinId} {J : List JEntry} {e : JEntry} {rest : List JEntry},
      JStackOk P cert enc fs J → lookupJ j J = some (e, rest) →
      e.id = j ∧ EnvOk cert enc fs e.env ∧ ParamsOk fs e.params (fs.join j) ∧
        CodeOk P cert fs e.body ∧ JStackOk P cert enc fs rest
  | _, [], _, _, _, h => by cases h
  | j, e' :: J', e, rest, hJ, h => by
    cases hJ with
    | cons henv hparams hbody hrest =>
      simp only [lookupJ] at h
      split at h
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [heq] at hparams
        exact ⟨heq, henv, hparams, hbody, hrest⟩
      · exact lookupJ_ok hrest h

/-- Entering a checked function on arguments of its parameter shapes, given soundness of
bodies at every smaller clock. -/
theorem callSound {enc : ArrEnc} {P : Program} {cert : ShapeCert} (hchk : Checked P cert)
    {k : Nat}
    (ih : ∀ m, m < k → ∀ (fs : FunShapes) (ρ : Env) (c : Code) (v : Val),
      EnvOk cert enc fs ρ → CodeOk P cert fs c → eval P m ρ [] c = .ok v →
      ValOk cert enc fs.ret v)
    {g : FunId} {vs : List Val} {rv : Val} (hvs : ValsOk cert enc (cert.fn g).params vs)
    (hcall : evalCall P k g vs = .ok rv) : ValOk cert enc (cert.fn g).ret rv := by
  rw [evalCall_eq] at hcall
  obtain ⟨gd, hgd, hcall⟩ := bind_ok hcall
  have hgd := ofOption_ok hgd
  obtain ⟨hgp, hgb⟩ := hchk.funs g gd hgd
  simp only [callFun] at hcall
  by_cases hlen : vs.length = gd.params.length
  · rw [ite_eq_left hlen] at hcall
    cases k with
    | zero => simp [later] at hcall
    | succ k0 =>
      simp only [later] at hcall
      exact ih k0 (Nat.lt_succ_self k0) (cert.fn g) _ gd.body rv
        (envOk_bindAll _ _ _ .leaf (envOk_leaf cert enc _) hgp hvs) hgb hcall
  · rw [ite_eq_right hlen] at hcall
    cases hcall

private theorem evalSound_aux (enc : ArrEnc) (P : Program) (cert : ShapeCert)
    (hchk : Checked P cert) :
    ∀ (k : Nat) (w : Nat) (fs : FunShapes) (ρ : Env) (J : List JEntry) (c : Code) (v : Val),
      c.size + jweight J ≤ w →
      EnvOk cert enc fs ρ →
      JStackOk P cert enc fs J →
      CodeOk P cert fs c →
      eval P k ρ J c = .ok v →
      ValOk cert enc fs.ret v := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ihk =>
    have ihc : ∀ m, m < k → ∀ (fs : FunShapes) (ρ : Env) (c : Code) (v : Val),
        EnvOk cert enc fs ρ → CodeOk P cert fs c → eval P m ρ [] c = .ok v →
        ValOk cert enc fs.ret v := fun m hm fs ρ c v hρ hc he =>
      ihk m hm (c.size + jweight []) fs ρ [] c v (Nat.le_refl _) hρ .nil hc he
    intro w
    induction w using Nat.strongRecOn with
    | ind w ihw =>
      intro fs ρ J c v hle hρ hJ hc heval
      cases c with
      | trap =>
        rw [eval_trap] at heval
        cases heval
      | ret a =>
        rw [eval_ret] at heval
        cases hc with
        | ret ha => exact argSound hρ ha (ofOption_ok heval)
      | bind x rhs k' =>
        cases hc with
        | bind hrhs hk' =>
          have hlt : k'.size + jweight J < w := by
            simp only [Code.size] at hle
            omega
          by_cases hcall : ∃ g as, rhs = .call g as
          · obtain ⟨g, as, rfl⟩ := hcall
            rw [eval_bindCall] at heval
            obtain ⟨vs, hvs, heval⟩ := bind_ok heval
            have hvs := ofOption_ok hvs
            obtain ⟨rv, hcallv, heval⟩ := bind_ok heval
            obtain ⟨hargs, hret⟩ := rhsOk_call_inv enc hrhs
            have hrv := callSound hchk ihc (argsSound hρ _ _ _ hargs hvs) hcallv
            exact ihw _ hlt fs (ρ.insert x rv) J k' v (Nat.le_refl _)
              (envOk_insert hρ (hret rv hrv)) hJ hk' heval
          · rw [eval_bindRhs P k ρ J x rhs k' (fun g as h => hcall ⟨g, as, h⟩)] at heval
            obtain ⟨rv, hr, heval⟩ := bind_ok heval
            exact ihw _ hlt fs (ρ.insert x rv) J k' v (Nat.le_refl _)
              (envOk_insert hρ (rhsSound hchk.wf hρ hrhs hr)) hJ hk' heval
      | jp j ps isRec body k' =>
        rw [eval_jp] at heval
        cases hc with
        | jp hps hbody hk' =>
          have hlt : k'.size + jweight
              ({ id := j, charged := false, env := ρ, params := ps, body := body,
                 isRec := isRec } :: J) < w := by
            simp only [Code.size] at hle
            simp only [jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]
            omega
          exact ihw _ hlt fs ρ _ k' v (Nat.le_refl _) hρ (.cons hρ hps hbody hJ) hk' heval
      | jmp j as =>
        rw [eval_jmp] at heval
        cases hc with
        | jmp hargs =>
          obtain ⟨p, hlu, heval⟩ := bind_ok heval
          have hlu := ofOption_ok hlu
          obtain ⟨e, rest⟩ := p
          obtain ⟨vs, hvs, heval⟩ := bind_ok heval
          have hvs := ofOption_ok hvs
          obtain ⟨hid, henv, hparams, hbody, hrest⟩ := lookupJ_ok hJ hlu
          have hρ' := envOk_bindAll _ _ _ e.env henv hparams (argsSound hρ _ _ _ hargs hvs)
          have hJ' : JStackOk P cert enc fs (e.after rest) := by
            unfold JEntry.after
            split
            · exact .cons henv (by rw [hid]; exact hparams) hbody hrest
            · exact hrest
          simp only [jumpTo] at heval
          by_cases hlen : vs.length = e.params.length
          · rw [ite_eq_left hlen] at heval
            by_cases hch : e.charged = true
            · rw [ite_eq_left hch] at heval
              cases k with
              | zero => simp [later] at heval
              | succ k0 =>
                simp only [later] at heval
                exact ihk k0 (Nat.lt_succ_self k0) (e.body.size + jweight (e.after rest))
                  fs _ (e.after rest) e.body v (Nat.le_refl _) hρ' hJ' hbody heval
            · rw [ite_eq_right hch] at heval
              have hchf : e.charged = false := Bool.eq_false_iff.2 hch
              have hw := lookupJ_weight j hlu
              have hafter := JEntry.jweight_after e rest
              have hlt : e.body.size + jweight (e.after rest) < w := by
                simp only [Code.size] at hle
                simp only [JEntry.weight, hchf, Bool.false_eq_true, ↓reduceIte] at hw
                omega
              exact ihw _ hlt fs _ (e.after rest) e.body v (Nat.le_refl _) hρ' hJ' hbody heval
          · rw [ite_eq_right hlen] at heval
            cases heval
      | case x alts d =>
        rw [eval_case] at heval
        cases hc with
        | case halts hd =>
          obtain ⟨vx, _, heval⟩ := bind_ok heval
          cases hasc : vx.asCtor P.known with
          | none => simp [hasc] at heval
          | some pair =>
            obtain ⟨key, flds⟩ := pair
            simp only [hasc] at heval
            have hwalk : ∀ (as' : List Alt), AltsOk P cert fs as' →
                Code.altsSize as' + Code.optSize d + 2 + jweight J ≤ w →
                evalAlts P k ρ J key as' d = .ok v → ValOk cert enc fs.ret v := by
              intro as'
              induction as' with
              | nil =>
                intro _ hsz he
                rw [evalAlts_nil] at he
                cases d with
                | none => cases he
                | some dc =>
                  cases hd with
                  | present hdc =>
                    have hlt : dc.size + jweight J < w := by
                      simp only [Code.altsSize, Code.optSize] at hsz
                      omega
                    exact ihw _ hlt fs ρ J dc v (Nat.le_refl _) hρ hJ hdc he
              | cons a rest ihA =>
                intro hca hsz he
                cases a with
                | mk akey abody =>
                  cases hca with
                  | cons hb hr =>
                    rw [evalAlts_cons] at he
                    by_cases hkey : akey = key
                    · rw [ite_eq_left hkey] at he
                      have hlt : abody.size + jweight J < w := by
                        simp only [Code.altsSize] at hsz
                        omega
                      exact ihw _ hlt fs ρ J abody v (Nat.le_refl _) hρ hJ hb he
                    · rw [ite_eq_right hkey] at he
                      refine ihA hr ?_ he
                      simp only [Code.altsSize] at hsz ⊢
                      omega
            exact hwalk alts halts (by simpa only [Code.size] using hle) heval
      | tcall g as =>
        rw [eval_tcall] at heval
        cases hc with
        | tcall hargs hret =>
          obtain ⟨vs, hvs, heval⟩ := bind_ok heval
          have hvs := ofOption_ok hvs
          exact leSound enc cert _ _ _ hret
            (callSound hchk ihc (argsSound hρ _ _ _ hargs hvs) heval)

/-- **Checked code is sound from any point of a body**: run in an environment and under a join
stack that have their shapes, it returns a value of the function's result shape. This is the
form a back end's simulation carries. -/
theorem evalSound {enc : ArrEnc} {P : Program} {cert : ShapeCert} (hchk : Checked P cert)
    {fs : FunShapes} {k : Nat} {ρ : Env} {J : List JEntry} {c : Code} {v : Val}
    (hρ : EnvOk cert enc fs ρ) (hJ : JStackOk P cert enc fs J) (hc : CodeOk P cert fs c)
    (heval : eval P k ρ J c = .ok v) : ValOk cert enc fs.ret v :=
  evalSound_aux enc P cert hchk k (c.size + jweight J) fs ρ J c v (Nat.le_refl _) hρ hJ hc heval

/-- **`CodeSound`**: the instance at a function's entry. -/
theorem codeSound (enc : ArrEnc) : CodeSound enc :=
  fun _ _ hchk _ _ _ _ _ hρ hc heval => evalSound hchk hρ .nil hc heval

/-- **`CheckSound`: soundness of the shape rules.** A checked program, run from arguments that
have a function's parameter shapes, returns a value that has its result shape, at every
clock. -/
theorem checkSound (enc : ArrEnc) : CheckSound enc := by
  intro P cert hchk f k args v _ hargs hrun
  rw [run_eq] at hrun
  exact callSound hchk (fun _ _ _ _ _ _ hρ hc he => evalSound hchk hρ .nil hc he) hargs hrun

/-! ## The Boolean checker implies the rules -/

theorem argOk_sound {fs : FunShapes} {a : Arg} {σ : Shape} (h : argOk fs a σ = true) :
    ArgOk fs a σ := by
  cases a with
  | var x => exact .var h
  | lit l =>
    cases l with
    | nat n => exact .nat h
    | str s =>
      simp only [argOk, beq_iff_eq] at h
      subst h
      exact .str
  | erased => exact .erased h

theorem argsOk_sound {fs : FunShapes} :
    ∀ (as : List Arg) (σs : List Shape), argsOk fs as σs = true → ArgsOk fs as σs
  | [], [], _ => .nil
  | a :: as, σ :: σs, h => by
    simp only [argsOk, Bool.and_eq_true] at h
    exact .cons (argOk_sound h.1) (argsOk_sound as σs h.2)
  | [], _ :: _, h => by simp [argsOk] at h
  | _ :: _, [], h => by simp [argsOk] at h

theorem paramsOk_sound {fs : FunShapes} :
    ∀ (xs : List Var) (σs : List Shape), paramsOk fs xs σs = true → ParamsOk fs xs σs
  | [], [], _ => .nil
  | x :: xs, σ :: σs, h => by
    simp only [paramsOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    exact .cons (paramsOk_sound xs σs h2)
  | [], _ :: _, h => by simp [paramsOk] at h
  | _ :: _, [], h => by simp [paramsOk] at h

theorem argShape_ok (fs : FunShapes) (a : Arg) : ArgOk fs a (argShape fs a) := by
  cases a with
  | var x => exact .var (Shape.le_refl _)
  | lit l =>
    cases l with
    | nat n => exact .nat (Shape.le_refl _)
    | str s => exact .str
  | erased => exact .erased (Shape.le_refl _)

theorem argShapes_ok (fs : FunShapes) : ∀ as : List Arg, ArgsOk fs as (as.map (argShape fs))
  | [] => .nil
  | a :: as => .cons (argShape_ok fs a) (argShapes_ok fs as)

theorem bound2_inv {σs : List Shape} {a b : Nat} (h : bound2 σs = some (a, b)) :
    σs = [.natLt a, .natLt b] := by
  unfold bound2 at h
  split at h
  · cases h
    rfl
  · cases h

theorem boundL_inv {σs : List Shape} {a : Nat} (h : boundL σs = some a) :
    ∃ τ, σs = [.natLt a, τ] := by
  unfold boundL at h
  split at h
  · cases h
    exact ⟨_, rfl⟩
  · cases h

theorem bound1_inv {σs : List Shape} {a : Nat} (h : bound1 σs = some a) : σs = [.natLt a] := by
  unfold bound1 at h
  split at h
  · cases h
    rfl
  · cases h

/-- The shape `primShape` computes is one the rules give. -/
theorem primShape_ok (op : Lam.Prim) (σs : List Shape) : PrimOk op σs (primShape op σs) := by
  cases op with
  | word w wop => exact .word
  | natAdd =>
    cases hb : bound2 σs with
    | none =>
      simp only [primShape, hb]
      exact .natAny rfl
    | some p =>
      obtain ⟨a, b⟩ := p
      have hσ := bound2_inv hb
      subst hσ
      simp only [primShape, hb]
      exact .add (Shape.le_refl _) (Shape.le_refl _)
  | natMul =>
    cases hb : bound2 σs with
    | none =>
      simp only [primShape, hb]
      exact .natAny rfl
    | some p =>
      obtain ⟨a, b⟩ := p
      have hσ := bound2_inv hb
      subst hσ
      simp only [primShape, hb]
      exact .mul (Shape.le_refl _) (Shape.le_refl _)
  | natSub =>
    cases hb : boundL σs with
    | none =>
      simp only [primShape, hb]
      exact .natAny rfl
    | some a =>
      obtain ⟨τ, hσ⟩ := boundL_inv hb
      subst hσ
      simp only [primShape, hb]
      exact .sub (Shape.le_refl _)
  | natDiv =>
    cases hb : boundL σs with
    | none =>
      simp only [primShape, hb]
      exact .natAny rfl
    | some a =>
      obtain ⟨τ, hσ⟩ := boundL_inv hb
      subst hσ
      simp only [primShape, hb]
      exact .div (Shape.le_refl _)
  | natMod =>
    cases hb : boundL σs with
    | none =>
      simp only [primShape, hb]
      exact .natAny rfl
    | some a =>
      obtain ⟨τ, hσ⟩ := boundL_inv hb
      subst hσ
      simp only [primShape, hb]
      exact .mod (Shape.le_refl _)
  | natLand =>
    cases hb : boundL σs with
    | none =>
      simp only [primShape, hb]
      exact .natAny rfl
    | some a =>
      obtain ⟨τ, hσ⟩ := boundL_inv hb
      subst hσ
      simp only [primShape, hb]
      exact .land (Shape.le_refl _)
  | natShr =>
    cases hb : boundL σs with
    | none =>
      simp only [primShape, hb]
      exact .natAny rfl
    | some a =>
      obtain ⟨τ, hσ⟩ := boundL_inv hb
      subst hσ
      simp only [primShape, hb]
      exact .shr (Shape.le_refl _)
  | natPred =>
    cases hb : bound1 σs with
    | none =>
      simp only [primShape, hb]
      exact .natAny rfl
    | some a =>
      have hσ := bound1_inv hb
      subst hσ
      simp only [primShape, hb]
      exact .pred (Shape.le_refl _)
  | _ => exact .natAny rfl

theorem ctorFields_mem {D : DataDecl Key.CtorKey} {c : Key.CtorKey} {fl : List Shape}
    (h : ctorFields D c = some fl) : (c, fl) ∈ D.ctors := by
  unfold ctorFields at h
  cases hf : D.ctors.find? (·.1 == c) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    cases h
    have hmem : e ∈ D.ctors := List.mem_of_find?_eq_some hf
    have hk : e.1 = c := by simpa using List.find?_some hf
    have he : e = (c, e.2) := by rw [← hk]
    rw [he] at hmem
    exact hmem

theorem isClo_inv {k : Key.CtorKey} (h : isClo k = true) : ∃ g n, k = .clo g n := by
  cases k with
  | src c => cases h
  | clo g n => exact ⟨g, n, rfl⟩

theorem ctorOk_sound {P : Program} {cert : ShapeCert} {fs : FunShapes} {c : CtorInfo}
    {args : List Arg} {τ : Shape} (h : ctorOk cert fs c args τ = true) :
    RhsOk P cert fs (.ctor c args) τ := by
  cases τ with
  | any => exact .ctorAny
  | data d =>
    simp only [ctorOk] at h
    cases hD : cert.data? d with
    | none => simp [hD] at h
    | some D =>
      simp only [hD] at h
      cases hf : ctorFields D c.key with
      | none => simp [hf] at h
      | some fl =>
        simp only [hf] at h
        exact .ctorData hD (ctorFields_mem hf) (argsOk_sound _ _ h)
  | enum ind =>
    simp only [ctorOk, Bool.and_eq_true] at h
    obtain ⟨hemp, hk⟩ := h
    have hnil : args = [] := by simpa using hemp
    subst hnil
    cases hE : cert.enum? ind with
    | none => simp [hE] at hk
    | some ks =>
      simp only [hE] at hk
      exact .ctorEnum hE (by simpa using hk)
  | fn a b =>
    simp only [ctorOk] at h
    obtain ⟨g, n, hk⟩ := isClo_inv h
    exact .ctorFn hk
  | _ => simp [ctorOk] at h

theorem projShape_ok {P : Program} {cert : ShapeCert} {fs : FunShapes} {x : Var}
    {c : Key.CtorKey} {i : Nat} {σ : Shape} (h : projShape P cert fs x c i = some σ) :
    RhsOk P cert fs (.proj x c i) σ := by
  unfold projShape at h
  split at h
  · rename_i d hx
    cases hD : cert.data? d with
    | none => simp [hD] at h
    | some D =>
      simp only [hD] at h
      cases hf : ctorFields D c with
      | none => simp [hf] at h
      | some fl =>
        simp only [hf] at h
        exact .projData hx hD (ctorFields_mem hf) h
  · split at h
    · rename_i hcond
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨hle, hs⟩, hi⟩ := hcond
      subst hi
      exact .projNat hs hle
    · cases h

/-- `rhsOk` decides a rule. -/
theorem rhsOk_sound {P : Program} {cert : ShapeCert} {fs : FunShapes} {r : Rhs} {τ : Shape}
    (h : rhsOk P cert fs r τ = true) : RhsOk P cert fs r τ := by
  cases r with
  | arg a => exact .arg (argOk_sound h)
  | ctor c args => exact ctorOk_sound h
  | proj x c i =>
    simp only [rhsOk, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · subst h
      exact .projAny
    · cases hp : projShape P cert fs x c i with
      | none => simp [hp] at h
      | some σ =>
        simp only [hp] at h
        exact .weaken (projShape_ok hp) h
  | prim op args =>
    simp only [rhsOk, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · subst h
      exact .primAny
    · exact .weaken (.prim (argShapes_ok fs args) (primShape_ok op _)) h
  | call g args =>
    simp only [rhsOk, Bool.and_eq_true] at h
    exact .weaken (.call (argsOk_sound _ _ h.1)) h.2

mutual

/-- `codeOk` decides `CodeOk`. -/
theorem codeOk_sound (P : Program) (cert : ShapeCert) (fs : FunShapes) :
    ∀ (c : Code), codeOk P cert fs c = true → CodeOk P cert fs c
  | .bind x r k, h => by
    simp only [codeOk, Bool.and_eq_true] at h
    exact .bind (rhsOk_sound h.1) (codeOk_sound P cert fs k h.2)
  | .jp j ps isRec body k, h => by
    simp only [codeOk, Bool.and_eq_true] at h
    exact .jp (paramsOk_sound _ _ h.1.1) (codeOk_sound P cert fs body h.1.2)
      (codeOk_sound P cert fs k h.2)
  | .jmp j args, h => by
    simp only [codeOk] at h
    exact .jmp (argsOk_sound _ _ h)
  | .case x alts d, h => by
    simp only [codeOk, Bool.and_eq_true] at h
    exact .case (altsOk_sound P cert fs alts h.1) (optOk_sound P cert fs d h.2)
  | .ret a, h => by
    simp only [codeOk] at h
    exact .ret (argOk_sound h)
  | .tcall g args, h => by
    simp only [codeOk, Bool.and_eq_true] at h
    exact .tcall (argsOk_sound _ _ h.1) h.2
  | .trap, _ => .trap

theorem altsOk_sound (P : Program) (cert : ShapeCert) (fs : FunShapes) :
    ∀ (alts : List Alt), altsOk P cert fs alts = true → AltsOk P cert fs alts
  | [], _ => .nil
  | .mk key body :: rest, h => by
    simp only [altsOk, Bool.and_eq_true] at h
    exact .cons (codeOk_sound P cert fs body h.1) (altsOk_sound P cert fs rest h.2)

theorem optOk_sound (P : Program) (cert : ShapeCert) (fs : FunShapes) :
    ∀ (d : Option Code), optOk P cert fs d = true → OptOk P cert fs d
  | none, _ => .absent
  | some c, h => by
    simp only [optOk] at h
    exact .present (codeOk_sound P cert fs c h)

end

theorem ctorsOk_sound :
    ∀ (l : List (Key.CtorKey × List Shape)), ctorsOk l = true →
      ∀ (c : Key.CtorKey) (fl fl' : List Shape), (c, fl) ∈ l → (c, fl') ∈ l → fl = fl'
  | [], _, _, _, _, h, _ => by cases h
  | e :: rest, hok, c, fl, fl', h1, h2 => by
    have hand : (!(rest.any (·.1 == e.1)) && ctorsOk rest) = true := hok
    rw [Bool.and_eq_true] at hand
    obtain ⟨hno, hrest⟩ := hand
    have hno' : ∀ fl'', (e.1, fl'') ∉ rest := by
      intro fl'' hm
      have hany : rest.any (·.1 == e.1) = true :=
        List.any_eq_true.2 ⟨(e.1, fl''), hm, by simp⟩
      rw [hany] at hno
      cases hno
    rcases List.mem_cons.1 h1 with h1 | h1 <;> rcases List.mem_cons.1 h2 with h2 | h2
    · exact (Prod.mk.inj (h1.trans h2.symm)).2
    · have hk : e.1 = c := by rw [← h1]
      exact absurd h2 (by rw [← hk]; exact hno' fl')
    · have hk : e.1 = c := by rw [← h2]
      exact absurd h1 (by rw [← hk]; exact hno' fl)
    · exact ctorsOk_sound rest hrest c fl fl' h1 h2

theorem wfOk_sound {cert : ShapeCert} (h : wfOk cert = true) : cert.WF := by
  intro d D hD c fl fl' h1 h2
  have hmem : D ∈ cert.datas := List.mem_of_getElem? hD
  exact ctorsOk_sound D.ctors (List.all_eq_true.1 h D hmem) c fl fl' h1 h2

/-- **The Boolean checker implies the rules.** -/
theorem check_checked {P : Program} {cert : ShapeCert} (h : check P cert = true) :
    Checked P cert := by
  have hand : (wfOk cert && P.funs.toList.all fun e => funOk P cert e.1 e.2) = true := h
  rw [Bool.and_eq_true] at hand
  refine ⟨wfOk_sound hand.1, ?_⟩
  intro f fd hfd
  have hmem : (f, fd) ∈ P.funs.toList := Src.NatMap.mem_toList hfd
  have hf : (paramsOk (cert.fn f) (fd.params.map (·.1)) (cert.fn f).params &&
      codeOk P cert (cert.fn f) fd.body) = true := List.all_eq_true.1 hand.2 (f, fd) hmem
  rw [Bool.and_eq_true] at hf
  exact ⟨paramsOk_sound _ _ hf.1, codeOk_sound P cert _ _ hf.2⟩

/-- **The checker is sound**: an accepted certificate states true facts of every run of every
function, for every array reader. -/
theorem check_sound (enc : ArrEnc) {P : Program} {cert : ShapeCert} (h : check P cert = true) :
    ShapeSound P cert enc :=
  checkSound enc P cert (check_checked h)

/-- The checker is sound from inside a body. -/
theorem check_codeSound (enc : ArrEnc) {P : Program} {cert : ShapeCert}
    (h : check P cert = true) {fs : FunShapes} {k : Nat} {ρ : Env} {c : Code} {v : Val}
    (hρ : EnvOk cert enc fs ρ) (hc : CodeOk P cert fs c) (heval : eval P k ρ [] c = .ok v) :
    ValOk cert enc fs.ret v :=
  codeSound enc P cert (check_checked h) fs k ρ c v hρ hc heval

end IxCC.Fir.Proof.Shape
