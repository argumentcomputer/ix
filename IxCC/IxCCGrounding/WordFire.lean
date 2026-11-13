import IxCCGrounding.WordAccel
import IxCCGrounding.Hyps

/-!
# F6w's meaning from the checked word facts (`IxCCGrounding.WordFire`, step W)

**The word clause** (`WordFacts`, decided by the check's conjunct `word`): every word entry
`c ↦ word w op thm` of `S` is a stored head (no level parameters, a binder for every argument), the
`Eq` basis is stored, and at the operation's width and at its result's (`WidthFacts`) the program's
tower pins have keys whose bridge and tower are stored as the word case reads them, the tower's
constructors in `S` without level parameters; and the entry's theorem states `wordStmtK` (or, at
`ofNat`, the operation is the bridge's own; `WordStmt`).

**`wordFires_of_facts`**: under the clause, F6w's meaning (`WordFires`) holds. F6w forces the
arguments and reads each as a word (`asWord?`) or, at `ofNat`, a literal; the sets they are related
to are the bridge's towers of those numbers (`tower_canon`) or the literal's set; the operation's set
applied to them is the bridge's tower of `WordOp.eval`'s word, or the literal of its `Nat`
(`wordAccel_of_eqns`); and F6w's result, the tower `mkWord?` builds or the literal, is related to it
(`relV_mkWord`). Laws: `proj_law`, `defn_value`, `cval_params`, `nat_accel`, `graded`, and `Model.mem`.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels Width WordOp WordResult)

universe w

/-- **A width's facts**: the program's tower pins with the keys `tk`, the bridge and the tower stored
as the word case reads them, and the tower's constructors in `S` without level parameters. -/
structure WidthFacts (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) (w : Width) (tk : TowKeys) : Prop where
  pins : TowPins p κ w tk
  bridge : ∃ kB kR kS, BridgeStored env tk w.bits w.size kB kR kS
  tower : ∃ ta, TowerStored env tk ta
  inS : ∀ c, (p.wordCtor? w = some c ∨ p.known.bitVecOfFin = some c ∨ p.known.finMk = some c) →
    S c ∧ lpsOf c = []

/-- **One word entry's facts**: the head stored, the `Eq` basis, the width's and the result width's
facts, the statement. -/
def WordEntryFacts (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) (c : CId) (w : Width) (op : WordOp) (thm : CId) : Prop :=
  (∃ ci : ConstantInfo .anon, env.find? (κ c) = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    op.arity ≤ kPis ci.toConstantVal.type) ∧
  EqBasis env ∧
  ∃ tk tk', WidthFacts p env κ lpsOf S w tk ∧ WidthFacts p env κ lpsOf S (op.resultWidth w) tk' ∧
    WordStmt env (κ c) (κ thm) w op tk tk'

/-- **The word clause** (step W): every word entry of `S` has its facts. -/
def WordFacts (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) : Prop :=
  ∀ c w op thm, S c → p.table.resolveOf c = some (.word w op thm) →
    WordEntryFacts p env κ lpsOf S c w op thm

/-- What F6w returns a value on: `ofNat` on a literal, a unary operation on a word, a binary one on
two words. -/
theorem wordValue_ok {p : Program} {w : Width} {op : WordOp} {vs : List Value} {v : Value}
    (h : p.wordValue w op vs = .ok v) :
    (∃ a x, vs = [a] ∧ op.arity = 1 ∧
      (op = .ofNat ∧ a = .lit x ∨ op ≠ .ofNat ∧ p.asWord? w a = some x) ∧
      p.wordResult (op.eval w x 0) = .ok v) ∨
    (∃ a b x y, vs = [a, b] ∧ op.arity = 2 ∧ p.asWord? w a = some x ∧ p.asWord? w b = some y ∧
      p.wordResult (op.eval w x y) = .ok v) := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [Program.wordValue] at h
  · left
    unfold Program.wordValue at h
    by_cases h1 : op.arity = 1
    · simp only [h1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i x hx
        refine ⟨a, x, rfl, h1, ?_, h⟩
        by_cases hO : op = .ofNat
        · subst hO
          left
          cases a <;> simp at hx
          exact ⟨rfl, by rw [hx]⟩
        · right
          refine ⟨hO, ?_⟩
          split at hx
          · exact absurd rfl hO
          · exact absurd rfl hO
          · exact hx
      · cases h
    · simp [h1] at h
  · right
    unfold Program.wordValue at h
    by_cases h2 : op.arity = 2
    · simp only [h2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i x y hx hy
        exact ⟨a, b, x, y, rfl, h2, hx, hy, h⟩
      · cases h
    · simp [h2] at h
  · simp [Program.wordValue] at h

section Fire

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env} {p : Program}
  {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop}

/-- **F6w's meaning from the word clause.** -/
theorem wordFires_of_facts (hL : LawsCore M) (hPL : ProjLaw M.cval env)
    (hgr : GradedLaw M.cval env) (hN : NatBasis env) (hWF : WordFacts p env κ lpsOf S) :
    WordFires M p κ lpsOf S Ok := by
  intro c w op thm hS hr
  obtain ⟨hhead, hE, tk, tk', hw, hw', hst⟩ := hWF c w op thm hS hr
  refine ⟨hhead, ?_⟩
  intro φ vs As v hrel hwv
  obtain ⟨ci, hfc, hlc, -⟩ := hhead
  have hkc : KeyStored env (κ c) := ⟨ci, hfc, hlc⟩
  obtain ⟨kB, kR, kS, hB⟩ := hw.bridge
  obtain ⟨ta, hT⟩ := hw.tower
  -- F6w's result is related to the operation's set at the argument sets
  have hres : ∀ x y, (op = .ofNat ∨ x < w.size) → y < w.size →
      p.wordResult (op.eval w x y) = .ok v →
      RelV M p κ lpsOf S Ok v ((wordArgs M tk w op φ x y).foldl app (M.cval (κ c) φ)) := by
    intro x y hx hy hwr
    obtain ⟨hword, hnat⟩ :=
      wordAccel_of_eqns M hL.nat_accel hN hE hw.bridge hw'.bridge hkc hst φ hx hy
    cases hev : op.eval w x y with
    | word w' n =>
      rw [hev] at hwr
      simp only [Program.wordResult] at hwr
      cases hmk : p.mkWord? w' n with
      | none => rw [hmk] at hwr; simp [IxCC.Sem.Result.ofOption] at hwr
      | some v' =>
        rw [hmk] at hwr
        simp only [IxCC.Sem.Result.ofOption, IxCC.Sem.Result.ok.injEq] at hwr
        subst hwr
        have hw'eq := eval_word_width hev
        subst hw'eq
        have hn := WordOp.eval_word_lt w op x y hx hy _ _ hev
        rw [hword _ n hev]
        obtain ⟨kB', kR', kS', hB'⟩ := hw'.bridge
        obtain ⟨ta', hT'⟩ := hw'.tower
        exact relV_mkWord hL.nat_accel hN hgr hB' hT' hw'.pins hw'.inS hn hmk φ
    | nat n =>
      rw [hev] at hwr
      simp only [Program.wordResult, IxCC.Sem.Result.ok.injEq] at hwr
      subst hwr
      rw [hnat n hev]
      exact relV_lit_intro hN φ n
    | dec b => rw [hev] at hwr; simp [Program.wordResult] at hwr
  rcases wordValue_ok hwv with ⟨a, x, rfl, h1, hax, hwr⟩ | ⟨a, b, x, y, rfl, h2, hx, hy, hwr⟩
  · cases hrel with
    | cons hXa hnil =>
      cases hnil
      rcases hax with ⟨rfl, rfl⟩ | ⟨hO, hx⟩
      · have hXa' := relV_lit_eq hL hN φ hXa
        subst hXa'
        have h := hres x 0 (.inl rfl) (Width.size_pos w) hwr
        have hargs : wordArgs M tk w .ofNat φ x 0 = [litSet M φ x] := by simp [wordArgs]
        rw [hargs] at h
        exact h
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hxs⟩ := asWord?_some hx
        have hXa' := tower_canon hL hPL hgr hN hB hT hw.pins rfl hXa hx φ
        subst hXa'
        have h := hres x 0 (.inr hxs) (Width.size_pos w) hwr
        have h2 : ¬ op.arity = 2 := by rw [h1]; decide
        have hargs : wordArgs M tk w op φ x 0 = [towV M tk w.bits w.size φ x] := by
          simp [wordArgs, hO, h2]
        rw [hargs] at h
        exact h
  · cases hrel with
    | cons hXa hrest =>
      cases hrest with
      | cons hXb hnil =>
        cases hnil
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hxs⟩ := asWord?_some hx
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hys⟩ := asWord?_some hy
        have hXa' := tower_canon hL hPL hgr hN hB hT hw.pins rfl hXa hx φ
        have hXb' := tower_canon hL hPL hgr hN hB hT hw.pins rfl hXb hy φ
        subst hXa' hXb'
        have hne : op ≠ .ofNat := by rintro rfl; simp [WordOp.arity] at h2
        have h := hres x y (.inr hxs) hys hwr
        have hargs : wordArgs M tk w op φ x y =
            [towV M tk w.bits w.size φ x, towV M tk w.bits w.size φ y] := by
          simp [wordArgs, hne, h2]
        rw [hargs] at h
        exact h

end Fire

end IxCC.Grounding
