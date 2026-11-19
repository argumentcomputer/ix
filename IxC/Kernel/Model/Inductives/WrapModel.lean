module

public import IxC.Kernel.Model.Swap
public import IxC.Kernel.Model.IndCons
public import IxC.Kernel.Model.Rules.RedSoundKit
public import IxC.Kernel.Semantics.Inductives.WrapRelFacts
import IxC.Kernel.Model.Annot.BitLevels
import IxC.Kernel.Model.Annot.BitLemmas
import IxC.Kernel.Model.Annot.BitShift
import IxC.Kernel.Verify.EnvWF

public section

/-!
# A stored recursor at its declared type

A block may store its recursor at the declared type and rules, related to the generated ones by
`WrapRel` (at binder domains the generated term carries type-annotation wrappers the declared one
does not). This file moves the model of the generated record to the declared one.

* **The wrapper, in the model.** A wrapper's value `λ x₁ … xₖ, x₁` reads, with every λ's datum
  nonzero, to a chain of graph-regime abstractions (`WrapperA`). Applied to `k` arguments under a
  grading, it is its first argument (`WrapperA.apply`): the grading of each application puts the
  graph in a graph-regime product (a graph is never the proof point), whose domain the argument
  inhabits, and the graph's domain contains the product's (`graph_dom_of_mem_piSet`).
* **The readings** (`wrapRel_read`): at a declared term without `let`, the declared reading is
  the generated one with wrappers consumed at binder domains (`AW`); `AW` keeps the grading and
  the interpretation (`AW.sem`), and moves a value-level fit from the declared telescope to the
  generated one (`AW.teleFit`).
* **The install** (`recDeclaredStep`): the model storing the generated recursor gives one storing
  the declared one, with the same leaf, through the recursor-cons install at its own hypotheses:
  the type facts by the readings, the capability laws and the other recursors' rules across the
  swap of one stored type (`swapCongr_ofCorr`, `CapsOk.swapRec`, `RecRuleLaw.swapP`), and the
  recursor's own rules by `RecRuleLaw.wrap`.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal RecRule IndCaps)
open Ix.Kernel.Model.Rules (PiChain piChain_succ_inv teleFit_of_teleFitPA PiChain.inst)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The wrapper, in the model -/

/-- `L` is a chain of `j` λs with nonzero data whose body is the variable bound `i` places
outside the chain. -/
inductive LamTo : Nat → Nat → AnnotTerm → Prop
  | ret (i : Nat) : LamTo 0 i (.bvar i)
  | lam {j i b : Nat} {T L : AnnotTerm} : b ≠ 0 → LamTo j (i + 1) L → LamTo (j + 1) i (.lam b T L)

/-- **A wrapper's reading at arity `k`**: `λ x₁ … xₖ, x₁` with nonzero data. -/
def WrapperA (k : Nat) (c : AnnotTerm) : Prop :=
  ∃ (b : Nat) (T L : AnnotTerm), c = .lam b T L ∧ b ≠ 0 ∧ 0 < k ∧ LamTo (k - 1) 0 L

/-- **A graph-regime abstraction applied under a grading is a β-step**: the grading puts the
graph in a product, never at a zero datum (a graph is not the proof point), so the argument lies
in the product's domain, which the graph's contains. -/
theorem interp_app_lamR {ρ : Nat → V} {f a : AnnotTerm} {b : Nat} {A : V} {F : V → V}
    (hb : b ≠ 0) (hf : interp V ρ f = lamR b A F) (hwd : WellDenoted V ρ (.app f a)) :
    interp V ρ (.app f a) = F (interp V ρ a) := by
  rw [WellDenoted_app] at hwd
  obtain ⟨-, -, v, A', B, hmem, ha, -⟩ := hwd
  rw [hf, lamR_pos hb] at hmem
  rw [interp_app, hf, lamR_pos hb]
  by_cases hv : v = 0
  · subst hv
    rw [piR_zero] at hmem
    exact absurd (mem_truthVal.mp hmem).2 graph_ne_pt
  · rw [piR_pos hv] at hmem
    exact app_graph (graph_dom_of_mem_piSet hmem _ ha)

theorem wellDenoted_mkAppN_head {ρ : Nat → V} :
    ∀ {as : List AnnotTerm} {X : AnnotTerm},
      WellDenoted V ρ (AnnotTerm.mkAppN X as) → WellDenoted V ρ X
  | [], _, h => h
  | a :: as, X, h => by
    have h' := wellDenoted_mkAppN_head (as := as) (X := .app X a) h
    rw [WellDenoted_app] at h'
    exact h'.1

theorem annotValid_mkAppN_head {ρ : Nat → V} :
    ∀ {as : List AnnotTerm} {X : AnnotTerm},
      AnnotValid V ρ (AnnotTerm.mkAppN X as) → AnnotValid V ρ X
  | [], _, h => h
  | a :: as, X, h => by
    have h' := annotValid_mkAppN_head (as := as) (X := .app X a) h
    rw [AnnotValid_app] at h'
    exact h'.1

theorem LamTo.apply {j i : Nat} {L : AnnotTerm} (hL : LamTo j i L) :
    ∀ (σ ρ : Nat → V) (H : AnnotTerm) (as : List AnnotTerm), as.length = j →
      interp V ρ H = interp V σ L → WellDenoted V ρ (AnnotTerm.mkAppN H as) →
      interp V ρ (AnnotTerm.mkAppN H as) = σ i := by
  induction hL with
  | ret i =>
    intro σ ρ H as hlen hH _
    obtain rfl := List.length_eq_zero_iff.mp hlen
    exact hH
  | @lam j i b T L hb _ ih =>
    intro σ ρ H as hlen hH hwd
    match as, hlen with
    | a :: as', hlen =>
      have hwdA : WellDenoted V ρ (.app H a) := wellDenoted_mkAppN_head (as := as') hwd
      have hstep : interp V ρ (.app H a) = interp V (cons (interp V ρ a) σ) L :=
        interp_app_lamR (A := interp V σ T) (F := fun x => interp V (cons x σ) L) hb
          (by rw [hH]; rfl) hwdA
      exact ih (cons (interp V ρ a) σ) ρ (.app H a) as' (by simpa using hlen) hstep hwd

/-- **A wrapper applied to its arity is its first argument**, under a grading. -/
theorem WrapperA.apply {k : Nat} {c : AnnotTerm} (hc : WrapperA k c) {ρ : Nat → V}
    {a : AnnotTerm} {rest : List AnnotTerm} (hlen : rest.length + 1 = k)
    (hwd : WellDenoted V ρ (AnnotTerm.mkAppN c (a :: rest))) :
    interp V ρ (AnnotTerm.mkAppN c (a :: rest)) = interp V ρ a := by
  obtain ⟨b, T, L, rfl, hb, -, hL⟩ := hc
  have hwdA : WellDenoted V ρ (.app (.lam b T L) a) := wellDenoted_mkAppN_head (as := rest) hwd
  have hstep : interp V ρ (.app (.lam b T L) a) = interp V (cons (interp V ρ a) ρ) L :=
    interp_app_lamR (A := interp V ρ T) (F := fun x => interp V (cons x ρ) L) hb rfl hwdA
  exact hL.apply (cons (interp V ρ a) ρ) ρ (.app (.lam b T L) a) rest (by omega) hstep hwd

/-! ## Readings related up to consumed wrappers -/

/-- Zero or more consumed wrapper applications, at the reading. -/
inductive AStar : AnnotTerm → AnnotTerm → Prop
  | refl (A : AnnotTerm) : AStar A A
  | step {c a A' : AnnotTerm} {rest : List AnnotTerm} :
      WrapperA (rest.length + 1) c → AStar a A' → AStar (AnnotTerm.mkAppN c (a :: rest)) A'

/-- **The generated reading and the declared one**: equal, except that at a binder domain the
generated one may apply wrappers. -/
inductive AW : AnnotTerm → AnnotTerm → Prop
  | refl (X : AnnotTerm) : AW X X
  | app {f a f' a' : AnnotTerm} : AW f f' → AW a a' → AW (.app f a) (.app f' a')
  | lam {v : Nat} {A a A' b b' : AnnotTerm} :
      AStar A a → AW a A' → AW b b' → AW (.lam v A b) (.lam v A' b')
  | pi {u u' v : Nat} {A a A' B B' : AnnotTerm} :
      AStar A a → AW a A' → AW B B' → AW (.pi u v A B) (.pi u' v A' B')
  | fst {e e' : AnnotTerm} : AW e e' → AW (.fst e) (.fst e')
  | snd {e e' : AnnotTerm} : AW e e' → AW (.snd e) (.snd e')

theorem AStar.sem {A a : AnnotTerm} (h : AStar A a) :
    ∀ ρ : Nat → V, WellDenotedV V ρ A → WellDenotedV V ρ a ∧ interp V ρ A = interp V ρ a := by
  induction h with
  | refl => intro ρ hA; exact ⟨hA, rfl⟩
  | @step c a A' rest hc _ ih =>
    intro ρ hA
    have hwa : WellDenotedV V ρ a := by
      refine ⟨?_, ?_⟩
      · have h := wellDenoted_mkAppN_head (as := rest) (X := .app c a) hA.1
        rw [WellDenoted_app] at h
        exact h.2.1
      · have h := annotValid_mkAppN_head (as := rest) (X := .app c a) hA.2
        rw [AnnotValid_app] at h
        exact h.2
    obtain ⟨h1, h2⟩ := ih ρ hwa
    exact ⟨h1, (hc.apply rfl hA.1).trans h2⟩

/-- **The relation keeps the grading and the interpretation.** -/
theorem AW.sem {X Y : AnnotTerm} (h : AW X Y) :
    ∀ ρ : Nat → V, WellDenotedV V ρ X → WellDenotedV V ρ Y ∧ interp V ρ X = interp V ρ Y := by
  induction h with
  | refl => intro ρ hX; exact ⟨hX, rfl⟩
  | app _ _ ihf iha =>
    intro ρ hX
    obtain ⟨hwd, hav⟩ := hX
    rw [WellDenoted_app] at hwd
    rw [AnnotValid_app] at hav
    obtain ⟨hwf, hwa, v, A, B, hfm, ham, hz⟩ := hwd
    obtain ⟨hf1, hf2⟩ := ihf ρ ⟨hwf, hav.1⟩
    obtain ⟨ha1, ha2⟩ := iha ρ ⟨hwa, hav.2⟩
    refine ⟨⟨?_, ?_⟩, by rw [interp_app, interp_app, hf2, ha2]⟩
    · rw [WellDenoted_app]
      exact ⟨hf1.1, ha1.1, v, A, B, by rw [← hf2]; exact hfm, by rw [← ha2]; exact ham, hz⟩
    · rw [AnnotValid_app]; exact ⟨hf1.2, ha1.2⟩
  | @lam v A a A' b b' hs _ _ ihd ihb =>
    intro ρ hX
    obtain ⟨hwd, hav⟩ := hX
    rw [WellDenoted_lam] at hwd
    rw [AnnotValid_lam] at hav
    obtain ⟨hwA, hwb, B, hBm, hBz⟩ := hwd
    obtain ⟨hs1, hs2⟩ := hs.sem ρ ⟨hwA, hav.1⟩
    obtain ⟨hd1, hd2⟩ := ihd ρ hs1
    have hA : interp V ρ A = interp V ρ A' := hs2.trans hd2
    have hb : ∀ x, x ∈ˢ interp V ρ A' →
        WellDenotedV V (cons x ρ) b' ∧ interp V (cons x ρ) b = interp V (cons x ρ) b' :=
      fun x hx => ihb (cons x ρ) ⟨hwb x (hA ▸ hx), hav.2 x (hA ▸ hx)⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [WellDenoted_lam]
      refine ⟨hd1.1, fun x hx => (hb x hx).1.1, B, fun x hx => ?_, fun h0 x hx => hBz h0 x (hA ▸ hx)⟩
      rw [← (hb x hx).2]; exact hBm x (hA ▸ hx)
    · rw [AnnotValid_lam]; exact ⟨hd1.2, fun x hx => (hb x hx).1.2⟩
    · rw [interp_lam, interp_lam, hA]
      exact lamR_congr fun x hx => (hb x hx).2
  | @pi u u' v A a A' B B' hs _ _ ihd ihb =>
    intro ρ hX
    obtain ⟨hwd, hav⟩ := hX
    rw [WellDenoted_pi] at hwd
    rw [AnnotValid_pi] at hav
    obtain ⟨hwA, hwB⟩ := hwd
    obtain ⟨hvA, hvB, hvz⟩ := hav
    obtain ⟨hs1, hs2⟩ := hs.sem ρ ⟨hwA, hvA⟩
    obtain ⟨hd1, hd2⟩ := ihd ρ hs1
    have hA : interp V ρ A = interp V ρ A' := hs2.trans hd2
    have hb : ∀ x, x ∈ˢ interp V ρ A' →
        WellDenotedV V (cons x ρ) B' ∧ interp V (cons x ρ) B = interp V (cons x ρ) B' :=
      fun x hx => ihb (cons x ρ) ⟨hwB x (hA ▸ hx), hvB x (hA ▸ hx)⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [WellDenoted_pi]; exact ⟨hd1.1, fun x hx => (hb x hx).1.1⟩
    · rw [AnnotValid_pi]
      refine ⟨hd1.2, fun x hx => (hb x hx).1.2, fun h0 x hx => ?_⟩
      rw [← (hb x hx).2]; exact hvz h0 x (hA ▸ hx)
    · rw [interp_pi, interp_pi, hA]
      exact piR_congr fun x hx => (hb x hx).2
  | fst _ ih =>
    intro ρ hX
    obtain ⟨hwd, hav⟩ := hX
    rw [WellDenoted] at hwd
    rw [AnnotValid_fst] at hav
    obtain ⟨hwe, u, v, A, Bf, hm, hAu, hBv⟩ := hwd
    obtain ⟨he1, he2⟩ := ih ρ ⟨hwe, hav⟩
    refine ⟨⟨?_, by rw [AnnotValid_fst]; exact he1.2⟩, by rw [interp_fst, interp_fst, he2]⟩
    rw [WellDenoted]; exact ⟨he1.1, u, v, A, Bf, by rw [← he2]; exact hm, hAu, hBv⟩
  | snd _ ih =>
    intro ρ hX
    obtain ⟨hwd, hav⟩ := hX
    rw [WellDenoted] at hwd
    rw [AnnotValid_snd] at hav
    obtain ⟨hwe, u, v, A, Bf, hm, hAu, hBv⟩ := hwd
    obtain ⟨he1, he2⟩ := ih ρ ⟨hwe, hav⟩
    refine ⟨⟨?_, by rw [AnnotValid_snd]; exact he1.2⟩, by rw [interp_snd, interp_snd, he2]⟩
    rw [WellDenoted]; exact ⟨he1.1, u, v, A, Bf, by rw [← he2]; exact hm, hAu, hBv⟩

theorem AW.projAV : ∀ (n : Nat) {X X' : AnnotTerm}, AW X X' → AW (projAV n X) (projAV n X')
  | 0, _, _, h => .fst h
  | n + 1, _, _, h => AW.projAV n (.snd h)

theorem AW.projPair {i : Nat} {X X' Y : AnnotTerm} (h : AW X X')
    (hp : AnnotTerm.projPair? i X = some Y) :
    ∃ Y', AnnotTerm.projPair? i X' = some Y' ∧ AW Y Y' := by
  match i, hp with
  | 0, hp => exact ⟨_, rfl, by obtain rfl := Option.some.inj hp; exact .fst h⟩
  | 1, hp => exact ⟨_, rfl, by obtain rfl := Option.some.inj hp; exact .snd h⟩

theorem AW.piChain : ∀ (n : Nat) {X Y : AnnotTerm}, AW X Y → PiChain n X → PiChain n Y
  | 0, _, _, _, _ => trivial
  | n + 1, X, Y, h, hpc => by
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc
    cases h with
    | refl => exact hpc
    | pi _ _ hb => exact AW.piChain n hb hB

theorem piChain_of_le : ∀ {m n : Nat} {X : AnnotTerm}, m ≤ n → PiChain n X → PiChain m X
  | 0, _, _, _, _ => trivial
  | m + 1, 0, _, hle, _ => absurd hle (Nat.not_succ_le_zero m)
  | m + 1, n + 1, _, hle, hpc => by
    obtain ⟨_, _, _, B, rfl, hB⟩ := piChain_succ_inv hpc
    show PiChain m B
    exact piChain_of_le (by omega : m ≤ n) hB

/-- **A value-level fit moves from the declared telescope to the generated one.** -/
theorem AW.teleFit : ∀ (vs : List V) {X Y : AnnotTerm} {ρ : Nat → V} {r : V},
    AW X Y → WellDenotedV V ρ X → TeleFit V ρ Y vs r → ∃ r', TeleFit V ρ X vs r'
  | [], _, _, _, _, _, _, _ => ⟨_, .nil⟩
  | v :: vs, X, Y, ρ, r, h, hX, hfit => by
    cases hfit with
    | @cons _ u₀ w₀ A₀ B₀ _ _ _ hmem hrest =>
      cases h with
      | refl => exact ⟨r, .cons hmem hrest⟩
      | @pi u₁ _ _ A₁ a₁ _ B₁ _ hs hw hb =>
        obtain ⟨hwd, hav⟩ := hX
        rw [WellDenoted_pi] at hwd
        rw [AnnotValid_pi] at hav
        obtain ⟨hs1, hs2⟩ := hs.sem ρ ⟨hwd.1, hav.1⟩
        have hA : interp V ρ A₁ = interp V ρ A₀ := hs2.trans (hw.sem ρ hs1).2
        have hmA : v ∈ˢ interp V ρ A₁ := by rw [hA]; exact hmem
        obtain ⟨r', hr'⟩ := AW.teleFit vs hb ⟨hwd.2 v hmA, hav.2.1 v hmA⟩ hrest
        exact ⟨r', .cons hmA hr'⟩

/-- **A value-level fit moves from the generated telescope to the declared one.** -/
theorem AW.teleFit_fwd : ∀ (vs : List V) {X Y : AnnotTerm} {ρ : Nat → V} {r : V},
    AW X Y → WellDenotedV V ρ X → TeleFit V ρ X vs r → ∃ r', TeleFit V ρ Y vs r'
  | [], _, _, _, _, _, _, _ => ⟨_, .nil⟩
  | v :: vs, X, Y, ρ, r, h, hX, hfit => by
    cases hfit with
    | @cons _ _ _ A₁ B₁ _ _ _ hmA hrest =>
      cases h with
      | refl => exact ⟨r, .cons hmA hrest⟩
      | @pi _ _ _ _ _ A₀ _ B₀ hs hw hb =>
        obtain ⟨hwd, hav⟩ := hX
        rw [WellDenoted_pi] at hwd
        rw [AnnotValid_pi] at hav
        obtain ⟨hs1, hs2⟩ := hs.sem ρ ⟨hwd.1, hav.1⟩
        have hA : interp V ρ A₁ = interp V ρ A₀ := hs2.trans (hw.sem ρ hs1).2
        have hmA₀ : v ∈ˢ interp V ρ A₀ := by rw [← hA]; exact hmA
        obtain ⟨r', hr'⟩ := AW.teleFit_fwd vs hb ⟨hwd.2 v hmA, hav.2.1 v hmA⟩ hrest
        exact ⟨r', .cons hmA₀ hr'⟩

/-- The fit instantiates, under the ∀-chain guard (`teleFit_of_inst`'s converse). -/
theorem teleFit_inst {aa : AnnotTerm} :
    ∀ {L : List V} {E : AnnotTerm} {k : Nat} {ρ : Nat → V} {rest : V},
      PiChain L.length E →
      TeleFit V (instE k (interp V (shiftE k 0 ρ) aa) ρ) E L rest →
      ∃ rest', TeleFit V ρ (E.inst aa k) L rest'
  | [], _, _, _, _, _, _ => ⟨_, .nil⟩
  | y :: ys, E, k, ρ, rest, hpc, h => by
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc
    rw [AnnotTerm.inst_pi]
    cases h with
    | cons hmem hfit =>
      rw [cons_instE, ← shiftE_succ_cons y k ρ] at hfit
      obtain ⟨r', hr'⟩ := teleFit_inst (aa := aa) (k := k + 1) (ρ := cons y ρ) hB hfit
      exact ⟨r', .cons (by rw [interp_inst]; exact hmem) hr'⟩

/-- **A value-level fit is an annotation-level one**, under the ∀-chain guard
(`teleFit_of_teleFitPA`'s converse). -/
theorem teleFitPA_of_teleFit {ρ : Nat → V} :
    ∀ {as : List AnnotTerm} {T : AnnotTerm} {r : V},
      PiChain as.length T → TeleFit V ρ T (as.map (interp V ρ)) r →
      ∃ rest, TeleFitPA V ρ T as rest
  | [], T, _, _, _ => ⟨T, .nil⟩
  | a :: as, T, r, hpc, h => by
    have hpc' : PiChain (as.length + 1) T := hpc
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc'
    rw [List.map_cons] at h
    cases h with
    | cons hmem hfit =>
      have h0 : TeleFit V (instE 0 (interp V (shiftE 0 0 ρ) a) ρ) B
          (as.map (interp V ρ)) r := by
        rw [shiftE_zero_zero, instE_zero]; exact hfit
      obtain ⟨r', hr'⟩ := teleFit_inst (aa := a) (by rw [List.length_map]; exact hB) h0
      obtain ⟨rest, hrest⟩ := teleFitPA_of_teleFit (PiChain.inst a 0 hB) hr'
      exact ⟨rest, .cons hmem hrest⟩

/-- The head of an application spine moves along an equal interpretation, keeping the grading. -/
theorem wellDenotedV_mkAppN_congr {ρ : Nat → V} : ∀ (as : List AnnotTerm) {X X' : AnnotTerm},
    WellDenotedV V ρ X' → interp V ρ X = interp V ρ X' →
    WellDenotedV V ρ (AnnotTerm.mkAppN X as) → WellDenotedV V ρ (AnnotTerm.mkAppN X' as)
  | [], _, _, hX', _, _ => hX'
  | a :: as, X, X', hX', he, h => by
    have hpre : WellDenotedV V ρ (.app X a) :=
      ⟨wellDenoted_mkAppN_head (as := as) h.1, annotValid_mkAppN_head (as := as) h.2⟩
    obtain ⟨hwd, hav⟩ := hpre
    rw [WellDenoted_app] at hwd
    rw [AnnotValid_app] at hav
    obtain ⟨-, hwa, v, A, B, hm, ha, hz⟩ := hwd
    refine wellDenotedV_mkAppN_congr as (X := .app X a) (X' := .app X' a) ⟨?_, ?_⟩
      (by rw [interp_app, interp_app, he]) h
    · rw [WellDenoted_app]; exact ⟨hX'.1, hwa, v, A, B, by rw [← he]; exact hm, ha, hz⟩
    · rw [AnnotValid_app]; exact ⟨hX'.2, hav.2⟩

/-! ## The readings -/

section Read

variable {acval : Key md → (LevelParam → Nat) → AnnotTerm} {env : Env md}
  {φ : LevelParam → Nat}

theorem denoteMeta_const_inv {d : Nat} {n : Key md} {us : List Level} {fa : AnnotTerm}
    {ci : ConstantInfo md} (hf : env.find? n = some ci)
    (h : denoteMeta acval env φ d (.const n us) = some fa) :
    fa = acval n (Level.substFn φ ci.toConstantVal.levelParams us) := by
  rw [denoteMeta, hf] at h
  dsimp only at h
  split at h
  · exact (Option.some.inj h).symm
  · exact nomatch h

/-- A read term has no `let`. -/
theorem letFree_of_denoteMeta : ∀ (n : Nat) (e : Expr md), e.sizeB < n →
    ∀ (d : Nat) (ea : AnnotTerm), denoteMeta acval env φ d e = some ea → letFree e = true
  | 0, _, hlt, _, _, _ => absurd hlt (Nat.not_lt_zero _)
  | n + 1, e, hlt, d, ea, h => by
    cases e with
    | bvar | fvar | sort | const | lit => rfl
    | app f a =>
      obtain ⟨fa, aa, hfa, haa, -⟩ := denoteMeta_app_inv h
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      simp only [letFree, Bool.and_eq_true]
      exact ⟨letFree_of_denoteMeta n f (by omega) d fa hfa,
        letFree_of_denoteMeta n a (by omega) d aa haa⟩
    | lam t b m =>
      obtain ⟨ta, ba, hta, hba, -⟩ := denoteMeta_lam_inv h
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      simp only [letFree, Bool.and_eq_true]
      refine ⟨letFree_of_denoteMeta n t (by omega) d ta hta,
        letFree_of_instantiate1 _ b 0 (letFree_of_denoteMeta n _ ?_ (d + 1) ba hba)⟩
      rw [Ix.Kernel.Expr.sizeB_instantiate1 (.fvar d t) rfl]; omega
    | forallE t b m =>
      obtain ⟨ta, ba, hta, hba, -⟩ := denoteMeta_forallE_inv h
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      simp only [letFree, Bool.and_eq_true]
      refine ⟨letFree_of_denoteMeta n t (by omega) d ta hta,
        letFree_of_instantiate1 _ b 0 (letFree_of_denoteMeta n _ ?_ (d + 1) ba hba)⟩
      rw [Ix.Kernel.Expr.sizeB_instantiate1 (.fvar d t) rfl]; omega
    | letE t v b l => rw [denoteMeta] at h; exact nomatch h
    | proj s i e =>
      obtain ⟨ia, hia, -⟩ := denoteMeta_proj_inv h
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      exact letFree_of_denoteMeta n e (by omega) d ia hia

/-- After the binders already opened, a chain of `j` λs with `never` data whose body is the
free variable `d₀`. -/
inductive LamToE : Nat → Nat → Expr md → Prop
  | ret (d₀ : Nat) (t : Expr md) : LamToE 0 d₀ (.fvar d₀ t)
  | lam {j d₀ : Nat} {t b : Expr md} {m : Ix.Kernel.BinderMeta} :
      m.pw.isNever = true → LamToE j d₀ b → LamToE (j + 1) d₀ (.lam t b m)

theorem LamToE.instantiate1 {j d₀ : Nat} {e : Expr md} (h : LamToE j d₀ e) (v : Expr md) :
    ∀ i, LamToE j d₀ (e.instantiate1 v i) := by
  induction h with
  | ret d₀ t => intro i; exact .ret d₀ t
  | lam hn _ ih => intro i; exact .lam hn (ih (i + 1))

theorem lamToE_read : ∀ (j : Nat) {d₀ d : Nat} {e : Expr md} {ea : AnnotTerm},
    LamToE j d₀ e → d₀ < d → denoteMeta acval env φ d e = some ea → LamTo j (d - 1 - d₀) ea
  | 0, d₀, d, e, ea, h, _, hr => by
    cases h with
    | ret _ t =>
      rw [denoteMeta_fvar] at hr
      obtain rfl := Option.some.inj hr
      exact .ret _
  | j + 1, d₀, d, e, ea, h, hlt, hr => by
    cases h with
    | @lam _ _ t b m hn hb =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_lam_inv hr
      have h1 := lamToE_read j (hb.instantiate1 (.fvar d t) 0) (by omega : d₀ < d + 1) hba
      rw [show d + 1 - 1 - d₀ = (d - 1 - d₀) + 1 by omega] at h1
      exact .lam (pwBit_ne_zero_of_isNever hn φ) h1

theorem lamFirstArity_lamToE : ∀ (e : Expr md) (n k : Nat) (t : Expr md),
    lamFirstArity e (n + 1) = some k →
      n + 1 ≤ k ∧ LamToE (k - (n + 1)) 0 (e.instantiate1 (.fvar 0 t) n)
  | .lam t' b m, n, k, t, h => by
    rw [lamFirstArity] at h
    split at h
    · next hn =>
      obtain ⟨hle, hL⟩ := lamFirstArity_lamToE b (n + 1) k t h
      refine ⟨by omega, ?_⟩
      rw [show k - (n + 1) = (k - (n + 1 + 1)) + 1 by omega]
      exact .lam hn hL
    · exact nomatch h
  | .bvar i, n, k, t, h => by
    rw [lamFirstArity] at h
    split at h
    · next hc =>
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain rfl : i = n := by omega
      refine ⟨Nat.le_refl _, ?_⟩
      rw [Nat.sub_self]
      show LamToE 0 0 (if i = i then Expr.fvar 0 t else if i > i then .bvar (i - 1) else .bvar i)
      rw [if_pos rfl]
      exact .ret 0 t
    · exact nomatch h
  | .fvar _ _, _, _, _, h | .sort _, _, _, _, h | .const _ _, _, _, _, h
  | .app _ _, _, _, _, h | .forallE _ _ _, _, _, _, h | .letE _ _ _ _, _, _, _, h
  | .lit _, _, _, _, h | .proj _ _ _, _, _, _, h => by simp [lamFirstArity] at h

/-- **A wrapper's value reads to a wrapper.** -/
theorem wrapperA_of_read {v : Expr md} {k : Nat} {c : AnnotTerm} {ψ : LevelParam → Nat}
    (hl : lamFirstArity v 0 = some k) (hr : denoteMeta acval env ψ 0 v = some c) :
    WrapperA k c := by
  cases v
  case lam t b m =>
    rw [lamFirstArity] at hl
    split at hl
    · next hn =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_lam_inv hr
      obtain ⟨hle, hL⟩ := lamFirstArity_lamToE b 0 k t hl
      have h1 := lamToE_read (k - (0 + 1)) hL (by omega : 0 < 0 + 1) hba
      exact ⟨_, ta, ba, rfl, pwBit_ne_zero_of_isNever hn ψ, by omega, by simpa using h1⟩
    · exact nomatch hl
  all_goals simp [lamFirstArity] at hl

variable {find? : Key md → Option (ConstantInfo md)}
  (hfind : ∀ w ci, find? w = some ci → env.find? w = some ci)
  (hdef : ∀ (ψ : LevelParam → Nat) (cv : ConstantVal md) (value : Expr md),
    (∃ hint : Ix.Kernel.ReducibilityHint, ConstantInfo.defnInfo cv value hint ∈ env.consts) →
    denoteMeta acval env ψ 0 value = some (acval cv.name ψ))

include hfind hdef in
/-- **Consumed wrappers, read**: the reading of what the consumptions leave is the reading of the
domain with the wrappers' readings consumed. -/
theorem consumeStar_read {k : Nat} : ∀ {t a : Expr md}, ConsumeStar find? t a →
    ∀ {ta : AnnotTerm}, denoteMeta acval env φ k t = some ta →
      ∃ aa, denoteMeta acval env φ k a = some aa ∧ AStar ta aa := by
  intro t a h
  induction h with
  | refl t => intro ta hta; exact ⟨ta, hta, .refl _⟩
  | @step t a₁ c hc _ ih =>
    intro ta hta
    obtain ⟨w, us, rest, rfl, hw⟩ := consumeWrapper_inv hc
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hta
    cases hsp with
    | cons ha hsp' =>
      unfold wrapperArity at hw
      split at hw
      · next cv v hint hfw =>
        have hfe := hfind w _ hfw
        have hmem := Ix.Kernel.Semantics.Env.find?_mem hfe
        have hnm : cv.name = w := Ix.Kernel.Semantics.Env.find?_name hfe
        have hfa' := denoteMeta_const_inv hfe hfa
        have hv := hdef (Level.substFn φ cv.levelParams us) cv v ⟨hint, hmem⟩
        rw [hnm] at hv
        have hwr : WrapperA (rest.length + 1) fa := by
          rw [hfa']; exact wrapperA_of_read hw hv
        obtain ⟨aa, haa, hAS⟩ := ih ha
        refine ⟨aa, haa, AStar.step ?_ hAS⟩
        rw [← hsp'.length]; exact hwr
      · exact nomatch hw

private theorem forall₂_length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → xs.length = ys.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => congrArg (· + 1) (forall₂_length_eq h)

private theorem substFn_eq_of_forall₂ (φ : LevelParam → Nat) :
    ∀ (ks : List LevelParam) {us vs : List Level},
      Forall₂ (fun u v => ∀ ψ : LevelParam → Nat, u.eval ψ = v.eval ψ) us vs →
      Level.substFn φ ks us = Level.substFn φ ks vs
  | [], _, _, _ => rfl
  | _ :: _, [], [], .nil => rfl
  | _ :: ks, _ :: _, _ :: _, .cons huv hrest => by
    funext n
    simp only [Level.substFn, huv φ, substFn_eq_of_forall₂ φ ks hrest]

include hfind hdef in
/-- **The declared reading, from the generated one**, along `WrapT`. -/
theorem wrapT_read : ∀ (n : Nat) (g d : Expr md), g.sizeB < n → WrapT find? g d →
    ∀ (k : Nat) (ga : AnnotTerm), denoteMeta acval env φ k g = some ga →
      ∃ da, denoteMeta acval env φ k d = some da ∧ AW ga da := by
  intro n
  induction n with
  | zero => intro g d hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro g d hlt h k ga hg
    cases h with
    | bvar i => exact ⟨ga, hg, .refl _⟩
    | fvar i t t' =>
      rw [denoteMeta_fvar] at hg
      obtain rfl := Option.some.inj hg
      exact ⟨_, denoteMeta_fvar acval k i t', .refl _⟩
    | @sort u v huv =>
      refine ⟨ga, ?_, .refl _⟩
      simpa only [denoteMeta, huv φ] using hg
    | @const nm us vs huvs =>
      refine ⟨ga, ?_, .refl _⟩
      simp only [denoteMeta] at hg ⊢
      cases hf : env.find? nm with
      | none => simp only [hf] at hg; exact nomatch hg
      | some ci =>
        simp only [hf] at hg ⊢
        rw [← forall₂_length_eq huvs, ← substFn_eq_of_forall₂ φ ci.toConstantVal.levelParams huvs]
        exact hg
    | lit l => exact ⟨ga, hg, .refl _⟩
    | @app f a f' a' hf ha =>
      obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hg
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      obtain ⟨fa', hfa', hAf⟩ := ih f f' (by omega) hf k fa hfa
      obtain ⟨aa', haa', hAa⟩ := ih a a' (by omega) ha k aa haa
      refine ⟨.app fa' aa', ?_, .app hAf hAa⟩
      rw [denoteMeta_app, hfa', haa']
      try rfl
    | @lam t a t' b b' m m' hpw hs hw hb =>
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv hg
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      obtain ⟨aa, haa, hAS⟩ := consumeStar_read hfind hdef hs hta
      obtain ⟨ta', hta', hAd⟩ := ih a t' (by have := hs.sizeB_le; omega) hw k aa haa
      have hbi := WrapT.instantiate1 (WrapT.fvar k t t') hb 0
      obtain ⟨ba', hba', hAb⟩ := ih _ _
        (by rw [Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t) rfl]; omega) hbi (k + 1) ba hba
      refine ⟨.lam (pwBit φ m'.pw) ta' ba', ?_, by rw [hpw]; exact .lam hAS hAd hAb⟩
      rw [denoteMeta_lam, hta', hba']
      try rfl
    | @forallE t a t' b b' m m' hpw hs hw hb =>
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hg
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      obtain ⟨aa, haa, hAS⟩ := consumeStar_read hfind hdef hs hta
      obtain ⟨ta', hta', hAd⟩ := ih a t' (by have := hs.sizeB_le; omega) hw k aa haa
      have hbi := WrapT.instantiate1 (WrapT.fvar k t t') hb 0
      obtain ⟨ba', hba', hAb⟩ := ih _ _
        (by rw [Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t) rfl]; omega) hbi (k + 1) ba hba
      refine ⟨.pi 0 (pwBit φ m'.pw) ta' ba', ?_, by rw [hpw]; exact .pi hAS hAd hAb⟩
      rw [denoteMeta_forallE, hta', hba']
      try rfl
    | @proj s i e e' he =>
      obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv hg
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      obtain ⟨ia', hia', hAW⟩ := ih e e' (by omega) he k ia hia
      rcases hcase with ⟨entry, hfp, rfl⟩ | ⟨hfp, hdec⟩
      · refine ⟨projAV (i + entry.off) ia', ?_, AW.projAV _ hAW⟩
        rw [denoteMeta_proj, hia']
        show (match env.findProj? s i with
          | some entry => some (projAV (i + entry.off) ia')
          | none => AnnotTerm.projPair? i ia') = _
        rw [hfp]
      · obtain ⟨ga', hdec', hAW'⟩ := AW.projPair hAW hdec
        refine ⟨ga', ?_, hAW'⟩
        rw [denoteMeta_proj, hia']
        show (match env.findProj? s i with
          | some entry => some (projAV (i + entry.off) ia')
          | none => AnnotTerm.projPair? i ia') = _
        rw [hfp]; exact hdec'

include hfind hdef in
/-- **The declared reading, from the generated one**, at a declared term without `let`. -/
theorem wrapRel_read {g d : Expr md} (h : WrapRel find? g d) (hd : letFree d = true)
    {k : Nat} {ga : AnnotTerm} (hg : denoteMeta acval env φ k g = some ga) :
    ∃ da, denoteMeta acval env φ k d = some da ∧ AW ga da :=
  wrapT_read hfind hdef (g.sizeB + 1) g d (Nat.lt_succ_self _) (h.toWrapT hd) k ga hg

end Read

/-- Stripping `k` binders on the declared side pulls back along `WrapT`. -/
theorem WrapT.stripPis_back {find? : Key md → Option (ConstantInfo md)} :
    ∀ (k : Nat) {g d : Expr md} {bs' : List (Expr md × Ix.Kernel.BinderMeta)} {body' : Expr md},
      WrapT find? g d → d.stripPis k = some (bs', body') →
        ∃ bs body, g.stripPis k = some (bs, body) ∧ WrapT find? body body'
  | 0, g, _, _, _, h, hs => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact ⟨[], g, rfl, h⟩
  | k + 1, _, _, _, _, h, hs => by
    obtain ⟨_, _, _, _, rfl, hs0⟩ := Ix.Kernel.Semantics.stripPis_succ_inv hs
    cases h with
    | forallE _ _ _ hb =>
      obtain ⟨bs, body, h1, h2⟩ := WrapT.stripPis_back k hb hs0
      exact ⟨_, body, Ix.Kernel.Semantics.stripPis_succ_forallE h1, h2⟩

/-! ## One stored type swapped -/

/-- **Lookups that agree off recursors whose level parameters agree** induce the swap
congruences (`SwapShList.congr` at a correspondence that may change a recursor's type). -/
theorem swapCongr_ofCorr {E₀ E₃ : Env md}
    (hcorr : ∀ n, E₃.find? n = E₀.find? n ∨
      ∃ (cv cv' : ConstantVal md) (mI rP : Nat) (r r' : List (RecRule md)),
        cv'.levelParams = cv.levelParams ∧ E₀.find? n = some (.recInfo cv mI rP r) ∧
        E₃.find? n = some (.recInfo cv' mI rP r'))
    (hstr : Ix.Kernel.strLitSupported E₀ = Ix.Kernel.strLitSupported E₃) :
    Ix.Kernel.SwapCongr E₀ E₃ := by
  have hchk : ∀ (chk : Option (ConstantInfo md) → Bool),
      (∀ cv cv' mI rP rules rules',
        chk (some (.recInfo cv mI rP rules)) = chk (some (.recInfo cv' mI rP rules'))) →
      ∀ n, chk (E₀.find? n) = chk (E₃.find? n) := by
    intro chk hins n
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, r, r', -, h₀, h₃⟩
    · rw [heq]
    · rw [h₀, h₃]; exact hins cv cv' mI rP r r'
  have hnat : Ix.Kernel.natLitSupported E₀ = Ix.Kernel.natLitSupported E₃ := by
    unfold Ix.Kernel.natLitSupported
    rw [hchk Ix.Kernel.natIndOk (fun _ _ _ _ _ _ => rfl) Ix.Kernel.natName,
      hchk Ix.Kernel.natZeroOk (fun _ _ _ _ _ _ => rfl) Ix.Kernel.natZeroName,
      hchk Ix.Kernel.natSuccOk (fun _ _ _ _ _ _ => rfl) Ix.Kernel.natSuccName]
  refine ⟨?_, ?_, hnat, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, r, r', hl, h₀, h₃⟩
    · rw [heq]
    · rw [h₀, h₃]
      show some cv.levelParams = some cv'.levelParams
      rw [hl]
  · intro n
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, r, r', -, h₀, h₃⟩
    · rw [heq]
    · rw [h₀, h₃]; try rfl
  · exact hstr
  · intro c
    unfold Ix.Kernel.natOpGuard
    rw [hnat]
    congr 1
    · congr 1
      refine congrArg (List.all (Ix.Kernel.natOpDeps c)) (funext fun n => ?_)
      rcases hcorr n with heq | ⟨cv, cv', mI, rP, r, r', -, h₀, h₃⟩
      · rw [heq]
      · rw [h₀, h₃]; try rfl
    · split
      · congr 1
        · rcases hcorr Ix.Kernel.boolTrueName with heq | ⟨cv, cv', mI, rP, r, r', hl, h₀, h₃⟩
          · rw [heq]
          · rw [h₀, h₃]
            show cv.levelParams.isEmpty = cv'.levelParams.isEmpty
            rw [hl]
        · rcases hcorr Ix.Kernel.boolFalseName with heq | ⟨cv, cv', mI, rP, r, r', hl, h₀, h₃⟩
          · rw [heq]
          · rw [h₀, h₃]
            show cv.levelParams.isEmpty = cv'.levelParams.isEmpty
            rw [hl]
      · rfl
  · intro n ci hf hnr
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, r, r', -, h₀, h₃⟩
    · rw [← heq]; exact hf
    · rw [h₃] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv' mI rP r')
  · intro n ci hf hnr
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, r, r', -, h₀, h₃⟩
    · rw [heq]; exact hf
    · rw [h₀] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv mI rP r)

/-- **The capability laws cross a swap of stored recursors** (`EnvModelM.swapP`'s `caps_ok`, at a
correspondence that may change a recursor's type). -/
theorem CapsOk.swapRec {E₀ E₃ : Env md} (hcg : Ix.Kernel.SwapCongr E₀ E₃)
    (hcorr : ∀ n, E₃.find? n = E₀.find? n ∨
      ∃ (cv cv' : ConstantVal md) (mI rP : Nat) (r r' : List (RecRule md)),
        cv'.levelParams = cv.levelParams ∧ E₀.find? n = some (.recInfo cv mI rP r) ∧
        E₃.find? n = some (.recInfo cv' mI rP r'))
    {m₀ : EnvModel V E₀} {m₃ : EnvModel V E₃} (hac : m₃.acval = m₀.acval) (h : CapsOk m₀) :
    CapsOk m₃ := by
  have hde : ∀ (ψ : LevelParam → Nat) (d : Nat) (e : Expr md),
      denoteMeta m₀.acval E₀ ψ d e = denoteMeta m₀.acval E₃ ψ d e :=
    fun ψ d e => denoteMeta_swap hcg ψ d e
  have hsame : ∀ (n : Key md) (ci : ConstantInfo md),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (E₃.find? n = some ci ↔ E₀.find? n = some ci) :=
    fun n ci hnr => ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  obtain ⟨he, hu⟩ := h
  have hfam : ∀ (T : Key md) (caps : IndCaps md),
      Ix.Kernel.EtaFamilyStored E₃ T caps → Ix.Kernel.EtaFamilyStored E₀ T caps := by
    intro T caps hst
    obtain ⟨C, hCe, h1, ⟨cvC, cnP, cnF, hC⟩, h3⟩ := hst
    refine ⟨C, hCe, h1, ⟨cvC, cnP, cnF, (hsame _ _
      (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))).mp hC⟩, ?_⟩
    intro j hj
    obtain ⟨cv, mI, rP, rules, hfj⟩ := h3 j hj
    rcases hcorr (Ix.Kernel.projFnName T j) with heq | ⟨cv2, cv3, mI2, rP2, r2, r3, -, h₀, -⟩
    · exact ⟨cv, mI, rP, rules, by rw [← heq]; exact hfj⟩
    · exact ⟨cv2, mI2, rP2, r2, h₀⟩
  refine ⟨?_, ?_⟩
  · intro T cvT caps hf hcap hres hfamS φ' C hC us hus
    obtain ⟨TVa, hTVa, hokT, hlaw⟩ :=
      he T cvT caps ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))).mp hf) hcap
        hres (hfam T caps hfamS) φ' C hC us hus
    refine ⟨TVa, by rw [hac, ← hde]; exact hTVa, hokT, ?_⟩
    rw [hac]; exact hlaw
  · intro T cvT caps hf hcap hres φ' us hus
    obtain ⟨TVa, hTVa, hokT, hlaw⟩ :=
      hu T cvT caps ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))).mp hf) hcap
        hres φ' us hus
    refine ⟨TVa, by rw [hac, ← hde]; exact hTVa, hokT, ?_⟩
    rw [hac]; exact hlaw

/-! ## The recursor's rules at the declared type -/

/-- **A fired rule at the generated type and rule is one at the declared type and rule**: the
declared type's reading is related to the generated one's, so a fit at it is a fit at the
generated one (`AW.teleFit`); the declared rule's reading has the generated one's interpretation
and grading. -/
theorem RecRuleLaw.wrap {Eg Ed : Env md} (hcg : Ix.Kernel.SwapCongr Eg Ed)
    {mg : EnvModel V Eg} {mdl : EnvModel V Ed} (hac : mdl.acval = mg.acval)
    {φ : LevelParam → Nat} {n : Key md} {cvg cvd : ConstantVal md} {mI rP : Nat}
    {r : RecRule md} {rhsG rhsD : Expr md}
    (hlps : cvd.levelParams = cvg.levelParams) (hfire : r.fire = .plain)
    (htyG : ∀ ψ, ∃ ta, denoteMeta mg.acval Eg ψ 0 cvg.type = some ta)
    (htyOk : ∀ ψ ta, denoteMeta mg.acval Eg ψ 0 cvg.type = some ta →
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧ PiChain (mI + 1) ta)
    (hty : ∀ ψ ta, denoteMeta mg.acval Eg ψ 0 cvg.type = some ta →
      ∃ td, denoteMeta mg.acval Eg ψ 0 cvd.type = some td ∧ AW ta td)
    (hrhs : ∀ ψ ra, denoteMeta mg.acval Eg ψ 0 rhsG = some ra →
      ∃ rd, denoteMeta mg.acval Eg ψ 0 rhsD = some rd ∧ AW ra rd)
    (h : RecRuleLaw mg φ n cvg mI rP { r with rhs := rhsG }) :
    RecRuleLaw mdl φ n cvd mI rP { r with rhs := rhsD } := by
  have hde : ∀ (ψ : LevelParam → Nat) (d : Nat) (e : Expr md),
      denoteMeta mg.acval Eg ψ d e = denoteMeta mg.acval Ed ψ d e :=
    fun ψ d e => denoteMeta_swap hcg ψ d e
  have hcmp : ∀ (x : Expr md), Ix.Kernel.recFireComparands { r with rhs := x }
      = Ix.Kernel.recFireComparands { r with rhs := rhsG } := by
    intro x; funext lps us cvjLps args rP'; unfold Ix.Kernel.recFireComparands; rfl
  unfold RecRuleLaw at h ⊢
  obtain ⟨hle, h⟩ := h
  refine ⟨hle, fun us hus => ?_⟩
  have husg : us.length = cvg.levelParams.length := by rw [← hlps]; exact hus
  obtain ⟨Ra, hRa, hokRa, -, hlaw⟩ := h us husg
  rw [denotePInstLevels mg] at hRa
  obtain ⟨Rd, hRd, hAWR⟩ := hrhs _ Ra hRa
  have hsemR : ∀ ρ : Nat → V, WellDenotedV V ρ Rd ∧ interp V ρ Ra = interp V ρ Rd :=
    fun ρ => hAWR.sem ρ (hokRa ρ)
  refine ⟨Rd, ?_, fun ρ => (hsemR ρ).1, ?_, ?_⟩
  · rw [denotePInstLevels mdl, hac, ← hde, hlps]; exact hRd
  · intro lvls pins hf
    exact absurd (hfire.symm.trans hf) (fun h => nomatch h)
  · intro cvj cnP cnF hfc usj ρ xs ys TVa TVja restR restC hxl hyl hujl hlev hplain _ hidx
      hTVa hTVja hfitR hfitC
    rw [denotePInstLevels mdl, hac, ← hde, hlps] at hTVa
    obtain ⟨TVg, hTVg⟩ := htyG (Level.substFn φ cvg.levelParams us)
    obtain ⟨hokG, hpcG⟩ := htyOk _ TVg hTVg
    obtain ⟨Td, hTd, hAWT⟩ := hty _ TVg hTVg
    obtain rfl : TVa = Td := Option.some.inj (hTVa.symm.trans hTd)
    have hlen : (xs ++ [AnnotTerm.mkAppN (mdl.acval (RecRule.ctor { r with rhs := rhsD })
        (Level.substFn φ cvj.levelParams usj)) ys]).length = mI + 1 := by simp [hxl]
    have hpcD : PiChain (xs ++ [AnnotTerm.mkAppN (mdl.acval (RecRule.ctor { r with rhs := rhsD })
        (Level.substFn φ cvj.levelParams usj)) ys]).length TVa := by
      rw [hlen]; exact hAWT.piChain (mI + 1) hpcG
    have hfitV := teleFit_of_teleFitPA hpcD hfitR
    obtain ⟨r', hfitG⟩ := AW.teleFit _ hAWT (hokG ρ) hfitV
    obtain ⟨restG, hfitPA⟩ := teleFitPA_of_teleFit (by rw [hlen]; exact hpcG) hfitG
    rw [hac] at hfitPA hTVja
    rw [← hde] at hTVja
    rw [hlps, hcmp] at hlev
    obtain ⟨heq, hwd⟩ := hlaw cvj cnP cnF (hcg.findDown _ _ hfc (fun _ _ _ _ hcon => nomatch hcon))
      usj ρ xs ys TVg TVja restG restC hxl hyl hujl hlev hplain
      (fun lvls pins hf => absurd (hfire.symm.trans hf) (fun h => nomatch h)) hidx
      (by rw [denotePInstLevels mg]; exact hTVg) hTVja hfitPA hfitC
    rw [hac, hlps]
    refine ⟨heq.trans ?_, fun hxs hys => ?_⟩
    · rw [interp_mkAppN, interp_mkAppN, (hsemR ρ).2]
    · exact wellDenotedV_mkAppN_congr _ (hsemR ρ).1 (hsemR ρ).2 (hwd hxs hys)

/-! ## The install -/

/-- **A block storing its declared recursor**: the model storing the generated recursor gives one
storing the declared one, with the same leaf. The declared type's reading is related to the
generated one's, and each fired declared rule is a generated fired rule with its right-hand side
replaced by a related one. -/
theorem recDeclaredStep {μ : CheckMode} {E : Env md} (mpC : EnvModelM V μ E)
    {cvg cvd : ConstantVal md} {mI rP : Nat} {rg rd : List (RecRule md)}
    (mpg : EnvModelM V μ ⟨.recInfo cvg mI rP rg :: E.consts⟩)
    {A : (LevelParam → Nat) → AnnotTerm}
    (hac : mpg.base2.acval = acvalWith mpC.base2.acval cvg.name A)
    (hname : cvd.name = cvg.name) (hlps : cvd.levelParams = cvg.levelParams)
    (hfresh : E.find? cvg.name = none)
    (hnres : Ix.Kernel.reservedBasisNames.contains cvg.name = false)
    (hhead : ConsHead E (.recInfo cvd mI rP rd) A)
    (hpiG : ∃ k, 2 ≤ k ∧ PiToBvar k cvg.type) (hpiD : ∃ k, 2 ≤ k ∧ PiToBvar k cvd.type)
    (hty : ∀ ψ ta, denoteMeta mpg.base2.acval ⟨.recInfo cvg mI rP rg :: E.consts⟩ ψ 0 cvg.type
        = some ta →
      ∃ td, denoteMeta mpg.base2.acval ⟨.recInfo cvg mI rP rg :: E.consts⟩ ψ 0 cvd.type = some td ∧
        AW ta td)
    (hrules : ∀ rl ∈ rd, rl.fire ≠ .inert → ∃ (r : RecRule md) (rhsG : Expr md),
      rl = { r with rhs := rl.rhs } ∧ { r with rhs := rhsG } ∈ rg ∧ r.fire = .plain ∧
      (∀ ψ ta, denoteMeta mpg.base2.acval ⟨.recInfo cvg mI rP rg :: E.consts⟩ ψ 0 cvg.type
          = some ta → PiChain (mI + 1) ta) ∧
      ∀ ψ ra, denoteMeta mpg.base2.acval ⟨.recInfo cvg mI rP rg :: E.consts⟩ ψ 0 rhsG = some ra →
        ∃ rd', denoteMeta mpg.base2.acval ⟨.recInfo cvg mI rP rg :: E.consts⟩ ψ 0 rl.rhs
          = some rd' ∧ AW ra rd') :
    ∃ mpd : EnvModelM V μ ⟨.recInfo cvd mI rP rd :: E.consts⟩,
      mpd.base2.acval = mpg.base2.acval := by
  have hfG : ∀ n, (⟨.recInfo cvg mI rP rg :: E.consts⟩ : Env md).find? n
      = if cvg.name = n then some (.recInfo cvg mI rP rg) else E.find? n :=
    fun n => Ix.Kernel.Env.find?_cons
  have hfD : ∀ n, (⟨.recInfo cvd mI rP rd :: E.consts⟩ : Env md).find? n
      = if cvd.name = n then some (.recInfo cvd mI rP rd) else E.find? n :=
    fun n => Ix.Kernel.Env.find?_cons
  have hstr : Ix.Kernel.strLitSupported (⟨.recInfo cvg mI rP rg :: E.consts⟩ : Env md)
      = Ix.Kernel.strLitSupported (⟨.recInfo cvd mI rP rd :: E.consts⟩ : Env md) := by
    obtain ⟨kg, hkg, hpg⟩ := hpiG
    obtain ⟨kd, hkd, hpd⟩ := hpiD
    rw [(litGuards_cons_rec (mI := mI) (rP := rP) (r := rg) hfresh hpg hkg).2,
      (litGuards_cons_rec (mI := mI) (rP := rP) (r := rd)
        (by rw [hname]; exact hfresh) hpd hkd).2]
  have hcorr : ∀ n, (⟨.recInfo cvd mI rP rd :: E.consts⟩ : Env md).find? n
        = (⟨.recInfo cvg mI rP rg :: E.consts⟩ : Env md).find? n ∨
      ∃ (cv cv' : ConstantVal md) (mI' rP' : Nat) (r r' : List (RecRule md)),
        cv'.levelParams = cv.levelParams ∧
        (⟨.recInfo cvg mI rP rg :: E.consts⟩ : Env md).find? n = some (.recInfo cv mI' rP' r) ∧
        (⟨.recInfo cvd mI rP rd :: E.consts⟩ : Env md).find? n = some (.recInfo cv' mI' rP' r') := by
    intro n
    by_cases hn : cvg.name = n
    · refine Or.inr ⟨cvg, cvd, mI, rP, rg, rd, hlps, ?_, ?_⟩
      · rw [hfG, if_pos hn]
      · rw [hfD, if_pos (hname.trans hn)]
    · refine Or.inl ?_
      rw [hfD, hfG, if_neg hn,
        if_neg (fun h => hn (hname.symm.trans h))]
  have hcg := swapCongr_ofCorr hcorr hstr
  have hde : ∀ (ψ : LevelParam → Nat) (d : Nat) (e : Expr md),
      denoteMeta mpg.base2.acval ⟨.recInfo cvg mI rP rg :: E.consts⟩ ψ d e
        = denoteMeta mpg.base2.acval ⟨.recInfo cvd mI rP rd :: E.consts⟩ ψ d e :=
    fun ψ d e => denoteMeta_swap hcg ψ d e
  have hacv : acvalWith mpC.base2.acval (ConstantInfo.recInfo cvd mI rP rd).name A
      = mpg.base2.acval := by
    show acvalWith _ cvd.name A = _
    rw [hname, ← hac]
  have hAeq : A = mpg.base2.acval cvg.name := by rw [hac, acvalWith_self]
  have hmemG : ConstantInfo.recInfo cvg mI rP rg
      ∈ (⟨.recInfo cvg mI rP rg :: E.consts⟩ : Env md).consts := List.mem_cons_self
  obtain ⟨mpd, hmpd⟩ := declStep_preserves_of_ind_rec_cons mpC
    (c₀ := .recInfo cvd mI rP rd) (A := A) (by show E.find? cvd.name = none; rw [hname]; exact hfresh)
    (by show Ix.Kernel.reservedBasisNames.contains cvd.name = false; rw [hname]; exact hnres)
    ⟨_, _, _, _, rfl⟩ hhead
    (fun ψ k => by rw [hAeq]; exact mpg.base2.acval_closed _ ψ k)
    (fun ψ₁ ψ₂ hp => by
      rw [hAeq]
      exact mpg.base2.acval_params cvg.name _ (Ix.Kernel.Env.find?_cons_self _ _) ψ₁ ψ₂
        (fun q hq => hp q (by show q ∈ cvd.levelParams; rw [hlps]; exact hq)))
    (fun ψ ρ => by rw [hAeq]; exact mpg.base2.acval_wellDenoted _ ψ ρ)
    (fun ψ ρ => by rw [hAeq]; exact mpg.acval_validV _ ψ ρ)
    (fun ψ => by
      rw [hacv]
      obtain ⟨tg, htg⟩ := mpg.type_reads _ hmemG ψ
      obtain ⟨td, htd, -⟩ := hty ψ tg htg
      exact ⟨td, by rw [← hde]; exact htd⟩)
    (fun ψ ta hta ρ => by
      rw [hacv, ← hde] at hta
      obtain ⟨tg, htg⟩ := mpg.type_reads _ hmemG ψ
      obtain ⟨td, htd, hAW⟩ := hty ψ tg htg
      obtain rfl := Option.some.inj (hta.symm.trans htd)
      exact (hAW.sem ρ (mpg.type_wellDenotedV _ hmemG ψ tg htg ρ)).1)
    (fun ψ ta hta ρ => by
      rw [hacv, ← hde] at hta
      obtain ⟨tg, htg⟩ := mpg.type_reads _ hmemG ψ
      obtain ⟨td, htd, hAW⟩ := hty ψ tg htg
      obtain rfl := Option.some.inj (hta.symm.trans htd)
      rw [← (hAW.sem ρ (mpg.type_wellDenotedV _ hmemG ψ tg htg ρ)).2, hAeq]
      exact mpg.mem_type _ hmemG ψ tg htg ρ)
    (fun m₂ hm₂ => CapsOk.swapRec hcg hcorr (hm₂.trans hacv) mpg.caps_ok)
    (fun m₂ hm₂ φ => by
      have hm₂' : m₂.acval = mpg.base2.acval := hm₂.trans hacv
      intro n cv mI' rP' rules hf rl hrl hfire
      by_cases hn : cvg.name = n
      · subst hn
        have h₃' : (⟨.recInfo cvd mI rP rd :: E.consts⟩ : Env md).find? cvg.name
            = some (.recInfo cvd mI rP rd) := by
          rw [hfD, if_pos hname]
        rw [h₃'] at hf
        simp only [Option.some.injEq, ConstantInfo.recInfo.injEq] at hf
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
        obtain ⟨r, rhsG, hrl', hmemR, hplain, hpc, hrhs⟩ := hrules rl hrl hfire
        have hfG : (⟨.recInfo cvg mI rP rg :: E.consts⟩ : Env md).find? cvg.name
            = some (.recInfo cvg mI rP rg) := Ix.Kernel.Env.find?_cons_self _ _
        have hlawG := mpg.rec_rules φ cvg.name cvg mI rP rg hfG _ hmemR
          (by show r.fire ≠ .inert; rw [hplain]; exact fun h => nomatch h)
        rw [hrl']
        exact RecRuleLaw.wrap hcg hm₂' hlps hplain
          (fun ψ => mpg.type_reads _ hmemG ψ)
          (fun ψ ta hta => ⟨mpg.type_wellDenotedV _ hmemG ψ ta hta, hpc ψ ta hta⟩)
          hty hrhs hlawG
      · have heq : (⟨.recInfo cvd mI rP rd :: E.consts⟩ : Env md).find? n
            = (⟨.recInfo cvg mI rP rg :: E.consts⟩ : Env md).find? n := by
          rw [hfD, hfG, if_neg hn,
            if_neg (fun h => hn (hname.symm.trans h))]
        rw [heq] at hf
        exact RecRuleLaw.swapP hcg hm₂' (mpg.rec_rules φ n cv mI' rP' rules hf rl hrl hfire))
  exact ⟨mpd, hmpd.trans hacv⟩

/-! ## Symmetric wrapper readings and twin rule prefix semantics -/

/-- **Symmetric reading relation up to consumed wrappers**: equal, except that at a binder domain
either side may apply wrappers. -/
inductive SymAW : AnnotTerm → AnnotTerm → Prop
  | refl (X : AnnotTerm) : SymAW X X
  | app {f a f' a' : AnnotTerm} : SymAW f f' → SymAW a a' → SymAW (.app f a) (.app f' a')
  | lamL {v : Nat} {A a A' b b' : AnnotTerm} :
      AStar A a → SymAW a A' → SymAW b b' → SymAW (.lam v A b) (.lam v A' b')
  | lamR {v : Nat} {A A' a b b' : AnnotTerm} :
      AStar A' a → SymAW A a → SymAW b b' → SymAW (.lam v A b) (.lam v A' b')
  | piL {u u' v : Nat} {A a A' B B' : AnnotTerm} :
      AStar A a → SymAW a A' → SymAW B B' → SymAW (.pi u v A B) (.pi u' v A' B')
  | piR {u u' v : Nat} {A A' a B B' : AnnotTerm} :
      AStar A' a → SymAW A a → SymAW B B' → SymAW (.pi u v A B) (.pi u' v A' B')
  | fst {e e' : AnnotTerm} : SymAW e e' → SymAW (.fst e) (.fst e')
  | snd {e e' : AnnotTerm} : SymAW e e' → SymAW (.snd e) (.snd e')

theorem SymAW.of_AW {X Y : AnnotTerm} (h : AW X Y) : SymAW X Y := by
  induction h with
  | refl X => exact .refl X
  | app _ _ ihf iha => exact .app ihf iha
  | lam hs _ _ ihd ihb => exact .lamL hs ihd ihb
  | pi hs _ _ ihd ihb => exact .piL hs ihd ihb
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih

theorem SymAW.symm {X Y : AnnotTerm} (h : SymAW X Y) : SymAW Y X := by
  induction h with
  | refl X => exact .refl X
  | app _ _ ihf iha => exact .app ihf iha
  | lamL hs _ _ ihd ihb => exact .lamR hs ihd ihb
  | lamR hs _ _ ihd ihb => exact .lamL hs ihd ihb
  | piL hs _ _ ihd ihb => exact .piR hs ihd ihb
  | piR hs _ _ ihd ihb => exact .piL hs ihd ihb
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih

/-- **Symmetric wrapper relation preserves interpretation** when both sides are graded. -/
theorem SymAW.sem {X Y : AnnotTerm} (h : SymAW X Y) :
    ∀ ρ : Nat → V, WellDenotedV V ρ X → WellDenotedV V ρ Y → interp V ρ X = interp V ρ Y := by
  induction h with
  | refl => intro _ _ _; rfl
  | app _ _ ihf iha =>
    intro ρ hX hY
    obtain ⟨hwdX, havX⟩ := hX
    obtain ⟨hwdY, havY⟩ := hY
    rw [WellDenoted_app] at hwdX hwdY
    rw [AnnotValid_app] at havX havY
    rw [interp_app, interp_app,
      ihf ρ ⟨hwdX.1, havX.1⟩ ⟨hwdY.1, havY.1⟩,
      iha ρ ⟨hwdX.2.1, havX.2⟩ ⟨hwdY.2.1, havY.2⟩]
  | lamL hs _ _ ihd ihb =>
    intro ρ hX hY
    obtain ⟨hwdX, havX⟩ := hX
    obtain ⟨hwdY, havY⟩ := hY
    rw [WellDenoted_lam] at hwdX hwdY
    rw [AnnotValid_lam] at havX havY
    obtain ⟨hs1, hs2⟩ := hs.sem ρ ⟨hwdX.1, havX.1⟩
    have hA := hs2.trans (ihd ρ hs1 ⟨hwdY.1, havY.1⟩)
    rw [interp_lam, interp_lam, hA]
    exact lamR_congr fun x hx =>
      ihb (cons x ρ) ⟨hwdX.2.1 x (hA ▸ hx), havX.2 x (hA ▸ hx)⟩ ⟨hwdY.2.1 x hx, havY.2 x hx⟩
  | lamR hs _ _ ihd ihb =>
    intro ρ hX hY
    obtain ⟨hwdX, havX⟩ := hX
    obtain ⟨hwdY, havY⟩ := hY
    rw [WellDenoted_lam] at hwdX hwdY
    rw [AnnotValid_lam] at havX havY
    obtain ⟨hs1, hs2⟩ := hs.sem ρ ⟨hwdY.1, havY.1⟩
    have hA := (ihd ρ ⟨hwdX.1, havX.1⟩ hs1).trans hs2.symm
    rw [interp_lam, interp_lam, hA]
    exact lamR_congr fun x hx =>
      ihb (cons x ρ) ⟨hwdX.2.1 x (hA ▸ hx), havX.2 x (hA ▸ hx)⟩ ⟨hwdY.2.1 x hx, havY.2 x hx⟩
  | piL hs _ _ ihd ihb =>
    intro ρ hX hY
    obtain ⟨hwdX, havX⟩ := hX
    obtain ⟨hwdY, havY⟩ := hY
    rw [WellDenoted_pi] at hwdX hwdY
    rw [AnnotValid_pi] at havX havY
    obtain ⟨hs1, hs2⟩ := hs.sem ρ ⟨hwdX.1, havX.1⟩
    have hA := hs2.trans (ihd ρ hs1 ⟨hwdY.1, havY.1⟩)
    rw [interp_pi, interp_pi, hA]
    exact piR_congr fun x hx =>
      ihb (cons x ρ) ⟨hwdX.2 x (hA ▸ hx), havX.2.1 x (hA ▸ hx)⟩ ⟨hwdY.2 x hx, havY.2.1 x hx⟩
  | piR hs _ _ ihd ihb =>
    intro ρ hX hY
    obtain ⟨hwdX, havX⟩ := hX
    obtain ⟨hwdY, havY⟩ := hY
    rw [WellDenoted_pi] at hwdX hwdY
    rw [AnnotValid_pi] at havX havY
    obtain ⟨hs1, hs2⟩ := hs.sem ρ ⟨hwdY.1, havY.1⟩
    have hA := (ihd ρ ⟨hwdX.1, havX.1⟩ hs1).trans hs2.symm
    rw [interp_pi, interp_pi, hA]
    exact piR_congr fun x hx =>
      ihb (cons x ρ) ⟨hwdX.2 x (hA ▸ hx), havX.2.1 x (hA ▸ hx)⟩ ⟨hwdY.2 x hx, havY.2.1 x hx⟩
  | fst _ ih =>
    intro ρ hX hY
    obtain ⟨hwdX, havX⟩ := hX
    obtain ⟨hwdY, havY⟩ := hY
    rw [WellDenoted] at hwdX hwdY
    rw [AnnotValid_fst] at havX havY
    rw [interp_fst, interp_fst, ih ρ ⟨hwdX.1, havX⟩ ⟨hwdY.1, havY⟩]
  | snd _ ih =>
    intro ρ hX hY
    obtain ⟨hwdX, havX⟩ := hX
    obtain ⟨hwdY, havY⟩ := hY
    rw [WellDenoted] at hwdX hwdY
    rw [AnnotValid_snd] at havX havY
    rw [interp_snd, interp_snd, ih ρ ⟨hwdX.1, havX⟩ ⟨hwdY.1, havY⟩]

theorem SymAW.projAV : ∀ (n : Nat) {X X' : AnnotTerm}, SymAW X X' →
    SymAW (projAV n X) (projAV n X')
  | 0, _, _, h => .fst h
  | n + 1, _, _, h => SymAW.projAV n (.snd h)

theorem SymAW.projPair {i : Nat} {X X' Y Y' : AnnotTerm} (h : SymAW X X')
    (hp : AnnotTerm.projPair? i X = some Y) (hp' : AnnotTerm.projPair? i X' = some Y') :
    SymAW Y Y' := by
  match i, hp, hp' with
  | 0, hp, hp' =>
    obtain rfl := Option.some.inj hp
    obtain rfl := Option.some.inj hp'
    exact .fst h
  | 1, hp, hp' =>
    obtain rfl := Option.some.inj hp
    obtain rfl := Option.some.inj hp'
    exact .snd h

theorem SymAW.piChain_left : ∀ (n : Nat) {X Y : AnnotTerm}, SymAW X Y → PiChain n Y → PiChain n X
  | 0, _, _, _, _ => trivial
  | n + 1, _, _, h, hpc => by
    obtain ⟨_, _, _, _, rfl, hB⟩ := piChain_succ_inv hpc
    cases h with
    | refl => exact hpc
    | piL _ _ hb => exact SymAW.piChain_left n hb hB
    | piR _ _ hb => exact SymAW.piChain_left n hb hB

/-- **A value-level fit moves across `SymAW`** when both telescopes are graded. -/
theorem SymAW.teleFit : ∀ (vs : List V) {X Y : AnnotTerm} {ρ : Nat → V} {r : V},
    SymAW X Y → WellDenotedV V ρ X → WellDenotedV V ρ Y →
    TeleFit V ρ Y vs r → ∃ r', TeleFit V ρ X vs r'
  | [], _, _, _, _, _, _, _, _ => ⟨_, .nil⟩
  | v :: vs, _, _, ρ, r, h, hX, hY, hfit => by
    cases hfit with
    | @cons _ u₀ w₀ A₀ B₀ _ _ _ hmem hrest =>
      cases h with
      | refl => exact ⟨r, .cons hmem hrest⟩
      | piL hs hw hb =>
        obtain ⟨hwdX, havX⟩ := hX
        obtain ⟨hwdY, havY⟩ := hY
        rw [WellDenoted_pi] at hwdX hwdY
        rw [AnnotValid_pi] at havX havY
        obtain ⟨hs1, hs2⟩ := hs.sem ρ ⟨hwdX.1, havX.1⟩
        have hA := hs2.trans (hw.sem ρ hs1 ⟨hwdY.1, havY.1⟩)
        have hmA := hA.symm ▸ hmem
        obtain ⟨r', hr'⟩ := SymAW.teleFit vs hb ⟨hwdX.2 v hmA, havX.2.1 v hmA⟩
          ⟨hwdY.2 v hmem, havY.2.1 v hmem⟩ hrest
        exact ⟨r', .cons hmA hr'⟩
      | piR hs hw hb =>
        obtain ⟨hwdX, havX⟩ := hX
        obtain ⟨hwdY, havY⟩ := hY
        rw [WellDenoted_pi] at hwdX hwdY
        rw [AnnotValid_pi] at havX havY
        obtain ⟨hs1, hs2⟩ := hs.sem ρ ⟨hwdY.1, havY.1⟩
        have hA := (hw.sem ρ ⟨hwdX.1, havX.1⟩ hs1).trans hs2.symm
        have hmA := hA.symm ▸ hmem
        obtain ⟨r', hr'⟩ := SymAW.teleFit vs hb ⟨hwdX.2 v hmA, havX.2.1 v hmA⟩
          ⟨hwdY.2 v hmem, havY.2.1 v hmem⟩ hrest
        exact ⟨r', .cons hmA hr'⟩

section SymRead

variable {acval : Key md → (LevelParam → Nat) → AnnotTerm} {env : Env md}
  {φ : LevelParam → Nat}

/-- Terms related by `WrapT (fun _ => none)` (level-equivalent, no wrapper consumption) have
identical `denoteMeta` readings. -/
theorem denoteMeta_eq_of_wrapT_empty_aux : ∀ (n : Nat) (e₁ e₂ : Expr md), e₁.sizeB < n →
    WrapT (fun _ : Key md => (none : Option (ConstantInfo md))) e₁ e₂ →
    ∀ k : Nat, denoteMeta acval env φ k e₁ = denoteMeta acval env φ k e₂
  | 0, _, _, hlt, _, _ => absurd hlt (Nat.not_lt_zero _)
  | n + 1, _, _, hlt, h, k => by
    cases h with
    | bvar | lit => rfl
    | fvar i t t' => rw [denoteMeta_fvar, denoteMeta_fvar]
    | sort huv => simp only [denoteMeta, huv φ]
    | const huvs =>
      simp only [denoteMeta]
      cases hf : env.find? _ with
      | none => rfl
      | some ci =>
        dsimp only
        rw [forall₂_length_eq huvs, substFn_eq_of_forall₂ φ ci.toConstantVal.levelParams huvs]
    | app hf ha =>
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      rw [denoteMeta_app, denoteMeta_app,
        denoteMeta_eq_of_wrapT_empty_aux n _ _ (by omega) hf k,
        denoteMeta_eq_of_wrapT_empty_aux n _ _ (by omega) ha k]
    | @lam t a t' b b' m m' hpw hs hw hb =>
      rcases hs.eq_of_empty with rfl
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      have hbi := WrapT.instantiate1 (WrapT.fvar k t t') hb 0
      rw [denoteMeta_lam, denoteMeta_lam, hpw,
        denoteMeta_eq_of_wrapT_empty_aux n t t' (by omega) hw k,
        denoteMeta_eq_of_wrapT_empty_aux n _ _
          (by rw [Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t) rfl]; omega) hbi (k + 1)]
    | @forallE t a t' b b' m m' hpw hs hw hb =>
      rcases hs.eq_of_empty with rfl
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      have hbi := WrapT.instantiate1 (WrapT.fvar k t t') hb 0
      rw [denoteMeta_forallE, denoteMeta_forallE, hpw,
        denoteMeta_eq_of_wrapT_empty_aux n t t' (by omega) hw k,
        denoteMeta_eq_of_wrapT_empty_aux n _ _
          (by rw [Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t) rfl]; omega) hbi (k + 1)]
    | proj he =>
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      rw [denoteMeta_proj, denoteMeta_proj,
        denoteMeta_eq_of_wrapT_empty_aux n _ _ (by omega) he k]

theorem denoteMeta_eq_of_wrapT_empty {e₁ e₂ : Expr md}
    (h : WrapT (fun _ : Key md => (none : Option (ConstantInfo md))) e₁ e₂) (k : Nat) :
    denoteMeta acval env φ k e₁ = denoteMeta acval env φ k e₂ :=
  denoteMeta_eq_of_wrapT_empty_aux (e₁.sizeB + 1) e₁ e₂ (Nat.lt_succ_self _) h k

variable {find? : Key md → Option (ConstantInfo md)}
  (hfind : ∀ w ci, find? w = some ci → env.find? w = some ci)
  (hdef : ∀ (ψ : LevelParam → Nat) (cv : ConstantVal md) (value : Expr md),
    (∃ hint : Ix.Kernel.ReducibilityHint, ConstantInfo.defnInfo cv value hint ∈ env.consts) →
    denoteMeta acval env ψ 0 value = some (acval cv.name ψ))

include hfind hdef in
theorem symWrapT_read_aux : ∀ (n : Nat) (d₁ d₂ : Expr md), d₁.sizeB + d₂.sizeB < n →
    SymWrapT find? d₁ d₂ →
    ∀ (k : Nat) (da₁ da₂ : AnnotTerm),
      denoteMeta acval env φ k d₁ = some da₁ →
      denoteMeta acval env φ k d₂ = some da₂ →
      SymAW da₁ da₂ := by
  intro n
  induction n with
  | zero => intro d₁ d₂ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro d₁ d₂ hlt h k da₁ da₂ hd₁ hd₂
    cases h with
    | bvar | lit =>
      obtain rfl := Option.some.inj (hd₁.symm.trans hd₂)
      exact .refl _
    | fvar i t t' =>
      rw [denoteMeta_fvar] at hd₁ hd₂
      obtain rfl := Option.some.inj (hd₁.symm.trans hd₂)
      exact .refl _
    | sort huv =>
      simp only [denoteMeta, huv φ] at hd₁
      simp only [denoteMeta] at hd₂
      obtain rfl := Option.some.inj (hd₁.symm.trans hd₂)
      exact .refl _
    | @const cn _ _ huvs =>
      simp only [denoteMeta] at hd₁ hd₂
      cases hf : env.find? cn with
      | none => simp only [hf] at hd₁; exact nomatch hd₁
      | some ci =>
        simp only [hf] at hd₁ hd₂
        rw [forall₂_length_eq huvs, substFn_eq_of_forall₂ φ ci.toConstantVal.levelParams huvs] at hd₁
        obtain rfl := Option.some.inj (hd₁.symm.trans hd₂)
        exact .refl _
    | app hf ha =>
      obtain ⟨fa₁, aa₁, hfa₁, haa₁, rfl⟩ := denoteMeta_app_inv hd₁
      obtain ⟨fa₂, aa₂, hfa₂, haa₂, rfl⟩ := denoteMeta_app_inv hd₂
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      exact .app (ih _ _ (by omega) hf k fa₁ fa₂ hfa₁ hfa₂)
        (ih _ _ (by omega) ha k aa₁ aa₂ haa₁ haa₂)
    | @lamL t a t' b b' m m' hpw hs hw hb =>
      obtain ⟨ta₁, ba₁, hta₁, hba₁, rfl⟩ := denoteMeta_lam_inv hd₁
      obtain ⟨ta₂, ba₂, hta₂, hba₂, rfl⟩ := denoteMeta_lam_inv hd₂
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      obtain ⟨aa, haa, hAS⟩ := consumeStar_read hfind hdef hs hta₁
      have hAd := ih a t' (by have := hs.sizeB_le; omega) hw k aa ta₂ haa hta₂
      have hbi := SymWrapT.instantiate1 (SymWrapT.fvar k t t') hb 0
      have hAb := ih _ _ (by
        rw [Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t) rfl,
          Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t') rfl]; omega) hbi (k + 1) ba₁ ba₂ hba₁ hba₂
      rw [hpw]; exact .lamL hAS hAd hAb
    | @lamR t t' a b b' m m' hpw hs hw hb =>
      obtain ⟨ta₁, ba₁, hta₁, hba₁, rfl⟩ := denoteMeta_lam_inv hd₁
      obtain ⟨ta₂, ba₂, hta₂, hba₂, rfl⟩ := denoteMeta_lam_inv hd₂
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      obtain ⟨aa, haa, hAS⟩ := consumeStar_read hfind hdef hs hta₂
      have hAd := ih t a (by have := hs.sizeB_le; omega) hw k ta₁ aa hta₁ haa
      have hbi := SymWrapT.instantiate1 (SymWrapT.fvar k t t') hb 0
      have hAb := ih _ _ (by
        rw [Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t) rfl,
          Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t') rfl]; omega) hbi (k + 1) ba₁ ba₂ hba₁ hba₂
      rw [hpw]; exact .lamR hAS hAd hAb
    | @forallEL t a t' b b' m m' hpw hs hw hb =>
      obtain ⟨ta₁, ba₁, hta₁, hba₁, rfl⟩ := denoteMeta_forallE_inv hd₁
      obtain ⟨ta₂, ba₂, hta₂, hba₂, rfl⟩ := denoteMeta_forallE_inv hd₂
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      obtain ⟨aa, haa, hAS⟩ := consumeStar_read hfind hdef hs hta₁
      have hAd := ih a t' (by have := hs.sizeB_le; omega) hw k aa ta₂ haa hta₂
      have hbi := SymWrapT.instantiate1 (SymWrapT.fvar k t t') hb 0
      have hAb := ih _ _ (by
        rw [Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t) rfl,
          Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t') rfl]; omega) hbi (k + 1) ba₁ ba₂ hba₁ hba₂
      rw [hpw]; exact .piL hAS hAd hAb
    | @forallER t t' a b b' m m' hpw hs hw hb =>
      obtain ⟨ta₁, ba₁, hta₁, hba₁, rfl⟩ := denoteMeta_forallE_inv hd₁
      obtain ⟨ta₂, ba₂, hta₂, hba₂, rfl⟩ := denoteMeta_forallE_inv hd₂
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      obtain ⟨aa, haa, hAS⟩ := consumeStar_read hfind hdef hs hta₂
      have hAd := ih t a (by have := hs.sizeB_le; omega) hw k ta₁ aa hta₁ haa
      have hbi := SymWrapT.instantiate1 (SymWrapT.fvar k t t') hb 0
      have hAb := ih _ _ (by
        rw [Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t) rfl,
          Ix.Kernel.Expr.sizeB_instantiate1 (.fvar k t') rfl]; omega) hbi (k + 1) ba₁ ba₂ hba₁ hba₂
      rw [hpw]; exact .piR hAS hAd hAb
    | proj he =>
      obtain ⟨ia₁, hia₁, hcase₁⟩ := denoteMeta_proj_inv hd₁
      obtain ⟨ia₂, hia₂, hcase₂⟩ := denoteMeta_proj_inv hd₂
      simp only [Ix.Kernel.Expr.sizeB] at hlt
      have hSAW := ih _ _ (by omega) he k ia₁ ia₂ hia₁ hia₂
      rcases hcase₁ with ⟨entry₁, hfp₁, rfl⟩ | ⟨hfp₁, hdec₁⟩
      · rcases hcase₂ with ⟨entry₂, hfp₂, rfl⟩ | ⟨hfp₂, _⟩
        · obtain rfl := Option.some.inj (hfp₁.symm.trans hfp₂)
          exact SymAW.projAV _ hSAW
        · rw [hfp₁] at hfp₂; cases hfp₂
      · rcases hcase₂ with ⟨_, hfp₂, _⟩ | ⟨_, hdec₂⟩
        · rw [hfp₁] at hfp₂; cases hfp₂
        · exact SymAW.projPair hSAW hdec₁ hdec₂

include hfind hdef in
/-- **Readings of symmetrically wrapper-related terms are related by `SymAW`.** -/
theorem symWrapT_read {d₁ d₂ : Expr md} (h : SymWrapT find? d₁ d₂)
    {k : Nat} {da₁ da₂ : AnnotTerm}
    (hd₁ : denoteMeta acval env φ k d₁ = some da₁)
    (hd₂ : denoteMeta acval env φ k d₂ = some da₂) :
    SymAW da₁ da₂ :=
  symWrapT_read_aux hfind hdef (d₁.sizeB + d₂.sizeB + 1) d₁ d₂ (Nat.lt_succ_self _) h k da₁ da₂ hd₁ hd₂

include hfind hdef in
private theorem symWrapT_lam_step {d : Nat} {lC dl bl : Expr md} {mW : Ix.Kernel.BinderMeta}
    {La Dp : AnnotTerm}
    (hSym : SymWrapT find? lC (.lam dl bl mW))
    (hC : denoteMeta acval env φ d lC = some La)
    (hDl : denoteMeta acval env φ d dl = some Dp) :
    ∃ (dc bc : Expr md) (mC : Ix.Kernel.BinderMeta) (Dc Bc : AnnotTerm),
      lC = .lam dc bc mC ∧
      mC.pw = mW.pw ∧
      SymWrapT find? bc bl ∧
      La = .lam (pwBit φ mC.pw) Dc Bc ∧
      denoteMeta acval env φ d dc = some Dc ∧
      denoteMeta acval env φ (d + 1) (bc.instantiate1 (.fvar d dc) 0) = some Bc ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ Dc → WellDenotedV V ρ Dp →
        interp V ρ Dc = interp V ρ Dp := by
  cases hSym with
  | @lamL dc a _ bc _ mC _ hpw hs hd hb =>
    obtain ⟨Dc, Bc, hDc, hBc, rfl⟩ := denoteMeta_lam_inv hC
    obtain ⟨aa, haa, hAS⟩ := consumeStar_read hfind hdef hs hDc
    have hSAW := symWrapT_read hfind hdef hd haa hDl
    refine ⟨dc, bc, mC, Dc, Bc, rfl, hpw, hb, rfl, hDc, hBc, fun ρ hokDc hokDp => ?_⟩
    obtain ⟨hokAa, heq1⟩ := hAS.sem ρ hokDc
    exact heq1.trans (hSAW.sem ρ hokAa hokDp)
  | @lamR dc _ a bc _ mC _ hpw hs hd hb =>
    obtain ⟨Dc, Bc, hDc, hBc, rfl⟩ := denoteMeta_lam_inv hC
    obtain ⟨aa, haa, hAS⟩ := consumeStar_read hfind hdef hs hDl
    have hSAW := symWrapT_read hfind hdef hd hDc haa
    refine ⟨dc, bc, mC, Dc, Bc, rfl, hpw, hb, rfl, hDc, hBc, fun ρ hokDc hokDp => ?_⟩
    obtain ⟨hokAa, heq1⟩ := hAS.sem ρ hokDp
    exact (hSAW.sem ρ hokDc hokAa).trans heq1.symm

private theorem wellDenotedV_lam_transfer {v : Nat} {Dc Dp Bc Bw : AnnotTerm} {ρ : Nat → V}
    (hokC : WellDenotedV V ρ (.lam v Dc Bc))
    (hokDp : WellDenotedV V ρ Dp)
    (hDom : interp V ρ Dc = interp V ρ Dp)
    (hBody : ∀ x, x ∈ˢ interp V ρ Dp →
      WellDenotedV V (cons x ρ) Bw ∧ interp V (cons x ρ) Bc = interp V (cons x ρ) Bw) :
    WellDenotedV V ρ (.lam v Dp Bw) ∧
      interp V ρ (.lam v Dc Bc) = interp V ρ (.lam v Dp Bw) := by
  obtain ⟨hwdC, havC⟩ := hokC
  rw [WellDenoted_lam] at hwdC
  rw [AnnotValid_lam] at havC
  obtain ⟨-, -, B, hBm, hBz⟩ := hwdC
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [WellDenoted_lam]
    refine ⟨hokDp.1, fun x hx => (hBody x hx).1.1, B, fun x hx => ?_,
      fun h0 x hx => hBz h0 x (hDom ▸ hx)⟩
    rw [← (hBody x hx).2]
    exact hBm x (hDom ▸ hx)
  · rw [AnnotValid_lam]
    exact ⟨hokDp.2, fun x hx => (hBody x hx).1.2⟩
  · rw [interp_lam, interp_lam, hDom]
    exact lamR_congr fun x hx => (hBody x hx).2

include hfind hdef in
/-- **Base λ-prefix semantics**: `lW` follows `p` for `n` λs whose bodies match `lC` under
`WrapT (fun _ => none)` and `SymWrapT`. -/
theorem lamDomAlong_base_sem :
    ∀ (n d : Nat) {lC lW p rC rW : Expr md} {La Pa : AnnotTerm},
      SymWrapT find? lC lW →
      LamDomAlong n lW p rW →
      stripLams n lC = some rC →
      WrapT (fun _ : Key md => (none : Option (ConstantInfo md))) rC rW →
      denoteMeta acval env φ d lC = some La →
      denoteMeta acval env φ d p = some Pa →
      ∃ Lw : AnnotTerm,
        denoteMeta acval env φ d lW = some Lw ∧
        ∀ ρ : Nat → V, WellDenotedV V ρ La → WellDenotedV V ρ Pa →
          WellDenotedV V ρ Lw ∧ interp V ρ La = interp V ρ Lw
  | 0, d, lC, lW, _, rC, rW, La, _, _, hLam, hSC, hBase, hC, _ => by
    cases hLam
    simp only [stripLams, Option.some.injEq] at hSC
    subst hSC
    refine ⟨La, ?_, fun ρ hokC _ => ⟨hokC, rfl⟩⟩
    rw [← denoteMeta_eq_of_wrapT_empty hBase d]
    exact hC
  | n + 1, d, lC, lW, p, rC, rW, La, Pa, hSym, hLam, hSC, hBase, hC, hP => by
    cases hLam with
    | @succ _ dl bl dp bp _ mW mp hdom hLam' =>
      obtain ⟨Dp, Bp, hDp, hBp, rfl⟩ := denoteMeta_forallE_inv hP
      have hDl : denoteMeta acval env φ d dl = some Dp := by
        rw [denoteMeta_eq_of_wrapT_empty hdom d]; exact hDp
      obtain ⟨dc, bc, mC, Dc, Bc, rfl, hpw, hSymB, rfl, _, hBc, hDomEq⟩ :=
        symWrapT_lam_step (V := V) hfind hdef hSym hC hDl
      simp only [stripLams] at hSC
      have hSymB' := SymWrapT.instantiate1 (SymWrapT.fvar d dc dl) hSymB 0
      have hLam'' := LamDomAlong.instantiate1 (WrapT.fvar d dl dp) hLam' 0
      have hSC' := stripLams_instantiate1 n hSC (.fvar d dc) 0
      have hBase' := WrapT.instantiate1 (WrapT.fvar d dc dl) hBase n
      simp only [Nat.zero_add] at hLam'' hSC'
      obtain ⟨Bw, hBw, ih⟩ := lamDomAlong_base_sem n (d + 1) hSymB' hLam'' hSC' hBase' hBc hBp
      refine ⟨.lam (pwBit φ mW.pw) Dp Bw, ?_, fun ρ hokC hokP => ?_⟩
      · rw [denoteMeta_lam, hDl, hBw]; rfl
      · obtain ⟨hwdP, havP⟩ := hokP
        rw [WellDenoted_pi] at hwdP
        rw [AnnotValid_pi] at havP
        have hokDp : WellDenotedV V ρ Dp := ⟨hwdP.1, havP.1⟩
        have hokDc : WellDenotedV V ρ Dc := by
          obtain ⟨hwC, hvC⟩ := hokC
          rw [WellDenoted_lam] at hwC; rw [AnnotValid_lam] at hvC
          exact ⟨hwC.1, hvC.1⟩
        have hdom_eq := hDomEq ρ hokDc hokDp
        rw [hpw] at hokC ⊢
        refine wellDenotedV_lam_transfer hokC hokDp hdom_eq fun x hx => ?_
        obtain ⟨hwC, hvC⟩ := hokC
        rw [WellDenoted_lam] at hwC; rw [AnnotValid_lam] at hvC
        exact ih (cons x ρ) ⟨hwC.2.1 x (hdom_eq ▸ hx), hvC.2 x (hdom_eq ▸ hx)⟩
          ⟨hwdP.2 x hx, havP.2.1 x hx⟩

include hfind hdef in
/-- **Second segment of `TwinRuleMatch`**: walks `s` λs while carrying `mW` lifted by `s`,
weakening `mW`'s reading one binder at a time via `denoteMeta_weaken_top`, then finishes with
`lamDomAlong_base_sem` at `s = 0`. -/
theorem lamDomAlong_lifted_sem
    (hacl : ∀ (n : Key md) (ψ : LevelParam → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) :
    ∀ (s d nf : Nat) {lC lW p mW afterW sbC sbW : Expr md} {La Pa Ma : AnnotTerm},
      SymWrapT find? lC lW →
      LamDomAlong s lW p afterW →
      LamDomAlong nf afterW (mW.liftLooseBVars s 0) sbW →
      stripLams (s + nf) lC = some sbC →
      WrapT (fun _ : Key md => (none : Option (ConstantInfo md))) sbC sbW →
      Expr.WScoped d mW →
      denoteMeta acval env φ d lC = some La →
      denoteMeta acval env φ d p = some Pa →
      denoteMeta acval env φ d mW = some Ma →
      ∃ Lw : AnnotTerm,
        denoteMeta acval env φ d lW = some Lw ∧
        ∀ ρ : Nat → V, WellDenotedV V ρ La → WellDenotedV V ρ Pa → WellDenotedV V ρ Ma →
          WellDenotedV V ρ Lw ∧ interp V ρ La = interp V ρ Lw
  | 0, d, nf, lC, lW, _, mW, afterW, sbC, sbW, La, _, Ma, hSym, hLam1, hLam2, hSC, hBase,
      _, hC, _, hM => by
    cases hLam1
    rw [liftLooseBVars_zero] at hLam2
    simp only [Nat.zero_add] at hSC
    obtain ⟨Lw, hLw, hsem⟩ := lamDomAlong_base_sem (V := V) hfind hdef nf d hSym hLam2 hSC hBase hC hM
    exact ⟨Lw, hLw, fun ρ hokC _ hokM => hsem ρ hokC hokM⟩
  | s + 1, d, nf, lC, lW, p, mW, afterW, sbC, sbW, La, Pa, Ma, hSym, hLam1, hLam2, hSC, hBase,
      hwsM, hC, hP, hM => by
    cases hLam1 with
    | @succ _ dl bl dp bp _ mW_b mp hdom hLam1' =>
      obtain ⟨Dp, Bp, hDp, hBp, rfl⟩ := denoteMeta_forallE_inv hP
      have hDl : denoteMeta acval env φ d dl = some Dp := by
        rw [denoteMeta_eq_of_wrapT_empty hdom d]; exact hDp
      obtain ⟨dc, bc, mC, Dc, Bc, rfl, hpw, hSymB, rfl, _, hBc, hDomEq⟩ :=
        symWrapT_lam_step (V := V) hfind hdef hSym hC hDl
      rw [show s + 1 + nf = (s + nf) + 1 by omega] at hSC
      simp only [stripLams] at hSC
      have hSymB' := SymWrapT.instantiate1 (SymWrapT.fvar d dc dl) hSymB 0
      have hLam1'' := LamDomAlong.instantiate1 (WrapT.fvar d dl dp) hLam1' 0
      have hLam2' := LamDomAlong.instantiate1 (WrapT.fvar d dl dp) hLam2 s
      have hSC' := stripLams_instantiate1 (s + nf) hSC (.fvar d dc) 0
      have hBase' := WrapT.instantiate1 (WrapT.fvar d dc dl) hBase (s + nf)
      simp only [Nat.zero_add] at hLam1'' hSC'
      have hlift : (mW.liftLooseBVars (s + 1) 0).instantiate1 (.fvar d dp) s =
          mW.liftLooseBVars s 0 := by
        simpa only [Nat.zero_add] using liftLooseBVars_succ_instantiate1 (.fvar d dp) s mW 0
      rw [hlift] at hLam2'
      have hM' : denoteMeta acval env φ (d + 1) mW = some (Ma.liftN 1 0) := by
        rw [denoteMeta_weaken_top hacl hwsM, hM]; rfl
      obtain ⟨Bw, hBw, ih⟩ := lamDomAlong_lifted_sem hacl s (d + 1) nf hSymB' hLam1'' hLam2'
        hSC' hBase' (hwsM.mono (Nat.le_succ d)) hBc hBp hM'
      refine ⟨.lam (pwBit φ mW_b.pw) Dp Bw, ?_, fun ρ hokC hokP hokM => ?_⟩
      · rw [denoteMeta_lam, hDl, hBw]; rfl
      · obtain ⟨hwdP, havP⟩ := hokP
        rw [WellDenoted_pi] at hwdP
        rw [AnnotValid_pi] at havP
        have hokDp : WellDenotedV V ρ Dp := ⟨hwdP.1, havP.1⟩
        have hokDc : WellDenotedV V ρ Dc := by
          obtain ⟨hwC, hvC⟩ := hokC
          rw [WellDenoted_lam] at hwC; rw [AnnotValid_lam] at hvC
          exact ⟨hwC.1, hvC.1⟩
        have hdom_eq := hDomEq ρ hokDc hokDp
        rw [hpw] at hokC ⊢
        refine wellDenotedV_lam_transfer hokC hokDp hdom_eq fun x hx => ?_
        obtain ⟨hwC, hvC⟩ := hokC
        rw [WellDenoted_lam] at hwC; rw [AnnotValid_lam] at hvC
        have hokM' : WellDenotedV V (cons x ρ) (Ma.liftN 1 0) := by
          refine ⟨?_, ?_⟩
          · rw [WellDenoted_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons,
              shiftE_zero_zero]
            exact hokM.1
          · rw [AnnotValid_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons,
              shiftE_zero_zero]
            exact hokM.2
        exact ih (cons x ρ) ⟨hwC.2.1 x (hdom_eq ▸ hx), hvC.2 x (hdom_eq ▸ hx)⟩
          ⟨hwdP.2 x hx, havP.2.1 x hx⟩ hokM'

include hfind hdef in
/-- **First segment of `TwinRuleMatch`**: walks `iMin` λs up to the minor premise `mdomW` in `p`,
then delegates to `lamDomAlong_lifted_sem`. -/
theorem lamDomAlong_prefix_sem
    (hacl : ∀ (n : Key md) (ψ : LevelParam → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) :
    ∀ (iMin d s nf : Nat) {lC lW p midW afterW mdomW restW sbC sbW : Expr md}
      {bs : List (Expr md × Ix.Kernel.BinderMeta)} {mmW : Ix.Kernel.BinderMeta}
      {La Pa : AnnotTerm},
      SymWrapT find? lC lW →
      LamDomAlong iMin lW p midW →
      p.stripPis iMin = some (bs, .forallE mdomW restW mmW) →
      LamDomAlong s midW (.forallE mdomW restW mmW) afterW →
      LamDomAlong nf afterW (mdomW.liftLooseBVars s 0) sbW →
      stripLams (iMin + s + nf) lC = some sbC →
      WrapT (fun _ : Key md => (none : Option (ConstantInfo md))) sbC sbW →
      Expr.WScoped d p →
      denoteMeta acval env φ d lC = some La →
      denoteMeta acval env φ d p = some Pa →
      ∃ Lw : AnnotTerm,
        denoteMeta acval env φ d lW = some Lw ∧
        ∀ ρ : Nat → V, WellDenotedV V ρ La → WellDenotedV V ρ Pa →
          WellDenotedV V ρ Lw ∧ interp V ρ La = interp V ρ Lw
  | 0, d, s, nf, lC, lW, p, midW, afterW, mdomW, restW, sbC, sbW, bs, mmW, La, Pa,
      hSym, hLam0, hStripP, hLam1, hLam2, hSC, hBase, hwsP, hC, hP => by
    cases hLam0
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hStripP
    obtain ⟨-, rfl⟩ := hStripP
    simp only [Nat.zero_add] at hSC
    obtain ⟨Ma, _, hMa, _, hPa⟩ := denoteMeta_forallE_inv hP
    simp only [Expr.WScoped] at hwsP
    obtain ⟨Lw, hLw, hsem⟩ := lamDomAlong_lifted_sem (V := V) hfind hdef hacl s d nf hSym hLam1 hLam2
      hSC hBase hwsP.1 hC hP hMa
    refine ⟨Lw, hLw, fun ρ hokC hokP => ?_⟩
    have hokM : WellDenotedV V ρ Ma := by
      rw [hPa] at hokP
      obtain ⟨hwdP, havP⟩ := hokP
      rw [WellDenoted_pi] at hwdP; rw [AnnotValid_pi] at havP
      exact ⟨hwdP.1, havP.1⟩
    exact hsem ρ hokC hokP hokM
  | iMin + 1, d, s, nf, lC, lW, p, midW, afterW, mdomW, restW, sbC, sbW, bs, mmW, La, Pa,
      hSym, hLam0, hStripP, hLam1, hLam2, hSC, hBase, hwsP, hC, hP => by
    cases hLam0 with
    | @succ _ dl bl dp bp _ mW_b mp hdom hLam0' =>
      obtain ⟨Dp, Bp, hDp, hBp, rfl⟩ := denoteMeta_forallE_inv hP
      have hDl : denoteMeta acval env φ d dl = some Dp := by
        rw [denoteMeta_eq_of_wrapT_empty hdom d]; exact hDp
      obtain ⟨dc, bc, mC, Dc, Bc, rfl, hpw, hSymB, rfl, _, hBc, hDomEq⟩ :=
        symWrapT_lam_step (V := V) hfind hdef hSym hC hDl
      obtain ⟨_, _, _, bs0, hpeq, hStripP0⟩ := stripPis_succ_inv hStripP
      injection hpeq with _ hbp_eq _
      subst hbp_eq
      rw [show iMin + 1 + s + nf = (iMin + s + nf) + 1 by omega] at hSC
      simp only [stripLams] at hSC
      have hSymB' := SymWrapT.instantiate1 (SymWrapT.fvar d dc dl) hSymB 0
      have hLam0'' := LamDomAlong.instantiate1 (WrapT.fvar d dl dp) hLam0' 0
      obtain ⟨bs0', hStripP'⟩ := stripPis_instantiate1 iMin hStripP0 (.fvar d dp) 0
      have hLam1' := LamDomAlong.instantiate1 (WrapT.fvar d dl dp) hLam1 iMin
      have hLam2' := LamDomAlong.instantiate1 (WrapT.fvar d dl dp) hLam2 (iMin + s)
      have hSC' := stripLams_instantiate1 (iMin + s + nf) hSC (.fvar d dc) 0
      have hBase' := WrapT.instantiate1 (WrapT.fvar d dc dl) hBase (iMin + s + nf)
      simp only [Nat.zero_add, Ix.Kernel.Expr.instantiate1] at hLam0'' hStripP' hLam1' hSC'
      rw [liftLooseBVars_instantiate1_fvar s d dp mdomW 0 iMin (Nat.zero_le _)] at hLam2'
      simp only [Expr.WScoped] at hwsP
      have hwsBp : Expr.WScoped (d + 1) (bp.instantiate1 (.fvar d dp) 0) :=
        Expr.WScoped.instantiate1 hwsP.1 0 hwsP.2
      obtain ⟨Bw, hBw, ih⟩ := lamDomAlong_prefix_sem hacl iMin (d + 1) s nf hSymB' hLam0''
        hStripP' hLam1' hLam2' hSC' hBase' hwsBp hBc hBp
      refine ⟨.lam (pwBit φ mW_b.pw) Dp Bw, ?_, fun ρ hokC hokP => ?_⟩
      · rw [denoteMeta_lam, hDl, hBw]; rfl
      · obtain ⟨hwdP, havP⟩ := hokP
        rw [WellDenoted_pi] at hwdP
        rw [AnnotValid_pi] at havP
        have hokDp : WellDenotedV V ρ Dp := ⟨hwdP.1, havP.1⟩
        have hokDc : WellDenotedV V ρ Dc := by
          obtain ⟨hwC, hvC⟩ := hokC
          rw [WellDenoted_lam] at hwC; rw [AnnotValid_lam] at hvC
          exact ⟨hwC.1, hvC.1⟩
        have hdom_eq := hDomEq ρ hokDc hokDp
        rw [hpw] at hokC ⊢
        refine wellDenotedV_lam_transfer hokC hokDp hdom_eq fun x hx => ?_
        obtain ⟨hwC, hvC⟩ := hokC
        rw [WellDenoted_lam] at hwC; rw [AnnotValid_lam] at hvC
        exact ih (cons x ρ) ⟨hwC.2.1 x (hdom_eq ▸ hx), hvC.2 x (hdom_eq ▸ hx)⟩
          ⟨hwdP.2 x hx, havP.2.1 x hx⟩

include hfind hdef in
/-- **Full semantics of `TwinRuleMatch`**: derives `rW'.rhs`'s reading, grading, and semantic
agreement with `rC.rhs.renameConsts f` directly from `w.cvW'.type` and `rC.rhs`. -/
theorem twinRuleMatch_sem
    (hacl : ∀ (n : Key md) (ψ : LevelParam → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    {f : Key md → Key md} {tyW' rhsC rhsW' : Expr md} {TVw' Rc : AnnotTerm}
    (hwsW' : Expr.WScoped 0 tyW')
    (hTVw' : denoteMeta acval env φ 0 tyW' = some TVw')
    (hokW' : ∀ ρ : Nat → V, WellDenotedV V ρ TVw')
    (hRc : denoteMeta acval env φ 0 (rhsC.renameConsts f) = some Rc)
    (hokRc : ∀ ρ : Nat → V, WellDenotedV V ρ Rc)
    (hMatch : TwinRuleMatch find? f tyW' rhsC rhsW') :
    ∃ Rw' : AnnotTerm,
      denoteMeta acval env φ 0 rhsW' = some Rw' ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ Rw' ∧ interp V ρ Rc = interp V ρ Rw' := by
  obtain ⟨hSym, nPre, nf, afterW, sbW, sbC, hLam1, hMid, hSC, hBase⟩ := hMatch
  rcases hMid with ⟨rfl, rfl⟩ | ⟨iMin, bs, mdomW, restW, mmW, hlt, hStripP, hLam2⟩
  · simp only [Nat.add_zero] at hSC
    obtain ⟨Rw', hRw', hsem⟩ := lamDomAlong_base_sem (V := V) hfind hdef nPre 0 hSym hLam1 hSC hBase hRc hTVw'
    exact ⟨Rw', hRw', fun ρ => hsem ρ (hokRc ρ) (hokW' ρ)⟩
  · have hsplit : iMin + (nPre - iMin) = nPre := by omega
    rw [← hsplit] at hLam1 hSC
    obtain ⟨midW, midP, bs', hLam0, hStripP', hLam1'⟩ :=
      LamDomAlong.split iMin (nPre - iMin) hLam1
    have hmidP : midP = .forallE mdomW restW mmW :=
      (Prod.mk.inj (Option.some.inj (hStripP'.symm.trans hStripP))).2
    subst hmidP
    obtain ⟨Rw', hRw', hsem⟩ := lamDomAlong_prefix_sem (V := V) hfind hdef hacl iMin 0 (nPre - iMin) nf
      hSym hLam0 hStripP hLam1' hLam2 hSC hBase hwsW' hRc hTVw'
    exact ⟨Rw', hRw', fun ρ => hsem ρ (hokRc ρ) (hokW' ρ)⟩

end SymRead

end Ix.Kernel.Model
