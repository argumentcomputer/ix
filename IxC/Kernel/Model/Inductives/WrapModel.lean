module

public import IxC.Kernel.Model.Swap
public import IxC.Kernel.Model.IndCons
public import IxC.Kernel.Model.Rules.RedSoundKit
public import IxC.Kernel.Semantics.Inductives.WrapRelFacts
import IxC.Kernel.Model.Annot.BitLevels
import IxC.Kernel.Model.Annot.BitLemmas
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
    | sort u => exact ⟨ga, hg, .refl _⟩
    | const n us => exact ⟨ga, hg, .refl _⟩
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

end Ix.Kernel.Model
