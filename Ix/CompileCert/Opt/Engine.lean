import Ix.CompileCert.Opt.Guard
import Ix.Compile.Pass.Driver

/-!
# M7 L3-def: the engine (`Ix/Compile/Pass/Opt/Engine.lean`) and the hook the rewrite calls

The docstring's *Faithfulness*: "O1-O6 are definitional (each module gives the conversion steps);
a composition of conversions is a conversion, so where only they fire the engine's output is
definitionally equal to the baseline. The proof-justified passes … fire only in the value of a
definition, and their output goes only to the definition's canonical form `c._ix`".

* **`engineN_faithful`**: a result of the engine (`engineN fuel`, any fuel: an exhausted fuel is a
  decline, a faithful baseline) whose pass is not proof-justified converts to the occurrence,
  given the laws of O1, O3, O4, O6 and the faithfulness of O2 and O11a (`O2Faithful`,
  `O11aFaithful`: pending their proofs, design D-3; O2's recursion is the engine itself, so its
  hypothesis asks `recur` to be faithful on site-free occurrences only);
* `engineN_site_none`: at an occurrence with no site every result is definitional (the
  proof-justified passes decline, `Guard.lean`);
* `engineN_site_irrel`: the definitional passes do not read the site, so a definitional result at
  a site is the result with no site;
* the hook (`hookOf env`, the function `Driver.optLookup` builds from its `OptEnv`, `optLookup_eq`):
  `hook_faithful` (`HookFaithful`: a site-free result converts and is untagged) and
  `hook_siteStable` (`HookSiteStable`: an untagged result does not depend on the site, and no
  result at a site means none without it) — the two hypotheses of the rewrite's theorems.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (mkAppN)
open Ix.Compile.Pass.Opt

/-! ## Lists of passes -/

theorem findSome_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {b : β}, l.findSome? f = some b → ∃ a ∈ l, f a = some b
  | [], _, h => by cases h
  | a :: l, b, h => by
    cases hfa : f a with
    | some b' =>
      have : (a :: l).findSome? f = some b' := by simp only [List.findSome?, hfa]
      rw [this] at h
      cases h
      exact ⟨a, List.mem_cons_self .., hfa⟩
    | none =>
      have : (a :: l).findSome? f = l.findSome? f := by simp only [List.findSome?, hfa]
      rw [this] at h
      obtain ⟨x, hx, hfx⟩ := findSome_some h
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

theorem findSome_append {α β : Type} (f : α → Option β) :
    ∀ (l₁ l₂ : List α), (l₁ ++ l₂).findSome? f = ((l₁.findSome? f).or (l₂.findSome? f))
  | [], l₂ => by simp only [List.nil_append, List.findSome?, Option.none_or]
  | a :: l₁, l₂ => by
    cases hfa : f a with
    | some b => simp only [List.cons_append, List.findSome?, hfa, Option.some_or]
    | none =>
      simp only [List.cons_append, List.findSome?, hfa]
      exact findSome_append f l₁ l₂

theorem omap_some {α β : Type} {x : Option α} {g : α → β} {y : β} (h : x.map g = some y) :
    ∃ a, x = some a ∧ g a = y := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

/-! ## Faithfulness -/

/-- **`O2Faithful`** (pending, D-3): O2's output converts to the occurrence when the engine it
recurs into (`recur`, its relocated calls, which have no site) is faithful. -/
def O2Faithful (Γ : Env) (env : OptEnv) : Prop :=
  ∀ (recur : Occ → Option Expr) (o : Occ) (e : Expr),
    (∀ o' e', o'.site = none → recur o' = some e' → ExprConv Γ e' (occTerm o')) →
    O2.apply recur env o = some e → ExprConv Γ e (occTerm o)

/-- **`O11aFaithful`** (pending, D-3). -/
def O11aFaithful (Γ : Env) (env : OptEnv) : Prop :=
  ∀ (o : Occ) (e : Expr), O11a.apply env o = some e → ExprConv Γ e (occTerm o)

/-- The laws of the definitional passes, together. -/
structure EngineLaws (Γ : Env) (env : OptEnv) : Prop where
  instClosed : Γ.InstClosed
  recL : RecLaw Γ env
  recOnL : RecOnLaw Γ env
  ixRecOnL : IxRecOnLaw Γ env
  casesOnL : CasesOnLaw Γ env
  o4L : O4Law Γ env
  o2L : O2Faithful Γ env
  o11aL : O11aFaithful Γ env

/-- The names `Engine.isProofJustified` accepts are those of O7–O12. -/
theorem isProofJustified_defs :
    isProofJustified "O1" = false ∧ isProofJustified "O11a" = false ∧ isProofJustified "O2" = false ∧
      isProofJustified "O3" = false ∧ isProofJustified "O4" = false ∧ isProofJustified "O6" = false := by
  decide

theorem isProofJustified_pj :
    isProofJustified "O8" = true ∧ isProofJustified "O7" = true ∧ isProofJustified "O9" = true ∧
      isProofJustified "O10" = true ∧ isProofJustified "O12" = true := by
  decide

/-- What a result of the engine is: some pass of the list, at the occurrence. -/
theorem engineN_cases {env : OptEnv} {fuel : Nat} {o : Occ} {nm : String} {e : Expr}
    (h : engineN (fuel + 1) env o = some (nm, e)) :
    (nm = "O1" ∧ O1.apply env o = some e) ∨ (nm = "O11a" ∧ O11a.apply env o = some e) ∨
    (nm = "O2" ∧ O2.apply (fun o' => (engineN fuel env o').map (·.2)) env o = some e) ∨
    (nm = "O3" ∧ O3.apply env o = some e) ∨ (nm = "O4" ∧ O4.apply env o = some e) ∨
    (nm = "O6" ∧ O6.apply env o = some e) ∨ (nm = "O8" ∧ O8.apply env o = some e) ∨
    (nm = "O7" ∧ O7.apply env o = some e) := by
  simp only [engineN] at h
  obtain ⟨⟨nm', p⟩, hmem, hp⟩ := findSome_some h
  obtain ⟨e', hpe, he'⟩ := omap_some hp
  simp only [Prod.mk.injEq] at he'
  obtain ⟨rfl, rfl⟩ := he'
  simp only [passes, pjPasses, List.cons_append, List.nil_append, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, hpe⟩
  · exact .inr (.inl ⟨rfl, hpe⟩)
  · exact .inr (.inr (.inl ⟨rfl, hpe⟩))
  · exact .inr (.inr (.inr (.inl ⟨rfl, hpe⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨rfl, hpe⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, hpe⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, hpe⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, hpe⟩))))))

/-- **At an occurrence with no site, every result of the engine is definitional.** -/
theorem engineN_site_none {env : OptEnv} {o : Occ} (hs : o.site = none) :
    ∀ {fuel : Nat} {nm : String} {e : Expr}, engineN fuel env o = some (nm, e) → isProofJustified nm = false
  | 0, _, _, h => by simp only [engineN] at h; cases h
  | fuel + 1, nm, e, h => by
    obtain ⟨h7, h8, -, -, -⟩ := pj_site_none (env := env) hs
    rcases engineN_cases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, h'⟩ | ⟨rfl, h'⟩
    all_goals first | decide | (rw [h8] at h'; cases h') | (rw [h7] at h'; cases h')

/-- **The engine is faithful**: a definitional result converts to the occurrence, at every fuel. -/
theorem engineN_faithful {Γ : Env} {env : OptEnv} (hL : EngineLaws Γ env) :
    ∀ (fuel : Nat) (o : Occ) (nm : String) (e : Expr), engineN fuel env o = some (nm, e) →
      isProofJustified nm = false → ExprConv Γ e (occTerm o)
  | 0, _, _, _, h, _ => by simp only [engineN] at h; cases h
  | fuel + 1, o, nm, e, h, hpj => by
    rcases engineN_cases h with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact O1_faithful hL.recL hL.recOnL hL.ixRecOnL h'
    · exact hL.o11aL o e h'
    · refine hL.o2L _ o e ?_ h'
      intro o' e' hs' hr
      obtain ⟨⟨nm', e''⟩, hen, rfl⟩ := omap_some hr
      exact engineN_faithful hL fuel o' nm' e'' hen (engineN_site_none hs' hen)
    · exact O3_faithful hL.instClosed hL.casesOnL h'
    · exact O4_faithful hL.instClosed hL.o4L h'
    · exact O6_faithful hL.recL hL.recOnL hL.ixRecOnL h'
    · exact absurd hpj (by decide)
    · exact absurd hpj (by decide)

/-! ## The site -/

/-- The definitional passes do not read the site. -/
theorem defs_site_irrel (env : OptEnv) (recur : Occ → Option Expr) (h : Name) (us : Array Level)
    (args : Array Expr) (s : Option Name) :
    O1.apply env ⟨h, us, args, s⟩ = O1.apply env ⟨h, us, args, none⟩ ∧
    O11a.apply env ⟨h, us, args, s⟩ = O11a.apply env ⟨h, us, args, none⟩ ∧
    O2.apply recur env ⟨h, us, args, s⟩ = O2.apply recur env ⟨h, us, args, none⟩ ∧
    O3.apply env ⟨h, us, args, s⟩ = O3.apply env ⟨h, us, args, none⟩ ∧
    O4.apply env ⟨h, us, args, s⟩ = O4.apply env ⟨h, us, args, none⟩ ∧
    O6.apply env ⟨h, us, args, s⟩ = O6.apply env ⟨h, us, args, none⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The engine at a site is its definitional part (read with no site) or else its proof-justified
part (read at the site). -/
theorem engineN_split (env : OptEnv) (fuel : Nat) (h : Name) (us : Array Level) (args : Array Expr)
    (s : Option Name) :
    engineN (fuel + 1) env ⟨h, us, args, s⟩ =
      ((passes (fun o' => (engineN fuel env o').map (·.2))).findSome?
          (fun (x : String × (OptEnv → Occ → Option Expr)) => (x.2 env ⟨h, us, args, none⟩).map (x.1, ·))).or
        (pjPasses.findSome?
          (fun (x : String × (OptEnv → Occ → Option Expr)) => (x.2 env ⟨h, us, args, s⟩).map (x.1, ·))) := by
  simp only [engineN]
  rw [findSome_append]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := defs_site_irrel env (fun o' => (engineN fuel env o').map (·.2)) h us args s
  simp only [passes, List.findSome?, h1, h2, h3, h4, h5, h6]

/-- With no site, the proof-justified part is empty. -/
theorem pjPart_none (env : OptEnv) (h : Name) (us : Array Level) (args : Array Expr) :
    pjPasses.findSome?
      (fun (x : String × (OptEnv → Occ → Option Expr)) => (x.2 env ⟨h, us, args, none⟩).map (x.1, ·)) = none := by
  obtain ⟨h7, h8, -, -, -⟩ := pj_site_none (env := env) (o := ⟨h, us, args, none⟩) rfl
  simp only [pjPasses, List.findSome?, h7, h8, Option.map_none]

theorem pjPart_pj {env : OptEnv} {h : Name} {us : Array Level} {args : Array Expr} {s : Option Name}
    {nm : String} {e : Expr}
    (hp : pjPasses.findSome?
      (fun (x : String × (OptEnv → Occ → Option Expr)) => (x.2 env ⟨h, us, args, s⟩).map (x.1, ·)) =
        some (nm, e)) : isProofJustified nm = true := by
  obtain ⟨⟨nm', p⟩, hmem, hp'⟩ := findSome_some hp
  obtain ⟨e', -, he'⟩ := omap_some hp'
  simp only [Prod.mk.injEq] at he'
  obtain ⟨rfl, -⟩ := he'
  simp only [pjPasses, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

/-- **A definitional result at a site is the result with no site**, and conversely. -/
theorem engineN_site_iff {env : OptEnv} {fuel : Nat} {h : Name} {us : Array Level}
    {args : Array Expr} {s : Option Name} {nm : String} {e : Expr} (hpj : isProofJustified nm = false) :
    engineN fuel env ⟨h, us, args, s⟩ = some (nm, e) ↔ engineN fuel env ⟨h, us, args, none⟩ = some (nm, e) := by
  cases fuel with
  | zero => simp only [engineN]
  | succ fuel =>
    rw [engineN_split env fuel h us args s, engineN_split env fuel h us args none, pjPart_none]
    cases hd : (passes (fun o' => (engineN fuel env o').map (·.2))).findSome?
        (fun (x : String × (OptEnv → Occ → Option Expr)) => (x.2 env ⟨h, us, args, none⟩).map (x.1, ·)) with
    | some y => simp only [Option.some_or]
    | none =>
      simp only [Option.none_or]
      constructor
      · intro hp
        have := pjPart_pj hp
        rw [hpj] at this
        cases this
      · intro hp; cases hp

theorem engineN_site_irrel {env : OptEnv} {fuel : Nat} {h : Name} {us : Array Level}
    {args : Array Expr} {s : Option Name} {nm : String} {e : Expr}
    (hr : engineN fuel env ⟨h, us, args, s⟩ = some (nm, e)) (hpj : isProofJustified nm = false) :
    engineN fuel env ⟨h, us, args, none⟩ = some (nm, e) :=
  (engineN_site_iff hpj).1 hr


/-! ## The hook -/

/-- The hook `Driver.optLookup` builds from its `OptEnv` (`optLookup_eq`). -/
def hookOf (env : OptEnv) : Option Name → Name → Array Level → Array Expr →
    Option (Expr × Array ConstantInfo × Option String) :=
  fun site n us args =>
    if !Ix.AuxGen.SourceIdentity.permitsOptimization env.ienv n then none
    else (engineFull env { head := n, us, args, site }).map fun (nm, e, cs) =>
      (e, cs, if isProofJustified nm then some nm else none)

/-- **`HookFaithful`**: a result of the hook with no site converts to the occurrence and is not
tagged proof-justified. -/
def HookFaithful (Γ : Env) (opt? : Option Name → Name → Array Level → Array Expr →
    Option (Expr × Array ConstantInfo × Option String)) : Prop :=
  ∀ n us args e cs t, opt? none n us args = some (e, cs, t) →
    t = none ∧ ExprConv Γ e (occTerm ⟨n, us, args, none⟩)

/-- **`HookSiteStable`**: an untagged result does not depend on the site, and a site with no
result has none without it. -/
def HookSiteStable (opt? : Option Name → Name → Array Level → Array Expr →
    Option (Expr × Array ConstantInfo × Option String)) : Prop :=
  (∀ c n us args e cs, opt? (some c) n us args = some (e, cs, none) →
      opt? none n us args = some (e, cs, none)) ∧
  (∀ c n us args, opt? (some c) n us args = none → opt? none n us args = none)

theorem engineFull_cases {env : OptEnv} {o : Occ} {nm : String} {e : Expr} {cs : Array ConstantInfo}
    (h : engineFull env o = some (nm, e, cs)) :
    (engine env o = some (nm, e) ∧ cs = #[]) ∨
    (engine env o = none ∧ ((nm = "O9" ∧ O9.apply env o = some (e, cs)) ∨
      (nm = "O10" ∧ O10.apply env o = some (e, cs)) ∨ (nm = "O12" ∧ O12.apply env o = some (e, cs)))) := by
  unfold engineFull at h
  cases he : engine env o with
  | some r =>
    rw [he] at h
    obtain ⟨nm', e'⟩ := r
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .inl ⟨rfl, rfl⟩
  | none =>
    rw [he] at h
    simp only at h
    obtain ⟨⟨nm', p⟩, hmem, hp⟩ := findSome_some h
    obtain ⟨⟨e', cs'⟩, hpe, he'⟩ := omap_some hp
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    simp only [emitPasses, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    refine .inr ⟨rfl, ?_⟩
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, hpe⟩
    · exact .inr (.inl ⟨rfl, hpe⟩)
    · exact .inr (.inr ⟨rfl, hpe⟩)

/-- **The hook is faithful** at no site. -/
theorem hook_faithful {Γ : Env} {env : OptEnv} (hL : EngineLaws Γ env) : HookFaithful Γ (hookOf env) := by
  intro n us args e cs t h
  unfold hookOf at h
  split at h <;> try contradiction
  obtain ⟨⟨nm, e', cs'⟩, hf, he⟩ := omap_some h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hs : ({ head := n, us, args, site := none } : Occ).site = none := rfl
  obtain ⟨-, -, h9, h10, h12⟩ := pj_site_none (env := env) hs
  rcases engineFull_cases hf with ⟨he, -⟩ | ⟨-, ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩⟩
  · have hpj := engineN_site_none hs he
    refine ⟨by simp only [hpj, Bool.false_eq_true, ↓reduceIte], ?_⟩
    exact engineN_faithful hL 64 _ nm _ he hpj
  · rw [h9] at h'; cases h'
  · rw [h10] at h'; cases h'
  · rw [h12] at h'; cases h'

/-- **The hook is site-stable.** -/
theorem hook_siteStable (env : OptEnv) : HookSiteStable (hookOf env) := by
  have hs : ∀ n us args, ({ head := n, us, args, site := none } : Occ).site = none := fun _ _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro c n us args e cs h
    unfold hookOf at h ⊢
    split at h <;> rename_i allowed
    · contradiction
    rw [ite_eq_right allowed]
    obtain ⟨⟨nm, e', cs'⟩, hf, he⟩ := omap_some h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, htag⟩ := he
    have hpj : isProofJustified nm = false := by
      cases hp : isProofJustified nm
      · rfl
      · rw [hp] at htag; simp at htag
    rcases engineFull_cases hf with ⟨he, rfl⟩ | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · have he' := engineN_site_irrel he hpj
      have hfull : engineFull env { head := n, us, args, site := none } = some (nm, e', #[]) := by
        unfold engineFull engine
        rw [he']
      rw [hfull]
      simp only [Option.map_some, hpj, Bool.false_eq_true, ↓reduceIte]
    all_goals exact absurd hpj (by decide)
  · intro c n us args h
    unfold hookOf at h ⊢
    split at h <;> rename_i allowed
    · rw [ite_eq_left allowed]
    rw [ite_eq_right allowed]
    have hf : engineFull env { head := n, us, args, site := some c } = none := by
      cases hf : engineFull env { head := n, us, args, site := some c } with
      | none => rfl
      | some x => rw [hf] at h; cases h
    obtain ⟨h7, h8, h9, h10, h12⟩ := pj_site_none (env := env) (hs n us args)
    have hnone : engineFull env { head := n, us, args, site := none } = none := by
      cases hf' : engineFull env { head := n, us, args, site := none } with
      | none => rfl
      | some x =>
        exfalso
        obtain ⟨nm, e, cs⟩ := x
        rcases engineFull_cases hf' with ⟨he, -⟩ | ⟨-, ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩⟩
        · -- a definitional result with no site is one at the site too
          have hpj := engineN_site_none (hs n us args) he
          have he' := (engineN_site_iff (s := some c) hpj).2 he
          have : engineFull env { head := n, us, args, site := some c } = some (nm, e, #[]) := by
            unfold engineFull engine
            rw [he']
          rw [hf] at this
          cases this
        · rw [h9] at h'; cases h'
        · rw [h10] at h'; cases h'
        · rw [h12] at h'; cases h'
    rw [hnone]
    rfl

/-- `Driver.optLookup` is the hook of its `OptEnv`. -/
theorem optLookup_eq (cenv : Ix.CompileM.CompileEnv) (blocks : Std.HashMap Name OptBlock) :
    Ix.Compile.Pass.optLookup cenv blocks =
      hookOf { ienv := cenv.env, resolves := fun n => (Ix.Compile.Pass.resolveAddr cenv n).isSome
               blockOf := fun h => (cenv.p3Heads.get? h).bind blocks.get?
               addrOf := Ix.Compile.Pass.resolveAddr cenv
               ixForm? := Ix.Compile.Pass.ixFormOf cenv } := rfl

end Ix.CompileCert.Opt
