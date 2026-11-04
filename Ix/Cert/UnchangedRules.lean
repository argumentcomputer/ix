import Ix.Cert.StrongModelLaws
import Ix.Cert.RulesRename

/-! # The Source laws of a renamed environment

`Obligation.UnchangedRules`: a strong model of an environment that installs the
constants of a renaming of `envQ` gives `envQ`'s recursor rules and capability laws,
at the pulled-back values. Take a law's step of `envQ` between closed, well-typed
terms.
* It is a rules-tier derivation (`IotaStep.red` and its siblings).
* Its terms are good, since a full-grade typing resolves every key
  (`RulesRename.infer_good`).
* The derivation and the typing, renamed, hold in the compiled environment
  (`RulesRename.red_rename`, `defEq_rename`, `infer_rename`).
* There, the strong model gives both renamed sides one denotation
  (`StrongLaws.red_denoteSame`, `defeq_denoteSame`).
* A denotation in the compiled environment pulls back to the original term at the
  pulled-back values (`Ix.Kernel.Denotes.pullback`). A term denotes at most one
  set, so the two sides denote alike. -/

namespace Ix.Cert.UnchangedLaws

open Ix.Kernel Ix.Kernel.Rules
open Ix.Cert.RulesRename (Renaming)

universe w

variable {P : Mode.Id .source → Prop} {f : Mode.Id .source → Mode.Id .anon}
variable {envQ : Env .source} {envR envA : Env .anon}

/-- Every key a good environment answers is good. -/
theorem EnvRel.found (rel : EnvRel P f envQ envR) (k : Key .source) (c : Ix.Kernel.ConstantInfo .source)
    (hc : envQ.find? k = some c) : k.Good (KeyScope.ofId P) := by
  obtain ⟨cs⟩ := envQ
  simp only [Env.find?] at hc
  have hname := List.find?_some hc
  have hmem := List.mem_of_find?_eq_some hc
  rw [beq_iff_eq] at hname
  rw [← hname]
  exact (rel.all c hmem).name

/-- **A renamed environment and one that answers its lookups alike are related
for the rules tier.** -/
theorem rulesRenaming (rel : EnvRel P f envQ envR) (same : SameEnv envA envR) :
    Renaming (KeyScope.ofId P) f envQ envA where
  rel :=
    ⟨rel.inj, fun k hk => by rw [same.find, rel.find k hk], fun k c hk hc => rel.good k c hk hc,
      fun _ hr => absurd trivial hr, fun _ _ => trivial, trivial⟩
  found := EnvRel.found rel
  roles := KeyScope.ofId_all P

/-- A closed, well-typed term of the original environment is good. -/
theorem _root_.Ix.Cert.TypedClosed.good (rel : EnvRel P f envQ envR) {e : Ix.Kernel.Expr .source}
    (h : TypedClosed envQ e) : e.Good (KeyScope.ofId P) := by
  obtain ⟨closed, -, t, ht⟩ := h
  refine RulesRename.infer_good (EnvRel.found rel) (KeyScope.ofId_all P) ht rfl ?_
  rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar closed]
  intro _ h
  exact nomatch h

/-- A closed, well-typed term stays closed and well-typed under the renaming. -/
theorem _root_.Ix.Cert.TypedClosed.rename (rel : EnvRel P f envQ envR) (same : SameEnv envA envR)
    {e : Ix.Kernel.Expr .source} (h : TypedClosed envQ e) : TypedClosed envA (e.mapKeys f) := by
  have hg := h.good rel
  obtain ⟨closed, bounded, t, ht⟩ := h
  exact ⟨by rw [Expr.hasFvar_mapKeys]; exact closed,
    by rw [Expr.looseBVarsBounded_mapKeys]; exact bounded,
    _, (RulesRename.infer_rename (rulesRenaming rel same) ht hg).2⟩

/-- **One denotation in the compiled environment is an alike denotation in the
original**, at the pulled-back values. -/
theorem denoteAlike_pull (rel : EnvRel P f envQ envR) (same : SameEnv envA envR)
    {V : Type w} [SetTheory V] (cval : Key .anon → (LevelParam → Nat) → V)
    {a b : Ix.Kernel.Expr .source} (ha : a.Good (KeyScope.ofId P)) (hb : b.Good (KeyScope.ofId P))
    (h : DenoteSame cval envA (a.mapKeys f) (b.mapKeys f)) :
    DenoteAlike (pullCval f cval) envQ a b := by
  intro φ ρ v v' hv hv'
  obtain ⟨X, hXa, hXb⟩ := h φ ρ
  have pa := Denotes.pullback rel (Denotes.sameFind same.find hXa) rfl ha
  have pb := Denotes.pullback rel (Denotes.sameFind same.find hXb) rfl hb
  rw [Denotes_functional hv pa, Denotes_functional hv' pb]

/-- A reduction from a closed, well-typed term of the original environment keeps
its denotation at the pulled-back values. -/
theorem red_denoteAlike (rel : EnvRel P f envQ envR) (same : SameEnv envA envR)
    {V : Type w} [SetTheory V] (M : Cached.StrongModel V envA) {e e' : Ix.Kernel.Expr .source}
    (ht : TypedClosed envQ e) (hr : Red envQ 0 e e') :
    DenoteAlike (pullCval f M.model.cval) envQ e e' := by
  have hg := ht.good rel
  obtain ⟨hg', hrA⟩ := RulesRename.red_rename (rulesRenaming rel same) hr hg
  exact denoteAlike_pull rel same _ hg hg'
    (StrongLaws.red_denoteSame M (ht.rename rel same) hrA)

/-- A conversion between closed, well-typed terms of the original environment is
an alike denotation at the pulled-back values. -/
theorem defeq_denoteAlike (rel : EnvRel P f envQ envR) (same : SameEnv envA envR)
    {V : Type w} [SetTheory V] (M : Cached.StrongModel V envA) {a b : Ix.Kernel.Expr .source}
    (ha : TypedClosed envQ a) (hb : TypedClosed envQ b) (h : DefEq envQ 0 a b) :
    DenoteAlike (pullCval f M.model.cval) envQ a b := by
  have hga := ha.good rel
  have hgb := hb.good rel
  exact denoteAlike_pull rel same _ hga hgb
    (StrongLaws.defeq_denoteSame M (ha.rename rel same) (hb.rename rel same)
      (RulesRename.defEq_rename (rulesRenaming rel same) h hga hgb))

end Ix.Cert.UnchangedLaws

namespace Ix.Cert

open Ix.Cert.UnchangedLaws

/-- **The Source laws of a renamed environment** (`Obligation.UnchangedRules`). -/
theorem unchangedRules : Obligation.UnchangedRules.{w} := by
  intro V _ P f envQ envR envA M rel same
  refine ⟨fun _ _ _ _ _ hfind _ _ _ _ _ h =>
      red_denoteAlike rel same M h.1 (h.red hfind),
    fun _ _ _ hT _ _ h =>
      defeq_denoteAlike rel same M h.1 h.2.1 (h.defEq hT),
    fun _ _ _ hT _ _ h =>
      defeq_denoteAlike rel same M h.1 h.2.1 (h.defEq hT),
    fun _ _ _ _ h => red_denoteAlike rel same M h.1 (h.red)⟩

/-- info: 'Ix.Cert.unchangedRules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unchangedRules

end Ix.Cert
