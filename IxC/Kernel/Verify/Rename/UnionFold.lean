module

public import IxC.Kernel.Verify.Rename.Installs

@[expose] public section

/-!
# The union of two accepted lists (S1)

The union runs the certificate's list, then the renamed Source's remainder
(the declarations the certificate does not declare) over the certificate's
environment. Each remaining Source step is framed: the Source run's
environment `B` and the union's `U` agree on a set of bases, the frame's
scope is that set (`agreeScope B U`), and the step installs, in `U`, what it
installed in `B` (`union_step`).
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md : Mode}

/-! ## Scopes from agreement -/

/-- **Two environments agree over a base**: at every key over `j`. -/
def AgreeOn (B U : Env md) (j : Key md) : Prop :=
  ∀ k : Key md, k.base = j → U.find? k = B.find? k

/-- **The scope of agreement**: the ids and roles over which `B` and `U`
agree. -/
def agreeScope (B U : Env md) : KeyScope md :=
  ⟨fun i => AgreeOn B U (.id i), fun r => AgreeOn B U (.role r)⟩

/-- A key is good at the scope of agreement exactly when the environments
agree over its base. -/
theorem agreeScope_good {B U : Env md} : ∀ {k : Key md},
    k.Good (agreeScope B U) ↔ AgreeOn B U k.base
  | .id _ => Iff.rfl
  | .role _ => Iff.rfl
  | .aux k _ => by
    simp only [Key.good_aux, Key.base_aux]
    exact agreeScope_good (k := k)

/-- **The frame at the scope of agreement.** -/
theorem EnvFrame.ofAgree {B U : Env md}
    (hgood : ∀ (k : Key md) (c : ConstantInfo md), k.Good (agreeScope B U) →
      B.find? k = some c → c.Good (agreeScope B U))
    (habsent : ∀ r : Role, ¬ AgreeOn B U (.role r) → B.find? (roleKey r) = none)
    (hpre : (agreeScope B U).Pre) : EnvFrame (agreeScope B U) B U :=
  EnvFrame.mk (fun k hk => agreeScope_good.mp hk k rfl) hgood habsent hpre

/-! ## One step of the union -/

/-- **A Source step outside the certificate, in the union**: a declaration
installing no operation, accepted over `B` under any evidence, is accepted
over `U` under any other, wherever `B` and `U` agree over every base it
mentions; the two results agree wherever `B` and `U` did. -/
theorem union_step (μ : CheckMode) (F : Nat) (ev₁ ev₂ : Evidences md) {B U B' : Env md}
    {d : Declaration md}
    (hgood : ∀ (k : Key md) (c : ConstantInfo md), k.Good (agreeScope B U) →
      B.find? k = some c → c.Good (agreeScope B U))
    (habsent : ∀ r : Role, ¬ AgreeOn B U (.role r) → B.find? (roleKey r) = none)
    (hpre : (agreeScope B U).Pre) (hd : d.Good (agreeScope B U)) (hop : d.NoOp)
    (h : checkDecl μ (fueledOps μ F) ev₂ B d = .ok B') :
    ∃ U', checkDecl μ (fueledOps μ F) ev₁ U d = .ok U' ∧ EnvFrame (agreeScope B U) B' U' := by
  have hE := EnvFrame.ofAgree hgood habsent hpre
  rw [checkDecl_ev_irrel μ F ev₂ [] B hop] at h
  have hev : Evidences.Good (agreeScope B U) ([] : Evidences md) := fun _ h => nomatch h
  obtain ⟨U', hU', hrel⟩ := checkDecl_frame μ F hev hE hd (Or.inl hop) B' h
  rw [checkDecl_ev_irrel μ F [] ev₁ U hop] at hU'
  exact ⟨U', hU', hrel⟩

/-! ## The join of two environments -/

/-- **The join**: `B`'s constants, then `E`'s. -/
def Env.join (B E : Env md) : Env md := ⟨B.consts ++ E.consts⟩

theorem Env.find?_join (B E : Env md) (k : Key md) :
    (B.join E).find? k = (B.find? k).or (E.find? k) := by
  simp only [Env.join, Env.find?, List.find?_append]

/-- `B` agrees with the join over a base where `E` holds nothing `B` lacks. -/
theorem AgreeOn.join_left {B E : Env md} {j : Key md}
    (h : ∀ k : Key md, k.base = j → B.find? k = none → E.find? k = none) :
    AgreeOn B (B.join E) j := by
  intro k hk
  rw [Env.find?_join]
  cases hb : B.find? k with
  | none => simp [h k hk hb]
  | some c => rfl

/-- `E` agrees with the join over a base where `B` holds what `E` does, or
nothing. -/
theorem AgreeOn.join_right {B E : Env md} {j : Key md}
    (h : ∀ k : Key md, k.base = j → B.find? k = none ∨ B.find? k = E.find? k) :
    AgreeOn E (B.join E) j := by
  intro k hk
  rw [Env.find?_join]
  rcases h k hk with hb | hb
  · rw [hb]; rfl
  · rw [hb]; cases E.find? k <;> rfl

/-! ## A shared step -/

/-- **A declaration both lists accept, framed into their join**: accepted
over `B` and over `E` (any evidence each), it is accepted over the join, and
each result agrees with the join's result wherever its environment agreed
with the join. (A declaration installing no operation.) -/
theorem shared_step (μ : CheckMode) (F : Nat) (ev₁ ev₂ : Evidences md) {B E B' E' : Env md}
    {d : Declaration md}
    (hfB : EnvFrame (agreeScope B (B.join E)) B (B.join E))
    (hfE : EnvFrame (agreeScope E (B.join E)) E (B.join E))
    (hdB : d.Good (agreeScope B (B.join E))) (hdE : d.Good (agreeScope E (B.join E)))
    (hop : d.NoOp)
    (hB : checkDecl μ (fueledOps μ F) ev₂ B d = .ok B')
    (hE : checkDecl μ (fueledOps μ F) ev₁ E d = .ok E') :
    ∃ G', checkDecl μ (fueledOps μ F) [] (B.join E) d = .ok G' ∧
      EnvFrame (agreeScope B (B.join E)) B' G' ∧ EnvFrame (agreeScope E (B.join E)) E' G' := by
  have hev : ∀ P : KeyScope md, Evidences.Good P ([] : Evidences md) := fun _ _ h => nomatch h
  rw [checkDecl_ev_irrel μ F ev₂ [] B hop] at hB
  rw [checkDecl_ev_irrel μ F ev₁ [] E hop] at hE
  obtain ⟨G₁, hG₁, hr₁⟩ := checkDecl_frame μ F (hev _) hfB hdB (Or.inl hop) B' hB
  obtain ⟨G₂, hG₂, hr₂⟩ := checkDecl_frame μ F (hev _) hfE hdE (Or.inl hop) E' hE
  rw [hG₁] at hG₂
  cases Except.ok.inj hG₂
  exact ⟨G₁, hG₁, hr₁, hr₂⟩

/-- **The core of a definition's check**: an accepted definition installs
what its constant check and value check install (the operations' gates only
gate). -/
theorem checkDecl_defn_core (μ : CheckMode) (ops : (CheckerOps md) (CheckM md))
    (ev : Evidences md) {env e : Env md} {cv : ConstantVal md} {value : Expr md}
    {hint : ReducibilityHint} (h : checkDecl μ ops ev env (.defnDecl cv value hint) = .ok e) :
    ∃ cvA, checkConstantVal ops env cv = .ok cvA ∧ checkDefnVal ops env cvA value hint = .ok e := by
  have hp : ExPost (checkDecl μ ops ev env (.defnDecl cv value hint)) (fun e =>
      ∃ cvA, checkConstantVal ops env cv = .ok cvA ∧ checkDefnVal ops env cvA value hint = .ok e) := by
    unfold checkDecl
    rw [ExPost.post_bind]
    intro cvA hcvA
    rw [ExPost.post_bind]
    intro env2 henv2
    have hk : ∃ cvA', checkConstantVal ops env cv = .ok cvA' ∧
        checkDefnVal ops env cvA' value hint = .ok env2 := ⟨cvA, hcvA, henv2⟩
    simp [hk]
    intro _ _ _ _
    split <;> simp [hk]
  exact hp e h

/-- **A shared definition, framed into the join**, whatever the evidence:
its core installs over the join, and each run's result agrees with the
join's where its environment did. -/
theorem shared_step_defn (μ : CheckMode) (F : Nat) (ev₁ ev₂ : Evidences md) {B E B' E' : Env md}
    {cv : ConstantVal md} {value : Expr md} {hint : ReducibilityHint}
    (hfB : EnvFrame (agreeScope B (B.join E)) B (B.join E))
    (hfE : EnvFrame (agreeScope E (B.join E)) E (B.join E))
    (hdB : (Declaration.defnDecl cv value hint).Good (agreeScope B (B.join E)))
    (hdE : (Declaration.defnDecl cv value hint).Good (agreeScope E (B.join E)))
    (hB : checkDecl μ (fueledOps μ F) ev₂ B (.defnDecl cv value hint) = .ok B')
    (hE : checkDecl μ (fueledOps μ F) ev₁ E (.defnDecl cv value hint) = .ok E') :
    ∃ G', EnvFrame (agreeScope B (B.join E)) B' G' ∧ EnvFrame (agreeScope E (B.join E)) E' G' := by
  obtain ⟨cvB, hcB, hvB⟩ := checkDecl_defn_core μ _ ev₂ hB
  obtain ⟨cvE, hcE, hvE⟩ := checkDecl_defn_core μ _ ev₁ hE
  have hopsB := fueledOps_sim (P := agreeScope B (B.join E)) (f := fun i => i) (L := TrueLink) μ F
  have hopsE := fueledOps_sim (P := agreeScope E (B.join E)) (f := fun i => i) (L := TrueLink) μ F
  obtain ⟨⟨hgB, -⟩, hcB'⟩ := checkConstantVal_sim_name hopsB hfB hdB.1 cvB hcB
  obtain ⟨⟨hgE, -⟩, hcE'⟩ := checkConstantVal_sim_name hopsE hfE hdE.1 cvE hcE
  simp only [ConstantVal.mapKeys_id] at hcB' hcE'
  rw [hcB'] at hcE'
  cases Except.ok.inj hcE'
  have hv₁ := checkDefnVal_sim hopsB hfB hgB hdB.2 hint B' hvB
  have hv₂ := checkDefnVal_sim hopsE hfE hgE hdE.2 hint E' hvE
  simp only [ConstantVal.mapKeys_id, Expr.mapKeys_id] at hv₁ hv₂
  obtain ⟨G₁, hG₁, hr₁⟩ := hv₁
  obtain ⟨G₂, hG₂, hr₂⟩ := hv₂
  rw [hG₁] at hG₂
  cases Except.ok.inj hG₂
  exact ⟨G₁, hr₁, hr₂⟩

/-! ## What a run installs -/

/-- **An accepted run installs over its list's names**: every key a run adds
has a role base or a base among the list's names, and is fresh. -/
theorem foldlM_checkDecl_post (μ : CheckMode) (ops : (CheckerOps md) (CheckM md))
    (ev : Evidences md) (ds : List (Declaration md)) (env : Env md) :
    ExPost (ds.foldlM (checkDecl μ ops ev) env) (Grows (Over (ds.flatMap Declaration.names)) env) :=
  foldlM_grows _ ds env fun e d hd =>
    ExPost.mono (fun _ h => h.mono fun _ hk =>
      hk.mono fun _ hn => List.mem_flatMap.mpr ⟨d, hd, hn⟩) (checkDecl_post μ ops ev e d)

/-! ## The scope of a list's names -/

/-- **The scope of names**: the ids that are bases of the names, and the roles
that are, or the prelude's. A key is good there exactly when it is over the
names (`Key.good_nameScope`). -/
def nameScope (ns : List (Key md)) : KeyScope md :=
  ⟨fun i => Key.id i ∈ ns.map Key.base,
    fun r => Key.role r ∈ ns.map Key.base ∨ r ∈ preludeRoles⟩

theorem Key.good_nameScope {ns : List (Key md)} : ∀ {k : Key md},
    k.Good (nameScope ns) ↔ Over ns k
  | .id i => by
    simp only [Over, Key.base_id]
    exact ⟨Or.inl, fun h => h.elim _root_.id fun ⟨_, _, h⟩ => nomatch h⟩
  | .role r => by
    simp only [Over, Key.base_role, Key.good_role]
    exact ⟨fun h => h.elim Or.inl fun h => Or.inr ⟨r, h, rfl⟩,
      fun h => h.elim Or.inl fun ⟨r', hr', he⟩ => Or.inr (by cases he; exact hr')⟩
  | .aux k _ => by
    simp only [Key.good_aux, Over, Key.base_aux]
    exact Key.good_nameScope (k := k)

theorem nameScope_pre (ns : List (Key md)) : (nameScope ns).Pre := fun _ h => Or.inr h

theorem nameScope_mono {ns ns' : List (Key md)} (h : ∀ n ∈ ns, n ∈ ns') :
    (∀ i, nameScope ns i → nameScope ns' i) ∧
      ∀ r, (nameScope ns).role r → (nameScope ns').role r := by
  have hm : ∀ k ∈ ns.map Key.base, k ∈ ns'.map Key.base := fun k hk => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hk
    exact List.mem_map_of_mem (h n hn)
  exact ⟨fun i hi => hm _ hi, fun r hr => hr.elim (fun h => Or.inl (hm _ h)) Or.inr⟩

/-- **Ordered closure**: every declaration is good at the scope of the names
declared before it, in `pre` and in the list, and its own. -/
def ClosedFrom (pre : List (Key md)) (ds : List (Declaration md)) : Prop :=
  ∀ i (h : i < ds.length),
    ds[i].Good (nameScope (pre ++ (ds.take (i + 1)).flatMap Declaration.names))

/-- **Ordered closure** of a whole list. -/
abbrev Closed (ds : List (Declaration md)) : Prop := ClosedFrom [] ds

end Ix.Kernel
