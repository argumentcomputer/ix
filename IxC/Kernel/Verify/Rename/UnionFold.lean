module

public import IxC.Kernel.Verify.Rename.Installs

@[expose] public section

/-!
# The union of two accepted lists (S1): the run lemma

What the union (`Rename/UnionRun.lean`, `Rename/UnionJoin.lean`) needs of one
run.

- **Agreement over a base** (`AgreeOn`) and the **join** of two environments
  (`Env.join`).
- **The core of a declaration's check** (`checkDeclCore`): what it installs,
  the evidence gates dropped. An accepted declaration installs its core under
  any evidence (`checkDecl_core`), and the core is framed
  (`checkDeclCore_frame`).
- **Ordered closure** (`ClosedFrom`, `Closed`): every declaration good at the
  scope of the names declared so far, its own included (`nameScope`, by
  bases, the prelude roles always in).
- **The run lemma** (`run_good`): an accepted closed run's lookups are good
  at, and over, the scope of its names so far.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md : Mode}

/-! ## Agreement and the join -/

/-- **Two environments agree over a base**: at every key over `j`. -/
def AgreeOn (B U : Env md) (j : Key md) : Prop :=
  ∀ k : Key md, k.base = j → U.find? k = B.find? k

/-- **The join**: `B`'s constants, then `E`'s. -/
def Env.join (B E : Env md) : Env md := ⟨B.consts ++ E.consts⟩

theorem Env.find?_join (B E : Env md) (k : Key md) :
    (B.join E).find? k = (B.find? k).or (E.find? k) := by
  simp only [Env.join, Env.find?, List.find?_append]

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

/-! ## The core of a declaration's check -/

/-- **The core of a declaration's check**: what it installs, the evidence
gates dropped. A definition's core is its constant and value checks; any
other declaration's is its check under the empty evidence. -/
def checkDeclCore (μ : CheckMode) (ops : (CheckerOps md) (CheckM md)) (env : Env md)
    (d : Declaration md) : CheckM md (Env md) :=
  match d with
  | .defnDecl cv value hint => do
    let cvA ← checkConstantVal ops env cv
    checkDefnVal ops env cvA value hint
  | d => checkDecl μ ops [] env d

theorem checkDecl_noop_empty (μ : CheckMode) (F : Nat) (ev : Evidences md) {env e : Env md}
    {d : Declaration md} (h : checkDecl μ (fueledOps μ F) ev env d = .ok e) (hop : d.NoOp) :
    checkDecl μ (fueledOps μ F) [] env d = .ok e := by
  rw [← checkDecl_ev_irrel μ F ev [] env hop]; exact h

/-- **An accepted declaration installs its core**, whatever the evidence. -/
theorem checkDecl_core (μ : CheckMode) (F : Nat) (ev : Evidences md) {env e : Env md}
    {d : Declaration md} (h : checkDecl μ (fueledOps μ F) ev env d = .ok e) :
    checkDeclCore μ (fueledOps μ F) env d = .ok e := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨cvA, hc, hv⟩ := checkDecl_defn_core μ _ ev h
    show (checkConstantVal (fueledOps μ F) env cv >>= fun cvA =>
      checkDefnVal (fueledOps μ F) env cvA value hint) = .ok e
    rw [hc]; exact hv
  | _ => exact checkDecl_noop_empty μ F ev h (by exact trivial)

/-- **The core, framed**: over a framing environment, a declaration naming
`P`-good keys only installs what frames the result. -/
theorem checkDeclCore_frame (μ : CheckMode) (F : Nat) {P : KeyScope md} {B U : Env md}
    (hE : EnvFrame P B U) {d : Declaration md} (hd : d.Good P) :
    SimR (EnvFrame P) (checkDeclCore μ (fueledOps μ F) B d)
      (checkDeclCore μ (fueledOps μ F) U d) := by
  have hops := fueledOps_sim (P := P) (f := fun i => i) (L := TrueLink) μ F
  have hev : Evidences.Good P ([] : Evidences md) := fun _ h => nomatch h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨hcv, hv⟩ := hd
    intro B' hB'
    change (checkConstantVal (fueledOps μ F) B cv >>= fun cvA =>
      checkDefnVal (fueledOps μ F) B cvA value hint) = .ok B' at hB'
    obtain ⟨cvA, hc, hdv⟩ : ∃ cvA, checkConstantVal (fueledOps μ F) B cv = .ok cvA ∧
        checkDefnVal (fueledOps μ F) B cvA value hint = .ok B' := by
      cases hcB : checkConstantVal (fueledOps μ F) B cv with
      | error x => rw [hcB] at hB'; exact nomatch hB'
      | ok cvA => rw [hcB] at hB'; exact ⟨cvA, rfl, hB'⟩
    obtain ⟨⟨hg, -⟩, hcU⟩ := checkConstantVal_sim_name hops hE hcv cvA hc
    obtain ⟨U', hU', hr⟩ := checkDefnVal_sim hops hE hg hv hint B' hdv
    simp only [ConstantVal.mapKeys_id, Expr.mapKeys_id] at hcU hU'
    refine ⟨U', ?_, hr⟩
    show (checkConstantVal (fueledOps μ F) U cv >>= fun cvA =>
      checkDefnVal (fueledOps μ F) U cvA value hint) = .ok U'
    rw [hcU]; exact hU'
  | _ => exact checkDecl_frame μ F hev hE hd (Or.inl (by exact trivial))

/-! ## Any accepted declaration, framed -/

/-- **An accepted declaration, framed** (any evidence): over a framing
environment its core installs what frames the result. -/
theorem frame_any (μ : CheckMode) (F : Nat) (ev : Evidences md) {P : KeyScope md}
    {B U B' : Env md} {d : Declaration md} (hE : EnvFrame P B U) (hd : d.Good P)
    (h : checkDecl μ (fueledOps μ F) ev B d = .ok B') : ∃ U', EnvFrame P B' U' := by
  obtain ⟨U', -, hr⟩ := checkDeclCore_frame μ F hE hd B' (checkDecl_core μ F ev h)
  exact ⟨U', hr⟩

/-! ## Scope inclusion -/

/-- **Scope inclusion**: every id and every role of `P` is `Q`'s. -/
def KeyScope.Le (P Q : KeyScope md) : Prop := (∀ i, P i → Q i) ∧ ∀ r, P.role r → Q.role r

theorem ConstantVal.Good.mono {P Q : KeyScope md} (h : P.Le Q) {cv : ConstantVal md}
    (hc : cv.Good P) : cv.Good Q :=
  ⟨Key.Good.mono h.1 h.2 hc.1, Expr.Good.mono h.1 h.2 hc.2⟩

theorem RecRule.Good.mono {P Q : KeyScope md} (h : P.Le Q) {r : RecRule md}
    (hr : r.Good P) : r.Good Q := by
  obtain ⟨h1, h2, h3⟩ := hr
  refine ⟨Key.Good.mono h.1 h.2 h1, ?_, Expr.Good.mono h.1 h.2 h3⟩
  cases hf : r.fire with
  | nested l pins =>
    simp only [hf, RecRuleFire.Good] at h2 ⊢
    exact fun e he => Expr.Good.mono h.1 h.2 (h2 e he)
  | _ => simp [hf]

theorem ConstantInfo.Good.mono {P Q : KeyScope md} (h : P.Le Q) :
    ∀ {c : ConstantInfo md}, c.Good P → c.Good Q
  | .axiomInfo _, hc => by
    simp only [ConstantInfo.Good] at hc ⊢; exact ConstantVal.Good.mono h hc
  | .defnInfo _ _ _, hc => by
    simp only [ConstantInfo.Good] at hc ⊢
    exact ⟨ConstantVal.Good.mono h hc.1, Expr.Good.mono h.1 h.2 hc.2⟩
  | .thmInfo _ _, hc => by
    simp only [ConstantInfo.Good] at hc ⊢
    exact ⟨ConstantVal.Good.mono h hc.1, Expr.Good.mono h.1 h.2 hc.2⟩
  | .indInfo _ _, hc => by
    simp only [ConstantInfo.Good] at hc ⊢
    exact ⟨ConstantVal.Good.mono h hc.1, fun k hk => Key.Good.mono h.1 h.2 (hc.2 k hk)⟩
  | .ctorInfo _ _ _, hc => by
    simp only [ConstantInfo.Good] at hc ⊢; exact ConstantVal.Good.mono h hc
  | .recInfo _ _ _ _, hc => by
    simp only [ConstantInfo.Good] at hc ⊢
    exact ⟨ConstantVal.Good.mono h hc.1, fun r hr => RecRule.Good.mono h (hc.2 r hr)⟩
  | .projInfo _, hc => by
    simp only [ConstantInfo.Good] at hc ⊢
    exact ⟨Key.Good.mono h.1 h.2 hc.1, Key.Good.mono h.1 h.2 hc.2.1,
      fun b hb => Expr.Good.mono h.1 h.2 (hc.2.2 b hb)⟩

theorem Declaration.Good.mono {P Q : KeyScope md} (h : P.Le Q) :
    ∀ {d : Declaration md}, d.Good P → d.Good Q
  | .axiomDecl _, hd => by
    simp only [Declaration.Good] at hd ⊢; exact ConstantVal.Good.mono h hd
  | .defnDecl _ _ _, hd => by
    simp only [Declaration.Good] at hd ⊢
    exact ⟨ConstantVal.Good.mono h hd.1, Expr.Good.mono h.1 h.2 hd.2⟩
  | .thmDecl _ _, hd => by
    simp only [Declaration.Good] at hd ⊢
    exact ⟨ConstantVal.Good.mono h hd.1, Expr.Good.mono h.1 h.2 hd.2⟩
  | .opaqueDecl _ _, hd => by
    simp only [Declaration.Good] at hd ⊢
    exact ⟨ConstantVal.Good.mono h hd.1, Expr.Good.mono h.1 h.2 hd.2⟩
  | .basisDecl _, _ => trivial
  | .indDecl _ _, hd => by
    simp only [Declaration.Good] at hd ⊢
    exact fun c hc => ConstantInfo.Good.mono h (hd c hc)
  | .quotDecl _ _, hd => by
    simp only [Declaration.Good] at hd ⊢; exact ConstantVal.Good.mono h hd

theorem nameScope_le {ns ns' : List (Key md)} (h : ∀ n ∈ ns, n ∈ ns') :
    (nameScope ns).Le (nameScope ns') :=
  nameScope_mono h

/-! ## What a run's lookups answer -/

/-- **Every lookup is good** at `P`. -/
def FindGood (P : KeyScope md) (env : Env md) : Prop :=
  ∀ k c, env.find? k = some c → c.Good P

/-- **Every key is over the names** `ns`. -/
def FindOver (ns : List (Key md)) (env : Env md) : Prop :=
  ∀ k c, env.find? k = some c → Over ns k

theorem FindOver.mono {ns ns' : List (Key md)} (hs : ∀ n ∈ ns, n ∈ ns') {env : Env md}
    (h : FindOver ns env) : FindOver ns' env :=
  fun k c hk => (h k c hk).mono hs

theorem FindGood.mono {P Q : KeyScope md} (hPQ : P.Le Q) {env : Env md} (h : FindGood P env) :
    FindGood Q env :=
  fun k c hk => ConstantInfo.Good.mono hPQ (h k c hk)

/-- A role outside the scope of the names is absent. -/
theorem FindOver.absent {ns : List (Key md)} {env : Env md} (h : FindOver ns env) {r : Role}
    (hr : ¬ (nameScope ns).role r) : env.find? (roleKey r) = none := by
  cases hf : env.find? (roleKey r) with
  | none => rfl
  | some c => exact absurd (Key.good_nameScope.mpr (h _ c hf)) hr

/-- **An environment frames itself** at the scope of its names. -/
theorem selfFrame {ns : List (Key md)} {env : Env md} (hg : FindGood (nameScope ns) env)
    (ho : FindOver ns env) : EnvFrame (nameScope ns) env env :=
  EnvFrame.refl (fun k c _ h => hg k c h) (fun _ hr => ho.absent hr) (nameScope_pre ns)

/-- **A lookup after growth**: the old one, or a key of the growth missing before. -/
theorem Grows.find_cases {Q : Key md → Prop} {env env' : Env md} (h : Grows Q env env')
    {k : Key md} {c : ConstantInfo md} (hk : env'.find? k = some c) :
    env.find? k = some c ∨ (Q k ∧ env.find? k = none) := by
  obtain ⟨new, hn, hq⟩ := h
  obtain ⟨cs'⟩ := env'
  simp only at hn
  subst hn
  simp only [Env.find?, List.find?_append] at hk
  cases hnf : new.find? (·.name == k) with
  | none => rw [hnf] at hk; exact Or.inl hk
  | some c' =>
    have hmem := List.mem_of_find?_eq_some hnf
    have hname : c'.name = k := by simpa using List.find?_some hnf
    have hq' := hq c' hmem
    rw [hname] at hq'
    exact Or.inr hq'

/-- An accepted step of a fold. -/
theorem foldlM_cons_ok {α : Type} {step : Env md → α → CheckM md (Env md)} {a : α}
    {as : List α} {env env' : Env md} (h : (a :: as).foldlM step env = .ok env') :
    ∃ e, step env a = .ok e ∧ as.foldlM step e = .ok env' := by
  simp only [List.foldlM_cons] at h
  cases he : step env a with
  | error x => rw [he] at h; exact nomatch h
  | ok e => rw [he] at h; exact ⟨e, rfl, h⟩

/-! ## A run's lookups are good at its names -/

/-- **One accepted step keeps the run's invariants**: lookups good at, and
keys over, the names so far. -/
theorem step_good (μ : CheckMode) (F : Nat) (ev : Evidences md) {pre : List (Key md)}
    {d : Declaration md} {env env' : Env md} (hg : FindGood (nameScope pre) env)
    (ho : FindOver pre env) (hd : d.Good (nameScope (pre ++ d.names)))
    (h : checkDecl μ (fueledOps μ F) ev env d = .ok env') :
    FindGood (nameScope (pre ++ d.names)) env' ∧ FindOver (pre ++ d.names) env' := by
  have hsub : ∀ n ∈ pre, n ∈ pre ++ d.names := fun n hn => List.mem_append_left _ hn
  have ho' : FindOver (pre ++ d.names) env' := by
    intro k c hk
    rcases (checkDecl_post μ _ ev env d env' h).find_cases hk with hk | ⟨hk, -⟩
    · exact (ho k c hk).mono hsub
    · exact hk.mono fun n hn => List.mem_append_right _ hn
  have hE : EnvFrame (nameScope (pre ++ d.names)) env env :=
    selfFrame ((hg.mono (nameScope_le hsub))) (ho.mono hsub)
  obtain ⟨U', hU'⟩ := frame_any μ F ev hE hd h
  exact ⟨fun k c hk => hU'.good k c (Key.good_nameScope.mpr (ho' k c hk)) hk, ho'⟩

/-- **A run's lookups are good at the scope of its names**: started from an
environment whose lookups are good at, and over, the names before, an
accepted closed list installs one whose lookups are good at, and over, all
the names. -/
theorem run_good (μ : CheckMode) (F : Nat) (ev : Evidences md) :
    ∀ (pre : List (Key md)) (ds : List (Declaration md)) (env env' : Env md),
      FindGood (nameScope pre) env → FindOver pre env → ClosedFrom pre ds →
      ds.foldlM (checkDecl μ (fueledOps μ F) ev) env = .ok env' →
      FindGood (nameScope (pre ++ ds.flatMap Declaration.names)) env' ∧
        FindOver (pre ++ ds.flatMap Declaration.names) env'
  | pre, [], env, env', hg, ho, _, h => by
    simp only [List.foldlM_nil] at h
    cases h
    simpa using ⟨hg, ho⟩
  | pre, d :: ds, env, env', hg, ho, hc, h => by
    obtain ⟨e, he, h⟩ := foldlM_cons_ok h
    have hd : d.Good (nameScope (pre ++ d.names)) := by
      have h0 := hc 0 (by simp)
      simp only [List.take_succ_cons, List.take_zero, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at h0
      exact h0
    obtain ⟨hg₁, ho₁⟩ := step_good μ F ev hg ho hd he
    have hc' : ClosedFrom (pre ++ d.names) ds := by
      intro i hi
      have h1 := hc (i + 1) (by simp; omega)
      simp only [List.take_succ_cons, List.flatMap_cons, List.append_assoc] at h1
      rw [List.append_assoc]; exact h1
    simpa [List.flatMap_cons, List.append_assoc] using
      run_good μ F ev (pre ++ d.names) ds e env' hg₁ ho₁ hc' h

end Ix.Kernel
