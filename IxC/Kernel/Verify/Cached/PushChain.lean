module

public import IxC.Kernel.Verify.Cached.AgreeFloor
public import IxC.Kernel.Verify.EnvBound
import IxC.Kernel.Verify.EnvWF
import IxC.Kernel.Verify.CheckerF
import all Init.LetFun

public section

/-!
# Every accepted install is a chain of fresh pushes (task #253)

The two-phase driver (`checkDeclsTwoPhase`, `IxC/Kernel/Cached/ParsedC.lean`)
checks each recorded value against a PREFIX VIEW of the final
environment, `feFinal.restrictTo vis`, and the prefix view's `find?` is
the truncated environment's only under name uniqueness
(`mkFEnv_find?_visibleBelow`, `IxC/Kernel/Verify/EnvBound.lean`).  Name
uniqueness is an install-time invariant: every push a driver step
performs is guarded by a lookup — `checkConstantValC`'s duplicate
guard, `checkMemberValF`'s, `installBasisDeclF`'s, the projection
name-family guards — so this file proves, once and OPERATIONALLY (no
environment well-formedness, no simulation: the final-value discipline
of `IxC/Kernel/Verify/Cached/AgreeFloor.lean`), that an accepted step
returns `PushChain env fe'`: a canonical index whose constants extend
`env` by fresh names.  Chained from the empty environment, that is
`NodupNames` of every environment a driver ever holds, and the
suffix relation between the environment a declaration was installed at
and the final one.
-/

namespace Ix.Kernel.Cached

open Ix.Kernel

variable {pins : List NatOpPinSet}

/-! ## Fresh chains -/

/-- `fe'` extends `env` by a chain of pushes, each of a name fresh at the
environment it was pushed onto: `fe'` is canonical, `env.consts` is a
suffix of its constants, and name uniqueness carries over. -/
@[expose] def PushChain (env : Env) (fe' : FEnv) : Prop :=
  fe' = mkFEnv fe'.env ∧ (∃ new, fe'.env.consts = new ++ env.consts) ∧
  (NodupNames env → NodupNames fe'.env)

theorem PushChain.refl (env : Env) : PushChain env (mkFEnv env) :=
  ⟨rfl, ⟨[], rfl⟩, id⟩

theorem PushChain.canon {env : Env} {fe : FEnv} (h : PushChain env fe) :
    fe = mkFEnv fe.env := h.1

/-- A canonical index is a chain from its own environment. -/
theorem PushChain.self {fe : FEnv} (h : fe = mkFEnv fe.env) : PushChain fe.env fe :=
  ⟨h, ⟨[], rfl⟩, id⟩

theorem PushChain.find? {env : Env} {fe : FEnv} (h : PushChain env fe)
    (n : Name) : fe.find? n = fe.env.find? n := by
  have h1 := h.1
  calc fe.find? n = (mkFEnv fe.env).find? n := by rw [← h1]
    _ = fe.env.find? n := mkFEnv_find? _ n

/-- A lookup that fails names no stored constant. -/
theorem Env.find?_none_notin {env : Env} {n : Name} (h : env.find? n = none) :
    n ∉ env.consts.map (·.name) := by
  intro hmem
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmem
  unfold Env.find? at h
  exact (List.find?_eq_none.mp h) c hc (beq_self_eq_true _)

theorem PushChain.push {env : Env} {fe : FEnv} (h : PushChain env fe)
    {ci : ConstantInfo} (hfresh : fe.find? ci.name = none) :
    PushChain env (fe.push ci) := by
  obtain ⟨hc, ⟨new, hnew⟩, hnd⟩ := h
  refine ⟨?_, ⟨ci :: new, ?_⟩, ?_⟩
  · calc fe.push ci = (mkFEnv fe.env).push ci := by rw [← hc]
      _ = mkFEnv (fe.push ci).env := push_mkFEnv fe.env ci
  · show ci :: fe.env.consts = _
    rw [hnew]
    rfl
  · intro hnd₀
    show ((ci :: fe.env.consts).map (·.name)).Nodup
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, hnd hnd₀⟩
    rw [PushChain.find? ⟨hc, ⟨new, hnew⟩, hnd⟩] at hfresh
    exact Env.find?_none_notin hfresh

theorem PushChain.trans {env : Env} {fe₁ fe₂ : FEnv} (h₁ : PushChain env fe₁)
    (h₂ : PushChain fe₁.env fe₂) : PushChain env fe₂ := by
  obtain ⟨hc₁, ⟨new₁, hnew₁⟩, hnd₁⟩ := h₁
  obtain ⟨hc₂, ⟨new₂, hnew₂⟩, hnd₂⟩ := h₂
  exact ⟨hc₂, ⟨new₂ ++ new₁, by rw [hnew₂, hnew₁, List.append_assoc]⟩,
    fun h => hnd₂ (hnd₁ h)⟩

/-- A list of names, pairwise distinct and all fresh at `env`: pushing
constants of these names in this order is a fresh chain. -/
def FreshNames (env : Env) (ns : List Name) : Prop :=
  ns.Nodup ∧ ∀ n ∈ ns, env.find? n = none

theorem FreshNames.nil (env : Env) : FreshNames env [] :=
  ⟨List.nodup_nil, fun _ h => nomatch h⟩

/-- After pushing the head's constant, the tail is fresh at the
extended environment. -/
theorem FreshNames.step {env : Env} {c : ConstantInfo} {ns : List Name}
    (h : FreshNames env (c.name :: ns)) : FreshNames ⟨c :: env.consts⟩ ns := by
  obtain ⟨hnd, hfr⟩ := h
  rw [List.nodup_cons] at hnd
  refine ⟨hnd.2, fun n hn => ?_⟩
  rw [Env.find?_cons, if_neg (fun he => hnd.1 (by rw [he]; exact hn))]
  exact hfr n (List.mem_cons_of_mem _ hn)

/-- Freshness at the extended environment, with the head fresh at the
base, is freshness of the whole list at the base. -/
theorem FreshNames.cons_of {env : Env} {c : ConstantInfo} {ns : List Name}
    (hc : env.find? c.name = none) (h : FreshNames ⟨c :: env.consts⟩ ns) :
    FreshNames env (c.name :: ns) := by
  obtain ⟨hnd, hfr⟩ := h
  have hne : ∀ n ∈ ns, c.name ≠ n ∧ env.find? n = none := by
    intro n hn
    have := hfr n hn
    rw [Env.find?_cons] at this
    by_cases he : c.name = n
    · rw [if_pos he] at this; exact nomatch this
    · rw [if_neg he] at this; exact ⟨he, this⟩
  refine ⟨List.nodup_cons.mpr ⟨fun hm => (hne _ hm).1 rfl, hnd⟩, ?_⟩
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hc
  · exact (hne n hn).2

/-! ## The generic stage helpers keep the name and record the guard -/

theorem checkConstantValF_fresh (ops : CheckerOps CheckCM) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValF ops fe cv)
      (fun cvA => cvA.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold checkConstantValF
  yields
  all_goals exact Yields.pure ⟨rfl, Option.not_isSome_iff_eq_none.mp (by assumption)⟩

theorem checkMemberValF_fresh (ops : CheckerOps CheckCM)
    (blockNames : List Name) (fe : FEnv) (cv : ConstantVal) :
    Yields (checkMemberValF ops blockNames fe cv)
      (fun cvA => cvA.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold checkMemberValF
  refine Yields.bind' (checkConstantValF_fresh ops fe cv) fun cvA hcvA => ?_
  yields
  all_goals (apply Yields.pure; exact hcvA)

theorem checkConstantValC_fresh (mode : CheckMode) (fe : FEnv)
    (cv : ConstantVal) :
    Yields (checkConstantValC mode fe cv)
      (fun p => p.1.name = cv.name ∧ fe.find? cv.name = none) := by
  unfold checkConstantValC
  yields
  all_goals exact Yields.pure ⟨rfl, Option.not_isSome_iff_eq_none.mp (by assumption)⟩

/-! ## The value kinds -/

theorem checkDefnValC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) {cvA : ConstantVal} (hfr : fe.find? cvA.name = none)
    (jty value : Expr) (hint : ReducibilityHint) :
    Yields (checkDefnValC mode fe cvA jty value hint)
      (fun fe' => PushChain env fe') := by
  unfold checkDefnValC
  yields
  all_goals (apply Yields.pure; exact h.push hfr)

theorem checkThmValC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) {cvA : ConstantVal} (hfr : fe.find? cvA.name = none)
    (jty value : Expr) :
    Yields (checkThmValC mode fe cvA jty value)
      (fun fe' => PushChain env fe') := by
  unfold checkThmValC
  yields
  all_goals (apply Yields.pure; exact h.push hfr)

theorem checkOpaqueValC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) {cvA : ConstantVal} (hfr : fe.find? cvA.name = none)
    (jty value : Expr) :
    Yields (checkOpaqueValC mode fe cvA jty value)
      (fun fe' => PushChain env fe') := by
  unfold checkOpaqueValC
  yields
  all_goals (apply Yields.pure; exact h.push hfr)

/-! ## The modeled route -/

theorem checkIndMemberS_push (mode : CheckMode) (blockNames : List Name)
    (caps : IndCaps) {env : Env} {fe : FEnv} (h : PushChain env fe)
    (ci : ConstantInfo) :
    Yields (checkIndMemberS mode blockNames caps fe ci)
      (fun fe' => PushChain env fe') := by
  unfold checkIndMemberS
  ybind
  refine Yields.bind'
    (checkMemberValF_fresh (sharedOpsC mode fe) blockNames fe ci.toConstantVal)
    fun cvA hcvA => ?_
  obtain ⟨hn, hfr⟩ := hcvA
  cases ci with
  | indInfo cvI capsI =>
    refine Yields.pure (h.push ?_)
    show fe.find? cvA.name = none
    rw [hn]; exact hfr
  | ctorInfo cvI nP nF =>
    refine Yields.pure (h.push ?_)
    show fe.find? cvA.name = none
    rw [hn]; exact hfr
  | _ => exact Yields.ofThrow

theorem provisionRecsS_fresh (mode : CheckMode) (blockNames : List Name) :
    ∀ (recs : List ConstantInfo) {env : Env} (feAcc : FEnv),
      PushChain env feAcc →
      Yields (provisionRecsS mode blockNames feAcc recs)
        (fun p => FreshNames feAcc.env (p.2.map (·.1.name)))
  | [], env, feAcc, _ => by
    unfold provisionRecsS
    exact Yields.pure (FreshNames.nil _)
  | ci :: rest, env, feAcc, h => by
    unfold provisionRecsS
    cases ci with
    | recInfo cv mI rP rules =>
      ybind
      refine Yields.bind'
        (checkMemberValF_fresh (sharedOpsC mode feAcc) blockNames feAcc _)
        fun cvA hcvA => ?_
      obtain ⟨hn, hfr⟩ := hcvA
      have hfr' : feAcc.find? cvA.name = none := by rw [hn]; exact hfr
      refine Yields.bind'
        (provisionRecsS_fresh mode blockNames rest
          (feAcc.push (.recInfo cvA mI rP [])) (h.push hfr'))
        fun q hq => ?_
      obtain ⟨feSelf, others⟩ := q
      refine Yields.pure ?_
      rw [h.find?] at hfr'
      exact FreshNames.cons_of (c := .recInfo cvA mI rP []) hfr' hq
    | _ => exact Yields.ofThrow

/-- The recursor group's install fold: the provisioned names are pushed
in order onto the group's base index. -/
theorem recFold_push (mode : CheckMode) (blockNames : List Name)
    (fe₂ feSelf : FEnv) (f : Name → Name) :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule)) {env : Env}
      (acc : FEnv), PushChain env acc →
      FreshNames acc.env (checked.map (·.1.name)) →
      Yields (checked.foldlM (fun (acc : FEnv) c => do
          let rules' ← checkIotaRulesF mode (sharedOpsC mode feSelf) fe₂ feSelf
            f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules'))) acc)
        (fun acc' => PushChain env acc')
  | [], env, acc, h, _ => by
    simp only [List.foldlM_nil]
    exact Yields.pure h
  | c :: cs, env, acc, h, hf => by
    simp only [List.foldlM_cons]
    have hfr : acc.find? c.1.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    refine Yields.bind' (Q := fun acc' => ∃ rules',
        acc' = acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules'))
      (Yields.bind fun rules' => Yields.pure ⟨rules', rfl⟩) fun acc' hacc' => ?_
    obtain ⟨rules', rfl⟩ := hacc'
    exact recFold_push mode blockNames fe₂ feSelf f cs _ (h.push hfr)
      (FreshNames.step (c := .recInfo c.1 c.2.1 c.2.2.1 rules') hf)

theorem checkIndRecsS_push (mode : CheckMode) (blockNames : List Name)
    {env : Env} {fe₂ : FEnv} (h : PushChain env fe₂)
    (recs : List ConstantInfo) :
    Yields (checkIndRecsS mode blockNames fe₂ recs)
      (fun fe' => PushChain env fe') := by
  unfold checkIndRecsS
  simp only []
  split
  · exact Yields.pure h
  · split
    · refine Yields.bind'
        (provisionRecsS_fresh mode blockNames recs fe₂ h) fun q hq => ?_
      obtain ⟨feSelf, checked⟩ := q
      ybind
      exact recFold_push mode blockNames fe₂ feSelf _ checked fe₂ h hq
    · exact Yields.ofThrowBind

theorem checkProjLookupsF_fresh (fe : FEnv) (T ctorName : Name)
    (lps : List Name) (nP nF i : Nat) :
    Yields (checkProjLookupsF (m := CheckCM) fe T ctorName lps nP nF i)
      (fun _ => fe.find? (projFnName T i) = none) := by
  unfold checkProjLookupsF
  yields
  all_goals (apply Yields.pure; exact Option.isNone_iff_eq_none.mp (by assumption))

theorem checkProjFnS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) :
    Yields (checkProjFnS mode fe T ctorName lps nP nF i)
      (fun fe' => PushChain env fe') := by
  unfold checkProjFnS
  refine Yields.bind' (checkProjLookupsF_fresh fe T ctorName lps nP nF i)
    fun pr hfr => ?_
  yields
  all_goals (apply Yields.pure; exact h.push hfr)

theorem installProjFnStepS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) :
    Yields (installProjFnStepS mode T ctorName lps nP nF fe i)
      (fun fe' => PushChain env fe') := by
  unfold installProjFnStepS
  split
  · ybind
    exact checkProjFnS_push mode h T ctorName lps nP nF i
  · exact Yields.pure h

/-- The members-then-recursors phase, shared by both arms of
`checkIndDeclSF`'s block match. -/
theorem indBase_push (mode : CheckMode) (blockNames : List Name)
    (caps : IndCaps) {env : Env} {fe : FEnv} (h : PushChain env fe)
    (nonrecs recs : List ConstantInfo) :
    Yields (do
        let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames caps) fe
        checkIndRecsS mode blockNames fe₂ recs)
      (fun fe' => PushChain env fe') := by
  refine Yields.bind'
    (Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe)
      (g := fun u _ => u)
      (fun acc ci _ hacc => checkIndMemberS_push mode blockNames caps hacc ci)
      nonrecs fe () h) fun fe₂ h₂ => ?_
  exact checkIndRecsS_push mode blockNames h₂ recs

theorem checkIndDeclSF_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (block : List ConstantInfo) :
    Yields (checkIndDeclSF mode fe block)
      (fun fe' => PushChain env fe') := by
  unfold checkIndDeclSF
  simp only []
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue =>
    split
    case h_1 cvT capsT cvC nP nF hI hC =>
      ybind
      refine Yields.bind'
        (Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe)
          (g := fun u _ => u)
          (fun acc ci _ hacc => checkIndMemberS_push mode _ _ hacc ci) _ fe () h)
        fun fe₂ h₂ => ?_
      refine Yields.bind' (checkIndRecsS_push mode _ h₂ _) fun fe₃ h₃ => ?_
      split
      case isFalse => exact Yields.ofThrowBind
      case isTrue =>
        split
        case isFalse => exact Yields.ofThrowBind
        case isTrue =>
          split
          · exact Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe)
              (g := fun u _ => u)
              (fun acc i _ hacc =>
                installProjFnStepS_push mode hacc cvT.name cvC.name
                  cvT.levelParams nP nF i) (List.range nF) fe₃ () h₃
          · exact Yields.pure h₃
    case h_2 => exact indBase_push mode _ _ h _ _

/-! ## The fixpoint route -/

theorem checkSumIndF_push {env : Env} {fe : FEnv} (h : PushChain env fe)
    (ops : CheckerOps CheckCM) (p : InductiveShape)
    (capsOf : InductiveShape → IndCaps) :
    Yields (checkSumIndF ops fe p capsOf)
      (fun r => PushChain env r.1 ∧ ∃ s, r.2.2 = p.withSort s) := by
  unfold checkSumIndF
  refine Yields.bind' (checkConstantValF_fresh ops fe p.cvT) fun cvTa₀ h₀ => ?_
  obtain ⟨hn₀, hfr⟩ := h₀
  refine Yields.bind' (checkSumTeleF_name ops fe p.cvT _ cvTa₀) fun r hn => ?_
  obtain ⟨cvTa, s⟩ := r
  have hn' : cvTa.name = p.cvT.name := by
    rcases hn with h1 | h1
    · exact h1.trans hn₀
    · exact h1
  yields
  all_goals
    (refine Yields.pure ⟨h.push ?_, s, rfl⟩
     show fe.find? cvTa.name = none
     rw [hn']; exact hfr)

theorem checkSumCtorF_fresh (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    Yields (checkSumCtorF ops fe₀ fe T lps nP nIdx rs isProp large cvC nF cvTa)
      (fun r => r.1.name = cvC.name ∧ fe.find? cvC.name = none) := by
  unfold checkSumCtorF
  refine Yields.bind' (checkConstantValF_fresh ops fe cvC) fun cvCa₀ h₀ => ?_
  obtain ⟨hn₀, hfr⟩ := h₀
  refine Yields.bind' (normCtorValF_name ops fe T nP nF cvC cvCa₀ hn₀) fun cvCa hn => ?_
  yields
  all_goals (apply Yields.pure; exact ⟨hn, hfr⟩)

theorem checkSumCtorsF_fresh (ops : CheckerOps CheckCM) (fe₀ fe : FEnv)
    (T : Name) (lps : List Name) (nP nIdx : Nat) (rs : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    ∀ (cs : List (ConstantVal × Nat)),
      Yields (checkSumCtorsF ops fe₀ fe T lps nP nIdx rs isProp large cvTa cs)
        (fun r => r.1.map (·.1.name) = cs.map (·.1.name) ∧
          ∀ c ∈ r.1, fe.find? c.1.name = none)
  | [] => Yields.pure ⟨rfl, fun _ hc => nomatch hc⟩
  | c :: cs => by
    unfold checkSumCtorsF
    refine Yields.bind' (checkSumCtorF_fresh ops fe₀ fe T lps nP nIdx rs isProp
      large c.1 c.2 cvTa) fun q hq => ?_
    obtain ⟨cvCa, sorts⟩ := q
    obtain ⟨hn, hfr⟩ := hq
    refine Yields.bind' (checkSumCtorsF_fresh ops fe₀ fe T lps nP nIdx rs isProp
      large cvTa cs) fun rest hrest => ?_
    obtain ⟨rest, srest⟩ := rest
    obtain ⟨hrest, hfrs⟩ := hrest
    have hn' : cvCa.name = c.1.name := hn
    have hrest' : rest.map (·.1.name) = cs.map (·.1.name) := hrest
    refine Yields.pure ⟨by simp [hn', hrest'], ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · show fe.find? cvCa.name = none
      rw [hn]; exact hfr
    · exact hfrs d hd

/-- The constructors' conses: a fresh chain from the former's index. -/
theorem consSumCtorsF_push (nP : Nat) :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env} {fe : FEnv},
      PushChain env fe → FreshNames fe.env (ctorsA.map (·.1.name)) →
      PushChain env (consSumCtorsF nP ctorsA fe)
  | [], _, _, h, _ => h
  | c :: cs, env, fe, h, hf => by
    have hfr : fe.find? c.1.name = none := by
      rw [h.find?]
      exact hf.2 _ (by simp)
    exact consSumCtorsF_push nP (ctorsA := cs) (h.push hfr)
      (FreshNames.step (c := .ctorInfo c.1 nP c.2) hf)

theorem checkNativeRecF_fresh (ops : CheckerOps CheckCM) {w : StructWalkers}
    (fe : FEnv) (p : NativeParts) (cvTa : ConstantVal)
    (ctorsA : List (ConstantVal × Nat)) :
    Yields (checkNativeRecF ops w fe p cvTa ctorsA)
      (fun r => r.1.name = p.cvR.name ∧ fe.find? p.cvR.name = none) := by
  unfold checkNativeRecF
  refine Yields.letFun ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  try simp only []
  refine Yields.letFun ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  try simp only []
  refine Yields.letFun ?_
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?_)
  try simp only []
  refine Yields.bind' (checkConstantValF_fresh ops fe p.cvR) fun cvRi hcv => ?_
  yields
  all_goals (apply Yields.pure; exact ⟨rfl, hcv.2⟩)

theorem checkStructProjTableF_push {w : StructWalkers} {env : Env} {fe : FEnv}
    (h : PushChain env fe) (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) :
    Yields (checkStructProjTableF (m := CheckCM) w T C lps nP nF resSort guards
        off cvCa fe)
      (fun fe' => PushChain env fe') := by
  unfold checkStructProjTableF
  yields
  all_goals exact Yields.pure (h.push (Option.isNone_iff_eq_none.mp (by assumption)))

theorem checkNativeTableF_push {w : StructWalkers} {env : Env} {fe : FEnv}
    (h : PushChain env fe) (p : NativeParts) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) :
    Yields (checkNativeTableF (m := CheckCM) w p ctorsA sortss fe)
      (fun fe' => PushChain env fe') := by
  unfold checkNativeTableF
  split
  · split
    · exact checkStructProjTableF_push h _ _ _ _ _ _ _ _ _
    · exact Yields.pure h
  · exact Yields.pure h

/-- One pass (task #268): the former's cons keeps the chain, the
constructors are the block's by name and fresh at its environment. -/
theorem checkNativePassS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (p : NativeParts) (isRec : Bool) :
    Yields (checkNativePassS mode fe p isRec)
      (fun r => PushChain env r.1.env₁ ∧ r.1.p.ctors = p.ctors ∧
        r.1.ctorsA.map (·.1.name) = r.1.p.ctors.map (·.1.name) ∧
        ∀ c ∈ r.1.ctorsA, r.1.env₁.find? c.1.name = none) := by
  unfold checkNativePassS
  refine Yields.bind' (checkSumIndF_push h _ p.toInductiveShape
    (fun p₁ => nativeCapsAt p₁ isRec)) fun r₁ h₁ => ?_
  obtain ⟨fe₁, cvTa, p₁⟩ := r₁
  obtain ⟨h₁, s, hps⟩ := h₁
  try simp only [] at hps
  subst hps
  try simp only []
  ybind
  refine Yields.bind' (checkSumCtorsF_fresh _ fe₁ fe₁ _ _ _ _ _ _ _ cvTa _) fun r hr => ?_
  obtain ⟨ctorsA, sortss⟩ := r
  obtain ⟨hns, hfrs⟩ := hr
  try simp only []
  refine Yields.bind fun kinds => ?_
  refine Yields.pure ⟨h₁, ?_, ?_, hfrs⟩
  · simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
  · rw [hns]
    simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]

/-- The install after the pass keeps the chain. -/
theorem checkNativeTailS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    {q : NativePass FEnv} (h₁ : PushChain env q.env₁)
    (hnd : (q.p.ctors.map (·.1.name)).Nodup)
    (hns : q.ctorsA.map (·.1.name) = q.p.ctors.map (·.1.name))
    (hfrs : ∀ c ∈ q.ctorsA, q.env₁.find? c.1.name = none) :
    Yields (checkNativeTailS mode fe q) (fun fe' => PushChain env fe') := by
  unfold checkNativeTailS
  -- the elimination restriction, on the completed record
  try apply Yields.letFun
  refine Yields.ofDecCases (fun _ => ?elim) (fun _ => Yields.ofThrowBind)
  case elim =>
  ybind
  refine Yields.bind fun _isorts => ?_
  try simp only []
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue hk =>
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue _ =>
  ybind
  have hbase : PushChain env (consSumCtorsF q.p.nP q.ctorsA q.env₁) := by
    refine consSumCtorsF_push q.p.nP h₁ ⟨?_, ?_⟩
    · rw [hns]; exact hnd
    · intro n hn
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
      rw [← h₁.find?]
      exact hfrs c hc
  refine Yields.bind' (checkNativeRecF_fresh _ (consSumCtorsF q.p.nP q.ctorsA q.env₁) q.p q.cvTa
    q.ctorsA) fun r₃ h₃ => ?_
  obtain ⟨cvRa, rhss⟩ := r₃
  obtain ⟨hnR, hfrR⟩ := h₃
  try simp only [] at hnR hfrR
  try simp only []
  have hpush := hbase.push (ci := .recInfo cvRa q.p.majorIdx q.p.rulePrefix
    (sumRules (consSumCtorsF q.p.nP q.ctorsA q.env₁).find? cvRa.name
      q.p.nP q.p.majorIdx q.p.rulePrefix cvRa.type q.ctorsA rhss))
    (by show (consSumCtorsF q.p.nP q.ctorsA q.env₁).find? cvRa.name = none
        rw [hnR]; exact hfrR)
  exact checkNativeTableF_push hpush q.p q.ctorsA q.sortss

theorem checkNativeS_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (p : NativeParts) :
    Yields (checkNativeS mode fe p) (fun fe' => PushChain env fe') := by
  unfold checkNativeS
  -- the front guard: the distinct constructor names
  try apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hnd => ?main)
  case main =>
  ybind
  -- the pass at the syntactic reading, and again where it overshot
  refine Yields.bind' (checkNativePassS_push mode h p (nativeRawRec p)) fun r hr => ?_
  obtain ⟨q, settled⟩ := r
  obtain ⟨h₁, hpC, hns, hfrs⟩ := hr
  try simp only [] at h₁ hpC hns hfrs
  try simp only []
  cases settled with
  | true =>
    simp only [↓reduceIte]
    exact checkNativeTailS_push mode h₁ (by rw [hpC]; exact hnd) hns hfrs
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  ybind
  refine Yields.bind' (checkNativePassS_push mode h p (nativeIsRec q.p.kinds)) fun r' hr' => ?_
  obtain ⟨q', settled'⟩ := r'
  obtain ⟨h₁', hpC', hns', hfrs'⟩ := hr'
  try simp only [] at h₁' hpC' hns' hfrs'
  try simp only []
  try ylet
  split
  case isFalse => exact Yields.ofThrowBind
  case isTrue _ =>
  exact checkNativeTailS_push mode h₁' (by rw [hpC']; exact hnd) hns' hfrs'

/-! ## The declaration clause and the two drivers' steps -/

theorem installBasisDeclF_push {env : Env} {fe : FEnv} (h : PushChain env fe)
    (ci : ConstantInfo) :
    Yields (installBasisDeclF (m := CheckCM) fe ci)
      (fun fe' => PushChain env fe') := by
  unfold installBasisDeclF
  yields
  all_goals exact Yields.pure (h.push (Option.isNone_iff_eq_none.mp (by assumption)))

/-- The pinned-block install pushes onto the chain (task #293: three of
`checkDeclC`'s arms share this body). -/
theorem checkBasisDeclC_push {env : Env} {fe : FEnv}
    (h : PushChain env fe) (kind : BasisKind) :
    Yields (checkBasisDeclC fe kind) (fun fe' => PushChain env fe') := by
  have hfold : ∀ (fe' : FEnv), PushChain env fe' →
      Yields (kind.declsA.foldlM installBasisDeclF fe')
        (fun x => PushChain env x) :=
    fun fe' h' =>
      Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe)
        (g := fun u _ => u)
        (fun acc ci _ hacc => installBasisDeclF_push hacc ci)
        kind.declsA fe' () h'
  unfold checkBasisDeclC
  yields
  all_goals exact hfold fe h

theorem checkDeclC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pd : Declaration) :
    Yields (checkDeclC mode pins fe pd) (fun fe' => PushChain env fe') := by
  unfold checkDeclC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    obtain ⟨hp, hfr⟩ := hp
    simp only []
    have key : Yields (checkDefnValC mode fe cvA jty value hint)
        (fun fe' => PushChain env fe') :=
      checkDefnValC_push mode h (by show fe.find? cvA.name = none; rw [hp]; exact hfr)
        jty value hint
    split
    · refine Yields.bind' key fun fe2 h2 => ?_
      yields
      all_goals (apply Yields.pure; exact h2)
    · exact key
  | thmDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    obtain ⟨hp, hfr⟩ := hp
    exact checkThmValC_push mode h
      (by show fe.find? cvA.name = none; rw [hp]; exact hfr) jty value
  | opaqueDecl cv value =>
    simp only []
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    obtain ⟨hp, hfr⟩ := hp
    simp only []
    have key : Yields (checkOpaqueValC mode fe cvA jty value)
        (fun fe' => PushChain env fe') :=
      checkOpaqueValC_push mode h
        (by show fe.find? cvA.name = none; rw [hp]; exact hfr) jty value
    split
    · refine Yields.bind' key fun fe2 h2 => ?_
      yields
      all_goals (apply Yields.pure; exact h2)
    · exact key
  | axiomDecl cv =>
    simp only []
    -- task #293: `Quot.sound` is compared with the pin and pushes
    -- nothing
    split
    · split
      · exact Yields.pure h
      · exact Yields.ofThrow
    refine Yields.bind' (checkConstantValC_fresh mode fe cv) fun p hp => ?_
    obtain ⟨cvA, jty⟩ := p
    obtain ⟨hp, hfr⟩ := hp
    simp only []
    have hfrA : fe.find? cvA.name = none := by rw [hp]; exact hfr
    by_cases ht : cvA.name = sorryAxName
    · rw [if_neg (by rw [tolerated_not_std fe cvA ht]; exact Bool.false_ne_true),
        if_neg (tolerated_ne_trust ht), if_neg (tolerated_ne_ofReduce ht),
        if_neg (tolerated_ne_std ht), if_pos ht]
      exact Yields.pure h
    · rw [if_neg ht]
      yields
      all_goals first
        | (apply Yields.pure; exact h.push hfrA)
        | exact absurd (by assumption) ht
  | basisDecl kind => exact checkBasisDeclC_push h kind
  | quotDecl k cv =>
    -- task #293: the `type` record installs the pinned block, the other
    -- members install nothing
    simp only []
    cases k <;>
      (split
       · first
         | exact checkBasisDeclC_push h .quotK
         | exact Yields.pure h
       · exact Yields.ofThrow)
  | indDecl block nP =>
    simp only []
    -- task #293: a block the fold recognises as a pinned one installs
    -- the pin
    split
    · exact checkBasisDeclC_push h _
    · split
      · cases nativeParts? nP block with
        | none => exact checkIndDeclSF_push mode h block
        | some p => exact checkNativeS_push mode h p
      · exact Yields.ofThrow

theorem checkDeclStepC_push (mode : CheckMode) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pd : Declaration) :
    Yields (checkDeclStepC mode pins fe pd) (fun fe' => PushChain env fe') := by
  unfold checkDeclStepC
  ybind
  exact checkDeclC_push mode h pd

/-- Phase A's step body: a fresh chain, and the pending records grow
by at most the one it may push. -/
theorem annotStepC_push (mode : CheckMode) (i : Nat) {env : Env} {fe : FEnv}
    (h : PushChain env fe) (pend : Array PendingCheck) (pd : Declaration) :
    Yields (annotStepC mode pins i fe pend pd)
      (fun r => PushChain env r.1 ∧ ∃ new, r.2.toList = pend.toList ++ new) := by
  have hord : ∀ pd', Yields (do pure (← checkDeclStepC mode pins fe pd', pend) :
      CheckCM (FEnv × Array PendingCheck))
      (fun r => PushChain env r.1 ∧ ∃ new, r.2.toList = pend.toList ++ new) :=
    fun pd' => Yields.bind' (checkDeclStepC_push mode h pd') fun fe' h' =>
      Yields.pure ⟨h', [], by simp⟩
  unfold annotStepC
  cases pd with
  | defnDecl cv value hint =>
    simp only []
    split
    · exact hord _
    · refine Yields.bind' (annotValueC_fresh mode fe cv value true) fun r hr => ?_
      obtain ⟨cvA, jty, jv⟩ := r
      obtain ⟨hp, hfr⟩ := hr
      exact Yields.pure ⟨h.push (by show fe.find? cvA.name = none; rw [hp]; exact hfr), _,
        Array.toList_push⟩
  | thmDecl cv value =>
    simp only []
    ybind
    refine Yields.bind' (annotConstantValC_fresh mode fe cv) fun p hr => ?_
    obtain ⟨cvA, jty⟩ := p
    obtain ⟨hp, hfr⟩ := hr
    ybind
    exact Yields.pure ⟨h.push (by show fe.find? cvA.name = none; rw [hp]; exact hfr), _,
      Array.toList_push⟩
  | opaqueDecl cv value =>
    simp only []
    split
    · exact hord _
    · refine Yields.bind' (annotValueC_fresh mode fe cv value false) fun r hr => ?_
      obtain ⟨cvA, jty, jv⟩ := r
      obtain ⟨hp, hfr⟩ := hr
      exact Yields.pure ⟨h.push (by show fe.find? cvA.name = none; rw [hp]; exact hfr), _,
        Array.toList_push⟩
  | axiomDecl cv => exact hord _
  | basisDecl kind => exact hord _
  | quotDecl k cv => exact hord _
  | indDecl block nP => exact hord _

/-- **Phase A is a fresh chain**: from a canonical index, an accepting
run returns a canonical index whose constants extend the start by
fresh names, and the pending records extend the start's. -/
theorem installRun_trace (mode : CheckMode) {ds : List Declaration} {env : Env}
    {p : Nat × FEnv × Array PendingCheck} {s : CState}
    {q : Nat × FEnv × Array PendingCheck} {s' : CState}
    (h : InstallRun mode pins ds p s q s') (hp : PushChain env p.2.1) :
    PushChain env q.2.1 ∧ ∃ new, q.2.2.toList = p.2.2.toList ++ new := by
  induction h with
  | nil p s => exact ⟨hp, [], by simp⟩
  | @cons pd ds p p₁ q s s₁ s' hstep rest ih =>
    obtain ⟨fe₁, pend₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    obtain ⟨h₁, new₁, hpend₁⟩ :=
      annotStepC_push mode p.1 hp p.2.2 _ s (fe₁, pend₁) _ hstepC
    obtain ⟨h₂, new₂, hpend₂⟩ := ih h₁
    exact ⟨h₂, new₁ ++ new₂, by rw [hpend₂, hpend₁, List.append_assoc]⟩

end Ix.Kernel.Cached
