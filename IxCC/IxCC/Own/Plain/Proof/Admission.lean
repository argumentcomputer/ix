import IxCC.Own.Plain.Proof.Program

/-! Derive the callee's actual numbered source body and checked scope from
the canonical checker. A call arity lookup cannot authorize an unchecked
out-of-range map entry. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

theorem programDomain_function {P : Fir.Program} (h : programDomain P = true)
    {f : Fir.FunId} {fd : Fir.Fun} (hf : f < P.size) (hd : P.fun? f = some fd) :
    funDomain fd = true ∧ fresh [] (fd.params.map (·.1)) = true ∧
      scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body = true := by
  unfold programDomain at h
  have he := List.all_eq_true.mp h f (List.mem_range.mpr hf)
  simpa only [hd, Bool.and_eq_true, and_assoc] using he

theorem contractProgramDomain_function {P : Fir.Program} (h : contractProgramDomain P = true)
    {f : Fir.FunId} {fd : Fir.Fun} (hf : f < P.size) (hd : P.fun? f = some fd) :
    contractFunDomain fd = true ∧ fresh [] (fd.params.map (·.1)) = true ∧
      scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body = true := by
  unfold contractProgramDomain at h
  have he := List.all_eq_true.mp h f (List.mem_range.mpr hf)
  simpa only [hd, Bool.and_eq_true, and_assoc] using he

theorem signatures_lookup {P : Fir.Program} {f : Fir.FunId} {n : Nat}
    (h : (signatures P).lookup f = some n) :
    ∃ fd, f < P.size ∧ P.fun? f = some fd ∧ fd.arity = n := by
  obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp h
  have hm : (f, n) ∈ signatures P := by rw [he]; simp
  unfold signatures at hm
  obtain ⟨⟨g, fd⟩, hg, hpair⟩ := List.mem_map.mp hm
  have hp : g = f ∧ fd.arity = n := by simpa using hpair
  rcases hp with ⟨rfl, hn⟩
  unfold Fir.Program.funList at hg
  obtain ⟨i, hi, hlookup⟩ := List.mem_filterMap.mp hg
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hlookup
  obtain ⟨fd', hfd, hif, hff⟩ := hlookup
  subst i
  subst fd'
  exact ⟨fd, List.mem_range.mp hi, hfd, hn⟩

theorem checkPlainMap_function {P : Fir.Program} {bodies : Src.NatMap Code}
    (checked : checkPlainMap P bodies = true)
    {f : Fir.FunId} {fd : Fir.Fun} (hf : f < P.size) (hd : P.fun? f = some fd) :
    funDomain fd = true ∧ fresh [] (fd.params.map (·.1)) = true ∧
      scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body = true ∧
      bodies.get? f = some (lowerCode (fd.params.map (·.1)) [] fd.body) := by
  obtain ⟨domain, _, canonical⟩ := checkPlainMap_parts checked
  obtain ⟨hdom, hfresh, hscope⟩ := programDomain_function domain hf hd
  have hbody : bodies = (Program.canonical P).bodies :=
    congrArg Program.bodies canonical
  rw [hbody]
  exact ⟨hdom, hfresh, hscope, canonical_body_of hd⟩

theorem checkContractPlainMap_function {P : Fir.Program} {bodies : Src.NatMap Code}
    (checked : checkContractPlainMap P bodies = true)
    {f : Fir.FunId} {fd : Fir.Fun} (hf : f < P.size) (hd : P.fun? f = some fd) :
    contractFunDomain fd = true ∧ fresh [] (fd.params.map (·.1)) = true ∧
      scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body = true ∧
      bodies.get? f = some (lowerCode (fd.params.map (·.1)) [] fd.body) := by
  obtain ⟨domain, _, canonical⟩ := checkContractPlainMap_parts checked
  obtain ⟨hdom, hfresh, hscope⟩ := contractProgramDomain_function domain hf hd
  have hbody : bodies = (Program.canonical P).bodies :=
    congrArg Program.bodies canonical
  rw [hbody]
  exact ⟨hdom, hfresh, hscope, canonical_body_of hd⟩

theorem checkContractPlainMap_pins {P : Fir.Program} {bodies : Src.NatMap Code}
    (checked : checkContractPlainMap P bodies = true) :
    BoolPinsOk P :=
  checkBoolPins_sound (checkContractPlainMap_parts checked).2.1

/-- Normalize a `Fir.Fun`'s surface contract metadata (`result`, `contracts`,
`letContracts`) to the plain `.shared`/`.many` defaults while preserving its
execution fields (`key`, `params`, `body`, `vars`, `joins`). -/
def normalizeFunContracts (fd : Fir.Fun) : Fir.Fun :=
  { fd with result := .shared, contracts := [], letContracts := [] }

/-- Normalize every function's surface contract metadata in `P`. -/
def normalizeProgramContracts (P : Fir.Program) : Fir.Program :=
  { P with funs := P.funs.map normalizeFunContracts }

theorem funDomain_normalizeFunContracts (fd : Fir.Fun) :
    funDomain (normalizeFunContracts fd) = contractFunDomain fd := by
  simp [funDomain, normalizeFunContracts, contractFunDomain]

theorem normalizeProgramContracts_fun? (P : Fir.Program) (f : Fir.FunId) :
    (normalizeProgramContracts P).fun? f = (P.fun? f).map normalizeFunContracts :=
  Proof.get?_map normalizeFunContracts P.funs f

theorem signatures_normalizeProgramContracts (P : Fir.Program) :
    signatures (normalizeProgramContracts P) = signatures P := by
  unfold signatures Fir.Program.funList
  have hsz : (normalizeProgramContracts P).size = P.size := rfl
  rw [hsz, List.map_filterMap, List.map_filterMap]
  refine congrArg (List.filterMap · (List.range P.size)) (funext fun f => ?_)
  rw [normalizeProgramContracts_fun?]
  cases P.fun? f <;> rfl

theorem programDomain_normalizeProgramContracts (P : Fir.Program) :
    programDomain (normalizeProgramContracts P) = contractProgramDomain P := by
  unfold programDomain contractProgramDomain
  have hsz : (normalizeProgramContracts P).size = P.size := rfl
  rw [hsz, signatures_normalizeProgramContracts]
  refine congrArg ((List.range P.size).all ·) (funext fun f => ?_)
  rw [normalizeProgramContracts_fun?]
  cases P.fun? f with
  | none => rfl
  | some fd =>
    simp only [Option.map_some, funDomain_normalizeFunContracts]
    rfl

private theorem natMap_map_map {α β γ : Type} (f : α → β) (g : β → γ)
    (m : Src.NatMap α) : (m.map f).map g = m.map (fun x => g (f x)) := by
  induction m with
  | leaf => rfl
  | node v z o iz io =>
    cases v <;> simp [Src.NatMap.map, iz, io]

theorem canonical_normalizeProgramContracts (P : Fir.Program) :
    (Program.canonical (normalizeProgramContracts P)).bodies = (Program.canonical P).bodies := by
  unfold Program.canonical normalizeProgramContracts
  dsimp only
  rw [natMap_map_map]
  rfl

theorem checkBoolPins_normalizeProgramContracts (P : Fir.Program) :
    checkBoolPins (normalizeProgramContracts P) = checkBoolPins P := rfl

theorem checkPlainMap_normalizeProgramContracts (P : Fir.Program) (candidate : Src.NatMap Code) :
    checkPlainMap (normalizeProgramContracts P) candidate = checkContractPlainMap P candidate := by
  unfold checkPlainMap checkContractPlainMap
  rw [programDomain_normalizeProgramContracts, checkBoolPins_normalizeProgramContracts,
    canonical_normalizeProgramContracts]

private theorem jump_measure_norm {j : Fir.JoinId} {J : List JEntry} {e : JEntry} {rest : List JEntry}
    (h : lookupJ j J = some (e, rest)) (hc : e.charged = false) :
    e.body.size + jweight (e.after rest) < (Code.jmp j []).size + jweight J := by
  have hw := lookupJ_weight j h
  rw [JEntry.jweight_after]
  simp only [JEntry.weight, hc, Bool.false_eq_true, ↓reduceIte] at hw
  simp only [Code.size]
  omega

section
set_option linter.unusedSectionVars false
variable (F : Fir.Program) (bodies : Src.NatMap Code) {k : Nat}
  (ih : ∀ j < k, ∀ ρ J H c,
    eval { source := normalizeProgramContracts F, bodies } j ρ J H c =
      eval { source := F, bodies } j ρ J H c)
include ih

theorem callFun_normalizeProgramContracts_of (fd : Fir.Fun) (body : Code)
    (vs : List RVal) (H : Heap) :
    callFun { source := normalizeProgramContracts F, bodies } k (normalizeFunContracts fd) body vs H =
      callFun { source := F, bodies } k fd body vs H := by
  unfold callFun normalizeFunContracts
  dsimp only
  split
  · cases k with
    | zero => rfl
    | succ j => exact ih j (Nat.lt_succ_self j) _ [] H body
  · rfl

theorem evalCall_normalizeProgramContracts_of (f : Fir.FunId) (vs : List RVal) (H : Heap) :
    evalCall { source := normalizeProgramContracts F, bodies } k f vs H =
      evalCall { source := F, bodies } k f vs H := by
  rw [evalCall_eq, evalCall_eq]
  dsimp only
  rw [normalizeProgramContracts_fun?]
  cases F.fun? f with
  | none => rfl
  | some fd =>
    simp only [Option.map_some, Sem.Result.ofOption, Sem.Result.bind_ok]
    cases bodies.get? f with
    | none => rfl
    | some body =>
      simp only [Sem.Result.bind_ok]
      exact callFun_normalizeProgramContracts_of F bodies ih fd body vs H

mutual
theorem eval_normalizeProgramContracts_of (ρ : Own.Env) (J : List JEntry) (H : Heap) (c : Code) :
    eval { source := normalizeProgramContracts F, bodies } k ρ J H c =
      eval { source := F, bodies } k ρ J H c := by
  match c with
  | .act a c' =>
    rw [eval_act, eval_act]
    cases evalAction ρ H a with
    | ok H' => exact eval_normalizeProgramContracts_of ρ J H' c'
    | timeout | resource _ | trap | stuck => rfl
  | .bind x r c' =>
    by_cases hr : ∃ f args, r = .call f args
    · obtain ⟨f, args, rfl⟩ := hr
      rw [eval_bindCall, eval_bindCall]
      cases Own.evalArgs ρ args with
      | none => rfl
      | some vs =>
        simp only [Sem.Result.ofOption, Sem.Result.bind_ok,
          evalCall_normalizeProgramContracts_of F bodies ih f vs H]
        cases evalCall { source := F, bodies } k f vs H with
        | ok p => exact eval_normalizeProgramContracts_of (ρ.insert x p.1) J p.2 c'
        | timeout | resource _ | trap | stuck => rfl
    · have hr' : ∀ f args, r ≠ .call f args := fun f args h => hr ⟨f, args, h⟩
      rw [eval_bindRhs _ _ _ _ _ _ _ _ hr', eval_bindRhs _ _ _ _ _ _ _ _ hr']
      have htables : ({ source := normalizeProgramContracts F, bodies } : Program).tables =
          ({ source := F, bodies } : Program).tables := rfl
      rw [htables]
      cases evalRhs ({ source := F, bodies } : Program).tables ρ H r with
      | ok p => exact eval_normalizeProgramContracts_of (ρ.insert x p.1) J p.2 c'
      | timeout | resource _ | trap | stuck => rfl
  | .jp j ps captured rec body c' =>
    rw [eval_jp, eval_jp]
    exact eval_normalizeProgramContracts_of ρ _ H c'
  | .jmp j args =>
    rw [eval_jmp, eval_jmp]
    cases hp : lookupJ j J with
    | none => rfl
    | some p =>
      obtain ⟨e, rest⟩ := p
      simp only [Sem.Result.ofOption, Sem.Result.bind_ok]
      cases Own.evalArgs ρ args with
      | none => rfl
      | some vs =>
        simp only [Sem.Result.bind_ok, jumpTo]
        split
        · split
          · cases k with
            | zero => rfl
            | succ i => exact ih i (Nat.lt_succ_self i) _ _ H e.body
          · next hc =>
            have := jump_measure_norm hp (by simpa using hc)
            exact eval_normalizeProgramContracts_of _ (e.after rest) H e.body
        · rfl
  | .case x alts d =>
    rw [eval_case, eval_case]
    cases ρ.get? x with
    | none => rfl
    | some v =>
      simp only [Sem.Result.ofOption, Sem.Result.bind_ok]
      have hknown : (normalizeProgramContracts F).known = F.known := rfl
      rw [hknown]
      cases v.asCtor F.known H with
      | some kf => exact evalAlts_normalizeProgramContracts_of ρ J H kf.1 alts d
      | none => rfl
  | .ret a => rw [eval_ret, eval_ret]
  | .tcall f args =>
    rw [eval_tcall, eval_tcall]
    cases Own.evalArgs ρ args with
    | none => rfl
    | some vs => exact evalCall_normalizeProgramContracts_of F bodies ih f vs H
  | .trap => rw [eval_trap, eval_trap]
termination_by c.size + jweight J
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Code.size]; omega)
    | (simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]; omega)
    | (simp only [Code.size] at this ⊢; omega)

theorem evalAlts_normalizeProgramContracts_of (ρ : Own.Env) (J : List JEntry) (H : Heap)
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code) :
    evalAlts { source := normalizeProgramContracts F, bodies } k ρ J H key alts d =
      evalAlts { source := F, bodies } k ρ J H key alts d := by
  match alts, d with
  | [], some c =>
    rw [evalAlts_nil, evalAlts_nil]
    exact eval_normalizeProgramContracts_of ρ J H c
  | [], none => rw [evalAlts_nil, evalAlts_nil]
  | .mk key' body :: rest, d =>
    rw [evalAlts_cons, evalAlts_cons]
    split
    · exact eval_normalizeProgramContracts_of ρ J H body
    · exact evalAlts_normalizeProgramContracts_of ρ J H key rest d
termination_by Code.altsSize alts + Code.optSize d + jweight J + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)
end
end

theorem eval_normalizeProgramContracts (F : Fir.Program) (bodies : Src.NatMap Code) :
    ∀ k ρ J H c,
      eval { source := normalizeProgramContracts F, bodies } k ρ J H c =
        eval { source := F, bodies } k ρ J H c := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih => intro ρ J H c; exact eval_normalizeProgramContracts_of F bodies ih ρ J H c

theorem evalCall_normalizeProgramContracts (F : Fir.Program) (bodies : Src.NatMap Code)
    (k : Nat) (f : Fir.FunId) (vs : List RVal) (H : Heap) :
    evalCall { source := normalizeProgramContracts F, bodies } k f vs H =
      evalCall { source := F, bodies } k f vs H :=
  evalCall_normalizeProgramContracts_of F bodies
    (fun j _ => eval_normalizeProgramContracts F bodies j) f vs H

theorem run_normalizeProgramContracts (F : Fir.Program) (bodies : Src.NatMap Code)
    (k : Nat) (f : Fir.FunId) (args : List RVal) (H : Heap := {}) :
    run { source := normalizeProgramContracts F, bodies } k f args H =
      run { source := F, bodies } k f args H :=
  evalCall_normalizeProgramContracts F bodies k f args H

end IxCC.Own.Plain
