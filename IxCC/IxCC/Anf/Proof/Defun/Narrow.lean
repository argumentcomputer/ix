import IxCC.Anf.Defun.Narrow
import IxCC.Anf.Proof.Pass.DeadParam
import IxCC.Src.Proof.NatMap
import IxCC.Anf.Proof.Walk.StepA
import IxCC.Sem.Dominance

/-! # P9 flow-directed dispatch narrowing is correct

`Narrow.run c P` validates an untrusted closed-world closure-flow certificate `c`
and narrows dispatch sites with `≤ c.maxArms` reachable closure keys to a short
`case` without a default arm; if validation fails (or `P` is not first-order or
has closure-keyed pinned constructors), it returns `P` unchanged.

Because validation is checked inside `run`, soundness holds unconditionally for
**any** certificate `c` (`run_refines`): a wrong flow oracle costs speed only.
The proof tracks an exact-equality value relation refined by `ValOk dc` (every
constructor's fields obey the certificate's field flows and no `Val.clos`
arises) and `ClosOk a` (every closure constructor key lies in `a`), proves
simulation for `checkExpPlain`, `instExp` (under an arbitrary continuation
matching the target continuation), and `checkRewriteExp` at every clock bound,
and concludes `run_wf`, `run_firstOrder`, `run_tables`, and `run_refines`. -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Narrow.Proof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Anf.WalkProof (later_bind_shift)

/-! ## Tables and roots -/

/-- `Narrow.run` leaves `known`, `ctors`, and `roots` untouched (no `Classical.choice`). -/
theorem run_tables (c : Cert) (P : Program) :
    (run c P).known = P.known ∧ (run c P).ctors = P.ctors ∧ (run c P).roots = P.roots := by
  unfold run
  split
  · exact ⟨rfl, rfl, rfl⟩
  · dsimp only
    split
    · exact ⟨rfl, rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩

/-! ## Value invariants and abstract flow bounds -/

/-- A value satisfies closure-key upper bound `a`: if it is a closure constructor
`.con (.clo f j) _` and `a = some ks`, then `.clo f j ∈ ks`. All non-closure
values satisfy every bound. -/
def ClosOk (a : KAbs) : Val → Prop
  | .con (.clo f j) _ =>
    match a with
    | none => True
    | some ks => Key.CtorKey.clo f j ∈ ks
  | _ => True

/-- Every constructor value in the tree has fields satisfying `dc`'s field flows,
and no higher-order `Val.clos` appears. -/
inductive ValOk (dc : DecCert) : Val → Prop where
  | lit (l : Lam.Lit) : ValOk dc (.lit l)
  | box : ValOk dc .box
  | con (c : Key.CtorKey) (fs : List Val) :
      (∀ (i : Nat) v, fs[i]? = some v → ValOk dc v) →
      (∀ (i : Nat) v, fs[i]? = some v → ClosOk (fieldFlow dc c i) v) →
      ValOk dc (.con c fs)

/-- Exact equality refined by `ValOk dc` and return closure bound `rflow`. -/
def ValRel (dc : DecCert) (rflow : KAbs) (v w : Val) : Prop :=
  v = w ∧ ValOk dc v ∧ ClosOk rflow v

theorem ClosOk.none (v : Val) : ClosOk none v := by
  cases v with
  | con c _ => cases c <;> trivial
  | _ => trivial

theorem ClosOk.lit (a : KAbs) (l : Lam.Lit) : ClosOk a (.lit l) := trivial

theorem ClosOk.box (a : KAbs) : ClosOk a .box := trivial

theorem ClosOk.src (a : KAbs) (s : Src.CId) (fs : List Val) :
    ClosOk a (.con (.src s) fs) := trivial

theorem kabsSub_sound {a b : KAbs} {v : Val} (h : kabsSub a b = true) (hv : ClosOk a v) :
    ClosOk b v := by
  cases v with
  | con c fs =>
    cases c with
    | src s => trivial
    | clo f j =>
      cases a with
      | none =>
        cases b with
        | none => trivial
        | some ys => simp [kabsSub] at h
      | some xs =>
        cases b with
        | none => trivial
        | some ys =>
          simp only [kabsSub, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
          obtain ⟨y, hy, hxy⟩ := h (.clo f j) hv
          show Key.CtorKey.clo f j ∈ ys
          rw [hxy]; exact hy
  | _ => trivial

theorem kabsListSub_length : ∀ {xs ys : List KAbs}, kabsListSub xs ys = true → xs.length = ys.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [kabsListSub, Bool.and_eq_true] at h
    simp [kabsListSub_length h.2]
  | [], _ :: _, h => by simp [kabsListSub] at h
  | _ :: _, [], h => by simp [kabsListSub] at h

theorem kabsListSub_get : ∀ {xs ys : List KAbs}, kabsListSub xs ys = true →
    ∀ {i : Nat} {a b : KAbs}, xs[i]? = some a → ys[i]? = some b → kabsSub a b = true
  | [], [], _, _, _, _, ha, _ => by simp at ha
  | _ :: _, _ :: _, h, 0, _, _, ha, hb => by
    simp only [kabsListSub, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
    subst ha; subst hb; exact h.1
  | _ :: xs, _ :: ys, h, i + 1, _, _, ha, hb => by
    simp only [kabsListSub, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_succ] at ha hb
    exact kabsListSub_get h.2 ha hb
  | [], _ :: _, h, _, _, _, _, _ => by simp [kabsListSub] at h
  | _ :: _, [], h, _, _, _, _, _ => by simp [kabsListSub] at h

theorem ValOk.not_clos {dc : DecCert} {v : Val} (h : ValOk dc v) :
    ∀ ρ n b got, v ≠ .clos ρ n b got := by
  cases h <;> intro _ _ _ _ he <;> cases he

/-! ## Environment invariant `EnvOk` -/

/-- Every value in `ρ` is `ValOk dc` and satisfies its flow entry in `env`
(defaulting to `none` past `env.length`). -/
def EnvOk (dc : DecCert) (env : List KAbs) (ρ : List Val) : Prop :=
  ∀ (i : Nat) v, ρ[i]? = some v → ValOk dc v ∧ ClosOk ((env[i]?).getD none) v

theorem EnvOk.nil (dc : DecCert) (env : List KAbs) : EnvOk dc env [] := by
  intro i v h; simp at h

theorem EnvOk.cons {dc : DecCert} {a : KAbs} {v : Val} {env : List KAbs} {ρ : List Val}
    (hv : ValOk dc v) (hc : ClosOk a v) (h : EnvOk dc env ρ) : EnvOk dc (a :: env) (v :: ρ) := by
  intro i w hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi; exact ⟨hv, hc⟩
  | succ i =>
    simp only [List.getElem?_cons_succ] at hi ⊢
    exact h i w hi

theorem EnvOk.append {dc : DecCert} {env₁ env₂ : List KAbs} {ρ₁ ρ₂ : List Val}
    (hl : env₁.length = ρ₁.length) (h₁ : EnvOk dc env₁ ρ₁) (h₂ : EnvOk dc env₂ ρ₂) :
    EnvOk dc (env₁ ++ env₂) (ρ₁ ++ ρ₂) := by
  intro i v hi
  by_cases hlt : i < ρ₁.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by omega)]
    exact h₁ i v hi
  · rw [List.getElem?_append_right (by omega)] at hi
    rw [List.getElem?_append_right (by omega), hl]
    exact h₂ (i - ρ₁.length) v hi

theorem EnvOk.reverse {dc : DecCert} {env : List KAbs} {ρ : List Val}
    (hl : env.length = ρ.length) (h : EnvOk dc env ρ) : EnvOk dc env.reverse ρ.reverse := by
  intro i v hi
  have hlt : i < ρ.length := by
    have := (List.getElem?_eq_some_iff.1 hi).1
    simpa using this
  rw [List.getElem?_reverse (by omega)] at hi
  rw [List.getElem?_reverse (by omega), hl]
  exact h (ρ.length - 1 - i) v hi

theorem EnvOk.sub {dc : DecCert} {xs ys : List KAbs} {vs : List Val}
    (hl : xs.length = vs.length) (hsub : kabsListSub xs ys = true) (h : EnvOk dc xs vs) :
    EnvOk dc ys vs := by
  have hyl := kabsListSub_length hsub
  intro i v hi
  have hlt : i < vs.length := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨hv, hc⟩ := h i v hi
  have hxa : xs[i]? = some xs[i] := List.getElem?_eq_getElem (by omega)
  have hyb : ys[i]? = some ys[i] := List.getElem?_eq_getElem (by omega)
  rw [hxa, Option.getD_some] at hc
  rw [hyb, Option.getD_some]
  exact ⟨hv, kabsSub_sound (kabsListSub_get hsub hxa hyb) hc⟩

theorem EnvOk.replicate_none {dc : DecCert} {n : Nat} {vs : List Val}
    (h : ∀ v ∈ vs, ValOk dc v) : EnvOk dc (List.replicate n none) vs := by
  intro i v hi
  have hmem : v ∈ vs := List.mem_of_getElem? hi
  refine ⟨h v hmem, ?_⟩
  cases hget : (List.replicate n (none : KAbs))[i]? with
  | none => exact ClosOk.none v
  | some a =>
    have ha : a = none := by
      have := List.mem_of_getElem? hget
      exact List.eq_of_mem_replicate this
    subst ha; exact ClosOk.none v

theorem EnvOk.lits (dc : DecCert) (ps : List KAbs) (ns : List Nat) :
    EnvOk dc ps (ns.map fun n => .lit (.nat n)) := by
  intro i v hi
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hi)
  exact ⟨.lit (.nat n), ClosOk.lit _ _⟩

theorem EnvOk.atom {dc : DecCert} {env : List KAbs} {ρ : List Val} (h : EnvOk dc env ρ)
    {a : Atom} {v : Val} (ha : a.eval ρ = some v) :
    ValOk dc v ∧ ClosOk (atomFlow env a) v := by
  cases a with
  | var i => exact h i v ha
  | lit l =>
    simp only [Atom.eval, Option.some.injEq] at ha
    subst ha; exact ⟨.lit l, ClosOk.lit _ _⟩
  | box =>
    simp only [Atom.eval, Option.some.injEq] at ha
    subst ha; exact ⟨.box, ClosOk.box _⟩

theorem atomsFlow_length (env : List KAbs) : ∀ as : List Atom, (atomsFlow env as).length = as.length
  | [] => rfl
  | _ :: as => by simp [atomsFlow, atomsFlow_length env as]

theorem EnvOk.atoms {dc : DecCert} {env : List KAbs} {ρ : List Val} (h : EnvOk dc env ρ) :
    ∀ {as : List Atom} {vs : List Val}, evalAtoms ρ as = some vs →
      EnvOk dc (atomsFlow env as) vs
  | [], vs, hs => by
    simp only [evalAtoms, Option.some.injEq] at hs
    subst hs; exact EnvOk.nil dc _
  | a :: as, vs, hs => by
    rw [evalAtoms_cons] at hs
    cases ha : a.eval ρ with
    | none => rw [ha] at hs; cases hs
    | some v =>
      rw [ha] at hs
      cases hss : evalAtoms ρ as with
      | none => rw [hss] at hs; cases hs
      | some ws =>
        rw [hss] at hs
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hs
        subst hs
        obtain ⟨hv, hc⟩ := h.atom ha
        exact (h.atoms hss).cons hv hc

theorem fieldFlows_length (dc : DecCert) (c : Key.CtorKey) (n : Nat) :
    (fieldFlows dc c n).length = n := by
  simp [fieldFlows]

theorem fieldFlows_get (dc : DecCert) (c : Key.CtorKey) (n i : Nat) (hi : i < n) :
    (fieldFlows dc c n)[i]? = some (fieldFlow dc c i) := by
  simp [fieldFlows, List.getElem?_map, List.getElem?_range hi]

theorem paramFlows_length (P : Program) (dc : DecCert) (g : GlobalId) (n : Nat) :
    (paramFlows P dc g n).length = n := by
  unfold paramFlows
  cases dc.params.get? g with
  | none => simp
  | some ps =>
    cases h : (ps.length == n) with
    | true => simp only [h, ↓reduceIte]; exact beq_iff_eq.1 h
    | false => simp only [h, Bool.false_eq_true, ↓reduceIte, List.length_replicate]

theorem knownClosure_false {K : Lam.Known} (h : knownClosure K = false) :
    (∀ c, K.natZero = some c → closureKey c = false) ∧
    (∀ c, K.natSucc = some c → closureKey c = false) ∧
    (∀ c, K.boolFalse = some c → closureKey c = false) ∧
    (∀ c, K.boolTrue = some c → closureKey c = false) := by
  unfold knownClosure at h
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc; have := h.1; simp [hc] at this; exact this
  · intro c hc; have := h.2.1; simp [hc] at this; exact this
  · intro c hc; have := h.2.2.1; simp [hc] at this; exact this
  · intro c hc; have := h.2.2.2; simp [hc] at this; exact this

theorem asCtor_ok {K : Lam.Known} {dc : DecCert} (hk : knownClosure K = false)
    {v : Val} (hv : ValOk dc v) {c : Key.CtorKey} {fs : List Val}
    (ha : v.asCtor K = some (c, fs)) :
    EnvOk dc (fieldFlows dc c fs.length) fs ∧
    (∀ f j, c = .clo f j → v = .con (.clo f j) fs) := by
  obtain ⟨h0, hS, _, _⟩ := knownClosure_false hk
  cases hv with
  | box => simp [Val.asCtor] at ha
  | con c' fs' hfsV hfsC =>
    simp only [Val.asCtor, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    refine ⟨fun i w hi => ?_, fun f j hc => by subst hc; rfl⟩
    have hlt : i < fs'.length := (List.getElem?_eq_some_iff.1 hi).1
    rw [fieldFlows_get dc c' fs'.length i hlt, Option.getD_some]
    exact ⟨hfsV i w hi, hfsC i w hi⟩
  | lit l =>
    cases l with
    | str s => simp [Val.asCtor] at ha
    | nat n =>
      cases n with
      | zero =>
        simp only [Val.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at ha
        obtain ⟨c0, hc0, rfl, rfl⟩ := ha
        refine ⟨EnvOk.nil dc _, fun f j hc => ?_⟩
        subst hc
        have := h0 (.clo f j) hc0
        simp [closureKey] at this
      | succ m =>
        simp only [Val.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at ha
        obtain ⟨c0, hc0, rfl, rfl⟩ := ha
        refine ⟨?_, fun f j hc => ?_⟩
        · intro i w hi
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi; exact ⟨.lit (.nat m), ClosOk.lit _ _⟩
          | succ i => simp at hi
        · subst hc
          have := hS (.clo f j) hc0
          simp [closureKey] at this

theorem primResult_ok {K : Lam.Known} {dc : DecCert} (hk : knownClosure K = false)
    {p : Lam.Prim} {vs : List Val} {v : Val} (h : primResult K p vs = .ok v) :
    ValOk dc v ∧ ClosOk (some []) v := by
  obtain ⟨_, _, hF, hT⟩ := knownClosure_false hk
  unfold primResult at h
  cases hn : natArgs vs with
  | none => rw [hn] at h; cases h
  | some ns =>
    rw [hn] at h; dsimp only at h
    cases hp : p.sem ns with
    | none => rw [hp] at h; cases h
    | some r =>
      rw [hp] at h
      cases r with
      | nat m =>
        dsimp only at h; cases h
        exact ⟨.lit (.nat m), ClosOk.lit _ _⟩
      | bool b =>
        dsimp only at h
        cases b with
        | true =>
          simp only [↓reduceIte] at h
          cases hc : K.boolTrue with
          | none => rw [hc] at h; cases h
          | some c =>
            rw [hc] at h; dsimp only at h; cases h
            have hnc := hT c hc
            cases c with
            | clo _ _ => simp [closureKey] at hnc
            | src s => exact ⟨.con (.src s) [] (fun _ _ hi => by simp at hi) (fun _ _ hi => by simp at hi), ClosOk.src _ _ _⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases hc : K.boolFalse with
          | none => rw [hc] at h; cases h
          | some c =>
            rw [hc] at h; dsimp only at h; cases h
            have hnc := hF c hc
            cases c with
            | clo _ _ => simp [closureKey] at hnc
            | src s => exact ⟨.con (.src s) [] (fun _ _ hi => by simp at hi) (fun _ _ hi => by simp at hi), ClosOk.src _ _ _⟩

/-! ## Deduplication and narrowed alternatives -/

theorem dedupKeysAux_mem : ∀ (seen ks : List Key.CtorKey) (k : Key.CtorKey),
    k ∈ dedupKeysAux seen ks ↔ k ∈ ks ∧ k ∉ seen
  | seen, [], k => by simp [dedupKeysAux]
  | seen, x :: ks, k => by
    unfold dedupKeysAux
    by_cases hs : seen.any (fun s => decide (s = x)) = true
    · rw [if_pos hs]
      have hx : x ∈ seen := by
        simp only [List.any_eq_true, decide_eq_true_eq] at hs
        obtain ⟨s, hm, rfl⟩ := hs; exact hm
      rw [dedupKeysAux_mem seen ks k]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨List.mem_cons_of_mem x h1, h2⟩
      · intro ⟨h1, h2⟩
        rcases List.mem_cons.1 h1 with rfl | hm
        · exact absurd hx h2
        · exact ⟨hm, h2⟩
    · rw [Bool.not_eq_true] at hs
      rw [hs]; simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      have hnx : x ∉ seen := by
        intro hmem
        have : seen.any (fun s => decide (s = x)) = true :=
          List.any_eq_true.2 ⟨x, hmem, by simp⟩
        rw [hs] at this; cases this
      rw [dedupKeysAux_mem (x :: seen) ks k]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, hnx⟩
        · exact ⟨Or.inr h1, fun hm => h2 (List.mem_cons_of_mem x hm)⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · by_cases hkx : k = x
          · exact Or.inl hkx
          · exact Or.inr ⟨h1, fun hm => by
              rcases List.mem_cons.1 hm with rfl | hm'
              · exact hkx rfl
              · exact h2 hm'⟩

theorem dedupKeys_mem (ks : List Key.CtorKey) (k : Key.CtorKey) :
    k ∈ dedupKeys ks ↔ k ∈ ks := by
  simpa [dedupKeys] using dedupKeysAux_mem [] ks k

theorem dedupKeysAux_nodup : ∀ (seen ks : List Key.CtorKey), (dedupKeysAux seen ks).Nodup
  | _, [] => List.nodup_nil
  | seen, x :: ks => by
    unfold dedupKeysAux
    split
    · exact dedupKeysAux_nodup seen ks
    · refine List.nodup_cons.2 ⟨?_, dedupKeysAux_nodup (x :: seen) ks⟩
      intro hmem
      have := (dedupKeysAux_mem (x :: seen) ks x).1 hmem
      exact this.2 List.mem_cons_self

theorem dedupKeys_nodup (ks : List Key.CtorKey) : (dedupKeys ks).Nodup :=
  dedupKeysAux_nodup [] ks

theorem evalAlts_allClo_src {P : Program} {k : Nat} {ρ : List Val} {J : List JClo}
    {s : Src.CId} {fs : List Val} : ∀ {alts : List Alt},
    allCloAlts alts = true → evalAlts P k ρ J (.src s) fs alts none = .stuck
  | [], _ => evalAlts_nil P k ρ J (.src s) fs none
  | .mk (.clo f j) n body :: rest, h => by
    rw [evalAlts_cons]
    have hne : ¬ (Key.CtorKey.clo f j = .src s ∧ n = fs.length) := fun hc => nomatch hc.1
    rw [if_neg hne]
    exact evalAlts_allClo_src h
  | .mk (.src _) _ _ :: _, h => by simp [allCloAlts] at h

theorem evalAlts_filter_nil {P : Program} {k : Nat} {ρ : List Val} {J : List JClo}
    {c : Key.CtorKey} {fs : List Val} : ∀ {alts : List Alt},
    alts.filter (fun a => decide (a.key = c)) = [] →
    evalAlts P k ρ J c fs alts none = .stuck
  | [], _ => evalAlts_nil P k ρ J c fs none
  | .mk key n body :: rest, h => by
    rw [evalAlts_cons]
    by_cases hk : key = c
    · subst hk; simp [Alt.key] at h
    · have hne : ¬ (key = c ∧ n = fs.length) := fun hc => hk hc.1
      rw [if_neg hne]
      have h' : rest.filter (fun a => decide (a.key = c)) = [] := by
        simpa [Alt.key, hk] using h
      exact evalAlts_filter_nil h'

theorem evalAlts_filter_singleton {P : Program} {k : Nat} {ρ : List Val} {J : List JClo}
    {c : Key.CtorKey} {fs : List Val} {nf : Nat} {body : Exp} : ∀ {alts : List Alt},
    alts.filter (fun a => decide (a.key = c)) = [.mk c nf body] →
    evalAlts P k ρ J c fs alts none =
      if nf = fs.length then eval P k (fs.reverse ++ ρ) J body else .stuck
  | [], h => by simp at h
  | .mk key n b :: rest, h => by
    rw [evalAlts_cons]
    by_cases hk : key = c
    · subst hk
      simp only [List.filter_cons, Alt.key, decide_true, ↓reduceIte, List.cons.injEq,
        Alt.mk.injEq] at h
      obtain ⟨⟨-, rfl, rfl⟩, hrest⟩ := h
      by_cases hn : n = fs.length
      · rw [if_pos ⟨rfl, hn⟩, if_pos hn]
      · rw [if_neg (fun hc => hn hc.2), if_neg hn]
        exact evalAlts_filter_nil hrest
    · have hne : ¬ (key = c ∧ n = fs.length) := fun hc => hk hc.1
      rw [if_neg hne]
      have h' : rest.filter (fun a => decide (a.key = c)) = [.mk c nf body] := by
        simpa [Alt.key, hk] using h
      exact evalAlts_filter_singleton h'

theorem narrowArms_keys_mem {P : Program} {dc : DecCert} {dispAlts : List Alt} {args : List Atom}
    {argFlows : List KAbs} {contJump : Bool} {siteRet : KAbs} :
    ∀ {ks : List Key.CtorKey} {nAlts : List Alt} {uArms : List GlobalId},
    narrowArms P dc dispAlts args argFlows contJump siteRet ks = some (nAlts, uArms) →
    ∀ a ∈ nAlts, a.key ∈ ks
  | [], _, _, h, a, hm => by
    simp only [narrowArms, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; cases hm
  | ck :: rest, nAlts, uArms, h, a, hm => by
    unfold narrowArms at h
    cases hf : dispAlts.filter (fun a => decide (a.key = ck)) with
    | nil =>
      rw [hf] at h
      exact List.mem_cons_of_mem ck (narrowArms_keys_mem h a hm)
    | cons alt more =>
      cases more with
      | nil =>
        obtain ⟨key, nf, altBody⟩ := alt
        rw [hf] at h; dsimp only at h
        have hkeq : key = ck := by
          have : Alt.mk key nf altBody ∈ dispAlts.filter (fun a => decide (a.key = ck)) := by
            rw [hf]; exact List.mem_cons_self
          have hdec := (List.mem_filter.1 this).2
          simp only [Alt.key] at hdec
          exact of_decide_eq_true hdec
        subst hkeq
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨u1, _, armBody, _, ⟨restAlts, u2⟩, hrest, rfl, rfl⟩ := h
        rcases List.mem_cons.1 hm with rfl | hm'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem key (narrowArms_keys_mem hrest a hm')
      | cons _ _ =>
        cases alt; rw [hf] at h; dsimp only at h; cases h

theorem narrowArms_spec {P : Program} {dc : DecCert} {dispAlts : List Alt} {args : List Atom}
    {argFlows : List KAbs} {contJump : Bool} {siteRet : KAbs} :
    ∀ {ks : List Key.CtorKey} {nAlts : List Alt} {uArms : List GlobalId},
    ks.Nodup →
    narrowArms P dc dispAlts args argFlows contJump siteRet ks = some (nAlts, uArms) →
    ∀ {c : Key.CtorKey}, c ∈ ks →
      dispAlts.filter (fun a => decide (a.key = c)) = [] ∨
      ∃ nf altBody armBody u1,
        dispAlts.filter (fun a => decide (a.key = c)) = [.mk c nf altBody] ∧
        nAlts.filter (fun a => decide (a.key = c)) = [.mk c nf armBody] ∧
        checkExpPlain P dc siteRet ((fieldFlows dc c nf).reverse ++ argFlows.reverse) [] altBody = some u1 ∧
        instExp args nf contJump 0 0 altBody = some armBody ∧
        (∀ h ∈ u1, h ∈ uArms)
  | [], _, _, _, _, _, hc => nomatch hc
  | ck :: rest, nAlts, uArms, hnd, h, c, hc => by
    obtain ⟨hckNot, hrestNd⟩ := List.nodup_cons.1 hnd
    unfold narrowArms at h
    cases hf : dispAlts.filter (fun a => decide (a.key = ck)) with
    | nil =>
      rw [hf] at h
      rcases List.mem_cons.1 hc with rfl | hcre
      · exact .inl hf
      · exact narrowArms_spec hrestNd h hcre
    | cons alt more =>
      cases more with
      | nil =>
        obtain ⟨key, nf, altBody⟩ := alt
        rw [hf] at h; dsimp only at h
        have hkeq : key = ck := by
          have : Alt.mk key nf altBody ∈ dispAlts.filter (fun a => decide (a.key = ck)) := by
            rw [hf]; exact List.mem_cons_self
          have hdec := (List.mem_filter.1 this).2
          simp only [Alt.key] at hdec
          exact of_decide_eq_true hdec
        subst hkeq
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨u1, hu1, armBody, harm, ⟨restAlts, u2⟩, hrest, rfl, rfl⟩ := h
        rcases List.mem_cons.1 hc with rfl | hcre
        · right
          have hrestNil : restAlts.filter (fun a => decide (a.key = c)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro a ha hdec
            have hkey : a.key = c := of_decide_eq_true hdec
            rw [← hkey] at hckNot
            exact hckNot (narrowArms_keys_mem hrest a ha)
          refine ⟨nf, altBody, armBody, u1, hf, ?_, hu1, harm, fun h hm => List.mem_append_left u2 hm⟩
          rw [List.filter_cons]
          simp only [Alt.key, decide_true, ↓reduceIte]
          exact congrArg _ hrestNil
        · have hne : key ≠ c := fun he => hckNot (he ▸ hcre)
          rcases narrowArms_spec hrestNd hrest hcre with hnil | ⟨nf', altB, armB, u1', hd, hn, hck, hi, hu⟩
          · exact .inl hnil
          · right
            refine ⟨nf', altB, armB, u1', hd, ?_, hck, hi, fun h hm => List.mem_append_right u1 (hu h hm)⟩
            rw [List.filter_cons]
            simp only [Alt.key, hne, decide_false, Bool.false_eq_true, ↓reduceIte]
            exact hn
      | cons _ _ =>
        cases alt; rw [hf] at h; dsimp only at h; cases h

/-! ## Instantiation preserves atom evaluation -/

theorem evalAtoms_get {ρ : List Val} : ∀ {as : List Atom} {vs : List Val},
    evalAtoms ρ as = some vs → ∀ {i : Nat} {a : Atom},
      as[i]? = some a → a.eval ρ = vs[i]?
  | [], vs, h, _, _, ha => by simp at ha
  | a :: as, vs, h, i, a', ha => by
    rw [evalAtoms_cons] at h
    cases ha0 : a.eval ρ with
    | none => rw [ha0] at h; cases h
    | some v =>
      rw [ha0] at h
      cases hss : evalAtoms ρ as with
      | none => rw [hss] at h; cases h
      | some ws =>
        rw [hss] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
          subst ha; exact ha0
        | succ i =>
          simp only [List.getElem?_cons_succ] at ha ⊢
          exact evalAtoms_get hss ha

theorem shiftAtom_eval {pre ρ : List Val} (a : Atom) :
    (shiftAtom pre.length a).eval (pre ++ ρ) = a.eval ρ := by
  cases a with
  | lit l => rfl
  | box => rfl
  | var x =>
    simp only [shiftAtom, Atom.eval]
    rw [List.getElem?_append_right (by omega)]
    congr 1; omega

theorem instAtom_eval {args : List Atom} {ρ_site allVs pre : List Val} {nf depth : Nat}
    (hargs : evalAtoms ρ_site args = some allVs) (hpre : pre.length = depth + nf)
    {a a' : Atom} (hi : instAtom args nf depth a = some a') :
    a'.eval (pre ++ ρ_site) = a.eval (pre ++ allVs.reverse) := by
  have hall : allVs.length = args.length := evalAtoms_length ρ_site hargs
  cases a with
  | lit l => simp only [instAtom, Option.some.injEq] at hi; subst hi; rfl
  | box => simp only [instAtom, Option.some.injEq] at hi; subst hi; rfl
  | var i =>
    simp only [instAtom] at hi
    split at hi
    · next hlt =>
      simp only [Option.some.injEq] at hi; subst hi
      simp only [Atom.eval, List.getElem?_append_left (show i < pre.length by omega)]
    · next hge =>
      split at hi
      · next hk =>
        obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hi
        rw [← hpre, shiftAtom_eval b, evalAtoms_get hargs hb]
        simp only [Atom.eval]
        rw [List.getElem?_append_right (by omega), hpre, List.getElem?_reverse (by omega), hall]
      · cases hi

theorem instAtoms_eval {args : List Atom} {ρ_site allVs pre : List Val} {nf depth : Nat}
    (hargs : evalAtoms ρ_site args = some allVs) (hpre : pre.length = depth + nf) :
    ∀ {as as' : List Atom}, instAtoms args nf depth as = some as' →
      evalAtoms (pre ++ ρ_site) as' = evalAtoms (pre ++ allVs.reverse) as
  | [], as', hi => by
    simp only [instAtoms, Option.some.injEq] at hi; subst hi; rfl
  | a :: as, as', hi => by
    simp only [instAtoms, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
    obtain ⟨a', ha', bs', hbs', rfl⟩ := hi
    rw [evalAtoms_cons, evalAtoms_cons, instAtom_eval hargs hpre ha', instAtoms_eval hargs hpre hbs']

/-! ## First-order preservation -/

mutual

theorem instExp_firstOrder {isFn : GlobalId → Bool} {args : List Atom} {nf : Nat}
    {contJump : Bool} {depth jdepth : Nat} :
    ∀ {e e' : Exp}, instExp args nf contJump depth jdepth e = some e' →
      e.firstOrder isFn = true → e'.firstOrder isFn = true
  | .bind c b e, _, hi, hfo => by
    simp only [instExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
    obtain ⟨b', hb', e', he', rfl⟩ := hi
    simp only [Exp.firstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨instBind_firstOrder hb' hfo.1, instExp_firstOrder he' hfo.2⟩
  | .join ar r b e, _, hi, hfo => by
    simp only [instExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
    obtain ⟨b', hb', e', he', rfl⟩ := hi
    simp only [Exp.firstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨instExp_firstOrder hb' hfo.1, instExp_firstOrder he' hfo.2⟩
  | .jump j as, _, hi, _ => by
    simp only [instExp] at hi
    split at hi
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
      obtain ⟨as', _, rfl⟩ := hi; rfl
    · cases hi
  | .case x alts dflt, _, hi, hfo => by
    simp only [instExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
    obtain ⟨x', _, alts', halts', dflt', hdflt', rfl⟩ := hi
    simp only [Exp.firstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨instAlts_firstOrder halts' hfo.1, instOpt_firstOrder hdflt' hfo.2⟩
  | .ret a, _, hi, _ => by
    simp only [instExp, Option.bind_eq_bind, Option.bind_eq_some_iff] at hi
    obtain ⟨a', _, h2⟩ := hi
    split at h2 <;> (simp only [Option.some.injEq] at h2; subst h2; rfl)
  | .tick e, _, hi, hfo => by
    simp only [instExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
    obtain ⟨e', he', rfl⟩ := hi
    simp only [Exp.firstOrder] at hfo ⊢
    exact instExp_firstOrder he' hfo
  | .trap, _, hi, _ => by
    simp only [instExp, Option.some.injEq] at hi; subst hi; rfl

theorem instBind_firstOrder {isFn : GlobalId → Bool} {args : List Atom} {nf depth : Nat} :
    ∀ {b b' : Bind}, instBind args nf depth b = some b' →
      b.firstOrder isFn = true → b'.firstOrder isFn = true
  | .atom a, _, hi, _ => by
    obtain ⟨a', _, rfl⟩ := Option.map_eq_some_iff.1 hi; rfl
  | .con c as, _, hi, _ => by
    obtain ⟨as', _, rfl⟩ := Option.map_eq_some_iff.1 hi; rfl
  | .proj c i x, _, hi, _ => by
    obtain ⟨x', _, rfl⟩ := Option.map_eq_some_iff.1 hi; rfl
  | .prim p as, _, hi, _ => by
    obtain ⟨as', _, rfl⟩ := Option.map_eq_some_iff.1 hi; rfl
  | .glob g, _, hi, hfo => by
    simp only [instBind, Option.some.injEq] at hi; subst hi; exact hfo
  | .call g as, _, hi, _ => by
    obtain ⟨as', _, rfl⟩ := Option.map_eq_some_iff.1 hi; rfl
  | .app .., _, hi, _ => by cases hi
  | .fn .., _, hi, _ => by cases hi

theorem instAlts_firstOrder {isFn : GlobalId → Bool} {args : List Atom} {nf : Nat}
    {contJump : Bool} {depth jdepth : Nat} :
    ∀ {alts alts' : List Alt}, instAlts args nf contJump depth jdepth alts = some alts' →
      Exp.altsFirstOrder isFn alts = true → Exp.altsFirstOrder isFn alts' = true
  | [], _, hi, _ => by simp only [instAlts, Option.some.injEq] at hi; subst hi; rfl
  | .mk k n b :: rest, _, hi, hfo => by
    simp only [instAlts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
    obtain ⟨b', hb', rest', hrest', rfl⟩ := hi
    simp only [Exp.altsFirstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨instExp_firstOrder hb' hfo.1, instAlts_firstOrder hrest' hfo.2⟩

theorem instOpt_firstOrder {isFn : GlobalId → Bool} {args : List Atom} {nf : Nat}
    {contJump : Bool} {depth jdepth : Nat} :
    ∀ {d d' : Option Exp}, instOpt args nf contJump depth jdepth d = some d' →
      Exp.optFirstOrder isFn d = true → Exp.optFirstOrder isFn d' = true
  | none, _, hi, _ => by simp only [instOpt, Option.some.injEq] at hi; subst hi; rfl
  | some e, _, hi, hfo => by
    obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.1 hi
    exact instExp_firstOrder he' hfo

end

theorem altsFirstOrder_mem {isFn : GlobalId → Bool} : ∀ {alts : List Alt},
    Exp.altsFirstOrder isFn alts = true → ∀ a ∈ alts, a.body.firstOrder isFn = true
  | [], _, _, hm => nomatch hm
  | .mk _ _ b :: rest, h, a, hm => by
    simp only [Exp.altsFirstOrder, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hm with rfl | hm'
    · exact h.1
    · exact altsFirstOrder_mem h.2 a hm'

theorem narrowArms_firstOrder {P : Program} {dc : DecCert} {isFn : GlobalId → Bool}
    {dispAlts : List Alt} {args : List Atom} {argFlows : List KAbs}
    {contJump : Bool} {siteRet : KAbs}
    (hdisp : Exp.altsFirstOrder isFn dispAlts = true) :
    ∀ {ks : List Key.CtorKey} {nAlts : List Alt} {uArms : List GlobalId},
    narrowArms P dc dispAlts args argFlows contJump siteRet ks = some (nAlts, uArms) →
    Exp.altsFirstOrder isFn nAlts = true
  | [], _, _, h => by
    simp only [narrowArms, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | ck :: rest, _, _, h => by
    unfold narrowArms at h
    cases hf : dispAlts.filter (fun a => decide (a.key = ck)) with
    | nil => rw [hf] at h; exact narrowArms_firstOrder hdisp h
    | cons alt more =>
      cases more with
      | nil =>
        obtain ⟨key, nf, altBody⟩ := alt
        rw [hf] at h
        have hmem : Alt.mk key nf altBody ∈ dispAlts := by
          have : Alt.mk key nf altBody ∈ dispAlts.filter (fun a => decide (a.key = ck)) := by
            rw [hf]; exact List.mem_cons_self
          exact (List.mem_filter.1 this).1
        have hfoB : altBody.firstOrder isFn = true := altsFirstOrder_mem hdisp _ hmem
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨_, _, armBody, harm, ⟨restAlts, _⟩, hrest, rfl, rfl⟩ := h
        simp only [Exp.altsFirstOrder, Bool.and_eq_true]
        exact ⟨instExp_firstOrder harm hfoB, narrowArms_firstOrder hdisp hrest⟩
      | cons _ _ => cases alt; rw [hf] at h; dsimp only at h; cases h

mutual

theorem checkRewriteExp_firstOrder {P : Program} {dc : DecCert}
    (hfoP : FirstOrder P) (hw : P.WF) :
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)} {st : RwSt}
      {e e' : Exp} {st' : RwSt},
    checkRewriteExp P dc rflow env jenv st e = some (e', st') →
    e.firstOrder (fun g => (P.arity? g).any (· > 0)) = true →
    e'.firstOrder (fun g => (P.arity? g).any (· > 0)) = true
  | rflow, env, jenv, st, .bind c b body, e', st', h, hfo => by
    simp only [Exp.firstOrder, Bool.and_eq_true] at hfo
    cases b with
    | call d args =>
      cases args with
      | nil =>
        simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨bf, u1⟩, _, ⟨body', st2⟩, hbody, rfl, rfl⟩ := h
        simp only [Exp.firstOrder, Bool.and_eq_true]
        exact ⟨hfo.1, checkRewriteExp_firstOrder hfoP hw hbody hfo.2⟩
      | cons f as =>
        unfold checkRewriteExp at h
        dsimp only at h
        split at h
        · rename_i res htried
          simp only [Option.some.injEq] at h; subst h
          cases hgd : P.global? d with
          | none => rw [hgd] at htried; dsimp only at htried; cases htried
          | some gd =>
            rw [hgd] at htried; dsimp only at htried
            have hmem : (d, gd) ∈ P.globalList :=
              DeadParam.Proof.mem_globalList_iff.2 ⟨hw.1 d gd hgd, hgd⟩
            have hfoD : gd.body.firstOrder (fun g => (P.arity? g).any (· > 0)) = true :=
              List.all_eq_true.1 hfoP (d, gd) hmem
            split at htried
            · cases hgb : gd.body with
              | bind _ _ _ | join _ _ _ _ | jump _ _ | ret _ | tick _ | trap => rw [hgb] at htried; dsimp only at htried; cases htried
              | case x dispAlts dflt =>
                cases x with
                | lit _ | box => rw [hgb] at htried; dsimp only at htried; cases htried
                | var m =>
                  cases dflt with
                  | some _ => rw [hgb] at htried; dsimp only at htried; cases htried
                  | none =>
                    rw [hgb] at htried hfoD; dsimp only at htried
                    simp only [Exp.firstOrder, Bool.and_eq_true] at hfoD
                    split at htried
                    · cases hat : atomFlow env f with
                      | none => rw [hat] at htried; dsimp only at htried; cases htried
                      | some ks =>
                        rw [hat] at htried; dsimp only at htried
                        split at htried
                        · split at htried
                          · next nAlts uArms hna =>
                            have hfoAlts := narrowArms_firstOrder hfoD.1 hna
                            cases htail : isTailRet body with
                            | true =>
                              simp only [htail, ↓reduceIte] at htried
                              have hite : ∀ {p : Prop} [Decidable p] {α : Type} {a b : α},
                                  (if p then some a else none) = some b → a = b := by
                                intro p _ _ _ _ hp; split at hp
                                · exact Option.some.inj hp
                                · cases hp
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hite htried)
                              simp [Exp.firstOrder, Exp.optFirstOrder, hfoAlts]
                            | false =>
                              simp only [htail, Bool.false_eq_true, ↓reduceIte] at htried
                              split at htried
                              · next body' st2 hbr =>
                                simp only [Option.some.injEq, Prod.mk.injEq] at htried
                                obtain ⟨rfl, rfl⟩ := htried
                                simp only [Exp.firstOrder, Exp.optFirstOrder, Bool.and_eq_true,
                                  and_true]
                                exact ⟨checkRewriteExp_firstOrder hfoP hw hbr hfo.2, hfoAlts⟩
                              · cases htried
                          · cases htried
                        · cases htried
                    · cases htried
            · cases htried
        · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨⟨bf, u1⟩, _, ⟨body', st2⟩, hbody, rfl, rfl⟩ := h
          simp only [Exp.firstOrder, Bool.and_eq_true]
          exact ⟨hfo.1, checkRewriteExp_firstOrder hfoP hw hbody hfo.2⟩
    | atom _ | con _ _ | proj _ _ _ | prim _ _ | glob _ | app _ _ | fn _ _ =>
      simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨bf, u1⟩, _, ⟨body', st2⟩, hbody, rfl, rfl⟩ := h
      simp only [Exp.firstOrder, Bool.and_eq_true]
      exact ⟨hfo.1, checkRewriteExp_firstOrder hfoP hw hbody hfo.2⟩
  | rflow, env, jenv, st, .join n r b body, e', st', h, hfo => by
    simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨b', st2⟩, hb, ⟨body', st3⟩, hbody, rfl, rfl⟩ := h
    simp only [Exp.firstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨checkRewriteExp_firstOrder hfoP hw hb hfo.1,
           checkRewriteExp_firstOrder hfoP hw hbody hfo.2⟩
  | rflow, env, jenv, st, .jump j as, e', st', h, _ => by
    simp only [checkRewriteExp] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
      · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | rflow, env, jenv, st, .case x alts dflt, e', st', h, hfo => by
    simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨alts', st1⟩, halts, ⟨dflt', st2⟩, hdflt, rfl, rfl⟩ := h
    simp only [Exp.firstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨checkRewriteAlts_firstOrder hfoP hw halts hfo.1,
           checkRewriteOpt_firstOrder hfoP hw hdflt hfo.2⟩
  | rflow, env, jenv, st, .ret a, e', st', h, _ => by
    simp only [checkRewriteExp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    · cases h
  | rflow, env, jenv, st, .tick e, e', st', h, hfo => by
    simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨e1, st1⟩, he, rfl, rfl⟩ := h
    simp only [Exp.firstOrder] at hfo ⊢
    exact checkRewriteExp_firstOrder hfoP hw he hfo
  | rflow, env, jenv, st, .trap, e', st', h, _ => by
    simp only [checkRewriteExp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl

theorem checkRewriteAlts_firstOrder {P : Program} {dc : DecCert}
    (hfoP : FirstOrder P) (hw : P.WF) :
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)} {st : RwSt}
      {alts alts' : List Alt} {st' : RwSt},
    checkRewriteAlts P dc rflow env jenv st alts = some (alts', st') →
    Exp.altsFirstOrder (fun g => (P.arity? g).any (· > 0)) alts = true →
    Exp.altsFirstOrder (fun g => (P.arity? g).any (· > 0)) alts' = true
  | _, _, _, _, [], _, _, h, _ => by
    simp only [checkRewriteAlts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | rflow, env, jenv, st, .mk c n b :: rest, _, _, h, hfo => by
    simp only [checkRewriteAlts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨b', st1⟩, hb, ⟨rest', st2⟩, hrest, rfl, rfl⟩ := h
    simp only [Exp.altsFirstOrder, Bool.and_eq_true] at hfo ⊢
    exact ⟨checkRewriteExp_firstOrder hfoP hw hb hfo.1,
           checkRewriteAlts_firstOrder hfoP hw hrest hfo.2⟩

theorem checkRewriteOpt_firstOrder {P : Program} {dc : DecCert}
    (hfoP : FirstOrder P) (hw : P.WF) :
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)} {st : RwSt}
      {d d' : Option Exp} {st' : RwSt},
    checkRewriteOpt P dc rflow env jenv st d = some (d', st') →
    Exp.optFirstOrder (fun g => (P.arity? g).any (· > 0)) d = true →
    Exp.optFirstOrder (fun g => (P.arity? g).any (· > 0)) d' = true
  | _, _, _, _, none, _, _, h, _ => by
    simp only [checkRewriteOpt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | rflow, env, jenv, st, some e, _, _, h, hfo => by
    simp only [checkRewriteOpt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨e', st'⟩, he, rfl, rfl⟩ := h
    exact checkRewriteExp_firstOrder hfoP hw he hfo

end

/-! ## Worklist closure (`checkDisps`) and global map assembly (`rewriteGlobals`) -/

/-- A closed set `S` of active globals: every non-dispatcher global passed
`checkRewriteExp` with all referenced globals in `S`, and every dispatcher
global in `S` is unchanged in `Q` and passed `checkExpPlain` with all
referenced globals in `S`. -/
structure Closed (P Q : Program) (dc : DecCert) (S : GlobalId → Prop) : Prop where
  known : Q.known = P.known
  knownOk : knownClosure P.known = false
  roots : ∀ r ∈ P.roots, S r
  arity : ∀ g, Q.arity? g = P.arity? g
  nonDisp : ∀ g gd, P.global? g = some gd → Walk.isDispatchKey gd.key = false →
    ∃ gd' st', Q.global? g = some gd' ∧ gd'.ps = gd.ps ∧
      checkRewriteExp P dc (retFlow dc g) (paramFlows P dc g gd.ps.length).reverse []
        { joins := (dc.joins.get? g).getD [], siteRets := (dc.siteRets.get? g).getD [], used := [] }
        gd.body = some (gd'.body, st') ∧
      ∀ h ∈ st'.used, S h
  disp : ∀ g gd, S g → P.global? g = some gd → Walk.isDispatchKey gd.key = true →
    Q.global? g = some gd ∧
    ∃ u, checkExpPlain P dc (retFlow dc g) (paramFlows P dc g gd.ps.length).reverse [] gd.body = some u ∧
      ∀ h ∈ u, S h

theorem natSet_contains_insert {s : Src.NatSet} {g x : Nat}
    (h : s.contains x = true) : (s.insert g).contains x = true := by
  unfold Src.NatMap.contains at h ⊢
  unfold Src.NatSet.insert
  by_cases hxe : x = g
  · subst hxe; rw [Src.NatMap.get?_insert_self]; rfl
  · rw [Src.NatMap.get?_insert_ne _ _ hxe]; exact h

theorem natSet_contains_insert_self (s : Src.NatSet) (g : Nat) :
    (s.insert g).contains g = true := by
  unfold Src.NatSet.insert Src.NatMap.contains
  rw [Src.NatMap.get?_insert_self]; rfl

theorem natSet_contains_insert_ne {s : Src.NatSet} {g x : Nat} (hne : x ≠ g)
    (h : (s.insert g).contains x = true) : s.contains x = true := by
  unfold Src.NatMap.contains at h ⊢
  unfold Src.NatSet.insert at h
  rw [Src.NatMap.get?_insert_ne _ _ hne] at h
  exact h

theorem checkDisps_closed {P : Program} {dc : DecCert} :
    ∀ (fuel : Nat) (todo : List GlobalId) (seen : Src.NatSet),
      checkDisps P dc fuel todo seen = true →
      (∀ g, seen.contains g = true → ∀ gd, P.global? g = some gd → Walk.isDispatchKey gd.key = true →
        ∃ u, checkExpPlain P dc (retFlow dc g) (paramFlows P dc g gd.ps.length).reverse [] gd.body = some u ∧
          ∀ h ∈ u, seen.contains h = true ∨ h ∈ todo) →
      ∃ final : Src.NatSet,
        (∀ g, seen.contains g = true → final.contains g = true) ∧
        (∀ g ∈ todo, final.contains g = true) ∧
        (∀ g, final.contains g = true → ∀ gd, P.global? g = some gd → Walk.isDispatchKey gd.key = true →
          ∃ u, checkExpPlain P dc (retFlow dc g) (paramFlows P dc g gd.ps.length).reverse [] gd.body = some u ∧
            ∀ h ∈ u, final.contains h = true)
  | 0, [], seen, _, hinv => by
    refine ⟨seen, fun _ h => h, fun _ h => False.elim (List.not_mem_nil h), fun g hg gd hgd hdk => ?_⟩
    obtain ⟨u, hu, hall⟩ := hinv g hg gd hgd hdk
    exact ⟨u, hu, fun h hm => (hall h hm).elim id (fun h' => False.elim (List.not_mem_nil h'))⟩
  | 0, _ :: _, _, h, _ => by simp [checkDisps] at h
  | _ + 1, [], seen, _, hinv => by
    refine ⟨seen, fun _ h => h, fun _ h => False.elim (List.not_mem_nil h), fun g hg gd hgd hdk => ?_⟩
    obtain ⟨u, hu, hall⟩ := hinv g hg gd hgd hdk
    exact ⟨u, hu, fun h hm => (hall h hm).elim id (fun h' => False.elim (List.not_mem_nil h'))⟩
  | fuel + 1, g :: todo, seen, h, hinv => by
    unfold checkDisps at h
    split at h
    · next hseen =>
      have hinv' : ∀ x, seen.contains x = true → ∀ gd, P.global? x = some gd →
          Walk.isDispatchKey gd.key = true →
          ∃ u, checkExpPlain P dc (retFlow dc x) (paramFlows P dc x gd.ps.length).reverse [] gd.body = some u ∧
            ∀ y ∈ u, seen.contains y = true ∨ y ∈ todo := by
        intro x hx gd hgd hdk
        obtain ⟨u, hu, hall⟩ := hinv x hx gd hgd hdk
        refine ⟨u, hu, fun y hy => ?_⟩
        rcases hall y hy with hs | hm
        · exact .inl hs
        · rcases List.mem_cons.1 hm with rfl | hm'
          · exact .inl hseen
          · exact .inr hm'
      obtain ⟨final, hf1, hf2, hf3⟩ := checkDisps_closed fuel todo seen h hinv'
      refine ⟨final, hf1, ?_, hf3⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact hf1 x hseen
      · exact hf2 x hx'
    · next hnseen =>
      cases hgd : P.global? g with
      | none =>
        rw [hgd] at h; dsimp only at h
        have hinv' : ∀ x, (seen.insert g).contains x = true → ∀ gd, P.global? x = some gd →
            Walk.isDispatchKey gd.key = true →
            ∃ u, checkExpPlain P dc (retFlow dc x) (paramFlows P dc x gd.ps.length).reverse [] gd.body = some u ∧
              ∀ y ∈ u, (seen.insert g).contains y = true ∨ y ∈ todo := by
          intro x hx gd hgd' hdk
          by_cases hxg : x = g
          · subst hxg; rw [hgd] at hgd'; cases hgd'
          · have hx' : seen.contains x = true := natSet_contains_insert_ne hxg hx
            obtain ⟨u, hu, hall⟩ := hinv x hx' gd hgd' hdk
            refine ⟨u, hu, fun y hy => ?_⟩
            rcases hall y hy with hs | hm
            · exact .inl (natSet_contains_insert hs)
            · rcases List.mem_cons.1 hm with rfl | hm'
              · exact .inl (natSet_contains_insert_self seen y)
              · exact .inr hm'
        obtain ⟨final, hf1, hf2, hf3⟩ := checkDisps_closed fuel todo (seen.insert g) h hinv'
        refine ⟨final, fun x hx => hf1 x (natSet_contains_insert hx), ?_, hf3⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact hf1 x (natSet_contains_insert_self seen x)
        · exact hf2 x hx'
      | some gd =>
        rw [hgd] at h; dsimp only at h
        cases hdk : Walk.isDispatchKey gd.key with
        | false =>
          rw [hdk] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          have hinv' : ∀ x, (seen.insert g).contains x = true → ∀ gd', P.global? x = some gd' →
              Walk.isDispatchKey gd'.key = true →
              ∃ u, checkExpPlain P dc (retFlow dc x) (paramFlows P dc x gd'.ps.length).reverse [] gd'.body = some u ∧
                ∀ y ∈ u, (seen.insert g).contains y = true ∨ y ∈ todo := by
            intro x hx gd' hgd' hdk'
            by_cases hxg : x = g
            · subst hxg; rw [hgd, Option.some.injEq] at hgd'; subst hgd'
              rw [hdk] at hdk'; cases hdk'
            · have hx' : seen.contains x = true := natSet_contains_insert_ne hxg hx
              obtain ⟨u, hu, hall⟩ := hinv x hx' gd' hgd' hdk'
              refine ⟨u, hu, fun y hy => ?_⟩
              rcases hall y hy with hs | hm
              · exact .inl (natSet_contains_insert hs)
              · rcases List.mem_cons.1 hm with rfl | hm'
                · exact .inl (natSet_contains_insert_self seen y)
                · exact .inr hm'
          obtain ⟨final, hf1, hf2, hf3⟩ := checkDisps_closed fuel todo (seen.insert g) h hinv'
          refine ⟨final, fun x hx => hf1 x (natSet_contains_insert hx), ?_, hf3⟩
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx'
          · exact hf1 x (natSet_contains_insert_self seen x)
          · exact hf2 x hx'
        | true =>
          rw [hdk] at h; simp only [↓reduceIte] at h
          cases hck : checkExpPlain P dc (retFlow dc g) (paramFlows P dc g gd.ps.length).reverse [] gd.body with
          | none => rw [hck] at h; dsimp only at h; cases h
          | some more =>
            rw [hck] at h; dsimp only at h
            have hinv' : ∀ x, (seen.insert g).contains x = true → ∀ gd', P.global? x = some gd' →
                Walk.isDispatchKey gd'.key = true →
                ∃ u, checkExpPlain P dc (retFlow dc x) (paramFlows P dc x gd'.ps.length).reverse [] gd'.body = some u ∧
                  ∀ y ∈ u, (seen.insert g).contains y = true ∨ y ∈ more ++ todo := by
              intro x hx gd' hgd' hdk'
              by_cases hxg : x = g
              · subst hxg; rw [hgd, Option.some.injEq] at hgd'; subst hgd'
                exact ⟨more, hck, fun y hy => .inr (List.mem_append_left todo hy)⟩
              · have hx' : seen.contains x = true := natSet_contains_insert_ne hxg hx
                obtain ⟨u, hu, hall⟩ := hinv x hx' gd' hgd' hdk'
                refine ⟨u, hu, fun y hy => ?_⟩
                rcases hall y hy with hs | hm
                · exact .inl (natSet_contains_insert hs)
                · rcases List.mem_cons.1 hm with rfl | hm'
                  · exact .inl (natSet_contains_insert_self seen y)
                  · exact .inr (List.mem_append_right more hm')
            obtain ⟨final, hf1, hf2, hf3⟩ := checkDisps_closed fuel (more ++ todo) (seen.insert g) h hinv'
            refine ⟨final, fun x hx => hf1 x (natSet_contains_insert hx), ?_, hf3⟩
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx'
            · exact hf1 x (natSet_contains_insert_self seen x)
            · exact hf2 x (List.mem_append_right more hx')

theorem rewriteGlobals_spec {P : Program} {dc : DecCert} :
    ∀ (xs : List (GlobalId × GDef)) (used : List GlobalId)
      (gs : List (GlobalId × GDef)) (used' : List GlobalId),
      rewriteGlobals P dc xs used = some (gs, used') →
      gs.map (·.1) = xs.map (·.1) ∧
      (∀ u ∈ used, u ∈ used') ∧
      (∀ g gd, (g, gd) ∈ xs →
        if Walk.isDispatchKey gd.key then
          (g, gd) ∈ gs
        else
          ∃ body' st', (g, { gd with body := body' }) ∈ gs ∧
            checkRewriteExp P dc (retFlow dc g) (paramFlows P dc g gd.ps.length).reverse []
              { joins := (dc.joins.get? g).getD [], siteRets := (dc.siteRets.get? g).getD [], used := [] }
              gd.body = some (body', st') ∧
            ∀ h ∈ st'.used, h ∈ used') ∧
      (∀ g gd', (g, gd') ∈ gs → ∃ gd, (g, gd) ∈ xs ∧ gd'.ps = gd.ps ∧ gd'.key = gd.key)
  | [], used, gs, used', h => by
    simp only [rewriteGlobals, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ hm => hm, fun _ _ hm => False.elim (List.not_mem_nil hm),
      fun _ _ hm => False.elim (List.not_mem_nil hm)⟩
  | (g, gd) :: rest, used, gs, used', h => by
    unfold rewriteGlobals at h
    cases hdk : Walk.isDispatchKey gd.key with
    | true =>
      rw [hdk] at h
      simp only [↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨⟨gs1, u1⟩, hrest, rfl, rfl⟩ := h
      obtain ⟨hkeys, hsub, hmem, hback⟩ := rewriteGlobals_spec rest used gs1 u1 hrest
      refine ⟨by simp [hkeys], hsub, ?_, ?_⟩
      · intro g0 gd0 hm
        rcases List.mem_cons.1 hm with hp | hm'
        · simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
          simp [hdk]
        · have h0 := hmem g0 gd0 hm'
          by_cases hdk0 : Walk.isDispatchKey gd0.key = true
          · simp only [hdk0, ↓reduceIte] at h0 ⊢
            exact List.mem_cons_of_mem _ h0
          · simp only [hdk0, ↓reduceIte] at h0 ⊢
            obtain ⟨b', st', hg', hck, hu⟩ := h0
            exact ⟨b', st', List.mem_cons_of_mem _ hg', hck, hu⟩
      · intro g0 gd0 hm
        rcases List.mem_cons.1 hm with hp | hm'
        · simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
          exact ⟨gd0, List.mem_cons_self, rfl, rfl⟩
        · obtain ⟨gd1, hm1, hps, hk⟩ := hback g0 gd0 hm'
          exact ⟨gd1, List.mem_cons_of_mem _ hm1, hps, hk⟩
    | false =>
      rw [hdk] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hck : checkRewriteExp P dc (retFlow dc g) (paramFlows P dc g gd.ps.length).reverse []
          { joins := (dc.joins.get? g).getD [], siteRets := (dc.siteRets.get? g).getD [], used := [] }
          gd.body with
      | none => rw [hck] at h; dsimp only at h; cases h
      | some p =>
        obtain ⟨body', st'⟩ := p
        rw [hck] at h; dsimp only at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨⟨gs1, u1⟩, hrest, rfl, rfl⟩ := h
        obtain ⟨hkeys, hsub, hmem, hback⟩ := rewriteGlobals_spec rest (st'.used ++ used) gs1 u1 hrest
        refine ⟨by simp [hkeys], fun u hu => hsub u (List.mem_append_right _ hu), ?_, ?_⟩
        · intro g0 gd0 hm
          rcases List.mem_cons.1 hm with hp | hm'
          · simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
            simp only [hdk, Bool.false_eq_true, ↓reduceIte]
            exact ⟨body', st', List.mem_cons_self, hck, fun u hu => hsub u (List.mem_append_left _ hu)⟩
          · have h0 := hmem g0 gd0 hm'
            by_cases hdk0 : Walk.isDispatchKey gd0.key = true
            · simp only [hdk0, ↓reduceIte] at h0 ⊢
              exact List.mem_cons_of_mem _ h0
            · simp only [hdk0, ↓reduceIte] at h0 ⊢
              obtain ⟨b', st2, hg', hck2, hu2⟩ := h0
              exact ⟨b', st2, List.mem_cons_of_mem _ hg', hck2, hu2⟩
        · intro g0 gd0 hm
          rcases List.mem_cons.1 hm with hp | hm'
          · simp only [Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
            exact ⟨gd, List.mem_cons_self, rfl, rfl⟩
          · obtain ⟨gd1, hm1, hps, hk⟩ := hback g0 gd0 hm'
            exact ⟨gd1, List.mem_cons_of_mem _ hm1, hps, hk⟩

/-- Decomposition of `Narrow.run` into unchanged or closed-rewritten program. -/
theorem run_spec {c : Cert} {P : Program} (hw : P.WF) :
    run c P = P ∨
    (FirstOrder P ∧
     (run c P).WF ∧
     ∃ S : GlobalId → Prop, Closed P (run c P) (decode P c) S) := by
  unfold run
  split
  · exact .inl rfl
  · next hcond =>
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hcond
    have hfo : FirstOrder P := by
      cases hf : firstOrder P with
      | true => exact hf
      | false => exact absurd hf hcond.1
    have hkc : knownClosure P.known = false := by
      cases hk : knownClosure P.known with
      | false => rfl
      | true => exact absurd hk hcond.2
    dsimp only
    cases hrw : rewriteGlobals P (decode P c) P.globalList P.roots with
    | none => exact .inl rfl
    | some p =>
      obtain ⟨gs, used⟩ := p
      dsimp only
      split
      · next hcd =>
        right
        let Q : Program := { P with globals := Src.NatMap.ofList gs }
        obtain ⟨hkeys, hused, hmem, hback⟩ := rewriteGlobals_spec P.globalList P.roots gs used hrw
        have hnd : (gs.map (·.1)).Nodup := by
          rw [hkeys]; exact DeadParam.Proof.globalList_keys_nodup P
        have hQget : ∀ g gd', Q.global? g = some gd' ↔ (g, gd') ∈ gs := fun g gd' =>
          ⟨fun h => Convert.Proof.natMap_ofList_mem hnd h,
           fun h => Src.NatMap.get?_ofList hnd h⟩
        have hQwf : Q.WF := by
          refine ⟨?_, ?_⟩
          · intro g gd' hg
            obtain ⟨gd, hgd, -, -⟩ := hback g gd' ((hQget g gd').1 hg)
            exact (DeadParam.Proof.mem_globalList_iff.1 hgd).1
          · intro g hg
            obtain ⟨gd, hgd⟩ := hw.2 g hg
            have hm := hmem g gd (DeadParam.Proof.mem_globalList_iff.2 ⟨hg, hgd⟩)
            split at hm
            · exact ⟨gd, (hQget g gd).2 hm⟩
            · obtain ⟨b', _, hb', -, -⟩ := hm
              exact ⟨{ gd with body := b' }, (hQget g _).2 hb'⟩
        have hQar : ∀ g, Q.arity? g = P.arity? g := by
          intro g
          show Option.map GDef.arity (Q.global? g) = Option.map GDef.arity (P.global? g)
          cases hPg : P.global? g with
          | none =>
            cases hQg : Q.global? g with
            | none => rfl
            | some gd' =>
              obtain ⟨gd, hgd, -, -⟩ := hback g gd' ((hQget g gd').1 hQg)
              have := (DeadParam.Proof.mem_globalList_iff.1 hgd).2
              rw [hPg] at this; cases this
          | some gd =>
            have hgl := DeadParam.Proof.mem_globalList_iff.2 ⟨hw.1 g gd hPg, hPg⟩
            have hm := hmem g gd hgl
            split at hm
            · rw [(hQget g gd).2 hm]
            · obtain ⟨b', _, hb', -, -⟩ := hm
              rw [(hQget g _).2 hb']; rfl
        obtain ⟨final, _, hfTodo, hfClosed⟩ := checkDisps_closed _ used .leaf hcd (fun g hg => by
          simp [Src.NatMap.contains, Src.NatMap.get?] at hg)
        refine ⟨hfo, hQwf, fun g => final.contains g = true, ?_⟩
        refine ⟨rfl, hkc, fun r hr => hfTodo r (hused r hr), hQar, ?_, ?_⟩
        · intro g gd hPg hndisp
          have hgl := DeadParam.Proof.mem_globalList_iff.2 ⟨hw.1 g gd hPg, hPg⟩
          have hm := hmem g gd hgl
          simp only [hndisp, Bool.false_eq_true, ↓reduceIte] at hm
          obtain ⟨body', st', hb', hck, hu⟩ := hm
          exact ⟨{ gd with body := body' }, st', (hQget g _).2 hb', rfl, hck,
            fun h hh => hfTodo h (hu h hh)⟩
        · intro g gd hSg hPg hdisp
          have hgl := DeadParam.Proof.mem_globalList_iff.2 ⟨hw.1 g gd hPg, hPg⟩
          have hm := hmem g gd hgl
          simp only [hdisp, ↓reduceIte] at hm
          exact ⟨(hQget g gd).2 hm, hfClosed g hSg gd hPg hdisp⟩
      · exact .inl rfl

/-- **P9 preserves `WF`**. -/
theorem run_wf {c : Cert} {P : Program} (hw : P.WF) : (run c P).WF := by
  rcases run_spec (c := c) hw with h | ⟨_, hw', _⟩
  · rw [h]; exact hw
  · exact hw'

/-- **P9 preserves `FirstOrder`**. -/
theorem run_firstOrder {c : Cert} {P : Program} (hw : P.WF) (hfo : FirstOrder P) :
    FirstOrder (run c P) := by
  have hfoP : FirstOrder P := hfo
  rcases run_spec (c := c) hw with h | ⟨_, hw', S, hcl⟩
  · rw [h]; exact hfo
  · unfold FirstOrder firstOrder at hfo ⊢
    rw [List.all_eq_true] at hfo ⊢
    have hisFn : (fun g => ((run c P).arity? g).any (· > 0)) =
        (fun g => (P.arity? g).any (· > 0)) := by
      funext g; rw [hcl.arity g]
    rw [hisFn]
    intro ⟨g, gd'⟩ hmem
    obtain ⟨hlt, hQg⟩ := DeadParam.Proof.mem_globalList_iff.1 hmem
    have hltP : g < P.size := by
      have hsz : (run c P).size = P.size := by
        unfold run; split
        · rfl
        · dsimp only; split
          · rfl
          · split <;> rfl
      rw [← hsz]; exact hlt
    obtain ⟨gd, hPg⟩ := hw.2 g hltP
    have hfoG : gd.body.firstOrder (fun h => (P.arity? h).any (· > 0)) = true :=
      hfo (g, gd) (DeadParam.Proof.mem_globalList_iff.2 ⟨hltP, hPg⟩)
    cases hdk : Walk.isDispatchKey gd.key with
    | false =>
      obtain ⟨gd1, st', hQg1, _, hck, _⟩ := hcl.nonDisp g gd hPg hdk
      rw [hQg1, Option.some.injEq] at hQg; subst hQg
      exact checkRewriteExp_firstOrder hfoP hw hck hfoG
    | true =>
      -- Dispatchers are copied verbatim from P to Q
      have hsame : gd' = gd := by
        unfold run at hQg
        split at hQg
        · rw [hPg, Option.some.injEq] at hQg; exact hQg.symm
        · dsimp only at hQg
          cases hrw : rewriteGlobals P (decode P c) P.globalList P.roots with
          | none => rw [hrw] at hQg; rw [hPg, Option.some.injEq] at hQg; exact hQg.symm
          | some p =>
            obtain ⟨gs, used⟩ := p
            rw [hrw] at hQg; dsimp only at hQg
            split at hQg
            · obtain ⟨hkeys, _, hmem', _⟩ := rewriteGlobals_spec P.globalList P.roots gs used hrw
              have hnd : (gs.map (·.1)).Nodup := by
                rw [hkeys]; exact DeadParam.Proof.globalList_keys_nodup P
              have hm := hmem' g gd (DeadParam.Proof.mem_globalList_iff.2 ⟨hltP, hPg⟩)
              simp only [hdk, ↓reduceIte] at hm
              have hget := Src.NatMap.get?_ofList hnd hm
              show gd' = gd
              change (Src.NatMap.ofList gs).get? g = some gd' at hQg
              rw [hget, Option.some.injEq] at hQg
              exact hQg.symm
            · rw [hPg, Option.some.injEq] at hQg; exact hQg.symm
      subst hsame; exact hfoG

/-! ## Simulation at clock bound `n` -/

/-- Calls and CAF reads of every active (non-dispatcher or in `S`) global
simulate up to clock bound `n`, preserving `ValOk dc` and `retFlow dc g`. -/
def CallOk (P Q : Program) (dc : DecCert) (S : GlobalId → Prop) (n : Nat) : Prop :=
  ∀ g gd, P.global? g = some gd → (Walk.isDispatchKey gd.key = false ∨ S g) →
    (gd.ps = [] →
      ∀ ρ, SimUpTo (ValRel dc (retFlow dc g)) n
        (fun k => evalBind P k ρ (.glob g))
        (fun k => evalBind Q k ρ (.glob g))) ∧
    (∀ vs, vs.length = gd.ps.length → EnvOk dc (paramFlows P dc g gd.ps.length) vs →
      SimUpTo (ValRel dc (retFlow dc g)) n
        (fun k => callVal P k gd vs)
        (fun k => (Result.ofOption (Q.global? g)).bind (callVal Q k · vs)))

theorem CallOk.mono {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n m : Nat}
    (h : CallOk P Q dc S n) (hmn : m ≤ n) : CallOk P Q dc S m := by
  intro g gd hPg hact
  obtain ⟨h1, h2⟩ := h g gd hPg hact
  exact ⟨fun hps ρ => (h1 hps ρ).mono_n hmn, fun vs hl hv => (h2 vs hl hv).mono_n hmn⟩

theorem CallOk.zero {P Q : Program} {dc : DecCert} {S : GlobalId → Prop}
    (hcl : Closed P Q dc S) : CallOk P Q dc S 0 := by
  intro g gd hPg hact
  have hQgd : ∃ gd', Q.global? g = some gd' ∧ gd'.ps.length = gd.ps.length := by
    cases hdk : Walk.isDispatchKey gd.key with
    | false =>
      obtain ⟨gd', _, hQg, hps, _, _⟩ := hcl.nonDisp g gd hPg hdk
      exact ⟨gd', hQg, by rw [hps]⟩
    | true =>
      have hSg : S g := hact.elim (fun hf => by rw [hdk] at hf; cases hf) id
      obtain ⟨hQg, _⟩ := hcl.disp g gd hSg hPg hdk
      exact ⟨gd, hQg, rfl⟩
  obtain ⟨gd', hQg, hpslen⟩ := hQgd
  refine ⟨fun hps ρ => ?_, fun vs hl _ => ?_⟩
  · have hps' : gd'.ps = [] := List.eq_nil_of_length_eq_zero (by rw [hpslen, hps]; rfl)
    refine ⟨fun k hk hne => ?_, fun k hk _ => ?_⟩
    · have hk0 : k = 0 := by omega
      subst hk0
      rw [evalBind_glob, hPg] at hne
      simp [Result.ofOption, globVal, hps] at hne
    · have hk0 : k = 0 := by omega
      subst hk0
      rw [evalBind_glob, hQg]
      exact .inl (by simp [Result.ofOption, globVal, hps'])
  · refine ⟨fun k hk hne => ?_, fun k hk _ => ?_⟩
    · have hk0 : k = 0 := by omega
      subst hk0
      simp [callVal, hl] at hne
    · have hk0 : k = 0 := by omega
      subst hk0
      rw [hQg]
      exact .inl (by simp [Result.ofOption, callVal, hpslen, hl])

/-- Plain join relation: jumping to both join closures with `ValOk` arguments
matching `ps` simulates at every bound up to `n`. -/
def PlainJoinR (P Q : Program) (dc : DecCert) (rflow : KAbs) (n : Nat)
    (ps : List KAbs) (jc₁ jc₂ : JClo) : Prop :=
  ∀ m ≤ n, ∀ vs, vs.length = ps.length → EnvOk dc ps vs →
    SimUpTo (ValRel dc rflow) m (fun k => jumpTo P k jc₁ vs) (fun k => jumpTo Q k jc₂ vs)

theorem PlainJoinR.mono {P Q : Program} {dc : DecCert} {rflow : KAbs} {n m : Nat}
    {ps : List KAbs} {jc₁ jc₂ : JClo}
    (h : PlainJoinR P Q dc rflow n ps jc₁ jc₂) (hmn : m ≤ n) :
    PlainJoinR P Q dc rflow m ps jc₁ jc₂ :=
  fun i hi => h i (Nat.le_trans hi hmn)

def PlainJEnv (P Q : Program) (dc : DecCert) (rflow : KAbs) (n : Nat)
    (jenv : List (List KAbs)) (J₁ J₂ : List JClo) : Prop :=
  J₁.length = jenv.length ∧ J₂.length = jenv.length ∧
  ∀ (j : Nat) ps jc₁ jc₂, jenv[j]? = some ps → J₁[j]? = some jc₁ → J₂[j]? = some jc₂ →
    PlainJoinR P Q dc rflow n ps jc₁ jc₂

theorem PlainJEnv.nil (P Q : Program) (dc : DecCert) (rflow : KAbs) (n : Nat) :
    PlainJEnv P Q dc rflow n [] [] [] :=
  ⟨rfl, rfl, fun _ _ _ _ h => by simp at h⟩

theorem PlainJEnv.mono {P Q : Program} {dc : DecCert} {rflow : KAbs} {n m : Nat}
    {jenv : List (List KAbs)} {J₁ J₂ : List JClo}
    (h : PlainJEnv P Q dc rflow n jenv J₁ J₂) (hmn : m ≤ n) :
    PlainJEnv P Q dc rflow m jenv J₁ J₂ :=
  ⟨h.1, h.2.1, fun j ps jc₁ jc₂ hj h1 h2 => (h.2.2 j ps jc₁ jc₂ hj h1 h2).mono hmn⟩

theorem PlainJEnv.cons {P Q : Program} {dc : DecCert} {rflow : KAbs} {n : Nat}
    {ps : List KAbs} {jc₁ jc₂ : JClo} {jenv : List (List KAbs)} {J₁ J₂ : List JClo}
    (hr : PlainJoinR P Q dc rflow n ps jc₁ jc₂)
    (h : PlainJEnv P Q dc rflow n jenv J₁ J₂) :
    PlainJEnv P Q dc rflow n (ps :: jenv) (jc₁ :: J₁) (jc₂ :: J₂) := by
  refine ⟨by simp [h.1], by simp [h.2.1], ?_⟩
  intro j ps' jc₁' jc₂' hj h1 h2
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj h1 h2
    subst hj; subst h1; subst h2; exact hr
  | succ j =>
    simp only [List.getElem?_cons_succ] at hj h1 h2
    exact h.2.2 j ps' jc₁' jc₂' hj h1 h2

/-! ### `checkBindPlain` simulation -/

theorem checkBindPlain_sim {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n : Nat}
    (hcl : Closed P Q dc S) (hcall : CallOk P Q dc S n)
    {env : List KAbs} {ρ : List Val} (henv : EnvOk dc env ρ)
    {b : Bind} {bf : KAbs} {u : List GlobalId}
    (hck : checkBindPlain P dc env b = some (bf, u)) (hu : ∀ h ∈ u, S h) :
    SimUpTo (ValRel dc bf) n (fun k => evalBind P k ρ b) (fun k => evalBind Q k ρ b) := by
  cases b with
  | atom a =>
    simp only [checkBindPlain, Option.some.injEq, Prod.mk.injEq] at hck
    obtain ⟨rfl, rfl⟩ := hck
    cases ha : a.eval ρ with
    | none =>
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [evalBind_atom, ha]; rfl
    | some v =>
      obtain ⟨hv, hc⟩ := henv.atom ha
      refine (SimUpTo.ok ⟨rfl, hv, hc⟩).congr (fun k => ?_) (fun k => ?_)
      · rw [evalBind_atom, ha]; rfl
      · rw [evalBind_atom, ha]; rfl
  | con c as =>
    simp only [checkBindPlain] at hck
    split at hck
    · next hsub =>
      cases hvs : evalAtoms ρ as with
      | none =>
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [evalBind_con, hvs]; rfl
      | some vs =>
        have hlen : vs.length = as.length := evalAtoms_length ρ hvs
        have hok := (henv.atoms hvs).sub (by rw [atomsFlow_length, hlen]) hsub
        have hvcon : ValOk dc (.con c vs) := .con c vs
          (fun i v hi => (hok i v hi).1)
          (fun i v hi => by
            have hlt : i < vs.length := (List.getElem?_eq_some_iff.1 hi).1
            have := (hok i v hi).2
            rw [fieldFlows_get dc c as.length i (by omega), Option.getD_some] at this
            exact this)
        cases c with
        | clo f j =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hck
          obtain ⟨rfl, rfl⟩ := hck
          refine (SimUpTo.ok ⟨rfl, hvcon, List.mem_cons_self⟩).congr (fun k => ?_) (fun k => ?_)
          · rw [evalBind_con, hvs]; rfl
          · rw [evalBind_con, hvs]; rfl
        | src s =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hck
          obtain ⟨rfl, rfl⟩ := hck
          refine (SimUpTo.ok ⟨rfl, hvcon, trivial⟩).congr (fun k => ?_) (fun k => ?_)
          · rw [evalBind_con, hvs]; rfl
          · rw [evalBind_con, hvs]; rfl
    · cases hck
  | proj c i x =>
    simp only [checkBindPlain, Option.some.injEq, Prod.mk.injEq] at hck
    obtain ⟨rfl, rfl⟩ := hck
    cases hx : x.eval ρ with
    | none =>
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [evalBind_proj, hx]; rfl
    | some v =>
      obtain ⟨hv, _⟩ := henv.atom hx
      cases hv with
      | con c' fs hfsV hfsC =>
        by_cases hceq : c' = c
        · subst hceq
          cases hfi : fs[i]? with
          | none =>
            refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
            rw [evalBind_proj, hx]; simp [Result.ofOption, projVal, hfi]
          | some w =>
            refine (SimUpTo.ok ⟨rfl, hfsV i w hfi, hfsC i w hfi⟩).congr (fun k => ?_) (fun k => ?_)
            · rw [evalBind_proj, hx]; simp [Result.ofOption, projVal, hfi]
            · rw [evalBind_proj, hx]; simp [Result.ofOption, projVal, hfi]
        · refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
          rw [evalBind_proj, hx]; simp [Result.ofOption, projVal, hceq]
      | lit _ =>
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [evalBind_proj, hx]; rfl
      | box =>
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [evalBind_proj, hx]; rfl
  | prim p as =>
    simp only [checkBindPlain, Option.some.injEq, Prod.mk.injEq] at hck
    obtain ⟨rfl, rfl⟩ := hck
    cases hvs : evalAtoms ρ as with
    | none =>
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [evalBind_prim, hvs]; rfl
    | some vs =>
      cases hpr : primResult P.known p vs with
      | ok v =>
        obtain ⟨hv, hc⟩ := primResult_ok hcl.knownOk hpr
        refine (SimUpTo.ok ⟨rfl, hv, hc⟩).congr (fun k => ?_) (fun k => ?_)
        · rw [evalBind_prim, hvs]; simp [Result.ofOption, hpr]
        · rw [evalBind_prim, hvs, hcl.known]; simp [Result.ofOption, hpr]
      | stuck =>
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [evalBind_prim, hvs]; simp [Result.ofOption, hpr]
      | trap =>
        refine SimUpTo.trap.congr (fun k => ?_) (fun k => ?_)
        · rw [evalBind_prim, hvs]; simp [Result.ofOption, hpr]
        · rw [evalBind_prim, hvs, hcl.known]; simp [Result.ofOption, hpr]
      | timeout =>
        unfold primResult at hpr
        cases hna : natArgs vs with
        | none => rw [hna] at hpr; cases hpr
        | some ns =>
          rw [hna] at hpr; dsimp only at hpr
          cases hp : p.sem ns with
          | none => rw [hp] at hpr; cases hpr
          | some r =>
            rw [hp] at hpr
            cases r with
            | nat _ => cases hpr
            | bool b => cases b <;> (simp only at hpr; cases hbt : P.known.boolTrue <;> cases hbf : P.known.boolFalse <;> simp [hbt, hbf] at hpr)
      | resource _ =>
        unfold primResult at hpr
        cases hna : natArgs vs with
        | none => rw [hna] at hpr; cases hpr
        | some ns =>
          rw [hna] at hpr; dsimp only at hpr
          cases hp : p.sem ns with
          | none => rw [hp] at hpr; cases hpr
          | some r =>
            rw [hp] at hpr
            cases r with
            | nat _ => cases hpr
            | bool b => cases b <;> (simp only at hpr; cases hbt : P.known.boolTrue <;> cases hbf : P.known.boolFalse <;> simp [hbt, hbf] at hpr)
  | glob g =>
    simp only [checkBindPlain] at hck
    cases hPg : P.global? g with
    | none =>
      rw [hPg] at hck
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [evalBind_glob, hPg]; rfl
    | some gd =>
      rw [hPg] at hck; dsimp only at hck
      split at hck
      · next hemp =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hck
        obtain ⟨rfl, rfl⟩ := hck
        have hps : gd.ps = [] := by cases h0 : gd.ps with | nil => rfl | cons _ _ => simp [h0] at hemp
        exact (hcall g gd hPg (.inr (hu g List.mem_cons_self))).1 hps ρ
      · cases hck
  | call g as =>
    simp only [checkBindPlain] at hck
    cases hPg : P.global? g with
    | none =>
      rw [hPg] at hck
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [evalBind_call, hPg]; rfl
    | some gd =>
      rw [hPg] at hck; dsimp only at hck
      split at hck
      · next hlen =>
        have hlen' : as.length = gd.ps.length := beq_iff_eq.1 hlen
        split at hck
        · next hsub =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hck
          obtain ⟨rfl, rfl⟩ := hck
          cases hvs : evalAtoms ρ as with
          | none =>
            refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
            rw [evalBind_call, hPg, hvs]; rfl
          | some vs =>
            have hvlen : vs.length = gd.ps.length := by rw [evalAtoms_length ρ hvs, hlen']
            have hok := (henv.atoms hvs).sub (by rw [atomsFlow_length, evalAtoms_length ρ hvs]) hsub
            refine ((hcall g gd hPg (.inr (hu g List.mem_cons_self))).2 vs hvlen hok).congr
              (fun k => ?_) (fun k => ?_)
            · rw [evalBind_call, hPg, hvs]; rfl
            · rw [evalBind_call, hvs]
              cases Q.global? g <;> rfl
        · cases hck
      · next hne =>
        have hne' : as.length ≠ gd.ps.length := fun he => hne (beq_iff_eq.2 he)
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [evalBind_call, hPg]
        cases hvs : evalAtoms ρ as with
        | none => rfl
        | some vs =>
          have : vs.length ≠ gd.ps.length := by rw [evalAtoms_length ρ hvs]; exact hne'
          simp [Result.ofOption, callVal, this]
  | app _ _ => simp [checkBindPlain] at hck
  | fn _ _ => simp [checkBindPlain] at hck

/-! ### `checkExpPlain` simulation -/

mutual

theorem checkExpPlain_sim {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n : Nat}
    (hcl : Closed P Q dc S) (hcall : CallOk P Q dc S n) :
    ∀ {m : Nat}, m ≤ n →
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)}
      {ρ : List Val} {J₁ J₂ : List JClo} {e : Exp} {u : List GlobalId},
    EnvOk dc env ρ → PlainJEnv P Q dc rflow m jenv J₁ J₂ →
    checkExpPlain P dc rflow env jenv e = some u → (∀ h ∈ u, S h) →
    SimUpTo (ValRel dc rflow) m (fun k => eval P k ρ J₁ e) (fun k => eval Q k ρ J₂ e)
  | m, hm, rflow, env, jenv, ρ, J₁, J₂, .bind c b e, u, henv, hJ, hck, hu => by
    simp only [checkExpPlain, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hck
    obtain ⟨⟨bf, u1⟩, hb, u2, he, rfl⟩ := hck
    have hbs := checkBindPlain_sim hcl (hcall.mono hm) henv hb (fun h hh => hu h (List.mem_append_left _ hh))
    refine (SimUpTo.bind (evalBind_mono Q ρ b) (fun w => eval_mono Q (w :: ρ) J₂ e) hbs
      fun v w hvw => ?_).congr (fun k => eval_bind P k ρ J₁ c b e) (fun k => eval_bind Q k ρ J₂ c b e)
    obtain ⟨rfl, hv, hcv⟩ := hvw
    exact checkExpPlain_sim hcl hcall hm (henv.cons hv hcv) hJ he
      (fun h hh => hu h (List.mem_append_right _ hh))
  | m, hm, rflow, env, jenv, ρ, J₁, J₂, .join ar r b e, u, henv, hJ, hck, hu => by
    simp only [checkExpPlain, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hck
    obtain ⟨u1, hb, u2, he, rfl⟩ := hck
    let ps : List KAbs := List.replicate ar none
    have hJR : PlainJoinR P Q dc rflow m ps (.mk ρ J₁ ar b r) (.mk ρ J₂ ar b r) := by
      intro m1
      induction m1 using Nat.strongRecOn with
      | _ m1 ih =>
      intro hm1 vs hvlen hvs
      have har : vs.length = ar := by simpa [ps] using hvlen
      have hstep : ∀ m', m' + 1 ≤ m1 →
          SimUpTo (ValRel dc rflow) m'
            (fun k => eval P k (vs.reverse ++ ρ) (if r then .mk ρ J₁ ar b r :: J₁ else J₁) b)
            (fun k => eval Q k (vs.reverse ++ ρ) (if r then .mk ρ J₂ ar b r :: J₂ else J₂) b) := by
        intro m' hm'
        have henvb : EnvOk dc (ps.reverse ++ env) (vs.reverse ++ ρ) :=
          EnvOk.append (by simp [ps, har]) (hvs.reverse (by rw [hvlen])) henv
        have hJb : PlainJEnv P Q dc rflow m' (if r then ps :: jenv else jenv)
            (if r then .mk ρ J₁ ar b r :: J₁ else J₁)
            (if r then .mk ρ J₂ ar b r :: J₂ else J₂) := by
          cases r with
          | false => exact hJ.mono (by omega)
          | true =>
            simp only [↓reduceIte]
            exact (hJ.mono (by omega)).cons (fun i hi => ih i (by omega) (by omega))
        exact checkExpPlain_sim hcl hcall (by omega) henvb hJb hb
          (fun h hh => hu h (List.mem_append_left _ hh))
      exact (SimUpTo.later hstep).congr
        (fun k => by simp [jumpTo, har]) (fun k => by simp [jumpTo, har])
    refine (checkExpPlain_sim hcl hcall hm henv (hJ.cons hJR) he
      (fun h hh => hu h (List.mem_append_right _ hh))).congr
      (fun k => eval_join' P k ρ J₁ ar r b e) (fun k => eval_join' Q k ρ J₂ ar r b e)
  | m, hm, rflow, env, jenv, ρ, J₁, J₂, .jump j as, u, henv, hJ, hck, _ => by
    simp only [checkExpPlain] at hck
    cases hj : jenv[j]? with
    | none =>
      have hlt : ¬ j < J₁.length := by
        rw [hJ.1]; intro hlt; exact absurd (List.getElem?_eq_none_iff.1 hj) (by omega)
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [eval_jump, List.getElem?_eq_none (by omega)]; rfl
    | some ps =>
      rw [hj] at hck; dsimp only at hck
      split at hck
      · next hcond =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hlen, hsub⟩ := hcond
        have hjlt : j < jenv.length := (List.getElem?_eq_some_iff.1 hj).1
        have hjlt1 : j < J₁.length := hJ.1 ▸ hjlt
        have hjlt2 : j < J₂.length := hJ.2.1 ▸ hjlt
        obtain ⟨jc₁, hj1⟩ : ∃ jc₁, J₁[j]? = some jc₁ := ⟨J₁[j]'hjlt1, List.getElem?_eq_getElem hjlt1⟩
        obtain ⟨jc₂, hj2⟩ : ∃ jc₂, J₂[j]? = some jc₂ := ⟨J₂[j]'hjlt2, List.getElem?_eq_getElem hjlt2⟩
        cases hvs : evalAtoms ρ as with
        | none =>
          refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
          rw [eval_jump, hj1, hvs]; rfl
        | some vs =>
          have hvlen : vs.length = ps.length := by rw [evalAtoms_length ρ hvs, hlen]
          have hok := (henv.atoms hvs).sub (by rw [atomsFlow_length, evalAtoms_length ρ hvs]) hsub
          refine (hJ.2.2 j ps jc₁ jc₂ hj hj1 hj2 m (Nat.le_refl m) vs hvlen hok).congr
            (fun k => ?_) (fun k => ?_)
          · rw [eval_jump, hj1, hvs]; rfl
          · rw [eval_jump, hj2, hvs]; rfl
      · cases hck
  | m, hm, rflow, env, jenv, ρ, J₁, J₂, .case x alts dflt, u, henv, hJ, hck, hu => by
    simp only [checkExpPlain, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hck
    obtain ⟨u1, ha, u2, hd, rfl⟩ := hck
    cases hx : x.eval ρ with
    | none =>
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [eval_case, hx]; rfl
    | some v =>
      obtain ⟨hv, _⟩ := henv.atom hx
      cases hac : v.asCtor P.known with
      | none =>
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [eval_case, hx]; simp [Result.ofOption, hac]
      | some p =>
        obtain ⟨c, fs⟩ := p
        obtain ⟨hfsOk, _⟩ := asCtor_ok hcl.knownOk hv hac
        have hdSim := checkOptPlain_sim hcl hcall hm henv hJ hd
          (fun h hh => hu h (List.mem_append_right _ hh))
        refine (checkAltsPlain_sim hcl hcall hm henv hJ hfsOk ha
          (fun h hh => hu h (List.mem_append_left _ hh)) hdSim).congr
          (fun k => ?_) (fun k => ?_)
        · rw [eval_case, hx]; simp [Result.ofOption, hac]
        · rw [eval_case, hx, hcl.known]; simp [Result.ofOption, hac]
  | m, _, rflow, env, _, ρ, J₁, J₂, .ret a, _, henv, _, hck, _ => by
    simp only [checkExpPlain] at hck
    split at hck
    · next hsub =>
      cases ha : a.eval ρ with
      | none =>
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [eval_ret', ha]; rfl
      | some v =>
        obtain ⟨hv, hc⟩ := henv.atom ha
        refine (SimUpTo.ok ⟨rfl, hv, kabsSub_sound hsub hc⟩).congr (fun k => ?_) (fun k => ?_)
        · rw [eval_ret', ha]; rfl
        · rw [eval_ret', ha]; rfl
    · cases hck
  | m, hm, rflow, env, jenv, ρ, J₁, J₂, .tick e, u, henv, hJ, hck, hu => by
    simp only [checkExpPlain] at hck
    refine (SimUpTo.later fun m' hm' =>
      checkExpPlain_sim hcl hcall (by omega) henv (hJ.mono (by omega)) hck hu).congr
      (fun k => eval_tick P k ρ J₁ e) (fun k => eval_tick Q k ρ J₂ e)
  | _, _, _, _, _, ρ, J₁, J₂, .trap, _, _, _, _, _ =>
    SimUpTo.trap.congr (fun k => eval_trap' P k ρ J₁) (fun k => eval_trap' Q k ρ J₂)

theorem checkOptPlain_sim {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n : Nat}
    (hcl : Closed P Q dc S) (hcall : CallOk P Q dc S n) :
    ∀ {m : Nat}, m ≤ n →
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)}
      {ρ : List Val} {J₁ J₂ : List JClo} {dflt : Option Exp} {u : List GlobalId},
    EnvOk dc env ρ → PlainJEnv P Q dc rflow m jenv J₁ J₂ →
    checkOptPlain P dc rflow env jenv dflt = some u → (∀ h ∈ u, S h) →
    SimUpTo (ValRel dc rflow) m
      (fun k => match dflt with | some e => eval P k ρ J₁ e | none => .stuck)
      (fun k => match dflt with | some e => eval Q k ρ J₂ e | none => .stuck)
  | _, _, _, _, _, _, _, _, none, _, _, _, _, _ => SimUpTo.stuck _
  | m, hm, _, _, _, _, _, _, some e, _, henv, hJ, hd, hu =>
    checkExpPlain_sim hcl hcall hm henv hJ hd hu

theorem checkAltsPlain_sim {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n : Nat}
    (hcl : Closed P Q dc S) (hcall : CallOk P Q dc S n) :
    ∀ {m : Nat}, m ≤ n →
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)}
      {ρ : List Val} {J₁ J₂ : List JClo} {c : Key.CtorKey} {fs : List Val}
      {alts : List Alt} {dflt : Option Exp} {u1 : List GlobalId},
    EnvOk dc env ρ → PlainJEnv P Q dc rflow m jenv J₁ J₂ →
    EnvOk dc (fieldFlows dc c fs.length) fs →
    checkAltsPlain P dc rflow env jenv alts = some u1 →
    (∀ h ∈ u1, S h) →
    SimUpTo (ValRel dc rflow) m
      (fun k => match dflt with | some e => eval P k ρ J₁ e | none => .stuck)
      (fun k => match dflt with | some e => eval Q k ρ J₂ e | none => .stuck) →
    SimUpTo (ValRel dc rflow) m
      (fun k => evalAlts P k ρ J₁ c fs alts dflt)
      (fun k => evalAlts Q k ρ J₂ c fs alts dflt)
  | _, _, _, _, _, ρ, J₁, J₂, c, fs, [], dflt, _, _, _, _, _, _, hdSim =>
    hdSim.congr (fun k => evalAlts_nil P k ρ J₁ c fs dflt) (fun k => evalAlts_nil Q k ρ J₂ c fs dflt)
  | m, hm, rflow, env, jenv, ρ, J₁, J₂, c, fs, .mk key nf body :: rest, dflt, u1,
      henv, hJ, hfsOk, ha, hu1, hdSim => by
    simp only [checkAltsPlain, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨ua, hba, urest, hrest, rfl⟩ := ha
    by_cases hmatch : key = c ∧ nf = fs.length
    · obtain ⟨rfl, rfl⟩ := hmatch
      have henvb : EnvOk dc ((fieldFlows dc key fs.length).reverse ++ env) (fs.reverse ++ ρ) :=
        EnvOk.append (by simp [fieldFlows_length]) (hfsOk.reverse (fieldFlows_length dc key fs.length)) henv
      refine (checkExpPlain_sim hcl hcall hm henvb hJ hba
        (fun h hh => hu1 h (List.mem_append_left _ hh))).congr (fun k => ?_) (fun k => ?_)
      · rw [evalAlts_cons, if_pos ⟨rfl, rfl⟩]
      · rw [evalAlts_cons, if_pos ⟨rfl, rfl⟩]
    · refine (checkAltsPlain_sim hcl hcall hm henv hJ hfsOk hrest
        (fun h hh => hu1 h (List.mem_append_right _ hh)) hdSim).congr (fun k => ?_) (fun k => ?_)
      · rw [evalAlts_cons, if_neg hmatch]
      · rw [evalAlts_cons, if_neg hmatch]

end

/-! ### `instExp` simulation (dispatcher arm instantiated under a continuation) -/

/-- Target continuation for `instExp`: either direct return (`contJump = false`)
or jumping to `jc_cont` at `J₂[jdepth]` (`contJump = true`). -/
def InstTarget (Q : Program) (contJump : Bool) (jc_cont : JClo) (v : Val) (k : Nat) : Result Val :=
  if contJump then jumpTo Q k jc_cont [v] else .ok v

theorem InstTarget_mono (Q : Program) (contJump : Bool) (jc_cont : JClo) (v : Val) :
    ClockMono (InstTarget Q contJump jc_cont v) := by
  cases contJump with
  | false => exact ClockMono.const (.ok v)
  | true =>
    unfold InstTarget
    simp only [↓reduceIte]
    cases jc_cont with
    | mk ρ' J' ar b r =>
      unfold jumpTo
      by_cases hl : [v].length = ar
      · simp only [hl, ↓reduceIte]; exact ClockMono.later (eval_mono Q _ _ b)
      · simp only [hl, ↓reduceIte]; exact ClockMono.const .stuck

/-- Local join relation inside an instantiated dispatcher arm: jumping to both
join closures, followed by `SK` on the source side, simulates jumping on the
target side (where returns jump to `T`). -/
def InstJoinR (P Q : Program) (dc : DecCert) (rflow siteRet : KAbs) (n : Nat)
    (T : Val → Nat → Result Val) (ps : List KAbs) (jc₁ jc₂ : JClo) : Prop :=
  ∀ m ≤ n, ∀ SK : Val → Nat → Result Val,
    (∀ x, ValOk dc x → ClosOk siteRet x → SimUpTo (ValRel dc rflow) m (SK x) (T x)) →
    ∀ vs, vs.length = ps.length → EnvOk dc ps vs →
      SimUpTo (ValRel dc rflow) m
        (fun k => (jumpTo P k jc₁ vs).bind (SK · k))
        (fun k => jumpTo Q k jc₂ vs)

theorem InstJoinR.mono {P Q : Program} {dc : DecCert} {rflow siteRet : KAbs} {n m : Nat}
    {T : Val → Nat → Result Val} {ps : List KAbs} {jc₁ jc₂ : JClo}
    (h : InstJoinR P Q dc rflow siteRet n T ps jc₁ jc₂) (hmn : m ≤ n) :
    InstJoinR P Q dc rflow siteRet m T ps jc₁ jc₂ :=
  fun i hi => h i (Nat.le_trans hi hmn)

def InstJEnv (P Q : Program) (dc : DecCert) (rflow siteRet : KAbs) (n : Nat)
    (contJump : Bool) (jc_cont : JClo) (jenv : List (List KAbs)) (J₁ J₂ : List JClo) : Prop :=
  J₁.length = jenv.length ∧
  (contJump = true → J₂[jenv.length]? = some jc_cont) ∧
  ∀ (j : Nat) ps jc₁, jenv[j]? = some ps → J₁[j]? = some jc₁ →
    ∃ jc₂, J₂[j]? = some jc₂ ∧
      InstJoinR P Q dc rflow siteRet n (InstTarget Q contJump jc_cont) ps jc₁ jc₂

theorem InstJEnv.nil (P Q : Program) (dc : DecCert) (rflow siteRet : KAbs) (n : Nat)
    (contJump : Bool) (jc_cont : JClo) (J_outer : List JClo)
    (hcont : contJump = true → J_outer[0]? = some jc_cont) :
    InstJEnv P Q dc rflow siteRet n contJump jc_cont [] [] J_outer :=
  ⟨rfl, hcont, fun _ _ _ h => by simp at h⟩

theorem InstJEnv.mono {P Q : Program} {dc : DecCert} {rflow siteRet : KAbs} {n m : Nat}
    {contJump : Bool} {jc_cont : JClo} {jenv : List (List KAbs)} {J₁ J₂ : List JClo}
    (h : InstJEnv P Q dc rflow siteRet n contJump jc_cont jenv J₁ J₂) (hmn : m ≤ n) :
    InstJEnv P Q dc rflow siteRet m contJump jc_cont jenv J₁ J₂ :=
  ⟨h.1, h.2.1, fun j ps jc₁ hj h1 =>
    let ⟨jc₂, h2, hr⟩ := h.2.2 j ps jc₁ hj h1
    ⟨jc₂, h2, hr.mono hmn⟩⟩

theorem InstJEnv.cons {P Q : Program} {dc : DecCert} {rflow siteRet : KAbs} {n : Nat}
    {contJump : Bool} {jc_cont : JClo} {ps : List KAbs} {jc₁ jc₂ : JClo}
    {jenv : List (List KAbs)} {J₁ J₂ : List JClo}
    (hr : InstJoinR P Q dc rflow siteRet n (InstTarget Q contJump jc_cont) ps jc₁ jc₂)
    (h : InstJEnv P Q dc rflow siteRet n contJump jc_cont jenv J₁ J₂) :
    InstJEnv P Q dc rflow siteRet n contJump jc_cont (ps :: jenv) (jc₁ :: J₁) (jc₂ :: J₂) := by
  refine ⟨by simp [h.1], fun hc => by simpa using h.2.1 hc, ?_⟩
  intro j ps' jc₁' hj h1
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj h1
    subst hj; subst h1
    exact ⟨jc₂, rfl, hr⟩
  | succ j =>
    simp only [List.getElem?_cons_succ] at hj h1
    obtain ⟨jc₂', h2, hr'⟩ := h.2.2 j ps' jc₁' hj h1
    exact ⟨jc₂', h2, hr'⟩

theorem instBind_sim {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n : Nat}
    (hcl : Closed P Q dc S) (hcall : CallOk P Q dc S n)
    {args : List Atom} {ρ_site allVs pre : List Val} {nf depth : Nat}
    (hargs : evalAtoms ρ_site args = some allVs) (hpre : pre.length = depth + nf)
    {env : List KAbs} (henv : EnvOk dc env (pre ++ allVs.reverse))
    {b b' : Bind} {bf : KAbs} {u : List GlobalId}
    (hck : checkBindPlain P dc env b = some (bf, u)) (hu : ∀ h ∈ u, S h)
    (hi : instBind args nf depth b = some b') :
    SimUpTo (ValRel dc bf) n
      (fun k => evalBind P k (pre ++ allVs.reverse) b)
      (fun k => evalBind Q k (pre ++ ρ_site) b') := by
  have heq : ∀ k, evalBind Q k (pre ++ ρ_site) b' = evalBind Q k (pre ++ allVs.reverse) b := by
    intro k
    cases b with
    | atom a =>
      obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.1 hi
      rw [evalBind_atom, evalBind_atom, instAtom_eval hargs hpre ha']
    | con c as =>
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some_iff.1 hi
      rw [evalBind_con, evalBind_con, instAtoms_eval hargs hpre has']
    | proj c i x =>
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 hi
      rw [evalBind_proj, evalBind_proj, instAtom_eval hargs hpre hx']
    | prim p as =>
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some_iff.1 hi
      rw [evalBind_prim, evalBind_prim, instAtoms_eval hargs hpre has']
    | glob g =>
      simp only [instBind, Option.some.injEq] at hi; subst hi
      rw [evalBind_glob, evalBind_glob]
    | call g as =>
      obtain ⟨as', has', rfl⟩ := Option.map_eq_some_iff.1 hi
      rw [evalBind_call, evalBind_call, instAtoms_eval hargs hpre has']
    | app _ _ => cases hi
    | fn _ _ => cases hi
  exact (checkBindPlain_sim hcl hcall henv hck hu).congr (fun _ => rfl) heq

theorem result_bind_assoc {α β γ : Type} (r : Result α) (f : α → Result β) (g : β → Result γ) :
    (r.bind f).bind g = r.bind fun x => (f x).bind g := by
  cases r <;> rfl

mutual

theorem instExp_sim {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n : Nat}
    (hcl : Closed P Q dc S) (hcall : CallOk P Q dc S n)
    {args : List Atom} {ρ_site allVs : List Val} {nf : Nat}
    (hargs : evalAtoms ρ_site args = some allVs)
    {contJump : Bool} {jc_cont : JClo} {rflow siteRet : KAbs} :
    ∀ (e : Exp) {m : Nat}, m ≤ n →
    ∀ {depth : Nat} {pre : List Val} {env : List KAbs} {jenv : List (List KAbs)}
      {J₁ J₂ : List JClo} {e' : Exp} {u : List GlobalId} {SK : Val → Nat → Result Val},
    pre.length = depth + nf →
    EnvOk dc env (pre ++ allVs.reverse) →
    InstJEnv P Q dc rflow siteRet m contJump jc_cont jenv J₁ J₂ →
    (∀ x, ValOk dc x → ClosOk siteRet x →
      SimUpTo (ValRel dc rflow) m (SK x) (InstTarget Q contJump jc_cont x)) →
    checkExpPlain P dc siteRet env jenv e = some u → (∀ h ∈ u, S h) →
    instExp args nf contJump depth jenv.length e = some e' →
    SimUpTo (ValRel dc rflow) m
      (fun k => (eval P k (pre ++ allVs.reverse) J₁ e).bind (SK · k))
      (fun k => eval Q k (pre ++ ρ_site) J₂ e')
  | .bind c b e, m, hm, depth, pre, env, jenv, J₁, J₂, e', u, SK, hpre, henv, hJ, hSK, hck, hu, hi => by
    simp only [checkExpPlain, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hck
    obtain ⟨⟨bf, u1⟩, hb, u2, he, rfl⟩ := hck
    simp only [instExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
    obtain ⟨b', hb', e1', he1', rfl⟩ := hi
    have hbs := instBind_sim hcl (hcall.mono hm) hargs hpre henv hb
      (fun h hh => hu h (List.mem_append_left _ hh)) hb'
    refine (SimUpTo.bind (evalBind_mono Q (pre ++ ρ_site) b')
      (fun w => eval_mono Q (w :: (pre ++ ρ_site)) J₂ e1') hbs fun v w hvw => ?_).congr
      (fun k => by rw [eval_bind, result_bind_assoc])
      (fun k => eval_bind Q k (pre ++ ρ_site) J₂ c b' e1')
    obtain ⟨rfl, hv, hcv⟩ := hvw
    exact instExp_sim hcl hcall hargs e hm (pre := v :: pre) (by simp [hpre]; omega)
      (henv.cons hv hcv) hJ hSK he (fun h hh => hu h (List.mem_append_right _ hh)) he1'
  | .join ar r b e, m, hm, depth, pre, env, jenv, J₁, J₂, e', u, SK, hpre, henv, hJ, hSK, hck, hu, hi => by
    simp only [checkExpPlain, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hck
    obtain ⟨u1, hb, u2, he, rfl⟩ := hck
    simp only [instExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
    obtain ⟨b', hb', e1', he1', rfl⟩ := hi
    let ps : List KAbs := List.replicate ar none
    have hJR : InstJoinR P Q dc rflow siteRet m (InstTarget Q contJump jc_cont) ps
        (.mk (pre ++ allVs.reverse) J₁ ar b r) (.mk (pre ++ ρ_site) J₂ ar b' r) := by
      intro m1
      induction m1 using Nat.strongRecOn with
      | _ m1 ih =>
      intro hm1 SK1 hSK1 vs hvlen hvs
      have har : vs.length = ar := by simpa [ps] using hvlen
      have hstep : ∀ m', m' + 1 ≤ m1 →
          SimUpTo (ValRel dc rflow) m'
            (fun k => (eval P k (vs.reverse ++ (pre ++ allVs.reverse))
              (if r then .mk (pre ++ allVs.reverse) J₁ ar b r :: J₁ else J₁) b).bind (SK1 · (k + 1)))
            (fun k => eval Q k (vs.reverse ++ (pre ++ ρ_site))
              (if r then .mk (pre ++ ρ_site) J₂ ar b' r :: J₂ else J₂) b') := by
        intro m' hm'
        have hpreb : (vs.reverse ++ pre).length = depth + ar + nf := by simp [har, hpre]; omega
        have henvb : EnvOk dc (ps.reverse ++ env) ((vs.reverse ++ pre) ++ allVs.reverse) := by
          rw [List.append_assoc]
          exact EnvOk.append (by simp [ps, har]) (hvs.reverse (by rw [hvlen])) henv
        have hJb : InstJEnv P Q dc rflow siteRet m' contJump jc_cont
            (if r then ps :: jenv else jenv)
            (if r then .mk (pre ++ allVs.reverse) J₁ ar b r :: J₁ else J₁)
            (if r then .mk (pre ++ ρ_site) J₂ ar b' r :: J₂ else J₂) := by
          cases r with
          | false => exact hJ.mono (by omega)
          | true =>
            simp only [↓reduceIte]
            exact (hJ.mono (by omega)).cons (fun i hi => ih i (by omega) (by omega))
        have hSKb : ∀ x, ValOk dc x → ClosOk siteRet x →
            SimUpTo (ValRel dc rflow) m' (fun j => SK1 x (j + 1)) (InstTarget Q contJump jc_cont x) :=
          fun x hx hcx =>
            SimUpTo.shift (InstTarget_mono Q contJump jc_cont x)
              ((hSK1 x hx hcx).mono_n (by omega))
        have hbi : instExp args nf contJump (depth + ar) (if r then ps :: jenv else jenv).length b = some b' := by
          cases r <;> simpa using hb'
        simpa [List.append_assoc] using instExp_sim hcl hcall hargs b (by omega) hpreb henvb hJb hSKb hb
          (fun h hh => hu h (List.mem_append_left _ hh)) hbi
      exact (SimUpTo.later hstep).congr
        (fun k => by simp only [jumpTo, har, ↓reduceIte]; exact later_bind_shift k _ _)
        (fun k => by simp only [jumpTo, har, ↓reduceIte])
    refine (instExp_sim hcl hcall hargs e hm hpre henv (hJ.cons hJR) hSK he
      (fun h hh => hu h (List.mem_append_right _ hh)) (by simpa using he1')).congr
      (fun k => by rw [eval_join'])
      (fun k => eval_join' Q k (pre ++ ρ_site) J₂ ar r b' e1')
  | .jump j as, m, hm, depth, pre, env, jenv, J₁, J₂, e', u, SK, hpre, henv, hJ, hSK, hck, _, hi => by
    simp only [instExp] at hi
    split at hi
    · next hjlt =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
      obtain ⟨as', has', rfl⟩ := hi
      obtain ⟨ps, hj⟩ : ∃ ps, jenv[j]? = some ps := ⟨jenv[j]'hjlt, List.getElem?_eq_getElem hjlt⟩
      simp only [checkExpPlain, hj] at hck
      split at hck
      · next hcond =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hlen, hsub⟩ := hcond
        obtain ⟨jc₁, hj1⟩ : ∃ jc₁, J₁[j]? = some jc₁ :=
          ⟨J₁[j]'(by rw [hJ.1]; exact hjlt), List.getElem?_eq_getElem (by rw [hJ.1]; exact hjlt)⟩
        obtain ⟨jc₂, hj2, hJR⟩ := hJ.2.2 j ps jc₁ hj hj1
        cases hvs : evalAtoms (pre ++ allVs.reverse) as with
        | none =>
          refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
          rw [eval_jump, hj1, hvs]; rfl
        | some vs =>
          have hvs' : evalAtoms (pre ++ ρ_site) as' = some vs := by
            rw [instAtoms_eval hargs hpre has', hvs]
          have hvlen : vs.length = ps.length := by rw [evalAtoms_length _ hvs, hlen]
          have hok := (henv.atoms hvs).sub (by rw [atomsFlow_length, evalAtoms_length _ hvs]) hsub
          refine (hJR m (Nat.le_refl m) SK hSK vs hvlen hok).congr (fun k => ?_) (fun k => ?_)
          · rw [eval_jump, hj1, hvs]; rfl
          · rw [eval_jump, hj2, hvs']; rfl
      · cases hck
    · cases hi
  | .case x alts dflt, m, hm, depth, pre, env, jenv, J₁, J₂, e', u, SK, hpre, henv, hJ, hSK, hck, hu, hi => by
    simp only [checkExpPlain, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hck
    obtain ⟨u1, ha, u2, hd, rfl⟩ := hck
    simp only [instExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
    obtain ⟨x', hx', alts', halts', dflt', hdflt', rfl⟩ := hi
    cases hx : x.eval (pre ++ allVs.reverse) with
    | none =>
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [eval_case, hx]; rfl
    | some v =>
      have hx2 : x'.eval (pre ++ ρ_site) = some v := by rw [instAtom_eval hargs hpre hx', hx]
      obtain ⟨hv, _⟩ := henv.atom hx
      cases hac : v.asCtor P.known with
      | none =>
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [eval_case, hx]; simp [Result.ofOption, hac]; rfl
      | some p =>
        obtain ⟨c, fs⟩ := p
        obtain ⟨hfsOk, _⟩ := asCtor_ok hcl.knownOk hv hac
        have hdSim : SimUpTo (ValRel dc rflow) m
            (fun k => (evalAlts P k (pre ++ allVs.reverse) J₁ c fs [] dflt).bind (SK · k))
            (fun k => evalAlts Q k (pre ++ ρ_site) J₂ c fs [] dflt') := by
          cases dflt with
          | none =>
            simp only [instOpt, Option.some.injEq] at hdflt'; subst hdflt'
            exact (SimUpTo.stuck _).congr (fun k => by rw [evalAlts_nil]; rfl) (fun _ => rfl)
          | some de =>
            obtain ⟨de', hde', rfl⟩ := Option.map_eq_some_iff.1 hdflt'
            exact (instExp_sim hcl hcall hargs de hm hpre henv hJ hSK hd
              (fun h hh => hu h (List.mem_append_right _ hh)) hde').congr
              (fun k => by rw [evalAlts_nil])
              (fun k => evalAlts_nil Q k (pre ++ ρ_site) J₂ c fs (some de'))
        refine (instAlts_sim hcl hcall hargs alts hm hpre henv hJ hSK hfsOk ha
          (fun h hh => hu h (List.mem_append_left _ hh)) halts' hdSim).congr
          (fun k => ?_) (fun k => ?_)
        · rw [eval_case, hx]; simp [Result.ofOption, hac]
        · rw [eval_case, hx2, hcl.known]; simp [Result.ofOption, hac]
  | .ret a, m, _, depth, pre, env, jenv, J₁, J₂, e', _, SK, hpre, henv, hJ, hSK, hck, _, hi => by
    simp only [checkExpPlain] at hck
    split at hck
    · next hsub =>
      simp only [instExp, Option.bind_eq_bind, Option.bind_eq_some_iff] at hi
      obtain ⟨a', ha', h2⟩ := hi
      cases ha : a.eval (pre ++ allVs.reverse) with
      | none =>
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [eval_ret', ha]; rfl
      | some v =>
        have ha2 : a'.eval (pre ++ ρ_site) = some v := by rw [instAtom_eval hargs hpre ha', ha]
        obtain ⟨hv, hc⟩ := henv.atom ha
        have hret := hSK v hv (kabsSub_sound hsub hc)
        cases contJump with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h2
          subst h2
          refine hret.congr (fun k => ?_) (fun k => ?_)
          · rw [eval_ret', ha]; rfl
          · rw [eval_ret', ha2]; rfl
        | true =>
          simp only [↓reduceIte, Option.some.injEq] at h2
          subst h2
          have hjc : J₂[jenv.length]? = some jc_cont := hJ.2.1 rfl
          refine hret.congr (fun k => ?_) (fun k => ?_)
          · rw [eval_ret', ha]; rfl
          · rw [eval_jump, hjc, evalAtoms_cons, ha2]
            simp [evalAtoms_nil, Result.ofOption, InstTarget]
    · cases hck
  | .tick e, m, hm, depth, pre, env, jenv, J₁, J₂, e', u, SK, hpre, henv, hJ, hSK, hck, hu, hi => by
    simp only [instExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
    obtain ⟨e1', he1', rfl⟩ := hi
    refine (SimUpTo.later fun m' hm' => ?_).congr
      (fun k => by rw [eval_tick]; exact later_bind_shift k _ _)
      (fun k => eval_tick Q k (pre ++ ρ_site) J₂ e1')
    have hSK' : ∀ x, ValOk dc x → ClosOk siteRet x →
        SimUpTo (ValRel dc rflow) m' (fun j => SK x (j + 1)) (InstTarget Q contJump jc_cont x) :=
      fun x hx hcx =>
        SimUpTo.shift (InstTarget_mono Q contJump jc_cont x)
          ((hSK x hx hcx).mono_n (by omega))
    exact instExp_sim hcl hcall hargs e (by omega) hpre henv (hJ.mono (by omega)) hSK' hck hu he1'
  | .trap, _, _, _, pre, _, _, J₁, J₂, e', _, _, _, _, _, _, _, _, hi => by
    simp only [instExp, Option.some.injEq] at hi; subst hi
    exact SimUpTo.trap.congr (fun k => by rw [eval_trap']; rfl)
      (fun k => eval_trap' Q k (pre ++ ρ_site) J₂)

theorem instAlts_sim {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n : Nat}
    (hcl : Closed P Q dc S) (hcall : CallOk P Q dc S n)
    {args : List Atom} {ρ_site allVs : List Val} {nf : Nat}
    (hargs : evalAtoms ρ_site args = some allVs)
    {contJump : Bool} {jc_cont : JClo} {rflow siteRet : KAbs} :
    ∀ (alts : List Alt) {m : Nat}, m ≤ n →
    ∀ {depth : Nat} {pre : List Val} {env : List KAbs} {jenv : List (List KAbs)}
      {J₁ J₂ : List JClo} {c : Key.CtorKey} {fs : List Val}
      {alts' : List Alt} {dflt dflt' : Option Exp} {u1 : List GlobalId}
      {SK : Val → Nat → Result Val},
    pre.length = depth + nf →
    EnvOk dc env (pre ++ allVs.reverse) →
    InstJEnv P Q dc rflow siteRet m contJump jc_cont jenv J₁ J₂ →
    (∀ x, ValOk dc x → ClosOk siteRet x →
      SimUpTo (ValRel dc rflow) m (SK x) (InstTarget Q contJump jc_cont x)) →
    EnvOk dc (fieldFlows dc c fs.length) fs →
    checkAltsPlain P dc siteRet env jenv alts = some u1 →
    (∀ h ∈ u1, S h) →
    instAlts args nf contJump depth jenv.length alts = some alts' →
    SimUpTo (ValRel dc rflow) m
      (fun k => (evalAlts P k (pre ++ allVs.reverse) J₁ c fs [] dflt).bind (SK · k))
      (fun k => evalAlts Q k (pre ++ ρ_site) J₂ c fs [] dflt') →
    SimUpTo (ValRel dc rflow) m
      (fun k => (evalAlts P k (pre ++ allVs.reverse) J₁ c fs alts dflt).bind (SK · k))
      (fun k => evalAlts Q k (pre ++ ρ_site) J₂ c fs alts' dflt')
  | [], _, _, _, pre, _, _, J₁, J₂, c, fs, alts', dflt, dflt', _, _, _, _, _, _, _, _, _, halts', hdSim => by
    simp only [instAlts, Option.some.injEq] at halts'; subst halts'
    exact hdSim
  | .mk key na body :: rest, m, hm, depth, pre, env, jenv, J₁, J₂, c, fs, alts', dflt, dflt',
      u1, SK, hpre, henv, hJ, hSK, hfsOk, ha, hu1, halts', hdSim => by
    simp only [checkAltsPlain, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨ua, hba, urest, hrest, rfl⟩ := ha
    simp only [instAlts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at halts'
    obtain ⟨b', hb', rest', hrest', rfl⟩ := halts'
    by_cases hmatch : key = c ∧ na = fs.length
    · obtain ⟨rfl, rfl⟩ := hmatch
      have hpreb : (fs.reverse ++ pre).length = depth + fs.length + nf := by simp [hpre]; omega
      have henvb : EnvOk dc ((fieldFlows dc key fs.length).reverse ++ env)
          ((fs.reverse ++ pre) ++ allVs.reverse) := by
        rw [List.append_assoc]
        exact EnvOk.append (by simp [fieldFlows_length])
          (hfsOk.reverse (fieldFlows_length dc key fs.length)) henv
      refine (instExp_sim hcl hcall hargs body hm hpreb henvb hJ hSK hba
        (fun h hh => hu1 h (List.mem_append_left _ hh)) hb').congr (fun k => ?_) (fun k => ?_)
      · rw [evalAlts_cons, if_pos ⟨rfl, rfl⟩, List.append_assoc]
      · rw [evalAlts_cons, if_pos ⟨rfl, rfl⟩, List.append_assoc]
    · refine (instAlts_sim hcl hcall hargs rest hm hpre henv hJ hSK hfsOk hrest
        (fun h hh => hu1 h (List.mem_append_right _ hh)) hrest' hdSim).congr
        (fun k => ?_) (fun k => ?_)
      · rw [evalAlts_cons, if_neg hmatch]
      · rw [evalAlts_cons, if_neg hmatch]

end

/-! ### `checkRewriteExp` monotonicity of `used` and simulation -/

mutual

theorem checkRewriteExp_used_mono {P : Program} {dc : DecCert} :
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)}
      {st : RwSt} {e e' : Exp} {st' : RwSt},
    checkRewriteExp P dc rflow env jenv st e = some (e', st') →
    ∀ h ∈ st.used, h ∈ st'.used
  | rflow, env, jenv, st, .bind c b body, e', st', h, x, hx => by
    cases b with
    | call d args =>
      cases args with
      | nil =>
        simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨bf, u1⟩, _, ⟨body', st2⟩, hbody, rfl, rfl⟩ := h
        exact checkRewriteExp_used_mono hbody x (List.mem_append_right u1 hx)
      | cons f as =>
        unfold checkRewriteExp at h
        dsimp only at h
        split at h
        · rename_i res htried
          simp only [Option.some.injEq] at h; subst h
          cases hgd : P.global? d with
          | none => rw [hgd] at htried; dsimp only at htried; cases htried
          | some gd =>
            rw [hgd] at htried; dsimp only at htried
            split at htried
            · cases hgb : gd.body with
              | bind _ _ _ | join _ _ _ _ | jump _ _ | ret _ | tick _ | trap => rw [hgb] at htried; dsimp only at htried; cases htried
              | case x0 dispAlts dflt =>
                cases x0 with
                | lit _ | box => rw [hgb] at htried; dsimp only at htried; cases htried
                | var m =>
                  cases dflt with
                  | some _ => rw [hgb] at htried; dsimp only at htried; cases htried
                  | none =>
                    rw [hgb] at htried; dsimp only at htried
                    split at htried
                    · cases hat : atomFlow env f with
                      | none => rw [hat] at htried; dsimp only at htried; cases htried
                      | some ks =>
                        rw [hat] at htried; dsimp only at htried
                        split at htried
                        · split at htried
                          · next nAlts uArms hna =>
                            cases htail : isTailRet body with
                            | true =>
                              simp only [htail, ↓reduceIte] at htried
                              have hite : ∀ {p : Prop} [Decidable p] {α : Type} {a b : α},
                                  (if p then some a else none) = some b → a = b := by
                                intro p _ _ _ _ hp; split at hp
                                · exact Option.some.inj hp
                                · cases hp
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hite htried)
                              exact List.mem_append_right uArms hx
                            | false =>
                              simp only [htail, Bool.false_eq_true, ↓reduceIte] at htried
                              split at htried
                              · next body' st2 hbr =>
                                simp only [Option.some.injEq, Prod.mk.injEq] at htried
                                obtain ⟨rfl, rfl⟩ := htried
                                exact checkRewriteExp_used_mono hbr x (List.mem_append_right uArms hx)
                              · cases htried
                          · cases htried
                        · cases htried
                    · cases htried
            · cases htried
        · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨⟨bf, u1⟩, _, ⟨body', st2⟩, hbody, rfl, rfl⟩ := h
          exact checkRewriteExp_used_mono hbody x (List.mem_append_right u1 hx)
    | atom _ | con _ _ | proj _ _ _ | prim _ _ | glob _ | app _ _ | fn _ _ =>
      simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨bf, u1⟩, _, ⟨body', st2⟩, hbody, rfl, rfl⟩ := h
      exact checkRewriteExp_used_mono hbody x (List.mem_append_right u1 hx)
  | rflow, env, jenv, st, .join n r b body, e', st', h, x, hx => by
    simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨b', st2⟩, hb, ⟨body', st3⟩, hbody, rfl, rfl⟩ := h
    exact checkRewriteExp_used_mono hbody x (checkRewriteExp_used_mono hb x hx)
  | _, _, _, _, .jump _ _, _, _, h, _, hx => by
    simp only [checkRewriteExp] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hx
      · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hx
  | rflow, env, jenv, st, .case _ alts dflt, e', st', h, x, hx => by
    simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨alts', st1⟩, halts, ⟨dflt', st2⟩, hdflt, rfl, rfl⟩ := h
    exact checkRewriteOpt_used_mono hdflt x (checkRewriteAlts_used_mono halts x hx)
  | _, _, _, _, .ret _, _, _, h, _, hx => by
    simp only [checkRewriteExp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hx
    · cases h
  | rflow, env, jenv, st, .tick e, _, _, h, x, hx => by
    simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨e1, st1⟩, he, rfl, rfl⟩ := h
    exact checkRewriteExp_used_mono he x hx
  | _, _, _, _, .trap, _, _, h, _, hx => by
    simp only [checkRewriteExp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hx

theorem checkRewriteAlts_used_mono {P : Program} {dc : DecCert} :
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)}
      {st : RwSt} {alts alts' : List Alt} {st' : RwSt},
    checkRewriteAlts P dc rflow env jenv st alts = some (alts', st') →
    ∀ h ∈ st.used, h ∈ st'.used
  | _, _, _, _, [], _, _, h, _, hx => by
    simp only [checkRewriteAlts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hx
  | _, _, _, _, .mk _ _ b :: rest, _, _, h, x, hx => by
    simp only [checkRewriteAlts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨b', st1⟩, hb, ⟨rest', st2⟩, hrest, rfl, rfl⟩ := h
    exact checkRewriteAlts_used_mono hrest x (checkRewriteExp_used_mono hb x hx)

theorem checkRewriteOpt_used_mono {P : Program} {dc : DecCert} :
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)}
      {st : RwSt} {d d' : Option Exp} {st' : RwSt},
    checkRewriteOpt P dc rflow env jenv st d = some (d', st') →
    ∀ h ∈ st.used, h ∈ st'.used
  | _, _, _, _, none, _, _, h, _, hx => by
    simp only [checkRewriteOpt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hx
  | _, _, _, _, some e, _, _, h, x, hx => by
    simp only [checkRewriteOpt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨e', st'⟩, he, rfl, rfl⟩ := h
    exact checkRewriteExp_used_mono he x hx

end

theorem isTailRet_eq : ∀ {e : Exp}, isTailRet e = true → e = .ret (.var 0)
  | .ret (.var 0), _ => rfl
  | .ret (.var (_ + 1)), h => by simp [isTailRet] at h
  | .ret (.lit _), h | .ret .box, h | .bind .., h | .join .., h
  | .jump .., h | .case .., h | .tick _, h | .trap, h => by simp [isTailRet] at h

/-- Simulation of one narrowed dispatch site (both tail and non-tail). -/
theorem narrowSite_sim {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n m : Nat}
    (hcl : Closed P Q dc S) (hcall : CallOk P Q dc S n) (hm : m ≤ n)
    {rflow siteRet : KAbs} {env : List KAbs} {ρ : List Val} {J₁ J₂ : List JClo}
    (henv : EnvOk dc env ρ)
    {c : Ixon.V3.LetMode} {d : GlobalId} {gd : GDef} {f : Atom} {as : List Atom}
    {dispAlts nAlts : List Alt} {ks : List Key.CtorKey} {uArms : List GlobalId}
    {body : Exp} {e' : Exp}
    (hgd : P.global? d = some gd)
    (hlen : gd.ps.length = as.length + 1)
    (hgb : gd.body = .case (.var as.length) dispAlts none)
    (hclo : allCloAlts dispAlts = true)
    (hat : atomFlow env f = some ks)
    (hna : narrowArms P dc dispAlts (f :: as) (atomFlow env f :: atomsFlow env as)
      (!isTailRet body) siteRet (dedupKeys ks) = some (nAlts, uArms))
    (huArms : ∀ h ∈ uArms, S h)
    (hcont :
      (isTailRet body = true ∧ kabsSub siteRet rflow = true ∧ e' = .tick (.case f nAlts none)) ∨
      (isTailRet body = false ∧ ∃ body',
        e' = .join 1 false body' (.tick (.case f nAlts none)) ∧
        ∀ v, ValOk dc v → ClosOk siteRet v →
          SimUpTo (ValRel dc rflow) m
            (fun k => eval P k (v :: ρ) J₁ body)
            (fun k => eval Q k (v :: ρ) J₂ body'))) :
    SimUpTo (ValRel dc rflow) m
      (fun k => eval P k ρ J₁ (.bind c (.call d (f :: as)) body))
      (fun k => eval Q k ρ J₂ e') := by
  cases hargs : evalAtoms ρ (f :: as) with
  | none =>
    refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
    rw [eval_bind, evalBind_call, hgd, hargs]; rfl
  | some allVs =>
    cases allVs with
    | nil =>
      have := evalAtoms_length ρ hargs; simp at this
    | cons fv vs =>
      have hargsCons := hargs
      rw [evalAtoms_cons] at hargsCons
      cases hf : f.eval ρ with
      | none => rw [hf] at hargsCons; cases hargsCons
      | some fv0 =>
        rw [hf] at hargsCons
        cases hvs : evalAtoms ρ as with
        | none => rw [hvs] at hargsCons; cases hargsCons
        | some vs0 =>
          rw [hvs] at hargsCons
          simp only [Option.bind_some, Option.map_some, Option.some.injEq, List.cons.injEq] at hargsCons
          obtain ⟨hfeq, hvseq⟩ := hargsCons
          subst fv0; subst vs0
          have hvslen : vs.length = as.length := evalAtoms_length ρ hvs
          have hallLen : (fv :: vs).length = gd.ps.length := by simp [hvslen, hlen]
          have hargEnv : EnvOk dc (atomFlow env f :: atomsFlow env as) (fv :: vs) :=
            henv.atoms hargs
          have hargFlowLen : (atomFlow env f :: atomsFlow env as).length = (fv :: vs).length := by
            simp [atomsFlow_length, hvslen]
          obtain ⟨hfv, hcfv⟩ := henv.atom hf
          rw [hat] at hcfv
          have hvar : (Atom.var as.length).eval (fv :: vs).reverse = some fv := by
            have hrl : vs.reverse.length = as.length := by simp [hvslen]
            simp [Atom.eval, List.reverse_cons, List.getElem?_append_right (Nat.le_of_eq hrl), hrl]
          -- Helper for matching the scrutinee inside the case after the call/tick charge
          have hcase : ∀ (m' : Nat) (hm' : m' + 1 ≤ m) (contJump : Bool) (jc_cont : JClo)
              (J_case : List JClo) (SK : Val → Nat → Result Val),
              contJump = !isTailRet body →
              (contJump = true → J_case[0]? = some jc_cont) →
              (∀ x, ValOk dc x → ClosOk siteRet x →
                SimUpTo (ValRel dc rflow) m' (SK x) (InstTarget Q contJump jc_cont x)) →
              SimUpTo (ValRel dc rflow) m'
                (fun k => (eval P k (fv :: vs).reverse [] gd.body).bind (SK · k))
                (fun k => eval Q k ρ J_case (.case f nAlts none)) := by
            intro m' hm' contJump jc_cont J_case SK hcj hJ0 hSK
            subst hcj
            cases hac : fv.asCtor P.known with
            | none =>
              refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
              rw [hgb, eval_case, hvar]; simp [Result.ofOption, hac]; rfl
            | some p =>
              obtain ⟨ck, fvs⟩ := p
              obtain ⟨hfvsOk, hcloEq⟩ := asCtor_ok hcl.knownOk hfv hac
              cases ck with
              | src s =>
                refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
                rw [hgb, eval_case, hvar]
                simp [Result.ofOption, hac, evalAlts_allClo_src hclo]; rfl
              | clo f0 j0 =>
                have hfvEq : fv = .con (.clo f0 j0) fvs := hcloEq f0 j0 rfl
                have hckInKs : Key.CtorKey.clo f0 j0 ∈ ks := by
                  rw [hfvEq] at hcfv; exact hcfv
                have hckInDedup : Key.CtorKey.clo f0 j0 ∈ dedupKeys ks :=
                  (dedupKeys_mem ks _).2 hckInKs
                rcases narrowArms_spec (dedupKeys_nodup ks) hna hckInDedup with
                  hnil | ⟨nf, altBody, armBody, u1, hfd, hfn, hckPlain, hinst, hu1⟩
                · refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
                  rw [hgb, eval_case, hvar]
                  simp [Result.ofOption, hac, evalAlts_filter_nil hnil]; rfl
                · by_cases hnf : nf = fvs.length
                  · subst hnf
                    have hpreLen : fvs.reverse.length = 0 + fvs.length := by simp
                    have henvArm : EnvOk dc
                        ((fieldFlows dc (.clo f0 j0) fvs.length).reverse ++
                          (atomFlow env f :: atomsFlow env as).reverse)
                        (fvs.reverse ++ (fv :: vs).reverse) :=
                      EnvOk.append (by simp [fieldFlows_length])
                        (hfvsOk.reverse (fieldFlows_length dc _ _))
                        (hargEnv.reverse hargFlowLen)
                    have hJarm := InstJEnv.nil P Q dc rflow siteRet m' (!isTailRet body)
                      jc_cont J_case hJ0
                    have hsim := instExp_sim hcl hcall hargs altBody (by omega) hpreLen henvArm hJarm hSK
                      hckPlain (fun h hh => huArms h (hu1 h hh)) hinst
                    refine hsim.congr (fun k => ?_) (fun k => ?_)
                    · rw [hgb, eval_case, hvar]
                      simp only [Result.ofOption, hac, Result.bind_ok,
                        evalAlts_filter_singleton hfd, ↓reduceIte]
                    · rw [eval_case, hf, hcl.known]
                      simp only [Result.ofOption, hac, Result.bind_ok,
                        evalAlts_filter_singleton hfn, ↓reduceIte]
                  · refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
                    rw [hgb, eval_case, hvar]
                    simp [Result.ofOption, hac, evalAlts_filter_singleton hfd, hnf]; rfl
          rcases hcont with ⟨htail, hsub, rfl⟩ | ⟨hntail, body', rfl, hbody⟩
          · have hbe : body = .ret (.var 0) := isTailRet_eq htail
            subst hbe
            refine (SimUpTo.later
              (c₁ := fun k => eval P k (fv :: vs).reverse [] gd.body)
              (c₂ := fun k => eval Q k ρ J₂ (.case f nAlts none))
              fun m' hm' => ?_).congr (fun k => ?_) (fun k => ?_)
            · have hSK : ∀ x, ValOk dc x → ClosOk siteRet x →
                  SimUpTo (ValRel dc rflow) m' (fun _ => .ok x)
                    (InstTarget Q (!isTailRet (.ret (.var 0))) default x) :=
                fun x hx hcx => SimUpTo.ok ⟨rfl, hx, kabsSub_sound hsub hcx⟩
              refine (hcase m' hm' false default J₂ (fun x _ => .ok x) (by simp [htail])
                (fun h => nomatch h) hSK).congr (fun k => ?_) (fun _ => rfl)
              cases eval P k (fv :: vs).reverse [] gd.body <;> rfl
            · rw [eval_bind, evalBind_call_of P k ρ hgd hargs hallLen]
              cases k with
              | zero => rfl
              | succ j =>
                simp only [later_succ]
                cases eval P j (fv :: vs).reverse [] gd.body with
                | ok val => simp [eval_ret', Atom.eval, Result.ofOption]
                | timeout | resource _ | trap | stuck => rfl
            · exact eval_tick Q k ρ J₂ (.case f nAlts none)
          · let jc_cont : JClo := .mk ρ J₂ 1 body' false
            refine (SimUpTo.later
              (c₁ := fun k => (eval P k (fv :: vs).reverse [] gd.body).bind fun x => eval P (k + 1) (x :: ρ) J₁ body)
              (c₂ := fun k => eval Q k ρ (jc_cont :: J₂) (.case f nAlts none))
              fun m' hm' => ?_).congr (fun k => ?_) (fun k => ?_)
            · have hSK : ∀ x, ValOk dc x → ClosOk siteRet x →
                  SimUpTo (ValRel dc rflow) m'
                    (fun j => eval P (j + 1) (x :: ρ) J₁ body)
                    (InstTarget Q true jc_cont x) := by
                intro x hx hcx
                have h1 := (hbody x hx hcx).mono_n (show m' + 1 ≤ m by omega)
                have h2 := SimUpTo.shift (eval_mono Q (x :: ρ) J₂ body') h1
                have h3 := SimUpTo.laterR (eval_mono Q (x :: ρ) J₂ body') h2
                refine h3.congr (fun _ => rfl) (fun k => ?_)
                simp [InstTarget, jc_cont, jumpTo]
              exact hcase m' hm' true jc_cont (jc_cont :: J₂)
                (fun x j => eval P (j + 1) (x :: ρ) J₁ body)
                (by simp [hntail]) (fun _ => rfl) hSK
            · rw [eval_bind, evalBind_call_of P k ρ hgd hargs hallLen]
              exact later_bind_shift k
                (fun j => eval P j (fv :: vs).reverse [] gd.body)
                (fun v j => eval P j (v :: ρ) J₁ body)
            · rw [eval_join', eval_tick]

mutual

theorem checkRewriteExp_sim {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n : Nat}
    (hcl : Closed P Q dc S) (hcall : CallOk P Q dc S n) :
    ∀ (e : Exp) {m : Nat}, m ≤ n →
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)}
      {ρ : List Val} {J₁ J₂ : List JClo} {st st' : RwSt} {e' : Exp},
    EnvOk dc env ρ → PlainJEnv P Q dc rflow m jenv J₁ J₂ →
    checkRewriteExp P dc rflow env jenv st e = some (e', st') →
    (∀ h ∈ st'.used, S h) →
    SimUpTo (ValRel dc rflow) m (fun k => eval P k ρ J₁ e) (fun k => eval Q k ρ J₂ e')
  | .bind c b body, m, hm, rflow, env, jenv, ρ, J₁, J₂, st, st', e', henv, hJ, hck, hu => by
    cases b with
    | call d args =>
      cases args with
      | nil =>
        simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at hck
        obtain ⟨⟨bf, u1⟩, hb, ⟨body', st2⟩, hbody, rfl, rfl⟩ := hck
        have hu1 : ∀ h ∈ u1, S h := fun h hh =>
          hu h (checkRewriteExp_used_mono hbody h (List.mem_append_left _ hh))
        have hbs := checkBindPlain_sim hcl (hcall.mono hm) henv hb hu1
        refine (SimUpTo.bind (evalBind_mono Q ρ (.call d []))
          (fun w => eval_mono Q (w :: ρ) J₂ body') hbs fun v w hvw => ?_).congr
          (fun k => eval_bind P k ρ J₁ c (.call d []) body)
          (fun k => eval_bind Q k ρ J₂ c (.call d []) body')
        obtain ⟨rfl, hv, hcv⟩ := hvw
        exact checkRewriteExp_sim hcl hcall body hm (henv.cons hv hcv) hJ hbody hu
      | cons f as =>
        unfold checkRewriteExp at hck
        dsimp only at hck
        split at hck
        · rename_i res htried
          simp only [Option.some.injEq] at hck; subst hck
          cases hgd : P.global? d with
          | none => rw [hgd] at htried; dsimp only at htried; cases htried
          | some gd =>
            rw [hgd] at htried; dsimp only at htried
            split at htried
            · next hcond1 =>
              simp only [Bool.and_eq_true, beq_iff_eq] at hcond1
              cases hgb : gd.body with
              | bind _ _ _ | join _ _ _ _ | jump _ _ | ret _ | tick _ | trap => rw [hgb] at htried; dsimp only at htried; cases htried
              | case x0 dispAlts dflt =>
                cases x0 with
                | lit _ | box => rw [hgb] at htried; dsimp only at htried; cases htried
                | var idx =>
                  cases dflt with
                  | some _ => rw [hgb] at htried; dsimp only at htried; cases htried
                  | none =>
                    rw [hgb] at htried; dsimp only at htried
                    split at htried
                    · next hcond2 =>
                      simp only [Bool.and_eq_true, beq_iff_eq] at hcond2
                      obtain ⟨hidx, hclo⟩ := hcond2
                      subst hidx
                      cases hat : atomFlow env f with
                      | none => rw [hat] at htried; dsimp only at htried; cases htried
                      | some ks =>
                        rw [hat] at htried; dsimp only at htried
                        split at htried
                        · split at htried
                          · next nAlts uArms hna =>
                            have hna' := hna
                            rw [← hat] at hna'
                            cases htail : isTailRet body with
                            | true =>
                              simp only [htail, ↓reduceIte] at htried
                              have hite : ∀ {p : Prop} [Decidable p] {α : Type} {a b : α},
                                  (if p then some a else none) = some b → p ∧ a = b := by
                                intro p _ _ _ _ hp; split at hp
                                · exact ⟨‹p›, Option.some.inj hp⟩
                                · cases hp
                              obtain ⟨hsub, hpair⟩ := hite htried
                              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
                              refine narrowSite_sim hcl hcall hm henv hgd hcond1.2 hgb hclo hat hna'
                                (fun h hh => hu h (List.mem_append_left _ hh)) (.inl ⟨htail, hsub, rfl⟩)
                            | false =>
                              simp only [htail, Bool.false_eq_true, ↓reduceIte] at htried
                              split at htried
                              · next body' st2 hbr =>
                                simp only [Option.some.injEq, Prod.mk.injEq] at htried
                                obtain ⟨rfl, rfl⟩ := htried
                                have huArms : ∀ h ∈ uArms, S h := fun h hh =>
                                  hu h (checkRewriteExp_used_mono hbr h (List.mem_append_left _ hh))
                                refine narrowSite_sim hcl hcall hm henv hgd hcond1.2 hgb hclo hat hna'
                                  huArms (.inr ⟨htail, body', rfl, fun v hv hcv =>
                                    checkRewriteExp_sim hcl hcall body hm (henv.cons hv hcv) hJ hbr hu⟩)
                              · cases htried
                          · cases htried
                        · cases htried
                    · cases htried
            · cases htried
        · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
            Prod.mk.injEq] at hck
          obtain ⟨⟨bf, u1⟩, hb, ⟨body', st2⟩, hbody, rfl, rfl⟩ := hck
          have hu1 : ∀ h ∈ u1, S h := fun h hh =>
            hu h (checkRewriteExp_used_mono hbody h (List.mem_append_left _ hh))
          have hbs := checkBindPlain_sim hcl (hcall.mono hm) henv hb hu1
          refine (SimUpTo.bind (evalBind_mono Q ρ (.call d (f :: as)))
            (fun w => eval_mono Q (w :: ρ) J₂ body') hbs fun v w hvw => ?_).congr
            (fun k => eval_bind P k ρ J₁ c (.call d (f :: as)) body)
            (fun k => eval_bind Q k ρ J₂ c (.call d (f :: as)) body')
          obtain ⟨rfl, hv, hcv⟩ := hvw
          exact checkRewriteExp_sim hcl hcall body hm (henv.cons hv hcv) hJ hbody hu
    | atom _ | con _ _ | proj _ _ _ | prim _ _ | glob _ | app _ _ | fn _ _ =>
      simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq, Prod.mk.injEq] at hck
      obtain ⟨⟨bf, u1⟩, hb, ⟨body', st2⟩, hbody, rfl, rfl⟩ := hck
      have hu1 : ∀ h ∈ u1, S h := fun h hh =>
        hu h (checkRewriteExp_used_mono hbody h (List.mem_append_left _ hh))
      have hbs := checkBindPlain_sim hcl (hcall.mono hm) henv hb hu1
      refine (SimUpTo.bind (evalBind_mono Q ρ _)
        (fun w => eval_mono Q (w :: ρ) J₂ body') hbs fun v w hvw => ?_).congr
        (fun k => eval_bind P k ρ J₁ c _ body)
        (fun k => eval_bind Q k ρ J₂ c _ body')
      obtain ⟨rfl, hv, hcv⟩ := hvw
      exact checkRewriteExp_sim hcl hcall body hm (henv.cons hv hcv) hJ hbody hu
  | .join ar r b body, m, hm, rflow, env, jenv, ρ, J₁, J₂, st, st', e', henv, hJ, hck, hu => by
    simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hck
    obtain ⟨⟨b', st2⟩, hb, ⟨body', st3⟩, hbody, rfl, rfl⟩ := hck
    let ps : List KAbs := (match st.joins with
      | p :: ps' => if p.length == ar then (p, ps') else (List.replicate ar none, ps')
      | [] => (List.replicate ar none, [])).1
    have hpsLen : ps.length = ar := by
      show (match st.joins with
        | p :: ps' => if p.length == ar then (p, ps') else (List.replicate ar none, ps')
        | [] => (List.replicate ar none, [])).1.length = ar
      cases st.joins with
      | nil => simp
      | cons p ps' =>
        dsimp only
        split
        · next h => exact beq_iff_eq.1 h
        · simp
    have hu2 : ∀ h ∈ st2.used, S h := fun h hh => hu h (checkRewriteExp_used_mono hbody h hh)
    have hJR : PlainJoinR P Q dc rflow m ps (.mk ρ J₁ ar b r) (.mk ρ J₂ ar b' r) := by
      intro m1
      induction m1 using Nat.strongRecOn with
      | _ m1 ih =>
      intro hm1 vs hvlen hvs
      have har : vs.length = ar := by rw [hvlen, hpsLen]
      have hstep : ∀ m', m' + 1 ≤ m1 →
          SimUpTo (ValRel dc rflow) m'
            (fun k => eval P k (vs.reverse ++ ρ) (if r then .mk ρ J₁ ar b r :: J₁ else J₁) b)
            (fun k => eval Q k (vs.reverse ++ ρ) (if r then .mk ρ J₂ ar b' r :: J₂ else J₂) b') := by
        intro m' hm'
        have henvb : EnvOk dc (ps.reverse ++ env) (vs.reverse ++ ρ) :=
          EnvOk.append (by simp [hvlen]) (hvs.reverse (by rw [hvlen])) henv
        have hJb : PlainJEnv P Q dc rflow m' (if r then ps :: jenv else jenv)
            (if r then .mk ρ J₁ ar b r :: J₁ else J₁)
            (if r then .mk ρ J₂ ar b' r :: J₂ else J₂) := by
          cases r with
          | false => exact hJ.mono (by omega)
          | true =>
            simp only [↓reduceIte]
            exact (hJ.mono (by omega)).cons (fun i hi => ih i (by omega) (by omega))
        exact checkRewriteExp_sim hcl hcall b (by omega) henvb hJb hb hu2
      exact (SimUpTo.later hstep).congr
        (fun k => by simp [jumpTo, har]) (fun k => by simp [jumpTo, har])
    refine (checkRewriteExp_sim hcl hcall body hm henv (hJ.cons hJR) hbody hu).congr
      (fun k => eval_join' P k ρ J₁ ar r b body)
      (fun k => eval_join' Q k ρ J₂ ar r b' body')
  | .jump j as, m, _, rflow, env, jenv, ρ, J₁, J₂, _, _, e', henv, hJ, hck, _ => by
    simp only [checkRewriteExp] at hck
    cases hj : jenv[j]? with
    | none =>
      have hlt : ¬ j < J₁.length := by
        rw [hJ.1]; intro hlt; exact absurd (List.getElem?_eq_none_iff.1 hj) (by omega)
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [eval_jump, List.getElem?_eq_none (by omega)]; rfl
    | some ps =>
      rw [hj] at hck; dsimp only at hck
      split at hck
      · next hcond =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hlen, hsub⟩ := hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at hck
        obtain ⟨rfl, rfl⟩ := hck
        have hjlt : j < jenv.length := (List.getElem?_eq_some_iff.1 hj).1
        have hjlt1 : j < J₁.length := hJ.1 ▸ hjlt
        have hjlt2 : j < J₂.length := hJ.2.1 ▸ hjlt
        obtain ⟨jc₁, hj1⟩ : ∃ jc₁, J₁[j]? = some jc₁ := ⟨J₁[j]'hjlt1, List.getElem?_eq_getElem hjlt1⟩
        obtain ⟨jc₂, hj2⟩ : ∃ jc₂, J₂[j]? = some jc₂ := ⟨J₂[j]'hjlt2, List.getElem?_eq_getElem hjlt2⟩
        cases hvs : evalAtoms ρ as with
        | none =>
          refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
          rw [eval_jump, hj1, hvs]; rfl
        | some vs =>
          have hvlen : vs.length = ps.length := by rw [evalAtoms_length ρ hvs, hlen]
          have hok := (henv.atoms hvs).sub (by rw [atomsFlow_length, evalAtoms_length ρ hvs]) hsub
          refine (hJ.2.2 j ps jc₁ jc₂ hj hj1 hj2 m (Nat.le_refl m) vs hvlen hok).congr
            (fun k => ?_) (fun k => ?_)
          · rw [eval_jump, hj1, hvs]; rfl
          · rw [eval_jump, hj2, hvs]; rfl
      · cases hck
  | .case x alts dflt, m, hm, rflow, env, jenv, ρ, J₁, J₂, st, st', e', henv, hJ, hck, hu => by
    simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hck
    obtain ⟨⟨alts', st1⟩, ha, ⟨dflt', st2⟩, hd, rfl, rfl⟩ := hck
    have hu1 : ∀ h ∈ st1.used, S h := fun h hh => hu h (checkRewriteOpt_used_mono hd h hh)
    cases hx : x.eval ρ with
    | none =>
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [eval_case, hx]; rfl
    | some v =>
      obtain ⟨hv, _⟩ := henv.atom hx
      cases hac : v.asCtor P.known with
      | none =>
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [eval_case, hx]; simp [Result.ofOption, hac]
      | some p =>
        obtain ⟨c, fs⟩ := p
        obtain ⟨hfsOk, _⟩ := asCtor_ok hcl.knownOk hv hac
        have hdSim : SimUpTo (ValRel dc rflow) m
            (fun k => evalAlts P k ρ J₁ c fs [] dflt)
            (fun k => evalAlts Q k ρ J₂ c fs [] dflt') := by
          cases dflt with
          | none =>
            simp only [checkRewriteOpt, Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨rfl, rfl⟩ := hd
            exact (SimUpTo.stuck _).congr (fun k => evalAlts_nil P k ρ J₁ c fs none) (fun _ => rfl)
          | some de =>
            simp only [checkRewriteOpt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
              Prod.mk.injEq] at hd
            obtain ⟨⟨de', st3⟩, hde, rfl, rfl⟩ := hd
            exact (checkRewriteExp_sim hcl hcall de hm henv hJ hde hu).congr
              (fun k => evalAlts_nil P k ρ J₁ c fs (some de))
              (fun k => evalAlts_nil Q k ρ J₂ c fs (some de'))
        refine (checkRewriteAlts_sim hcl hcall alts hm henv hJ hfsOk ha hu1 hdSim).congr
          (fun k => ?_) (fun k => ?_)
        · rw [eval_case, hx]; simp [Result.ofOption, hac]
        · rw [eval_case, hx, hcl.known]; simp [Result.ofOption, hac]
  | .ret a, _, _, rflow, env, _, ρ, J₁, J₂, _, _, e', henv, _, hck, _ => by
    simp only [checkRewriteExp] at hck
    split at hck
    · next hsub =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hck
      obtain ⟨rfl, rfl⟩ := hck
      cases ha : a.eval ρ with
      | none =>
        refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
        rw [eval_ret', ha]; rfl
      | some v =>
        obtain ⟨hv, hc⟩ := henv.atom ha
        refine (SimUpTo.ok ⟨rfl, hv, kabsSub_sound hsub hc⟩).congr (fun k => ?_) (fun k => ?_)
        · rw [eval_ret', ha]; rfl
        · rw [eval_ret', ha]; rfl
    · cases hck
  | .tick e, m, hm, rflow, env, jenv, ρ, J₁, J₂, _, _, e', henv, hJ, hck, hu => by
    simp only [checkRewriteExp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hck
    obtain ⟨⟨e1, st1⟩, he, rfl, rfl⟩ := hck
    refine (SimUpTo.later fun m' hm' =>
      checkRewriteExp_sim hcl hcall e (by omega) henv (hJ.mono (by omega)) he hu).congr
      (fun k => eval_tick P k ρ J₁ e) (fun k => eval_tick Q k ρ J₂ e1)
  | .trap, _, _, _, _, _, ρ, J₁, J₂, _, _, e', _, _, hck, _ => by
    simp only [checkRewriteExp, Option.some.injEq, Prod.mk.injEq] at hck
    obtain ⟨rfl, rfl⟩ := hck
    exact SimUpTo.trap.congr (fun k => eval_trap' P k ρ J₁) (fun k => eval_trap' Q k ρ J₂)

theorem checkRewriteAlts_sim {P Q : Program} {dc : DecCert} {S : GlobalId → Prop} {n : Nat}
    (hcl : Closed P Q dc S) (hcall : CallOk P Q dc S n) :
    ∀ (alts : List Alt) {m : Nat}, m ≤ n →
    ∀ {rflow : KAbs} {env : List KAbs} {jenv : List (List KAbs)}
      {ρ : List Val} {J₁ J₂ : List JClo} {c : Key.CtorKey} {fs : List Val}
      {st st1 : RwSt} {alts' : List Alt} {dflt dflt' : Option Exp},
    EnvOk dc env ρ → PlainJEnv P Q dc rflow m jenv J₁ J₂ →
    EnvOk dc (fieldFlows dc c fs.length) fs →
    checkRewriteAlts P dc rflow env jenv st alts = some (alts', st1) →
    (∀ h ∈ st1.used, S h) →
    SimUpTo (ValRel dc rflow) m
      (fun k => evalAlts P k ρ J₁ c fs [] dflt)
      (fun k => evalAlts Q k ρ J₂ c fs [] dflt') →
    SimUpTo (ValRel dc rflow) m
      (fun k => evalAlts P k ρ J₁ c fs alts dflt)
      (fun k => evalAlts Q k ρ J₂ c fs alts' dflt')
  | [], _, _, _, _, _, ρ, J₁, J₂, c, fs, _, _, alts', dflt, dflt', _, _, _, ha, _, hdSim => by
    simp only [checkRewriteAlts, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact hdSim
  | .mk key nf body :: rest, m, hm, rflow, env, jenv, ρ, J₁, J₂, c, fs, st, st1, alts',
      dflt, dflt', henv, hJ, hfsOk, ha, hu1, hdSim => by
    simp only [checkRewriteAlts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at ha
    obtain ⟨⟨b', stB⟩, hb, ⟨rest', stR⟩, hrest, rfl, rfl⟩ := ha
    have huB : ∀ h ∈ stB.used, S h := fun h hh => hu1 h (checkRewriteAlts_used_mono hrest h hh)
    by_cases hmatch : key = c ∧ nf = fs.length
    · obtain ⟨rfl, rfl⟩ := hmatch
      have henvb : EnvOk dc ((fieldFlows dc key fs.length).reverse ++ env) (fs.reverse ++ ρ) :=
        EnvOk.append (by simp [fieldFlows_length]) (hfsOk.reverse (fieldFlows_length dc key fs.length)) henv
      refine (checkRewriteExp_sim hcl hcall body hm henvb hJ hb huB).congr (fun k => ?_) (fun k => ?_)
      · rw [evalAlts_cons, if_pos ⟨rfl, rfl⟩]
      · rw [evalAlts_cons, if_pos ⟨rfl, rfl⟩]
    · refine (checkRewriteAlts_sim hcl hcall rest hm henv hJ hfsOk hrest hu1 hdSim).congr
        (fun k => ?_) (fun k => ?_)
      · rw [evalAlts_cons, if_neg hmatch]
      · rw [evalAlts_cons, if_neg hmatch]

end

/-! ## Clock induction and full refinement -/

theorem callOk_all {P Q : Program} {dc : DecCert} {S : GlobalId → Prop}
    (hcl : Closed P Q dc S) : ∀ n, CallOk P Q dc S n
  | 0 => CallOk.zero hcl
  | n + 1 => by
    have ih := callOk_all hcl n
    intro g gd hPg hact
    cases hdk : Walk.isDispatchKey gd.key with
    | false =>
      obtain ⟨gd', st', hQg, hps, hck, hu⟩ := hcl.nonDisp g gd hPg hdk
      refine ⟨fun hnil ρ => ?_, fun vs hvlen hvs => ?_⟩
      · have hnil' : gd'.ps = [] := by rw [hps, hnil]
        exact (SimUpTo.later fun m' hm' =>
          checkRewriteExp_sim hcl ih gd.body (by omega) (EnvOk.nil dc _) (PlainJEnv.nil P Q dc _ m') hck hu).congr
          (fun k => by rw [evalBind_glob, hPg]; simp [Result.ofOption, globVal, hnil])
          (fun k => by rw [evalBind_glob, hQg]; simp [Result.ofOption, globVal, hnil'])
      · have hpslen' : gd'.ps.length = gd.ps.length := by rw [hps]
        have henv : EnvOk dc (paramFlows P dc g gd.ps.length).reverse vs.reverse :=
          hvs.reverse (by rw [paramFlows_length, hvlen])
        exact (SimUpTo.later fun m' hm' =>
          checkRewriteExp_sim hcl ih gd.body (by omega) henv (PlainJEnv.nil P Q dc _ m') hck hu).congr
          (fun k => by simp [callVal, hvlen])
          (fun k => by rw [hQg]; simp [Result.ofOption, callVal, hpslen', hvlen])
    | true =>
      have hSg : S g := hact.elim (fun hf => by rw [hdk] at hf; cases hf) id
      obtain ⟨hQg, u, hck, hu⟩ := hcl.disp g gd hSg hPg hdk
      refine ⟨fun hnil ρ => ?_, fun vs hvlen hvs => ?_⟩
      · exact (SimUpTo.later fun m' hm' =>
          checkExpPlain_sim hcl ih (by omega) (EnvOk.nil dc _) (PlainJEnv.nil P Q dc _ m') hck hu).congr
          (fun k => by rw [evalBind_glob, hPg]; simp [Result.ofOption, globVal, hnil])
          (fun k => by rw [evalBind_glob, hQg]; simp [Result.ofOption, globVal, hnil])
      · have henv : EnvOk dc (paramFlows P dc g gd.ps.length).reverse vs.reverse :=
          hvs.reverse (by rw [paramFlows_length, hvlen])
        exact (SimUpTo.later fun m' hm' =>
          checkExpPlain_sim hcl ih (by omega) henv (PlainJEnv.nil P Q dc _ m') hck hu).congr
          (fun k => by simp [callVal, hvlen])
          (fun k => by rw [hQg]; simp [Result.ofOption, callVal, hvlen])

theorem applyN_valOk_sim {P Q : Program} {dc : DecCert} {rflow : KAbs} {n : Nat}
    {v w : Val} (hvw : ValRel dc rflow v w) (xs : List Val) :
    SimUpTo (fun a b => obsV a = obsV b) n
      (fun k => applyN P k v xs) (fun k => applyN Q k w xs) := by
  obtain ⟨rfl, hv, _⟩ := hvw
  cases xs with
  | nil =>
    exact (SimUpTo.ok (R := fun a b => obsV a = obsV b) (v := v) (w := v) rfl).congr
      (fun k => applyN_nil' P k v) (fun k => applyN_nil' Q k v)
  | cons x rest =>
    refine (SimUpTo.stuck _).congr (fun k => applyN_not_clos P k v x rest hv.not_clos) (fun _ => rfl)

theorem closed_refines {P Q : Program} {dc : DecCert} {S : GlobalId → Prop}
    (hcl : Closed P Q dc S) (hroots : Q.roots = P.roots) : Sem.Refines P Q := by
  refine Sem.Refines.of_sim (R := fun a b => obsV a = obsV b) (fun _ _ h => h)
    fun ⟨idx, ns⟩ => ⟨id, SimUpTo.sim fun n => ?_⟩
  show SimUpTo (fun a b => obsV a = obsV b) n (anfRun P (idx, ns)) (anfRun Q (idx, ns))
  unfold anfRun
  rw [hroots]
  cases hr : P.roots[idx]? with
  | none => exact SimUpTo.stuck _
  | some r =>
    dsimp only
    have hrMem : r ∈ P.roots := List.mem_of_getElem? hr
    have hSr : S r := hcl.roots r hrMem
    let xs : List Val := ns.map fun m => .lit (.nat m)
    change SimUpTo (fun a b => obsV a = obsV b) n (fun k => Anf.run P k r xs) (fun k => Anf.run Q k r xs)
    cases hPr : P.global? r with
    | none =>
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      rw [run_eq, evalBind_glob, hPr]; rfl
    | some gd =>
      have hcall := callOk_all hcl n
      cases hps : gd.ps with
      | nil =>
        have hcaf := (hcall r gd hPr (.inr hSr)).1 hps []
        refine (SimUpTo.bind (evalBind_mono Q [] (.glob r)) (fun w => applyN_mono Q w xs) hcaf
          fun v w hvw => applyN_valOk_sim hvw xs).congr
          (fun k => run_eq P k r xs) (fun k => run_eq Q k r xs)
      | cons bm bms =>
        have hQgd : ∃ gd', Q.global? r = some gd' ∧ gd'.ps.length = (bm :: bms).length := by
          cases hdk : Walk.isDispatchKey gd.key with
          | false =>
            obtain ⟨gd', _, hQg, hps', _, _⟩ := hcl.nonDisp r gd hPr hdk
            exact ⟨gd', hQg, by rw [hps', hps]⟩
          | true =>
            obtain ⟨hQg, _⟩ := hcl.disp r gd hSr hPr hdk
            exact ⟨gd, hQg, by rw [hps]⟩
        obtain ⟨gd', hQr, hpslen'⟩ := hQgd
        have hpsEq : gd'.ps.length = gd.ps.length := by rw [hpslen', ← hps]
        cases hps' : gd'.ps with
        | nil => simp [hps'] at hpslen'
        | cons bm' bms' =>
          cases hxs : xs with
          | nil =>
            refine (SimUpTo.ok (v := Val.clos [] gd.ps.length gd.body [])
              (w := Val.clos [] gd'.ps.length gd'.body []) rfl).congr (fun k => ?_) (fun k => ?_)
            · rw [run_eq, evalBind_glob, hPr]; simp [Result.ofOption, globVal, hps, applyN_nil']
            · rw [run_eq, evalBind_glob, hQr]; simp [Result.ofOption, globVal, hps', applyN_nil']
          | cons x0 xrest =>
            have hlt0 : 0 < gd.ps.length := by simp [hps]
            have hlt0' : 0 < gd'.ps.length := by simp [hps']
            by_cases hunder : (x0 :: xrest).length < gd.ps.length
            · have hunder' : (x0 :: xrest).length < gd'.ps.length := by
                rw [hpsEq]; exact hunder
              have hlt : xrest.length < bms.length := by simp [hps] at hunder; omega
              have hlt' : xrest.length < bms'.length := by simp [hps'] at hunder'; omega
              refine (SimUpTo.later fun _ _ => SimUpTo.ok
                (v := Val.clos [] gd.ps.length gd.body (x0 :: xrest))
                (w := Val.clos [] gd'.ps.length gd'.body (x0 :: xrest)) rfl).congr
                (fun k => ?_) (fun k => ?_)
              · rw [run_eq, evalBind_glob, hPr]
                simp [Result.ofOption, globVal, hps, applyN_clos, hlt]
              · rw [run_eq, evalBind_glob, hQr]
                simp [Result.ofOption, globVal, hps', applyN_clos, hlt']
            · have hunder' : ¬ (x0 :: xrest).length < gd'.ps.length := by
                rw [hpsEq]; exact hunder
              let takeVs : List Val := (x0 :: xrest).take gd.ps.length
              let dropVs : List Val := (x0 :: xrest).drop gd.ps.length
              have htakeLen : takeVs.length = gd.ps.length := by
                simp only [takeVs, List.length_take]; omega
              have htakeEq : (x0 :: xrest).take gd'.ps.length = takeVs := by
                simp only [takeVs, hpsEq]
              have hdropEq : (x0 :: xrest).drop gd'.ps.length = dropVs := by
                simp only [dropVs, hpsEq]
              have htakeOk : EnvOk dc (paramFlows P dc r gd.ps.length) takeVs := by
                have hxsLit : ∀ v ∈ xs, ∃ m, v = .lit (.nat m) := by
                  intro v hv
                  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hv
                  exact ⟨m, rfl⟩
                intro i v hi
                have hvMem : v ∈ takeVs := List.mem_of_getElem? hi
                have hvInXs : v ∈ xs := by rw [hxs]; exact List.mem_of_mem_take hvMem
                obtain ⟨m, rfl⟩ := hxsLit v hvInXs
                exact ⟨.lit (.nat m), ClosOk.lit _ _⟩
              have hnlt : ¬ xrest.length < bms.length := by simp [hps] at hunder; omega
              have hnlt' : ¬ xrest.length < bms'.length := by simp [hps'] at hunder'; omega
              have htk : (x0 :: xrest).take (bms.length + 1) = takeVs := by simp [takeVs, hps]
              have hdr : (x0 :: xrest).drop (bms.length + 1) = dropVs := by simp [dropVs, hps]
              have htk' : (x0 :: xrest).take (bms'.length + 1) = takeVs := by
                rw [← htakeEq, hps']; rfl
              have hdr' : (x0 :: xrest).drop (bms'.length + 1) = dropVs := by
                rw [← hdropEq, hps']; rfl
              refine (SimUpTo.later
                (c₁ := fun k => (eval P k takeVs.reverse [] gd.body).bind fun v => applyN P (k + 1) v dropVs)
                (c₂ := fun k => (eval Q k takeVs.reverse [] gd'.body).bind fun v => applyN Q (k + 1) v dropVs)
                fun m' hm' => ?_).congr (fun k => ?_) (fun k => ?_)
              · -- Evaluate body at m' via callOk_all at m' + 1
                have hbodySim : SimUpTo (ValRel dc (retFlow dc r)) m'
                    (fun k => eval P k takeVs.reverse [] gd.body)
                    (fun k => eval Q k takeVs.reverse [] gd'.body) := by
                  have hcm := callOk_all hcl m'
                  cases hdk : Walk.isDispatchKey gd.key with
                  | false =>
                    obtain ⟨gd1, st', hQ1, _, hck, hu⟩ := hcl.nonDisp r gd hPr hdk
                    rw [hQr, Option.some.injEq] at hQ1; subst hQ1
                    exact checkRewriteExp_sim hcl hcm gd.body (Nat.le_refl m')
                      (htakeOk.reverse (by rw [paramFlows_length, htakeLen]))
                      (PlainJEnv.nil P Q dc _ m') hck hu
                  | true =>
                    obtain ⟨hQ1, u, hck, hu⟩ := hcl.disp r gd hSr hPr hdk
                    rw [hQr, Option.some.injEq] at hQ1; subst hQ1
                    exact checkExpPlain_sim hcl hcm (Nat.le_refl m')
                      (htakeOk.reverse (by rw [paramFlows_length, htakeLen]))
                      (PlainJEnv.nil P Q dc _ m') hck hu
                refine SimUpTo.bind (eval_mono Q takeVs.reverse [] gd'.body)
                  (fun w _ _ h => applyN_mono Q w dropVs (Nat.succ_le_succ h))
                  hbodySim fun v w hvw => ?_
                obtain ⟨rfl, hv, _⟩ := hvw
                cases hdrop : dropVs with
                | nil =>
                  exact (SimUpTo.ok (R := fun a b => obsV a = obsV b) (v := v) (w := v) rfl).congr
                    (fun k => applyN_nil' P (k + 1) v)
                    (fun k => applyN_nil' Q (k + 1) v)
                | cons d0 drest =>
                  refine (SimUpTo.stuck _).congr
                    (fun k => applyN_not_clos P (k + 1) v d0 drest hv.not_clos) (fun _ => rfl)
              · rw [run_eq, evalBind_glob, hPr]
                simp only [Result.ofOption, Result.bind_ok, globVal, hps, List.length_cons,
                  applyN_clos, List.length_nil, Nat.zero_lt_succ, ↓reduceIte, Nat.zero_add,
                  Nat.add_lt_add_iff_right, hnlt, enter, List.nil_append, List.append_nil, htk, hdr]
              · rw [run_eq, evalBind_glob, hQr]
                simp only [Result.ofOption, Result.bind_ok, globVal, hps', List.length_cons,
                  applyN_clos, List.length_nil, Nat.zero_lt_succ, ↓reduceIte, Nat.zero_add,
                  Nat.add_lt_add_iff_right, hnlt', enter, List.nil_append, List.append_nil, htk', hdr']

/-- **P9 is unconditionally sound for any certificate `c`**: `Narrow.run c P`
preserves `WF` and refines `P` on all inputs. -/
theorem run_refines {c : Cert} {P : Program} (hw : P.WF) :
    (run c P).WF ∧ Sem.Refines P (run c P) := by
  rcases run_spec (c := c) hw with h | ⟨_, hw', _, hcl⟩
  · rw [h]; exact ⟨hw, Sem.Refines.refl P⟩
  · exact ⟨hw', closed_refines hcl (run_tables c P).2.2⟩

end IxCC.Anf.Defun.Narrow.Proof
