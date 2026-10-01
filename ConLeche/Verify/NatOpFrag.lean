module

public import ConLeche.Verify.Denote.SubstConst

public section

/-!
# The pinned-`Nat` recurrence fragment (V-free)

`natOpEquations`' equation sides live in a four-constructor grammar —
`sort`, the two `Nat`-annotated free variables, resolving constants,
and application — and `natOpGuard` pins exactly the constants that
grammar admits.

**Why this is here and not in a lane.**  Both soundness routes need
the characterisation and neither may import the other
(`ConLeche/SetR/*` must not see `ConLeche/TTVerify/*`; the two routes are
independent by design).  Every statement below mentions only `Env`,
`Expr` and the kernel's own `natOp*` data, so the shared tier is where
it belongs — task #148 T6's relocation, at the rule's stated
threshold: a second consumer and nothing lane-specific in the
statement.

The one piece that stays in the TT lane is `natFrag_subst_facts`,
which is stated over an `EnvTT`.
-/

-- the namespace follows the house convention of the other shared-tier
-- files that the TT lane grew into (`Verify/Denote/SubstConst.lean`
-- is `ConLeche/Verify/*` in `ConLeche.Verify` too), so nothing
-- downstream re-qualifies
namespace ConLeche.Verify

open ConLeche.Term

variable {env : Env}

/-- The syntactic fragment the pinned `Nat` equations live in: spines
over resolving constants (the operation `c` itself, level-free, or any
stored constant applied to as many levels as it declares) and the two
frame variables `x`, `y`, annotated by `Nat`.

Shared with the div/mod certificates (`ConLeche/TTVerify/DivModPin.lean`),
whose statements are the same shape but mention `Eq.{1}` — which is why
the constant clause counts levels instead of demanding none. -/
@[expose] def natFragOk (env : Env) (c : Name) : Expr → Bool
  | .sort _ => true
  | .fvar i ty =>
    (decide (i = 0) || decide (i = 1)) && (ty == .const natName [])
  | .const n us => (decide (n = c) && us.isEmpty) ||
      (match env.find? n with
       | some ci => us.length == ci.toConstantVal.levelParams.length
       | none => false)
  | .app f a => natFragOk env c f && natFragOk env c a
  | _ => false

/-- A fragment expression is shallow, so `substConst0` is faithful on
it. -/
theorem shallowE_of_natFragOk {env : Env} {c : Name} :
    ∀ {e : Expr}, natFragOk env c e = true → shallowE e = true
  | .sort _, _ => rfl
  | .fvar _ _, _ => rfl
  | .const _ _, _ => rfl
  | .app f a, h => by
    simp only [natFragOk, Bool.and_eq_true] at h
    simp only [shallowE, Bool.and_eq_true]
    exact ⟨shallowE_of_natFragOk h.1, shallowE_of_natFragOk h.2⟩
  | .bvar _, h | .lam _ _ _, h | .forallE _ _ _, h
  | .letE _ _ _, h | .proj _ _ _, h | .lit _, h => by
    simp [natFragOk] at h

/-! ## The equations are in the fragment

Seven operations carry recurrences (`natOpEquations` is `[]` for the
WF-recursive family, so their obligation is vacuous), and each mentions
exactly the constants the guard pins. -/

/-- A constant is stored at empty level parameters. -/
def storedNoLevels (env : Env) (n : Name) : Prop :=
  (match env.find? n with
   | some ci => ci.toConstantVal.levelParams.isEmpty
   | none => false) = true

theorem natFragOk_const {env : Env} {c n : Name}
    (h : storedNoLevels env n) : natFragOk env c (.const n []) = true := by
  simp only [natFragOk, Bool.or_eq_true]
  refine Or.inr ?_
  unfold storedNoLevels at h
  revert h
  cases env.find? n with
  | none => intro h; exact nomatch h
  | some ci =>
    intro h
    rw [List.isEmpty_iff] at h
    simp [h]

theorem natFragOk_self {env : Env} {c : Name} :
    natFragOk env c (.const c []) = true := by
  simp [natFragOk]

/-- Both sides of every recurrence lie in the fragment. -/
theorem natOpEquations_frag {env : Env} {c : Name}
    (hz : storedNoLevels env natZeroName)
    (hs : storedNoLevels env natSuccName)
    (hdep : ∀ n ∈ natOpDeps c, n ≠ c → storedNoLevels env n)
    (hbT : c = natBeqName ∨ c = natBleName → storedNoLevels env boolTrueName)
    (hbF : c = natBeqName ∨ c = natBleName →
      storedNoLevels env boolFalseName) :
    ∀ eq ∈ natOpEquations 0 c,
      natFragOk env c eq.1 = true ∧ natFragOk env c eq.2 = true := by
  have hx : natFragOk env c
      (.fvar 0 (.const natName [])) = true := by
    simp [natFragOk]
  have hy : natFragOk env c
      (.fvar 1 (.const natName [])) = true := by
    simp [natFragOk]
  have happ : ∀ f a, natFragOk env c f = true → natFragOk env c a = true →
      natFragOk env c (.app f a) = true := by
    intro f a h1 h2; simp [natFragOk, h1, h2]
  have hzc := natFragOk_const (c := c) hz
  have hsc := natFragOk_const (c := c) hs
  have hself : natFragOk env c (.const c []) = true := natFragOk_self
  unfold natOpEquations
  split
  · next hc =>
    intro eq hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact ⟨happ _ _ hself hzc, hzc⟩
    · rcases List.mem_cons.mp hq' with rfl | hq''
      · exact ⟨happ _ _ hself (happ _ _ hsc hx), hx⟩
      · exact nomatch hq''
  · split
    · next hc =>
      intro eq hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨happ _ _ (happ _ _ hself hx) hzc, hx⟩
      · rcases List.mem_cons.mp hq' with rfl | hq''
        · exact ⟨happ _ _ (happ _ _ hself hx) (happ _ _ hsc hy),
            happ _ _ hsc (happ _ _ (happ _ _ hself hx) hy)⟩
        · exact nomatch hq''
    · split
      · next hc =>
        intro eq hq
        have hdc := natFragOk_const (c := c)
          (hdep natPredName (by subst hc; decide) (by subst hc; decide))
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact ⟨happ _ _ (happ _ _ hself hx) hzc, hx⟩
        · rcases List.mem_cons.mp hq' with rfl | hq''
          · exact ⟨happ _ _ (happ _ _ hself hx) (happ _ _ hsc hy),
              happ _ _ hdc (happ _ _ (happ _ _ hself hx) hy)⟩
          · exact nomatch hq''
      · split
        · next hc =>
          intro eq hq
          have hdc := natFragOk_const (c := c)
            (hdep natAddName (by subst hc; decide) (by subst hc; decide))
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact ⟨happ _ _ (happ _ _ hself hx) hzc, hzc⟩
          · rcases List.mem_cons.mp hq' with rfl | hq''
            · exact ⟨happ _ _ (happ _ _ hself hx) (happ _ _ hsc hy),
                happ _ _ (happ _ _ hdc
                  (happ _ _ (happ _ _ hself hx) hy)) hx⟩
            · exact nomatch hq''
        · split
          · next hc =>
            intro eq hq
            have hdc := natFragOk_const (c := c)
              (hdep natMulName (by subst hc; decide) (by subst hc; decide))
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact ⟨happ _ _ (happ _ _ hself hx) hzc, happ _ _ hsc hzc⟩
            · rcases List.mem_cons.mp hq' with rfl | hq''
              · exact ⟨happ _ _ (happ _ _ hself hx) (happ _ _ hsc hy),
                  happ _ _ (happ _ _ hdc
                    (happ _ _ (happ _ _ hself hx) hy)) hx⟩
              · exact nomatch hq''
          · split
            · next hc =>
              intro eq hq
              have hT := natFragOk_const (c := c) (hbT (Or.inl hc))
              have hF := natFragOk_const (c := c) (hbF (Or.inl hc))
              rcases List.mem_cons.mp hq with rfl | hq'
              · exact ⟨happ _ _ (happ _ _ hself hzc) hzc, hT⟩
              · rcases List.mem_cons.mp hq' with rfl | hq'
                · exact ⟨happ _ _ (happ _ _ hself hzc) (happ _ _ hsc hy), hF⟩
                · rcases List.mem_cons.mp hq' with rfl | hq'
                  · exact ⟨happ _ _ (happ _ _ hself (happ _ _ hsc hx)) hzc,
                      hF⟩
                  · rcases List.mem_cons.mp hq' with rfl | hq'
                    · exact ⟨happ _ _ (happ _ _ hself (happ _ _ hsc hx))
                        (happ _ _ hsc hy),
                        happ _ _ (happ _ _ hself hx) hy⟩
                    · exact nomatch hq'
            · split
              · next hc =>
                intro eq hq
                have hT := natFragOk_const (c := c) (hbT (Or.inr hc))
                have hF := natFragOk_const (c := c) (hbF (Or.inr hc))
                rcases List.mem_cons.mp hq with rfl | hq'
                · exact ⟨happ _ _ (happ _ _ hself hzc) hy, hT⟩
                · rcases List.mem_cons.mp hq' with rfl | hq'
                  · exact ⟨happ _ _ (happ _ _ hself (happ _ _ hsc hx)) hzc,
                      hF⟩
                  · rcases List.mem_cons.mp hq' with rfl | hq'
                    · exact ⟨happ _ _ (happ _ _ hself (happ _ _ hsc hx))
                        (happ _ _ hsc hy),
                        happ _ _ (happ _ _ hself hx) hy⟩
                    · exact nomatch hq'
              · intro eq hq; exact nomatch hq

/-! ## The guard delivers exactly those facts -/

theorem storedNoLevels_exists {env : Env} {n : Name}
    (h : storedNoLevels env n) :
    ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = [] := by
  unfold storedNoLevels at h
  cases hf : env.find? n with
  | none => rw [hf] at h; exact nomatch h
  | some ci => rw [hf] at h; exact ⟨ci, rfl, by simpa [List.isEmpty_iff] using h⟩

theorem storedNoLevels_of_cons {env : Env} {ci : ConstantInfo} {c n : Name}
    (hname : ci.name = c) (hne : n ≠ c)
    (h : storedNoLevels ⟨ci :: env.consts⟩ n) : storedNoLevels env n := by
  unfold storedNoLevels at h ⊢
  rwa [Env.find?_cons, if_neg (by rw [hname]; exact Ne.symm hne)] at h

/-- A name that occurs in no `natOpNames` entry differs from the
operation being installed. -/
theorem ne_of_mem_natOpNames {n c : Name}
    (h : natOpNames.all (fun x => n != x) = true) (hc : c ∈ natOpNames) :
    n ≠ c := fun hh => by
  have := List.all_eq_true.mp h c hc
  rw [hh] at this; simp at this

theorem storedNoLevels_of_ctorOk {env : Env} {n : Name}
    (h : natZeroOk (env.find? n) = true ∨ natSuccOk (env.find? n) = true) :
    storedNoLevels env n := by
  unfold storedNoLevels
  rcases h with h | h
  · unfold natZeroOk at h
    split at h
    · next _ _ _ hfd =>
      rw [hfd]; exact (Bool.and_eq_true _ _ ▸ h : _ ∧ _).1
    · exact nomatch h
  · unfold natSuccOk at h
    split at h
    · next _ _ _ hfd =>
      rw [hfd]; exact (Bool.and_eq_true _ _ ▸ h : _ ∧ _).1
    · exact nomatch h

/-- The guard's three clauses, as the fragment lemma wants them. -/
theorem natOpGuard_stored {env : Env} {c : Name}
    (h : natOpGuard env c = true) :
    storedNoLevels env natName ∧ storedNoLevels env natZeroName ∧
    storedNoLevels env natSuccName ∧
    (∀ n ∈ natOpDeps c, storedNoLevels env n) ∧
    ((decide (c = natBeqName) || decide (c = natBleName) ||
        natDivModNames.contains c) = true →
      storedNoLevels env boolTrueName ∧ storedNoLevels env boolFalseName) := by
  simp only [natOpGuard, Bool.and_eq_true] at h
  obtain ⟨⟨hlit, hdeps⟩, hbool⟩ := h
  simp only [natLitSupported, Bool.and_eq_true] at hlit
  obtain ⟨⟨hind, hzero⟩, hsucc⟩ := hlit
  refine ⟨?_, storedNoLevels_of_ctorOk (Or.inl hzero),
    storedNoLevels_of_ctorOk (Or.inr hsucc), ?_, ?_⟩
  · unfold storedNoLevels
    unfold natIndOk at hind
    split at hind
    · next _ _ hfd =>
      rw [hfd]; exact (Bool.and_eq_true _ _ ▸ hind : _ ∧ _).1
    · exact nomatch hind
  · intro n hn
    have hd := List.all_eq_true.mp hdeps n hn
    unfold storedNoLevels
    split at hd
    · next _ _ _ hfd => rw [hfd]; exact hd
    · exact nomatch hd
  · intro hc
    rw [if_pos hc] at hbool
    simp only [Bool.and_eq_true] at hbool
    exact ⟨hbool.1, hbool.2⟩


end ConLeche.Verify
