module

public import ConLeche.Verify.Inductives.StructResid
public import ConLeche.Verify.ProjTele
import ConLeche.Verify.Cached.Erase

public section

/-!
# The projection bodies, opened (task #175 S1)

The direct install's table stores `bodies[i] = F_i[p⃗ ↦ bvars, f_j ↦
.proj T j (bvar 0)]` (`structProjBodies`, the domain of field `i` of
the constructor telescope peeled at the loose parameter variables and
the earlier projections of the subject — `structProjResidP`).  The
reading side opens a body at fresh variables (`projTele`'s reading),
and what it needs is the syntactic identity between that opened body
and the constructor telescope peeled at the **variables** themselves:

    instSpine (fvsD nP ++ [tfvD nP]) nP bodies[i]
      = the domain of `instPisAt (fvsD nP ++ projArgsD T i nP) cty`

(`structProjBody_open`).  It is `instSeq_instSeqLift` — the collapse
of a capture-avoiding instantiation at open arguments followed by a
closed instantiation of the ambient variables into the plain
instantiation at the already-instantiated arguments — applied to the
raw binder domain, with `instPisAtLift_head`/`instPisAt_head`
identifying the two walks' head domains.
-/

namespace ConLeche

open Expr

/-! ## The plain peel's head (the `instantiate1` twin of
`instPisAtLift_head`) -/

theorem stripPis_instantiate1_full {v : Expr} :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr} (j : Nat),
      e.stripPis k = some (bs, body) →
      ∃ bs', (e.instantiate1 v j).stripPis k =
          some (bs', body.instantiate1 v (j + k)) ∧
        ∀ (i : Nat) (b : Expr × BinderMeta), bs[i]? = some b →
          bs'[i]? = some (b.1.instantiate1 v (j + i), b.2) := by
  intro k
  induction k with
  | zero =>
    intro e bs body j h
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [stripPis], fun i b hb => by simp at hb⟩
  | succ k ih =>
    intro e bs body j h
    match e, h with
    | .forallE d bo m, h =>
      simp only [stripPis] at h
      cases hs : bo.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hb, hbody⟩ : (d, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbody
        obtain ⟨bs', h1, h2⟩ := ih (j + 1) (by rw [hs])
        refine ⟨(d.instantiate1 v j, m) :: bs', ?_, ?_⟩
        · simp only [instantiate1, stripPis, h1,
            show j + 1 + k = j + (k + 1) from by omega, Option.map_some]
        · intro i b hbi
          rw [← hb] at hbi
          cases i with
          | zero =>
            obtain rfl : (d, m) = b := by simpa using hbi
            rfl
          | succ i =>
            simp only [List.getElem?_cons_succ] at hbi ⊢
            rw [show j + (i + 1) = j + 1 + i from by omega]
            exact h2 i b hbi

/-- The head binder of a partial plain `∀`-instantiation walk,
characterized by the raw telescope's binder list. -/
theorem instPisAt_head :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr} {mrem : Nat}
      {bs : List (Expr × BinderMeta)} {body : Expr}
      {b : Expr × BinderMeta},
      Expr.instPisAt args e = some (ds, rest) →
      e.stripPis (args.length + (mrem + 1)) = some (bs, body) →
      bs[args.length]? = some b →
      ∃ bodyR, rest = .forallE
        (instSeq args (args.length - 1) b.1) bodyR b.2 := by
  intro args
  induction args with
  | nil =>
    intro e ds rest mrem bs body b h hstrip hb
    simp only [instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [show [].length + (mrem + 1) = mrem + 1 from by simp] at hstrip
    match e, hstrip with
    | .forallE d bo m, hstrip =>
      simp only [stripPis] at hstrip
      cases hs : bo.stripPis mrem with
      | none => rw [hs] at hstrip; exact nomatch hstrip
      | some p =>
        rw [hs] at hstrip
        simp only [Option.map_some, Option.some.injEq] at hstrip
        obtain ⟨hbs, -⟩ : (d, m) :: p.1 = bs ∧ p.2 = body := by
          cases hstrip; exact ⟨rfl, rfl⟩
        rw [← hbs] at hb
        obtain rfl : (d, m) = b := by simpa using hb
        exact ⟨bo, rfl⟩
  | cons a as ih =>
    intro e ds rest mrem bs body b h hstrip hb
    match e, h with
    | .forallE d bo m, h =>
      simp only [instPisAt, Option.map_eq_some_iff] at h
      obtain ⟨⟨ds', rest'⟩, h', heq⟩ := h
      obtain ⟨-, rfl⟩ : d :: ds' = ds ∧ rest' = rest := by simpa using heq
      rw [show (a :: as).length + (mrem + 1) =
        (as.length + (mrem + 1)) + 1 from by simp; omega] at hstrip
      simp only [stripPis] at hstrip
      cases hs : bo.stripPis (as.length + (mrem + 1)) with
      | none => rw [hs] at hstrip; exact nomatch hstrip
      | some q =>
        rw [hs] at hstrip
        simp only [Option.map_some, Option.some.injEq] at hstrip
        obtain ⟨hbs, -⟩ : (d, m) :: q.1 = bs ∧ q.2 = body := by
          cases hstrip; exact ⟨rfl, rfl⟩
        rw [← hbs] at hb
        simp only [List.length_cons, List.getElem?_cons_succ] at hb
        obtain ⟨bs', hstrip', hpos⟩ :=
          stripPis_instantiate1_full (v := a) (as.length + (mrem + 1)) 0 hs
        obtain ⟨bodyR, hhead⟩ := ih (b := (b.1.instantiate1 a as.length,
            b.2)) h' hstrip'
          (by rw [hpos as.length b hb]; simp)
        exact ⟨bodyR, by rw [hhead]; rfl⟩

/-! ## Instantiation sequences at bounded cuts -/

/-- An instantiation sequence whose every cut is at or above the
subject's loose-variable bound is the identity. -/
theorem instSeq_eq_self_of_bounded :
    ∀ (args : List Expr) (t : Nat) {e : Expr} {k : Nat},
      e.looseBVarsBounded k = true → k + args.length ≤ t + 1 →
      instSeq args t e = e := by
  intro args
  induction args with
  | nil => intro t e k _ _; rfl
  | cons a as ih =>
    intro t e k hb hle
    show instSeq as (t - 1) (e.instantiate1 a t) = e
    rw [instantiate1_eq_self (looseBVarsBounded_mono
      (by simp only [List.length_cons] at hle; omega) hb)]
    exact ih (t - 1) hb (by simp only [List.length_cons] at hle; omega)

theorem instSeq_proj :
    ∀ (args : List Expr) (t : Nat) (s : Name) (j : Nat) (e : Expr),
      instSeq args t (.proj s j e) = .proj s j (instSeq args t e)
  | [], _, _, _, _ => rfl
  | a :: as, t, s, j, e => by
    show instSeq as (t - 1) (.proj s j (e.instantiate1 a t)) = _
    rw [instSeq_proj as]
    rfl

/-- A stripped telescope's binder domains are bounded at their own
depth. -/
theorem stripPis_binder_bounded :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr} {j : Nat},
      e.stripPis k = some (bs, body) → e.looseBVarsBounded j = true →
      ∀ (i : Nat) (b : Expr × BinderMeta), bs[i]? = some b →
        b.1.looseBVarsBounded (j + i) = true := by
  intro k
  induction k with
  | zero =>
    intro e bs body j h _ i b hb
    simp only [stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hb
    simp at hb
  | succ k ih =>
    intro e bs body j h hb i b hbi
    match e, h with
    | .forallE ty bo m, h =>
      simp only [stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hbstrip, heq⟩ := h
      obtain ⟨rfl, -⟩ : (ty, m) :: bs' = bs ∧ body' = body := by
        simpa using heq
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      cases i with
      | zero =>
        obtain rfl : (ty, m) = b := by simpa using hbi
        simpa using hb.1
      | succ i =>
        simp only [List.getElem?_cons_succ] at hbi
        have := ih hbstrip hb.2 i b hbi
        rw [show j + 1 + i = j + (i + 1) from by omega] at this
        exact this

/-! ## The generator -/

theorem structProjBodiesGo_spec (T : Name) :
    ∀ (k i : Nat) (r : Expr) (bs : List Expr),
      structProjBodiesGo T k i r = some bs →
      bs.length = k ∧
      ∀ j, j < k → ∃ b' mb,
        ((List.range j).foldl
            (fun acc jj => acc.bind (Expr.instPisAtLift [structProjArgP T (i + jj)]))
            (some r))
          = some (.forallE (bs.getD j default) b' mb)
  | 0, i, r, bs, h => by
    simp only [structProjBodiesGo, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | k + 1, i, r, bs, h => by
    match r, h with
    | .forallE fdom body mb, h =>
      simp only [structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨bs', hrec, rfl⟩ := h
      obtain ⟨hlen, hrest⟩ := structProjBodiesGo_spec T k (i + 1) _ bs' hrec
      refine ⟨by simp [hlen], fun j hj => ?_⟩
      cases j with
      | zero => exact ⟨body, mb, rfl⟩
      | succ j =>
        obtain ⟨b', mb', hj'⟩ := hrest j (by omega)
        refine ⟨b', mb', ?_⟩
        rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
        simp only [List.getD_cons_succ, Option.bind_some, Expr.instPisAtLift,
          Nat.add_zero]
        rw [← hj']
        congr 1
        funext acc jj
        rw [show i + (jj + 1) = i + 1 + jj from by omega]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      exact nomatch h

/-- **The bodies are the peel's domains**: body `i` is the head domain
of the constructor telescope peeled at the loose parameters and the
first `i` subject projections (`structProjResidP`), and there is one
per field. -/
theorem structProjBodies_spec {T : Name} {nP nF : Nat} {cty : Expr}
    {bodies : Array Expr} (h : structProjBodies T nP nF cty = some bodies) :
    bodies.size = nF ∧
    ∀ i, i < nF → ∃ b' mb,
      structProjResidP T nP cty i
        = some (.forallE (bodies.getD i default) b' mb) := by
  unfold structProjBodies at h
  cases hr : Expr.instPisAtLift (structProjPs nP) cty with
  | none => rw [hr] at h; exact nomatch h
  | some r =>
    rw [hr] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨bs, hgo, rfl⟩ := h
    obtain ⟨hlen, hspec⟩ := structProjBodiesGo_spec T nF 0 r bs hgo
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    obtain ⟨b', mb, hfold⟩ := hspec i hi
    refine ⟨b', mb, ?_⟩
    have hgetD : bs.toArray.getD i default = bs.getD i default := by
      simp [Array.getD, List.getD_eq_getElem?_getD]
      split <;> simp_all
    rw [hgetD, ← hfold]
    clear hfold hgetD hspec hlen hgo
    -- the incremental residual is the fold of the single-step peels
    induction i with
    | zero => simp [structProjResidP, hr]
    | succ i ih =>
      rw [structProjResidP, ih (by omega), List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, Nat.zero_add]

/-! ## The opened body -/

/-- The parameter variables, dummy-annotated (the reading ignores
annotations). -/
@[expose] def fvsD (nP : Nat) : List Expr :=
  (List.range nP).map fun k => Expr.fvar k (.sort .zero)

/-- The subject variable. -/
@[expose] def tfvD (nP : Nat) : Expr := Expr.fvar nP (.sort .zero)

/-- The earlier projections of the subject variable. -/
@[expose] def projArgsD (T : Name) (i nP : Nat) : List Expr :=
  (List.range i).map fun j => Expr.proj T j (tfvD nP)

theorem fvsD_length (nP : Nat) : (fvsD nP).length = nP := by simp [fvsD]

theorem projArgsD_length (T : Name) (i nP : Nat) : (projArgsD T i nP).length = i := by
  simp [projArgsD]

theorem fvsD_closed (nP : Nat) : ∀ a ∈ fvsD nP ++ [tfvD nP], a.looseBVarsBounded 0 = true := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; rfl
  · rw [List.mem_singleton] at ha; subst ha; rfl

theorem fvsD_getElem? (nP k : Nat) (hk : k < nP) :
    (fvsD nP)[k]? = some (Expr.fvar k (.sort .zero)) := by
  simp [fvsD, List.getElem?_map, List.getElem?_range hk]

/-- The loose parameter variables and projection substitutes are
bounded at the parameters and the subject. -/
theorem structProjArgs_bounded (T : Name) (nP i : Nat) :
    ∀ a ∈ structProjPs nP ++ (List.range i).map (structProjArgP T),
      a.looseBVarsBounded (nP + 1) = true := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    have := List.mem_range.mp hk
    simp only [looseBVarsBounded, decide_eq_true_eq]
    omega
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
    rfl

/-- Instantiating the loose parameter variables and projection
substitutes at the variables gives the variables and their
projections. -/
theorem structProjArgs_instSeq (T : Name) (nP i : Nat) :
    (structProjPs nP ++ (List.range i).map (structProjArgP T)).map
        (instSeq (fvsD nP ++ [tfvD nP]) nP)
      = fvsD nP ++ projArgsD T i nP := by
  have hclosed := fvsD_closed nP
  have hlen : (fvsD nP ++ [tfvD nP]).length = nP + 1 := by simp [fvsD_length]
  -- the variable at each slot
  have hget : ∀ k, k < nP + 1 →
      (fvsD nP ++ [tfvD nP])[k]? = some (Expr.fvar k (.sort .zero)) := by
    intro k hk
    rcases Nat.lt_or_ge k nP with hk' | hk'
    · rw [List.getElem?_append_left (by rw [fvsD_length]; exact hk')]
      exact fvsD_getElem? nP k hk'
    · obtain rfl : k = nP := by omega
      rw [List.getElem?_append_right (by rw [fvsD_length]; exact Nat.le_refl _),
        fvsD_length, Nat.sub_self]
      rfl
  have hbvar : ∀ j, j ≤ nP →
      instSeq (fvsD nP ++ [tfvD nP]) nP (.bvar j)
        = Expr.fvar (nP - j) (.sort .zero) := by
    intro j hj
    have := instSeq_bvar (fvsD nP ++ [tfvD nP]) nP j hclosed hj (by rw [hlen]; omega)
    rw [hget (nP - j) (by omega)] at this
    exact (Option.some.inj this).symm
  rw [List.map_append]
  congr 1
  · show (structProjPs nP).map (instSeq (fvsD nP ++ [tfvD nP]) nP)
      = (List.range nP).map (fun k => Expr.fvar k (.sort .zero))
    unfold structProjPs
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    show instSeq (fvsD nP ++ [tfvD nP]) nP (.bvar (nP - k)) = _
    rw [hbvar (nP - k) (by omega), show nP - (nP - k) = k from by omega]
  · show ((List.range i).map (structProjArgP T)).map (instSeq (fvsD nP ++ [tfvD nP]) nP)
      = (List.range i).map (fun j => Expr.proj T j (tfvD nP))
    rw [List.map_map]
    apply List.map_congr_left
    intro j _
    show instSeq (fvsD nP ++ [tfvD nP]) nP (.proj T j (.bvar 0)) = _
    rw [instSeq_proj, hbvar 0 (Nat.zero_le _), Nat.sub_zero]
    rfl

/-- **The body, opened at the variables, is the variable peel's
domain** (task #175 S1): instantiating body `i` at the parameter and
subject variables (the reading's opening of `projTele`) is the head
domain of the constructor telescope instantiated at the variables and
the subject's earlier projections — the fvar-side peel the readings
already know how to read. -/
theorem structProjBody_open {T : Name} {nP nF : Nat} {cty : Expr}
    {bodies : Array Expr} (h : structProjBodies T nP nF cty = some bodies)
    (hstrip : (cty.stripPis (nP + nF)).isSome = true)
    (hcl : cty.looseBVarsBounded 0 = true) {i : Nat} (hi : i < nF) :
    ∃ (cds : List Expr) (bodyC : Expr) (mb : BinderMeta),
      Expr.instPisAt (fvsD nP ++ projArgsD T i nP) cty
        = some (cds, .forallE
            (Expr.instSpine (fvsD nP ++ [tfvD nP]) nP (bodies.getD i default)) bodyC mb) := by
  obtain ⟨-, hspec⟩ := structProjBodies_spec h
  obtain ⟨b', mb, hres⟩ := hspec i hi
  rw [structProjResidP_eq] at hres
  -- the raw telescope's binder `nP + i`
  have hlenB : (structProjPs nP ++ (List.range i).map (structProjArgP T)).length = nP + i := by
    simp [structProjPs]
  have hlenF : (fvsD nP ++ projArgsD T i nP).length = nP + i := by
    simp [fvsD_length, projArgsD_length]
  obtain ⟨⟨bs, body0⟩, hs⟩ := Option.isSome_iff_exists.mp
    (stripPis_isSome_of_le (k := nP + i + 1) (by omega) hstrip)
  have hbsLen : bs.length = nP + i + 1 := stripPis_length _ hs
  obtain ⟨b, hb⟩ : ∃ b, bs[nP + i]? = some b :=
    ⟨bs[nP + i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  -- the bvar peel's head: the body is the domain's capture-avoiding sequence
  obtain ⟨bodyR, hhead⟩ := instPisAtLift_head _ (mrem := 0) hres
    (by rw [hlenB]; exact hs) (by rw [hlenB]; exact hb)
  obtain ⟨hbody, -, -⟩ := Expr.forallE.inj hhead
  -- the fvar peel exists, and its head is the domain's plain sequence
  obtain ⟨⟨cds, rest⟩, hpa⟩ := Option.isSome_iff_exists.mp
    (instPisAt_isSome_of_stripPis (fvsD nP ++ projArgsD T i nP)
      (by rw [hlenF]; exact stripPis_isSome_of_le (by omega) hstrip))
  obtain ⟨bodyC, hheadF⟩ := instPisAt_head _ (mrem := 0) hpa
    (by rw [hlenF]; exact hs) (by rw [hlenF]; exact hb)
  refine ⟨cds, bodyC, b.2, ?_⟩
  rw [hpa, hheadF, hbody, Expr.instSpine_eq_instSeq]
  -- the collapse
  have hdomB : b.1.looseBVarsBounded (nP + i) = true := by
    have := stripPis_binder_bounded (nP + i + 1) hs hcl (nP + i) b hb
    simpa using this
  have hcol := instSeq_instSeqLift (fvsD nP ++ [tfvD nP]) nP (fvsD_closed nP)
    (by simp [fvsD_length]) _ (structProjArgs_bounded T nP i) b.1
  rw [hlenB, structProjArgs_instSeq,
    instSeq_eq_self_of_bounded _ _ hdomB (by simp [fvsD_length]; omega)] at hcol
  rw [hlenB, hlenF, hcol]

/-! ## The `bvarB` cutoff of `hasLooseBVar` (task #214, P4) -/

/-- A node bounded at or below `i` has no loose `bvar i`. -/
theorem Expr.hasLooseBVar_eq_false_of_bound : ∀ (e : Expr) (i : Nat),
    e.bvarBound ≤ i → e.hasLooseBVar i = false
  | .bvar j, i, h => by
    simp only [Expr.bvarBound] at h
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne, ne_eq]
    omega
  | .fvar .., _, _ => rfl
  | .sort _, _, _ => rfl
  | .const .., _, _ => rfl
  | .lit _, _, _ => rfl
  | .app f a, i, h => by
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨hasLooseBVar_eq_false_of_bound f i h.1, hasLooseBVar_eq_false_of_bound a i h.2⟩
  | .lam ty b _, i, h => by
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨hasLooseBVar_eq_false_of_bound ty i h.1,
      hasLooseBVar_eq_false_of_bound b (i + 1) (by omega)⟩
  | .forallE ty b _, i, h => by
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨hasLooseBVar_eq_false_of_bound ty i h.1,
      hasLooseBVar_eq_false_of_bound b (i + 1) (by omega)⟩
  | .letE t v b, i, h => by
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨⟨hasLooseBVar_eq_false_of_bound t i h.1.1, hasLooseBVar_eq_false_of_bound v i h.1.2⟩,
      hasLooseBVar_eq_false_of_bound b (i + 1) (by omega)⟩
  | .proj _ _ e, i, h => by
    simp only [Expr.bvarBound] at h
    simp only [Expr.hasLooseBVar]
    exact hasLooseBVar_eq_false_of_bound e i h

/-- **The cutoff walk is `hasLooseBVar`.** -/
theorem Expr.hasLooseBVarB_eq : ∀ (i : Nat) (e : Expr), e.hasLooseBVarB i = e.hasLooseBVar i := by
  intro i e
  induction e generalizing i with
  | bvar j =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · rfl
  | fvar idx ty _ =>
    rw [Expr.hasLooseBVarB]; split <;> rfl
  | sort u => rw [Expr.hasLooseBVarB]; split <;> rfl
  | const n us => rw [Expr.hasLooseBVarB]; split <;> rfl
  | lit l => rw [Expr.hasLooseBVarB]; split <;> rfl
  | app f a ihf iha =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · simp only [Expr.hasLooseBVar, ihf, iha]
  | lam ty b m iht ihb =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · simp only [Expr.hasLooseBVar, iht, ihb]
  | forallE ty b m iht ihb =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · simp only [Expr.hasLooseBVar, iht, ihb]
  | letE t v b iht ihv ihb =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · simp only [Expr.hasLooseBVar, iht, ihv, ihb]
  | proj s i' e ih =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · simp only [Expr.hasLooseBVar, ih]

end ConLeche
