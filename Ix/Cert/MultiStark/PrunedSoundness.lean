import CertiFriP3.Pruned
import CertiFriProofs.Exec.Extract
import CertiFriProofs.Exec.SoundnessUnconditional
import CertiFriProofs.Theory.Compiled.SoundnessView
import CertiFriProofs.Theory.Oracle.MerkleVerify
import Ix.Cert.MultiStark.FieldModel
import Ix.Cert.MultiStark.SmallHeight

/-! # Pruned MMCS ROM Soundness & Base-Field Polynomial Extraction (Gap 3)

Extends CertiFRI's `Exec.soundness_uniqueDecoding` and `Exec.extractColumn` from
unpruned `merkleMmcs` (one full path per query) to Plonky3's `CertiFri.P3.prunedMmcs`
(`PrunedPaths D`):

1. **`restorePathsM`:** Monadic random-oracle version of `CertiFri.P3.restorePaths`
   using `MerkleRO.groupDigestM`, `MerkleRO.parentM`, and `MerkleRO.injectM`.
   - `run_restorePathsM`: against any oracle function `f`, `(restorePathsM ...).run f`
     equals `CertiFri.P3.restorePaths (hasherOf f) ...`.
   - `queryBound_restorePathsM`: makes at most `indices.size * (3 * maxLogHeight dims + 1)`
     hash queries (bounded by the exact same formula as `verifyOpeningsM`!).
   - `restorePaths_map`: `restorePaths (mapHasher g H) dims indices openedRows proof =
     restorePaths H dims indices (openedRows.map (·.map (·.map g))) proof`, unifying
     `inputHasher` (`m.base.toModel`) and `friHasher` (`m.ext.toModel`).

2. **`experimentPruned` & `soundness_pruned_uniqueDecoding`:**
   After the Fiat–Shamir transcript determines the query indices, `rest` runs
   `restorePathsM` on all input and folding-round pruned proofs, then runs
   `Compiled.Params.verifyGrindView` on the restored unpruned `Compiled.Proof`
   (total verifier queries `R = 2 * P.verifierQueries`). By `prunedMmcs_accepts`,
   `Exec.run_model_of_accepts`, and `Compiled.Params.soundness_grind_view_of_accepts`,
   pruned acceptance implies model acceptance with the exact unique-decoding ROM bound.

3. **Base-Field Descent (`basePoly_of_eval_c1_zero`):**
   Any polynomial `P : K[X]` of degree `< d + 1` whose evaluations at `≥ d + 1` points
   in the base field `Fp ⊆ K` all have `c1 = 0` has EVERY coefficient in `Fp`
   (`P = Polynomial.map K.embedHom P₀`). Hence every extracted preprocessed/main/quotient
   column polynomial evaluates to a base-field element `Fp` on the entire trace domain `H_ℓ`!

Zero `sorry`, standard axioms only.
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3 CertiFri.Oracle CertiFri.Oracle.MerkleRO CertiFri.Oracle.OracleComp
open CertiFri.Fri CertiFri.PcsRbr
open Polynomial

/-! ## 1. Monadic Pruned Path Restoration (`restorePathsM`) -/

section RestoreM

variable {Msg : Type} {Chal : ℕ → Type} {T D : Type}

/-- Map a list of computations sequentially, collecting results. -/
def mapM_oc {X : Type*} {Y : X → Type*} {α β : Type*} (f : α → OracleComp Y β) :
    List α → OracleComp Y (List β)
  | [] => .pure []
  | a :: as => (f a).bind fun b => (mapM_oc f as).bind fun bs => .pure (b :: bs)

theorem run_mapM_oc {X : Type*} {Y : X → Type*} {α β : Type*}
    (f : α → OracleComp Y β) (g : ∀ x, Y x) :
    ∀ l : List α, (mapM_oc f l).run g = l.map (fun a => (f a).run g)
  | [] => rfl
  | a :: as => by
    simp only [mapM_oc, run_bind, run_pure, List.map_cons, run_mapM_oc f g as]

theorem queryBound_mapM_oc {X : Type*} {Y : X → Type*} {α β : Type*}
    {f : α → OracleComp Y β} {q : ℕ} (hf : ∀ a, (f a).QueryBound q) :
    ∀ l : List α, (mapM_oc f l).QueryBound (l.length * q)
  | [] => by simp [mapM_oc]
  | a :: as => by
    unfold mapM_oc
    refine (QueryBound.bind (hf a) fun b =>
      QueryBound.bind (queryBound_mapM_oc hf as) fun bs =>
        queryBound_pure (b :: bs) 0).mono ?_
    simp [Nat.succ_mul]; omega

/-- Monadic version of `Pruned.leaves`. -/
def leavesM (dims : List Dimensions) (top : ℕ)
    (queries : List (ℕ × List (Array T))) :
    OracleComp (MerkleAnswer Msg Chal T D) (List (Pruned.Node T D)) :=
  let ascending := queries.mergeSort fun a b => a.1 ≤ b.1
  let uniq := ascending.eraseRepsBy fun a b => a.1 == b.1
  mapM_oc (fun (index, rows) =>
    (groupDigestM (Msg := Msg) (Chal := Chal) dims rows top).bind fun digest =>
      .pure { index, rows, digest, below := [(index, [])] }) uniq

theorem run_leavesM (f : ∀ x, MerkleAnswer Msg Chal T D x) (dims : List Dimensions) (top : ℕ)
    (queries : List (ℕ × List (Array T))) :
    (leavesM dims top queries).run f = Pruned.leaves (hasherOf f) dims top queries := by
  unfold leavesM Pruned.leaves
  rw [run_mapM_oc]
  apply List.map_congr_left
  intro p _
  rcases p with ⟨index, rows⟩
  simp [run_bind, run_pure, run_groupDigestM]

private lemma length_eraseRepsBy_le {α : Type*} (r : α → α → Bool) :
    ∀ l : List α, (l.eraseRepsBy r).length ≤ l.length := by
  suffices ∀ (a : α) (l : List α), (List.eraseRepsBy.loop r a l []).length ≤ l.length + 1 by
    intro l
    cases l with
    | nil => simp [List.eraseRepsBy]
    | cons a l => simpa [List.eraseRepsBy] using this a l
  suffices ∀ (a : α) (l acc : List α),
      (List.eraseRepsBy.loop r a l acc).length ≤ l.length + acc.length + 1 by
    intro a l; simpa using this a l []
  intro a l
  induction l generalizing a with
  | nil => intro acc; simp [List.eraseRepsBy.loop]
  | cons b bs ih =>
    intro acc
    unfold List.eraseRepsBy.loop
    split
    · have h := ih a acc; simp; omega
    · have h := ih b (a :: acc); simp at h ⊢; omega

theorem queryBound_leavesM (dims : List Dimensions) (top : ℕ)
    (queries : List (ℕ × List (Array T))) :
    (leavesM (Msg := Msg) (Chal := Chal) (D := D) dims top queries).QueryBound queries.length := by
  unfold leavesM
  dsimp only
  have h1 := queryBound_mapM_oc (q := 1)
    (f := fun p : ℕ × List (Array T) =>
      (groupDigestM (Msg := Msg) (Chal := Chal) (D := D) dims p.2 top).bind fun digest =>
        .pure ({ index := p.1, rows := p.2, digest, below := [(p.1, [])] } : Pruned.Node T D))
    (fun p => by
      unfold groupDigestM hashRowsM
      exact (QueryBound.bind (queryBound_query (Y := MerkleAnswer Msg Chal T D) _) fun _ =>
        queryBound_pure _ 0).mono (by omega))
    ((queries.mergeSort fun a b => a.1 ≤ b.1).eraseRepsBy fun a b => a.1 == b.1)
  have hlen : ((queries.mergeSort fun a b => a.1 ≤ b.1).eraseRepsBy fun a b => a.1 == b.1).length ≤
      queries.length := by
    calc _ ≤ (queries.mergeSort fun a b => a.1 ≤ b.1).length := length_eraseRepsBy_le _ _
      _ = queries.length := List.length_mergeSort _
  exact h1.mono (by omega)

/-- Monadic version of `Pruned.Node.parent`. -/
def nodeParentM (dims : List Dimensions) (h : ℕ) (node : Pruned.Node T D)
    (sibling : D) (belowSibling : List (ℕ × List D)) :
    OracleComp (MerkleAnswer Msg Chal T D) (Pruned.Node T D) :=
  (parentM (Msg := Msg) (Chal := Chal) node.index node.digest sibling).bind fun p =>
    (injectM dims node.rows h p).bind fun d =>
      .pure { index := node.index / 2
              digest := d
              rows := node.rows
              below := Pruned.addSibling sibling node.below ++ belowSibling }

theorem run_nodeParentM (f : ∀ x, MerkleAnswer Msg Chal T D x) (dims : List Dimensions) (h : ℕ)
    (node : Pruned.Node T D) (sibling : D) (belowSibling : List (ℕ × List D)) :
    (nodeParentM dims h node sibling belowSibling).run f =
      node.parent (hasherOf f) dims h sibling belowSibling := by
  simp [nodeParentM, Pruned.Node.parent, run_bind, run_pure, run_parentM, run_injectM]

theorem queryBound_nodeParentM (dims : List Dimensions) (h : ℕ)
    (node : Pruned.Node T D) (sibling : D) (belowSibling : List (ℕ × List D)) :
    (nodeParentM (Msg := Msg) (Chal := Chal) dims h node sibling belowSibling).QueryBound 3 := by
  unfold nodeParentM
  have hp : (parentM (Msg := Msg) (Chal := Chal) (T := T) node.index node.digest sibling).QueryBound 1 := by
    unfold parentM compressM
    by_cases hpar : node.index % 2 = 0
    · simp only [hpar, ↓reduceIte]
      exact queryBound_query (Y := MerkleAnswer Msg Chal T D) _
    · simp only [hpar, ↓reduceIte]
      exact queryBound_query (Y := MerkleAnswer Msg Chal T D) _
  have hi : ∀ p, (injectM (Msg := Msg) (Chal := Chal) dims node.rows h p).QueryBound 2 := fun p => by
    unfold injectM
    split_ifs
    · have hq1 : (groupDigestM (Msg := Msg) (Chal := Chal) (D := D) dims node.rows h).QueryBound 1 :=
        queryBound_query (Y := MerkleAnswer Msg Chal T D) _
      have hq2 : ∀ g, (compressM (Msg := Msg) (Chal := Chal) (T := T) p g).QueryBound 1 := fun _ =>
        queryBound_query (Y := MerkleAnswer Msg Chal T D) _
      exact (QueryBound.bind hq1 hq2).mono (by omega)
    · exact queryBound_pure _ 2
  exact (QueryBound.bind hp fun p =>
    QueryBound.bind (hi p) fun _ => queryBound_pure _ 0).mono (by omega)

/-- Monadic version of `Pruned.ascend`. -/
def ascendM (dims : List Dimensions) (h : ℕ) :
    List (Pruned.Node T D) → List D →
      OracleComp (MerkleAnswer Msg Chal T D) (Option (List (Pruned.Node T D) × List D))
  | [], supplied => .pure (some ([], supplied))
  | node :: nodes, supplied =>
    match nodes with
    | next :: rest =>
      if node.index / 2 = next.index / 2 then
        (ascendM dims h rest supplied).bind fun res =>
          match res with
          | none => .pure none
          | some (parents, supplied') =>
            let below := Pruned.addSibling node.digest next.below
            (nodeParentM dims h node next.digest below).bind fun p =>
              .pure (some (p :: parents, supplied'))
      else
        match supplied with
        | [] => .pure none
        | sibling :: supplied =>
          (ascendM dims h (next :: rest) supplied).bind fun res =>
            match res with
            | none => .pure none
            | some (parents, supplied') =>
              (nodeParentM dims h node sibling []).bind fun p =>
                .pure (some (p :: parents, supplied'))
    | [] =>
      match supplied with
      | [] => .pure none
      | sibling :: supplied =>
        (nodeParentM dims h node sibling []).bind fun p =>
          .pure (some ([p], supplied))

theorem run_ascendM (f : ∀ x, MerkleAnswer Msg Chal T D x) (dims : List Dimensions) (h : ℕ) :
    ∀ (nodes : List (Pruned.Node T D)) (supplied : List D),
      (ascendM dims h nodes supplied).run f = Pruned.ascend (hasherOf f) dims h nodes supplied
  | [], supplied => by simp [ascendM, Pruned.ascend]
  | [node], [] => by simp [ascendM, Pruned.ascend]
  | [node], sibling :: supplied => by
    simp [ascendM, Pruned.ascend, run_bind, run_pure, run_nodeParentM]
  | node :: next :: rest, supplied => by
    unfold ascendM Pruned.ascend
    dsimp only
    split_ifs with heq
    · rw [run_bind, run_ascendM f dims h rest supplied]
      cases Pruned.ascend (hasherOf f) dims h rest supplied with
      | none => rfl
      | some ps =>
        rcases ps with ⟨parents, supplied'⟩
        simp [run_bind, run_pure, run_nodeParentM]
    · cases supplied with
      | nil => rfl
      | cons sibling supplied =>
        dsimp only
        rw [run_bind, run_ascendM f dims h (next :: rest) supplied]
        cases Pruned.ascend (hasherOf f) dims h (next :: rest) supplied with
        | none => rfl
        | some ps =>
          rcases ps with ⟨parents, supplied'⟩
          simp [run_bind, run_pure, run_nodeParentM]

theorem ascendM_length_le [DecidableEq Msg] [∀ i, DecidableEq (Chal i)]
    [DecidableEq T] [DecidableEq D]
    {dims : List Dimensions} {h : ℕ}
    {nodes : List (Pruned.Node T D)} {supplied : List D}
    {l l' : Log (MerkleAnswer Msg Chal T D)} {parents : List (Pruned.Node T D)} {rem : List D}
    (hout : Outcome (ascendM dims h nodes supplied) l (some (parents, rem)) l') :
    parents.length ≤ nodes.length := by
  induction hn : nodes.length using Nat.strong_induction_on generalizing nodes supplied l l' parents rem with
  | h n ih =>
    cases nodes with
    | nil =>
      simp only [ascendM, outcome_pure, Option.some.injEq, Prod.mk.injEq] at hout
      obtain ⟨⟨rfl, _⟩, _⟩ := hout
      omega
    | cons node rest =>
      cases rest with
      | nil =>
        cases supplied with
        | nil => simp [ascendM] at hout
        | cons s ss =>
          unfold ascendM at hout
          dsimp only at hout
          rw [outcome_bind] at hout
          obtain ⟨p, l₁, _, h2⟩ := hout
          simp only [outcome_pure, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨⟨rfl, _⟩, _⟩ := h2
          simp at hn ⊢; omega
      | cons next tail =>
        unfold ascendM at hout
        dsimp only at hout
        split_ifs at hout with heq
        · rw [outcome_bind] at hout
          obtain ⟨res, l₁, h1, h2⟩ := hout
          cases res with
          | none => simp at h2
          | some ps =>
            rcases ps with ⟨ps', rem'⟩
            rw [outcome_bind] at h2
            obtain ⟨p, l₂, _, h3⟩ := h2
            simp only [outcome_pure, Option.some.injEq, Prod.mk.injEq] at h3
            obtain ⟨⟨rfl, _⟩, _⟩ := h3
            have hle := ih tail.length (by simp only [List.length_cons] at hn; omega) h1 rfl
            simp only [List.length_cons] at hn ⊢; omega
        · cases supplied with
          | nil => simp at hout
          | cons s ss =>
            rw [outcome_bind] at hout
            obtain ⟨res, l₁, h1, h2⟩ := hout
            cases res with
            | none => simp at h2
            | some ps =>
              rcases ps with ⟨ps', rem'⟩
              rw [outcome_bind] at h2
              obtain ⟨p, l₂, _, h3⟩ := h2
              simp only [outcome_pure, Option.some.injEq, Prod.mk.injEq] at h3
              obtain ⟨⟨rfl, _⟩, _⟩ := h3
              have hle := ih (next :: tail).length (by simp only [List.length_cons] at hn ⊢; omega) h1 rfl
              simp only [List.length_cons] at hn hle ⊢; omega

theorem queryBound_ascendM (dims : List Dimensions) (h : ℕ) :
    ∀ (nodes : List (Pruned.Node T D)) (supplied : List D),
      (ascendM (Msg := Msg) (Chal := Chal) dims h nodes supplied).QueryBound (3 * nodes.length) := by
  intro nodes
  induction hn : nodes.length using Nat.strong_induction_on generalizing nodes with
  | h n ih =>
    intro supplied
    cases nodes with
    | nil => simp [ascendM]
    | cons node rest =>
      cases rest with
      | nil =>
        cases supplied with
        | nil => exact queryBound_pure _ _
        | cons s ss =>
          unfold ascendM
          dsimp only
          exact (QueryBound.bind (queryBound_nodeParentM dims h node s []) fun _ =>
            queryBound_pure _ 0).mono (by simp at hn; omega)
      | cons next tail =>
        unfold ascendM
        dsimp only
        split_ifs with heq
        · refine (QueryBound.bind (m := 3)
            (ih tail.length (by simp only [List.length_cons] at hn; omega) tail rfl supplied)
            fun res => ?_).mono (by simp only [List.length_cons] at hn; omega)
          cases res with
          | none => exact queryBound_pure _ 3
          | some ps =>
            exact (QueryBound.bind (queryBound_nodeParentM dims h node next.digest _) fun _ =>
              queryBound_pure _ 0).mono (by omega)
        · cases supplied with
          | nil => exact queryBound_pure _ _
          | cons s ss =>
            refine (QueryBound.bind (m := 3)
              (ih (next :: tail).length (by simp only [List.length_cons] at hn ⊢; omega) (next :: tail) rfl ss)
              fun res => ?_).mono (by simp only [List.length_cons] at hn ⊢; omega)
            cases res with
            | none => exact queryBound_pure _ 3
            | some ps =>
              exact (QueryBound.bind (queryBound_nodeParentM dims h node s []) fun _ =>
                queryBound_pure _ 0).mono (by omega)

/-- Monadic version of `Pruned.walk`, explicitly checking frontier-size monotonicity so
its `OracleComp.QueryBound` holds structurally across all continuation paths. -/
def walkM (dims : List Dimensions) :
    (h : ℕ) → List (Pruned.Node T D) → List D →
      OracleComp (MerkleAnswer Msg Chal T D) (Option (List (Pruned.Node T D) × List D))
  | 0, nodes, supplied => .pure (some (nodes, supplied))
  | h + 1, nodes, supplied =>
    (ascendM dims h nodes supplied).bind fun res =>
      match res with
      | none => .pure none
      | some (parents, supplied') =>
        if parents.length ≤ nodes.length then walkM dims h parents supplied'
        else .pure none

private theorem ascend_length_le (H : MerkleHasher T D) (dims : List Dimensions) (h : ℕ) :
    ∀ (nodes : List (Pruned.Node T D)) (supplied : List D)
      {parents : List (Pruned.Node T D)} {rem : List D},
      Pruned.ascend H dims h nodes supplied = some (parents, rem) →
      parents.length ≤ nodes.length := by
  intro nodes
  induction hn : nodes.length using Nat.strong_induction_on generalizing nodes with
  | h n ih =>
    intro supplied parents rem heq
    cases nodes with
    | nil =>
      simp only [Pruned.ascend, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, _⟩ := heq; omega
    | cons node rest =>
      cases rest with
      | nil =>
        cases supplied with
        | nil => simp [Pruned.ascend] at heq
        | cons s ss =>
          simp only [Pruned.ascend, Pure.pure, Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, _⟩ := heq; simp at hn ⊢; omega
      | cons next tail =>
        unfold Pruned.ascend at heq
        dsimp only at heq
        split_ifs at heq with hpair
        · cases hrec : Pruned.ascend H dims h tail supplied with
          | none => simp [hrec] at heq
          | some ps =>
            rw [hrec] at heq
            simp at heq
            obtain ⟨rfl, _⟩ := heq
            have hle := ih tail.length (by simp only [List.length_cons] at hn; omega) tail rfl supplied hrec
            simp only [List.length_cons] at hn ⊢; omega
        · cases supplied with
          | nil => simp at heq
          | cons s ss =>
            dsimp only at heq
            cases hrec : Pruned.ascend H dims h (next :: tail) ss with
            | none => simp [hrec] at heq
            | some ps =>
              rw [hrec] at heq
              simp at heq
              obtain ⟨rfl, _⟩ := heq
              have hle := ih (next :: tail).length (by simp only [List.length_cons] at hn ⊢; omega) (next :: tail) rfl ss hrec
              simp only [List.length_cons] at hn hle ⊢; omega

theorem run_walkM (f : ∀ x, MerkleAnswer Msg Chal T D x) (dims : List Dimensions) :
    ∀ (h : ℕ) (nodes : List (Pruned.Node T D)) (supplied : List D),
      (walkM dims h nodes supplied).run f = Pruned.walk (hasherOf f) dims h nodes supplied
  | 0, _, _ => rfl
  | h + 1, nodes, supplied => by
    unfold walkM Pruned.walk
    rw [run_bind, run_ascendM]
    cases hres : Pruned.ascend (hasherOf f) dims h nodes supplied with
    | none => rfl
    | some ps =>
      have hle := ascend_length_le (hasherOf f) dims h nodes supplied hres
      simp only [hle, ↓reduceIte]
      exact run_walkM f dims h ps.1 ps.2

/-- Monadic `restorePathsM`: computes the exact same result as `CertiFri.P3.restorePaths`
against `hasherOf f`, while logging all Merkle hash queries into the ROM oracle log. -/
def restorePathsM (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (proof : PrunedPaths D) :
    OracleComp (MerkleAnswer Msg Chal T D) (Option (Array (List D))) :=
  if dims.isEmpty || openedRows.size != indices.size then .pure none
  else
    let top := Merkle.maxLogHeight dims.toList
    let queries := indices.toList.zip (openedRows.toList.map (·.toList))
    (leavesM dims.toList top queries).bind fun lvs =>
      if lvs.length ≤ indices.size then
        (walkM dims.toList top lvs proof.siblingHashes.toList).bind fun res =>
          match res with
          | some (nodes, []) =>
            let found := nodes.flatMap (·.below)
            .pure (indices.mapM fun index => (found.lookup index).map List.reverse)
          | _ => .pure none
      else .pure none

theorem run_restorePathsM (f : ∀ x, MerkleAnswer Msg Chal T D x)
    (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (proof : PrunedPaths D) :
    (restorePathsM dims indices openedRows proof).run f =
      CertiFri.P3.restorePaths (hasherOf f) dims indices openedRows proof := by
  unfold restorePathsM CertiFri.P3.restorePaths
  split_ifs with h
  · rfl
  · rw [run_bind, run_leavesM]
    have hlvs_le : (Pruned.leaves (hasherOf f) dims.toList (Merkle.maxLogHeight dims.toList)
        (indices.toList.zip (openedRows.toList.map (·.toList)))).length ≤ indices.size := by
      unfold Pruned.leaves
      rw [List.length_map]
      have h1 := length_eraseRepsBy_le (fun a b : ℕ × List (Array T) => a.1 == b.1)
        ((indices.toList.zip (openedRows.toList.map (·.toList))).mergeSort fun a b => a.1 ≤ b.1)
      have h2 := List.length_mergeSort (indices.toList.zip (openedRows.toList.map (·.toList)))
        (le := fun a b => a.1 ≤ b.1)
      have h3 : (indices.toList.zip (openedRows.toList.map (·.toList))).length ≤ indices.size := by
        rw [List.length_zip]; simp
      omega
    simp only [hlvs_le, ↓reduceIte, run_bind, run_walkM]
    cases Pruned.walk (hasherOf f) dims.toList (Merkle.maxLogHeight dims.toList)
        (Pruned.leaves (hasherOf f) dims.toList (Merkle.maxLogHeight dims.toList)
          (indices.toList.zip (openedRows.toList.map (·.toList))))
        proof.siblingHashes.toList with
    | none => rfl
    | some ps =>
      rcases ps with ⟨nodes, rem⟩
      cases rem <;> rfl

/-- `walkM` over `h` levels with at most `q` frontier nodes makes at most `3 * h * q` queries. -/
theorem queryBound_walkM (dims : List Dimensions) (q : ℕ) :
    ∀ (h : ℕ) (nodes : List (Pruned.Node T D)) (supplied : List D),
      nodes.length ≤ q →
      (walkM (Msg := Msg) (Chal := Chal) dims h nodes supplied).QueryBound (3 * h * q) := by
  intro h
  induction h with
  | zero => intro nodes supplied _; simp [walkM]
  | succ h ih =>
    intro nodes supplied hle
    unfold walkM
    have hasc : (ascendM (Msg := Msg) (Chal := Chal) dims h nodes supplied).QueryBound (3 * q) :=
      (queryBound_ascendM dims h nodes supplied).mono (by omega)
    refine (QueryBound.bind (m := 3 * h * q) hasc fun res => ?_).mono (by ring_nf; omega)
    cases res with
    | none => exact queryBound_pure _ (3 * h * q)
    | some ps =>
      dsimp only
      split_ifs with hps
      · exact ih ps.1 ps.2 (hps.trans hle)
      · exact queryBound_pure _ (3 * h * q)

/-- **`restorePathsM` Query Bound:** restoring pruned Merkle paths for `indices.size` queries
into a tree of depth `top = maxLogHeight dims` makes at most `indices.size * (3 * top + 1)`
hash queries — the exact same upper bound as `verifyOpeningsM`! -/
theorem queryBound_restorePathsM (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (proof : PrunedPaths D) :
    (restorePathsM (Msg := Msg) (Chal := Chal) dims indices openedRows proof).QueryBound
      (indices.size * (3 * Merkle.maxLogHeight dims.toList + 1)) := by
  unfold restorePathsM
  split_ifs with h
  · exact queryBound_pure _ _
  · have hqlen : (indices.toList.zip (openedRows.toList.map (·.toList))).length ≤ indices.size := by
      rw [List.length_zip]; simp
    have hlv := (queryBound_leavesM (Msg := Msg) (Chal := Chal) (D := D)
      dims.toList (Merkle.maxLogHeight dims.toList)
      (indices.toList.zip (openedRows.toList.map (·.toList)))).mono hqlen
    refine (QueryBound.bind (m := 3 * Merkle.maxLogHeight dims.toList * indices.size) hlv fun lvs => ?_).mono
      (by ring_nf; omega)
    split_ifs with hlvs
    · exact (QueryBound.bind (m := 0)
        (queryBound_walkM dims.toList indices.size (Merkle.maxLogHeight dims.toList)
          lvs proof.siblingHashes.toList hlvs)
        fun res => by
          cases res with
          | none => exact queryBound_pure _ 0
          | some ps => rcases ps with ⟨nodes, rem⟩; cases rem <;> exact queryBound_pure _ 0).mono
        (by omega)
    · exact queryBound_pure _ _

end RestoreM

/-! ## 2. Base-Field Descent for Extracted Column Polynomials (`Fp^3`) -/

/-- Projection of a `K`-polynomial `P` onto its base-field coordinates `P₀, P₁, P₂ : GoldilocksField[X]`,
satisfying `P = map embedHom P₀ + C ⟨0, 1, 0⟩ * map embedHom P₁ + C ⟨0, 0, 1⟩ * map embedHom P₂`. -/
noncomputable def polyC0 (P : K[X]) : GoldilocksField[X] :=
  ∑ k ∈ P.support, Polynomial.monomial k (Fp3Model.c0 (P.coeff k))

noncomputable def polyC1 (P : K[X]) : GoldilocksField[X] :=
  ∑ k ∈ P.support, Polynomial.monomial k (Fp3Model.c1 (P.coeff k))

noncomputable def polyC2 (P : K[X]) : GoldilocksField[X] :=
  ∑ k ∈ P.support, Polynomial.monomial k (Fp3Model.c2 (P.coeff k))

@[simp] theorem coeff_polyC0 (P : K[X]) (k : ℕ) : (polyC0 P).coeff k = Fp3Model.c0 (P.coeff k) := by
  unfold polyC0
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · rw [Polynomial.notMem_support_iff.mp hk]; rfl

@[simp] theorem coeff_polyC1 (P : K[X]) (k : ℕ) : (polyC1 P).coeff k = Fp3Model.c1 (P.coeff k) := by
  unfold polyC1
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · rw [Polynomial.notMem_support_iff.mp hk]; rfl

@[simp] theorem coeff_polyC2 (P : K[X]) (k : ℕ) : (polyC2 P).coeff k = Fp3Model.c2 (P.coeff k) := by
  unfold polyC2
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · rw [Polynomial.notMem_support_iff.mp hk]; rfl

theorem eval_c1_eq_eval_polyC1 (P : K[X]) (x : GoldilocksField) :
    Fp3Model.c1 (P.eval (Fp3Model.embedHom x)) = (polyC1 P).eval x := by
  induction P using Polynomial.induction_on' with
  | add p q ihp ihq =>
    have hadd : polyC1 (p + q) = polyC1 p + polyC1 q := by
      ext k; simp
    rw [eval_add, Fp3Model.add_c1, ihp, ihq, hadd, eval_add]
  | monomial n a =>
    have hmon : polyC1 (monomial n a) = monomial n (Fp3Model.c1 a) := by
      ext k
      simp only [coeff_polyC1, coeff_monomial]
      split_ifs <;> rfl
    rw [hmon, eval_monomial, eval_monomial, ← map_pow]
    simp [Fp3Model.mul_c1, Fp3Model.embedHom_apply]

theorem eval_c2_eq_eval_polyC2 (P : K[X]) (x : GoldilocksField) :
    Fp3Model.c2 (P.eval (Fp3Model.embedHom x)) = (polyC2 P).eval x := by
  induction P using Polynomial.induction_on' with
  | add p q ihp ihq =>
    have hadd : polyC2 (p + q) = polyC2 p + polyC2 q := by
      ext k; simp
    rw [eval_add, Fp3Model.add_c2, ihp, ihq, hadd, eval_add]
  | monomial n a =>
    have hmon : polyC2 (monomial n a) = monomial n (Fp3Model.c2 a) := by
      ext k
      simp only [coeff_polyC2, coeff_monomial]
      split_ifs <;> rfl
    rw [hmon, eval_monomial, eval_monomial, ← map_pow]
    simp [Fp3Model.mul_c2, Fp3Model.embedHom_apply]

theorem degree_polyC1_le (P : K[X]) : (polyC1 P).degree ≤ P.degree := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  rw [coeff_polyC1, Polynomial.coeff_eq_zero_of_degree_lt hm]
  rfl

theorem degree_polyC2_le (P : K[X]) : (polyC2 P).degree ≤ P.degree := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  rw [coeff_polyC2, Polynomial.coeff_eq_zero_of_degree_lt hm]
  rfl

/-- **Base-Field Descent Theorem (`Fp^3`):** If `P : K[X]` has degree `< d + 1` and
`(P.eval (embedHom x)).c1 = 0 ∧ (P.eval (embedHom x)).c2 = 0` on a set `B : Finset GoldilocksField`
of at least `d + 1` points, then `polyC1 P = 0` and `polyC2 P = 0`, so every coefficient of `P`
lies in `Fp` and `P = Polynomial.map Fp3Model.embedHom (polyC0 P)`. -/
theorem basePoly_of_eval_c1_c2_zero {P : K[X]} {d : ℕ} (hdeg : P.degree < (d + 1 : ℕ))
    {B : Finset GoldilocksField} (hcard : d + 1 ≤ B.card)
    (heval : ∀ x ∈ B, Fp3Model.c1 (P.eval (Fp3Model.embedHom x)) = 0 ∧
      Fp3Model.c2 (P.eval (Fp3Model.embedHom x)) = 0) :
    polyC1 P = 0 ∧ polyC2 P = 0 ∧ P = Polynomial.map Fp3Model.embedHom (polyC0 P) := by
  have hdeg1 : (polyC1 P).degree < (d + 1 : ℕ) := lt_of_le_of_lt (degree_polyC1_le P) hdeg
  have hzero1 : polyC1 P = 0 := by
    by_contra hne
    have hroots : B ⊆ (polyC1 P).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def, ← eval_c1_eq_eval_polyC1]
      exact (heval x hx).1
    have hle1 := Finset.card_le_card hroots
    have hle2 := Multiset.toFinset_card_le (polyC1 P).roots
    have hle3 := Polynomial.card_roots' (polyC1 P)
    have hnat : (polyC1 P).natDegree < d + 1 := by
      rwa [Polynomial.degree_eq_natDegree hne, Nat.cast_lt] at hdeg1
    omega
  have hdeg2 : (polyC2 P).degree < (d + 1 : ℕ) := lt_of_le_of_lt (degree_polyC2_le P) hdeg
  have hzero2 : polyC2 P = 0 := by
    by_contra hne
    have hroots : B ⊆ (polyC2 P).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def, ← eval_c2_eq_eval_polyC2]
      exact (heval x hx).2
    have hle1 := Finset.card_le_card hroots
    have hle2 := Multiset.toFinset_card_le (polyC2 P).roots
    have hle3 := Polynomial.card_roots' (polyC2 P)
    have hnat : (polyC2 P).natDegree < d + 1 := by
      rwa [Polynomial.degree_eq_natDegree hne, Nat.cast_lt] at hdeg2
    omega
  refine ⟨hzero1, hzero2, ?_⟩
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map, coeff_polyC0]
  have hc1 : Fp3Model.c1 (P.coeff k) = 0 := by
    rw [← coeff_polyC1, hzero1, coeff_zero]
  have hc2 : Fp3Model.c2 (P.coeff k) = 0 := by
    rw [← coeff_polyC2, hzero2, coeff_zero]
  exact Fp3Model.ext rfl hc1 hc2

/-! ## 3. Pruned Path Restoration Under Entry Maps (`restorePaths_map`) -/

section RestoreMap

private def mapNode {T U D : Type} (g : T → U) (n : Pruned.Node T D) : Pruned.Node U D :=
  { n with rows := n.rows.map (·.map g) }

private lemma eraseRepsBy_map {α β : Type*} (f : α → β) (r : α → α → Bool) (s : β → β → Bool)
    (h : ∀ a b, s (f a) (f b) = r a b) :
    ∀ l : List α, (l.map f).eraseRepsBy s = (l.eraseRepsBy r).map f := by
  have hloop : ∀ (a : α) (l acc : List α),
      List.eraseRepsBy.loop s (f a) (l.map f) (acc.map f) =
        (List.eraseRepsBy.loop r a l acc).map f := by
    intro a l
    induction l generalizing a with
    | nil =>
      intro acc
      simp [List.eraseRepsBy.loop, List.map_reverse]
    | cons b bs ih =>
      intro acc
      simp only [List.map_cons]
      unfold List.eraseRepsBy.loop
      rw [h a b]
      cases r a b
      · simpa only [List.map_cons] using ih b (a :: acc)
      · exact ih a acc
  intro l
  cases l with
  | nil => rfl
  | cons a as =>
    simp only [List.map_cons, List.eraseRepsBy]
    simpa only [List.map_nil] using hloop a as []

private lemma leaves_map {T U D : Type} (g : T → U) (H : MerkleHasher U D)
    (dims : List Dimensions) (top : ℕ) (queries : List (ℕ × List (Array T))) :
    Pruned.leaves H dims top (queries.map fun p => (p.1, p.2.map (·.map g))) =
      (Pruned.leaves ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims top queries).map
        (mapNode g) := by
  unfold Pruned.leaves
  dsimp only
  have hsort := (List.map_mergeSort
    (f := fun p : ℕ × List (Array T) => (p.1, p.2.map (·.map g)))
    (r := fun a b => decide (a.1 ≤ b.1)) (s := fun a b => decide (a.1 ≤ b.1))
    (l := queries) (fun _ _ _ _ => rfl)).symm
  rw [hsort]
  rw [eraseRepsBy_map (f := fun p : ℕ × List (Array T) => (p.1, p.2.map (·.map g)))
    (r := fun a b => a.1 == b.1) (s := fun a b => a.1 == b.1) (fun _ _ => rfl)]
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_def, mapNode, Exec.Checks.groupDigest_map]

private lemma nodeParent_map {T U D : Type} (g : T → U) (H : MerkleHasher U D)
    (dims : List Dimensions) (h : ℕ) (node : Pruned.Node T D)
    (sibling : D) (belowSibling : List (ℕ × List D)) :
    (mapNode g node).parent H dims h sibling belowSibling =
      mapNode g (node.parent ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h sibling belowSibling) := by
  simp only [Pruned.Node.parent, mapNode, Exec.Checks.parent_map, Exec.Checks.inject_map]

private lemma ascend_map {T U D : Type} (g : T → U) (H : MerkleHasher U D)
    (dims : List Dimensions) (h : ℕ) :
    ∀ (nodes : List (Pruned.Node T D)) (supplied : List D),
      Pruned.ascend H dims h (nodes.map (mapNode g)) supplied =
        (Pruned.ascend ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h nodes supplied).map
          (fun ps => (ps.1.map (mapNode g), ps.2)) := by
  intro nodes
  induction hn : nodes.length using Nat.strong_induction_on generalizing nodes with
  | h n ih =>
    intro supplied
    cases nodes with
    | nil => simp [Pruned.ascend]
    | cons node rest =>
      cases rest with
      | nil =>
        cases supplied with
        | nil => simp [Pruned.ascend]
        | cons s ss =>
          simp only [List.map_cons, List.map_nil, Pruned.ascend, Pure.pure,
            Option.map_some, nodeParent_map]
      | cons next tail =>
        simp only [List.map_cons]
        unfold Pruned.ascend
        dsimp only [mapNode]
        by_cases heq : node.index / 2 = next.index / 2
        · simp only [heq, ↓reduceIte]
          have hrec := ih tail.length (by simp only [List.length_cons] at hn; omega) tail rfl supplied
          rw [hrec]
          cases Pruned.ascend ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h tail supplied with
          | none => rfl
          | some ps =>
            simp only [Option.map_some, Bind.bind, Option.bind_some, Pure.pure, List.map_cons]
            exact congrArg some (congrArg (·, ps.2) (congrArg (· :: _)
              (nodeParent_map g H dims h node next.digest (Pruned.addSibling node.digest next.below))))
        · simp only [heq, ↓reduceIte]
          cases supplied with
          | nil => rfl
          | cons s ss =>
            dsimp only
            have hrec := ih (next :: tail).length
              (by simp only [List.length_cons] at hn ⊢; omega) (next :: tail) rfl ss
            simp only [List.map_cons] at hrec
            change (do
                let __x ← Pruned.ascend H dims h (mapNode g next :: tail.map (mapNode g)) ss
                Pure.pure (Pruned.Node.parent H dims h (mapNode g node) s [] :: __x.1, __x.2)) = _
            rw [hrec]
            cases Pruned.ascend ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h (next :: tail) ss with
            | none => rfl
            | some ps =>
              simp only [Option.map_some, Bind.bind, Option.bind_some, Pure.pure, List.map_cons,
                nodeParent_map]

private lemma walk_map {T U D : Type} (g : T → U) (H : MerkleHasher U D)
    (dims : List Dimensions) :
    ∀ (h : ℕ) (nodes : List (Pruned.Node T D)) (supplied : List D),
      Pruned.walk H dims h (nodes.map (mapNode g)) supplied =
        (Pruned.walk ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h nodes supplied).map
          (fun ps => (ps.1.map (mapNode g), ps.2))
  | 0, _, _ => rfl
  | h + 1, nodes, supplied => by
    unfold Pruned.walk
    rw [ascend_map]
    cases Pruned.ascend ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims h nodes supplied with
    | none => rfl
    | some ps =>
      simp only [Option.map_some]
      exact walk_map g H dims h ps.1 ps.2

/-- **`restorePaths` commutes with entry maps:** restoring pruned paths under the mapped hasher
`inputHasher` / `friHasher` produces the exact same Merkle paths as restoring under the model
hasher `H` on mapped rows. -/
theorem restorePaths_map {T U D : Type} (g : T → U) (H : MerkleHasher U D)
    (dims : Array Dimensions) (indices : Array ℕ)
    (openedRows : Array (Array (Array T))) (proof : PrunedPaths D) :
    CertiFri.P3.restorePaths ⟨fun xs => H.hashRows (xs.map g), H.compress⟩
        dims indices openedRows proof =
      CertiFri.P3.restorePaths H dims indices
        (openedRows.map fun r => r.map fun row => row.map g) proof := by
  unfold CertiFri.P3.restorePaths
  simp only [Array.size_map]
  split_ifs with h
  · rfl
  · have hzip : indices.toList.zip ((openedRows.map fun r => r.map fun row => row.map g).toList.map (·.toList)) =
        (indices.toList.zip (openedRows.toList.map (·.toList))).map
          (fun p => (p.1, p.2.map (·.map g))) := by
      rw [Array.toList_map, List.map_map]
      clear h
      generalize openedRows.toList = rs
      generalize indices.toList = is
      induction is generalizing rs with
      | nil => simp
      | cons i is ih =>
        cases rs with
        | nil => simp
        | cons r rs =>
          simp only [List.map_cons, List.zip_cons_cons]
          rw [ih]
          simp only [Function.comp_def, Array.toList_map]
    rw [hzip, leaves_map, walk_map]
    cases Pruned.walk ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims.toList
        (Merkle.maxLogHeight dims.toList)
        (Pruned.leaves ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims.toList
          (Merkle.maxLogHeight dims.toList) (indices.toList.zip (openedRows.toList.map (·.toList))))
        proof.siblingHashes.toList with
    | none => rfl
    | some ps =>
      rcases ps with ⟨nodes, rem⟩
      cases rem with
      | cons _ _ => rfl
      | nil =>
        simp only [Option.map_some]
        have hflat : (nodes.map (mapNode g)).flatMap (·.below) = nodes.flatMap (·.below) := by
          rw [List.flatMap_map]; rfl
        rw [hflat]

end RestoreMap

/-! ## 4. Full ROM Unique-Decoding Soundness for `CertiFri.P3.prunedMmcs` -/

section PrunedRom

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : Exec.FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : Exec.WellFormed m params shape)

/-- An adversary's statement and proof using Plonky3's pruned MMCS (`PrunedPaths D`). -/
structure PrunedAttempt (F EF D : Type) where
  commitments : Array D
  points : Array EF
  values : Array EF
  proof : FriProof F EF D (PrunedPaths D) (PrunedPaths D)

def PrunedAttempt.messages (params : FriParams) (shape : ClaimShape) (a : PrunedAttempt F EF D) :
    ℕ → Exec.RawMsg F EF D :=
  Exec.messages params shape a.commitments a.points a.values a.proof

/-- Executable FRI verifier with `CertiFri.P3.prunedMmcs` against an ideal ROM oracle `f`. -/
noncomputable def acceptsPruned
    (f : ∀ x, Exec.OracleAnswer (D := D) m params shape wf x) (a : PrunedAttempt F EF D) : Bool :=
  Fri.verify
    (prunedMmcs (Exec.inputHasher m (hasherOf f)))
    (prunedMmcs (Exec.friHasher m (hasherOf f)))
    (Exec.freeChallenger (Exec.modelParams m params shape wf) (Exec.powBits params shape) f m)
    Exec.FreeState.init params shape a.commitments a.points a.values a.proof

/-- Replace the pruned opening proofs in `a` with explicit unpruned path arrays, preserving
every commitment, opening point, claimed value, opened row, sibling, and PoW witness. -/
def PrunedAttempt.withPaths (a : PrunedAttempt F EF D)
    (inPaths comPaths : Array (Array (List D))) : Exec.Attempt F EF D where
  commitments := a.commitments
  points := a.points
  values := a.values
  proof :=
    { commitPhaseCommits := a.proof.commitPhaseCommits
      commitPowWitnesses := a.proof.commitPowWitnesses
      inputOpenings := a.proof.inputOpenings.mapIdx fun i o =>
        { openedValues := o.openedValues, openingProof := inPaths.getD i #[] }
      commitPhaseOpenings := a.proof.commitPhaseOpenings.mapIdx fun i o =>
        { logArity := o.logArity
          siblingValues := o.siblingValues
          openingProof := comPaths.getD i #[] }
      finalPoly := a.proof.finalPoly
      queryPowWitness := a.proof.queryPowWitness }

omit [FieldOps EF] [ExtensionOps F EF] [DecidableEq D] [Inhabited D] in
private lemma withPaths_shapeOk (a : PrunedAttempt F EF D)
    (inPaths comPaths : Array (Array (List D))) :
    Fri.shapeOk (F := F) params shape (a.withPaths inPaths comPaths).commitments
      (a.withPaths inPaths comPaths).points (a.withPaths inPaths comPaths).values
      (a.withPaths inPaths comPaths).proof =
    Fri.shapeOk (F := F) params shape a.commitments a.points a.values a.proof := by
  have hall1 : ((a.proof.commitPhaseOpenings.mapIdx fun i o =>
      ({ logArity := o.logArity, siblingValues := o.siblingValues,
         openingProof := comPaths.getD i #[] } : CommitPhaseStep EF (Array (List D)))).all
      (fun o => o.logArity == 1 && o.siblingValues.size == params.numQueries &&
        o.siblingValues.all fun s => s.size == 1)) =
      a.proof.commitPhaseOpenings.all (fun o => o.logArity == 1 &&
        o.siblingValues.size == params.numQueries && o.siblingValues.all fun s => s.size == 1) := by
    apply Bool.eq_iff_iff.mpr
    rw [Array.all_eq_true, Array.all_eq_true]
    simp only [Array.size_mapIdx, Array.getElem_mapIdx]
  unfold Fri.shapeOk
  simp only [PrunedAttempt.withPaths]
  rw [hall1]
  simp only [Array.size_mapIdx]
  apply congrArg (_ && ·)
  apply congrArg (List.all _)
  funext b
  rw [Array.getElem?_mapIdx]
  cases a.proof.inputOpenings[b]? <;> rfl

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] in
private lemma withPaths_messages (a : PrunedAttempt F EF D)
    (inPaths comPaths : Array (Array (List D))) (j : ℕ) :
    (a.withPaths inPaths comPaths).messages params shape j = a.messages params shape j := by
  simp [Exec.Attempt.messages, PrunedAttempt.messages, Exec.messages, PrunedAttempt.withPaths]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] in
private lemma withPaths_transcript {S : Type} (ch : Challenger S F EF D) (s : S)
    (a : PrunedAttempt F EF D) (inPaths comPaths : Array (Array (List D))) :
    Fri.transcript ch s params shape (a.withPaths inPaths comPaths).commitments
      (a.withPaths inPaths comPaths).points (a.withPaths inPaths comPaths).values
      (a.withPaths inPaths comPaths).proof =
    Fri.transcript ch s params shape a.commitments a.points a.values a.proof := by
  rfl

omit [DecidableEq D] [Inhabited D] in
private lemma withPaths_queryResult (a : PrunedAttempt F EF D)
    (inPaths comPaths : Array (Array (List D))) (ch : Fri.Challenges EF) (t : ℕ) :
    Exec.queryResult (F := F) params shape (a.withPaths inPaths comPaths).points
      (a.withPaths inPaths comPaths).values (a.withPaths inPaths comPaths).proof ch t =
    Exec.queryResult (F := F) params shape a.points a.values a.proof ch t := by
  have hqr : Fri.queryRows (a.withPaths inPaths comPaths).proof t = Fri.queryRows a.proof t := by
    unfold Fri.queryRows
    simp only [PrunedAttempt.withPaths]
    apply Array.ext
    · simp
    · intro i hi1 hi2
      simp [Array.getElem_map, Array.getElem_mapIdx]
  have hsib : ∀ i, Fri.sibling (a.withPaths inPaths comPaths).proof i t = Fri.sibling a.proof i t := by
    intro i
    unfold Fri.sibling
    simp only [PrunedAttempt.withPaths, Array.getElem?_mapIdx]
    cases a.proof.commitPhaseOpenings[i]? <;> rfl
  have hsib_fn : (fun i => Fri.sibling (a.withPaths inPaths comPaths).proof i t) =
      (fun i => Fri.sibling a.proof i t) := funext hsib
  unfold Exec.queryResult Fri.checkQuery
  rw [hqr, hsib_fn]
  rfl

/-- Base `Compiled.Proof` extracted from a `PrunedAttempt` (carries `inputRows` and `siblings`;
paths are filled in after `restorePathsM`). -/
def baseModelProof (a : PrunedAttempt F EF D) :
    Compiled.Proof K D shape.length params.numQueries :=
  Exec.modelProof m params shape (a.withPaths #[] #[]).proof

omit [TwoAdicOps F] [DecidableEq K] [DecidableEq D] [Inhabited D] in
private lemma baseModelProof_inputRows (a : PrunedAttempt F EF D)
    (inPaths comPaths : Array (Array (List D))) :
    (Exec.modelProof m params shape (a.withPaths inPaths comPaths).proof).inputRows =
      (baseModelProof m params shape a).inputRows := by
  funext b t
  have hqr : Fri.queryRows (a.withPaths inPaths comPaths).proof t.val =
      Fri.queryRows (a.withPaths #[] #[]).proof t.val := by
    unfold Fri.queryRows
    simp only [PrunedAttempt.withPaths]
    apply Array.ext
    · simp
    · intro i hi1 hi2
      simp [Array.getElem_map, Array.getElem_mapIdx]
  rw [baseModelProof, Exec.modelProof, Exec.modelProof]
  dsimp only
  rw [hqr]

omit [TwoAdicOps F] [DecidableEq K] [DecidableEq D] [Inhabited D] in
private lemma baseModelProof_siblings (a : PrunedAttempt F EF D)
    (inPaths comPaths : Array (Array (List D))) :
    (Exec.modelProof m params shape (a.withPaths inPaths comPaths).proof).siblings =
      (baseModelProof m params shape a).siblings := by
  funext i t
  simp only [baseModelProof, Exec.modelProof, Fri.sibling, PrunedAttempt.withPaths,
    Array.getElem?_mapIdx]
  cases a.proof.commitPhaseOpenings[i]? <;> rfl

/-- Monadic pruned-proof unpruner + verifier: restores all input and folding-round Merkle
paths via `restorePathsM` (bounded by `P.verifierQueries`), then runs `P.verifyGrindView`
on the restored `Compiled.Proof` (bounded by `P.verifierQueries`), for total query bound
`2 * P.verifierQueries`. -/
noncomputable def unpruneAndVerifyM
    (a : PrunedAttempt F EF D)
    (t : Transcript (Exec.RawMsg F EF D)
      (PcsRbr.GrindChal (Exec.powBits params shape)
        (PcsRbr.Chal (Exec.modelParams m params shape wf).ldt
          (Exec.modelParams m params shape wf).queries))
      ((Exec.modelParams m params shape wf).rounds + 2)) :
    OracleComp (Exec.OracleAnswer (D := D) m params shape wf) Bool :=
  let P := Exec.modelParams m params shape wf
  let basePf := baseModelProof m params shape a
  let ut := PcsRbr.ungrind t
  let msg : ℕ → Compiled.Msg K D P.batches := fun j =>
    Exec.view m params shape (Compiled.msgAt ut j)
  let α := PcsRbr.alphaOf ut
  let β := PcsRbr.betasOf ut
  let index : Fin P.queries → ℕ := fun k => P.indexOf (PcsRbr.queriesOf ut k)
  let inComp := mapM_oc (fun b : Fin P.batches =>
    let dims := P.dims b
    let indices := Array.ofFn fun k : Fin P.queries =>
      index k >>> (P.n - Merkle.maxLogHeight dims.toList)
    let rows := Array.ofFn (basePf.inputRows b)
    let pproof : PrunedPaths D :=
      match a.proof.inputOpenings[b.val]? with
      | some o => o.openingProof
      | none => ⟨#[]⟩
    restorePathsM (Msg := Exec.RawMsg F EF D)
      (Chal := PcsRbr.GrindChal (Exec.powBits params shape) (PcsRbr.Chal P.ldt P.queries))
      dims indices rows pproof) (List.finRange P.batches)
  let comComp := mapM_oc (fun i : ℕ =>
    let dims := P.commitDims i
    let indices := Array.ofFn fun k : Fin P.queries => index k >>> (i + 1)
    let rows := Array.ofFn fun k : Fin P.queries =>
      #[#[(P.commitRow basePf (msg 0) α β (index k) k i).1,
          (P.commitRow basePf (msg 0) α β (index k) k i).2]]
    let pproof : PrunedPaths D :=
      match a.proof.commitPhaseOpenings[i]? with
      | some o => o.openingProof
      | none => ⟨#[]⟩
    restorePathsM (Msg := Exec.RawMsg F EF D)
      (Chal := PcsRbr.GrindChal (Exec.powBits params shape) (PcsRbr.Chal P.ldt P.queries))
      dims indices rows pproof) (List.range P.rounds)
  inComp.bind fun inOpts =>
    comComp.bind fun comOpts =>
      match inOpts.mapM id, comOpts.mapM id with
      | some inPaths, some comPaths =>
        let unpruned := a.withPaths inPaths.toArray comPaths.toArray
        P.verifyGrindView (Exec.powBits params shape) (Exec.view m params shape)
          (Exec.modelProof m params shape unpruned.proof) t
      | _, _ => .pure false

theorem queryBound_unpruneAndVerifyM (a : PrunedAttempt F EF D)
    (t : Transcript (Exec.RawMsg F EF D)
      (PcsRbr.GrindChal (Exec.powBits params shape)
        (PcsRbr.Chal (Exec.modelParams m params shape wf).ldt
          (Exec.modelParams m params shape wf).queries))
      ((Exec.modelParams m params shape wf).rounds + 2)) :
    (unpruneAndVerifyM m params shape wf a t).QueryBound
      (2 * (Exec.modelParams m params shape wf).verifierQueries) := by
  unfold unpruneAndVerifyM
  dsimp only
  refine (QueryBound.bind
    (n := (Exec.modelParams m params shape wf).batches *
      ((Exec.modelParams m params shape wf).queries * (3 * (Exec.modelParams m params shape wf).n + 1)))
    (m := (Exec.modelParams m params shape wf).rounds *
      ((Exec.modelParams m params shape wf).queries * (3 * (Exec.modelParams m params shape wf).n + 1)) +
      (Exec.modelParams m params shape wf).verifierQueries)
    ?_ fun inOpts =>
      QueryBound.bind
        (n := (Exec.modelParams m params shape wf).rounds *
          ((Exec.modelParams m params shape wf).queries * (3 * (Exec.modelParams m params shape wf).n + 1)))
        (m := (Exec.modelParams m params shape wf).verifierQueries)
        ?_ fun comOpts => ?_).mono ?_
  · refine (queryBound_mapM_oc
      (q := (Exec.modelParams m params shape wf).queries * (3 * (Exec.modelParams m params shape wf).n + 1))
      (fun b => by
        refine (queryBound_restorePathsM _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        exact Nat.mul_le_mul_left _ (by have := (Exec.modelParams m params shape wf).height_le b; omega))
      (List.finRange (Exec.modelParams m params shape wf).batches)).mono ?_
    rw [List.length_finRange]
  · refine (queryBound_mapM_oc
      (q := (Exec.modelParams m params shape wf).queries * (3 * (Exec.modelParams m params shape wf).n + 1))
      (fun i => by
        refine (queryBound_restorePathsM _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        have hdim : Merkle.maxLogHeight ((Exec.modelParams m params shape wf).commitDims i).toList ≤
            (Exec.modelParams m params shape wf).n := by
          simp only [Compiled.Params.commitDims, List.toList_toArray, Merkle.maxLogHeight]
          omega
        exact Nat.mul_le_mul_left _ (by omega))
      (List.range (Exec.modelParams m params shape wf).rounds)).mono ?_
    rw [List.length_range]
  · split
    · exact (Exec.modelParams m params shape wf).queryBound_verifyGrindView
        (Exec.powBits params shape) (Exec.view m params shape) _ t
    · exact queryBound_pure false (Exec.modelParams m params shape wf).verifierQueries
  · simp only [Compiled.Params.verifierQueries]; ring_nf; omega

/-- **Refinement for Pruned MMCS:** If the executable FRI verifier with `prunedMmcs` accepts `a`
against oracle `f`, then `unpruneAndVerifyM` returns `true` against `f` on `a`'s Fiat–Shamir
transcript (recovering the exact unpruned paths and passing `P.verifyGrindView`). -/
theorem run_unpruneAndVerifyM_of_acceptsPruned
    (f : ∀ x, Exec.OracleAnswer (D := D) m params shape wf x) (a : PrunedAttempt F EF D)
    (hacc : acceptsPruned m params shape wf f a = true) :
    (unpruneAndVerifyM m params shape wf a
      (fsTranscript f (a.messages params shape)
        ((Exec.modelParams m params shape wf).rounds + 2))).run f = true := by
  set P := Exec.modelParams m params shape wf
  set t := fsTranscript f (a.messages params shape) (P.rounds + 2)
  set H := hasherOf f
  unfold acceptsPruned Fri.verify at hacc
  rw [Bool.and_eq_true] at hacc
  obtain ⟨hshape, hwith⟩ := hacc
  -- Run `transcript_free` on the dummy-paths unpruned version (identical messages/transcript)
  set a0 := a.withPaths #[] #[]
  have hshape0 : Fri.shapeOk (F := F) params shape a0.commitments a0.points a0.values a0.proof = true := by
    rwa [withPaths_shapeOk]
  have hmsg0 : a0.messages params shape = a.messages params shape := by
    funext j; exact withPaths_messages params shape a #[] #[] j
  obtain ⟨hα, hβ, -, -, hidx⟩ :=
    Exec.transcript_free m params shape wf f a0.commitments a0.points a0.values a0.proof hshape0
  rw [show Exec.messages params shape a0.commitments a0.points a0.values a0.proof =
      a.messages params shape from hmsg0] at hα hβ hidx
  have htr : Fri.transcript (Exec.freeChallenger P (Exec.powBits params shape) f m)
      Exec.FreeState.init params shape a.commitments a.points a.values a.proof =
      Fri.transcript (Exec.freeChallenger P (Exec.powBits params shape) f m)
        Exec.FreeState.init params shape a0.commitments a0.points a0.values a0.proof :=
    (withPaths_transcript params shape _ _ a #[] #[]).symm
  set ch := Fri.transcript (Exec.freeChallenger P (Exec.powBits params shape) f m)
    Exec.FreeState.init params shape a.commitments a.points a.values a.proof
  rw [← htr] at hα hβ hidx
  have hag0 : Exec.Agrees m params shape a0.commitments a0.points a0.values a0.proof ch
      (fun j => Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) j))
      (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
      (fun k => P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) :=
    { msg := fun j hj => by
        rw [show t = fsTranscript f (a0.messages params shape) (P.rounds + 2) by rw [hmsg0]]
        rw [Exec.msgAt_fsTranscript m params shape wf f a0 hj]; rfl
      alpha := hα.symm
      beta := fun i _ => (hβ i).symm
      index := fun k => (hidx k).symm }
  -- Unpack `Fri.verifyWith` acceptance for `prunedMmcs`
  have hwith' : (ch.powOk && ch.indices.size == params.numQueries
      && (List.range params.numQueries).all (fun k =>
        decide (ch.indices.getD k 0 < 2 ^ Fri.logMaxHeight params.logBlowup shape))
      && Fri.inputChecks (prunedMmcs (Exec.inputHasher m H)) params shape a.commitments
        a.proof.inputOpenings ch.indices
      && (Array.ofFn fun k : Fin params.numQueries =>
        Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).all (·.ok)
      && Fri.commitChecks (prunedMmcs (Exec.friHasher m H)) params.numQueries
        (Fri.logMaxHeight params.logBlowup shape) (Fri.numRounds params shape)
        a.proof.commitPhaseCommits a.proof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun k : Fin params.numQueries =>
          Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).map (·.rows)))
      = true := hwith
  simp only [Bool.and_eq_true] at hwith'
  obtain ⟨⟨⟨⟨⟨hpow, hidxSz⟩, hidxLt⟩, hinPruned⟩, hqOk⟩, hcomPruned⟩ := hwith'
  -- Step 1: Every input batch `b` restores to `some paths_b` passing `Merkle.verifyOpenings`
  have hinEach : ∀ b : Fin P.batches,
      ∃ (root : D) (o : BatchOpening F (PrunedPaths D)) (paths : Array (List D)),
        a.commitments[b.val]? = some root ∧
        a.proof.inputOpenings[b.val]? = some o ∧
        restorePaths H (P.dims b)
          (Array.ofFn fun k : Fin P.queries =>
            P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k) >>>
              (P.n - Merkle.maxLogHeight (P.dims b).toList))
          (Array.ofFn ((baseModelProof m params shape a).inputRows b)) o.openingProof = some paths ∧
        Merkle.verifyOpenings (Exec.inputHasher m H) root
          (Fri.batchDims params.logBlowup (shape.getD b.val []))
          (Array.ofFn (n := params.numQueries) fun k =>
            ch.indices.getD k.val 0 >>>
              (Fri.logMaxHeight params.logBlowup shape -
                Merkle.maxLogHeight (Fri.batchDims params.logBlowup (shape.getD b.val [])).toList))
          o.openedValues paths = true := by
    intro b
    simp only [Fri.inputChecks, List.all_eq_true, List.mem_range] at hinPruned
    have hb := hinPruned b.val b.isLt
    split at hb
    · next root o hroot ho =>
      obtain ⟨paths, hrest, hver⟩ := prunedMmcs_accepts hb
      obtain ⟨hrowsSz, _⟩ := Exec.Checks.size_of_verifyOpenings hver
      rw [Array.size_ofFn] at hrowsSz
      have hrestM : restorePaths H (P.dims b)
          (Array.ofFn fun k : Fin P.queries =>
            P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k) >>>
              (P.n - Merkle.maxLogHeight (P.dims b).toList))
          (Array.ofFn ((baseModelProof m params shape a).inputRows b)) o.openingProof = some paths := by
        have ho' : a.proof.inputOpenings[b.val]? = some (o : BatchOpening F (PrunedPaths D)) := ho
        have ho0 : a0.proof.inputOpenings[b.val]? =
            some { openedValues := o.openedValues, openingProof := #[] } := by
          dsimp only [a0, PrunedAttempt.withPaths]
          rw [Array.getElem?_mapIdx, ho']
          rfl
        have hrowsEq : Array.ofFn ((baseModelProof m params shape a).inputRows b) =
            o.openedValues.map fun r => r.map fun row => row.map m.base.toModel :=
          Exec.Checks.ofFn_inputRows m params shape b ho0 hrowsSz
        have hidx_eq :
            (Array.ofFn fun k : Fin P.queries =>
              P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k) >>>
                (P.n - Merkle.maxLogHeight (P.dims b).toList)) =
            (Array.ofFn (n := params.numQueries) fun k =>
              ch.indices.getD k.val 0 >>>
                (Fri.logMaxHeight params.logBlowup shape -
                  Merkle.maxLogHeight (Fri.batchDims params.logBlowup (shape.getD b.val [])).toList)) := by
          congr 1; funext k; rw [hag0.index k]; rfl
        rw [hrowsEq, hidx_eq]
        exact (restorePaths_map m.base.toModel H (P.dims b) _ o.openedValues o.openingProof).symm.trans hrest
      exact ⟨root, o, paths, hroot, ho, hrestM, hver⟩
    · exact absurd hb (by simp)
  -- Step 2: Every folding round `i` restores to `some paths_i` passing `Merkle.verifyOpenings`
  have hcomEach : ∀ i : ℕ, i < P.rounds →
      ∃ (root : D) (o : CommitPhaseStep EF (PrunedPaths D)) (paths : Array (List D)),
        a.proof.commitPhaseCommits[i]? = some root ∧
        a.proof.commitPhaseOpenings[i]? = some o ∧
        restorePaths H (P.commitDims i)
          (Array.ofFn fun k : Fin P.queries =>
            P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k) >>> (i + 1))
          (Array.ofFn fun k : Fin P.queries =>
            #[#[(P.commitRow (baseModelProof m params shape a)
                  (Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) 0))
                  (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
                  (P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) k i).1,
                (P.commitRow (baseModelProof m params shape a)
                  (Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) 0))
                  (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
                  (P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) k i).2]])
          o.openingProof = some paths ∧
        Merkle.verifyOpenings (Exec.friHasher m H) root #[⟨2, P.n - i - 1⟩]
          (Array.ofFn (n := params.numQueries) fun k => ch.indices.getD k.val 0 >>> (i + 1))
          (Array.ofFn (n := params.numQueries) fun k =>
            #[#[((Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).rows.getD i (0, 0)).1,
                ((Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).rows.getD i (0, 0)).2]])
          paths = true := by
    intro i hi
    simp only [Fri.commitChecks, List.all_eq_true, List.mem_range] at hcomPruned
    have hci := hcomPruned i hi
    split at hci
    · next root o hroot ho =>
      obtain ⟨paths, hrest, hver⟩ := prunedMmcs_accepts hci
      have hrowsEq :
          (Array.ofFn (n := params.numQueries) fun k =>
            #[#[((Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).rows.getD i (0, 0)).1,
                ((Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).rows.getD i (0, 0)).2]]).map
            (fun r => r.map fun row => row.map m.ext.toModel) =
          Array.ofFn fun k : Fin P.queries =>
            #[#[(P.commitRow (baseModelProof m params shape a)
                  (Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) 0))
                  (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
                  (P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) k i).1,
                (P.commitRow (baseModelProof m params shape a)
                  (Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) 0))
                  (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
                  (P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) k i).2]] := by
        rw [Exec.Checks.map_ofFn_pair]
        congr 1; funext k
        have hqr := Exec.rows_queryResult m params shape wf hshape0 hag0 k hi
        rw [withPaths_queryResult] at hqr
        have h1 := congrArg Prod.fst hqr
        have h2 := congrArg Prod.snd hqr
        dsimp only at h1 h2
        rw [h1, h2]
        rfl
      have hrestM : restorePaths H (P.commitDims i)
          (Array.ofFn fun k : Fin P.queries =>
            P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k) >>> (i + 1))
          (Array.ofFn fun k : Fin P.queries =>
            #[#[(P.commitRow (baseModelProof m params shape a)
                  (Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) 0))
                  (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
                  (P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) k i).1,
                (P.commitRow (baseModelProof m params shape a)
                  (Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) 0))
                  (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
                  (P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) k i).2]])
          o.openingProof = some paths := by
        have hidx_eq :
            (Array.ofFn fun k : Fin P.queries =>
              P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k) >>> (i + 1)) =
            (Array.ofFn (n := params.numQueries) fun k =>
              ch.indices.getD k.val 0 >>> (i + 1)) := by
          congr 1; funext k; rw [hag0.index k]
        rw [← hrowsEq, hidx_eq]
        simp only [Exec.Checks.getD_map_ofFn] at hrest
        exact (restorePaths_map m.ext.toModel H (P.commitDims i) _ _ o.openingProof).symm.trans hrest
      have hver' : Merkle.verifyOpenings (Exec.friHasher m H) root #[⟨2, P.n - i - 1⟩]
          (Array.ofFn (n := params.numQueries) fun k => ch.indices.getD k.val 0 >>> (i + 1))
          (Array.ofFn (n := params.numQueries) fun k =>
            #[#[((Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).rows.getD i (0, 0)).1,
                ((Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).rows.getD i (0, 0)).2]])
          paths = true := by
        simpa [P, Exec.modelParams, Exec.Checks.getD_map_ofFn] using hver
      exact ⟨root, o, paths, hroot, ho, hrestM, hver'⟩
    · exact absurd hci (by simp)
  -- Step 3: Evaluate `unpruneAndVerifyM` under `f`
  unfold unpruneAndVerifyM
  simp only [run_bind, run_mapM_oc, run_restorePathsM]
  -- Evaluate input restoration list to `some inPaths`
  have hinList : ∃ inPaths : List (Array (List D)),
      (List.map (fun b : Fin P.batches =>
        restorePaths H (P.dims b)
          (Array.ofFn fun k : Fin P.queries =>
            P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k) >>>
              (P.n - Merkle.maxLogHeight (P.dims b).toList))
          (Array.ofFn ((baseModelProof m params shape a).inputRows b))
          (match a.proof.inputOpenings[b.val]? with | some o => o.openingProof | none => ⟨#[]⟩))
        (List.finRange P.batches)).mapM id = some inPaths ∧
      inPaths.length = P.batches ∧
      ∀ b : Fin P.batches, ∃ (root : D) (o : BatchOpening F (PrunedPaths D)),
        a.commitments[b.val]? = some root ∧ a.proof.inputOpenings[b.val]? = some o ∧
        Merkle.verifyOpenings (Exec.inputHasher m H) root
          (Fri.batchDims params.logBlowup (shape.getD b.val []))
          (Array.ofFn (n := params.numQueries) fun k =>
            ch.indices.getD k.val 0 >>>
              (Fri.logMaxHeight params.logBlowup shape -
                Merkle.maxLogHeight (Fri.batchDims params.logBlowup (shape.getD b.val [])).toList))
          o.openedValues (inPaths.toArray.getD b.val #[]) = true := by
    choose roots os paths hroots hos hrests hvers using hinEach
    refine ⟨(List.finRange P.batches).map paths, ?_, by simp, ?_⟩
    · have hmapM : ∀ (l : List (Array (List D))), (l.map some).mapM id = some l := by
        intro l; induction l with | nil => rfl | cons x xs ih => simp [ih]
      rw [← hmapM]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro b _
      simp only [Function.comp_def, hos b, hrests b]
    · intro b
      refine ⟨roots b, os b, hroots b, hos b, ?_⟩
      have hget : (((List.finRange P.batches).map paths).toArray.getD b.val #[]) = paths b := by
        simp [Array.getD, b.isLt]
      rw [hget]
      exact hvers b
  -- Evaluate commit restoration list to `some comPaths`
  have hcomList : ∃ comPaths : List (Array (List D)),
      (List.map (fun i : ℕ =>
        restorePaths H (P.commitDims i)
          (Array.ofFn fun k : Fin P.queries =>
            P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k) >>> (i + 1))
          (Array.ofFn fun k : Fin P.queries =>
            #[#[(P.commitRow (baseModelProof m params shape a)
                  (Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) 0))
                  (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
                  (P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) k i).1,
                (P.commitRow (baseModelProof m params shape a)
                  (Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) 0))
                  (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
                  (P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) k i).2]])
          (match a.proof.commitPhaseOpenings[i]? with | some o => o.openingProof | none => ⟨#[]⟩))
        (List.range P.rounds)).mapM id = some comPaths ∧
      comPaths.length = P.rounds ∧
      ∀ i (hi : i < P.rounds), ∃ (root : D) (o : CommitPhaseStep EF (PrunedPaths D)),
        a.proof.commitPhaseCommits[i]? = some root ∧ a.proof.commitPhaseOpenings[i]? = some o ∧
        Merkle.verifyOpenings (Exec.friHasher m H) root #[⟨2, P.n - i - 1⟩]
          (Array.ofFn (n := params.numQueries) fun k => ch.indices.getD k.val 0 >>> (i + 1))
          (Array.ofFn (n := params.numQueries) fun k =>
            #[#[((Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).rows.getD i (0, 0)).1,
                ((Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).rows.getD i (0, 0)).2]])
          (comPaths.toArray.getD i #[]) = true := by
    have hcomFin : ∀ i : Fin P.rounds,
        ∃ (root : D) (o : CommitPhaseStep EF (PrunedPaths D)) (paths : Array (List D)),
          a.proof.commitPhaseCommits[i.val]? = some root ∧
          a.proof.commitPhaseOpenings[i.val]? = some o ∧
          restorePaths H (P.commitDims i.val)
            (Array.ofFn fun k : Fin P.queries =>
              P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k) >>> (i.val + 1))
            (Array.ofFn fun k : Fin P.queries =>
              #[#[(P.commitRow (baseModelProof m params shape a)
                    (Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) 0))
                    (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
                    (P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) k i.val).1,
                  (P.commitRow (baseModelProof m params shape a)
                    (Exec.view m params shape (Compiled.msgAt (PcsRbr.ungrind t) 0))
                    (PcsRbr.alphaOf (PcsRbr.ungrind t)) (PcsRbr.betasOf (PcsRbr.ungrind t))
                    (P.indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) k i.val).2]])
            o.openingProof = some paths ∧
          Merkle.verifyOpenings (Exec.friHasher m H) root #[⟨2, P.n - i.val - 1⟩]
            (Array.ofFn (n := params.numQueries) fun k => ch.indices.getD k.val 0 >>> (i.val + 1))
            (Array.ofFn (n := params.numQueries) fun k =>
              #[#[((Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).rows.getD i.val (0, 0)).1,
                  ((Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val).rows.getD i.val (0, 0)).2]])
            paths = true := fun i => hcomEach i.val i.isLt
    choose roots os paths hroots hos hrests hvers using hcomFin
    refine ⟨(List.finRange P.rounds).map paths, ?_, by simp, ?_⟩
    · have hmapM : ∀ (l : List (Array (List D))), (l.map some).mapM id = some l := by
        intro l; induction l with | nil => rfl | cons x xs ih => simp [ih]
      rw [← hmapM]
      congr 1
      have hrg : List.range P.rounds = (List.finRange P.rounds).map Fin.val := by
        apply List.ext_getElem <;> simp
      rw [hrg, List.map_map, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_def, hos i, hrests i]
    · intro i hi
      refine ⟨roots ⟨i, hi⟩, os ⟨i, hi⟩, hroots ⟨i, hi⟩, hos ⟨i, hi⟩, ?_⟩
      have hget : (((List.finRange P.rounds).map paths).toArray.getD i #[]) = paths ⟨i, hi⟩ := by
        simp [Array.getD, hi]
      rw [hget]
      exact hvers ⟨i, hi⟩
  obtain ⟨inPaths, hinEq, -, hinVer⟩ := hinList
  obtain ⟨comPaths, hcomEq, -, hcomVer⟩ := hcomList
  rw [hinEq, hcomEq]
  dsimp only
  -- Step 4: The restored unpruned attempt is accepted by `Exec.accepts`, so `Exec.run_model_of_accepts` finishes!
  set unpruned := a.withPaths inPaths.toArray comPaths.toArray
  have hUnprunedAcc : Exec.accepts m params shape wf f unpruned = true := by
    unfold Exec.accepts Fri.verify
    rw [Bool.and_eq_true]
    refine ⟨(withPaths_shapeOk params shape a inPaths.toArray comPaths.toArray).trans hshape, ?_⟩
    have htrU : Fri.transcript (Exec.freeChallenger (Exec.modelParams m params shape wf) (Exec.powBits params shape) f m)
        Exec.FreeState.init params shape unpruned.commitments unpruned.points unpruned.values unpruned.proof = ch :=
      withPaths_transcript params shape _ _ a _ _
    refine Eq.trans
      (congrArg (Fri.verifyWith (merkleMmcs (Exec.inputHasher m (hasherOf f)))
        (merkleMmcs (Exec.friHasher m (hasherOf f))) params shape
        unpruned.commitments unpruned.points unpruned.values unpruned.proof) htrU) ?_
    simp only [Fri.verifyWith, Bool.and_eq_true]
    have hqEq :
        (Array.ofFn fun k : Fin params.numQueries =>
          Exec.queryResult (F := F) params shape unpruned.points unpruned.values unpruned.proof ch k.val) =
        (Array.ofFn fun k : Fin params.numQueries =>
          Exec.queryResult (F := F) params shape a.points a.values a.proof ch k.val) := by
      congr 1; funext k; exact withPaths_queryResult params shape a _ _ ch k.val
    refine ⟨⟨⟨⟨⟨hpow, hidxSz⟩, hidxLt⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [Fri.inputChecks, List.all_eq_true, List.mem_range]
      intro b hb
      obtain ⟨root, o, hroot, ho, hver⟩ := hinVer ⟨b, hb⟩
      have hrootU : unpruned.commitments[b]? = some root := hroot
      have hoU : unpruned.proof.inputOpenings[b]? =
          some { openedValues := o.openedValues, openingProof := inPaths.toArray.getD b #[] } := by
        dsimp only [unpruned, PrunedAttempt.withPaths]
        rw [Array.getElem?_mapIdx, ho]
        rfl
      split
      · next r' o' hr' ho' =>
        have h1 : r' = root := Option.some.inj (hr'.symm.trans hrootU)
        have h2 : o' = { openedValues := o.openedValues, openingProof := inPaths.toArray.getD b #[] } :=
          Option.some.inj (ho'.symm.trans hoU)
        subst h1; subst h2
        exact hver
      · next hmiss =>
        exact (hmiss root { openedValues := o.openedValues, openingProof := inPaths.toArray.getD b #[] }
          hrootU hoU).elim
    · change ((Array.ofFn fun k : Fin params.numQueries =>
          Exec.queryResult (F := F) params shape unpruned.points unpruned.values
            unpruned.proof ch k.val).all (·.ok)) = true
      rw [hqEq]
      exact hqOk
    · simp only [Fri.commitChecks, List.all_eq_true, List.mem_range]
      intro i hi
      obtain ⟨root, o, hroot, ho, hver⟩ := hcomVer i hi
      have hrootU : unpruned.proof.commitPhaseCommits[i]? = some root := hroot
      have hoU : unpruned.proof.commitPhaseOpenings[i]? =
          some { logArity := o.logArity, siblingValues := o.siblingValues,
                 openingProof := comPaths.toArray.getD i #[] } := by
        dsimp only [unpruned, PrunedAttempt.withPaths]
        rw [Array.getElem?_mapIdx, ho]
        rfl
      split
      · next r' o' hr' ho' =>
        have h1 : r' = root := Option.some.inj (hr'.symm.trans hrootU)
        have h2 : o' = { logArity := o.logArity, siblingValues := o.siblingValues,
                         openingProof := comPaths.toArray.getD i #[] } :=
          Option.some.inj (ho'.symm.trans hoU)
        subst h1; subst h2
        change Merkle.verifyOpenings (Exec.friHasher m (hasherOf f)) r'
          #[⟨2, Fri.logMaxHeight params.logBlowup shape - i - 1⟩]
          (Array.ofFn (n := params.numQueries) fun t => ch.indices.getD t.val 0 >>> (i + 1))
          (Array.ofFn (n := params.numQueries) fun t =>
            #[#[(((Array.ofFn fun k : Fin params.numQueries =>
                  Exec.queryResult (F := F) params shape unpruned.points unpruned.values
                    unpruned.proof ch k.val).map (·.rows)).getD t.val []).getD i (0, 0) |>.1,
                (((Array.ofFn fun k : Fin params.numQueries =>
                  Exec.queryResult (F := F) params shape unpruned.points unpruned.values
                    unpruned.proof ch k.val).map (·.rows)).getD t.val []).getD i (0, 0) |>.2]])
          (comPaths.toArray.getD i #[]) = true
        rw [hqEq]
        simp only [Exec.Checks.getD_map_ofFn]
        exact hver
      · next hmiss =>
        exact (hmiss root { logArity := o.logArity, siblingValues := o.siblingValues,
                            openingProof := comPaths.toArray.getD i #[] } hrootU hoU).elim
  have hrun := Exec.run_model_of_accepts m params shape wf f unpruned hUnprunedAcc
  have hmsgU : unpruned.messages params shape = a.messages params shape := by
    funext j; exact withPaths_messages params shape a inPaths.toArray comPaths.toArray j
  rwa [hmsgU] at hrun

section SoundnessPruned

variable [DecidableEq F] [DecidableEq EF] [Fintype K] [Fintype D]

/-- The pruned-MMCS soundness experiment: adversary runs, Fiat–Shamir transcript is derived,
then `unpruneAndVerifyM` unprunes and verifies the proof, logging all Merkle queries. -/
noncomputable def experimentPruned {A : Type*}
    (adv : OracleComp (Exec.OracleAnswer (D := D) m params shape wf) A)
    (attempt : A → PrunedAttempt F EF D) :
    OracleComp (Exec.OracleAnswer (D := D) m params shape wf) (A × Bool) :=
  (fsExperiment ((Exec.modelParams m params shape wf).rounds + 2) adv
      (fun a => (attempt a).messages params shape)).bind fun out =>
    (unpruneAndVerifyM m params shape wf (attempt out.1) out.2).bind fun b =>
      .pure (out.1, b)

/-- **Unconditional ROM Soundness of `CertiFri.P3.prunedMmcs` at the Unique-Decoding Radius (Gap 3):**

Extends `CertiFri.Exec.soundness_uniqueDecoding` from unpruned `merkleMmcs` to Plonky3's
pruned multi-opening scheme `CertiFri.P3.prunedMmcs` (`PrunedPaths D`). With no proximity
hypothesis (`2 * δ + (1 / 2) ^ logBlowup ≤ 1`), the probability that `Fri.verify` with
`prunedMmcs` accepts an adversary's attempt while the committed claims fail at agreement
`1 - δ` is at most:

    N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|),

where `N = Q + (rounds + 2) + 2 * P.verifierQueries`. -/
theorem soundness_pruned_uniqueDecoding
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax)
    {A : Type*}
    {adv : OracleComp (Exec.OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → PrunedAttempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, Exec.OracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            acceptsPruned m params shape wf f (attempt res.1) = true) ∧
        ClaimsFail (Exec.modelParams m params shape wf).ldt
          (Exec.modelParams m params shape wf).shift (1 - δ)
          ((Exec.modelParams m params shape wf).claims
            (Exec.view m params shape (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (committedRow l)))
      (experimentPruned m params shape wf adv attempt) [] ≤
      (Q + ((Exec.modelParams m params shape wf).rounds + 2) +
          2 * (Exec.modelParams m params shape wf).verifierQueries) * εmax +
        ((max ((Exec.modelParams m params shape wf).batches +
            (Exec.modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((Exec.modelParams m params shape wf).rounds + 2) +
            2 * (Exec.modelParams m params shape wf).verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  set P := Exec.modelParams m params shape wf
  have hθ : 0 ≤ 1 - δ := by
    have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ params.logBlowup := by positivity
    linarith
  have hn : P.n = P.rounds + params.logBlowup + params.logFinalPolyLen := by
    show Fri.logMaxHeight params.logBlowup shape =
      Fri.numRounds params shape + params.logBlowup + params.logFinalPolyLen
    unfold Fri.numRounds FriParams.logFinalHeight at *
    omega
  have hfinal : P.finalDegree = 2 ^ params.logFinalPolyLen := rfl
  set c : ℝ := (1 + δ) * (2 : ℝ) ^ P.n
  have hc_nonneg : 0 ≤ c := by positivity
  -- Proximity gap bounds (linear unique decoding)
  have hmca : ∀ j ≤ P.rounds,
      CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) (1 - δ)
        (((P.numClaims j - 1 : ℕ) : ℝ) * c / Fintype.card K) := by
    intro j hj
    have hcard : ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card = 2 ^ (P.n - j) := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne),
        card_twoAdicDomain P.prim (by have := P.rounds_le; omega)]
    have hle : (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) ≤ 2 ^ P.n := by
      rw [hcard]; exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le P.n j)
    have hdist : 2 * (δ * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) +
        (2 ^ (P.rounds - j) * P.finalDegree : ℕ) ≤
        ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card := by
      rw [hcard, hfinal]
      have hexp : 2 ^ (P.rounds - j) * 2 ^ params.logFinalPolyLen =
          2 ^ (P.n - j - params.logBlowup) := by
        rw [← pow_add]; congr 1; omega
      have hcast : ((2 ^ (P.rounds - j) * 2 ^ params.logFinalPolyLen : ℕ) : ℝ) =
          (2 : ℝ) ^ (P.n - j) * (1 / 2 : ℝ) ^ params.logBlowup := by
        rw [hexp]
        have hsub : P.n - j = (P.n - j - params.logBlowup) + params.logBlowup := by omega
        push_cast
        conv_rhs => rw [hsub, pow_add]
        rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
      rw [hcast]
      push_cast
      have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (P.n - j) := by positivity
      nlinarith
    have hbase := curveMCA_uniqueDecoding ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) δ hδ hdist
    intro u
    obtain ⟨bad, hbad, hok⟩ := hbase u
    refine ⟨bad, hbad.trans ?_, hok⟩
    dsimp only [c]
    gcongr
  have hstep : ∀ i < P.rounds,
      StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree) (1 - δ) (c / Fintype.card K) := by
    intro i hi
    have hcard : (twoAdicDomain P.ω P.n (i + 1)).card = 2 ^ (P.n - (i + 1)) :=
      card_twoAdicDomain P.prim (by have := P.rounds_le; omega)
    have hle : 2 * ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ) ≤ 2 ^ P.n := by
      rw [hcard]
      have hsub : 2 * 2 ^ (P.n - (i + 1)) = 2 ^ (P.n - i) := by
        have hpos : P.n - i = P.n - (i + 1) + 1 := by have := P.rounds_le; omega
        rw [hpos, pow_succ']
      exact_mod_cast (hsub ▸ Nat.pow_le_pow_right two_pos (Nat.sub_le P.n i))
    have hdist : 2 * (δ * (twoAdicDomain P.ω P.n (i + 1)).card) +
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree : ℕ) ≤
        (twoAdicDomain P.ω P.n (i + 1)).card := by
      rw [hcard, hfinal]
      have hexp : 2 ^ (P.rounds - (i + 1)) * 2 ^ params.logFinalPolyLen =
          2 ^ (P.n - (i + 1) - params.logBlowup) := by
        rw [← pow_add]; congr 1; omega
      have hcast : ((2 ^ (P.rounds - (i + 1)) * 2 ^ params.logFinalPolyLen : ℕ) : ℝ) =
          (2 : ℝ) ^ (P.n - (i + 1)) * (1 / 2 : ℝ) ^ params.logBlowup := by
        rw [hexp]
        have hsub : P.n - (i + 1) = (P.n - (i + 1) - params.logBlowup) + params.logBlowup := by omega
        push_cast
        conv_rhs => rw [hsub, pow_add]
        rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
      rw [hcast]
      push_cast
      have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (P.n - (i + 1)) := by positivity
      nlinarith
    have hbase := stepMCA_uniqueDecoding (P.ldt.step i hi)
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) hδ hdist
    intro ro cc
    obtain ⟨bad, hbad, hok⟩ := hbase ro cc
    refine ⟨bad, hbad.trans ?_, hok⟩
    have hmul : 2 * ((1 + δ) * ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ)) ≤ c := by
      dsimp only [c]
      nlinarith
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hmul (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hα' : (∑ j ∈ Finset.range (P.rounds + 1),
      ((P.numClaims j - 1 : ℕ) : ℝ) * c / Fintype.card K) / 2 ^ Exec.powBits params shape 0 ≤ εmax := by
    rw [Exec.powBits_zero, pow_zero, div_one, ← Finset.sum_div, ← Finset.sum_mul]
    have hsum : ((∑ j ∈ Finset.range (P.rounds + 1), (P.numClaims j - 1) : ℕ) : ℝ) ≤
        ((Fri.claimRefs params.logBlowup shape).length : ℝ) :=
      Nat.cast_le.mpr (Exec.sum_numClaims_sub_one_le m params shape wf)
    rw [← Nat.cast_sum]
    calc _ ≤ ((Fri.claimRefs params.logBlowup shape).length : ℝ) * c / Fintype.card K := by gcongr
      _ ≤ εmax := hα
  have hβ' : ∀ i < P.rounds,
      (c / Fintype.card K) / 2 ^ Exec.powBits params shape (i + 1) ≤ εmax := by
    intro i hi
    rw [Exec.powBits_succ_of_lt params shape hi]
    exact hβ
  have hq' : (1 - δ) ^ P.queries / 2 ^ Exec.powBits params shape (P.rounds + 1) ≤ εmax := by
    rw [show P.rounds = Fri.numRounds params shape from rfl, Exec.powBits_last]
    exact hq
  -- Invoke `Compiled.Params.soundness_grind_view_of_accepts` with `R = 2 * P.verifierQueries`
  have hbound := P.soundness_grind_view_of_accepts (Exec.powBits params shape) (Exec.view m params shape)
    hθ hmca hstep hα' hβ' hq' hadv (fun a => (attempt a).messages params shape)
    (rest := fun out =>
      (unpruneAndVerifyM m params shape wf (attempt out.1) out.2).bind fun b => .pure (out.1, b))
    (R := 2 * P.verifierQueries)
    (fun out => (queryBound_unpruneAndVerifyM m params shape wf (attempt out.1) out.2).bind (m := 0)
      fun _ => queryBound_pure _ _)
    (E := fun res l =>
      (∃ f : ∀ x, Exec.OracleAnswer (D := D) m params shape wf x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          acceptsPruned m params shape wf f (attempt res.1) = true) ∧
      ClaimsFail P.ldt P.shift (1 - δ)
        (P.claims (Exec.view m params shape (Fri.firstMessage (attempt res.1).commitments
          (attempt res.1).points (attempt res.1).values)) (committedRow l)))
    (fun out l res l' hexp hrun hres hno => by
      obtain ⟨b, l₁, hunp, hpure⟩ := outcome_bind.mp hrun
      obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
      obtain ⟨⟨f, hf, hacc⟩, hfail⟩ := hres
      -- Unpack `unpruneAndVerifyM` outcome into `inComp`, `comComp`, and `verifyGrindView`
      unfold unpruneAndVerifyM at hunp
      obtain ⟨inOpts, l_in, hinOut, hrest1⟩ := outcome_bind.mp hunp
      obtain ⟨comOpts, l_com, hcomOut, hrest2⟩ := outcome_bind.mp hrest1
      -- Show `b = true` by running `unpruneAndVerifyM` against `f` (which agrees with `l'`)
      have hrunF : (unpruneAndVerifyM m params shape wf (attempt out.1) out.2).run f = b := by
        have h1 := hunp.run_toFun f
        rw [Exec.toFun_eq_self hf] at h1
        exact h1
      have hfsEq : out.2 = fsTranscript f ((attempt out.1).messages params shape) (P.rounds + 2) := by
        have hpre : l <+: l' := hunp.prefix
        have h2 := Compiled.eq_fsTranscript_of_outcome_fsExperiment hexp hpre f
        rw [Exec.toFun_eq_self hf] at h2
        exact h2
      have hb_true : b = true := by
        rw [← hrunF, hfsEq]
        exact run_unpruneAndVerifyM_of_acceptsPruned m params shape wf f (attempt out.1) hacc
      -- Therefore `inOpts.mapM id = some inPaths` and `comOpts.mapM id = some comPaths`
      -- and `hrest2` is an `Outcome` of `P.verifyGrindView ... l_com true l'`!
      cases hinM : inOpts.mapM id with
      | none =>
        simp only [hinM] at hrest2
        obtain ⟨rfl, _⟩ := outcome_pure.mp hrest2
        exact absurd hb_true Bool.false_ne_true
      | some inPaths =>
        cases hcomM : comOpts.mapM id with
        | none =>
          simp only [hinM, hcomM] at hrest2
          obtain ⟨rfl, _⟩ := outcome_pure.mp hrest2
          exact absurd hb_true Bool.false_ne_true
        | some comPaths =>
          simp only [hinM, hcomM] at hrest2
          rw [hb_true] at hrest2
          exact ⟨hfail, P.accepts_of_outcome_verifyGrindView hrest2 hno⟩)
  push_cast at hbound ⊢
  exact hbound

end SoundnessPruned

end PrunedRom

end Ix.Cert.MultiStark
