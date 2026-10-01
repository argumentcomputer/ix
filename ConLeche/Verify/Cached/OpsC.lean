module

public import ConLeche.Cached.ExprOpsC
public import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Subst
import ConLeche.Verify.InstList
import ConLeche.Verify.AbstractRange

public section

/-!
# The cached representation's syntactic operations are the pure ones

Task #163, batch 3; rewritten at #172 B3a/B3b.  Every operation of
`ConLeche/Cached/ExprOpsC.lean` — memoized, `Std.HashMap`-backed — is
proved **equal to its `ConLeche.Expr` counterpart**.  These are the
transpositions of the arena twins' `*I_spec` theorems in
`ConLeche/Verify/IExprOps.lean`: same case structure, no store, no
`Ext`, no `TWF`.

Two conjuncts each of these statements used to carry are gone: the
erasure (B3a — one type, so the equation is between the cached and the
pure function at the *same* argument) and the field invariant `WFc` of
the result (B3b — the fields are the compiler's, so there is nothing
for an operation to preserve).  What is left is the memo invariant,
which is real: a clause says every stored value is the pure function at
its key, and insert-preservation goes through
`Std.HashMap.getElem?_insert` plus `beq_sound` on the colliding key —
a memo hit's key is only `BEq`-equal to the query.

That last shape is gone from the walks: not one of them carries a memo
invariant any more (tasks #317, #319).  Each is verified intrinsically
— its result type carries its proof against a plain descent — and its
memo's entries prove themselves, so what this file states about them is
the plain descents (`*P`) and the wrappers.  It survives only where a
memo is not a per-call traversal memo.
-/

namespace ConLeche.Expr

/-! ## Pair keys

The memo tables are keyed by `Expr` paired with cursors.  The
`Std.HashMap` lemmas want `EquivBEq` and `LawfulHashable` of the whole
key type; `Erase.lean` supplies them for `Expr` itself, and products
inherit them componentwise. -/

section PairKey

variable {β : Type} [BEq β] [Hashable β] [EquivBEq β] [LawfulHashable β]

instance : EquivBEq (Expr × β) where
  symm := by
    intro a b h
    simp only [BEq.beq, Bool.and_eq_true] at *
    exact ⟨by rw [beq_eq h.1]; exact beq_self _, BEq.symm h.2⟩
  trans := by
    intro a b c h₁ h₂
    simp only [BEq.beq, Bool.and_eq_true] at *
    exact ⟨by rw [beq_eq h₁.1]; exact h₂.1, BEq.trans h₁.2 h₂.2⟩
  rfl := by
    intro a
    simp only [BEq.beq, Bool.and_eq_true]
    exact ⟨beq_self _, BEq.refl _⟩

instance : LawfulHashable (Expr × β) where
  hash_eq := by
    intro a b h
    simp only [BEq.beq, Bool.and_eq_true] at h
    have h₂ := LawfulHashable.hash_eq _ _ h.2
    simp only [Hashable.hash]
    rw [show Prod.fst a = Prod.fst b from beq_eq h.1]
    exact congrArg _ h₂

omit [Hashable β] [EquivBEq β] [LawfulHashable β] in
/-- The key components of a `BEq`-equal pair key: the `Expr` halves
have equal erasures, the rest is honest equality. -/
theorem pairKey_inv {a c : Expr} {b d : β} (h : ((a, b) == (c, d)) = true) :
    a = c ∧ (b == d) = true := by
  simp only [BEq.beq, Bool.and_eq_true] at h
  exact ⟨beq_sound h.1, h.2⟩

end PairKey

/-! ## Optional results

The arena's `OptDen` (an optional index relates to an optional
expression) transposes to this. -/

/-- An optional cached result agrees with the optional `Expr`-side
result.  (Before task #172 B3b this also carried the field invariant
of the value; the invariant is the compiler's now.) -/
@[expose] def OptEr : Option Expr → Option Expr → Prop
  | none, none => True
  | some e, some x => e = x
  | _, _ => False

/-! ## Spines -/

theorem getAppArgsAccC_spec : ∀ (e : Expr) (acc : List Expr),
    (Expr.getAppArgsAccC e acc) = (Expr.getAppArgs e) ++ acc := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro acc
    rw [show Expr.getAppArgsAccC (.app f a) acc
        = Expr.getAppArgsAccC f (a :: acc) from rfl, ihf,
      show ((.app f a : Expr)).getAppArgs
        = (Expr.getAppArgs f) ++ [a] from rfl,
      List.append_assoc]
    rfl
  | _ => intro acc; rfl

theorem getAppArgsC_spec (e : Expr) :
    (Expr.getAppArgsC e) = (Expr.getAppArgs e) := by
  simpa [Expr.getAppArgsC] using getAppArgsAccC_spec e []

/-! ## Scope queries -/

/-! ## Instantiation of one bound variable

The walks themselves are verified INTRINSICALLY (their result type
carries the proof: `ConLeche/Cached/ExprOpsC.lean`), so what this file
proves is the plain descent each walk is stated against — the `*P`
functions — and the wrappers, which read that proof off the walk's
result through `Expr.resTerm_eq`. -/

/-- **The plain descent computes `Expr.instantiate1`.**  It is the
reference `instantiate1XP` carries its own proof against, so the
wrapper reads through it. -/
theorem instantiate1P_spec {v : Expr} : ∀ (e : Expr) (d : Nat),
    Expr.instantiate1P v e d = Expr.instantiate1 e v d := by
  intro e
  induction e with
  | bvar i =>
    intro d
    rw [Expr.instantiate1P.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
    · dsimp only
      by_cases hid : i = d <;> by_cases hid' : i > d <;>
        simp [Expr.instantiate1, hid, hid']
  | fvar idx ty _ =>
    intro d
    rw [Expr.instantiate1P.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
    · rfl
  | sort u =>
    intro d
    rw [Expr.instantiate1P.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
    · rfl
  | const n us =>
    intro d
    rw [Expr.instantiate1P.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
    · rfl
  | lit l =>
    intro d
    rw [Expr.instantiate1P.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
    · rfl
  | app f a ihf iha =>
    intro d
    rw [Expr.instantiate1P.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
    · dsimp only
      rw [mkApp_eq, ihf d, iha d]
      rfl
  | lam ty bd m iht ihb =>
    intro d
    rw [Expr.instantiate1P.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
    · dsimp only
      rw [mkLam_eq, iht d, ihb (d + 1)]
      rfl
  | forallE ty bd m iht ihb =>
    intro d
    rw [Expr.instantiate1P.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
    · dsimp only
      rw [mkForallE_eq, iht d, ihb (d + 1)]
      rfl
  | letE ty val bd iht ihv ihb =>
    intro d
    rw [Expr.instantiate1P.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
    · dsimp only
      rw [mkLetE_eq, iht d, ihv d, ihb (d + 1)]
      rfl
  | proj sn i sub ih =>
    intro d
    rw [Expr.instantiate1P.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
    · dsimp only
      rw [mkProj_eq, ih d]
      rfl

theorem instantiate1C_spec {e v : Expr} {d : Nat} :
      (Expr.instantiate1C e v d) = (Expr.instantiate1 e v d) := by
  rw [Expr.instantiate1C]
  split
  · rename_i hcut
    exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
  · rw [Expr.resTerm_eq]
    exact instantiate1P_spec e d

/-! ## Bulk instantiation -/

/-! `Expr.instantiateList` is well founded, so it does not reduce
definitionally: the per-constructor equations have to be named. -/

private theorem instList_app (f a : Expr) (ws : List Expr) (d : Nat) :
    (Expr.app f a).instantiateList ws d
      = .app (f.instantiateList ws d) (a.instantiateList ws d) := by
  rw [Expr.instantiateList]

private theorem instList_lam (ty b : Expr) (m : BinderMeta)
    (ws : List Expr) (d : Nat) :
    (Expr.lam ty b m).instantiateList ws d
      = .lam (ty.instantiateList ws d) (b.instantiateList ws (d + 1)) m := by
  rw [Expr.instantiateList]

private theorem instList_forallE (ty b : Expr) (m : BinderMeta)
    (ws : List Expr) (d : Nat) :
    (Expr.forallE ty b m).instantiateList ws d
      = .forallE (ty.instantiateList ws d)
          (b.instantiateList ws (d + 1)) m := by
  rw [Expr.instantiateList]

private theorem instList_letE (ty v b : Expr) (ws : List Expr)
    (d : Nat) :
    (Expr.letE ty v b).instantiateList ws d
      = .letE (ty.instantiateList ws d) (v.instantiateList ws d)
          (b.instantiateList ws (d + 1)) := by
  rw [Expr.instantiateList]

private theorem instList_proj (s : Name) (i : Nat) (e : Expr)
    (ws : List Expr) (d : Nat) :
    (Expr.proj s i e).instantiateList ws d
      = .proj s i (e.instantiateList ws d) := by
  rw [Expr.instantiateList]

/-- The leaf arms: `fvar`/`sort`/`const`/`lit` erasures are
`looseBVarsBounded` at every cursor, so bulk instantiation is the
identity on them (`Expr.instantiateList` is well-founded, hence does
not reduce definitionally — the equation has to be supplied). -/
private theorem instList_leaf {e : Expr} {ws : List Expr} {d : Nat}
    (h : (Expr.looseBVarsBounded d e) = true) :
    e = (Expr.instantiateList e ws d) :=
  (Expr.instantiateList_eq_self h).symm

/-- **The plain bulk descent computes `Expr.instantiateList`.**  The
induction is strong on the live prefix `k` (the `bvar` arm re-enters
at the replacement with a shorter prefix) and structural on the node
inside it.  The reference of `instantiateListXP`. -/
theorem instantiateListP_spec {vs : Array Expr} :
    ∀ (k : Nat) (e : Expr), ∀ {d : Nat}, k ≤ vs.size →
      Expr.instantiateListP vs e k d
        = Expr.instantiateList e (vs.toList.take k) d := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro e
  induction e with
  | bvar i =>
    intro d hk
    rw [Expr.instantiateListP.eq_def]
    split
    · rename_i hk0
      subst hk0
      simp [Expr.instantiateList_nil]
    · split
      · rename_i hcut
        exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
      · rename_i hk0 hcut
        have hlen : ((vs.toList).take k).length = k := by
          simp; omega
        dsimp only
        split
        · rename_i hid
          simp [Expr.instantiateList, hid]
        · rename_i hid
          split
          · rename_i hidk
            split
            · rename_i hidv
              have hget : ((vs.toList).take k)[i - d]'(by
                  rw [hlen]; exact hidk) = vs[i - d] := by
                rw [List.getElem_take]
                simp
              have htk : ((vs.toList).take k).take (i - d)
                  = (vs.toList).take (i - d) := by
                rw [List.take_take]
                congr 1
                omega
              have hRHS : (Expr.instantiateList (Expr.bvar i)
                    ((vs.toList).take k) d)
                  = (Expr.instantiateList vs[i - d]
                      ((vs.toList).take (i - d)) d) := by
                rw [Expr.instantiateList, if_neg hid,
                  dif_pos (by rw [hlen]; exact hidk), hget, htk]
              split
              · rename_i hfast
                rw [hRHS]
                rcases Bool.or_eq_true .. |>.mp hfast with h0 | hb
                · have hnil : (vs.toList).take (i - d) = [] := by
                    have h0' : i - d = 0 := by simpa using h0
                    rw [h0']
                    simp
                  rw [hnil]
                  exact (Expr.instantiateList_nil _ _).symm
                · have hb' : vs[i - d].bvarB ≤ d := by simpa using hb
                  exact (Expr.instantiateList_eq_self (bvarB_le hb')).symm
              · rw [hRHS]
                exact ihk (i - d) hidk vs[i - d] (d := d)
                  (Nat.le_of_lt hidv)
            · rename_i hidv
              exact absurd (by omega : i - d < vs.size) hidv
          · rename_i hidk
            rw [Expr.mkBvar_eq, Expr.instantiateList,
              if_neg hid, dif_neg (by rw [hlen]; exact hidk), hlen]
  | fvar idx ty _ =>
    intro d hk
    rw [Expr.instantiateListP.eq_def]
    split
    · rename_i hk0
      subst hk0
      simp [Expr.instantiateList_nil]
    · split
      · rename_i hcut
        exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
      · exact instList_leaf rfl
  | sort u =>
    intro d hk
    rw [Expr.instantiateListP.eq_def]
    split
    · rename_i hk0
      subst hk0
      simp [Expr.instantiateList_nil]
    · split
      · rename_i hcut
        exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
      · exact instList_leaf rfl
  | const n us =>
    intro d hk
    rw [Expr.instantiateListP.eq_def]
    split
    · rename_i hk0
      subst hk0
      simp [Expr.instantiateList_nil]
    · split
      · rename_i hcut
        exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
      · exact instList_leaf rfl
  | lit l =>
    intro d hk
    rw [Expr.instantiateListP.eq_def]
    split
    · rename_i hk0
      subst hk0
      simp [Expr.instantiateList_nil]
    · split
      · rename_i hcut
        exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
      · exact instList_leaf rfl
  | app f a ihf iha =>
    intro d hk
    rw [Expr.instantiateListP.eq_def]
    split
    · rename_i hk0
      subst hk0
      simp [Expr.instantiateList_nil]
    · split
      · rename_i hcut
        exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
      · dsimp only
        rw [instList_app, mkApp_eq, ihf (d := d) hk, iha (d := d) hk]
  | lam ty bd m iht ihb =>
    intro d hk
    rw [Expr.instantiateListP.eq_def]
    split
    · rename_i hk0
      subst hk0
      simp [Expr.instantiateList_nil]
    · split
      · rename_i hcut
        exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
      · dsimp only
        rw [instList_lam, mkLam_eq, iht (d := d) hk, ihb (d := d + 1) hk]
  | forallE ty bd m iht ihb =>
    intro d hk
    rw [Expr.instantiateListP.eq_def]
    split
    · rename_i hk0
      subst hk0
      simp [Expr.instantiateList_nil]
    · split
      · rename_i hcut
        exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
      · dsimp only
        rw [instList_forallE, mkForallE_eq, iht (d := d) hk, ihb (d := d + 1) hk]
  | letE ty val bd iht ihv ihb =>
    intro d hk
    rw [Expr.instantiateListP.eq_def]
    split
    · rename_i hk0
      subst hk0
      simp [Expr.instantiateList_nil]
    · split
      · rename_i hcut
        exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
      · dsimp only
        rw [instList_letE, mkLetE_eq, iht (d := d) hk, ihv (d := d) hk,
          ihb (d := d + 1) hk]
  | proj sn i sub ih =>
    intro d hk
    rw [Expr.instantiateListP.eq_def]
    split
    · rename_i hk0
      subst hk0
      simp [Expr.instantiateList_nil]
    · split
      · rename_i hcut
        exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
      · dsimp only
        rw [instList_proj, mkProj_eq, ih (d := d) hk]

theorem instantiateListC_spec {e : Expr} {vs : List Expr} {d : Nat} :
    (Expr.instantiateListC e vs d)
      = (Expr.instantiateList e vs d) := by
  cases vs with
  | nil => rw [Expr.instantiateListC]; simp [Expr.instantiateList_nil]
  | cons v vs' =>
    have harr : (v :: vs').toArray.toList = v :: vs' := rfl
    have htail : ∀ x : Expr,
        x = (Expr.instantiateList e
              ((v :: vs').toArray.toList.take (v :: vs').toArray.size) d) →
        x = (Expr.instantiateList e (v :: vs') d) := by
      intro x hx
      rw [hx, harr]
      congr 1
      rw [show (v :: vs').toArray.size = ((v :: vs')).length from
          by simp, List.take_length]
    rw [Expr.instantiateListC]
    dsimp only
    split
    · rename_i hcut
      exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
    · rw [Expr.resTerm_eq]
      exact htail _ (instantiateListP_spec (vs := (v :: vs').toArray)
        (v :: vs').toArray.size e (d := d) (Nat.le_refl _))

/-! ## Telescope-context spine instantiation -/

theorem instSpineChainC_spec : ∀ (args : List Expr) (t : Nat) (e : Expr),
    (Expr.instSpineChainC args t e) = Expr.instSpine args t e
  | [], _, _ => rfl
  | a :: as, t, e => by
    have h2 := instantiate1C_spec (e := e) (v := a) (d := t)
    have h4 := instSpineChainC_spec as (t - 1) (Expr.instantiate1C e a t)
    rw [show Expr.instSpineChainC (a :: as) t e
        = Expr.instSpineChainC as (t - 1) (Expr.instantiate1C e a t) from rfl, h4, h2]
    rfl

theorem instSpineC_spec {args : List Expr} {t : Nat} {e : Expr} :
    (Expr.instSpineC args t e) = Expr.instSpine args t e := by
  rw [Expr.instSpineC]
  split
  · rename_i hlen
    have hxlen : args.length = t + 1 := by simpa using hlen
    have h2 := instantiateListC_spec (e := e) (vs := args.reverse) (d := 0)
    rw [h2, Expr.instSpine_eq_instantiateList _ t _ hxlen]
  · exact instSpineChainC_spec args t e

/-! ## Bulk instantiation on a reversed accumulator

As in the arena (`instantiateRevIGo_eq`), the reversed walk is the
forward walk on the reversed array — proved pointwise, so every
`instantiateList` fact transfers. -/

/-- The reversed plain descent is the forward one on the reversed
array — `instantiateRevBC_eq` without the fuel, so every
`instantiateList` fact transfers unchanged. -/
theorem instantiateRevP_eq {vs : Array Expr} :
    ∀ (k : Nat) (e : Expr) (d : Nat),
      Expr.instantiateRevP vs e k d
        = Expr.instantiateListP vs.reverse e k d := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro e
  induction e with
  | bvar i =>
    intro d
    rw [Expr.instantiateRevP.eq_def, Expr.instantiateListP.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.bvar i).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    dsimp only
    by_cases hid : i < d
    · rw [if_pos hid, if_pos hid]
    rw [if_neg hid, if_neg hid]
    by_cases hidk : i - d < k
    · rw [dif_pos hidk, dif_pos hidk]
      have hsz : vs.reverse.size = vs.size := by simp
      by_cases hidv : i - d < vs.size
      · rw [dif_pos hidv, dif_pos (hsz ▸ hidv)]
        have hget : vs.reverse[i - d]'(hsz ▸ hidv)
            = vs[vs.size - 1 - (i - d)]'(by omega) := by
          simp [Array.getElem_reverse]
        rw [ihk (i - d) hidk, hget]
      · rw [dif_neg hidv, dif_neg (fun h => hidv (hsz ▸ h))]
    · rw [dif_neg hidk, dif_neg hidk]
  | fvar idx ty _ =>
    intro d
    rw [Expr.instantiateRevP.eq_def, Expr.instantiateListP.eq_def]
  | sort u =>
    intro d
    rw [Expr.instantiateRevP.eq_def, Expr.instantiateListP.eq_def]
  | const n us =>
    intro d
    rw [Expr.instantiateRevP.eq_def, Expr.instantiateListP.eq_def]
  | lit l =>
    intro d
    rw [Expr.instantiateRevP.eq_def, Expr.instantiateListP.eq_def]
  | app f a ihf iha =>
    intro d
    rw [Expr.instantiateRevP.eq_def, Expr.instantiateListP.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.app f a).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    dsimp only
    rw [ihf d, iha d]
  | lam ty bd m iht ihb =>
    intro d
    rw [Expr.instantiateRevP.eq_def, Expr.instantiateListP.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.lam ty bd m).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    dsimp only
    rw [iht d, ihb (d + 1)]
  | forallE ty bd m iht ihb =>
    intro d
    rw [Expr.instantiateRevP.eq_def, Expr.instantiateListP.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.forallE ty bd m).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    dsimp only
    rw [iht d, ihb (d + 1)]
  | letE ty val bd iht ihv ihb =>
    intro d
    rw [Expr.instantiateRevP.eq_def, Expr.instantiateListP.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.letE ty val bd).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    dsimp only
    rw [iht d, ihv d, ihb (d + 1)]
  | proj sn i sub ih =>
    intro d
    rw [Expr.instantiateRevP.eq_def, Expr.instantiateListP.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.proj sn i sub).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    dsimp only
    rw [ih d]

theorem instantiateRev_spec {e : Expr} {vs : Array Expr} {d : Nat}
    :
      (Expr.instantiateRev e vs d)
        = (Expr.instantiateList e (vs.toList.reverse) d) := by
  have hws : vs.reverse.toList = vs.toList.reverse := by
    simp
  rw [instantiateRev]
  split
  · rename_i h0
    have hnil : vs.toList.reverse = [] := by
      have he : vs.toList = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using h0
      simp [he]
    rw [hnil]
    exact (Expr.instantiateList_nil _ _).symm
  · split
    · rename_i hcut
      exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
    · have htail : ∀ x : Expr,
          x = (Expr.instantiateList e (vs.reverse.toList.take vs.size) d) →
          x = (Expr.instantiateList e vs.toList.reverse d) := by
        intro x hx
        rw [hx, hws]
        congr 1
        rw [show vs.size = (vs.toList.reverse).length from by simp,
          List.take_length]
      rw [Expr.resTerm_eq]
      exact htail _ ((instantiateRevP_eq vs.size e d).trans
        (instantiateListP_spec (vs := vs.reverse) vs.size e (d := d)
          (by simp)))

/-! ## Abstraction

The clone's abstraction walks carry a **documented deviation** from the
arena twins: a node whose cached fvar range is at or below the
abstracted level is returned unchanged (the arena does not need the
cutoff — its rebuild re-interns to the same index).  The identity is
exactly `abstractRange_eq_self` / its `abstract1` twin below, so the
value is the same either way. -/

/-- `Expr.abstract1` at or above a term's fvar range is the identity —
the `abstract1` twin of `abstractRange_eq_self`, which `ConLeche/Verify`
has only for the bulk form. -/
private theorem abstract1_eq_self : ∀ {e : Expr} {d k : Nat},
    Expr.fvarsBelow d e → e.abstract1 d k = e := by
  intro e
  induction e <;> intro d k hb <;>
    simp_all only [Expr.fvarsBelow, Expr.abstract1]
  rw [if_neg (by omega)]

/-- **The plain descent computes `Expr.abstract1`**: the reference of
`abstract1XP`. -/
theorem abstract1P_spec {d : Nat} : ∀ (e : Expr) (k : Nat),
    Expr.abstract1P d e k = Expr.abstract1 e d k := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro k
    rw [Expr.abstract1P.eq_def]
    split
    · rename_i hcut
      exact (abstract1_eq_self (fvarB_le hcut)).symm
    · dsimp only
      by_cases hidx : idx = d <;> simp [Expr.abstract1, hidx]
  | bvar i =>
    intro k
    rw [Expr.abstract1P.eq_def]
    split
    · rename_i hcut
      exact (abstract1_eq_self (fvarB_le hcut)).symm
    · rfl
  | sort u =>
    intro k
    rw [Expr.abstract1P.eq_def]
    split
    · rename_i hcut
      exact (abstract1_eq_self (fvarB_le hcut)).symm
    · rfl
  | const n us =>
    intro k
    rw [Expr.abstract1P.eq_def]
    split
    · rename_i hcut
      exact (abstract1_eq_self (fvarB_le hcut)).symm
    · rfl
  | lit l =>
    intro k
    rw [Expr.abstract1P.eq_def]
    split
    · rename_i hcut
      exact (abstract1_eq_self (fvarB_le hcut)).symm
    · rfl
  | app f a ihf iha =>
    intro k
    rw [Expr.abstract1P.eq_def]
    split
    · rename_i hcut
      exact (abstract1_eq_self (fvarB_le hcut)).symm
    · dsimp only
      rw [mkApp_eq, ihf k, iha k]
      rfl
  | lam ty bd m iht ihb =>
    intro k
    rw [Expr.abstract1P.eq_def]
    split
    · rename_i hcut
      exact (abstract1_eq_self (fvarB_le hcut)).symm
    · dsimp only
      rw [mkLam_eq, iht k, ihb (k + 1)]
      rfl
  | forallE ty bd m iht ihb =>
    intro k
    rw [Expr.abstract1P.eq_def]
    split
    · rename_i hcut
      exact (abstract1_eq_self (fvarB_le hcut)).symm
    · dsimp only
      rw [mkForallE_eq, iht k, ihb (k + 1)]
      rfl
  | letE ty val bd iht ihv ihb =>
    intro k
    rw [Expr.abstract1P.eq_def]
    split
    · rename_i hcut
      exact (abstract1_eq_self (fvarB_le hcut)).symm
    · dsimp only
      rw [mkLetE_eq, iht k, ihv k, ihb (k + 1)]
      rfl
  | proj sn i sub ih =>
    intro k
    rw [Expr.abstract1P.eq_def]
    split
    · rename_i hcut
      exact (abstract1_eq_self (fvarB_le hcut)).symm
    · dsimp only
      rw [mkProj_eq, ih k]
      rfl

theorem abstract1C_spec {e : Expr} {d k : Nat} :
      (Expr.abstract1C e d k) = (Expr.abstract1 e d k) := by
  rw [Expr.abstract1C]
  split
  · rename_i hcut
    exact (abstract1_eq_self (fvarB_le hcut)).symm
  · rw [Expr.resTerm_eq]
    exact abstract1P_spec e k

/-! ### Bulk abstraction -/

/-- Abstracting an empty range is the identity. -/
private theorem abstractRange_zero : ∀ (e : Expr) (d c : Nat),
    e.abstractRange d 0 c = e := by
  intro e
  induction e <;> intro d c <;> simp_all [Expr.abstractRange]

/-- **The plain bulk descent computes `Expr.abstractRange`**: the
reference of `abstractRangeXP`. -/
theorem abstractRangeP_spec {d k : Nat} : ∀ (e : Expr) (c : Nat),
    Expr.abstractRangeP d k e c = Expr.abstractRange e d k c := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro c
    rw [Expr.abstractRangeP.eq_def]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · dsimp only
      by_cases hidx : d ≤ idx ∧ idx < d + k <;> simp [Expr.abstractRange, hidx]
  | bvar i =>
    intro c
    rw [Expr.abstractRangeP.eq_def]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · rfl
  | sort u =>
    intro c
    rw [Expr.abstractRangeP.eq_def]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · rfl
  | const n us =>
    intro c
    rw [Expr.abstractRangeP.eq_def]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · rfl
  | lit l =>
    intro c
    rw [Expr.abstractRangeP.eq_def]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · rfl
  | app f a ihf iha =>
    intro c
    rw [Expr.abstractRangeP.eq_def]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · dsimp only
      rw [mkApp_eq, ihf c, iha c]
      rfl
  | lam ty bd m iht ihb =>
    intro c
    rw [Expr.abstractRangeP.eq_def]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · dsimp only
      rw [mkLam_eq, iht c, ihb (c + 1)]
      rfl
  | forallE ty bd m iht ihb =>
    intro c
    rw [Expr.abstractRangeP.eq_def]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · dsimp only
      rw [mkForallE_eq, iht c, ihb (c + 1)]
      rfl
  | letE ty val bd iht ihv ihb =>
    intro c
    rw [Expr.abstractRangeP.eq_def]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · dsimp only
      rw [mkLetE_eq, iht c, ihv c, ihb (c + 1)]
      rfl
  | proj sn i sub ih =>
    intro c
    rw [Expr.abstractRangeP.eq_def]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · dsimp only
      rw [mkProj_eq, ih c]
      rfl

theorem abstractRangeC_spec {e : Expr} {d k c : Nat} :
      (Expr.abstractRangeC e d k c) = (Expr.abstractRange e d k c) := by
  cases k with
  | zero => exact (abstractRange_zero _ _ _).symm
  | succ k' =>
    rw [Expr.abstractRangeC]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · rw [Expr.resTerm_eq]
      exact abstractRangeP_spec e c

/-! ## Level instantiation -/

/-- **The plain descent computes `Expr.instantiateLevelParams`**: the
reference of `instLevelParamsXP`. -/
theorem instLevelParamsP_spec {ks : List Name} {us : List Level} : ∀ (e : Expr),
    Expr.instLevelParamsP ks us e = e.instantiateLevelParams ks us := by
  intro e
  induction e with
  | bvar i =>
    rw [Expr.instLevelParamsP.eq_def]
    split
    · exact (hasLP_false (by simp)).symm
    · rfl
  | lit l =>
    rw [Expr.instLevelParamsP.eq_def]
    split
    · exact (hasLP_false (by simp)).symm
    · rfl
  | sort u =>
    rw [Expr.instLevelParamsP.eq_def]
    split
    · rename_i hcut
      exact (hasLP_false (by simpa using hcut)).symm
    · rfl
  | const n vs =>
    rw [Expr.instLevelParamsP.eq_def]
    split
    · rename_i hcut
      exact (hasLP_false (by simpa using hcut)).symm
    · rfl
  | fvar idx ty iht =>
    rw [Expr.instLevelParamsP.eq_def]
    split
    · rename_i hcut
      exact (hasLP_false (by simpa using hcut)).symm
    · dsimp only
      rw [mkFVar_eq, iht]
      rfl
  | app f a ihf iha =>
    rw [Expr.instLevelParamsP.eq_def]
    split
    · rename_i hcut
      exact (hasLP_false (by simpa using hcut)).symm
    · dsimp only
      rw [mkApp_eq, ihf, iha]
      rfl
  | lam ty bd m iht ihb =>
    rw [Expr.instLevelParamsP.eq_def]
    split
    · rename_i hcut
      exact (hasLP_false (by simpa using hcut)).symm
    · dsimp only
      rw [mkLam_eq, iht, ihb]
      rfl
  | forallE ty bd m iht ihb =>
    rw [Expr.instLevelParamsP.eq_def]
    split
    · rename_i hcut
      exact (hasLP_false (by simpa using hcut)).symm
    · dsimp only
      rw [mkForallE_eq, iht, ihb]
      rfl
  | letE ty val bd iht ihv ihb =>
    rw [Expr.instLevelParamsP.eq_def]
    split
    · rename_i hcut
      exact (hasLP_false (by simpa using hcut)).symm
    · dsimp only
      rw [mkLetE_eq, iht, ihv, ihb]
      rfl
  | proj sn i sub ih =>
    rw [Expr.instLevelParamsP.eq_def]
    split
    · rename_i hcut
      exact (hasLP_false (by simpa using hcut)).symm
    · dsimp only
      rw [mkProj_eq, ih]
      rfl

theorem instLevelParams_spec {ks : List Name} {us : List Level} {e : Expr} :
    (Expr.instLevelParams ks us e) = e.instantiateLevelParams ks us := by
  rw [instLevelParams]
  split
  · rename_i hcut
    exact (hasLP_false (by simpa using hcut)).symm
  · rw [Expr.resTerm_eq]
    exact instLevelParamsP_spec e

/-- The executable projection-type instantiation is the spec's
(`ProjEntry.typeAt`), value for value — the two memoized walks each
equal their tree-walk spec. -/
theorem _root_.ConLeche.ProjEntry.typeAtI_eq (entry : ProjEntry) (us : List Level)
    (targs : List Expr) (pe : Expr) :
    entry.typeAtI us targs pe = entry.typeAt us targs pe := by
  unfold ProjEntry.typeAtI ProjEntry.typeAt
  rw [instantiateListC_spec, instLevelParams_spec]

/-! ## The scope walk

`Expr.wscopedB` is well founded (on `sizeF`, since it descends into
`fvar` annotations), so its per-constructor equations are named here
too. -/

private theorem wscopedB_bvar (i d : Nat) :
    (Expr.bvar i).wscopedB d = true := by rw [Expr.wscopedB]

private theorem wscopedB_sort (u : Level) (d : Nat) :
    (Expr.sort u).wscopedB d = true := by rw [Expr.wscopedB]

private theorem wscopedB_const (n : Name) (us : List Level) (d : Nat) :
    (Expr.const n us).wscopedB d = true := by rw [Expr.wscopedB]

private theorem wscopedB_lit (l : Literal) (d : Nat) :
    (Expr.lit l).wscopedB d = true := by rw [Expr.wscopedB]

private theorem wscopedB_fvar (idx : Nat) (ty : Expr) (d : Nat) :
    (Expr.fvar idx ty).wscopedB d
      = (decide (idx < d) && ty.wscopedB idx) := by rw [Expr.wscopedB]

private theorem wscopedB_app (f a : Expr) (d : Nat) :
    (Expr.app f a).wscopedB d = (f.wscopedB d && a.wscopedB d) := by
  rw [Expr.wscopedB]

private theorem wscopedB_lam (ty b : Expr) (m : BinderMeta)
    (d : Nat) :
    (Expr.lam ty b m).wscopedB d = (ty.wscopedB d && b.wscopedB d) := by
  rw [Expr.wscopedB]

private theorem wscopedB_forallE (ty b : Expr) (m : BinderMeta)
    (d : Nat) :
    (Expr.forallE ty b m).wscopedB d = (ty.wscopedB d && b.wscopedB d) := by
  rw [Expr.wscopedB]

private theorem wscopedB_letE (ty v b : Expr) (d : Nat) :
    (Expr.letE ty v b).wscopedB d
      = (ty.wscopedB d && v.wscopedB d && b.wscopedB d) := by
  rw [Expr.wscopedB]

private theorem wscopedB_proj (s : Name) (i : Nat) (e : Expr) (d : Nat) :
    (Expr.proj s i e).wscopedB d = e.wscopedB d := by rw [Expr.wscopedB]

/-- The clone's `fvarB == 0` shortcut: a node whose cached fvar range is
zero has no `fvar` leaf at all (annotations only exist under `fvar`
nodes), so it is well scoped at every cursor.  The arena twin has no
such cutoff. -/
private theorem wscopedB_of_fvarsBelow_zero : ∀ (e : Expr),
    Expr.fvarsBelow 0 e → ∀ d, e.wscopedB d = true := by
  intro e
  induction e <;> intro hb d <;> simp_all [Expr.fvarsBelow, Expr.wscopedB]

/-- The walk's cutoff, read as the specification: a node whose cached
fvar range is zero is well scoped at every cursor. -/
private theorem wscopedBP_cut_spec {e : Expr} {d : Nat} (h : (e.fvarB == 0) = true) :
    true = Expr.wscopedB d e :=
  (wscopedB_of_fvarsBelow_zero _ (fvarB_le (Nat.le_of_eq (by simpa using h))) d).symm

/-- **The plain descent is `Expr.wscopedB`.** -/
theorem wscopedBP_spec : ∀ (e : Expr) (d : Nat),
    Expr.wscopedBP e d = Expr.wscopedB d e := by
  intro e
  induction e with
  | bvar i =>
    intro d; rw [Expr.wscopedBP.eq_def]; split <;> exact (wscopedB_bvar i d).symm
  | sort u =>
    intro d; rw [Expr.wscopedBP.eq_def]; split <;> exact (wscopedB_sort u d).symm
  | const n us =>
    intro d; rw [Expr.wscopedBP.eq_def]; split <;> exact (wscopedB_const n us d).symm
  | lit l =>
    intro d; rw [Expr.wscopedBP.eq_def]; split <;> exact (wscopedB_lit l d).symm
  | fvar idx ty iht =>
    intro d
    rw [Expr.wscopedBP.eq_def]
    split
    · next h => exact wscopedBP_cut_spec h
    · simp only [wscopedB_fvar, iht]
  | app f a ihf iha =>
    intro d
    rw [Expr.wscopedBP.eq_def]
    split
    · next h => exact wscopedBP_cut_spec h
    · simp only [wscopedB_app, ihf, iha]
  | lam ty bd m iht ihb =>
    intro d
    rw [Expr.wscopedBP.eq_def]
    split
    · next h => exact wscopedBP_cut_spec h
    · simp only [wscopedB_lam, iht, ihb]
  | forallE ty bd m iht ihb =>
    intro d
    rw [Expr.wscopedBP.eq_def]
    split
    · next h => exact wscopedBP_cut_spec h
    · simp only [wscopedB_forallE, iht, ihb]
  | letE ty val bd iht ihv ihb =>
    intro d
    rw [Expr.wscopedBP.eq_def]
    split
    · next h => exact wscopedBP_cut_spec h
    · simp only [wscopedB_letE, iht, ihv, ihb]
  | proj s i sub ihe =>
    intro d
    rw [Expr.wscopedBP.eq_def]
    split
    · next h => exact wscopedBP_cut_spec h
    · simp only [wscopedB_proj, ihe]

theorem wscopedBC_spec {d : Nat} {e : Expr} :
    Expr.wscopedBC d e = (Expr.wscopedB d e) := by
  rw [Expr.wscopedBC.eq_def]
  split
  · next h => exact wscopedBP_cut_spec h
  · rw [Expr.resBool_eq]; exact wscopedBP_spec e d

/-! ## The `∀`-telescope residual

`piResidualAcc` follows the arena twin's accumulator discipline: the
`forallE` arm consumes an argument into the accumulator, the `bvar` arm
flushes a nonempty accumulator by one bulk instantiation and re-enters.
The induction is the function's own measure `(as.length, acc.length)`. -/

theorem piResidualAcc_spec :
    ∀ (as acc : List Expr) (e : Expr),
      OptEr (Expr.piResidualAcc acc e as)
        (_root_.ConLeche.piResidual
          ((Expr.instantiateList e acc)) as)
  | [], acc, e => by
    rw [piResidualAcc.eq_def]
    exact instantiateListC_spec (d := 0)
  | a :: as, acc, e => by
    cases e with
    | forallE ty b m =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [instList_forallE,
        show _root_.ConLeche.piResidual
            (Expr.forallE ((Expr.instantiateList ty acc 0))
              ((Expr.instantiateList b acc 1)) m)
            (a :: as)
          = _root_.ConLeche.piResidual
              (((Expr.instantiateList b acc 1)).instantiate1
                a) as from rfl,
        ← Expr.instantiateList_cons]
      exact piResidualAcc_spec as (a :: acc) b
    | bvar i =>
      rw [piResidualAcc.eq_def]
      dsimp only
      cases acc with
      | nil =>
        rw [Expr.instantiateList_nil]
        exact trivial
      | cons a' acc' =>
        have h2 :=
          instantiateListC_spec (e := Expr.bvar i)
            (vs := a' :: acc') (d := 0)
        have hrec := piResidualAcc_spec (a :: as) []
          (Expr.instantiateListC (Expr.bvar i) (a' :: acc') 0)
        rw [Expr.instantiateList_nil] at hrec
        rw [← h2]
        exact hrec
    | fvar idx ty =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.fvar idx ty)
        (ws := acc) (d := 0) rfl]
      exact trivial
    | sort u =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.sort u)
        (ws := acc) (d := 0) rfl]
      exact trivial
    | const n us =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.const n us)
        (ws := acc) (d := 0) rfl]
      exact trivial
    | lit l =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.lit l)
        (ws := acc) (d := 0) rfl]
      exact trivial
    | app f a' =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [instList_app]
      exact trivial
    | lam ty b m =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [instList_lam]
      exact trivial
    | letE ty v b =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [instList_letE]
      exact trivial
    | proj s i sub =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [instList_proj]
      exact trivial
termination_by as acc => (as.length, acc.length)
decreasing_by
  · apply Prod.Lex.right' <;> simp_all
  · apply Prod.Lex.left; simp

theorem piResidual_spec {e : Expr} {args : List Expr} :
    OptEr (Expr.piResidual e args)
      (_root_.ConLeche.piResidual e args) := by
  have h := piResidualAcc_spec args [] e
  rw [Expr.instantiateList_nil] at h
  exact h

/-! ## The capture-avoiding instantiation (task #214, P4)

`instantiate1Lift`'s twin: the same two facts as `instantiate1`'s —
the cutoff is `Expr.instantiate1Lift_eq_self`, and the plain descent
rebuilds exactly the substitution. -/

/-- **The plain descent computes `Expr.instantiate1Lift`**: the
reference of `instantiate1LiftXP`. -/
theorem instantiate1LiftP_spec {v : Expr} : ∀ (e : Expr) (d : Nat),
    Expr.instantiate1LiftP v e d = Expr.instantiate1Lift e v d := by
  intro e
  induction e with
  | bvar i =>
    intro d
    rw [Expr.instantiate1LiftP.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
    · dsimp only
      by_cases hid : i = d <;> by_cases hid' : i > d <;>
        simp [Expr.instantiate1Lift, hid, hid']
  | fvar idx ty _ =>
    intro d
    rw [Expr.instantiate1LiftP.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
    · rfl
  | sort u =>
    intro d
    rw [Expr.instantiate1LiftP.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
    · rfl
  | const n us =>
    intro d
    rw [Expr.instantiate1LiftP.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
    · rfl
  | lit l =>
    intro d
    rw [Expr.instantiate1LiftP.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
    · rfl
  | app f a ihf iha =>
    intro d
    rw [Expr.instantiate1LiftP.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
    · dsimp only
      rw [mkApp_eq, ihf d, iha d]
      rfl
  | lam ty bd m iht ihb =>
    intro d
    rw [Expr.instantiate1LiftP.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
    · dsimp only
      rw [mkLam_eq, iht d, ihb (d + 1)]
      rfl
  | forallE ty bd m iht ihb =>
    intro d
    rw [Expr.instantiate1LiftP.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
    · dsimp only
      rw [mkForallE_eq, iht d, ihb (d + 1)]
      rfl
  | letE ty val bd iht ihv ihb =>
    intro d
    rw [Expr.instantiate1LiftP.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
    · dsimp only
      rw [mkLetE_eq, iht d, ihv d, ihb (d + 1)]
      rfl
  | proj sn i sub ih =>
    intro d
    rw [Expr.instantiate1LiftP.eq_def]
    split
    · rename_i hcut
      exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
    · dsimp only
      rw [mkProj_eq, ih d]
      rfl

/-- **`instantiate1Lift`'s twin computes `Expr.instantiate1Lift`.** -/
theorem instantiate1LiftC_spec (e v : Expr) (d : Nat) :
    Expr.instantiate1LiftC e v d = Expr.instantiate1Lift e v d := by
  unfold Expr.instantiate1LiftC
  split
  · rename_i hcut
    exact (Expr.instantiate1Lift_eq_self (bvarB_le hcut)).symm
  · rw [Expr.resTerm_eq]
    exact instantiate1LiftP_spec e d

end ConLeche.Expr
