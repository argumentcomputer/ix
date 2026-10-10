import Ix.CompileCert.Conv
import Ix.Compile.Pass.Opt.Engine

/-!
# M7 L3-def: telescopes, their β-reduction, and selections of arguments

The definitional passes (`Ix/Compile/Pass/Opt/{O1,…,O6,O11a}.lean`) replace an occurrence
`a.{us} a₁ … a_m` of an image-kind auxiliary by an Ix auxiliary applied to a selection of the same
arguments. Their faithfulness (design document §1.5, each module's *Faithfulness*) is a chain of
δ-steps (a head's value, a λ over a telescope) and β-steps (the telescope applied to the
arguments). This module gives the β-steps in one lemma and the arithmetic of argument lists:

* `lamN ts b`: the λ-telescope with binder types `ts` and body `b`; `betaN as b`: the body with
  the arguments `as` substituted (the result of `|as|` β-steps, `beta_lamN`);
* `betaN_bvar`: telescope position `p` (the bound variable `bvar (|as| - 1 - p)` of the body) is
  replaced by `as[p]`; `betaN_appN`, `betaN_const`: the substitution goes through spines and
  leaves constants;
* `gL L p`: position `p` of an argument list; a **selection** is `idx.map (gL L)`; selections
  compose (`sel_sel`);
* **`delta_sel`**: a head whose δ-rule is a telescope over `c.{ls}` applied to telescope positions
  `idx` converts, at an occurrence, to `c.{ls}` applied to the selection `idx` of the arguments
  and the arguments past the telescope;
* `argT a i`: the erasure of argument `i` of an array; the compiler's `Array.extract` slices and
  `pick` selections erase to selections (`extract_map`, `pick_extract`).
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (getAppFnArgs mkAppN)
open Ix.Compile.Pass.Opt (Occ)

/-! ## Telescopes -/

/-- The λ-telescope `λ (x₁ : t₁) … (xₙ : tₙ). b`. -/
def lamN : List Tm → Tm → Tm
  | [], b => b
  | t :: ts, b => .lam t (lamN ts b)

/-- The binder types of a telescope after a substitution at `k` (each one binder deeper). -/
def instTs (v : Tm) : Nat → List Tm → List Tm
  | _, [] => []
  | k, t :: ts => Tm.inst v k t :: instTs v (k + 1) ts

theorem instTs_length (v : Tm) : ∀ (k : Nat) (ts : List Tm), (instTs v k ts).length = ts.length
  | _, [] => rfl
  | k, _ :: ts => by simp only [instTs, List.length_cons, instTs_length v (k + 1) ts]

theorem inst_lamN (v : Tm) : ∀ (ts : List Tm) (k : Nat) (b : Tm),
    Tm.inst v k (lamN ts b) = lamN (instTs v k ts) (Tm.inst v (k + ts.length) b)
  | [], k, b => by simp only [lamN, instTs, List.length_nil, Nat.add_zero]
  | t :: ts, k, b => by
    simp only [lamN, instTs, Tm.inst, List.length_cons]
    rw [inst_lamN v ts (k + 1) b, show k + 1 + ts.length = k + (ts.length + 1) by omega]

/-- The body of a telescope with the arguments substituted: `as[0]` for the outermost binder.
`betaN (a :: as) b = betaN as (b[|as| := a])`. -/
def betaN : List Tm → Tm → Tm
  | [], b => b
  | a :: as, b => betaN as (Tm.inst a as.length b)

/-- **β on a telescope**: a telescope of `|as|` binders applied to `as ++ rest` converts to its
body with `as` substituted, applied to `rest`. -/
theorem beta_lamN {Γ : Env} : ∀ (as ts : List Tm) (b : Tm) (rest : List Tm),
    ts.length = as.length → Conv Γ (Tm.appN (lamN ts b) (as ++ rest)) (Tm.appN (betaN as b) rest)
  | [], [], b, rest, _ => .refl _
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, t :: ts, b, rest, h => by
    have hl : ts.length = as.length := by simpa using h
    have h1 : Conv Γ (Tm.appN (lamN (t :: ts) b) ((a :: as) ++ rest))
        (Tm.appN (Tm.inst a 0 (lamN ts b)) (as ++ rest)) := by
      simp only [lamN, List.cons_append]
      exact Conv.beta_appN t (lamN ts b) a (as ++ rest)
    have h2 : Tm.inst a 0 (lamN ts b) = lamN (instTs a 0 ts) (Tm.inst a as.length b) := by
      rw [inst_lamN a ts 0 b, Nat.zero_add, hl]
    rw [h2] at h1
    have h3 := beta_lamN (Γ := Γ) as (instTs a 0 ts) (Tm.inst a as.length b) rest
      (by rw [instTs_length]; exact hl)
    exact .trans h1 h3

theorem betaN_app : ∀ (as : List Tm) (f x : Tm), betaN as (.app f x) = .app (betaN as f) (betaN as x)
  | [], _, _ => rfl
  | a :: as, f, x => by
    simp only [betaN, Tm.inst]
    exact betaN_app as _ _

theorem betaN_appN (as : List Tm) : ∀ (f : Tm) (xs : List Tm),
    betaN as (Tm.appN f xs) = Tm.appN (betaN as f) (xs.map (betaN as))
  | _, [] => rfl
  | f, x :: xs => by
    simp only [Tm.appN_cons, List.map_cons]
    rw [betaN_appN as (.app f x) xs, betaN_app]

theorem betaN_const : ∀ (as : List Tm) (c : Name) (us : Array Level), betaN as (.const c us) = .const c us
  | [], _, _ => rfl
  | a :: as, c, us => by simp only [betaN, Tm.inst]; exact betaN_const as c us

theorem betaN_lift : ∀ (as : List Tm) (t : Tm), betaN as (Tm.lift as.length 0 t) = t
  | [], t => Tm.lift_zero 0 t
  | a :: as, t => by
    have h1 : Tm.lift 1 as.length (Tm.lift as.length 0 t) = Tm.lift (as.length + 1) 0 t := by
      have := Tm.lift_lift_of_le 1 as.length 0 as.length t (Nat.zero_le _) (by omega)
      rwa [Nat.add_comm 1 as.length] at this
    simp only [betaN, List.length_cons]
    rw [← h1, Tm.inst_lift_self]
    exact betaN_lift as t

theorem inst_bvar_self (v : Tm) (k : Nat) : Tm.inst v k (.bvar k) = Tm.lift k 0 v := by
  simp only [Tm.inst, ↓reduceIte]

theorem inst_bvar_lt (v : Tm) {k i : Nat} (h : i < k) : Tm.inst v k (.bvar i) = .bvar i := by
  have h1 : i ≠ k := by omega
  have h2 : ¬ k < i := by omega
  simp only [Tm.inst, h1, h2, ↓reduceIte]

/-- Telescope position `p` is replaced by argument `p`. -/
theorem betaN_bvar : ∀ (as : List Tm) (p : Nat) (x : Tm), as[p]? = some x →
    betaN as (.bvar (as.length - 1 - p)) = x
  | [], p, x, h => by simp at h
  | a :: as, 0, x, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have e : (a :: as).length - 1 - 0 = as.length := by simp
    rw [e]
    show betaN as (Tm.inst a as.length (.bvar as.length)) = a
    rw [inst_bvar_self]
    exact betaN_lift as a
  | a :: as, p + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    have hp : p < as.length := by
      rcases Nat.lt_or_ge p as.length with hp | hp
      · exact hp
      · rw [List.getElem?_eq_none hp] at h; cases h
    have e : (a :: as).length - 1 - (p + 1) = as.length - 1 - p := by simp; omega
    rw [e]
    show betaN as (Tm.inst a as.length (.bvar (as.length - 1 - p))) = x
    rw [inst_bvar_lt a (k := as.length) (i := as.length - 1 - p) (by omega)]
    exact betaN_bvar as p x h

/-- A spine of telescope positions is replaced by the arguments at those positions. -/
theorem betaN_vars (as : List Tm) : ∀ (idx : List Nat), (∀ p ∈ idx, p < as.length) →
    (idx.map fun p => betaN as (.bvar (as.length - 1 - p))) = idx.map fun p => as.getD p (.bvar 0)
  | [], _ => rfl
  | p :: idx, h => by
    simp only [List.map_cons]
    have hp : p < as.length := h p (List.mem_cons_self ..)
    have hx : as[p]? = some (as.getD p (.bvar 0)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
    rw [betaN_bvar as p _ hx, betaN_vars as idx (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-! ## Selections -/

/-- Position `p` of an argument list (a placeholder past the end). -/
def gL (L : List Tm) (p : Nat) : Tm := L.getD p (.bvar 0)

theorem getD_append_lt {α : Type} {A B : List α} {p : Nat} {d : α} (h : p < A.length) :
    (A ++ B).getD p d = A.getD p d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge {α : Type} {A B : List α} {p : Nat} {d : α} (h : A.length ≤ p) :
    (A ++ B).getD p d = B.getD (p - A.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_map {α β : Type} {l : List α} {f : α → β} {p : Nat} {d : α} {d' : β} (h : p < l.length) :
    (l.map f).getD p d' = f (l.getD p d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some, Option.getD_some]

theorem getD_range {n p : Nat} (h : p < n) : (List.range n).getD p 0 = p := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_range h, Option.getD_some]

theorem range_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun k => l.getD k d) = l := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map]
  rcases Nat.lt_or_ge k l.length with hk | hk
  · rw [List.getElem?_range hk, Option.map_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk, Option.getD_some]
  · have h1 : (List.range l.length)[k]? = none := List.getElem?_eq_none (by simpa using hk)
    rw [h1, List.getElem?_eq_none hk]
    try rfl

theorem range_add (n : Nat) : ∀ (m : Nat),
    List.range (n + m) = List.range n ++ (List.range m).map (n + ·)
  | 0 => by simp
  | m + 1 => by
    rw [show n + (m + 1) = (n + m) + 1 by omega, List.range_succ, range_add n m, List.range_succ,
      List.map_append, List.append_assoc]
    try rfl

theorem gL_append_lt {A B : List Tm} {p : Nat} (h : p < A.length) : gL (A ++ B) p = gL A p :=
  getD_append_lt h

theorem gL_append_ge {A B : List Tm} {p : Nat} (h : A.length ≤ p) :
    gL (A ++ B) p = gL B (p - A.length) :=
  getD_append_ge h

theorem gL_sel {L : List Tm} {idx : List Nat} {p : Nat} (h : p < idx.length) :
    gL (idx.map (gL L)) p = gL L (idx.getD p 0) :=
  getD_map h

/-- **Selections compose.** -/
theorem sel_sel {L R : List Tm} {idx1 idx2 : List Nat} (h : ∀ p ∈ idx2, p < idx1.length) :
    idx2.map (gL (idx1.map (gL L) ++ R)) = (idx2.map (fun p => idx1.getD p 0)).map (gL L) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  have hp' : p < (idx1.map (gL L)).length := by rw [List.length_map]; exact h p hp
  rw [gL_append_lt hp', gL_sel (h p hp)]
  rfl

theorem drop_sel {L R : List Tm} {idx : List Nat} : (idx.map (gL L) ++ R).drop idx.length = R := by
  have := List.drop_left (l₁ := idx.map (gL L)) (l₂ := R)
  rwa [List.length_map] at this

/-! ## δ then β, at an occurrence -/

/-- **δ then β on a telescope**: if the head `h.{us}` δ-reduces (a rule of `Γ`) to a telescope of
`n ≤ |L|` binders whose body is the constant `c.{ls}` applied to the telescope positions `idx`,
then `h.{us} L` converts to `c.{ls}` applied to the selection `idx` of `L` and the rest of `L`. -/
theorem delta_sel {Γ : Env} {h c : Name} {us ls : Array Level} {L : List Tm} {n : Nat}
    {ts : List Tm} {idx : List Nat} (hn : n ≤ L.length) (hts : ts.length = n)
    (hidx : ∀ p ∈ idx, p < n)
    (hδ : Γ.ax (.const h us) (lamN ts (Tm.appN (.const c ls) (idx.map fun p => .bvar (n - 1 - p))))) :
    Conv Γ (Tm.appN (.const h us) L) (Tm.appN (.const c ls) (idx.map (gL L) ++ L.drop n)) := by
  have hAlen : (L.take n).length = n := by rw [List.length_take]; omega
  have hl : (idx.map fun p => Tm.bvar (n - 1 - p)).map (betaN (L.take n)) = idx.map (gL L) := by
    rw [List.map_map]
    have hv := betaN_vars (L.take n) idx (fun p hp => by rw [hAlen]; exact hidx p hp)
    rw [hAlen] at hv
    refine Eq.trans ?_ (Eq.trans hv ?_)
    · rfl
    · apply List.map_congr_left
      intro p hp
      have hpn := hidx p hp
      simp only [gL, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hpn]
  have e : Tm.appN (.const h us) L = Tm.appN (.const h us) (L.take n ++ L.drop n) := by
    rw [List.take_append_drop]
  rw [e]
  refine .trans (Conv.appN (.step (.ax hδ)) (Conv.forall₂_refl _)) ?_
  refine .trans (beta_lamN (L.take n) ts _ _ (by rw [hts, hAlen])) ?_
  rw [betaN_appN, betaN_const, hl, ← Tm.appN_append]
  exact .refl _

/-! ## The arguments of an occurrence -/

/-- The erasure of argument `i` of an array (a placeholder past the end). -/
def argT (a : Array Expr) (i : Nat) : Tm := ((a[i]?).map er).getD (.bvar 0)

theorem argT_of_lt {a : Array Expr} {i : Nat} (h : i < a.size) : argT a i = er a[i] := by
  simp only [argT, Array.getElem?_eq_getElem h, Option.map_some, Option.getD_some]

theorem gL_args (a : Array Expr) (i : Nat) : gL (a.toList.map er) i = argT a i := by
  simp only [gL, argT, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList]

/-- A slice `a[i:j]` erases to the positions `i + k`, `k < j - i`. -/
theorem extract_map (a : Array Expr) {i j : Nat} (hj : j ≤ a.size) :
    (a.extract i j).toList.map er = (List.range (j - i)).map (fun k => argT a (i + k)) := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_extract]
  rcases Nat.lt_or_ge k (j - i) with hk | hk
  · have hk' : k < min j a.size - i := by
      rw [Nat.min_eq_left hj]; exact hk
    have hia : i + k < a.size := by omega
    simp only [hk', ↓reduceIte]
    rw [List.getElem?_range hk, Array.getElem?_eq_getElem hia, Option.map_some,
      Option.map_some, argT_of_lt hia]
  · have hk' : ¬ k < min j a.size - i := by
      rw [Nat.min_eq_left hj]; omega
    have h1 : (List.range (j - i))[k]? = none := List.getElem?_eq_none (by simpa using hk)
    simp only [hk', ↓reduceIte, h1]
    try rfl

/-- The erased arguments past position `n`. -/
theorem args_drop (a : Array Expr) {n : Nat} (hn : n ≤ a.size) :
    (a.toList.map er).drop n = (List.range (a.size - n)).map (fun k => argT a (n + k)) := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_drop, List.getElem?_map, List.getElem?_map, Array.getElem?_toList]
  rcases Nat.lt_or_ge k (a.size - n) with hk | hk
  · have hnk : n + k < a.size := by omega
    rw [List.getElem?_range hk, Array.getElem?_eq_getElem hnk, Option.map_some, Option.map_some,
      argT_of_lt hnk]
  · have h1 : a[n + k]? = none := Array.getElem?_eq_none (by omega)
    have h2 : (List.range (a.size - n))[k]? = none := List.getElem?_eq_none (by simpa using hk)
    rw [h1, h2]
    try rfl

/-- `Opt.pick` (a selection by positions) erases to the selected positions, and only succeeds
on positions in range. -/
theorem pick_list {xs : Array Expr} : ∀ {src : List Nat} {ys : List Expr},
    src.mapM (xs[·]?) = some ys →
      ys.map er = src.map (fun p => argT xs p) ∧ ∀ p ∈ src, p < xs.size
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun _ hp => by simp at hp⟩
  | p :: src, ys, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys', rfl⟩ := h
    obtain ⟨ih1, ih2⟩ := pick_list hys'
    have hp : p < xs.size := by
      rcases Nat.lt_or_ge p xs.size with hp | hp
      · exact hp
      · rw [Array.getElem?_eq_none hp] at hy; cases hy
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, ih1]
      rw [Array.getElem?_eq_getElem hp, Option.some.injEq] at hy
      rw [argT_of_lt hp, hy]
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact ih2 q hq

theorem pick_map {xs : Array Expr} {src : Array Nat} {ys : Array Expr}
    (h : Ix.Compile.Pass.Opt.pick xs src = some ys) :
    ys.toList.map er = src.toList.map (fun p => argT xs p) ∧ ∀ p ∈ src.toList, p < xs.size := by
  unfold Ix.Compile.Pass.Opt.pick at h
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : src.toList.mapM (xs[·]?) with
  | none => rw [hm] at h; cases h
  | some l =>
    rw [hm] at h
    have e : l.toArray = ys := Option.some.inj h
    subst e
    rw [List.toList_toArray]
    exact pick_list hm

theorem argT_extract {a : Array Expr} {i j p : Nat} (hj : j ≤ a.size) (hp : p < j - i) :
    argT (a.extract i j) p = argT a (i + p) := by
  have h1 : p < (a.extract i j).size := by rw [Array.size_extract]; omega
  have h2 : i + p < a.size := by omega
  rw [argT_of_lt h1, argT_of_lt h2]
  congr 1
  have hc : p < min j a.size - i := by rw [Nat.min_eq_left hj]; exact hp
  have hx : (a.extract i j)[p]? = a[i + p]? := by rw [Array.getElem?_extract]; simp only [hc, ↓reduceIte]
  rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at hx
  exact Option.some.inj hx

/-- A selection from a slice `a[i:j]`: the positions `i + p`. -/
theorem pick_extract {a : Array Expr} {i j : Nat} {src : Array Nat} {ys : Array Expr}
    (hj : j ≤ a.size) (h : Ix.Compile.Pass.Opt.pick (a.extract i j) src = some ys) :
    ys.toList.map er = src.toList.map (fun p => argT a (i + p)) ∧ ∀ p ∈ src.toList, p < j - i := by
  obtain ⟨h1, h2⟩ := pick_map h
  have hsz : (a.extract i j).size = j - i := by rw [Array.size_extract]; omega
  refine ⟨?_, fun p hp => hsz ▸ h2 p hp⟩
  rw [h1]
  apply List.map_congr_left
  intro p hp
  exact argT_extract hj (hsz ▸ h2 p hp)

/-! ## The occurrence -/

/-- The occurrence `head.{us} args` as a term. -/
def occTerm (o : Occ) : Expr := mkAppN (Expr.mkConst o.head o.us) o.args

theorem er_occTerm (o : Occ) :
    er (occTerm o) = Tm.appN (.const o.head o.us) (o.args.toList.map er) := by
  simp only [occTerm, er_mkAppN, er_mkConst]

end Ix.CompileCert.Opt
