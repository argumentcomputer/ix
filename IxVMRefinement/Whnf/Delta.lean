import IxVMRefinement.Whnf.Heads

/-! # Step lemmas of `KernelWhnf`: δ and the projection-function shortcut

* **Positional levels.** A loaded constant's level parameters are a permutation of the positions
  (`ValRep`), so instantiating the positional form of a term (`posOf`) at the positions is
  instantiating the term at its own parameters, whatever parameters it mentions
  (`posOf_ilp_perm`): a parameter outside the list is not a position either.
* `red_unfold`: a definition's (theorem's) value at the use's levels, `Red.delta`'s
  (`Red.deltaThm`'s) reduct.
* `projection_definition_info`: by a strong induction of its own (the arity is a field counter,
  so the registry's hypothesis at a bounded arity does not reach the recursive call at the
  bound): the value is `m` `λ`s over a projection of a bound variable; `m` is below `2^39`, a heap
  descent through the `λ` cells (`RomBound.bounded_descent_lt`), so at an arity below `2^32` the
  counter does not wrap.
* `try_reduce_projection_definition`: `Red.delta`, then `Red.betaGate` at each of the value's
  `λ`s (`beta_strip`; their data are `never` at the use's levels, `lams_never`), the projected
  argument substituted. Proved here as `try_reduce_core` with the level count below `2^32` as a
  hypothesis (the spec does not bound it, and the circuit compares counts in the field). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace WhnfAux

/-! ## Positional levels at a permutation of the positions -/

/-- `Level.subst.go` over the positions `s, s+1, …`: position `i` reads the `(i - s)`-th
replacement. -/
theorem getElem?_subst_go_range' :
    ∀ (s : Nat) (us : List KLevel) (i : Nat), s ≤ i → i < s + us.length →
      us[i - s]? = some (Ix.Kernel.Level.subst.go (List.range' s us.length) us i)
  | s, [], i, h1, h2 => by
    have : ([] : List KLevel).length = 0 := rfl
    omega
  | s, u :: us, i, h1, h2 => by
    show _ = some (if s = i then u else
      Ix.Kernel.Level.subst.go (List.range' (s + 1) us.length) us i)
    have hl : (u :: us).length = us.length + 1 := rfl
    by_cases h : s = i
    · subst h
      rw [ite_eq_left rfl, Nat.sub_self, List.getElem?_cons_zero]
    · rw [ite_eq_right h, show i - s = i - (s + 1) + 1 by omega, List.getElem?_cons_succ]
      exact getElem?_subst_go_range' (s + 1) us i (by omega) (by omega)

/-- `Level.subst.go` over the positions `0, …, n - 1`: position `i` reads the `i`-th
replacement. -/
theorem getElem?_eq_subst_go_range {us : List KLevel} {i : Nat} (hi : i < us.length) :
    us[i]? = some (Ix.Kernel.Level.subst.go (List.range us.length) us i) := by
  have := getElem?_subst_go_range' 0 us i (Nat.zero_le i) (by omega)
  rwa [Nat.sub_zero, ← List.range_eq_range'] at this

theorem subst_go_not_mem {q : Ix.Kernel.LevelParam} :
    ∀ (ks : List Ix.Kernel.LevelParam) (vs : List KLevel), q ∉ ks →
      Ix.Kernel.Level.subst.go ks vs q = .param q
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | k :: ks, v :: vs, h => by
    have hk : k ≠ q := by rintro rfl; exact h (List.mem_cons_self ..)
    show (if k = q then v else Ix.Kernel.Level.subst.go ks vs q) = _
    rw [ite_eq_right hk]
    exact subst_go_not_mem ks vs (fun hm => h (List.mem_cons_of_mem _ hm))

theorem subst_go_getElem {q : Ix.Kernel.LevelParam} :
    ∀ (ks : List Ix.Kernel.LevelParam) (vs : List KLevel) (i : Nat), ks.Nodup → ks[i]? = some q →
      vs.length = ks.length → vs[i]? = some (Ix.Kernel.Level.subst.go ks vs q)
  | [], _, i, _, h, _ => by simp at h
  | k :: ks, [], i, _, _, hl => by simp at hl
  | k :: ks, v :: vs, 0, hnd, h, hl => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.getElem?_cons_zero]
    show some v = some (if k = k then v else _)
    rw [ite_eq_left rfl]
  | k :: ks, v :: vs, i + 1, hnd, h, hl => by
    simp only [List.getElem?_cons_succ] at h ⊢
    have hq : q ∈ ks := List.mem_of_getElem? h
    have hk : k ≠ q := by rintro rfl; exact (List.nodup_cons.mp hnd).1 hq
    show _ = some (if k = q then v else Ix.Kernel.Level.subst.go ks vs q)
    rw [ite_eq_right hk]
    exact subst_go_getElem ks vs i (List.nodup_cons.mp hnd).2 h (by simpa using hl)

/-- A parameter, instantiated positionally after the renaming to positions, is its own
instantiation. -/
theorem subst_pos_perm {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length)
    (q : Ix.Kernel.LevelParam) :
    Ix.Kernel.Level.subst (List.range us.length) us
        (Ix.Kernel.Level.subst.go ps (posLevels ps) q) =
      Ix.Kernel.Level.subst.go ps us q := by
  have hnd : ps.Nodup := hperm.nodup_iff.mpr List.nodup_range
  by_cases hq : q ∈ ps
  · obtain ⟨i, hi, hiq⟩ := List.getElem_of_mem hq
    have hpi : ps[i]? = some q := by rw [List.getElem?_eq_getElem hi, hiq]
    have h1 := subst_go_getElem ps (posLevels ps) i hnd hpi (by simp [posLevels])
    have h2 := subst_go_getElem ps us i hnd hpi hlen
    have hP : (posLevels ps)[i]? = some (.param i) := by
      rw [posLevels, List.getElem?_map, List.getElem?_range hi]; rfl
    rw [hP] at h1
    injection h1 with h1
    rw [← h1]
    show Ix.Kernel.Level.subst.go (List.range us.length) us i = _
    have h3 := getElem?_eq_subst_go_range (us := us) (i := i) (by omega)
    exact Option.some.inj (h3.symm.trans h2)
  · rw [subst_go_not_mem ps _ hq, subst_go_not_mem ps us hq]
    show Ix.Kernel.Level.subst.go (List.range us.length) us q = _
    exact subst_go_not_mem _ us (by
      rw [hlen]; exact fun hm => hq (hperm.mem_iff.mpr hm))

theorem subst_posOf_level {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length) :
    ∀ u : KLevel, Ix.Kernel.Level.subst (List.range us.length) us
        (Ix.Kernel.Level.subst ps (posLevels ps) u) = Ix.Kernel.Level.subst ps us u
  | .zero => rfl
  | .succ l => by
    simp only [Ix.Kernel.Level.subst, subst_posOf_level hperm hlen l]
  | .max a b => by
    simp only [Ix.Kernel.Level.subst, subst_posOf_level hperm hlen a,
      subst_posOf_level hperm hlen b]
  | .imax a b => by
    simp only [Ix.Kernel.Level.subst, subst_posOf_level hperm hlen a,
      subst_posOf_level hperm hlen b]
  | .param q => subst_pos_perm hperm hlen q

theorem substPW_posOf {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length)
    (pw : Ix.Kernel.PropWhen) :
    Ix.Kernel.Level.substPW (List.range us.length) us
        (Ix.Kernel.Level.substPW ps (posLevels ps) pw) = Ix.Kernel.Level.substPW ps us pw := by
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Ix.Kernel.Level.holds_substPW, Ix.Kernel.Level.holds_substPW,
    Ix.Kernel.Level.holds_substPW]
  congr 1
  funext q
  rw [← Ix.Kernel.Level.eval_subst_go, ← Ix.Kernel.Level.eval_subst_go,
    ← Ix.Kernel.Level.eval_subst, subst_pos_perm hperm hlen q]

/-- **Instantiating a positional term positionally**, at parameters that are a permutation of
the positions: the term instantiated at its own parameters. -/
theorem posOf_ilp_perm {ps : List Ix.Kernel.LevelParam} {us : List KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hlen : us.length = ps.length) (T : KExpr) :
    (posOf ps T).instantiateLevelParams (List.range us.length) us =
      T.instantiateLevelParams ps us := by
  unfold posOf
  induction T with
  | bvar _ => rfl
  | fvar idx ty ih => simp only [Ix.Kernel.Expr.instantiateLevelParams, ih]
  | sort u => simp only [Ix.Kernel.Expr.instantiateLevelParams, subst_posOf_level hperm hlen]
  | const n ls =>
    simp only [Ix.Kernel.Expr.instantiateLevelParams, List.map_map, Function.comp_def,
      subst_posOf_level hperm hlen]
  | app f a ihf iha => simp only [Ix.Kernel.Expr.instantiateLevelParams, ihf, iha]
  | lam ty body m iht ihb =>
    simp only [Ix.Kernel.Expr.instantiateLevelParams, iht, ihb, substPW_posOf hperm hlen]
  | forallE ty body m iht ihb =>
    simp only [Ix.Kernel.Expr.instantiateLevelParams, iht, ihb, substPW_posOf hperm hlen]
  | letE ty val body l iht ihv ihb =>
    simp only [Ix.Kernel.Expr.instantiateLevelParams, iht, ihv, ihb]
  | lit _ => rfl
  | proj s i e ih => simp only [Ix.Kernel.Expr.instantiateLevelParams, ih]

/-! ## Loaded theorems, cells, tuples -/

/-- A loaded `Thm` represents a stored theorem. -/
theorem thm_inv {κ : _root_.Address → KKey} {h : Heap F} {nl ty val : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Thm" [nl, ty, val]) ci) :
    ∃ cv V, ci = .thmInfo cv V ∧ ValRep κ h nl ty cv ∧ TmC κ h (posOf cv.levelParams V) val := by
  generalize hv : (Value.construct kciEnum "Thm" [nl, ty, val] : SourceValue F) = v at r
  cases r
  case thm hvr hV =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨_, _, rfl, hvr, hV⟩
  all_goals (injection hv with _ hc _; exact absurd hc (by decide))

/-- A load is a pointer's cell, of the pointer's type. -/
theorem cell_of_load {h : Heap F} {p v : SourceValue F} (hl : loadValue h p = .ok v) :
    ∃ t addr, p = .ptr t addr ∧ h[addr]? = some v ∧ v.type = t := by
  cases p
  case ptr t addr =>
    cases hc : h[addr]? with
    | none => simp [loadValue, hc] at hl
    | some v0 =>
      by_cases typed : v0.type = t
      · simp [loadValue, hc, typed, pure, Except.pure, bind, Except.bind] at hl
        subst hl
        exact ⟨t, addr, rfl, hc, typed⟩
      · simp [loadValue, hc, typed] at hl
  all_goals simp [loadValue] at hl

theorem tuple5_inj {a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 : SourceValue F}
    (h : (Value.tuple [a1, a2, a3, a4, a5] : SourceValue F) = .tuple [b1, b2, b3, b4, b5]) :
    a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 := by
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at h
  exact h

theorem tag_eq {t t' : F} {x y : SourceValue F}
    (h : (Value.tuple [.field t, x] : SourceValue F) = .tuple [.field t', y]) : t = t' ∧ x = y := by
  simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq, and_true] at h
  exact h

/-! ## `projection_definition_info`, by its own induction -/

theorem pdi_strong (c : Ctx) (N : Nat) :
    ∀ {val arity : SourceValue F} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)},
      calls.length < N →
      ObsFn W "KernelWhnf::projection_definition_info" [val, arity] h r h' calls → Good c calls →
      ∀ {d : Nat} {Γ : Nat → KExpr} {K : Nat} {V : KExpr}, arity = .field (K : F) →
        c.tmk d Γ K h V val →
      ∀ {xa sp xf xj : SourceValue F}, r = .tuple [.field 1, xa, sp, xf, xj] →
        ∃ (n f j i : F) (s : Bytes.Address) (m : Nat) (X : KExpr) (bp : SourceValue F),
          xa = .field n ∧ xf = .field f ∧ xj = .field j ∧ RepAddr h s sp ∧ h' = h ∧
          n = ((K + m : Nat) : F) ∧ ZMod.val i < ZMod.val n ∧ ZMod.val n < 4294967296 ∧
          j = n - 1 - i ∧ RomBound.HeapDescent h (.enum kexprEnum) val m ∧ m < 549755813889 ∧
          Specs.Whnf.stripLams m V = some (.proj (c.κ (ixAddr s)) (ZMod.val f) X) ∧
          c.tmk d Γ (K + m) h X bp ∧
          loadValue h bp = .ok (.construct kexprEnum "BVar" [.field i]) := by
  induction N with
  | zero => intro _ _ _ _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ N ihN =>
    intro val arity h h' r calls hlt ev good d Γ K V harity hV xa sp xf xj hr
    subst harity
    rcases Obs.«KernelWhnf::projection_definition_info».obs ev with
      ⟨w20, x_body, w21, cs40, v44, ld12, op65, ev42, hc67⟩ |
      ⟨x_struct_addr, x_field, x_projected, x_i, m115, cs126, v155, x190, ld12, ld101, ev128,
        he156, op205, op197, he208, hc209⟩ |
      ⟨x_struct_addr, x_field, x_projected, x_i, v114, m115, cs126, m235, ld12, ld101, ev128,
        hne210, he221, hm243, he258, hc259⟩ |
      ⟨x_struct_addr, x_field, x_projected, v90, m285, ld12, ld101, hne260, he271, hm293, he308,
        hc309⟩ |
      ⟨v1, m335, ld12, hne68, hne310, he321, hm343, he358, hc359⟩
    · -- a `λ`: one more binder, then the walk below it
      subst hc67
      obtain rfl : v44 = .field (((K + 1 : Nat) : F)) := by
        rw [NatAux.add_ok op65, Nat.cast_succ]
      obtain ⟨T, B, ℓ, rfl, -, hB, -⟩ := hV.lam_of_load ld12
      obtain ⟨n, f, j, i, s, m, X, bp, hxa, hxf, hxj, hs, hh, hn, hi, hn32, hj, hdesc, hm,
          hstrip, hX, hbp⟩ :=
        ihN (by simp only [List.length_cons] at hlt; omega) ev42
          (good.sub fun x hx => by simp [hx]) rfl hB hr
      have hm' : m < 2 ^ 39 := RomBound.bounded_descent_lt good.2
        (c := ⟨"KernelWhnf::projection_definition_info",
          [x_body, .field (((K + 1 : Nat) : F))], h⟩) (by simp) (by simp) hdesc
      have h39 : (2 : ℕ) ^ 39 = 549755813888 := by norm_num
      obtain ⟨t, loc, rfl, hcell, htyped⟩ := cell_of_load ld12
      obtain rfl : t = .enum kexprEnum := htyped.symm.trans (by simp)
      refine ⟨n, f, j, i, s, m + 1, X, bp, hxa, hxf, hxj, hs, hh, ?_, hi, hn32, hj,
        .down hcell (by simp) (by simp [RomBound.cellArgs]) hdesc, by omega, hstrip,
        ?_, hbp⟩
      · rw [hn, show K + 1 + m = K + (m + 1) by omega]
      · rw [show K + (m + 1) = K + 1 + m by omega]; exact hX
    · -- a projection of a bound variable below the arity
      subst hc209 he208
      obtain ⟨s, i0, Es, rfl, rfl, hs, hEs⟩ := hV.proj_of_load ld12
      obtain ⟨a0, b0, rfl, hb0, ha32, hb32, hr1, rfl⟩ := Lib.less_than_fields_spec ev128
      obtain rfl := Value.field.inj hb0
      obtain rfl := NatAux.sub_ok op205
      obtain rfl := NatAux.sub_ok op197
      obtain ⟨-, rfl, rfl, rfl, rfl⟩ := tuple5_inj (hr.symm.trans he156)
      have hlt' : ZMod.val a0 < ZMod.val ((K : Nat) : F) := by
        by_contra hn
        exact field_one_ne_zero (by rw [hr1, ite_eq_right hn])
      obtain ⟨t, loc, rfl, hcell, htyped⟩ := cell_of_load ld12
      obtain rfl : t = .enum kexprEnum := htyped.symm.trans (by simp)
      refine ⟨((K : Nat) : F), i0, ((K : Nat) : F) - 1 - a0, a0, s, 0, Es, x_projected, rfl, rfl,
        rfl, hs, rfl, by simp, hlt', hb32, rfl, .here hcell (by simp), by omega, rfl,
        hEs, ld101⟩
    · exact (field_one_ne_zero (tuple5_inj (hr.symm.trans he221)).1).elim
    · exact (field_one_ne_zero (tuple5_inj (hr.symm.trans he271)).1).elim
    · exact (field_one_ne_zero (tuple5_inj (hr.symm.trans he321)).1).elim

/-- `projection_definition_info` at an arity below `2^32`: the counts as naturals, the
projected bound variable read off the image. -/
theorem pdi_top (c : Ctx) {val : SourceValue F} {a : F} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::projection_definition_info" [val, .field a] h r h' calls)
    (good : Good c calls) (ha : ZMod.val a < 4294967296) {d : Nat} {Γ : Nat → KExpr}
    {V : KExpr} (hV : c.tmk d Γ (ZMod.val a) h V val) {xa sp xf xj : SourceValue F}
    (hr : r = .tuple [.field 1, xa, sp, xf, xj]) :
    ∃ (n f j : F) (s : Bytes.Address) (m : Nat), xa = .field n ∧ xf = .field f ∧
      xj = .field j ∧ RepAddr h s sp ∧ h' = h ∧ ZMod.val n = ZMod.val a + m ∧
      ZMod.val j < ZMod.val n ∧
      Specs.Whnf.stripLams m V = some (.proj (c.κ (ixAddr s)) (ZMod.val f)
        (.bvar (ZMod.val n - 1 - ZMod.val j))) := by
  obtain ⟨n, f, j, i, s, m, X, bp, hxa, hxf, hxj, hs, hh, hn, hi, hn32, hj, -, hm, hstrip, hX,
      hbp⟩ :=
    pdi_strong c (calls.length + 1) (Nat.lt_succ_self _) ev good (K := ZMod.val a)
      (by rw [NatAux.natCast_val]) hV hr
  have hnv : ZMod.val n = ZMod.val a + m := by rw [hn]; exact NatAux.val_natCast (by omega)
  have hn0 : n ≠ 0 := by intro h0; rw [h0, ZMod.val_zero] at hi; omega
  have hv1 : ZMod.val (n - 1) = ZMod.val n - 1 := NatAux.val_sub_one hn0
  have hvj : ZMod.val j = ZMod.val n - 1 - ZMod.val i := by
    rw [hj, NatAux.val_sub (x := n - 1) (y := i) (by omega), hv1]
  rcases hX.bvar_of_load hbp with ⟨i', hi', -, ⟨hlt, rfl⟩ | ⟨hge, -, -⟩⟩
  · obtain rfl := Value.field.inj hi'
    refine ⟨n, f, j, s, m, hxa, hxf, hxj, hs, hh, hnv, by omega, ?_⟩
    rw [hstrip, show ZMod.val n - 1 - ZMod.val j = ZMod.val i by omega]
  · obtain rfl := Value.field.inj hi'
    exfalso
    omega

/-! ## β at a telescope of `never` data -/

/-- The first `n` binders are `λ`s whose data are `never`. -/
def LamsNv : Nat → KExpr → Prop
  | 0, _ => True
  | n + 1, .lam _ b m => m.pw.isNever = true ∧ LamsNv n b
  | _ + 1, _ => False

theorem ilp_lamsNever (ks : List Ix.Kernel.LevelParam) (us : List KLevel) :
    ∀ (n : Nat) (P : KExpr), Specs.Whnf.lamsNeverAt ks us n P →
      LamsNv n (P.instantiateLevelParams ks us) := by
  intro n
  induction n with
  | zero => intro P _; exact trivial
  | succ n ih =>
    intro P hP
    cases P
    case lam T B m =>
      have hP' : (Ix.Kernel.Level.substPW ks us m.pw).isNever = true ∧
          Specs.Whnf.lamsNeverAt ks us n B := hP
      show (Ix.Kernel.Level.substPW ks us m.pw).isNever = true ∧
        LamsNv n (B.instantiateLevelParams ks us)
      exact ⟨hP'.1, ih B hP'.2⟩
    all_goals exact False.elim hP

theorem ilp_strip (ks : List Ix.Kernel.LevelParam) (us : List KLevel) :
    ∀ (n : Nat) (P D : KExpr), Specs.Whnf.stripLams n P = some D →
      Specs.Whnf.stripLams n (P.instantiateLevelParams ks us) =
        some (D.instantiateLevelParams ks us) := by
  intro n
  induction n with
  | zero =>
    intro P D h
    simp only [Specs.Whnf.stripLams, Option.some.injEq] at h ⊢
    rw [h]
  | succ n ih =>
    intro P D h
    cases P
    case lam T B m => exact ih B D h
    all_goals simp [Specs.Whnf.stripLams] at h

theorem strip_instantiate1 :
    ∀ (n : Nat) (L D A : KExpr) (k : Nat), Specs.Whnf.stripLams n L = some D → LamsNv n L →
      Specs.Whnf.stripLams n (L.instantiate1 A k) = some (D.instantiate1 A (k + n)) ∧
        LamsNv n (L.instantiate1 A k)
  | 0, L, D, A, k, hs, _ => by
    have : L = D := by simpa [Specs.Whnf.stripLams] using hs
    subst this
    exact ⟨by simp [Specs.Whnf.stripLams], trivial⟩
  | n + 1, L, D, A, k, hs, hn => by
    cases L
    case lam T B m =>
      have hs' : Specs.Whnf.stripLams n B = some D := hs
      have hn' : m.pw.isNever = true ∧ LamsNv n B := hn
      obtain ⟨h1, h2⟩ := strip_instantiate1 n B D A (k + 1) hs' hn'.2
      refine ⟨?_, ?_⟩
      · show Specs.Whnf.stripLams n (B.instantiate1 A (k + 1)) =
          some (D.instantiate1 A (k + (n + 1)))
        rw [h1, show k + 1 + n = k + (n + 1) by omega]
      · show m.pw.isNever = true ∧ LamsNv n (B.instantiate1 A (k + 1))
        exact ⟨hn'.1, h2⟩
    all_goals simp [Specs.Whnf.stripLams] at hs

/-- **The β chain at a telescope of `never` data**: a term with `|As|` leading `λ`s of `never`
data, over `D`, applied to `As` then `rest`, reduces to `D` under the reversed arguments applied
to `rest` (`Red.betaGate` at each binder). -/
theorem beta_strip {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (As : List KExpr) (L D : KExpr) (rest : List KExpr),
      Specs.Whnf.stripLams As.length L = some D → LamsNv As.length L →
      Red env d (Ix.Kernel.Expr.mkAppN L (As ++ rest))
        (Ix.Kernel.Expr.mkAppN (D.instantiateList As.reverse 0) rest)
  | [], L, D, rest, hs, _ => by
    have : L = D := by simpa [Specs.Whnf.stripLams] using hs
    subst this
    rw [List.reverse_nil, Ix.Kernel.Expr.instantiateList_nil]
    exact .refl
  | A :: As, L, D, rest, hs, hn => by
    cases L
    case lam T B m =>
      have hs' : Specs.Whnf.stripLams As.length B = some D := hs
      have hn' : m.pw.isNever = true ∧ LamsNv As.length B := hn
      obtain ⟨hs'', hn''⟩ := strip_instantiate1 As.length B D A 0 hs' hn'.2
      have hrec := beta_strip (env := env) (d := d) As (B.instantiate1 A 0) _ rest hs'' hn''
      have hstep : Red env d (Ix.Kernel.Expr.mkAppN (.app (.lam T B m) A) (As ++ rest))
          (Ix.Kernel.Expr.mkAppN (B.instantiate1 A 0) (As ++ rest)) :=
        red_mkAppN (As ++ rest) (.betaGate hn'.1)
      refine .trans hstep ?_
      rw [List.reverse_cons, Ix.Kernel.Expr.instantiateList_append_one, List.length_reverse]
      exact hrec
    all_goals simp [Specs.Whnf.stripLams] at hs

theorem instantiateList_proj (s : KKey) (i : Nat) (e : KExpr) (vs : List KExpr) (d : Nat) :
    (Ix.Kernel.Expr.proj s i e).instantiateList vs d = .proj s i (e.instantiateList vs d) := by
  simp only [Ix.Kernel.Expr.instantiateList]

theorem instantiateList_bvar_some {vs : List KExpr} {i : Nat} {A : KExpr} (hA : vs[i]? = some A)
    (hcl : A.looseBVarsBounded 0 = true) :
    (Ix.Kernel.Expr.bvar i : KExpr).instantiateList vs 0 = A := by
  obtain ⟨hi, hAi⟩ := List.getElem?_eq_some_iff.mp hA
  simp only [Ix.Kernel.Expr.instantiateList]
  simp [hi, hAi, Ix.Kernel.Expr.instantiateList_eq_self hcl]

end WhnfAux

/-! ## `red_unfold` -/

/-- `KernelWhnf::red_unfold`: a definition's (theorem's) value at levels of its count, tag `1`
(`2`); its positional form instantiated positionally is the value at its own parameters. -/
theorem red_unfold_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::red_unfold" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.red_unfold c args h r h' calls := by
  intro v lvls hargs good ci us hci hus t x hr ht
  subst hargs
  rcases Obs.«KernelWhnf::red_unfold».obs ev with
    ⟨x_nl, w17, x_value, w18, w19, x54, m56, cs65, v84, m93, cs101, hv15, ev67, op61, he85, ev103,
      he120, hc121⟩ |
    ⟨x_nl, w17, x_value, w18, w19, v45, x54, m56, cs65, hv15, ev67, op61, hne122, he130, he144,
      hc145⟩ |
    ⟨x_nl, w153, x_value, x178, m180, cs189, v208, m217, cs225, hne146, hv151, ev191, op185, he209,
      ev227, he244, hc245⟩ |
    ⟨x_nl, w153, x_value, v169, x178, m180, cs189, hne146, hv151, ev191, op185, hne246, he254,
      he268, hc269⟩ |
    ⟨m286, hne146, hne270, he278, hm294, he305, hc306⟩
  · -- a definition
    subst hv15 hc121 he120
    obtain ⟨rfl, rfl⟩ := WhnfAux.tag_eq (hr.symm.trans he85)
    obtain ⟨cv, V, hn, rfl, ⟨hnl, hlt32, hperm, -⟩, hV⟩ := CIRep.defn_inv hci
    subst hnl
    obtain ⟨ls, hls, hEq⟩ := hus
    obtain ⟨rfl, -⟩ := WhnfAux.lv_length ev67 (by rw [klevelListEnum_eq]; exact hls)
    have hb39 : ls.length < 2 ^ 39 :=
      RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [lvls], h⟩) (by simp)
        (by simp) hls
    have hlen := WhnfAux.len_eq_of_sub hb39 (lt_trans hlt32 (by norm_num)) op61
    have hlenus : us.length = cv.levelParams.length := by
      rw [WhnfAux.evalEqList_length us ls (hEq fun _ => 0), hlen]
    have e67 := ObsFn.heap_extends ev67
    have hinst := ih.get (.subst .expr_inst_levels) (by lt_calls) ev103 x_value lvls rfl
      (good.sub fun x hx => by simp [hx]) (fun _ => .bvar 0) 0 _ us
      (Tm.mono e67 (hV 0 fun _ => .bvar 0)) ⟨ls, hls.mono e67, hEq⟩
    rw [WhnfAux.posOf_ilp_perm hperm hlenus] at hinst
    exact .inl ⟨rfl, cv, V, hn, rfl, hlenus, TmC.of_depth_zero hinst⟩
  · exact absurd (WhnfAux.tag_eq (hr.symm.trans he130)).1 ht
  · -- a theorem
    subst hv151 hc245 he244
    obtain ⟨rfl, rfl⟩ := WhnfAux.tag_eq (hr.symm.trans he209)
    obtain ⟨cv, V, rfl, ⟨hnl, hlt32, hperm, -⟩, hV⟩ := WhnfAux.thm_inv hci
    subst hnl
    obtain ⟨ls, hls, hEq⟩ := hus
    obtain ⟨rfl, -⟩ := WhnfAux.lv_length ev191 (by rw [klevelListEnum_eq]; exact hls)
    have hb39 : ls.length < 2 ^ 39 :=
      RomBound.bounded_length_lt good.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [lvls], h⟩) (by simp)
        (by simp) hls
    have hlen := WhnfAux.len_eq_of_sub hb39 (lt_trans hlt32 (by norm_num)) op185
    have hlenus : us.length = cv.levelParams.length := by
      rw [WhnfAux.evalEqList_length us ls (hEq fun _ => 0), hlen]
    have e191 := ObsFn.heap_extends ev191
    have hinst := ih.get (.subst .expr_inst_levels) (by lt_calls) ev227 x_value lvls rfl
      (good.sub fun x hx => by simp [hx]) (fun _ => .bvar 0) 0 _ us
      (Tm.mono e191 (hV 0 fun _ => .bvar 0)) ⟨ls, hls.mono e191, hEq⟩
    rw [WhnfAux.posOf_ilp_perm hperm hlenus] at hinst
    exact .inr ⟨rfl, cv, V, rfl, hlenus, TmC.of_depth_zero hinst⟩
  · exact absurd (WhnfAux.tag_eq (hr.symm.trans he254)).1 ht
  · exact absurd (WhnfAux.tag_eq (hr.symm.trans he278)).1 ht

/-! ## `projection_definition_info` -/

/-- `KernelWhnf::projection_definition_info`: tag `1` is `m` `λ`s over a projection of the bound
variable `n - 1 - j`, at an arity below `2^32`. -/
theorem projection_definition_info_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::projection_definition_info" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.projection_definition_info c args h r h' calls := by
  intro val arity hargs good d Γ a V harity ha hV n f j sp hr
  subst hargs harity
  obtain ⟨n', f', j', s, m, hxa, hxf, hxj, hs, hh, hnv, hj, hstrip⟩ :=
    WhnfAux.pdi_top c ev good ha hV hr
  obtain rfl := Value.field.inj hxa
  obtain rfl := Value.field.inj hxf
  obtain rfl := Value.field.inj hxj
  subst hh
  exact ⟨s, m, hs, hnv, hj, hstrip⟩

/-! ## The projection-function shortcut -/

/-- **`try_reduce_projection_definition`, at a level count below `2^32`**: `Red.delta`, the
`never` β chain over the value's `λ`s, the projected argument substituted. -/
theorem try_reduce_core (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::try_reduce_projection_definition" args h r h' calls)
    (ih : IH c calls) :
    ∀ value nl lvls sp, args = [value, nl, lvls, sp] → Good c calls →
      ∀ d Γ k cv V hn us As, c.env.find? k = some (.defnInfo cv V hn) →
        c.tmc h (posOf cv.levelParams V) value →
        cv.levelParams.Perm (List.range cv.levelParams.length) →
        cv.levelParams.length < 4294967296 →
        nl = .field (cv.levelParams.length : F) → LvListRep h us lvls → c.tml d Γ h As sp →
        ∀ x, r = .tuple [.field 1, x] →
          ∃ E, c.tm d Γ h' E x ∧ Red c.env d (Specs.Whnf.mkAppN (.const k us) As) E := by
  intro value nl lvls sp hargs good d Γ k cv V hn us As hfind hP hperm hps hnl hus hAs x hr
  subst hargs hnl
  rcases Obs.«KernelWhnf::try_reduce_projection_definition».obs ev with
    ⟨m2, cs13, x_arity, x_struct_addr, x_field, x_struct_arg_idx, m65, x73, y74, m75, y82, cs92,
      v95, m98, cs106, cs127, v130, x137, m139, cs148, m165, cs176, v207, m208, cs218, m238, v276,
      m277, cs287, v309, m318, cs326, ev15, ev108, ev94, op88, ev150, op144, ev129, op80, ev178,
      ev220, hm248, ev289, he310, ev328, he345, hc346⟩ |
    ⟨m2, cs13, x_arity, x_struct_addr, x_field, x_struct_arg_idx, m65, x73, y74, m75, y82, cs92,
      v95, m98, cs106, cs127, v130, x137, m139, cs148, v164, m165, cs176, m363, ev15, ev108, ev94,
      op88, ev150, op144, ev129, op80, ev178, hne347, he355, hm371, he382, hc383⟩ |
    ⟨m2, cs13, x_arity, x_struct_addr, x_field, x_struct_arg_idx, v64, m65, x73, y74, m75, y82,
      cs92, v95, m98, cs106, cs127, v130, x137, m139, cs148, m400, ev15, ev108, ev94, op88, ev150,
      op144, ev129, op80, hne384, he392, hm408, he419, hc420⟩ |
    ⟨v1, m2, cs13, m436, ev15, he428, hm444, he455, hc456⟩
  · subst hc346 he345
    obtain ⟨-, rfl⟩ := WhnfAux.tag_eq (hr.symm.trans he310)
    -- the value: `m` `λ`s over a projection of a bound variable
    obtain ⟨nF, f, j, s, m, rfl, rfl, rfl, hs, -, hnv, hjn, hstrip⟩ :=
      WhnfAux.pdi_top c ev15 (good.sub fun x hx => by simp [hx]) (by simp)
        (by rw [ZMod.val_zero]; exact hP d Γ) rfl
    rw [ZMod.val_zero, Nat.zero_add] at hnv
    subst hnv
    have e15 := ObsFn.heap_extends ev15
    -- the spine is long enough, the level count matches
    obtain ⟨rfl, -⟩ := PrimNat.kl_length ev108 (tml_mono e15 hAs)
    have h39 : (2 : ℕ) ^ 39 = 549755813888 := by norm_num
    have hlenA : As.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [sp], m2⟩) (by simp) (by simp)
      (tml_mono e15 hAs)
    obtain ⟨a1, b1, ha1, hb1, ha32, hb32, hy82, -⟩ := Lib.less_than_fields_spec ev94
    obtain rfl := Value.field.inj ha1
    obtain rfl := Value.field.inj hb1
    rw [hy82] at op88
    obtain rfl := NatAux.sub_ok op88
    have e108 := ObsFn.heap_extends ev108
    have e94 := ObsFn.heap_extends ev94
    have ext75 := (e15.trans e108).trans e94
    obtain ⟨ls, hls, hEq⟩ := hus
    obtain ⟨rfl, -⟩ := WhnfAux.lv_length ev150 (by rw [klevelListEnum_eq]; exact hls.mono ext75)
    have hlenL : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [lvls], m75⟩) (by simp)
      (by simp) (hls.mono ext75)
    obtain rfl := NatAux.sub_ok op144
    obtain ⟨rfl, -⟩ := Lib.is_zero_field ev129
    have hmul := (NatAux.field_inj (NatAux.mul_ok op80)).symm
    have hz : ((ls.length : ℕ) : F) - ((cv.levelParams.length : ℕ) : F) = 0 := by
      by_contra hne
      have := right_ne_zero_of_mul_eq_one hmul
      rw [ite_eq_right hne] at this
      exact this rfl
    have hlenus : us.length = cv.levelParams.length := by
      have h1 : ((ls.length : ℕ) : F) = ((cv.levelParams.length : ℕ) : F) := sub_eq_zero.mp hz
      rw [WhnfAux.evalEqList_length us ls (hEq fun _ => 0)]
      exact (NatAux.natCast_inj (by omega) (by omega)).mp h1
    have hvA : ZMod.val ((As.length : ℕ) : F) = As.length := NatAux.val_natCast (by omega)
    have hnle : ZMod.val nF ≤ As.length := by
      by_contra hlt
      have := left_ne_zero_of_mul_eq_one hmul
      rw [ite_eq_left (by omega : ZMod.val ((As.length : ℕ) : F) < ZMod.val nF), sub_self] at this
      exact this rfl
    -- the λs' data
    have e150 := ObsFn.heap_extends ev150
    have e129 := ObsFn.heap_extends ev129
    have ext65 := ext75.trans (e150.trans e129)
    have hlam := ih.get (.whnf .lams_never) (by lt_calls) ev178 value _ lvls rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 (posOf cv.levelParams V) nF us
      (Tm.mono ext65 (hP d Γ)) rfl ⟨ls, hls.mono ext65, hEq⟩ field_one_ne_zero
    have ext165 := ext65.trans (ObsFn.heap_extends ev178)
    -- the projected argument and the rest of the spine
    obtain ⟨⟨A, hA, hAt⟩, -⟩ := PrimNat.kl_lookup ev220 (tml_mono ext165 hAs)
    have e220 := ObsFn.heap_extends ev220
    have esn : Heap.Extends m208 m238 := by rw [hm248]; exact Heap.Extends.snoc _ _
    have ext238 := (ext165.trans e220).trans esn
    obtain ⟨-, hdrop, -⟩ := PrimNat.kl_drop ev289 (tml_mono ext238 hAs)
    have e289 := ObsFn.heap_extends ev289
    have hcell : Tm c.κ d Γ m238 0 (.proj (c.κ (ixAddr s)) (ZMod.val f) A)
        (.ptr (.enum kexprEnum) m208.length) := by
      subst hm248
      exact .proj List.getElem?_concat_length
        (Bytes.repAddressRef_heapMono₂ addrTy ((ext165.trans e220).trans (Heap.Extends.snoc _ _))
          hs)
        (Tm.mono (e220.trans (Heap.Extends.snoc _ _)) hAt)
    have happ := ih.get (.whnf .apply_spine) (by lt_calls) ev328 _ v276 rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ (As.drop (ZMod.val nF)) (Tm.mono e289 hcell)
      (tml_mono e289 hdrop)
    refine ⟨_, happ, ?_⟩
    -- δ, then the never β chain
    have hlenT : (As.take (ZMod.val nF)).length = ZMod.val nF := by
      rw [List.length_take]; omega
    have hstrip' := WhnfAux.ilp_strip (List.range us.length) us _ _ _ hstrip
    have hnv' := WhnfAux.ilp_lamsNever (List.range us.length) us _ _ hlam
    have hchain := WhnfAux.beta_strip (env := c.env) (d := d) (As.take (ZMod.val nF))
      ((posOf cv.levelParams V).instantiateLevelParams (List.range us.length) us) _
      (As.drop (ZMod.val nF)) (by rw [hlenT]; exact hstrip') (by rw [hlenT]; exact hnv')
    rw [List.take_append_drop] at hchain
    have hv : ((As.take (ZMod.val nF)).reverse)[ZMod.val nF - 1 - ZMod.val j]? = some A := by
      rw [List.getElem?_reverse (by rw [hlenT]; omega), hlenT,
        show ZMod.val nF - 1 - (ZMod.val nF - 1 - ZMod.val j) = ZMod.val j by omega]
      simp [hjn, hA]
    have hfin : ((Ix.Kernel.Expr.proj (c.κ (ixAddr s)) (ZMod.val f)
        (.bvar (ZMod.val nF - 1 - ZMod.val j)) : KExpr).instantiateLevelParams
          (List.range us.length) us).instantiateList (As.take (ZMod.val nF)).reverse 0 =
        .proj (c.κ (ixAddr s)) (ZMod.val f) A := by
      show (Ix.Kernel.Expr.proj (c.κ (ixAddr s)) (ZMod.val f)
        (.bvar (ZMod.val nF - 1 - ZMod.val j))).instantiateList _ 0 = _
      rw [WhnfAux.instantiateList_proj, WhnfAux.instantiateList_bvar_some hv
        (Tm.looseBVarsBounded hAt)]
    rw [hfin, WhnfAux.posOf_ilp_perm hperm hlenus] at hchain
    exact .trans (.delta (unfold_const_mkAppN As hfind hlenus)) hchain
  · exact absurd (WhnfAux.tag_eq (hr.symm.trans he355)).1 one_ne_zero
  · exact absurd (WhnfAux.tag_eq (hr.symm.trans he392)).1 one_ne_zero
  · exact absurd (WhnfAux.tag_eq (hr.symm.trans he428)).1 one_ne_zero

end IxVM.Refinement.Core
