module

public import ConLeche.Kernel.DeclCheck

public section

/-!
# The index's installation counters and the prefix view (task #108)

`FEnv` (`ConLeche/Kernel/CoreI.lean`) stores, beside each indexed
constant, the number of constants installed before it — its
*installation counter* — and a bound `visibleBelow`; `FEnv.find?`
hides every entry whose counter is at or above the bound.  This file
proves what that bound means:

* `mkFEnv_find?` — with nothing hidden the index *is* `Env.find?`
  (the pre-#108 statement, now with the counters in play);
* `mkFEnv_find?_visibleBelow_some` — **unconditional soundness**:
  anything the bounded lookup returns is what the environment
  truncated to that prefix returns.  A bounded lookup can therefore
  never reach a constant installed at or after the bound; this is the
  no-circularity fact the split driver rests on.
* `mkFEnv_find?_visibleBelow` — the full equivalence
  `bounded find? = find? in the truncated environment`, under name
  uniqueness (the only thing the bounded lookup can miss is an *older*
  constant shadowed by a same-named newer one; the checker rejects
  duplicate names at insertion, so this never happens on an accepted
  stream, and its absence is the safe direction anyway);
* `restrictTo_push_find?` — pushing the next installed constant onto a
  restricted view is the same as raising the bound by one, so a
  re-check that walks a declaration's provisional environments sees
  exactly what the original interleaved run saw.

Spec-side only: nothing here is called by the checker.
-/

namespace ConLeche

/-! ## The index's specification -/

/-- What the name index holds: the newest constant of the given name
together with its installation counter — the number of *older*
constants, i.e. the length of the tail it heads (`consts` is
newest-first). -/
def idxSpec : List ConstantInfo → Name → Option (Nat × ConstantInfo)
  | [], _ => none
  | ci :: cs, n => if ci.name == n then some (cs.length, ci) else idxSpec cs n

theorem mkFEnvGo_fst : ∀ l : List ConstantInfo, (mkFEnvGo l).1 = l.length
  | [] => rfl
  | ci :: cs => by
    show (mkFEnvGo cs).1 + 1 = _
    rw [mkFEnvGo_fst cs, List.length_cons]

theorem mkFEnvGo_snd (n : Name) : ∀ l : List ConstantInfo,
    (mkFEnvGo l).2[n]? = idxSpec l n
  | [] => by simp [mkFEnvGo, idxSpec]
  | ci :: cs => by
    show ((mkFEnvGo cs).2.insert ci.name ((mkFEnvGo cs).1, ci))[n]? = _
    rw [Std.HashMap.getElem?_insert, idxSpec]
    by_cases hn : ci.name == n
    · rw [if_pos hn, if_pos hn, mkFEnvGo_fst]
    · rw [if_neg hn, if_neg hn, mkFEnvGo_snd n cs]

/-- The index of `mkFEnv`, as the specification. -/
theorem mkFEnv_idx (env : Env) (n : Name) :
    (mkFEnv env).idx[n]? = idxSpec env.consts n :=
  mkFEnvGo_snd n env.consts

/-- `mkFEnv` hides nothing: its bound is the constant count. -/
theorem mkFEnv_visibleBelow (env : Env) :
    (mkFEnv env).visibleBelow = env.consts.length :=
  mkFEnvGo_fst env.consts

/-- Counters are positions from the bottom, so they are below the
length. -/
theorem idxSpec_lt {n : Name} : ∀ {l : List ConstantInfo} {c : Nat}
    {ci : ConstantInfo}, idxSpec l n = some (c, ci) → c < l.length
  | [], _, _, h => by simp [idxSpec] at h
  | cj :: cs, c, ci, h => by
    rw [idxSpec] at h
    by_cases hn : cj.name == n
    · rw [if_pos hn] at h
      injection h with h
      injection h with h1 _
      subst h1
      simp
    · rw [if_neg hn] at h
      have := idxSpec_lt h
      simp only [List.length_cons]
      omega

/-- Forgetting the counter, the index's specification is `List.find?`. -/
theorem idxSpec_snd (n : Name) : ∀ l : List ConstantInfo,
    (idxSpec l n).map (·.2) = l.find? (·.name == n)
  | [] => rfl
  | ci :: cs => by
    rw [idxSpec]
    by_cases hn : ci.name == n
    · rw [if_pos hn]
      simp [hn]
    · rw [if_neg hn, idxSpec_snd n cs]
      simp [Bool.of_not_eq_true hn]

/-- The per-entry-call name index computes `Env.find?` (nothing is
hidden: `mkFEnv`'s bound is the constant count). -/
theorem mkFEnv_find? (env : Env) (n : Name) :
    (mkFEnv env).find? n = env.find? n := by
  rw [FEnv.find?, mkFEnv_idx, mkFEnv_visibleBelow, Env.find?,
    ← idxSpec_snd n env.consts]
  cases h : idxSpec env.consts n with
  | none => rfl
  | some p =>
    obtain ⟨c, ci⟩ := p
    show (if c < env.consts.length then some ci else none) = some ci
    rw [if_pos (idxSpec_lt h)]

/-! ## The prefix view -/

/-- The environment truncated to its first `k` installed constants
(`consts` is newest-first, so the prefix is the *tail*). -/
def Env.prefixTo (env : Env) (k : Nat) : Env :=
  ⟨env.consts.drop (env.consts.length - k)⟩

/-- The prefix at the length of a suffix environment is that
environment (task #253: the environment a declaration was installed at,
read off the final one). -/
theorem Env.prefixTo_of_extends {env env' : Env} {new : List ConstantInfo}
    (h : env'.consts = new ++ env.consts) :
    env'.prefixTo env.consts.length = env := by
  unfold Env.prefixTo
  rw [h, List.length_append, Nat.add_sub_cancel, List.drop_left]

/-- Name uniqueness of an environment's constants — the hypothesis of
`mkFEnv_find?_visibleBelow`, an install-time invariant of every driver
(`ConLeche/Verify/Cached/PushChain.lean`). -/
@[expose] def NodupNames (env : Env) : Prop := (env.consts.map (·.name)).Nodup

/-- The bounded index lookup, on the specification. -/
private def idxBelow (l : List ConstantInfo) (k : Nat) (n : Name) :
    Option ConstantInfo :=
  match idxSpec l n with
  | some (c, ci) => if c < k then some ci else none
  | none => none

private theorem idxBelow_cons_pos {k : Nat} {n : Name} {cj : ConstantInfo}
    {cs : List ConstantInfo} (hn : cj.name == n) :
    idxBelow (cj :: cs) k n = if cs.length < k then some cj else none := by
  rw [idxBelow, idxSpec, if_pos hn]

private theorem idxBelow_cons_neg {k : Nat} {n : Name} {cj : ConstantInfo}
    {cs : List ConstantInfo} (hn : ¬ (cj.name == n)) :
    idxBelow (cj :: cs) k n = idxBelow cs k n := by
  rw [idxBelow, idxSpec, if_neg hn, idxBelow]

/-- **Soundness of the bound, unconditional**: whatever the bounded
lookup finds, the truncated list finds too — a bounded lookup can never
see past its bound. -/
private theorem idxBelow_eq_some {k : Nat} {n : Name} {ci : ConstantInfo} :
    ∀ {l : List ConstantInfo}, idxBelow l k n = some ci →
      (l.drop (l.length - k)).find? (·.name == n) = some ci
  | [], h => by simp [idxBelow, idxSpec] at h
  | cj :: cs, h => by
    by_cases hn : cj.name == n
    · rw [idxBelow_cons_pos hn] at h
      by_cases hk : cs.length < k
      · rw [if_pos hk] at h
        injection h with h; subst h
        rw [List.length_cons, Nat.sub_eq_zero_of_le hk, List.drop_zero,
          List.find?_cons]
        simp only [hn]
      · rw [if_neg hk] at h; exact absurd h (by simp)
    · rw [idxBelow_cons_neg hn] at h
      have ih := idxBelow_eq_some (l := cs) h
      by_cases hk : cs.length < k
      · rw [List.length_cons, Nat.sub_eq_zero_of_le hk, List.drop_zero,
          List.find?_cons]
        simp only [Bool.of_not_eq_true hn]
        rwa [Nat.sub_eq_zero_of_le (Nat.le_of_lt hk), List.drop_zero] at ih
      · rw [List.length_cons,
          show cs.length + 1 - k = (cs.length - k) + 1 by omega,
          List.drop_succ_cons]
        exact ih

/-- **The bound is the prefix**: under name uniqueness the bounded
lookup is exactly the lookup in the truncated list.  (Without it the
bounded lookup can only return *less*: a name shadowed inside the
prefix by a newer entry above the bound.) -/
private theorem idxBelow_eq {k : Nat} {n : Name} :
    ∀ {l : List ConstantInfo}, (l.map (·.name)).Nodup →
      idxBelow l k n = (l.drop (l.length - k)).find? (·.name == n)
  | [], _ => by simp [idxBelow, idxSpec]
  | cj :: cs, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hmem, hnd⟩ := hnd
    have ih := idxBelow_eq (k := k) (n := n) hnd
    by_cases hk : cs.length < k
    · rw [List.length_cons, Nat.sub_eq_zero_of_le hk, List.drop_zero,
        List.find?_cons]
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hk), List.drop_zero] at ih
      by_cases hn : cj.name == n
      · rw [idxBelow_cons_pos hn, if_pos hk]
        simp only [hn]
      · rw [idxBelow_cons_neg hn, ih]
        simp only [Bool.of_not_eq_true hn]
    · rw [List.length_cons,
        show cs.length + 1 - k = (cs.length - k) + 1 by omega,
        List.drop_succ_cons]
      by_cases hn : cj.name == n
      · rw [idxBelow_cons_pos hn, if_neg hk]
        refine Eq.symm ((List.find?_eq_none).2 (fun x hx => ?_))
        have hx' : x ∈ cs := List.mem_of_mem_drop hx
        have hne : x.name ≠ cj.name := fun he =>
          hmem (List.mem_map.2 ⟨x, hx', he⟩)
        have hcj : cj.name = n := by simpa using hn
        simp only [beq_iff_eq]
        exact fun he => hne (he.trans hcj.symm)
      · rw [idxBelow_cons_neg hn, ih]

/-- The bounded index lookup on `mkFEnv` is the specification's. -/
private theorem restrictTo_find?_eq (env : Env) (k : Nat) (n : Name) :
    ((mkFEnv env).restrictTo k).find? n = idxBelow env.consts k n := by
  show (match (mkFEnv env).idx[n]? with
        | some (c, ci) => if c < k then some ci else none
        | none => none) = _
  rw [mkFEnv_idx, idxBelow]

/-- **Soundness of the bound** (unconditional): a bounded lookup in the
full index returns only what the environment truncated to that prefix
returns.  Nothing installed at or after the bound is reachable. -/
theorem mkFEnv_find?_visibleBelow_some {env : Env} {k : Nat} {n : Name}
    {ci : ConstantInfo} (h : ((mkFEnv env).restrictTo k).find? n = some ci) :
    (env.prefixTo k).find? n = some ci := by
  rw [restrictTo_find?_eq] at h
  exact idxBelow_eq_some h

/-- **The bounded index is the prefix environment** (the load-bearing
equivalence for the split driver): looking a name up in the full index
with the bound `k` is looking it up in the environment truncated to its
first `k` installed constants.  The hypothesis is name uniqueness, which
the checker establishes at insertion (`checkConstantValP` rejects a
duplicate name before any push). -/
theorem mkFEnv_find?_visibleBelow (env : Env) (k : Nat) (n : Name)
    (hnd : (env.consts.map (·.name)).Nodup) :
    ((mkFEnv env).restrictTo k).find? n = (env.prefixTo k).find? n := by
  rw [restrictTo_find?_eq, idxBelow_eq hnd, Env.prefixTo, Env.find?]

/-- Pushing the next installed constant onto a restricted view is
raising the bound by one: a re-check that walks a declaration's
provisional environments sees exactly what the original interleaved run
saw at each of them. -/
theorem restrictTo_push_find? (env : Env) (k : Nat) (n : Name)
    (ci : ConstantInfo) (hnd : (env.consts.map (·.name)).Nodup)
    (hci : (env.prefixTo (k + 1)).consts = ci :: (env.prefixTo k).consts) :
    (((mkFEnv env).restrictTo k).push ci).find? n
      = ((mkFEnv env).restrictTo (k + 1)).find? n := by
  show (match ((mkFEnv env).idx.insert ci.name (k, ci))[n]? with
        | some (c, cj) => if c < k + 1 then some cj else none
        | none => none)
      = ((mkFEnv env).restrictTo (k + 1)).find? n
  rw [Std.HashMap.getElem?_insert]
  by_cases hn : ci.name == n
  · rw [if_pos hn]
    show (if k < k + 1 then some ci else none) = _
    rw [if_pos (Nat.lt_succ_self k)]
    have hb := mkFEnv_find?_visibleBelow env (k + 1) n hnd
    rw [hb, Env.find?, hci, List.find?_cons]
    simp only [hn]
  · rw [if_neg hn]
    show _ = (match (mkFEnv env).idx[n]? with
        | some (c, cj) => if c < k + 1 then some cj else none
        | none => none)
    rfl


/-! ## The `FEnv` index agrees with `Env.find?`

(`mkFEnv_find?` itself, and the bounded-lookup theory it now sits in,
are in `ConLeche/Verify/EnvBound.lean`.) -/

/-- The indexed projection lookup computes `Env.findProj?`. -/
theorem mkFEnv_findProj? (env : Env) (T : Name) (i : Nat) :
    (mkFEnv env).findProj? T i = env.findProj? T i := by
  rw [FEnv.findProj?, Env.findProj?, mkFEnv_find?]
  rfl

/-! ## Guard twins agree with the `Env` versions -/

theorem natLitSupportedF_eq (env : Env) :
    natLitSupportedF (mkFEnv env) = natLitSupported env := by
  simp only [natLitSupportedF, natLitSupported, mkFEnv_find?]

theorem strLitSupportedF_eq (env : Env) :
    strLitSupportedF (mkFEnv env) = strLitSupported env := by
  simp only [strLitSupportedF, strLitSupported, mkFEnv_find?,
    natLitSupportedF_eq]

theorem natOpStoredF_eq (env : Env) (c : Name) :
    natOpStoredF (mkFEnv env) c = natOpStored env c := by
  simp only [natOpStoredF, natOpStored, mkFEnv_find?]
  rfl

theorem natOpGuardF_eq (env : Env) (c : Name) :
    natOpGuardF (mkFEnv env) c = natOpGuard env c := by
  simp only [natOpGuardF, natOpGuard, mkFEnv_find?, natLitSupportedF_eq]
  rfl

/-! ## The `Pi`-residual spelling

`Expr.instPis` (the spec's telescope instantiation) and the core's
`piResidual` are the same function; both engines' `inferSpine` reduce
through it. -/

/-- `Expr.instPis` and the core's `piResidual` are the same function. -/
theorem instPis_eq_piResidual :
    ∀ (e : Expr) (as : List Expr), e.instPis as = piResidual e as
  | _, [] => rfl
  | .forallE _ b _, a :: as => instPis_eq_piResidual (b.instantiate1 a) as
  | .bvar _, _ :: _ | .fvar _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _ _, _ :: _
  | .letE _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

end ConLeche
