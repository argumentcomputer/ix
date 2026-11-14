import IxVMRefinement.Core.Ctx

/-! # Roles in force bring their blocks and dependencies into force

A well-formed role table (`RoleTable.wf`: `RoleTable.check` succeeds) binds, with every role it
binds, the roles of that role's block (`Role.block`) and the roles it depends on (`Role.deps`):
`check`'s loops over the bound roles test exactly that (`RoleClosure.check_closed`). The
validation schedule (`Ix.SpecDigest.groupOf`) puts a block in one group and a dependency in an
earlier group (`RoleClosure.groupOf_block`, `RoleClosure.groupOf_dep`, decided). So a role in
force (`Ctx.inForce`) brings its block and its dependencies into force
(`Ctx.inForce_of_block_or_dep`).

The native rules' guards read off the roles a circuit lookup finds come with it: a lookup that
finds `Nat.zero` or `Nat.succ` in force has `Nat`'s block in force (`natLitSupported`), one that
finds `Nat.add` has its dependency `Nat`, and one that finds `String.ofList` has `String`
(`strLitSupported`). -/

namespace IxVM.Refinement.Core

namespace RoleClosure

open Ix.Kernel Ix.SpecDigest

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- A bind in `Except` that succeeds: both steps succeed. -/
theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- **A loop in `Except` that succeeds, over a body that only continues**: the body succeeds,
continuing, at every element. -/
theorem forIn_ok_all {ε α : Type} {l : List α} {f : α → Unit → Except ε (ForInStep Unit)}
    (h : forIn l () f = .ok ()) (hf : ∀ a s, f a () = .ok s → s = .yield ()) :
    ∀ a ∈ l, f a () = .ok (.yield ()) := by
  induction l with
  | nil => intro a ha; cases ha
  | cons x xs ih =>
    intro a ha
    rw [List.forIn_cons] at h
    obtain ⟨s, hs, h2⟩ := except_bind_ok h
    obtain rfl := hf x s hs
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hs
    · exact ih h2 a ha

/-- A well-formed table passes its check. -/
theorem check_ok_of_wf {t : RoleTable} (hwf : t.wf = true) : t.check = .ok () := by
  unfold Ix.Kernel.RoleTable.wf at hwf
  cases hc : t.check with
  | ok u => rfl
  | error e => rw [hc] at hwf; simp [Except.isOk, Except.toBool] at hwf

/-- **A table that passes its check binds the block and the dependencies of every role it
binds** (`RoleTable.check`'s loop over the bound roles). -/
theorem check_closed {t : RoleTable} (h : t.check = .ok ()) :
    ∀ p ∈ t.bound.toList, ∀ s, s ∈ p.1.block ∨ s ∈ p.1.deps → s ∈ t.bound.toList.map (·.1) := by
  intro p hp s hs
  obtain ⟨r, a⟩ := p
  dsimp only at hs
  unfold RoleTable.check at h
  by_cases hv : (t.version == specVersion) = true
  case neg =>
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, h1, -⟩ := except_bind_ok h
    first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
  by_cases hn : (List.map (fun x => x.fst) t.bound.toList).Nodup
  case neg =>
    simp only [hv, hn, ↓reduceIte] at h
    obtain ⟨_, h1, -⟩ := except_bind_ok h
    first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
  cases hfr : RoleTable.firstRepeat (List.map (fun x => x.snd) t.bound.toList) with
  | some a0 =>
    simp only [hv, hn, hfr, ↓reduceIte] at h
    obtain ⟨_, h1, -⟩ := except_bind_ok h
    first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
  | none =>
    simp only [hv, hn, hfr, ↓reduceIte] at h
    obtain ⟨v, heq, -⟩ := except_bind_ok h
    cases v
    rw [← Array.forIn_toList] at heq
    have key := forIn_ok_all heq (by
      intro b st hst
      obtain ⟨r', a'⟩ := b
      obtain ⟨_, -, hst⟩ := except_bind_ok hst
      obtain ⟨_, -, hst⟩ := except_bind_ok hst
      simp only [pure, Except.pure, Except.ok.injEq] at hst
      exact hst.symm) (r, a) hp
    obtain ⟨v1, hblock, key⟩ := except_bind_ok key
    obtain ⟨v2, hdeps, -⟩ := except_bind_ok key
    cases v1
    cases v2
    rcases hs with hs | hs
    · have h3 := forIn_ok_all hblock (by
        intro b st hst
        dsimp only at hst
        split at hst
        · simp only [pure, Except.pure, Except.ok.injEq] at hst
          exact hst.symm
        · obtain ⟨_, h1, -⟩ := except_bind_ok hst
          first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1) s hs
      dsimp only at h3
      split at h3
      · rename_i hc
        simpa using hc
      · obtain ⟨_, h1, -⟩ := except_bind_ok h3
        first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1
    · have h3 := forIn_ok_all hdeps (by
        intro b st hst
        dsimp only at hst
        split at hst
        · simp only [pure, Except.pure, Except.ok.injEq] at hst
          exact hst.symm
        · obtain ⟨_, h1, -⟩ := except_bind_ok hst
          first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1) s hs
      dsimp only at h3
      split at h3
      · rename_i hc
        simpa using hc
      · obtain ⟨_, h1, -⟩ := except_bind_ok h3
        first | cases h1 | simp [throw, throwThe, MonadExceptOf.throw] at h1

/-- The table binds a role exactly when the role is among its bound roles. -/
theorem isSome_addressOf {t : RoleTable} {r : Role} :
    (t.addressOf? r).isSome = true ↔ r ∈ t.bound.toList.map (·.1) := by
  unfold RoleTable.addressOf?
  simp [Array.find?_isSome]

/-- **A well-formed table that binds a role binds its block and its dependencies.** -/
theorem binds_of_block_or_dep {t : RoleTable} (hwf : t.wf = true) {r s : Role}
    (hr : (t.addressOf? r).isSome = true) (hs : s ∈ r.block ∨ s ∈ r.deps) :
    (t.addressOf? s).isSome = true := by
  obtain ⟨p, hp, hpr⟩ := List.mem_map.mp (isSome_addressOf.mp hr)
  obtain ⟨r', a⟩ := p
  dsimp only at hpr
  subst hpr
  exact isSome_addressOf.mpr (check_closed (check_ok_of_wf hwf) (r', a) hp s hs)

set_option maxRecDepth 100000 in
/-- **A dependency is validated in an earlier group** (the schedule, decided). -/
theorem groupOf_dep : ∀ r : Role, ∀ s ∈ r.deps, groupOf s < groupOf r := by
  intro r; cases r <;> decide

set_option maxRecDepth 100000 in
/-- **A block is validated in one group** (the schedule, decided). -/
theorem groupOf_block : ∀ r : Role, ∀ s ∈ r.block, groupOf s = groupOf r := by
  intro r; cases r <;> decide

end RoleClosure

/-- **A role in force brings its block and its dependencies into force**, under a well-formed
table: the table binds them with it (`RoleTable.check`), and the schedule validates a block in
one group and a dependency earlier (`Ix.SpecDigest.groupOf`). -/
theorem Ctx.inForce_of_block_or_dep {c : Ctx} (hwf : c.t.wf = true) {r s : Ix.Kernel.Role}
    (hr : c.inForce r) (hs : s ∈ r.block ∨ s ∈ r.deps) : c.inForce s := by
  obtain ⟨hb, hg⟩ := hr
  refine ⟨RoleClosure.binds_of_block_or_dep hwf hb hs, fun n hn => ?_⟩
  rcases hs with hs | hs
  · rw [RoleClosure.groupOf_block r s hs]
    exact hg n hn
  · exact Nat.lt_trans (RoleClosure.groupOf_dep r s hs) (hg n hn)

end IxVM.Refinement.Core
