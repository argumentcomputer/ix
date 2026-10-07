import Ix.CompileCert.Canon.NestedCanon
import Ix.CompileCert.Canon.Perm

/-!
# M7 L1, evaporation

`Ix.Compile.Canon.evaporate env rules all comps here n` (design document §2.6; the compiler's
`AuxLayout.evaporated`) sets the evaporation flag of each of Lean's nested positions `j` of the
component `here` that

1. has no canonical position in the component (`n.perm[j] = none`),
2. is owned by a member of the component,
3. was exported by Lean (`all₀.rec_{j+1}` exists),
4. is discovered canonically by no other component of the block: no other component whose members
   the occurrence mentions has, in its own canonical expansion, a signature matching it
   (`ClaimedElsewhere`), and
5. whose external head's recursor has one motive (`TargetOk`).

`evaporate_spec`: the flags are exactly the old flags plus the positions satisfying 1–5
(`Evaporates`), and nothing else of the nested data changes. Corollaries: an evaporated position of
a component has no canonical position there (`evaporated_perm_none`, for the nested data
`canonBlock` computes), so the block name map never sends one name both to a canonical auxiliary and
to `evaporated` within a component.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name ConstantInfo)

/-- The names of a component's classes, as `evaporate` collects them. -/
abbrev compMembersOf (cls : Array (Array Name)) : Std.HashSet Name :=
  cls.foldl (fun s c => c.foldl (fun x1 x2 => x1.insert x2) s) ∅

/-- The block's members outside a component, compared strictly by name. -/
abbrev strictFor (all : Array Name) (cls : Array (Array Name)) : Std.HashSet Name :=
  all.foldl (fun st m => if (compMembersOf cls).contains m = true then st else st.insert m) ∅

/-- The block members a source occurrence mentions (constants and projection names). -/
abbrev refsOfSig (all : Array Name) (s : Sig) : Std.HashSet Name :=
  s.specs.foldl (fun acc e => (constsIn (originalsOf all) e).fold (fun x1 x2 => x1.insert x2) acc) ∅

/-- The deduplication key the rule set uses for a canonical expansion. -/
abbrev keyAddrOf (rules : Rules) (env : Env) : Option (Name → Option Address) :=
  if (rules.nested == .discovery) = true then some env.addr? else none

/-- The component `ci` (classes `cls`) discovers the source occurrence `s` canonically: it is not
`here`, the occurrence mentions one of its members, and its canonical expansion has a signature
matching the occurrence (its members renamed to their representatives). -/
def Claims (env : Env) (rules : Rules) (all : Array Name) (here : Nat) (s : Sig)
    (e : Array (Array Name) × Nat) : Prop :=
  e.2 ≠ here ∧ (refsOfSig all s).toList.any (compMembersOf e.1).contains = true ∧
    ∃ x, expand env.ind? rules.dedup (repsOf e.1) (aliasesOf e.1) env.groupOf (keyAddrOf rules env) = .ok x ∧
      (matchSig env.addr? (strictFor all e.1) x.sigs s.head s.levels
        (s.specs.map (replaceConstNames (origToCanonOf e.1)))).isSome = true

/-- Another component of the block discovers the occurrence canonically. -/
def ClaimedElsewhere (env : Env) (rules : Rules) (all : Array Name)
    (comps : Array (Array (Array Name))) (here : Nat) (s : Sig) : Prop :=
  (refsOfSig all s).isEmpty = false ∧ ∃ ci cls, comps[ci]? = some cls ∧ Claims env rules all here s (cls, ci)

/-- The external head's recursor has one motive. -/
def TargetOk (env : Env) (s : Sig) : Prop :=
  ∃ r, env.const? (s.head.mkStr "rec") = some (.recInfo r) ∧ r.numMotives = 1

/-- Lean's position `j` evaporates from the component `here` (conditions 1–5). -/
def Evaporates (env : Env) (rules : Rules) (all : Array Name) (comps : Array (Array (Array Name)))
    (here : Nat) (n : NestedCanon) (j : Nat) : Prop :=
  n.perm[j]? = some none ∧ ∃ all0 hereComp s, all[0]? = some all0 ∧ comps[here]? = some hereComp ∧
    n.source[j]? = some s ∧ (compMembersOf hereComp).contains s.owner = true ∧
    (env.const? (all0.mkStr s!"rec_{j + 1}")).isSome = true ∧
    ¬ ClaimedElsewhere env rules all comps here s ∧ TargetOk env s

theorem bfalse {b : Bool} (h : ¬ b = true) : b = false := by cases b <;> simp_all

theorem targetOk_iff {env : Env} {s : Sig} :
    (match env.const? (s.head.mkStr "rec") with
      | some (ConstantInfo.recInfo r) => r.numMotives == 1
      | _ => false) = true ↔ TargetOk env s := by
  unfold TargetOk
  split
  · rename_i r hr
    rw [hr]
    simp only [beq_iff_eq, Option.some.injEq, ConstantInfo.recInfo.injEq, exists_eq_left']
  · rename_i hr
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro r hr'
    exact absurd hr' (hr r)

/-- The flag invariant of the outer loop over the processed prefix. -/
def FlagsInv (env : Env) (rules : Rules) (all : Array Name) (comps : Array (Array (Array Name)))
    (here : Nat) (n : NestedCanon) (pre : List (Option Nat × Nat)) (flags : Array Bool) : Prop :=
  flags.size = n.evaporated.size ∧ ∀ j, flags[j]? = some true ↔
    (n.evaporated[j]? = some true ∨
      (j ∈ pre.map Prod.snd ∧ j < n.evaporated.size ∧ Evaporates env rules all comps here n j))

theorem setBang_getElem? (a : Array Bool) (j j' : Nat) :
    (a.set! j true)[j']? = if j' = j ∧ j < a.size then some true else a[j']? := by
  unfold Array.set!
  rw [Array.getElem?_setIfInBounds]
  by_cases h1 : j = j'
  · subst h1
    by_cases h2 : j < a.size
    · simp [h2]
    · simp [h2]
  · have h1' : ¬ j' = j := fun h => h1 h.symm
    simp [h1, h1']

/-- **Evaporation, against the code**: the flags are exactly the old flags and the positions
satisfying the five conditions (`Evaporates`); nothing else of the nested data changes. -/
theorem evaporate_spec {env : Env} {rules : Rules} {all : Array Name}
    {comps : Array (Array (Array Name))} {here : Nat} {n n' : NestedCanon}
    (h : evaporate env rules all comps here n = .ok n') :
    n'.source = n.source ∧ n'.canonClasses = n.canonClasses ∧ n'.canon = n.canon ∧
      n'.perm = n.perm ∧ n'.addrDecided = n.addrDecided ∧
      n'.evaporated.size = n.evaporated.size ∧
      ∀ j, n'.evaporated[j]? = some true ↔
        (n.evaporated[j]? = some true ∨
          (j < n.evaporated.size ∧ Evaporates env rules all comps here n j)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := evaporate_fields h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  unfold evaporate at h
  split at h
  · -- no `none` in `perm`: nothing evaporates
    rename_i hc
    cases except_pure_ok h
    refine ⟨rfl, fun j => ⟨.inl, ?_⟩⟩
    rintro (h | ⟨-, hp, -⟩)
    · exact h
    · exfalso
      have : none ∈ n.perm := by
        obtain ⟨k, hk⟩ := (⟨j, hp⟩ : ∃ k, n.perm[k]? = some none)
        exact Array.mem_of_getElem? hk
      have := Array.contains_iff_mem.2 this
      simp only [this, Bool.not_true] at hc
      exact absurd hc (by decide)
  · split at h
    · rename_i all0 hall0
      split at h
      · rename_i hereComp hhere
        obtain ⟨flags, hfl, h⟩ := except_bind_ok.1 h
        cases except_pure_ok h
        have inv := forIn_except_array_mem _ (FlagsInv env rules all comps here n) n.perm.zipIdx
          ?step (⟨rfl, fun j => ⟨.inl, by rintro (h | ⟨hj, -⟩); exact h; simp at hj⟩⟩) hfl
        · refine ⟨inv.1, fun j => ?_⟩
          rw [inv.2 j]
          constructor
          · rintro (h | ⟨-, hj, he⟩)
            · exact .inl h
            · exact .inr ⟨hj, he⟩
          · rintro (h | ⟨hj, he⟩)
            · exact .inl h
            · refine .inr ⟨?_, hj, he⟩
              have hp := he.1
              rw [Array.toList_zipIdx, List.mem_map]
              exact ⟨(none, j), List.mem_zipIdx_iff_getElem?.2 (by
                rw [Array.getElem?_toList]; simpa using hp), rfl⟩
        case step =>
          intro pre x fl st hx hinv hs
          obtain ⟨p, j⟩ := x
          have hpj : n.perm[j]? = some p := by
            rw [Array.toList_zipIdx] at hx
            have := List.mem_zipIdx_iff_getElem?.1 hx
            rw [Array.getElem?_toList] at this
            simpa using this
          -- the cases where the flags stay
          have keep : ¬ Evaporates env rules all comps here n j → FlagsInv env rules all comps here n
              (pre ++ [(p, j)]) fl := by
            intro hne
            refine ⟨hinv.1, fun j' => ?_⟩
            rw [hinv.2 j']
            simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
              List.mem_singleton]
            constructor
            · rintro (h | ⟨hm, hl, he⟩)
              · exact .inl h
              · exact .inr ⟨.inl hm, hl, he⟩
            · rintro (h | ⟨hm | rfl, hl, he⟩)
              · exact .inl h
              · exact .inr ⟨hm, hl, he⟩
              · exact absurd he hne
          dsimp only at hs
          by_cases hsome : p.isSome = true
          · simp only [hsome, ↓reduceIte] at hs
            cases except_pure_ok hs
            refine ⟨fl, rfl, keep fun he => ?_⟩
            have hp' := he.1
            rw [hpj] at hp'; cases hp'
            simp at hsome
          have hp : p = none := Option.not_isSome_iff_eq_none.1 hsome
          subst hp
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hs
          cases hsj : n.source[j]? with
          | none =>
            simp only [hsj] at hs
            cases except_pure_ok hs
            refine ⟨fl, rfl, keep fun he => ?_⟩
            obtain ⟨-, -, -, s', -, -, hs', -⟩ := he
            rw [hsj] at hs'; cases hs'
          | some s => ?_
          simp only [hsj] at hs
          by_cases hin0 : (compMembersOf hereComp).contains s.owner = false
          · simp only [hin0, Bool.not_false, ↓reduceIte] at hs
            cases except_pure_ok hs
            refine ⟨fl, rfl, keep fun he => ?_⟩
            obtain ⟨-, a0, hc, s', ha0, hhc, hs', hin', -⟩ := he
            rw [hhere] at hhc; cases hhc
            rw [hsj] at hs'; cases hs'
            rw [hin0] at hin'; cases hin'
          have hin : (compMembersOf hereComp).contains s.owner = true := by simpa using hin0
          simp only [hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
          by_cases hrec : (env.const? (all0.mkStr s!"rec_{j + 1}")).isNone = true
          · simp only [hrec, ↓reduceIte] at hs
            cases except_pure_ok hs
            refine ⟨fl, rfl, keep fun he => ?_⟩
            obtain ⟨-, a0, hc, s', ha0, hhc, hs', -, hr, -⟩ := he
            rw [hall0] at ha0; cases ha0
            rw [hsj] at hs'; cases hs'
            rw [Option.isNone_iff_eq_none] at hrec
            rw [hrec] at hr; cases hr
          have hrec0 : (env.const? (all0.mkStr s!"rec_{j + 1}")).isNone = false := bfalse hrec
          simp only [hrec0, Bool.false_eq_true, ↓reduceIte] at hs
          have hrec' : (env.const? (all0.mkStr s!"rec_{j + 1}")).isSome = true := by
            cases hq : env.const? (all0.mkStr s!"rec_{j + 1}") with
            | none => rw [hq] at hrec0; cases hrec0
            | some _ => rfl
          -- the target's recursor
          have notTarget : ¬ TargetOk env s → ∀ c : Bool,
              (if c = true then (pure (ForInStep.yield fl) : Except String (ForInStep (Array Bool)))
                else pure (ForInStep.yield fl)) = .ok st →
              ∃ r', st = .yield r' ∧ FlagsInv env rules all comps here n (pre ++ [(none, j)]) r' := by
            intro ht c hc
            have : st = .yield fl := by cases c <;> exact (except_pure_ok hc).symm
            subst this
            refine ⟨fl, rfl, keep fun he => ?_⟩
            obtain ⟨-, a0, hc', s', ha0, hhc, hs', -, -, -, ht'⟩ := he
            rw [hsj] at hs'; cases hs'
            exact ht ht'
          -- the claim loop, when the occurrence mentions some member
          have claimFinal : ∀ (cl : Bool),
              (cl = true ↔ ∃ e ∈ comps.zipIdx.toList, Claims env rules all here s e) →
              (refsOfSig all s).isEmpty = false →
              (cl = true ↔ ClaimedElsewhere env rules all comps here s) := by
            intro cl cinv hne
            rw [cinv]
            constructor
            · rintro ⟨⟨cls, ci⟩, he, hc⟩
              refine ⟨hne, ci, cls, ?_, hc⟩
              have := List.mem_zipIdx_iff_getElem?.1 (by rwa [Array.toList_zipIdx] at he)
              rw [Array.getElem?_toList] at this; simpa using this
            · rintro ⟨-, ci, cls, hci, hc⟩
              refine ⟨(cls, ci), ?_, hc⟩
              rw [Array.toList_zipIdx]
              exact List.mem_zipIdx_iff_getElem?.2 (by rw [Array.getElem?_toList]; simpa using hci)
          cases hrecv : env.const? (s.head.mkStr "rec") with
          | none =>
            have ht : ¬ TargetOk env s := by rintro ⟨r, hr, -⟩; rw [hrecv] at hr; cases hr
            simp only [hrecv, Bool.false_eq_true, ↓reduceIte] at hs
            split at hs
            · obtain ⟨cl, -, hs⟩ := except_bind_ok.1 hs
              exact notTarget ht cl hs
            · exact notTarget ht false hs
          | some ci => ?_
          cases ci with
          | recInfo r =>
            by_cases hmot : r.numMotives = 1
            · have ht : TargetOk env s := ⟨r, hrecv, hmot⟩
              simp only [hrecv, hmot, beq_self_eq_true, ↓reduceIte] at hs
              have setCase : ∀ c : Bool, (c = true ↔ ClaimedElsewhere env rules all comps here s) →
                  (if c = true then (pure (ForInStep.yield fl) : Except String (ForInStep (Array Bool)))
                    else pure (ForInStep.yield (fl.set! j true))) = .ok st →
                  ∃ r', st = .yield r' ∧ FlagsInv env rules all comps here n (pre ++ [(none, j)]) r' := by
                intro c hcl hc
                cases c with
                | true =>
                  cases except_pure_ok hc
                  refine ⟨fl, rfl, keep fun he => ?_⟩
                  obtain ⟨-, a0, hc', s', ha0, hhc, hs', -, -, hno, -⟩ := he
                  rw [hsj] at hs'; cases hs'
                  exact hno (hcl.1 rfl)
                | false =>
                  cases except_pure_ok hc
                  have he : Evaporates env rules all comps here n j :=
                    ⟨hpj, all0, hereComp, s, hall0, hhere, hsj, hin, hrec',
                      (fun hce => by have := hcl.2 hce; cases this), ht⟩
                  refine ⟨fl.set! j true, rfl, ?_, fun j' => ?_⟩
                  · rw [Array.size_set!]; exact hinv.1
                  · rw [setBang_getElem?]
                    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                      List.mem_singleton]
                    by_cases hjj : j' = j
                    · subst hjj
                      by_cases hsz : j' < fl.size
                      · simp only [and_self, hsz, ite_true, true_iff]
                        rw [hinv.1] at hsz
                        exact .inr ⟨.inr trivial, hsz, he⟩
                      · simp only [hsz, and_false, ite_false]
                        rw [hinv.2 j']
                        rw [hinv.1] at hsz
                        constructor
                        · rintro (h | ⟨-, hl, -⟩)
                          · exact .inl h
                          · exact absurd hl hsz
                        · rintro (h | ⟨-, hl, -⟩)
                          · exact .inl h
                          · exact absurd hl hsz
                    · simp only [hjj, false_and, ite_false]
                      rw [hinv.2 j']
                      constructor
                      · rintro (h | ⟨hm, hl, he⟩)
                        · exact .inl h
                        · exact .inr ⟨.inl hm, hl, he⟩
                      · rintro (h | ⟨hm | hm, hl, he⟩)
                        · exact .inl h
                        · exact .inr ⟨hm, hl, he⟩
                        · exact hm.elim
              split at hs
              · rename_i hne
                have hne0 : (refsOfSig all s).isEmpty = false := by simpa using hne
                obtain ⟨cl, hcl, hs⟩ := except_bind_ok.1 hs
                have cinv := forIn_except_array_mem _
                  (fun pre (c : Bool) => c = true ↔ ∃ e ∈ pre, Claims env rules all here s e)
                  comps.zipIdx (by
                    intro cpre e c cst _ hci hcs
                    obtain ⟨cls, ci⟩ := e
                    have keepC : ¬ Claims env rules all here s (cls, ci) → cst = .yield c →
                        ∃ c', cst = .yield c' ∧
                          (c' = true ↔ ∃ e' ∈ cpre ++ [(cls, ci)], Claims env rules all here s e') := by
                      intro hnc hcst
                      refine ⟨c, hcst, ?_⟩
                      rw [hci]; simp only [List.mem_append, List.mem_singleton]
                      constructor
                      · rintro ⟨e, he, hc⟩; exact ⟨e, .inl he, hc⟩
                      · rintro ⟨e, he | rfl, hc⟩
                        · exact ⟨e, he, hc⟩
                        · exact absurd hc hnc
                    dsimp only at hcs
                    split at hcs
                    · rename_i heq
                      have heq' : ci = here := by simpa using heq
                      exact keepC (fun hc => hc.1 heq') (except_pure_ok hcs).symm
                    · rename_i heq
                      have heq' : ci ≠ here := by simpa using heq
                      split at hcs
                      · rename_i hany
                        have hany0 : (refsOfSig all s).toList.any (compMembersOf cls).contains = false := by
                          simpa using hany
                        exact keepC (fun hc => by have := hc.2.1; rw [hany0] at this; cases this)
                          (except_pure_ok hcs).symm
                      · rename_i hany
                        have hany1 : (refsOfSig all s).toList.any (compMembersOf cls).contains = true := by
                          simpa using hany
                        obtain ⟨x, hx, hcs⟩ := except_bind_ok.1 hcs
                        split at hcs
                        · rename_i hm
                          cases except_pure_ok hcs
                          refine ⟨true, rfl, ?_⟩
                          simp only [List.mem_append, List.mem_singleton, true_iff]
                          exact ⟨(cls, ci), .inr rfl, heq', hany1, x, hx, hm⟩
                        · rename_i hm
                          refine keepC (fun hc => ?_) (except_pure_ok hcs).symm
                          obtain ⟨-, -, x', hx', hm'⟩ := hc
                          have e := hx.symm.trans hx'; cases e
                          exact hm hm') (by simp) hcl
                exact setCase cl (claimFinal cl cinv hne0) hs
              · rename_i hne
                have hne1 : (refsOfSig all s).isEmpty = true := by simpa using hne
                refine setCase false ?_ hs
                simp only [Bool.false_eq_true, false_iff]
                rintro ⟨hne', -⟩
                rw [hne1] at hne'; cases hne'
            · have ht : ¬ TargetOk env s := by
                rintro ⟨r', hr', hm'⟩; rw [hrecv] at hr'; cases hr'; exact hmot hm'
              have hmot0 : (r.numMotives == 1) = false := bfalse (fun h => hmot (beq_iff_eq.1 h))
              simp only [hrecv, hmot0, Bool.false_eq_true, ↓reduceIte] at hs
              split at hs
              · obtain ⟨cl, -, hs⟩ := except_bind_ok.1 hs
                exact notTarget ht cl hs
              · exact notTarget ht false hs
          | _ =>
            all_goals
              have ht : ¬ TargetOk env s := by rintro ⟨r', hr', -⟩; rw [hrecv] at hr'; cases hr'
              simp only [hrecv, Bool.false_eq_true, ↓reduceIte] at hs
              split at hs
              · obtain ⟨cl, -, hs⟩ := except_bind_ok.1 hs
                exact notTarget ht cl hs
              · exact notTarget ht false hs
      · cases h
    · rename_i hall0
      cases except_pure_ok h
      refine ⟨rfl, fun j => ⟨.inl, ?_⟩⟩
      rintro (h | ⟨-, -, a0, -, -, ha0, -⟩)
      · exact h
      · exact absurd ha0 (fun h => hall0 _ h)

theorem evaporates_congr {env : Env} {rules : Rules} {all : Array Name}
    {comps : Array (Array (Array Name))} {here : Nat} {n m : NestedCanon} (hp : n.perm = m.perm)
    (hs : n.source = m.source) (j : Nat) :
    Evaporates env rules all comps here n j ↔ Evaporates env rules all comps here m j := by
  unfold Evaporates; rw [hp, hs]

/-- **Evaporation in `canonBlock`** (under the discovery rule): a component's evaporation flags have
one entry per Lean position, and a position is flagged exactly when it evaporates from the component
(`Evaporates`: in particular it then has no canonical position there). -/
theorem canonBlock_evaporated {rules : Rules} (hr : rules.nested = .discovery) {env : Env}
    {all : Array Name} {b : BlockCanon} (h : canonBlock rules env all = .ok b)
    {c : ComponentCanon} (hc : c ∈ b.components) {n : NestedCanon} (hn : c.nested = some n) :
    ∃ i, n.evaporated.size = n.perm.size ∧ ∀ j, n.evaporated[j]? = some true ↔
      (j < n.perm.size ∧ Evaporates env rules all (b.components.map (·.classes)) i n j) := by
  obtain ⟨i, hs⟩ := canonBlock_mem_spec h hc
  obtain ⟨n0, hn0, hev⟩ := hs.hnest
  rw [hn] at hev
  cases n0 with
  | none => cases except_pure_ok hev
  | some m =>
    obtain ⟨m', hm', hev⟩ := except_bind_ok.1 hev
    have := except_pure_ok hev
    simp only [Option.some.injEq] at this
    subst this
    obtain ⟨-, -, -, -, -, -, hrep⟩ := componentNested_some hr hn0
    obtain ⟨hsrc, -, -, hperm, -, hsize, hflags⟩ := evaporate_spec hm'
    refine ⟨i, by rw [hsize, hrep, Array.size_replicate, hperm], fun j => ?_⟩
    rw [hflags j, hrep, Array.getElem?_replicate, Array.size_replicate, hperm,
      evaporates_congr hperm hsrc]
    constructor
    · rintro (h | h)
      · split at h <;> simp at h
      · exact h
    · intro h; exact .inr h

/-- An evaporated position has no canonical position in its component. -/
theorem canonBlock_evaporated_perm {rules : Rules} (hr : rules.nested = .discovery) {env : Env}
    {all : Array Name} {b : BlockCanon} (h : canonBlock rules env all = .ok b)
    {c : ComponentCanon} (hc : c ∈ b.components) {n : NestedCanon} (hn : c.nested = some n) {j : Nat}
    (he : n.evaporated[j]? = some true) : n.perm[j]? = some none := by
  obtain ⟨i, -, hf⟩ := canonBlock_evaporated hr h hc hn
  exact ((hf j).1 he).2.1

end Ix.CompileCert.Canon
