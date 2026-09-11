import Ix.Compiler.Erase

/-!
# Argument-policy cursors

Constructor and recursor spines do not preserve argument positions
pointwise: a `keep` position consumes a source and target argument, a
`ghost` position consumes both but fixes the target argument to `◻`, and a
`drop` position consumes only a source argument.  `PolicyPrefix` records a
prefix of such a spine together with the unconsumed policy suffix.  Keeping
the suffix in the relation is the cursor needed for partial applications.

The relation is generic in the source/target argument relation and in the
target ghost value, so the simulation can instantiate it for expressions
and for evaluated values without introducing a dependency cycle.
-/

namespace Ix.Compiler.Sim

open Ix.Compiler.Erase (ArgPolicy)

/-- The structural policy of a constructor with `params` parameters and
`fields` runtime fields. -/
def ctorPolicy (params fields : Nat) : List ArgPolicy :=
  List.replicate params .drop ++ List.replicate fields .keep

/-- Generic pointwise list relation, kept here to avoid tying policy
reasoning to either evaluator's value type. -/
inductive ListRel {S T : Type} (R : S → T → Prop) :
    List S → List T → Prop where
  | nil : ListRel R [] []
  | cons {sarg targ sargs targs} :
      R sarg targ → ListRel R sargs targs →
      ListRel R (sarg :: sargs) (targ :: targs)

namespace ListRel

theorem length {S T : Type} {R : S → T → Prop}
    {sargs : List S} {targs : List T} (h : ListRel R sargs targs) :
    sargs.length = targs.length := by
  induction h <;> simp_all

theorem append {S T : Type} {R : S → T → Prop}
    {sargs : List S} {targs : List T} {sarg : S} {targ : T}
    (h : ListRel R sargs targs) (hr : R sarg targ) :
    ListRel R (sargs ++ [sarg]) (targs ++ [targ]) := by
  induction h with
  | nil => exact .cons hr .nil
  | cons hhead _ ih => exact .cons hhead ih

theorem lookup {S T : Type} {R : S → T → Prop} (i : Nat)
    {sargs : List S} {targs : List T} (h : ListRel R sargs targs)
    {sarg : S} (hs : sargs[i]? = some sarg) :
    ∃ targ, targs[i]? = some targ ∧ R sarg targ := by
  induction i generalizing sargs targs with
  | zero =>
    cases h with
    | nil => simp at hs
    | cons hhead htail =>
      simp only [List.getElem?_cons_zero] at hs ⊢
      injection hs with heq
      subst heq
      exact ⟨_, rfl, hhead⟩
  | succ i ih =>
    cases h with
    | nil => simp at hs
    | cons hhead htail =>
      simp only [List.getElem?_cons_succ] at hs ⊢
      exact ih htail hs

end ListRel

/-- Number of target arguments emitted by a policy list. -/
def policyTargetArity : List ArgPolicy → Nat
  | [] => 0
  | .keep :: rest => policyTargetArity rest + 1
  | .ghost :: rest => policyTargetArity rest + 1
  | .drop :: rest => policyTargetArity rest

@[simp] theorem policyTargetArity_replicate_drop (n : Nat) :
    policyTargetArity (List.replicate n .drop) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, policyTargetArity]

/-- A related prefix of an argument spine.  The first policy list is the
complete policy and the last one is its unconsumed suffix. -/
inductive PolicyPrefix {S T : Type} (R : S → T → Prop) (ghost : T) :
    List ArgPolicy → List S → List T → List ArgPolicy → Prop where
  | stop (policies : List ArgPolicy) :
      PolicyPrefix R ghost policies [] [] policies
  | keep {policies sargs targs rest sarg targ} :
      R sarg targ →
      PolicyPrefix R ghost policies sargs targs rest →
      PolicyPrefix R ghost (.keep :: policies) (sarg :: sargs)
        (targ :: targs) rest
  | ghost {policies sargs targs rest sarg} :
      PolicyPrefix R ghost policies sargs targs rest →
      PolicyPrefix R ghost (.ghost :: policies) (sarg :: sargs)
        (ghost :: targs) rest
  | drop {policies sargs targs rest sarg} :
      PolicyPrefix R ghost policies sargs targs rest →
      PolicyPrefix R ghost (.drop :: policies) (sarg :: sargs) targs rest

/-- All policy positions have been consumed. -/
abbrev PolicyRel {S T : Type} (R : S → T → Prop) (ghost : T)
    (policies : List ArgPolicy) (sargs : List S) (targs : List T) : Prop :=
  PolicyPrefix R ghost policies sargs targs []

/-- Runtime cursor used for recursor paps.  A ghost position still consumes a
target slot, but its value is intentionally unconstrained: exact erasure fixes
that slot to `ghost` in `PErase`, while the semantic relation remains closed
under the generic application constructor. -/
inductive RuntimePolicyPrefix {S T : Type} (R : S → T → Prop) :
    List ArgPolicy → List S → List T → List ArgPolicy → Prop where
  | stop (policies : List ArgPolicy) :
      RuntimePolicyPrefix R policies [] [] policies
  | keep {policies sargs targs rest sarg targ} :
      R sarg targ →
      RuntimePolicyPrefix R policies sargs targs rest →
      RuntimePolicyPrefix R (.keep :: policies) (sarg :: sargs)
        (targ :: targs) rest
  | ghost {policies sargs targs rest sarg targ} :
      RuntimePolicyPrefix R policies sargs targs rest →
      RuntimePolicyPrefix R (.ghost :: policies) (sarg :: sargs)
        (targ :: targs) rest
  | drop {policies sargs targs rest sarg} :
      RuntimePolicyPrefix R policies sargs targs rest →
      RuntimePolicyPrefix R (.drop :: policies) (sarg :: sargs) targs rest

/-- Every runtime policy position has been consumed. -/
abbrev RuntimePolicyRel {S T : Type} (R : S → T → Prop)
    (policies : List ArgPolicy) (sargs : List S) (targs : List T) : Prop :=
  RuntimePolicyPrefix R policies sargs targs []

namespace RuntimePolicyPrefix

theorem source_length {S T : Type} {R : S → T → Prop}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy}
    (h : RuntimePolicyPrefix R policies sargs targs rest) :
    sargs.length + rest.length = policies.length := by
  induction h <;> simp_all <;> omega

theorem target_length {S T : Type} {R : S → T → Prop}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy}
    (h : RuntimePolicyPrefix R policies sargs targs rest) :
    targs.length + policyTargetArity rest = policyTargetArity policies := by
  induction h <;> simp_all [policyTargetArity] <;> omega

/-- The stored suffix is the policy list after the consumed source prefix. -/
theorem remaining_eq_drop {S T : Type} {R : S → T → Prop}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy}
    (h : RuntimePolicyPrefix R policies sargs targs rest) :
    rest = policies.drop sargs.length := by
  induction h with
  | stop => rfl
  | keep _ _ ih | ghost _ ih | drop _ ih => simpa using ih

theorem append_keep {S T : Type} {R : S → T → Prop}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy} {sarg : S} {targ : T}
    (h : RuntimePolicyPrefix R policies sargs targs (.keep :: rest))
    (hr : R sarg targ) :
    RuntimePolicyPrefix R policies (sargs ++ [sarg]) (targs ++ [targ])
      rest := by
  generalize hrem : (.keep :: rest) = remaining at h
  induction h with
  | stop => cases hrem; exact .keep hr (.stop rest)
  | keep hhead _ ih =>
    simpa only [List.cons_append] using RuntimePolicyPrefix.keep hhead (ih hrem)
  | ghost _ ih =>
    simpa only [List.cons_append] using RuntimePolicyPrefix.ghost (ih hrem)
  | drop _ ih =>
    simpa only [List.cons_append] using RuntimePolicyPrefix.drop (ih hrem)

theorem append_ghost {S T : Type} {R : S → T → Prop}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy} {sarg : S} {targ : T}
    (h : RuntimePolicyPrefix R policies sargs targs (.ghost :: rest)) :
    RuntimePolicyPrefix R policies (sargs ++ [sarg]) (targs ++ [targ])
      rest := by
  generalize hrem : (.ghost :: rest) = remaining at h
  induction h with
  | stop => cases hrem; exact .ghost (.stop rest)
  | keep hhead _ ih =>
    simpa only [List.cons_append] using RuntimePolicyPrefix.keep hhead (ih hrem)
  | ghost _ ih =>
    simpa only [List.cons_append] using RuntimePolicyPrefix.ghost (ih hrem)
  | drop _ ih =>
    simpa only [List.cons_append] using RuntimePolicyPrefix.drop (ih hrem)

theorem append_drop {S T : Type} {R : S → T → Prop}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy} {sarg : S}
    (h : RuntimePolicyPrefix R policies sargs targs (.drop :: rest)) :
    RuntimePolicyPrefix R policies (sargs ++ [sarg]) targs rest := by
  generalize hrem : (.drop :: rest) = remaining at h
  induction h with
  | stop => cases hrem; exact .drop (.stop rest)
  | keep hhead _ ih =>
    simpa only [List.cons_append] using RuntimePolicyPrefix.keep hhead (ih hrem)
  | ghost _ ih =>
    simpa only [List.cons_append] using RuntimePolicyPrefix.ghost (ih hrem)
  | drop _ ih =>
    simpa only [List.cons_append] using RuntimePolicyPrefix.drop (ih hrem)

/-- Split a fully consumed runtime policy at a policy-list boundary. -/
theorem split {S T : Type} {R : S → T → Prop}
    {left right : List ArgPolicy} {sargs : List S} {targs : List T}
    (h : RuntimePolicyRel R (left ++ right) sargs targs) :
    ∃ sleft sright tleft tright,
      sargs = sleft ++ sright ∧ targs = tleft ++ tright ∧
      RuntimePolicyRel R left sleft tleft ∧
      RuntimePolicyRel R right sright tright := by
  induction left generalizing sargs targs with
  | nil =>
    exact ⟨[], sargs, [], targs, rfl, rfl, .stop [], by simpa using h⟩
  | cons policy left ih =>
    cases policy with
    | keep =>
      cases h with
      | keep hrel htail =>
        rename_i sarg targ
        obtain ⟨sl, sr, tl, tr, hs, ht, hl, hr⟩ := ih htail
        exact ⟨sarg :: sl, sr, targ :: tl, tr, by simp [hs], by simp [ht],
          .keep hrel hl, hr⟩
    | ghost =>
      cases h with
      | ghost htail =>
        rename_i sarg targ
        obtain ⟨sl, sr, tl, tr, hs, ht, hl, hr⟩ := ih htail
        exact ⟨sarg :: sl, sr, targ :: tl, tr, by simp [hs], by simp [ht],
          .ghost hl, hr⟩
    | drop =>
      cases h with
      | drop htail =>
        rename_i sarg
        obtain ⟨sl, sr, tl, tr, hs, ht, hl, hr⟩ := ih htail
        exact ⟨sarg :: sl, sr, tl, tr, by simp [hs], ht, .drop hl, hr⟩

/-- Split a fully consumed policy whose suffix consists only of source drops.
The suffix contributes no target arguments. -/
theorem split_suffix_drops {S T : Type} {R : S → T → Prop}
    {policies : List ArgPolicy} {n : Nat}
    {sargs : List S} {targs : List T}
    (h : RuntimePolicyRel R (policies ++ List.replicate n .drop)
      sargs targs) :
    ∃ sfront dropped,
      sargs = sfront ++ dropped ∧ dropped.length = n ∧
      RuntimePolicyRel R policies sfront targs := by
  obtain ⟨sfront, dropped, targets, discarded, hs, ht, hp, hd⟩ := h.split
  have hdiscarded : discarded = [] := by
    cases discarded with
    | nil => rfl
    | cons value rest =>
      have hlen := hd.target_length
      simp at hlen
  subst discarded
  simp only [List.append_nil] at ht
  subst targets
  refine ⟨sfront, dropped, hs, ?_, hp⟩
  have hlen := hd.source_length
  simpa using hlen

end RuntimePolicyPrefix

namespace PolicyPrefix

/-- A cursor consumes exactly one source argument per policy position. -/
theorem source_length {S T : Type} {R : S → T → Prop} {ghost : T}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy}
    (h : PolicyPrefix R ghost policies sargs targs rest) :
    sargs.length + rest.length = policies.length := by
  induction h <;> simp_all <;> omega

/-- The target side has one slot for every consumed `keep` or `ghost`, and
no slot for a consumed `drop`. -/
theorem target_length {S T : Type} {R : S → T → Prop} {ghost : T}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy}
    (h : PolicyPrefix R ghost policies sargs targs rest) :
    targs.length + policyTargetArity rest = policyTargetArity policies := by
  induction h <;> simp_all [policyTargetArity] <;> omega

/-- Advance a cursor through a `keep` position, appending the newly
consumed arguments in application order. -/
theorem append_keep {S T : Type} {R : S → T → Prop} {ghost : T}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy} {sarg : S} {targ : T}
    (h : PolicyPrefix R ghost policies sargs targs (.keep :: rest))
    (hr : R sarg targ) :
    PolicyPrefix R ghost policies (sargs ++ [sarg]) (targs ++ [targ])
      rest := by
  generalize hrem : (.keep :: rest) = remaining at h
  induction h with
  | stop =>
    cases hrem
    exact .keep hr (.stop rest)
  | keep hhead _ ih =>
    simpa only [List.cons_append] using PolicyPrefix.keep hhead (ih hrem)
  | ghost _ ih =>
    simpa only [List.cons_append] using PolicyPrefix.ghost (ih hrem)
  | drop _ ih =>
    simpa only [List.cons_append] using PolicyPrefix.drop (ih hrem)

/-- Advance a cursor through a `ghost` position. -/
theorem append_ghost {S T : Type} {R : S → T → Prop} {ghost : T}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy} {sarg : S}
    (h : PolicyPrefix R ghost policies sargs targs (.ghost :: rest)) :
    PolicyPrefix R ghost policies (sargs ++ [sarg]) (targs ++ [ghost])
      rest := by
  generalize hrem : (.ghost :: rest) = remaining at h
  induction h with
  | stop =>
    cases hrem
    exact .ghost (.stop rest)
  | keep hhead _ ih =>
    simpa only [List.cons_append] using PolicyPrefix.keep hhead (ih hrem)
  | ghost _ ih =>
    simpa only [List.cons_append] using PolicyPrefix.ghost (ih hrem)
  | drop _ ih =>
    simpa only [List.cons_append] using PolicyPrefix.drop (ih hrem)

/-- Advance a cursor through a `drop` position. -/
theorem append_drop {S T : Type} {R : S → T → Prop} {ghost : T}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy} {sarg : S}
    (h : PolicyPrefix R ghost policies sargs targs (.drop :: rest)) :
    PolicyPrefix R ghost policies (sargs ++ [sarg]) targs rest := by
  generalize hrem : (.drop :: rest) = remaining at h
  induction h with
  | stop =>
    cases hrem
    exact .drop (.stop rest)
  | keep hhead _ ih =>
    simpa only [List.cons_append] using PolicyPrefix.keep hhead (ih hrem)
  | ghost _ ih =>
    simpa only [List.cons_append] using PolicyPrefix.ghost (ih hrem)
  | drop _ ih =>
    simpa only [List.cons_append] using PolicyPrefix.drop (ih hrem)

/-- A full policy relation consumes every source position. -/
theorem source_length_eq {S T : Type} {R : S → T → Prop} {ghost : T}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    (h : PolicyRel R ghost policies sargs targs) :
    sargs.length = policies.length := by
  simpa using h.source_length

/-- A full policy relation emits precisely the policy's target arity. -/
theorem target_length_eq {S T : Type} {R : S → T → Prop} {ghost : T}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    (h : PolicyRel R ghost policies sargs targs) :
    targs.length = policyTargetArity policies := by
  simpa [policyTargetArity] using h.target_length

/-- The cursor cannot have consumed more source arguments than there are
policy positions. -/
theorem source_length_le {S T : Type} {R : S → T → Prop} {ghost : T}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy}
    (h : PolicyPrefix R ghost policies sargs targs rest) :
    sargs.length ≤ policies.length := by
  have := h.source_length
  omega

/-- The cursor cannot have emitted more target arguments than the full
policy emits. -/
theorem target_length_le {S T : Type} {R : S → T → Prop} {ghost : T}
    {policies : List ArgPolicy} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy}
    (h : PolicyPrefix R ghost policies sargs targs rest) :
    targs.length ≤ policyTargetArity policies := by
  have := h.target_length
  omega

/-- A full all-`keep` policy is exactly pointwise list relatedness. -/
theorem listRel_of_full_keep {S T : Type} {R : S → T → Prop}
    {ghost : T} {n : Nat} {sargs : List S} {targs : List T}
    (h : PolicyRel R ghost (List.replicate n .keep) sargs targs) :
    ListRel R sargs targs := by
  induction n generalizing sargs targs with
  | zero =>
    cases h
    exact .nil
  | succ n ih =>
    simp only [List.replicate_succ] at h
    cases h with
    | keep hr hrest => exact .cons hr (ih hrest)

/-- After a constructor's dropped parameter segment, its source fields and
target fields are pointwise related. -/
theorem ctor_fields {S T : Type} {R : S → T → Prop}
    {ghost : T} {params fields : Nat} {sargs : List S} {targs : List T}
    (h : PolicyRel R ghost (ctorPolicy params fields) sargs targs) :
    ListRel R (sargs.drop params) targs := by
  induction params generalizing sargs targs with
  | zero =>
    simpa [ctorPolicy] using
      (listRel_of_full_keep (n := fields) h)
  | succ params ih =>
    simp only [ctorPolicy, List.replicate_succ, List.cons_append] at h
    cases h with
    | drop hrest =>
      simpa [ctorPolicy] using ih hrest

/-- Every consumed position of an all-`keep` cursor is pointwise related,
even when the cursor is not yet saturated. -/
theorem listRel_of_replicate_keep {S T : Type} {R : S → T → Prop}
    {ghost : T} {n : Nat} {sargs : List S} {targs : List T}
    {rest : List ArgPolicy}
    (h : PolicyPrefix R ghost (List.replicate n .keep) sargs targs rest) :
    ListRel R sargs targs := by
  induction n generalizing sargs targs rest with
  | zero =>
    cases h
    exact .nil
  | succ n ih =>
    simp only [List.replicate_succ] at h
    cases h with
    | stop => exact .nil
    | keep hhead htail => exact .cons hhead (ih htail)

/-- Construct the canonical cursor for a pointwise-related prefix of an
all-`keep` policy. -/
theorem replicate_keep_of_listRel {S T : Type} {R : S → T → Prop}
    {ghost : T} {n : Nat} {sargs : List S} {targs : List T}
    (h : ListRel R sargs targs) (hle : sargs.length ≤ n) :
    PolicyPrefix R ghost (List.replicate n .keep) sargs targs
      (List.replicate (n - sargs.length) .keep) := by
  induction h generalizing n with
  | nil =>
    simpa using (PolicyPrefix.stop (R := R) (ghost := ghost)
      (List.replicate n .keep))
  | cons hhead htail ih =>
    cases n with
    | zero => simp at hle
    | succ n =>
      have htail' := ih (n := n) (by simpa using hle)
      simpa [List.replicate_succ] using PolicyPrefix.keep hhead htail'

/-- Build the canonical constructor cursor from its unconstrained source
parameter prefix and the relation on fields consumed so far. Once all
parameters have been consumed, the remaining cursor contains only `keep`
positions. -/
theorem ctor_of_fields {S T : Type} {R : S → T → Prop} {ghost : T}
    {params fields : Nat} {sargs : List S} {targs : List T}
    (hparams : params ≤ sargs.length)
    (harity : sargs.length ≤ params + fields)
    (hfields : ListRel R (sargs.drop params) targs) :
    PolicyPrefix R ghost (ctorPolicy params fields) sargs targs
      (List.replicate (params + fields - sargs.length) .keep) := by
  induction params generalizing sargs targs with
  | zero =>
    simpa [ctorPolicy] using
      (replicate_keep_of_listRel (n := fields) hfields (by simpa using harity))
  | succ params ih =>
    cases sargs with
    | nil => simp at hparams
    | cons sarg sargs =>
      have hparams' : params ≤ sargs.length := by simpa using hparams
      have harity' : sargs.length ≤ params + fields := by
        simp only [List.length_cons] at harity
        omega
      have htail := ih hparams' harity' (by simpa using hfields)
      have hsuffix : params + 1 + fields - (sargs.length + 1) =
          params + fields - sargs.length := by omega
      simpa [ctorPolicy, List.replicate_succ, hsuffix] using
        (PolicyPrefix.drop (sarg := sarg) htail)

end PolicyPrefix

@[simp] theorem policyTargetArity_replicate_keep (n : Nat) :
    policyTargetArity (List.replicate n .keep) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, policyTargetArity, ih]

@[simp] theorem policyTargetArity_replicate_ghost (n : Nat) :
    policyTargetArity (List.replicate n .ghost) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, policyTargetArity, ih]

@[simp] theorem policyTargetArity_append (left right : List ArgPolicy) :
    policyTargetArity (left ++ right) =
      policyTargetArity left + policyTargetArity right := by
  induction left with
  | nil => simp [policyTargetArity]
  | cons policy rest ih =>
    cases policy <;> simp [policyTargetArity, ih, Nat.add_comm,
      Nat.add_left_comm]

@[simp] theorem policyTargetArity_ctorPolicy (params fields : Nat) :
    policyTargetArity (ctorPolicy params fields) = fields := by
  simp [ctorPolicy]

/-! Small elaborated witnesses pin the cursor orientation and each policy
transition. -/

example : PolicyRel (fun x y : Nat => x = y) 0
    [.drop, .ghost, .keep] [10, 20, 30] [0, 30] :=
  .drop (.ghost (.keep rfl (.stop [])))

example : PolicyPrefix (fun x y : Nat => x = y) 0
    [.drop, .ghost, .keep] [10] [] [.ghost, .keep] :=
  .drop (.stop [.ghost, .keep])

example : PolicyPrefix (fun x y : Nat => x = y) 0
    [.drop, .ghost, .keep] [10, 20] [0] [.keep] := by
  exact PolicyPrefix.append_ghost (.drop (.stop [.ghost, .keep]))

end Ix.Compiler.Sim
