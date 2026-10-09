import Ix.CompileCert.Canon.ExpansionInitialize

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

/-- A successful structural lookup returns an actual specification entry. -/
theorem occurrenceLookup_some_mem {entries : List (OccurrenceKey × Name)}
    {key : OccurrenceKey} {value : Name}
    (found : occurrenceLookup entries key = some value) : (key,value) ∈ entries := by
  induction entries with
  | nil => cases found
  | cons pair rest ih =>
    obtain ⟨stored,target⟩ := pair
    simp only [occurrenceLookup] at found
    split at found
    · rename_i equal
      cases found
      subst stored
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih found)

/-- Range invariant over the structural table, independent of cache hints. -/
def OccurrenceRange (P : Name → Prop) (table : OccurrenceTable) : Prop :=
  ∀ key value, (key,value) ∈ table.entries → P value

theorem OccurrenceRange.empty (P : Name → Prop) : OccurrenceRange P {} := by
  change ∀ key value, (key,value) ∈ ([] : List (OccurrenceKey × Name)) → P value
  simp

theorem OccurrenceRange.mono {P Q : Name → Prop} {table : OccurrenceTable}
    (range : OccurrenceRange P table) (included : ∀ name, P name → Q name) :
    OccurrenceRange Q table := fun key value member => included value (range key value member)

theorem OccurrenceRange.get {P : Name → Prop} {table : OccurrenceTable}
    (range : OccurrenceRange P table) {input : OccurrenceInput} {value : Name}
    (found : table.get? input = some value) : P value :=
  range input.key value (occurrenceLookup_some_mem found)

theorem OccurrenceRange.insert {P : Name → Prop} {table : OccurrenceTable}
    (range : OccurrenceRange P table) (input : OccurrenceInput) (value : Name)
    (known : P value) : OccurrenceRange P (table.insert input value) := by
  unfold OccurrenceTable.insert
  split
  · intro key target member
    rcases List.mem_cons.mp member with equal | old
    · cases equal
      exact known
    · exact range key target old
  · exact range

/-- The reference invariant additionally records that every cached nested
replacement names an actual queued member. Both parts start from real data. -/
def ExpansionReferenceInvariant (cx : XCtx) (st : XSt) : Prop :=
  (∀ member ∈ st.types, MemberScope (RunKnown cx st) member) ∧
  (st.sourceNames? = none ∨ st.sourceNames? =
    some (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames) ∧
  OccurrenceRange (fun name => st.typeNames.contains name = true) st.seen

theorem ExpansionReferenceInvariant.scope {cx : XCtx} {st : XSt}
    (invariant : ExpansionReferenceInvariant cx st) : ExpansionScope cx st :=
  ⟨invariant.1,invariant.2.1⟩

theorem ExpansionReferenceInvariant.seen {cx : XCtx} {st : XSt}
    (invariant : ExpansionReferenceInvariant cx st) :
    OccurrenceRange (fun name => st.typeNames.contains name = true) st.seen := invariant.2.2

theorem ExpansionReferenceInvariant.empty (cx : XCtx) :
    ExpansionReferenceInvariant cx {} :=
  ⟨by simp,Or.inl rfl,OccurrenceRange.empty _⟩

theorem ExpansionReferenceInvariant.push {cx : XCtx} {st : XSt}
    (invariant : ExpansionReferenceInvariant cx st) (member : XMember)
    (memberScope : MemberScope (RunKnown cx (st.push member)) member) :
    ExpansionReferenceInvariant cx (st.push member) := by
  have scopeProof := invariant.scope.push member memberScope
  refine ⟨scopeProof.members,scopeProof.sourceCache,?_⟩
  exact invariant.seen.mono (fun name known =>
      NameTable.contains_insert_mono st.typeNames member.name name () known)

/-- A successful real original-member initializer has made no nested cache
insertion, including when a source lookup spelling aliases another record. -/
theorem initialMembers_seen {cx : XCtx} (ordered : Array Name)
    (aliases : Std.HashMap Name Name) {st : XSt}
    (run : initialMembers cx ordered aliases = .ok st) : st.seen.entries = [] := by
  unfold initialMembers at run
  apply forIn_except_array_mem _ (fun _ state => state.seen.entries = []) ordered ?_ rfl run
  intro pre name before step member invariant result
  split at result
  · cases except_pure_ok result
    exact ⟨_,rfl,invariant⟩
  · cases result

/-- The additional cache-range component is derived from the actual loop;
it is not a premise added to the public expansion statement. -/
theorem initialize_referenceInvariant {cx : XCtx}
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (ordered : Array Name) (members : ∀ n ∈ ordered, RunReach cx n)
    (aliases : Std.HashMap Name Name)
    (range : ∀ query value, aliases.get? query = some value → RunReach cx value)
    {st : XSt} (run : initialMembers cx ordered aliases = .ok st) :
    ExpansionReferenceInvariant cx st := by
  have scopeProof := initialize_scope lookup ordered members aliases range run
  refine ⟨scopeProof.members,scopeProof.sourceCache,?_⟩
  intro key value member
  rw [initialMembers_seen ordered aliases run] at member
  cases member

end Ix.CompileCert.Canon
namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

abbrev SeenRange (st : XSt) : Prop :=
  OccurrenceRange (fun name => st.typeNames.contains name = true) st.seen

theorem SeenRange.push {st : XSt} (member : XMember)
    (range : OccurrenceRange
      (fun name => (st.typeNames.insert member.name ()).contains name = true) st.seen) :
    SeenRange (st.push member) := range

/-- During discovery the alias cache may already name the pending auxiliary.
The actual transition pushes that member before returning, restoring its range
in the real queue. This covers every query/error/dedup/group branch. -/
theorem replaceIfNested_seenRange (cx : XCtx) (np : Nat) (owner : Name)
    (e : Expr) (depth : Nat) (st : XSt) (range : SeenRange st) :
    SeenRange (replaceIfNested cx np owner e depth st).2 := by
  unfold replaceIfNested
  dsimp only [Id.run]
  repeat' (first | exact range | split)
  all_goals
    show SeenRange
      (forIn (m := Id) (β := XSt × Option Expr) (_ : Array (Array Name)) _ _).1
    refine forIn_id_inv_array (fun r : XSt × Option Expr => SeenRange r.1)
      _ ?_ _ _ range
    intro cls r hr
    try dsimp only
    split
    · split
      · simp only [id_bind_eq]
        repeat' split
        all_goals
          apply SeenRange.push
          refine forIn_id_inv_array (fun q : XSt × Array XCtor =>
            OccurrenceRange (fun name => (q.1.typeNames.insert _ ()).contains name = true) q.1.seen)
            _ ?_ _ _ ?_
          · intro x q hq
            obtain ⟨cn,ct,nf⟩ := x
            exact hq
          · first
            | exact hr.mono (fun name known => NameTable.contains_insert_mono _ _ _ () known)
            | exact (hr.mono (fun name known => NameTable.contains_insert_mono _ _ _ () known)).insert
                _ _ (NameTable.contains_insert_self _ _ ())
            | (refine array_foldl_inv (fun q : XSt =>
                OccurrenceRange (fun name => (q.typeNames.insert _ ()).contains name = true) q.seen)
                _ ?_ _ _ ?_
               · intro q k hq
                 try dsimp only
                 repeat' (first
                   | exact hq
                   | exact hq.insert _ _ (NameTable.contains_insert_self _ _ ())
                   | split)
               · exact hr.mono (fun name known => NameTable.contains_insert_mono _ _ _ () known))
      · exact hr
    · exact hr

end Ix.CompileCert.Canon
namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

theorem replaceAll_seenRange (cx : XCtx) (np : Nat) (owner : Name) :
    ∀ (e : Expr) (d : Nat) (st : XSt) (_range : SeenRange st), SeenRange (replaceAll cx np owner e d st).2 := by
  intro e
  induction e with
  | app f a h ihf iha =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.app f a h) d st range
    revert hR
    cases replaceIfNested cx np owner (.app f a h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihf d st1 hR
        revert h1
        cases replaceAll cx np owner f d st1 with
        | mk f' st2 =>
          intro h1
          have h2 := iha d st2 h1
          revert h2
          cases replaceAll cx np owner a d st2 with
          | mk a' st3 => intro h2; exact h2
  | lam n t b bi h iht ihb =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.lam n t b bi h) d st range
    revert hR
    cases replaceIfNested cx np owner (.lam n t b bi h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1 hR
        revert h1
        cases replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihb (d + 1) st2 h1
          revert h2
          cases replaceAll cx np owner b (d + 1) st2 with
          | mk b' st3 => intro h2; exact h2
  | forallE n t b bi h iht ihb =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.forallE n t b bi h) d st range
    revert hR
    cases replaceIfNested cx np owner (.forallE n t b bi h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1 hR
        revert h1
        cases replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihb (d + 1) st2 h1
          revert h2
          cases replaceAll cx np owner b (d + 1) st2 with
          | mk b' st3 => intro h2; exact h2
  | letE n t v b nd h iht ihv ihb =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.letE n t v b nd h) d st range
    revert hR
    cases replaceIfNested cx np owner (.letE n t v b nd h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := iht d st1 hR
        revert h1
        cases replaceAll cx np owner t d st1 with
        | mk t' st2 =>
          intro h1
          have h2 := ihv d st2 h1
          revert h2
          cases replaceAll cx np owner v d st2 with
          | mk v' st3 =>
            intro h2
            have h3 := ihb (d + 1) st3 h2
            revert h3
            cases replaceAll cx np owner b (d + 1) st3 with
            | mk b' st4 => intro h3; exact h3
  | proj n i s h ihs =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.proj n i s h) d st range
    revert hR
    cases replaceIfNested cx np owner (.proj n i s h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihs d st1 hR
        revert h1
        cases replaceAll cx np owner s d st1 with
        | mk s' st2 => intro h1; exact h1
  | mdata md x h ihx =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.mdata md x h) d st range
    revert hR
    cases replaceIfNested cx np owner (.mdata md x h) d st with
    | mk o st1 =>
      intro hR
      cases o with
      | some r => exact hR
      | none =>
        dsimp only
        have h1 := ihx d st1 hR
        revert h1
        cases replaceAll cx np owner x d st1 with
        | mk x' st2 => intro h1; exact h1
  | bvar i h =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.bvar i h) d st range
    revert hR
    cases replaceIfNested cx np owner (.bvar i h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | fvar n h =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.fvar n h) d st range
    revert hR
    cases replaceIfNested cx np owner (.fvar n h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | mvar n h =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.mvar n h) d st range
    revert hR
    cases replaceIfNested cx np owner (.mvar n h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | sort u h =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.sort u h) d st range
    revert hR
    cases replaceIfNested cx np owner (.sort u h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | const n us h =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.const n us h) d st range
    revert hR
    cases replaceIfNested cx np owner (.const n us h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR
  | lit l h =>
    intro d st range
    rw [replaceAll.eq_1]
    have hR := replaceIfNested_seenRange cx np owner (.lit l h) d st range
    revert hR
    cases replaceIfNested cx np owner (.lit l h) d st with
    | mk o st1 => intro hR; cases o <;> exact hR


end Ix.CompileCert.Canon
namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

theorem walkCtor_seenRange (cx : XCtx) (qi ci : Nat) (st : XSt)
    (range : SeenRange st) : SeenRange (walkCtor cx qi ci st) := by
  unfold walkCtor
  split
  · exact range
  · rename_i member found
    split
    · exact range
    · rename_i ctor foundCtor
      exact replaceAll_seenRange cx (peelForalls cx.nParams ctor.typ #[]).1.size
        member.sourceOwner (peelForalls cx.nParams ctor.typ #[]).2 0 st range

/-- A successful real queue never returns a dangling cached auxiliary.
The claim includes both dedup modes and every initial error state. -/
theorem walkQueue_seenRange (cx : XCtx) : ∀ (fuel qi : Nat) (st fin : XSt),
    SeenRange st → walkQueue cx fuel qi st = .ok fin → SeenRange fin
  | 0,qi,st,fin,range,run => by
    rw [walkQueue.eq_1] at run
    split at run
    · cases run
    · split at run
      · cases run
      · cases except_pure_ok run
        exact range
  | fuel+1,qi,st,fin,range,run => by
    rw [walkQueue.eq_2] at run
    split at run
    · cases run
    · split at run
      · cases except_pure_ok run
        exact range
      · rename_i member found
        have step : SeenRange
            ((List.range member.ctors.size).foldl (fun s ci => walkCtor cx qi ci s) st) := by
          refine list_foldl_inv SeenRange _ ?_ _ _ range
          intro s ci current
          exact walkCtor_seenRange cx qi ci s current
        exact walkQueue_seenRange cx fuel (qi+1) _ fin step run

/-- The real original-member initializer discharges the queue's seen-range
invariant. No key/hash/name/source completeness premise is introduced. -/
theorem initializedQueue_seenRange (cx : XCtx) (ordered : Array Name)
    (aliases : Std.HashMap Name Name) (fuel qi : Nat) {initial final : XSt}
    (start : initialMembers cx ordered aliases = .ok initial)
    (run : walkQueue cx fuel qi initial = .ok final) : SeenRange final := by
  apply walkQueue_seenRange cx fuel qi initial final ?_ run
  intro key value member
  rw [initialMembers_seen ordered aliases start] at member
  cases member

end Ix.CompileCert.Canon

