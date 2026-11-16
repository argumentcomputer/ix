import IxC.Kernel.Ixon.Shape

/-! # Reference support of symbolic reader shapes -/

namespace Ix.Kernel.Reader.Shape

def RawRefs (P : Nat → Prop) : Ixon.Expr → Prop
  | .ref i _ => P i.toNat
  | .prj i _ value => P i.toNat ∧ RawRefs P value
  | .app fn arg | .lam fn arg | .all fn arg => RawRefs P fn ∧ RawRefs P arg
  | .letE _ _ type value body => RawRefs P type ∧ RawRefs P value ∧ RawRefs P body
  | _ => True

def KeyRefs (P : Nat → Prop) : Key .source → Prop
  | .id (.num (.num .anonymous 0) i) => P i
  | _ => True

def Refs (P : Nat → Prop) : Term → Prop
  | .const key _ => KeyRefs P key
  | .app fn arg => Refs P fn ∧ Refs P arg
  | .lam type body _ | .forallE type body _ => Refs P type ∧ Refs P body
  | .letE type value body _ => Refs P type ∧ Refs P value ∧ Refs P body
  | .proj key _ value => KeyRefs P key ∧ Refs P value
  | _ => True

theorem refs_lift {P : Nat → Prop} (amount : Nat) :
    ∀ (expression : Term) (cutoff : Nat), Refs P expression →
      Refs P (expression.liftLooseBVars amount cutoff)
  | .bvar _, cutoff, _ => by rw [Expr.liftLooseBVars]; split <;> trivial
  | .fvar .., _, _ | .sort _, _, _ | .lit _, _, _ => trivial
  | .const .., _, supported => supported
  | .app fn arg, cutoff, ⟨hf, ha⟩ =>
    ⟨refs_lift amount fn cutoff hf, refs_lift amount arg cutoff ha⟩
  | .lam type body _, cutoff, ⟨ht, hb⟩ =>
    ⟨refs_lift amount type cutoff ht, refs_lift amount body (cutoff + 1) hb⟩
  | .forallE type body _, cutoff, ⟨ht, hb⟩ =>
    ⟨refs_lift amount type cutoff ht, refs_lift amount body (cutoff + 1) hb⟩
  | .letE type value body _, cutoff, ⟨ht, hv, hb⟩ =>
    ⟨refs_lift amount type cutoff ht, refs_lift amount value cutoff hv,
      refs_lift amount body (cutoff + 1) hb⟩
  | .proj _ _ value, cutoff, ⟨hk, hv⟩ => ⟨hk, refs_lift amount value cutoff hv⟩

theorem refs_subst {P : Nat → Prop} {value : Term} (hv : Refs P value) :
    ∀ (expression : Term) (depth : Nat), Refs P expression →
      Refs P (expression.instantiate1Lift value depth)
  | .bvar _, depth, _ => by
    rw [Expr.instantiate1Lift]
    split
    · exact refs_lift depth value 0 hv
    · split <;> trivial
  | .fvar .., _, _ | .sort _, _, _ | .lit _, _, _ => trivial
  | .const .., _, supported => supported
  | .app fn arg, depth, ⟨hf, ha⟩ =>
    ⟨refs_subst hv fn depth hf, refs_subst hv arg depth ha⟩
  | .lam type body _, depth, ⟨ht, hb⟩ =>
    ⟨refs_subst hv type depth ht, refs_subst hv body (depth + 1) hb⟩
  | .forallE type body _, depth, ⟨ht, hb⟩ =>
    ⟨refs_subst hv type depth ht, refs_subst hv body (depth + 1) hb⟩
  | .letE type val body _, depth, ⟨ht, hval, hb⟩ =>
    ⟨refs_subst hv type depth ht, refs_subst hv val depth hval,
      refs_subst hv body (depth + 1) hb⟩
  | .proj _ _ sub, depth, ⟨hk, hs⟩ => ⟨hk, refs_subst hv sub depth hs⟩

def TableRefs (P : Nat → Prop) (table : Array (Option Term)) : Prop :=
  ∀ (i : Nat) (value : Term), table[i]? = some (some value) → Refs P value

theorem convert_refs {P : Nat → Prop} {table : Array (Option Term)}
    (entries : TableRefs P table) :
    ∀ {raw : Ixon.Expr} {value : Term}, RawRefs P raw →
      convert table raw = some value → Refs P value := by
  intro raw
  induction raw with
  | var i | sort i | nat i | str i =>
    intro value _ ran
    cases ran
    trivial
  | ref i us =>
    intro value supported ran
    cases ran
    exact supported
  | recur i us =>
    intro value _ ran
    cases ran
    trivial
  | prj i field sub ih =>
    intro value supported ran
    simp only [convert, bind, Option.bind_eq_some_iff, pure] at ran
    obtain ⟨subValue, subRead, returned⟩ := ran
    cases Option.some.inj returned
    exact ⟨supported.1, ih supported.2 subRead⟩
  | app fn arg ihf iha | lam fn arg ihf iha | all fn arg ihf iha =>
    intro value supported ran
    simp only [convert, bind, Option.bind_eq_some_iff, pure] at ran
    obtain ⟨fnValue, fnRead, argValue, argRead, returned⟩ := ran
    cases Option.some.inj returned
    exact ⟨ihf supported.1 fnRead, iha supported.2 argRead⟩
  | letE nonDep mode type val body _ ihv ihb =>
    intro value supported ran
    simp only [convert, bind, Option.bind_eq_some_iff, pure] at ran
    obtain ⟨bodyValue, bodyRead, valValue, valRead, returned⟩ := ran
    cases Option.some.inj returned
    exact refs_subst (ihv supported.2.1 valRead) _ 0 (ihb supported.2.2 bodyRead)
  | share i =>
    intro value _ ran
    change (table[i.toNat]? >>= id) = some value at ran
    obtain ⟨entry, found, returned⟩ := Option.bind_eq_some_iff.mp ran
    change entry = some value at returned
    rw [returned] at found
    exact entries _ _ found

theorem TableRefs.push {P : Nat → Prop} {table : Array (Option Term)}
    (entries : TableRefs P table) {entry : Option Term}
    (supported : ∀ value, entry = some value → Refs P value) :
    TableRefs P (table.push entry) := by
  intro i value found
  rw [Array.getElem?_push] at found
  by_cases last : i = table.size
  · simp only [last, ↓reduceIte, Option.some.injEq] at found
    exact supported _ found
  · simp only [last, ↓reduceIte] at found
    exact entries _ _ found

theorem fold_refs {P : Nat → Prop} (raw : List Ixon.Expr)
    (supported : ∀ expression ∈ raw, RawRefs P expression)
    {table : Array (Option Term)} (entries : TableRefs P table) :
    TableRefs P (raw.foldl (fun table entry => table.push (convert table entry)) table) := by
  induction raw generalizing table with
  | nil => exact entries
  | cons first rest ih =>
    apply ih (fun expression present => supported expression (List.mem_cons_of_mem _ present))
    exact entries.push (fun value ran => convert_refs entries (supported first List.mem_cons_self) ran)

theorem sharing_refs {P : Nat → Prop} {entries : Array Ixon.Expr}
    (supported : ∀ expression ∈ entries, RawRefs P expression) :
    TableRefs P (sharing entries) := by
  rw [sharing, ← Array.foldl_toList]
  exact fold_refs entries.toList (fun expression present =>
    supported expression (Array.mem_toList_iff.mp present)) (fun i value found => by simp at found)

theorem read_refs {P : Nat → Prop} {constant : Ixon.Constant}
    (shared : ∀ expression ∈ constant.sharing, RawRefs P expression)
    {raw : Ixon.Expr} {value : Term} (supported : RawRefs P raw)
    (ran : read constant raw = some value) : Refs P value :=
  convert_refs (sharing_refs shared) supported ran

theorem appHead_refs {P : Nat → Prop} (fuel : Nat) {expression : Term}
    (supported : Refs P expression) : Refs P (appHead fuel expression) := by
  induction fuel generalizing expression with
  | zero => exact supported
  | succ fuel ih =>
    cases expression with
    | app fn arg => exact ih supported.1
    | _ => exact supported

theorem stripAll_refs {P : Nat → Prop} (count : Nat) {expression : Term}
    (supported : Refs P expression) {domains : List Term} {body : Term}
    (ran : stripAll count expression = some (domains, body)) :
    (∀ domain ∈ domains, Refs P domain) ∧ Refs P body := by
  induction count generalizing expression domains body with
  | zero =>
    cases ran
    exact ⟨by simp, supported⟩
  | succ count ih =>
    cases expression with
    | forallE type tail metadata =>
      simp only [stripAll, bind, Option.bind_eq_some_iff, pure] at ran
      obtain ⟨⟨rest, result⟩, restRead, returned⟩ := ran
      cases Option.some.inj returned
      obtain ⟨restSupport, resultSupport⟩ := ih supported.2 restRead
      exact ⟨fun domain present => (List.mem_cons.mp present).elim
        (fun same => by subst domain; exact supported.1) (restSupport domain), resultSupport⟩
    | _ => cases ran

theorem stripAllFull_refs {P : Nat → Prop} (fuel : Nat) {expression : Term}
    (supported : Refs P expression) :
    (∀ domain ∈ (stripAllFull fuel expression).1, Refs P domain) ∧
      Refs P (stripAllFull fuel expression).2 := by
  induction fuel generalizing expression with
  | zero => exact ⟨by simp [stripAllFull], supported⟩
  | succ fuel ih =>
    cases expression with
    | forallE type body metadata =>
      obtain ⟨bodySupport, resultSupport⟩ := ih supported.2
      exact ⟨fun domain present => (List.mem_cons.mp present).elim
        (fun same => by subst domain; exact supported.1) (bodySupport domain), resultSupport⟩
    | _ => exact ⟨by simp [stripAllFull], supported⟩

def Head.Refs (P : Nat → Prop) : Head → Prop
  | .ref i => P i
  | .recur _ => True

theorem head_refs {P : Nat → Prop} {fuel : Nat} {expression : Term}
    (supported : Refs P expression) {result : Head}
    (ran : head fuel expression = some result) : result.Refs P := by
  have headSupport := appHead_refs fuel supported
  unfold head at ran
  split at ran
  · cases ran
    simp_all only [Refs, KeyRefs, Head.Refs]
  · cases ran
    trivial
  · cases ran

private theorem mapM_all {α β : Type} {f : α → Option β} {Q : β → Prop} :
    ∀ (inputs : List α) (outputs : List β),
      (∀ input ∈ inputs, ∀ output, f input = some output → Q output) →
      inputs.mapM f = some outputs → ∀ output ∈ outputs, Q output
  | [], outputs, _, ran => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at ran
    subst outputs
    simp
  | input :: rest, outputs, step, ran => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at ran
    obtain ⟨output, first, tail, later, rfl⟩ := ran
    have firstQ := step input List.mem_cons_self output first
    have tailQ := mapM_all rest tail
      (fun item present => step item (List.mem_cons_of_mem _ present)) later
    intro item present
    exact (List.mem_cons.mp present).elim (fun same => by subst item; exact firstQ) (tailQ item)

theorem telescope_refs {P : Nat → Prop} {constant : Ixon.Constant} {recursor : Ixon.Recursor}
    (shared : ∀ raw ∈ constant.sharing, RawRefs P raw) (typeRefs : RawRefs P recursor.typ)
    {fuel motive : Nat} {domains : List Term}
    (ran : telescope fuel constant recursor = some (motive, domains)) :
    ∀ domain ∈ domains, Refs P domain := by
  unfold telescope at ran
  simp only [bind, Option.bind_eq_some_iff, pure] at ran
  obtain ⟨term, converted, ⟨types, body⟩, parsed, ran⟩ := ran
  have domainsRef := (stripAll_refs _ (read_refs shared typeRefs converted) parsed).1
  split at ran
  · simp only [Option.bind_eq_some_iff] at ran
    obtain ⟨u, _, returned⟩ := ran
    cases Option.some.inj returned
    exact domainsRef
  · cases ran

theorem telescope_motive_lt {constant : Ixon.Constant} {recursor : Ixon.Recursor}
    {fuel motive : Nat} {domains : List Term}
    (ran : telescope fuel constant recursor = some (motive, domains)) :
    motive < recursor.motives.toNat := by
  unfold telescope at ran
  simp only [bind, Option.bind_eq_some_iff, pure] at ran
  obtain ⟨term, _, ⟨types, body⟩, _, ran⟩ := ran
  split at ran
  · simp only [Option.bind_eq_some_iff] at ran
    obtain ⟨u, valid, returned⟩ := ran
    cases Option.some.inj returned
    unfold guard at valid
    split at valid
    · rename_i condition
      simp only [Bool.and_eq_true, decide_eq_true_eq] at condition
      omega
    · cases valid
  · cases ran

/-- Every carrier queried by the general shape analysis is drawn from the raw
type's and sharing table's reference support, including let-bound values. -/
theorem analyse_refs {P : Nat → Prop} {constant : Ixon.Constant} {recursor : Ixon.Recursor}
    (shared : ∀ raw ∈ constant.sharing, RawRefs P raw) (typeRefs : RawRefs P recursor.typ)
    {fuel : Nat} {result : Nat × Array Head × Head}
    (ran : analyse fuel constant recursor = some result) :
    (∀ carrier ∈ result.2.1, carrier.Refs P) ∧ result.2.2.Refs P := by
  unfold analyse at ran
  simp only [bind, Option.bind_eq_some_iff, pure] at ran
  obtain ⟨⟨motive, domains⟩, parsed, carriers, carrierRead, last, lastFound, major,
    majorRead, returned⟩ := ran
  cases Option.some.inj returned
  have domainsRef := telescope_refs shared typeRefs parsed
  rw [Array.mapM_eq_mapM_toList, List.toList_toArray, Option.map_eq_map,
    Option.map_eq_some_iff] at carrierRead
  obtain ⟨entries, entriesRead, rfl⟩ := carrierRead
  have entriesRef := mapM_all _ entries (fun domain present carrier queried => by
    have domainRef := domainsRef domain
      (List.mem_of_mem_drop (List.mem_of_mem_take present))
    obtain ⟨last, lastFound, headRead⟩ := Option.bind_eq_some_iff.mp queried
    exact head_refs ((stripAllFull_refs fuel domainRef).1 last
      (List.mem_of_getLast? lastFound)) headRead) entriesRead
  exact ⟨fun carrier present => entriesRef carrier (by simpa using present),
    head_refs (domainsRef last (List.mem_of_getLast? lastFound)) majorRead⟩

theorem analyse_telescope {constant : Ixon.Constant} {recursor : Ixon.Recursor}
    {fuel motive : Nat} {carriers : Array Head} {major : Head}
    (ran : analyse fuel constant recursor = some (motive, carriers, major)) :
    ∃ domains, telescope fuel constant recursor = some (motive, domains) := by
  unfold analyse at ran
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at ran
  obtain ⟨⟨motive', domains⟩, parsed, carriers', _, last, _, major', _, rfl, rfl, rfl⟩ := ran
  exact ⟨domains, parsed⟩

theorem analyse_motive_lt {constant : Ixon.Constant} {recursor : Ixon.Recursor}
    {fuel motive : Nat} {carriers : Array Head} {major : Head}
    (ran : analyse fuel constant recursor = some (motive, carriers, major)) :
    motive < recursor.motives.toNat :=
  let ⟨_, parsed⟩ := analyse_telescope ran
  telescope_motive_lt parsed

end Ix.Kernel.Reader.Shape
