import Ix.CompileCert.RecursorSharing

/-! The certified reader's syntactic walks through sharing encodings.
These results connect the existing expansion meaning to the actual bounded
reader operations, before conversion to kernel expressions. -/

namespace Ix.CompileCert.ReaderSpines

open Ix Kernel.Reader
open Ix.Sharing.Verify.SharingExact

def Entries (constant : Ixon.Constant) (expand : Nat → Ixon.Expr) : Prop :=
  ∀ index, index < constant.sharing.size →
    expand index = substShares expand constant.sharing[index]! ∧
      SharesIn (fun slot => slot < index) constant.sharing[index]!

def InlineHead : Ixon.Expr → Prop
  | .share _ => False
  | _ => True

theorem shares_mono (P Q : Nat → Prop) (implies : ∀ index, P index → Q index)
    (expression : Ixon.Expr) (bounded : SharesIn P expression) : SharesIn Q expression := by
  induction expression with
  | share index => exact implies index.toNat bounded
  | prj _ _ _ ih => exact ih bounded
  | app _ _ ihf iha | lam _ _ _ ihf iha | all _ _ _ _ ihf iha => exact ⟨ihf bounded.1, iha bounded.2⟩
  | letE _ _ _ _ iht ihv ihb => exact ⟨iht bounded.1, ihv bounded.2.1, ihb bounded.2.2⟩
  | _ => trivial

/-- Backward table references make the reader's actual share-following bound
sufficient. The resulting head is inline and retains the same expansion. -/
theorem unshare_go (constant : Ixon.Constant) (expand : Nat → Ixon.Expr) (entries : Entries constant expand)
    (fuel limit : Nat) (within : limit ≤ constant.sharing.size) (enough : limit < fuel)
    (expression : Ixon.Expr) (bounded : SharesIn (fun slot => slot < limit) expression) :
    InlineHead (unshare.go constant fuel expression) ∧
      SharesIn (fun slot => slot < constant.sharing.size) (unshare.go constant fuel expression) ∧
      substShares expand (unshare.go constant fuel expression) = substShares expand expression := by
  induction fuel generalizing limit expression with
  | zero => omega
  | succ fuel ih =>
    cases expression with
    | share index =>
      have bound : index.toNat < limit := bounded
      have inside : index.toNat < constant.sharing.size := Nat.lt_of_lt_of_le bound within
      have row := entries index.toNat inside
      have stored : constant.sharing[index.toNat]? = some constant.sharing[index.toNat]! := by
        simp only [Array.getElem?_eq_getElem inside, getElem!_pos constant.sharing index.toNat inside]
      have walked := ih index.toNat (Nat.le_of_lt inside) (by omega) constant.sharing[index.toNat]! row.2
      simpa only [unshare.go, stored, substShares] using
        And.intro walked.1 (And.intro walked.2.1 (walked.2.2.trans row.1.symm))
    | _ => exact ⟨trivial, shares_mono _ _ (fun slot bound => Nat.lt_of_lt_of_le bound within) _ bounded, rfl⟩

theorem unshare_expansion (constant : Ixon.Constant) (expand : Nat → Ixon.Expr) (entries : Entries constant expand)
    (expression : Ixon.Expr) (bounded : SharesIn (fun slot => slot < constant.sharing.size) expression) :
    InlineHead (unshare constant expression) ∧
      SharesIn (fun slot => slot < constant.sharing.size) (unshare constant expression) ∧
      substShares expand (unshare constant expression) = substShares expand expression :=
  unshare_go constant expand entries (constant.sharing.size + 1) constant.sharing.size
    (Nat.le_refl _) (Nat.lt_succ_self _) expression bounded

theorem unshare_empty (constant : Ixon.Constant) (empty : constant.sharing = #[]) (expression : Ixon.Expr) :
    unshare constant expression = expression := by
  unfold unshare
  rw [empty]
  cases expression <;> simp [unshare.go, empty]

def expandTele (expand : Nat → Ixon.Expr) (telescope : List Ixon.Expr × Ixon.Expr) : List Ixon.Expr × Ixon.Expr :=
  (telescope.1.map (substShares expand), substShares expand telescope.2)

/-- Exact-length telescope analysis commutes with the proved sharing
expansion, including failure to find the requested number of binders. -/
theorem stripAll_expand (constant flat : Ixon.Constant) (empty : flat.sharing = #[])
    (expand : Nat → Ixon.Expr) (entries : Entries constant expand) (count : Nat)
    (expression : Ixon.Expr) (bounded : SharesIn (fun slot => slot < constant.sharing.size) expression) :
    (stripAll constant count expression).map (expandTele expand) =
      stripAll flat count (substShares expand expression) := by
  induction count generalizing expression with
  | zero => rfl
  | succ count ih =>
    have exposed := unshare_expansion constant expand entries expression bounded
    simp only [stripAll, unshare_empty flat empty, ← exposed.2.2]
    cases head : unshare constant expression with
    | share index => simp only [head, InlineHead, false_and] at exposed
    | all contract binder type body =>
      have bound : SharesIn (fun slot => slot < constant.sharing.size) body := by
        have pair := exposed.2.1
        rw [head] at pair
        exact pair.2
      have later := ih body bound
      cases ran : stripAll constant count body with
      | none => simp only [ran, Option.map_none] at later; simp [substShares, ran, ← later]
      | some value => simp only [ran, Option.map_some] at later; simp [substShares, ran, ← later, expandTele]
    | _ => rfl

def TeleBounded (constant : Ixon.Constant) (telescope : List Ixon.Expr × Ixon.Expr) : Prop :=
  (∀ type ∈ telescope.1, SharesIn (fun slot => slot < constant.sharing.size) type) ∧
    SharesIn (fun slot => slot < constant.sharing.size) telescope.2

theorem stripAll_bounded (constant : Ixon.Constant) (expand : Nat → Ixon.Expr)
    (entries : Entries constant expand) (count : Nat) (expression : Ixon.Expr)
    (bounded : SharesIn (fun slot => slot < constant.sharing.size) expression)
    (telescope : List Ixon.Expr × Ixon.Expr) (ran : stripAll constant count expression = some telescope) :
    TeleBounded constant telescope := by
  induction count generalizing expression telescope with
  | zero =>
    cases Option.some.inj ran
    exact ⟨by simp, bounded⟩
  | succ count ih =>
    have exposed := unshare_expansion constant expand entries expression bounded
    rw [stripAll] at ran
    cases head : unshare constant expression with
    | all contract binder type body =>
      have pair := exposed.2.1
      rw [head] at pair
      simp only [head] at ran
      cases tail : stripAll constant count body with
      | none => simp [tail] at ran
      | some result =>
        have same : (type :: result.1, result.2) = telescope := by simpa [tail] using ran
        subst telescope
        have rest := ih body pair.2 result tail
        exact ⟨fun type member => (List.mem_cons.mp member).elim (fun same => same ▸ pair.1)
          (fun member => rest.1 type member), rest.2⟩
    | _ => simp [head] at ran

/-- Fuel-bounded telescope analysis returns exactly the expanded domains
and residual expression, even at the fuel boundary. -/
theorem stripAllFull_expand (constant flat : Ixon.Constant) (empty : flat.sharing = #[])
    (expand : Nat → Ixon.Expr) (entries : Entries constant expand) (fuel : Nat)
    (expression : Ixon.Expr) (bounded : SharesIn (fun slot => slot < constant.sharing.size) expression) :
    expandTele expand (stripAllFull constant fuel expression) =
      stripAllFull flat fuel (substShares expand expression) := by
  induction fuel generalizing expression with
  | zero => rfl
  | succ fuel ih =>
    have exposed := unshare_expansion constant expand entries expression bounded
    simp only [stripAllFull, unshare_empty flat empty, ← exposed.2.2]
    cases head : unshare constant expression with
    | share index => simp only [head, InlineHead, false_and] at exposed
    | all contract binder type body =>
      have pair := exposed.2.1
      rw [head] at pair
      have rest := ih body pair.2
      have types : (stripAllFull constant fuel body).1.map (substShares expand) =
          (stripAllFull flat fuel (substShares expand body)).1 := congrArg Prod.fst rest
      have tail : substShares expand (stripAllFull constant fuel body).2 =
          (stripAllFull flat fuel (substShares expand body)).2 := congrArg Prod.snd rest
      have withHead := congrArg (substShares expand type :: ·) types
      exact Prod.ext withHead tail
    | _ => rfl

theorem stripAllFull_bounded (constant : Ixon.Constant) (expand : Nat → Ixon.Expr)
    (entries : Entries constant expand) (fuel : Nat) (expression : Ixon.Expr)
    (bounded : SharesIn (fun slot => slot < constant.sharing.size) expression) :
    TeleBounded constant (stripAllFull constant fuel expression) := by
  induction fuel generalizing expression with
  | zero =>
    change TeleBounded constant ([], expression)
    exact ⟨by simp, bounded⟩
  | succ fuel ih =>
    have exposed := unshare_expansion constant expand entries expression bounded
    rw [stripAllFull]
    cases head : unshare constant expression with
    | all contract binder type body =>
      have pair := exposed.2.1
      rw [head] at pair
      have rest := ih body pair.2
      exact ⟨fun type member => (List.mem_cons.mp member).elim (fun same => same ▸ pair.1)
        (fun member => rest.1 type member), rest.2⟩
    | _ => exact ⟨by simp, by simpa only [head] using exposed.2.1⟩

/-- Application-head analysis commutes with expansion for every fuel value;
the residual at exhausted fuel is expanded on both sides of this equation. -/
theorem appHead_expand (constant flat : Ixon.Constant) (empty : flat.sharing = #[])
    (expand : Nat → Ixon.Expr) (entries : Entries constant expand) (fuel : Nat)
    (expression : Ixon.Expr) (bounded : SharesIn (fun slot => slot < constant.sharing.size) expression) :
    substShares expand (appHead constant fuel expression) = appHead flat fuel (substShares expand expression) := by
  induction fuel generalizing expression with
  | zero => rfl
  | succ fuel ih =>
    have exposed := unshare_expansion constant expand entries expression bounded
    simp only [appHead, unshare_empty flat empty, ← exposed.2.2]
    cases head : unshare constant expression with
    | share index => simp only [head, InlineHead, false_and] at exposed
    | app function argument =>
      have pair := exposed.2.1
      rw [head] at pair
      exact ih function pair.1
    | _ => rfl

def appDepth : Ixon.Expr → Nat
  | .app function _ => appDepth function + 1
  | _ => 0

/-- A strict bound on the expanded application's spine leaves enough fuel to
expose its final head, including any sharing indirection at that last node. -/
theorem appHead_inline (constant : Ixon.Constant) (expand : Nat → Ixon.Expr)
    (entries : Entries constant expand) (fuel : Nat) (expression : Ixon.Expr)
    (bounded : SharesIn (fun slot => slot < constant.sharing.size) expression)
    (enough : appDepth (substShares expand expression) < fuel) :
    InlineHead (appHead constant fuel expression) := by
  induction fuel generalizing expression with
  | zero => omega
  | succ fuel ih =>
    have exposed := unshare_expansion constant expand entries expression bounded
    rw [← exposed.2.2] at enough
    rw [appHead]
    cases head : unshare constant expression with
    | share index => simp only [head, InlineHead, false_and] at exposed
    | app function argument =>
      have pair := exposed.2.1
      rw [head] at pair enough
      simp only [substShares, appDepth] at enough
      exact ih function pair.1 (by omega)
    | _ => trivial

def selfRef (constant : Ixon.Constant) (owner : Address) (index : UInt64) : Option (Kernel.ConstRef Address) :=
  match constant.info with
  | .muts members => if index.toNat < members.size then some (.member owner index.toNat) else none
  | _ => if index == 0 then some (.member owner 0) else none

/-- Reference-head lookup is preserved when sharing preserves the reference
table and self-member interpretation, with explicit application-spine fuel. -/
theorem headRef_expand (store : Store) (owner : Address) (constant flat : Ixon.Constant)
    (empty : flat.sharing = #[]) (refs : constant.refs = flat.refs)
    (self : ∀ index, selfRef constant owner index = selfRef flat owner index)
    (expand : Nat → Ixon.Expr) (entries : Entries constant expand)
    (expression : Ixon.Expr) (bounded : SharesIn (fun slot => slot < constant.sharing.size) expression)
    (enough : appDepth (substShares expand expression) < spineFuel) :
    headRef store owner constant expression = headRef store owner flat (substShares expand expression) := by
  have meaning := appHead_expand constant flat empty expand entries spineFuel expression bounded
  have inline := appHead_inline constant expand entries spineFuel expression bounded enough
  unfold headRef
  rw [← meaning]
  cases head : appHead constant spineFuel expression with
  | share index => simp only [head, InlineHead] at inline
  | ref index levels => simp only [substShares, refs]
  | recur index levels => exact self index
  | _ => rfl

def lastHead (store : Store) (owner : Address) (constant : Ixon.Constant)
    (types : List Ixon.Expr) : Option (Kernel.ConstRef Address) := do
  headRef store owner constant (← types.getLast?)

theorem lastHead_expand (store : Store) (owner : Address) (constant flat : Ixon.Constant)
    (empty : flat.sharing = #[]) (refs : constant.refs = flat.refs)
    (self : ∀ index, selfRef constant owner index = selfRef flat owner index)
    (expand : Nat → Ixon.Expr) (entries : Entries constant expand) (types : List Ixon.Expr)
    (bounded : ∀ type ∈ types, SharesIn (fun slot => slot < constant.sharing.size) type)
    (enough : ∀ type, types.getLast? = some type → appDepth (substShares expand type) < spineFuel) :
    lastHead store owner constant types = lastHead store owner flat (types.map (substShares expand)) := by
  unfold lastHead
  rw [List.getLast?_map]
  cases last : types.getLast? with
  | none => rfl
  | some type =>
    have present := List.mem_of_getLast? last
    exact headRef_expand store owner constant flat empty refs self expand entries type (bounded type present) (enough type last)

def carrier (store : Store) (owner : Address) (constant : Ixon.Constant) (domain : Ixon.Expr) :
    Option (Kernel.ConstRef Address) :=
  lastHead store owner constant (stripAllFull constant spineFuel domain).1

theorem carrier_expand (store : Store) (owner : Address) (constant flat : Ixon.Constant)
    (empty : flat.sharing = #[]) (refs : constant.refs = flat.refs)
    (self : ∀ index, selfRef constant owner index = selfRef flat owner index)
    (expand : Nat → Ixon.Expr) (entries : Entries constant expand) (domain : Ixon.Expr)
    (bounded : SharesIn (fun slot => slot < constant.sharing.size) domain)
    (enough : ∀ type, (stripAllFull flat spineFuel (substShares expand domain)).1.getLast? = some type →
      appDepth type < spineFuel) :
    carrier store owner constant domain = carrier store owner flat (substShares expand domain) := by
  have domains : (stripAllFull constant spineFuel domain).1.map (substShares expand) =
      (stripAllFull flat spineFuel (substShares expand domain)).1 :=
    congrArg Prod.fst (stripAllFull_expand constant flat empty expand entries spineFuel domain bounded)
  have bounds := stripAllFull_bounded constant expand entries spineFuel domain bounded
  unfold carrier
  rw [← domains]
  apply lastHead_expand store owner constant flat empty refs self expand entries _ bounds.1
  intro type last
  apply enough (substShares expand type)
  rw [← domains, List.getLast?_map, last]
  rfl

private theorem list_mapM_congr (items : List α) (left right : α → Option β)
    (same : ∀ item ∈ items, left item = right item) : items.mapM left = items.mapM right := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
    rw [List.mapM_cons, List.mapM_cons, same head (by simp), ih (fun item present => same item (by simp [present]))]

theorem carriers_expand (store : Store) (owner : Address) (constant flat : Ixon.Constant)
    (empty : flat.sharing = #[]) (refs : constant.refs = flat.refs)
    (self : ∀ index, selfRef constant owner index = selfRef flat owner index)
    (expand : Nat → Ixon.Expr) (entries : Entries constant expand) (domains : List Ixon.Expr)
    (bounded : ∀ domain ∈ domains, SharesIn (fun slot => slot < constant.sharing.size) domain)
    (enough : ∀ domain ∈ domains, ∀ type,
      (stripAllFull flat spineFuel (substShares expand domain)).1.getLast? = some type → appDepth type < spineFuel) :
    domains.toArray.mapM (carrier store owner constant) =
      (domains.map (substShares expand)).toArray.mapM (carrier store owner flat) := by
  simp only [Array.mapM_eq_mapM_toList, List.mapM_map]
  apply congrArg (fun values : Option (List (Kernel.ConstRef Address)) => List.toArray <$> values)
  apply list_mapM_congr
  intro domain present
  exact carrier_expand store owner constant flat empty refs self expand entries domain (bounded domain present) (enough domain present)

def depth (recursor : Ixon.Recursor) : Nat :=
  recursor.params.toNat + recursor.motives.toNat + recursor.minors.toNat + recursor.indices.toNat + 1

/-- Bounds on exactly the application spines inspected by recursor analysis.
This does not assume that either recursor analysis succeeds. -/
def AnalysisBounds (flat : Ixon.Constant) (recursor : Ixon.Recursor) : Prop :=
  ∀ types body, stripAll flat (depth recursor) recursor.typ = some (types, body) →
    appDepth body < spineFuel ∧
    (∀ type, types.getLast? = some type → appDepth type < spineFuel) ∧
    (∀ domain ∈ (types.drop recursor.params.toNat).take recursor.motives.toNat,
      ∀ type, (stripAllFull flat spineFuel domain).1.getLast? = some type → appDepth type < spineFuel)

/-- The complete syntactic recursor analysis, including rejection, agrees
with expansion when its inspected application spines fit the actual bound. -/
theorem analyse_expand (store : Store) (owner : Address) (constant flat : Ixon.Constant)
    (empty : flat.sharing = #[]) (refs : constant.refs = flat.refs)
    (self : ∀ index, selfRef constant owner index = selfRef flat owner index)
    (expand : Nat → Ixon.Expr) (entries : Entries constant expand) (recursor : Ixon.Recursor)
    (bounded : SharesIn (fun slot => slot < constant.sharing.size) recursor.typ)
    (enough : AnalysisBounds flat { recursor with typ := substShares expand recursor.typ }) :
    analyseRecursor store owner constant recursor =
      analyseRecursor store owner flat { recursor with typ := substShares expand recursor.typ } := by
  have telescope := stripAll_expand constant flat empty expand entries (depth recursor) recursor.typ bounded
  cases parsed : stripAll constant (depth recursor) recursor.typ with
  | none =>
    simp only [parsed, Option.map_none] at telescope
    dsimp only [depth] at parsed telescope
    simp only [analyseRecursor, parsed, ← telescope, bind, Option.bind]
  | some result =>
    rcases result with ⟨types, body⟩
    simp only [parsed, Option.map_some] at telescope
    have fits := enough (types.map (substShares expand)) (substShares expand body) telescope.symm
    have scopes := stripAll_bounded constant expand entries (depth recursor) recursor.typ bounded (types, body) parsed
    have headMeaning := appHead_expand constant flat empty expand entries spineFuel body scopes.2
    have inline := appHead_inline constant expand entries spineFuel body scopes.2 fits.1
    have major := lastHead_expand store owner constant flat empty refs self expand entries types scopes.1
      (fun type last => fits.2.1 _ (by rw [List.getLast?_map, last]; rfl))
    have motives := carriers_expand store owner constant flat empty refs self expand entries
      ((types.drop recursor.params.toNat).take recursor.motives.toNat)
      (fun domain present => scopes.1 domain (List.mem_of_mem_drop (List.mem_of_mem_take present))) (by
        intro domain present type inType
        apply fits.2.2 (substShares expand domain) _ type inType
        rw [← List.map_drop, ← List.map_take]
        exact List.mem_map.mpr ⟨domain, present, rfl⟩)
    dsimp only [depth] at parsed telescope
    simp only [analyseRecursor, parsed, ← telescope, expandTele, bind, Option.bind,
      ← headMeaning]
    cases head : appHead constant spineFuel body with
    | share index => simp only [head, InlineHead] at inline
    | var index =>
      simp only [substShares, List.map_drop, List.map_take] at motives ⊢
      unfold carrier lastHead at motives
      unfold lastHead at major
      simp only [bind, Option.bind] at motives major
      rw [motives]
      cases last : types.getLast? with
      | none => simp only [List.getLast?_map, last, Option.map_none]
      | some type =>
        simp only [List.getLast?_map, last, Option.map_some] at major ⊢
        rw [major]
    | _ => rfl

open Ix.CompileM in
/-- The actual sharing builder preserves standalone recursor analysis. Its
checked expansion supplies table and root invariants; only the unshared
input's explicit application-spine bounds remain a source obligation. -/
theorem build_analyse (store : Store) (owner : Address) (limits : Sharing.Exact.Limits)
    (source : Ixon.Recursor) (refs : Array Address) (univs : Array Ixon.Univ) (output : Ixon.Constant)
    (ran : buildConstantWithSharing limits (.recr source) refs univs = .ok output)
    (enough : AnalysisBounds { info := .recr source, sharing := #[], refs, univs } source) :
    ∃ target, output.info = .recr target ∧
      analyseRecursor store owner output target =
        analyseRecursor store owner { info := .recr source, sharing := #[], refs, univs } source := by
  obtain ⟨shared, info, sharedRun, size, written, shape⟩ := Sharing.Verify.buildConstantWithSharing_eq_ok ran
  obtain ⟨type, rhss, rootsEq, count, header⟩ := RecursorSharing.writeback source shared.result.roots info
    (by simpa [RecursorSharing.roots] using size) written
  subst info
  subst output
  have meaning := Sharing.Verify.CanonicalMeaning.canonicalSharingTiered_meaning .tagN limits
    (constantInfoRootExprs (.recr source)) shared sharedRun
  rw [RecursorSharing.roots, rootsEq] at meaning
  obtain ⟨expand, entries, bounded, same⟩ := meaning
  have listEq := congrArg Array.toList same
  simp only [Array.toList_map, List.map_cons] at listEq
  have typeEq : substShares expand type = source.typ := (List.cons.inj listEq).1
  let target := RecursorSharing.rewrite source type rhss
  let flat : Ixon.Constant := { info := .recr source, sharing := #[], refs, univs }
  let constant : Ixon.Constant := { info := .recr target, sharing := shared.result.sharing, refs, univs }
  have typeBound : SharesIn (fun slot => slot < constant.sharing.size) target.typ :=
    bounded type (by simp)
  have fits : AnalysisBounds flat { target with typ := substShares expand target.typ } := by
    intro types body parsed
    change stripAll flat (depth source) (substShares expand type) = some (types, body) at parsed
    rw [typeEq] at parsed
    exact enough types body parsed
  have analysed := analyse_expand store owner constant flat rfl rfl (fun _ => rfl)
    expand entries target typeBound fits
  refine ⟨target, rfl, ?_⟩
  change analyseRecursor store owner constant target = analyseRecursor store owner flat source
  rw [analysed]
  simp only [analyseRecursor, target, RecursorSharing.rewrite, typeEq]

end Ix.CompileCert.ReaderSpines
