import IxSharingVerify.CanonicalMeaning
import IxSharingVerify.Builder
import Ix.CompileCert.ExpressionRead

/-! # Canonical sharing preserves the reading of every root

The compiler builds every block with `Ix.CompileM.buildConstantWithSharing`:
the payload's roots (`constantInfoRootExprs`, in cursor order) go through
the canonical sharing construction and are written back by `withRoots`.
This module proves, once for every `Ixon.ConstantInfo` (R07-01/02):

* `withRoots_inv`: a successful write-back replaces exactly the roots, in
  order (`constantInfoRoots info' = roots`), and keeps everything else
  (`erase info' = erase info`, where `erase` replaces every root by one
  placeholder, `Ix.Sharing.Exact.mapRoots`);
* `build_roots`: the actual member reader (`MemberReader.mk'`) of the shared
  constant reads every root of the result exactly as the reader of the
  unshared payload over the same tables reads the input roots, errors
  included (`canonicalSharingTiered_meaning`, which assumes no pointer or
  hash injectivity, through `meaning_read_before`);
* `build_read`: hence the compiler's in-flight reading of the payload's
  roots (`ExpressionRead.blockReader`) is the emitted record's reading of
  its roots, and so is every relation stated root by root (`RootsRead`):
  the "header plus ordered roots" view of each payload kind.

CT-15's `SharingRead` and the per-kind `writeback`/`build_read` lemmas of
`HeaderBlock`, `RecursorSharing` and `InductiveSharing`, as one theorem;
it covers mutual blocks too. -/

namespace Ix.CompileCert.SharingRoots

open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader
open Ix.Sharing.Verify.SharingExact (substShares SharesIn)
open Ix.Sharing.Verify.CanonicalMeaning (SharingMeaning)

variable {md : Mode}

/-! ## The certified reader against a sharing substitution -/

/-- Every converted sharing entry is the reading of its expansion. -/
def TableMeaning (context : ECx md) (substitution : Nat → Ixon.Expr) (table : Array (ReadM (CExpr md))) :
    Prop :=
  ∀ index, index < table.size → table[index]? = some (convExpr context #[] (substitution index))

/-- The certified expression reader agrees with share substitution, errors
included, whenever every referenced table slot has its interpretation. -/
theorem convExpr_subst (context : ECx md) (substitution : Nat → Ixon.Expr)
    (table : Array (ReadM (CExpr md))) (meaning : TableMeaning context substitution table)
    (source : Ixon.Expr) (bounded : SharesIn (fun index => index < table.size) source) :
    convExpr context table source = convExpr context #[] (substShares substitution source) := by
  induction source with
  | share index => simp only [convExpr, substShares, meaning index.toNat bounded]
  | prj _ _ _ ih => simp only [convExpr, substShares, ih bounded]
  | app _ _ ihf iha | lam _ _ _ ihf iha | all _ _ _ _ ihf iha =>
    simp only [convExpr, substShares, ihf bounded.1, iha bounded.2]
  | letE _ _ _ _ iht ihv ihb =>
    simp only [convExpr, substShares, iht bounded.1, ihv bounded.2.1, ihb bounded.2.2]
  | _ => rfl

theorem table_empty (context : ECx md) (substitution : Nat → Ixon.Expr) :
    TableMeaning context substitution #[] := by
  intro index bound
  simp at bound

theorem table_push (context : ECx md) (substitution : Nat → Ixon.Expr)
    (table : Array (ReadM (CExpr md))) (meaning : TableMeaning context substitution table)
    (source : Ixon.Expr) (bounded : SharesIn (fun index => index < table.size) source)
    (equation : substitution table.size = substShares substitution source) :
    TableMeaning context substitution (table.push (convExpr context table source)) := by
  have read : convExpr context table source = convExpr context #[] (substitution table.size) := by
    rw [convExpr_subst context substitution table meaning source bounded, equation]
  intro index bound
  by_cases old : index < table.size
  · rw [Array.getElem?_push_lt old]
    have prior := meaning index old
    rw [Array.getElem?_eq_getElem old] at prior
    exact prior
  · have last : index = table.size := by simp only [Array.size_push] at bound; omega
    subst index
    rw [Array.getElem?_push_size, read]

/-- The reader's conversion of a sharing table, entry by entry. -/
def buildTable (context : ECx md) (sources : List Ixon.Expr) (initial : Array (ReadM (CExpr md))) :
    Array (ReadM (CExpr md)) :=
  sources.foldl (fun table source => table.push (convExpr context table source)) initial

theorem buildTable_meaning (context : ECx md) (substitution : Nat → Ixon.Expr)
    (sources : List Ixon.Expr) (initial : Array (ReadM (CExpr md)))
    (meaning : TableMeaning context substitution initial)
    (entries : ∀ index, index < sources.length →
      substitution (initial.size + index) = substShares substitution sources[index]! ∧
      SharesIn (fun slot => slot < initial.size + index) sources[index]!) :
    (buildTable context sources initial).size = initial.size + sources.length ∧
      TableMeaning context substitution (buildTable context sources initial) := by
  induction sources generalizing initial with
  | nil => exact ⟨by simp [buildTable], meaning⟩
  | cons source rest ih =>
    have first := entries 0 (by simp)
    simp only [Nat.add_zero, List.getElem!_cons_zero] at first
    have next := table_push context substitution initial meaning source first.2 first.1
    have tail := ih (initial.push (convExpr context initial source)) next (by
      intro index bound
      have row := entries (index + 1) (by simp only [List.length_cons]; omega)
      simpa only [Array.size_push, List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 index] using row)
    refine ⟨?_, tail.2⟩
    change (buildTable context rest (initial.push (convExpr context initial source))).size = _
    rw [tail.1]
    simp only [Array.size_push, List.length_cons]
    omega

/-- The expression context `MemberReader.mk'` reads a record's members in. -/
def expressionContext (context : Ctx md) (source : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) : ECx md :=
  ⟨context, source, source.univs.map (convUniv param), self⟩

theorem memberReader_eq (context : Ctx md) (source : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) :
    MemberReader.mk' context source param self =
      ⟨expressionContext context source param self,
        buildTable (expressionContext context source param self) source.sharing.toList #[]⟩ := by
  simp [MemberReader.mk', expressionContext, buildTable, Array.forIn_pure_yield_eq_foldl, Array.mkEmpty]

theorem memberReader_table (context : Ctx md) (source : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (substitution : Nat → Ixon.Expr)
    (entries : ∀ index, index < source.sharing.size →
      substitution index = substShares substitution source.sharing[index]! ∧
      SharesIn (fun slot => slot < index) source.sharing[index]!) :
    (MemberReader.mk' context source param self).tbl.size = source.sharing.size ∧
      TableMeaning (expressionContext context source param self) substitution
        (MemberReader.mk' context source param self).tbl := by
  rw [memberReader_eq]
  have built := buildTable_meaning (expressionContext context source param self) substitution
    source.sharing.toList #[] (table_empty _ _) (by
      intro index bound
      simpa [getElem!_def] using entries index (by simpa using bound))
  simpa using built

theorem memberReader_subst (context : Ctx md) (source : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (substitution : Nat → Ixon.Expr)
    (entries : ∀ index, index < source.sharing.size →
      substitution index = substShares substitution source.sharing[index]! ∧
      SharesIn (fun slot => slot < index) source.sharing[index]!)
    (root : Ixon.Expr) (bounded : SharesIn (fun slot => slot < source.sharing.size) root) :
    (MemberReader.mk' context source param self).read root =
      convExpr (expressionContext context source param self) #[] (substShares substitution root) := by
  have table := memberReader_table context source param self substitution entries
  exact convExpr_subst (expressionContext context source param self) substitution
    (MemberReader.mk' context source param self).tbl table.2 root (by simpa only [table.1] using bounded)

/-- **The actual member reader reads a sharing encoding as the unfolded
ordered roots**, errors included. -/
theorem meaning_read (context : Ctx md) (source : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (originals roots : Array Ixon.Expr)
    (meaning : SharingMeaning originals source.sharing roots) :
    roots.map (MemberReader.mk' context source param self).read =
      originals.map (convExpr (expressionContext context source param self) #[]) := by
  obtain ⟨substitution, entries, bounded, same⟩ := meaning
  rw [← same, Array.map_map]
  apply Array.ext (by simp)
  intro index beforeBound afterBound
  simp only [Array.size_map] at beforeBound afterBound
  simp only [Array.getElem_map, Function.comp_apply]
  exact memberReader_subst context source param self substitution entries roots[index]
    (bounded _ (Array.getElem_mem beforeBound))

/-- Reading depends on a record only through its reference and universe
tables. -/
theorem convExpr_same_tables (context : Ctx md) (before after : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (refs : before.refs = after.refs)
    (univs : before.univs = after.univs) (table : Array (ReadM (CExpr md))) (source : Ixon.Expr) :
    convExpr (expressionContext context before param self) table source =
      convExpr (expressionContext context after param self) table source := by
  have level : (expressionContext context before param self).level =
      (expressionContext context after param self).level := by
    funext index
    simp only [ECx.level, expressionContext, univs]
  have levels : (expressionContext context before param self).levels =
      (expressionContext context after param self).levels := by
    funext indices
    unfold ECx.levels
    rw [level]
  have key : (expressionContext context before param self).keyAt =
      (expressionContext context after param self).keyAt := by
    funext index
    simp only [ECx.keyAt, expressionContext, refs]
  have blob : (expressionContext context before param self).blobAt =
      (expressionContext context after param self).blobAt := by
    funext index
    simp only [ECx.blobAt, expressionContext, refs]
  induction source
  all_goals simp only [convExpr, *]
  all_goals rfl

theorem memberReader_empty (context : Ctx md) (source : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (empty : source.sharing = #[]) (root : Ixon.Expr) :
    (MemberReader.mk' context source param self).read root =
      convExpr (expressionContext context source param self) #[] root := by
  rw [memberReader_eq]
  simp only [MemberReader.read, empty, Array.toList_empty, buildTable, List.foldl_nil]

/-- **Sharing preserves every root's reading**: the shared record's reader
reads the shared roots as the unshared record's reader, over the same
tables, reads the original roots, errors included. -/
theorem meaning_read_before (context : Ctx md) (before after : Ixon.Constant) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (refs : before.refs = after.refs)
    (univs : before.univs = after.univs) (empty : before.sharing = #[]) (originals roots : Array Ixon.Expr)
    (meaning : SharingMeaning originals after.sharing roots) :
    roots.map (MemberReader.mk' context after param self).read =
      originals.map (MemberReader.mk' context before param self).read := by
  rw [meaning_read context after param self originals roots meaning]
  apply Array.ext (by simp)
  intro index leftBound rightBound
  simp only [Array.size_map] at leftBound rightBound
  simp only [Array.getElem_map]
  rw [memberReader_empty context before param self empty]
  exact (convExpr_same_tables context before after param self refs univs #[] originals[index]).symm

/-- The compiler's in-flight reader is the actual member reader of an
unshared record over the block's tables. -/
theorem unshared_read (context : Ctx md) (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md)))
    (state : Ix.CompileM.BlockState) (info : Ixon.ConstantInfo) (root : Ixon.Expr) :
    (MemberReader.mk' (ExpressionRead.withBlockBlobs context state)
      { info, sharing := #[], refs := state.refs, univs := state.univs } param self).read root =
      (ExpressionRead.blockReader context param self state).read root := by
  unfold ExpressionRead.blockReader
  rw [memberReader_empty _ _ _ _ rfl, memberReader_empty _ _ _ _ rfl]
  exact convExpr_same_tables (ExpressionRead.withBlockBlobs context state)
    { info, sharing := #[], refs := state.refs, univs := state.univs } (ExpressionRead.tablesRecord state)
    param self rfl rfl #[] root

/-! ## Root write-back -/

section WriteBack

open Ix.Sharing.Exact

/-- A payload with every root replaced by one placeholder: what a root
write-back keeps. -/
def erase (info : Ixon.ConstantInfo) : Ixon.ConstantInfo := mapRoots (fun _ => .sort 0) info

/-- A mutual member with every root replaced by the placeholder. -/
def eraseMut (member : Ixon.MutConst) : Ixon.MutConst := mapMutConstRoots (fun _ => .sort 0) member

theorem zip_ctors (ctors : List Ixon.Constructor) (types : List Ixon.Expr) (count : types.length = ctors.length) :
    ((ctors.zip types).map fun (c, t) => { c with typ := t }).map (·.typ) = types ∧
      ((ctors.zip types).map fun (c, t) => { c with typ := t }).map
        (fun c => { c with typ := Ixon.Expr.sort 0 }) = ctors.map (fun c => { c with typ := Ixon.Expr.sort 0 }) := by
  induction ctors generalizing types with
  | nil => cases types <;> simp_all
  | cons ctor rest ih =>
    cases types with
    | nil => simp at count
    | cons type types =>
      have tail := ih types (by simpa using count)
      simp only [List.zip_cons_cons, List.map_cons, tail.1, tail.2, and_self]

theorem zip_rules (rules : List Ixon.RecursorRule) (rhss : List Ixon.Expr) (count : rhss.length = rules.length) :
    ((rules.zip rhss).map fun (r, e) => { r with rhs := e }).map (·.rhs) = rhss ∧
      ((rules.zip rhss).map fun (r, e) => { r with rhs := e }).map
        (fun r => { r with rhs := Ixon.Expr.sort 0 }) = rules.map (fun r => { r with rhs := Ixon.Expr.sort 0 }) := by
  induction rules generalizing rhss with
  | nil => cases rhss <;> simp_all
  | cons rule rest ih =>
    cases rhss with
    | nil => simp at count
    | cons rhs rhss =>
      have tail := ih rhss (by simpa using count)
      simp only [List.zip_cons_cons, List.map_cons, tail.1, tail.2, and_self]

/-- A successful member write-back takes exactly its roots off the cursor,
in order, and keeps everything but the roots. -/
theorem withMutConstRoots_inv {m m' : Ixon.MutConst} {rs rest : List Ixon.Expr}
    (h : withMutConstRoots m rs = .ok (m', rest)) :
    rs = mutConstRoots m' ++ rest ∧ eraseMut m' = eraseMut m := by
  cases m with
  | defn d =>
    simp only [withMutConstRoots] at h
    cases h1 : takeRoot rs with
    | error err => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨typ, r1⟩ := p
      cases h2 : takeRoot r1 with
      | error err => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨value, r2⟩ := q
        simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain rfl := Ix.Sharing.Verify.takeRoot_eq_ok h1
        obtain rfl := Ix.Sharing.Verify.takeRoot_eq_ok h2
        exact ⟨rfl, rfl⟩
  | indc i =>
    simp only [withMutConstRoots] at h
    cases h1 : takeRoot rs with
    | error err => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨typ, r1⟩ := p
      cases h2 : takeRoots i.ctors.size r1 with
      | error err => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨tys, r2⟩ := q
        simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain rfl := Ix.Sharing.Verify.takeRoot_eq_ok h1
        obtain ⟨count, rfl⟩ := Ix.Sharing.Verify.takeRoots_eq_ok h2
        have zipped := zip_ctors i.ctors.toList tys (by simpa using count)
        refine ⟨?_, ?_⟩
        · simp only [mutConstRoots, zipped.1, List.cons_append]
        · simp only [eraseMut, mapMutConstRoots, Ixon.MutConst.indc.injEq]
          congr 1
          apply Array.ext'
          simp only [Array.toList_map, zipped.2]
  | recr r =>
    simp only [withMutConstRoots] at h
    cases h1 : takeRoot rs with
    | error err => simp [h1, bind, Except.bind] at h
    | ok p =>
      obtain ⟨typ, r1⟩ := p
      cases h2 : takeRoots r.rules.size r1 with
      | error err => simp [h1, h2, bind, Except.bind] at h
      | ok q =>
        obtain ⟨rhss, r2⟩ := q
        simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain rfl := Ix.Sharing.Verify.takeRoot_eq_ok h1
        obtain ⟨count, rfl⟩ := Ix.Sharing.Verify.takeRoots_eq_ok h2
        have zipped := zip_rules r.rules.toList rhss (by simpa using count)
        refine ⟨?_, ?_⟩
        · simp only [mutConstRoots, zipped.1, List.cons_append]
        · simp only [eraseMut, mapMutConstRoots, Ixon.MutConst.recr.injEq]
          congr 1
          apply Array.ext'
          simp only [Array.toList_map, zipped.2]

/-- **A successful root write-back replaces exactly the roots**, in order,
and keeps everything else, for every payload kind. -/
theorem withRoots_inv {info info' : Ixon.ConstantInfo} {roots : Array Ixon.Expr}
    (h : withRoots info roots = .ok info') : constantInfoRoots info' = roots ∧ erase info' = erase info := by
  simp only [withRoots] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  cases info with
  | defn d =>
    obtain ⟨⟨m, rest⟩, hw, h⟩ := Ix.Sharing.Verify.except_bind_eq_ok h
    have inv := withMutConstRoots_inv hw
    cases m with
    | defn d' =>
      simp only [bind, Except.bind, pure, Except.pure] at h
      have tail := h
      split at tail
      · rename_i empty
        cases Except.ok.inj tail
        simp only [List.isEmpty_iff] at empty
        subst empty
        refine ⟨?_, ?_⟩
        · apply Array.ext'
          simp [constantInfoRoots, inv.1]
        · have same := inv.2
          simp only [eraseMut, mapMutConstRoots, Ixon.MutConst.defn.injEq] at same
          simp only [erase, mapRoots, same]
      · cases tail
    | _ => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | recr r =>
    obtain ⟨⟨m, rest⟩, hw, h⟩ := Ix.Sharing.Verify.except_bind_eq_ok h
    have inv := withMutConstRoots_inv hw
    cases m with
    | recr r' =>
      simp only [bind, Except.bind, pure, Except.pure] at h
      have tail := h
      split at tail
      · rename_i empty
        cases Except.ok.inj tail
        simp only [List.isEmpty_iff] at empty
        subst empty
        refine ⟨?_, ?_⟩
        · apply Array.ext'
          simp [constantInfoRoots, inv.1]
        · have same := inv.2
          simp only [eraseMut, mapMutConstRoots, Ixon.MutConst.recr.injEq] at same
          simp only [erase, mapRoots, same]
      · cases tail
    | _ => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | axio a =>
    obtain ⟨⟨typ, rest⟩, hw, h⟩ := Ix.Sharing.Verify.except_bind_eq_ok h
    have taken := Ix.Sharing.Verify.takeRoot_eq_ok hw
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · rename_i empty
      cases Except.ok.inj h
      simp only [List.isEmpty_iff] at empty
      subst empty
      refine ⟨?_, rfl⟩
      apply Array.ext'
      simp [constantInfoRoots, taken]
    · cases h
  | quot q =>
    obtain ⟨⟨typ, rest⟩, hw, h⟩ := Ix.Sharing.Verify.except_bind_eq_ok h
    have taken := Ix.Sharing.Verify.takeRoot_eq_ok hw
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · rename_i empty
      cases Except.ok.inj h
      simp only [List.isEmpty_iff] at empty
      subst empty
      refine ⟨?_, rfl⟩
      apply Array.ext'
      simp [constantInfoRoots, taken]
    · cases h
  | cPrj p | rPrj p | iPrj p | dPrj p =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · rename_i empty
      cases Except.ok.inj h
      simp only [List.isEmpty_iff, Array.toList_eq_nil_iff] at empty
      exact ⟨by simp [constantInfoRoots, empty], rfl⟩
    · cases h
  | muts ms =>
    dsimp only at h
    rw [← Array.forIn_toList] at h
    obtain ⟨s, hs, h⟩ := Ix.Sharing.Verify.except_bind_eq_ok h
    have loop := Ix.Sharing.Verify.forIn_except_inv
      (fun (pending : List Ixon.MutConst) (b : Array Ixon.MutConst × List Ixon.Expr) =>
        ∃ done, ms.toList = done ++ pending ∧ b.1.toList.map eraseMut = done.map eraseMut ∧
          roots.toList = b.1.toList.flatMap mutConstRoots ++ b.2) _
      (by
        intro member pending b r inv step
        obtain ⟨⟨m', rest⟩, hw, step⟩ := Ix.Sharing.Verify.except_bind_eq_ok step
        simp only [pure, Except.pure, Except.ok.injEq] at step
        obtain ⟨done, split, erased, cursor⟩ := inv
        have one := withMutConstRoots_inv hw
        refine ⟨_, step.symm, done ++ [member], by simp [split], ?_, ?_⟩
        · simp [erased, one.2]
        · simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.append_assoc]
          rw [cursor, one.1])
      ms.toList (#[], roots.toList) s ⟨[], by simp, by simp, by simp⟩ hs
    obtain ⟨done, split, erased, cursor⟩ := loop
    simp only [List.append_nil] at split
    subst split
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · rename_i empty
      cases Except.ok.inj h
      simp only [List.isEmpty_iff] at empty
      rw [empty, List.append_nil] at cursor
      refine ⟨?_, ?_⟩
      · apply Array.ext'
        simp [constantInfoRoots, cursor]
      · simp only [erase, mapRoots, Ixon.ConstantInfo.muts.injEq]
        apply Array.ext'
        have same : s.1.toList.map (mapMutConstRoots fun _ => .sort 0) =
            ms.toList.map (mapMutConstRoots fun _ => .sort 0) := erased
        simpa using same
    · cases h

end WriteBack

/-! ## The sharing builder -/

/-- **The sharing builder preserves every root's reading**: a successful
build keeps the payload but its roots (`erase`) and the tables, and the
actual member reader of the built constant reads its roots as the unshared
payload's reader reads the input roots, errors included. -/
theorem build_roots (limits : Ix.Sharing.Exact.Limits) (info : Ixon.ConstantInfo) (refs : Array Address)
    (univs : Array Ixon.Univ) (out : Ixon.Constant)
    (ran : Ix.CompileM.buildConstantWithSharing limits info refs univs = .ok out) :
    erase out.info = erase info ∧ out.refs = refs ∧ out.univs = univs ∧
      ∀ (context : Ctx md) (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md))),
        (Ix.CompileM.constantInfoRootExprs out.info).map (MemberReader.mk' context out param self).read =
          (Ix.CompileM.constantInfoRootExprs info).map
            (MemberReader.mk' context { info, sharing := #[], refs, univs } param self).read := by
  obtain ⟨shared, info', sharedRan, _, written, rfl⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok ran
  have rewritten : Ix.Sharing.Exact.withRoots info shared.result.roots = .ok info' := by
    simp only [Ix.CompileM.withRootExprs] at written
    cases w : Ix.Sharing.Exact.withRoots info shared.result.roots with
    | error error => rw [w] at written; cases written
    | ok value => rw [w] at written; cases written; rfl
  have inv := withRoots_inv rewritten
  have meaning := Ix.Sharing.Verify.CanonicalMeaning.canonicalSharingTiered_meaning .tagN limits
    (Ix.CompileM.constantInfoRootExprs info) shared sharedRan
  refine ⟨inv.2, rfl, rfl, fun context param self => ?_⟩
  rw [Ix.Sharing.Verify.constantInfoRootExprs_eq_roots info', inv.1]
  exact meaning_read_before context { info, sharing := #[], refs, univs }
    { info := info', sharing := shared.result.sharing, refs, univs } param self rfl rfl rfl
    (Ix.CompileM.constantInfoRootExprs info) shared.result.roots meaning

/-! ## Relations stated root by root -/

/-- Each root reads as a term related to its source, in order. -/
def RootsRead (reader : MemberReader md) (related : Ix.Expr → CExpr md → Prop)
    (sources : List Ix.Expr) (roots : List Ixon.Expr) : Prop :=
  List.Forall₂ (fun source root => ∃ target, related source target ∧ reader.read root = .ok target) sources roots

/-- A root-by-root relation transfers to roots that read the same. -/
theorem RootsRead.transfer {before after : MemberReader md} {related : Ix.Expr → CExpr md → Prop}
    {sources : List Ix.Expr} {roots roots' : List Ixon.Expr}
    (same : roots'.map after.read = roots.map before.read) (holds : RootsRead before related sources roots) :
    RootsRead after related sources roots' := by
  induction holds generalizing roots' with
  | nil =>
    cases roots' with
    | nil => exact .nil
    | cons _ _ => simp at same
  | cons head _ ih =>
    cases roots' with
    | nil => simp at same
    | cons root' rest' =>
      simp only [List.map_cons, List.cons.injEq] at same
      obtain ⟨target, rel, read⟩ := head
      exact .cons ⟨target, rel, same.1.trans read⟩ (ih same.2)

/-- A root-by-root relation survives every extension of the in-flight
reader. -/
theorem RootsRead.grow {context : Ctx md} {param : Nat → LevelParam} {self : Nat → Option (ReadM (CName md))}
    {before after : Ix.CompileM.BlockState} {related : Ix.Expr → CExpr md → Prop}
    {sources : List Ix.Expr} {roots : List Ixon.Expr}
    (growth : ExpressionRead.Extends (ExpressionRead.blockReader context param self before).ecx
      (ExpressionRead.blockReader context param self after).ecx)
    (holds : RootsRead (ExpressionRead.blockReader context param self before) related sources roots) :
    RootsRead (ExpressionRead.blockReader context param self after) related sources roots := by
  induction holds with
  | nil => exact .nil
  | cons head _ ih =>
    obtain ⟨target, rel, read⟩ := head
    refine .cons ⟨target, rel, ?_⟩ ih
    apply ExpressionRead.convExpr_preserves growth ?_ _ target read
    intro index value found
    rw [ExpressionRead.blockReader_tbl] at found
    simp at found

theorem RootsRead.append {reader : MemberReader md} {related : Ix.Expr → CExpr md → Prop}
    {sources sources' : List Ix.Expr} {roots roots' : List Ixon.Expr}
    (first : RootsRead reader related sources roots) (second : RootsRead reader related sources' roots') :
    RootsRead reader related (sources ++ sources') (roots ++ roots') :=
  by
    induction first with
    | nil => exact second
    | cons head _ ih => exact .cons head ih

/-- **The emitted record reads its roots as the compiler's in-flight reader
read the payload's roots**: a successful build over the block's tables
keeps the payload but its roots, and transfers every root-by-root relation
to the built constant's actual member reader (with the block's blobs
overlaid on the context's, as the compiler's reader has them). -/
theorem build_read (context : Ctx md) (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md)))
    (state : Ix.CompileM.BlockState) (limits : Ix.Sharing.Exact.Limits) (info : Ixon.ConstantInfo)
    (out : Ixon.Constant)
    (ran : Ix.CompileM.buildConstantWithSharing limits info state.refs state.univs = .ok out)
    {related : Ix.Expr → CExpr md → Prop} {sources : List Ix.Expr}
    (holds : RootsRead (ExpressionRead.blockReader context param self state) related sources
      (Ix.CompileM.constantInfoRootExprs info).toList) :
    erase out.info = erase info ∧
      RootsRead (MemberReader.mk' (ExpressionRead.withBlockBlobs context state) out param self) related sources
        (Ix.CompileM.constantInfoRootExprs out.info).toList := by
  obtain ⟨erased, _, _, reads⟩ := build_roots limits info state.refs state.univs out ran
  refine ⟨erased, RootsRead.transfer ?_ holds⟩
  have same := congrArg Array.toList (reads (ExpressionRead.withBlockBlobs context state) param self)
  simp only [Array.toList_map] at same
  rw [same]
  apply List.map_congr_left
  intro root _
  exact unshared_read context param self state info root

end Ix.CompileCert.SharingRoots
