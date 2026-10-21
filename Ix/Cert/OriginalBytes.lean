import Ix.Cert.Resolution
import Ix.Cert.Unchanged
import Ix.CompileCert.PreseedInsertion
import Batteries.Tactic.OpenPrivate

open private Ix.AuxGen.findSorted?.go from Ix.AuxGen.Report

/-! # Original-form identity on bytes (B9d)

An auxiliary table's identical verdict comes from an actual true identity
row, never from a tail's admission verdict. The promotion's true row records
the bytes it compared: a singleton, or a projection together with the
original-form block. These facts survive extension of the byte store; no
address equality is used to infer byte equality.

`reach_rows` carries the original-form compile witness and the compared
bytes through every driver outcome. `compileEnvFold_identity` follows them
through clique rows and serialization. Check15 then identifies the final
published address (`compileReport_identical`); `unchanged_original` restores
B9a's byte-level conclusion for an unchanged original-form record. These
are byte-provenance claims, not a semantic theorem for changed code.
-/

namespace Ix.Cert.OriginalBytes

open Ix.AuxGen
open Ix.CompileM

local instance : LawfulBEq ByteArray where
  eq_of_beq := (Ix.CompileCert.PreseedInsertion.bytes_beq_iff _ _).mp
  rfl := (Ix.CompileCert.PreseedInsertion.bytes_beq_iff _ _).mpr rfl

theorem find_go_origin {α : Type} (xs : Array α) (key : α → Ix.Name) (n : Ix.Name) :
    ∀ fuel lo hi (x : α), Ix.AuxGen.findSorted?.go xs key n lo hi fuel = some x →
      x ∈ xs ∧ Ix.Name.cmpRaw n (key x) = .eq := by
  intro fuel
  induction fuel with
  | zero => intro lo hi x h; simp [Ix.AuxGen.findSorted?.go] at h
  | succ fuel ih =>
    intro lo hi x h
    unfold Ix.AuxGen.findSorted?.go at h
    split at h
    · cases found : xs[(lo + hi) / 2]? with
      | none => simp [found] at h
      | some value =>
        simp only [found] at h
        cases order : Ix.Name.cmpRaw n (key value) with
        | lt => exact ih _ _ x (by simpa [order] using h)
        | gt => exact ih _ _ x (by simpa [order] using h)
        | eq =>
          simp only [order, Option.some.injEq] at h
          subst x
          exact ⟨Array.mem_of_getElem? found, order⟩
    · cases h

theorem find_origin {α : Type} {xs : Array α} {key : α → Ix.Name} {n : Ix.Name} {x : α}
    (h : findSorted? xs key n = some x) : x ∈ xs ∧ n = key x := by
  obtain ⟨mem, same⟩ := find_go_origin xs key n _ _ _ _ h
  exact ⟨mem, Ix.CompileCert.Canon.cmpRaw_eq_iff.mp same⟩

theorem sorted_mem {β : Type} {xs : Array (Ix.Name × β)} {x : Ix.Name × β}
    (h : x ∈ sortByName xs) : x ∈ xs := by
  suffices inside : ∀ y ∈ sortByName xs, y ∈ xs from inside x h
  unfold sortByName
  simp only [Id.run]
  refine Resolution.loop_bind
    (P := fun out : Array (Ix.Name × β) => ∀ y ∈ out, y ∈ xs)
    (I := fun out : Array (Ix.Name × β) => ∀ y ∈ out, y ∈ xs)
    _ _ _ _ ?_ ?_ ?_
  · intro y hy; simp at hy
  · intro e he out keep
    have own : e ∈ xs := Ix.CompileCert.Canon.mem_qsort.mp he
    split
    · split
      · intro y hy
        rcases Array.mem_push.mp hy with hy | rfl
        · exact keep y hy
        · exact own
      · exact keep
    · intro y hy
      rcases Array.mem_push.mp hy with hy | rfl
      · exact keep y hy
      · exact own
  · intro out keep
    exact keep

theorem table_identical_origin (identity : Array (Ix.Name × Bool × Address))
    (generated : Array (Ix.Name × GeneratedKind)) (admitted : Array (Ix.Name × AuxVerdict))
    (exempt : Array (Ix.Name × String)) (display : Array (Ix.Name × Ix.Name)) (n : Ix.Name)
    (h : (AuxTable.ofFacts identity generated admitted exempt display).identical n = true) :
    ∃ a, (n, true, a) ∈ identity := by
  let kinds := sortByName generated
  let checked (n : Ix.Name) : AuxVerdict :=
    match findByName? (sortByName exempt) n with
    | some why => .exempt why
    | none =>
      match findByName? (sortByName admitted) n with
      | some .identical => .refused AuxTable.admittedIdenticalReason
      | some v => v
      | none => .refused AuxTable.lateReason
  have not_identical (name : Ix.Name) : checked name ≠ .identical := by
    cases he : findByName? (sortByName exempt) name with
    | some why => simp [checked, he]
    | none =>
      cases ha : findByName? (sortByName admitted) name with
      | none => simp [checked, he, ha]
      | some verdict => cases verdict <;> simp [checked, he, ha]
  let promoted : Array (Ix.Name × AuxRow) := identity.map fun (name, same, a) =>
    (name, { name := name, kind := (findByName? kinds name).getD .other,
             verdict := if same then .identical else checked name, addr := some a })
  let displayed : Array (Ix.Name × AuxRow) := display.map fun (name, d) =>
    (d, { name := d, kind := (findByName? kinds name).getD .other, verdict := checked name })
  unfold AuxTable.identical AuxTable.verdict? at h
  cases found : findSorted? (AuxTable.ofFacts identity generated admitted exempt display).rows
      (·.name) n with
  | none => simp [found] at h
  | some row =>
    have verdict : row.verdict = .identical := by
      rw [found] at h
      change (row.verdict == AuxVerdict.identical) = true at h
      cases hv : row.verdict
      all_goals first | rfl | (rw [hv] at h; change false = true at h; cases h)
    obtain ⟨mem, named⟩ := find_origin found
    change row ∈ (sortByName (promoted ++ displayed)).map Prod.snd at mem
    obtain ⟨pair, hp, hpRow⟩ := Array.mem_map.mp mem
    have hp := sorted_mem hp
    rcases Array.mem_append.mp hp with hp | hp
    · obtain ⟨⟨name, same, a⟩, hi, eq⟩ := Array.mem_map.mp hp
      subst pair
      dsimp only [promoted] at hpRow
      subst row
      dsimp only at named verdict
      subst n
      cases same with
      | false => exact False.elim (not_identical name verdict)
      | true => exact ⟨a, hi⟩
    · obtain ⟨⟨name, d⟩, _, eq⟩ := Array.mem_map.mp hp
      subst pair
      dsimp only [displayed] at hpRow
      subst row
      exact False.elim (not_identical name verdict)

/-- What the promotion compared: a singleton's bytes, or a projection's
bytes together with its original-form block's bytes. -/
def Compared (store : Address → Option ByteArray) (lo : Ix.Name) (result : BlockResult)
    (name : Ix.Name) (address : Address) : Prop :=
  (result.projections.isEmpty = true ∧ name = lo ∧ store address = some result.blockBytes) ∨
    ∃ projection metadata, (name, projection, metadata) ∈ result.projections ∧
      store address = some (Ixon.ser projection) ∧ store result.blockAddr = some result.blockBytes

theorem Compared.mono {before after : Address → Option ByteArray} {lo name : Ix.Name}
    {result : BlockResult} {address : Address} (h : Compared before lo result name address)
    (keeps : ∀ a b, before a = some b → after a = some b) : Compared after lo result name address := by
  rcases h with ⟨empty, named, bytes⟩ | ⟨projection, metadata, member, bytes, block⟩
  · exact .inl ⟨empty, named, keeps _ _ bytes⟩
  · exact .inr ⟨projection, metadata, member, keeps _ _ bytes, keeps _ _ block⟩

theorem originalIdentities_true {cenv : CompileEnv} {lo name : Ix.Name} {result : BlockResult}
    {address : Address} (h : (name, true, address) ∈ originalIdentities cenv lo result) :
    Compared cenv.constants.get? lo result name address := by
  unfold originalIdentities at h
  split at h
  · rename_i empty
    cases named : cenv.nameToNamed.get? lo with
    | none => simp only [named, Option.map_none] at h; simp at h
    | some row =>
      simp only [named, Option.map_some, Array.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, same, rfl⟩ := h
      exact .inl ⟨empty, rfl, beq_iff_eq.mp same.symm⟩
  · obtain ⟨⟨n, projection, metadata⟩, member, equal⟩ := Array.mem_filterMap.mp h
    cases named : cenv.nameToNamed.get? n with
    | none => simp only [named, Option.map_none] at equal; cases equal
    | some row =>
      simp only [named, Option.map_some, Option.some.injEq, Prod.mk.injEq] at equal
      obtain ⟨rfl, same, rfl⟩ := equal
      obtain ⟨block, bytes⟩ := Bool.and_eq_true_iff.mp same
      exact .inr ⟨projection, metadata, member, beq_iff_eq.mp bytes, beq_iff_eq.mp block⟩


open Ix.Cert.Resolution

def Rows (F : Ix.Name → BlockResult → Prop) (c : CompileEnv) : Prop :=
  ∀ n a, (n, true, a) ∈ c.auxReport.identity →
    ∃ lo result, F lo result ∧ Compared c.constants.get? lo result n a

theorem Rows.mono {F : Ix.Name → BlockResult → Prop} {c c' : CompileEnv}
    (h : Rows F c) (same : c'.auxReport.identity = c.auxReport.identity)
    (keeps : ∀ a b, c.constants.get? a = some b → c'.constants.get? a = some b) : Rows F c' := by
  intro n a member
  rw [same] at member
  obtain ⟨lo, result, witness, bytes⟩ := h n a member
  exact ⟨lo, result, witness, bytes.mono keeps⟩

theorem Rows.of_eq {F : Ix.Name → BlockResult → Prop} {c c' : CompileEnv}
    (h : Rows F c) (same : c'.auxReport.identity = c.auxReport.identity := by rfl)
    (store : c'.constants = c.constants := by rfl) : Rows F c' :=
  h.mono same (by intro a b hb; rw [store]; exact hb)

theorem addBlock_identity (r : CompileReport) (key : Ix.Name) (b : BlockReport) :
    (r.addBlock key b).identity = r.identity := by
  unfold CompileReport.addBlock
  split <;> split <;> split <;> split <;> split <;> split <;> rfl

set_option hygiene false in
local macro "identity_tail" initial:term : tactic => `(tactic| (
  refine loop_bind (P := fun d : DriverAcc => d.cenv.auxReport.identity = acc.cenv.auxReport.identity)
    (I := fun c : CompileEnv => c.auxReport.identity = acc.cenv.auxReport.identity)
    _ _ _ _ $initial (by intro _ _ s hs; exact hs) ?_
  intro L hL
  refine loop_bind (P := fun d : DriverAcc => d.cenv.auxReport.identity = acc.cenv.auxReport.identity)
    (I := fun c : CompileEnv => c.auxReport.identity = acc.cenv.auxReport.identity)
    _ _ _ _ hL (by intro _ _ s hs; split <;> exact hs) ?_
  intro L' hL'
  split
  · refine loop_bind (P := fun d : DriverAcc => d.cenv.auxReport.identity = acc.cenv.auxReport.identity)
      (I := fun c : CompileEnv => c.auxReport.identity = acc.cenv.auxReport.identity)
      _ _ _ _ ?_ ?_ ?_
    · exact (addBlock_identity _ _ _).trans hL'
    · intro cls _ s hs
      exact forIn_inv_array (fun c : CompileEnv => c.auxReport.identity = acc.cenv.auxReport.identity)
        _ cls (by intro _ _ s hs; exact hs) s hs
    · intro L'' hL''
      refine loop_bind (P := fun d : DriverAcc => d.cenv.auxReport.identity = acc.cenv.auxReport.identity)
        (I := fun _ : Array Ix.Name => True) _ _ _ _ trivial (by intros; trivial) ?_
      intro _ _; exact hL''
  · refine loop_bind (P := fun d : DriverAcc => d.cenv.auxReport.identity = acc.cenv.auxReport.identity)
      (I := fun _ : Array Ix.Name => True) _ _ _ _ trivial (by intros; trivial) ?_
    intro _ _; exact (addBlock_identity _ _ _).trans hL'))

theorem mergeCompiledBlock_identity (acc : DriverAcc) (lo : Ix.Name) (result : BlockResult)
    (cache : BlockState) (published : Ix.Compile.Pass.Published) :
    (mergeCompiledBlock acc lo result cache published).cenv.auxReport.identity = acc.cenv.auxReport.identity := by
  unfold mergeCompiledBlock
  simp only [Id.run]
  split
  · split <;> identity_tail rfl
  · refine loop_bind (P := fun d : DriverAcc => d.cenv.auxReport.identity = acc.cenv.auxReport.identity)
      (I := fun c : CompileEnv => c.auxReport.identity = acc.cenv.auxReport.identity)
      _ _ _ _ rfl (by intro _ _ s hs; split <;> exact hs) ?_
    intro L hL
    identity_tail hL

theorem failAuxPromotion_rows {F : Ix.Name → BlockResult → Prop} {acc : DriverAcc}
    (h : Rows F acc.cenv) (all : Ix.Set Ix.Name) (msg : String) :
    Rows F (failAuxPromotion acc all msg).cenv := by
  unfold failAuxPromotion
  simp only [Id.run]
  refine loop_bind_set (P := fun d : DriverAcc => Rows F d.cenv)
    (I := fun d : DriverAcc => Rows F d.cenv) _ _ _ _ h ?_ ?_
  · intro _ s hs; exact hs.of_eq
  · intro L hL; exact hL

theorem promoteAuxWrites_identity (cenv : CompileEnv) (name : Ix.Name) (origAddr : Address)
    (origMeta : Ixon.ConstantMeta) :
    (promoteAuxWrites cenv name origAddr origMeta).auxReport.identity = cenv.auxReport.identity := by
  unfold promoteAuxWrites
  simp only [Id.run]
  split <;> split <;> rfl

theorem promoteOriginalWrites_rows {F : Ix.Name → BlockResult → Prop} {acc : DriverAcc}
    {lo : Ix.Name} {result : BlockResult} (cache : BlockState) (old : Rows F acc.cenv)
    (witness : F lo result) : Rows F (promoteOriginalWrites acc lo result cache).cenv := by
  unfold promoteOriginalWrites
  simp only [Id.run]
  refine loop_bind (P := fun d : DriverAcc => Rows F d.cenv)
    (I := fun s : DriverAcc => s.cenv.auxReport.identity = acc.cenv.auxReport.identity ∧
      ∀ a b, acc.cenv.constants.get? a = some b → s.cenv.constants.get? a = some b)
    _ _ _ _ ⟨rfl, fun _ _ h => h⟩ ?_ ?_
  · intro x _ s hs
    exact ⟨(promoteAuxWrites_identity _ _ _ _).trans hs.1,
      fun a b hb => (promoteAuxWrites_step _ _ _ _ (fun _ _ _ => True)).1.1 a b (hs.2 a b hb)⟩
  · intro L hL n a member
    change (n, true, a) ∈ (L.cenv.auxReport.addIdentity (originalIdentities acc.cenv lo result)).identity at member
    unfold CompileReport.addIdentity at member
    split at member
    · obtain ⟨key, r, hw, hb⟩ := old n a (hL.1 ▸ member)
      exact ⟨key, r, hw, hb.mono hL.2⟩
    · rcases Array.mem_append.mp member with member | member
      · obtain ⟨key, r, hw, hb⟩ := old n a (hL.1 ▸ member)
        exact ⟨key, r, hw, hb.mono hL.2⟩
      · exact ⟨lo, result, witness, (originalIdentities_true member).mono hL.2⟩

theorem promoteRemainingWrites_rows {F : Ix.Name → BlockResult → Prop} {acc : DriverAcc}
    (h : Rows F acc.cenv) (all : Ix.Set Ix.Name) : Rows F (promoteRemainingWrites acc all).1.cenv := by
  unfold promoteRemainingWrites
  simp only [Id.run]
  refine loop_bind_set (P := fun d : DriverAcc × Array Ix.Name => Rows F d.1.cenv)
    (I := fun d : DriverAcc × Array Ix.Name => Rows F d.1.cenv) _ _ _ _ h ?_ ?_
  · intro name s hs
    split
    · exact hs
    · split <;> exact hs.of_eq
  · intro L hL; exact hL

theorem finishAuxPromotion_rows {F : Ix.Name → BlockResult → Prop} {acc : DriverAcc}
    (old : Rows F acc.cenv) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (original : Option (BlockResult × BlockState))
    (allowed : ∀ result cache, original = some (result, cache) → F lo result) :
    Rows F (finishAuxPromotion acc lo all original).1.cenv := by
  have tail : ∀ o : Option (BlockResult × BlockState),
      (∀ result cache, o = some (result, cache) → F lo result) →
      Rows F (promoteRemainingWrites (match o with
        | some (result, cache) => promoteOriginalWrites acc lo result cache
        | none => acc) all).1.cenv := by
    intro o ho
    cases o with
    | none => exact promoteRemainingWrites_rows old all
    | some p =>
      obtain ⟨result, cache⟩ := p
      exact promoteRemainingWrites_rows (promoteOriginalWrites_rows cache old (ho _ _ rfl)) all
  unfold finishAuxPromotion
  simp only [Id.run]
  split
  · rename_i result cache
    split
    · exact failAuxPromotion_rows old all _
    · split
      · exact failAuxPromotion_rows old all _
      · refine loop_bind (P := fun r : DriverAcc × Array Ix.Name × Bool => Rows F r.1.cenv)
          (I := fun s : Option (DriverAcc × Array Ix.Name × Bool) × PUnit =>
            s.1 = none ∨ ∃ msg, s.1 = some (failAuxPromotion acc all msg, #[], true))
          _ _ _ _ (.inl rfl) ?_ ?_
        · intro name _ s _
          split
          · exact .inr ⟨_, rfl⟩
          · exact .inl rfl
        · intro L hL
          rcases hL with h | ⟨msg, h⟩
          · simp only [h]
            exact promoteRemainingWrites_rows (promoteOriginalWrites_rows cache old (allowed _ _ rfl)) all
          · simp only [h]
            exact failAuxPromotion_rows old all msg
  · split
    · exact failAuxPromotion_rows old all _
    · refine loop_bind (P := fun r : DriverAcc × Array Ix.Name × Bool => Rows F r.1.cenv)
        (I := fun s : Option (DriverAcc × Array Ix.Name × Bool) × PUnit =>
          s.1 = none ∨ ∃ msg, s.1 = some (failAuxPromotion acc all msg, #[], true))
        _ _ _ _ (.inl rfl) ?_ ?_
      · intro name _ s _
        split
        · exact .inr ⟨_, rfl⟩
        · exact .inl rfl
      · intro L hL
        rcases hL with h | ⟨msg, h⟩
        · simp only [h]
          exact tail original allowed
        · simp only [h]
          exact failAuxPromotion_rows old all msg

theorem mergeCompiledBlock_rows {F : Ix.Name → BlockResult → Prop} {acc : DriverAcc}
    (old : Rows F acc.cenv) {lo : Ix.Name} {result : BlockResult}
    {cache : BlockState} {published : Ix.Compile.Pass.Published}
    (check : checkCompiledBlock acc.cenv lo result cache published = .ok ()) :
    Rows F (mergeCompiledBlock acc lo result cache published).cenv :=
  old.mono (mergeCompiledBlock_identity _ _ _ _ _)
    (mergeCompiledBlock_step _ _ _ _ _ (checkCompiledBlock_content check)).1.1

theorem rows_pure {F : Ix.Name → BlockResult → Prop} {d : DriverAcc} {names : Array Ix.Name}
    {failed : Bool} (h : Rows F d.cenv) :
    Rows F (pure (d, names, failed) : Id (DriverAcc × Array Ix.Name × Bool)).1.cenv := h

theorem rows_loop_names {F : Ix.Name → BlockResult → Prop} {α : Type} (xs : Array α)
    (init : Array Ix.Name) (f : α → Array Ix.Name → Id (ForInStep (Array Ix.Name)))
    (k : Array Ix.Name → Id (DriverAcc × Array Ix.Name × Bool)) (cont : ∀ L, Rows F (k L).1.cenv) :
    Rows F (forIn (m := Id) xs init f >>= k).1.cenv :=
  loop_bind xs init f k (fun _ => True) (fun r => Rows F r.1.cenv)
    trivial (fun _ _ _ _ => trivial) (fun L _ => cont L)

theorem rows_loop_acc {F : Ix.Name → BlockResult → Prop} {α : Type} (xs : Array α)
    (init : DriverAcc) (f : α → DriverAcc → Id (ForInStep DriverAcc))
    (k : DriverAcc → Id DriverAcc) (hinit : Rows F init.cenv)
    (body : ∀ x ∈ xs, ∀ s, Rows F s.cenv → Rows F (f x s).value.cenv)
    (cont : ∀ L, Rows F L.cenv → Rows F (k L).cenv) :
    Rows F (forIn (m := Id) xs init f >>= k).cenv :=
  loop_bind xs init f k (fun d => Rows F d.cenv) (fun d => Rows F d.cenv) hinit body cont

theorem rows_loop_ret {F : Ix.Name → BlockResult → Prop} {α : Type} (xs : Array α)
    (init : DriverAcc) (f : α → DriverAcc → Id (ForInStep DriverAcc))
    (k : DriverAcc → Id (DriverAcc × Array Ix.Name × Bool)) (hinit : Rows F init.cenv)
    (body : ∀ x ∈ xs, ∀ s, Rows F s.cenv → Rows F (f x s).value.cenv)
    (cont : ∀ L, Rows F L.cenv → Rows F (k L).1.cenv) :
    Rows F (forIn (m := Id) xs init f >>= k).1.cenv :=
  loop_bind xs init f k (fun d => Rows F d.cenv) (fun d => Rows F d.1.cenv) hinit body cont

local macro "rows_keep_loop" : tactic => `(tactic|
  refine rows_loop_acc _ _ _ _ ?_ (by intro _ _ s hs; exact hs.of_eq) fun _ h => h)

theorem apply_compiled_rows {F : Ix.Name → BlockResult → Prop} {acc : DriverAcc}
    (old : Rows F acc.cenv) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (result : BlockResult) (cache : BlockState) (published : Ix.Compile.Pass.Published) :
    Rows F (applyAuxBlockOutcome acc lo all (.compiled result cache published)).1.cenv := by
  unfold applyAuxBlockOutcome
  simp only [Id.run]
  split
  · refine rows_pure ?_
    rows_keep_loop
    exact old
  · rename_i check
    have merged := mergeCompiledBlock_rows old check
    split
    · exact rows_loop_names _ _ _ _ fun _ => rows_pure merged
    · refine rows_loop_names _ _ _ _ fun _ => ?_
      exact rows_loop_names _ _ _ _ fun _ => rows_pure merged

local macro "rows_prom_tail" allowed:ident x:tactic : tactic => `(tactic| (
  split
  · refine rows_pure (failAuxPromotion_rows ?_ _ _); $x
  · split
    · refine rows_pure (failAuxPromotion_rows ?_ _ _); $x
    · split
      · refine rows_pure (finishAuxPromotion_rows ?_ _ _ _ $allowed); $x
      · refine rows_pure (finishAuxPromotion_rows ?_ _ _ _ $allowed); $x))

theorem apply_promoted_rows {F : Ix.Name → BlockResult → Prop} {acc : DriverAcc}
    (old : Rows F acc.cenv) (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (cs : Option (Ix.Name × BlockResult × BlockState × Ix.Compile.Pass.Published)) (cn : Array Ix.Name)
    (cf : Option (Array Ix.Name × String)) (im : Option String) (na : Option (BlockResult × BlockState))
    (nf : Option String) (allowed : ∀ result cache, na = some (result, cache) → F lo result) :
    Rows F (applyAuxBlockOutcome acc lo all (.promoted cs cn cf im na nf)).1.cenv := by
  rcases cs with _ | ⟨clo, result, cache, published⟩
  · rcases cf with _ | ⟨names, msg⟩
    · unfold applyAuxBlockOutcome; simp only [Id.run]
      rows_prom_tail allowed (exact old)
    · unfold applyAuxBlockOutcome; simp only [Id.run]
      rows_prom_tail allowed (rows_keep_loop; exact old)
  · rcases cf with _ | ⟨names, msg⟩
    · unfold applyAuxBlockOutcome; simp only [Id.run]
      split
      · rows_prom_tail allowed (rows_keep_loop; exact old)
      · rename_i check
        split
        · refine rows_loop_names _ _ _ _ fun _ => ?_
          refine rows_loop_ret _ _ _ _ (mergeCompiledBlock_rows old check)
            (by intro _ _ s hs; exact hs.of_eq) fun L hL => ?_
          rows_prom_tail allowed (exact hL)
        · refine rows_loop_names _ _ _ _ fun _ => ?_
          refine rows_loop_names _ _ _ _ fun _ => ?_
          refine rows_loop_ret _ _ _ _ (mergeCompiledBlock_rows old check)
            (by intro _ _ s hs; exact hs.of_eq) fun L hL => ?_
          rows_prom_tail allowed (exact hL)
    · unfold applyAuxBlockOutcome; simp only [Id.run]
      split
      · rows_prom_tail allowed (rows_keep_loop; rows_keep_loop; exact old)
      · rename_i check
        split
        · refine rows_loop_names _ _ _ _ fun _ => ?_
          refine rows_loop_ret _ _ _ _ (mergeCompiledBlock_rows ?_ check)
            (by intro _ _ s hs; exact hs.of_eq) fun L hL => ?_
          · rows_keep_loop; exact old
          · rows_prom_tail allowed (exact hL)
        · refine rows_loop_names _ _ _ _ fun _ => ?_
          refine rows_loop_names _ _ _ _ fun _ => ?_
          refine rows_loop_ret _ _ _ _ (mergeCompiledBlock_rows ?_ check)
            (by intro _ _ s hs; exact hs.of_eq) fun L hL => ?_
          · rows_keep_loop; exact old
          · rows_prom_tail allowed (exact hL)

def OutcomeOriginal (F : Ix.Name → BlockResult → Prop) (lo : Ix.Name) : AuxBlockOutcome → Prop
  | .promoted _ _ _ _ original _ => ∀ result cache, original = some (result, cache) → F lo result
  | _ => True

theorem apply_rows {F : Ix.Name → BlockResult → Prop} {acc : DriverAcc}
    (old : Rows F acc.cenv) (lo : Ix.Name) (all : Ix.Set Ix.Name) (outcome : AuxBlockOutcome)
    (allowed : OutcomeOriginal F lo outcome) :
    Rows F (applyAuxBlockOutcome acc lo all outcome).1.cenv := by
  cases outcome with
  | compiled r c p => exact apply_compiled_rows old lo all r c p
  | promoted cs cn cf im na nf => exact apply_promoted_rows old lo all cs cn cf im na nf allowed
  | failed msg =>
    unfold applyAuxBlockOutcome; simp only [Id.run]
    refine rows_pure ?_
    rows_keep_loop; exact old

theorem auxBlockOutcome_original {cenv : CompileEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {cs : Option (Ix.Name × BlockResult × BlockState × Ix.Compile.Pass.Published)}
    {cn : Array Ix.Name} {cf : Option (Array Ix.Name × String)} {im nf : Option String}
    {result : BlockResult} {cache : BlockState}
    (h : auxBlockOutcome cenv lo all = .promoted cs cn cf im (some (result, cache)) nf) :
    compileConstNoAuxPure cenv lo all = .ok (result, cache) := by
  unfold auxBlockOutcome at h
  simp only [Id.run] at h
  split at h
  · revert h
    refine loop_bind_set _ _ _ _ (fun _ => True)
      (fun o : AuxBlockOutcome => o = .promoted cs cn cf im (some (result, cache)) nf →
        compileConstNoAuxPure cenv lo all = .ok (result, cache)) trivial
      (fun _ _ _ => trivial) ?_
    intro L _ h'
    repeat' (first | (focus (cases h'; done)) | split at h')
    all_goals (cases h'; assumption)
  · split at h <;> cases h

theorem auxBlockOutcome_originals {F : Ix.Name → BlockResult → Prop} (cenv : CompileEnv)
    (lo : Ix.Name) (all : Ix.Set Ix.Name)
    (witness : ∀ result cache, compileConstNoAuxPure cenv lo all = .ok (result, cache) → F lo result) :
    OutcomeOriginal F lo (auxBlockOutcome cenv lo all) := by
  generalize ho : auxBlockOutcome cenv lo all = outcome
  cases outcome with
  | compiled => trivial
  | failed => trivial
  | promoted cs cn cf im na nf =>
    intro result cache same
    subst na
    exact witness result cache (auxBlockOutcome_original ho)

/-- An original-form compile against a state reached by the actual driver,
for a condensation block under its own key. -/
def Original (blocks : Ix.CondensedBlocks) (init : DriverAcc) (lo : Ix.Name) (result : BlockResult) : Prop :=
  ∃ (snapshot : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name) (cache : BlockState),
    Reach blocks init snapshot ∧ blocks.blocks.get? rep = some all ∧ lo = blockKey rep all ∧
      compileConstNoAuxPure snapshot.cenv lo all = .ok (result, cache)

theorem reach_rows {blocks : Ix.CondensedBlocks} {init acc : DriverAcc}
    (empty : init.cenv.auxReport.identity = #[]) (reached : Reach blocks init acc) :
    Rows (Original blocks init) acc.cenv := by
  induction reached with
  | init =>
    intro n a member
    rw [empty] at member
    simp at member
  | @step snap acc rep all hsnap hacc follows member _ ih =>
    apply apply_rows ih
    apply auxBlockOutcome_originals
    intro result cache compiled
    exact ⟨snap, rep, all, cache, hsnap, member, rfl, compiled⟩

open Ix.Cert.Schedule in
/-- The report in a successful driver result is precisely the waves' report.
Clique rows, assembly and the final environment reset add no identity rows. -/
theorem compileEnvFold_report {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {dbg : Bool}
    {unmaterialized : Nat} {sharingLimits : Ix.Sharing.Exact.Limits} {width : Nat} {ixe : Ixon.Env}
    {bytes : Nat} {cenv : CompileEnv}
    (h : compileEnvFold env blocks dbg unmaterialized sharingLimits width = .ok (ixe, bytes, cenv)) :
    ∃ (cenv₀ : CompileEnv) (sched : FoldSchedule) (st : FoldState) (rows : BlockState),
      (FoldState.init cenv₀ blocks sched).acc.cenv.auxReport.identity = #[] ∧
      (FoldState.init cenv₀ blocks sched).acc.cenv.env = { consts := {}, fallback? := some env.get? } ∧
      ((FoldState.init cenv₀ blocks sched).acc.cenv.p3Cliques,
        (FoldState.init cenv₀ blocks sched).acc.cenv.p3CliqueRoots) =
        (Ix.Compile.Pass.Clique.scheduleCliques { consts := {}, fallback? := some env.get? } blocks).2 ∧
      foldWavesSeq blocks sched (blocks.blocks.size + 1) (FoldState.init cenv₀ blocks sched) = .ok st ∧
      cenv.auxReport.identity = st.acc.cenv.auxReport.identity ∧
      ixe = (assembleEnv (mergeRows st.acc rows)).1 := by
  rw [compileEnvFold_eq_seq] at h
  unfold compileEnvFoldSeq compileEnvFoldWithSourceSeq at h
  generalize missingBlockRefs? blocks = missing at h
  generalize validateInductiveFlags env = flags at h
  generalize validateMutualSafety env blocks = safety at h
  cases missing <;> cases flags <;> cases safety <;>
    simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at h <;> try cases h
  generalize Ix.Compile.Pass.Clique.scheduleCliques { consts := {}, fallback? := some env.get? } blocks = sc at h ⊢
  generalize hr : foldWavesSeq _ _ _ _ = r at h
  cases r with
  | error => cases h
  | ok st =>
    simp only at h
    unfold emitRows at h
    generalize hc : Ix.Compile.Pass.cliqueRows st.acc.cenv = c at h
    cases c with
    | error => cases h
    | ok rows =>
      simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact ⟨_, _, st, rows, rfl, rfl, rfl, hr, rfl, rfl⟩

/-- The bytes physically stored in the final environment, independent of a
lazy record's decode cache. -/
def storedBytes (ixe : Ixon.Env) (address : Address) : Option ByteArray :=
  (ixe.consts.get? address).map Ixon.LazyConstant.rawBytes

open Ix.Cert.Schedule in
theorem compileEnvFold_identity {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {dbg : Bool}
    {unmaterialized : Nat} {sharingLimits : Ix.Sharing.Exact.Limits} {width : Nat} {ixe : Ixon.Env}
    {bytes : Nat} {cenv : CompileEnv}
    (h : compileEnvFold env blocks dbg unmaterialized sharingLimits width = .ok (ixe, bytes, cenv)) :
    ∃ (cenv₀ : CompileEnv) (sched : FoldSchedule),
      (FoldState.init cenv₀ blocks sched).acc.cenv.env = { consts := {}, fallback? := some env.get? } ∧
      ((FoldState.init cenv₀ blocks sched).acc.cenv.p3Cliques,
        (FoldState.init cenv₀ blocks sched).acc.cenv.p3CliqueRoots) =
        (Ix.Compile.Pass.Clique.scheduleCliques { consts := {}, fallback? := some env.get? } blocks).2 ∧
      ∀ n a, (n, true, a) ∈ cenv.auxReport.identity →
        ∃ lo result, Original blocks (FoldState.init cenv₀ blocks sched).acc lo result ∧
          Compared (storedBytes ixe) lo result n a := by
  obtain ⟨cenv₀, sched, st, rows, empty, source, cliques, folded, report, assembled⟩ :=
    compileEnvFold_report h
  refine ⟨cenv₀, sched, source, cliques, ?_⟩
  intro n a member
  rw [report] at member
  obtain ⟨lo, result, original, compared⟩ :=
    reach_rows empty (foldWavesSeq_reach _ _ _ folded Reach.init) n a member
  refine ⟨lo, result, original, compared.mono ?_⟩
  intro address value stored
  unfold storedBytes
  rw [assembled, assembleEnv_consts _ (mergeRows_constants stored)]
  simp [Ixon.LazyConstant.rawBytes]

/-- **B9d: an identical verdict describes the final published bytes.** The
original-form result came from the driver's condensation block and reached
snapshot. For a projection, both its own bytes and the original block's
bytes agree. Check15 supplies the final published address; content checks
preserve bytes. No address-to-byte injectivity premise is needed. -/
theorem compileReport_identical {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (compiled : compileReport env = .ok (ixe, failures)) {name : Ix.Name}
    (identical : (compileTable env).identical name = true) :
    ∃ (snapshot : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name) (result : BlockResult)
      (cache : BlockState) (address : Address),
      snapshot.cenv.env = { consts := {}, fallback? := some (Ix.Environment.get? { consts := env.consts }) } ∧
      (compileBlocks env).blocks.get? rep = some all ∧
      compileConstNoAuxPure snapshot.cenv (blockKey rep all) all = .ok (result, cache) ∧
      (ixe.named.get? name).map (·.addr) = some address ∧
      Compared (storedBytes ixe) (blockKey rep all) result name address := by
  obtain ⟨cenv, unchecked, -, published⟩ := identityRowsAgree compiled
  have table : cenv.auxReport.table.identical name = true := by
    simpa only [compileTable, unchecked] using identical
  obtain ⟨address, member⟩ := table_identical_origin _ _ _ _ _ name table
  obtain ⟨bytes, folded⟩ := compileUnchecked_fold unchecked
  obtain ⟨cenv₀, sched, source, -, rows⟩ := compileEnvFold_identity folded
  obtain ⟨lo, result, original, compared⟩ := rows name address member
  obtain ⟨snapshot, rep, all, cache, reached, block, rfl, originalCompile⟩ := original
  exact ⟨snapshot, rep, all, result, cache, address, (reach_env reached).trans source,
    block, originalCompile, published name address (Array.mem_toList_iff.mpr member), compared⟩

/-- B9a's `Unchanged.original` now yields original bytes at the final
published address, rather than stopping at the table's verdict. -/
theorem unchanged_original {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (compiled : compileReport env = .ok (ixe, failures)) {name : Ix.Name}
    (unchanged : Unchanged.Unchanged { consts := env.consts } (compileBlocks env) (compileTable env) ixe name)
    {named : Ixon.Named} (member : (name, named) ∈ ixe.named.toList)
    (original : named.original.isSome = true)
    (input : (Ix.Environment.get? { consts := env.consts } name).isSome = true) :
    ∃ (snapshot : DriverAcc) (rep : Ix.Name) (all : Ix.Set Ix.Name) (result : BlockResult) (cache : BlockState),
      snapshot.cenv.env = { consts := {}, fallback? := some (Ix.Environment.get? { consts := env.consts }) } ∧
      (compileBlocks env).blocks.get? rep = some all ∧
      compileConstNoAuxPure snapshot.cenv (blockKey rep all) all = .ok (result, cache) ∧
      Compared (storedBytes ixe) (blockKey rep all) result name named.addr := by
  have published : ixe.named.get? name = some named := by
    rw [Std.HashMap.get?_eq_getElem?]
    exact (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp member).2
  obtain ⟨snapshot, rep, all, result, cache, address, source, block, origCompile, final, bytes⟩ :=
    compileReport_identical compiled (unchanged.original name named member BEq.rfl original input)
  rw [published] at final
  simp only [Option.map_some, Option.some.injEq] at final
  subst address
  exact ⟨snapshot, rep, all, result, cache, source, block, origCompile, bytes⟩

end Ix.Cert.OriginalBytes
