import IxVMRefinement.Assembly.SubStore
import IxVMRefinement.RoleVal.CommittedData
import IxVMRefinement.RoleVal.ReaderTable
import Ix.Cert.EvidenceTransfer

/-! # Role-prelude bridge (`RolePreludeBridge`)

Discharges the committed-fallback and role-table obligations of `RolePreludeInputs`:

* `fallback_not_padding`: every address in `pre.records ++ pre.evidence` is distinct from
  `Ix.HostAdmission.Merkle.padding`;
* `prelude_in_bound_of_preludeFor`: for any `t` with `preludeFor t = .ok pre`, every record in
  `pre.records` is either directly bound in `t.bound` to a non-`compilerTrust` prelude role, or is
  an inductive `.muts` block owned by one of its projection records in `pre.records` that is;
* `prelude_in_bindingSeeds_of_check` and `prelude_in_bindingSeeds_of_admitBinding`: upgrades
  `prelude_in_bound_of_preludeFor` unconditionally to `BindingSeeds t` whenever `t.check = .ok ()`
  (in particular under `admitBinding _ b = .ok t`);
* `UncheckedPreludeTableGap` and `rolePreludeInputs`: isolates the single missing `t.check = .ok ()`
  premise on `RolePreludeInputs.prelude_in_bindingSeeds`. -/

namespace IxVM.Refinement.Assembly

open Ix.Kernel (ConstRef Mode Role)
open Ix.Kernel.Reader

/-! ## Non-padding of committed fallback addresses -/

private theorem not_contains_padding :
    IxVM.Refinement.RoleVal.containsAddrFast
      (IxVM.Refinement.RoleVal.committedPreAddrs ++ IxVM.Refinement.RoleVal.committedEvAddrs)
      Ix.HostAdmission.Merkle.padding = false := by
  decide +kernel

/-- Every record `(a, c)` in `pre.records ++ pre.evidence` has non-padding address. -/
theorem fallback_not_padding {md : Mode}
    {t : Ix.Kernel.RoleTable} {pre : Prelude md}
    (hpre : preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records ++ pre.evidence) :
    a ≠ Ix.HostAdmission.Merkle.padding := by
  obtain ⟨hr, he⟩ := Ix.Cert.ReaderFallback.preludeFor_records hpre
  have hrec_eq : pre.records = IxVM.Refinement.RoleVal.committedPrelude := by
    rw [IxVM.Refinement.RoleVal.preludeRecords_eq] at hr
    injection hr with h
    exact h.symm
  obtain ⟨ev, hev_ok, hev_fst, _⟩ := IxVM.Refinement.RoleVal.evidenceRecords_spec
  have hev_eq : pre.evidence = ev := by
    rw [hev_ok] at he
    injection he with h
    exact h.symm
  have ha_mem : a ∈ IxVM.Refinement.RoleVal.committedPreAddrs ++
      IxVM.Refinement.RoleVal.committedEvAddrs := by
    rcases Array.mem_append.mp hmem with h1 | h2
    · rw [hrec_eq] at h1
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨(a, c), Array.mem_toList_iff.mpr h1, rfl⟩)
    · rw [hev_eq] at h2
      refine List.mem_append_right _ ?_
      rw [← hev_fst]
      exact List.mem_map.mpr ⟨(a, c), Array.mem_toList_iff.mpr h2, rfl⟩
  intro hpad
  subst hpad
  have hcont :
      IxVM.Refinement.RoleVal.containsAddrFast
        (IxVM.Refinement.RoleVal.committedPreAddrs ++ IxVM.Refinement.RoleVal.committedEvAddrs)
        Ix.HostAdmission.Merkle.padding = true := by
    rw [IxVM.Refinement.RoleVal.containsAddrFast_eq, List.contains_iff_mem]
    exact ha_mem
  rw [not_contains_padding] at hcont
  cases hcont

/-! ## Finite list pigeonhole for deterministic partial maps -/

private theorem filterMap_len_le {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (l.filterMap f).length ≤ l.length
  | [] => Nat.zero_le _
  | x :: xs => by
    simp only [List.filterMap_cons]
    cases f x with
    | none => exact Nat.le_trans (filterMap_len_le f xs) (Nat.le_succ _)
    | some _ => exact Nat.succ_le_succ (filterMap_len_le f xs)

private theorem erase_len_succ {β : Type} [DecidableEq β] :
    ∀ {W : List β} {x : β}, x ∈ W → (W.erase x).length + 1 = W.length
  | [], _, hx => nomatch hx
  | y :: ys, x, hx => by
    rw [List.erase_cons]
    by_cases h : y == x
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      rcases List.mem_cons.mp hx with hxy | hmem
      · subst hxy
        exact absurd (beq_self_eq_true _) h
      · exact congrArg (· + 1) (erase_len_succ hmem)

private theorem mem_erase_of_ne {β : Type} [DecidableEq β] :
    ∀ {W : List β} {z x : β}, z ≠ x → z ∈ W → z ∈ W.erase x
  | [], _, _, _, hz => nomatch hz
  | y :: ys, z, x, hne, hz => by
    rw [List.erase_cons]
    by_cases hyx : y == x
    · simp only [hyx, ↓reduceIte]
      rcases List.mem_cons.mp hz with rfl | hmem
      · exact absurd (beq_iff_eq.mp hyx) hne
      · exact hmem
    · simp only [hyx, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rcases List.mem_cons.mp hz with rfl | hmem
      · exact .inl rfl
      · exact .inr (mem_erase_of_ne hne hmem)

private theorem nodup_len_le_of_subset {β : Type} [DecidableEq β] :
    ∀ {V W : List β}, V.Nodup → (∀ v ∈ V, v ∈ W) → V.length ≤ W.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, W, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hxW : x ∈ W := hsub x List.mem_cons_self
    have hsub' : ∀ v ∈ xs, v ∈ W.erase x := by
      intro v hv
      have hne : v ≠ x := fun heq => hnd.1 (heq ▸ hv)
      exact mem_erase_of_ne hne (hsub v (List.mem_cons_of_mem _ hv))
    have ih := nodup_len_le_of_subset hnd.2 hsub'
    have hlen := erase_len_succ hxW
    rw [List.length_cons]
    omega

private theorem filterMap_eq_len_all_some {α β : Type} :
    ∀ {l : List α} {g : α → Option β},
      (l.filterMap g).length = l.length → ∀ u ∈ l, ∃ v, g u = some v
  | [], _, _, _, hu => nomatch hu
  | x :: xs, g, hlen, u, hu => by
    rw [List.filterMap_cons, List.length_cons] at hlen
    cases hgx : g x with
    | none =>
      simp only [hgx] at hlen
      have hle := filterMap_len_le g xs
      omega
    | some v =>
      simp only [hgx, List.length_cons] at hlen
      have hlen' : (xs.filterMap g).length = xs.length := by omega
      rcases List.mem_cons.mp hu with rfl | hmem
      · exact ⟨v, hgx⟩
      · exact filterMap_eq_len_all_some hlen' u hmem

private theorem pigeonhole_filterMap {α β : Type} [DecidableEq β]
    {U : List α} {V : List β} {f : α → Option β}
    (hlen : U.length ≤ V.length)
    (hnd : V.Nodup)
    (hsurj : ∀ v ∈ V, ∃ u ∈ U, f u = some v) :
    ∀ u ∈ U, ∃ v ∈ V, f u = some v := by
  let g : α → Option β := fun u =>
    match f u with
    | some v => if v ∈ V then some v else none
    | none => none
  have hsub : ∀ v ∈ V, v ∈ U.filterMap g := by
    intro v hv
    obtain ⟨u, hu, hfu⟩ := hsurj v hv
    refine List.mem_filterMap.mpr ⟨u, hu, ?_⟩
    simp [g, hfu, hv]
  have hle1 : V.length ≤ (U.filterMap g).length := nodup_len_le_of_subset hnd hsub
  have hle2 : (U.filterMap g).length ≤ U.length := filterMap_len_le g U
  have heq : (U.filterMap g).length = U.length := by omega
  intro u hu
  obtain ⟨v, hgu⟩ := filterMap_eq_len_all_some heq u hu
  dsimp only [g] at hgu
  generalize hfu : f u = opt at hgu
  cases opt with
  | none => cases hgu
  | some v' =>
    by_cases hv' : v' ∈ V
    · simp only [hv', ↓reduceIte, Option.some.injEq] at hgu
      subst hgu
      exact ⟨v', hv', hfu⟩
    · simp [hv'] at hgu

/-! ## Kernel-decided classification of the 33 committed prelude records -/

private def validPreRefs : List (ConstRef _root_.Address) :=
  IxVM.Refinement.RoleVal.committedPreludeList.flatMap fun (a, c) =>
    match c.info with
    | .axio _ | .quot _ | .recr _ => [.member a 0]
    | .muts ms =>
      (List.range ms.toList.length).flatMap fun i =>
        match IxVM.Refinement.RoleVal.nth? ms.toList i with
        | some (.indc ind) =>
          .member a i :: (List.range ind.ctors.toList.length).map (fun j => .ctor a i j)
        | _ => []
    | _ => []

private theorem validPreRefs_len :
    validPreRefs.length = Ix.Kernel.preludeShape.flatten.length := by
  decide +kernel

private theorem preludeRoles_nodup :
    Ix.Kernel.preludeShape.flatten.Nodup := by
  decide +kernel

private theorem prelude_role_not_compilerTrust :
    ∀ s ∈ Ix.Kernel.preludeShape.flatten, IxVM.Refinement.compilerTrust s = false := by
  decide +kernel

private def isMutsConst (c : Ixon.Constant) : Bool :=
  match c.info with
  | .muts _ => true
  | _ => false

private def preConstShapeOk (c : Ixon.Constant) : Bool :=
  match c.info with
  | .defn _ => false
  | .muts ms =>
    ms.any (fun | .indc _ => true | _ => false) &&
    !ms.any (fun | .defn _ => true | _ => false) &&
    !ms.any (fun | .recr _ => true | _ => false)
  | _ => true

private theorem committedPre_shapes_ok :
    (IxVM.Refinement.RoleVal.committedPreludeList.all fun (_, c) => preConstShapeOk c) = true := by
  decide +kernel

private def preRowClassified (a : _root_.Address) (c : Ixon.Constant) : Bool :=
  if isMutsConst c then
    IxVM.Refinement.RoleVal.committedPreludeList.any fun (a', c') =>
      !IxVM.Refinement.RoleVal.beqAddrFast a a' &&
      !isMutsConst c' &&
      IxVM.Refinement.RoleVal.beqAddrFast (Ix.Cert.ownerOf a' c') a
  else
    match resolve IxVM.Refinement.RoleVal.preStorePure a with
    | some ref => validPreRefs.any (IxVM.Refinement.RoleVal.beqConstRefFast · ref)
    | none => false

private theorem committedPre_all_classified :
    (IxVM.Refinement.RoleVal.committedPreludeList.all fun (a, c) =>
      preRowClassified a c) = true := by
  decide +kernel

/-! ## Store & `memberKey` helpers on `contextOf t recs [] evs blobs` -/

private theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => nomatch h
  | (k, v) :: tl, a, b, h => by
    rw [List.lookup_cons] at h
    cases hbeq : (a == k) with
    | true =>
      rw [hbeq] at h
      injection h with hv
      subst hv
      rw [beq_iff_eq.mp hbeq]
      exact List.mem_cons_self
    | false =>
      rw [hbeq] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

private theorem prelude_context_store_mem {t : Ix.Kernel.RoleTable}
    {recs evs : Array (_root_.Address × Ixon.Constant)}
    {blobs : List (_root_.Address × ByteArray)}
    {a : _root_.Address} {c : Ixon.Constant}
    (hs : (contextOf (md := .anon) t recs [] evs blobs).store a = some c) :
    (a, c) ∈ recs ++ evs := by
  change ((recordMap recs)[a]? <|> ((recordMap evs)[a]? <|> none)) = some c at hs
  cases h1 : (recordMap recs)[a]? with
  | some c1 =>
    rw [h1] at hs
    injection hs with heq; subst heq
    rw [Ix.Cert.ReaderClosureKeys.recordMap_get] at h1
    exact Array.mem_append_left _ (Array.mem_toList_iff.mp (lookup_mem h1))
  | none =>
    rw [h1] at hs
    cases h2 : (recordMap evs)[a]? with
    | some c2 =>
      rw [h2] at hs
      injection hs with heq; subst heq
      rw [Ix.Cert.ReaderClosureKeys.recordMap_get] at h2
      exact Array.mem_append_right _ (Array.mem_toList_iff.mp (lookup_mem h2))
    | none =>
      rw [h2] at hs
      cases hs

private theorem memberKey_role_exact_of_no_reconstruct {cx : Ctx .anon}
    (hrec_none : ∀ r, cx.reconstruct r = none)
    {ref : ConstRef _root_.Address} {s : Role}
    (h : cx.memberKey ref = .ok (.role s)) :
    cx.roles.names[ref]? = some (.role s) := by
  unfold Ctx.memberKey at h
  cases hn : cx.roles.names[ref]? with
  | some k =>
    rw [hn] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [h]
  | none =>
    exfalso
    rw [hn] at h
    simp only [bind, Except.bind] at h
    cases ha : cx.addressOf ref with
    | error _ => rw [ha] at h; cases h
    | ok a =>
      have hres : resolve cx.store a = some ref := by
        unfold Ctx.addressOf at ha
        cases hk_addr : cx.keys.address[ref]? with
        | some a0 =>
          rw [hk_addr] at ha
          simp only [pure, Except.pure, Except.ok.injEq] at ha
          subst ha
          exact cx.keys.address_sound ref a0 hk_addr
        | none =>
          rw [hk_addr] at ha
          cases hsing : singletonAt cx.store ref with
          | some a0 =>
            rw [hsing] at ha
            simp only [pure, Except.pure, Except.ok.injEq] at ha
            subst ha
            exact Ix.Cert.ReaderKeys.singletonAt_resolves hsing
          | none =>
            rw [hsing, hrec_none ref] at ha
            simp [declined, throw, throwThe, MonadExceptOf.throw] at ha
      rw [ha] at h
      dsimp only at h
      cases hb : cx.keys.byAddress[a]? with
      | some k =>
        rw [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hs := cx.keys.byAddress_sound a (.role s) hb
        unfold keyOfAddress at hs
        rw [hres] at hs
        simp only [Option.bind_eq_bind, Option.bind_some, hn] at hs
        cases hi : Mode.addressId? .anon a <;> simp [hi] at hs
      | none =>
        rw [hb] at h
        cases hi : Mode.addressId? .anon a <;>
          simp [hi, declined, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h

private theorem resolve_preStorePure_eq_context {t : Ix.Kernel.RoleTable}
    {recs evs : Array (_root_.Address × Ixon.Constant)}
    {blobs : List (_root_.Address × ByteArray)}
    (hrecs_list : recs.toList = IxVM.Refinement.RoleVal.committedPreludeList)
    {a : _root_.Address} {c : Ixon.Constant}
    (hc : (a, c) ∈ IxVM.Refinement.RoleVal.committedPreludeList) :
    resolve (contextOf (md := .anon) t recs [] evs blobs).store a =
      resolve IxVM.Refinement.RoleVal.preStorePure a := by
  let cx := contextOf (md := .anon) t recs [] evs blobs
  have hnodup_recs : (recs.toList.map Prod.fst).Nodup := by
    rw [hrecs_list]
    exact IxVM.Refinement.RoleVal.committedPreAddrs_nodup
  have hstore_eq : ∀ {b : _root_.Address}, b ∈ IxVM.Refinement.RoleVal.committedPreAddrs →
      cx.store b = IxVM.Refinement.RoleVal.preStorePure b := by
    intro b hb
    obtain ⟨cb, hcb⟩ := List.mem_map.mp hb
    rcases cb with ⟨b', cb⟩
    dsimp only at hcb
    obtain ⟨hcb_mem, rfl⟩ := hcb
    have hcb_recs : (b', cb) ∈ recs := by
      apply Array.mem_toList_iff.mp
      rwa [hrecs_list]
    have hcx_b : cx.store b' = some cb :=
      Ix.Cert.ReaderClosureKeys.context_input t recs evs [] blobs
        (fun _ => none) (fun _ _ => none) hnodup_recs hcb_recs
    have hpure_b : IxVM.Refinement.RoleVal.preStorePure b' = some cb := by
      rw [IxVM.Refinement.RoleVal.preStorePure_eq]
      exact Ix.Cert.ReaderClosureKeys.lookup_of_nodup
        IxVM.Refinement.RoleVal.committedPreAddrs_nodup hcb_mem
    rw [hcx_b, hpure_b]
  have hclosed_all : IxVM.Refinement.RoleVal.preRefsAndProjClosedBool = true :=
    IxVM.Refinement.RoleVal.preRefsAndProjClosed
  unfold IxVM.Refinement.RoleVal.preRefsAndProjClosedBool at hclosed_all
  have hclosed := List.all_eq_true.mp hclosed_all (a, c) hc
  dsimp only at hclosed
  have hproj_closed := (Bool.and_eq_true_iff.mp hclosed).2
  have hc_recs : (a, c) ∈ recs := by
    apply Array.mem_toList_iff.mp
    rwa [hrecs_list]
  have hcx_a : cx.store a = some c :=
    Ix.Cert.ReaderClosureKeys.context_input t recs evs [] blobs
      (fun _ => none) (fun _ _ => none) hnodup_recs hc_recs
  have hpure_a : IxVM.Refinement.RoleVal.preStorePure a = some c := by
    rw [IxVM.Refinement.RoleVal.preStorePure_eq]
    exact Ix.Cert.ReaderClosureKeys.lookup_of_nodup
      IxVM.Refinement.RoleVal.committedPreAddrs_nodup hc
  unfold resolve
  rw [hcx_a, hpure_a]
  simp only [Option.bind_eq_bind, Option.bind_some]
  unfold resolveSource
  cases hci : c.info with
  | defn _ | recr _ | axio _ | quot _ | muts _ => rfl
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    rw [hci] at hproj_closed
    dsimp only at hproj_closed
    rw [IxVM.Refinement.RoleVal.containsAddrFast_eq, List.contains_iff_mem] at hproj_closed
    simp only [hstore_eq hproj_closed]

/-! ## Upper bound: every role emitted when reading `committedPrelude` comes from `validPreRefs` -/

private theorem mem_validPreRefs_indc {owner : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {ind : Ixon.Inductive}
    (hc : (owner, c) ∈ IxVM.Refinement.RoleVal.committedPreludeList)
    (hci : c.info = .muts ms)
    (hmi : ms[i]? = some (.indc ind)) :
    ConstRef.member owner i ∈ validPreRefs ∧
      ∀ j < ind.ctors.size, ConstRef.ctor owner i j ∈ validPreRefs := by
  have hi_lt : i < ms.toList.length := by
    rw [Array.length_toList]
    by_contra hge
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at hmi
    cases hmi
  have hnth : IxVM.Refinement.RoleVal.nth? ms.toList i = some (.indc ind) := by
    rw [IxVM.Refinement.RoleVal.nth?_eq]
    simpa using hmi
  refine ⟨?_, fun j hj => ?_⟩
  · unfold validPreRefs
    refine List.mem_flatMap.mpr ⟨(owner, c), hc, ?_⟩
    dsimp only
    rw [hci]
    dsimp only
    refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi_lt, ?_⟩
    dsimp only
    rw [hnth]
    exact List.mem_cons_self
  · have hj_lt : j < ind.ctors.toList.length := by rwa [Array.length_toList]
    unfold validPreRefs
    refine List.mem_flatMap.mpr ⟨(owner, c), hc, ?_⟩
    dsimp only
    rw [hci]
    dsimp only
    refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi_lt, ?_⟩
    dsimp only
    rw [hnth]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj_lt, rfl⟩)

private theorem readInductive_validPreRefs {t : Ix.Kernel.RoleTable}
    {recs evs : Array (_root_.Address × Ixon.Constant)}
    {blobs : List (_root_.Address × ByteArray)}
    (hrecs_list : recs.toList = IxVM.Refinement.RoleVal.committedPreludeList)
    (hev_defn : ∀ p ∈ evs.toList, ∃ d, p.2.info = .defn d)
    {st : State .anon} {owner : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} {r : Read .anon}
    (hc : (owner, c) ∈ IxVM.Refinement.RoleVal.committedPreludeList)
    (hci : c.info = .muts ms)
    (h : readInductive
      (contextOf (md := .anon) t recs [] evs blobs)
      st owner c ms = .ok r) :
    ∃ gens d, r.decls.toList = gens ++ [d] ∧ r.generated = gens.length ∧
      ∀ k ∈ d.names, ∃ ref ∈ validPreRefs,
        (contextOf (md := .anon) t recs [] evs blobs).memberKey ref =
          .ok k := by
  let cx := contextOf (md := .anon) t recs [] evs blobs
  change readInductive cx st owner c ms = .ok r at h
  unfold readInductive at h
  split at h
  · rename_i shape hshape
    dsimp only at h
    rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
    · split at h
      · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
        · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
        · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
          · obtain ⟨types, htypes, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
            let indcs : Array (Nat × Ixon.Inductive) :=
              shape.order.filterMap fun i => match (ms[i]? : Option Ixon.MutConst) with
                | some (.indc ind) => some (i, ind)
                | _ => none
            have hindcs_mem : ∀ x ∈ indcs.toList, ms[x.1]? = some (.indc x.2) := by
              intro x hx
              obtain ⟨i, _, hfm⟩ := Array.mem_filterMap.mp (Array.mem_toList_iff.mp hx)
              cases hmi : ms[i]? with
              | none => simp [hmi] at hfm
              | some m =>
                cases m with
                | indc ind =>
                  simp only [hmi, Option.some.injEq] at hfm
                  subst hfm
                  exact hmi
                | defn _ | recr _ => simp [hmi] at hfm
            have tk := Ix.Cert.ReaderUnits.forIn_pushes (fun s => s)
              (Ix.Cert.ReaderUnits.KeyedBy cx (· ∈ validPreRefs) (·.1.name)) _ _
              (fun x hx s r0 hf => by
                obtain ⟨k, hk, hf⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hf
                obtain ⟨_, -, hf⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hf
                simp only [pure, Except.pure, Except.ok.injEq] at hf
                subst hf
                have hmem_ref := (mem_validPreRefs_indc hc hci (hindcs_mem x hx)).1
                refine ⟨_, rfl, fun e he => ?_⟩
                rcases Array.mem_push.mp he with he | rfl
                · exact .inl he
                · exact .inr ⟨_, hmem_ref, hk⟩)
              (fun e he => by simp at he) htypes
            obtain ⟨cs, hcs, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
            have ck := Ix.Cert.ReaderUnits.forIn_pushes (fun s => s.1)
              (Ix.Cert.ReaderUnits.KeyedBy cx (· ∈ validPreRefs) (·.1.name)) _ _
              (fun x hx s r0 hf => by
                obtain ⟨s1, hs1, hf⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hf
                simp only [pure, Except.pure, Except.ok.injEq] at hf
                subst hf
                have hctor_mem := (mem_validPreRefs_indc hc hci (hindcs_mem x hx)).2
                refine ⟨_, rfl, ?_⟩
                refine Ix.Cert.ReaderUnits.forIn_pushes (fun s => s.1)
                  (fun e => e ∈ s.1 ∨ Ix.Cert.ReaderUnits.KeyedBy cx (· ∈ validPreRefs) (·.1.name) e) _ _
                  (fun y hy t0 q hq => ?_) (fun e he => .inl he) hs1
                have hy_lt : y.2 < x.2.ctors.size := by
                  have hz := Array.mk_mem_zipIdx_iff_getElem?.mp (Array.mem_def.mpr hy)
                  by_contra hge
                  rw [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at hz
                  cases hz
                rcases Ix.Cert.ReaderUnits.ite_ok hq with hq | hq
                · rcases Ix.Cert.ReaderUnits.ite_ok hq with hq | hq
                  · exact (Ix.Cert.ReaderUnits.fail_bind hq).elim
                  · obtain ⟨k, hk, hq⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hq
                    obtain ⟨_, -, hq⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hq
                    rcases Ix.Cert.ReaderUnits.ite_ok hq with hq | hq
                    · simp only [pure, Except.pure, Except.ok.injEq] at hq
                      subst hq
                      refine ⟨_, rfl, fun e he => ?_⟩
                      rcases Array.mem_push.mp he with he | rfl
                      · exact .inl he
                      · exact .inr (.inr ⟨_, hctor_mem y.2 hy_lt, hk⟩)
                    · exact (Ix.Cert.ReaderUnits.fail_bind hq).elim
                · exact (Ix.Cert.ReaderUnits.fail_bind hq).elim)
              (fun e he => by simp at he) hcs
            obtain ⟨recs_arr, hrecs_arr, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
            have rk := Ix.Cert.ReaderUnits.forIn_pushes (fun s => s)
              (Ix.Cert.ReaderUnits.KeyedBy cx (· ∈ validPreRefs) (·.1.name)) _ _
              (fun x hx s r0 hf => by
                split at hf
                · obtain ⟨rv, hrv, hf⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hf
                  simp only [pure, Except.pure, Except.ok.injEq] at hf
                  subst hf
                  obtain ⟨s_blk, hs_blk, hx_recs⟩ :=
                    Ix.Cert.ReaderUnits.blockShapeOf_recs hshape (Array.mem_def.mpr hx)
                  obtain ⟨rOwner, rc, pos, recVal, href_eq, hrc_src, hrmem⟩ :=
                    Ix.Cert.ReaderClosureKeys.selected_origin t
                      recs evs [] blobs
                      (fun _ => none) (fun _ _ => none) hs_blk hx_recs
                  have hx_valid : x ∈ validPreRefs := by
                    rcases hrc_src with hrc_pre | ⟨hrc_ev, _⟩
                    · have hrc_list : (rOwner, rc) ∈ IxVM.Refinement.RoleVal.committedPreludeList := by
                        rw [← hrecs_list]
                        exact Array.mem_toList_iff.mpr hrc_pre
                      have hms_src := Ix.CompileCert.ReaderIndex.member_source rc pos recVal hrmem
                      cases hrci : rc.info with
                      | recr _ =>
                        rw [hrci] at hms_src
                        obtain ⟨rfl, _⟩ := hms_src
                        rw [href_eq]
                        unfold validPreRefs
                        refine List.mem_flatMap.mpr ⟨(rOwner, rc), hrc_list, ?_⟩
                        simp [hrci]
                      | muts rms =>
                        rw [hrci] at hms_src
                        have hsh_ok := List.all_eq_true.mp committedPre_shapes_ok (rOwner, rc) hrc_list
                        simp only [preConstShapeOk, hrci, Bool.and_eq_true, Bool.not_eq_true'] at hsh_ok
                        have hmem_rms : Ixon.MutConst.recr recVal ∈ rms := Array.mem_of_getElem? hms_src
                        have hany : (rms.any fun | .recr _ => true | _ => false) = true :=
                          Array.any_eq_true'.mpr ⟨.recr recVal, hmem_rms, rfl⟩
                        rw [hsh_ok.2] at hany
                        cases hany
                      | defn _ | axio _ | quot _ | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
                        rw [hrci] at hms_src; exact False.elim hms_src
                    · obtain ⟨d_ev, hdev⟩ := hev_defn (rOwner, rc) (Array.mem_toList_iff.mpr hrc_ev)
                      have hms_src := Ix.CompileCert.ReaderIndex.member_source rc pos recVal hrmem
                      rw [hdev] at hms_src
                      exact False.elim hms_src
                  refine ⟨_, rfl, fun e he => ?_⟩
                  rcases Array.mem_push.mp he with he | rfl
                  · exact .inl he
                  · exact .inr ⟨_, hx_valid, Ix.Cert.ReaderUnits.readRecursor_key hrv⟩
                · exact (Ix.Cert.ReaderUnits.throw_ok hf).elim)
              (fun e he => by simp at he) hrecs_arr
            obtain ⟨gens, d, hd, hg, hnames⟩ := Ix.Cert.ReaderUnits.lowerInductive_decls h
            refine ⟨gens, d, hd, hg, fun k hk => ?_⟩
            rw [hnames] at hk
            simp only [List.mem_append, List.mem_map] at hk
            rcases hk with (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
            · exact tk e (Array.mem_def.mpr he)
            · exact ck e (Array.mem_def.mpr he)
            · exact rk e (Array.mem_def.mpr he)
          · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
      · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
    · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
  · exact (Ix.Cert.ReaderUnits.throw_ok h).elim

private theorem emitted_role_in_validPreRefs {t : Ix.Kernel.RoleTable}
    {recs evs : Array (_root_.Address × Ixon.Constant)}
    {blobs : List (_root_.Address × ByteArray)}
    (hrecs_list : recs.toList = IxVM.Refinement.RoleVal.committedPreludeList)
    (hev_defn : ∀ p ∈ evs.toList, ∃ d, p.2.info = .defn d)
    {st' : State .anon} {decls : Array (CDecl .anon)}
    (hrr : readRecords
      (contextOf (md := .anon) t recs [] evs blobs)
      {} recs = .ok (st', decls))
    {d : CDecl .anon} (hd : d ∈ decls.toList)
    {s : Role} (hs : Ix.Kernel.Key.role s ∈ d.names) :
    ∃ ref ∈ validPreRefs,
      (contextOf (md := .anon) t recs [] evs blobs).memberKey ref =
        .ok (.role s) := by
  obtain ⟨rs, hall, flat⟩ := Ix.Cert.ReaderUnits.readRecords_lowerings hrr
  have hd' : d ∈ (rs.map fun r => r.decls.toList).flatten := by
    rw [← flat]; exact hd
  obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
  obtain ⟨⟨owner, c⟩, hc_mem, st₀, hread⟩ := Ix.Cert.FallbackStore.forall₂_mem_right hall r hr
  have hc_list : (owner, c) ∈ IxVM.Refinement.RoleVal.committedPreludeList := by
    rwa [← hrecs_list]
  have hsh_ok := List.all_eq_true.mp committedPre_shapes_ok (owner, c) hc_list
  have hgen := Ix.Cert.EvidenceTransfer.readRecord_generated hread
  cases hci : c.info with
  | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
    unfold readRecord at hread
    rw [hci] at hread
    dsimp only at hread
    rcases Ix.Cert.ReaderUnits.ite_ok hread with h0 | h0
    · exact (Ix.Cert.ReaderUnits.fail_bind h0).elim
    · simp only [pure, Except.pure, Except.ok.injEq] at h0
      subst h0; simp at hdl
  | defn _ =>
    simp [preConstShapeOk, hci] at hsh_ok
  | axio a =>
    unfold readRecord at hread
    rw [hci] at hread
    dsimp only at hread
    rcases Ix.Cert.ReaderUnits.ite_ok hread with h0 | h0
    · exact (Ix.Cert.ReaderUnits.fail_bind h0).elim
    · obtain ⟨k, hk, h0⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h0
      obtain ⟨_, -, h0⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h0
      simp only [pure, Except.pure, Except.ok.injEq] at h0
      subst h0
      simp at hdl
      subst hdl
      simp only [Ix.Kernel.Declaration.names, List.mem_singleton] at hs
      subst hs
      refine ⟨.member owner 0, ?_, hk⟩
      unfold validPreRefs
      exact List.mem_flatMap.mpr ⟨(owner, c), hc_list, by simp [hci]⟩
  | quot q =>
    unfold readRecord at hread
    rw [hci] at hread
    dsimp only at hread
    obtain ⟨k, hk, h0⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hread
    obtain ⟨_, -, h0⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h0
    simp only [pure, Except.pure, Except.ok.injEq] at h0
    subst h0
    simp at hdl
    subst hdl
    simp only [Ix.Kernel.Declaration.names, List.mem_singleton] at hs
    subst hs
    refine ⟨.member owner 0, ?_, hk⟩
    unfold validPreRefs
    exact List.mem_flatMap.mpr ⟨(owner, c), hc_list, by simp [hci]⟩
  | recr _ =>
    unfold readRecord at hread
    rw [hci] at hread
    dsimp only at hread
    rcases Ix.Cert.ReaderUnits.ite_ok hread with h0 | h0
    · simp only [pure, Except.pure, Except.ok.injEq] at h0
      subst h0; simp at hdl
    · split at h0
      · obtain ⟨x, hx, hk⟩ := (Ix.Cert.ReaderUnits.lowerTwin_spec h0).2 d hdl _ hs
        simp at hx
        subst hx
        refine ⟨.member owner 0, ?_, hk⟩
        unfold validPreRefs
        exact List.mem_flatMap.mpr ⟨(owner, c), hc_list, by simp [hci]⟩
      · exact (Ix.Cert.ReaderUnits.throw_ok h0).elim
  | muts ms =>
    simp only [preConstShapeOk, hci, Bool.and_eq_true, Bool.not_eq_true'] at hsh_ok
    obtain ⟨⟨hindc_any, _⟩, _⟩ := hsh_ok
    unfold readRecord at hread
    rw [hci] at hread
    dsimp only at hread
    rw [if_pos hindc_any] at hread
    rcases Ix.Cert.ReaderUnits.ite_ok hread with h0 | h0
    · exact (Ix.Cert.ReaderUnits.fail_bind h0).elim
    · obtain ⟨gens, d', hdecls, hg, hk_fn⟩ :=
        readInductive_validPreRefs hrecs_list hev_defn hc_list hci h0
      rw [hdecls] at hdl
      rcases List.mem_append.mp hdl with hgen_mem | hlast
      · exfalso
        have hgd : d.isGenerated = true := hgen d (by rw [hdecls, hg, List.take_left]; exact hgen_mem)
        unfold Ix.Kernel.Declaration.isGenerated at hgd
        have haux := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hgd).2) _ hs
        cases haux
      · rw [List.mem_singleton] at hlast
        subst hlast
        exact hk_fn _ hs

/-! ## Unconditional `t.bound` coverage and `t.check = .ok ()` upgrade to `BindingSeeds` -/

/-- For **any** role table `t` (even unchecked) with `preludeFor t = .ok pre`, every record `(a, c)`
in `pre.records` either has `(r, a) ∈ t.bound.toList` for a non-`compilerTrust` prelude role `r`,
or is a `.muts` block owned by a projection record `(a', c') ∈ pre.records` with that property. -/
theorem prelude_in_bound_of_preludeFor
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    (hpre : preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records) :
    (∃ r ∈ Ix.Kernel.preludeShape.flatten,
      IxVM.Refinement.compilerTrust r = false ∧ (r, a) ∈ t.bound.toList) ∨
    ∃ a' c', (a', c') ∈ pre.records ∧
      (∃ r ∈ Ix.Kernel.preludeShape.flatten,
        IxVM.Refinement.compilerTrust r = false ∧ (r, a') ∈ t.bound.toList) ∧
      Ix.Cert.ownerOf a' c' = a ∧ a ≠ a' := by
  have hshape := Ix.Kernel.Reader.preludeFor_shape hpre
  have hpre_copy := hpre
  unfold preludeFor at hpre_copy
  obtain ⟨pre₀, hread, hrest⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hpre_copy
  obtain ⟨_, _, hrest'⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hrest
  obtain ⟨_, _, hpure⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hrest'
  simp only [pure, Except.pure, Except.ok.injEq] at hpure
  subst hpure
  unfold preludeRead at hread
  obtain ⟨recs, hrecs, hr1⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hread
  obtain ⟨evs, hevs, hr2⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hr1
  obtain ⟨blobs, _, hr3⟩ := Ix.CompileCert.Loop.except_bind_ok.mp hr2
  unfold readPrelude at hr3
  dsimp only at hr3
  cases hrr : readRecords (contextOf (md := .anon) t recs [] evs blobs) {} recs with
  | error err => rcases err with ⟨_, _⟩; rw [hrr] at hr3; cases hr3
  | ok pair =>
    rcases pair with ⟨st', decls⟩
    rw [hrr] at hr3
    simp only [pure, Except.pure, Except.ok.injEq] at hr3
    subst hr3
    have hrec_eq : recs = IxVM.Refinement.RoleVal.committedPrelude := by
      rw [IxVM.Refinement.RoleVal.preludeRecords_eq] at hrecs
      injection hrecs with h; exact h.symm
    have hrecs_list : recs.toList = IxVM.Refinement.RoleVal.committedPreludeList := by
      rw [hrec_eq]; rfl
    obtain ⟨ev0, hev_ok, _, hev_defn₀⟩ := IxVM.Refinement.RoleVal.evidenceRecords_spec
    have hev_eq : evs = ev0 := by
      rw [hev_ok] at hevs
      injection hevs with h; exact h.symm
    have hevs_defn : ∀ p ∈ evs.toList, ∃ d, p.2.info = .defn d := by
      rw [hev_eq]; exact hev_defn₀
    let cx := contextOf (md := .anon) t recs [] evs blobs
    -- Surjectivity onto `preludeShape.flatten`
    have hsurj : ∀ s ∈ Ix.Kernel.preludeShape.flatten,
        ∃ ref ∈ validPreRefs,
          (match cx.memberKey ref with
           | .ok (.role r) => some r
           | _ => none) = some s := by
      intro s hs_flat
      obtain ⟨rs, hrs, hs_rs⟩ := List.mem_flatten.mp hs_flat
      have hrs_map : rs.map (Ix.Kernel.Key.role (md := .anon)) ∈
          decls.toList.map (·.names) := by
        rw [hshape]
        exact List.mem_map.mpr ⟨rs, hrs, rfl⟩
      obtain ⟨d, hd, hdn⟩ := List.mem_map.mp hrs_map
      have hs_dn : Ix.Kernel.Key.role (md := .anon) s ∈ d.names := by
        rw [hdn]
        exact List.mem_map.mpr ⟨s, hs_rs, rfl⟩
      obtain ⟨ref, href, hmk⟩ :=
        emitted_role_in_validPreRefs hrecs_list hevs_defn hrr hd hs_dn
      refine ⟨ref, href, ?_⟩
      change (match (contextOf (md := .anon) t recs [] evs blobs).memberKey ref with
        | .ok (.role r) => some r | _ => none) = some s
      rw [hmk]
    have hall_refs := pigeonhole_filterMap (Nat.le_of_eq validPreRefs_len) preludeRoles_nodup hsurj
    -- Authentic store for `resolve_inj`
    have hauth : ∀ x cx', cx.store x = some cx' →
        x = _root_.Address.admissionHash (Ixon.serConstant cx') := by
      intro x cx' hsx
      exact (Ix.Cert.FallbackStore.fallback_authentic IxVM.Refinement.RoleVal.fallbackHashed
        hpre (prelude_context_store_mem hsx)).1
    -- Helper: any non-`.muts` record `(x, cx_rec) ∈ committedPreludeList` is directly in `t.bound`
    have hnon_muts : ∀ {x : _root_.Address} {cx_rec : Ixon.Constant},
        (x, cx_rec) ∈ IxVM.Refinement.RoleVal.committedPreludeList →
        isMutsConst cx_rec = false →
        ∃ r ∈ Ix.Kernel.preludeShape.flatten,
          IxVM.Refinement.compilerTrust r = false ∧ (r, x) ∈ t.bound.toList := by
      intro x cx_rec hx_mem hx_nm
      have hcls := List.all_eq_true.mp committedPre_all_classified (x, cx_rec) hx_mem
      simp only [preRowClassified, hx_nm, Bool.false_eq_true, ↓reduceIte] at hcls
      cases hres_pure : resolve IxVM.Refinement.RoleVal.preStorePure x with
      | none => rw [hres_pure] at hcls; cases hcls
      | some ref =>
        rw [hres_pure, List.any_eq_true] at hcls
        obtain ⟨ref', href', hbeq_ref⟩ := hcls
        rw [IxVM.Refinement.RoleVal.beqConstRefFast_eq, beq_iff_eq] at hbeq_ref
        subst hbeq_ref
        obtain ⟨s, hs_flat, hmk_opt⟩ := hall_refs ref' href'
        have hmk : cx.memberKey ref' = .ok (.role s) := by
          cases hm : cx.memberKey ref' with
          | error _ => rw [hm] at hmk_opt; cases hmk_opt
          | ok k =>
            cases k with
            | role r' =>
              rw [hm] at hmk_opt
              injection hmk_opt with hr'
              subst hr'; rfl
            | id _ | aux _ _ => rw [hm] at hmk_opt; cases hmk_opt
        have hrole_map : cx.roles.names[ref']? = some (.role s) :=
          memberKey_role_exact_of_no_reconstruct (fun _ => rfl) hmk
        obtain ⟨a_b, hab_mem, hres_b⟩ := Ix.Cert.ReaderKeys.bindings_role_origin cx.store t hrole_map
        have hres_x : resolve cx.store x = some ref' := by
          change resolve (contextOf (md := .anon) t recs [] evs blobs).store x = some ref'
          rw [resolve_preStorePure_eq_context hrecs_list hx_mem]
          exact hres_pure
        have hab_eq : a_b = x := Ix.Cert.ReadingKeys.resolve_inj hauth hres_b hres_x
        subst hab_eq
        exact ⟨s, hs_flat, prelude_role_not_compilerTrust s hs_flat, hab_mem⟩
    have hc_list : (a, c) ∈ IxVM.Refinement.RoleVal.committedPreludeList := by
      rw [← hrecs_list]
      exact Array.mem_toList_iff.mpr hmem
    cases hm : isMutsConst c with
    | false => exact .inl (hnon_muts hc_list hm)
    | true =>
      right
      have hcls := List.all_eq_true.mp committedPre_all_classified (a, c) hc_list
      simp only [preRowClassified, hm, ↓reduceIte, List.any_eq_true] at hcls
      obtain ⟨⟨a', c'⟩, ha'_mem, hcond⟩ := hcls
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      obtain ⟨⟨hne_b, hnm'⟩, hown_b⟩ := hcond
      have hne : a ≠ a' := by
        intro heq
        subst heq
        rw [IxVM.Refinement.RoleVal.beqAddrFast_eq, beq_self_eq_true] at hne_b
        cases hne_b
      rw [IxVM.Refinement.RoleVal.beqAddrFast_eq, beq_iff_eq] at hown_b
      have ha'_recs : (a', c') ∈ recs := by
        apply Array.mem_toList_iff.mp
        rwa [hrecs_list]
      exact ⟨a', c', ha'_recs, hnon_muts ha'_mem hnm', hown_b, hne⟩

/-- Upgrade `prelude_in_bound_of_preludeFor` to `BindingSeeds t` under `t.check = .ok ()`. -/
theorem prelude_in_bindingSeeds_of_check
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    (hchk : t.check = .ok ())
    (hpre : preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records) :
    IxVM.Refinement.BindingSeeds t a ∨
    ∃ a' c', (a', c') ∈ pre.records ∧
      IxVM.Refinement.BindingSeeds t a' ∧
      Ix.Cert.ownerOf a' c' = a ∧ a ≠ a' := by
  rcases prelude_in_bound_of_preludeFor hpre hmem with
    ⟨r, _, hnt, hbound⟩ | ⟨a', c', hm', ⟨r, _, hnt, hbound'⟩, hown, hne⟩
  · exact .inl (.inl ⟨r, hnt, Ix.Cert.ReadingKeys.addressOf_of_bound hchk hbound⟩)
  · exact .inr ⟨a', c', hm', .inl ⟨r, hnt, Ix.Cert.ReadingKeys.addressOf_of_bound hchk hbound'⟩,
      hown, hne⟩

/-- Extract `t.check = .ok ()` from `Ix.Kernel.Admission.admitBinding hash b = .ok t`. -/
theorem check_of_admitBinding {hash : ByteArray → _root_.Address}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding hash b = .ok t) :
    t.check = .ok () :=
  ((Ix.Kernel.Admission.admitBinding_ok_iff hash b t).mp hadm).wellFormed

/-- Upgrade `prelude_in_bound_of_preludeFor` to `BindingSeeds t` under `admitBinding`. -/
theorem prelude_in_bindingSeeds_of_admitBinding
    {hash : ByteArray → _root_.Address} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    (hadm : Ix.Kernel.Admission.admitBinding hash b = .ok t)
    (hpre : preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records) :
    IxVM.Refinement.BindingSeeds t a ∨
    ∃ a' c', (a', c') ∈ pre.records ∧
      IxVM.Refinement.BindingSeeds t a' ∧
      Ix.Cert.ownerOf a' c' = a ∧ a ≠ a' :=
  prelude_in_bindingSeeds_of_check (check_of_admitBinding hadm) hpre hmem

/-- Minimal boundary hypothesis for `RolePreludeInputs.prelude_in_bindingSeeds` when `t` is not
assumed well-formed (`t.check = .ok ()`): `bindingsOf` skips unresolved entries (`resolve = none`),
whereas `RoleTable.addressOf?` picks the first matching role entry in `t.bound`. Under
`t.check = .ok ()` (available at `TableAdmittedAt.admitBinding`), `RoleTable.check_nodup` makes
`t.bound` role-unique and `prelude_in_bindingSeeds_of_check` holds unconditionally. -/
structure UncheckedPreludeTableGap : Prop where
  addressOf_of_prelude_bound :
    ∀ {t : Ix.Kernel.RoleTable} {pre : Prelude .anon},
      preludeFor t = .ok pre →
      ∀ {r : Role} {a : _root_.Address},
        r ∈ Ix.Kernel.preludeShape.flatten →
        a ∈ pre.records.toList.map Prod.fst →
        (r, a) ∈ t.bound.toList →
        t.addressOf? r = some a

/-- Assemble `RolePreludeInputs` from the proven `RoleVal` theorems and `fallback_not_padding` /
`prelude_in_bound_of_preludeFor`. -/
theorem rolePreludeInputs (hGap : UncheckedPreludeTableGap) : RolePreludeInputs where
  fallbackHashed := IxVM.Refinement.RoleVal.fallbackHashed
  preludeFor_of_readerTable := IxVM.Refinement.RoleVal.preludeFor_of_readerTable
  literalSupportBound_of_readerTable := IxVM.Refinement.RoleVal.literalSupportBound_of_readerTable
  fallback_record_agree := IxVM.Refinement.RoleVal.fallback_record_agree_of_loadedBy
  fallback_blob_agree := IxVM.Refinement.RoleVal.fallback_blob_agree_of_loadedBy
  fallback_not_padding := fallback_not_padding
  prelude_in_bindingSeeds := fun {_} {pre} hpre {a} {c} hmem => by
    rcases prelude_in_bound_of_preludeFor hpre hmem with
      ⟨r, hr, hnt, hbound⟩ | ⟨a', c', hm', ⟨r, hr, hnt, hbound'⟩, hown, hne⟩
    · have ha_fst : a ∈ pre.records.toList.map Prod.fst :=
        List.mem_map.mpr ⟨(a, c), Array.mem_toList_iff.mpr hmem, rfl⟩
      exact .inl (.inl ⟨r, hnt, hGap.addressOf_of_prelude_bound hpre hr ha_fst hbound⟩)
    · have ha'_fst : a' ∈ pre.records.toList.map Prod.fst :=
        List.mem_map.mpr ⟨(a', c'), Array.mem_toList_iff.mpr hm', rfl⟩
      exact .inr ⟨a', c', hm',
        .inl ⟨r, hnt, hGap.addressOf_of_prelude_bound hpre hr ha'_fst hbound'⟩, hown, hne⟩

end IxVM.Refinement.Assembly
