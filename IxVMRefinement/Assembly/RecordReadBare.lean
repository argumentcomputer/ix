import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.Roles.Tables
import IxVMRefinement.Roles.Lookups
import Ix.Cert.SourcePrelude

/-! # Walked non-role record bare reading and full stream assembly (`RecordReadBare`)

Discharges per-record `Ix.Kernel.Reader.readRecordBare` completeness, `L1.RecordReadsAs`, and
prefix-ordered `CheckedConstOrigin` / `CheckedIndOrigin` witnesses across the combined role+walked
closure `(E, order)`:

1. **`CheckedConstOrigin` & `CheckedIndOrigin`**: concrete per-declaration VM check witnesses
   extracted from `Claim.CheckedAtFull` / `Claim.MutsMemberCheckedAtFull` and
   `Obs.«KernelCheck::check_const».obs`, carrying `Core.TmC (Core.keyOf t)`,
   `IxVM.Consistency.Annotates`, `looseBVarsBounded`, `allLevelParamsDefined`, `Claim.RCFullRep`,
   and the exact `k_ensure_sort` / `k_check` / `level_equal` / `axiom_standing` `ObsFn` calls
   (with zero `Core.LoadFacts`).
2. **Prelude-key disjointness & `State.SameAt` preservation**: proves every key in `pre.state.keys`
   is a prelude role (`compilerTrust = false`, hence in `order_role`) and any `Read` whose outputs
   have keys `Core.keyOf t x` (`x ∉ order_role`) with empty `owners`/`blocks` and `generated = 0`
   preserves `SameAt pre.state`.
3. **Quotient exclusion (`not_quot_of_nonRole_checked`)**: proves no walked record outside
   `order_role` can have `c.info = .quot q`, since `KernelCheck::check_quot` enforces
   `KernelRoles::role_is` on `.quot`/`.quotMk`/`.quotLift`/`.quotInd` (`compilerTrust = false`).
4. **Per-record bare reading & full stream fold (`walkedStreamReadBare`)**: combines
   `SafeRefsInputs.rolePrefixStreamReadBare` on `order_role` with induction on
   `order.filter (· ∉ order_role)` to produce `StreamReadBare`, `keepsPrelude`, prefix
   `RecordReadsAs` invariants, and seed coverage. -/

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Obs

/-! ## Section 1: `CheckedConstOrigin` and `CheckedIndOrigin` -/

/-- Concrete VM check witness for a walked non-role constant declaration (`.axiomDecl`,
`.defnDecl`, `.thmDecl`, or `.opaqueDecl`). Carries `Core.TmC (Core.keyOf t)` and
`IxVM.Consistency.Annotates` directly on the exact heaps of `k_ensure_sort` and `k_check`, with
zero `Core.LoadFacts`. -/
inductive CheckedConstOrigin (calls : List (Call F)) (t : Ix.Kernel.RoleTable)
    (bAddr : _root_.Address) (E_core : Ixon.Env) (order_role : List _root_.Address) :
    Ix.Kernel.Declaration .anon → Prop where
  | axiomDecl
      {a : _root_.Address} {c : Ixon.Constant} {ax : Ixon.Axiom}
      {nlvls : Nat} {ty₀ ty' : Core.KExpr}
      {lim : Nat} {m_pre m_es m_es' m_ax m_ax' : Heap F}
      {x_rc x_ty x_addr v_sort v_ax : SourceValue F}
      {cs_es cs_ax : List (Call F)}
      (hnot_role : a ∉ order_role)
      (hrec : Ix.Cert.recordAt E_core a = some c)
      (hinfo : c.info = .axio ax)
      (hsafe : ax.isUnsafe = false)
      (hnlvls : nlvls < 4294967296)
      (hty_lbb : ty₀.looseBVarsBounded 0 = true)
      (hty_def : ty₀.allLevelParamsDefined (List.range nlvls) = true)
      (hty_ann : IxVM.Consistency.Annotates ty' ty₀)
      (hm_es : m_es = m_pre ++
        [.construct Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc : Core.TmC (Core.keyOf t) m_es (Core.posOf (List.range nlvls) ty') x_ty)
      (hrc_es : Claim.RCFullRep t bAddr lim m_es x_rc)
      (ev_es : ObsFn Core.W "KernelInfer::k_ensure_sort"
        [x_rc, x_ty, .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre.length]
        m_es v_sort m_es' cs_es)
      (hcl_es : (⟨"KernelInfer::k_ensure_sort",
        [x_rc, x_ty, .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre.length],
        m_es⟩ : Call F) ∈ calls)
      (hsub_es : ∀ cl ∈ cs_es, cl ∈ calls)
      (hext_ax : Heap.Extends m_es' m_ax)
      (hrc_ax : Claim.RCFullRep t bAddr lim m_ax x_rc)
      (ha_ax : Core.S0.addr m_ax x_addr a)
      (ev_ax : ObsFn Core.W "KernelRoles::axiom_standing" [x_rc, x_addr] m_ax v_ax m_ax' cs_ax)
      (hne_ax : v_ax ≠ .field 0)
      (hcl_ax : (⟨"KernelRoles::axiom_standing", [x_rc, x_addr], m_ax⟩ : Call F) ∈ calls)
      (hsub_ax : ∀ cl ∈ cs_ax, cl ∈ calls) :
      CheckedConstOrigin calls t bAddr E_core order_role
        (.axiomDecl ⟨Core.keyOf t a, List.range nlvls, ty₀⟩)
  | defnDecl
      {a : _root_.Address} {nlvls : Nat} {ty₀ val₀ ty' val' : Core.KExpr}
      {hn : Ix.Kernel.ReducibilityHint}
      {lim : Nat} {m_pre1 m_es m_es' m_pre2 m_kc m_kc' : Heap F}
      {x_rc x_ty x_val v_sort r_kc : SourceValue F}
      {cs_es cs_kc : List (Call F)}
      (hnot_role : a ∉ order_role)
      (hnlvls : nlvls < 4294967296)
      (hty_lbb : ty₀.looseBVarsBounded 0 = true)
      (hty_def : ty₀.allLevelParamsDefined (List.range nlvls) = true)
      (hval_lbb : val₀.looseBVarsBounded 0 = true)
      (hval_def : val₀.allLevelParamsDefined (List.range nlvls) = true)
      (hty_ann : IxVM.Consistency.Annotates ty' ty₀)
      (hval_ann : IxVM.Consistency.Annotates val' val₀)
      (hm_es : m_es = m_pre1 ++
        [.construct Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc_es : Core.TmC (Core.keyOf t) m_es (Core.posOf (List.range nlvls) ty') x_ty)
      (hrc_es : Claim.RCFullRep t bAddr lim m_es x_rc)
      (ev_es : ObsFn Core.W "KernelInfer::k_ensure_sort"
        [x_rc, x_ty, .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre1.length]
        m_es v_sort m_es' cs_es)
      (hcl_es : (⟨"KernelInfer::k_ensure_sort",
        [x_rc, x_ty, .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre1.length],
        m_es⟩ : Call F) ∈ calls)
      (hsub_es : ∀ cl ∈ cs_es, cl ∈ calls)
      (hext_kc : Heap.Extends m_es' m_kc)
      (hm_kc : m_kc = m_pre2 ++
        [.construct Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc_kc : Core.TmC (Core.keyOf t) m_kc (Core.posOf (List.range nlvls) ty') x_ty)
      (hval_tmc_kc : Core.TmC (Core.keyOf t) m_kc (Core.posOf (List.range nlvls) val') x_val)
      (hrc_kc : Claim.RCFullRep t bAddr lim m_kc x_rc)
      (ev_kc : ObsFn Core.W "KernelInfer::k_check"
        [x_rc, x_val, x_ty,
         .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length]
        m_kc r_kc m_kc' cs_kc)
      (hcl_kc : (⟨"KernelInfer::k_check",
        [x_rc, x_val, x_ty,
         .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length],
        m_kc⟩ : Call F) ∈ calls)
      (hsub_kc : ∀ cl ∈ cs_kc, cl ∈ calls) :
      CheckedConstOrigin calls t bAddr E_core order_role
        (.defnDecl ⟨Core.keyOf t a, List.range nlvls, ty₀⟩ val₀ hn)
  | thmDecl
      {a : _root_.Address} {nlvls : Nat} {ty₀ val₀ ty' val' : Core.KExpr}
      {lim : Nat} {m_pre1 m_es m_es' m_le m_le' m_pre2 m_kc m_kc' : Heap F}
      {x_rc x_ty x_val v_sort r_kc : SourceValue F}
      {cs_es cs_le cs_kc : List (Call F)}
      (hnot_role : a ∉ order_role)
      (hnlvls : nlvls < 4294967296)
      (hty_lbb : ty₀.looseBVarsBounded 0 = true)
      (hty_def : ty₀.allLevelParamsDefined (List.range nlvls) = true)
      (hval_lbb : val₀.looseBVarsBounded 0 = true)
      (hval_def : val₀.allLevelParamsDefined (List.range nlvls) = true)
      (hty_ann : IxVM.Consistency.Annotates ty' ty₀)
      (hval_ann : IxVM.Consistency.Annotates val' val₀)
      (hm_es : m_es = m_pre1 ++
        [.construct Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc_es : Core.TmC (Core.keyOf t) m_es (Core.posOf (List.range nlvls) ty') x_ty)
      (hrc_es : Claim.RCFullRep t bAddr lim m_es x_rc)
      (ev_es : ObsFn Core.W "KernelInfer::k_ensure_sort"
        [x_rc, x_ty, .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre1.length]
        m_es v_sort m_es' cs_es)
      (hcl_es : (⟨"KernelInfer::k_ensure_sort",
        [x_rc, x_ty, .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre1.length],
        m_es⟩ : Call F) ∈ calls)
      (hsub_es : ∀ cl ∈ cs_es, cl ∈ calls)
      (hm_le : m_le = m_es' ++ [.construct "KernelTypes::KLevelNode" "Zero" []])
      (ev_le : ObsFn Core.W "KernelLevels::level_equal"
        [v_sort, .ptr (.enum "KernelTypes::KLevelNode") m_es'.length]
        m_le (.field 1) m_le' cs_le)
      (hcl_le : (⟨"KernelLevels::level_equal",
        [v_sort, .ptr (.enum "KernelTypes::KLevelNode") m_es'.length],
        m_le⟩ : Call F) ∈ calls)
      (hsub_le : ∀ cl ∈ cs_le, cl ∈ calls)
      (hext_kc : Heap.Extends m_le' m_kc)
      (hm_kc : m_kc = m_pre2 ++
        [.construct Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc_kc : Core.TmC (Core.keyOf t) m_kc (Core.posOf (List.range nlvls) ty') x_ty)
      (hval_tmc_kc : Core.TmC (Core.keyOf t) m_kc (Core.posOf (List.range nlvls) val') x_val)
      (hrc_kc : Claim.RCFullRep t bAddr lim m_kc x_rc)
      (ev_kc : ObsFn Core.W "KernelInfer::k_check"
        [x_rc, x_val, x_ty,
         .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length]
        m_kc r_kc m_kc' cs_kc)
      (hcl_kc : (⟨"KernelInfer::k_check",
        [x_rc, x_val, x_ty,
         .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length],
        m_kc⟩ : Call F) ∈ calls)
      (hsub_kc : ∀ cl ∈ cs_kc, cl ∈ calls) :
      CheckedConstOrigin calls t bAddr E_core order_role
        (.thmDecl ⟨Core.keyOf t a, List.range nlvls, ty₀⟩ val₀)
  | opaqueDecl
      {a : _root_.Address} {nlvls : Nat} {ty₀ val₀ ty' val' : Core.KExpr}
      {lim : Nat} {m_pre1 m_es m_es' m_pre2 m_kc m_kc' : Heap F}
      {x_rc x_ty x_val v_sort r_kc : SourceValue F}
      {cs_es cs_kc : List (Call F)}
      (hnot_role : a ∉ order_role)
      (hnlvls : nlvls < 4294967296)
      (hty_lbb : ty₀.looseBVarsBounded 0 = true)
      (hty_def : ty₀.allLevelParamsDefined (List.range nlvls) = true)
      (hval_lbb : val₀.looseBVarsBounded 0 = true)
      (hval_def : val₀.allLevelParamsDefined (List.range nlvls) = true)
      (hty_ann : IxVM.Consistency.Annotates ty' ty₀)
      (hval_ann : IxVM.Consistency.Annotates val' val₀)
      (hm_es : m_es = m_pre1 ++
        [.construct Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc_es : Core.TmC (Core.keyOf t) m_es (Core.posOf (List.range nlvls) ty') x_ty)
      (hrc_es : Claim.RCFullRep t bAddr lim m_es x_rc)
      (ev_es : ObsFn Core.W "KernelInfer::k_ensure_sort"
        [x_rc, x_ty, .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre1.length]
        m_es v_sort m_es' cs_es)
      (hcl_es : (⟨"KernelInfer::k_ensure_sort",
        [x_rc, x_ty, .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre1.length],
        m_es⟩ : Call F) ∈ calls)
      (hsub_es : ∀ cl ∈ cs_es, cl ∈ calls)
      (hext_kc : Heap.Extends m_es' m_kc)
      (hm_kc : m_kc = m_pre2 ++
        [.construct Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []])
      (hty_tmc_kc : Core.TmC (Core.keyOf t) m_kc (Core.posOf (List.range nlvls) ty') x_ty)
      (hval_tmc_kc : Core.TmC (Core.keyOf t) m_kc (Core.posOf (List.range nlvls) val') x_val)
      (hrc_kc : Claim.RCFullRep t bAddr lim m_kc x_rc)
      (ev_kc : ObsFn Core.W "KernelInfer::k_check"
        [x_rc, x_val, x_ty,
         .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length]
        m_kc r_kc m_kc' cs_kc)
      (hcl_kc : (⟨"KernelInfer::k_check",
        [x_rc, x_val, x_ty,
         .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m_pre2.length],
        m_kc⟩ : Call F) ∈ calls)
      (hsub_kc : ∀ cl ∈ cs_kc, cl ∈ calls) :
      CheckedConstOrigin calls t bAddr E_core order_role
        (.opaqueDecl ⟨Core.keyOf t a, List.range nlvls, ty₀⟩ val₀)

/-- Concrete VM check witness for a walked non-role inductive/recursor declaration (`.indDecl`
emitted by `readInductiveBare` or `lowerTwin`). -/
inductive CheckedIndOrigin (calls : List (Call F)) (b : Ix.Kernel.Admission.Binding)
    (t : Ix.Kernel.RoleTable) (E₀ E : Ixon.Env) (pre : Ix.Kernel.Reader.Prelude .anon)
    (order order_role : List _root_.Address)
    (d : Ix.Kernel.Declaration .anon) : Prop where
  | mk
      (addr : _root_.Address)
      (const : Ixon.Constant)
      (st₀ : Ix.Kernel.Reader.State .anon)
      (rd : Ix.Kernel.Reader.Read .anon)
      (not_role : addr ∉ order_role)
      (mem_decoded : (addr, const) ∈ Ix.Cert.Stream.decodedOf E order)
      (rec₀ : Ix.Cert.recordAt E₀ addr = some const)
      (wkAll : WkAll calls b.address t E₀ addr)
      (not_outside : ¬ IxVM.Consistency.OutsideLogicAt E₀ addr)
      (sameAt : ∀ k ∈ pre.state.keys, st₀.SameAt pre.state k)
      (read_ok :
        Ix.Kernel.Reader.readRecordBare
          (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
            (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
          st₀ addr const = .ok rd)
      (mem_decls : d ∈ rd.decls.toList)
      (is_ind : ∃ block nP, d = .indDecl block nP)
      (names_nonRole : ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role)
      (checked :
        (∃ rc, const.info = .recr rc ∧ Claim.CheckedAtFull calls b.address t addr) ∨
        (∃ ms, const.info = .muts ms ∧
          ¬ ms.all (fun | .defn _ => true | _ => false) ∧
          ∀ k < ms.size, Claim.MutsMemberCheckedAtFull calls b.address t addr ms k)) :
      CheckedIndOrigin calls b t E₀ E pre order order_role d

/-! ## Section 2: Prelude-key characterization and `State.SameAt` preservation -/

private theorem preludeShape_nonempty : ∀ rs ∈ Ix.Kernel.preludeShape, rs ≠ [] := by
  decide

private theorem prelude_role_not_compilerTrust :
    ∀ s ∈ Ix.Kernel.preludeShape.flatten, IxVM.Refinement.compilerTrust s = false := by
  decide

/-- Every declaration in `pre.ix.decls` (`preludeFor t = .ok pre`) is non-`basisDecl` and its names
are roles in `Ix.Kernel.preludeShape.flatten`. -/
theorem preludeFor_decls_roles {md : Ix.Kernel.Mode} {t : Ix.Kernel.RoleTable}
    {pre : Ix.Kernel.Reader.Prelude md}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre) :
    (∀ d ∈ pre.ix.decls.toList, ∀ k, d ≠ .basisDecl k) ∧
    (∀ d ∈ pre.ix.decls.toList, ∀ n ∈ d.names,
      ∃ s ∈ Ix.Kernel.preludeShape.flatten, n = .role s) := by
  have hshape := Ix.Kernel.Reader.preludeFor_shape hpre
  refine ⟨fun d hd k hdk => ?_, fun d hd n hn => ?_⟩
  · subst hdk
    have hm : ([] : List (Ix.Kernel.Key md)) ∈ pre.ix.decls.toList.map (·.names) :=
      List.mem_map.mpr ⟨.basisDecl k, hd, rfl⟩
    rw [hshape] at hm
    obtain ⟨rs, hrs, hemp⟩ := List.mem_map.mp hm
    have hrs_nil : rs = [] := by
      cases rs with
      | nil => rfl
      | cons _ _ => cases hemp
    exact preludeShape_nonempty rs hrs hrs_nil
  · have hm : d.names ∈ pre.ix.decls.toList.map (·.names) :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    rw [hshape] at hm
    obtain ⟨rs, hrs, hmap⟩ := List.mem_map.mp hm
    rw [← hmap] at hn
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hn
    exact ⟨s, List.mem_flatten.mpr ⟨rs, hrs, hs⟩, rfl⟩

private theorem projRecOwners_keys_any {md : Ix.Kernel.Mode}
    {block : List (Ix.Kernel.ConstantInfo md)}
    {types : List (Ix.Kernel.Key md × List Ix.Kernel.LevelParam × Ix.Kernel.Expr md ×
      Nat × Nat × List (Ix.Kernel.Key md) × Bool)}
    {ctors : List (Ix.Kernel.Key md × Nat × Ix.Kernel.Expr md)}
    {recs : List (Ix.Kernel.Key md × List Ix.Kernel.LevelParam × Ix.Kernel.Expr md ×
      Nat × Nat)}
    {o : Ix.Kernel.Frontend.ProjRecOwner md}
    (ho : o ∈ Ix.Kernel.Frontend.projRecOwners block types ctors recs) :
    o.T ∈ types.map Prod.fst := by
  unfold Ix.Kernel.Frontend.projRecOwners at ho
  dsimp only at ho
  split at ho
  · simp at ho
  · split at ho
    · simp at ho
    · obtain ⟨t, ht, hf⟩ := List.mem_filterMap.mp ho
      have hk : o.T = t.1.1 := by
        obtain ⟨⟨T, lps, tty, nP, nI, cs, isRec⟩, j⟩ := t
        simp only [bind, Option.bind, guard, pure] at hf
        repeat' first | (dsimp only at hf) | (split at hf) | (cases hf)
        all_goals rfl
      rw [hk]
      have hm : t.1 ∈ types := by
        have hm : t.1 ∈ types.zipIdx.map Prod.fst := List.mem_map.mpr ⟨t, ht, rfl⟩
        simpa using hm
      exact List.mem_map.mpr ⟨t.1, hm, rfl⟩

private theorem lowerInductive_sideNames_any {md : Ix.Kernel.Mode}
    {st : Ix.Kernel.Reader.State md} {rb : Ix.Kernel.Reader.BlockRead md}
    {r : Ix.Kernel.Reader.Read md}
    (h : Ix.Kernel.Reader.lowerInductive st rb = .ok r) :
    (∀ o ∈ r.owners, o.T ∈ (Ix.Cert.CtxAgree.indDeclOf rb).names) ∧
    (∀ b ∈ r.blocks, b.1 ∈ (Ix.Cert.CtxAgree.indDeclOf rb).names) := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  have keyMem (x : (Ix.Kernel.Reader.CVal md × Nat × Nat) × List (Ix.Kernel.Key md))
      (hx : x ∈ types.toList.zip ctorNames.toList) :
      x.1.1.name ∈ (Ix.Cert.CtxAgree.indDeclOf ⟨nPd, types, ctors, ctorNames, recs⟩).names := by
    simp only [Ix.Cert.CtxAgree.indDeclOf, Ix.Kernel.Declaration.names, List.map_append,
      List.map_map]
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨x.1, (List.of_mem_zip hx).1, rfl⟩))
  replace h := Ix.Cert.LowerDistinct.lowerInductiveDecls_of_ok h
  unfold Ix.Kernel.Reader.lowerInductiveDecls at h
  simp only [ite_not, bne_iff_ne, ne_eq] at h
  split at h
  all_goals
    rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
    all_goals obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    all_goals
      rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
      · split at h
        · simp [Ix.Kernel.Reader.declined, throw, throwThe, MonadExceptOf.throw] at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst r
          constructor
          · intro o ho
            have hm := projRecOwners_keys_any ho
            simp only [List.map_map] at hm
            obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
            rw [← he]
            exact keyMem x hx
          · intro b hb
            have hm := (List.mem_map (f := Prod.fst)).mpr ⟨b, hb, rfl⟩
            simp only [List.map_map] at hm
            obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
            rw [← he]
            exact keyMem x hx
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst r
        constructor
        · intro o ho
          have hm := projRecOwners_keys_any ho
          simp only [List.map_map] at hm
          obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
          rw [← he]
          exact keyMem x hx
        · intro b hb
          have hm := (List.mem_map (f := Prod.fst)).mpr ⟨b, hb, rfl⟩
          simp only [List.map_map] at hm
          obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
          rw [← he]
          exact keyMem x hx

private theorem lowerTwin_empty_sides {md : Ix.Kernel.Mode} {cx : Ix.Kernel.Reader.Ctx md}
    {twins : Array (Ix.Kernel.ConstRef _root_.Address × Ix.Kernel.Reader.RecEntry)}
    {r : Ix.Kernel.Reader.Read md} (h : Ix.Kernel.Reader.lowerTwin cx twins = .ok r) :
    r.owners = [] ∧ r.blocks = [] := by
  unfold Ix.Kernel.Reader.lowerTwin at h
  split at h
  · dsimp only at h
    rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
    · split at h
      · split at h
        · split at h
          · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
            · split at h
              · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
                · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
                · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
                  · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
                    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
                    simp only [ite_not, bne_iff_ne, ne_eq] at h
                    split at h
                    all_goals
                      rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
                      all_goals obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
                      all_goals
                        split at h
                        · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
                        · simp only [pure, Except.pure, Except.ok.injEq] at h
                          subst h
                          exact ⟨rfl, rfl⟩
                  · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
              · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
            · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
          · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
        · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
      · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
    · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

private theorem lowerInductive_sideNames_decls {md : Ix.Kernel.Mode}
    {st : Ix.Kernel.Reader.State md} {rb : Ix.Kernel.Reader.BlockRead md}
    {r : Ix.Kernel.Reader.Read md}
    (h : Ix.Kernel.Reader.lowerInductive st rb = .ok r) :
    (∀ o ∈ r.owners, ∃ d ∈ r.decls.toList, o.T ∈ d.names) ∧
    (∀ b ∈ r.blocks, ∃ d ∈ r.decls.toList, b.1 ∈ d.names) := by
  obtain ⟨hsO, hsB⟩ := lowerInductive_sideNames_any h
  obtain ⟨_, hd_eq, _, _, _⟩ := Ix.Cert.CtxAgree.lowerInductive_ok h
  have hind_mem : Ix.Cert.CtxAgree.indDeclOf rb ∈ r.decls.toList := by
    rw [hd_eq]; simp
  exact ⟨fun o ho => ⟨_, hind_mem, hsO o ho⟩,
    fun b hb => ⟨_, hind_mem, hsB b hb⟩⟩

private theorem readRecord_sideNames_any {md : Ix.Kernel.Mode}
    {cx : Ix.Kernel.Reader.Ctx md} {st : Ix.Kernel.Reader.State md}
    {owner : _root_.Address} {c : Ixon.Constant} {r : Ix.Kernel.Reader.Read md}
    (h : Ix.Kernel.Reader.readRecord cx st owner c = .ok r) :
    (∀ o ∈ r.owners, ∃ d ∈ r.decls.toList, o.T ∈ d.names) ∧
    (∀ b ∈ r.blocks, ∃ d ∈ r.decls.toList, b.1 ∈ d.names) := by
  cases hinfo : c.info with
  | muts ms =>
    unfold Ix.Kernel.Reader.readRecord at h
    simp only [hinfo] at h
    rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
    · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
      · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
      · unfold Ix.Kernel.Reader.readInductive at h
        split at h
        · dsimp only at h
          rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
          · split at h
            · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
              · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
              · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
                · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
                  obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
                  obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
                  exact lowerInductive_sideNames_decls h
                · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
            · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
          · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
        · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
    · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
      · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨by simp, by simp⟩
        · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
          obtain ⟨ho, hb⟩ := lowerTwin_empty_sides h
          exact ⟨by simp [ho], by simp [hb]⟩
      · rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
        · split at h
          · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
          · split at h
            · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
              simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨by simp, by simp⟩
            · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
        · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
  | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
    unfold Ix.Kernel.Reader.readRecord at h; simp only [hinfo] at h
    rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
    · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨by simp, by simp⟩
  | defn _ =>
    unfold Ix.Kernel.Reader.readRecord at h; simp only [hinfo] at h
    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨by simp, by simp⟩
  | recr _ =>
    unfold Ix.Kernel.Reader.readRecord at h; simp only [hinfo] at h
    rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨by simp, by simp⟩
    · split at h
      · obtain ⟨ho, hb⟩ := lowerTwin_empty_sides h
        exact ⟨by simp [ho], by simp [hb]⟩
      · exact (Ix.Cert.ReaderUnits.throw_ok h).elim
  | axio _ =>
    unfold Ix.Kernel.Reader.readRecord at h; simp only [hinfo] at h
    rcases Ix.Cert.ReaderUnits.ite_ok h with h | h
    · exact (Ix.Cert.ReaderUnits.fail_bind h).elim
    · obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨by simp, by simp⟩
  | quot _ =>
    unfold Ix.Kernel.Reader.readRecord at h; simp only [hinfo] at h
    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨by simp, by simp⟩

private theorem noteEntries_names_any {md : Ix.Kernel.Mode} {d : Ix.Kernel.Declaration md}
    (hb : ∀ k, d ≠ .basisDecl k) :
    (Ix.Cert.CtxAgree.noteEntries d).map Prod.fst = d.names := by
  cases d with
  | basisDecl k => exact (hb k rfl).elim
  | indDecl block n =>
    simp only [Ix.Cert.CtxAgree.noteEntries, Ix.Kernel.Declaration.names, List.map_map]; rfl
  | _ => rfl

private theorem fold_ins_other_any {md : Ix.Kernel.Mode} {α β : Type}
    (g : α → Option (Ix.Kernel.Key md × β)) (k : Ix.Kernel.Key md) :
    ∀ (xs : List α) (m : Std.HashMap (Ix.Kernel.Key md) β),
      (∀ x ∈ xs, ∀ p, g x = some p → p.1 ≠ k) →
      (xs.foldl (Ix.Cert.CtxAgree.insOpt g) m)[k]? = m[k]?
  | [], _, _ => rfl
  | x :: xs, m, hn => by
    rw [List.foldl_cons, fold_ins_other_any g k xs _ (fun y hy => hn y (List.mem_cons_of_mem _ hy))]
    unfold Ix.Cert.CtxAgree.insOpt
    cases hg : g x with
    | none => rfl
    | some p =>
      rw [Std.HashMap.getElem?_insert]
      simp [hn x List.mem_cons_self p hg]

private theorem sameAt_refl_any {md : Ix.Kernel.Mode} (st : Ix.Kernel.Reader.State md)
    (k : Ix.Kernel.Key md) : st.SameAt st k :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem sameAt_trans_any {md : Ix.Kernel.Mode} {a b c : Ix.Kernel.Reader.State md}
    {k : Ix.Kernel.Key md} (h1 : a.SameAt b k) (h2 : b.SameAt c k) : a.SameAt c k :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1,
   h1.2.2.2.1.trans h2.2.2.2.1, h1.2.2.2.2.trans h2.2.2.2.2⟩

private theorem note_other_any {md : Ix.Kernel.Mode} (st : Ix.Kernel.Reader.State md)
    (d : Ix.Kernel.Declaration md) (k : Ix.Kernel.Key md)
    (hb : ∀ b, d ≠ .basisDecl b) (hk : k ∉ d.names) :
    (st.note d).SameAt st k := by
  have he : ∀ e ∈ Ix.Cert.CtxAgree.noteEntries d, e.1 ≠ k := by
    intro e hm heq
    apply hk
    rw [← noteEntries_names_any hb, ← heq]
    exact List.mem_map.mpr ⟨e, hm, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Ix.Cert.CtxAgree.note_constTypes]
    apply fold_ins_other_any
    intro e hm p hp
    cases hp
    exact he e hm
  · rw [Ix.Cert.CtxAgree.note_heights]
    apply fold_ins_other_any
    intro e hm p hp
    unfold Ix.Cert.CtxAgree.htOf at hp
    cases hh : e.2.2.2 with
    | none => simp [hh] at hp
    | some v => simp only [hh, Option.map_some, Option.some.injEq] at hp; subst p; exact he e hm
  · rw [Ix.Cert.CtxAgree.note_indBlocks]
  · rw [Ix.Cert.CtxAgree.note_projOwners]
  · rw [Ix.Cert.CtxAgree.note_projLevels]

private theorem noteGenerated_other_any {md : Ix.Kernel.Mode} (st : Ix.Kernel.Reader.State md)
    (d : Ix.Kernel.Declaration md) (k : Ix.Kernel.Key md)
    (hb : ∀ b, d ≠ .basisDecl b) (hk : k ∉ d.names) :
    (st.noteGenerated d).SameAt st k := by
  cases d with
  | thmDecl cv value =>
    have hn : cv.name ≠ k := by simpa [Ix.Kernel.Declaration.names, eq_comm] using hk
    unfold Ix.Kernel.Reader.State.noteGenerated
    by_cases hp : cv.name.isProjIota = true
    · simp only [hp, ite_true]
      cases hl : Ix.Kernel.Frontend.projIotaLevel cv.type with
      | none => exact note_other_any st (.thmDecl cv value) k hb hk
      | some l =>
        apply sameAt_trans_any (note_other_any _ (.thmDecl cv value) k hb hk)
        exact ⟨rfl, rfl, rfl, rfl, by simp [Std.HashMap.getElem?_insert, hn]⟩
    · simp only [hp]
      exact note_other_any st (.thmDecl cv value) k hb hk
  | _ => exact note_other_any st _ k hb hk

private theorem sameAt_fold_any {md : Ix.Kernel.Mode} {α : Type}
    (f : Ix.Kernel.Reader.State md → α → Ix.Kernel.Reader.State md) (k : Ix.Kernel.Key md) :
    ∀ (xs : List α) (st : Ix.Kernel.Reader.State md),
      (∀ x ∈ xs, ∀ s, (f s x).SameAt s k) → (xs.foldl f st).SameAt st k
  | [], st, _ => sameAt_refl_any st k
  | x :: xs, st, hf =>
    sameAt_trans_any (sameAt_fold_any f k xs _ (fun y hy => hf y (List.mem_cons_of_mem _ hy)))
      (hf x List.mem_cons_self st)

/-- Generic `State.commit` frame at key `k`. -/
theorem commit_other_any {md : Ix.Kernel.Mode} (st : Ix.Kernel.Reader.State md)
    (r : Ix.Kernel.Reader.Read md) (k : Ix.Kernel.Key md)
    (hd : ∀ d ∈ r.decls.toList, (∀ b, d ≠ .basisDecl b) ∧ k ∉ d.names)
    (ho : ∀ o ∈ r.owners, o.T ≠ k)
    (hb : ∀ b ∈ r.blocks, b.1 ≠ k) :
    (st.commit r).SameAt st k := by
  let s₁ := r.owners.foldl (fun s o => { s with projOwners := s.projOwners.insert o.T o }) st
  let s₂ := r.blocks.foldl (fun s b => { s with indBlocks := s.indBlocks.insert b.1 b.2 }) s₁
  let s₃ := r.decls.toList.zipIdx.foldl
    (fun s x => if x.2 < r.generated then s.noteGenerated x.1 else s.note x.1) s₂
  rw [Ix.Cert.CtxAgree.commit_eq]
  change s₃.SameAt st k
  have h₁ : s₁.SameAt st k := sameAt_fold_any _ k r.owners st (by
    intro o hm s
    exact ⟨rfl, rfl, rfl, by simp [Std.HashMap.getElem?_insert, ho o hm], rfl⟩)
  have h₂ : s₂.SameAt s₁ k := sameAt_fold_any _ k r.blocks s₁ (by
    intro b hm s
    exact ⟨rfl, rfl, by simp [Std.HashMap.getElem?_insert, hb b hm], rfl, rfl⟩)
  have h₃ : s₃.SameAt s₂ k := sameAt_fold_any _ k r.decls.toList.zipIdx s₂ (by
    intro x hx s
    have hm : x.1 ∈ r.decls.toList := by
      have hm := (List.mem_map (f := Prod.fst)).mpr ⟨x, hx, rfl⟩
      simpa using hm
    split
    · exact noteGenerated_other_any s x.1 k (hd x.1 hm).1 (hd x.1 hm).2
    · exact note_other_any s x.1 k (hd x.1 hm).1 (hd x.1 hm).2)
  exact sameAt_trans_any h₃ (sameAt_trans_any h₂ h₁)

private theorem streamRead_sameAt_other {md : Ix.Kernel.Mode} {cx : Ix.Kernel.Reader.Ctx md}
    {st st' : Ix.Kernel.Reader.State md}
    {records : List (_root_.Address × Ixon.Constant)} {out : Array (Ix.Kernel.Reader.CDecl md)}
    (h : Ix.Kernel.Reader.StreamRead cx st records st' out)
    {k : Ix.Kernel.Key md}
    (hd : ∀ d ∈ out.toList, (∀ b, d ≠ .basisDecl b) ∧ k ∉ d.names) :
    st'.SameAt st k := by
  induction h with
  | nil => exact sameAt_refl_any _ k
  | @cons st₀ _ _ _ r _ tailOut read _ ih =>
    have hd_r : ∀ d ∈ r.decls.toList, (∀ b, d ≠ .basisDecl b) ∧ k ∉ d.names := fun d hm =>
      hd d (by rw [Array.toList_append]; exact List.mem_append_left _ hm)
    have hd_tail : ∀ d ∈ tailOut.toList, (∀ b, d ≠ .basisDecl b) ∧ k ∉ d.names := fun d hm =>
      hd d (by rw [Array.toList_append]; exact List.mem_append_right _ hm)
    obtain ⟨hsO, hsB⟩ := readRecord_sideNames_any read
    have hstep := commit_other_any st₀ r k hd_r
      (fun o ho heq => by obtain ⟨d, hm, hn⟩ := hsO o ho; rw [heq] at hn; exact (hd_r d hm).2 hn)
      (fun b hb heq => by obtain ⟨d, hm, hn⟩ := hsB b hb; rw [heq] at hn; exact (hd_r d hm).2 hn)
    exact sameAt_trans_any (ih hd_tail) hstep

/-- Every key in `pre.state.keys` (`preludeFor t = .ok pre`) is `.role s` for some
`s ∈ Ix.Kernel.preludeShape.flatten`. -/
theorem prelude_state_keys_roles {md : Ix.Kernel.Mode} {t : Ix.Kernel.RoleTable}
    {pre : Ix.Kernel.Reader.Prelude md}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre) :
    ∀ k ∈ pre.state.keys, ∃ s ∈ Ix.Kernel.preludeShape.flatten, k = .role s := by
  obtain ⟨hnb, hroles⟩ := preludeFor_decls_roles hpre
  obtain ⟨rs, extra, extraBlobs, hrr⟩ :=
    preludeRead_unpack (Ix.Kernel.Reader.preludeFor_checks hpre).1
  have hsr := Ix.Kernel.Reader.readRecords_spec hrr
  intro k hk
  by_contra hnot
  have hdisj : ∀ d ∈ pre.ix.decls.toList, (∀ b, d ≠ .basisDecl b) ∧ k ∉ d.names := by
    intro d hd
    refine ⟨hnb d hd, fun hn => ?_⟩
    obtain ⟨s, hs, rfl⟩ := hroles d hd k hn
    exact hnot ⟨s, hs, rfl⟩
  have hsame := streamRead_sameAt_other hsr hdisj
  have hmem_empty : ∀ {V : Type} {m : Std.HashMap (Ix.Kernel.Key md) V},
      m[k]? = ({} : Std.HashMap (Ix.Kernel.Key md) V)[k]? → k ∉ m.keys := by
    intro V m heq hmk
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains,
      Std.HashMap.contains_eq_isSome_getElem?, heq] at hmk
    simp at hmk
  unfold Ix.Kernel.Reader.State.keys at hk
  rcases List.mem_append.mp hk with hk4 | hk5
  · rcases List.mem_append.mp hk4 with hk3 | hk4'
    · rcases List.mem_append.mp hk3 with hk2 | hk3'
      · rcases List.mem_append.mp hk2 with hk1 | hk2'
        · exact hmem_empty hsame.1 hk1
        · exact hmem_empty hsame.2.1 hk2'
      · exact hmem_empty hsame.2.2.1 hk3'
    · exact hmem_empty hsame.2.2.2.1 hk4'
  · exact hmem_empty hsame.2.2.2.2 hk5

/-- Under `TableAdmittedAt`, no address `x ∉ order_role` can have `Core.keyOf t x ∈ pre.state.keys`,
 nor can `Core.keyOf t x = Ix.Kernel.quotSoundName`. -/
theorem keyOf_nonRole_disjoint_prelude
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    {x : _root_.Address} (hx : x ∉ order_role) :
    Core.keyOf t x ∉ pre.state.keys ∧ Core.keyOf t x ≠ Ix.Kernel.quotSoundName := by
  have hrole_in : ∀ s : Ix.Kernel.Role,
      IxVM.Refinement.compilerTrust s = false → Core.keyOf t x ≠ .role s := by
    intro s hct heq
    unfold Core.keyOf at heq
    cases hfind : t.bound.find? (·.2 == x) with
    | none => rw [hfind] at heq; cases heq
    | some p =>
      rcases p with ⟨r, x'⟩
      rw [hfind] at heq
      injection heq with hrs
      subst r
      have hp_mem : (s, x') ∈ t.bound.toList :=
        Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)
      have hp_beq : (s, x').2 == x :=
        list_find?_pred (xs := t.bound.toList) (by rw [Array.find?_toList]; exact hfind)
      have hp_eq : x' = x := beq_iff_eq.mp hp_beq
      subst x'
      have haddr := Ix.Cert.ReadingKeys.addressOf_of_bound hba.wellFormed hp_mem
      have hb : IxVM.Refinement.BindingSeeds t x := Or.inl ⟨s, hct, haddr⟩
      exact hx ((hadm.closureOrder.complete x).mpr (.seed hb (hadm.seeds_in x hb)))
  refine ⟨fun hmem => ?_, hrole_in .quotSound rfl⟩
  obtain ⟨s, hs, heq⟩ := prelude_state_keys_roles hadm.preludeFor (Core.keyOf t x) hmem
  exact hrole_in s (prelude_role_not_compilerTrust s hs) heq

/-- Committing a non-inductive `Read` (`owners = []`, `blocks = []`) whose declarations are
non-`basisDecl` and named by `Core.keyOf t x` (`x ∉ order_role`) preserves `SameAt pre.state`. -/
theorem commit_sameAt_of_nonRole
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role st : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {r : Ix.Kernel.Reader.Read .anon}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    (hsame : ∀ k ∈ pre.state.keys, st.SameAt pre.state k)
    (hown : r.owners = [])
    (hblk : r.blocks = [])
    (hnb : ∀ d ∈ r.decls.toList, ∀ k, d ≠ .basisDecl k)
    (hnames : ∀ d ∈ r.decls.toList, ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role) :
    ∀ k ∈ pre.state.keys, (st.commit r).SameAt pre.state k := by
  intro k hk
  have hstep : (st.commit r).SameAt st k := by
    refine commit_other_any st r k (fun d hd => ⟨hnb d hd, fun hn => ?_⟩)
      (by rw [hown]; simp) (by rw [hblk]; simp)
    obtain ⟨x, rfl, hx⟩ := hnames d hd k hn
    exact (keyOf_nonRole_disjoint_prelude hadm hba hx).1 hk
  exact sameAt_trans_any hstep (hsame k hk)

/-! ## Section 3: `streamContext` store/blob helpers & `MemberReader.read` congruence -/

private theorem mem_decodedOf {E : Ixon.Env} {order : List _root_.Address}
    {a : _root_.Address} {c : Ixon.Constant}
    (h : (a, c) ∈ Ix.Cert.Stream.decodedOf E order) :
    a ∈ order ∧ Ix.Cert.recordAt E a = some c := by
  unfold Ix.Cert.Stream.decodedOf at h
  obtain ⟨a', ha', hmap⟩ := List.mem_filterMap.mp h
  cases hrec : Ix.Cert.recordAt E a' with
  | none => simp [hrec] at hmap
  | some c' =>
    simp only [hrec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
    obtain ⟨h1, h2⟩ := hmap
    subst a'; subst c'
    exact ⟨ha', hrec⟩

private theorem mem_decodedOf_of_mem {E : Ixon.Env} {order : List _root_.Address}
    {a : _root_.Address} {c : Ixon.Constant}
    (ha : a ∈ order) (hrec : Ix.Cert.recordAt E a = some c) :
    (a, c) ∈ Ix.Cert.Stream.decodedOf E order := by
  unfold Ix.Cert.Stream.decodedOf
  exact List.mem_filterMap.mpr ⟨a, ha, by simp [hrec]⟩

private theorem toUInt64_toNat_eq {n : Nat} (hn : n < UInt64.size) :
    n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- `AuthenticExactStore` holds for `streamContext` on `(E, order)` whenever `E` has pure-BLAKE3
authenticated exact-decoded constants and `preludeFor t = .ok pre`. -/
theorem streamContext_authenticExactStore (hRP : RolePreludeInputs)
    {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    {E : Ixon.Env} {order : List _root_.Address}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (hauth_rec : ∀ a lc, E.consts.get? a = some lc → _root_.Address.blake3Pure lc.rawBytes = a)
    (hdec : ∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c) :
    AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)).store := by
  intro a c hst
  rcases Ix.Cert.ReadingKeys.context_store hst with hmem_dec | hmem_fb
  · obtain ⟨ha_ord, hrecE⟩ := mem_decodedOf hmem_dec
    unfold Ix.Cert.recordAt at hrecE
    cases hget : E.consts.get? a with
    | none => rw [hget] at hrecE; cases hrecE
    | some lc =>
      rw [hget] at hrecE
      obtain ⟨c', hlc_c', hex⟩ := hdec a ha_ord lc hget
      have hc_eq : c' = c := Option.some.inj (hlc_c'.symm.trans hrecE)
      subst c'
      exact ⟨lc.rawBytes, hauth_rec a lc hget, hex⟩
  · obtain ⟨_, hbl, hwf, _⟩ :=
      hRP.serConstant_mem_committedImages hpre hmem_fb
    exact ⟨Ixon.serConstant c, hbl, Ixon.Verify.deConstantExact_serConstant c hwf⟩

private theorem blobFold_get_of_mem {a : _root_.Address} {bs : ByteArray} :
    ∀ (xs : List (_root_.Address × ByteArray)) (m : Std.HashMap _root_.Address ByteArray),
      (xs.map Prod.fst).Nodup →
      (a, bs) ∈ xs →
      m.contains a = false →
      (xs.foldl (fun acc (k, v) => if acc.contains k then acc else acc.insert k v) m)[a]? = some bs := by
  intro xs
  induction xs with
  | nil =>
    intro _ _ hm _
    nomatch hm
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    intro m hnd hm hnc
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with hhd | htl
    · obtain ⟨hk_eq, hv_eq⟩ := Prod.mk.inj hhd
      subst k; subst v
      simp only [hnc, Bool.false_eq_true, ↓reduceIte]
      have hpres : ∀ (ys : List (_root_.Address × ByteArray))
          (acc : Std.HashMap _root_.Address ByteArray),
          acc[a]? = some bs →
          (ys.foldl (fun s (k', v') => if s.contains k' then s else s.insert k' v') acc)[a]? =
            some bs := by
        intro ys
        induction ys with
        | nil => intro _ h; exact h
        | cons p rest ihy =>
          rcases p with ⟨k', v'⟩
          intro acc hacc
          simp only [List.foldl_cons]
          split
          · exact ihy acc hacc
          · rename_i hnk'
            apply ihy
            have hne : k' ≠ a := by
              intro heq; subst k'
              rw [Std.HashMap.contains_eq_isSome_getElem?, hacc] at hnk'
              exact hnk' rfl
            rw [Std.HashMap.getElem?_insert]
            simp [hne, hacc]
      exact hpres tl (m.insert a bs) (by simp)
    · have hne : k ≠ a := fun heq => by
        subst k
        exact hnd.1 (List.mem_map.mpr ⟨(a, bs), htl, rfl⟩)
      split
      · exact ih m hnd.2 htl hnc
      · apply ih (m.insert k v) hnd.2 htl
        rw [Std.HashMap.contains_insert]
        simp [hne, hnc]

/-- Every blob `(x, bs) ∈ blobsOf E order` is returned by `cx.blob x` in `streamContext`. -/
theorem streamContext_blob_of_mem_blobsOf
    {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    {E : Ixon.Env} {order : List _root_.Address}
    {x : _root_.Address} {bs : ByteArray}
    (hm : (x, bs) ∈ Ix.Cert.blobsOf E order) :
    (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)).blob x =
      some bs := by
  have hnd := Ix.Cert.Stream.blobsOf_keys E order
  change ((Ix.Cert.blobsOf E order ++ pre.blobs).foldl
    (fun (m : Std.HashMap _root_.Address ByteArray) (a, b) =>
      if m.contains a then m else m.insert a b) {})[x]? = some bs
  rw [List.foldl_append]
  have h1 := blobFold_get_of_mem (Ix.Cert.blobsOf E order) {} hnd hm (by simp)
  have hpres : ∀ (ys : List (_root_.Address × ByteArray))
      (acc : Std.HashMap _root_.Address ByteArray),
      acc[x]? = some bs →
      (ys.foldl (fun s (k', v') => if s.contains k' then s else s.insert k' v') acc)[x]? =
        some bs := by
    intro ys
    induction ys with
    | nil => intro _ h; exact h
    | cons p rest ihy =>
      rcases p with ⟨k', v'⟩
      intro acc hacc
      simp only [List.foldl_cons]
      split
      · exact ihy acc hacc
      · rename_i hnk'
        apply ihy
        have hne : k' ≠ x := by
          intro heq; subst heq
          rw [Std.HashMap.contains_eq_isSome_getElem?, hacc] at hnk'
          exact hnk' rfl
        rw [Std.HashMap.getElem?_insert]
        simp [hne, hacc]
  exact hpres pre.blobs _ h1

/-- Any blob `(x, bs)` in `E.blobs` referenced via `x ∈ c.refs` by a record `(owner, c)` with
`owner ∈ order` and `recordAt E owner = some c` belongs to `blobsOf E order`. -/
theorem mem_blobsOf_of_ref {E : Ixon.Env} {order : List _root_.Address}
    {owner x : _root_.Address} {c : Ixon.Constant} {bs : ByteArray}
    (hown : owner ∈ order) (hrec : Ix.Cert.recordAt E owner = some c)
    (href : x ∈ c.refs) (hblob : E.blobs.get? x = some bs) :
    (x, bs) ∈ Ix.Cert.blobsOf E order := by
  unfold Ix.Cert.blobsOf
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [Std.HashMap.get?_eq_getElem?] at hblob
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hblob
  · have hmem_used : ∀ (ys : List _root_.Address) (init : Std.HashSet _root_.Address),
        (owner ∈ ys ∨ init.contains x = true) →
        (ys.foldl (fun s a => match Ix.Cert.recordAt E a with
          | some c' => c'.refs.foldl (·.insert ·) s
          | none => s) init).contains x = true := by
      intro ys
      induction ys with
      | nil =>
        intro init h
        rcases h with hm | hc
        · nomatch hm
        · exact hc
      | cons hd tl ih =>
        intro init h
        simp only [List.foldl_cons]
        have hpres_arr : ∀ (zs : List _root_.Address) (s : Std.HashSet _root_.Address),
            (x ∈ zs ∨ s.contains x = true) →
            (zs.foldl (·.insert ·) s).contains x = true := by
          intro zs
          induction zs with
          | nil =>
            intro s hs
            rcases hs with hm | hc
            · nomatch hm
            · exact hc
          | cons z ztl ihz =>
            intro s hs
            simp only [List.foldl_cons]
            apply ihz
            rcases hs with hm | hc
            · rcases List.mem_cons.mp hm with rfl | hztl
              · exact Or.inr (by simp)
              · exact Or.inl hztl
            · exact Or.inr (by rw [Std.HashSet.contains_insert]; simp [hc])
        rcases h with hm | hc
        · rcases List.mem_cons.mp hm with rfl | htl
          · apply ih
            rw [hrec]
            dsimp only
            rw [← Array.foldl_toList]
            exact Or.inr (hpres_arr c.refs.toList init
              (Or.inl (Array.mem_toList_iff.mpr href)))
          · exact ih _ (Or.inl htl)
        · apply ih
          cases hhd : Ix.Cert.recordAt E hd with
          | none => exact Or.inr hc
          | some c' =>
            dsimp only
            rw [← Array.foldl_toList]
            exact Or.inr (hpres_arr c'.refs.toList init (Or.inr hc))
    exact hmem_used order {} (Or.inl hown)

/-- Restricting the blob table of a `RawConvExpr` to addresses in `refs` preserves `RawConvExpr`. -/
theorem rawConvExpr_filter_refs
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr refs recurAddrs univs sharing blobs h bound e kp) :
    L1.RawConvExpr refs recurAddrs univs sharing
      (blobs.filter (fun p => refs.contains p.1)) h bound e kp := by
  induction raw with
  | var h1 h2 => exact .var h1 h2
  | sort h1 h2 h3 h4 => exact .sort h1 h2 h3 h4
  | ref h1 h2 h3 h4 h5 h6 h7 => exact .ref h1 h2 h3 h4 h5 h6 h7
  | recur h1 h2 h3 h4 h5 h6 h7 => exact .recur h1 h2 h3 h4 h5 h6 h7
  | prj h1 h2 h3 h4 h5 _ h7 ih => exact .prj h1 h2 h3 h4 h5 ih h7
  | str h1 href hmem h4 h5 h6 =>
    have hc : refs.contains _ = true := List.contains_iff_mem.mpr (List.mem_of_getElem? href)
    exact .str h1 href (List.mem_filter.mpr ⟨hmem, hc⟩) h4 h5 h6
  | nat h1 href hmem h4 h5 h6 h7 h8 =>
    have hc : refs.contains _ = true := List.contains_iff_mem.mpr (List.mem_of_getElem? href)
    exact .nat h1 href (List.mem_filter.mpr ⟨hmem, hc⟩) h4 h5 h6 h7 h8
  | app _ _ h3 ih1 ih2 => exact .app ih1 ih2 h3
  | lam h1 _ _ h4 ih1 ih2 => exact .lam h1 ih1 ih2 h4
  | all h1 _ _ h4 ih1 ih2 => exact .all h1 ih1 ih2 h4
  | letE _ _ _ h4 ih1 ih2 ih3 => exact .letE ih1 ih2 ih3 h4
  | share h1 h2 _ ih => exact .share h1 h2 ih

/-- Congruence of `MemberReader.read` across two reader contexts and `self` callbacks that agree on
`keyAt`, `recurAddrs`, and `blobs`. In particular, when `recurAddrs = []`, any `self₁` and `self₂`
produce the identical `Core.KExpr`. -/
theorem memberReader_read_congr_of_rawConvExpr
    {cx₁ cx₂ : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {param : Nat → Ix.Kernel.LevelParam}
    {self₁ self₂ : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkey : ∀ a, cx₁.keyAt a = cx₂.keyAt a)
    (hself : ∀ i a, recurAddrs[i]? = some a →
      ∃ k, self₁ i = some (.ok k) ∧ self₂ i = some (.ok k))
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx₁.blob a = some bs ∧ cx₂.blob a = some bs)
    {h : Heap F} {e : Ixon.Expr} {kp : SourceValue F} {E_rd : Core.KExpr}
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (hrd₁ : (Ix.Kernel.Reader.MemberReader.mk' cx₁ src param self₁).read e = .ok E_rd) :
    (Ix.Kernel.Reader.MemberReader.mk' cx₂ src param self₂).read e = .ok E_rd := by
  obtain ⟨hecx₁, htbl₁⟩ := L1.memberReader_mk'_eq cx₁ src param self₁
  obtain ⟨hecx₂, htbl₂⟩ := L1.memberReader_mk'_eq cx₂ src param self₂
  unfold Ix.Kernel.Reader.MemberReader.read at hrd₁ ⊢
  rw [hecx₁, htbl₁, ← List.take_length (l := src.sharing.toList)] at hrd₁
  rw [hecx₂, htbl₂, ← List.take_length (l := src.sharing.toList)]
  let ecx₁ : Ix.Kernel.Reader.ECx .anon :=
    ⟨cx₁, src, src.univs.map (Ix.Kernel.Reader.convUniv param), self₁⟩
  let ecx₂ : Ix.Kernel.Reader.ECx .anon :=
    ⟨cx₂, src, src.univs.map (Ix.Kernel.Reader.convUniv param), self₂⟩
  have hgo : ∀ {bnd : Nat} {e' : Ixon.Expr} {kp' : SourceValue F},
      L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
        h bnd e' kp' →
      ∀ {n : Nat} {E' : Core.KExpr},
        n ≤ src.sharing.toList.length →
        (bnd ≤ n ∨ n = src.sharing.toList.length) →
        Ix.Kernel.Reader.convExpr ecx₁ (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) e' =
          .ok E' →
        Ix.Kernel.Reader.convExpr ecx₂ (L1.buildShareTbl ecx₂ (src.sharing.toList.take n)) e' =
          .ok E' := by
    intro bnd e' kp' r'
    induction r' with
    | var _ _ => intro _ _ _ _ h1; exact h1
    | sort _ _ _ _ => intro _ _ _ _ h1; exact h1
    | @ref _ _ rIdx uIdxs _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ _ _ _ h1
      have hk_eq : ecx₁.keyAt rIdx = ecx₂.keyAt rIdx := by
        simp only [Ix.Kernel.Reader.ECx.keyAt, ecx₁, ecx₂]
        cases src.refs[rIdx.toNat]? <;> simp [hkey]
      have hl_eq : ecx₁.levels uIdxs = ecx₂.levels uIdxs := rfl
      simpa only [Ix.Kernel.Reader.convExpr, hk_eq, hl_eq] using h1
    | @recur _ _ rIdx uIdxs a _ _ _ _ _ hrec _ _ _ _ _ =>
      intro _ _ _ _ h1
      obtain ⟨k, hs₁, hs₂⟩ := hself rIdx.toNat a hrec
      have hl_eq : ecx₁.levels uIdxs = ecx₂.levels uIdxs := rfl
      simpa only [Ix.Kernel.Reader.convExpr, ecx₁, ecx₂, hs₁, hs₂, hl_eq] using h1
    | @prj _ _ tIdx _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro n _ hn hbnd h1
      have hk_eq : ecx₁.keyAt tIdx = ecx₂.keyAt tIdx := by
        simp only [Ix.Kernel.Reader.ECx.keyAt, ecx₁, ecx₂]
        cases src.refs[tIdx.toNat]? <;> simp [hkey]
      simp only [Ix.Kernel.Reader.convExpr] at h1 ⊢
      rw [hk_eq] at h1
      cases hk2 : ecx₂.keyAt tIdx with
      | error _ => rw [hk2] at h1; simp [bind, Except.bind] at h1
      | ok k =>
        rw [hk2] at h1
        simp only [bind, Except.bind] at h1
        cases hsub : Ix.Kernel.Reader.convExpr ecx₁
            (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) _ with
        | error _ => rw [hsub] at h1; cases h1
        | ok Ein =>
          rw [hsub] at h1
          rw [ih hn hbnd hsub]
          exact h1
    | @str _ _ bIdx a bs _ _ _ href hmem _ _ _ =>
      intro _ _ _ _ h1
      have href_arr : src.refs[bIdx.toNat]? = some a := by
        rwa [← Array.getElem?_toList]
      obtain ⟨hb1, hb2⟩ := hblob a ⟨bs.toArray⟩ hmem
      have hba : ecx₁.blobAt bIdx = ecx₂.blobAt bIdx := by
        simp [Ix.Kernel.Reader.ECx.blobAt, ecx₁, ecx₂, href_arr, hb1, hb2]
      simpa only [Ix.Kernel.Reader.convExpr, hba] using h1
    | @nat _ _ bIdx a bs _ _ _ href hmem _ _ _ _ _ =>
      intro _ _ _ _ h1
      have href_arr : src.refs[bIdx.toNat]? = some a := by
        rwa [← Array.getElem?_toList]
      obtain ⟨hb1, hb2⟩ := hblob a ⟨bs.toArray⟩ hmem
      have hna : ecx₁.natAt bIdx = ecx₂.natAt bIdx := by
        simp [Ix.Kernel.Reader.ECx.natAt, Ix.Kernel.Reader.ECx.blobAt, ecx₁, ecx₂, href_arr,
          hb1, hb2]
      simpa only [Ix.Kernel.Reader.convExpr, hna] using h1
    | app _ _ _ ihf iha =>
      intro n _ hn hbnd h1
      simp only [Ix.Kernel.Reader.convExpr] at h1 ⊢
      cases hf : Ix.Kernel.Reader.convExpr ecx₁
          (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) _ with
      | error _ => rw [hf] at h1; simp [bind, Except.bind] at h1
      | ok Ef =>
        rw [hf] at h1
        simp only [bind, Except.bind] at h1
        cases ha : Ix.Kernel.Reader.convExpr ecx₁
            (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) _ with
        | error _ => rw [ha] at h1; cases h1
        | ok Ea =>
          rw [ha] at h1
          rw [ihf hn hbnd hf, iha hn hbnd ha]
          exact h1
    | lam _ _ _ _ iht ihb =>
      intro n _ hn hbnd h1
      simp only [Ix.Kernel.Reader.convExpr] at h1 ⊢
      cases ht : Ix.Kernel.Reader.convExpr ecx₁
          (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) _ with
      | error _ => rw [ht] at h1; simp [bind, Except.bind] at h1
      | ok Et =>
        rw [ht] at h1
        simp only [bind, Except.bind] at h1
        cases hb : Ix.Kernel.Reader.convExpr ecx₁
            (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) _ with
        | error _ => rw [hb] at h1; cases h1
        | ok Eb =>
          rw [hb] at h1
          rw [iht hn hbnd ht, ihb hn hbnd hb]
          exact h1
    | all _ _ _ _ iht ihb =>
      intro n _ hn hbnd h1
      simp only [Ix.Kernel.Reader.convExpr] at h1 ⊢
      cases ht : Ix.Kernel.Reader.convExpr ecx₁
          (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) _ with
      | error _ => rw [ht] at h1; simp [bind, Except.bind] at h1
      | ok Et =>
        rw [ht] at h1
        simp only [bind, Except.bind] at h1
        cases hb : Ix.Kernel.Reader.convExpr ecx₁
            (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) _ with
        | error _ => rw [hb] at h1; cases h1
        | ok Eb =>
          rw [hb] at h1
          rw [iht hn hbnd ht, ihb hn hbnd hb]
          exact h1
    | letE _ _ _ _ iht ihv ihb =>
      intro n _ hn hbnd h1
      simp only [Ix.Kernel.Reader.convExpr] at h1 ⊢
      cases ht : Ix.Kernel.Reader.convExpr ecx₁
          (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) _ with
      | error _ => rw [ht] at h1; simp [bind, Except.bind] at h1
      | ok Et =>
        rw [ht] at h1
        simp only [bind, Except.bind] at h1
        cases hv : Ix.Kernel.Reader.convExpr ecx₁
            (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) _ with
        | error _ => rw [hv] at h1; cases h1
        | ok Ev =>
          rw [hv] at h1
          cases hb : Ix.Kernel.Reader.convExpr ecx₁
              (L1.buildShareTbl ecx₁ (src.sharing.toList.take n)) _ with
          | error _ => rw [hb] at h1; cases h1
          | ok Eb =>
            rw [hb] at h1
            rw [iht hn hbnd ht, ihv hn hbnd hv, ihb hn hbnd hb]
            exact h1
    | @share b2 idx2 s2 _ hidx2 hsh2 _ ih =>
      intro n _ hn hbnd h1
      have hi_len : idx2.toNat < src.sharing.toList.length :=
        (List.getElem?_eq_some_iff.mp hsh2).1
      have hi_n : idx2.toNat < n := by rcases hbnd with hb | rfl <;> omega
      simp only [Ix.Kernel.Reader.convExpr] at h1 ⊢
      rw [L1.buildShareTbl_take_getElem? ecx₁ src.sharing.toList hi_n hsh2] at h1
      rw [L1.buildShareTbl_take_getElem? ecx₂ src.sharing.toList hi_n hsh2]
      exact ih (Nat.le_of_lt hi_len) (Or.inl (Nat.le_refl _)) h1
  exact hgo raw (Nat.le_refl _) (Or.inr rfl) hrd₁

private theorem ctx_with_blob_keyAt (cx : Ix.Kernel.Reader.Ctx .anon)
    (b' : _root_.Address → Option ByteArray) (a : _root_.Address) :
    ({ cx with blob := b' } : Ix.Kernel.Reader.Ctx .anon).keyAt a = cx.keyAt a := by
  cases cx
  rfl

private theorem memberReader_read_with_blob
    (cx : Ix.Kernel.Reader.Ctx .anon) (b' : _root_.Address → Option ByteArray)
    {src : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {blobs : List (_root_.Address × ByteArray)}
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs ∧ b' a = some bs)
    {h : Heap F} {e : Ixon.Expr} {kp : SourceValue F} {E_rd : Core.KExpr}
    (raw : L1.RawConvExpr src.refs.toList [] src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (hrd : (Ix.Kernel.Reader.MemberReader.mk' cx src param self).read e = .ok E_rd) :
    (Ix.Kernel.Reader.MemberReader.mk' { cx with blob := b' } src param self).read e = .ok E_rd :=
  memberReader_read_congr_of_rawConvExpr (cx₁ := cx) (cx₂ := { cx with blob := b' })
    (self₁ := self) (self₂ := self) (recurAddrs := [])
    (fun a => (ctx_with_blob_keyAt cx b' a).symm)
    (fun _ _ h => nomatch h)
    hblob raw hrd

/-- Pointwise-at-`Core.dprjAddr owner i` version of `streamContext_memberKey_dprj`: only requires
`cx.store` presence if `Core.dprjAddr owner i` itself is bound in `t.bound` (which follows from
`TableAdmittedAt.boundConsistent`). -/
theorem streamContext_memberKey_dprj_at {t : Ix.Kernel.RoleTable}
    {pre : Ix.Kernel.Reader.Prelude .anon}
    {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store)
    (hchk : t.check = .ok ())
    {owner : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {i : Nat} {d : Ixon.Definition}
    (hcb : (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
      owner = some cb)
    (hinfo : cb.info = .muts ms)
    (hms : ms[i]? = some (.defn d))
    (hi : i < UInt64.size)
    (hbound_at : ∀ r, (r, Core.dprjAddr owner i) ∈ t.bound.toList →
      ∃ c_b, (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
        (Core.dprjAddr owner i) = some c_b)
    (hdprj_eq : ∀ c',
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
        (Core.dprjAddr owner i) = some c' →
      c' = ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩) :
    (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).memberKey
      (.member owner i) = .ok (Core.keyOf t (Core.dprjAddr owner i)) := by
  let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint
  change cx.store owner = some cb at hcb
  change cx.memberKey (.member owner i) = .ok (Core.keyOf t (Core.dprjAddr owner i))
  let c_proj : Ixon.Constant := ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩
  have hi_toNat : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt hi
  have hres_proj : ∀ {a' : _root_.Address}, cx.store a' = some c_proj →
      Ix.Kernel.Reader.resolve cx.store a' = some (.member owner i) := by
    intro a' ha'
    unfold Ix.Kernel.Reader.resolve Ix.Kernel.Reader.resolveSource
    simp [ha', c_proj, Ix.Kernel.Reader.emptyTables, hcb, hinfo, hi_toNat, hms]
  have hres_inv : ∀ {a' : _root_.Address},
      Ix.Kernel.Reader.resolve cx.store a' = some (.member owner i) →
      a' = Core.dprjAddr owner i := by
    intro a' ha'
    unfold Ix.Kernel.Reader.resolve at ha'
    obtain ⟨c', hc', hsrc⟩ := Option.bind_eq_some_iff.mp ha'
    rcases Ix.Cert.ReadingKeys.resolveSource_cases hsrc with ⟨heq, hns⟩ | hpat
    · injection heq with hown _
      subst hown
      rw [hc'] at hcb
      injection hcb with hcc
      subst hcc
      exact absurd hinfo (hns ms)
    · simp only [Ix.Cert.ReadingKeys.projectionAt, Ix.Cert.ReadingKeys.memberAt,
        bind, Option.bind, hcb, hinfo, hms, Option.some.injEq] at hpat
      rcases hpat with rfl
      obtain ⟨bytes, hbl, hdec⟩ := hauth a' c_proj hc'
      obtain ⟨hbs, _⟩ := deConstantExact_proj_eq_serConstant hdec rfl trivial
      rw [hbs] at hbl
      exact hbl.symm
  have hroles : cx.roles = Ix.Kernel.Reader.bindingsOf cx.store t := rfl
  cases hrole : cx.roles.names[Ix.Kernel.ConstRef.member owner i]? with
  | some k =>
    obtain ⟨r, rfl⟩ := Ix.Cert.ReaderUnits.bindingsOf_keyed cx.store t (.member owner i) k
      (by rwa [← hroles])
    obtain ⟨a', hmem', hres'⟩ := Ix.Cert.ReaderKeys.bindings_role_origin cx.store t
      (by rwa [← hroles])
    have ha'_eq := hres_inv hres'
    subst ha'_eq
    rw [keyOf_eq_of_bound hchk hmem']
    unfold Ix.Kernel.Reader.Ctx.memberKey
    rw [hrole]
    rfl
  | none =>
    have hunb : ∀ r, (r, Core.dprjAddr owner i) ∉ t.bound.toList := by
      intro r hm
      obtain ⟨c_b, hc_b⟩ := hbound_at r hm
      have hc_eq := hdprj_eq c_b hc_b
      subst hc_eq
      have hres_b := hres_proj hc_b
      have hbind := Ix.Cert.ReadingKeys.bindings_bound hchk hm hres_b (fun _ h' => hres_inv h')
      rw [← hroles, hrole] at hbind
      cases hbind
    rw [keyOf_eq_of_unbound hunb]
    have hsing_none : Ix.Kernel.Reader.singletonAt cx.store (.member owner i) = none := by
      cases i with
      | zero => simp [Ix.Kernel.Reader.singletonAt, hcb, hinfo]
      | succ _ => rfl
    have hrec_addr : cx.reconstruct (.member owner i) = some (Core.dprjAddr owner i) :=
      projectionAddress_dprj hcb hinfo hms hi
    have ha_of : cx.addressOf (.member owner i) = .ok (Core.dprjAddr owner i) := by
      unfold Ix.Kernel.Reader.Ctx.addressOf
      cases haddr : cx.keys.address[Ix.Kernel.ConstRef.member owner i]? with
      | some a' =>
        have hsnd := cx.keys.address_sound (.member owner i) a' haddr
        rw [hres_inv hsnd]
        rfl
      | none =>
        rw [hsing_none, hrec_addr]
        rfl
    have hcompat : Ix.Cert.ReaderKeys.ReconCompatible cx (· = .member owner i) := by
      intro ref a' href _ _ _ hrec hcached
      subst href
      rw [hrec_addr] at hrec
      injection hrec with ha'_eq
      subst ha'_eq
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hcached
      have hsnd := cx.keys.byAddress_sound (Core.dprjAddr owner i) v hv
      cases hst_p : cx.store (Core.dprjAddr owner i) with
      | none => simp [Ix.Kernel.Reader.keyOfAddress, Ix.Kernel.Reader.resolve, hst_p] at hsnd
      | some c' =>
        have hc' := hdprj_eq c' hst_p
        subst hc'
        exact hres_proj hst_p
    unfold Ix.Kernel.Reader.Ctx.memberKey
    rw [hrole, ha_of]
    simp only [bind, Except.bind]
    cases hby : cx.keys.byAddress[Core.dprjAddr owner i]? with
    | none => rfl
    | some v =>
      have hres_d := Ix.Cert.ReaderKeys.addressOf_resolves_of_cached hcompat rfl hrole ha_of
        (by rw [hby]; rfl)
      have hsnd := cx.keys.byAddress_sound (Core.dprjAddr owner i) v hby
      have hv : v = .id (Core.dprjAddr owner i) := by
        simpa [Ix.Kernel.Reader.keyOfAddress, hres_d, hrole, Ix.Kernel.Mode.addressId?] using hsnd.symm
      rw [hv]
      rfl

/-! ## Section 4: Quotient exclusion outside `order_role` -/

private theorem role_quot_step_local {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Core.W "KernelRoleSpec::role_quot" [] h r h' cs) :
    r = .field (Core.roleNum .quot) ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.role_quot.lookup
    (by simp [IxVM.KernelRoleSpec.role_quot, ControlLower.hasControl]) ev
  simp only [IxVM.KernelRoleSpec.role_quot] at d0
  obtain ⟨rfl, rfl, -⟩ := d0.literal_inv
  exact ⟨congrArg Value.field (by decide), rfl⟩

/-- No walked constant `a ∉ order_role` checked via `Claim.CheckedAtFull` can have `c.info = .quot q`:
`KernelCheck::check_quot` checks `KernelRoles::role_is` against one of the four quotient roles, all
of which have `compilerTrust = false` and therefore lie in `order_role`. -/
theorem not_quot_of_nonRole_checked
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {bAddr a : _root_.Address} {c : Ixon.Constant} {q : Ixon.Quotient}
    (hbound : IxVM.Consistency.Bounded calls)
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hrec₀ : Ix.Cert.recordAt E₀ a = some c)
    (hq : c.info = .quot q)
    (hnot_role : a ∉ order_role)
    (hchk : Claim.CheckedAtFull calls bAddr t a) :
    False := by
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    bytes, E_ld, hrc_pre, hrc_m, ha_pre, ha_m, hhash_ld, hblake_ld, _, hL1,
    hsub_ld, hld, ev_chk, _, _⟩ := checkedAtFull_loadedL1 hbound hchk
  obtain ⟨c_ld, hdec_ld, _, _, v', hld', hraw⟩ := hL1
  rw [hld] at hld'; injection hld' with hvv; subst hvv
  unfold Ix.Cert.recordAt at hrec₀
  cases hget₀ : E₀.consts.get? a with
  | none => rw [hget₀] at hrec₀; cases hrec₀
  | some lc₀ =>
    rw [hget₀] at hrec₀
    obtain ⟨hh₀, hbl₀⟩ := hload.1 a lc₀ hget₀
    obtain ⟨c₀, hlc₀, hex₀⟩ := hexact₀ a lc₀ hget₀
    have hc₀_eq : c₀ = c := Option.some.inj (hlc₀.symm.trans hrec₀)
    subst c₀
    have hraw_eq : bytes = lc₀.rawBytes := by
      by_contra hne
      exact hnoCol (Or.inl ⟨a, lc₀.rawBytes, bytes, Or.inr (Or.inr ⟨hh₀, hbl₀⟩),
        Core.hashed_mono hsub_ld hhash_ld, hne, hblake_ld⟩)
    rw [hraw_eq, hex₀] at hdec_ld
    injection hdec_ld with hcld
    subst c_ld
    rw [hblake_ld] at hraw
    unfold L1.RawCIRep at hraw
    rw [hq] at hraw
    obtain ⟨_, _, _, tyPtr, rfl, _⟩ := hraw
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn | Thm | Opaque
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [Core.kciEnum]
    | Quot _ m2 _ _ _ x_kind _ m1094 _ _ m1131 _ m1162 _ m1175 _ _
        ev14 _ _ _ _ hv1076 ev1106 hm1170 ev1143 ev1187 ev1209 _ =>
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv1076
      rcases hv1076 with ⟨_, _, rfl⟩
      have ext_all : Heap.Extends m_chk m1175 :=
        ev14.heap_extends.trans (ev1106.heap_extends.trans
          ((by rw [hm1170]; exact Heap.Extends.snoc _ _ : Heap.Extends m1094 m1162).trans
            (ev1143.heap_extends.trans ev1187.heap_extends)))
      cases «KernelCheck::check_quot».obs ev1209 with
      | run v67 m68 _ v87 _ _ sg75 ev100 heq131 _ _ _ =>
        have hro_spec : ∃ ro : Ix.Kernel.Role,
            IxVM.Refinement.compilerTrust ro = false ∧
            v67 = .field (Core.roleNum ro) ∧ m68 = m1175 := by
          cases sg75 with
          | Typ _ _ ev22 _ =>
            obtain ⟨hv, hm⟩ := role_quot_step_local ev22
            exact ⟨.quot, rfl, hv, hm⟩
          | Ctor _ _ _ ev36 _ =>
            obtain ⟨hv, hm⟩ := Core.role_quot_mk_step ⟨{}, .empty, t, none⟩ ev36 rfl
            exact ⟨.quotMk, rfl, hv, hm⟩
          | Lift _ _ _ _ ev50 _ =>
            obtain ⟨hv, hm⟩ := Core.role_quot_lift_step ⟨{}, .empty, t, none⟩ ev50 rfl
            exact ⟨.quotLift, rfl, hv, hm⟩
          | Ind _ _ _ _ _ ev64 _ =>
            obtain ⟨hv, hm⟩ := Core.role_quot_ind_step ⟨{}, .empty, t, none⟩ ev64 rfl
            exact ⟨.quotInd, rfl, hv, hm⟩
        obtain ⟨ro, hct, rfl, rfl⟩ := hro_spec
        cases «KernelRoles::role_is».obs ev100 with
        | n0_n0 _ _ _ _ _ _ _ _ _ _ he88 _ _ =>
          rw [he88] at heq131
          exact absurd (congrArg ZMod.val (Value.field.inj heq131)) (by decide)
        | other _ _ _ _ _ _ _ _ _ he102 _ _ =>
          rw [he102] at heq131
          exact absurd (congrArg ZMod.val (Value.field.inj heq131)) (by decide)
        | n0_other x10 y11 _ _ _ _ _ ev23 op47 op17 _ _ _ _ _ =>
          obtain rfl := Core.RolesAux.evalBinOp_add_field_inv op47
          obtain ⟨_, hx1, hx2⟩ := Core.RolesAux.evalBinOp_sub_eq_zero_inv op17
          have hx10 : x10 = .field (Core.roleNum ro + 1) := hx1.trans hx2.symm
          obtain ⟨_, hidx⟩ :=
            Claim.role_index_of_full_spec (hrc_m.mono ext_all)
              (Core.S0.addr_mono ext_all ha_m) ev23
          rcases hidx with ⟨hx0, _⟩ | ⟨ro₁, hxr, haddr₁⟩
          · exact Core.RolesAux.roleNum_add_one_ne_zero ro
              (Value.field.inj (hx10.symm.trans hx0))
          · obtain rfl := Core.RolesAux.roleNum_add_one_inj
              (Value.field.inj (hx10.symm.trans hxr))
            have hb : IxVM.Refinement.BindingSeeds t a := Or.inl ⟨ro, hct, haddr₁⟩
            exact hnot_role ((hadm.closureOrder.complete a).mpr (.seed hb (hadm.seeds_in a hb)))

/-! ## Section 5: Per-record `readRecordBare` + `CheckedConstOrigin` + `L1.RecordReadsAs` -/

/-- Helper: in `(E, order)` built via `Keep := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x`,
any `RawConvExpr` on `src` (at `src_addr ∈ order` with `WkAll calls b.address t E₀ src_addr` and
`recordAt E₀ src_addr = some src` and `recordAt E src_addr = some src`) validated by
`KernelCheck::safe_refs_only` has all reachable `.ref`/`.prj` targets resolving in `cx.keyAt` to
`Core.keyOf t`, and all its filtered blobs present in both `cx.blob` and `E_core.blobs`. -/
private theorem safe_rawConvExpr_ctx_ready
    (hSR : SafeRefsInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {seeds : List _root_.Address}
    {src_addr : _root_.Address} {src : Ixon.Constant}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {E_ld : Ixon.Env} {cs_load cs_sr : List (Call F)}
    {h₀ h_sr h'_sr : Heap F} {e : Ixon.Expr} {kp : SourceValue F}
    (hbound : IxVM.Consistency.Bounded calls)
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hblobs₀ : ∀ bytes, Hashed calls bytes →
      E₀.blobs.get? (_root_.Address.blake3Pure bytes) = some bytes)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hord : IxVM.Consistency.UsedClosureOrderAt t
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role))
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) order)
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.blobsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.hintsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)))).store)
    (hsrc_ord : src_addr ∈ order)
    (hsrc_rec₀ : Ix.Cert.recordAt E₀ src_addr = some src)
    (hsrc_recE : Ix.Cert.recordAt
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) src_addr = some src)
    (hsrc_wk : WkAll calls b.address t E₀ src_addr)
    (hdir : ∀ x ∈ IxVM.Consistency.exprRefIdxs e, x ∈ IxVM.Consistency.usedRefIdxs src)
    (hload_ld : IxVM.Consistency.LoadedBy cs_load E_ld)
    (hsub_ld : ∀ cl ∈ cs_load, cl ∈ calls)
    (hb_ld : L1.BlobTableLoaded E_ld blobs)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h₀ 4294967295 e kp)
    (hext_sr : Heap.Extends h₀ h_sr)
    (ev_sr : ObsFn Core.W "KernelCheck::safe_refs_only" [kp] h_sr (.field 1) h'_sr cs_sr)
    (hsub_sr : ∀ cl ∈ cs_sr, cl ∈ calls) :
    let Keep := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x
    let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
    let E_core := coreEnvRole E₀ Keep (roleSuppOf E_role order_role)
      (Ix.Cert.blobsOf E_role order_role) pre
    let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
    let blobs' := blobs.filter (fun p => src.refs.toList.contains p.1)
    L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs'
      h₀ 4294967295 e kp ∧
    (∀ x bs, (x, bs) ∈ blobs' → cx.blob x = some bs ∧ E_core.blobs.get? x = some bs) ∧
    (∀ idx ∈ reachRefsExpr (buildReachRefsTbl src.sharing.toList) e,
      ∀ r, src.refs[idx]? = some r → cx.keyAt r = .ok (Core.keyOf t r)) := by
  intro Keep E E_core cx blobs'
  have hnoCol_ld : ¬ L1.EnvInternalCollision E_ld := by
    rintro ⟨x, d, lc, hbl, hcn, hne⟩
    obtain ⟨hh_d, hblk_d⟩ := hload_ld.2 x d hbl
    obtain ⟨hh_c, hblk_c⟩ := hload_ld.1 x lc hcn
    exact hnoCol (Or.inl ⟨x, d, lc.rawBytes,
      Or.inr (Or.inr ⟨Core.hashed_mono hsub_ld hh_d, hblk_d⟩),
      Core.hashed_mono hsub_ld hh_c, hne.symm, hblk_c⟩)
  have raw' := rawConvExpr_filter_refs raw
  have hblobs_ok : ∀ x bs, (x, bs) ∈ blobs' →
      cx.blob x = some bs ∧ E_core.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hm_b, hc_ref⟩ := List.mem_filter.mp hm
    have hx_ref : x ∈ src.refs :=
      Array.mem_toList_iff.mp (List.contains_iff_mem.mp hc_ref)
    rcases hb_ld with hok_b | hcol_b
    · obtain ⟨hget_ld, _⟩ := hok_b x bs hm_b
      obtain ⟨hh_bs, hblk_bs⟩ := hload_ld.2 x bs hget_ld
      have hget₀ : E₀.blobs.get? x = some bs := by
        rw [← hblk_bs]
        exact hblobs₀ bs (Core.hashed_mono hsub_ld hh_bs)
      have hcont₀ : E₀.blobs.contains x = true := by
        rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hget₀]
        rfl
      have hgetE : E.blobs.get? x = some bs := by
        change (addBlobSupplements E₀.blobs (Ix.Cert.blobsOf E_role order_role)).get? x = some bs
        rw [addBlobSupplements_get?_of_contains E₀.blobs _ hcont₀]
        exact hget₀
      have hm_bof := mem_blobsOf_of_ref hsrc_ord hsrc_recE hx_ref hgetE
      exact ⟨streamContext_blob_of_mem_blobsOf hm_bof, hgetE⟩
    · exact absurd hcol_b hnoCol_ld
  have hnd_dec : ((Ix.Cert.Stream.decodedOf E order).map Prod.fst).Nodup :=
    hord.nodup.sublist (Ix.Cert.Stream.decodedOf_keys E order)
  have hkeys : ∀ idx ∈ reachRefsExpr (buildReachRefsTbl src.sharing.toList) e,
      ∀ r, src.refs[idx]? = some r → cx.keyAt r = .ok (Core.keyOf t r) := by
    intro idx hidx r hr
    have raw_sr := raw.mono hext_sr (fun _ hm => hm)
    obtain ⟨hnot_out_r, hres₀_r⟩ :=
      hSR.safe_expr_refs_resolve hbound hload hnoCol ev_sr hsub_sr raw_sr hidx hr
    have hidx_used : idx ∈ IxVM.Consistency.usedRefIdxs src :=
      reachRefs_subset_usedRefIdxs hdir idx hidx
    have hidx_s0 : idx ∈ Core.S0.usedRefIdxs src := by rwa [usedRefIdxs_eq]
    have hedge_r : Core.S0.WalkEdge E₀ src_addr r := ⟨src, hsrc_rec₀, Or.inr ⟨idx, hidx_s0, hr⟩⟩
    obtain ⟨hwk_r, _⟩ := (wkAll_closedSubwalk calls b.address t E₀).step src_addr r hsrc_wk hedge_r
    obtain ⟨c_r, hrec₀_r, hchk_r⟩ := (wkAll_closedSubwalk calls b.address t E₀).checked r hwk_r
    have hkeep_r : Keep r := Or.inr ⟨hwk_r, hnot_out_r⟩
    have hrecE_r : Ix.Cert.recordAt E r = some c_r :=
      recordAt_subEnv_of_keep E₀ Keep _ hkeep_r hrec₀_r
    have hreach_src := (hord.complete src_addr).mp hsrc_ord
    have hr_ord : r ∈ order :=
      (hord.complete r).mpr
        (.step hreach_src ⟨src, hsrc_recE, Or.inr ⟨⟨idx, hidx_used, hr⟩, contains_of_recordAt hrecE_r⟩⟩)
    have hst_r : cx.store r = some c_r :=
      streamContext_store_of_mem hnd_dec (mem_decodedOf_of_mem hr_ord hrecE_r)
    have hres_some := hres₀_r c_r hrec₀_r
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hres_some
    have hres_cx : Ix.Kernel.Reader.resolve cx.store r = some q := by
      unfold Ix.Kernel.Reader.resolve
      rw [hst_r]
      dsimp only [bind, Option.bind]
      unfold Ix.Kernel.Reader.resolveSource at hq ⊢
      cases hi_r : c_r.info with
      | defn _ | recr _ | axio _ | quot _ | muts _ =>
        dsimp only at hq ⊢
        exact hq
      | dPrj p | iPrj p | rPrj p | cPrj p =>
        dsimp only at hq ⊢
        have hblk_some : ∃ cb ms, Ix.Cert.recordAt E₀ p.block = some cb ∧ cb.info = .muts ms := by
          cases hgb : Ix.Cert.recordAt E₀ p.block with
          | none =>
            cases Ix.Kernel.Reader.emptyTables c_r <;>
              simp [hgb, guard, bind, Option.bind] at hq
          | some cb =>
            cases hcb_i : cb.info with
            | muts ms => exact ⟨cb, ms, rfl, hcb_i⟩
            | _ =>
              cases Ix.Kernel.Reader.emptyTables c_r <;>
                simp [hgb, hcb_i, guard, bind, Option.bind] at hq
        obtain ⟨cb, ms, hrec₀_blk, hcb_mut⟩ := hblk_some
        have hown_eq : Ix.Cert.ownerOf r c_r = p.block := by simp [Ix.Cert.ownerOf, hi_r]
        have hown_ne : Ix.Cert.ownerOf r c_r ≠ r := by
          rw [hown_eq]
          intro heq
          rw [heq, hrec₀_r] at hrec₀_blk
          injection hrec₀_blk with hcc
          subst cb
          rw [hi_r] at hcb_mut
          cases hcb_mut
        have hwk_blk : WkSafe calls b.address t E₀ p.block := by
          rw [← hown_eq]
          exact (wkSafe_owner_of_nonproj ⟨hwk_r, hnot_out_r⟩ hrec₀_r hown_ne (fun cb' hrec' => by
            rw [hown_eq, hrec₀_blk] at hrec'
            injection hrec' with heq'
            subst cb'
            simp [Ix.Cert.ownerOf, hcb_mut])).1
        have hrecE_blk : Ix.Cert.recordAt E p.block = some cb :=
          recordAt_subEnv_of_keep E₀ Keep _ (Or.inr hwk_blk) hrec₀_blk
        have hreach_r := (hord.complete r).mp hr_ord
        have hblk_ord : p.block ∈ order :=
          (hord.complete p.block).mpr
            (.step hreach_r ⟨c_r, hrecE_r, Or.inl ⟨hown_eq, by rwa [← hown_eq]⟩⟩)
        have hst_blk : cx.store p.block = some cb :=
          streamContext_store_of_mem hnd_dec (mem_decodedOf_of_mem hblk_ord hrecE_blk)
        rw [hst_blk]
        rw [hrec₀_blk] at hq
        exact hq
    exact streamContext_keyAt_eq_keyOf hauth hba.wellFormed hres_cx
  exact ⟨raw', hblobs_ok, hkeys⟩

/-- Injectivity of `Core.keyOf t` under a well-formed role table (`t.check = .ok ()`). -/
theorem keyOf_injective {t : Ix.Kernel.RoleTable} (hchk : t.check = .ok ())
    {x y : _root_.Address} (heq : Core.keyOf t x = Core.keyOf t y) :
    x = y := by
  unfold Core.keyOf at heq
  cases hfx : t.bound.find? (·.2 == x) with
  | none =>
    rw [hfx] at heq
    cases hfy : t.bound.find? (·.2 == y) with
    | none =>
      rw [hfy] at heq
      exact Ix.Kernel.Key.id.inj heq
    | some py =>
      rw [hfy] at heq
      cases heq
  | some px =>
    rcases px with ⟨rx, x'⟩
    rw [hfx] at heq
    cases hfy : t.bound.find? (·.2 == y) with
    | none =>
      rw [hfy] at heq
      cases heq
    | some py =>
      rcases py with ⟨ry, y'⟩
      rw [hfy] at heq
      injection heq with hry
      subst ry
      have hmx : (rx, x') ∈ t.bound.toList :=
        Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfx)
      have hmy : (rx, y') ∈ t.bound.toList :=
        Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfy)
      have hbx : x' = x := beq_iff_eq.mp (list_find?_pred (xs := t.bound.toList)
        (by rw [Array.find?_toList]; exact hfx))
      have hby : y' = y := beq_iff_eq.mp (list_find?_pred (xs := t.bound.toList)
        (by rw [Array.find?_toList]; exact hfy))
      subst x'; subst y'
      have hax := Ix.Cert.ReadingKeys.addressOf_of_bound hchk hmx
      have hay := Ix.Cert.ReadingKeys.addressOf_of_bound hchk hmy
      exact Option.some.inj (hax.symm.trans hay)

private theorem mem_sublist_of_cons_left {α : Type} {x : α} {ys cs : List α}
    (h : ∀ c ∈ x :: ys, c ∈ cs) : ∀ c ∈ ys, c ∈ cs :=
  fun c hm => h c (List.mem_cons_of_mem _ hm)

private theorem mem_sublist_of_append_right {α : Type} {xs ys cs : List α}
    (h : ∀ c ∈ xs ++ ys, c ∈ cs) : ∀ c ∈ ys, c ∈ cs :=
  fun c hm => h c (List.mem_append_right _ hm)

/-- Helper: unpack `is_unsafe_ci` on `defnValShape d` when `safetyDecline d = none`:
returns `.field 0` without heap growth. -/
private theorem is_unsafe_ci_defnValShape_safe {d : Ixon.Definition}
    {tyPtr valPtr hint v1 : SourceValue F} {h m2 : Heap F} {cs : List (Call F)}
    (hsafe : Ix.Kernel.Reader.safetyDecline d = none)
    (ev : ObsFn Core.W "KernelCheck::is_unsafe_ci"
      [L1.defnValShape d tyPtr valPtr hint] h v1 m2 cs) :
    v1 = .field 0 ∧ m2 = h := by
  cases hk : d.kind with
  | defn =>
    have hs : d.safety = .safe := by
      cases hds : d.safety <;>
        simp [Ix.Kernel.Reader.safetyDecline, Ix.Kernel.Reader.safetyDeclineOf, hk, hds] at hsafe ⊢
    simp only [L1.defnValShape, hk, hs] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Defn_Safe _ _ _ _ _ _ he hr _ => exact ⟨he, hr⟩
    | Defn_other _ _ _ _ _ _ hv hne _ _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hs_eq, _⟩
      exact (hne [] rfl (by simpa [L1.repDefSafetyVal] using hs_eq.symm)).elim
    | Axiom _ _ _ hv | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv
  | opaq =>
    have hns : (d.safety == .unsaf) = false := by
      simpa [Ix.Kernel.Reader.safetyDecline, Ix.Kernel.Reader.safetyDeclineOf, hk] using hsafe
    simp only [L1.defnValShape, hk, hns] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Opaque _ _ _ _ _ _ _ hv he hr _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hu_eq⟩
      rw [← hu_eq] at he
      exact ⟨he, hr⟩
    | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
    | Thm _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv
  | thm =>
    simp only [L1.defnValShape, hk] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Thm _ _ _ _ _ _ he hr _ => exact ⟨he, hr⟩
    | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
    | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv

private theorem is_unsafe_ci_axio_safe {ax : Ixon.Axiom}
    {tyPtr v1 : SourceValue F} {h m2 : Heap F} {cs : List (Call F)}
    (hsafe : ax.isUnsafe = false)
    (ev : ObsFn Core.W "KernelCheck::is_unsafe_ci"
      [.construct Core.kciEnum "Axiom"
        [.field (ax.lvls.toNat : F), tyPtr, L1.repBoolField ax.isUnsafe]] h v1 m2 cs) :
    v1 = .field 0 ∧ m2 = h := by
  cases «KernelCheck::is_unsafe_ci».obs ev with
  | Axiom _ _ _ hv he hr _ =>
    simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv
    rcases hv with ⟨_, _, hu⟩
    simp [hsafe, L1.repBoolField] at hu
    exact ⟨he.trans hu.symm, hr⟩
  | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
  | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
  | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
  | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
    simp [Core.kciEnum] at hv

/-- Standalone `.axio ax` bare reading + `CheckedConstOrigin.axiomDecl` + `L1.RecordReadsAs`. -/
private theorem checkedAxiom_of_checkedAtFull
    (hSR : SafeRefsInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role st : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {seeds : List _root_.Address}
    {a : _root_.Address} {c : Ixon.Constant} {ax : Ixon.Axiom}
    (hbound : IxVM.Consistency.Bounded calls)
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hblobs₀ : ∀ bytes, Hashed calls bytes →
      E₀.blobs.get? (_root_.Address.blake3Pure bytes) = some bytes)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hnoInt_core : ¬ L1.EnvInternalCollision
      (coreEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role) pre))
    (hsub_rec : ∀ x c_x,
      Ix.Cert.recordAt (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) x = some c_x →
      Ix.Cert.recordAt (coreEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role) pre) x = some c_x)
    (hord : IxVM.Consistency.UsedClosureOrderAt t
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role))
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) order)
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.blobsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.hintsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)))).store)
    (ha_ord : a ∈ order)
    (ha_not_role : a ∉ order_role)
    (hrec₀ : Ix.Cert.recordAt E₀ a = some c)
    (hrecE : Ix.Cert.recordAt
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) a = some c)
    (hwk : WkAll calls b.address t E₀ a)
    (hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a)
    (hinfo : c.info = .axio ax)
    (hchk : Claim.CheckedAtFull calls b.address t a) :
    let Keep := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x
    let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
    let E_core := coreEnvRole E₀ Keep (roleSuppOf E_role order_role)
      (Ix.Cert.blobsOf E_role order_role) pre
    let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
    ∃ ty₀ : Core.KExpr,
      let cv : Ix.Kernel.ConstantVal .anon := ⟨Core.keyOf t a, List.range ax.lvls.toNat, ty₀⟩
      let decl : Ix.Kernel.Declaration .anon := .axiomDecl cv
      let ci₀ : Ix.Kernel.ConstantInfo .anon := .axiomInfo cv
      Ix.Kernel.Reader.readRecordBare cx st a c = .ok { decls := #[decl] } ∧
      CheckedConstOrigin calls t b.address E_core order_role decl ∧
      L1.RecordReadsAs t E_core a c ci₀ ∧
      (IxVM.Consistency.inertKey (Core.keyOf t a) = false →
        ci₀ ∈ IxVM.Consistency.installs decl) := by
  intro Keep E E_core cx
  have hinLogic : IxVM.Consistency.InLogic c := by
    by_contra hnin
    exact hnot_out ⟨c, hrec₀, Or.inl hnin⟩
  have hsafe : ax.isUnsafe = false := by simpa [IxVM.Consistency.InLogic, hinfo] using hinLogic
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    bytes, E_ld, hrc_pre, hrc_m, ha_pre, ha_m, hhash_ld, hblake_ld, hload_ld, hL1,
    hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := checkedAtFull_loadedL1 hbound hchk
  obtain ⟨c_ld, hdec_ld, _, _, v', hld', hraw⟩ := hL1
  rw [hld] at hld'; injection hld' with hvv; subst hvv
  have hc_ld_eq : c_ld = c := by
    unfold Ix.Cert.recordAt at hrec₀
    cases hget₀ : E₀.consts.get? a with
    | none => rw [hget₀] at hrec₀; cases hrec₀
    | some lc₀ =>
      rw [hget₀] at hrec₀
      obtain ⟨hh₀, hbl₀⟩ := hload.1 a lc₀ hget₀
      obtain ⟨c₀, hlc₀, hex₀⟩ := hexact₀ a lc₀ hget₀
      have hraw_eq : bytes = lc₀.rawBytes := by
        by_contra hne
        exact hnoCol (Or.inl ⟨a, lc₀.rawBytes, bytes, Or.inr (Or.inr ⟨hh₀, hbl₀⟩),
          Core.hashed_mono hsub_ld hhash_ld, hne, hblake_ld⟩)
      rw [hraw_eq, hex₀] at hdec_ld
      have hcc : c₀ = c_ld := Except.ok.inj hdec_ld
      rw [hcc] at hlc₀
      exact Option.some.inj (hlc₀.symm.trans hrec₀)
  subst c_ld
  rw [hblake_ld] at hraw
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨blobs, hb_ld, hnlvls, tyPtr, rfl, raw_ty⟩ := hraw
  cases «KernelCheck::check_const».obs ev_chk with
  | Defn | Thm | Opaque | Quot
  | Induct_n0 | Induct_other_n0 | Induct_other_other
  | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
  | Rec_n0 | Rec_other =>
    simp_all [Core.kciEnum]
  | Axiom_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ _ _ _ =>
    have h10 := (is_unsafe_ci_axio_safe hsafe ev14).1
    exact absurd (congrArg ZMod.val (Value.field.inj h10)) (by decide)
  | Axiom_other_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq249 _ _ _ =>
    exact absurd (congrArg ZMod.val (Value.field.inj heq249)) (by decide)
  | Axiom_other_other v1 m2 cs12 x_nlvls x_ty _ _ m56 cs66 v92 m93 cs103 m124 _ m137 cs147
      v189 m190 cs201 ev14 hv37 ev68 hm132 ev105 ev149 _ ev203 hne255 _ _ hc263 =>
    obtain ⟨hv1, hm2⟩ := is_unsafe_ci_axio_safe hsafe ev14
    subst v1; subst m2
    simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv37
    obtain ⟨hx_nl, hx_ty, -⟩ := hv37
    subst x_nlvls; subst x_ty
    have hsub1 : ∀ cl ∈ (⟨"KernelCheck::validate_expr_well_scoped",
        [tyPtr, .field 0, .field (ax.lvls.toNat : F)], m_chk⟩ : Call F) ::
        (cs66 ++ ((⟨"KernelInfer::k_ensure_sort",
          [rc, tyPtr, .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m56.length],
          m124⟩ : Call F) :: (cs103 ++ ((⟨"KernelCheck::assert_safety", [.field 0, tyPtr], m93⟩ : Call F) ::
            (cs147 ++ ((⟨"KernelRoles::axiom_standing", [rc, ap], m137⟩ : Call F) :: cs201)))))),
        cl ∈ calls :=
      mem_sublist_of_append_right (mem_sublist_of_cons_left (by rwa [hc263] at hsub_chk))
    have hcl_val : (⟨"KernelCheck::validate_expr_well_scoped",
        [tyPtr, .field 0, .field (ax.lvls.toNat : F)], m_chk⟩ : Call F) ∈ calls :=
      hsub1 _ List.mem_cons_self
    have hsub2 := mem_sublist_of_append_right (mem_sublist_of_cons_left hsub1)
    have hcl_es : (⟨"KernelInfer::k_ensure_sort",
        [rc, tyPtr, .ptr (.enum Names.«Lists::Node<&KernelTypes::KExprNode>») m56.length],
        m124⟩ : Call F) ∈ calls :=
      hsub2 _ List.mem_cons_self
    have hsub_es : ∀ cl ∈ cs103, cl ∈ calls :=
      fun cl hm => (mem_sublist_of_cons_left hsub2) cl (List.mem_append_left _ hm)
    have hsub3 := mem_sublist_of_append_right (mem_sublist_of_cons_left hsub2)
    have hsub_as : ∀ cl ∈ cs147, cl ∈ calls :=
      fun cl hm => (mem_sublist_of_cons_left hsub3) cl (List.mem_append_left _ hm)
    have hsub4 := mem_sublist_of_append_right (mem_sublist_of_cons_left hsub3)
    have hcl_ax : (⟨"KernelRoles::axiom_standing", [rc, ap], m137⟩ : Call F) ∈ calls :=
      hsub4 _ List.mem_cons_self
    have hsub_ax : ∀ cl ∈ cs201, cl ∈ calls :=
      mem_sublist_of_cons_left hsub4
    obtain ⟨cs_sr, ev_sr, hcs147⟩ := assert_safety_zero_spec ev149
    have hsub_sr : ∀ cl ∈ cs_sr, cl ∈ calls :=
      fun cl hm => hsub_as cl (by rw [hcs147]; exact List.mem_cons_of_mem _ hm)
    have ext_m56_m124 : Heap.Extends m56 m124 := by
      rw [hm132]; exact Heap.Extends.snoc _ _
    have ext_m_m93 : Heap.Extends m_chk m93 :=
      ev68.heap_extends.trans (ext_m56_m124.trans ev105.heap_extends)
    have hdir_ty : ∀ x ∈ IxVM.Consistency.exprRefIdxs ax.typ, x ∈ IxVM.Consistency.usedRefIdxs c := by
      intro x hx
      simp [IxVM.Consistency.usedRefIdxs, hinfo, hx]
    obtain ⟨raw_ty', hblobs_ok, hkeys_ty⟩ :=
      safe_rawConvExpr_ctx_ready hSR hbound hadm hba hload hexact₀ hblobs₀ hnoCol hord hauth
        ha_ord hrec₀ hrecE hwk hdir_ty hload_ld hsub_ld hb_ld raw_ty ext_m_m93 ev_sr hsub_sr
    obtain ⟨ty₀, hrd_ty⟩ :=
      memberReader_read_ok_of_rawConvExpr (cx := cx) (param := id) (self := fun _ => none)
        raw_ty' (by simp) (fun x bs hm => (hblobs_ok x bs hm).1)
        (fun idx hidx r hr => ⟨Core.keyOf t r, hkeys_ty idx hidx r hr⟩)
    have hnd_dec : ((Ix.Cert.Stream.decodedOf E order).map Prod.fst).Nodup :=
      hord.nodup.sublist (Ix.Cert.Stream.decodedOf_keys E order)
    have hst_a : cx.store a = some c :=
      streamContext_store_of_mem hnd_dec (mem_decodedOf_of_mem ha_ord hrecE)
    have hmkey : cx.memberKey (.member a 0) = .ok (Core.keyOf t a) :=
      streamContext_memberKey_singleton hauth hba.wellFormed hst_a (by rw [hinfo]; trivial)
    have hread_rec :
        Ix.Kernel.Reader.readRecordBare cx st a c =
          .ok { decls := #[.axiomDecl ⟨Core.keyOf t a, List.range ax.lvls.toNat, ty₀⟩] } := by
      unfold Ix.Kernel.Reader.readRecordBare Ix.Kernel.Reader.readRecord
      simp [hinfo, hsafe, hmkey, hrd_ty, bind, Except.bind, pure, Except.pure]
    obtain ⟨_, hty_lbb, hty_def⟩ :=
      validate_expr_well_scoped_spec hbound hnlvls raw_ty' (Heap.Extends.refl m_chk) hrd_ty
        ev68 hcl_val
    have ext_m_m124 : Heap.Extends m_chk m124 := ev68.heap_extends.trans ext_m56_m124
    have raw_ty_m124 := raw_ty'.mono ext_m_m124 (fun _ hm => hm)
    have hrd_ty_rp :
        (Ix.Kernel.Reader.MemberReader.mk' cx c
          (Ix.Kernel.Reader.recParam (List.range ax.lvls.toNat)) (fun _ => none)).read ax.typ =
          .ok ty₀ := by
      rwa [recParam_range]
    obtain ⟨ty', hty_ann, hty_tmc⟩ :=
      raw_ty_m124.toTmC (κ := Core.keyOf t) (ps := List.range ax.lvls.toNat)
        (by simp) (by simpa using hnlvls)
        (fun _ _ hk => streamContext_keyAt_ok_inv hauth hba.wellFormed hk)
        (by simp)
        (fun x bs hm => (hblobs_ok x bs hm).1)
        hrd_ty_rp hty_lbb hty_def
    have ext_m_m137 : Heap.Extends m_chk m137 := ext_m_m93.trans ev_sr.heap_extends
    have hcco : CheckedConstOrigin calls t b.address E_core order_role
        (.axiomDecl ⟨Core.keyOf t a, List.range ax.lvls.toNat, ty₀⟩) :=
      .axiomDecl ha_not_role (hsub_rec a c hrecE) hinfo hsafe hnlvls hty_lbb hty_def hty_ann
        hm132 hty_tmc (hrc_m.mono ext_m_m124) ev105 hcl_es hsub_es
        ev_sr.heap_extends (hrc_m.mono ext_m_m137) (Core.S0.addr_mono ext_m_m137 ha_m)
        ev203 hne255 hcl_ax hsub_ax
    let cx' : Ix.Kernel.Reader.Ctx .anon := { cx with blob := E_core.blobs.get? }
    have hrd_ty_cx' :
        (Ix.Kernel.Reader.MemberReader.mk' cx' c
          (Ix.Kernel.Reader.recParam (List.range ax.lvls.toNat)) (fun _ => none)).read ax.typ =
          .ok ty₀ :=
      memberReader_read_with_blob cx E_core.blobs.get? hblobs_ok raw_ty' hrd_ty_rp
    have hrra : L1.RecordReadsAs t E_core a c
        (.axiomInfo ⟨Core.keyOf t a, List.range ax.lvls.toNat, ty₀⟩) := by
      refine ⟨hnoInt_core, ?_⟩
      rw [hinfo]
      exact ⟨cx', fun _ => none, Core.keyOf t a, List.range ax.lvls.toNat, ty₀,
        by simp, by simp,
        fun x' _ hk => streamContext_keyAt_ok_inv hauth hba.wellFormed
          ((ctx_with_blob_keyAt cx E_core.blobs.get? x').symm.trans hk),
        fun _ _ hb => hb, hrd_ty_cx', hty_lbb, hty_def, rfl⟩
    have hinst_ax : IxVM.Consistency.inertKey (Core.keyOf t a) = false →
        (.axiomInfo ⟨Core.keyOf t a, List.range ax.lvls.toNat, ty₀⟩ :
          Ix.Kernel.ConstantInfo .anon) ∈
          IxVM.Consistency.installs
            (.axiomDecl ⟨Core.keyOf t a, List.range ax.lvls.toNat, ty₀⟩) := by
      intro hinert
      have hne_qs := (keyOf_nonRole_disjoint_prelude hadm hba ha_not_role).2
      simp [IxVM.Consistency.installs, hne_qs, hinert]
    exact ⟨ty₀, hread_rec, hcco, hrra, hinst_ax⟩

set_option maxHeartbeats 3200000 in
/-- Unified safe definition helper for BOTH standalone `.defn d` at `src_addr` (`decl_addr = src_addr`)
and `.muts ms` member `ms[i]? = some (.defn d)` at `src_addr` (`decl_addr = Core.dprjAddr src_addr i`):
proves `readDefinition` succeeds with `rw = false`, constructs `CheckedConstOrigin`, and supplies the
exact `MemberReader.read` witness on `cx' := { cx with blob := E_core.blobs.get? }` together with
`recurDeps src d = ∅`. -/
private theorem checkedDefnCore
    (hSR : SafeRefsInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role st : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {seeds : List _root_.Address}
    {src_addr decl_addr : _root_.Address} {src : Ixon.Constant} {d : Ixon.Definition}
    {ref : Ix.Kernel.ConstRef _root_.Address}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    (hbound : IxVM.Consistency.Bounded calls)
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hblobs₀ : ∀ bytes, Hashed calls bytes →
      E₀.blobs.get? (_root_.Address.blake3Pure bytes) = some bytes)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hord : IxVM.Consistency.UsedClosureOrderAt t
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role))
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) order)
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.blobsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.hintsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)))).store)
    (hproj_emp : ∀ k : Core.KKey, st.projLevels[k]? = none)
    (hsrc_ord : src_addr ∈ order)
    (hdecl_not_role : decl_addr ∉ order_role)
    (hsrc_rec₀ : Ix.Cert.recordAt E₀ src_addr = some src)
    (hsrc_recE : Ix.Cert.recordAt
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) src_addr = some src)
    (hsrc_wk : WkAll calls b.address t E₀ src_addr)
    (hsafe_decl : Ix.Kernel.Reader.safetyDecline d = none)
    (hdir_ty : ∀ x ∈ IxVM.Consistency.exprRefIdxs d.typ, x ∈ IxVM.Consistency.usedRefIdxs src)
    (hdir_val : ∀ x ∈ IxVM.Consistency.exprRefIdxs d.value, x ∈ IxVM.Consistency.usedRefIdxs src)
    (hmkey : (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf
        (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
          (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
      (Ix.Cert.blobsOf
        (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
          (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
      (Ix.Cert.hintsOf
        (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
          (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)))).memberKey ref =
      .ok (Core.keyOf t decl_addr))
    {lim : Nat} {m_chk h'_chk : Heap F} {rc ap v r_chk : SourceValue F}
    {cs_load cs_chk : List (Call F)} {E_ld : Ixon.Env}
    {blobs : List (_root_.Address × ByteArray)}
    (hrc_m : Claim.RCFullRep t b.address lim m_chk rc)
    (hload_ld : IxVM.Consistency.LoadedBy cs_load E_ld)
    (hsub_ld : ∀ cl ∈ cs_load, cl ∈ calls)
    (hb_ld : L1.BlobTableLoaded E_ld blobs)
    (hraw_d : L1.RawDefnValRep src.refs.toList [] src.univs.toList src.sharing.toList blobs
      m_chk d v)
    (ev_chk : ObsFn Core.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk)
    (hsub_chk : ∀ cl ∈ cs_chk, cl ∈ calls) :
    let Keep := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x
    let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
    let E_core := coreEnvRole E₀ Keep (roleSuppOf E_role order_role)
      (Ix.Cert.blobsOf E_role order_role) pre
    let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
    let cx' : Ix.Kernel.Reader.Ctx .anon := { cx with blob := E_core.blobs.get? }
    (Ix.Kernel.Reader.recurDeps src d).toList = [] ∧
    ∃ ty₀ val₀ : Core.KExpr,
      (Ix.Kernel.Reader.MemberReader.mk' cx' src
        (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.typ = .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      (Ix.Kernel.Reader.MemberReader.mk' cx' src
        (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.value = .ok val₀ ∧
      val₀.looseBVarsBounded 0 = true ∧
      val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      ∀ heights : Core.KKey → Nat,
        ∃ (decl : Ix.Kernel.Declaration .anon) (ci₀ : Ix.Kernel.ConstantInfo .anon)
          (hn : Ix.Kernel.ReducibilityHint),
          Ix.Kernel.Reader.readDefinition cx st heights ref (List.range d.lvls.toNat)
            (Ix.Kernel.Reader.MemberReader.mk' cx src id self) d = .ok (decl, false) ∧
          CheckedConstOrigin calls t b.address E_core order_role decl ∧
          IxVM.Consistency.installs decl = [ci₀] ∧
          ci₀.name = Core.keyOf t decl_addr ∧
          decl.names = [Core.keyOf t decl_addr] ∧
          (∀ kb, decl ≠ .basisDecl kb) ∧
          ci₀ = match d.kind with
            | .defn => .defnInfo ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩ val₀ hn
            | .opaq => .axiomInfo ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩
            | .thm => .thmInfo ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩ val₀ := by
  intro Keep E E_core cx cx'
  obtain ⟨hnlvls, tyPtr, valPtr, hintVal, rfl, raw_ty, raw_val⟩ := hraw_d
  have hrecDeps : (Ix.Kernel.Reader.recurDeps src d).toList = [] :=
    recurDeps_empty_of_rawConvExpr raw_ty raw_val
  cases hk : d.kind with
  | defn =>
    have hv_shape : L1.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Defn"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, L1.repDefSafetyVal d.safety, hintVal] := by
      simp [L1.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other
    | Thm | Opaque | Quot
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [L1.defnValShape, Core.kciEnum]
    | Defn v1 m2 cs12 x_nlvls x_ty x_val _ _ _ m299 cs309 _ m336 cs346 v372 m373 cs383 m404
        _ m417 cs427 _ m447 cs457 cs479 m508
        ev14 _ hv269 ev311 ev348 hm412 ev385 ev429 ev459 hm516 ev481 hc520 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe hsafe_decl ev14
      subst v1; subst m2
      rw [hv_shape] at hv269
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv269
      obtain ⟨hxn, hxt, hxv, -, -⟩ := hv269
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right (mem_sublist_of_cons_left (by rwa [hc520] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs383, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs3)
      have hsub_as1 : ∀ cl ∈ cs427, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs4) cl (List.mem_append_left _ hm)
      have hs5 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs4)
      have hsub_as2 : ∀ cl ∈ cs457, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs5) cl (List.mem_append_left _ hm)
      have hs6 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs5)
      have hcl_kc := hs6 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left hs6
      obtain ⟨cs_sr1, ev_sr1, hcs427⟩ := assert_safety_zero_spec ev429
      obtain ⟨cs_sr2, ev_sr2, hcs457⟩ := assert_safety_zero_spec ev459
      have hsub_sr1 : ∀ cl ∈ cs_sr1, cl ∈ calls :=
        fun cl hm => hsub_as1 cl (by rw [hcs427]; exact List.mem_cons_of_mem _ hm)
      have hsub_sr2 : ∀ cl ∈ cs_sr2, cl ∈ calls :=
        fun cl hm => hsub_as2 cl (by rw [hcs457]; exact List.mem_cons_of_mem _ hm)
      have ext_336_404 : Heap.Extends m336 m404 := by rw [hm412]; exact Heap.Extends.snoc _ _
      have ext_447_508 : Heap.Extends m447 m508 := by rw [hm516]; exact Heap.Extends.snoc _ _
      have ext_m_373 : Heap.Extends m_chk m373 :=
        ev311.heap_extends.trans (ev348.heap_extends.trans (ext_336_404.trans ev385.heap_extends))
      have ext_m_417 : Heap.Extends m_chk m417 := ext_m_373.trans ev_sr1.heap_extends
      obtain ⟨raw_ty', hblobs_ok1, hkeys_ty⟩ :=
        safe_rawConvExpr_ctx_ready hSR hbound hadm hba hload hexact₀ hblobs₀ hnoCol hord hauth
          hsrc_ord hsrc_rec₀ hsrc_recE hsrc_wk hdir_ty hload_ld hsub_ld hb_ld raw_ty
          ext_m_373 ev_sr1 hsub_sr1
      obtain ⟨raw_val', hblobs_ok2, hkeys_val⟩ :=
        safe_rawConvExpr_ctx_ready hSR hbound hadm hba hload hexact₀ hblobs₀ hnoCol hord hauth
          hsrc_ord hsrc_rec₀ hsrc_recE hsrc_wk hdir_val hload_ld hsub_ld hb_ld raw_val
          ext_m_417 ev_sr2 hsub_sr2
      obtain ⟨ty₀, hrd_ty⟩ :=
        memberReader_read_ok_of_rawConvExpr (cx := cx) (param := id) (self := self)
          raw_ty' (by simp) (fun x bs hm => (hblobs_ok1 x bs hm).1)
          (fun idx hidx r hr => ⟨Core.keyOf t r, hkeys_ty idx hidx r hr⟩)
      obtain ⟨val₀, hrd_val⟩ :=
        memberReader_read_ok_of_rawConvExpr (cx := cx) (param := id) (self := self)
          raw_val' (by simp) (fun x bs hm => (hblobs_ok2 x bs hm).1)
          (fun idx hidx r hr => ⟨Core.keyOf t r, hkeys_val idx hidx r hr⟩)
      obtain ⟨_, hty_lbb, hty_def⟩ :=
        validate_expr_well_scoped_spec hbound hnlvls raw_ty' (Heap.Extends.refl m_chk) hrd_ty
          ev311 hcl_v1
      obtain ⟨_, hval_lbb, hval_def⟩ :=
        validate_expr_well_scoped_spec hbound hnlvls raw_val' ev311.heap_extends hrd_val
          ev348 hcl_v2
      have hrd_ty_rp :
          (Ix.Kernel.Reader.MemberReader.mk' cx src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.typ = .ok ty₀ := by
        rwa [recParam_range]
      have hrd_val_rp :
          (Ix.Kernel.Reader.MemberReader.mk' cx src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.value = .ok val₀ := by
        rwa [recParam_range]
      have ext_m_404 : Heap.Extends m_chk m404 :=
        ev311.heap_extends.trans (ev348.heap_extends.trans ext_336_404)
      have ext_373_508 : Heap.Extends m373 m508 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_447_508)
      have ext_404_508 : Heap.Extends m404 m508 := ev385.heap_extends.trans ext_373_508
      have ext_m_508 : Heap.Extends m_chk m508 := ext_m_404.trans ext_404_508
      obtain ⟨ty', hty_ann, hty_tmc_404⟩ :=
        (raw_ty'.mono ext_m_404 (fun _ hm => hm)).toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls)
          (fun _ _ hk' => streamContext_keyAt_ok_inv hauth hba.wellFormed hk')
          (fun _ _ _ _ h => nomatch h) (fun x bs hm => (hblobs_ok1 x bs hm).1)
          hrd_ty_rp hty_lbb hty_def
      obtain ⟨val', hval_ann, hval_tmc_508⟩ :=
        (raw_val'.mono ext_m_508 (fun _ hm => hm)).toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls)
          (fun _ _ hk' => streamContext_keyAt_ok_inv hauth hba.wellFormed hk')
          (fun _ _ _ _ h => nomatch h) (fun x bs hm => (hblobs_ok2 x bs hm).1)
          hrd_val_rp hval_lbb hval_def
      have hrd_ty_cx' :
          (Ix.Kernel.Reader.MemberReader.mk' cx' src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.typ = .ok ty₀ :=
        memberReader_read_with_blob cx E_core.blobs.get? hblobs_ok1 raw_ty' hrd_ty_rp
      have hrd_val_cx' :
          (Ix.Kernel.Reader.MemberReader.mk' cx' src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.value = .ok val₀ :=
        memberReader_read_with_blob cx E_core.blobs.get? hblobs_ok2 raw_val' hrd_val_rp
      refine ⟨hrecDeps, ty₀, val₀, hrd_ty_cx', hty_lbb, hty_def, hrd_val_cx', hval_lbb, hval_def,
        fun heights => ?_⟩
      let cv : Ix.Kernel.ConstantVal .anon := ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩
      let hn : Ix.Kernel.ReducibilityHint :=
        (cx.hint ref).getD (Ix.Kernel.Frontend.InModel.hintFor heights val₀)
      have hprw : Ix.Kernel.Reader.projRewrite st cv val₀ = none :=
        projRewrite_eq_none hproj_emp cv val₀
      have hsdo : Ix.Kernel.Reader.safetyDeclineOf d.kind d.safety = none := by
        simpa [Ix.Kernel.Reader.safetyDecline] using hsafe_decl
      have hrd_def :
          Ix.Kernel.Reader.readDefinition cx st heights ref (List.range d.lvls.toNat)
            (Ix.Kernel.Reader.MemberReader.mk' cx src id self) d =
            .ok (.defnDecl cv val₀ hn, false) := by
        unfold Ix.Kernel.Reader.readDefinition Ix.Kernel.Reader.lowerDefinition
        rw [hmkey, hrd_ty, hrd_val]
        simp only [bind, Except.bind, cv, hprw, hsdo, hk, Option.getD_none, Option.isSome_none,
          Bool.false_and, pure, Except.pure, hn]
      have hcco : CheckedConstOrigin calls t b.address E_core order_role (.defnDecl cv val₀ hn) :=
        .defnDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hm412 hty_tmc_404 (hrc_m.mono ext_m_404) ev385 hcl_es hsub_es
          ext_373_508 hm516 (Core.TmC.mono ext_404_508 hty_tmc_404) hval_tmc_508
          (hrc_m.mono ext_m_508) ev481 hcl_kc hsub_kc
      exact ⟨.defnDecl cv val₀ hn, .defnInfo cv val₀ hn, hn, hrd_def, hcco,
        rfl, rfl, rfl, fun _ h => by cases h, rfl⟩
  | thm =>
    have hv_shape : L1.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Thm" [.field (d.lvls.toNat : F), tyPtr, valPtr] := by
      simp [L1.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn
    | Opaque | Quot
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [L1.defnValShape, Core.kciEnum]
    | Thm v1 m2 cs12 x_nlvls x_ty x_val _ m544 cs554 _ m581 cs591 v617 m618 cs628 m649
        v672 m675 cs683 m696 _ m716 cs726 _ m746 cs756 cs778 m807
        ev14 _ _ hv526 ev556 ev593 hm657 ev630 hm704 ev685 heq714 ev728 ev758 hm815 ev780 hc819 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe hsafe_decl ev14
      subst v1; subst m2
      subst v672
      rw [hv_shape] at hv526
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv526
      obtain ⟨hxn, hxt, hxv⟩ := hv526
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right (mem_sublist_of_cons_left (by rwa [hc819] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs628, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs3)
      have hcl_le := hs4 _ List.mem_cons_self
      have hsub_le : ∀ cl ∈ cs683, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs4) cl (List.mem_append_left _ hm)
      have hs5 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs4)
      have hsub_as1 : ∀ cl ∈ cs726, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs5) cl (List.mem_append_left _ hm)
      have hs6 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs5)
      have hsub_as2 : ∀ cl ∈ cs756, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs6) cl (List.mem_append_left _ hm)
      have hs7 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs6)
      have hcl_kc := hs7 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left hs7
      obtain ⟨cs_sr1, ev_sr1, hcs726⟩ := assert_safety_zero_spec ev728
      obtain ⟨cs_sr2, ev_sr2, hcs756⟩ := assert_safety_zero_spec ev758
      have hsub_sr1 : ∀ cl ∈ cs_sr1, cl ∈ calls :=
        fun cl hm => hsub_as1 cl (by rw [hcs726]; exact List.mem_cons_of_mem _ hm)
      have hsub_sr2 : ∀ cl ∈ cs_sr2, cl ∈ calls :=
        fun cl hm => hsub_as2 cl (by rw [hcs756]; exact List.mem_cons_of_mem _ hm)
      have ext_581_649 : Heap.Extends m581 m649 := by rw [hm657]; exact Heap.Extends.snoc _ _
      have ext_618_696 : Heap.Extends m618 m696 := by rw [hm704]; exact Heap.Extends.snoc _ _
      have ext_746_807 : Heap.Extends m746 m807 := by rw [hm815]; exact Heap.Extends.snoc _ _
      have ext_m_649 : Heap.Extends m_chk m649 :=
        ev556.heap_extends.trans (ev593.heap_extends.trans ext_581_649)
      have ext_649_675 : Heap.Extends m649 m675 :=
        ev630.heap_extends.trans (ext_618_696.trans ev685.heap_extends)
      have ext_m_675 : Heap.Extends m_chk m675 := ext_m_649.trans ext_649_675
      have ext_m_716 : Heap.Extends m_chk m716 := ext_m_675.trans ev_sr1.heap_extends
      obtain ⟨raw_ty', hblobs_ok1, hkeys_ty⟩ :=
        safe_rawConvExpr_ctx_ready hSR hbound hadm hba hload hexact₀ hblobs₀ hnoCol hord hauth
          hsrc_ord hsrc_rec₀ hsrc_recE hsrc_wk hdir_ty hload_ld hsub_ld hb_ld raw_ty
          ext_m_675 ev_sr1 hsub_sr1
      obtain ⟨raw_val', hblobs_ok2, hkeys_val⟩ :=
        safe_rawConvExpr_ctx_ready hSR hbound hadm hba hload hexact₀ hblobs₀ hnoCol hord hauth
          hsrc_ord hsrc_rec₀ hsrc_recE hsrc_wk hdir_val hload_ld hsub_ld hb_ld raw_val
          ext_m_716 ev_sr2 hsub_sr2
      obtain ⟨ty₀, hrd_ty⟩ :=
        memberReader_read_ok_of_rawConvExpr (cx := cx) (param := id) (self := self)
          raw_ty' (by simp) (fun x bs hm => (hblobs_ok1 x bs hm).1)
          (fun idx hidx r hr => ⟨Core.keyOf t r, hkeys_ty idx hidx r hr⟩)
      obtain ⟨val₀, hrd_val⟩ :=
        memberReader_read_ok_of_rawConvExpr (cx := cx) (param := id) (self := self)
          raw_val' (by simp) (fun x bs hm => (hblobs_ok2 x bs hm).1)
          (fun idx hidx r hr => ⟨Core.keyOf t r, hkeys_val idx hidx r hr⟩)
      obtain ⟨_, hty_lbb, hty_def⟩ :=
        validate_expr_well_scoped_spec hbound hnlvls raw_ty' (Heap.Extends.refl m_chk) hrd_ty
          ev556 hcl_v1
      obtain ⟨_, hval_lbb, hval_def⟩ :=
        validate_expr_well_scoped_spec hbound hnlvls raw_val' ev556.heap_extends hrd_val
          ev593 hcl_v2
      have hrd_ty_rp :
          (Ix.Kernel.Reader.MemberReader.mk' cx src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.typ = .ok ty₀ := by
        rwa [recParam_range]
      have hrd_val_rp :
          (Ix.Kernel.Reader.MemberReader.mk' cx src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.value = .ok val₀ := by
        rwa [recParam_range]
      have ext_675_807 : Heap.Extends m675 m807 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_746_807)
      have ext_649_807 : Heap.Extends m649 m807 := ext_649_675.trans ext_675_807
      have ext_m_807 : Heap.Extends m_chk m807 := ext_m_649.trans ext_649_807
      obtain ⟨ty', hty_ann, hty_tmc_649⟩ :=
        (raw_ty'.mono ext_m_649 (fun _ hm => hm)).toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls)
          (fun _ _ hk' => streamContext_keyAt_ok_inv hauth hba.wellFormed hk')
          (fun _ _ _ _ h => nomatch h) (fun x bs hm => (hblobs_ok1 x bs hm).1)
          hrd_ty_rp hty_lbb hty_def
      obtain ⟨val', hval_ann, hval_tmc_807⟩ :=
        (raw_val'.mono ext_m_807 (fun _ hm => hm)).toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls)
          (fun _ _ hk' => streamContext_keyAt_ok_inv hauth hba.wellFormed hk')
          (fun _ _ _ _ h => nomatch h) (fun x bs hm => (hblobs_ok2 x bs hm).1)
          hrd_val_rp hval_lbb hval_def
      have hrd_ty_cx' :
          (Ix.Kernel.Reader.MemberReader.mk' cx' src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.typ = .ok ty₀ :=
        memberReader_read_with_blob cx E_core.blobs.get? hblobs_ok1 raw_ty' hrd_ty_rp
      have hrd_val_cx' :
          (Ix.Kernel.Reader.MemberReader.mk' cx' src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.value = .ok val₀ :=
        memberReader_read_with_blob cx E_core.blobs.get? hblobs_ok2 raw_val' hrd_val_rp
      refine ⟨hrecDeps, ty₀, val₀, hrd_ty_cx', hty_lbb, hty_def, hrd_val_cx', hval_lbb, hval_def,
        fun heights => ?_⟩
      let cv : Ix.Kernel.ConstantVal .anon := ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩
      have hprw : Ix.Kernel.Reader.projRewrite st cv val₀ = none :=
        projRewrite_eq_none hproj_emp cv val₀
      have hsdo : Ix.Kernel.Reader.safetyDeclineOf d.kind d.safety = none := by
        simpa [Ix.Kernel.Reader.safetyDecline] using hsafe_decl
      have hrd_def :
          Ix.Kernel.Reader.readDefinition cx st heights ref (List.range d.lvls.toNat)
            (Ix.Kernel.Reader.MemberReader.mk' cx src id self) d =
            .ok (.thmDecl cv val₀, false) := by
        unfold Ix.Kernel.Reader.readDefinition Ix.Kernel.Reader.lowerDefinition
        rw [hmkey, hrd_ty, hrd_val]
        simp only [bind, Except.bind, cv, hprw, hsdo, hk, Option.getD_none, Option.isSome_none,
          Bool.false_and, pure, Except.pure]
      have hcco : CheckedConstOrigin calls t b.address E_core order_role (.thmDecl cv val₀) :=
        .thmDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hm657 hty_tmc_649 (hrc_m.mono ext_m_649) ev630 hcl_es hsub_es
          hm704 ev685 hcl_le hsub_le
          ext_675_807 hm815 (Core.TmC.mono ext_649_807 hty_tmc_649) hval_tmc_807
          (hrc_m.mono ext_m_807) ev780 hcl_kc hsub_kc
      exact ⟨.thmDecl cv val₀, .thmInfo cv val₀, .opaque, hrd_def, hcco,
        rfl, rfl, rfl, fun _ h => by cases h, rfl⟩
  | opaq =>
    have hv_shape : L1.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Opaque"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, L1.repBoolField (d.safety == .unsaf)] := by
      simp [L1.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn | Thm
    | Quot
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [L1.defnValShape, Core.kciEnum]
    | Opaque v1 m2 cs12 x_nlvls x_ty x_val _ _ m849 cs859 _ m886 cs896 v922 m923 cs933 m954
        _ m967 cs977 _ m997 cs1007 cs1029 m1058
        ev14 _ _ _ hv825 ev861 ev898 hm962 ev935 ev979 ev1009 hm1066 ev1031 hc1070 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe hsafe_decl ev14
      subst v1; subst m2
      rw [hv_shape] at hv825
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv825
      obtain ⟨hxn, hxt, hxv, -⟩ := hv825
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right (mem_sublist_of_cons_left (by rwa [hc1070] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs933, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs3)
      have hsub_as1 : ∀ cl ∈ cs977, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs4) cl (List.mem_append_left _ hm)
      have hs5 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs4)
      have hsub_as2 : ∀ cl ∈ cs1007, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs5) cl (List.mem_append_left _ hm)
      have hs6 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs5)
      have hcl_kc := hs6 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left hs6
      obtain ⟨cs_sr1, ev_sr1, hcs977⟩ := assert_safety_zero_spec ev979
      obtain ⟨cs_sr2, ev_sr2, hcs1007⟩ := assert_safety_zero_spec ev1009
      have hsub_sr1 : ∀ cl ∈ cs_sr1, cl ∈ calls :=
        fun cl hm => hsub_as1 cl (by rw [hcs977]; exact List.mem_cons_of_mem _ hm)
      have hsub_sr2 : ∀ cl ∈ cs_sr2, cl ∈ calls :=
        fun cl hm => hsub_as2 cl (by rw [hcs1007]; exact List.mem_cons_of_mem _ hm)
      have ext_886_954 : Heap.Extends m886 m954 := by rw [hm962]; exact Heap.Extends.snoc _ _
      have ext_997_1058 : Heap.Extends m997 m1058 := by rw [hm1066]; exact Heap.Extends.snoc _ _
      have ext_m_923 : Heap.Extends m_chk m923 :=
        ev861.heap_extends.trans (ev898.heap_extends.trans (ext_886_954.trans ev935.heap_extends))
      have ext_m_967 : Heap.Extends m_chk m967 := ext_m_923.trans ev_sr1.heap_extends
      obtain ⟨raw_ty', hblobs_ok1, hkeys_ty⟩ :=
        safe_rawConvExpr_ctx_ready hSR hbound hadm hba hload hexact₀ hblobs₀ hnoCol hord hauth
          hsrc_ord hsrc_rec₀ hsrc_recE hsrc_wk hdir_ty hload_ld hsub_ld hb_ld raw_ty
          ext_m_923 ev_sr1 hsub_sr1
      obtain ⟨raw_val', hblobs_ok2, hkeys_val⟩ :=
        safe_rawConvExpr_ctx_ready hSR hbound hadm hba hload hexact₀ hblobs₀ hnoCol hord hauth
          hsrc_ord hsrc_rec₀ hsrc_recE hsrc_wk hdir_val hload_ld hsub_ld hb_ld raw_val
          ext_m_967 ev_sr2 hsub_sr2
      obtain ⟨ty₀, hrd_ty⟩ :=
        memberReader_read_ok_of_rawConvExpr (cx := cx) (param := id) (self := self)
          raw_ty' (by simp) (fun x bs hm => (hblobs_ok1 x bs hm).1)
          (fun idx hidx r hr => ⟨Core.keyOf t r, hkeys_ty idx hidx r hr⟩)
      obtain ⟨val₀, hrd_val⟩ :=
        memberReader_read_ok_of_rawConvExpr (cx := cx) (param := id) (self := self)
          raw_val' (by simp) (fun x bs hm => (hblobs_ok2 x bs hm).1)
          (fun idx hidx r hr => ⟨Core.keyOf t r, hkeys_val idx hidx r hr⟩)
      obtain ⟨_, hty_lbb, hty_def⟩ :=
        validate_expr_well_scoped_spec hbound hnlvls raw_ty' (Heap.Extends.refl m_chk) hrd_ty
          ev861 hcl_v1
      obtain ⟨_, hval_lbb, hval_def⟩ :=
        validate_expr_well_scoped_spec hbound hnlvls raw_val' ev861.heap_extends hrd_val
          ev898 hcl_v2
      have hrd_ty_rp :
          (Ix.Kernel.Reader.MemberReader.mk' cx src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.typ = .ok ty₀ := by
        rwa [recParam_range]
      have hrd_val_rp :
          (Ix.Kernel.Reader.MemberReader.mk' cx src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.value = .ok val₀ := by
        rwa [recParam_range]
      have ext_m_954 : Heap.Extends m_chk m954 :=
        ev861.heap_extends.trans (ev898.heap_extends.trans ext_886_954)
      have ext_923_1058 : Heap.Extends m923 m1058 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_997_1058)
      have ext_954_1058 : Heap.Extends m954 m1058 := ev935.heap_extends.trans ext_923_1058
      have ext_m_1058 : Heap.Extends m_chk m1058 := ext_m_954.trans ext_954_1058
      obtain ⟨ty', hty_ann, hty_tmc_954⟩ :=
        (raw_ty'.mono ext_m_954 (fun _ hm => hm)).toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls)
          (fun _ _ hk' => streamContext_keyAt_ok_inv hauth hba.wellFormed hk')
          (fun _ _ _ _ h => nomatch h) (fun x bs hm => (hblobs_ok1 x bs hm).1)
          hrd_ty_rp hty_lbb hty_def
      obtain ⟨val', hval_ann, hval_tmc_1058⟩ :=
        (raw_val'.mono ext_m_1058 (fun _ hm => hm)).toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls)
          (fun _ _ hk' => streamContext_keyAt_ok_inv hauth hba.wellFormed hk')
          (fun _ _ _ _ h => nomatch h) (fun x bs hm => (hblobs_ok2 x bs hm).1)
          hrd_val_rp hval_lbb hval_def
      have hrd_ty_cx' :
          (Ix.Kernel.Reader.MemberReader.mk' cx' src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.typ = .ok ty₀ :=
        memberReader_read_with_blob cx E_core.blobs.get? hblobs_ok1 raw_ty' hrd_ty_rp
      have hrd_val_cx' :
          (Ix.Kernel.Reader.MemberReader.mk' cx' src
            (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.value = .ok val₀ :=
        memberReader_read_with_blob cx E_core.blobs.get? hblobs_ok2 raw_val' hrd_val_rp
      refine ⟨hrecDeps, ty₀, val₀, hrd_ty_cx', hty_lbb, hty_def, hrd_val_cx', hval_lbb, hval_def,
        fun heights => ?_⟩
      let cv : Ix.Kernel.ConstantVal .anon := ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩
      have hprw : Ix.Kernel.Reader.projRewrite st cv val₀ = none :=
        projRewrite_eq_none hproj_emp cv val₀
      have hsdo : Ix.Kernel.Reader.safetyDeclineOf d.kind d.safety = none := by
        simpa [Ix.Kernel.Reader.safetyDecline] using hsafe_decl
      have hrd_def :
          Ix.Kernel.Reader.readDefinition cx st heights ref (List.range d.lvls.toNat)
            (Ix.Kernel.Reader.MemberReader.mk' cx src id self) d =
            .ok (.opaqueDecl cv val₀, false) := by
        unfold Ix.Kernel.Reader.readDefinition Ix.Kernel.Reader.lowerDefinition
        rw [hmkey, hrd_ty, hrd_val]
        simp only [bind, Except.bind, cv, hprw, hsdo, hk, Option.getD_none, Option.isSome_none,
          Bool.false_and, pure, Except.pure]
      have hcco : CheckedConstOrigin calls t b.address E_core order_role (.opaqueDecl cv val₀) :=
        .opaqueDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hm962 hty_tmc_954 (hrc_m.mono ext_m_954) ev935 hcl_es hsub_es
          ext_923_1058 hm1066 (Core.TmC.mono ext_954_1058 hty_tmc_954) hval_tmc_1058
          (hrc_m.mono ext_m_1058) ev1031 hcl_kc hsub_kc
      exact ⟨.opaqueDecl cv val₀, .axiomInfo cv, .opaque, hrd_def, hcco,
        rfl, rfl, rfl, fun _ h => by cases h, rfl⟩


/-- No address `x ∉ order_role` can have `Core.keyOf t x = .role s` for a non-`compilerTrust` role `s`. -/
theorem keyOf_nonRole_ne_role
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    {x : _root_.Address} (hx : x ∉ order_role)
    {s : Ix.Kernel.Role} (hct : IxVM.Refinement.compilerTrust s = false) :
    Core.keyOf t x ≠ .role s := by
  intro heq
  unfold Core.keyOf at heq
  cases hfind : t.bound.find? (·.2 == x) with
  | none => rw [hfind] at heq; cases heq
  | some p =>
    rcases p with ⟨r, x'⟩
    rw [hfind] at heq
    injection heq with hrs
    subst r
    have hp_mem : (s, x') ∈ t.bound.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)
    have hp_beq : (s, x').2 == x :=
      list_find?_pred (xs := t.bound.toList) (by rw [Array.find?_toList]; exact hfind)
    have hp_eq : x' = x := beq_iff_eq.mp hp_beq
    subst x'
    have haddr := Ix.Cert.ReadingKeys.addressOf_of_bound hba.wellFormed hp_mem
    have hb : IxVM.Refinement.BindingSeeds t x := Or.inl ⟨s, hct, haddr⟩
    exact hx ((hadm.closureOrder.complete x).mpr (.seed hb (hadm.seeds_in x hb)))

/-- Any `.indDecl block nP` whose names are all `Core.keyOf t x` (`x ∉ order_role`) cannot match a
pinned basis inductive (`basisPinHit block = none`), so `installs (.indDecl block nP) = block`. -/
theorem basisPinHit_eq_none_of_nonRole
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    {block : List (Ix.Kernel.ConstantInfo .anon)} {nP : Nat}
    (hnames : ∀ n ∈ (Ix.Kernel.Declaration.indDecl block nP).names,
      ∃ x, n = Core.keyOf t x ∧ x ∉ order_role) :
    Ix.Kernel.basisPinHit block = none ∧
      IxVM.Consistency.installs (.indDecl block nP) = block := by
  have hnone : Ix.Kernel.basisPinHit block = none := by
    cases hpin : Ix.Kernel.basisPinHit block with
    | none => rfl
    | some k =>
      unfold Ix.Kernel.basisPinHit at hpin
      cases hfind : ([Ix.Kernel.BasisKind.eqK, .natK, .punitK, .emptyK, .falseK].find? fun k' =>
          (k'.decls (md := .anon)).map (·.name) == block.map (·.name)) with
      | none => simp [hfind] at hpin
      | some k' =>
        have hk_mem := List.mem_of_find?_eq_some hfind
        have hk_eq : (k'.decls (md := .anon)).map (·.name) = block.map (·.name) :=
          beq_iff_eq.mp (List.find?_eq_some_iff_append.mp hfind).1
        have hrole_in_pin : ∃ s : Ix.Kernel.Role,
            IxVM.Refinement.compilerTrust s = false ∧
            Ix.Kernel.Key.role s ∈ (k'.decls (md := .anon)).map (·.name) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk_mem
          rcases hk_mem with rfl | rfl | rfl | rfl | rfl
          · exact ⟨.eq, rfl, by decide⟩
          · exact ⟨.nat, rfl, by decide⟩
          · exact ⟨.punit, rfl, by decide⟩
          · exact ⟨.empty, rfl, by decide⟩
          · exact ⟨.false, rfl, by decide⟩
        obtain ⟨s, hct, hs_mem⟩ := hrole_in_pin
        rw [hk_eq] at hs_mem
        obtain ⟨x, hx_eq, hx_not_role⟩ := hnames (.role s) hs_mem
        exact absurd hx_eq.symm (keyOf_nonRole_ne_role hadm hba hx_not_role hct)
  exact ⟨hnone, by simp [IxVM.Consistency.installs, hnone]⟩

/-- Every constant stored in `streamContext` over `(E, order)` (`E := subEnvRole E₀ Keep ...`) has
an authenticated exact-decoded byte image from `V.Preimage`, `extra`, or `Hashed calls`. -/
private theorem streamContext_store_raw_source (hRP : RolePreludeInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {Keep : _root_.Address → Prop}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    {x : _root_.Address} {c' : Ixon.Constant}
    (hst : (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf
        (subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
      (Ix.Cert.blobsOf
        (subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
      (Ix.Cert.hintsOf
        (subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)))).store x =
      some c') :
    ∃ raw', _root_.Address.blake3Pure raw' = x ∧
      Ixon.deConstantExact raw' = .ok c' ∧
      (V.Preimage x raw' ∨ raw' ∈ extra ∨ Hashed calls raw') := by
  let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
  rcases Ix.Cert.ReadingKeys.context_store hst with hmem_dec | hmem_fb
  · obtain ⟨_, hrecE⟩ := mem_decodedOf hmem_dec
    rcases recordAt_subEnv_some_inv E₀ Keep (roleSuppOf E_role order_role) hrecE with
      ⟨_, hrec₀⟩ | ⟨_, raw, hm_supp⟩
    · unfold Ix.Cert.recordAt at hrec₀
      cases hget₀ : E₀.consts.get? x with
      | none => rw [hget₀] at hrec₀; cases hrec₀
      | some lc₀ =>
        rw [hget₀] at hrec₀
        obtain ⟨hh₀, hbl₀⟩ := hload.1 x lc₀ hget₀
        obtain ⟨c₀, hlc₀, hex₀⟩ := hexact₀ x lc₀ hget₀
        have hc_eq : c₀ = c' := Option.some.inj (hlc₀.symm.trans hrec₀)
        subst c₀
        exact ⟨lc₀.rawBytes, hbl₀, hex₀, Or.inr (Or.inr hh₀)⟩
    · obtain ⟨hx_role, lc_r, hget_r, hrec_r, rfl⟩ := mem_roleSuppOf_iff.mp hm_supp
      obtain ⟨lc_r', c_r', hget_r', _, hrec_r', hbl_r, _, _, hex_r, hpreV⟩ :=
        hadm.order_record_spec hx_role
      rw [hget_r] at hget_r'; injection hget_r' with hlceq; subst lc_r'
      have hc_eq : c_r' = c' := Option.some.inj (hrec_r'.symm.trans hrec_r)
      subst c_r'
      exact ⟨lc_r.rawBytes, hbl_r, hex_r, Or.inl hpreV⟩
  · obtain ⟨himg, hbl, hwf, _⟩ := hRP.serConstant_mem_committedImages hadm.preludeFor hmem_fb
    exact ⟨Ixon.serConstant c', hbl, Ixon.Verify.deConstantExact_serConstant c' hwf,
      Or.inr (Or.inl (hcomm_extra _ himg))⟩

/-- Injectivity of `Core.dprjAddr` across checked `.muts` definition members: if
`Core.dprjAddr owner₁ i₁ = Core.dprjAddr owner₂ i₂` for two checked `.defn` members, then
`owner₁ = owner₂ ∧ i₁ = i₂`. -/
theorem dprjAddr_inj_of_mutsMemberChecked
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {bAddr owner₁ owner₂ : _root_.Address} {t : Ix.Kernel.RoleTable}
    {ms₁ ms₂ : Array Ixon.MutConst} {i₁ i₂ : Nat} {d₁ d₂ : Ixon.Definition}
    (hbound : IxVM.Consistency.Bounded calls)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hm₁ : Claim.MutsMemberCheckedAtFull calls bAddr t owner₁ ms₁ i₁)
    (hms₁ : ms₁[i₁]? = some (.defn d₁))
    (hm₂ : Claim.MutsMemberCheckedAtFull calls bAddr t owner₂ ms₂ i₂)
    (hms₂ : ms₂[i₂]? = some (.defn d₂))
    (heq : Core.dprjAddr owner₁ i₁ = Core.dprjAddr owner₂ i₂) :
    owner₁ = owner₂ ∧ i₁ = i₂ := by
  obtain ⟨hi₁, huniq₁⟩ := dprj_store_eq_of_mutsMemberChecked hbound hnoCol hm₁ hms₁
  obtain ⟨hi₂, huniq₂⟩ := dprj_store_eq_of_mutsMemberChecked hbound hnoCol hm₂ hms₂
  have hchk₁ : Claim.CheckedAtFull calls bAddr t (Core.dprjAddr owner₁ i₁) := by
    have h0 := mutsMemberCheckedAtFull_to_checkedAtFull hbound hm₁ hms₁
    simpa only [Core.Specs.Callees.memberProjInfo, Core.dprjAddr] using h0
  obtain ⟨_, _, _, _, _, _, _, _, _, cs_load, _, bytes, _,
    _, _, _, _, hhash_ld, hblake_ld, _, hL1, hsub_ld, _, _, _, _⟩ :=
    checkedAtFull_loadedL1 hbound hchk₁
  obtain ⟨c_ld, hdec_ld, _, _, _, _, _⟩ := hL1
  have hh_calls : Hashed calls bytes := Core.hashed_mono hsub_ld hhash_ld
  have hc₁ := huniq₁ bytes c_ld hblake_ld hdec_ld (Or.inr (Or.inr hh_calls))
  have hc₂ := huniq₂ bytes c_ld (hblake_ld.trans heq) hdec_ld (Or.inr (Or.inr hh_calls))
  have hc_eq := hc₁.symm.trans hc₂
  injection hc_eq with hinfo_eq
  injection hinfo_eq with hp_eq
  rcases Ixon.DefinitionProj.mk.inj hp_eq with ⟨hidx_eq, hown_eq⟩
  have hi_eq : i₁ = i₂ := by
    have h := congrArg UInt64.toNat hidx_eq
    rwa [toUInt64_toNat_eq hi₁, toUInt64_toNat_eq hi₂] at h
  exact ⟨hown_eq, hi_eq⟩

/-- For any `.defn` member `i` of a walked `.muts ms` block `cb` at `owner ∉ order_role`,
`Core.dprjAddr owner i ∉ order_role` and `cx.memberKey (.member owner i)` succeeds with
`Core.keyOf t (Core.dprjAddr owner i)`. -/
private theorem dprj_nonRole_and_memberKey (hRP : RolePreludeInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {seeds : List _root_.Address}
    {owner : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {i : Nat} {d : Ixon.Definition}
    (hbound : IxVM.Consistency.Bounded calls)
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hord : IxVM.Consistency.UsedClosureOrderAt t
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role))
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) order)
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.blobsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.hintsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)))).store)
    (hown_ord : owner ∈ order)
    (hown_not_role : owner ∉ order_role)
    (hrecE : Ix.Cert.recordAt
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) owner = some cb)
    (hinfo : cb.info = .muts ms)
    (hms : ms[i]? = some (.defn d))
    (hm : Claim.MutsMemberCheckedAtFull calls b.address t owner ms i) :
    let Keep := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x
    let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
    let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
    i < UInt64.size ∧
      Core.dprjAddr owner i ∉ order_role ∧
      cx.memberKey (.member owner i) = .ok (Core.keyOf t (Core.dprjAddr owner i)) := by
  intro Keep E cx
  obtain ⟨hi, huniq⟩ := dprj_store_eq_of_mutsMemberChecked hbound hnoCol hm hms
  have hagree : ∀ x ∈ order_role, Ix.Cert.recordAt E x = Ix.Cert.recordAt E_role x := by
    intro x hx
    have h := (subEnvRole_agrees_on_role hadm hload hexact₀ hnoCol
      (Keep := Keep) (fun z hz => Or.inl hz) []).1 x hx
    rw [List.append_nil] at h
    exact h.1
  have hd_not_role : Core.dprjAddr owner i ∉ order_role := by
    intro hd_role
    obtain ⟨lc_r, c_r, _, _, hrec_r, hbl_r, _, _, hex_r, hpreV⟩ := hadm.order_record_spec hd_role
    have hc_r := huniq lc_r.rawBytes c_r hbl_r hex_r (Or.inl hpreV)
    subst c_r
    have hne : Core.dprjAddr owner i ≠ owner := by
      intro heq
      have hrecE_d : Ix.Cert.recordAt E (Core.dprjAddr owner i) =
          some ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ :=
        (hagree _ hd_role).trans hrec_r
      rw [heq, hrecE] at hrecE_d
      injection hrecE_d with hcc
      rw [hcc] at hinfo
      cases hinfo
    have hreach_d := (hadm.closureOrder.complete (Core.dprjAddr owner i)).mp hd_role
    have hreach_own : Ix.Cert.CompiledReachAt t E_role (IxVM.Refinement.BindingSeeds t) owner :=
      .step hreach_d ⟨_, hrec_r, Or.inl ⟨rfl, hne.symm⟩⟩
    exact hown_not_role ((hadm.closureOrder.complete owner).mpr hreach_own)
  have hnd_dec : ((Ix.Cert.Stream.decodedOf E order).map Prod.fst).Nodup :=
    hord.nodup.sublist (Ix.Cert.Stream.decodedOf_keys E order)
  have hst_own : cx.store owner = some cb :=
    streamContext_store_of_mem hnd_dec (mem_decodedOf_of_mem hown_ord hrecE)
  have hbound_at : ∀ r, (r, Core.dprjAddr owner i) ∈ t.bound.toList →
      ∃ c_b, cx.store (Core.dprjAddr owner i) = some c_b := by
    intro r hrb
    have haddr := Ix.Cert.ReadingKeys.addressOf_of_bound hba.wellFormed hrb
    have hi_toNat : i.toUInt64.toNat = i := toUInt64_toNat_eq hi
    have hpr₀ := Ix.Kernel.Egress.ProjectionReads.definition ⟨i.toUInt64, owner⟩
    have hpr : Ix.Kernel.Egress.ProjectionReads
        ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ .definition (.member owner i) := by
      simpa only [hi_toNat] using hpr₀
    have hwp := Ix.Kernel.Egress.writeProjection_of_reading hpr
    obtain ⟨hct, _⟩ := hadm.boundConsistent r (Core.dprjAddr owner i) .definition (.member owner i)
      ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ haddr hwp rfl
    have hb : IxVM.Refinement.BindingSeeds t (Core.dprjAddr owner i) := Or.inl ⟨r, hct, haddr⟩
    exact (hd_not_role ((hadm.closureOrder.complete _).mpr (.seed hb (hadm.seeds_in _ hb)))).elim
  have hdprj_eq : ∀ c', cx.store (Core.dprjAddr owner i) = some c' →
      c' = ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ := by
    intro c' hst'
    obtain ⟨raw', hbl', hex', hsrc'⟩ :=
      streamContext_store_raw_source hRP hadm hcomm_extra hload hexact₀ hst'
    exact huniq raw' c' hbl' hex' hsrc'
  exact ⟨hi, hd_not_role,
    streamContext_memberKey_dprj_at hauth hba.wellFormed hst_own hinfo hms hi hbound_at hdprj_eq⟩

/-- Standalone `.defn d` bare reading + `CheckedConstOrigin` + `L1.RecordReadsAs`. -/
private theorem checkedDefn_standalone
    (hSR : SafeRefsInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role st : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {seeds : List _root_.Address}
    {a : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hbound : IxVM.Consistency.Bounded calls)
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hblobs₀ : ∀ bytes, Hashed calls bytes →
      E₀.blobs.get? (_root_.Address.blake3Pure bytes) = some bytes)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hnoInt_core : ¬ L1.EnvInternalCollision
      (coreEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role) pre))
    (hord : IxVM.Consistency.UsedClosureOrderAt t
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role))
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) order)
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.blobsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.hintsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)))).store)
    (hproj_emp : ∀ k : Core.KKey, st.projLevels[k]? = none)
    (ha_ord : a ∈ order)
    (ha_not_role : a ∉ order_role)
    (hrec₀ : Ix.Cert.recordAt E₀ a = some c)
    (hrecE : Ix.Cert.recordAt
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) a = some c)
    (hwk : WkAll calls b.address t E₀ a)
    (hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a)
    (hinfo : c.info = .defn d)
    (hchk : Claim.CheckedAtFull calls b.address t a) :
    let Keep := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x
    let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
    let E_core := coreEnvRole E₀ Keep (roleSuppOf E_role order_role)
      (Ix.Cert.blobsOf E_role order_role) pre
    let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
    ∃ (decl : Ix.Kernel.Declaration .anon) (ci₀ : Ix.Kernel.ConstantInfo .anon),
      Ix.Kernel.Reader.readRecordBare cx st a c = .ok { decls := #[decl] } ∧
      CheckedConstOrigin calls t b.address E_core order_role decl ∧
      IxVM.Consistency.installs decl = [ci₀] ∧
      ci₀.name = Core.keyOf t a ∧
      decl.names = [Core.keyOf t a] ∧
      (∀ kb, decl ≠ .basisDecl kb) ∧
      L1.RecordReadsAs t E_core a c ci₀ := by
  intro Keep E E_core cx
  have hinLogic : IxVM.Consistency.InLogic c := by
    by_contra hnin
    exact hnot_out ⟨c, hrec₀, Or.inl hnin⟩
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    simpa [IxVM.Consistency.InLogic, hinfo] using hinLogic
  have hnu : L1.defnIsUnsafeCI d = false := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    bytes, E_ld, _, hrc_m, _, _, hhash_ld, hblake_ld, hload_ld, hL1,
    hsub_ld, hld, ev_chk, _, hsub_chk⟩ := checkedAtFull_loadedL1 hbound hchk
  obtain ⟨c_ld, hdec_ld, _, _, v', hld', hraw⟩ := hL1
  rw [hld] at hld'; injection hld' with hvv; subst hvv
  have hc_ld_eq : c_ld = c := by
    unfold Ix.Cert.recordAt at hrec₀
    cases hget₀ : E₀.consts.get? a with
    | none => rw [hget₀] at hrec₀; cases hrec₀
    | some lc₀ =>
      rw [hget₀] at hrec₀
      obtain ⟨hh₀, hbl₀⟩ := hload.1 a lc₀ hget₀
      obtain ⟨c₀, hlc₀, hex₀⟩ := hexact₀ a lc₀ hget₀
      have hraw_eq : bytes = lc₀.rawBytes := by
        by_contra hne
        exact hnoCol (Or.inl ⟨a, lc₀.rawBytes, bytes, Or.inr (Or.inr ⟨hh₀, hbl₀⟩),
          Core.hashed_mono hsub_ld hhash_ld, hne, hblake_ld⟩)
      rw [hraw_eq, hex₀] at hdec_ld
      have hcc : c₀ = c_ld := Except.ok.inj hdec_ld
      rw [hcc] at hlc₀
      exact Option.some.inj (hlc₀.symm.trans hrec₀)
  subst c_ld
  rw [hblake_ld] at hraw
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨blobs, hb_ld, hraw_d⟩ := hraw
  have hrec_nil : L1.defnRecurAddrs d a = [] := by simp [L1.defnRecurAddrs, hnu]
  rw [hrec_nil] at hraw_d
  have hnd_dec : ((Ix.Cert.Stream.decodedOf E order).map Prod.fst).Nodup :=
    hord.nodup.sublist (Ix.Cert.Stream.decodedOf_keys E order)
  have hst_a : cx.store a = some c :=
    streamContext_store_of_mem hnd_dec (mem_decodedOf_of_mem ha_ord hrecE)
  have hmkey : cx.memberKey (.member a 0) = .ok (Core.keyOf t a) :=
    streamContext_memberKey_singleton hauth hba.wellFormed hst_a (by rw [hinfo]; trivial)
  have hdir_ty : ∀ x ∈ IxVM.Consistency.exprRefIdxs d.typ, x ∈ IxVM.Consistency.usedRefIdxs c := by
    intro x hx; simp [IxVM.Consistency.usedRefIdxs, hinfo, hx]
  have hdir_val : ∀ x ∈ IxVM.Consistency.exprRefIdxs d.value, x ∈ IxVM.Consistency.usedRefIdxs c := by
    intro x hx; simp [IxVM.Consistency.usedRefIdxs, hinfo, hx]
  let self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey) :=
    fun i => if i == 0 then some (cx.memberKey (.member a 0)) else none
  obtain ⟨_, ty₀, val₀, hrd_ty_cx', hty_lbb, hty_def, hrd_val_cx', hval_lbb, hval_def, hheights⟩ :=
    checkedDefnCore hSR (ref := .member a 0) (self := self)
      hbound hadm hba hload hexact₀ hblobs₀ hnoCol hord hauth hproj_emp ha_ord ha_not_role
      hrec₀ hrecE hwk hsafe hdir_ty hdir_val hmkey hrc_m hload_ld hsub_ld hb_ld hraw_d ev_chk hsub_chk
  obtain ⟨decl, ci₀, hn, hrd_def, hcco, hinst, hname, hdnames, hnb, hci₀_eq⟩ :=
    hheights (st.heights.getD · 0)
  have hread_rec : Ix.Kernel.Reader.readRecordBare cx st a c = .ok { decls := #[decl] } := by
    have haux : ∀ (cx₀ : Ix.Kernel.Reader.Ctx .anon) (st₀ : Ix.Kernel.Reader.State .anon)
        (owner : _root_.Address) (c₀ : Ixon.Constant) (d₀ : Ixon.Definition)
        (decl₀ : Ix.Kernel.Declaration .anon),
        c₀.info = .defn d₀ →
        Ix.Kernel.Reader.readDefinition cx₀ st₀ (st₀.heights.getD · 0) (.member owner 0)
          (List.range d₀.lvls.toNat)
          (Ix.Kernel.Reader.MemberReader.mk' cx₀ c₀ id
            (fun i => if i == 0 then some (cx₀.memberKey (.member owner 0)) else none))
          d₀ = .ok (decl₀, false) →
        Ix.Kernel.Reader.readRecordBare cx₀ st₀ owner c₀ = .ok { decls := #[decl₀] } := by
      intro cx₀ st₀ owner c₀ d₀ decl₀ hi₀ hrd₀
      unfold Ix.Kernel.Reader.readRecordBare
      rw [hi₀]
      unfold Ix.Kernel.Reader.readRecord
      rw [hi₀]
      dsimp only
      rw [hrd₀]
      rfl
    exact haux cx st a c d decl hinfo hrd_def
  have hrra : L1.RecordReadsAs t E_core a c ci₀ := by
    refine ⟨hnoInt_core, ?_⟩
    rw [hinfo]
    exact ⟨{ cx with blob := E_core.blobs.get? }, self,
      Core.keyOf t a, List.range d.lvls.toNat, ty₀, val₀, hn,
      by simp, by simp,
      fun x' _ hk => streamContext_keyAt_ok_inv hauth hba.wellFormed
        ((ctx_with_blob_keyAt cx E_core.blobs.get? x').symm.trans hk),
      by simp [hrec_nil],
      fun _ _ hb => hb,
      hrd_ty_cx', hty_lbb, hty_def, hrd_val_cx', hval_lbb, hval_def, hci₀_eq⟩
  exact ⟨decl, ci₀, hread_rec, hcco, hinst, hname, hdnames, hnb, hrra⟩

/-- Single `.defn` member `i` of a walked `.muts ms` block `c` at `a ∉ order_role`: supplies
`(recurDeps c d).toList = []`, `readDefinition = .ok (decl, false)` for every `heights`,
`CheckedConstOrigin`, and `L1.RecordReadsAs t E_core (Core.dprjAddr a i) c_dprj ci₀`. -/
private theorem checkedMutsDefn_member
    (hRP : RolePreludeInputs) (hSR : SafeRefsInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role st : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {seeds : List _root_.Address}
    {a : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    {i : Nat} {d : Ixon.Definition}
    (hbound : IxVM.Consistency.Bounded calls)
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hblobs₀ : ∀ bytes, Hashed calls bytes →
      E₀.blobs.get? (_root_.Address.blake3Pure bytes) = some bytes)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hnoInt_core : ¬ L1.EnvInternalCollision
      (coreEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role) pre))
    (hsub_rec : ∀ x c_x,
      Ix.Cert.recordAt (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) x = some c_x →
      Ix.Cert.recordAt (coreEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role) pre) x = some c_x)
    (hord : IxVM.Consistency.UsedClosureOrderAt t
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role))
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) order)
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.blobsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.hintsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)))).store)
    (hproj_emp : ∀ k : Core.KKey, st.projLevels[k]? = none)
    (ha_ord : a ∈ order)
    (ha_not_role : a ∉ order_role)
    (hrec₀ : Ix.Cert.recordAt E₀ a = some c)
    (hrecE : Ix.Cert.recordAt
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) a = some c)
    (hwk : WkAll calls b.address t E₀ a)
    (hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a)
    (hinfo : c.info = .muts ms)
    (hms : ms[i]? = some (.defn d))
    (hm : Claim.MutsMemberCheckedAtFull calls b.address t a ms i) :
    let Keep := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x
    let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
    let E_core := coreEnvRole E₀ Keep (roleSuppOf E_role order_role)
      (Ix.Cert.blobsOf E_role order_role) pre
    let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
    let self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey) :=
      fun j => if j < ms.size then some (cx.memberKey (.member a j)) else none
    i < UInt64.size ∧
    Core.dprjAddr a i ∉ order_role ∧
    (Ix.Kernel.Reader.recurDeps c d).toList = [] ∧
    ∀ heights : Core.KKey → Nat,
      ∃ (decl : Ix.Kernel.Declaration .anon) (ci₀ : Ix.Kernel.ConstantInfo .anon),
        Ix.Kernel.Reader.readDefinition cx st heights (.member a i) (List.range d.lvls.toNat)
          (Ix.Kernel.Reader.MemberReader.mk' cx c id self) d = .ok (decl, false) ∧
        CheckedConstOrigin calls t b.address E_core order_role decl ∧
        IxVM.Consistency.installs decl = [ci₀] ∧
        ci₀.name = Core.keyOf t (Core.dprjAddr a i) ∧
        decl.names = [Core.keyOf t (Core.dprjAddr a i)] ∧
        (∀ kb, decl ≠ .basisDecl kb) ∧
        L1.RecordReadsAs t E_core (Core.dprjAddr a i)
          ⟨.dPrj ⟨i.toUInt64, a⟩, #[], #[], #[], #[]⟩ ci₀ := by
  intro Keep E E_core cx self
  have hinLogic : IxVM.Consistency.InLogic c := by
    by_contra hnin
    exact hnot_out ⟨c, hrec₀, Or.inl hnin⟩
  have hmem_ms : Ixon.MutConst.defn d ∈ ms.toList :=
    List.mem_of_getElem? (by simpa using hms)
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    rw [IxVM.Consistency.InLogic, hinfo] at hinLogic
    exact hinLogic (.defn d) hmem_ms
  have hnu : L1.defnIsUnsafeCI d = false := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
  obtain ⟨hi, hd_not_role, hmkey⟩ :=
    dprj_nonRole_and_memberKey hRP hbound hadm hba hcomm_extra hload hexact₀ hnoCol hord hauth
      ha_ord ha_not_role hrecE hinfo hms hm
  obtain ⟨_, huniq_dprj⟩ := dprj_store_eq_of_mutsMemberChecked hbound hnoCol hm hms
  have hchk_i : Claim.CheckedAtFull calls b.address t (Core.dprjAddr a i) := by
    have h0 := mutsMemberCheckedAtFull_to_checkedAtFull hbound hm hms
    simpa only [Core.Specs.Callees.memberProjInfo, Core.dprjAddr] using h0
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    bytes, E_ld, _, hrc_m, _, _, hhash_ld, hblake_ld, hload_ld, hL1,
    hsub_ld, hld, ev_chk, _, hsub_chk⟩ := checkedAtFull_loadedL1 hbound hchk_i
  obtain ⟨c_ld, hdec_ld, _, _, v', hld', hraw⟩ := hL1
  rw [hld] at hld'; injection hld' with hvv; subst hvv
  have hc_ld_eq : c_ld = ⟨.dPrj ⟨i.toUInt64, a⟩, #[], #[], #[], #[]⟩ :=
    huniq_dprj bytes c_ld hblake_ld hdec_ld (Or.inr (Or.inr (Core.hashed_mono hsub_ld hhash_ld)))
  subst c_ld
  rw [hblake_ld] at hraw
  unfold L1.RawCIRep at hraw
  dsimp only at hraw
  obtain ⟨_, lcB, cb_ld, ms_ld, d_ld, blobs, hgetB, hlcB, _, hexB, _, hcb_info, hms_ld, hb_ld, hraw_d⟩ := hraw
  have hcb_eq : cb_ld = c := by
    unfold Ix.Cert.recordAt at hrec₀
    cases hget₀ : E₀.consts.get? a with
    | none => rw [hget₀] at hrec₀; cases hrec₀
    | some lc₀ =>
      rw [hget₀] at hrec₀
      obtain ⟨hh₀, hbl₀⟩ := hload.1 a lc₀ hget₀
      obtain ⟨hhB, hblB⟩ := hload_ld.1 a lcB hgetB
      obtain ⟨c₀, hlc₀, hex₀⟩ := hexact₀ a lc₀ hget₀
      have hraw_eq : lcB.rawBytes = lc₀.rawBytes := by
        by_contra hne
        exact hnoCol (Or.inl ⟨a, lc₀.rawBytes, lcB.rawBytes, Or.inr (Or.inr ⟨hh₀, hbl₀⟩),
          Core.hashed_mono hsub_ld hhB, hne, hblB⟩)
      rw [hraw_eq, hex₀] at hexB
      have hcc : c₀ = cb_ld := Except.ok.inj hexB
      rw [hcc] at hlc₀
      exact Option.some.inj (hlc₀.symm.trans hrec₀)
  subst cb_ld
  have hms_eq : ms = ms_ld := by
    rw [hinfo] at hcb_info
    exact Ixon.ConstantInfo.muts.inj hcb_info
  subst ms_ld
  have hi_toNat : i.toUInt64.toNat = i := toUInt64_toNat_eq hi
  rw [hi_toNat] at hms_ld
  have hms_list : ms.toList[i]? = some (.defn d) := by simpa using hms
  rw [hms_list] at hms_ld
  injection hms_ld with hmc_eq
  injection hmc_eq with hd_eq
  subst d_ld
  have hrec_nil : L1.defnMemberRecurAddrs d a ms.toList = [] := by
    simp [L1.defnMemberRecurAddrs, hnu]
  rw [hrec_nil] at hraw_d
  have hdir_ty : ∀ x ∈ IxVM.Consistency.exprRefIdxs d.typ, x ∈ IxVM.Consistency.usedRefIdxs c := by
    intro x hx
    simp only [IxVM.Consistency.usedRefIdxs, hinfo, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨.defn d, hmem_ms,
      by simp [IxVM.Consistency.mutRefIdxs, hx]⟩)
  have hdir_val : ∀ x ∈ IxVM.Consistency.exprRefIdxs d.value, x ∈ IxVM.Consistency.usedRefIdxs c := by
    intro x hx
    simp only [IxVM.Consistency.usedRefIdxs, hinfo, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨.defn d, hmem_ms,
      by simp [IxVM.Consistency.mutRefIdxs, hx]⟩)
  obtain ⟨hrecDeps, ty₀, val₀, hrd_ty_cx', hty_lbb, hty_def, hrd_val_cx', hval_lbb, hval_def, hheights⟩ :=
    checkedDefnCore hSR (decl_addr := Core.dprjAddr a i) (ref := .member a i) (self := self)
      hbound hadm hba hload hexact₀ hblobs₀ hnoCol hord hauth hproj_emp ha_ord hd_not_role
      hrec₀ hrecE hwk hsafe hdir_ty hdir_val hmkey hrc_m hload_ld hsub_ld hb_ld hraw_d ev_chk hsub_chk
  refine ⟨hi, hd_not_role, hrecDeps, fun heights => ?_⟩
  obtain ⟨decl, ci₀, hn, hrd_def, hcco, hinst, hname, hdnames, hnb, hci₀_eq⟩ := hheights heights
  have hrec_core : Ix.Cert.recordAt E_core a = some c := hsub_rec a c hrecE
  have hrra : L1.RecordReadsAs t E_core (Core.dprjAddr a i)
      ⟨.dPrj ⟨i.toUInt64, a⟩, #[], #[], #[], #[]⟩ ci₀ := by
    refine ⟨hnoInt_core, ?_⟩
    dsimp only
    intro cb' ms' d' hrecB' hinfo' hms'
    rw [hrec_core] at hrecB'
    injection hrecB' with hcb'
    subst cb'
    rw [hinfo] at hinfo'
    injection hinfo' with hms_eq'
    subst ms'
    rw [hi_toNat, hms_list] at hms'
    injection hms' with hmc'
    injection hmc' with hd'
    subst d'
    exact ⟨{ cx with blob := E_core.blobs.get? }, self,
      Core.keyOf t (Core.dprjAddr a i), List.range d.lvls.toNat, ty₀, val₀, hn,
      by simp, by simp,
      fun x' _ hk => streamContext_keyAt_ok_inv hauth hba.wellFormed
        ((ctx_with_blob_keyAt cx E_core.blobs.get? x').symm.trans hk),
      by simp [hrec_nil],
      fun _ _ hb => hb,
      hrd_ty_cx', hty_lbb, hty_def, hrd_val_cx', hval_lbb, hval_def, hci₀_eq⟩
  exact ⟨decl, ci₀, hrd_def, hcco, hinst, hname, hdnames, hnb, hrra⟩

/-- Forward `forIn` completeness over an array when every step yields and preserves invariant `I`. -/
private theorem forIn_complete_list {α σ ε : Type}
    {f : α → σ → Except ε (ForInStep σ)}
    (I : List α → σ → Prop) (full : List α)
    (step : ∀ pre x post s, pre ++ x :: post = full → I pre s →
      ∃ s', f x s = .ok (.yield s') ∧ I (pre ++ [x]) s') :
    ∀ (post pre : List α) (s : σ), pre ++ post = full → I pre s →
      ∃ res, forIn post s f = .ok res ∧ I full res
  | [], pre, s, whole, holds => by
    rw [List.append_nil] at whole
    subst whole
    exact ⟨s, rfl, holds⟩
  | x :: post, pre, s, whole, holds => by
    obtain ⟨s', hf, holds'⟩ := step pre x post s whole holds
    rw [List.forIn_cons, hf]
    simp only [bind, Except.bind]
    exact forIn_complete_list I full step post (pre ++ [x]) s'
      (by rw [List.append_assoc]; exact whole) holds'

private theorem forIn_complete_array {α σ ε : Type}
    {f : α → σ → Except ε (ForInStep σ)}
    (I : List α → σ → Prop) (xs : Array α) (s₀ : σ)
    (hinit : I [] s₀)
    (step : ∀ pre x post s, pre ++ x :: post = xs.toList → I pre s →
      ∃ s', f x s = .ok (.yield s') ∧ I (pre ++ [x]) s') :
    ∃ res, forIn xs s₀ f = .ok res ∧ I xs.toList res := by
  rw [← Array.forIn_toList]
  exact forIn_complete_list I xs.toList step xs.toList [] s₀ rfl hinit

private theorem list_filterMap_defn_all :
    ∀ (xs : List Ixon.MutConst),
      xs.all (fun | .defn _ => true | _ => false) = true →
      (xs.filterMap (fun | .defn d => some d | _ => none)).length = xs.length ∧
      ∀ (i : Nat),
        ((xs.filterMap (fun | .defn d => some d | _ => none))[i]? =
          match xs[i]? with | some (.defn d) => some d | _ => none)
  | [], _ => ⟨rfl, fun _ => rfl⟩
  | mc :: tl, hall => by
    rw [List.all_cons, Bool.and_eq_true] at hall
    cases mc with
    | defn d =>
      obtain ⟨hlen, hget⟩ := list_filterMap_defn_all tl hall.2
      refine ⟨by simp [hlen], fun i => ?_⟩
      cases i with
      | zero => rfl
      | succ j => exact hget j
    | indc _ | recr _ => cases hall.1

private theorem list_all_defn_eq_map :
    ∀ (xs : List Ixon.MutConst),
      xs.all (fun | .defn _ => true | _ => false) = true →
      ∃ ts : List Ixon.Definition, xs = ts.map Ixon.MutConst.defn
  | [], _ => ⟨[], rfl⟩
  | mc :: tl, hall => by
    rw [List.all_cons, Bool.and_eq_true] at hall
    cases mc with
    | defn d =>
      obtain ⟨ts, rfl⟩ := list_all_defn_eq_map tl hall.2
      exact ⟨d :: ts, rfl⟩
    | indc _ | recr _ => cases hall.1

private theorem list_flatMap_of_getElem?_singleton {α β : Type} (f : α → List β) (g : Nat → β) :
    ∀ (xs : List α),
      (∀ k < xs.length, ∃ x, xs[k]? = some x ∧ f x = [g k]) →
      xs.flatMap f = (List.range xs.length).map g
  | [], _ => rfl
  | x :: tl, h => by
    obtain ⟨x', hx0, hf0⟩ := h 0 (by simp)
    injection hx0 with hxeq; subst hxeq
    have htl : ∀ k < tl.length, ∃ y, tl[k]? = some y ∧ f y = [g (k + 1)] := by
      intro k hk
      exact h (k + 1) (by simp; omega)
    rw [List.flatMap_cons, hf0, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.singleton_append, List.cons.injEq]
    exact ⟨rfl, (list_flatMap_of_getElem?_singleton f (fun k => g (k + 1)) tl htl).trans
      (by rw [List.map_map]; rfl)⟩

private theorem nodup_map_of_inj_on {α β : Type} {xs : List α} {f : α → β}
    (hnd : xs.Nodup)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a tl ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih hnd.2 (fun x hx y hy hxy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    have hab := hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb
    subst hab
    exact hnd.1 hb

private theorem append_eq_append_cons_inv {α : Type} :
    ∀ (xs ys pre : List α) (d : α) (suf : List α),
      xs ++ ys = pre ++ d :: suf →
      (∃ suf₁, xs = pre ++ d :: suf₁ ∧ suf = suf₁ ++ ys) ∨
      (∃ r_before, pre = xs ++ r_before ∧ ys = r_before ++ d :: suf)
  | [], ys, pre, d, suf, h => Or.inr ⟨pre, rfl, by simpa using h⟩
  | x :: xs, ys, [], d, suf, h => by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact Or.inl ⟨xs, by rw [h.1]; rfl, h.2.symm⟩
  | x :: xs, ys, p :: pre, d, suf, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases append_eq_append_cons_inv xs ys pre d suf h.2 with
      ⟨suf₁, hxs, hsuf⟩ | ⟨r_before, hpre, hys⟩
    · exact Or.inl ⟨suf₁, by rw [h.1, hxs]; rfl, hsuf⟩
    · exact Or.inr ⟨r_before, by rw [h.1, hpre]; rfl, hys⟩

/-- No checked projection record `(a, c)` in `E₀` can be its own owner (`ownerOf a c ≠ a`), since
its `RawCIRep` owner record at `ownerOf a c` is a `.muts` block. -/
private theorem proj_ownerOf_ne_self
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {a : _root_.Address} {c : Ixon.Constant}
    (hbound : IxVM.Consistency.Bounded calls)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hrec₀ : Ix.Cert.recordAt E₀ a = some c)
    (hprojInfo : IsProjInfo c.info)
    (hchk : Claim.CheckedAtFull calls bAddr t a) :
    Ix.Cert.ownerOf a c ≠ a := by
  intro heq
  obtain ⟨_, _, _, _, _, _, _, _, _, cs_load, _,
    bytes, E_ld, _, _, _, _, hhash_ld, hblake_ld, hload_ld, hL1,
    hsub_ld, hld, _, _, _⟩ := checkedAtFull_loadedL1 hbound hchk
  obtain ⟨c_ld, hdec_ld, _, _, _, hld', hraw⟩ := hL1
  rw [hld] at hld'; injection hld' with hvv; subst hvv
  unfold Ix.Cert.recordAt at hrec₀
  cases hget₀ : E₀.consts.get? a with
  | none => rw [hget₀] at hrec₀; cases hrec₀
  | some lc₀ =>
    rw [hget₀] at hrec₀
    obtain ⟨hh₀, hbl₀⟩ := hload.1 a lc₀ hget₀
    obtain ⟨c₀, hlc₀, hex₀⟩ := hexact₀ a lc₀ hget₀
    have hraw_eq : bytes = lc₀.rawBytes := by
      by_contra hne
      exact hnoCol (Or.inl ⟨a, lc₀.rawBytes, bytes, Or.inr (Or.inr ⟨hh₀, hbl₀⟩),
        Core.hashed_mono hsub_ld hhash_ld, hne, hblake_ld⟩)
    rw [hraw_eq, hex₀] at hdec_ld
    have hc₀_eq : c₀ = c := Option.some.inj (hlc₀.symm.trans hrec₀)
    subst c₀
    have hcc : c = c_ld := Except.ok.inj hdec_ld
    subst c_ld
    rw [hblake_ld] at hraw
    have hblk_false : ∀ (lcB : Ixon.LazyConstant) (cb : Ixon.Constant) (ms : Array Ixon.MutConst),
        E_ld.consts.get? a = some lcB →
        Ixon.deConstantExact lcB.rawBytes = .ok cb →
        cb.info = .muts ms → False := by
      intro lcB cb ms hgetB hexB hcb_info
      obtain ⟨hhB, hblB⟩ := hload_ld.1 a lcB hgetB
      have hrawB : lcB.rawBytes = lc₀.rawBytes := by
        by_contra hne
        exact hnoCol (Or.inl ⟨a, lc₀.rawBytes, lcB.rawBytes, Or.inr (Or.inr ⟨hh₀, hbl₀⟩),
          Core.hashed_mono hsub_ld hhB, hne, hblB⟩)
      rw [hrawB, hex₀] at hexB
      have hcb_c : c = cb := Except.ok.inj hexB
      subst cb
      rw [hcb_info] at hprojInfo
      cases hprojInfo
    unfold L1.RawCIRep at hraw
    cases hc : c.info with
    | defn _ | axio _ | quot _ | recr _ | muts _ =>
      simp [IsProjInfo, hc] at hprojInfo
    | dPrj p | iPrj p | rPrj p =>
      have hp : p.block = a := by simpa [Ix.Cert.ownerOf, hc] using heq
      dsimp only at hraw
      rw [hp] at hraw
      obtain ⟨_, lcB, cb, ms, _, _, hgetB, _, _, hexB, _, hcb_info, _, _, _⟩ := hraw
      exact hblk_false lcB cb ms hgetB hexB hcb_info
    | cPrj p =>
      have hp : p.block = a := by simpa [Ix.Cert.ownerOf, hc] using heq
      dsimp only at hraw
      rw [hp] at hraw
      obtain ⟨_, _, lcB, cb, ms, _, _, _, hgetB, _, _, hexB, _, hcb_info, _, _, _, _⟩ := hraw
      exact hblk_false lcB cb ms hgetB hexB hcb_info

/-- Every `WkSafe` projection record `(a, c)` (`ownerOf a c ≠ a`) has a `.muts` owner record in
`E₀` that is itself `WkSafe` with strictly smaller `rankAll`. -/
private theorem wkSafe_owner_of_proj
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {a : _root_.Address} {c : Ixon.Constant}
    (hbound : IxVM.Consistency.Bounded calls)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hwkSafe : WkSafe calls bAddr t E₀ a)
    (hrec₀ : Ix.Cert.recordAt E₀ a = some c)
    (hproj : Ix.Cert.ownerOf a c ≠ a) :
    ∃ cb ms,
      Ix.Cert.recordAt E₀ (Ix.Cert.ownerOf a c) = some cb ∧
      cb.info = .muts ms ∧
      WkSafe calls bAddr t E₀ (Ix.Cert.ownerOf a c) ∧
      rankAll calls bAddr t E₀ (Ix.Cert.ownerOf a c) < rankAll calls bAddr t E₀ a := by
  obtain ⟨c', hrec₀', hchk_or⟩ := (wkAll_closedSubwalk calls bAddr t E₀).checked a hwkSafe.1
  have hc_eq : c' = c := Option.some.inj (hrec₀'.symm.trans hrec₀)
  subst c'
  have hchk : Claim.CheckedAtFull calls bAddr t a := by
    rcases hchk_or with ⟨ms', hmuts, _⟩ | hchk
    · simp [Ix.Cert.ownerOf, hmuts] at hproj
    · exact hchk
  obtain ⟨_, _, _, _, _, _, _, _, _, cs_load, _,
    bytes, E_ld, _, _, _, _, hhash_ld, hblake_ld, hload_ld, hL1,
    hsub_ld, hld, _, _, _⟩ := checkedAtFull_loadedL1 hbound hchk
  obtain ⟨c_ld, hdec_ld, _, _, v', hld', hraw⟩ := hL1
  rw [hld] at hld'; injection hld' with hvv; subst v'
  have hc_ld_eq : c_ld = c := by
    unfold Ix.Cert.recordAt at hrec₀
    cases hget₀ : E₀.consts.get? a with
    | none => rw [hget₀] at hrec₀; cases hrec₀
    | some lc₀ =>
      rw [hget₀] at hrec₀
      obtain ⟨hh₀, hbl₀⟩ := hload.1 a lc₀ hget₀
      obtain ⟨c₀, hlc₀, hex₀⟩ := hexact₀ a lc₀ hget₀
      have hraw_eq : bytes = lc₀.rawBytes := by
        by_contra hne
        exact hnoCol (Or.inl ⟨a, lc₀.rawBytes, bytes, Or.inr (Or.inr ⟨hh₀, hbl₀⟩),
          Core.hashed_mono hsub_ld hhash_ld, hne, hblake_ld⟩)
      rw [hraw_eq, hex₀] at hdec_ld
      have hcc : c₀ = c_ld := Except.ok.inj hdec_ld
      rw [hcc] at hlc₀
      exact Option.some.inj (hlc₀.symm.trans hrec₀)
  subst c_ld
  rw [hblake_ld] at hraw
  obtain ⟨lcB, cb, ms, hgetB_ld, _, _, hexB_ld, _, hcb_info⟩ := hraw.owner_recordAt hproj
  have hedge_own : Core.S0.WalkEdge E₀ a (Ix.Cert.ownerOf a c) :=
    ⟨c, hrec₀, Or.inl ⟨rfl, hproj⟩⟩
  obtain ⟨hwk_own, _⟩ := (wkAll_closedSubwalk calls bAddr t E₀).step a _ hwkSafe.1 hedge_own
  obtain ⟨cb₀, hrec₀_own, _⟩ := (wkAll_closedSubwalk calls bAddr t E₀).checked _ hwk_own
  have hcb₀_eq : cb₀ = cb := by
    unfold Ix.Cert.recordAt at hrec₀_own
    cases hget₀_b : E₀.consts.get? (Ix.Cert.ownerOf a c) with
    | none => rw [hget₀_b] at hrec₀_own; cases hrec₀_own
    | some lc₀_b =>
      rw [hget₀_b] at hrec₀_own
      obtain ⟨hh₀_b, hbl₀_b⟩ := hload.1 _ lc₀_b hget₀_b
      obtain ⟨hhB, hblB⟩ := hload_ld.1 _ lcB hgetB_ld
      obtain ⟨c₀_b, hlc₀_b, hex₀_b⟩ := hexact₀ _ lc₀_b hget₀_b
      have hraw_eq : lcB.rawBytes = lc₀_b.rawBytes := by
        by_contra hne
        exact hnoCol (Or.inl ⟨Ix.Cert.ownerOf a c, lc₀_b.rawBytes, lcB.rawBytes,
          Or.inr (Or.inr ⟨hh₀_b, hbl₀_b⟩),
          Core.hashed_mono hsub_ld hhB, hne, hblB⟩)
      rw [hraw_eq, hex₀_b] at hexB_ld
      have hcc : c₀_b = cb := Except.ok.inj hexB_ld
      rw [hcc] at hlc₀_b
      exact Option.some.inj (hrec₀_own.symm.trans hlc₀_b)
  subst cb₀
  obtain ⟨hwkSafe_own, hrk_lt⟩ := wkSafe_owner_of_nonproj hwkSafe hrec₀ hproj
    (fun cb' hrec' => by
      rw [hrec₀_own] at hrec'
      injection hrec' with heq
      subst cb'
      simp [Ix.Cert.ownerOf, hcb_info])
  exact ⟨cb, ms, hrec₀_own, hcb_info, hwkSafe_own, hrk_lt⟩

/-- Walked projection resolution helper: any walked safe record `(a, c)` with `ownerOf a c ≠ a`
and `ownerOf a c ∈ order` has `(resolveSource cx.store a c).isNone = false`, and its parent block
`ownerOf a c` is a `.muts` block in `WkSafe` with strictly smaller `rankAll`. -/
private theorem walkedProjResolveOk
    (hSR : SafeRefsInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {seeds : List _root_.Address}
    {a : _root_.Address} {c : Ixon.Constant}
    (hbound : IxVM.Consistency.Bounded calls)
    (_hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hord : IxVM.Consistency.UsedClosureOrderAt t
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role))
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) order)
    (hown_ord : Ix.Cert.ownerOf a c ∈ order)
    (hrec₀ : Ix.Cert.recordAt E₀ a = some c)
    (hwk : WkAll calls b.address t E₀ a)
    (hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a)
    (hproj : Ix.Cert.ownerOf a c ≠ a)
    (hchk : Claim.CheckedAtFull calls b.address t a) :
    let Keep := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x
    let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
    let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
    (Ix.Kernel.Reader.resolveSource cx.store a c).isNone = false ∧
    ∃ cb ms,
      Ix.Cert.recordAt E₀ (Ix.Cert.ownerOf a c) = some cb ∧
      Ix.Cert.recordAt E (Ix.Cert.ownerOf a c) = some cb ∧
      cb.info = .muts ms ∧
      WkSafe calls b.address t E₀ (Ix.Cert.ownerOf a c) ∧
      rankAll calls b.address t E₀ (Ix.Cert.ownerOf a c) < rankAll calls b.address t E₀ a ∧
      (∀ d_all : ms.all (fun | .defn _ => true | _ => false) = true,
        ∃ (i : Nat) (d_m : Ixon.Definition),
          i < ms.size ∧ i < UInt64.size ∧
          ms[i]? = some (.defn d_m) ∧
          a = Core.dprjAddr (Ix.Cert.ownerOf a c) i ∧
          c = ⟨.dPrj ⟨i.toUInt64, Ix.Cert.ownerOf a c⟩, #[], #[], #[], #[]⟩) := by
  intro Keep E cx
  obtain ⟨cb, ms, hrec₀_own, hcb_info, hwkSafe_own, hrk_lt⟩ :=
    wkSafe_owner_of_proj hbound hload hexact₀ hnoCol ⟨hwk, hnot_out⟩ hrec₀ hproj
  obtain ⟨_, _, _, _, _, _, _, _, _, cs_load, _,
    bytes, E_ld, _, _, _, _, hhash_ld, hblake_ld, hload_ld, hL1,
    hsub_ld, hld, _, _, _⟩ := checkedAtFull_loadedL1 hbound hchk
  obtain ⟨c_ld, hdec_ld, _, htv, _, hld', hraw⟩ := hL1
  rw [hld] at hld'; injection hld' with hvv; subst hvv
  have hc_ld_eq : c_ld = c := by
    unfold Ix.Cert.recordAt at hrec₀
    cases hget₀ : E₀.consts.get? a with
    | none => rw [hget₀] at hrec₀; cases hrec₀
    | some lc₀ =>
      rw [hget₀] at hrec₀
      obtain ⟨hh₀, hbl₀⟩ := hload.1 a lc₀ hget₀
      obtain ⟨c₀, hlc₀, hex₀⟩ := hexact₀ a lc₀ hget₀
      have hraw_eq : bytes = lc₀.rawBytes := by
        by_contra hne
        exact hnoCol (Or.inl ⟨a, lc₀.rawBytes, bytes, Or.inr (Or.inr ⟨hh₀, hbl₀⟩),
          Core.hashed_mono hsub_ld hhash_ld, hne, hblake_ld⟩)
      rw [hraw_eq, hex₀] at hdec_ld
      have hcc : c₀ = c_ld := Except.ok.inj hdec_ld
      rw [hcc] at hlc₀
      exact Option.some.inj (hlc₀.symm.trans hrec₀)
  subst c_ld
  rw [hblake_ld] at hraw
  have hrecE_own : Ix.Cert.recordAt E (Ix.Cert.ownerOf a c) = some cb :=
    recordAt_subEnv_of_keep E₀ Keep _ (Or.inr hwkSafe_own) hrec₀_own
  have hnd_dec : ((Ix.Cert.Stream.decodedOf E order).map Prod.fst).Nodup :=
    hord.nodup.sublist (Ix.Cert.Stream.decodedOf_keys E order)
  have hst_own : cx.store (Ix.Cert.ownerOf a c) = some cb :=
    streamContext_store_of_mem hnd_dec (mem_decodedOf_of_mem hown_ord hrecE_own)
  have hcb_from_ld : ∀ (lcB' : Ixon.LazyConstant) (cb' : Ixon.Constant),
      E_ld.consts.get? (Ix.Cert.ownerOf a c) = some lcB' →
      Ixon.deConstantExact lcB'.rawBytes = .ok cb' →
      cb' = cb := by
    intro lcB' cb' hgetB' hexB'
    unfold Ix.Cert.recordAt at hrec₀_own
    cases hget₀_b : E₀.consts.get? (Ix.Cert.ownerOf a c) with
    | none => rw [hget₀_b] at hrec₀_own; cases hrec₀_own
    | some lc₀_b =>
      rw [hget₀_b] at hrec₀_own
      obtain ⟨hh₀_b, hbl₀_b⟩ := hload.1 _ lc₀_b hget₀_b
      obtain ⟨hhB, hblB⟩ := hload_ld.1 _ lcB' hgetB'
      obtain ⟨c₀_b, hlc₀_b, hex₀_b⟩ := hexact₀ _ lc₀_b hget₀_b
      have hraw_eq : lcB'.rawBytes = lc₀_b.rawBytes := by
        by_contra hne
        exact hnoCol (Or.inl ⟨Ix.Cert.ownerOf a c, lc₀_b.rawBytes, lcB'.rawBytes,
          Or.inr (Or.inr ⟨hh₀_b, hbl₀_b⟩),
          Core.hashed_mono hsub_ld hhB, hne, hblB⟩)
      rw [hraw_eq, hex₀_b] at hexB'
      have hcc : c₀_b = cb' := Except.ok.inj hexB'
      rw [hcc] at hlc₀_b
      exact Option.some.inj (hlc₀_b.symm.trans hrec₀_own)
  have hres_ok : (Ix.Kernel.Reader.resolveSource cx.store a c).isNone = false ∧
      (∀ d_all : ms.all (fun | .defn _ => true | _ => false) = true,
        ∃ (i : Nat) (d_m : Ixon.Definition),
          i < ms.size ∧ i < UInt64.size ∧
          ms[i]? = some (.defn d_m) ∧
          a = Core.dprjAddr (Ix.Cert.ownerOf a c) i ∧
          c = ⟨.dPrj ⟨i.toUInt64, Ix.Cert.ownerOf a c⟩, #[], #[], #[], #[]⟩) := by
    unfold L1.ConstantTablesValid at htv
    unfold L1.RawCIRep at hraw
    cases hc : c.info with
    | defn _ | axio _ | quot _ | recr _ | muts _ =>
      simp [Ix.Cert.ownerOf, hc] at hproj
    | dPrj p =>
      rw [hc] at htv hraw
      obtain ⟨hsh, hrefs, hunivs, hbind⟩ := htv
      obtain ⟨_, lcB', cb', ms', d_m, _, hgetB', _, _, hexB', _, hcb', hms', _, _⟩ := hraw
      have hemp : Ix.Kernel.Reader.emptyTables c = true := by
        simp [Ix.Kernel.Reader.emptyTables, hsh, hrefs, hunivs, hbind]
      have hown_eq : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc]
      rw [← hown_eq] at hgetB'
      have hcb_eq' := hcb_from_ld lcB' cb' hgetB' hexB'
      subst cb'
      rw [hcb_info] at hcb'; injection hcb' with hmseq; subst ms'
      have hms_arr : ms[p.idx.toNat]? = some (.defn d_m) := by simpa using hms'
      have hres : Ix.Kernel.Reader.resolveSource cx.store a c =
          some (.member p.block p.idx.toNat) := by
        unfold Ix.Kernel.Reader.resolveSource
        rw [hc]
        simp [hemp, ← hown_eq, hst_own, hcb_info, hms_arr, bind, Option.bind, guard, pure]
      have hc_emp := Ix.Cert.ReadingKeys.empty_constant hemp
      have hp_eq : (⟨(p.idx.toNat).toUInt64, Ix.Cert.ownerOf a c⟩ : Ixon.DefinitionProj) = p := by
        cases p with
        | mk idx blk =>
          have hidx : (idx.toNat).toUInt64 = idx := UInt64.ofNat_toNat
          simp only [hown_eq, hidx]
      have hc_form : c = ⟨.dPrj ⟨(p.idx.toNat).toUInt64, Ix.Cert.ownerOf a c⟩, #[], #[], #[], #[]⟩ := by
        rw [hp_eq, ← hc]
        exact hc_emp
      refine ⟨by simp [hres], fun _ => ⟨p.idx.toNat, d_m, ?_, p.idx.toNat_lt, hms_arr, ?_, hc_form⟩⟩
      · exact (Array.getElem?_eq_some_iff.mp hms_arr).1
      · have hser := (deConstantExact_proj_eq_serConstant hdec_ld hemp (by simp [IsProjInfo, hc])).1
        exact hblake_ld.symm.trans ((congrArg _root_.Address.blake3Pure hser).trans
          (congrArg (fun x => _root_.Address.blake3Pure (Ixon.serConstant x)) hc_form))
    | iPrj p =>
      rw [hc] at htv hraw
      obtain ⟨hsh, hrefs, hunivs, hbind⟩ := htv
      obtain ⟨_, lcB', cb', ms', ind, _, hgetB', _, _, hexB', _, hcb', hms', _, _⟩ := hraw
      have hemp : Ix.Kernel.Reader.emptyTables c = true := by
        simp [Ix.Kernel.Reader.emptyTables, hsh, hrefs, hunivs, hbind]
      have hown_eq : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc]
      rw [← hown_eq] at hgetB'
      have hcb_eq' := hcb_from_ld lcB' cb' hgetB' hexB'
      subst cb'
      rw [hcb_info] at hcb'; injection hcb' with hmseq; subst ms'
      have hms_arr : ms[p.idx.toNat]? = some (.indc ind) := by simpa using hms'
      have hres : Ix.Kernel.Reader.resolveSource cx.store a c =
          some (.member p.block p.idx.toNat) := by
        unfold Ix.Kernel.Reader.resolveSource
        rw [hc]
        simp [hemp, ← hown_eq, hst_own, hcb_info, hms_arr, bind, Option.bind, guard, pure]
      refine ⟨by simp [hres], fun d_all => ?_⟩
      have hmem_ind : Ixon.MutConst.indc ind ∈ ms.toList := List.mem_of_getElem? hms'
      rw [← Array.all_toList, List.all_eq_true] at d_all
      cases d_all _ hmem_ind
    | rPrj p =>
      rw [hc] at htv hraw
      obtain ⟨hsh, hrefs, hunivs, hbind⟩ := htv
      obtain ⟨_, lcB', cb', ms', rc, _, hgetB', _, _, hexB', _, hcb', hms', _, _⟩ := hraw
      have hemp : Ix.Kernel.Reader.emptyTables c = true := by
        simp [Ix.Kernel.Reader.emptyTables, hsh, hrefs, hunivs, hbind]
      have hown_eq : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc]
      rw [← hown_eq] at hgetB'
      have hcb_eq' := hcb_from_ld lcB' cb' hgetB' hexB'
      subst cb'
      rw [hcb_info] at hcb'; injection hcb' with hmseq; subst ms'
      have hms_arr : ms[p.idx.toNat]? = some (.recr rc) := by simpa using hms'
      have hres : Ix.Kernel.Reader.resolveSource cx.store a c =
          some (.member p.block p.idx.toNat) := by
        unfold Ix.Kernel.Reader.resolveSource
        rw [hc]
        simp [hemp, ← hown_eq, hst_own, hcb_info, hms_arr, bind, Option.bind, guard, pure]
      refine ⟨by simp [hres], fun d_all => ?_⟩
      have hmem_rc : Ixon.MutConst.recr rc ∈ ms.toList := List.mem_of_getElem? hms'
      rw [← Array.all_toList, List.all_eq_true] at d_all
      cases d_all _ hmem_rc
    | cPrj p =>
      rw [hc] at htv hraw
      obtain ⟨hsh, hrefs, hunivs, hbind⟩ := htv
      obtain ⟨_, _, lcB', cb', ms', ind, ct, _, hgetB', _, _, hexB', _, hcb', hms', hct', _, _⟩ := hraw
      have hemp : Ix.Kernel.Reader.emptyTables c = true := by
        simp [Ix.Kernel.Reader.emptyTables, hsh, hrefs, hunivs, hbind]
      have hown_eq : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc]
      rw [← hown_eq] at hgetB'
      have hcb_eq' := hcb_from_ld lcB' cb' hgetB' hexB'
      subst cb'
      rw [hcb_info] at hcb'; injection hcb' with hmseq; subst ms'
      have hms_arr : ms[p.idx.toNat]? = some (.indc ind) := by simpa using hms'
      have hct_arr : ind.ctors[p.cidx.toNat]? = some ct := by simpa using hct'
      have hcidx_nat : ct.cidx.toNat = p.cidx.toNat :=
        hSR.indBlockCtorIdx hbound hload hwkSafe_own.1 hwkSafe_own.2 hrec₀_own hcb_info hms_arr hct_arr
      have hcidx_eq : ct.cidx = p.cidx := UInt64.toNat_inj.mp hcidx_nat
      have hres : Ix.Kernel.Reader.resolveSource cx.store a c =
          some (.ctor p.block p.idx.toNat p.cidx.toNat) := by
        unfold Ix.Kernel.Reader.resolveSource
        rw [hc]
        simp [hemp, ← hown_eq, hst_own, hcb_info, hms_arr, hct_arr, hcidx_eq,
          bind, Option.bind, guard, pure]
      refine ⟨by simp [hres], fun d_all => ?_⟩
      have hmem_ind : Ixon.MutConst.indc ind ∈ ms.toList := List.mem_of_getElem? hms'
      rw [← Array.all_toList, List.all_eq_true] at d_all
      cases d_all _ hmem_ind
  exact ⟨hres_ok.1, cb, ms, hrec₀_own, hrecE_own, hcb_info, hwkSafe_own, hrk_lt, hres_ok.2⟩

/-- Inversion of `OwnedOrProjOf E a x c_x` at a non-role record `(a, c)` in `order`: `c` must be a
`.muts ms` block, and if `ms` consists solely of `.defn` members then `(x, c_x)` is the canonical
`.dPrj` projection record of some member `i < ms.size`. -/
private theorem ownedOrProjOf_inv
    (hSR : SafeRefsInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {seeds : List _root_.Address}
    {a x : _root_.Address} {c c_x : Ixon.Constant}
    (hbound : IxVM.Consistency.Bounded calls)
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ z lc, E₀.consts.get? z = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hord : IxVM.Consistency.UsedClosureOrderAt t
      (subEnvRole E₀ (fun z => z ∈ order_role ∨ WkSafe calls b.address t E₀ z)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role))
      (fun z => z ∈ seeds ∨ IxVM.Refinement.BindingSeeds t z) order)
    (ha_ord : a ∈ order)
    (ha_not_role : a ∉ order_role)
    (hrec₀ : Ix.Cert.recordAt E₀ a = some c)
    (hrecE : Ix.Cert.recordAt
      (subEnvRole E₀ (fun z => z ∈ order_role ∨ WkSafe calls b.address t E₀ z)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) a = some c)
    (hown_p : OwnedOrProjOf
      (subEnvRole E₀ (fun z => z ∈ order_role ∨ WkSafe calls b.address t E₀ z)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) a x c_x) :
    ∃ ms, c.info = .muts ms ∧
      (ms.all (fun | .defn _ => true | _ => false) = true →
        ∃ (i : Nat) (d_m : Ixon.Definition),
          i < ms.size ∧ i < UInt64.size ∧
          ms[i]? = some (.defn d_m) ∧
          x = Core.dprjAddr a i ∧
          c_x = ⟨.dPrj ⟨i.toUInt64, a⟩, #[], #[], #[], #[]⟩) := by
  let Keep := fun z => z ∈ order_role ∨ WkSafe calls b.address t E₀ z
  let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
  rcases hown_p with ⟨hrecE_x, hne_xa, hown_xa⟩ | ⟨cb, ms, i, hrecE_cb, hcb_info, hi_u64, hmem_p⟩
  · have hagree : ∀ z ∈ order_role, Ix.Cert.recordAt E z = Ix.Cert.recordAt E_role z := by
      intro z hz
      have h := (subEnvRole_agrees_on_role hadm hload hexact₀ hnoCol
        (Keep := Keep) (fun u hu => Or.inl hu) []).1 z hz
      rw [List.append_nil] at h
      exact h.1
    have hx_not_role : x ∉ order_role := by
      intro hx_role
      have hrec_role_x : Ix.Cert.recordAt E_role x = some c_x :=
        (hagree x hx_role).symm.trans hrecE_x
      have hreach_x := (hadm.closureOrder.complete x).mp hx_role
      have hreach_a : Ix.Cert.CompiledReachAt t E_role (IxVM.Refinement.BindingSeeds t) a :=
        .step hreach_x ⟨c_x, hrec_role_x, Or.inl ⟨hown_xa, hne_xa.symm⟩⟩
      exact ha_not_role ((hadm.closureOrder.complete a).mpr hreach_a)
    obtain ⟨hkeep_x, hrec₀_x⟩ : Keep x ∧ Ix.Cert.recordAt E₀ x = some c_x := by
      rcases recordAt_subEnv_some_inv E₀ Keep (roleSuppOf E_role order_role) hrecE_x with
        hkp | ⟨_, _, hm_supp⟩
      · exact hkp
      · exact absurd (mem_roleSuppOf_iff.mp hm_supp).1 hx_not_role
    have hwkSafe_x : WkSafe calls b.address t E₀ x := by
      rcases hkeep_x with hrole | hws
      · exact absurd hrole hx_not_role
      · exact hws
    obtain ⟨c_x', hrec₀_x', hchk_or⟩ := (wkAll_closedSubwalk calls b.address t E₀).checked x hwkSafe_x.1
    have hcx_eq : c_x' = c_x := Option.some.inj (hrec₀_x'.symm.trans hrec₀_x)
    subst c_x'
    have hproj_x : Ix.Cert.ownerOf x c_x ≠ x := by rw [hown_xa]; exact hne_xa.symm
    have hchk_x : Claim.CheckedAtFull calls b.address t x := by
      rcases hchk_or with ⟨ms', hmuts, _⟩ | hchk
      · simp [Ix.Cert.ownerOf, hmuts] at hproj_x
      · exact hchk
    obtain ⟨_, cb, ms, hrec₀_cb, _, hcb_info, _, _, hd_all⟩ :=
      walkedProjResolveOk hSR hbound hadm hload hexact₀ hnoCol hord
        (by rw [hown_xa]; exact ha_ord) hrec₀_x hwkSafe_x.1 hwkSafe_x.2 hproj_x hchk_x
    rw [hown_xa] at hrec₀_cb hd_all
    have hcb_eq : cb = c := Option.some.inj (hrec₀_cb.symm.trans hrec₀)
    subst cb
    exact ⟨ms, hcb_info, hd_all⟩
  · have hcb_eq : cb = c := Option.some.inj (hrecE_cb.symm.trans hrecE)
    subst cb
    refine ⟨ms, hcb_info, fun hall => ?_⟩
    rcases hmem_p with ⟨d_m, hms_i, rfl, rfl⟩ | ⟨ind, hms_i, _, _⟩ | ⟨ind, _, hms_i, _, _, _⟩
    · exact ⟨i, d_m, (Array.getElem?_eq_some_iff.mp hms_i).1, hi_u64, hms_i, rfl, rfl⟩
    · have hmem_ind : Ixon.MutConst.indc ind ∈ ms.toList :=
        List.mem_of_getElem? (by simpa using hms_i)
      rw [← Array.all_toList, List.all_eq_true] at hall
      cases hall _ hmem_ind
    · have hmem_ind : Ixon.MutConst.indc ind ∈ ms.toList :=
        List.mem_of_getElem? (by simpa using hms_i)
      rw [← Array.all_toList, List.all_eq_true] at hall
      cases hall _ hmem_ind

private def updateBlockHeights (bh : Std.HashMap Core.KKey Nat)
    (decl : Ix.Kernel.Declaration .anon) : Std.HashMap Core.KKey Nat :=
  match decl with
  | .defnDecl cv _ h => bh.insert cv.name (Ix.Kernel.Frontend.InModel.hintHeight h)
  | _ => bh

private theorem readRecordBare_muts_defn
    (cx : Ix.Kernel.Reader.Ctx .anon) (st : Ix.Kernel.Reader.State .anon)
    (owner : _root_.Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst)
    (defs : Array Ixon.Definition) (ord : Array Nat)
    (hinfo : c.info = .muts ms)
    (hany_indc : ms.any (fun | .indc _ => true | _ => false) = false)
    (hall_recr : ms.all (fun | .recr _ => true | _ => false) = false)
    (hall_defn : ms.all (fun | .defn _ => true | _ => false) = true)
    (hdefs : (ms.filterMap fun | .defn d => some d | _ => none) = defs)
    (hsafe : defs.findSome? Ix.Kernel.Reader.safetyDecline = none)
    (hord : Ix.Kernel.Reader.defOrder (defs.map (Ix.Kernel.Reader.recurDeps c)) = some ord) :
    ∃ f : Nat →
        Std.HashMap Core.KKey Nat × Array (Ix.Kernel.Declaration .anon) × Nat →
        Ix.Kernel.Reader.ReadM
          (ForInStep (Std.HashMap Core.KKey Nat × Array (Ix.Kernel.Declaration .anon) × Nat)),
      Ix.Kernel.Reader.readRecordBare cx st owner c =
        (forIn ord ({}, #[], 0) f >>= fun s' =>
          pure ({ decls := s'.2.1, projRewrites := s'.2.2 } : Ix.Kernel.Reader.Read .anon)) ∧
      (∀ (i : Nat)
        (s : Std.HashMap Core.KKey Nat × Array (Ix.Kernel.Declaration .anon) × Nat)
        (decl : Ix.Kernel.Declaration .anon),
        Ix.Kernel.Reader.readDefinition cx st (fun n => s.1.getD n (st.heights.getD n 0))
          (.member owner i) (List.range defs[i]!.lvls.toNat)
          (Ix.Kernel.Reader.MemberReader.mk' cx c id
            (fun j => if j < ms.size then some (cx.memberKey (.member owner j)) else none))
          defs[i]! = .ok (decl, false) →
        f i s = .ok (.yield (updateBlockHeights s.1 decl, s.2.1.push decl, s.2.2))) := by
  have hb : Ix.Kernel.Reader.readRecordBare cx st owner c =
      Ix.Kernel.Reader.readRecord cx st owner c := by
    unfold Ix.Kernel.Reader.readRecordBare
    rw [hinfo]
    dsimp only
    rw [hany_indc]
    rfl
  rw [hb]
  unfold Ix.Kernel.Reader.readRecord
  rw [hinfo]
  dsimp only
  rw [hany_indc, hall_recr, hall_defn]
  dsimp only [Bool.false_eq_true, ↓reduceIte]
  rw [hdefs, hsafe, hord]
  refine ⟨_, rfl, ?_⟩
  intro i s decl hrd
  dsimp only
  rw [hrd]
  cases decl <;> rfl

/-- Full `.muts ms` definition block (`ms.all (.defn) = true`) bare reading at `a ∉ order_role`:
`readRecordBare cx st a c` succeeds with `owners = []`, `blocks = []`, `generated = 0`,
`projRewrites = 0`, `CheckedConstOrigin` for every emitted declaration, distinct installed keys
`Core.keyOf t (Core.dprjAddr a k)` (`k < ms.size`), and `L1.RecordReadsAs` at every member. -/
private theorem checkedMutsDefn_block
    (hRP : RolePreludeInputs) (hSR : SafeRefsInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role st : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {seeds : List _root_.Address}
    {a : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hbound : IxVM.Consistency.Bounded calls)
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hba : Ix.Kernel.Admission.BindingAdmitted _root_.Address.admissionHash b t)
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hblobs₀ : ∀ bytes, Hashed calls bytes →
      E₀.blobs.get? (_root_.Address.blake3Pure bytes) = some bytes)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hnoInt_core : ¬ L1.EnvInternalCollision
      (coreEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role) pre))
    (hsub_rec : ∀ x c_x,
      Ix.Cert.recordAt (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) x = some c_x →
      Ix.Cert.recordAt (coreEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role) pre) x = some c_x)
    (hord : IxVM.Consistency.UsedClosureOrderAt t
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role))
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) order)
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.blobsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) order)
        (Ix.Cert.hintsOf
          (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
            (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)))).store)
    (hproj_emp : ∀ k : Core.KKey, st.projLevels[k]? = none)
    (ha_ord : a ∈ order)
    (ha_not_role : a ∉ order_role)
    (hrec₀ : Ix.Cert.recordAt E₀ a = some c)
    (hrecE : Ix.Cert.recordAt
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) a = some c)
    (hwk : WkAll calls b.address t E₀ a)
    (hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a)
    (hinfo : c.info = .muts ms)
    (hall : ms.all (fun | .defn _ => true | _ => false) = true)
    (hm_all : ∀ k < ms.size, Claim.MutsMemberCheckedAtFull calls b.address t a ms k) :
    let Keep := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x
    let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
    let E_core := coreEnvRole E₀ Keep (roleSuppOf E_role order_role)
      (Ix.Cert.blobsOf E_role order_role) pre
    let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
      (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
    ∃ r : Ix.Kernel.Reader.Read .anon,
      Ix.Kernel.Reader.readRecordBare cx st a c = .ok r ∧
      r.owners = [] ∧
      r.blocks = [] ∧
      (∀ d ∈ r.decls.toList,
        CheckedConstOrigin calls t b.address E_core order_role d ∧
        (∀ kb, d ≠ .basisDecl kb) ∧
        ∃ k < ms.size, ∃ d_m ci₀,
          ms[k]? = some (.defn d_m) ∧
          Core.dprjAddr a k ∉ order_role ∧
          d.names = [Core.keyOf t (Core.dprjAddr a k)] ∧
          IxVM.Consistency.installs d = [ci₀] ∧
          ci₀.name = Core.keyOf t (Core.dprjAddr a k)) ∧
      ((r.decls.toList.flatMap (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup) ∧
      (∀ k < ms.size,
        ∃ d ∈ r.decls.toList, ∃ ci₀,
          ci₀ ∈ IxVM.Consistency.installs d ∧
          ci₀.name = Core.keyOf t (Core.dprjAddr a k) ∧
          L1.RecordReadsAs t E_core (Core.dprjAddr a k)
            ⟨.dPrj ⟨k.toUInt64, a⟩, #[], #[], #[], #[]⟩ ci₀) := by
  intro Keep E E_core cx
  obtain ⟨ts, hts⟩ := list_all_defn_eq_map ms.toList (by rwa [← Array.all_toList] at hall)
  have hms_arr : ms = (ts.map Ixon.MutConst.defn).toArray := by
    apply Array.ext'
    simp [hts]
  cases ts with
  | nil =>
    have hms_emp : ms = #[] := by rw [hms_arr]; rfl
    have hread : Ix.Kernel.Reader.readRecordBare cx st a c = .ok {} := by
      unfold Ix.Kernel.Reader.readRecordBare Ix.Kernel.Reader.readRecord
      rw [hinfo, hms_emp]
      simp [pure, Except.pure]
    exact ⟨{}, hread, rfl, rfl, by simp, by simp, fun k hk => by rw [hms_emp] at hk; simp at hk⟩
  | cons d₀ ts' =>
    have hall_recr : ms.all (fun | .recr _ => true | _ => false) = false := by
      rw [hms_arr]; simp
    let ts := d₀ :: ts'
    change ms.toList = ts.map Ixon.MutConst.defn at hts
    change ms = (ts.map Ixon.MutConst.defn).toArray at hms_arr
    have hsz : ms.size = ts.length := by rw [hms_arr]; simp
    have hany_indc : ms.any (fun | .indc _ => true | _ => false) = false := by
      rw [hms_arr]; simp
    have hdefs : ms.filterMap (fun | .defn d => some d | _ => none) = ts.toArray := by
      apply Array.ext'
      rw [hms_arr]
      simp
    have hinLogic : IxVM.Consistency.InLogic c := by
      by_contra hnin
      exact hnot_out ⟨c, hrec₀, Or.inl hnin⟩
    have hsafe_ts : ∀ d_t ∈ ts, Ix.Kernel.Reader.safetyDecline d_t = none := by
      intro d_t hdt
      rw [IxVM.Consistency.InLogic, hinfo] at hinLogic
      exact hinLogic (.defn d_t) (by rw [hts]; exact List.mem_map.mpr ⟨d_t, hdt, rfl⟩)
    have hfind : ts.toArray.findSome? Ix.Kernel.Reader.safetyDecline = none :=
      Array.findSome?_eq_none_iff.mpr (fun d_t hdt => hsafe_ts d_t (by simpa using hdt))
    have hms_k : ∀ (k : Nat) (hk : k < ts.length), ms[k]? = some (.defn ts[k]) := by
      intro k hk
      have h1 : ms.toList[k]? = some (.defn ts[k]) := by
        rw [hts, List.getElem?_map, List.getElem?_eq_getElem hk]
        rfl
      simpa using h1
    have hempty_deps :
        ∀ k : Nat, k < (ts.toArray.map (Ix.Kernel.Reader.recurDeps c)).size →
          ((ts.toArray.map (Ix.Kernel.Reader.recurDeps c))[k]!).toList = [] := by
      intro k hk
      have hk_len : k < ts.length := by simpa using hk
      have hbang : (ts.toArray.map (Ix.Kernel.Reader.recurDeps c))[k]! =
          Ix.Kernel.Reader.recurDeps c ts[k] := by
        rw [getElem!_pos _ k hk]
        simp
      rw [hbang]
      exact (checkedMutsDefn_member hRP hSR (st := st) hbound hadm hba hcomm_extra hload hexact₀
        hblobs₀ hnoCol hnoInt_core hsub_rec hord hauth hproj_emp ha_ord ha_not_role hrec₀ hrecE
        hwk hnot_out hinfo (hms_k k hk_len) (hm_all k (by omega))).2.2.1
    have hdefOrd : Ix.Kernel.Reader.defOrder (ts.toArray.map (Ix.Kernel.Reader.recurDeps c)) =
        some (Array.range ts.length) := by
      have h0 := defOrder_all_empty (ts.toArray.map (Ix.Kernel.Reader.recurDeps c)) hempty_deps
      simpa using h0
    obtain ⟨F_step, hread_eq, hF_step⟩ :=
      readRecordBare_muts_defn cx st a c ms ts.toArray (Array.range ts.length)
        hinfo hany_indc hall_recr hall hdefs hfind hdefOrd
    let Inv : List Nat →
        Std.HashMap Core.KKey Nat × Array (Ix.Kernel.Declaration .anon) × Nat → Prop :=
      fun pre_idx s =>
        pre_idx = List.range s.2.1.size ∧
        s.2.2 = 0 ∧
        ∀ k < s.2.1.size,
          k < ts.length ∧
          ∃ (decl : Ix.Kernel.Declaration .anon) (ci₀ : Ix.Kernel.ConstantInfo .anon),
            s.2.1[k]? = some decl ∧
            CheckedConstOrigin calls t b.address E_core order_role decl ∧
            IxVM.Consistency.installs decl = [ci₀] ∧
            ci₀.name = Core.keyOf t (Core.dprjAddr a k) ∧
            decl.names = [Core.keyOf t (Core.dprjAddr a k)] ∧
            Core.dprjAddr a k ∉ order_role ∧
            (∀ kb, decl ≠ .basisDecl kb) ∧
            L1.RecordReadsAs t E_core (Core.dprjAddr a k)
              ⟨.dPrj ⟨k.toUInt64, a⟩, #[], #[], #[], #[]⟩ ci₀
    have hloop :
        ∃ res, forIn (Array.range ts.length) ({}, #[], 0) F_step = .ok res ∧
          Inv (Array.range ts.length).toList res := by
      refine forIn_complete_array Inv (Array.range ts.length) ({}, #[], 0)
        ⟨rfl, rfl, fun _ hk => by simp at hk⟩ ?_
      intro pre_idx i post_idx s hwhole ⟨hpre_eq, hrw0, hinv⟩
      rw [Array.toList_range] at hwhole
      have hlen_lt : s.2.1.size < ts.length := by
        have hlen := congrArg List.length hwhole
        rw [hpre_eq, List.length_append, List.length_range, List.length_cons,
          List.length_range] at hlen
        omega
      have hi_eq : i = s.2.1.size := by
        have hget := congrArg (fun l => l[s.2.1.size]?) hwhole
        have hpre_len : pre_idx.length = s.2.1.size := by rw [hpre_eq, List.length_range]
        rw [List.getElem?_append_right (by omega), hpre_len, Nat.sub_self,
          List.getElem?_range hlen_lt] at hget
        exact Option.some.inj hget
      subst i
      have hbang_i : ts.toArray[s.2.1.size]! = ts[s.2.1.size] := by
        rw [getElem!_pos ts.toArray s.2.1.size (by simp [hlen_lt])]
        simp
      obtain ⟨_, hd_not_role, _, hheights⟩ :=
        checkedMutsDefn_member hRP hSR (st := st) hbound hadm hba hcomm_extra hload hexact₀
          hblobs₀ hnoCol hnoInt_core hsub_rec hord hauth hproj_emp ha_ord ha_not_role hrec₀ hrecE
          hwk hnot_out hinfo (hms_k s.2.1.size hlen_lt) (hm_all s.2.1.size (by omega))
      obtain ⟨decl, ci₀, hrd_def, hcco, hinst, hname, hdnames, hnb, hrra⟩ :=
        hheights (fun n => s.1.getD n (st.heights.getD n 0))
      have hrd_def' :
          Ix.Kernel.Reader.readDefinition cx st (fun n => s.1.getD n (st.heights.getD n 0))
            (.member a s.2.1.size) (List.range ts.toArray[s.2.1.size]!.lvls.toNat)
            (Ix.Kernel.Reader.MemberReader.mk' cx c id
              (fun j => if j < ms.size then some (cx.memberKey (.member a j)) else none))
            ts.toArray[s.2.1.size]! = .ok (decl, false) := by
        rw [hbang_i]
        exact hrd_def
      have hf : F_step s.2.1.size s =
          .ok (.yield (updateBlockHeights s.1 decl, s.2.1.push decl, 0)) := by
        have h0 := hF_step s.2.1.size s decl hrd_def'
        rwa [hrw0] at h0
      refine ⟨_, hf, ?_, rfl, ?_⟩
      · rw [hpre_eq, Array.size_push, List.range_succ]
      · intro k hk_push
        rw [Array.size_push] at hk_push
        by_cases hk_lt : k < s.2.1.size
        · obtain ⟨hk_ts, decl_k, ci_k, hget_k, hrest_k⟩ := hinv k hk_lt
          refine ⟨hk_ts, decl_k, ci_k, ?_, hrest_k⟩
          rw [Array.getElem?_push]
          simp [Nat.ne_of_lt hk_lt, hget_k]
        · have hk_eq : k = s.2.1.size := by omega
          subst k
          refine ⟨hlen_lt, decl, ci₀, ?_, hcco, hinst, hname, hdnames, hd_not_role, hnb, hrra⟩
          rw [Array.getElem?_push]
          simp
    obtain ⟨res, hfor, hres_range, hres_rw, hres_inv⟩ := hloop
    rw [Array.toList_range] at hres_range
    have hres_sz : res.2.1.size = ts.length := by
      have hlen := congrArg List.length hres_range
      simpa using hlen.symm
    have hread : Ix.Kernel.Reader.readRecordBare cx st a c =
        .ok { decls := res.2.1, projRewrites := 0 } := by
      rw [hread_eq, hfor, hres_rw]
      rfl
    have hflat :
        res.2.1.toList.flatMap (fun d => (IxVM.Consistency.installs d).map (·.name)) =
          (List.range ms.size).map (fun k => Core.keyOf t (Core.dprjAddr a k)) := by
      have h0 := list_flatMap_of_getElem?_singleton
        (fun d => (IxVM.Consistency.installs d).map (·.name))
        (fun k => Core.keyOf t (Core.dprjAddr a k))
        res.2.1.toList
        (fun k hk => by
          have hk_sz : k < res.2.1.size := by simpa using hk
          obtain ⟨_, decl, ci₀, hget_k, _, hinst, hname, _⟩ := hres_inv k hk_sz
          exact ⟨decl, by simpa using hget_k, by rw [hinst, List.map_singleton, hname]⟩)
      rw [Array.length_toList, hres_sz, ← hsz] at h0
      exact h0
    have hnd_flat :
        (res.2.1.toList.flatMap (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup := by
      rw [hflat]
      refine nodup_map_of_inj_on List.nodup_range ?_
      intro i hi j hj hij
      rw [List.mem_range] at hi hj
      have hdprj_eq := keyOf_injective hba.wellFormed hij
      have hmi := hm_all i hi
      have hmj := hm_all j hj
      have hmsi := hms_k i (by omega)
      have hmsj := hms_k j (by omega)
      exact (dprjAddr_inj_of_mutsMemberChecked hbound hnoCol hmi hmsi hmj hmsj hdprj_eq).2
    refine ⟨{ decls := res.2.1, projRewrites := 0 }, hread, rfl, rfl, ?_, hnd_flat, ?_⟩
    · intro d hd_mem
      obtain ⟨k, hk_lt, hdk⟩ := List.mem_iff_getElem.mp hd_mem
      have hk_sz : k < res.2.1.size := by simpa using hk_lt
      obtain ⟨hk_ts, decl, ci₀, hget_k, hcco, hinst, hname, hdnames, hd_not_role, hnb, _⟩ :=
        hres_inv k hk_sz
      have hget_list : res.2.1.toList[k]? = some decl := by simpa using hget_k
      rw [List.getElem?_eq_getElem hk_lt] at hget_list
      injection hget_list with hdecl_eq
      rw [hdecl_eq] at hdk
      subst d
      exact ⟨hcco, hnb, k, by omega, ts[k], ci₀, hms_k k hk_ts,
        hd_not_role, hdnames, hinst, hname⟩
    · intro k hk
      have hk_sz : k < res.2.1.size := by omega
      obtain ⟨_, decl, ci₀, hget_k, _, hinst, hname, _, _, _, hrra⟩ := hres_inv k hk_sz
      have hd_mem : decl ∈ res.2.1.toList :=
        List.mem_of_getElem? (by simpa using hget_k)
      exact ⟨decl, hd_mem, ci₀, by rw [hinst]; exact List.mem_singleton_self _, hname, hrra⟩

/-! ## Section 6: Full role + walked `StreamReadBare` assembly (`walkedStreamReadBare`) -/

/-- Classification of keys installed by walked non-role declarations, used to prove pairwise
freshness across `order_w`. -/
private def WalkedKeyOrigin (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (order_role pre_w : List _root_.Address)
    (n : Core.KKey) : Prop :=
  (∃ a' ∈ pre_w, n = Core.keyOf t a' ∧
    ∃ c', Ix.Cert.recordAt E₀ a' = some c' ∧
      ((∃ ax, c'.info = .axio ax) ∨ (∃ df, c'.info = .defn df))) ∨
  (∃ a' ∈ pre_w, ∃ ms' i' d_m',
    n = Core.keyOf t (Core.dprjAddr a' i') ∧
    Claim.MutsMemberCheckedAtFull calls bAddr t a' ms' i' ∧
    ms'[i']? = some (.defn d_m')) ∨
  (∃ x', n = Core.keyOf t x' ∧
    x' ∉ order_role ∧
    (∀ c', Ix.Cert.recordAt E₀ x' = some c' →
      (∃ rc, c'.info = .recr rc) ∨ (∃ p, c'.info = .iPrj p) ∨
      (∃ p, c'.info = .cPrj p) ∨ (∃ p, c'.info = .rPrj p)) ∧
    (∀ owner ms (j : Nat) d_m,
      Claim.MutsMemberCheckedAtFull calls bAddr t owner ms j →
      ms[j]? = some (.defn d_m) →
      x' ≠ Core.dprjAddr owner j))

private theorem walkedKeyOrigin_mono {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {order_role pre₁ pre₂ : List _root_.Address}
    {n : Core.KKey}
    (hsub : ∀ z ∈ pre₁, z ∈ pre₂)
    (h : WalkedKeyOrigin calls bAddr t E₀ order_role pre₁ n) :
    WalkedKeyOrigin calls bAddr t E₀ order_role pre₂ n := by
  rcases h with ⟨a', ha', hrest⟩ | ⟨a', ha', hrest⟩ | h3
  · exact Or.inl ⟨a', hsub a' ha', hrest⟩
  · exact Or.inr (Or.inl ⟨a', hsub a' ha', hrest⟩)
  · exact Or.inr (Or.inr h3)

/-- Concrete per-declaration origin witness for a walked declaration `d` at prefix
`(ds_pre, env_pre)`. Bundles `CheckedConstOrigin ∨ CheckedIndOrigin`, the exact bare reader split
at `addr ∈ order`, `RecordReadsAs` + `StoredAs` in `env_pre` for every constant in or owned by the
already-read prefix `order_role ++ pre_w`, and prefix containment of all used references of
`const`. -/
inductive WalkedStepOrigin (calls : List (Call F)) (b : Ix.Kernel.Admission.Binding)
    (t : Ix.Kernel.RoleTable) (E₀ E E_core : Ixon.Env)
    (pre : Ix.Kernel.Reader.Prelude .anon) (order order_role : List _root_.Address)
    (ds_pre : List (Ix.Kernel.Declaration .anon))
    (env_pre : Ix.Kernel.Env .anon)
    (d : Ix.Kernel.Declaration .anon) : Prop where
  | mk
      (addr : _root_.Address)
      (const : Ixon.Constant)
      (pre_w : List _root_.Address)
      (suf_w : List _root_.Address)
      (st₀ : Ix.Kernel.Reader.State .anon)
      (prev_cDecls : Array (Ix.Kernel.Reader.CDecl .anon))
      (rd : Ix.Kernel.Reader.Read .anon)
      (r_before : List (Ix.Kernel.Declaration .anon))
      (r_after : List (Ix.Kernel.Declaration .anon))
      (order_split : order = (order_role ++ pre_w) ++ addr :: suf_w)
      (not_role : addr ∉ order_role)
      (rec₀ : Ix.Cert.recordAt E₀ addr = some const)
      (recE : Ix.Cert.recordAt E addr = some const)
      (wkSafe : WkSafe calls b.address t E₀ addr)
      (stream_pre :
        StreamReadBare
          (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
            (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
          pre.state (Ix.Cert.Stream.decodedOf E (order_role ++ pre_w)) st₀ prev_cDecls)
      (sameAt_pre : ∀ k ∈ pre.state.keys, st₀.SameAt pre.state k)
      (read_ok :
        Ix.Kernel.Reader.readRecordBare
          (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
            (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
          st₀ addr const = .ok rd)
      (decls_split : rd.decls.toList = r_before ++ d :: r_after)
      (ds_pre_split :
        ds_pre = (Ix.Kernel.Frontend.preparePrelude pre.ix prev_cDecls).toList ++ r_before)
      (prefix_readsAs :
        ∀ x c_x,
          ((x ∈ order_role ++ pre_w ∧ Ix.Cert.recordAt E x = some c_x ∧
              ((∃ d_x, c_x.info = .defn d_x) ∨ (∃ ax, c_x.info = .axio ax) ∨
                (∃ qt, c_x.info = .quot qt) ∨ (∃ rc, c_x.info = .recr rc) ∨
                Ix.Cert.ownerOf x c_x ≠ x)) ∨
            (∃ blk ∈ order_role ++ pre_w, OwnedOrProjOf E blk x c_x)) →
          ∃ ci₀,
            ci₀.name = Core.keyOf t x ∧
            L1.RecordReadsAs t E_core x c_x ci₀ ∧
            (IxVM.Consistency.inertKey (Core.keyOf t x) = false →
              ∃ ci, env_pre.find? (Core.keyOf t x) = some ci ∧
                IxVM.Consistency.StoredAs ci ci₀))
      (usedRef_in_prev :
        ∀ i ∈ IxVM.Consistency.usedRefIdxs const, ∀ r c_r,
          const.refs[i]? = some r →
          Ix.Cert.recordAt E r = some c_r →
          Ix.Cert.ownerOf r c_r ∈ order_role ++ pre_w)
      (origin :
        CheckedConstOrigin calls t b.address E_core order_role d ∨
        CheckedIndOrigin calls b t E₀ E pre order order_role d) :
      WalkedStepOrigin calls b t E₀ E E_core pre order order_role ds_pre env_pre d

theorem streamReadBare_append {md : Ix.Kernel.Mode} {cx : Ix.Kernel.Reader.Ctx md}
    {st₀ st₁ st₂ : Ix.Kernel.Reader.State md}
    {rs₁ rs₂ : List (_root_.Address × Ixon.Constant)}
    {out₁ out₂ : Array (Ix.Kernel.Reader.CDecl md)}
    (h₁ : StreamReadBare cx st₀ rs₁ st₁ out₁)
    (h₂ : StreamReadBare cx st₁ rs₂ st₂ out₂) :
    StreamReadBare cx st₀ (rs₁ ++ rs₂) st₂ (out₁ ++ out₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | @cons _ _ _ _ r _ _ read _ ih =>
    rw [List.cons_append, Array.append_assoc]
    exact .cons read (ih h₂)

private theorem decodedOf_append (E : Ixon.Env) (l₁ l₂ : List _root_.Address) :
    Ix.Cert.Stream.decodedOf E (l₁ ++ l₂) =
      Ix.Cert.Stream.decodedOf E l₁ ++ Ix.Cert.Stream.decodedOf E l₂ := by
  unfold Ix.Cert.Stream.decodedOf
  exact List.filterMap_append

private theorem decodedOf_cons_of_recordAt {E : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    (rest : List _root_.Address) (hrec : Ix.Cert.recordAt E a = some c) :
    Ix.Cert.Stream.decodedOf E (a :: rest) = (a, c) :: Ix.Cert.Stream.decodedOf E rest := by
  rw [Ix.Cert.Stream.decodedOf_cons, hrec]
  rfl

private theorem pairwise_eq_filter_append {α : Type} (p₁ p₂ : α → Bool) (rk : α → Nat)
    (hcomp : ∀ x, p₂ x = !p₁ x)
    (hsep : ∀ x y, p₁ x = false → p₁ y = true → rk y < rk x) :
    ∀ (xs : List α), xs.Pairwise (fun x y => rk x ≤ rk y) →
      xs = xs.filter p₁ ++ xs.filter p₂
  | [], _ => rfl
  | x :: tl, hpw => by
    rw [List.pairwise_cons] at hpw
    have hp₂x := hcomp x
    cases hp₁x : p₁ x with
    | true =>
      rw [hp₁x] at hp₂x
      simp only [List.filter_cons_of_pos hp₁x, Bool.not_true, hp₂x, Bool.false_eq_true,
        not_false_eq_true, List.filter_cons_of_neg, List.cons_append]
      exact congrArg (x :: ·) (pairwise_eq_filter_append p₁ p₂ rk hcomp hsep tl hpw.2)
    | false =>
      have hall_false : ∀ y ∈ tl, p₁ y = false := by
        intro y hy
        cases hp₁y : p₁ y with
        | false => rfl
        | true =>
          have hle := hpw.1 y hy
          have hlt := hsep x y hp₁x hp₁y
          omega
      have hfil₁ : tl.filter p₁ = [] := List.filter_eq_nil_iff.mpr (by
        intro y hy; rw [hall_false y hy]; decide)
      have hfil₂ : tl.filter p₂ = tl := List.filter_eq_self.mpr (by
        intro y hy; rw [hcomp y, hall_false y hy]; rfl)
      rw [hp₁x] at hp₂x
      simp [hp₁x, hp₂x, hfil₁, hfil₂]

private theorem pairwise_of_idxOf_lt {α : Type} [DecidableEq α] {R : α → α → Prop} :
    ∀ {xs : List α} {a b : α},
      xs.Pairwise R → a ∈ xs → b ∈ xs → xs.idxOf a < xs.idxOf b → R a b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: tl, a, b, hpw, ha, hb, hlt => by
    rw [List.pairwise_cons] at hpw
    by_cases hbx : b = x
    · subst b
      rw [List.idxOf_cons_self] at hlt
      omega
    · have hb_tl : b ∈ tl := by
        rcases List.mem_cons.mp hb with rfl | htl
        · exact absurd rfl hbx
        · exact htl
      by_cases hax : a = x
      · subst a
        exact hpw.1 b hb_tl
      · have ha_tl : a ∈ tl := by
          rcases List.mem_cons.mp ha with rfl | htl
          · exact absurd rfl hax
          · exact htl
        rw [List.idxOf_cons_ne _ (Ne.symm hax), List.idxOf_cons_ne _ (Ne.symm hbx)] at hlt
        exact pairwise_of_idxOf_lt hpw.2 ha_tl hb_tl (by omega)

/-- Every used reference `r` of a walked non-role record `(a, c)` at `order = prev ++ a :: suf`
has its owner `ownerOf r c_r` strictly in `prev`. -/
private theorem usedRef_mem_prev_of_nonRole
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order order_role prev suf : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    {seeds : List _root_.Address}
    {a : _root_.Address} {c : Ixon.Constant}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c')
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hord : IxVM.Consistency.UsedClosureOrderAt t
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role))
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) order)
    (hsplit : order = prev ++ a :: suf)
    (ha_not_role : a ∉ order_role)
    (hrec₀ : Ix.Cert.recordAt E₀ a = some c)
    (hrecE : Ix.Cert.recordAt
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) a = some c)
    (hwk : WkAll calls b.address t E₀ a)
    {i : Nat} {r : _root_.Address} {c_r : Ixon.Constant}
    (hi : i ∈ IxVM.Consistency.usedRefIdxs c)
    (hr : c.refs[i]? = some r)
    (hrecE_r : Ix.Cert.recordAt
      (subEnvRole E₀ (fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x)
        (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)) r = some c_r) :
    Ix.Cert.ownerOf r c_r ∈ prev := by
  let Keep := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x
  let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role) (Ix.Cert.blobsOf E_role order_role)
  let blk := Ix.Cert.ownerOf r c_r
  have hi_s0 : i ∈ Core.S0.usedRefIdxs c := by rwa [usedRefIdxs_eq]
  have hedge_ar : Core.S0.WalkEdge E₀ a r := ⟨c, hrec₀, Or.inr ⟨i, hi_s0, hr⟩⟩
  obtain ⟨hwk_r, hlt_ra⟩ := (wkAll_closedSubwalk calls b.address t E₀).step a r hwk hedge_ar
  have hblk_ne_a : blk ≠ a := by
    intro heq
    by_cases hr_eq_a : r = a
    · subst r
      exact Nat.lt_irrefl _ hlt_ra
    · by_cases hr_role : r ∈ order_role
      · have hagree := (subEnvRole_agrees_on_role hadm hload hexact₀ hnoCol
          (Keep := Keep) (fun u hu => Or.inl hu) []).1 r hr_role
        rw [List.append_nil] at hagree
        have hrec_role_r : Ix.Cert.recordAt E_role r = some c_r := hagree.1.symm.trans hrecE_r
        have hreach_r := (hadm.closureOrder.complete r).mp hr_role
        have hreach_a : Ix.Cert.CompiledReachAt t E_role (IxVM.Refinement.BindingSeeds t) a :=
          .step hreach_r ⟨c_r, hrec_role_r, Or.inl ⟨heq, hr_eq_a.symm⟩⟩
        exact ha_not_role ((hadm.closureOrder.complete a).mpr hreach_a)
      · have hrec₀_r : Ix.Cert.recordAt E₀ r = some c_r := by
          rcases recordAt_subEnv_some_inv E₀ Keep (roleSuppOf E_role order_role) hrecE_r with
            hkp | ⟨_, _, hm_supp⟩
          · exact hkp.2
          · exact absurd (mem_roleSuppOf_iff.mp hm_supp).1 hr_role
        have hedge_ra : Core.S0.WalkEdge E₀ r a := ⟨c_r, hrec₀_r, Or.inl ⟨heq, hr_eq_a.symm⟩⟩
        obtain ⟨_, hlt_ar⟩ := (wkAll_closedSubwalk calls b.address t E₀).step r a hwk_r hedge_ra
        exact Nat.lt_asymm hlt_ra hlt_ar
  have href_blk : IxVM.Consistency.UsedRecordRef E a blk :=
    ⟨c, hrecE, i, hi, r, hr, c_r, hrecE_r, rfl, hblk_ne_a⟩
  have ha_ord : a ∈ order := by rw [hsplit]; simp
  have hreach_a := (hord.complete a).mp ha_ord
  have hreach_r : IxVM.Consistency.UsedCompiledReachAt t E
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) r :=
    .step hreach_a ⟨c, hrecE, Or.inr ⟨⟨i, hi, hr⟩, contains_of_recordAt hrecE_r⟩⟩
  have hreach_blk : IxVM.Consistency.UsedCompiledReachAt t E
      (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) blk := by
    by_cases hbr : blk = r
    · rwa [hbr]
    · exact .step hreach_r ⟨c_r, hrecE_r, Or.inl ⟨rfl, hbr⟩⟩
  have hblk_ord : blk ∈ order := (hord.complete blk).mpr hreach_blk
  rw [hsplit] at hblk_ord
  rcases List.mem_append.mp hblk_ord with hprev | htail
  · exact hprev
  · rcases List.mem_cons.mp htail with rfl | hsuf
    · exact absurd rfl hblk_ne_a
    · have hpw := hord.ordered
      rw [hsplit, List.pairwise_append] at hpw
      rw [List.pairwise_cons] at hpw
      exact absurd href_blk (hpw.2.1.1 blk hsuf)

/-- **Full role + walked `StreamReadBare` assembly**: combines `RolePreludeInputs`,
`SafeRefsInputs`, `TableAdmittedComplete V b`, and `Claim.WalkedL6` into `DrawsRoleLocal`,
`UsedClosureOrderAt`, `StreamReadBare`, `keepsPrelude`, per-declaration role/walked origin
witnesses, and seed coverage. -/
theorem walkedStreamReadBare
    (hRP : RolePreludeInputs) (hSR : SafeRefsInputs)
    {calls : List (Call F)} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {seeds : List _root_.Address}
    {V : IxVM.Refinement.View} {extra : List ByteArray}
    (hbound : IxVM.Consistency.Bounded calls)
    (hadmV : TableAdmittedComplete V b)
    (hadm_b : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hseedOk : ∀ a ∈ seeds, ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a)
    (hwalk : Claim.WalkedL6 calls t E₀ seeds)
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hnoCol : ¬ V.HashedCollision extra calls) :
    ∃ (E E_role E_core : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
      (order order_role : List _root_.Address) (envA : Ix.Kernel.Env .anon)
      (pre : Ix.Kernel.Reader.Prelude .anon)
      (st_role st' : Ix.Kernel.Reader.State .anon)
      (decls_role decls : Array (Ix.Kernel.Reader.CDecl .anon)),
      TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role ∧
      DrawsRoleLocal E E₀ V.env ∧
      IxVM.Consistency.UsedClosureOrderAt t E
        (fun a => a ∈ seeds ∨ IxVM.Refinement.BindingSeeds t a) order ∧
      Ix.Kernel.Reader.preludeFor t = .ok pre ∧
      (∀ a lc, E.consts.get? a = some lc → _root_.Address.blake3Pure lc.rawBytes = a) ∧
      (∀ a bytes, E.blobs.get? a = some bytes → _root_.Address.blake3Pure bytes = a) ∧
      (∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
        ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c) ∧
      L1.EnvDecoded E_core ∧
      ¬ L1.EnvInternalCollision E_core ∧
      (∀ env_pre : Ix.Kernel.Env .anon, Core.Good ⟨E_core, env_pre, t, none⟩ calls) ∧
      (∀ x c_x, Ix.Cert.recordAt E x = some c_x → Ix.Cert.recordAt E_core x = some c_x) ∧
      (∀ a c_f, (a, c_f) ∈ pre.records ++ pre.evidence → Ix.Cert.recordAt E_core a = some c_f) ∧
      E_core.blobs = E.blobs ∧
      StreamReadBare
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        pre.state (Ix.Cert.Stream.decodedOf E order) st' decls ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true ∧
      ((Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList.flatMap
        (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup ∧
      (∀ ds_pre d ds_suf env_pre,
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList = ds_pre ++ d :: ds_suf →
        IxVM.Consistency.Installs ds_pre env_pre →
        (∃ ds_role_suf,
          (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList =
            ds_pre ++ d :: ds_role_suf) ∨
        WalkedStepOrigin calls b t E₀ E E_core pre order order_role ds_pre env_pre d) ∧
      (∀ a ∈ seeds,
        IxVM.Consistency.IsBlockAt E₀ a ∨
        ∃ (k : Ix.Kernel.Key .anon) (d : Ix.Kernel.Declaration .anon)
          (ci₀ : Ix.Kernel.ConstantInfo .anon),
          IxVM.Refinement.AddressKey b a k ∧ ci₀.name = k ∧
          d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList ∧
          ci₀ ∈ IxVM.Consistency.installs d) := by
  obtain ⟨t', E_role, limits, order_role, envA, pre, st_role, decls_role, hadm⟩ := hadmV
  have ht_eq : t' = t := Except.ok.inj (hadm.admitBinding.symm.trans hadm_b)
  subst t'
  have hba := (Ix.Kernel.Admission.admitBinding_ok_iff _root_.Address.admissionHash b t).mp hadm_b
  have hwalk_orig := hwalk
  obtain ⟨bAddr, ⟨rb, _, rfl, hadm_rb⟩, _, hexact₀_full, hblobs₀, _, Wk, rank,
    hwk_seeds, hwk_step, hwk_chk⟩ := hwalk
  have hexact₀ : ∀ x lc, E₀.consts.get? x = some lc →
      ∃ c', lc.get? = some c' ∧ Ixon.deConstantExact lc.rawBytes = .ok c' :=
    fun x lc h => let ⟨_, c', h1, _, h3⟩ := hexact₀_full x lc h; ⟨c', h1, h3⟩
  have hba_rb := (Ix.Kernel.Admission.admitBinding_ok_iff _root_.Address.admissionHash _ t).mp hadm_rb
  have hbAddr_eq : rb.address = b.address :=
    hba_rb.authentic.symm.trans (by rw [hba_rb.canonical.2.symm.trans hba.canonical.2]; exact hba.authentic)
  rw [hbAddr_eq] at hwk_chk
  have hcsw_wk : ClosedSubwalk calls b.address t E₀ Wk rank :=
    closedSubwalk_of_walked hwk_step hwk_chk
  have hwkSafe_seeds : ∀ a ∈ seeds, WkSafe calls b.address t E₀ a :=
    fun a ha => ⟨wkAll_of_closedSubwalk hcsw_wk (hwk_seeds a ha), (hseedOk a ha).1⟩
  let Keep : _root_.Address → Prop := fun x => x ∈ order_role ∨ WkSafe calls b.address t E₀ x
  let supp : List SuppEntry := roleSuppOf E_role order_role
  let roleBlobs : List (_root_.Address × ByteArray) := Ix.Cert.blobsOf E_role order_role
  let E : Ixon.Env := subEnvRole E₀ Keep supp roleBlobs
  let E_core : Ixon.Env := coreEnvRole E₀ Keep supp roleBlobs pre
  let S : _root_.Address → Prop := fun a => a ∈ seeds ∨ IxVM.Refinement.BindingSeeds t a
  let rk : _root_.Address → Nat :=
    roleTwoTierRank order_role (WkSafe calls b.address t E₀) (rankAll calls b.address t E₀) id
  let order : List _root_.Address := closureOrderByRank t E S rk
  let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
    (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)
  have hsupp_spec : ∀ a raw c, (a, raw, c) ∈ supp →
      a ∈ order_role ∧ _root_.Address.blake3Pure raw = a ∧
      Ixon.deConstantExact raw = .ok c ∧ V.Preimage a raw ∧
      ∃ lcV, V.env.consts.get? a = some lcV ∧ lcV.rawBytes = raw := by
    intro a raw c hm
    obtain ⟨ha, lc_r, hget_r, hrec_r, rfl⟩ := mem_roleSuppOf_iff.mp hm
    obtain ⟨lc_r', c_r, hget_r', hlc_r', _, hblk_r, _, _, hex_r, hpreV⟩ := hadm.order_record_spec ha
    rw [hget_r] at hget_r'; injection hget_r' with hlceq; subst lc_r'
    unfold Ix.Cert.recordAt at hrec_r
    rw [hget_r] at hrec_r
    dsimp only [bind, Option.bind] at hrec_r
    rw [hlc_r'] at hrec_r
    injection hrec_r with hceq; subst c_r
    obtain ⟨⟨lcV, hgetV, hrawV⟩, _⟩ := hadm.viewConsts a ha lc_r hget_r
    exact ⟨ha, hblk_r, hex_r, hpreV, lcV, hgetV, hrawV⟩
  have hdraws : DrawsRoleLocal E E₀ V.env :=
    subEnvRole_drawsRoleLocal Keep supp roleBlobs
      (fun a raw c hm => Or.inl (hsupp_spec a raw c hm).2.2.2.2)
      (fun a bytes hm => (hadm.blobs_spec.2 a bytes hm).2.2.1)
  have hsub_auth := subEnvRole_authentic_exact (Keep := Keep) hload hexact₀
    (fun a raw c hm => ⟨(hsupp_spec a raw c hm).2.1, (hsupp_spec a raw c hm).2.2.1⟩)
    (fun a bytes hm => (hadm.blobs_spec.2 a bytes hm).1)
  have hord : IxVM.Consistency.UsedClosureOrderAt t E S order := by
    refine subEnvRole_usedClosureOrderAt hadm hload hexact₀ hnoCol Keep S id
      (fun a ha => Or.inl ha)
      (fun x hwx => Or.inr hwx)
      (fun x c hwx hrec₀ hne => ?_)
      (fun x y hwx hedge hy_nr hkeep_y => ?_)
      (fun x hwx => ?_)
      (fun x c hx_nr hnwx hrecE => ?_)
      (fun a c ha_nr hnwa hrecE _ _ _ _ _ _ _ _ _ => ?_)
    · obtain ⟨_, _, _, _, hws, hlt⟩ :=
        wkSafe_owner_of_proj hbound hload hexact₀ hnoCol hwx hrec₀ hne
      exact ⟨hws, hlt⟩
    · have hwy : WkSafe calls b.address t E₀ y := by
        rcases hkeep_y with hr | hw
        · exact absurd hr hy_nr
        · exact hw
      exact ⟨hwy, ((wkAll_closedSubwalk calls b.address t E₀).step x y hwx.1 hedge).2⟩
    · obtain ⟨c, hrec, _⟩ := (wkAll_closedSubwalk calls b.address t E₀).checked x hwx.1
      exact ⟨c, hrec⟩
    · rcases recordAt_subEnv_some_inv E₀ Keep supp hrecE with ⟨hkp, _⟩ | ⟨_, _, hm⟩
      · rcases hkp with hr | hw
        · exact absurd hr hx_nr
        · exact absurd hw hnwx
      · exact absurd (hsupp_spec x _ c hm).1 hx_nr
    · rcases recordAt_subEnv_some_inv E₀ Keep supp hrecE with ⟨hkp, _⟩ | ⟨_, _, hm⟩
      · rcases hkp with hr | hw
        · exact absurd hr ha_nr
        · exact absurd hw hnwa
      · exact absurd (hsupp_spec a _ c hm).1 ha_nr
  have hsorted : order.Pairwise (fun x y => rk x ≤ rk y) := by
    have hms := List.pairwise_mergeSort (le := fun a b => decide (rk a ≤ rk b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (closureReachKeys t E S)
    exact hms.imp (by intro x y h; exact of_decide_eq_true h)
  have hord_filter : order = order.filter (· ∈ order_role) ++ order.filter (· ∉ order_role) := by
    refine pairwise_eq_filter_append (· ∈ order_role) (· ∉ order_role) rk
      (fun x => by by_cases hx : x ∈ order_role <;> simp [hx])
      (fun x y hx hy => ?_) order hsorted
    have hx' : x ∉ order_role := by simpa using hx
    have hy' : y ∈ order_role := by simpa using hy
    have hlt_len : order_role.idxOf y < order_role.length := List.idxOf_lt_length_iff.mpr hy'
    simp only [rk, roleTwoTierRank, hx', hy', ↓reduceIte]
    omega
  have hord_idxOf : ∀ a b', a ∈ order.filter (· ∈ order_role) →
      b' ∈ order.filter (· ∈ order_role) →
      order.idxOf a < order.idxOf b' → order_role.idxOf a < order_role.idxOf b' := by
    intro a b' ha hb' hlt
    obtain ⟨ha_ord, ha_role⟩ := List.mem_filter.mp ha
    obtain ⟨hb_ord, hb_role⟩ := List.mem_filter.mp hb'
    have ha_r : a ∈ order_role := of_decide_eq_true ha_role
    have hb_r : b' ∈ order_role := of_decide_eq_true hb_role
    have hne : a ≠ b' := fun heq => by subst heq; exact Nat.lt_irrefl _ hlt
    have hrk_le : rk a ≤ rk b' :=
      pairwise_of_idxOf_lt (R := fun x y => rk x ≤ rk y) hsorted ha_ord hb_ord hlt
    simp only [rk, roleTwoTierRank, ha_r, hb_r, ↓reduceIte] at hrk_le
    have hidx_ne : order_role.idxOf a ≠ order_role.idxOf b' := by
      intro heq_i
      have hga : order_role[order_role.idxOf a]? = some a :=
        List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr ha_r) |>.trans
          (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr ha_r)))
      have hgb : order_role[order_role.idxOf b']? = some b' :=
        List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hb_r) |>.trans
          (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hb_r)))
      rw [heq_i, hgb] at hga
      exact hne (Option.some.inj hga).symm
    omega
  have hdec_core : L1.EnvDecoded E_core :=
    coreEnvRole_envDecoded hRP hwalk_orig hadm.preludeFor
      (fun a raw c hm => (hsupp_spec a raw c hm).2.2.1)
  have hnoInt_core : ¬ L1.EnvInternalCollision E_core :=
    coreEnvRole_not_internalCollision hRP hadm hcomm_extra hload hnoCol
  have hgood_core : ∀ env_pre : Ix.Kernel.Env .anon, Core.Good ⟨E_core, env_pre, t, none⟩ calls :=
    fun env_pre => coreEnvRole_good hRP env_pre none hcomm_extra hload hadm.preludeFor
      (fun a raw c hm => ⟨(hsupp_spec a raw c hm).2.1, Or.inl (hsupp_spec a raw c hm).2.2.2.1⟩)
      (fun a bytes hm => (hadm.blobs_spec.2 a bytes hm).2.2.2)
      hnoCol hbound
  have hsub_rec : ∀ x c_x, Ix.Cert.recordAt E x = some c_x →
      Ix.Cert.recordAt E_core x = some c_x :=
    fun _ _ hrec => recordAt_coreEnvRole_of_subEnvRole (roleSuppOf_nodup hadm.closureOrder.nodup) hrec
  have hfb_rec : ∀ a c_f, (a, c_f) ∈ pre.records ++ pre.evidence →
      Ix.Cert.recordAt E_core a = some c_f := by
    intro a c_f hmem
    refine recordAt_coreEnvRole_of_fallback hRP hcomm_extra hload hexact₀ hnoCol hadm.preludeFor
      (fun x raw c' c₀ hm hmem' => ?_) hmem
    obtain ⟨hx_role, lc_r, hget_r, hrec_r, _⟩ := mem_roleSuppOf_iff.mp hm
    have hrec_role := hadm.order_agrees_with_fallback hRP hx_role hmem'
    exact Option.some.inj (hrec_r.symm.trans hrec_role)
  have hagree_pair := subEnvRole_agrees_on_role hadm hload hexact₀ hnoCol
    (Keep := Keep) (fun a ha => Or.inl ha) []
  rw [List.append_nil] at hagree_pair
  have hauth_cx : AuthenticExactStore cx.store :=
    streamContext_authenticExactStore hRP hadm.preludeFor
      (fun a lc hget => (hsub_auth.1 a lc hget).1)
      (fun a _ lc hget => (hsub_auth.1 a lc hget).2)
  obtain ⟨hfilt_role, hprep_split, hnd_role, hrole_names,
    st_r, hsr_role, hsame_role, hrole_rra⟩ :=
    hSR.rolePrefixStreamReadBare hadm hbound hload hnoCol hdec_core hnoInt_core
      hsub_rec (fun _ _ hb => hb) hagree_pair.1 hagree_pair.2 hord hord_filter hord_idxOf hauth_cx
  let order_w := order.filter (· ∉ order_role)
  have hord_split : order = order_role ++ order_w := by
    rw [← hfilt_role]
    exact hord_filter
  have hord_w_nodup : order_w.Nodup := by
    have hnd := hord.nodup
    rw [hord_split, List.nodup_append] at hnd
    exact hnd.2.1
  have hnonRole_mem : ∀ a' ∈ order_w,
      ∃ c', Ix.Cert.recordAt E a' = some c' ∧
        Ix.Cert.recordAt E₀ a' = some c' ∧
        WkSafe calls b.address t E₀ a' := by
    intro a' ha'_w
    obtain ⟨ha'_ord, ha'_nr_b⟩ := List.mem_filter.mp ha'_w
    have ha'_nr : a' ∉ order_role := of_decide_eq_true ha'_nr_b
    have hcont : E.consts.contains a' = true :=
      usedCompiledReachAt_contains
        (fun x c_x hrec => by
          by_cases hx_r : x ∈ order_role
          · have hrec_r : Ix.Cert.recordAt E_role x = some c_x :=
              (hagree_pair.1 x hx_r).1.symm.trans hrec
            by_cases ho : Ix.Cert.ownerOf x c_x = x
            · rw [ho]; exact (hagree_pair.1 x hx_r).2
            · exact (hagree_pair.1 _ ((hadm.closureOrder.complete _).mpr
                (.step ((hadm.closureOrder.complete x).mp hx_r) ⟨c_x, hrec_r, Or.inl ⟨rfl, ho⟩⟩))).2
          · rcases recordAt_subEnv_some_inv E₀ Keep supp hrec with ⟨hkp, hrec₀⟩ | ⟨_, _, hm⟩
            · rcases hkp with hr | hws
              · exact absurd hr hx_r
              · by_cases ho : Ix.Cert.ownerOf x c_x = x
                · rw [ho]; exact contains_of_recordAt hrec
                · obtain ⟨cb, _, hrec₀_cb, _, hws_cb, _⟩ :=
                    wkSafe_owner_of_proj hbound hload hexact₀ hnoCol hws hrec₀ ho
                  exact contains_of_recordAt (recordAt_subEnv_of_keep E₀ Keep supp (Or.inr hws_cb) hrec₀_cb)
            · exact absurd (hsupp_spec x _ c_x hm).1 hx_r)
        ((hord.complete a').mp ha'_ord)
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?] at hcont
    obtain ⟨lcE, hgetE⟩ := Option.isSome_iff_exists.mp hcont
    obtain ⟨_, c', hlc_c', _⟩ := hsub_auth.1 a' lcE hgetE
    have hrecE : Ix.Cert.recordAt E a' = some c' := by unfold Ix.Cert.recordAt; rw [hgetE]; exact hlc_c'
    rcases recordAt_subEnv_some_inv E₀ Keep supp hrecE with ⟨hkp, hrec₀⟩ | ⟨_, _, hm⟩
    · rcases hkp with hr | hws
      · exact absurd hr ha'_nr
      · exact ⟨c', hrecE, hrec₀, hws⟩
    · exact absurd (hsupp_spec a' _ c' hm).1 ha'_nr
  have hdec_nonRole_all : ∀ a' c', (a', c') ∈ Ix.Cert.Stream.decodedOf E order → a' ∉ order_role →
      Ix.Cert.recordAt E₀ a' = some c' ∧
      WkAll calls b.address t E₀ a' ∧
      ¬ IxVM.Consistency.OutsideLogicAt E₀ a' := by
    intro a' c' hmem_dec ha'_nr
    obtain ⟨ha'_ord, hrecE'⟩ := mem_decodedOf hmem_dec
    have ha'_w : a' ∈ order_w := List.mem_filter.mpr ⟨ha'_ord, decide_eq_true ha'_nr⟩
    obtain ⟨c'', hrecE'', hrec₀'', hws⟩ := hnonRole_mem a' ha'_w
    have hceq : c'' = c' := Option.some.inj (hrecE''.symm.trans hrecE')
    subst c''
    exact ⟨hrec₀'', hws.1, hws.2⟩
  let ds_role := (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList
  have hstep_loop :
      ∀ (suf_w pre_w : List _root_.Address)
        (st : Ix.Kernel.Reader.State .anon)
        (decls_w : Array (Ix.Kernel.Declaration .anon)),
        pre_w ++ suf_w = order_w →
        StreamReadBare cx st_r (Ix.Cert.Stream.decodedOf E pre_w) st decls_w →
        (∀ k ∈ pre.state.keys, st.SameAt pre.state k) →
        (∀ d ∈ decls_w.toList, ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role) →
        (∀ d ∈ decls_w.toList, ∀ ci₀ ∈ IxVM.Consistency.installs d,
          WalkedKeyOrigin calls b.address t E₀ order_role pre_w ci₀.name) →
        (((ds_role ++ decls_w.toList).flatMap
          (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup) →
        (∀ x c_x,
          ((x ∈ order_role ++ pre_w ∧ Ix.Cert.recordAt E x = some c_x ∧
              ((∃ d_x, c_x.info = .defn d_x) ∨ (∃ ax, c_x.info = .axio ax) ∨
                (∃ qt, c_x.info = .quot qt) ∨ (∃ rc, c_x.info = .recr rc) ∨
                Ix.Cert.ownerOf x c_x ≠ x)) ∨
            (∃ blk ∈ order_role ++ pre_w, OwnedOrProjOf E blk x c_x)) →
          ∃ ci₀,
            ci₀.name = Core.keyOf t x ∧
            L1.RecordReadsAs t E_core x c_x ci₀ ∧
            (IxVM.Consistency.inertKey (Core.keyOf t x) = false →
              ∃ d ∈ ds_role ++ decls_w.toList, ci₀ ∈ IxVM.Consistency.installs d)) →
        (∀ ds_pre d ds_suf env_pre,
          ds_role ++ decls_w.toList = ds_pre ++ d :: ds_suf →
          IxVM.Consistency.Installs ds_pre env_pre →
          (∃ ds_role_suf, ds_role = ds_pre ++ d :: ds_role_suf) ∨
          WalkedStepOrigin calls b t E₀ E E_core pre order order_role ds_pre env_pre d) →
        ∃ st' decls_w_final,
          StreamReadBare cx st_r (Ix.Cert.Stream.decodedOf E order_w) st' decls_w_final ∧
          (∀ k ∈ pre.state.keys, st'.SameAt pre.state k) ∧
          (∀ d ∈ decls_w_final.toList, ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role) ∧
          (((ds_role ++ decls_w_final.toList).flatMap
            (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup) ∧
          (∀ x c_x,
            ((x ∈ order ∧ Ix.Cert.recordAt E x = some c_x ∧
                ((∃ d_x, c_x.info = .defn d_x) ∨ (∃ ax, c_x.info = .axio ax) ∨
                  (∃ qt, c_x.info = .quot qt) ∨ (∃ rc, c_x.info = .recr rc) ∨
                  Ix.Cert.ownerOf x c_x ≠ x)) ∨
              (∃ blk ∈ order, OwnedOrProjOf E blk x c_x)) →
            ∃ ci₀,
              ci₀.name = Core.keyOf t x ∧
              L1.RecordReadsAs t E_core x c_x ci₀ ∧
              (IxVM.Consistency.inertKey (Core.keyOf t x) = false →
                ∃ d ∈ ds_role ++ decls_w_final.toList, ci₀ ∈ IxVM.Consistency.installs d)) ∧
          (∀ ds_pre d ds_suf env_pre,
            ds_role ++ decls_w_final.toList = ds_pre ++ d :: ds_suf →
            IxVM.Consistency.Installs ds_pre env_pre →
            (∃ ds_role_suf, ds_role = ds_pre ++ d :: ds_role_suf) ∨
            WalkedStepOrigin calls b t E₀ E E_core pre order order_role ds_pre env_pre d) := by
    intro suf_w
    induction suf_w with
    | nil =>
      intro pre_w st decls_w hwhole hsr hsame hnames _ hnd hpref horig
      rw [List.append_nil] at hwhole
      subst pre_w
      refine ⟨st, decls_w, hsr, hsame, hnames, hnd, ?_, horig⟩
      intro x c_x hx
      rw [← hord_split] at hpref
      exact hpref x c_x hx
    | cons a suf_w' ih =>
      intro pre_w st decls_w hwhole hsr hsame hnames hkeys hnd hpref horig
      have ha_w : a ∈ order_w := by rw [← hwhole]; simp
      have ha_not_pre_w : a ∉ pre_w := by
        have hnd_w := hord_w_nodup
        rw [← hwhole, List.nodup_append] at hnd_w
        intro ha_pre
        exact hnd_w.2.2 a ha_pre a List.mem_cons_self rfl
      have ha_not_role : a ∉ order_role :=
        of_decide_eq_true (List.mem_filter.mp ha_w).2
      have hsplit_a : order = (order_role ++ pre_w) ++ a :: suf_w' := by
        rw [hord_split, ← hwhole, List.append_assoc]
      have ha_ord : a ∈ order := by rw [hsplit_a]; simp
      obtain ⟨c, hrecE, hrec₀, hwkSafe_a⟩ := hnonRole_mem a ha_w
      have hsr_pre : StreamReadBare cx pre.state
          (Ix.Cert.Stream.decodedOf E (order_role ++ pre_w)) st (decls_role ++ decls_w) := by
        rw [decodedOf_append]
        exact streamReadBare_append hsr_role hsr
      have hproj_emp : ∀ k : Core.KKey, st.projLevels[k]? = none :=
        streamReadBare_projLevels_empty hsr_pre (preludeFor_projLevels_empty hadm.preludeFor)
      have hprep_cur :
          (Ix.Kernel.Frontend.preparePrelude pre.ix (decls_role ++ decls_w)).toList =
            ds_role ++ decls_w.toList :=
        hprep_split decls_w hnames
      have hdec_split_a :
          Ix.Cert.Stream.decodedOf E order =
            Ix.Cert.Stream.decodedOf E (order_role ++ pre_w) ++
              (a, c) :: Ix.Cert.Stream.decodedOf E suf_w' := by
        rw [hsplit_a, decodedOf_append, decodedOf_cons_of_recordAt suf_w' hrecE]
      have hmem_dec_a : (a, c) ∈ Ix.Cert.Stream.decodedOf E order :=
        mem_decodedOf_of_mem ha_ord hrecE
      obtain ⟨c_chk', hrec₀_chk', hchk_or_muts⟩ :=
        (wkAll_closedSubwalk calls b.address t E₀).checked a hwkSafe_a.1
      have hc_chk_eq : c_chk' = c := Option.some.inj (hrec₀_chk'.symm.trans hrec₀)
      subst c_chk'
      -- Helper for key freshness at singleton key `Core.keyOf t a` when `c.info` is `.axio`/`.defn`
      have hfresh_singleton :
          ((∃ ax, c.info = .axio ax) ∨ (∃ df, c.info = .defn df)) →
          ∀ d₀ ∈ ds_role ++ decls_w.toList, ∀ ci₁ ∈ IxVM.Consistency.installs d₀,
            ci₁.name ≠ Core.keyOf t a := by
        intro hkind d₀ hd₀ ci₁ hci₁ heq_k
        rcases List.mem_append.mp hd₀ with hd_r | hd_w
        · rcases hrole_names d₀ hd_r ci₁ hci₁ a heq_k with ha_r | hown_r
          · exact ha_not_role ha_r
          · have hown_a := hown_r c (Or.inl hrec₀)
            have hown_self : Ix.Cert.ownerOf a c = a := by
              rcases hkind with ⟨ax, hax⟩ | ⟨df, hdf⟩
              · simp [Ix.Cert.ownerOf, hax]
              · simp [Ix.Cert.ownerOf, hdf]
            rw [hown_self] at hown_a
            exact ha_not_role hown_a
        · rcases hkeys d₀ hd_w ci₁ hci₁ with
            ⟨a', ha', hname', c', hrec', _⟩ |
            ⟨a', _, ms', i', d_m', hname', hm', hms'⟩ |
            ⟨x', hname', _, hc_ind, _⟩
          · have ha_eq := keyOf_injective hba.wellFormed (hname'.symm.trans heq_k)
            subst a'
            exact ha_not_pre_w ha'
          · have hdprj_eq := keyOf_injective hba.wellFormed (hname'.symm.trans heq_k)
            rw [← hdprj_eq] at hrec₀
            unfold Ix.Cert.recordAt at hrec₀
            cases hget₀_a : E₀.consts.get? (Core.dprjAddr a' i') with
            | none => rw [hget₀_a] at hrec₀; cases hrec₀
            | some lc₀_a =>
              rw [hget₀_a] at hrec₀
              obtain ⟨hh₀_a, hbl₀_a⟩ := hload.1 _ lc₀_a hget₀_a
              obtain ⟨c₀_a, hlc₀_a, hex₀_a⟩ := hexact₀ _ lc₀_a hget₀_a
              have hc₀_eq : c₀_a = c := Option.some.inj (hlc₀_a.symm.trans hrec₀)
              subst c₀_a
              obtain ⟨_, huniq_d⟩ := dprj_store_eq_of_mutsMemberChecked hbound hnoCol hm' hms'
              have hc_dprj := huniq_d lc₀_a.rawBytes c hbl₀_a hex₀_a
                (Or.inr (Or.inr hh₀_a))
              rw [hc_dprj] at hkind
              rcases hkind with ⟨_, hax⟩ | ⟨_, hdf⟩ <;> cases hax <;> cases hdf
          · have hx_eq := keyOf_injective hba.wellFormed (hname'.symm.trans heq_k)
            subst x'
            rcases hc_ind c hrec₀ with ⟨_, hi⟩ | ⟨_, hi⟩ | ⟨_, hi⟩ | ⟨_, hi⟩ <;>
              (rw [hi] at hkind; rcases hkind with ⟨_, h1⟩ | ⟨_, h1⟩ <;> cases h1)
      -- Now dispatch on `c.info` to obtain the step reading `r` and all invariants!
      have hstep_a :
          ∃ r : Ix.Kernel.Reader.Read .anon,
            Ix.Kernel.Reader.readRecordBare cx st a c = .ok r ∧
            (∀ k ∈ pre.state.keys, (st.commit r).SameAt pre.state k) ∧
            (∀ d ∈ r.decls.toList, ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role) ∧
            (∀ d ∈ r.decls.toList,
              CheckedConstOrigin calls t b.address E_core order_role d ∨
              CheckedIndOrigin calls b t E₀ E pre order order_role d) ∧
            (∀ d ∈ r.decls.toList, ∀ ci₀ ∈ IxVM.Consistency.installs d,
              WalkedKeyOrigin calls b.address t E₀ order_role (pre_w ++ [a]) ci₀.name) ∧
            ((r.decls.toList.flatMap (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup) ∧
            (∀ d ∈ r.decls.toList, ∀ ci₀ ∈ IxVM.Consistency.installs d,
              ∀ d₀ ∈ ds_role ++ decls_w.toList,
              ∀ ci₁ ∈ IxVM.Consistency.installs d₀, ci₁.name ≠ ci₀.name) ∧
            (∀ x c_x,
              ((x = a ∧ c_x = c ∧
                  ((∃ d_x, c_x.info = .defn d_x) ∨ (∃ ax, c_x.info = .axio ax) ∨
                    (∃ qt, c_x.info = .quot qt) ∨ (∃ rc, c_x.info = .recr rc) ∨
                    Ix.Cert.ownerOf x c_x ≠ x)) ∨
                OwnedOrProjOf E a x c_x) →
              ∃ ci₀,
                ci₀.name = Core.keyOf t x ∧
                L1.RecordReadsAs t E_core x c_x ci₀ ∧
                (IxVM.Consistency.inertKey (Core.keyOf t x) = false →
                  ∃ d ∈ (ds_role ++ decls_w.toList) ++ r.decls.toList,
                    ci₀ ∈ IxVM.Consistency.installs d)) := by
        cases hinfo : c.info with
        | quot q =>
          have hchk : Claim.CheckedAtFull calls b.address t a := by
            rcases hchk_or_muts with ⟨_, hm, _⟩ | hchk
            · rw [hinfo] at hm; cases hm
            · exact hchk
          exact (not_quot_of_nonRole_checked hbound hadm hload hexact₀ hnoCol
            hrec₀ hinfo ha_not_role hchk).elim
        | dPrj p | iPrj p | rPrj p | cPrj p =>
          have hchk : Claim.CheckedAtFull calls b.address t a := by
            rcases hchk_or_muts with ⟨_, hm, _⟩ | hchk
            · rw [hinfo] at hm; cases hm
            · exact hchk
          have hproj_a : Ix.Cert.ownerOf a c ≠ a :=
            proj_ownerOf_ne_self hbound hload hexact₀ hnoCol hrec₀
              (by simp [IsProjInfo, hinfo]) hchk
          have hown_ord_a : Ix.Cert.ownerOf a c ∈ order :=
            (hord.complete _).mpr (.step ((hord.complete a).mp ha_ord) ⟨c, hrecE, Or.inl ⟨rfl, hproj_a⟩⟩)
          obtain ⟨hres_ok, _, _, _, _, _, hws_own, hrk_lt, _⟩ :=
            walkedProjResolveOk hSR hbound hadm hload hexact₀ hnoCol hord hown_ord_a
              hrec₀ hwkSafe_a.1 hwkSafe_a.2 hproj_a hchk
          have hres_cx : (Ix.Kernel.Reader.resolveSource cx.store a c).isNone = false := hres_ok
          have hread : Ix.Kernel.Reader.readRecordBare cx st a c = .ok {} := by
            unfold Ix.Kernel.Reader.readRecordBare Ix.Kernel.Reader.readRecord
            rw [hinfo]
            dsimp only
            rw [hres_cx]
            rfl
          have hsame' := commit_sameAt_of_nonRole hadm hba hsame (r := {}) rfl rfl (by simp) (by simp)
          have hown_prev : Ix.Cert.ownerOf a c ∈ order_role ++ pre_w := by
            have hrk_own_lt : rk (Ix.Cert.ownerOf a c) < rk a := by
              by_cases ho_r : Ix.Cert.ownerOf a c ∈ order_role
              · have hlt_l : order_role.idxOf (Ix.Cert.ownerOf a c) < order_role.length :=
                  List.idxOf_lt_length_iff.mpr ho_r
                simp only [rk, roleTwoTierRank, ho_r, ha_not_role, ↓reduceIte]
                omega
              · simp only [rk, roleTwoTierRank, ho_r, ha_not_role, ↓reduceIte,
                  twoTierRank, hws_own, hwkSafe_a]
                omega
            rw [hsplit_a] at hown_ord_a
            rcases List.mem_append.mp hown_ord_a with hprev | htail
            · exact hprev
            · rcases List.mem_cons.mp htail with heq_oa | hsuf
              · rw [heq_oa] at hrk_own_lt
                exact absurd hrk_own_lt (Nat.lt_irrefl _)
              · have hpw := hsorted
                rw [hsplit_a, List.pairwise_append, List.pairwise_cons] at hpw
                have hle := hpw.2.1.1 _ hsuf
                omega
          refine ⟨{}, hread, hsame', by simp, by simp, by simp, by simp, by simp, ?_⟩
          intro x c_x hx_or
          rcases hx_or with ⟨rfl, rfl, _⟩ | hown_p
          · obtain ⟨ci₀, hname, hrra, hinst⟩ := hpref a c
              (Or.inr ⟨Ix.Cert.ownerOf a c, hown_prev, Or.inl ⟨hrecE, hproj_a.symm, rfl⟩⟩)
            exact ⟨ci₀, hname, hrra, fun hin =>
              let ⟨d, hd, hci⟩ := hinst hin; ⟨d, List.mem_append_left _ hd, hci⟩⟩
          · obtain ⟨ms, hm, _⟩ := ownedOrProjOf_inv hSR hbound hadm hload hexact₀ hnoCol hord
              ha_ord ha_not_role hrec₀ hrecE hown_p
            rw [hinfo] at hm; cases hm
        | axio ax =>
          have hchk : Claim.CheckedAtFull calls b.address t a := by
            rcases hchk_or_muts with ⟨_, hm, _⟩ | hchk
            · rw [hinfo] at hm; cases hm
            · exact hchk
          obtain ⟨ty₀, hread, hcco, hrra, hinst_ax⟩ :=
            checkedAxiom_of_checkedAtFull hSR (st := st) hbound hadm hba hload hexact₀ hblobs₀
              hnoCol hnoInt_core hsub_rec hord hauth_cx ha_ord ha_not_role hrec₀ hrecE
              hwkSafe_a.1 hwkSafe_a.2 hinfo hchk
          let cv : Ix.Kernel.ConstantVal .anon := ⟨Core.keyOf t a, List.range ax.lvls.toNat, ty₀⟩
          let decl : Ix.Kernel.Declaration .anon := .axiomDecl cv
          let ci₀ : Ix.Kernel.ConstantInfo .anon := .axiomInfo cv
          have hsame' := commit_sameAt_of_nonRole hadm hba hsame (r := { decls := #[decl] })
            rfl rfl (by simp [decl])
            (by intro d hd n hn; simp [decl] at hd; subst d; simp [Ix.Kernel.Declaration.names, cv] at hn;
                subst n; exact ⟨a, rfl, ha_not_role⟩)
          have hci_name : ∀ ci' ∈ IxVM.Consistency.installs decl, ci'.name = Core.keyOf t a := by
            intro ci' hci'
            unfold IxVM.Consistency.installs at hci'
            dsimp only [decl] at hci'
            split at hci'
            · cases hci'
            · simp [cv] at hci'
              rw [hci']
              rfl
          have hnd_ax :
              ((#[decl].toList.flatMap (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup) := by
            change ((([decl]).flatMap (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup)
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            unfold IxVM.Consistency.installs
            dsimp only [decl]
            split <;> simp
          refine ⟨{ decls := #[decl] }, hread, hsame', ?_, ?_, ?_, hnd_ax, ?_, ?_⟩
          · intro d hd n hn
            simp at hd; subst d
            simp [decl, Ix.Kernel.Declaration.names, cv] at hn; subst n
            exact ⟨a, rfl, ha_not_role⟩
          · intro d hd
            simp at hd; subst d
            exact Or.inl hcco
          · intro d hd ci' hci'
            simp at hd; subst d
            exact Or.inl ⟨a, by simp, hci_name ci' hci', c, hrec₀, Or.inl ⟨ax, hinfo⟩⟩
          · intro d hd ci' hci' d₀ hd₀ ci₁ hci₁
            simp at hd; subst d
            rw [hci_name ci' hci']
            exact hfresh_singleton (Or.inl ⟨ax, hinfo⟩) d₀ hd₀ ci₁ hci₁
          · intro x c_x hx_or
            rcases hx_or with ⟨rfl, rfl, _⟩ | hown_p
            · refine ⟨ci₀, rfl, hrra, fun hin => ⟨decl, ?_, hinst_ax hin⟩⟩
              exact List.mem_append_right _ (by simp)
            · obtain ⟨ms, hm, _⟩ := ownedOrProjOf_inv hSR hbound hadm hload hexact₀ hnoCol hord
                ha_ord ha_not_role hrec₀ hrecE hown_p
              rw [hinfo] at hm; cases hm
        | defn df =>
          have hchk : Claim.CheckedAtFull calls b.address t a := by
            rcases hchk_or_muts with ⟨_, hm, _⟩ | hchk
            · rw [hinfo] at hm; cases hm
            · exact hchk
          obtain ⟨decl, ci₀, hread, hcco, hinst, hname, hdnames, hnb, hrra⟩ :=
            checkedDefn_standalone hSR (st := st) hbound hadm hba hload hexact₀ hblobs₀
              hnoCol hnoInt_core hord hauth_cx hproj_emp ha_ord ha_not_role hrec₀ hrecE
              hwkSafe_a.1 hwkSafe_a.2 hinfo hchk
          have hsame' := commit_sameAt_of_nonRole hadm hba hsame (r := { decls := #[decl] })
            rfl rfl
            (by intro d hd; simp at hd; subst d; exact hnb)
            (by intro d hd n hn; simp at hd; subst d; rw [hdnames] at hn; simp at hn; subst n;
                exact ⟨a, rfl, ha_not_role⟩)
          have hnd_df :
              ((#[decl].toList.flatMap (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup) := by
            simp [hinst]
          refine ⟨{ decls := #[decl] }, hread, hsame', ?_, ?_, ?_, hnd_df, ?_, ?_⟩
          · intro d hd n hn
            simp at hd; subst d
            rw [hdnames] at hn; simp at hn; subst n
            exact ⟨a, rfl, ha_not_role⟩
          · intro d hd
            simp at hd; subst d
            exact Or.inl hcco
          · intro d hd ci' hci'
            simp at hd; subst d
            rw [hinst] at hci'; simp at hci'; subst ci'
            exact Or.inl ⟨a, by simp, hname, c, hrec₀, Or.inr ⟨df, hinfo⟩⟩
          · intro d hd ci' hci' d₀ hd₀ ci₁ hci₁
            simp at hd; subst d
            rw [hinst] at hci'; simp at hci'; subst ci'
            rw [hname]
            exact hfresh_singleton (Or.inr ⟨df, hinfo⟩) d₀ hd₀ ci₁ hci₁
          · intro x c_x hx_or
            rcases hx_or with ⟨rfl, rfl, _⟩ | hown_p
            · refine ⟨ci₀, hname, hrra, fun _ => ⟨decl, ?_, by rw [hinst]; simp⟩⟩
              exact List.mem_append_right _ (by simp)
            · obtain ⟨ms, hm, _⟩ := ownedOrProjOf_inv hSR hbound hadm hload hexact₀ hnoCol hord
                ha_ord ha_not_role hrec₀ hrecE hown_p
              rw [hinfo] at hm; cases hm
        | recr rc =>
          have hchk : Claim.CheckedAtFull calls b.address t a := by
            rcases hchk_or_muts with ⟨_, hm, _⟩ | hchk
            · rw [hinfo] at hm; cases hm
            · exact hchk
          obtain ⟨r, hread, hsame', hdecls_ind, hnd_r, hdisj_r, hrra_r⟩ :=
            hSR.indRecRecordReadBare hadm hbound hload hnoCol hdec_core hnoInt_core
              hsub_rec (fun _ _ hb => hb) hauth_cx hord hdec_split_a hsr_pre
              ha_not_role hrec₀ hwkSafe_a.1 hwkSafe_a.2 hdec_nonRole_all hsame
              (Or.inl ⟨rc, hinfo⟩)
          refine ⟨r, hread, hsame', ?_, ?_, ?_, hnd_r, ?_, ?_⟩
          · intro d hd n hn
            obtain ⟨x, rfl, hx_nr, _, _⟩ := (hdecls_ind d hd).2 n hn
            exact ⟨x, rfl, hx_nr⟩
          · intro d hd
            obtain ⟨⟨block, nP, hd_eq⟩, hdn⟩ := hdecls_ind d hd
            exact Or.inr ⟨a, c, st, r, ha_not_role, hmem_dec_a, hrec₀,
              hwkSafe_a.1, hwkSafe_a.2, hsame, hread, hd, ⟨block, nP, hd_eq⟩,
              fun n hn => let ⟨x, hx1, hx2, _, _⟩ := hdn n hn; ⟨x, hx1, hx2⟩,
              Or.inl ⟨rc, hinfo, hchk⟩⟩
          · intro d hd ci' hci'
            obtain ⟨⟨block, nP, rfl⟩, hdn⟩ := hdecls_ind d hd
            have hinst_eq := (basisPinHit_eq_none_of_nonRole hadm hba
              (fun n hn => let ⟨x, hx1, hx2, _, _⟩ := hdn n hn; ⟨x, hx1, hx2⟩)).2
            rw [hinst_eq] at hci'
            have hn_mem : ci'.name ∈ (Ix.Kernel.Declaration.indDecl block nP).names :=
              List.mem_map.mpr ⟨ci', hci', rfl⟩
            obtain ⟨x', hx1, hx2, hx3, hx4⟩ := hdn ci'.name hn_mem
            exact Or.inr (Or.inr ⟨x', hx1, hx2, hx3, hx4⟩)
          · intro d hd ci' hci' d₀ hd₀ ci₁ hci₁
            rw [← hprep_cur] at hd₀
            exact hdisj_r d hd ci' hci' d₀ hd₀ ci₁ hci₁
          · intro x c_x hx_or
            have hx_rc : (x = a ∧ c_x = c ∧ ∃ rc', c.info = .recr rc') ∨ OwnedOrProjOf E a x c_x := by
              rcases hx_or with ⟨rfl, rfl, _⟩ | hp
              · exact Or.inl ⟨rfl, rfl, rc, hinfo⟩
              · exact Or.inr hp
            obtain ⟨d, ci₀, hd_mem, hci_mem, hname, hrra⟩ := hrra_r x c_x hx_rc
            rw [hprep_cur] at hd_mem
            exact ⟨ci₀, hname, hrra, fun _ => ⟨d, hd_mem, hci_mem⟩⟩
        | muts ms =>
          have hm_all : ∀ k < ms.size, Claim.MutsMemberCheckedAtFull calls b.address t a ms k := by
            rcases hchk_or_muts with ⟨ms', hm_eq, hm_k⟩ | hchk
            · rw [hinfo] at hm_eq
              injection hm_eq with hmseq
              subst ms'
              exact hm_k
            · obtain ⟨_, _, _, _, _, _, _, _, _, _, _,
                bytes, _, _, _, _, _, hhash_ld, hblake_ld, _, hL1,
                hsub_ld, hld, _, _, _⟩ := checkedAtFull_loadedL1 hbound hchk
              obtain ⟨c_ld, hdec_ld, _, _, _, hld', hraw⟩ := hL1
              rw [hld] at hld'; injection hld' with hvv; subst hvv
              unfold Ix.Cert.recordAt at hrec₀
              cases hget₀ : E₀.consts.get? a with
              | none => rw [hget₀] at hrec₀; cases hrec₀
              | some lc₀ =>
                rw [hget₀] at hrec₀
                obtain ⟨hh₀, hbl₀⟩ := hload.1 a lc₀ hget₀
                obtain ⟨c₀, hlc₀, hex₀⟩ := hexact₀ a lc₀ hget₀
                have hraw_eq : bytes = lc₀.rawBytes := by
                  by_contra hne
                  exact hnoCol (Or.inl ⟨a, lc₀.rawBytes, bytes, Or.inr (Or.inr ⟨hh₀, hbl₀⟩),
                    Core.hashed_mono hsub_ld hhash_ld, hne, hblake_ld⟩)
                rw [hraw_eq, hex₀] at hdec_ld
                have hcc : c_ld = c :=
                  (Except.ok.inj hdec_ld).symm.trans (Option.some.inj (hlc₀.symm.trans hrec₀))
                subst c_ld
                unfold L1.RawCIRep at hraw
                rw [hinfo] at hraw
                cases hraw
          by_cases hall : ms.all (fun | .defn _ => true | _ => false) = true
          · obtain ⟨r, hread, hown_r, hblk_r, hdecls_r, hnd_r, hrra_r⟩ :=
              checkedMutsDefn_block hRP hSR (st := st) hbound hadm hba hcomm_extra hload hexact₀
                hblobs₀ hnoCol hnoInt_core hsub_rec hord hauth_cx hproj_emp ha_ord ha_not_role
                hrec₀ hrecE hwkSafe_a.1 hwkSafe_a.2 hinfo hall hm_all
            have hsame' := commit_sameAt_of_nonRole hadm hba hsame hown_r hblk_r
              (fun d hd => (hdecls_r d hd).2.1)
              (fun d hd n hn => by
                obtain ⟨_, _, k, _, _, _, _, hd_nr, hdnames, _, _⟩ := hdecls_r d hd
                rw [hdnames] at hn; simp at hn; subst n
                exact ⟨Core.dprjAddr a k, rfl, hd_nr⟩)
            refine ⟨r, hread, hsame', ?_, ?_, ?_, hnd_r, ?_, ?_⟩
            · intro d hd n hn
              obtain ⟨_, _, k, _, _, _, _, hd_nr, hdnames, _, _⟩ := hdecls_r d hd
              rw [hdnames] at hn; simp at hn; subst n
              exact ⟨Core.dprjAddr a k, rfl, hd_nr⟩
            · intro d hd
              exact Or.inl (hdecls_r d hd).1
            · intro d hd ci' hci'
              obtain ⟨_, _, k, hk_sz, d_m, ci₀, hms_k, _, _, hinst_d, hname_d⟩ := hdecls_r d hd
              rw [hinst_d] at hci'; simp at hci'; subst ci'
              exact Or.inr (Or.inl ⟨a, by simp, ms, k, d_m, hname_d, hm_all k hk_sz, hms_k⟩)
            · intro d hd ci' hci' d₀ hd₀ ci₁ hci₁ heq_k
              obtain ⟨_, _, k, hk_sz, d_m, ci₀, hms_k, hd_nr, _, hinst_d, hname_d⟩ := hdecls_r d hd
              rw [hinst_d] at hci'; simp at hci'; subst ci'
              rw [hname_d] at heq_k
              have hm_k := hm_all k hk_sz
              obtain ⟨hk_u64, huniq_k⟩ := dprj_store_eq_of_mutsMemberChecked hbound hnoCol hm_k hms_k
              rcases List.mem_append.mp hd₀ with hd_r | hd_w
              · rcases hrole_names d₀ hd_r ci₁ hci₁ (Core.dprjAddr a k) heq_k with hk_r | hown_r
                · exact hd_nr hk_r
                · have hown_a := hown_r ⟨.dPrj ⟨k.toUInt64, a⟩, #[], #[], #[], #[]⟩
                    (Or.inr ⟨a, ms, k, d_m, rfl, hk_u64, rfl, hm_k, hms_k⟩)
                  simp [Ix.Cert.ownerOf] at hown_a
                  exact ha_not_role hown_a
              · rcases hkeys d₀ hd_w ci₁ hci₁ with
                  ⟨a', _, hname', c', hrec', hkind'⟩ |
                  ⟨a', ha', ms', i', d_m', hname', hm', hms'⟩ |
                  ⟨x', hname', _, _, hne_dprj⟩
                · have ha_eq := keyOf_injective hba.wellFormed (hname'.symm.trans heq_k)
                  rw [ha_eq] at hrec'
                  unfold Ix.Cert.recordAt at hrec'
                  cases hget_d : E₀.consts.get? (Core.dprjAddr a k) with
                  | none => rw [hget_d] at hrec'; cases hrec'
                  | some lc_d =>
                    rw [hget_d] at hrec'
                    obtain ⟨hh_d, hbl_d⟩ := hload.1 _ lc_d hget_d
                    obtain ⟨c₀_d, hlc_d, hex_d⟩ := hexact₀ _ lc_d hget_d
                    have hc'_eq : c₀_d = c' := Option.some.inj (hlc_d.symm.trans hrec')
                    subst c₀_d
                    have hc_dprj := huniq_k lc_d.rawBytes c' hbl_d hex_d
                      (Or.inr (Or.inr hh_d))
                    rw [hc_dprj] at hkind'
                    rcases hkind' with ⟨_, h1⟩ | ⟨_, h1⟩ <;> cases h1
                · have hdprj_eq := keyOf_injective hba.wellFormed (hname'.symm.trans heq_k)
                  have ha_eq :=
                    (dprjAddr_inj_of_mutsMemberChecked hbound hnoCol hm' hms' hm_k hms_k hdprj_eq).1
                  subst a'
                  exact ha_not_pre_w ha'
                · have hx_eq := keyOf_injective hba.wellFormed (hname'.symm.trans heq_k)
                  exact hne_dprj a ms k d_m hm_k hms_k hx_eq
            · intro x c_x hx_or
              rcases hx_or with ⟨rfl, rfl, hbad⟩ | hown_p
              · rcases hbad with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | hproj_m
                · rw [hinfo] at h1; cases h1
                · rw [hinfo] at h1; cases h1
                · rw [hinfo] at h1; cases h1
                · rw [hinfo] at h1; cases h1
                · simp [Ix.Cert.ownerOf, hinfo] at hproj_m
              · obtain ⟨ms', hm_eq, hd_all⟩ := ownedOrProjOf_inv hSR hbound hadm hload hexact₀
                  hnoCol hord ha_ord ha_not_role hrec₀ hrecE hown_p
                rw [hinfo] at hm_eq; injection hm_eq with hmseq; subst ms'
                obtain ⟨k, _, hk_sz, _, _, rfl, rfl⟩ := hd_all hall
                obtain ⟨d, hd_mem, ci₀, hci_mem, hname, hrra⟩ := hrra_r k hk_sz
                exact ⟨ci₀, hname, hrra, fun _ => ⟨d, List.mem_append_right _ hd_mem, hci_mem⟩⟩
          · obtain ⟨r, hread, hsame', hdecls_ind, hnd_r, hdisj_r, hrra_r⟩ :=
              hSR.indRecRecordReadBare hadm hbound hload hnoCol hdec_core hnoInt_core
                hsub_rec (fun _ _ hb => hb) hauth_cx hord hdec_split_a hsr_pre
                ha_not_role hrec₀ hwkSafe_a.1 hwkSafe_a.2 hdec_nonRole_all hsame
                (Or.inr ⟨ms, hinfo, hall⟩)
            refine ⟨r, hread, hsame', ?_, ?_, ?_, hnd_r, ?_, ?_⟩
            · intro d hd n hn
              obtain ⟨x, rfl, hx_nr, _, _⟩ := (hdecls_ind d hd).2 n hn
              exact ⟨x, rfl, hx_nr⟩
            · intro d hd
              obtain ⟨⟨block, nP, hd_eq⟩, hdn⟩ := hdecls_ind d hd
              exact Or.inr ⟨a, c, st, r, ha_not_role, hmem_dec_a, hrec₀,
                hwkSafe_a.1, hwkSafe_a.2, hsame, hread, hd, ⟨block, nP, hd_eq⟩,
                fun n hn => let ⟨x, hx1, hx2, _, _⟩ := hdn n hn; ⟨x, hx1, hx2⟩,
                Or.inr ⟨ms, hinfo, hall, hm_all⟩⟩
            · intro d hd ci' hci'
              obtain ⟨⟨block, nP, rfl⟩, hdn⟩ := hdecls_ind d hd
              have hinst_eq := (basisPinHit_eq_none_of_nonRole hadm hba
                (fun n hn => let ⟨x, hx1, hx2, _, _⟩ := hdn n hn; ⟨x, hx1, hx2⟩)).2
              rw [hinst_eq] at hci'
              have hn_mem : ci'.name ∈ (Ix.Kernel.Declaration.indDecl block nP).names :=
                List.mem_map.mpr ⟨ci', hci', rfl⟩
              obtain ⟨x', hx1, hx2, hx3, hx4⟩ := hdn ci'.name hn_mem
              exact Or.inr (Or.inr ⟨x', hx1, hx2, hx3, hx4⟩)
            · intro d hd ci' hci' d₀ hd₀ ci₁ hci₁
              rw [← hprep_cur] at hd₀
              exact hdisj_r d hd ci' hci' d₀ hd₀ ci₁ hci₁
            · intro x c_x hx_or
              rcases hx_or with ⟨rfl, rfl, hbad⟩ | hown_p
              · rcases hbad with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | hproj_m
                · rw [hinfo] at h1; cases h1
                · rw [hinfo] at h1; cases h1
                · rw [hinfo] at h1; cases h1
                · rw [hinfo] at h1; cases h1
                · simp [Ix.Cert.ownerOf, hinfo] at hproj_m
              · obtain ⟨d, ci₀, hd_mem, hci_mem, hname, hrra⟩ := hrra_r x c_x (Or.inr hown_p)
                rw [hprep_cur] at hd_mem
                exact ⟨ci₀, hname, hrra, fun _ => ⟨d, hd_mem, hci_mem⟩⟩
      obtain ⟨r, hread_r, hsame_next, hnames_r, horig_r, hkeys_r, hnd_r, hdisj_r, hrra_step⟩ :=
        hstep_a
      have hsr_next :
          StreamReadBare cx st_r (Ix.Cert.Stream.decodedOf E (pre_w ++ [a]))
            (st.commit r) (decls_w ++ r.decls) := by
        rw [decodedOf_append, decodedOf_cons_of_recordAt [] hrecE]
        exact streamReadBare_append hsr (.cons hread_r .nil)
      have hnames_next :
          ∀ d ∈ (decls_w ++ r.decls).toList, ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role := by
        intro d hd
        rw [Array.toList_append] at hd
        rcases List.mem_append.mp hd with hd1 | hd2
        · exact hnames d hd1
        · exact hnames_r d hd2
      have hkeys_next :
          ∀ d ∈ (decls_w ++ r.decls).toList, ∀ ci₀ ∈ IxVM.Consistency.installs d,
            WalkedKeyOrigin calls b.address t E₀ order_role (pre_w ++ [a]) ci₀.name := by
        intro d hd ci₀ hci₀
        rw [Array.toList_append] at hd
        rcases List.mem_append.mp hd with hd1 | hd2
        · exact walkedKeyOrigin_mono (fun z hz => List.mem_append_left _ hz) (hkeys d hd1 ci₀ hci₀)
        · exact hkeys_r d hd2 ci₀ hci₀
      have hnd_next :
          (((ds_role ++ (decls_w ++ r.decls).toList).flatMap
            (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup) := by
        rw [Array.toList_append, ← List.append_assoc, List.flatMap_append, List.nodup_append]
        refine ⟨hnd, hnd_r, ?_⟩
        intro k₁ hk₁ k₂ hk₂ heq
        obtain ⟨d₀, hd₀, hmap₁⟩ := List.mem_flatMap.mp hk₁
        obtain ⟨ci₁, hci₁, rfl⟩ := List.mem_map.mp hmap₁
        obtain ⟨d, hd, hmap₂⟩ := List.mem_flatMap.mp hk₂
        obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmap₂
        exact hdisj_r d hd ci₀ hci₀ d₀ hd₀ ci₁ hci₁ heq
      have hpref_next :
          ∀ x c_x,
            ((x ∈ order_role ++ (pre_w ++ [a]) ∧ Ix.Cert.recordAt E x = some c_x ∧
                ((∃ d_x, c_x.info = .defn d_x) ∨ (∃ ax, c_x.info = .axio ax) ∨
                  (∃ qt, c_x.info = .quot qt) ∨ (∃ rc, c_x.info = .recr rc) ∨
                  Ix.Cert.ownerOf x c_x ≠ x)) ∨
              (∃ blk ∈ order_role ++ (pre_w ++ [a]), OwnedOrProjOf E blk x c_x)) →
            ∃ ci₀,
              ci₀.name = Core.keyOf t x ∧
              L1.RecordReadsAs t E_core x c_x ci₀ ∧
              (IxVM.Consistency.inertKey (Core.keyOf t x) = false →
                ∃ d ∈ ds_role ++ (decls_w ++ r.decls).toList, ci₀ ∈ IxVM.Consistency.installs d) := by
        intro x c_x hx
        rw [Array.toList_append, ← List.append_assoc]
        rcases hx with ⟨hx_mem, hrec_x, hkind_x⟩ | ⟨blk, hblk_mem, hown_x⟩
        · rw [← List.append_assoc] at hx_mem
          rcases List.mem_append.mp hx_mem with hx_prev | hx_a
          · obtain ⟨ci₀, hname, hrra, hinst⟩ := hpref x c_x (Or.inl ⟨hx_prev, hrec_x, hkind_x⟩)
            exact ⟨ci₀, hname, hrra, fun hin =>
              let ⟨d, hd, hci⟩ := hinst hin; ⟨d, List.mem_append_left _ hd, hci⟩⟩
          · simp at hx_a; subst x
            have hc_eq : c_x = c := Option.some.inj (hrec_x.symm.trans hrecE)
            subst c_x
            exact hrra_step a c (Or.inl ⟨rfl, rfl, hkind_x⟩)
        · rw [← List.append_assoc] at hblk_mem
          rcases List.mem_append.mp hblk_mem with hb_prev | hb_a
          · obtain ⟨ci₀, hname, hrra, hinst⟩ := hpref x c_x (Or.inr ⟨blk, hb_prev, hown_x⟩)
            exact ⟨ci₀, hname, hrra, fun hin =>
              let ⟨d, hd, hci⟩ := hinst hin; ⟨d, List.mem_append_left _ hd, hci⟩⟩
          · simp at hb_a; subst blk
            exact hrra_step x c_x (Or.inr hown_x)
      have horig_next :
          ∀ ds_pre d ds_suf env_pre,
            ds_role ++ (decls_w ++ r.decls).toList = ds_pre ++ d :: ds_suf →
            IxVM.Consistency.Installs ds_pre env_pre →
            (∃ ds_role_suf, ds_role = ds_pre ++ d :: ds_role_suf) ∨
            WalkedStepOrigin calls b t E₀ E E_core pre order order_role ds_pre env_pre d := by
        intro ds_pre d ds_suf env_pre hsplit_ds hinst_pre
        rw [Array.toList_append, ← List.append_assoc] at hsplit_ds
        rcases append_eq_append_cons_inv (ds_role ++ decls_w.toList) r.decls.toList
            ds_pre d ds_suf hsplit_ds with
          ⟨suf₁, hxs, _⟩ | ⟨r_before, hds_pre, hr_split⟩
        · exact horig ds_pre d suf₁ env_pre hxs hinst_pre
        · have hd_mem_r : d ∈ r.decls.toList := by rw [hr_split]; simp
          refine Or.inr ⟨a, c, pre_w, suf_w', st, decls_role ++ decls_w, r, r_before, ds_suf,
            hsplit_a, ha_not_role, hrec₀, hrecE, hwkSafe_a,
            hsr_pre, hsame, hread_r, hr_split, ?_, ?_, ?_, horig_r d hd_mem_r⟩
          · rw [hprep_cur]
            exact hds_pre
          · intro x c_x hx_pre
            obtain ⟨ci₀, hname, hrra, hinst_x⟩ := hpref x c_x hx_pre
            refine ⟨ci₀, hname, hrra, fun hin => ?_⟩
            obtain ⟨d₀, hd₀, hci₀⟩ := hinst_x hin
            have hd₀_pre : d₀ ∈ ds_pre := by
              rw [hds_pre]
              exact List.mem_append_left _ hd₀
            obtain ⟨ci, hfind, hstored⟩ := installs_prefix_stored hinst_pre hd₀_pre hci₀
            rw [hname] at hfind
            exact ⟨ci, hfind, hstored⟩
          · intro i hi ref c_r href hrec_r
            exact usedRef_mem_prev_of_nonRole hadm hload hexact₀ hnoCol hord hsplit_a
              ha_not_role hrec₀ hrecE hwkSafe_a.1 hi href hrec_r
      exact ih (pre_w ++ [a]) (st.commit r) (decls_w ++ r.decls)
        (by rw [List.append_assoc]; exact hwhole)
        hsr_next hsame_next hnames_next hkeys_next hnd_next hpref_next horig_next
  obtain ⟨st_final, decls_w_final, hsr_w_final, hsame_final, hnames_final,
    hnd_final, hpref_final, horig_final⟩ :=
    hstep_loop order_w [] st_r #[] rfl .nil hsame_role (by simp) (by simp)
      (by simpa using hnd_role)
      (by intro x c_x hx; rw [List.append_nil] at hx; rw [Array.toList_empty, List.append_nil]; exact hrole_rra x c_x hx)
      (by intro ds_pre d ds_suf _ hsplit_ds _; simp only [Array.toList_empty, List.append_nil] at hsplit_ds;
          exact Or.inl ⟨ds_suf, hsplit_ds⟩)
  let decls := decls_role ++ decls_w_final
  have hsr_total : StreamReadBare cx pre.state (Ix.Cert.Stream.decodedOf E order) st_final decls := by
    rw [hord_split, decodedOf_append]
    exact streamReadBare_append hsr_role hsr_w_final
  have hkeeps : Ix.Kernel.Reader.State.keepsPrelude pre.state st_final = true :=
    Ix.Kernel.Reader.State.keepsPrelude_iff.mpr hsame_final
  have hprep_final :
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList = ds_role ++ decls_w_final.toList :=
    hprep_split decls_w_final hnames_final
  refine ⟨E, E_role, E_core, limits, order, order_role, envA, pre, st_role, st_final,
    decls_role, decls, hadm, hdraws, hord, hadm.preludeFor,
    fun a lc hget => (hsub_auth.1 a lc hget).1,
    hsub_auth.2,
    fun a _ lc hget => (hsub_auth.1 a lc hget).2,
    hdec_core, hnoInt_core, hgood_core, hsub_rec, hfb_rec,
    blobs_coreEnvRole E₀ Keep supp roleBlobs pre,
    hsr_total, hkeeps,
    by rwa [hprep_final],
    fun ds_pre d ds_suf env_pre hsp hinst =>
      horig_final ds_pre d ds_suf env_pre (hprep_final.symm.trans hsp) hinst,
    ?_⟩
  intro a ha_seed
  have hws_a := hwkSafe_seeds a ha_seed
  obtain ⟨c, hrec₀_a, hchk_or⟩ := (wkAll_closedSubwalk calls b.address t E₀).checked a hws_a.1
  by_cases hmuts_a : ∃ ms, c.info = .muts ms
  · obtain ⟨ms, hinfo_a⟩ := hmuts_a
    exact Or.inl ⟨c, ms, hrec₀_a, hinfo_a⟩
  · have hrecE_a : Ix.Cert.recordAt E a = some c :=
      recordAt_subEnv_of_keep E₀ Keep supp (Or.inr hws_a) hrec₀_a
    have ha_ord : a ∈ order :=
      (hord.complete a).mpr (.seed (Or.inl ha_seed) (contains_of_recordAt hrecE_a))
    have hkind_a :
        (∃ d_x, c.info = .defn d_x) ∨ (∃ ax, c.info = .axio ax) ∨
        (∃ qt, c.info = .quot qt) ∨ (∃ rc, c.info = .recr rc) ∨
        Ix.Cert.ownerOf a c ≠ a := by
      cases hinfo_a : c.info with
      | muts ms => exact absurd ⟨ms, hinfo_a⟩ hmuts_a
      | defn d_x => exact Or.inl ⟨d_x, rfl⟩
      | axio ax => exact Or.inr (Or.inl ⟨ax, rfl⟩)
      | quot qt => exact Or.inr (Or.inr (Or.inl ⟨qt, rfl⟩))
      | recr rc => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rc, rfl⟩)))
      | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
        have hchk_a : Claim.CheckedAtFull calls b.address t a := by
          rcases hchk_or with ⟨_, hm, _⟩ | hchk
          · rw [hinfo_a] at hm; cases hm
          · exact hchk
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (proj_ownerOf_ne_self hbound hload hexact₀ hnoCol hrec₀_a
            (by simp [IsProjInfo, hinfo_a]) hchk_a))))
    obtain ⟨ci₀, hname, _, hinst_a⟩ := hpref_final a c (Or.inl ⟨ha_ord, hrecE_a, hkind_a⟩)
    have hninert_k : IxVM.Consistency.inertKey (Core.keyOf t a) = false :=
      inertKey_false_of_addressKey_not_inert hadm_b (addressKey_keyOf hadm_b a) (hseedOk a ha_seed).2
    obtain ⟨d, hd_mem, hci_mem⟩ := hinst_a hninert_k
    rw [← hprep_final] at hd_mem
    exact Or.inr ⟨Core.keyOf t a, d, ci₀, addressKey_keyOf hadm_b a, hname, hd_mem, hci_mem⟩

end IxVM.Refinement.Assembly
