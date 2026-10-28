import Ix.Cert.RefTables
import Ix.Cert.BlockRefs
import Ix.Cert.LayoutRefs
import Ix.Cert.BlockPublication
import Ix.Cert.GraphRefs

/-! # A compiled block's stored references

A compiled block's stored reference is the published address of a name a member's terms
mention, outside the block (`blockRefs_of`). The block's reference table holds only bindings of
mentioned names and blobs (`RefTables.runBlock_refs`); a blob is not a stored record when the
artifact keeps blobs and records apart (`BlobsApart`); a mentioned name is published at its
binding; and a block's own member is published at a record the block owns, which the reference
check excludes (`BlockRefs.no_self_reference`). -/

namespace Ix.Cert.CompiledRefs

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState
open Ix.Cert.ClosureLayout (addrOf)
open Ix.Cert.RefTables (Allowed Mentioned TermOf)
open Ix.LeanIngress (Graph Group FiberMap graphCollapsed scheduleOf)

/-- **No address is both a stored blob and a stored record** (the compile report's check). -/
def BlobsApart (ixe : Ixon.Env) : Prop :=
  ∀ a, (ixe.blobs.get? a).isSome = true → (ixe.consts.get? a).isSome = true → False

/-- **`runBlock_refs` at the cache the driver merges**: every entry of a block's table is the
binding of a name its members' terms mention, or a blob the cache or the environment holds. It
follows from `RefTables.runBlock_refs` once the block compile's tail only adds blobs (without
the aux entry registration). -/
def CacheRefs : Prop :=
  ∀ (cenv : CompileEnv) (all : Ix.Set Ix.Name) (lo : Ix.Name) (r : BlockResult) (c : BlockState)
    (layout : Option Ixon.AuxLayout), runBlock cenv all lo = .ok (r, c, layout) → ∀ a ∈ r.block.refs,
      Allowed (fun _ => Mentioned cenv.env (fun x => all.contains x = true ∨ x = lo)) (bindingView {}) cenv c a

/-- **A compiled block's stored reference is a mentioned name's publication, outside the
block**, given the artifact facts: the block's record is stored, the artifact keeps blobs and
records apart and has no reference cycle, the blobs the block reads are stored, a mentioned name
the block binds is published at its binding, and each member is published at a record the block
owns. -/
theorem blockRefs_of (cacheRefs : CacheRefs) {cenv : CompileEnv} {all : Ix.Set Ix.Name} {k : Ix.Name}
    {r : BlockResult} {c : BlockState} {layout : Option Ixon.AuxLayout}
    (hr : runBlock cenv all k = .ok (r, c, layout)) {ixe : Ixon.Env} (apart : BlobsApart ixe)
    (acyclic : referenceCycle ixe = none) (stored : recordAt ixe r.blockAddr = some r.block)
    (blobs : ∀ a, (BlobWrites.readBlob cenv.blobs c a).isSome = true → (ixe.blobs.get? a).isSome = true)
    (published : ∀ m a, Mentioned cenv.env (fun x => all.contains x = true ∨ x = k) m →
      lookupBinding cenv (bindingView {}) m = some a → addrOf ixe m = some a)
    (owned : ∀ x, all.contains x = true →
      ∃ P c', addrOf ixe x = some P ∧ recordAt ixe P = some c' ∧ ownerOf P c' = r.blockAddr)
    {a : Address} (ha : a ∈ r.block.refs) (hs : ixe.consts.contains a = true) :
    ∃ m, Mentioned cenv.env (fun x => all.contains x = true ∨ x = k) m ∧ addrOf ixe m = some a ∧
      lookupBinding cenv (bindingView {}) m = some a ∧ all.contains m = false := by
  rcases cacheRefs cenv all k r c layout hr a ha with ⟨m, hm, hb⟩ | blob
  · have hpub := published m a hm hb
    refine ⟨m, hm, hpub, hb, ?_⟩
    cases hin : all.contains m with
    | false => rfl
    | true =>
      obtain ⟨P, c', hP, hrec, hown⟩ := owned m hin
      rw [hpub] at hP
      cases hP
      exact (BlockRefs.no_self_reference acyclic stored ha hrec hown).elim
  · refine (apart a (blobs a blob) ?_).elim
    rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]
    exact hs


/-! ## Blocks of the condensation are closed under mutual reachability -/

open Ix.Cert.Condense (Path nodesOf namesOf edgesOf compsOf rootNames)
open Ix.CompileCert.Canon (Reach filt)

/-- **A path of references is reachability in the condensation's graph.** -/
theorem path_reach {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {x y : Ix.Name} (p : Path refs x y) :
    ∀ {u : Nat} (hu : u < (nodesOf refs).1.size), ((nodesOf refs).1[u].1 == x) = true →
      ∃ (w : Nat) (hw : w < (nodesOf refs).1.size), ((nodesOf refs).1[w].1 == y) = true ∧
        Reach (filt (edgesOf refs)) u w := by
  induction p with
  | refl e => intro u hu hx; exact ⟨u, hu, BEq.trans hx e, .refl u⟩
  | @step x z y rs hrs hz hzk _ ih =>
    intro u hu hx
    have hkey : refs.contains z = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?]; exact hzk
    obtain ⟨j, hj⟩ := FreshSnapshot.nodesOf_idx refs hkey
    obtain ⟨hj', hname⟩ := (Condense.nodesOf_spec refs).2 z j hj
    have hent : (nodesOf refs).1[u].2 = rs := by
      have h1 := Condense.node_get hu
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr hx, ← Std.HashMap.get?_eq_getElem?, hrs] at h1
      exact (Option.some.inj h1).symm
    have e := FreshSnapshot.edge_of_ref hu hj' (by rw [hent]; exact hz) hname
    obtain ⟨w, hw, hy, r⟩ := ih hj' hname
    exact ⟨w, hw, hy, Ix.CompileCert.Canon.Reach.trans (.tail (.refl u) e) r⟩

/-- **Two mutually reachable nodes have the same representative.** -/
theorem root_of_reach {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {u w : Nat}
    (hr : ∀ p ∈ (compsOf refs).comps.zip (compsOf refs).roots, p.2 < (namesOf refs).size)
    (hu : u < (namesOf refs).size) (hw : w < (namesOf refs).size)
    (r₁ : Reach (filt (edgesOf refs)) u w) (r₂ : Reach (filt (edgesOf refs)) w u) :
    (rootNames (namesOf refs) (compsOf refs) hr)[u] = (rootNames (namesOf refs) (compsOf refs) hr)[w] := by
  have hc := Condense.compsOf_eq refs
  obtain ⟨cm, hcm, hum, hwm⟩ := (Ix.CompileCert.Canon.condensation_scc hc u w).mpr
    ⟨by rw [← Condense.namesOf_size]; exact hu, by rw [← Condense.namesOf_size]; exact hw, r₁, r₂⟩
  obtain ⟨k, hk, ek⟩ := Array.mem_iff_getElem.mp hcm
  have hkr : k < (compsOf refs).roots.size := by
    rw [(CondenseRoots.condensation_roots_mem hc).1]; exact hk
  have hrn : (compsOf refs).roots[k] < (namesOf refs).size := by
    rw [Condense.namesOf_size]
    exact Ix.CompileCert.Canon.condensation_roots_lt hc (Array.getElem_mem hkr)
  have uniq := Ix.CompileCert.Canon.condensation_unique hc
  rw [Condense.rootNames_get uniq (by rw [Array.getElem?_eq_getElem hk, ek]) (Array.getElem?_eq_getElem hkr) hum hu hrn,
    Condense.rootNames_get uniq (by rw [Array.getElem?_eq_getElem hk, ek]) (Array.getElem?_eq_getElem hkr) hwm hw hrn]

/-- **A block holds every member of a block it reaches and is reached from**: two names of
blocks of the condensation on a cycle of references are in one block. -/
theorem same_block {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {rep repm : Ix.Name} {all allm : Ix.Set Ix.Name}
    {n m : Ix.Name} (hb : (Ix.CondenseM.run refs).blocks.get? rep = some all) (hn : all.contains n = true)
    (hbm : (Ix.CondenseM.run refs).blocks.get? repm = some allm) (hm : allm.contains m = true)
    (p₁ : Path refs n m) (p₂ : Path refs m n) : all.contains m = true := by
  obtain ⟨hr, hv, e⟩ := Condense.blocks_eq refs
  rw [e] at hb hbm
  obtain ⟨_, _, hbn, hrepn, hnn⟩ := Condense.blocksOfDisc_mem hb hn
  obtain ⟨vn, hvn, rfl⟩ := Condense.discOf_get hbn
  obtain ⟨_, _, hbm', hrepm, hnm⟩ := Condense.blocksOfDisc_mem hbm hm
  obtain ⟨vm, hvm, rfl⟩ := Condense.discOf_get hbm'
  dsimp only at hrepn hnn hrepm hnm
  have hvn' : vn < (nodesOf refs).1.size := by simpa [namesOf] using hvn
  have hvm' : vm < (nodesOf refs).1.size := by simpa [namesOf] using hvm
  simp only [namesOf, Array.getElem_map] at hnn hnm
  obtain ⟨w, hw, hwm, r₁⟩ := path_reach p₁ hvn' hnn
  have hwv : w = vm := Condense.namesOf_inj (by simpa [namesOf] using hw) hvm
    (by simp only [namesOf, Array.getElem_map]; exact BEq.trans hwm (BEq.symm hnm))
  subst hwv
  obtain ⟨w', hw', hwn, r₂⟩ := path_reach p₂ hw hnm
  have hwv' : w' = vn := Condense.namesOf_inj (by simpa [namesOf] using hw') hvn
    (by simp only [namesOf, Array.getElem_map]; exact BEq.trans hwn (BEq.symm hnn))
  subst hwv'
  have same := root_of_reach hr hvn hvm r₁ r₂
  have hrr : (repm == rep) = true := BEq.trans (BEq.symm hrepm) (same ▸ hrepn)
  have hg : (Condense.blocksOfDisc (Condense.discOf (namesOf refs) (compsOf refs)
      (rootNames (namesOf refs) (compsOf refs) hr) hv)).get? repm =
      (Condense.blocksOfDisc (Condense.discOf (namesOf refs) (compsOf refs)
      (rootNames (namesOf refs) (compsOf refs) hr) hv)).get? rep := by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr hrr]
  rw [hg, hb] at hbm
  cases hbm
  exact hm

/-- **A block's member is a node of the graph.** -/
theorem key_of_member {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {rep x : Ix.Name} {all : Ix.Set Ix.Name}
    (hb : (Ix.CondenseM.run refs).blocks.get? rep = some all) (hx : all.contains x = true) :
    refs.contains x = true := by
  obtain ⟨hr, hv, e⟩ := Condense.blocks_eq refs
  rw [e] at hb
  obtain ⟨_, _, hbx, _, hnx⟩ := Condense.blocksOfDisc_mem hb hx
  obtain ⟨vx, hvx, rfl⟩ := Condense.discOf_get hbx
  dsimp only at hnx
  have hvx' : vx < (nodesOf refs).1.size := by simpa [namesOf] using hvx
  simp only [namesOf, Array.getElem_map] at hnx
  rw [← Std.HashMap.contains_congr hnx, Std.HashMap.contains_eq_isSome_getElem?,
    ← Std.HashMap.get?_eq_getElem?, Condense.node_get hvx']
  rfl

/-! ## A claimed name's records -/

/-- **A claimed name's records**: its record and that record's block are the block's record, or a
projection with no references. -/
theorem claim_records {cenv : CompileEnv} {all : Ix.Set Ix.Name} {k : Ix.Name} {r : BlockResult}
    {c : BlockState} {layout : Option Ixon.AuxLayout} (hr : runBlock cenv all k = .ok (r, c, layout))
    {ixe : Ixon.Env} {n : Ix.Name} {P : Address} {b : ByteArray}
    (hclaim : (n, P, b) ∈ Resolution.claimWrites k r) (hP : ixe.consts.get? P = some { buf := b, len := b.size })
    (stored : recordAt ixe r.blockAddr = some r.block) :
    ∀ a ∈ [P, ClosureLayout.blockAt ixe P], ∀ c', recordAt ixe a = some c' → c'.refs = #[] ∨ c' = r.block := by
  have shape := BlockLayout.runBlock_shape hr
  have atBlock : ClosureLayout.blockAt ixe r.blockAddr = r.blockAddr := by
    unfold ClosureLayout.blockAt
    rw [stored]
    exact shape.built.owner _
  have blockCase : ∀ a ∈ [r.blockAddr, ClosureLayout.blockAt ixe r.blockAddr], ∀ c',
      recordAt ixe a = some c' → c'.refs = #[] ∨ c' = r.block := by
    intro a ha c' hc'
    rw [atBlock] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ha
    subst ha
    rw [stored] at hc'
    exact .inr (Option.some.inj hc').symm
  unfold Resolution.claimWrites at hclaim
  split at hclaim
  · simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
    obtain ⟨-, rfl, rfl⟩ := hclaim
    exact blockCase
  · obtain ⟨p, hp, e⟩ := Array.mem_map.mp hclaim
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    rcases shape.rows p hp with same | ⟨pwire, prefs, powner⟩
    · rw [same, ← shape.bytes, ← shape.addr]
      exact blockCase
    · have prec := BlockLayout.recordAt_ser pwire hP
      have hat : ClosureLayout.blockAt ixe (Address.admissionHash (Ixon.ser p.2.1)) = r.blockAddr := by
        unfold ClosureLayout.blockAt
        rw [prec]
        exact powner _
      intro a ha c' hc'
      rw [hat] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · rw [prec] at hc'
        cases hc'
        exact .inl prefs
      · rw [stored] at hc'
        exact .inr (Option.some.inj hc').symm

/-! ## The closure's grounded graph against the environment's -/

/-- **An edge of one grounded graph is an edge of another** between two of its nodes, when the
source constant is the same in both environments. -/
theorem edge_transfer {E₁ E₂ : Ix.Environment} {x z : Ix.Name} {rs : Ix.Set Ix.Name}
    (hrs : (groundSplit E₁).1.get? x = some rs) (hz : rs.contains z = true)
    (hx : (groundSplit E₂).1.contains x = true) (hzk : (groundSplit E₂).1.contains z = true)
    (same : E₂.consts.get? x = E₁.consts.get? x) :
    ∃ rs', (groundSplit E₂).1.get? x = some rs' ∧ rs'.contains z = true := by
  obtain ⟨rs₀, h₀, sub⟩ := Condense.groundSplit_get hrs
  obtain ⟨ci, hci, rfl⟩ := Condense.envSerial_get h₀
  have hx' : ((groundSplit E₂).1.get? x).isSome = true := by
    rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]; exact hx
  obtain ⟨rs', hrs'⟩ := Option.isSome_iff_exists.mp hx'
  obtain ⟨rs₀', h₀', -⟩ := Condense.groundSplit_get hrs'
  obtain ⟨ci', hci', rfl⟩ := Condense.envSerial_get h₀'
  rw [same, hci] at hci'
  cases hci'
  exact ⟨rs', hrs', FreshSnapshot.groundSplit_keep hrs' h₀' (sub z hz) hzk⟩

/-- **A path of one grounded graph is a path of another**, along names `S` keeps that are nodes
of the other with the same constant. -/
theorem path_transfer {E₁ E₂ : Ix.Environment} (S : Ix.Name → Prop)
    (closed : ∀ x z rs, S x → (groundSplit E₁).1.get? x = some rs → rs.contains z = true →
      ((groundSplit E₁).1.get? z).isSome = true → S z)
    (key : ∀ x, S x → (groundSplit E₂).1.contains x = true)
    (same : ∀ x, S x → E₂.consts.get? x = E₁.consts.get? x) {x y : Ix.Name}
    (p : Path (groundSplit E₁).1 x y) (hx : S x) : Path (groundSplit E₂).1 x y := by
  induction p with
  | refl e => exact .refl e
  | @step x z y rs hrs hz hzk _ ih =>
    have hSz := closed x z rs hx hrs hz hzk
    obtain ⟨rs', hrs', hz'⟩ := edge_transfer hrs hz (key x hx) (key z hSz) (same x hx)
    refine .step hrs' hz' ?_ (ih hSz)
    rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]
    exact key z hSz

/-- A node of a grounded graph is a constant of its environment. -/
theorem node_const {E : Ix.Environment} {z : Ix.Name} (h : ((groundSplit E).1.get? z).isSome = true) :
    (E.consts.get? z).isSome = true := by
  obtain ⟨rs, hrs⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨rs₀, h₀, -⟩ := Condense.groundSplit_get hrs
  obtain ⟨ci, hci, -⟩ := Condense.envSerial_get h₀
  rw [hci]
  rfl

/-- **The environment's grounded paths from a closure name stay in the closure.** -/
theorem closure_closed_env {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) :
    ∀ x z rs, (sub.consts.get? x).isSome = true → (groundSplit { consts := env.consts }).1.get? x = some rs →
      rs.contains z = true → ((groundSplit { consts := env.consts }).1.get? z).isSome = true →
        (sub.consts.get? z).isSome = true := by
  intro x z rs hx hrs hz hzk
  exact Condense.closure_path hcl (.step hrs hz hzk (.refl (BEq.refl z))) hx

/-- **The closure's grounded paths stay in the closure.** -/
theorem closure_closed_sub {sub : Ix.Environment} :
    ∀ x z rs, (sub.consts.get? x).isSome = true → (groundSplit sub).1.get? x = some rs →
      rs.contains z = true → ((groundSplit sub).1.get? z).isSome = true → (sub.consts.get? z).isSome = true :=
  fun _ _ _ _ _ _ hzk => node_const hzk

theorem closure_same {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) {x : Ix.Name} (hx : (sub.consts.get? x).isSome = true) :
    sub.consts.get? x = env.consts.get? x := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hx
  rw [hci, IsClosure.mem_env hcl hci]

/-! ## Under the schedule, every closure name is in quotient Source's condensation -/

/-- **A closure name is in a block of the closure's condensation**, when the schedule lets every
group through. -/
theorem placed {ρ : FiberMap} {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    {sub : Ix.Environment}
    (scheduled : ∀ x ∈ (scheduleOf (graphCollapsed ρ hints sub (blocksOf sub))).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {x : Ix.Name} (hx : (sub.consts.get? x).isSome = true) :
    ∃ lo all, (blocksOf sub).lowLinks.get? x = some lo ∧ (blocksOf sub).blocks.get? lo = some all ∧
      all.contains x = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hx
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hci
  obtain ⟨k, ek, hk⟩ := hci
  obtain ⟨gr, hgrm, hkn⟩ := SourceDeclares.stored_grouped sub (blocksOf sub) hk
  obtain ⟨i, hi, hgi⟩ := Array.getElem_of_mem hgrm
  have hgr : (graphCollapsed ρ hints sub (blocksOf sub)).groups[i]? = some gr := by
    show (Ix.LeanIngress.groupsOf sub (blocksOf sub))[i]? = some gr
    rw [Array.getElem?_eq_getElem hi, hgi]
  obtain ⟨c0, hmem⟩ := Ix.LeanIngress.scheduleOf_complete _ (Array.getElem?_eq_some_iff.mp hgr).1
  obtain ⟨q, hq, hqe⟩ := Array.getElem_of_mem hmem
  have hxz : ((i, c0), q) ∈ (scheduleOf (graphCollapsed ρ hints sub (blocksOf sub))).zipIdx.toList :=
    Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr (by simp [hq, hqe]))
  obtain ⟨conv, hconv⟩ := scheduled _ hxz
  have hplaced := GroupRefs.scheduled_placed (x := (i, c0)) hmem hconv
  obtain ⟨lo, hlo, -⟩ := GroupRefs.graphOf_covers (blocksOf sub) (Ix.LeanIngress.groupsOf sub (blocksOf sub))
    ((Ix.LeanIngress.groupsOf sub (blocksOf sub)).map Ix.LeanIngress.convert) hgr hplaced hkn
  obtain ⟨all, hall, hkall⟩ := GroupRefs.condense_lowLinks hlo
  refine ⟨lo, all, ?_, hall, ?_⟩
  · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr ek, ← Std.HashMap.get?_eq_getElem?]
    exact hlo
  · rw [Std.HashSet.contains_congr ek]
    exact hkall

/-! ## `CompiledRefs` -/

/-- The environment's condensation: the compile's blocks. -/
abbrev envBlocks (env : Ix.Environment) : Ix.CondensedBlocks :=
  Ix.CondenseM.run (groundSplit { consts := env.consts }).1

/-- **What the fold gives of a published closure name's block, for its references**: the
block of the environment's condensation the name is in, compiled from a snapshot whose
environment is the input's, with the name's claim at its address, the block's record stored, the
blobs it reads stored, each mentioned name it binds published at its binding (an input
constant), and each member published at a record the block owns. -/
def RefsAt (env : Ix.Environment) (ixe : Ixon.Env) (n : Ix.Name) (P : Address) : Prop :=
  ∃ (cenv : CompileEnv) (rep : Ix.Name) (all : Ix.Set Ix.Name) (r : BlockResult) (c : BlockState)
    (layout : Option Ixon.AuxLayout) (b : ByteArray),
    (envBlocks env).blocks.get? rep = some all ∧ all.contains n = true ∧
    all.contains (blockKey rep all) = true ∧ runBlock cenv all (blockKey rep all) = .ok (r, c, layout) ∧
    (n, P, b) ∈ Resolution.claimWrites (blockKey rep all) r ∧
    ixe.consts.get? P = some { buf := b, len := b.size } ∧ recordAt ixe r.blockAddr = some r.block ∧
    (∀ x, cenv.env.get? x = env.consts.get? x) ∧
    (∀ a, (BlobWrites.readBlob cenv.blobs c a).isSome = true → (ixe.blobs.get? a).isSome = true) ∧
    (∀ m a, Mentioned cenv.env (fun x => all.contains x = true ∨ x = blockKey rep all) m →
      lookupBinding cenv (bindingView {}) m = some a → addrOf ixe m = some a ∧ (env.consts.get? m).isSome = true) ∧
    (∀ x, all.contains x = true →
      ∃ P' c', addrOf ixe x = some P' ∧ recordAt ixe P' = some c' ∧ ownerOf P' c' = r.blockAddr)

theorem reaches_of_sub {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) {x : Ix.Name} (hx : (sub.consts.get? x).isSome = true) : Reaches env roots x := by
  by_contra hr
  rw [(hcl x).2 hr] at hx
  cases hx

/-- A reference of a closure constant to an input constant is a closure constant. -/
theorem sub_of_ref {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    (hcl : IsClosure env roots sub) {x y : Ix.Name} {ci : Ix.ConstantInfo} (hx : (sub.consts.get? x).isSome = true)
    (hci : env.consts.get? x = some ci) (hr : (refsOf ci).contains y = true) (hy : (env.consts.get? y).isSome = true) :
    (sub.consts.get? y).isSome = true := by
  have hry : Reaches env roots y := .step (reaches_of_sub hcl hx) ⟨ci, hci, .inl hr⟩
  rw [(hcl y).1 hry]
  exact hy

/-- **`CompiledRefs` from the fold's blocks**, when the schedule lets every group through: the
block record of a group name's claim holds only mentioned names' publications outside the block
(`blockRefs_of`); the mentioning member and the mentioned name are closure names, so they are
nodes of the closure's grounded graph (`placed`) with the same references there, and the closure's
component of the name is the compile's block (`path_transfer`, `same_block`). -/
theorem compiledRefs_of {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment} {ixe : Ixon.Env}
    {failures : Failures} {ρ : FiberMap}
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (hcl : IsClosure env roots sub) (compiled : compileReport env = .ok (ixe, failures))
    (scheduled : ∀ x ∈ (scheduleOf (graphCollapsed ρ hints sub (blocksOf sub))).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    (cacheRefs : CacheRefs) (apart : BlobsApart ixe) (acyclic : referenceCycle ixe = none)
    (inBlocks : ∀ x, (sub.consts.get? x).isSome = true → FreshSnapshot.Member (envBlocks env) x)
    (refsAt : ∀ (i : Nat) (gr : Group), (graphCollapsed ρ hints sub (blocksOf sub)).groups[i]? = some gr →
      ∀ n ∈ gr.names, ∀ P,
      addrOf ixe n = some P → (sub.consts.get? n).isSome = true ∧ RefsAt env ixe n P) :
    LayoutRefs.CompiledRefs ixe sub (graphCollapsed ρ hints sub (blocksOf sub)) := by
  intro i gr hgr n hn a ha c hc r hr hs
  unfold ClosureLayout.nameRecords at ha
  cases hP : addrOf ixe n with
  | none => rw [hP] at ha; simp at ha
  | some P =>
  rw [hP] at ha
  obtain ⟨hnsub, cenv, rep, all, rb, cb, layout, b, hall, hnall, hkey, hrun, hclaim, hPb, stored, hagree, blobs,
    published, owned⟩ := refsAt i gr hgr n hn P hP
  rcases claim_records hrun hclaim hPb stored a ha c hc with empty | rfl
  · rw [empty] at hr
    simp at hr
  obtain ⟨m, ⟨x, e, hN, ⟨ci, hci, hte⟩, hme⟩, hm, hbind, hmout⟩ := blockRefs_of cacheRefs hrun apart acyclic stored
    blobs (fun m a hm hb => (published m a hm hb).1) owned hr hs
  have hmenv := (published m r ⟨x, e, hN, ⟨ci, hci, hte⟩, hme⟩ hbind).2
  have allSub : ∀ y, all.contains y = true → (sub.consts.get? y).isSome = true := fun y hy =>
    Condense.closure_path hcl (Condense.condense_scc hall hnall hy) hnsub
  have hxall : all.contains x = true := hN.elim id fun h => h ▸ hkey
  have hcix : env.consts.get? x = some ci := by rw [← hagree]; exact hci
  -- the member whose references hold `m`
  obtain ⟨x', ci', hx'all, hci', hrefm⟩ : ∃ x' ci', all.contains x' = true ∧ env.consts.get? x' = some ci' ∧
      (refsOf ci').contains m = true := by
    rcases hte with he | ⟨iv, cn, cv, rfl, hcn, hcv, rfl⟩
    · exact ⟨x, ci, hxall, hcix, GraphRefs.refsOf_mentions ci he hme⟩
    · have hcnenv : env.consts.get? cn = some (.ctorInfo cv) := by rw [← hagree]; exact hcv
      have hcnsub : (sub.consts.get? cn).isSome = true :=
        sub_of_ref hcl (allSub x hxall) hcix (FreshSnapshot.refsOf_induct iv hcn) (by rw [hcnenv]; rfl)
      have hcnall := FreshSnapshot.ctorsInBlock compiled (E := cenv.env) hagree rep all x iv cn hall hxall hci hcn
        (inBlocks cn hcnsub)
      exact ⟨cn, .ctorInfo cv, hcnall, hcnenv,
        GraphRefs.refsOf_mentions (.ctorInfo cv) (by simp [termsOf, Ix.ConstantInfo.getCnst]) hme⟩
  have hx'sub := allSub x' hx'all
  have hmsub : (sub.consts.get? m).isSome = true := sub_of_ref hcl hx'sub hci' hrefm hmenv
  let S : Ix.Name → Prop := fun y => (sub.consts.get? y).isSome = true
  have keySub : ∀ y, S y → (groundSplit sub).1.contains y = true := fun y hy => by
    obtain ⟨_, allY, -, hallY, hyY⟩ := placed scheduled hy
    exact key_of_member hallY hyY
  have keyEnv : ∀ y, S y → (groundSplit { consts := env.consts }).1.contains y = true := fun y hy => by
    obtain ⟨_, allY, hallY, hyY⟩ := inBlocks y hy
    exact key_of_member hallY hyY
  refine ⟨x', m, hm, ?_, fun lo allS hlo hallS => ?_⟩
  · -- `m` is a grounded reference of `x'` in the closure
    have kx := keySub x' hx'sub
    have hx'g : ((groundSplit sub).1.get? x').isSome = true := by
      rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]; exact kx
    obtain ⟨rs, hrs⟩ := Option.isSome_iff_exists.mp hx'g
    obtain ⟨rs₀, h₀, -⟩ := Condense.groundSplit_get hrs
    obtain ⟨ci'', hci'', rfl⟩ := Condense.envSerial_get h₀
    rw [closure_same hcl hx'sub, hci'] at hci''
    cases hci''
    have hkeep := FreshSnapshot.groundSplit_keep hrs h₀ hrefm (keySub m hmsub)
    show (((groundSplit sub).1).getD x' {}).contains m = true
    rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, hrs]
    exact hkeep
  · obtain ⟨all₀, hall₀, hn₀⟩ := GroupRefs.condense_lowLinks hlo
    have e : some all₀ = some allS := hall₀.symm.trans hallS
    cases e
    constructor
    · -- `x'` is in `n`'s component of the closure
      have q₁ := path_transfer (E₁ := { consts := env.consts }) (E₂ := sub) S (closure_closed_env hcl) keySub
        (fun y hy => closure_same hcl hy) (Condense.condense_scc hall hnall hx'all) hnsub
      have q₂ := path_transfer (E₁ := { consts := env.consts }) (E₂ := sub) S (closure_closed_env hcl) keySub
        (fun y hy => closure_same hcl hy) (Condense.condense_scc hall hx'all hnall) hx'sub
      obtain ⟨_, allX, -, hallX, hxX⟩ := placed scheduled hx'sub
      exact same_block (refs := (groundSplit sub).1) hallS hn₀ hallX hxX q₁ q₂
    · -- `m` is not: it is outside the compile's block
      cases hmS : allS.contains m with
      | false => rfl
      | true =>
        have q₁ := path_transfer (E₁ := sub) (E₂ := { consts := env.consts }) S closure_closed_sub keyEnv
          (fun y hy => (closure_same hcl hy).symm) (Condense.condense_scc (refs := (groundSplit sub).1) hallS hn₀ hmS)
          hnsub
        have q₂ := path_transfer (E₁ := sub) (E₂ := { consts := env.consts }) S closure_closed_sub keyEnv
          (fun y hy => (closure_same hcl hy).symm) (Condense.condense_scc (refs := (groundSplit sub).1) hallS hmS hn₀)
          hmsub
        obtain ⟨_, allM, hallM, hmM⟩ := inBlocks m hmsub
        have hin := same_block hall hnall hallM hmM q₁ q₂
        rw [hin] at hmout
        cases hmout

/--
info: 'Ix.Cert.CompiledRefs.blockRefs_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blockRefs_of

/--
info: 'Ix.Cert.CompiledRefs.compiledRefs_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms compiledRefs_of

end Ix.Cert.CompiledRefs
