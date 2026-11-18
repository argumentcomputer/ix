import IxVMRefinement.Binding.AdviceBlockReads

/-! # A record the run loads reads over a used-closed store

`Ingress::get_ci` takes no role context: a load of the record at `x` anywhere in the run (the
claim walk, a family check, an advice or witness check nested in another check) is a verified
load of the bytes the run hashed at `x`, with their decoding. For every kind but recursors and
quotients that load fixes a reading of the record over the run's store
(`LoadedReads.loadedL1_{defn,axio,dprj,ind,ctor}_reads`), and a reading over the run's store at
an address a used-closed store within the run's records holds is one over that store
(`reads_of_closed_sub`).

* `GetCILoad calls x`: an observed `Ingress::get_ci` at `x`, its calls among the run's.
* `getCILoad_reads`: a record the run loads, held by a used-closed store `R` within the run's
  records that holds the run's blobs, reads over `R`. Premises on the record: it is no recursor
  and no quotient record; it is in Lean's logic with its block; an axiom is at no inert role's
  address; a constructor projection is at the position its block declares for it. A block record
  has no load (`L1.RawCIRep` of a block is `False`). -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

set_option linter.unusedVariables false

/-- **An observed load of the record at `x`**: a call of `Ingress::get_ci` at `x`, under no role
context (the load takes none), with its calls among the run's. -/
def GetCILoad (calls : List (Call F)) (x : _root_.Address) : Prop :=
  ∃ (h h' : Heap F) (ap ptr : SourceValue F) (cs : List (Call F)),
    Core.S0.addr h ap x ∧ ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs ∧
    ∀ cl ∈ cs, cl ∈ calls

/-- The load of a sub-derivation is the run's. -/
theorem GetCILoad.mono {cs₁ cs₂ : List (Call F)} (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂)
    {x : _root_.Address} (h : GetCILoad cs₁ x) : GetCILoad cs₂ x := by
  obtain ⟨h, h', ap, ptr, cs, ha, ev, hs⟩ := h
  exact ⟨h, h', ap, ptr, cs, ha, ev, fun cl hcl => hsub cl (hs cl hcl)⟩

section Reads

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ R : Ixon.Env}

/-- **A record the run loads reads over a used-closed store holding it** (module docstring). -/
theorem getCILoad_reads (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hcl : UsedClosed R)
    (hsubR : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → R.blobs.get? y = some b)
    {x : _root_.Address} (hld : GetCILoad calls x) {c : Ixon.Constant}
    (hE : recordOf E₀ x = some c)
    (hrecr : ∀ r, c.info ≠ .recr r) (hrprj : ∀ p, c.info ≠ .rPrj p)
    (hquot : ∀ q, c.info ≠ .quot q) (hlog : InLogic c)
    (hlogB : ∀ cb, recordOf E₀ (Ix.Cert.ownerOf x c) = some cb → InLogic cb)
    (hinert : ∀ ax, c.info = .axio ax → ¬ InertAt t x)
    (hcidx : ∀ p, c.info = .cPrj p → ∀ cb ms ind ct, recordOf E₀ p.block = some cb →
      cb.info = .muts ms → ms[p.idx.toNat]? = some (.indc ind) →
      ind.ctors[p.cidx.toNat]? = some ct → ct.cidx.toNat = p.cidx.toNat)
    (hxR : (recordOf R x).isSome = true) : ∃ ci₀, Reads t R x ci₀ := by
  obtain ⟨h, h', ap, ptr, cs, ⟨a', ha', he⟩, ev, hsub⟩ := hld
  obtain ⟨-, bytes, E_ld, hhash, hblake, hloaded, hL1⟩ :=
    L1.get_ci_loadedL1_spec (RomBound.bounded_mono hbound hsub) ha' ev
  have hblake' : Address.blake3Pure bytes = x := hblake.trans he
  have hrecA : Ix.Cert.recordAt E₀ x = some c := (hS.recordOf_eq_recordAt _).symm.trans hE
  have hcR : recordOf R x = some c := by
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hxR
    rw [hc', Option.some.inj ((hsubR x c' hc').symm.trans hE)]
  have hown : (recordOf R (Ix.Cert.ownerOf x c)).isSome = true := (hcl.1 x c hcR).1
  -- the block of a projection record: held by `R`, so a record of the run's store
  have hblock : ∀ B, Ix.Cert.ownerOf x c = B →
      ∃ cb, Ix.Cert.recordAt E₀ B = some cb ∧ InLogic cb := by
    intro B hB
    rw [← hB]
    obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp hown
    have hcbE := hsubR _ cb hcb
    exact ⟨cb, (hS.recordOf_eq_recordAt _).symm.trans hcbE, hlogB cb hcbE⟩
  suffices hE' : ∃ ci₀, Reads t E₀ x ci₀ by
    obtain ⟨ci₀, hr⟩ := hE'
    exact ⟨ci₀, reads_of_closed_sub ht (wf_of_check ht) hsubR hcl hblob hxR hr⟩
  cases hi : c.info with
  | defn d =>
    obtain ⟨_, _, -, -, hreads, -⟩ :=
      LoadedReads.loadedL1_defn_reads ht hS hloaded hsub hhash hblake' hL1 hrecA hi hlog
    exact ⟨_, hreads default⟩
  | axio ax =>
    obtain ⟨_, -, hreads, -⟩ :=
      LoadedReads.loadedL1_axio_reads ht hS hloaded hsub hhash hblake' hL1 hrecA hi hlog
        (hinert ax hi)
    exact ⟨_, hreads⟩
  | quot q => exact absurd hi (hquot q)
  | recr r => exact absurd hi (hrecr r)
  | rPrj p => exact absurd hi (hrprj p)
  | dPrj p =>
    obtain ⟨cb, hcb, hlb⟩ := hblock p.block (by unfold Ix.Cert.ownerOf; simp only [hi])
    obtain ⟨_, _, _, _, -, -, -, -, -, hreads, -⟩ :=
      LoadedReads.loadedL1_dprj_reads ht hS hloaded hsub hhash hblake' hL1 hrecA hi hcb hlb
    exact ⟨_, hreads default⟩
  | iPrj p =>
    obtain ⟨cb, hcb, hlb⟩ := hblock p.block (by unfold Ix.Cert.ownerOf; simp only [hi])
    obtain ⟨_, _, _, -, -, -, -, hreads, -⟩ :=
      LoadedReads.loadedL1_ind_reads ht hS hloaded hsub hhash hblake' hL1 hrecA hi hcb hlb
    exact ⟨_, hreads default⟩
  | cPrj p =>
    obtain ⟨cb, hcb, hlb⟩ := hblock p.block (by unfold Ix.Cert.ownerOf; simp only [hi])
    have hcbE : recordOf E₀ p.block = some cb := hS.recordOf_of_recordAt hcb
    obtain ⟨_, _, _, _, -, -, -, -, -, hreads, -⟩ :=
      LoadedReads.loadedL1_ctor_reads ht hS hloaded hsub hhash hblake' hL1 hrecA hi hcb hlb
        (fun ms ind ct h1 h2 h3 => hcidx p hi cb ms ind ct hcbE h1 h2 h3)
    exact ⟨_, hreads⟩
  | muts ms =>
    obtain ⟨-, -, v, -, hraw⟩ := LoadedReads.loadedL1_record hS hsub hhash hblake' hL1 hrecA
    unfold L1.RawCIRep at hraw
    rw [hi] at hraw
    exact False.elim hraw

end Reads

end IxVM.Refinement.Binding
