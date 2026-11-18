import IxVMRefinement.FamilyGraph.Graph
import IxVMRefinement.Binding.Carried

/-! # The typing skeleton over the family graph

The fold of `Assembly/TypingSkeleton.lean` steps every top-walked anchor by a plain `UnitStep`.
With mutual and nested families three things differ: a block installs its family record with
itself (and is handed the advice its family check validated), a family record a block claims
is no unit of its own, and a second family record of a block (a twin) is a unit that needs the
block's family record stored. This module proves the fold and the typing conclusion over
`familyFold` from `TopGraph` and `FamilyGraph`:

* `fold_steps_family`: the fold's steps from three step hypotheses: `UnitStep` for a unit with
  no family record that is no twin, `UnitStepFam` for a block with a family record,
  `UnitStepTwin` for a twin;
* `owner_of_top_const`: an unstored constant address of a top-walked record in Lean's logic is
  owned by a unit: the record itself, or, where a block claims the record as its family
  record, that block;
* `typing_skeleton_core_family`: the typing conclusion (`ConsistentReadOver`) from the walk,
  the family graph and the three step hypotheses. A seed that is a recursor of a claimed family
  record is served by the block that claims the record. -/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal)

set_option linter.unusedVariables false

section Fold

variable {X : Ix.Kernel.Env .anon → Prop} {t : Ix.Kernel.RoleTable} {R E₀ E : Ixon.Env}
  {envT : Ix.Kernel.Env .anon} {seeds : List _root_.Address} {Top : _root_.Address → Prop}
  {rank : _root_.Address → Nat} {lim : Option Nat} {us : List _root_.Address}
  {fam twin : _root_.Address → Option _root_.Address}
  {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}

/-- A reading kept over the run of a constant address that holds no axiom record. -/
private theorem kept_of_reads_run {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    {x : _root_.Address} {ci ci₀ : ConstantInfo .anon} (hr : Reads t E₀ x ci₀)
    (hst : StoredAs ci ci₀)
    (hnax : ∀ c' ax, recordOf E₀ x = some c' → c'.info = .axio ax → False) :
    KeptIn t (storeOver E₀ R) (blobOver E₀ R) x ci :=
  keptIn_over_run ⟨fun c' ax hc' hinfo => (hnax c' ax hc' hinfo).elim, ci₀, hr, hst⟩

/-- **An unstored constant address of a top-walked record in Lean's logic is owned by a unit**:
the record itself, or the block that claims it as its family record. -/
theorem owner_of_top_const (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hus : ∀ A, A ∈ us ↔ IsUnit t envT E₀ Top Inner fam A) {D x : _root_.Address}
    {cb : Ixon.Constant} (hT : Top D) (hcb : recordOf E₀ D = some cb) (hlog : InLogic cb)
    (hx : ConstAddrOf D cb x) (hst : ¬ StoredAt t envT x) :
    ∃ b ∈ us, FamOwns E₀ fam b x := by
  rcases Classical.em (∃ B, fam B = some D) with ⟨B, hB⟩ | hne
  · obtain ⟨hUB, cB, hcB, hlogB, x₀, hx₀, hun⟩ := hF.famUnit B D hB
    exact ⟨B, (hus B).mpr ⟨Or.inl (hF.famBlock B D hB), hUB, cB, hcB, hlogB, x₀, hx₀, hun⟩,
      cB, hcB, Or.inr ⟨D, cb, hB, hcb, hx⟩⟩
  · exact ⟨D, (hus D).mpr ⟨Or.inl hT, fun B hB => hne ⟨B, hB⟩, cb, hcb, hlog, x, hx, hst⟩,
      cb, hcb, Or.inl hx⟩

/-- **The steps of the fold over the family graph**, from `UnitStep` for each unit with no
family record that is no twin, `UnitStepFam` for each block with a family record, and
`UnitStepTwin` for each twin. -/
theorem fold_steps_family (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    (hwhole : ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored t envT B ms)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c)
    (hus : ∀ A, A ∈ us ↔ IsUnit t envT E₀ Top Inner fam A)
    (hstep : ∀ A c, Walked Top Inner A → Unclaimed fam A → recordOf E₀ A = some c → InLogic c →
      UnitKind c → fam A = none → twin A = none → UnitStep.{u} X t envT E₀ E lim A c)
    (hstepFam : ∀ A c rb crb rs, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
      fam A = some rb → FamRecRecord E₀ rb crb rs →
      UnitStepFam.{u} X t envT E₀ E lim A c rb crb (adv A))
    (hstepTwin : ∀ A c B rb crb, Walked Top Inner A → recordOf E₀ A = some c → InLogic c →
      twin A = some B → fam B = some rb → recordOf E₀ rb = some crb →
      UnitStepTwin.{u} X t envT E₀ E lim A c rb crb) :
    (familyFold.{u} X t E₀ R E lim rank fam twin adv).Steps envT us := by
  intro env A hA hinv hext hneed hfr
  have hFI : FoldInv.{u} X t E₀ R E lim env := hinv
  have hextT : ∀ ci ∈ envT.consts, ci ∈ env.consts := hext
  have hAu := (hus A).mp hA
  obtain ⟨hW, hU, c, hc, hlog, x₀, hx₀, hun⟩ := hAu
  have hkind : UnitKind c := by
    rcases kind_cases c with hsa | hpr | hbl
    · rcases hsa with ⟨d, h⟩ | ⟨rc, h⟩ | hax | hq
      · exact Or.inl ⟨d, h⟩
      · exact Or.inr (Or.inl ⟨rc, h⟩)
      · exfalso
        rcases hW with hT | hI
        · obtain ⟨r, hr, ha⟩ := hG.standing A c hT hc (Or.inl hax)
          exact unit_fresh hG hF hwhole hrun ((hus A).mp hA) hc
            (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl hax))⟩) (standing_stored hshape htwf hr ha)
        · obtain ⟨ax, hax'⟩ := hax
          exact (hF.innerKind A c hI hc).1 ax hax'
      · exfalso
        rcases hW with hT | hI
        · obtain ⟨r, hr, ha⟩ := hG.standing A c hT hc (Or.inr hq)
          exact unit_fresh hG hF hwhole hrun ((hus A).mp hA) hc
            (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr hq))⟩) (standing_stored hshape htwf hr ha)
        · obtain ⟨q, hq'⟩ := hq
          exact (hF.innerKind A c hI hc).2 q hq'
    · exfalso
      rcases hx₀ with ⟨-, hs⟩ | ⟨ms, i, m, hms, -, -⟩
      · exact standalone_not_proj hs hpr
      · exact proj_not_block hpr ⟨ms, hms⟩
    · exact Or.inr (Or.inr hbl)
  -- an own constant address holds no axiom record
  have hnaxA : ∀ x, ConstAddrOf A c x → ∀ c' ax, recordOf E₀ x = some c' →
      c'.info = .axio ax → False := by
    intro x hx c' ax hc' hinfo
    rcases walked_constAddr_cases hG hF hW hc hx with ⟨h1, -⟩ | ⟨-, P, hP, hPp, -⟩
    · rw [h1, hc] at hc'
      have hcc : c = c' := Option.some.inj hc'
      rw [← hcc] at hinfo
      rcases hkind with ⟨d, h⟩ | ⟨rc, h⟩ | ⟨ms, h⟩ <;> (rw [h] at hinfo; cases hinfo)
    · rw [hP] at hc'
      have hcc : P = c' := Option.some.inj hc'
      rw [← hcc] at hinfo
      rcases hPp with ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ <;> (rw [h] at hinfo; cases hinfo)
  -- the frame and the new state, once the step has given `new` at the owned addresses
  have hfinish : ∀ (new : List (ConstantInfo .anon)) (Own : _root_.Address → Prop),
      (∀ x, Own x ↔ FamOwns E₀ fam A x) →
      (new.map (·.name)).Nodup → (∀ ci ∈ new, env.find? ci.name = none) →
      Decl.PrefixInv.{u} E t lim ⟨new ++ env.consts⟩ → X ⟨new ++ env.consts⟩ →
      (∀ x, Own x → ∃ ci ∈ new, ci.name = keyOf t x ∧
        KeptIn t (storeOver E₀ R) (blobOver E₀ R) x ci) →
      (∀ ci ∈ new, (∃ x, Own x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s) →
      ∃ s', (familyFold.{u} X t E₀ R E lim rank fam twin adv).Inv s' ∧
        (∀ ci ∈ env.consts, ci ∈ s'.consts) ∧
        (∀ x, FamOwns E₀ fam A x → StoredAt t s' x) ∧
        (familyFold.{u} X t E₀ R E lim rank fam twin adv).Post A s' ∧
        ∀ x, StoredAt t s' x → StoredAt t env x ∨ FamOwns E₀ fam A x := by
    intro new Own hOwn hnd' hfresh' hinv' hX' hkept hnames
    have hgrow : Ix.Kernel.Grows (fun _ => True) env ⟨new ++ env.consts⟩ :=
      ⟨new, rfl, fun ci hci => ⟨trivial, hfresh' ci hci⟩, hnd'⟩
    have hprov : ∀ ci ∈ (claimedEnv ⟨new ++ env.consts⟩).consts,
        (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
          ∃ a, KeptIn t (storeOver E₀ R) (blobOver E₀ R) a ci := by
      intro ci hci
      obtain ⟨hmem, hkeep⟩ := List.mem_filter.mp hci
      rcases List.mem_append.mp hmem with hnew | hold
      · rcases hnames ci hnew with ⟨x, hx, hname⟩ | haux
        · obtain ⟨ci', hci', hname', hk⟩ := hkept x hx
          have hcc : ci' = ci := eq_of_name_eq hnd' hci' hnew (hname'.trans hname.symm)
          rw [hcc] at hk
          exact Or.inr (Or.inr ⟨x, hk⟩)
        · exact Or.inl (projInfo_of_aux haux (by simpa using hkeep))
      · exact hFI.prov ci (List.mem_filter.mpr ⟨hold, hkeep⟩)
    have hFI' : FoldInv.{u} X t E₀ R E lim ⟨new ++ env.consts⟩ :=
      ⟨hgrow.nodup hFI.nodup, hinv', hX', hprov⟩
    refine ⟨⟨new ++ env.consts⟩, hFI', fun ci hci => List.mem_append_right _ hci, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨ci, hci, hname, -⟩ := hkept x ((hOwn x).mpr hx)
      exact ⟨ci, List.mem_append_left _ hci, hname⟩
    · intro x hx
      obtain ⟨ci, hci, hname, hk⟩ := hkept x ((hOwn x).mpr hx)
      exact ⟨ci, List.mem_append_left _ hci, hname, hk⟩
    · intro x hx
      obtain ⟨ci, hci, hname⟩ := hx
      rcases List.mem_append.mp hci with hnew | hold
      · rcases hnames ci hnew with ⟨x', hx', hname'⟩ | ⟨k, s, haux⟩
        · have hxx : x = x' := keyOf_inj hroles (hname.symm.trans hname')
          rw [hxx]
          exact Or.inr ((hOwn x').mp hx')
        · exact absurd (hname.symm.trans haux) (keyOf_nonAux t x k s)
      · exact Or.inl ⟨ci, hold, hname⟩
  cases hfa : fam A with
  | none =>
    have hOwn : ∀ x, ConstAddrOf A c x ↔ FamOwns E₀ fam A x := by
      intro x
      constructor
      · intro hx
        exact ⟨c, hc, Or.inl hx⟩
      · rintro ⟨c', hc', hx | ⟨rb, crb, hrb, -⟩⟩
        · rw [hc] at hc'
          have hcc : c = c' := Option.some.inj hc'
          rw [hcc]
          exact hx
        · rw [hfa] at hrb
          cases hrb
    have hrefs : ∀ x, UsedRef E₀ A x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x := by
      intro x hused
      by_cases hok : NeedOk E₀ x
      · rcases hneed x (Or.inl (Or.inl ⟨Or.inl hused, hok⟩)) with hs | hown
        · exact Or.inl (find_isSome_of_storedAt hs)
        · exact Or.inr (Or.inl ((hOwn x).mpr hown))
      · exact Or.inr (Or.inr hok)
    have hfresh : ∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none :=
      fun x hx => find_none_of_not_storedAt (hfr x ((hOwn x).mp hx))
    have hstepped : ∃ new : List (ConstantInfo .anon),
        (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
        Decl.PrefixInv.{u} E t lim ⟨new ++ env.consts⟩ ∧ X ⟨new ++ env.consts⟩ ∧
        (∀ x, ConstAddrOf A c x →
          ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
        ∀ ci ∈ new, (∃ x, ConstAddrOf A c x ∧ ci.name = keyOf t x) ∨
          ∃ k s, ci.name = .aux k s := by
      cases htw : twin A with
      | none =>
        exact hstep A c hW hU hc hlog hkind hfa htw env hextT hFI.nodup hFI.inv hFI.extra
          hrefs hfresh
      | some B =>
        obtain ⟨rb, hrb, hne, -⟩ := hF.twinBlock A B htw
        obtain ⟨crb, rs, hR, -⟩ := hF.famRecord B rb hrb
        have hcanon : ∀ x, ConstAddrOf rb crb x → (env.find? (keyOf t x)).isSome = true := by
          intro x hx
          rcases hneed x (Or.inr ⟨B, rb, crb, htw, hrb, hR.record, hx⟩) with hs | hown
          · exact find_isSome_of_storedAt hs
          · exfalso
            exact hne (walked_eq_famRecord hG hF hW hc ((hOwn x).mpr hown) hrb hR.record hx)
        exact hstepTwin A c B rb crb hW hc hlog htw hrb hR.record env hextT hFI.nodup hFI.inv
          hFI.extra hrefs hcanon hfresh
    obtain ⟨new, hnd', hfresh', hinv', hX', hreads, hnames⟩ := hstepped
    obtain ⟨s', h1, h2, h3, h4, h5⟩ := hfinish new (ConstAddrOf A c) hOwn hnd' hfresh' hinv' hX'
      (fun x hx => by
        obtain ⟨ci, hci, ci₀, hname, hr, hst⟩ := hreads x hx
        exact ⟨ci, hci, hname, kept_of_reads_run hr hst (hnaxA x hx)⟩)
      hnames
    exact ⟨s', h1, h2, h3, h4, h5⟩
  | some rb =>
    obtain ⟨crb, rs, hR, -⟩ := hF.famRecord A rb hfa
    have hOwn : ∀ x, FamAddr A c rb crb x ↔ FamOwns E₀ fam A x := by
      intro x
      constructor
      · rintro (hx | hx)
        · exact ⟨c, hc, Or.inl hx⟩
        · exact ⟨c, hc, Or.inr ⟨rb, crb, hfa, hR.record, hx⟩⟩
      · rintro ⟨c', hc', hx | ⟨rb', crb', hrb', hcrb', hx⟩⟩
        · rw [hc] at hc'
          have hcc : c = c' := Option.some.inj hc'
          rw [hcc]
          exact Or.inl hx
        · rw [hfa] at hrb'
          have hrr : rb = rb' := Option.some.inj hrb'
          subst hrr
          have hcc : crb = crb' := Option.some.inj (hR.record.symm.trans hcrb')
          subst hcc
          exact Or.inr hx
    have hrefs : ∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
        (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x := by
      intro x hused
      by_cases hok : NeedOk E₀ x
      · have hn : FamNeeds E₀ fam adv A x := by
          refine Or.inl ⟨?_, hok⟩
          rcases hused with h | h
          · exact Or.inl h
          · exact Or.inr ⟨rb, hfa, h⟩
        rcases hneed x (Or.inl hn) with hs | hown
        · exact Or.inl (find_isSome_of_storedAt hs)
        · exact Or.inr (Or.inl ((hOwn x).mpr hown))
      · exact Or.inr (Or.inr hok)
    have hadv : ∀ a, adv A a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
        (env.find? (keyOf t x)).isSome = true := by
      intro a ha ca hca x hxa
      rcases hneed x (Or.inl (Or.inr ⟨a, ca, ha, hca, hxa⟩)) with hs | hown
      · exact find_isSome_of_storedAt hs
      · by_cases hstT : StoredAt t envT x
        · obtain ⟨ci, hci, hname⟩ := hstT
          exact find_isSome_of_storedAt ⟨ci, hextT ci hci, hname⟩
        · exfalso
          obtain ⟨hWa, hUa, hrk, hloga⟩ := hF.advEarlier A a ha
          have haU : a ∈ us := (hus a).mpr ⟨hWa, hUa, ca, hca, hloga ca hca, x, hxa, hstT⟩
          have hAa : a = A :=
            owns_apart_family.{u} (X := X) (R := R) (E := E) (lim := lim) hG hF hus
              a haU A hA x ⟨ca, hca, Or.inl hxa⟩ hown
          rw [hAa] at hrk
          exact Nat.lt_irrefl _ hrk
    have hfresh : ∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none :=
      fun x hx => find_none_of_not_storedAt (hfr x ((hOwn x).mp hx))
    obtain ⟨new, hnd', hfresh', hinv', hX', hreads, hnames⟩ :=
      hstepFam A c rb crb rs (hF.famBlock A rb hfa) hc hlog hkind hfa hR env hextT hFI.nodup
        hFI.inv hFI.extra hrefs hadv hfresh
    have hnax : ∀ x, FamAddr A c rb crb x → ∀ c' ax, recordOf E₀ x = some c' →
        c'.info = .axio ax → False := by
      rintro x (hx | hx) c' ax hc' hinfo
      · exact hnaxA x hx c' ax hc' hinfo
      · obtain ⟨P, hP, hPp, -⟩ := hR.constAddr hx
        rw [hP] at hc'
        have hcc : P = c' := Option.some.inj hc'
        rw [← hcc] at hinfo
        rcases hPp with ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ <;> (rw [h] at hinfo; cases hinfo)
    obtain ⟨s', h1, h2, h3, h4, h5⟩ := hfinish new (FamAddr A c rb crb) hOwn hnd' hfresh'
      hinv' hX'
      (fun x hx => by
        obtain ⟨ci, hci, ci₀, hname, hr, hst⟩ := hreads x hx
        exact ⟨ci, hci, hname, kept_of_reads_run hr hst (hnax x hx)⟩)
      hnames
    exact ⟨s', h1, h2, h3, h4, h5⟩

end Fold

/-! ## Top-walked blocks of recursors -/

/-- **Every top-walked non-empty block of recursors is a block's family record or a twin.** The
circuit accepts such a record only through the family check of a mutual or nested block. With
it, no top-walked block of recursors is a plain unit (`no_plain_recursorBlock`). -/
def RecursorBlocksClaimed (E₀ : Ixon.Env) (Top : _root_.Address → Prop)
    (fam twin : _root_.Address → Option _root_.Address) : Prop :=
  ∀ (A : _root_.Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst), Top A →
    recordOf E₀ A = some c → c.info = .muts ms → 0 < ms.size →
    (∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r) →
    (∃ B, fam B = some A) ∨ ∃ B, twin A = some B

/-- An unclaimed top-walked non-empty block of recursors that is no twin does not exist. -/
theorem no_plain_recursorBlock {E₀ : Ixon.Env} {Top : _root_.Address → Prop}
    {fam twin : _root_.Address → Option _root_.Address}
    (h : RecursorBlocksClaimed E₀ Top fam twin) {A : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hT : Top A) (hc : recordOf E₀ A = some c)
    (hms : c.info = .muts ms) (hne : 0 < ms.size)
    (hrec : ∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r) (hU : Unclaimed fam A)
    (htw : twin A = none) : False := by
  rcases h A c ms hT hc hms hne hrec with ⟨B, hB⟩ | ⟨B, hB⟩
  · exact hU B hB
  · rw [htw] at hB
    cases hB

/-! ## The skeleton -/

section Skeleton

variable {t : Ix.Kernel.RoleTable} {R E₀ : Ixon.Env} {envT : Ix.Kernel.Env .anon}
  {seeds : List _root_.Address} {calls : List (Call F)}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}

/-- **The typing conclusion from the walk, the family graph and the steps**, with a
store-relative extra clause and the witness's prefix invariant at the walk's limit only, where
the run hashed no collision: `typing_skeleton_core_lim` over `familyFold`. A top-walked unit
with no family record that is no twin is stepped by `UnitStep`, as is a unit checked inside a
family check; a block with a family record by `UnitStepFam`; a twin by `UnitStepTwin`. -/
theorem typing_skeleton_core_family {V : View} {extra : List ByteArray}
    {X : Ixon.Env → Ix.Kernel.Env .anon → Prop} {lim : Option Nat}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hinvL : ∀ E, RecordsFor R E → Decl.PrefixInv.{u} E t lim envT)
    (hwholeL : ∀ E, RecordsFor R E →
      ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
        (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
        Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb →
        cb.info = .muts ms → BlockStored t envT B ms)
    (hX : ∀ E, RecordsFor R E → X E envT)
    (ht : t.check = .ok ())
    (hb : Bounded calls) (hextra : ∀ x ∈ committedFootprint, x ∈ extra)
    (hnc : ¬ CollisionWith V extra R calls) (hS : LoadedReads.RunStore calls E₀)
    (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hstepTop : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Top A → Unclaimed fam A →
      recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
      UnitStep.{u} (X E) t envT E₀ E lim A c)
    (hstepInner : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
      recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
      UnitStep.{u} (X E) t envT E₀ E lim A c)
    (hstepFam : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c rb crb rs, Top A →
      recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = some rb →
      FamRecRecord E₀ rb crb rs → UnitStepFam.{u} (X E) t envT E₀ E lim A c rb crb (adv A))
    (hstepTwin : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c B rb crb, Walked Top Inner A →
      recordOf E₀ A = some c → InLogic c → twin A = some B → fam B = some rb →
      recordOf E₀ rb = some crb → UnitStepTwin.{u} (X E) t envT E₀ E lim A c rb crb) :
    ConsistentReadOver.{u} calls t R envT seeds := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hload : LoadedBy calls E₀ := hS.loaded
  have hdec : L1.EnvDecoded E₀ := hS.decoded
  obtain ⟨E, hM⟩ := merged_exists E₀ R
  have hrf : RecordsFor R E := hM.recordsFor hload hdec hshape.committed hextra hnc
  have hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c :=
    fun a c h => hM.run_record hload hdec hextra hnc h
  have hctx : StepCtx.{u} calls t R envT E₀ E :=
    ⟨hshape, hrf, hrun, fun a b h => hM.run_blob hload hnc h,
      fun env lim => hM.good hload hshape.zeroFree hextra hnc hb env t lim⟩
  have hrec := records_agree hload hnc
  have hblob := blobs_agree hload hnc
  have hinvT : Decl.PrefixInv.{u} E t lim envT := hinvL E hrf
  have hwhole := hwholeL E hrf
  obtain ⟨us, hus⟩ := exists_list_of_records E₀ (IsUnit t envT E₀ Top Inner fam)
    (fun A hA => by
      obtain ⟨-, -, c, hc, -⟩ := hA
      exact ⟨c, hc⟩)
  have h₀ : FoldInv.{u} (X E) t E₀ R E lim envT :=
    ⟨hshape.reading.nodup, hinvT, hX E hrf,
      provenance_over_witness hrec hblob hshape.reading.provenance⟩
  have hstep : ∀ A c, Walked Top Inner A → Unclaimed fam A → recordOf E₀ A = some c →
      InLogic c → UnitKind c → fam A = none → twin A = none →
      UnitStep.{u} (X E) t envT E₀ E lim A c := by
    intro A c hW hU hc hlog hkind hfa htw
    rcases hW with hT | hI
    · exact hstepTop E hctx A c hT hU hc hlog hkind hfa htw
    · exact hstepInner E hctx A c hI hU hc hlog hkind hfa htw
  obtain ⟨env, hinv, hext, hdone, -⟩ :=
    (familyFold.{u} (X E) t E₀ R E lim rank fam twin adv).run h₀
      (owns_apart_family hG hF hus) (fresh_at_family hG hF hwhole hrun hus)
      (needs_earlier_family hG hF hshape htwf hus)
      (fold_steps_family hG hF hshape htwf hroles hwhole hrun hus hstep
        (hstepFam E hctx) (hstepTwin E hctx))
  have hFI : FoldInv.{u} (X E) t E₀ R E lim env := hinv
  have hextT : ∀ ci ∈ envT.consts, ci ∈ env.consts := hext
  refine ⟨E₀, env, hload, hFI.nodup, hextT, hFI.prov, ?_,
    claimedEnv_models_of_prefixInv hFI.inv hFI.nodup hFI.prov⟩
  intro a ha a' hsc
  have hTa := hG.seedsTop a ha
  obtain ⟨c, hc⟩ := hG.record a hTa
  obtain ⟨hlogc, hlogB⟩ := hG.seedLogic a ha c hc
  by_cases hst : StoredAt t envT a'
  · obtain ⟨ci, hci, hname⟩ := hst
    have hfT := find_of_mem_nodup hshape.reading.nodup hci
    rw [hname] at hfT
    have hf := find_of_mem_nodup hFI.nodup (hextT ci hci)
    rw [hname] at hf
    exact ⟨ci, hf, stored_provenance hroles hrec hblob hshape.reading.provenance hfT⟩
  · have hown : ∃ b ∈ us, FamOwns E₀ fam b a' := by
      rcases hsc with ⟨haa, hnm⟩ | ⟨c', ms, i, m, hc', hms, hm, hx⟩
      · rw [haa] at hst
        rw [haa]
        rcases kind_cases c with hsa | hpr | hbl
        · exact owner_of_top_const hG hF hus hTa hc hlogc (Or.inl ⟨rfl, hsa⟩) hst
        · obtain ⟨hTB, -⟩ := hG.owner a c hTa hc hpr
          obtain ⟨cb, hcb, hconst⟩ := hG.projMember a c hTa hc hpr
          exact owner_of_top_const hG hF hus hTB hcb (hlogB cb hcb) hconst hst
        · obtain ⟨ms, hms⟩ := hbl
          exact absurd hms (hnm c ms hc)
      · rw [hc] at hc'
        have hcc : c = c' := Option.some.inj hc'
        rw [← hcc] at hms
        exact owner_of_top_const hG hF hus hTa hc hlogc (Or.inr ⟨ms, i, m, hms, hm, hx⟩) hst
    obtain ⟨b, hb, hbo⟩ := hown
    obtain ⟨ci, hci, hname, hk⟩ := (hdone b hb).2 a' hbo
    have hf := find_of_mem_nodup hFI.nodup hci
    rw [hname] at hf
    exact ⟨ci, hf, Or.inr hk⟩

end Skeleton

end IxVM.Refinement.Typing
