module

public import ConLeche.Semantics.DeclRun

@[expose] public section

/-!
# `declEtaStep` — the declaration fold's η-closure half, model-free
(task #161 S3, THE SEPARATION; the design census's **C4**)

The P fold (`Interp/FoldP.lean`) used to run the *entire* v1
declaration fold — `declStepS`, with its five install obligations and
an `EnvS` at the prefix environment — and keep only the second
component, `EtaFamiliesClosed env₂`.  The census sized the extraction
of that component at "≈60 lines, six branches, no `V`, no `EnvS`",
reading `declStepS`'s own per-kind proofs.

**That sizing is REFUTED at one kind, and the refutation is recorded
here** (restrictions-are-findings).  Five of the six kinds are exactly
as the census read them — the η-closure follows from `DeclR`'s `find?`
freshness guard and the cons's kind, by `EtaFamiliesClosed.cons_nonind`
(and, at `basisDecl`, by `basisInstallRun_etaClosed`, which is itself
model-free).  The sixth, `indDecl`, is **not**: `declStepS`'s ind
branch takes its η-closure from `hind m hE h` — the `DeclIndS`
obligation — and that obligation's own discharge (`Install/DeclIndS.lean`)
reads `hEC₁`/`hBP₁` off `indMembersS` and `hnonrecUp` off `indRecsS`,
both **model-carrying** installs.  The facts themselves are
relation-level (`EtaFamiliesClosedO.cons` at a fresh member, the
`indMembersR_*`/`indRecsR_*` inversions), but they are proved
*interleaved* with the `EnvS` fold, so extracting them means re-running
two ~800-line inductions η-only.

So `declEtaStep` is stated with the ind kind's η-closure as its one
premise, at the *fixed* environment and valuation the fold is at.
That is the honest decomposition: it removes the P fold's dependence
on `divModPinS`, `reducePinS`, `stdAxiomKeyS` and `declBasisS`
outright, and it names what remains as exactly one obligation whose
model-freeing is S4/S5's measurable bill.

This module is model-free by construction: no `V`, no `SetTheory`, no
`EnvS`.  It sits in the R tree only because `DeclR` does; when
`SetR/Decl.lean` moves to the shared base (S2's finding 2 removed its
blocker), this file moves with it.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- Does every pinned basis declaration that is an eta-capable
former carry a reserved name?  Decidable, and `decide`d at each
kind — the basis blocks are literal lists. -/
def basisIndOk (l : List ConstantInfo) : Bool :=
  l.all (fun ci => match ci with
    | .indInfo _ caps => !caps.eta || reservedBasisNames.contains ci.name
    | _ => true)

/-- `basisIndOk` at one member. -/
theorem basisIndOk_mem {l : List ConstantInfo} (h : basisIndOk l = true)
    {ci : ConstantInfo} (hci : ci ∈ l) {cv : ConstantVal}
    {caps : IndCaps} (heq : ci = .indInfo cv caps)
    (hcape : caps.eta = true) :
    reservedBasisNames.contains ci.name = true := by
  have hm := List.all_eq_true.mp h ci hci
  rw [heq] at hm ⊢
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hm
  rcases hm with hm | hm
  · rw [hcape] at hm; exact nomatch hm
  · exact hm

/-- The pinned basis fold keeps the stored eta families closed: every
pinned former it stores carries a reserved name. -/
theorem basisInstallRun_etaClosed :
    ∀ (l : List ConstantInfo) {env env₂ : Env},
      BasisInstallRun env l env₂ → basisIndOk l = true →
      EtaFamiliesClosed env → EtaFamiliesClosed env₂
  | [], _, _, h, _, hE => by rw [h]; exact hE
  | ci :: rest, env, env₂, h, hok, hE => by
    obtain ⟨hfresh, htail⟩ := h
    refine basisInstallRun_etaClosed rest htail ?_ ?_
    · have := List.all_eq_true.mp hok
      exact List.all_eq_true.mpr fun x hx =>
        this x (List.mem_cons_of_mem _ hx)
    · exact EtaFamiliesClosed.cons_nonind hE
        (Option.isNone_iff_eq_none.mp hfresh)
        (fun cv caps heq hcape =>
          basisIndOk_mem hok List.mem_cons_self heq hcape)

/-- Every pinned basis block passes the former check, by computation. -/
theorem basisIndOk_declsA (kind : BasisKind) :
    basisIndOk kind.declsA = true := by
  cases kind <;> decide

/-- **The declaration fold's η-closure half, on the run projection**
(task #161 S4).  The proof never looked at a derivation conjunct — it
reads `ConstantValR`'s freshness guard and the kinds' cons shapes and
nothing else — so it is stated over `DeclRun` (`SetBase/DeclRun.lean`)
and `declEtaStep` below is its `DeclR` instance.  This is what lets the
P fold take its η half from a valuation-free record.

The inductive kind is `DeclRun`'s `Ind` parameter here, so the one
premise is at whatever payload the caller instantiates — today
`DeclIndRun`, after S5's ind unit `DeclIndRun`. -/
theorem declEtaStepRun {μ : CheckMode} {F : Nat}
    {Ind : List ConstantInfo → Nat → Env → Prop}
    {env : Env} {d : Declaration} {env₂ : Env}
    (hind : ∀ {block : List ConstantInfo} {nP : Nat} {envI : Env},
      Ind block nP envI → EtaFamiliesClosed envI)
    (hE : EtaFamiliesClosed env)
    (h : DeclRun μ F Ind env d env₂) : EtaFamiliesClosed env₂ := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl, -⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | axiomDecl cv =>
    -- the `Quot.sound` arm (task #293) installs nothing
    rcases h with ⟨-, rfl⟩ | h
    · exact hE
    obtain ⟨type', hcv, harm⟩ := h
    have hfresh : env.find? cv.name = none :=
      Option.isNone_iff_eq_none.mp hcv.1
    rcases harm with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ |
      ⟨-, -, -, -, -, -, -, rfl⟩
    · exact EtaFamiliesClosed.cons_nonind hE hfresh
        (fun _ _ heq => nomatch heq)
    · exact EtaFamiliesClosed.cons_nonind hE hfresh
        (fun _ _ heq => nomatch heq)
    · exact EtaFamiliesClosed.cons_nonind hE hfresh
        (fun _ _ heq => nomatch heq)
    · exact hE
  | basisDecl kind =>
    exact basisInstallRun_etaClosed kind.declsA h.2
      (basisIndOk_declsA kind) hE
  | quotDecl k cv =>
    -- the quotient package's `type` record installs the pinned block;
    -- its other records install nothing (task #293)
    cases k with
    | type => exact basisInstallRun_etaClosed _ h.2 (basisIndOk_declsA .quotK) hE
    | _ => exact (show env₂ = env from h) ▸ hE
  | indDecl block nP =>
    -- a block the fold recognises as a pinned one installs the pin
    -- (task #293)
    simp only [DeclRun] at h
    split at h
    · exact basisInstallRun_etaClosed _ h.2 (basisIndOk_declsA _) hE
    · exact hind h

/-! `declEtaStep` — the `DeclR` instance — moved to
`SetBase/DeclStructEta.lean` at task #175 wiring W5, where the
`.indDecl` dispatch's η half is proved for BOTH arms and the instance
reads the kernel's own case split instead of the flag. -/

end ConLeche.Semantics
