import IxCCCorrect.ComposeExe
import IxCCCorrect.Shape2Check
import IxCCCorrect.Shape2Produce

/-!
# The escape-free composition (`IxCCCorrect.GroundShape`)

`IxCCCorrect.Compose` and `IxCCCorrect.ComposeExe` prove "the object computes the kernel meaning"
under two facts about SrcEval: `NeverWrong` (the viewed source is never stuck, never traps, and
returns only values the root's view reads back) and `ReturnsCanon` (what it returns at root 0 is a
canonical form of the root's first-order result type). The shape discipline of milestone M2
(`IxCCCorrect.Shape2`, `IxCCCorrect.Shape2Check`) proves both from a decision, `certOk`, on a
certificate an untrusted producer proposes: `run_ok` gives a value of the root's result shape,
`ValOk.nat_inv` / `ValOk.enum_inv` make it a canonical form, and `neverWrong_of_cert_nat` /
`neverWrong_of_cert_enum` give `NeverWrong`. This module decides both checks together and drops
the two hypotheses:

```lean
groundShapeCheck (inp : Recheck.Input) (c : Recheck.Cert) (a : Recheck.Artifact)
    (sc : Shape2.Cert) (target : Ixon.Address) : Except String Abi

groundShapeCheck_sound : groundShapeCheck inp c a sc target = .ok abi →
  GroundShapeOk inp.kernel.acc a target abi   -- GroundOk, and NeverWrong and ReturnsCanon
                                              -- on every input of the claim's arity

recheck_agrees_shaped : Recheck.run cfg P c = .ok a →
  groundShapeCheck inp c a sc claim.target = .ok claim.abi → D.Ok … →
  ns.length = claim.abi.arity → a.front.Covered c (0, ns) →
  Lang.run (a.linked D) (0, ns) k = .ok (some o) →
  ∃ answer, o = abiObs claim.abi answer ∧ Agrees claim inp.kernel.acc ns answer

plain_exe_tier1Stdout_shaped : Recheck.run cfg P c = .ok a → Exe.build a layout = .ok ⟨inp', ce⟩ →
  groundShapeCheck inp c a sc claim.target = .ok claim.abi →
  Tier1Stdout claim inp.kernel.acc ce.bytes

tier1Check_sound : Recheck.ingress envBytes equations roots claim.kernelLimits = .ok inp →
  Recheck.run cfg P c = .ok a → Exe.build a layout = .ok ⟨inp', ce⟩ →
  tier1Check claim inp c a sc = true →
  ∃ acc, Admits claim envBytes acc ∧ Tier1Stdout claim acc ce.bytes
```

No source evaluator, no "source goes wrong" and no hypothesis about SrcEval remains: every
premise is a function the checker runs (`Recheck.ingress`, `Recheck.run`, `Exe.build`,
`tier1Check`). What is left of `Tier1` is the shipped-file link (`LoadedFile exe`, `FileTrace
exe` for the core `ce.bytes`, another lane's) and its second clause (a trace that exits with
status 0 wrote the whole rendering), both stated in `IxCCCorrect.ComposeExe`.

**The certificate is not trusted.** `sc` is any shape certificate; `groundShapeCheckP` takes the
one the untrusted producer proposes (`Shape2.Produce.produce`). The theorems hold for every `sc`.

**The shape side** (`shapeRootB`): the certificate lists the instance `Nat → … → Nat → res` for
root 0's constant, at the root's declared arity and at the first-order result type the grounding
check read (`resTy`); at a `Nat` result the compiler reads the root back as `Nat`
(`Recheck.resultTy`); at an enumeration result the certificate lists the enumeration. At an
enumeration result the view's acceptance of every listed constructor, which
`neverWrong_of_cert_enum` needs, is what `groundCheck`'s result part already established (G5).
These are the conditions of `ShapeHook.natRootOk` / `enumRootOk` (branch `ixcc2/source-progress`)
with the enumeration tied to the declared result type, so `runShaped`'s acceptance gives the shape
side once that hook is integrated.
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.Src (Value Slot Term CId Program Levels)
open IxCC.Sem (Obs Lang Result)
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.Grounding (FoTy)

universe u

/-! ## The shape side -/

/-- **The shape side of the check** at root `root` of `n` parameters and first-order result type
`res` (see the module note). -/
def shapeRootB (src : Program) (sc : Shape2.Cert) (root : CId) (n : Nat) : FoTy → Bool
  | .nat =>
    decide ((root, ([] : Levels), Shape2.arrows (List.replicate n .nat) .nat) ∈ sc.insts) &&
      decide (Recheck.resultTy src root = some .nat)
  | .enum D =>
    decide ((root, ([] : Levels), Shape2.arrows (List.replicate n .nat) (.enum D)) ∈ sc.insts) &&
      (Shape2.lookupEnum sc.enums D).isSome

/-- **SrcEval returns canonical forms, from the shape check.** A certificate that passes `certOk`
and lists root 0's instance at its result type: whatever SrcEval returns at root 0 on literals is a
literal (at `Nat`) or a field-less value of a constructor the program declares for the result
enumeration (`run_ok`, `ValOk.nat_inv`, `ValOk.enum_inv`, `SigOk.enums`). -/
theorem returnsCanon_of_shape {src : Program} {sc : Shape2.Cert}
    (hc : Shape2.certOk src sc = true) {addr : Ixon.Address} {root : CId} {res : FoTy}
    (hroot : src.roots.head? = some (addr, root)) (hres : resTy src root = some res)
    {ns : List Nat} (hs : shapeRootB src sc root ns.length res = true) :
    ReturnsCanon src ns := by
  intro addr' root' k v hroot' hrun
  have hrr : root' = root := (Prod.mk.inj (Option.some.inj (hroot'.symm.trans hroot))).2
  rw [hrr] at hrun ⊢
  have hsig := Shape2.sigOk_of_cert hc
  refine ⟨res, hres, ?_⟩
  cases res with
  | nat =>
    simp only [shapeRootB, Bool.and_eq_true, decide_eq_true_eq] at hs
    rcases Shape2.run_ok hsig ns hs.1 k with h | ⟨w, h, hw⟩
    · rw [hrun] at h
      cases h
    · rw [hrun] at h
      cases h
      exact hw.nat_inv
  | enum D =>
    simp only [shapeRootB, Bool.and_eq_true, decide_eq_true_eq] at hs
    rcases Shape2.run_ok hsig ns hs.1 k with h | ⟨w, h, hw⟩
    · rw [hrun] at h
      cases h
    · rw [hrun] at h
      cases h
      obtain ⟨c, ls, cs, rfl, hI, hcm⟩ := hw.enum_inv
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hcm
      obtain ⟨s, lv, ty, hd, -, -⟩ := hsig.enums D cs hI i c hi
      exact ⟨c, ls, [], s, lv, i, ty, rfl, hd⟩

/-- **The viewed source is never wrong, from the two checks.** At a `Nat` result by
`neverWrong_of_cert_nat`; at an enumeration result by `neverWrong_of_cert_enum`, whose premise
(every listed constructor is level-monomorphic and read back by the root's view) is `groundCheck`'s
result part at the constructors `SigOk.enums` says the listed ones are. -/
theorem neverWrong_of_groundShape {acc : Src.KernelFront.Accepted} {a : Recheck.Artifact}
    {target : Ixon.Address} {abi : Abi}
    (hok : GroundOk acc a.src (Lam.Erase.Input.ofProgram a.src a.checked) (a.front.view 0) target
      abi)
    {sc : Shape2.Cert} (hc : Shape2.certOk a.src sc = true) {root : CId} {res : FoTy}
    (hroot : a.src.roots.head? = some (target, root)) (hres : resTy a.src root = some res)
    {ns : List Nat} (hs : shapeRootB a.src sc root ns.length res = true) :
    NeverWrong a.front.source (0, ns) := by
  have hroot0 : a.front.src.roots[0]? = some (target, root) := by
    rw [← List.head?_eq_getElem?]
    exact hroot
  cases res with
  | nat =>
    simp only [shapeRootB, Bool.and_eq_true, decide_eq_true_eq] at hs
    have h2 : Recheck.resultTy a.front.src root = some .nat := hs.2
    have hty : a.front.tys 0 = some ({}, .nat) := by
      simp [Recheck.Front.tys, hroot0, Recheck.rootTy, h2]
    exact Shape2.neverWrong_of_cert_nat (f := a.front) hc hroot0 ns hs.1 (.inr hty)
  | enum D =>
    simp only [shapeRootB, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨hinst, hB⟩ := hs
    obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 hB
    have hsig := Shape2.sigOk_of_cert hc
    obtain ⟨κ, lpsOf, ann, Sl, Inst, root', res', hroot', hres', -, -, -, hRes⟩ := hok
    have hrr : root' = root := (Prod.mk.inj (Option.some.inj (hroot'.symm.trans hroot))).2
    rw [hrr, hres] at hres'
    have hD : FoTy.enum D = res' := Option.some.inj hres'
    subst hD
    obtain ⟨addrs, -, -, hall⟩ := hRes
    refine Shape2.neverWrong_of_cert_enum (f := a.front) hc hroot0 ns hinst hcs ?_
    intro c' hc'
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc'
    obtain ⟨s, lv, ty, hd, -, -⟩ := hsig.enums D cs hcs i c' hi
    obtain ⟨hl, t, hv, -, -⟩ := hall c' s lv i ty hd
    refine ⟨hl, ?_⟩
    have hv' : a.front.view 0 (obsOf (Lam.Erase.Input.ofProgram a.src a.checked)
        (.con c' [] [] [])) = some (some (.ctor t [])) := hv
    show a.front.view 0 (obsOf (Lam.Erase.Input.ofProgram a.src a.checked) (.con c' [] [] [])) ≠
      none
    rw [hv']
    exact Option.some_ne_none _

/-! ## The combined check -/

/-- **The pipeline check with the shape check**: `groundCheck` on what the certificate checker
checked (`groundCheckRecheck`), then `certOk` on the checked source and the shape side at root 0.
`.ok abi`: the calling convention `groundCheck` validated. -/
def groundShapeCheck (inp : Recheck.Input) (c : Recheck.Cert) (a : Recheck.Artifact)
    (sc : Shape2.Cert) (target : Ixon.Address) : Except String Abi :=
  match groundCheckRecheck inp c a target with
  | .error e => .error e
  | .ok abi =>
    match a.src.roots.head? with
    | none => .error "noRoot"
    | some (_, root) =>
      match resTy a.src root with
      | none => .error "resultType"
      | some res =>
        if Shape2.certOk a.src sc then
          if shapeRootB a.src sc root (arityOf a.src root) res then .ok abi
          else .error "shape: the certificate does not list root 0 at its first-order type"
        else .error "shape: certOk refused the certificate"

/-- The same, with the certificate the untrusted producer proposes for root 0 (at most 4000
steps; a certificate of 4000 instances or more is refused unchecked: the producer's instance list
is quadratic, and `Closures.polyRec` does not converge). -/
def groundShapeCheckP (inp : Recheck.Input) (c : Recheck.Cert) (a : Recheck.Artifact)
    (target : Ixon.Address) : Except String Abi :=
  match a.src.roots.head? with
  | none => .error "noRoot"
  | some (_, root) =>
    let sc := Shape2.Produce.produce a.src root 400 4000
    if sc.insts.length < 4000 then groundShapeCheck inp c a sc target
    else .error "shape: the producer did not converge (4000 instances)"

/-- **What the combined check establishes**: `groundCheck`'s `GroundOk`, and on every input of the
claim's arity the two facts about SrcEval the composed theorems take as hypotheses. -/
structure GroundShapeOk (acc : Src.KernelFront.Accepted) (a : Recheck.Artifact)
    (target : Ixon.Address) (abi : Abi) : Prop where
  ground : GroundOk acc a.src (Lam.Erase.Input.ofProgram a.src a.checked) (a.front.view 0) target
    abi
  neverWrong : ∀ ns : List Nat, ns.length = abi.arity → NeverWrong a.front.source (0, ns)
  canon : ∀ ns : List Nat, ns.length = abi.arity → ReturnsCanon a.src ns

/-- **The combined check is sound.** -/
theorem groundShapeCheck_sound {inp : Recheck.Input} {c : Recheck.Cert} {a : Recheck.Artifact}
    {sc : Shape2.Cert} {target : Ixon.Address} {abi : Abi}
    (h : groundShapeCheck inp c a sc target = .ok abi) :
    GroundShapeOk inp.kernel.acc a target abi := by
  unfold groundShapeCheck at h
  cases hg : groundCheckRecheck inp c a target with
  | error e => rw [hg] at h; cases h
  | ok abi' =>
    rw [hg] at h
    dsimp only at h
    have hok := groundCheckRecheck_sound hg
    cases hr : a.src.roots.head? with
    | none => rw [hr] at h; cases h
    | some ar =>
      obtain ⟨addr, root⟩ := ar
      rw [hr] at h
      dsimp only at h
      cases hres : resTy a.src root with
      | none => rw [hres] at h; cases h
      | some res =>
        rw [hres] at h
        dsimp only at h
        split at h
        · rename_i hc
          split at h
          · rename_i hs
            simp only [Except.ok.injEq] at h
            rw [← h]
            -- the root and the arity `GroundOk` read
            have hok0 := hok
            obtain ⟨κ, lpsOf, ann, Sl, Inst, root', res', hroot', -, -, hparams, -, -⟩ := hok0
            have hrr := Prod.mk.inj (Option.some.inj (hroot'.symm.trans hr))
            rw [hrr.2] at hparams
            have hr' : a.src.roots.head? = some (target, root) := by rw [hrr.1]; exact hr
            have harity : ∀ ns : List Nat, ns.length = abi'.arity →
                ns.length = arityOf a.src root := by
              intro ns hns
              rw [hns]
              simp [Abi.arity, hparams]
            refine ⟨hok, fun ns hns => ?_, fun ns hns => ?_⟩
            · have hs' : shapeRootB a.src sc root ns.length res = true := by
                rw [harity ns hns]; exact hs
              exact neverWrong_of_groundShape hok hc hr' hres hs'
            · have hs' : shapeRootB a.src sc root ns.length res = true := by
                rw [harity ns hns]; exact hs
              exact returnsCanon_of_shape hc hr' hres hs'
          · cases h
        · cases h

/-- The producer's variant is sound too: its certificate is only checked. -/
theorem groundShapeCheckP_sound {inp : Recheck.Input} {c : Recheck.Cert} {a : Recheck.Artifact}
    {target : Ixon.Address} {abi : Abi} (h : groundShapeCheckP inp c a target = .ok abi) :
    GroundShapeOk inp.kernel.acc a target abi := by
  unfold groundShapeCheckP at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · exact groundShapeCheck_sound h
    · cases h

/-! ## The escape-free theorems -/

/-- **The compiled object computes the kernel meaning, with no hypothesis about the source**
(immortal and zero-RC objects). For a program the certificate checker accepted and the combined
check accepted at the claim's target and calling convention: on every covered input of the claim's
arity, an observation the linked object returns for root 0 is an answer that agrees with the kernel
meaning of the claimed address. -/
theorem recheck_agrees_shaped {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a) {inp : Recheck.Input}
    {sc : Shape2.Cert} {claim : Claim}
    (hg : groundShapeCheck inp c a sc claim.target = .ok claim.abi)
    (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size) {ns : List Nat}
    (hlen : ns.length = claim.abi.arity) (hi : a.front.Covered c (0, ns))
    {k : Nat} {o : Obs} (hw : Lang.run (a.linked D) (0, ns) k = .ok (some o)) :
    ∃ answer, o = abiObs claim.abi answer ∧ Agrees.{u} claim inp.kernel.acc ns answer := by
  have hs := groundShapeCheck_sound hg
  exact recheck_agrees h hs.ground hlen (hs.neverWrong ns hlen) (hs.canon ns hlen) D hD hi hw

/-- **What the plain executable prints agrees with the kernel meaning, with no hypothesis about
the source** (immortal and zero-RC objects): the first clause of `Tier1` for the checked core
`ce.bytes`, over every invocation, loader state and finite trace. -/
theorem plain_exe_tier1Stdout_shaped {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {a : Recheck.Artifact} (h : Recheck.run cfg P c = .ok a)
    {layout : X86.Exe.Layout} {inp' : X86.Exe.Input} {ce : X86.Exe.Certified inp'}
    (hb : IxCC.Exe.build a layout = .ok ⟨inp', ce⟩) {inp : Recheck.Input} {sc : Shape2.Cert}
    {claim : Claim} (hg : groundShapeCheck inp c a sc claim.target = .ok claim.abi) :
    Tier1Stdout.{u} claim inp.kernel.acc ce.bytes := by
  have hs := groundShapeCheck_sound hg
  have harity := recheck_arity h hb hs.ground
  exact plain_exe_tier1Stdout h hb hs.ground harity
    (fun ns hns => hs.neverWrong ns (hns.trans harity.symm))
    (fun ns hns => hs.canon ns (hns.trans harity.symm))

/-- What `groundCheck` accepted resolves at the reader: the target has a key (`Admits`, P4). -/
theorem GroundOk.target_key {acc : Src.KernelFront.Accepted} {src : Program} {I : Lam.Erase.Input}
    {view : View} {target : Ixon.Address} {abi : Abi} (h : GroundOk acc src I view target abi) :
    keyOf acc target ≠ none := by
  obtain ⟨κ, -, -, -, -, root, -, -, -, hk, -⟩ := h
  rw [hk]
  exact Option.some_ne_none _

/-! ## The check a `compile` calls, and the theorem about it -/

/-- **The tier-1 check**: the committed environment the checker ingested has the claim's root and
role table, and the combined check accepts the claim's target at the claim's calling convention. -/
def tier1Check (claim : Claim) (inp : Recheck.Input) (c : Recheck.Cert) (a : Recheck.Artifact)
    (sc : Shape2.Cert) : Bool :=
  decide (inp.env.root = claim.env) && decide (inp.env.bindingAddress = some claim.roleTable) &&
    match groundShapeCheck inp c a sc claim.target with
    | .ok abi => decide (abi = claim.abi)
    | .error _ => false

/-- **The tier-1 check is sound**: if ingress accepted the committed environment at the claim's
limits, the certificate checker and the executable writer accepted, and `tier1Check` returned
`true`, then the kernel admits the committed environment and what the checked core prints agrees
with the kernel meaning of the claimed address (the first clause of `Tier1`, for `ce.bytes`). -/
theorem tier1Check_sound {claim : Claim} {envBytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {inp : Recheck.Input}
    (hin : Recheck.ingress envBytes equations roots claim.kernelLimits = .ok inp)
    {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert} {a : Recheck.Artifact}
    (h : Recheck.run cfg P c = .ok a)
    {layout : X86.Exe.Layout} {inp' : X86.Exe.Input} {ce : X86.Exe.Certified inp'}
    (hb : IxCC.Exe.build a layout = .ok ⟨inp', ce⟩) {sc : Shape2.Cert}
    (hcheck : tier1Check claim inp c a sc = true) :
    ∃ acc, Admits claim envBytes acc ∧ Tier1Stdout.{u} claim acc ce.bytes := by
  unfold tier1Check at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨henv, hrole⟩, hg⟩ := hcheck
  cases hgs : groundShapeCheck inp c a sc claim.target with
  | error e => rw [hgs] at hg; cases hg
  | ok abi =>
    rw [hgs] at hg
    have habi : abi = claim.abi := of_decide_eq_true hg
    subst habi
    exact ⟨inp.kernel.acc, admits_of_ingress hin henv hrole (groundShapeCheck_sound hgs).ground.target_key,
      plain_exe_tier1Stdout_shaped h hb hgs⟩

end IxCC.Correct
