import IxCC.Recheck.Proof.Object

/-!
# `Recheck.sound`

The correctness statement at stage S for the recheck path: for every object
`Recheck.run` makes (`a.object`, the bytes the kernel gate evaluates,
`Artifact.bytes`) and every driver that keeps its contract
(`X86.Driver.Ok`), on every input it covers (`Front.Covered`: of exactly its
root's declared parameter count, or any input when the closures step left
the certificate's program unchanged),

- a value the object returns is the view of a value SrcEval returns
  (relabelled by tag at the root's readback type), or the source goes
  wrong (`Front.GoesWrong`);
- if the source does not go wrong, the object goes wrong at no clock;
- a diverging source has an object that runs at every clock or fails for a
  resource (`sound`).

For a program the closures step leaves unchanged, which is every program
that compiled before the step was added with its roots at their declared
counts, every input is covered (`sound_unchanged`).

Such a driver exists for every object (`driver_exists`). Its three clauses
are `compile_sound_linked`, `compile_safe_linked` and
`compile_diverges_linked`; an object the kernel gate evaluates is such an
artifact's (`sound_bytes`). (Theorems about `Recheck.compile` or
`compileInput` are not stated: their definitions reach Blake3 lemmas
proved by native evaluation, through ingress and `produce`, which are not
on the recheck path, so their axiom sets are not the standard three.)
-/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

variable {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}

/-- The driver's contract can be kept for every object `Recheck.run` makes. -/
theorem driver_exists (h : run cfg P c = .ok a) : ∃ D : X86.Driver, D.Ok a.backend.encoded.text.size := by
  obtain ⟨-, -, -, -, he, -⟩ := run_parts h
  obtain ⟨input, em⟩ := Backend.emit_parts he
  apply X86.Driver.exists_ok
  rw [← em.encoded, em.stream.textLength]
  exact em.stream.textBound

/-- **`Recheck.sound`**: the correctness statement at stage S for the object
`Recheck.run` makes, run by any driver that keeps its contract, on every
covered input: the object's values are the source's viewed at the roots' readback
types unless the source goes wrong; a source that does not go wrong has an
object that never goes wrong; a diverging source has an object that runs
or fails for a resource.
It holds for every `P`; that the check runs within an 8 MiB stack assumes
`P` came from ingress (`Recheck.run`'s precondition). -/
theorem sound (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    (i : Nat × List Nat) (hi : a.front.Covered c i) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i) ∧
    (¬ a.front.GoesWrong i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
      (∀ k, Lang.run (a.linked D) i k = .timeout) ∨ ∃ k failure, Lang.run (a.linked D) i k = .resource failure) :=
  have href := object_refines h D hD
  ⟨fun _ _ hw => Front.sound_of href hi hw, fun hs k => Front.safe_of href hi hs k,
    fun hs => Front.diverges_of href hi hs⟩

/-- **What `Recheck.sound` gave before the closures step, for every program
the step leaves unchanged**: when the certificate's middle end gives the
final Anf program (every program that compiled before the step was added,
with its roots at their declared counts, `anfOf_of_lower`), on every
input. -/
theorem sound_unchanged (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    (hu : Anf.Pipeline.run c.mid a.lam = .ok a.anf) (i : Nat × List Nat) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i) ∧
    (¬ a.front.GoesWrong i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
      (∀ k, Lang.run (a.linked D) i k = .timeout) ∨ ∃ k failure, Lang.run (a.linked D) i k = .resource failure) :=
  sound h D hD i (covered_of_unchanged hu i)

/-- An object the kernel gate evaluates (`(run cfg P c).map Artifact.bytes =
.ok bytes`) is an artifact's, whose linked object has those bytes. -/
theorem sound_bytes {bytes : List UInt8} (h : (run cfg P c).map Artifact.bytes = .ok bytes) :
    ∃ a, run cfg P c = .ok a ∧ a.bytes = bytes ∧ ∀ D : X86.Driver, (a.linked D).object.data.toList = bytes := by
  cases hr : run cfg P c with
  | error e => rw [hr] at h; cases h
  | ok a =>
    rw [hr] at h
    simp only [Except.map, Except.ok.injEq] at h
    exact ⟨a, rfl, h, fun _ => h⟩

/-- **`compile_sound` for the object** (stage S), from
`Recheck.sound`: a value the object returns is the view of a value SrcEval
returns, or the source goes wrong. -/
theorem compile_sound_linked (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} (hi : a.front.Covered c i) {k : Nat} {w : Option Obs} (hw : Lang.run (a.linked D) i k = .ok w) :
    (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
      a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i :=
  (sound h D hD i hi).1 k w hw

/-- **`compile_safe` for the object**, from `Recheck.sound`: if the source
does not go wrong, the object goes wrong at no clock. -/
theorem compile_safe_linked (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} (hi : a.front.Covered c i) (hs : ¬ a.front.GoesWrong i) (k : Nat) :
    ¬ (Lang.run (a.linked D) i k).GoesWrong :=
  (sound h D hD i hi).2.1 hs k

/-- **Divergence for the object**, from `Recheck.sound`: a diverging source
has an object that runs at every clock or fails for a resource. -/
theorem compile_diverges_linked (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} (hi : a.front.Covered c i)
    (hs : ∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) :
    (∀ k, Lang.run (a.linked D) i k = .timeout) ∨ ∃ k failure, Lang.run (a.linked D) i k = .resource failure :=
  (sound h D hD i hi).2.2 hs

/-- **Non-vacuous `Recheck.sound` on a viewed source evaluation**: when
`CheckedProgram` evaluates to `.ok v` and `a.front.view i.1 (Lang.obs v) =
some o`, the `a.front.GoesWrong i` disjunct is discharged, the linked object
never goes wrong, and any value `w` returned by the linked object equals `o`. -/
theorem sound_of_eval (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} (hi : a.front.Covered c i) {k_src : Nat} {v : Lang.Val CheckedProgram} {o : Option Obs}
    (heval : Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k_src = .ok v)
    (hview : a.front.view i.1 (Lang.obs v) = some o) :
    ¬ a.front.GoesWrong i ∧
    (∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    (∀ k w, Lang.run (a.linked D) i k = .ok w → w = o) := by
  have hngw : ¬ a.front.GoesWrong i := Front.not_goesWrong_of_eval (f := a.front) heval hview
  have hs := sound h D hD i hi
  refine ⟨hngw, hs.2.1 hngw, fun k w hw => ?_⟩
  rcases hs.1 k w hw with ⟨k', v', heval', hview'⟩ | hgw
  · have hv : v = v' := Front.eval_unique (f := a.front) heval heval'
    subst hv
    rw [hview] at hview'
    exact (Option.some.inj hview').symm
  · exact absurd hgw hngw

/-- **Non-vacuous `Recheck.sound` at a `Nat` root**: when `CheckedProgram`
evaluates to `.ok v` with `Lang.obs v = some (.nat n)` at a `Nat` root,
`¬ a.front.GoesWrong i`, `a.front.treeView` agrees with `a.front.view`, the
linked object never goes wrong, and any value returned by the linked object
is `some (.nat n)`. -/
theorem sound_nat (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} (hi : a.front.Covered c i) {k_src : Nat} {v : Lang.Val CheckedProgram} {n : Nat}
    (hty : a.front.tys i.1 = some ({}, .nat))
    (heval : Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k_src = .ok v)
    (hobs : Lang.obs v = some (.nat n)) :
    a.front.view i.1 (Lang.obs v) = some (some (.nat n)) ∧
    a.front.treeView i.1 (Lang.obs v) = some (some (.nat n)) ∧
    ¬ a.front.GoesWrong i ∧
    (∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    (∀ k w, Lang.run (a.linked D) i k = .ok w → w = some (.nat n)) := by
  obtain ⟨hview, _⟩ := Front.not_goesWrong_of_nat (f := a.front) hty heval hobs
  have htree := (Front.view_eq_treeView_of_tagify hview).2
  exact ⟨hview, htree, sound_of_eval h D hD hi heval hview⟩

/-- **Non-vacuous `Recheck.sound` at a field-less constructor**: when
`CheckedProgram` evaluates to `.ok v` with `Lang.obs v = some (.ctor cid [])`
matching the root's signature, `¬ a.front.GoesWrong i`, `a.front.treeView`
agrees with `a.front.view`, the linked object never goes wrong, and any
value returned by the linked object is `some (.ctor c.tag [])`. -/
theorem sound_ctor0 (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} (hi : a.front.Covered c i) {k_src : Nat} {v : Lang.Val CheckedProgram}
    {sig : Rt.Sig} {idx : Nat} {cid : Src.CId} {c : Fir.CtorInfo}
    (hty : a.front.tys i.1 = some (sig, .ind idx))
    (hc : Fir.CtorInfo.ofKey a.front.cfg.ctors (.src cid) = some c)
    (hsig : sig.ctor? idx c.tag = some [])
    (heval : Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k_src = .ok v)
    (hobs : Lang.obs v = some (.ctor cid [])) :
    a.front.view i.1 (Lang.obs v) = some (some (.ctor c.tag [])) ∧
    a.front.treeView i.1 (Lang.obs v) = some (some (.ctor c.tag [])) ∧
    ¬ a.front.GoesWrong i ∧
    (∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    (∀ k w, Lang.run (a.linked D) i k = .ok w → w = some (.ctor c.tag [])) := by
  obtain ⟨hview, _⟩ := Front.not_goesWrong_of_ctor0 (f := a.front) hty hc hsig heval hobs
  have htree := (Front.view_eq_treeView_of_tagify hview).2
  exact ⟨hview, htree, sound_of_eval h D hD hi heval hview⟩

end IxCC.Recheck
