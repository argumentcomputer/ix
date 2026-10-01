/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import ConLeche.Verify.Cached.AgreeFloor

/-! # What con-leche's fold installs (plan v4, L5)

The kernel half of the fidelity theorem of the con-leche entry
(`Ix.Ixon.ConLecheConsistency`). Con-leche proves that the environment an
accepted `Cached.checkDecls` returns has exactly the install skeletons its
input declares (`Cached.checkDecls_skels`, `ConLeche/Verify/Cached/AgreeFloor.lean`):
the same constants, in the same order, with the same names, kinds,
constructor arities and recursor rule constructors. A skeleton forgets
what the checker computes (annotated types and values, inductive caps,
rule right-hand sides).

This module reads that equation per declaration: a definition, theorem,
opaque or axiom declaration of an accepted array is installed under its
name with its kind (`checkDecls_installs`). Two declared axioms install
nothing of their own, as con-leche specifies (`declCSkels`): `sorryAx`
(tolerated, never modelled) and `Quot.sound` (a member of the pinned
quotient block). -/

namespace Ix.Kernel.ConLecheFold

open ConLeche ConLeche.Cached

/-- The install skeleton a value or axiom declaration contributes under its
own name; `none` for the declarations whose skeletons depend on the block
(`basisDecl`, `quotDecl`, `indDecl`) and for the two axioms that install
nothing of their own. -/
def declSkel : Declaration → Option InstallSkel
  | .defnDecl cv _ _ => some (.defn cv.name)
  | .thmDecl cv _ => some (.thm cv.name)
  | .opaqueDecl cv _ => some (.ax cv.name)
  | .axiomDecl cv => if cv.name = sorryAxName ∨ cv.name = quotSoundName then none else some (.ax cv.name)
  | _ => none

private theorem foldl_suffix {α β : Type} {g : List α → β → List α}
    (hg : ∀ acc y, acc <:+ g acc y) : ∀ (l : List β) (acc : List α), acc <:+ l.foldl g acc
  | [], _ => List.suffix_refl _
  | y :: l, acc => (hg acc y).trans (foldl_suffix hg l (g acc y))

private theorem cons_suffix {α : Type} (x : α) (l : List α) : l <:+ x :: l := List.suffix_cons x l

private theorem consFold_suffix {α β : Type} (f : β → α) (l : List β) (acc : List α) :
    acc <:+ l.foldl (fun acc y => f y :: acc) acc :=
  foldl_suffix (fun acc y => cons_suffix (f y) acc) l acc

private theorem projFnStepSkels_suffix (T c : Name) (nP : Nat) (sk : List InstallSkel) (i : Nat) :
    sk <:+ projFnStepSkels T c nP sk i := by
  unfold projFnStepSkels
  split
  · exact cons_suffix _ _
  · exact List.suffix_refl _

private theorem indDeclSkelsModeled_suffix (block : List ConstantInfo) (sk : List InstallSkel) :
    sk <:+ indDeclSkelsModeled block sk := by
  have hbase : sk <:+ (block.filter isRecCI).foldl recMemberSkels
      ((block.filter isNonRecCI).foldl indMemberSkels sk) :=
    (foldl_suffix (fun acc y => cons_suffix _ acc) _ sk).trans
      (foldl_suffix (fun acc y => cons_suffix _ acc) _ _)
  unfold indDeclSkelsModeled
  split
  · split
    · exact hbase.trans (foldl_suffix (projFnStepSkels_suffix _ _ _) _ _)
    · exact hbase
  · exact hbase

private theorem nativeSkels_suffix (p : NativeParts) (sk : List InstallSkel) : sk <:+ nativeSkels p sk := by
  have hsum : sk <:+ sumSkels p.toInductiveShape sk := by
    unfold sumSkels sumCtorSkels
    exact ((cons_suffix _ sk).trans (consFold_suffix _ _ _)).trans (cons_suffix _ _)
  unfold nativeSkels
  split
  · exact hsum.trans (cons_suffix _ _)
  · exact hsum

/-- A declaration only adds skeletons: the ones already installed stay. -/
theorem declCSkels_suffix (pd : Declaration) (sk : List InstallSkel) : sk <:+ declCSkels pd sk := by
  cases pd with
  | defnDecl cv _ _ => exact cons_suffix _ _
  | thmDecl cv _ => exact cons_suffix _ _
  | opaqueDecl cv _ => exact cons_suffix _ _
  | axiomDecl cv =>
    simp only [declCSkels]
    split
    · exact List.suffix_refl _
    · exact cons_suffix _ _
  | basisDecl kind => exact consFold_suffix _ _ _
  | quotDecl k cv =>
    simp only [declCSkels]
    cases k
    · exact consFold_suffix _ _ _
    all_goals exact List.suffix_refl _
  | indDecl block nP =>
    simp only [declCSkels]
    split
    · exact consFold_suffix _ _ _
    · unfold indDeclSkels
      split
      · exact nativeSkels_suffix _ _
      · exact indDeclSkelsModeled_suffix _ _

/-- A declaration's own skeleton is among those it installs. -/
theorem declSkel_mem {pd : Declaration} {s : InstallSkel} (h : declSkel pd = some s)
    (sk : List InstallSkel) : s ∈ declCSkels pd sk := by
  cases pd with
  | defnDecl cv _ _ => cases h; exact List.mem_cons_self
  | thmDecl cv _ => cases h; exact List.mem_cons_self
  | opaqueDecl cv _ => cases h; exact List.mem_cons_self
  | axiomDecl cv =>
    simp only [declSkel] at h
    simp only [declCSkels]
    split at h
    · cases h
    · rename_i hn
      cases h
      simp only [hn, ↓reduceIte]
      exact List.mem_cons_self
  | basisDecl _ | quotDecl _ _ | indDecl _ _ => cases h

/-- Every declaration of a stream contributes its skeleton to the stream's
skeletons. -/
theorem streamSkels_mem {ds : List Declaration} {d : Declaration} (hd : d ∈ ds)
    {s : InstallSkel} (hs : declSkel d = some s) : s ∈ streamSkels ds := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hd
  unfold streamSkels
  rw [List.foldl_append, List.foldl_cons]
  exact (foldl_suffix (fun acc pd => declCSkels_suffix pd acc) l₂ _).mem (declSkel_mem hs _)

/-- **Installation by name and kind.** A definition, theorem, opaque or
axiom declaration of an accepted array is installed under its name, as a
constant of its kind (a definition as a definition, a theorem as a theorem,
an opaque or an axiom as an axiom); `sorryAx` and `Quot.sound` excepted. -/
theorem checkDecls_installs {pins : List NatOpPinSet} {mode : CheckMode} {ds : Array Declaration}
    {env : Env} (h : checkDecls mode pins ds = .ok env) {d : Declaration} (hd : d ∈ ds)
    {s : InstallSkel} (hs : declSkel d = some s) : ∃ ci ∈ env.consts, ciSkel ci = s := by
  have hm : s ∈ envSkels env := by
    rw [checkDecls_skels h]
    exact streamSkels_mem (Array.mem_toList_iff.mpr hd) hs
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
  exact ⟨ci, hci, rfl⟩

end Ix.Kernel.ConLecheFold
