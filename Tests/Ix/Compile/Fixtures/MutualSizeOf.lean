/- Runtime fixture of `compiler-selected-closure` and
`compiler-selected-closure-e2e` (`Tests.Ix.Compile.SelectedClosure`): it is
elaborated at run time (`getFileEnv`) and is in no Lake library.

`SA`/`SB` is a mutual block. Lean generates its size functions
`PassO2.SA._sizeOf_1`/`_sizeOf_2`, one instance `_sizeOf_inst` per member,
and the constructors' `sizeOf_spec` lemmas. The functions never mention the
instances. The instances and lemmas belong to the logical unit of the block
(`Ix.EnvScope.unitMembers`), so a selected closure of a size function
carries them, and a raw closure does not. The other declarations are value
pins by `rfl`.

The declarations are those of a9cf3607 `Tests/Ix/Compile/Pass/O2Split.lean`
(the Pass 3 O2 fixture), kept verbatim so the closures are the ones the
donor suite checked. Only this comment is new. This line has no Pass 3, and
the `PassO2` namespace is kept for the roots' names. -/
set_option Elab.async false

namespace PassO2
mutual
inductive SA
  | a : SB → SA
  | stop : SA
inductive SB
  | b : SB → SB
  | leaf : SB
end

noncomputable def SA.viaRec (x : SA) : Nat :=
  @SA.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) 0 x

noncomputable def SB.viaRec (x : SB) : Nat :=
  @SB.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) 0 x

noncomputable def SA.recBare := @SA.rec

theorem viaRec_a : SA.viaRec (.a (.b .leaf)) = 2 := rfl
theorem viaRec_b : SB.viaRec (.b (.b .leaf)) = 2 := rfl
theorem recBare_stop :
    SA.recBare (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
      (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) 0 .stop = 0 := rfl
end PassO2
