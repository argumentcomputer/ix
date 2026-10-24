/- A4 per-pass fixture (`pass3` suite), elaborated at run time and in no Lake library.
O2, the recursor of a split block: `SA` has a field into the lower component `SB`. `SA.viaRec`
(a full application of `SA.rec`) gets the component's recursor with the relocated `SB` recursion
inside the adapted minor (O2 fires; the relocated call is itself rewritten by O6), byte-identical
to the switch-off output. `SB.viaRec` (the lower component, no cross field) is O6. `SA.recBare`
is a bare occurrence: no pass applies and the image constant stays (`BARE`). Value pins by `rfl`. -/
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
