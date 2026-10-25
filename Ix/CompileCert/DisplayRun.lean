module
public import Ix.Compile.Pass.Driver
import all Ix.Compile.Pass.Driver

namespace Ix.CompileCert.DisplayAddressFrame
open Ix Ix.CompileM Ix.Compile.Pass Ix.Compile.ExactKey

/-- Expose the actual loop's private option matcher for the run proof. -/
public theorem moveToDisplay_eq (all : Array Name) (rep0 : Name)
    (perm : Array (Option Nat)) (sel : Name → Bool) :
    moveToDisplay all rep0 perm sel = (do
      let st ← getBlockState
      let registered : Array Name := st.auxNameToAddr.fold
        (fun acc n _ => acc.push n) (st.auxNamed.map (·.1))
      let display ← forIn (m := CompileM) (α := Name) registered ({} : Std.HashMap ExactName Name) fun (n : Name) m =>
        if m.contains n || hasReserved n || !sel n then pure (.yield m)
        else (ixAuxName all rep0 perm n).elim (pure (.yield m))
          (fun d => pure (.yield (m.insert n d)))
      if display.isEmpty then return
      let (named, addresses, extra) := (SideCarEdit.mk display).apply
        st.auxNamed st.auxNameToAddr st.auxGenExtraNames
      modifyBlockState fun s => { s with auxNamed := named, auxNameToAddr := addresses, auxGenExtraNames := extra }
      for (_, d) in display do compileName d) := by
  unfold moveToDisplay
  congr 1
  funext st
  dsimp only
  congr 1
  congr 1
  funext n m
  split <;> try rfl
  cases ixAuxName all rep0 perm n <;> rfl

end Ix.CompileCert.DisplayAddressFrame
