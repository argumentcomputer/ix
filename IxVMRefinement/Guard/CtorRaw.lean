import IxVMRefinement.Assembly.GuardRawLookup

/-! # The constructor's raw telescope, read from a store

`ctorRaw E B i j` is the type of constructor `j` of member `i` of the block `E` holds at `B`, as
the field classifier reads it: the raw dictionary's reading (`GuardRaw.memberRoot`,
`GuardRaw.readRoot`) of the constructor's type expression in the block record. It is a function
of the block record and of the store's literal blobs, and it is kept by every record store for
a witness store (`ctorRaw_recordsFor`).
-/

namespace IxVM.Refinement.Guard

open IxVM.Consistency
open Ix.Kernel (Expr)

/-- **The type of constructor `j` of member `i` of the block `E` holds at `B`, as the field
classifier reads it**: address keys, the constructor's own level parameters, `let` nodes kept,
binder data erased. A function of the block record and of the literal blobs. -/
def ctorRaw (E : Ixon.Env) (B : _root_.Address) (i j : Nat) : Option (Expr .anon) :=
  (GuardRaw.memberRoot (recordOf E) B i (GuardRaw.constructorType j)).bind
    (GuardRaw.readRoot (fun x => E.blobs.get? x))

private theorem recordOf_eq_recordAt {E : Ixon.Env} (hd : L1.EnvDecoded E)
    (a : _root_.Address) : recordOf E a = Ix.Cert.recordAt E a := by
  unfold recordOf Ix.Cert.recordAt
  cases hget : E.consts.get? a with
  | none => rfl
  | some lc =>
    obtain ⟨c, hc, hdec⟩ := hd a lc hget
    change (Ixon.deConstantExact lc.rawBytes).toOption = lc.get?
    rw [hdec, hc]
    rfl

/-- A record store for `R` holds every record of `R` that decodes. -/
theorem recordOf_recordsFor {R E : Ixon.Env} (h : Typing.RecordsFor R E) :
    ∀ a c, recordOf R a = some c → recordOf E a = some c :=
  fun a c hc => (recordOf_eq_recordAt h.1 a).trans (h.2.1 a c hc)

/-- **The raw telescope is the same over every record store for `R`.** -/
theorem ctorRaw_recordsFor {R E : Ixon.Env} (h : Typing.RecordsFor R E)
    {B : _root_.Address} {i j : Nat} {raw : Expr .anon}
    (hr : ctorRaw R B i j = some raw) : ctorRaw E B i j = some raw := by
  unfold ctorRaw at hr ⊢
  obtain ⟨root, hroot, hread⟩ := Option.bind_eq_some_iff.mp hr
  exact Option.bind_eq_some_iff.mpr
    ⟨root, GuardRaw.memberRoot_mono (recordOf_recordsFor h) hroot,
      GuardRaw.readRoot_mono h.2.2.1 hread⟩

end IxVM.Refinement.Guard
