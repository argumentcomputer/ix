import Compilatrix.Rt.Rc.View
import Compilatrix.Rt.Rc.Proof.Readback.Source

set_option autoImplicit false
namespace Compilatrix.Rt.Rc.Procs.Readback
open Compilatrix.Sem (Obs)

mutual
/-- Constructor provenance comes from the already-proved actual Anf-to-Fir
value relation. Successful view checking supplies result signature typing;
the caller does not assume SourceTree or a source typing theorem. -/
theorem treeView_of_vr {A : Anf.Program} {sig : Sig} :
    ∀ {v : Anf.Val} {value : Fir.Val}, Fir.Proof.VR A v value →
      ∀ {ty : FoTy} {source target : Obs}, Fir.obsV value = some source →
        treeView A.ctors sig ty source = some target →
        SourceTree A.ctors sig ty value source target
  | _, _, .lit (.nat n), ty, source, target, hs, ht => by
    simp only [Fir.obsV, Option.some.injEq] at hs
    subst source
    cases ty with
    | nat => simp only [treeView, Option.some.injEq] at ht; subst target; exact .nat n
    | ind _ => simp [treeView] at ht
  | _, _, .lit (.str s), ty, source, target, hs, ht => by
    simp only [Fir.obsV, Option.some.injEq] at hs
    subst source
    cases ty <;> simp [treeView] at ht
  | _, _, .box, _, _, _, hs, _ => by simp [Fir.obsV] at hs
  | .con key vs, .ctor c values, .con row related arity, ty, source, target, hs, ht => by
    have keyEq := Fir.Proof.ofKey_key row
    cases key with
    | clo _ _ => simp [Fir.obsV, keyEq] at hs
    | src cid =>
      simp only [Fir.obsV, keyEq] at hs
      obtain ⟨sourceFields, sourceRead, sourceEq⟩ := Option.map_eq_some_iff.mp hs
      subst source
      cases ty with
      | nat => simp [treeView] at ht
      | ind i =>
        simp only [treeView, row, bind, Option.bind_some] at ht
        cases signature : sig.ctor? i c.tag with
        | none => simp [signature] at ht
        | some types =>
          simp only [signature, bind, Option.bind_some] at ht
          cases fields : fieldsView A.ctors sig types sourceFields with
          | none => simp [fields] at ht
          | some targetFields =>
            simp only [fields, bind, Option.bind_some, pure, Option.some.injEq] at ht
            subst target
            exact .ctor keyEq (by rw [keyEq]; exact row) signature arity.symm
              (fieldsView_of_vrs related sourceRead fields)

theorem fieldsView_of_vrs {A : Anf.Program} {sig : Sig} :
    ∀ {vs : List Anf.Val} {values : List Fir.Val}, Fir.Proof.VRs A vs values →
      ∀ {types : List FoTy} {source target : List Obs}, Fir.obsList values = some source →
        fieldsView A.ctors sig types source = some target →
        SourceForest A.ctors sig types values source target
  | _, _, .nil, types, source, target, hs, ht => by
    simp only [Fir.obsList, Option.some.injEq] at hs
    subst source
    cases types with
    | nil => simp only [fieldsView, Option.some.injEq] at ht; subst target; exact .nil
    | cons _ _ => simp [fieldsView] at ht
  | v :: vs, value :: values, .cons related rest, types, source, target, hs, ht => by
    cases headObs : Fir.obsV value with
    | none => simp [Fir.obsList, headObs] at hs
    | some head =>
      cases tailObs : Fir.obsList values with
      | none => simp [Fir.obsList, headObs, tailObs] at hs
      | some tail =>
        simp only [Fir.obsList, headObs, tailObs, Option.some.injEq] at hs
        subst source
        cases types with
        | nil => simp [fieldsView] at ht
        | cons ty types =>
          cases headView : treeView A.ctors sig ty head with
          | none => simp [fieldsView, headView] at ht
          | some first =>
            cases tailView : fieldsView A.ctors sig types tail with
            | none => simp [fieldsView, headView, tailView] at ht
            | some remaining =>
              simp only [fieldsView, headView, tailView, bind, Option.bind_some, pure,
                Option.some.injEq] at ht
              subst target
              exact .cons (treeView_of_vr related headObs headView)
                (fieldsView_of_vrs rest tailObs tailView)
end

theorem viewed_readback_region {A : Anf.Program} {sig : Sig} {ty : FoTy}
    {anfValue : Anf.Val} {logical : Fir.Val} {source target : Obs}
    (related : Fir.Proof.VR A anfValue logical)
    (observed : Fir.obsV logical = some source)
    (viewed : treeView A.ctors sig ty source = some target)
    {H : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {base bump limit : Lir.Word} {slots : List Slot} {regionBytes : Nat}
    (heap : HeapLive H addresses mem)
    (partition : ArenaPartition H addresses base bump limit slots)
    (ordered : Own.Rc.HeapOk H) (region : limit.toNat-base.toNat ≤ regionBytes)
    {v : Own.RVal} {word : Lir.Word} (den : Own.Proof.Den H v logical)
    (represented : valueWord addresses v = some word) :
    Rt.readback sig (regionBytes/8) mem ty word = some target :=
  (source_readback_region (treeView_of_vr related observed viewed)
    heap partition ordered region den represented).2

end Compilatrix.Rt.Rc.Procs.Readback
