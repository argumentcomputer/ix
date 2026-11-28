import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedCtorEnv
import IxCC.Cfg.Rc.Proof.Native.Pipeline

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Rt.Proof
open IxCC.Cfg.Rc.Native.Spec

/-- Constructor compatibility ignores runtime procedure IDs and Boolean word
caches; only exact rows and pinned Nat keys occur in the invariant. -/
theorem ctorOk_retable {T U : Rt.Lower.Tables}
    (ctors : T.ctors = U.ctors) (known : T.known = U.known)
    {ctor : Fir.CtorInfo} (before : CtorOk T ctor) : CtorOk U ctor := by
  refine ⟨?_, ?_, before.tag⟩
  · rw [← ctors]
    exact before.table
  · simpa only [Rt.Lower.isNatKey, known] using before.notNat

theorem valueCtorOk_retable {T U : Rt.Lower.Tables}
    (ctors : T.ctors = U.ctors) (known : T.known = U.known)
    {value : Own.RVal} (before : ValueCtorOk T value) : ValueCtorOk U value := by
  cases value with
  | loc _ | lit _ | erased => trivial
  | ctor0 ctor => exact ⟨ctorOk_retable ctors known before.1, before.2⟩

theorem HeapCtorOk.retable {T U : Rt.Lower.Tables}
    (ctors : T.ctors = U.ctors) (known : T.known = U.known)
    {heap : Own.Heap} (before : HeapCtorOk T heap) : HeapCtorOk U heap := by
  intro location refs mode body cell
  obtain ⟨ctor, nonempty, fields⟩ := before location refs mode body cell
  exact ⟨ctorOk_retable ctors known ctor, nonempty,
    fun value member => valueCtorOk_retable ctors known (fields value member)⟩

theorem FusedCtorOk.retable {T U : Rt.Lower.Tables}
    (ctors : T.ctors = U.ctors) (known : T.known = U.known)
    {D : Nat → Prop} {env : Own.Env} (before : FusedCtorOk T D env) : FusedCtorOk U D env :=
  fun x value lookup live => valueCtorOk_retable ctors known (before x value lookup live)

theorem ctorOk_tablesOf {P : Cfg.Rc.Program} (pairs : List (Nat × Cfg.Fun))
    {ctor : Fir.CtorInfo} (before : CtorOk (Rt.Lower.tables P.base) ctor) :
    CtorOk (tablesOf P pairs) ctor :=
  ctorOk_retable (T := Rt.Lower.tables P.base) (U := tablesOf P pairs) rfl rfl before

theorem valueCtorOk_tablesOf {P : Cfg.Rc.Program} (pairs : List (Nat × Cfg.Fun))
    {value : Own.RVal} (before : ValueCtorOk (Rt.Lower.tables P.base) value) :
    ValueCtorOk (tablesOf P pairs) value :=
  valueCtorOk_retable (T := Rt.Lower.tables P.base) (U := tablesOf P pairs) rfl rfl before

theorem heapCtorOk_tablesOf {P : Cfg.Rc.Program} (pairs : List (Nat × Cfg.Fun))
    {heap : Own.Heap} (before : HeapCtorOk (Rt.Lower.tables P.base) heap) :
    HeapCtorOk (tablesOf P pairs) heap :=
  HeapCtorOk.retable (T := Rt.Lower.tables P.base) (U := tablesOf P pairs) rfl rfl before








end IxCC.Cfg.Rc.Proof.Physical.Bridge
