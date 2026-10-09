import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Tokens
import Compilatrix.Rt.Rc.Proof.ReleaseInvariant
import Compilatrix.Cfg.Rc.Proof.Physical.PublicationRegisters
import Compilatrix.Rt.Lower

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Rc.Procs Compilatrix.Cfg.Rc.Native

/-- Live lexical ownership, rather than a persistent map entry, authorizes
reading the physical parent. Recycled dead addresses supply no such token. -/
theorem projection_parent
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {y location : Nat}
    (before : Tokens H external held live ρf ρo roots)
    (member : y ∈ live) (lookup : ρo.get? y = some (.loc location))
    {addresses : AddressMap} {mem : X86.Memory} (physical : HeapLive H addresses mem) :
    ∃ refs body address, H.cell? location = some (.live refs .dyn body) ∧
      addresses location = some address ∧ LiveCell addresses mem address refs body := by
  obtain ⟨refs, body, cell, _⟩ := balance_pending_live before.balance
    (before.exactRoots.member member lookup)
  obtain ⟨_, address, placed, represented⟩ := physical.cell location refs .dyn body cell
  exact ⟨refs, body, address, cell, placed, represented⟩

/-- Inserting a borrowed field preserves the existing owned roots exactly.
The destination does not become an owned live variable until explicit inc. -/
theorem Tokens.borrow
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    (x : Nat) (value : RVal) (fresh : x ∉ live) :
    Tokens H external held live ρf (ρo.insert x value) roots := by
  refine ⟨?_, ?_, before.balance, before.distinct⟩
  · intro y member
    obtain ⟨v, w, lookup, logical, den⟩ := before.den y member
    refine ⟨v, w, ?_, logical, den⟩
    rw [Src.NatMap.get?_insert_ne _ _ (by intro equal; subst y; exact fresh member)]
    exact lookup
  · change Own.evalArgs (ρo.insert x value) (live.map Fir.Arg.var) = some roots
    rw [Own.Plain.evalVars_congr (ρo.insert x value) ρo live (fun y member =>
      Src.NatMap.get?_insert_ne _ _ (by intro equal; subst y; exact fresh member))]
    exact before.exactRoots

/-- Actual dynamic bytes yield the field read. The source projection is
borrowed, so heap/counts are unchanged; duplication permission comes from
the live incoming edge. No successful evaluation is a premise. -/
theorem projection_field
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    {y location refs : Nat} {body : Own.Body}
    (lookup : ρo.get? y = some (.loc location))
    (cell : H.cell? location = some (.live refs .dyn body))
    {addresses : AddressMap} {mem : X86.Memory} {address : Lir.Word}
    (physical : LiveCell addresses mem address refs body)
    {ρl : Lir.Env} {bound : Nat}
    (registers : EnvWordsBelow addresses bound ρo ρl)
    (parentRegister : ρl[y]? = some address)
    (x i : Nat) (value : RVal) (fresh : x ∉ live)
    (field : body.fields[i]? = some value) (tables : Own.Tables) (context : Lir.Word) :
    ∃ word, valueWord addresses value = some word ∧
      Own.evalRhs .rc tables ρo H (.proj y body.ctor.key i) = .ok (value, H) ∧
      Lir.Rhs.eval ρl mem context
        (.load .w64 .zero (Rt.Lower.mem y ((8+8*i : Nat) : Int))) = some word ∧
      Tokens H external held live ρf (ρo.insert x value) roots ∧
      EnvWordsBelow addresses bound (ρo.insert x value) (ρl.insert x word) ∧
      CanDup H value := by
  obtain ⟨word, represented, bytes⟩ := physical.fields i value field
  refine ⟨word, represented, ?_, ?_, before.borrow x value fresh,
    registers.bind represented, ?_⟩
  · simp [Own.evalRhs, lookup, RVal.asCtor, cell, field, Sem.Result.ofOption, Sem.Result.map]
  · have addr : Lir.Addr.eval ρl context (Rt.Lower.mem y ((8+8*i : Nat) : Int)) =
        some (address + UInt64.ofNat (8+8*i)) := by
      simp only [Lir.Addr.eval, Rt.Lower.mem, Option.bind_eq_bind,
        Option.bind_some, Lir.option_pure, parentRegister]
      rw [Lir.dispWord_ofNat]
      simp
    simp only [Lir.Rhs.eval, addr, Option.bind_eq_bind, Option.bind_some,
      Lir.loadWord, bytes.read64]
  · exact canDup_field before.balance cell (List.mem_of_getElem? field)




end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
