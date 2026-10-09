import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.ScalarInstr
import Compilatrix.Cfg.Rc.Proof.Native.Cursor

/-! Execute the actual lowering receipt at the current source instruction.
The dynamic environment covers the full source map; fusion may omit the last
comparison. No emitted-code or successful-operand hypothesis is required. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
open Compilatrix Compilatrix.Rt Compilatrix.Rt.Proof Compilatrix.Rt.Lower
open Compilatrix.Rt.Rc.Procs Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Lir (Word)

theorem cursor_step {T : Tables} (bools : BoolsOk T) {P : Cfg.Program} {lp : Lir.Program}
    (pow : lp.funcs[T.natPow]? = some Procs.natPow)
    (gcd : lp.funcs[T.natGcd]? = some Procs.natGcd)
    {source : Cfg.Frame} {target : Lir.Frame} {fd : Cfg.Fun}
    (lookup : P.fun? source.fn = some fd)
    (cursor : Cursor T P lp source target)
    {addresses : AddressMap} {bound size : Nat}
    (words : FusedWords addresses (Fused T fd) bound source.env target.env)
    (ctors : FusedCtorOk T (Fused T fd) source.env)
    (bounded : Own.Plain.EnvBounded size source.env)
    (supply : bound ≤ supOf fd)
    {x : Nat} {rhs : Own.Rhs} {tail : List Cfg.Instr}
    (head : source.rest = .bind x rhs :: tail) (pureRhs : PureRhs rhs) (real : x < bound)
    {H H' : Own.Heap} {value : Own.RVal}
    (effect : Own.evalRhs .rc (ownTables T) source.env H rhs = .ok (value, H'))
    (mem : X86.Memory) (context : Word) (callers : List Lir.Frame) :
    H' = H ∧
    ((∃ charge after, after.dsts = [] ∧
      Sem.Star (Lir.semStep lp)
        (Lir.atState mem context target.fn target.label target.pos target.env callers) charge
        (Lir.atState mem context after.fn after.label after.pos after.env callers) ∧
      Cursor T P lp {source with rest := tail, env := source.env.insert x value} after ∧
      FusedWords addresses (Fused T fd) bound (source.env.insert x value) after.env ∧
      FusedCtorOk T (Fused T fd) (source.env.insert x value) ∧
      Own.Plain.EnvBounded size (source.env.insert x value) ∧
      ∀ block, fd.blocks[source.blk]? = some block →
        FusedDone T fd block {source with rest := tail, env := source.env.insert x value}) ∨
    Sem.Fails (Lir.semStep lp)
      (Lir.atState mem context target.fn target.label target.pos target.env callers)) := by
  obtain ⟨sameHeap, valueBound⟩ := pure_effect pureRhs bounded effect
  refine ⟨sameHeap, ?_⟩
  obtain ⟨otherFd, block, function, starts, off, chunk, state, final, sourceLookup, blockLookup,
    targetLookup, layout, start, held, lowering, extension, labeled, opened, fresh,
    ⟨pre, body⟩, fn, label, pos⟩ := cursor
  rw [lookup] at sourceLookup
  cases sourceLookup
  rw [head] at lowering body
  have related := EnvRel.of_fused words ctors
  have live := instr_live (T := T) blockLookup body
  by_cases last : (fusable T (useCounts fd) block).isSome = true ∧ tail = []
  · obtain ⟨someFused, rfl⟩ := last
    obtain ⟨⟨init, cond, a, b⟩, fused⟩ := Option.isSome_iff_exists.1 someFused
    obtain ⟨y, op, alts, default, equal, rfl, comparison, term⟩ := fused_last fused body
    simp only [Cfg.Instr.bind.injEq] at equal
    obtain ⟨rfl, rfl⟩ := equal
    have omitted : Fused T fd x :=
      ⟨source.blk, block, pre, cond, a, b, alts, default, blockLookup, fused, term⟩
    obtain ⟨_, values, args, result⟩ := evalRhs_prim effect
    obtain ⟨va, vb, rfl⟩ := evalArgs_two args
    have different : ∀ y ∈ Cfg.Check.argVars [a, b], y ≠ x := by
      intro y member equal
      subst y
      exact live x (by simpa [Cfg.Check.rhsVars] using member) omitted
    let after : Lir.Frame := { target with dsts := [] }
    obtain ⟨afterWords, afterCtors⟩ := (related.insert_dead real omitted (v := value)).to_fused
    refine .inl ⟨0, after, rfl, .refl _, ?_, afterWords, afterCtors,
      bounded.insert x valueBound, ?_⟩
    · refine ⟨fd, block, function, starts, off, chunk, state, final,
        lookup, blockLookup, targetLookup, layout, start, held, ?_, extension, labeled, opened, fresh,
        ⟨pre ++ [.bind x (.fir (.prim op [a, b]))], by simpa using body⟩, fn, label, pos⟩
      unfold restAct at lowering ⊢
      simp only [fused] at lowering ⊢
      simpa using lowering
    · intro block' blockLookup'
      rw [blockLookup] at blockLookup'
      cases blockLookup'
      intro init' cond' a' b' fused' _
      rw [fused] at fused'
      simp only [Option.some.injEq, Prod.mk.injEq] at fused'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := fused'
      exact ⟨x, op, va, vb, value, body.symm,
        by rw [evalArgs_insert_irrel different]; exact args, result, Src.NatMap.get?_insert_self ..⟩
  · have unfused : (fusable T (useCounts fd) block).isSome = true → tail ≠ [] :=
      fun someFused empty => last ⟨someFused, empty⟩
    obtain ⟨continues, next, lowered, ⟨rfl, rest⟩ | ⟨rfl, rfl⟩⟩ := rest_cons lowering unfused
    · obtain ⟨grows, labeled', opened'⟩ := instr_mono lowered labeled opened
      have nextExt : Ext chunk next := (rest_grows rest labeled' opened').ext extension
      have simulate := instr_sim bools targetLookup held pow gcd pureRhs lowered nextExt labeled opened
        (Nat.le_trans supply fresh) real live (ctx := context)
      rcases simulate addresses H source.env target.env mem callers value H' related effect with
        ⟨charge, registers, trace, afterRelated⟩ | failed
      · let after : Lir.Frame :=
          {fn := source.fn, label := off + next.cur, pos := next.acc.length, env := registers}
        obtain ⟨afterWords, afterCtors⟩ := afterRelated.to_fused
        refine .inl ⟨charge, after, rfl, ?_, ?_, afterWords, afterCtors,
          bounded.insert x valueBound, ?_⟩
        · simpa only [fn, label, pos] using trace
        · exact ⟨fd, block, function, starts, off, chunk, next, final,
            lookup, blockLookup, targetLookup, layout, start, held, rest, extension, labeled', opened',
            Nat.le_trans fresh grows.fresh,
            ⟨pre ++ [.bind x rhs], by simpa using body⟩, rfl, rfl, rfl⟩
        · intro block' blockLookup'
          rw [blockLookup] at blockLookup'
          cases blockLookup'
          intro init cond a b fused empty
          exact False.elim ((unfused (by simp [fused])) empty)
      · exact .inr (by simpa only [fn, label, pos] using failed)
    · right
      rw [fn, label, pos]
      exact instr_fails targetLookup held lowered extension opened mem target.env callers


end Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Scalar
