import IxVMRefinement.Assembly.TypingBasisCanon
import IxVMRefinement.Assembly.TypingBasisUnit

/-! # `Facts` at the environment of the pins, from the load contract

Every field of `Decl.PrefixInv` at the environment of the pins other than `loads` is proved
(`TypingBasisInv`), and so is the `whole` clause of `Facts` (`basis_whole`). These theorems
assemble them: the invariant, and `Facts` on the six basis groups, follow from the load
contract at the prefix context alone.

The fields of the load contract there are proved in `TypingBasisLoads`, `TypingBasisCanon`
(`getCI` at all nineteen pins) and `TypingBasisUnit`, except six (`getCprj`, `getIprj`, `eta`,
`ctorIndRes`, `projTables`, `projTablesAt`), which relate a block a run hashed to a stored
constant through the address of one of its projection records. `TypingBasisProj` proves those
six from one hypothesis about the store (`HashedBlockProjectionsHeld`) and assembles the
contract (`basis_loads`) and `Facts` (`basis_facts`).
-/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Refinement.TableInhabit (basisEnv)

/-- **The invariant at the environment of the pins, from its load contract**: for every store
of the basis records and every limit within the six basis groups. -/
theorem basis_prefixInv_of_loads {E : Ixon.Env} (hE : RecordsFor StoreInhabit.basisStore E)
    {lim : Option Nat} (hlim : LimWithin (fun g => g < 6) ctab lim)
    (hloads : Core.ScopedLoadFacts (bctx E lim).stored) :
    Decl.PrefixInv.{u} E ctab lim basisEnv where
  decl := basisEnv_decl
  store := basisEnv_store
  unresolved := basisEnv_unresolved
  tableWf := committedTable_wf
  companions := basisEnv_companions hE hlim
  loads := hloads
  etaStable := basisEnv_etaStable

/-- **`Facts` on the six basis groups at the environment of the pins, from the load
contract.** -/
theorem basis_facts_of_loads
    (hloads : ∀ E, RecordsFor StoreInhabit.basisStore E → ∀ lim,
      LimWithin (fun g => g < 6) ctab lim → Core.ScopedLoadFacts (bctx E lim).stored) :
    Facts.{u} ctab (fun g => g < 6) StoreInhabit.basisStore basisEnv where
  inv := fun E hE lim hlim => basis_prefixInv_of_loads hE hlim (hloads E hE lim hlim)
  whole := basis_whole

end IxVM.Refinement.Typing
