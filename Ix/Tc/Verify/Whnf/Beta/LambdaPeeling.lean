import Ix.Tc.Verify.Whnf.Structural.StepAssembly

/-!
# Certified lambda peeling for general beta

`consumeBetaLams` is an accumulator loop, so its result equation alone does
not expose which lambdas were removed or which prefix of the application
spine was consumed.  This slice gives the loop a structural certificate and
proves that the returned array is exactly a prefix of the input arguments.
-/

namespace Ix.Tc
namespace RecM

/-- A sequence of lambda bodies reached by consuming arguments in production
order.  The snoc constructor matches `consumeBetaLamsFuel`'s accumulator. -/
inductive BetaPeel : KExpr .anon -> List (KExpr .anon) -> KExpr .anon -> Prop
  | nil (start) : BetaPeel start [] start
  | snoc {start consumed name bi ty body info arg} :
      BetaPeel start consumed (.lam name bi ty body info) ->
      BetaPeel start (consumed ++ [arg]) body

namespace BetaPeel

/-- The accumulator loop preserves both its structural peel trace and its
exact-prefix invariant. -/
theorem fuel
    {start current : KExpr .anon} {args consumed : Array (KExpr .anon)}
    (hpeel : BetaPeel start consumed.toList current)
    (hprefix : consumed.toList = args.toList.take consumed.size)
    (hsize : consumed.size <= args.size) :
    forall fuel,
      let result := consumeBetaLamsFuel fuel current args consumed
      BetaPeel start result.2.toList result.1 /\
        result.2.toList = args.toList.take result.2.size /\
        result.2.size <= args.size := by
  intro fuel
  induction fuel generalizing current consumed with
  | zero =>
      simpa only [consumeBetaLamsFuel_zero] using
        And.intro hpeel (And.intro hprefix hsize)
  | succ fuel ih =>
      rw [consumeBetaLamsFuel_succ]
      by_cases hdone : consumed.size >= args.size
      · simp only [hdone, if_true]
        exact ⟨hpeel, hprefix, hsize⟩
      · simp only [hdone, if_false]
        cases current with
        | lam name bi ty body info =>
            have hlt : consumed.size < args.size := by omega
            have hnextPrefix :
                (consumed.push args[consumed.size]!).toList =
                  args.toList.take (consumed.push args[consumed.size]!).size := by
              rw [Array.toList_push, Array.size_push, hprefix]
              rw [List.take_succ_eq_append_getElem]
              · rw [getElem!_pos args consumed.size hlt,
                  Array.getElem_toList hlt]
              · simpa using hlt
            have hnextSize :
                (consumed.push args[consumed.size]!).size <= args.size := by
              simp only [Array.size_push]
              omega
            have hnextPeel :
                BetaPeel start
                  (consumed.push args[consumed.size]!).toList body := by
              rw [Array.toList_push]
              exact BetaPeel.snoc (arg := args[consumed.size]!) hpeel
            exact ih hnextPeel hnextPrefix hnextSize
        | var | fvar | sort | const | app | all | letE | prj | nat | str =>
            exact ⟨hpeel, hprefix, hsize⟩

/-- Public `consumeBetaLams` result: the returned body is reached by peeling
exactly the returned production-order argument prefix. -/
theorem of_consume
    {start body : KExpr .anon} {args consumed : Array (KExpr .anon)}
    (hconsume : consumeBetaLams start args = (body, consumed)) :
    BetaPeel start consumed.toList body /\
      consumed.toList = args.toList.take consumed.size /\
      consumed.size <= args.size := by
  have h := fuel (start := start) (current := start) (args := args)
    (consumed := Array.mkEmpty args.size) (.nil start) (by simp) (by simp)
      args.size
  dsimp only at h
  rw [consumeBetaLams_equation] at hconsume
  rw [hconsume] at h
  exact h

/-- Production's extracted remainder is exactly the list suffix after the
certified consumed prefix. -/
theorem remaining_eq_drop
    {start body : KExpr .anon} {args consumed : Array (KExpr .anon)}
    (hconsume : consumeBetaLams start args = (body, consumed)) :
    (args.extract consumed.size args.size).toList =
      args.toList.drop consumed.size := by
  obtain ⟨_, _, _⟩ := of_consume hconsume
  rw [Array.toList_extract]
  simp only [List.extract_eq_take_drop]
  have hargsLength : args.toList.length = args.size := by
    simpa using congrArg Array.size (Array.toArray_toList (xs := args))
  have hdropLength :
      (args.toList.drop consumed.size).length =
        args.size - consumed.size := by
    rw [List.length_drop, hargsLength]
  have htake :
      (args.toList.drop consumed.size).take (args.size - consumed.size) =
        args.toList.drop consumed.size := by
    rw [← hdropLength]
    exact List.take_length
  exact htake

/-- The unconsumed `extract` is precisely the suffix complementary to the
certified consumed prefix. -/
theorem consumed_append_remaining
    {start body : KExpr .anon} {args consumed : Array (KExpr .anon)}
    (hconsume : consumeBetaLams start args = (body, consumed)) :
    consumed.toList ++ (args.extract consumed.size args.size).toList =
      args.toList := by
  obtain ⟨_, hprefix, _⟩ := of_consume hconsume
  rw [hprefix, remaining_eq_drop hconsume]
  exact List.take_append_drop consumed.size args.toList

end BetaPeel

end RecM
end Ix.Tc
