import Ix.Compile.Canon.Nested

/-!
Uncompiled full-result refinement for the additive callback-generic core.
Every left-hand function is the original cb67 definition, retained byte-for-byte
in Nested. These equalities quantify over arbitrary source contexts/states and
retain errors and every result field. No source completeness/freshness premise
is required for this representation equality.
-/

namespace Ix.CompileCert.Canon.CoreBridge

open Ix.Compile.Canon
open Ix (Name Expr)

/-- Arbitrary prepopulated cache values are retained; only an actual cache miss
forces the source context's real lazy protection computation. -/
theorem sourceNames_eq_core (cx : XCtx) (st : XSt) :
    st.sourceNames cx = ExpansionCore.sourceNames (ExpansionCore.Ctx.ofSource cx) st := rfl

/-- One complete query, including error recording, all skipped/hit cases,
class/alias insertion and every generated constructor/state field. -/
theorem replaceIfNested_eq_core (cx : XCtx) (np : Nat) (owner : Name)
    (e : Expr) (d : Nat) (st : XSt) :
    replaceIfNested cx np owner e d st =
      ExpansionCore.replaceIfNested (ExpansionCore.Ctx.ofSource cx) np owner e d st := by
  unfold replaceIfNested ExpansionCore.replaceIfNested
  rfl

/-- Exact expression and state equality for the recursive pre-order walk. -/
theorem replaceAll_eq_core (cx : XCtx) (np : Nat) (owner : Name) (e : Expr) :
    ∀ (d : Nat) (st : XSt), replaceAll cx np owner e d st =
      ExpansionCore.replaceAll (ExpansionCore.Ctx.ofSource cx) np owner e d st := by
  induction e with
  | app f a h ihf iha =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
    cases ExpansionCore.replaceIfNested (ExpansionCore.Ctx.ofSource cx) np owner (.app f a h) d st with
    | mk result st' =>
      cases result with
      | some value => rfl
      | none => simp only [ihf, iha]
  | lam n t b bi h iht ihb =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
    cases ExpansionCore.replaceIfNested (ExpansionCore.Ctx.ofSource cx) np owner (.lam n t b bi h) d st with
    | mk result st' =>
      cases result with
      | some value => rfl
      | none => simp only [iht, ihb]
  | forallE n t b bi h iht ihb =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
    cases ExpansionCore.replaceIfNested (ExpansionCore.Ctx.ofSource cx) np owner (.forallE n t b bi h) d st with
    | mk result st' =>
      cases result with
      | some value => rfl
      | none => simp only [iht, ihb]
  | letE n t v b nd h iht ihv ihb =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
    cases ExpansionCore.replaceIfNested (ExpansionCore.Ctx.ofSource cx) np owner (.letE n t v b nd h) d st with
    | mk result st' =>
      cases result with
      | some value => rfl
      | none => simp only [iht, ihv, ihb]
  | proj n i s h ihs =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
    cases ExpansionCore.replaceIfNested (ExpansionCore.Ctx.ofSource cx) np owner (.proj n i s h) d st with
    | mk result st' =>
      cases result with
      | some value => rfl
      | none => simp only [ihs]
  | mdata md x h ihx =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
    cases ExpansionCore.replaceIfNested (ExpansionCore.Ctx.ofSource cx) np owner (.mdata md x h) d st with
    | mk result st' =>
      cases result with
      | some value => rfl
      | none => simp only [ihx]
  | bvar i h =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
  | fvar n h =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
  | mvar n h =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
  | sort u h =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
  | const n us h =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]
  | lit value h =>
    intro d st
    rw [replaceAll.eq_1, ExpansionCore.replaceAll.eq_1, replaceIfNested_eq_core]

/-- All queue/constructor lookup failures and every rewritten state field agree. -/
theorem walkCtor_eq_core (cx : XCtx) (qi ci : Nat) (st : XSt) :
    walkCtor cx qi ci st = ExpansionCore.walkCtor (ExpansionCore.Ctx.ofSource cx) qi ci st := by
  unfold walkCtor ExpansionCore.walkCtor
  simp only [replaceAll_eq_core, ExpansionCore.Ctx.ofSource]

/-- Equality of the full Except result for every fuel, queue index and initial
state, including pending-key errors and exhausted fuel. -/
theorem walkQueue_eq_core (cx : XCtx) :
    ∀ (fuel qi : Nat) (st : XSt), walkQueue cx fuel qi st =
      ExpansionCore.walkQueue (ExpansionCore.Ctx.ofSource cx) fuel qi st
  | 0, _, _ => rfl
  | fuel + 1, qi, st => by
    rw [walkQueue.eq_2, ExpansionCore.walkQueue.eq_2]
    cases st.keyError with
    | some err => rfl
    | none =>
      cases st.types[qi]? with
      | none => rfl
      | some mem =>
        simpa only [walkCtor_eq_core] using
          walkQueue_eq_core cx fuel (qi + 1)
            ((List.range mem.ctors.size).foldl (fun state ci => walkCtor cx qi ci state) st)

/-- The existing actual source wrapper equals the generic core on the entire
Except value, with no success premise. The lazy source thunk is the real
collector over the exact ordered members and selected compiled-group registry. -/
theorem expand_eq_core (source : Ix.Environment) (dedup : Dedup) (ordered : Array Name)
    (aliases : Std.HashMap Name Name) (groups : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) :
    expandSourceSpec source dedup ordered aliases groups keyAddr? =
      ExpansionCore.expand
        (fun () => (sourceContext source ordered groups.blocks).protectedNames)
        (IndView.ofConst? source.get?) dedup ordered aliases groups.apply keyAddr? := by
  unfold expandSourceSpec ExpansionCore.expand
  simp only [walkQueue_eq_core, ExpansionCore.Ctx.ofSource]

/-- Both successful outputs are propositionally equal as complete Expanded
records, including origin maps, universe parameters and sourceNames. -/
theorem expand_outputs_eq (source : Ix.Environment) (dedup : Dedup) (ordered : Array Name)
    (aliases : Std.HashMap Name Name) (groups : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {left right : Expanded}
    (hl : expandSourceSpec source dedup ordered aliases groups keyAddr? = .ok left)
    (hr : ExpansionCore.expand
      (fun () => (sourceContext source ordered groups.blocks).protectedNames)
      (IndView.ofConst? source.get?) dedup ordered aliases groups.apply keyAddr? = .ok right) :
    left = right := by
  have equal := expand_eq_core source dedup ordered aliases groups keyAddr?
  rw [hl, hr] at equal
  exact Except.ok.inj equal

/-- Every original refusal is retained with the same error string; equality
is not restricted to accepted or successfully expanded inputs. -/
theorem expand_errors_iff (source : Ix.Environment) (dedup : Dedup) (ordered : Array Name)
    (aliases : Std.HashMap Name Name) (groups : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) (err : String) :
    (expandSourceSpec source dedup ordered aliases groups keyAddr? = .error err) ↔
      (ExpansionCore.expand
        (fun () => (sourceContext source ordered groups.blocks).protectedNames)
        (IndView.ofConst? source.get?) dedup ordered aliases groups.apply keyAddr? = .error err) := by
  rw [expand_eq_core]

/-- The migrated production entry returns exactly the complete retained
finite-source result, including all error strings and all Expanded fields. -/
theorem expandSource_eq_spec (source : Ix.Environment) (dedup : Dedup)
    (ordered : Array Name) (aliases : Std.HashMap Name Name) (groups : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) :
    expandSource source dedup ordered aliases groups keyAddr? =
      expandSourceSpec source dedup ordered aliases groups keyAddr? := by
  exact (expand_eq_core source dedup ordered aliases groups keyAddr?).symm

end Ix.CompileCert.Canon.CoreBridge
