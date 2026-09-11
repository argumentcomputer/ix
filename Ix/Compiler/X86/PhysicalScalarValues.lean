import Ix.Compiler.X86.PhysicalScalar

namespace Ix.Compiler.X86.PhysicalScalar

inductive Each {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Each relation [] []
  | cons {a b as bs} (head : relation a b) (tail : Each relation as bs) : Each relation (a :: as) (b :: bs)

theorem Each.length {α β : Type} {r : α → β → Prop} {as bs} (related : Each r as bs) : as.length = bs.length := by
  induction related <;> simp_all

theorem Each.lookup {α β : Type} {r : α → β → Prop} {as bs} (related : Each r as bs)
    {index : Nat} {a : α} (found : as[index]? = some a) : ∃ b, bs[index]? = some b ∧ r a b := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp at found; subst a; exact ⟨_, rfl, head⟩
    | succ index => exact ih found

theorem Each.append {α β : Type} {r : α → β → Prop} {as bs cs ds}
    (first : Each r as bs) (second : Each r cs ds) : Each r (as ++ cs) (bs ++ ds) := by
  induction first with
  | nil => exact second
  | cons head _ ih => exact .cons head ih

theorem Each.mono {α β : Type} {r s : α → β → Prop} {as bs}
    (related : Each r as bs) (imp : ∀ a b, r a b → s a b) : Each s as bs := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (imp _ _ head) ih

theorem each_mapM {α β : Type} {f : α → Option β} {as : List α} {bs : List β}
    (mapped : as.mapM f = some bs) : Each (fun a b => f a = some b) as bs := by
  induction as generalizing bs with
  | nil => simp at mapped; subst bs; exact .nil
  | cons a as ih =>
    cases head : f a with
    | none => simp [List.mapM_cons, head] at mapped
    | some b =>
      cases tail : as.mapM f with
      | none => simp [List.mapM_cons, head, tail] at mapped
      | some rest =>
        simp [List.mapM_cons, head, tail] at mapped
        subst bs
        exact .cons head (ih tail)

theorem Each.mapM {α β : Type} {f : α → Option β} {as : List α} {bs : List β}
    (related : Each (fun a b => f a = some b) as bs) : as.mapM f = some bs := by
  induction related with
  | nil => rfl
  | cons head _ ih => simp [List.mapM_cons, head, ih]

theorem array_each_mapM {α β : Type} {f : α → Option β} {as : Array α} {bs : Array β}
    (mapped : as.mapM f = some bs) : Each (fun a b => f a = some b) as.toList bs.toList := by
  apply each_mapM
  have same := congrArg (Option.map Array.toList) mapped
  change (Array.toList <$> as.mapM f) = some bs.toList at same
  simpa only [Array.toList_mapM, Option.map_some] using same

theorem each_array_mapM {α β : Type} {f : α → Option β} {as : Array α} {bs : Array β}
    (related : Each (fun a b => f a = some b) as.toList bs.toList) : as.mapM f = some bs := by
  simp [Array.mapM_eq_mapM_toList, related.mapM]

def rval (word : Word) : IxIR2.Eval.RVal := .lit (.nat word.toNat)

def EnvRel (bindings : Array Scalar.Atom) (native physical : Array Word) : Prop :=
  Each (fun atom word => atom.eval native = some word) bindings.toList physical.toList

theorem EnvRel.size {bindings native physical} (related : EnvRel bindings native physical) : bindings.size = physical.size := by
  simpa using related.length

theorem EnvRel.parameters (values : Array Word) : EnvRel (parameters values.size) values values := by
  suffices ∀ (xs : List Nat), (∀ i ∈ xs, i < values.size) →
      Each (fun atom word => atom.eval values = some word) (xs.map Scalar.Atom.var) (xs.map (fun i => values[i]!)) by
    have h := this (List.range values.size) (by simp)
    have same : (List.range values.size).map (fun i => values[i]!) = values.toList := by
      apply List.ext_getElem
      · simp
      · intro index left right
        simp at left
        simp [left]
    simpa [EnvRel, PhysicalScalar.parameters, same] using h
  intro xs bounds
  induction xs with
  | nil => exact .nil
  | cons index indices ih =>
    exact .cons (by simp [Scalar.Atom.eval, bounds index (by simp)])
      (ih (fun i h => bounds i (by simp [h])))

theorem atom_sound {bindings native physical source target}
    (related : EnvRel bindings native physical) (lowered : lowerAtom bindings source = some target) :
    ∃ word, target.eval native = some word ∧ IxIR2.Eval.resolveAtom (physical.map rval) source = .ok (rval word) := by
  cases source with
  | reg index =>
    obtain ⟨word, found, evaluated⟩ := related.lookup (by simpa [lowerAtom] using lowered)
    have found : physical[index]? = some word := by simpa using found
    exact ⟨word, evaluated, by simp [IxIR2.Eval.resolveAtom, found]⟩
  | erased => simp [lowerAtom] at lowered
  | lit literal =>
    cases literal with
    | nat number =>
      cases encoded : ExactNat.encode number with
      | none => simp [lowerAtom, encoded] at lowered
      | some word =>
        simp [lowerAtom, encoded] at lowered
        subst target
        exact ⟨word, rfl, by simp [IxIR2.Eval.resolveAtom, rval, ← ExactNat.encode_some_iff.mp encoded]⟩
    | _ => simp [lowerAtom] at lowered

theorem atom_resolves {bindings native physical source target word}
    (related : EnvRel bindings native physical) (lowered : lowerAtom bindings source = some target)
    (evaluated : target.eval native = some word) :
    IxIR2.Eval.resolveAtom (physical.map rval) source = .ok (rval word) := by
  obtain ⟨actual, value, resolved⟩ := atom_sound related lowered
  have same := Option.some.inj (value.symm.trans evaluated)
  subst actual
  exact resolved

theorem atom_push {atom : Scalar.Atom} {values : Array Word} {word : Word}
    (evaluated : atom.eval values = some word) (bound : Word) : atom.eval (values.push bound) = some word := by
  cases atom with
  | constant value => exact evaluated
  | var index =>
    have found : values[index]? = some word := evaluated
    obtain ⟨lt, eq⟩ := Array.getElem?_eq_some_iff.mp found
    simp [Scalar.Atom.eval, Array.getElem?_push, lt, eq, Nat.ne_of_lt lt]

theorem EnvRel.weaken {bindings native physical} (related : EnvRel bindings native physical) (word : Word) :
    EnvRel bindings (native.push word) physical := related.mono (fun _ _ value => atom_push value word)

theorem EnvRel.push {bindings native physical target word}
    (related : EnvRel bindings native physical) (evaluated : target.eval native = some word) :
    EnvRel (bindings.push target) native (physical.push word) := by
  simpa [EnvRel] using related.append (Each.cons evaluated Each.nil)

theorem EnvRel.bind {bindings native physical locals}
    (related : EnvRel bindings native physical) (size : native.size = locals) (word : Word) :
    EnvRel (bindings.push (.var locals)) (native.push word) (physical.push word) := by
  apply (related.weaken word).push
  simp [Scalar.Atom.eval, ← size]

theorem EnvRel.prepend {bindings native physical locals}
    (related : EnvRel bindings native physical) (size : native.size = locals) (word : Word) :
    EnvRel (#[.var locals] ++ bindings) (native.push word) (#[word] ++ physical) := by
  change Each _ _ _
  simp only [Array.toList_append, List.cons_append, List.nil_append]
  exact .cons (by simp [Scalar.Atom.eval, ← size]) (related.weaken word)

theorem resolves_each {physical : Array Word} {sources : List IxIR2.Atom} {words : List Word}
    (resolved : Each (fun source word => IxIR2.Eval.resolveAtom (physical.map rval) source = .ok (rval word)) sources words)
    (accumulator : Array IxIR2.Eval.RVal) :
    sources.foldlM (fun output source => do return output.push (← IxIR2.Eval.resolveAtom (physical.map rval) source)) accumulator =
      .ok (accumulator ++ (words.toArray.map rval)) := by
  induction resolved generalizing accumulator with
  | nil => simp [pure, Except.pure]
  | @cons source word sources words head tail ih =>
    simp only [List.foldlM_cons, head, bind, Except.bind, pure, Except.pure]
    have rest := ih (accumulator.push (rval word))
    simp only [bind, Except.bind, pure, Except.pure] at rest
    rw [rest]
    congr 1
    apply Array.ext'
    simp

theorem atoms_sound {bindings native physical sources targets}
    (related : EnvRel bindings native physical) (lowered : lowerAtoms bindings sources = some targets) :
    ∃ words, EnvRel targets native words ∧ targets.mapM (Scalar.Atom.eval native) = some words ∧
      IxIR2.Eval.resolveAtoms (physical.map rval) sources = .ok (words.map rval) := by
  have translated := array_each_mapM lowered
  have many : ∀ {ss ts}, Each (fun s t => lowerAtom bindings s = some t) ss ts →
      ∃ ws, Each (fun t w => t.eval native = some w) ts ws ∧
        Each (fun s w => IxIR2.Eval.resolveAtom (physical.map rval) s = .ok (rval w)) ss ws := by
    intro ss ts h
    induction h with
    | nil => exact ⟨[], .nil, .nil⟩
    | cons head tail ih =>
      obtain ⟨word, evaluated, resolved⟩ := atom_sound related head
      obtain ⟨words, values, resolutions⟩ := ih
      exact ⟨word :: words, .cons evaluated values, .cons resolved resolutions⟩
  obtain ⟨words, values, resolutions⟩ := many translated
  have env : EnvRel targets native words.toArray := by simpa [EnvRel] using values
  refine ⟨words.toArray, env, each_array_mapM env, ?_⟩
  simpa [IxIR2.Eval.resolveAtoms, ← Array.foldlM_toList] using resolves_each resolutions #[]

end Ix.Compiler.X86.PhysicalScalar
