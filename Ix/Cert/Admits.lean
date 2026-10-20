import Ix.Cert.Statement
import Ix.CompileCert.SourceConstructorPositions

/-! # Source acceptance admits every inductive block (N-READS, N1)

R12 (`Ix.CompileCert.SourceConstructorPositions`) reads the Source premises of
`inductive_reads` (safety, constructor positions, telescope arity) and R9a's
`ConstructorPositions` off `Admits env first`: the inductive block `first` heads
converts. This file derives `Admits` from Source acceptance:

* `mem_groupsOf`: the ingress's groups (`Ix.LeanIngress.groupsOf`) hold the
  group of every inductive stored under its block's first member (its loops
  only append: `mem_forIn_of_mem`, `mem_forIn_of_step`);
* `admits_of_checkSource`, `admits_of_sourceAccepts`: so an accepted check
  admits it, since every group of `groupsOf` converts
  (`Ix.LeanIngress.checkSource_converts`, through the structural `orderOf`);
* `source_premises_of_sourceAccepts`, `mkIndc_positions_of_sourceAccepts`:
  R12's outputs from Source acceptance.

The first member is taken as stored under its own name
(`(n, .inductInfo first) ∈ sub.consts.toList`): `Ix.Name`'s `==` compares
hashes, so a lookup by `get?` could answer for a hash-equal name. -/

namespace Ix.Cert.Admits

open Ix.LeanIngress
open Ix.CompileCert.Loop (idBind idPure)

/-- A loop in `Id` each of whose steps continues, keeping its state's elements. -/
def Grows {α G : Type} (f : α → Array G → Id (ForInStep (Array G))) : Prop :=
  ∀ a acc, ∃ b, f a acc = .yield b ∧ ∀ y, y ∈ acc → y ∈ b

/-- Such a loop keeps its initial elements. -/
theorem mem_forIn_of_mem {α G : Type} {f : α → Array G → Id (ForInStep (Array G))}
    (grows : Grows f) : ∀ (l : List α) (init : Array G) (x : G), x ∈ init →
      x ∈ Id.run (forIn l init f)
  | [], _, _, h => h
  | a :: l, init, x, h => by
    obtain ⟨b, hb, keep⟩ := grows a init
    rw [List.forIn_cons, hb]
    exact mem_forIn_of_mem grows l b x (keep x h)

/-- Such a loop holds every element one of its steps adds. -/
theorem mem_forIn_of_step {α G : Type} {f : α → Array G → Id (ForInStep (Array G))}
    (grows : Grows f) {a : α} {x : G} (adds : ∀ acc, ∃ b, f a acc = .yield b ∧ x ∈ b) :
    ∀ (l : List α), a ∈ l → ∀ init : Array G, x ∈ Id.run (forIn l init f)
  | [], h, _ => by cases h
  | a' :: l, h, init => by
    rw [List.forIn_cons]
    rcases List.mem_cons.1 h with rfl | h
    · obtain ⟨b, hb, hx⟩ := adds init
      rw [hb]
      exact mem_forIn_of_mem grows l b x hx
    · obtain ⟨b, hb, _⟩ := grows a' init
      rw [hb]
      exact mem_forIn_of_step grows adds l h b

theorem mem_groupsOf (env : Ix.Environment) (blocks : Ix.CondensedBlocks) {n : Ix.Name}
    {v : Ix.InductiveVal} (stored : (n, Ix.ConstantInfo.inductInfo v) ∈ env.consts.toList)
    (head : v.all[0]? = some n) :
    ∃ cands, inductiveGroup env v cands ∈ groupsOf env blocks := by
  unfold groupsOf
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, idBind, idPure]
  apply Exists.intro
  apply mem_forIn_of_mem
  · intro a acc
    dsimp only
    split
    · exact ⟨_, rfl, fun _ h => h⟩
    · exact ⟨_, rfl, fun _ h => Array.mem_push_of_mem _ h⟩
  apply mem_forIn_of_mem
  · intro a acc
    dsimp only
    split
    · exact ⟨_, rfl, fun _ h => Array.mem_push_of_mem _ h⟩
    · exact ⟨_, rfl, fun _ h => h⟩
  refine mem_forIn_of_step ?_ ?_ _ stored _
  · intro a acc
    dsimp only
    split
    · split
      · exact ⟨_, rfl, fun _ h => Array.mem_push_of_mem _ h⟩
      · exact ⟨_, rfl, fun _ h => h⟩
    · exact ⟨_, rfl, fun _ h => h⟩
  · intro acc
    dsimp only
    have hb : Option.any (fun x => x.beqRaw n) v.all[0]? = true := by
      simp [head, Ix.Name.beqRaw_iff]
    simp only [hb, ↓reduceIte]
    exact ⟨_, rfl, Array.mem_push_self⟩

open Ix.CompileCert.SourceConstructorPositions (Admits)

/-- **An accepted Source-mode check admits every inductive block** stored
under its first member: the block's group is one of `groupsOf`'s, and every
one of those converts (`checkSource_converts`). -/
theorem admits_of_checkSource {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env .source} (accepted : checkSource env blocks = .ok kenv) {n : Ix.Name}
    {first : Ix.InductiveVal} (stored : (n, Ix.ConstantInfo.inductInfo first) ∈ env.consts.toList)
    (head : first.all[0]? = some n) : Admits env first := by
  obtain ⟨cands, mem⟩ := mem_groupsOf env blocks stored head
  obtain ⟨converted, ok⟩ := checkSource_converts accepted _ mem
  exact ⟨cands, converted, ok⟩

/-- **An accepted bundled check admits every inductive block** stored under its
first member (`checkSourceBundled_converts`). -/
theorem admits_of_checkSourceBundled {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env .source} (accepted : checkSourceBundled env blocks = .ok kenv) {n : Ix.Name}
    {first : Ix.InductiveVal} (stored : (n, Ix.ConstantInfo.inductInfo first) ∈ env.consts.toList)
    (head : first.all[0]? = some n) : Admits env first := by
  obtain ⟨cands, mem⟩ := mem_groupsOf env blocks stored head
  obtain ⟨converted, ok⟩ := checkSourceBundled_converts accepted _ mem
  exact ⟨cands, converted, ok⟩

/-- **Source acceptance admits every inductive block of `sub`** stored under
its first member. -/
theorem admits_of_sourceAccepts {condense : Ix.Environment → Ix.CondensedBlocks}
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {envS : Ix.Kernel.Env .source} (accepted : SourceAccepts condense env roots sub envS) {n : Ix.Name}
    {first : Ix.InductiveVal} (stored : (n, Ix.ConstantInfo.inductInfo first) ∈ sub.consts.toList)
    (head : first.all[0]? = some n) : Admits sub first :=
  admits_of_checkSourceBundled accepted.2 stored head

open Ix.CompileM in
/-- **R12's Source premises of `inductive_reads`, from Source acceptance**:
the member's safety, its constructors' safety and positions, and their
telescopes' arity. -/
theorem source_premises_of_sourceAccepts {condense : Ix.Environment → Ix.CondensedBlocks}
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {envS : Ix.Kernel.Env .source} (accepted : SourceAccepts condense env roots sub envS) {n : Ix.Name}
    {first : Ix.InductiveVal} (stored : (n, Ix.ConstantInfo.inductInfo first) ∈ sub.consts.toList)
    (head : first.all[0]? = some n) (context : CompileEnv × BlockEnv)
    (free : context.1.surgeryFree = true) {source : Ix.InductiveVal}
    (member : source.cnst.name ∈ first.all.toList)
    (sourceFound : sub.consts.get? source.cnst.name = some (.inductInfo source))
    (agree : ∀ n ∈ source.ctors.toList, context.1.env.get? n = sub.consts.get? n)
    {constructors : Array Ix.ConstructorVal} {before : BlockState}
    (found : (Ix.CompileCert.rawRun (lookupInductiveConstructors source)
      (Ix.CompileCert.EmissionDispatch.singletonContext source.cnst.name context) before).1 =
        .ok constructors) :
    source.isUnsafe = false ∧ (∀ ctor ∈ constructors.toList, ctor.isUnsafe = false) ∧
      (∀ j (inside : j < constructors.size), constructors[j].cidx = j) ∧
      (∀ ctor ∈ constructors.toList, ∃ types body,
        Ix.CompileCert.ReaderSourceSpines.sourceStrip (source.numParams + ctor.numFields)
            ctor.cnst.type = some (types, body) ∧
          Ix.CompileCert.ReaderSourceSpines.SourceNonForall body) :=
  Ix.CompileCert.SourceConstructorPositions.source_premises context free
    (admits_of_sourceAccepts accepted stored head) member sourceFound agree found

open Ix.CompileM in
/-- **R9a's `ConstructorPositions` for the compiler's mutual members, from
Source acceptance.** -/
theorem mkIndc_positions_of_sourceAccepts {condense : Ix.Environment → Ix.CondensedBlocks}
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {envS : Ix.Kernel.Env .source} (accepted : SourceAccepts condense env roots sub envS) {n : Ix.Name}
    {first : Ix.InductiveVal} (stored : (n, Ix.ConstantInfo.inductInfo first) ∈ sub.consts.toList)
    (head : first.all[0]? = some n) (context : CompileEnv × BlockEnv) {i : Ix.InductiveVal}
    (member : i.cnst.name ∈ first.all.toList)
    (found : sub.consts.get? i.cnst.name = some (.inductInfo i))
    (agree : ∀ n ∈ i.ctors.toList, context.1.env.get? n = sub.consts.get? n)
    {state : BlockState} {m : Ix.MutConst}
    (ran : (Ix.CompileCert.rawRun (MutConst.mkIndc i) context state).1 = .ok m) :
    Ix.CompileCert.MutualProjections.ConstructorPositions m :=
  Ix.CompileCert.SourceConstructorPositions.mkIndc_positions context
    (admits_of_sourceAccepts accepted stored head) member found agree ran

end Ix.Cert.Admits
