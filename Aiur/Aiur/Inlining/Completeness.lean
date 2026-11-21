import Aiur.Inlining.Facts

namespace Aiur.Inlining
open Generic

variable [Field F] [DecidableEq F] {p q : Aiur.Program F} {names : List String}

/-- Retained calls keep their calling convention, with a certified expanded
body. This also covers static map leaves. -/
def ForwardCalls (p q : Aiur.Program F) (names : List String) : Prop :=
  ∀ n ∉ names, ∀ (args : List (SourceValue F)) ls body, prepareCall p n args = .ok (ls,body) →
    ∃ tree : Tree F, tree.source = body ∧ tree.Safe p names ∧
      prepareCall q n args = .ok (ls,tree.target)

theorem completeExpr (sameEnums : p.enums = q.enums) (forward : ForwardCalls p q names)
    (ev : Engine.EvalExpr (.ofProgram p) locals expr before result after) :
    ∀ tree : Tree F, tree.source = expr → tree.Safe p names →
      Engine.EvalExpr (.ofProgram q) locals tree.target before result after := by
  induction ev using Engine.EvalExpr.rec
    (motive_2 := fun ls es b vs a _ => ∀ trees : List (Tree F),
      trees.map Tree.source = es → (∀ t ∈ trees, t.Safe p names) →
      Engine.EvalArgs (.ofProgram q) ls (trees.map Tree.target) b vs a)
    (motive_3 := fun n xs b v a _ => ∀ (tree : Tree F) ls,
      prepareCall p n xs = .ok (ls,tree.source) → tree.Safe p names →
      Engine.EvalExpr (.ofProgram q) ls tree.target b v a) with
  | literal =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.literal.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      subst_vars; exact .literal
  | var found =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.var.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      subst_vars; exact .var found
  | tuple _ ih =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.tuple.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      exact .tuple (ih _ same safe)
  | construct _ ih =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.construct.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      rcases same with ⟨rfl,rfl,same⟩
      exact .construct (ih _ same safe)
  | project _ op ih =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.project.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      rcases same with ⟨same,rfl⟩
      exact .project (ih _ same safe) op
  | letValue _ matched _ ih1 ih2 =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.letValue.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      rcases same with ⟨rfl,first,last⟩
      exact .letValue (ih1 _ first safe.1) matched (ih2 _ last safe.2)
  | store _ ih =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.store.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      exact .store (ih _ same safe)
  | load _ op ih =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.load.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      exact .load (ih _ same safe) op
  | hint _ typed ih =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.hint.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      rcases same with ⟨rfl,same,rfl⟩
      exact .hint (ih _ same safe) (by simpa only [Engine.World.ofProgram,sameEnums] using typed)
  | neg _ op ih =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.neg.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      exact .neg (ih _ same safe) op
  | binary _ _ op ih1 ih2 =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.binary.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      rcases same with ⟨rfl,first,last⟩
      exact .binary (ih1 _ first safe.1) (ih2 _ last safe.2) op
  | assertEq _ _ op ih1 ih2 =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.assertEq.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      rcases same with ⟨rfl,first,last⟩
      exact .assertEq (ih1 _ first safe.1) (ih2 _ last safe.2) op
  | @call ls es b values middle n v a arguments callee ih1 ih2 =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.call.injEq, reduceCtorEq] at same <;> simp only [Tree.Safe] at safe <;> simp only [Tree.target]
      · rcases same with ⟨rfl,args⟩
        cases callee with
        | intro prepared body =>
            obtain ⟨out,source,valid,preparedOut⟩ := forward _ safe.1 _ _ _ prepared
            exact .call (ih1 _ args safe.2)
              (.intro preparedOut (ih2 out _ (by simpa only [source, Engine.World.ofProgram] using prepared) valid))
      · rename_i f children body
        rcases same with ⟨rfl,args⟩
        obtain ⟨found,_,bodySource,scope,bodySafe,childrenSafe⟩ := safe
        cases callee with
        | intro prepared evaluated =>
            rcases prepareCall_spec prepared with ⟨g,looked,types,formed,rfl,rfl⟩ | ⟨value,absent,_⟩
            · have eq : g = f := Option.some.inj (looked.symm.trans found)
              subst g
              have bodyEv := ih2 body _ (by simpa only [bodySource, Engine.World.ofProgram] using prepared) bodySafe
              have length : (f.params.map Prod.fst).length = values.length := by
                simpa using congrArg List.length types
              have binding := PatternLowering.bindingsList_binders (f.params.map Prod.fst) values length
              have scope : hasScope (((f.params.map Prod.fst).zip values).map Prod.fst) body.target = true := by
                rwa [List.map_fst_zip (by omega)]
              apply Engine.EvalExpr.letValue (bindings := (f.params.map Prod.fst).zip values) (.tuple (ih1 _ args childrenSafe))
              · simpa only [Aiur.Pattern.bindings, List.map_map, Function.comp_def] using binding
              · exact ((isolated_iff scope).mp (OpenCore.of_closed bodyEv)).close
            · simp [found] at absent
  | @matchValue ls e b input mid arms bs body v a scrutinee selected branch ih1 ih2 =>
      intro tree same safe
      cases tree <;> simp only [Tree.source, Aiur.Expr.matchValue.injEq, reduceCtorEq] at same
      simp only [Tree.Safe] at safe
      simp only [Tree.target]
      rename_i value armsOut
      rcases same with ⟨valueSame,rfl⟩
      rw [select_map] at selected
      obtain ⟨⟨bindings,chosen⟩,chosenEq,same⟩ := Option.map_eq_some_iff.mp selected
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
      obtain ⟨pat,member,_⟩ := choose_member chosenEq
      exact .matchValue (ih1 _ valueSame safe.1)
        (by rw [select_map,chosenEq]; rfl) (ih2 chosen rfl (safe.2 (pat,chosen) member))
  | nil =>
      rename_i trees same safe
      cases trees <;> simp_all only [List.map_nil, List.map_cons, reduceCtorEq]
      exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i trees same safe
      cases trees with
      | nil => simp at same
      | cons head tail =>
          obtain ⟨headEq,tailEq⟩ := List.cons.inj same
          exact .cons (ih1 head headEq (safe _ (by simp)))
            (ih2 tail tailEq (fun t ht => safe _ (by simp [ht])))
  | intro prepared _ ih =>
      rename_i tree ls preparedTree safe
      obtain ⟨rfl,same⟩ := Prod.mk.inj (Except.ok.inj (prepared.symm.trans preparedTree))
      exact ih tree same.symm safe

end Aiur.Inlining
