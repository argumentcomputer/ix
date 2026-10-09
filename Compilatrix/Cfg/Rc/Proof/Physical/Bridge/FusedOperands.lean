import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FusedWords
import Compilatrix.Rt.Proof.Block

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Rt Compilatrix.Rt.Rc.Procs
open Compilatrix.Rt.Proof (LiveArg ArgReads Fused otherUses ListRel)

theorem fused_operand_word
    {addresses : AddressMap} {D : Nat → Prop} {bound : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses D bound source target)
    {f : Fir.FunId} {a : Fir.Arg} {operand : Lir.Arg} {value : Own.RVal}
    (lowered : Lower.operand f a = .ok (some operand)) (live : LiveArg D a)
    (evaluated : Own.evalArg source a = some value) :
    ∃ word, operand.eval target = some word ∧ valueWord addresses value = some word ∧
      ArgReads bound operand := by
  cases a with
  | var x =>
    simp only [Lower.operand, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at lowered
    subst operand
    obtain ⟨word, hw, hr⟩ := related.word evaluated (live x rfl)
    refine ⟨word, hr, hw, ?_⟩
    intro y equal
    cases equal
    exact related.dom evaluated
  | lit literal =>
    cases literal with
    | nat n =>
      simp only [Own.evalArg, Option.some.injEq] at evaluated
      subst value
      cases hn : natWord n with
      | none => simp [Lower.operand, hn, pure, Except.pure] at lowered
      | some word =>
        simp only [Lower.operand, hn, Option.map_some, pure, Except.pure,
          Except.ok.injEq, Option.some.injEq] at lowered
        subst operand
        exact ⟨word, rfl, hn, ArgReads.imm _ _⟩
    | str s => simp [Lower.operand, throw, throwThe, MonadExceptOf.throw] at lowered
  | erased =>
    simp only [Lower.operand, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at lowered
    subst operand
    simp only [Own.evalArg, Option.some.injEq] at evaluated
    subst value
    exact ⟨erasedWord, rfl, rfl, ArgReads.imm _ _⟩

theorem fused_operands_words
    {addresses : AddressMap} {D : Nat → Prop} {bound : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses D bound source target) {f : Fir.FunId} :
    ∀ {args : List Fir.Arg} {operands : List Lir.Arg},
      Lower.operands f args = .ok (some operands) → (∀ a ∈ args, LiveArg D a) →
      ∀ {fields : List Own.RVal}, Own.evalArgs source args = some fields →
      ∃ words, Lir.evalArgs target operands = some words ∧
        ListRel (fun value word => valueWord addresses value = some word) fields words ∧
        ∀ operand ∈ operands, ArgReads bound operand
  | [], operands, lowered, _, fields, evaluated => by
    simp only [Lower.operands, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at lowered
    subst operands
    simp only [Own.evalArgs, Option.some.injEq] at evaluated
    subst fields
    exact ⟨[], rfl, .nil, by simp⟩
  | a :: args, operands, lowered, live, fields, evaluated => by
    simp only [Lower.operands, bind, Except.bind] at lowered
    cases ha : Lower.operand f a with
    | error e => simp [ha] at lowered
    | ok oa =>
      cases has : Lower.operands f args with
      | error e => simp [ha, has] at lowered
      | ok oas =>
        simp only [ha, has, pure, Except.pure, Except.ok.injEq] at lowered
        cases oa with
        | none => simp at lowered
        | some operand =>
          cases oas with
          | none => simp at lowered
          | some tail =>
            simp only [Option.some.injEq] at lowered
            subst operands
            simp only [Own.evalArgs] at evaluated
            cases hva : Own.evalArg source a with
            | none => simp [hva] at evaluated
            | some value =>
              cases hvas : Own.evalArgs source args with
              | none => simp [hva, hvas] at evaluated
              | some values =>
                simp only [hva, hvas, Option.some.injEq] at evaluated
                subst fields
                obtain ⟨word, hw, hv, hr⟩ := fused_operand_word related ha (live a (by simp)) hva
                obtain ⟨words, hws, hvs, hrs⟩ := fused_operands_words related has
                  (fun a' member => live a' (by simp [member])) hvas
                refine ⟨word :: words, by simp [hw, hws], .cons hv hvs, ?_⟩
                intro operand' member
                rcases List.mem_cons.mp member with rfl | member
                · exact hr
                · exact hrs operand' member

/-- The actual fusable/useCounts receipt excludes each operand read anywhere
in the consumed function. No variable-membership liveness assumption is used. -/
theorem fused_instruction_live
    {tables : Lower.Tables} {function : Cfg.Fun} {index : Nat} {block : Cfg.Block}
    (blockLookup : function.blocks[index]? = some block)
    {x : Nat} {rhs : Own.Rhs} (instruction : Cfg.Instr.bind x rhs ∈ block.body) :
    ∀ y ∈ Cfg.Check.rhsVars rhs, ¬ Fused tables function y := by
  intro y member omitted
  apply (Rt.Proof.fused_once omitted blockLookup).1
  simp only [otherUses, List.mem_append, List.mem_flatMap]
  exact .inl ⟨.bind x rhs, instruction, member⟩

theorem fused_argVars_member {args : List Fir.Arg} {y : Nat}
    (member : Fir.Arg.var y ∈ args) : y ∈ Cfg.Check.argVars args := by
  induction args with
  | nil => simp at member
  | cons a args ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp [Cfg.Check.argVars]
    · cases a <;> simp_all [Cfg.Check.argVars]

theorem fused_args_live {D : Nat → Prop} {args : List Fir.Arg}
    (variables : ∀ y ∈ Cfg.Check.argVars args, ¬ D y) : ∀ a ∈ args, LiveArg D a := by
  intro a member y equal
  subst a
  exact variables y (fused_argVars_member member)

theorem fused_call_live
    {tables : Lower.Tables} {function : Cfg.Fun} {index : Nat} {block : Cfg.Block}
    (blockLookup : function.blocks[index]? = some block)
    {x callee : Nat} {args : List Fir.Arg}
    (instruction : Cfg.Instr.bind x (.fir (.call callee args)) ∈ block.body) :
    ∀ a ∈ args, LiveArg (Fused tables function) a := by
  apply fused_args_live
  exact fused_instruction_live blockLookup instruction

theorem fused_alloc_live
    {tables : Lower.Tables} {function : Cfg.Fun} {index : Nat} {block : Cfg.Block}
    (blockLookup : function.blocks[index]? = some block)
    {x : Nat} {ctor : Fir.CtorInfo} {args : List Fir.Arg} {kind : Own.Kind}
    (instruction : Cfg.Instr.bind x (.alloc ctor args kind) ∈ block.body) :
    ∀ a ∈ args, LiveArg (Fused tables function) a := by
  apply fused_args_live
  exact fused_instruction_live blockLookup instruction

theorem fused_prim_live
    {tables : Lower.Tables} {function : Cfg.Fun} {index : Nat} {block : Cfg.Block}
    (blockLookup : function.blocks[index]? = some block)
    {x : Nat} {op : Lam.Prim} {args : List Fir.Arg}
    (instruction : Cfg.Instr.bind x (.fir (.prim op args)) ∈ block.body) :
    ∀ a ∈ args, LiveArg (Fused tables function) a := by
  apply fused_args_live
  exact fused_instruction_live blockLookup instruction

theorem fused_projection_live
    {tables : Lower.Tables} {function : Cfg.Fun} {index : Nat} {block : Cfg.Block}
    (blockLookup : function.blocks[index]? = some block)
    {x y field : Nat} {key : Key.CtorKey}
    (instruction : Cfg.Instr.bind x (.proj y key field) ∈ block.body) :
    ¬ Fused tables function y :=
  fused_instruction_live blockLookup instruction y (by simp [Cfg.Check.rhsVars])

theorem fused_term_live
    {tables : Lower.Tables} {function : Cfg.Fun} {index : Nat} {block : Cfg.Block}
    (blockLookup : function.blocks[index]? = some block)
    {args : List Fir.Arg} (reads : ∀ y, Fir.Arg.var y ∈ args → y ∈ otherUses block) :
    ∀ a ∈ args, LiveArg (Fused tables function) a := by
  intro a member y equal omitted
  subst a
  exact (Rt.Proof.fused_once omitted blockLookup).1 (reads y member)

theorem unfused_switch_live
    {tables : Lower.Tables} {function : Cfg.Fun} {index : Nat} {block : Cfg.Block}
    (blockLookup : function.blocks[index]? = some block)
    {x : Nat} {alts : List (Key.CtorKey × Cfg.Edge)} {default : Option Cfg.Edge}
    (term : block.term = .switch x alts default)
    (unfused : Lower.fusable tables (Lower.useCounts function) block = none) :
    ¬ Fused tables function x := by
  intro omitted
  have fused := (Rt.Proof.fused_once omitted blockLookup).2 alts default term
  simp [unfused] at fused

/-- Actual consumed calls include native allocation wrappers and inc/dec
markers. Their lowered operands are derived without a LiveArg premise. -/
theorem fused_call_operands_words
    {addresses : AddressMap} {tables : Lower.Tables} {function : Cfg.Fun} {bound : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses (Fused tables function) bound source target)
    {index : Nat} {block : Cfg.Block} (blockLookup : function.blocks[index]? = some block)
    {x callee f : Nat} {args : List Fir.Arg}
    (instruction : Cfg.Instr.bind x (.fir (.call callee args)) ∈ block.body)
    {operands : List Lir.Arg} (lowered : Lower.operands f args = .ok (some operands))
    {values : List Own.RVal} (evaluated : Own.evalArgs source args = some values) :
    ∃ words, Lir.evalArgs target operands = some words ∧
      ListRel (fun value word => valueWord addresses value = some word) values words ∧
      ∀ operand ∈ operands, ArgReads bound operand :=
  fused_operands_words related lowered (fused_call_live blockLookup instruction) evaluated

/-- The comparison feeding a fused branch uses represented operands even
though its result register is absent. Liveness follows from the real block. -/
theorem fused_compare_operands_words
    {addresses : AddressMap} {tables : Lower.Tables} {function : Cfg.Fun} {bound : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses (Fused tables function) bound source target)
    {index : Nat} {block : Cfg.Block} (blockLookup : function.blocks[index]? = some block)
    {init : List Cfg.Instr} {cond : Lir.Cond} {a b : Fir.Arg}
    (receipt : Lower.fusable tables (Lower.useCounts function) block = some (init, cond, a, b))
    {f : Nat} {operands : List Lir.Arg}
    (lowered : Lower.operands f [a, b] = .ok (some operands))
    {values : List Own.RVal} (evaluated : Own.evalArgs source [a, b] = some values) :
    ∃ words, Lir.evalArgs target operands = some words ∧
      ListRel (fun value word => valueWord addresses value = some word) values words ∧
      ∀ operand ∈ operands, ArgReads bound operand := by
  obtain ⟨x, op, _, _, body, _, _, _, _⟩ := Rt.Proof.fusable_some receipt
  apply fused_operands_words related lowered ?_ evaluated
  apply fused_prim_live blockLookup (x := x) (op := op)
  rw [body]
  simp

/-- An omitted source result may be populated while its native register is
absent. This rules out using full EnvWordsBelow at a fused cursor. -/
theorem fused_result_without_register
    (addresses : AddressMap) {tables : Lower.Tables} {function : Cfg.Fun}
    {x bound : Nat} (real : x < bound) (omitted : Fused tables function x) (value : Own.RVal) :
    FusedWords addresses (Fused tables function) bound
      ((.leaf : Own.Env).insert x value) ({} : Lir.Env) ∧
      ¬ Compilatrix.Cfg.Rc.Native.EnvWordsBelow addresses bound
        ((.leaf : Own.Env).insert x value) ({} : Lir.Env) := by
  refine ⟨FusedWords.empty.bind_omitted real omitted value, ?_⟩
  intro full
  obtain ⟨word, _, impossible⟩ := full x value real (Src.NatMap.get?_insert_self ..)
  simp at impossible















end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
