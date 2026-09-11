import Ix.Compiler.IxIR0.Recursion
import Ix.Compiler.IxIR0.Mono

/-!
# Forward simulation for the first recovered recursor

Fuel only witnesses termination. The proof constructs successful executions
of the eager tuple fold and the derived accumulator recursor for every finite
list, then uses determinism to transport any successful literal execution.
No evaluator, cost counter, or ownership rule is changed by recovery.
-/

namespace Ix.Compiler.IxIR0.Recursion

open Ix.Compiler.Ixon (Address Uses)

def Evaluates (ctx : Ctx) (env : List Value) (expr : Expr) (value : Value) : Prop :=
  ∃ fuel, eval ctx fuel env expr = .ok value

def Applies (ctx : Ctx) (fn arg value : Value) : Prop :=
  ∃ fuel, apply ctx fuel fn arg = .ok value

@[simp] private theorem bindOk {α β : Type} (a : α) (f : α → Except Err β) :
    (Except.ok a >>= f) = f a := rfl

theorem Evaluates.unique {ctx : Ctx} {env : List Value} {expr : Expr} {v w : Value}
    (hv : Evaluates ctx env expr v) (hw : Evaluates ctx env expr w) : v = w := by
  obtain ⟨fv, hv⟩ := hv
  obtain ⟨fw, hw⟩ := hw
  have hv' := eval_mono (fuel' := fv + fw) (by omega) hv
  have hw' := eval_mono (fuel' := fv + fw) (by omega) hw
  exact Except.ok.inj (hv'.symm.trans hw')

theorem evaluatesVar {ctx : Ctx} {env : List Value} {i : Nat} {v : Value}
    (h : env[i]? = some v) : Evaluates ctx env (.var i) v := by
  refine ⟨1, ?_⟩
  simp [eval, h]

theorem evaluatesLam (ctx : Ctx) (env : List Value) (u : Uses) (body : Expr) :
    Evaluates ctx env (.lam u body) (.clos u env body) :=
  ⟨1, by simp [eval]⟩

theorem evaluatesErased (ctx : Ctx) (env : List Value) :
    Evaluates ctx env .erased .erased := ⟨1, by simp [eval]⟩

theorem evaluatesLit (ctx : Ctx) (env : List Value) (l : Literal) :
    Evaluates ctx env (.lit l) (.lit l) := ⟨1, by simp [eval]⟩

theorem evaluatesDef {ctx : Ctx} {env : List Value} {address : Address}
    {world : Ixon.Owned} {body : Expr} {v : Value}
    (hdecl : ctx.env address = some (.defn world body))
    (hbody : Evaluates ctx [] body v) : Evaluates ctx env (.ref address) v := by
  obtain ⟨fuel, hbody⟩ := hbody
  refine ⟨fuel + 1, ?_⟩
  rw [eval.eq_def]
  simpa only [hdecl] using hbody

theorem evaluatesRecursor {ctx : Ctx} {env : List Value} {address : Address}
    {arity : Nat} {natLit : Bool} {rules : Array RecRule}
    (hdecl : ctx.env address = some (.recursor arity natLit rules)) :
    Evaluates ctx env (.ref address) (.pap (.rec_ address (arity + 1)) []) := by
  refine ⟨1, ?_⟩
  simp [eval, hdecl]

theorem evaluatesNullary {ctx : Ctx} {env : List Value} {address : Address} {tag : Nat}
    (hdecl : ctx.env address = some (.ctor tag 0)) :
    Evaluates ctx env (.ref address) (.ctor address tag []) := by
  refine ⟨4, ?_⟩
  simp [eval, saturate, fire, Head.arity, hdecl]

theorem evaluatesBinary {ctx : Ctx} {env : List Value} {address : Address} {tag : Nat}
    (hdecl : ctx.env address = some (.ctor tag 2)) :
    Evaluates ctx env (.ref address) (.pap (.ctor address tag 2) []) := by
  refine ⟨2, ?_⟩
  simp [eval, saturate, Head.arity, hdecl]

theorem appliesBinaryFirst (ctx : Ctx) (address : Address) (tag : Nat) (v : Value) :
    Applies ctx (.pap (.ctor address tag 2) []) v
      (.pap (.ctor address tag 2) [v]) := by
  refine ⟨2, ?_⟩
  simp [apply, saturate, Head.arity]

theorem appliesBinaryLast (ctx : Ctx) (address : Address) (tag : Nat) (v w : Value) :
    Applies ctx (.pap (.ctor address tag 2) [v]) w (.ctor address tag [v, w]) := by
  refine ⟨4, ?_⟩
  simp [apply, saturate, fire, Head.arity]

theorem appliesClosure {ctx : Ctx} {env : List Value} {u : Uses} {body : Expr}
    {arg v : Value} (h : Evaluates ctx (arg :: env) body v) :
    Applies ctx (.clos u env body) arg v := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel + 1, ?_⟩
  rw [apply.eq_def]
  exact h

theorem evaluatesApp {ctx : Ctx} {env : List Value} {fn arg : Expr} {f a v : Value}
    (hf : Evaluates ctx env fn f) (ha : Evaluates ctx env arg a)
    (happly : Applies ctx f a v) : Evaluates ctx env (.app fn arg) v := by
  obtain ⟨ff, hf⟩ := hf
  obtain ⟨fa, ha⟩ := ha
  obtain ⟨fp, happly⟩ := happly
  have hf' := eval_mono (fuel' := ff + fa + fp) (by omega) hf
  have ha' := eval_mono (fuel' := ff + fa + fp) (by omega) ha
  have hp' := apply_mono (fuel' := ff + fa + fp) (by omega) happly
  refine ⟨ff + fa + fp + 1, ?_⟩
  rw [eval.eq_def]
  simp only [hf', ha', hp', bindOk]

theorem evaluatesLet {ctx : Ctx} {env : List Value} {u : Uses} {val body : Expr}
    {w v : Value} (hv : Evaluates ctx env val w)
    (hb : Evaluates ctx (w :: env) body v) : Evaluates ctx env (.letE u val body) v := by
  obtain ⟨fv, hv⟩ := hv
  obtain ⟨fb, hb⟩ := hb
  have hv' := eval_mono (fuel' := fv + fb) (by omega) hv
  have hb' := eval_mono (fuel' := fv + fb) (by omega) hb
  refine ⟨fv + fb + 1, ?_⟩
  rw [eval.eq_def]
  simp only [hv', hb', bindOk]

theorem evaluatesFirst {ctx : Ctx} {env : List Value} {expr : Expr}
    {address : Address} {tag : Nat} {v w : Value}
    (h : Evaluates ctx env expr (.ctor address tag [v, w])) :
    Evaluates ctx env (.proj 0 expr) v := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel + 1, ?_⟩
  rw [eval.eq_def]
  simp only [h, bindOk, List.getElem?_cons_zero]

theorem evaluatesGhost {ctx : Ctx} {env : List Value} {body : Expr} {v : Value}
    (h : Evaluates ctx (.erased :: env) body v) :
    Evaluates ctx env (ghost body) v :=
  evaluatesApp (evaluatesLam ctx env .many body) (evaluatesErased ctx env)
    (appliesClosure h)

theorem evaluatesCtor2 {ctx : Ctx} {env : List Value} {address : Address}
    {tag : Nat} {left right : Expr} {v w : Value}
    (hdecl : ctx.env address = some (.ctor tag 2))
    (hv : Evaluates ctx env left v) (hw : Evaluates ctx env right w) :
    Evaluates ctx env (app2 (.ref address) left right) (.ctor address tag [v, w]) :=
  evaluatesApp
    (evaluatesApp (evaluatesBinary hdecl) hv (appliesBinaryFirst ctx address tag v))
    hw (appliesBinaryLast ctx address tag v w)

/-- One actual recursor dispatch, with the evaluator's field and pre-major
environment order. This lemma does not assume any recursive progress. -/
theorem appliesRecursor {ctx : Ctx} {address majorAddress : Address}
    {numArgs tag : Nat} {rules : Array RecRule} {rule : RecRule}
    {pre fields : List Value} {v : Value}
    (hdecl : ctx.env address = some (.recursor numArgs false rules))
    (hpre : pre.length = numArgs) (hrule : rules[tag]? = some rule)
    (hfields : fields.length = rule.fields)
    (hbody : Evaluates ctx
      (fields.reverse ++ pre.reverse ++ [.pap (.rec_ address (numArgs + 1)) []]) rule.rhs v) :
    Applies ctx (.pap (.rec_ address (numArgs + 1)) pre)
      (.ctor majorAddress tag fields) v := by
  obtain ⟨fuel, hbody⟩ := hbody
  refine ⟨fuel + 3, ?_⟩
  rw [apply.eq_def]
  dsimp only
  rw [saturate.eq_def]
  simp only [Head.arity, List.length_append, List.length_singleton, hpre,
    beq_self_eq_true, ite_true]
  rw [fire.eq_def]
  simpa [hdecl, majorCtor, hrule, hfields] using hbody

theorem appliesAccumulator (ctx : Ctx) (address : Address) (v : Value) :
    Applies ctx (.pap (.rec_ address 2) []) v (.pap (.rec_ address 2) [v]) := by
  refine ⟨2, ?_⟩
  simp [apply, saturate, Head.arity]

def listValue (s : Schema) : List Value → Value
  | [] => .ctor s.nil 0 []
  | v :: vs => .ctor s.cons 1 [v, listValue s vs]

def baseValue (s : Schema) : Value :=
  .ctor s.pack 0 [.clos .many [.erased] (.var 0), .ctor s.unit 1 []]

def stepValue (s : Schema) : Value :=
  .clos .many [] (.lam .many (.lam .many
    (packExpr s (ghost (.lam .many (stepBody s))) (.var 0))))

/-- The literal evaluator retains every recursively built below tuple in
the next tuple and in the function's closure environment. -/
def belowValue (s : Schema) : List Value → Value
  | [] => baseValue s
  | v :: vs =>
      let below := belowValue s vs
      .ctor s.pack 0
        [.clos .many [.erased, below, listValue s vs, v] (stepBody s), below]

def belowFunction (s : Schema) : List Value → Value
  | [] => .clos .many [.erased] (.var 0)
  | v :: vs =>
      .clos .many [.erased, belowValue s vs, listValue s vs, v] (stepBody s)

def belowTail (s : Schema) : List Value → Value
  | [] => .ctor s.unit 1 []
  | _ :: vs => belowValue s vs

theorem belowValue_eq (s : Schema) (vs : List Value) :
    belowValue s vs = .ctor s.pack 0 [belowFunction s vs, belowTail s vs] := by
  cases vs <;> rfl

def reverseOnto (s : Schema) : List Value → Value → Value
  | [], acc => acc
  | v :: vs, acc => reverseOnto s vs (.ctor s.cons 1 [v, acc])

theorem reverseOnto_listValue (s : Schema) (vs acc : List Value) :
    reverseOnto s vs (listValue s acc) = listValue s (vs.reverse ++ acc) := by
  induction vs generalizing acc with
  | nil => rfl
  | cons v vs ih =>
      change reverseOnto s vs (listValue s (v :: acc)) = _
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem evaluatesBase {ctx : Ctx} {s : Schema} (hs : SourceMatches ctx.env s)
    (env : List Value) : Evaluates ctx env (.ref s.base) (baseValue s) :=
  evaluatesDef hs.base (evaluatesCtor2 hs.pack
    (evaluatesGhost (evaluatesLam _ _ _ _)) (evaluatesGhost (evaluatesNullary hs.unit)))

theorem evaluatesStep {ctx : Ctx} {s : Schema} (hs : SourceMatches ctx.env s)
    (env : List Value) : Evaluates ctx env (.ref s.step) (stepValue s) :=
  evaluatesDef hs.step (evaluatesLam _ _ _ _)

theorem appliesTernaryFirst (ctx : Ctx) (address : Address) (v : Value) :
    Applies ctx (.pap (.rec_ address 3) []) v (.pap (.rec_ address 3) [v]) := by
  refine ⟨2, ?_⟩
  simp [apply, saturate, Head.arity]

theorem appliesTernaryNext (ctx : Ctx) (address : Address) (v w : Value) :
    Applies ctx (.pap (.rec_ address 3) [v]) w (.pap (.rec_ address 3) [v, w]) := by
  refine ⟨2, ?_⟩
  simp [apply, saturate, Head.arity]

theorem appliesStepFirst (ctx : Ctx) (s : Schema) (head : Value) :
    Applies ctx (stepValue s) head
      (.clos .many [head] (.lam .many
        (packExpr s (ghost (.lam .many (stepBody s))) (.var 0)))) :=
  appliesClosure (evaluatesLam _ _ _ _)

theorem appliesStepNext (ctx : Ctx) (s : Schema) (head tail : Value) :
    Applies ctx (.clos .many [head] (.lam .many
        (packExpr s (ghost (.lam .many (stepBody s))) (.var 0)))) tail
      (.clos .many [tail, head] (packExpr s (ghost (.lam .many (stepBody s))) (.var 0))) :=
  appliesClosure (evaluatesLam _ _ _ _)

theorem appliesStepLast {ctx : Ctx} {s : Schema} (hs : SourceMatches ctx.env s)
    (head tail below : Value) :
    Applies ctx (.clos .many [tail, head]
        (packExpr s (ghost (.lam .many (stepBody s))) (.var 0))) below
      (.ctor s.pack 0 [.clos .many [.erased, below, tail, head] (stepBody s), below]) :=
  appliesClosure (evaluatesCtor2 hs.pack
    (evaluatesGhost (evaluatesLam _ _ _ _)) (evaluatesVar (by rfl)))

/-- The literal fold is total on finite constructor lists. Every recursive
call in this proof is the evaluator's actual eager call on the tail. -/
theorem sourceTuple {ctx : Ctx} {s : Schema} (hs : SourceMatches ctx.env s)
    (vs : List Value) :
    Applies ctx (.pap (.rec_ s.recursor 3) [baseValue s, stepValue s])
      (listValue s vs) (belowValue s vs) := by
  induction vs with
  | nil =>
      apply appliesRecursor hs.recursor (pre := [baseValue s, stepValue s])
        (tag := 0) (by rfl) (by rfl) (by rfl)
      exact evaluatesVar (by rfl)
  | cons v vs ih =>
      apply appliesRecursor hs.recursor (pre := [baseValue s, stepValue s])
        (tag := 1) (by rfl) (by rfl) (by rfl)
      exact evaluatesApp
        (evaluatesApp
          (evaluatesApp (evaluatesVar (by rfl)) (evaluatesVar (by rfl))
            (appliesStepFirst ctx s v))
          (evaluatesVar (by rfl)) (appliesStepNext ctx s v (listValue s vs)))
        (evaluatesApp
          (evaluatesApp
            (evaluatesApp (evaluatesVar (by rfl)) (evaluatesVar (by rfl))
              (appliesTernaryFirst ctx s.recursor (baseValue s)))
            (evaluatesVar (by rfl)) (appliesTernaryNext ctx s.recursor (baseValue s) (stepValue s)))
          (evaluatesVar (by rfl)) ih)
        (appliesStepLast hs v (listValue s vs) (belowValue s vs))

/-- Applying the literal function demands only the immediate tail's function
projection. Its other below data remains observationally irrelevant. -/
theorem sourceFunction {ctx : Ctx} {s : Schema} (hs : SourceMatches ctx.env s)
    (vs : List Value) (acc : Value) :
    Applies ctx (belowFunction s vs) acc (reverseOnto s vs acc) := by
  induction vs generalizing acc with
  | nil => exact appliesClosure (evaluatesVar (by rfl))
  | cons v vs ih =>
      apply appliesClosure
      apply evaluatesApp
        (evaluatesFirst (address := s.pack) (tag := 0) (w := belowTail s vs) ?_)
        (evaluatesCtor2 hs.cons (evaluatesVar (by rfl)) (evaluatesVar (by rfl)))
        (ih (.ctor s.cons 1 [v, acc]))
      rw [← belowValue_eq]
      exact evaluatesVar (by rfl)

/-- The derived recursor computes the same accumulator fold by direct self
application. No tuple or function value is allocated by its rules. -/
theorem directLoop {ctx : Ctx} {s : Schema} {address : Address}
    (hcons : ctx.env s.cons = some (.ctor 1 2))
    (hrec : ctx.env address = some (directRecursor s))
    (vs : List Value) (acc : Value) :
    Applies ctx (.pap (.rec_ address 2) [acc]) (listValue s vs)
      (reverseOnto s vs acc) := by
  induction vs generalizing acc with
  | nil =>
      apply appliesRecursor hrec (pre := [acc]) (tag := 0) (by rfl) (by rfl) (by rfl)
      exact evaluatesVar (by rfl)
  | cons v vs ih =>
      apply appliesRecursor hrec (pre := [acc]) (tag := 1) (by rfl) (by rfl) (by rfl)
      exact evaluatesApp
        (evaluatesApp (evaluatesVar (by rfl))
          (evaluatesCtor2 hcons (evaluatesVar (by rfl)) (evaluatesVar (by rfl)))
          (appliesAccumulator ctx address (.ctor s.cons 1 [v, acc])))
        (evaluatesVar (by rfl)) (ih (.ctor s.cons 1 [v, acc]))

theorem literalRun {ctx : Ctx} {s : Schema} {env : List Value}
    {major accumulator : Expr} {vs : List Value} {acc : Value}
    (hs : SourceMatches ctx.env s)
    (hmajor : Evaluates ctx env major (listValue s vs))
    (hacc : Evaluates ctx env accumulator acc) :
    Evaluates ctx env (literalCall s major accumulator) (reverseOnto s vs acc) := by
  have htuple := evaluatesApp
    (evaluatesApp
      (evaluatesApp (evaluatesDef hs.alias (evaluatesRecursor hs.recursor))
        (evaluatesBase hs env) (appliesTernaryFirst ctx s.recursor (baseValue s)))
      (evaluatesStep hs env) (appliesTernaryNext ctx s.recursor (baseValue s) (stepValue s)))
    hmajor (sourceTuple hs vs)
  rw [belowValue_eq] at htuple
  exact evaluatesApp (evaluatesFirst htuple) hacc (sourceFunction hs vs acc)

theorem directRun {ctx : Ctx} {s : Schema} {address : Address} {env : List Value}
    {major accumulator : Expr} {vs : List Value} {acc : Value}
    (hcons : ctx.env s.cons = some (.ctor 1 2))
    (hrec : ctx.env address = some (directRecursor s))
    (hmajor : Evaluates ctx env major (listValue s vs))
    (hacc : Evaluates ctx env accumulator acc) :
    Evaluates ctx env (directCall address major accumulator) (reverseOnto s vs acc) :=
  evaluatesApp
    (evaluatesApp (evaluatesRecursor hrec) hacc (appliesAccumulator ctx address acc))
    hmajor (directLoop hcons hrec vs acc)

/-- The schema theorem is independent of ground input syntax: it covers
arbitrary element values, arbitrary accumulators, and every successful
literal fuel. Source and target execute the actual IxIR₀ evaluator. -/
theorem recursorForwardSimulation {source target : Ctx} {s : Schema} {address : Address}
    (hs : SourceMatches source.env s)
    (hcons : target.env s.cons = some (.ctor 1 2))
    (hrec : target.env address = some (directRecursor s))
    (vs : List Value) (acc : Value) {sourceFuel : Nat} {value : Value}
    (hsource : eval source sourceFuel [acc, listValue s vs]
      (literalCall s (.var 1) (.var 0)) = .ok value) :
    ∃ targetFuel, eval target targetFuel [acc, listValue s vs]
      (directCall address (.var 1) (.var 0)) = .ok value := by
  have hliteral := literalRun hs (vs := vs) (acc := acc)
    (evaluatesVar (env := [acc, listValue s vs]) (i := 1) (by rfl))
    (evaluatesVar (i := 0) (by rfl))
  have hvalue := Evaluates.unique ⟨sourceFuel, hsource⟩ hliteral
  rw [hvalue]
  exact directRun hcons hrec (evaluatesVar (by rfl)) (evaluatesVar (by rfl))

def natValues (ns : List Nat) : List Value := ns.map (fun n => .lit (.nat n))

theorem literalListRun {ctx : Ctx} {s : Schema} (hs : SourceMatches ctx.env s)
    (env : List Value) (ns : List Nat) :
    Evaluates ctx env (literalList s ns) (listValue s (natValues ns)) := by
  induction ns with
  | nil => exact evaluatesGhost (evaluatesNullary hs.nil)
  | cons n ns ih =>
      exact evaluatesCtor2 hs.cons (evaluatesGhost (evaluatesLit _ _ _)) ih

theorem directListRun {ctx : Ctx} {s : Schema}
    (hnil : ctx.env s.nil = some (.ctor 0 0))
    (hcons : ctx.env s.cons = some (.ctor 1 2)) (env : List Value) (ns : List Nat) :
    Evaluates ctx env (directList s ns) (listValue s (natValues ns)) := by
  induction ns with
  | nil => exact evaluatesNullary hnil
  | cons n ns ih => exact evaluatesCtor2 hcons (evaluatesLit _ _ _) ih

def Plan.value (p : Plan) : Value :=
  let reversed := reverseOnto p.schema (natValues p.values) (.ctor p.schema.nil 0 [])
  match p.retainedAlias with
  | none => reversed
  | some pair => .ctor pair 0 [reversed, listValue p.schema (natValues p.values)]

theorem literalMainRun {ctx : Ctx} {p : Plan}
    (hs : SourceMatches ctx.env p.schema) (ha : p.aliasMatches ctx.env) :
    Evaluates ctx [] p.literalMain p.value := by
  cases hpair : p.retainedAlias with
  | none =>
      simpa only [Plan.literalMain, Plan.value, hpair] using
        literalRun hs (literalListRun hs [] p.values) (evaluatesGhost (evaluatesNullary hs.nil))
  | some pair =>
      have hp : ctx.env pair = some (.ctor 0 2) := by
        simpa only [Plan.aliasMatches, hpair] using ha
      simp only [Plan.literalMain, Plan.value, hpair]
      exact evaluatesLet (literalListRun hs [] p.values)
        (evaluatesCtor2 hp
          (literalRun hs (evaluatesVar (by rfl)) (evaluatesGhost (evaluatesNullary hs.nil)))
          (evaluatesVar (by rfl)))

theorem directMainRun {ctx : Ctx} {p : Plan} {address : Address}
    (ht : TargetMatches ctx.env p address) :
    Evaluates ctx [] (p.directMain address) p.value := by
  cases hpair : p.retainedAlias with
  | none =>
      simpa only [Plan.directMain, Plan.value, hpair] using
        directRun ht.cons ht.recursor (directListRun ht.nil ht.cons [] p.values)
          (evaluatesNullary ht.nil)
  | some pair =>
      have hp : ctx.env pair = some (.ctor 0 2) := by
        simpa only [Plan.aliasMatches, hpair] using ht.alias
      simp only [Plan.directMain, Plan.value, hpair]
      exact evaluatesLet (directListRun ht.nil ht.cons [] p.values)
        (evaluatesCtor2 hp
          (directRun ht.cons ht.recursor (evaluatesVar (by rfl)) (evaluatesNullary ht.nil))
          (evaluatesVar (by rfl)))

theorem Checked.sourceEvaluates {declarations : List (Address × Decl)} {main : Expr}
    (checked : Checked declarations main) :
    Evaluates { env := Env.ofList declarations } [] main checked.plan.value := by
  simpa only [checked.mainEq] using
    evaluatesDef (env := []) checked.entry (literalMainRun checked.source checked.alias)

/-- Exact checked whole-entry preservation, including removal of the
source-only argument wrappers and optional retention of the input alias. -/
theorem Recovered.forwardSimulation {declarations : List (Address × Decl)} {main : Expr}
    (result : Recovered declarations main) {sourceFuel : Nat} {value : Value}
    (hsource : eval { env := Env.ofList declarations } sourceFuel [] main = .ok value) :
    ∃ targetFuel,
      eval { env := Env.ofList (targetDeclarations result.checked.plan result.address) }
        targetFuel [] (result.checked.plan.directMain result.address) = .ok value := by
  have hvalue := Evaluates.unique ⟨sourceFuel, hsource⟩ result.checked.sourceEvaluates
  rw [hvalue]
  exact directMainRun result.target

/-- Failed or unsupported proposals keep the literal execution; successful
proposals use the exact checked replacement. Callers supply no rewrite facts.
-/
theorem Selection.forwardSimulation {declarations : List (Address × Decl)} {main : Expr}
    (selection : Selection declarations main) {sourceFuel : Nat} {value : Value}
    (hsource : eval { env := Env.ofList declarations } sourceFuel [] main = .ok value) :
    ∃ targetFuel, eval { env := Env.ofList selection.declarations }
      targetFuel [] selection.main = .ok value := by
  cases selection with
  | literal reason => exact ⟨sourceFuel, hsource⟩
  | recovered result => exact result.forwardSimulation hsource

end Ix.Compiler.IxIR0.Recursion
