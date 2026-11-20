import IxAIRefine.Core.Obs

/-! # Inversion of observed derivations in continuation form

The path lemmas rewritten by `ix/combined/obs_rewrite.py --fuse` invert a derivation with these
lemmas instead of the existential `*_inv` lemmas of `IxAIRefine.Core.Obs`. Checking cost in
IxVM grows with the number of subterms that mention a bound variable times their binder depth;
these lemmas keep both small.

## One construct

`h.X_elim k` hands the components of `h.X_inv` to the continuation `k`: the proof term is one
application and one telescope of binders, where destructuring the existential of `X_inv` builds
one `Exists.casesOn` or `And.casesOn` per component, each carrying the remaining statement. -/

namespace Aiur.Generic.SourceSemantics

variable {F : Type} [Field F] [DecidableEq F] {world : World F} {types : Types}
  {locals : Environment F Nat} {before after : Heap F} {result : SourceValue F}
  {calls : List (Call F)} {K : Prop}

theorem ObsExpr.letValue_elim {pat : Pattern F} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue pat e rest) before result after calls)
    (k : ∀ input middle bindings calls₁ calls₂,
      ObsExpr world types locals e before input middle calls₁ →
      world.matchPattern types middle pat input = .ok (some bindings) →
      ObsExpr world types (bindings ++ locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  cases h with | letValue value matched body => exact k _ _ _ _ _ value matched body rfl

theorem ObsExpr.call_elim {name : String} {typeArgs : Option (List Ty)} {args : List (Expr F)}
    (h : ObsExpr world types locals (.call name typeArgs args) before result after calls)
    (k : ∀ values middle calls₁ calls₂,
      ObsArgs world types locals args before values middle calls₁ →
      ObsFn world (instanceName types name typeArgs) values middle result after calls₂ →
      calls = calls₁ ++ ⟨instanceName types name typeArgs, values, middle⟩ :: calls₂ → K) : K := by
  cases h with | call arguments callee => exact k _ _ _ _ arguments callee rfl

theorem ObsExpr.binary_elim {op : BinOp} {lhs rhs : Expr F}
    (h : ObsExpr world types locals (.binary op lhs rhs) before result after calls)
    (k : ∀ x y middle calls₁ calls₂, ObsExpr world types locals lhs before x middle calls₁ →
      ObsExpr world types locals rhs middle y after calls₂ → evalBinOp op x y = .ok result →
      calls = calls₁ ++ calls₂ → K) : K := by
  cases h with | binary left right operation => exact k _ _ _ _ _ left right operation rfl

theorem ObsExpr.var_elim {name : String}
    (h : ObsExpr world types locals (.var name) before result after calls)
    (k : locals.find? (·.1 == name) = some (name, result) → after = before → calls = [] → K) :
    K := by
  cases h with | var lookup => exact k lookup rfl rfl

theorem ObsExpr.literal_elim {x : F}
    (h : ObsExpr world types locals (.literal x) before result after calls)
    (k : result = .field x → after = before → calls = [] → K) : K := by
  cases h; exact k rfl rfl rfl

theorem ObsExpr.index_elim {e : Expr F} {i : Nat}
    (h : ObsExpr world types locals (.index e i) before result after calls)
    (k : ∀ input, ObsExpr world types locals e before input after calls →
      projectValue input i = .ok result → K) : K := by
  cases h with | index value projected => exact k _ value projected

theorem ObsExpr.project_elim {e : Expr F} {i : Nat}
    (h : ObsExpr world types locals (.project e i) before result after calls)
    (k : ∀ input, ObsExpr world types locals e before input after calls →
      projectValue input i = .ok result → K) : K := by
  cases h with | project value projected => exact k _ value projected

theorem ObsExpr.tuple_elim {es : List (Expr F)}
    (h : ObsExpr world types locals (.tuple es) before result after calls)
    (k : ∀ values, ObsArgs world types locals es before values after calls →
      result = .tuple values → K) : K := by
  cases h with | tuple items => exact k _ items rfl

theorem ObsExpr.array_elim {es : List (Expr F)}
    (h : ObsExpr world types locals (.array es) before result after calls)
    (k : ∀ values, ObsArgs world types locals es before values after calls →
      result = .tuple values → K) : K := by
  cases h with | array items => exact k _ items rfl

theorem ObsExpr.builtin_elim {op : Builtin} {es : List (Expr F)}
    (h : ObsExpr world types locals (.builtin op es) before result after calls)
    (k : ∀ values, ObsArgs world types locals es before values after calls →
      op.apply values = .ok result → K) : K := by
  cases h with | builtin items applied => exact k _ items applied

theorem ObsExpr.hint_elim {t : Ty} {key : Expr F} {channel : String}
    (h : ObsExpr world types locals (.hint t key channel) before result after calls)
    (k : ∀ input value, ObsExpr world types locals key before input after calls →
      world.typed (t.subst types).toCore value = true → result = value.toValue → K) : K := by
  cases h with | hint key typed => exact k _ _ key typed rfl

theorem ObsArgs.nil_elim {values : List (SourceValue F)}
    (h : ObsArgs world types locals [] before values after calls)
    (k : values = [] → after = before → calls = [] → K) : K := by
  cases h; exact k rfl rfl rfl

theorem ObsArgs.cons_elim {e : Expr F} {es : List (Expr F)} {values : List (SourceValue F)}
    (h : ObsArgs world types locals (e :: es) before values after calls)
    (k : ∀ v vs middle calls₁ calls₂, values = v :: vs →
      ObsExpr world types locals e before v middle calls₁ →
      ObsArgs world types locals es middle vs after calls₂ → calls = calls₁ ++ calls₂ → K) : K := by
  cases h with | cons head tail => exact k _ _ _ _ _ rfl head tail rfl

end Aiur.Generic.SourceSemantics

namespace Aiur.Generic.SourceSemantics

variable {F : Type} [Field F] [DecidableEq F] {world : World F} {types : Types} {K : Prop}

omit [Field F] [DecidableEq F] in
theorem matchListWith_cons_elim {A : Type}
    {f : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {p : A} {ps : List A} {vs : List (SourceValue F)} {bs : Environment F Nat}
    (h : matchListWith f (p :: ps) vs = .ok (some bs))
    (k : ∀ v vs' b1 b2, vs = v :: vs' → f p v = .ok (some b1) →
      matchListWith f ps vs' = .ok (some b2) → bs = b1 ++ b2 → K) : K := by
  obtain ⟨v, vs', b1, b2, e1, e2, e3, e4⟩ := matchListWith_cons_inv h
  exact k v vs' b1 b2 e1 e2 e3 e4

omit [Field F] [DecidableEq F] in
theorem matchListWith_nil_elim {A : Type}
    {f : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {vs : List (SourceValue F)} {bs : Environment F Nat}
    (h : matchListWith f [] vs = .ok (some bs)) (k : vs = [] → bs = [] → K) : K :=
  k (matchListWith_nil_inv h).1 (matchListWith_nil_inv h).2

omit [Field F] in
theorem matchPattern_tuple_elim {ps : List (Pattern F)} {v : SourceValue F} {heap : Heap F}
    {bs : Environment F Nat} (h : world.matchPattern types heap (.tuple ps) v = .ok (some bs))
    (k : ∀ vs, v = .tuple vs → ps.length = vs.length →
      matchListWith (world.matchPattern types heap) ps vs = .ok (some bs) → K) : K := by
  obtain ⟨vs, e1, e2, e3⟩ := matchPattern_tuple_inv h
  exact k vs e1 e2 e3

omit [Field F] in
theorem matchPattern_array_elim {ps : List (Pattern F)} {v : SourceValue F} {heap : Heap F}
    {bs : Environment F Nat} (h : world.matchPattern types heap (.array ps) v = .ok (some bs))
    (k : ∀ vs, v = .tuple vs → ps.length = vs.length →
      matchListWith (world.matchPattern types heap) ps vs = .ok (some bs) → K) : K := by
  obtain ⟨vs, e1, e2, e3⟩ := matchPattern_array_inv h
  exact k vs e1 e2 e3

end Aiur.Generic.SourceSemantics

/-! ## Whole shapes

A variable argument, a projection `x[i]` of a variable argument, a call of a plain function, and
a `let` binding a name or a flat tuple or array of names (one lemma per width, 2 to 20), each
inverted in one step. A variable's value is given by its lookup `locals.find? … = some (n, x)`,
which a use site proves by `rfl`, so its continuation receives the value itself. -/

namespace Aiur.Generic.SourceSemantics.Fused

variable {F : Type} [Field F] [DecidableEq F] {world : World F} {types : Types}
  {locals : Environment F Nat} {before after : Heap F} {result : SourceValue F}
  {calls : List (Call F)} {K : Prop}

theorem var_val {n : String} {x : SourceValue F}
    (h : ObsExpr world types locals (.var n) before result after calls)
    (l : locals.find? (·.1 == n) = some (n, x)) :
    result = x ∧ after = before ∧ calls = [] := by
  obtain ⟨e, rfl, rfl⟩ := h.var_inv
  rw [l] at e
  cases e
  exact ⟨rfl, rfl, rfl⟩

theorem var_is {n : String} {x : SourceValue F}
    (h : ObsExpr world types locals (.var n) before result after calls)
    (l : locals.find? (·.1 == n) = some (n, x))
    (k : x = result → after = before → calls = [] → K) : K := by
  obtain ⟨e, rfl, rfl⟩ := h.var_inv
  rw [l] at e
  cases e
  exact k rfl rfl rfl

theorem args_var_cons {n : String} {x : SourceValue F} {es : List (Expr F)}
    {values : List (SourceValue F)}
    (h : ObsArgs world types locals (.var n :: es) before values after calls)
    (l : locals.find? (·.1 == n) = some (n, x))
    (k : ∀ vs, values = x :: vs → ObsArgs world types locals es before vs after calls → K) : K := by
  obtain ⟨v, vs, m, c1, c2, rfl, d, a, rfl⟩ := h.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := var_val d l
  exact k vs rfl a

theorem args_index_var_cons {n : String} {i : Nat} {x : SourceValue F} {es : List (Expr F)}
    {values : List (SourceValue F)}
    (h : ObsArgs world types locals (.index (.var n) i :: es) before values after calls)
    (l : locals.find? (·.1 == n) = some (n, x))
    (k : ∀ v vs, projectValue x i = .ok v → values = v :: vs →
      ObsArgs world types locals es before vs after calls → K) : K := by
  obtain ⟨v, vs, m, c1, c2, rfl, d, a, rfl⟩ := h.cons_inv
  obtain ⟨p, e, pr⟩ := d.index_inv
  obtain ⟨rfl, rfl, rfl⟩ := var_val e l
  exact k v vs pr rfl a

theorem call_plain {name : String} {args : List (Expr F)}
    (h : ObsExpr world types locals (.call name (some []) args) before result after calls)
    (k : ∀ values middle calls₁ calls₂, ObsArgs world types locals args before values middle calls₁ →
      ObsFn world name values middle result after calls₂ →
      calls = calls₁ ++ ⟨name, values, middle⟩ :: calls₂ → K) : K := by
  obtain ⟨values, middle, c1, c2, a, ev, rfl⟩ := h.call_inv
  rw [instanceName_plain_some] at ev
  exact k values middle c1 c2 a ev (by rw [instanceName_plain_some])

theorem let_bind {n : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.bind n) e rest) before result after calls)
    (k : ∀ v middle calls₁ calls₂, ObsExpr world types locals e before v middle calls₁ →
      ObsExpr world types ((n, v) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain rfl := matchPattern_bind_inv mt
  exact k v m c1 c2 de dr rfl

theorem let_tuple_2 {a1 a2 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2]) e rest) before result after calls)
    (k : ∀ v1 v2 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml2
  exact k _ _ m c1 c2 de dr rfl

theorem let_tuple_3 {a1 a2 a3 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml3
  exact k _ _ _ m c1 c2 de dr rfl

theorem let_tuple_4 {a1 a2 a3 a4 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml4
  exact k _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_5 {a1 a2 a3 a4 a5 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml5
  exact k _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_6 {a1 a2 a3 a4 a5 a6 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml6
  exact k _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_7 {a1 a2 a3 a4 a5 a6 a7 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml7
  exact k _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_8 {a1 a2 a3 a4 a5 a6 a7 a8 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml8
  exact k _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_9 {a1 a2 a3 a4 a5 a6 a7 a8 a9 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml9
  exact k _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_10 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml10
  exact k _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_11 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml11
  exact k _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_12 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml12
  exact k _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_13 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml13
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_14 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml14
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_15 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml15
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_16 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15, .bind a16]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: (a16, v16) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨v16, ws16, b16, b16', rfl, mt16, ml16, rfl⟩ := matchListWith_cons_inv ml15
  obtain rfl := matchPattern_bind_inv mt16
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml16
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_17 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15, .bind a16, .bind a17]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: (a16, v16) :: (a17, v17) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨v16, ws16, b16, b16', rfl, mt16, ml16, rfl⟩ := matchListWith_cons_inv ml15
  obtain rfl := matchPattern_bind_inv mt16
  obtain ⟨v17, ws17, b17, b17', rfl, mt17, ml17, rfl⟩ := matchListWith_cons_inv ml16
  obtain rfl := matchPattern_bind_inv mt17
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml17
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_18 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15, .bind a16, .bind a17, .bind a18]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: (a16, v16) :: (a17, v17) :: (a18, v18) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨v16, ws16, b16, b16', rfl, mt16, ml16, rfl⟩ := matchListWith_cons_inv ml15
  obtain rfl := matchPattern_bind_inv mt16
  obtain ⟨v17, ws17, b17, b17', rfl, mt17, ml17, rfl⟩ := matchListWith_cons_inv ml16
  obtain rfl := matchPattern_bind_inv mt17
  obtain ⟨v18, ws18, b18, b18', rfl, mt18, ml18, rfl⟩ := matchListWith_cons_inv ml17
  obtain rfl := matchPattern_bind_inv mt18
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml18
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_19 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15, .bind a16, .bind a17, .bind a18, .bind a19]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: (a16, v16) :: (a17, v17) :: (a18, v18) :: (a19, v19) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨v16, ws16, b16, b16', rfl, mt16, ml16, rfl⟩ := matchListWith_cons_inv ml15
  obtain rfl := matchPattern_bind_inv mt16
  obtain ⟨v17, ws17, b17, b17', rfl, mt17, ml17, rfl⟩ := matchListWith_cons_inv ml16
  obtain rfl := matchPattern_bind_inv mt17
  obtain ⟨v18, ws18, b18, b18', rfl, mt18, ml18, rfl⟩ := matchListWith_cons_inv ml17
  obtain rfl := matchPattern_bind_inv mt18
  obtain ⟨v19, ws19, b19, b19', rfl, mt19, ml19, rfl⟩ := matchListWith_cons_inv ml18
  obtain rfl := matchPattern_bind_inv mt19
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml19
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_tuple_20 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.tuple [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15, .bind a16, .bind a17, .bind a18, .bind a19, .bind a20]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: (a16, v16) :: (a17, v17) :: (a18, v18) :: (a19, v19) :: (a20, v20) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_tuple_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨v16, ws16, b16, b16', rfl, mt16, ml16, rfl⟩ := matchListWith_cons_inv ml15
  obtain rfl := matchPattern_bind_inv mt16
  obtain ⟨v17, ws17, b17, b17', rfl, mt17, ml17, rfl⟩ := matchListWith_cons_inv ml16
  obtain rfl := matchPattern_bind_inv mt17
  obtain ⟨v18, ws18, b18, b18', rfl, mt18, ml18, rfl⟩ := matchListWith_cons_inv ml17
  obtain rfl := matchPattern_bind_inv mt18
  obtain ⟨v19, ws19, b19, b19', rfl, mt19, ml19, rfl⟩ := matchListWith_cons_inv ml18
  obtain rfl := matchPattern_bind_inv mt19
  obtain ⟨v20, ws20, b20, b20', rfl, mt20, ml20, rfl⟩ := matchListWith_cons_inv ml19
  obtain rfl := matchPattern_bind_inv mt20
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml20
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_2 {a1 a2 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2]) e rest) before result after calls)
    (k : ∀ v1 v2 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml2
  exact k _ _ m c1 c2 de dr rfl

theorem let_array_3 {a1 a2 a3 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml3
  exact k _ _ _ m c1 c2 de dr rfl

theorem let_array_4 {a1 a2 a3 a4 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml4
  exact k _ _ _ _ m c1 c2 de dr rfl

theorem let_array_5 {a1 a2 a3 a4 a5 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml5
  exact k _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_6 {a1 a2 a3 a4 a5 a6 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml6
  exact k _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_7 {a1 a2 a3 a4 a5 a6 a7 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml7
  exact k _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_8 {a1 a2 a3 a4 a5 a6 a7 a8 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml8
  exact k _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_9 {a1 a2 a3 a4 a5 a6 a7 a8 a9 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml9
  exact k _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_10 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml10
  exact k _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_11 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml11
  exact k _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_12 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml12
  exact k _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_13 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml13
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_14 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml14
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_15 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml15
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_16 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15, .bind a16]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: (a16, v16) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨v16, ws16, b16, b16', rfl, mt16, ml16, rfl⟩ := matchListWith_cons_inv ml15
  obtain rfl := matchPattern_bind_inv mt16
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml16
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_17 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15, .bind a16, .bind a17]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: (a16, v16) :: (a17, v17) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨v16, ws16, b16, b16', rfl, mt16, ml16, rfl⟩ := matchListWith_cons_inv ml15
  obtain rfl := matchPattern_bind_inv mt16
  obtain ⟨v17, ws17, b17, b17', rfl, mt17, ml17, rfl⟩ := matchListWith_cons_inv ml16
  obtain rfl := matchPattern_bind_inv mt17
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml17
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_18 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15, .bind a16, .bind a17, .bind a18]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: (a16, v16) :: (a17, v17) :: (a18, v18) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨v16, ws16, b16, b16', rfl, mt16, ml16, rfl⟩ := matchListWith_cons_inv ml15
  obtain rfl := matchPattern_bind_inv mt16
  obtain ⟨v17, ws17, b17, b17', rfl, mt17, ml17, rfl⟩ := matchListWith_cons_inv ml16
  obtain rfl := matchPattern_bind_inv mt17
  obtain ⟨v18, ws18, b18, b18', rfl, mt18, ml18, rfl⟩ := matchListWith_cons_inv ml17
  obtain rfl := matchPattern_bind_inv mt18
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml18
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_19 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15, .bind a16, .bind a17, .bind a18, .bind a19]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: (a16, v16) :: (a17, v17) :: (a18, v18) :: (a19, v19) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨v16, ws16, b16, b16', rfl, mt16, ml16, rfl⟩ := matchListWith_cons_inv ml15
  obtain rfl := matchPattern_bind_inv mt16
  obtain ⟨v17, ws17, b17, b17', rfl, mt17, ml17, rfl⟩ := matchListWith_cons_inv ml16
  obtain rfl := matchPattern_bind_inv mt17
  obtain ⟨v18, ws18, b18, b18', rfl, mt18, ml18, rfl⟩ := matchListWith_cons_inv ml17
  obtain rfl := matchPattern_bind_inv mt18
  obtain ⟨v19, ws19, b19, b19', rfl, mt19, ml19, rfl⟩ := matchListWith_cons_inv ml18
  obtain rfl := matchPattern_bind_inv mt19
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml19
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

theorem let_array_20 {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 : String} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue (.array [.bind a1, .bind a2, .bind a3, .bind a4, .bind a5, .bind a6, .bind a7, .bind a8, .bind a9, .bind a10, .bind a11, .bind a12, .bind a13, .bind a14, .bind a15, .bind a16, .bind a17, .bind a18, .bind a19, .bind a20]) e rest) before result after calls)
    (k : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 middle calls₁ calls₂,
      ObsExpr world types locals e before (.tuple [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20]) middle calls₁ →
      ObsExpr world types ((a1, v1) :: (a2, v2) :: (a3, v3) :: (a4, v4) :: (a5, v5) :: (a6, v6) :: (a7, v7) :: (a8, v8) :: (a9, v9) :: (a10, v10) :: (a11, v11) :: (a12, v12) :: (a13, v13) :: (a14, v14) :: (a15, v15) :: (a16, v16) :: (a17, v17) :: (a18, v18) :: (a19, v19) :: (a20, v20) :: locals) rest middle result after calls₂ →
      calls = calls₁ ++ calls₂ → K) : K := by
  obtain ⟨v, m, bs, c1, c2, de, mt, dr, rfl⟩ := h.letValue_inv
  obtain ⟨ws, rfl, -, ml⟩ := matchPattern_array_inv mt
  obtain ⟨v1, ws1, b1, b1', rfl, mt1, ml1, rfl⟩ := matchListWith_cons_inv ml
  obtain rfl := matchPattern_bind_inv mt1
  obtain ⟨v2, ws2, b2, b2', rfl, mt2, ml2, rfl⟩ := matchListWith_cons_inv ml1
  obtain rfl := matchPattern_bind_inv mt2
  obtain ⟨v3, ws3, b3, b3', rfl, mt3, ml3, rfl⟩ := matchListWith_cons_inv ml2
  obtain rfl := matchPattern_bind_inv mt3
  obtain ⟨v4, ws4, b4, b4', rfl, mt4, ml4, rfl⟩ := matchListWith_cons_inv ml3
  obtain rfl := matchPattern_bind_inv mt4
  obtain ⟨v5, ws5, b5, b5', rfl, mt5, ml5, rfl⟩ := matchListWith_cons_inv ml4
  obtain rfl := matchPattern_bind_inv mt5
  obtain ⟨v6, ws6, b6, b6', rfl, mt6, ml6, rfl⟩ := matchListWith_cons_inv ml5
  obtain rfl := matchPattern_bind_inv mt6
  obtain ⟨v7, ws7, b7, b7', rfl, mt7, ml7, rfl⟩ := matchListWith_cons_inv ml6
  obtain rfl := matchPattern_bind_inv mt7
  obtain ⟨v8, ws8, b8, b8', rfl, mt8, ml8, rfl⟩ := matchListWith_cons_inv ml7
  obtain rfl := matchPattern_bind_inv mt8
  obtain ⟨v9, ws9, b9, b9', rfl, mt9, ml9, rfl⟩ := matchListWith_cons_inv ml8
  obtain rfl := matchPattern_bind_inv mt9
  obtain ⟨v10, ws10, b10, b10', rfl, mt10, ml10, rfl⟩ := matchListWith_cons_inv ml9
  obtain rfl := matchPattern_bind_inv mt10
  obtain ⟨v11, ws11, b11, b11', rfl, mt11, ml11, rfl⟩ := matchListWith_cons_inv ml10
  obtain rfl := matchPattern_bind_inv mt11
  obtain ⟨v12, ws12, b12, b12', rfl, mt12, ml12, rfl⟩ := matchListWith_cons_inv ml11
  obtain rfl := matchPattern_bind_inv mt12
  obtain ⟨v13, ws13, b13, b13', rfl, mt13, ml13, rfl⟩ := matchListWith_cons_inv ml12
  obtain rfl := matchPattern_bind_inv mt13
  obtain ⟨v14, ws14, b14, b14', rfl, mt14, ml14, rfl⟩ := matchListWith_cons_inv ml13
  obtain rfl := matchPattern_bind_inv mt14
  obtain ⟨v15, ws15, b15, b15', rfl, mt15, ml15, rfl⟩ := matchListWith_cons_inv ml14
  obtain rfl := matchPattern_bind_inv mt15
  obtain ⟨v16, ws16, b16, b16', rfl, mt16, ml16, rfl⟩ := matchListWith_cons_inv ml15
  obtain rfl := matchPattern_bind_inv mt16
  obtain ⟨v17, ws17, b17, b17', rfl, mt17, ml17, rfl⟩ := matchListWith_cons_inv ml16
  obtain rfl := matchPattern_bind_inv mt17
  obtain ⟨v18, ws18, b18, b18', rfl, mt18, ml18, rfl⟩ := matchListWith_cons_inv ml17
  obtain rfl := matchPattern_bind_inv mt18
  obtain ⟨v19, ws19, b19, b19', rfl, mt19, ml19, rfl⟩ := matchListWith_cons_inv ml18
  obtain rfl := matchPattern_bind_inv mt19
  obtain ⟨v20, ws20, b20, b20', rfl, mt20, ml20, rfl⟩ := matchListWith_cons_inv ml19
  obtain rfl := matchPattern_bind_inv mt20
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml20
  exact k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m c1 c2 de dr rfl

end Aiur.Generic.SourceSemantics.Fused
