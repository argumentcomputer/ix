import IxCC.Anf.Defun
import IxCC.Anf.Proof.Unfold

/-! # P8's dispatchers compute `applyN`

The target half of the dispatcher lemma (`docs/closures-design.md`, "Proof
obligation"): what P8's dispatcher of arity `m` does, in Anf's semantics,
with a closure cell `con (clo s.key j) fs` of a source `s` (`j` arguments
supplied, `fs` its captures and those arguments) and `m` further arguments,
when no source before `s` in the dispatcher's alternatives has `s`'s key:

* `m` is the number of parameters still missing (`dispatch_exact`): the call
  of the dispatcher is the call of `s` on `fs` and the arguments, two charges
  in all (the dispatcher's and `s`'s);
* `m` is fewer (`dispatch_under`): the cell with `j + m` arguments, one
  charge;
* `m` is more (`dispatch_over`): the call of `s` on `fs` and the first `r`
  arguments, then the call of the dispatcher of arity `m - r` on the result
  and the rest, each two charges.

Where the source applies a closure (`applyN`) it charges once per
application: the dispatcher's own call is the target's extra charge. -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

open IxCC.Sem (Result later later_succ)

/-! ## Atoms -/

theorem evalAtoms_append {ρ : List Val} : ∀ {as bs : List Atom} {xs ys : List Val},
    evalAtoms ρ as = some xs → evalAtoms ρ bs = some ys → evalAtoms ρ (as ++ bs) = some (xs ++ ys)
  | [], _, xs, _, ha, hb => by
    rw [evalAtoms_nil, Option.some.injEq] at ha
    subst ha
    exact hb
  | a :: as, bs, xs, ys, ha, hb => by
    rw [evalAtoms_cons] at ha
    cases hv : a.eval ρ with
    | none => rw [hv] at ha; cases ha
    | some v =>
      cases hr : evalAtoms ρ as with
      | none => rw [hv, hr] at ha; cases ha
      | some vs =>
        rw [hv, hr] at ha
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at ha
        subst ha
        rw [List.cons_append, evalAtoms_cons, hv, evalAtoms_append hr hb]
        simp only [Option.bind_some, Option.map_some, List.cons_append]

theorem downFrom_succ (top c : Nat) : downFrom top (c + 1) = .var top :: downFrom (top - 1) c := by
  simp only [downFrom, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.sub_zero]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, Atom.var.injEq]
  omega

/-- The variables of `xs`, bound last to first after `ys`, read back `xs`. -/
theorem evalAtoms_downFrom : ∀ (ys xs ρ : List Val),
    evalAtoms (ys ++ xs.reverse ++ ρ) (downFrom (ys.length + xs.length - 1) xs.length) = some xs
  | _, [], _ => rfl
  | ys, x :: xs, ρ => by
    have ht : ys.length + (x :: xs).length - 1 = ys.length + xs.length := by
      simp only [List.length_cons]; omega
    have he : ys ++ (x :: xs).reverse ++ ρ = ys ++ xs.reverse ++ (x :: ρ) := by
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    have h1 : (ys ++ xs.reverse ++ x :: ρ)[ys.length + xs.length]? = (xs.reverse ++ x :: ρ)[xs.length]? := by
      rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    have h2 : (xs.reverse ++ x :: ρ)[xs.length]? = some x := by
      rw [List.getElem?_append_right (Nat.le_of_eq List.length_reverse), List.length_reverse, Nat.sub_self,
        List.getElem?_cons_zero]
    have hx : (Atom.var (ys.length + xs.length)).eval (ys ++ xs.reverse ++ x :: ρ) = some x := by
      show (ys ++ xs.reverse ++ x :: ρ)[ys.length + xs.length]? = some x
      rw [h1, h2]
    rw [ht, he, List.length_cons, downFrom_succ, evalAtoms_cons, evalAtoms_downFrom ys xs (x :: ρ)]
    simp only [hx, Option.bind_some, Option.map_some]

theorem evalAtoms_downFrom_nil (xs ρ : List Val) :
    evalAtoms (xs.reverse ++ ρ) (downFrom (xs.length - 1) xs.length) = some xs := by
  have := evalAtoms_downFrom [] xs ρ
  simpa only [List.nil_append, List.length_nil, Nat.zero_add] using this

theorem downFrom_take : ∀ (top n r : Nat), r ≤ n → (downFrom top n).take r = downFrom top r
  | _, _, 0, _ => rfl
  | _, 0, _ + 1, h => absurd h (by omega)
  | top, n + 1, r + 1, h => by
    rw [downFrom_succ top n, downFrom_succ top r, List.take_succ_cons, downFrom_take (top - 1) n r (by omega)]

theorem downFrom_drop : ∀ (top n r : Nat), r ≤ n → (downFrom top n).drop r = downFrom (top - r) (n - r)
  | _, _, 0, _ => rfl
  | _, 0, _ + 1, h => absurd h (by omega)
  | top, n + 1, r + 1, h => by
    rw [downFrom_succ top n, List.drop_succ_cons, downFrom_drop (top - 1) n r (by omega)]
    have e1 : top - 1 - r = top - (r + 1) := by omega
    have e2 : n - r = n + 1 - (r + 1) := by omega
    rw [e1, e2]

/-- Shifting every variable by one shifts the block. -/
theorem downFrom_map_shift : ∀ (top n : Nat), n ≤ top + 1 →
    (downFrom top n).map shiftVar = downFrom (top + 1) n
  | _, 0, _ => rfl
  | top, n + 1, h => by
    rw [downFrom_succ top n, downFrom_succ (top + 1) n, List.map_cons,
      downFrom_map_shift (top - 1) n (by omega)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · have : top - 1 + 1 = top + 1 - 1 := by omega
      rw [this]
      all_goals rfl

/-! ## Expressions -/

theorem eval_bind_ret (P : Program) (k : Nat) (ρ : List Val) (J : List JClo) (c : Ixon.V3.LetContract)
    (b : Bind) : eval P k ρ J (.bind c b (.ret (.var 0))) = evalBind P k ρ b := by
  rw [eval_bind]
  cases evalBind P k ρ b with
  | ok v => rw [Result.bind_ok, eval_ret']; all_goals rfl
  | timeout => rfl
  | resource r => rfl
  | trap => rfl
  | stuck => rfl

/-- Alternatives none of whose keys is `c` are passed over. -/
theorem evalAlts_skip {P : Program} {k : Nat} {ρ : List Val} {J : List JClo} {c : Key.CtorKey}
    {fs : List Val} {d : Option Exp} : ∀ (l rest : List Alt),
    (∀ key n b, Alt.mk key n b ∈ l → key ≠ c) →
      evalAlts P k ρ J c fs (l ++ rest) d = evalAlts P k ρ J c fs rest d
  | [], _, _ => rfl
  | .mk key n b :: l, rest, h => by
    have hne : ¬(key = c ∧ n = fs.length) := fun he => h key n b List.mem_cons_self he.1
    rw [List.cons_append, evalAlts_cons, ite_eq_right hne]
    exact evalAlts_skip l rest fun key n b hm => h key n b (List.mem_cons_of_mem _ hm)

/-- Among a source's alternatives, the cell with `j` arguments takes the
`j`th. -/
theorem evalAlts_keyAlts {P : Program} {k : Nat} {ρ : List Val} {J : List JClo} {d : Option Exp}
    {size m : Nat} {s : Source} {j : Nat} {fs : List Val} (hfs : fs.length = s.caps + j) :
    ∀ (n : Nat) (rest : List Alt), j < n →
      evalAlts P k ρ J (.clo s.key j) fs
        ((List.range n).map (fun t => Alt.mk (.clo s.key t) (s.caps + t) (altBody size s t m)) ++ rest) d =
      eval P k (fs.reverse ++ ρ) J (altBody size s j m)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, rest, h => by
    rw [List.range_succ, List.map_append, List.append_assoc, List.map_cons, List.map_nil,
      List.singleton_append]
    by_cases hjn : j < n
    · exact evalAlts_keyAlts hfs n _ hjn
    · have hj : n = j := by omega
      have hmatch : Key.CtorKey.clo s.key j = .clo s.key j ∧ s.caps + j = fs.length := ⟨rfl, hfs.symm⟩
      rw [hj, evalAlts_skip, evalAlts_cons, ite_eq_left hmatch]
      intro key n' b hm he
      obtain ⟨t, ht, heq⟩ := List.mem_map.1 hm
      cases heq
      injection he with _ htj
      exact absurd (List.mem_range.1 ht) (by omega)

/-- In a dispatcher's alternatives, a cell of `s` takes `s`'s, when no
source before `s` has its key. -/
theorem evalAlts_dispAlts {P : Program} {k : Nat} {ρ : List Val} {J : List JClo} {d : Option Exp}
    {size m : Nat} {s : Source} {j : Nat} {fs : List Val} (hj : j < s.arity) (hfs : fs.length = s.caps + j) :
    ∀ (pre post : List Source), (∀ s' ∈ pre, s'.key ≠ s.key) →
      evalAlts P k ρ J (.clo s.key j) fs (dispAlts size m (pre ++ s :: post)) d =
        eval P k (fs.reverse ++ ρ) J (altBody size s j m)
  | [], post, _ => by
    rw [List.nil_append, dispAlts]
    exact evalAlts_keyAlts hfs s.arity _ hj
  | s' :: pre, post, hpre => by
    rw [List.cons_append, dispAlts, evalAlts_skip]
    · exact evalAlts_dispAlts hj hfs pre post fun s'' h => hpre s'' (List.mem_cons_of_mem _ h)
    · intro key n b hm he
      obtain ⟨t, -, heq⟩ := List.mem_map.1 hm
      cases heq
      injection he with hk _
      exact hpre s' List.mem_cons_self hk

/-- The dispatcher of arity `m` on a cell of `s` and `m` arguments reaches
`s`'s alternative, with no charge. -/
theorem eval_dispatcher {P : Program} {k : Nat} {size m : Nat} {srcs pre post : List Source} {s : Source}
    (hsrcs : srcs = pre ++ s :: post) (hpre : ∀ s' ∈ pre, s'.key ≠ s.key) {j : Nat} (hj : j < s.arity)
    {fs args : List Val} (hfs : fs.length = s.caps + j) (hargs : args.length = m) :
    eval P k (args.reverse ++ [.con (.clo s.key j) fs]) [] (dispatcher size srcs m).body =
      eval P k (fs.reverse ++ (args.reverse ++ [.con (.clo s.key j) fs])) [] (altBody size s j m) := by
  have hl : args.reverse.length ≤ m := Nat.le_of_eq (by rw [List.length_reverse, hargs])
  have hc : (Atom.var m).eval (args.reverse ++ [Val.con (.clo s.key j) fs]) = some (.con (.clo s.key j) fs) := by
    show (args.reverse ++ [Val.con (.clo s.key j) fs])[m]? = _
    rw [List.getElem?_append_right hl, List.length_reverse, hargs, Nat.sub_self, List.getElem?_cons_zero]
  simp only [dispatcher]
  rw [eval_case, hc]
  show evalAlts P k _ [] (.clo s.key j) fs (dispAlts size m srcs) none = _
  rw [hsrcs]
  exact evalAlts_dispAlts hj hfs pre post hpre

/-! ## The three alternatives -/

/-- The fields and the arguments, read by an alternative's atoms. -/
theorem evalAtoms_alt {s : Source} {j m : Nat} {fs args ρ : List Val} (hfs : fs.length = s.caps + j)
    (hargs : args.length = m) :
    evalAtoms (fs.reverse ++ (args.reverse ++ ρ))
      (downFrom (s.caps + j - 1) (s.caps + j) ++ downFrom (s.caps + j + m - 1) m) = some (fs ++ args) := by
  apply evalAtoms_append
  · have := evalAtoms_downFrom_nil fs (args.reverse ++ ρ)
    rwa [hfs] at this
  · have := evalAtoms_downFrom fs.reverse args ρ
    rwa [List.length_reverse, hfs, hargs, List.append_assoc] at this

theorem eval_altBody_exact {P : Program} {k : Nat} {size m : Nat} {s : Source} {j : Nat}
    {fs args ρ : List Val} {gd : GDef} (hs : P.global? s.id = some gd) (hps : gd.ps.length = s.caps + s.arity)
    (hj : j < s.arity) (hfs : fs.length = s.caps + j) (hargs : args.length = m) (hm : m = s.arity - j) :
    eval P (k + 1) (fs.reverse ++ (args.reverse ++ ρ)) [] (altBody size s j m) =
      eval P k (fs ++ args).reverse [] gd.body := by
  have hn : (fs ++ args).length = gd.ps.length := by
    rw [List.length_append, hfs, hargs, hps, hm]; omega
  simp only [altBody]
  rw [ite_eq_left hm, eval_bind_ret, evalBind_call_of P (k + 1) _ hs (evalAtoms_alt hfs hargs) hn, later_succ]

theorem eval_altBody_under {P : Program} {k : Nat} {size m : Nat} {s : Source} {j : Nat}
    {fs args ρ : List Val} (hfs : fs.length = s.caps + j) (hargs : args.length = m) (hm : m < s.arity - j) :
    eval P k (fs.reverse ++ (args.reverse ++ ρ)) [] (altBody size s j m) =
      .ok (.con (.clo s.key (j + m)) (fs ++ args)) := by
  have hne : ¬m = s.arity - j := by omega
  simp only [altBody]
  rw [ite_eq_right hne, ite_eq_left hm, eval_bind_ret, evalBind_con, evalAtoms_alt hfs hargs]
  all_goals rfl

theorem eval_altBody_over {P : Program} {k : Nat} {size m : Nat} {s : Source} {j : Nat}
    {fs args ρ : List Val} {gd D : GDef} (hs : P.global? s.id = some gd)
    (hps : gd.ps.length = s.caps + s.arity) (hj : j < s.arity) (hfs : fs.length = s.caps + j)
    (hargs : args.length = m) (hm : s.arity - j < m)
    (hd : P.global? (dispId size (m - (s.arity - j))) = some D) (hD : D.ps.length = m - (s.arity - j) + 1) :
    eval P (k + 1) (fs.reverse ++ (args.reverse ++ ρ)) [] (altBody size s j m) =
      (eval P k (fs ++ args.take (s.arity - j)).reverse [] gd.body).bind fun v =>
        eval P k (v :: args.drop (s.arity - j)).reverse [] D.body := by
  have hrm : s.arity - j ≤ m := Nat.le_of_lt hm
  have henv : fs.reverse ++ (args.reverse ++ ρ) =
      fs.reverse ++ (args.drop (s.arity - j)).reverse ++ ((args.take (s.arity - j)).reverse ++ ρ) := by
    conv => lhs; rw [← List.take_append_drop (s.arity - j) args]
    simp only [List.reverse_append, List.append_assoc]
  have hlt : (args.take (s.arity - j)).length = s.arity - j := by
    rw [List.length_take, hargs]; omega
  have hld : (args.drop (s.arity - j)).length = m - (s.arity - j) := by
    rw [List.length_drop, hargs]
  -- the first call: the fields and the first `r` arguments
  have h1 : evalAtoms (fs.reverse ++ (args.reverse ++ ρ))
      (downFrom (s.caps + j - 1) (s.caps + j) ++ (downFrom (s.caps + j + m - 1) m).take (s.arity - j)) =
      some (fs ++ args.take (s.arity - j)) := by
    apply evalAtoms_append
    · have := evalAtoms_downFrom_nil fs (args.reverse ++ ρ)
      rwa [hfs] at this
    · rw [downFrom_take _ _ _ hrm, henv]
      have := evalAtoms_downFrom (fs.reverse ++ (args.drop (s.arity - j)).reverse) (args.take (s.arity - j)) ρ
      rw [List.length_append, List.length_reverse, List.length_reverse, hfs, hld, hlt] at this
      have e : s.caps + j + (m - (s.arity - j)) + (s.arity - j) - 1 = s.caps + j + m - 1 := by omega
      rw [e] at this
      simp only [List.append_assoc] at this ⊢
      exact this
  -- the second call: the result and the rest of the arguments
  have h2 : ∀ v : Val, evalAtoms (v :: (fs.reverse ++ (args.reverse ++ ρ)))
      (.var 0 :: ((downFrom (s.caps + j + m - 1) m).drop (s.arity - j)).map shiftVar) =
      some (v :: args.drop (s.arity - j)) := by
    intro v
    rw [evalAtoms_cons, downFrom_drop _ _ _ hrm,
      downFrom_map_shift (s.caps + j + m - 1 - (s.arity - j)) (m - (s.arity - j)) (by omega), henv]
    have := evalAtoms_downFrom (v :: fs.reverse) (args.drop (s.arity - j)) ((args.take (s.arity - j)).reverse ++ ρ)
    rw [List.length_cons, List.length_reverse, hfs, hld] at this
    have e : s.caps + j + 1 + (m - (s.arity - j)) - 1 = s.caps + j + m - 1 - (s.arity - j) + 1 := by omega
    rw [e] at this
    simp only [List.cons_append, List.append_assoc] at this ⊢
    rw [this]
    all_goals rfl
  have hn1 : (fs ++ args.take (s.arity - j)).length = gd.ps.length := by
    rw [List.length_append, hfs, hlt, hps]; omega
  have hn2 : ∀ v : Val, (v :: args.drop (s.arity - j)).length = D.ps.length := fun v => by
    rw [List.length_cons, hld, hD]
  have hne1 : ¬m = s.arity - j := by omega
  have hne2 : ¬m < s.arity - j := by omega
  simp only [altBody]
  rw [ite_eq_right hne1, ite_eq_right hne2, eval_bind, evalBind_call_of P (k + 1) _ hs h1 hn1, later_succ]
  congr 1
  funext v
  rw [eval_bind_ret, evalBind_call_of P (k + 1) _ hd (h2 v) (hn2 v), later_succ]

/-! ## Calls of a dispatcher -/

theorem call_dispatcher {P : Program} {k : Nat} {ρ : List Val} {size m : Nat} {srcs : List Source}
    {as : List Atom} {callee : Val} {args : List Val}
    (hd : P.global? (dispId size m) = some (dispatcher size srcs m))
    (hv : evalAtoms ρ as = some (callee :: args)) (hargs : args.length = m) :
    evalBind P (k + 1) ρ (.call (dispId size m) as) =
      eval P k (args.reverse ++ [callee]) [] (dispatcher size srcs m).body := by
  have hn : (callee :: args).length = (dispatcher size srcs m).ps.length := by
    simp [dispatcher, hargs]
  rw [evalBind_call_of P (k + 1) ρ hd hv hn, later_succ, List.reverse_cons]

/-- **Exactly the missing arguments**: the call of the dispatcher is the call
of `s`, two charges in all. -/
theorem dispatch_exact {P : Program} {k : Nat} {ρ : List Val} {size m : Nat} {srcs pre post : List Source}
    {s : Source} {as : List Atom} {j : Nat} {fs args : List Val} {gd : GDef}
    (hd : P.global? (dispId size m) = some (dispatcher size srcs m))
    (hsrcs : srcs = pre ++ s :: post) (hpre : ∀ s' ∈ pre, s'.key ≠ s.key)
    (hs : P.global? s.id = some gd) (hps : gd.ps.length = s.caps + s.arity) (hj : j < s.arity)
    (hfs : fs.length = s.caps + j) (hv : evalAtoms ρ as = some (.con (.clo s.key j) fs :: args))
    (hargs : args.length = m) (hm : m = s.arity - j) :
    evalBind P (k + 2) ρ (.call (dispId size m) as) = eval P k (fs ++ args).reverse [] gd.body := by
  rw [call_dispatcher hd hv hargs, eval_dispatcher hsrcs hpre hj hfs hargs,
    eval_altBody_exact hs hps hj hfs hargs hm]

/-- **Fewer arguments**: the cell with `j + m` arguments, one charge. -/
theorem dispatch_under {P : Program} {k : Nat} {ρ : List Val} {size m : Nat} {srcs pre post : List Source}
    {s : Source} {as : List Atom} {j : Nat} {fs args : List Val}
    (hd : P.global? (dispId size m) = some (dispatcher size srcs m))
    (hsrcs : srcs = pre ++ s :: post) (hpre : ∀ s' ∈ pre, s'.key ≠ s.key) (hj : j < s.arity)
    (hfs : fs.length = s.caps + j) (hv : evalAtoms ρ as = some (.con (.clo s.key j) fs :: args))
    (hargs : args.length = m) (hm : m < s.arity - j) :
    evalBind P (k + 1) ρ (.call (dispId size m) as) = .ok (.con (.clo s.key (j + m)) (fs ++ args)) := by
  rw [call_dispatcher hd hv hargs, eval_dispatcher hsrcs hpre hj hfs hargs,
    eval_altBody_under hfs hargs hm]

/-- **More arguments**: the call of `s` on the fields and the first `r`
arguments, then the dispatcher of arity `m - r` on its result and the rest. -/
theorem dispatch_over {P : Program} {k : Nat} {ρ : List Val} {size m : Nat} {srcs pre post : List Source}
    {s : Source} {as : List Atom} {j : Nat} {fs args : List Val} {gd : GDef}
    (hd : P.global? (dispId size m) = some (dispatcher size srcs m))
    (hsrcs : srcs = pre ++ s :: post) (hpre : ∀ s' ∈ pre, s'.key ≠ s.key)
    (hs : P.global? s.id = some gd) (hps : gd.ps.length = s.caps + s.arity) (hj : j < s.arity)
    (hfs : fs.length = s.caps + j) (hv : evalAtoms ρ as = some (.con (.clo s.key j) fs :: args))
    (hargs : args.length = m) (hm : s.arity - j < m)
    (hd' : P.global? (dispId size (m - (s.arity - j))) = some (dispatcher size srcs (m - (s.arity - j)))) :
    evalBind P (k + 2) ρ (.call (dispId size m) as) =
      (eval P k (fs ++ args.take (s.arity - j)).reverse [] gd.body).bind fun v =>
        eval P k (v :: args.drop (s.arity - j)).reverse [] (dispatcher size srcs (m - (s.arity - j))).body := by
  have hD : (dispatcher size srcs (m - (s.arity - j))).ps.length = m - (s.arity - j) + 1 := by
    simp [dispatcher]
  rw [call_dispatcher hd hv hargs, eval_dispatcher hsrcs hpre hj hfs hargs,
    eval_altBody_over hs hps hj hfs hargs hm hd' hD]

end IxCC.Anf.Defun.Proof
