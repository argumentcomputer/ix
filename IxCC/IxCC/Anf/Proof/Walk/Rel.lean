import IxCC.Anf.Proof.Rel.Fund
import IxCC.Anf.Proof.Walk.Beq
import IxCC.Anf.Proof.Walk.Monad
import IxCC.Anf.Proof.Convert.Rel

/-! # The rewriting walk: the relation

The relation the walk's simulation keeps (P2 shrink, P3 inline, P4's
specialisation bodies; M2.3), an instance of `Anf.Rel`'s structural
relations between a source program `P` and a target program `Q`:

* `WV v w`: literals, □, constructors of related fields, closures of the
  same code over related environments (`idc`), and *walked* closures
  (`walkc`): the target body is the walk of the source body, for a valid
  walk configuration, under a walk environment that maps the source
  closure's parameters to the target closure's captured operands (the
  arguments a β-reduction already supplied) or its own parameters, and its
  captured variables to operands of its captured environment (`WEnv`).
* `WEnv live σ ρ ρ'`: each source variable's walk entry (`Walk.Ent`) against
  the target environment: an operand whose value is related, or a local
  function the walk inlines at its single application; `live = false`
  marks a binding the walk dropped because nothing reads it (`NoDead`).
* `FactsOk`: the walk's facts about target levels hold in the target
  environment (constructor views, `y + 1`, a function global's closure,
  a partial application of one).
* `JEnv`: the source join closures against their walk entries: emitted at
  a target level (`JoinR`: jumping to both, then the continuation, simulates
  for every continuation that matches the target meaning `T` of the walk's
  continuation), inlined at their single jump, or dead.
* `VOk C ρ ρ'`: walk configuration `C` may walk a term whose source
  environment is `ρ` and target environment `ρ'`: the pass's predicate
  `Valid C ρ ρ' prs` holds with pairs `prs` of related values (P4 relates a
  redirected call's source arguments to its activation's, and records the
  activation's values that stand for the caller's); entries that walk a body
  later under another source environment (an inlined local function, a join
  point) record its validity in every extension of the target environment.
* `KontW n k SK`: the walk's continuation `k` against a source continuation
  `SK`: `ret` returns, `jump l` jumps to the target join closure at level
  `l` (its charge included), and a meta-continuation simulates `SK` on every
  related operand in every extension of the target environments. -/

set_option autoImplicit false

namespace IxCC.Anf.WalkProof

open IxCC.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open IxCC.Anf.Rel (Pw)
open Walk (Ent JEnt Fact Here Cfg Kont Fires)

variable (P Q : Program) (Valid : Cfg → List Val → List Val → List (Val × Val) → Prop)
  (Xc : Nat → List Val → Exp → Exp → Prop)

/-- No dead variable or join point occurs in the term. -/
def NoDead (live jlive : List Bool) (e : Exp) : Prop :=
  (∀ i, live[i]? = some false → e.occ i = 0) ∧ (∀ j, jlive[j]? = some false → e.jocc j = 0)

/-- What a walk fact says about a level of the target environment. -/
def FactOk (ρ' : List Val) (l : Nat) : Fact → Prop
  | .ctor c fs => ∃ w ws, (Opd.lvl l).val ρ' = some w ∧ fs.mapM (·.val ρ') = some ws ∧
      w.asCtor Q.known = some (c, ws)
  | .succ y => ∃ m, (Opd.lvl l).val ρ' = some (.lit (.nat (m + 1))) ∧ y.val ρ' = some (.lit (.nat m))
  | .prim p os => ∃ w ws, (Opd.lvl l).val ρ' = some w ∧ os.mapM (·.val ρ') = some ws ∧
      primResult Q.known p ws = .ok w
  | .glob g => ∃ gd, Q.global? g = some gd ∧ gd.ps ≠ [] ∧
      (∀ C ρ ρ' prs, Valid C ρ ρ' prs → C.prog.arity? g = some gd.ps.length) ∧
      (Opd.lvl l).val ρ' = some (.clos [] gd.ps.length gd.body [])
  | .pap g as => ∃ gd ws, Q.global? g = some gd ∧ as.mapM (·.val ρ') = some ws ∧
      (∀ C ρ ρ' prs, Valid C ρ ρ' prs → C.prog.arity? g = some gd.ps.length) ∧
      ws.length < gd.ps.length ∧ (Opd.lvl l).val ρ' = some (.clos [] gd.ps.length gd.body ws)

/-- Every fact holds. -/
def FactsOk (facts : Src.NatMap Fact) (ρ' : List Val) : Prop :=
  ∀ l f, facts.get? l = some f → FactOk Q Valid ρ' l f

mutual

/-- Source and target values. -/
inductive WV : Val → Val → Prop
  | lit {l : Lam.Lit} : WV (.lit l) (.lit l)
  | box : WV .box .box
  | con {c : Key.CtorKey} {vs ws : List Val} : WVs vs ws → WV (.con c vs) (.con c ws)
  | idc {ρ ρ' got got' : List Val} {n : Nat} {b : Exp} :
      WVs ρ ρ' → WVs got got' → WV (.clos ρ n b got) (.clos ρ' n b got')
  | walkc {C : Cfg} {fuel : Nat} {s s' : Fires} {σP σ0 : List Ent} {live : List Bool}
      {facts : Src.NatMap Fact} {lvl : Nat} {ρ ρ' got got' : List Val} {n m : Nat} {b b' : Exp}
      {oOf : Nat → Opd} {wOf : Nat → Val} :
      VOk C ρ ρ' →
      (Walk.walk C fuel { σ := σP ++ σ0, jσ := [] } { d := ρ'.length + m, dj := 0, facts, lvl } b
        .ret).run s = .ok (b', s') →
      WEnv C live σ0 ρ ρ' → FactsOk Q Valid facts ρ' → NoDead (List.replicate n true ++ live) [] b →
      σP.length = n → m ≤ n → n - m ≤ got.length → got.length < n →
      got'.length + (n - m) = got.length →
      (∀ p, p < n - m → σP[n - 1 - p]? = some (.opd (oOf p)) ∧ (oOf p).val ρ' = some (wOf p)) →
      (∀ p v, p < n - m → got[p]? = some v → WV v (wOf p)) →
      (∀ p, n - m ≤ p → p < n → σP[n - 1 - p]? = some (.opd (.lvl (ρ'.length + (p - (n - m)))))) →
      (∀ p v w, n - m ≤ p → p < n → got[p]? = some v → got'[p - (n - m)]? = some w → WV v w) →
      WV (.clos ρ n b got) (.clos ρ' m b' got')
  /-- A closure of another pass's code (`Xc`: arity, source environment,
  source body, target body). -/
  | xc {ρ ρ' got got' : List Val} {n : Nat} {b b' : Exp} :
      WVs ρ ρ' → WVs got got' → Xc n ρ b b' → WV (.clos ρ n b got) (.clos ρ' n b' got')

inductive WVs : List Val → List Val → Prop
  | nil : WVs [] []
  | cons {v w : Val} {vs ws : List Val} : WV v w → WVs vs ws → WVs (v :: vs) (w :: ws)

/-- A source environment entry against its walk entry, for walk
configuration `C`. -/
inductive WEnt : Cfg → Ent → Val → List Val → Prop
  | opd {C : Cfg} {o : Opd} {v w : Val} {ρ' : List Val} : o.val ρ' = some w → WV v w → WEnt C (.opd o) v ρ'
  | fn {C : Cfg} {σf : List Ent} {livef : List Bool} {ρf : List Val} {n : Nat} {fb : Exp} {ρ' : List Val} :
      WEnv C livef σf ρf ρ' → NoDead (List.replicate n true ++ livef) [] fb → 0 < n →
      (∀ ρ'', ρ' <:+ ρ'' → VOk C ρf ρ'') →
      WEnt C (.fn σf n fb) (.clos ρf n fb []) ρ'

/-- A source environment against its walk environment; `false` marks a
dropped binding. -/
inductive WEnv : Cfg → List Bool → List Ent → List Val → List Val → Prop
  | nil {C : Cfg} {ρ' : List Val} : WEnv C [] [] [] ρ'
  | live {C : Cfg} {e : Ent} {v : Val} {live : List Bool} {σ : List Ent} {ρ ρ' : List Val} :
      WEnt C e v ρ' → WEnv C live σ ρ ρ' → WEnv C (true :: live) (e :: σ) (v :: ρ) ρ'
  | dead {C : Cfg} {v : Val} {live : List Bool} {σ : List Ent} {ρ ρ' : List Val} :
      WEnv C live σ ρ ρ' → WEnv C (false :: live) (.opd .box :: σ) (v :: ρ) ρ'

/-- A valid walk configuration for a source and a target environment: the
pass's predicate holds with pairs of values that are related. -/
inductive VOk : Cfg → List Val → List Val → Prop
  | mk {C : Cfg} {ρ ρ' : List Val} {prs : List (Val × Val)} :
      Valid C ρ ρ' prs → (∀ p ∈ prs, WV p.1 p.2) → VOk C ρ ρ'

end

/-- No closures of another pass's code. -/
def noXc : Nat → List Val → Exp → Exp → Prop := fun _ _ _ _ => False

/-- Jumping to a source and a target join closure, then a continuation
that matches the target meaning `T`, simulates, at every bound up to `n`. -/
def JoinR (n : Nat) (T : Val → Nat → Result Val) (jc jc' : JClo) : Prop :=
  ∀ m ≤ n, ∀ SK : Val → Nat → Result Val,
    (∀ x w, WV Q Valid Xc x w → SimUpTo (WV Q Valid Xc) m (SK x) (T w)) →
    ∀ vs ws, WVs Q Valid Xc vs ws →
      SimUpTo (WV Q Valid Xc) m (fun k => (jumpTo P k jc vs).bind (SK · k)) (fun k => jumpTo Q k jc' ws)

/-- Source join closures against their walk entries, for walk configuration
`C`. -/
inductive JEnv (C : Cfg) (n : Nat) (T : Option (Val → Nat → Result Val)) (ρ' : List Val) (J' : List JClo) :
    List Bool → List JEnt → List JClo → Prop
  | nil : JEnv C n T ρ' J' [] [] []
  | emitted {l ar : Nat} {r : Bool} {b : Exp} {σj : List Ent} {jσj : List JEnt} {livej jlj : List Bool}
      {ρj : List Val} {Jj : List JClo} {jc' : JClo} {Tk : Val → Nat → Result Val} {jl : List Bool}
      {jσ : List JEnt} {J : List JClo} :
      l < J'.length → J'[J'.length - 1 - l]? = some jc' → T = some Tk →
      JoinR P Q Valid Xc n Tk (.mk ρj Jj ar b r) jc' →
      WEnv Q Valid Xc C livej σj ρj ρ' → JEnv C n T ρ' J' jlj jσj Jj →
      NoDead (List.replicate ar true ++ livej) (if r then true :: jlj else jlj) b →
      (∀ ρ'', ρ' <:+ ρ'' → VOk Q Valid Xc C ρj ρ'') →
      JEnv C n T ρ' J' jl jσ J →
      JEnv C n T ρ' J' (true :: jl) (.mk (some l) σj jσj ar r b :: jσ) (.mk ρj Jj ar b r :: J)
  | once {ar : Nat} {b : Exp} {σj : List Ent} {jσj : List JEnt} {livej jlj : List Bool}
      {ρj : List Val} {Jj : List JClo} {jl : List Bool} {jσ : List JEnt} {J : List JClo} :
      WEnv Q Valid Xc C livej σj ρj ρ' → JEnv C n T ρ' J' jlj jσj Jj →
      NoDead (List.replicate ar true ++ livej) jlj b →
      (∀ ρ'', ρ' <:+ ρ'' → VOk Q Valid Xc C ρj ρ'') →
      JEnv C n T ρ' J' jl jσ J →
      JEnv C n T ρ' J' (true :: jl) (.mk none σj jσj ar false b :: jσ) (.mk ρj Jj ar b false :: J)
  | dead {je : JEnt} {jc : JClo} {jl : List Bool} {jσ : List JEnt} {J : List JClo} :
      JEnv C n T ρ' J' jl jσ J → JEnv C n T ρ' J' (false :: jl) (je :: jσ) (jc :: J)

/-- The target meaning of a walk continuation that is not a
meta-continuation. -/
def KT (k : Kont) (J' : List JClo) : Option (Val → Nat → Result Val) :=
  match k with
  | .ret => some fun w _ => .ok w
  | .jump l => if l < J'.length then
      (J'[J'.length - 1 - l]?).map fun jcl w k => jumpTo Q k jcl [w] else none
  | .cont _ => none

/-- A walk continuation against a source continuation. -/
def KontW (n : Nat) (k : Kont) (SK : Val → Nat → Result Val) (ρ' : List Val) (J' : List JClo) : Prop :=
  match k with
  | .cont f => ∀ (here' : Here) (o : Opd) (e : Exp) (s s' : Fires) (ρ'' : List Val) (J'' : List JClo),
      (f here' o).run s = .ok (e, s') → ρ' <:+ ρ'' → J' <:+ J'' → here'.d = ρ''.length →
      here'.dj = J''.length → FactsOk Q Valid here'.facts ρ'' →
      ∀ x w, o.val ρ'' = some w → WV Q Valid Xc x w →
        SimUpTo (WV Q Valid Xc) n (SK x) (fun k => eval Q k ρ'' J'' e)
  | k => ∃ T, KT Q k J' = some T ∧ ∀ x w, WV Q Valid Xc x w → SimUpTo (WV Q Valid Xc) n (SK x) (T w)

end IxCC.Anf.WalkProof
