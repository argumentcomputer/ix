import Compilatrix.Lam.Erase

/-! # What erasure produces, as relations

The Lam terms erasure can produce for a Src term (design note 02 §5.1, as
built in `Lam.Erase.Term` and `Lam.Erase`), as inductive relations that
follow the translation's cases one to one. They are parametrised by the
erasure input `I` and by `G`, the key-to-global map of the finished
program (`G key g`: global `g` has key `key`), so they do not mention
erasure's state; `Proof.Build` shows that every successful erasure is
described by them, and `Proof.Sim` that everything they describe simulates
SrcEval (M2.2).

* `TR cx t t'`: `t'` is an erasure of `t` under the context map `cx` (`term`);
  a λ's mode is free, since `setModes` changes the modes of by-name
  telescopes and modes are inert in `eval`.
* `ArgsR` (`strictArgs`), `BindR` (`bindArgs`: the `let`-bound arguments of
  a saturated spine and a `Ref` per argument), `RefR` (`refTerm`), `SatR`
  (`saturated`), `FieldsR` (a constructor's fields), `MinorR` (`minorApp`),
  `AltsR` (a `casesOn`'s alternatives) and `RecArgsR` (a recursor spine's
  arguments to `r⋆`).
* `BodyR key body` (outside the mutual block): the body of the global with
  key `key` (`keyBody`), and `ProgR G L`: every global of `L` that `G`
  names has a body so related. -/

set_option autoImplicit false

namespace Compilatrix.Lam.Erase.Proof

open Compilatrix.Src (CId Head Profile)

variable (I : Input)

/-- The field arguments `minorApp` passes: a case-bound level, or □. -/
def fieldArgs (cx : Cx) (fields : List (Option Nat)) : List (Term × Mode) :=
  fields.map fun
    | some l => (cx.lvl l, .strict)
    | none => (.box, .strict)

/-- Argument `i` of a recursor spine is a minor. -/
def IsMinor (np nmot nmin i : Nat) : Prop := np + nmot ≤ i ∧ i < np + nmot + nmin

/-- `casesOn` rule `j`'s alternative, as `ruleAlt` computes it: the
constructor's key, its kept arity at the constructors' profile, and the
level (from `base`) of each field, `none` for a dropped one. -/
def RuleAltR (r : CId) (q : Profile) (base : Nat) (ind : CId) (j : Nat) (rule : Src.Rule)
    (key : Key.CtorKey) (arity : Nat) (fields : List (Option Nat)) : Prop :=
  ∃ s lv cidx np nf ty, I.decl? rule.ctor = some (.ctor s lv ind cidx np nf ty) ∧
    cidx = j ∧ nf = rule.fields ∧ key = I.ctorKey rule.ctor ∧
    arity = I.keptCount rule.ctor (I.ctorProfile r q) nf ∧
    fields = (List.range nf).map fun i =>
      if I.kept rule.ctor (I.ctorProfile r q) i then
        some (base + I.rank rule.ctor (I.ctorProfile r q) i)
      else none

/-- The universe profile of a reference to `c` under `cx`. -/
abbrev qOf (cx : Cx) (c : CId) (us : List Ixon.Univ) : Profile := I.profileOf c cx.prof us

/-- A wrapper's argument class for position `i` (`wrapperBody`). -/
def wrapClass (h : Head) (c : CId) (i : Nat) : Src.Rel :=
  if headReads I h i then .rel else (I.params c).getD i .rel

variable (G : Key.GKey → GlobalId → Prop)

mutual

/-- `t'` is an erasure of `t` under `cx` (`Erase.term`). -/
inductive TR : Cx → Src.Term → Term → Prop
  | varSome {cx : Cx} {i l : Nat} : cx.ctx[i]? = some (some l) → TR cx (.var i) (cx.lvl l)
  | varNone {cx : Cx} {i : Nat} : cx.ctx[i]? = some none → TR cx (.var i) .box
  | sort {cx : Cx} {u : Ixon.Univ} : TR cx (.sort u) .box
  | pi {cx : Cx} {b : Src.Binder} {res : Ixon.V3.ValueContract} {d c : Src.Term} :
      TR cx (.pi b res d c) .box
  | natLit {cx : Cx} {n : Nat} : TR cx (.natLit n) (.lit (.nat n))
  | lam {cx : Cx} {b : Src.Binder} {d body : Src.Term} {body' : Term} (m : Mode) :
      TR cx.bind body body' → TR cx (.lam b d body) (.lam m b.contract body')
  | letIrr {cx : Cx} {c : Ixon.V3.LetContract} {r : Src.Rel} {ty v b : Src.Term} {b' : Term} :
      r.irrP cx.prof = true → TR cx.bind b b' → TR cx (.letE c r ty v b) (.letE c .box b')
  | letRel {cx : Cx} {c : Ixon.V3.LetContract} {r : Src.Rel} {ty v b : Src.Term} {v' b' : Term} :
      r.irrP cx.prof = false → TR cx v v' → TR cx.bind b b' →
      TR cx (.letE c r ty v b) (.letE c v' b')
  | projDrop {cx : Cx} {s i : Nat} {e : Src.Term} {e' : Term} {k : CId}
      {fields : List Src.Relevance.FieldClass} {cls : Src.Relevance.FieldClass} :
      TR cx e e' → I.ctorsOf s = [k] → I.fields? k = some fields → fields[i]? = some cls →
      cls.dropP [] = true → TR cx (.proj s i e) (.letE letC e' .box)
  | projUnbox {cx : Cx} {s i : Nat} {e : Src.Term} {e' : Term} {k : CId}
      {fields : List Src.Relevance.FieldClass} {cls : Src.Relevance.FieldClass} :
      TR cx e e' → I.ctorsOf s = [k] → I.fields? k = some fields → fields[i]? = some cls →
      cls.dropP [] = false → (I.unbox? s []).isSome = true → TR cx (.proj s i e) e'
  | projKey {cx : Cx} {s i : Nat} {e : Src.Term} {e' : Term} {k : CId}
      {fields : List Src.Relevance.FieldClass} {cls : Src.Relevance.FieldClass}
      {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Src.Term} :
      TR cx e e' → I.ctorsOf s = [k] → I.fields? k = some fields → fields[i]? = some cls →
      cls.dropP [] = false → I.unbox? s [] = none →
      I.decl? k = some (.ctor sf lv ind cidx np nf ty) →
      TR cx (.proj s i e) (.proj (I.ctorKey k) (I.rank k [] i) e')
  /-- A spine whose head is not a constant: the head, then its arguments. -/
  | app {cx : Cx} {head : Src.Term} {args : List Src.Term.Arg} {h' : Term}
      {args' : List (Term × Mode)} :
      (∀ c us, head ≠ .const c us) → args ≠ [] → TR cx head h' → ArgsR cx args args' →
      TR cx (Src.Term.mkApps head args) (Term.apps h' args')
  /-- A constant with a δ body, not through its by-name variant. -/
  | plain {cx : Cx} {c : CId} {us : List Ixon.Univ} {args : List Src.Term.Arg} {b : Src.Term}
      {g : GlobalId} {args' : List (Term × Mode)} :
      us.length ≤ I.lvls c → I.deltaBody c = some b →
      (∀ a, I.lazy.get? c = some a → a ≤ args.length →
        hasName (lazyModes I c (qOf I cx c us) a) = false) →
      G (.const c (qOf I cx c us)) g → ArgsR cx args args' →
      TR cx (Src.Term.mkApps (.const c us) args) (Term.apps (.glob g) args')
  /-- A saturated `lazy` spine with a relevant by-name position: the
  by-name variant. -/
  | variant {cx : Cx} {c : CId} {us : List Ixon.Univ} {args : List Src.Term.Arg}
      {b : Src.Term} {a : Nat} {g : GlobalId} {lazyArgs rest' : List (Term × Mode)} :
      us.length ≤ I.lvls c → I.deltaBody c = some b → I.lazy.get? c = some a →
      a ≤ args.length → hasName (lazyModes I c (qOf I cx c us) a) = true →
      G (.byName c (qOf I cx c us)) g →
      LazyArgsR cx (lazyModes I c (qOf I cx c us) a) (args.take a) lazyArgs →
      ArgsR cx (args.drop a) rest' →
      TR cx (Src.Term.mkApps (.const c us) args) (Term.apps (.glob g) (lazyArgs ++ rest'))
  /-- An unsaturated special head: its wrapper global. -/
  | wrap {cx : Cx} {c : CId} {us : List Ixon.Univ} {args : List Src.Term.Arg} {h : Head}
      {g : GlobalId} {args' : List (Term × Mode)} :
      us.length ≤ I.lvls c → I.headOf c = some h → args.length < headArity I h →
      G (.wrapper h (qOf I cx c us)) g → ArgsR cx args args' →
      TR cx (Src.Term.mkApps (.const c us) args) (Term.apps (.glob g) args')
  /-- A saturated special head, in place; extra arguments applied after. -/
  | sat {cx : Cx} {c : CId} {us : List Ixon.Univ} {args : List Src.Term.Arg} {h : Head}
      {t₀ : Term} {args' : List (Term × Mode)} :
      us.length ≤ I.lvls c → I.headOf c = some h → headArity I h ≤ args.length →
      SatR cx h (qOf I cx c us) (args.take (headArity I h)) t₀ →
      ArgsR cx (args.drop (headArity I h)) args' →
      TR cx (Src.Term.mkApps (.const c us) args) (Term.apps t₀ args')

/-- `strictArgs`: □ where irrelevant, else a strict argument. -/
inductive ArgsR : Cx → List Src.Term.Arg → List (Term × Mode) → Prop
  | nil {cx : Cx} : ArgsR cx [] []
  | irr {cx : Cx} {a : Src.Term} {m : Src.Mode} {r : Src.Rel} {rest : List Src.Term.Arg}
      {rest' : List (Term × Mode)} :
      r.irrP cx.prof = true → ArgsR cx rest rest' →
      ArgsR cx ((a, m, r) :: rest) ((.box, .strict) :: rest')
  | strict {cx : Cx} {a : Src.Term} {r : Src.Rel} {a' : Term} {rest : List Src.Term.Arg}
      {rest' : List (Term × Mode)} :
      r.irrP cx.prof = false → TR cx a a' → ArgsR cx rest rest' →
      ArgsR cx ((a, .strict, r) :: rest) ((a', .strict) :: rest')

/-- The arguments of a by-name variant's leading telescope. -/
inductive LazyArgsR : Cx → List Mode → List Src.Term.Arg → List (Term × Mode) → Prop
  | nil {cx : Cx} {ms : List Mode} : LazyArgsR cx ms [] []
  | irr {cx : Cx} {m : Mode} {ms : List Mode} {a : Src.Term} {sm : Src.Mode} {r : Src.Rel}
      {rest : List Src.Term.Arg} {rest' : List (Term × Mode)} :
      m = .strict → r.irrP cx.prof = true → LazyArgsR cx ms rest rest' →
      LazyArgsR cx (m :: ms) ((a, sm, r) :: rest) ((.box, .strict) :: rest')
  | name {cx : Cx} {m : Mode} {ms : List Mode} {a : Src.Term} {r : Src.Rel} {a' : Term}
      {rest : List Src.Term.Arg} {rest' : List (Term × Mode)} :
      m = .name → r.irrP cx.prof = false → TR cx a a' → LazyArgsR cx ms rest rest' →
      LazyArgsR cx (m :: ms) ((a, .byName, r) :: rest) ((a', .name) :: rest')

/-- `bindArgs`: the relevant strict arguments `let`-bound in order (their
values erased at the context of the lets before them), a by-name argument
kept for later erasure where allowed, □ where irrelevant. -/
inductive BindR : Cx → List (Src.Term.Arg × Bool) → List Term → List Ref → Cx → Prop
  | nil {cx : Cx} : BindR cx [] [] [] cx
  | irr {cx cx' : Cx} {a : Src.Term} {m : Src.Mode} {r : Src.Rel} {ok : Bool}
      {rest : List (Src.Term.Arg × Bool)} {lets : List Term} {refs : List Ref} :
      r.irrP cx.prof = true → BindR cx rest lets refs cx' →
      BindR cx (((a, m, r), ok) :: rest) lets (.box :: refs) cx'
  | name {cx cx' : Cx} {a : Src.Term} {r : Src.Rel} {rest : List (Src.Term.Arg × Bool)}
      {lets : List Term} {refs : List Ref} :
      r.irrP cx.prof = false → BindR cx rest lets refs cx' →
      BindR cx (((a, .byName, r), true) :: rest) lets (.name a :: refs) cx'
  | strict {cx cx' : Cx} {a : Src.Term} {r : Src.Rel} {ok : Bool} {v : Term}
      {rest : List (Src.Term.Arg × Bool)} {lets : List Term} {refs : List Ref} :
      r.irrP cx.prof = false → TR cx a v → BindR (cx.extra 1) rest lets refs cx' →
      BindR cx (((a, .strict, r), ok) :: rest) (v :: lets) (.lvl cx.depth :: refs) cx'

/-- `refTerm`. -/
inductive RefR : Cx → Ref → Term → Prop
  | box {cx : Cx} : RefR cx .box .box
  | lvl {cx : Cx} {l : Nat} : RefR cx (.lvl l) (cx.lvl l)
  | name {cx : Cx} {a : Src.Term} {a' : Term} : TR cx a a' → RefR cx (.name a) a'

/-- A saturated special head in place (`saturated`). -/
inductive SatR : Cx → Head → Profile → List Src.Term.Arg → Term → Prop
  | prim {cx : Cx} {op : Src.PrimOp} {q : Profile} {args : List Src.Term.Arg}
      {args' : List (Term × Mode)} :
      ArgsR cx args args' → SatR cx (.prim op) q args (.prim (Prim.ofSrc op) (args'.map (·.1)))
  | natZero {cx : Cx} {c : CId} {q : Profile} {args : List Src.Term.Arg}
      {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Src.Term} :
      I.decl? c = some (.ctor sf lv ind cidx np nf ty) → I.known.natZero = some c →
      SatR cx (.ctor c) q args (.lit (.nat 0))
  | natSucc {cx cx' : Cx} {c : CId} {q : Profile} {args : List Src.Term.Arg}
      {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Src.Term}
      {lets : List Term} {refs : List Ref} {fs : List (Term × Mode)} :
      I.decl? c = some (.ctor sf lv ind cidx np nf ty) → I.known.natZero ≠ some c →
      I.known.natSucc = some c →
      BindR cx ((args.take np).map (·, false)) lets refs cx' → ArgsR cx' (args.drop np) fs →
      SatR cx (.ctor c) q args (wrapLets lets (.prim .natAdd (fs.map (·.1) ++ [.lit (.nat 1)])))
  | ctorUnbox {cx cx' : Cx} {c : CId} {q : Profile} {args : List Src.Term.Arg}
      {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Src.Term}
      {lets : List Term} {refs : List Ref} {f : Term} {j : Nat} :
      I.decl? c = some (.ctor sf lv ind cidx np nf ty) → I.known.natZero ≠ some c →
      I.known.natSucc ≠ some c →
      BindR cx ((args.take np).map (·, false)) lets refs cx' →
      FieldsR cx cx' c q 0 (args.drop np) [f] → I.unbox? ind q = some j →
      SatR cx (.ctor c) q args (wrapLets lets f)
  | ctorBox {cx cx' : Cx} {c : CId} {q : Profile} {args : List Src.Term.Arg}
      {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat} {ty : Src.Term}
      {lets : List Term} {refs : List Ref} {fields : List Term} :
      I.decl? c = some (.ctor sf lv ind cidx np nf ty) → I.known.natZero ≠ some c →
      I.known.natSucc ≠ some c →
      BindR cx ((args.take np).map (·, false)) lets refs cx' →
      FieldsR cx cx' c q 0 (args.drop np) fields → I.unbox? ind q = none →
      SatR cx (.ctor c) q args (wrapLets lets (.con (I.ctorKey c) fields))
  | quotMk {cx cx' : Cx} {c : CId} {q : Profile} {args : List Src.Term.Arg}
      {lets : List Term} {refs : List Ref} {e : Term} :
      BindR cx (args.map (·, false)) lets refs cx' → RefR cx' (refs.getD 2 .box) e →
      SatR cx (.quotMk c) q args (wrapLets lets e)
  | quotLift {cx cx' : Cx} {c : CId} {q : Profile} {args : List Src.Term.Arg}
      {lets : List Term} {refs : List Ref} {f x : Term} :
      BindR cx (args.map (·, false)) lets refs cx' → RefR cx' (refs.getD 3 .box) f →
      RefR cx' (refs.getD 5 .box) x →
      SatR cx (.quotLift c) q args (wrapLets lets (.tick (.app f x .strict)))
  | casesEmpty {cx cx' : Cx} {c r : CId} {q : Profile} {args : List Src.Term.Arg}
      {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Src.Rule}
      {ty : Src.Term} {lets : List Term} {refs : List Ref} :
      I.resolve.get? c = some (.case r) →
      I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
      BindR cx (args.zipIdx.map fun (a, i) => (a, decide (np + 1 + ni + 1 ≤ i))) lets refs cx' →
      I.kindAt r q = some .empty →
      SatR cx (.cases c) q args (wrapLets lets (.tick .trap))
  | casesSub {cx cx' : Cx} {c r : CId} {q : Profile} {args : List Src.Term.Arg}
      {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Src.Rule}
      {ty : Src.Term} {lets : List Term} {refs : List Ref} {w : Src.PropWhen}
      {srcs : List Src.FieldSrc} {body : Term} :
      I.resolve.get? c = some (.case r) →
      I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
      BindR cx (args.zipIdx.map fun (a, i) => (a, decide (np + 1 + ni + 1 ≤ i))) lets refs cx' →
      I.kindAt r q = some (.subsingleton w srcs) →
      MinorR cx' (refs.getD (np + 1 + ni + 1 + 0) .box)
        (srcs.map fun
          | .index i => (refs.getD (np + 1 + i) .box).level?
          | .proof => none) body →
      SatR cx (.cases c) q args (wrapLets lets (.tick body))
  | casesOrd {cx cx' : Cx} {c r : CId} {q : Profile} {args : List Src.Term.Arg}
      {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Src.Rule}
      {ty : Src.Term} {lets : List Term} {refs : List Ref} {l : Nat} {alts : List Alt} :
      I.resolve.get? c = some (.case r) →
      I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
      BindR cx (args.zipIdx.map fun (a, i) => (a, decide (np + 1 + ni + 1 ≤ i))) lets refs cx' →
      I.kindAt r q = some .ordinary → refs.getD (np + 1 + ni) .box = .lvl l →
      I.unbox? ind q = none →
      AltsR cx' r q ind refs (np + 1 + ni + 1) 0 rules alts →
      SatR cx (.cases c) q args (wrapLets lets (.tick (.case (cx'.lvl l) alts none)))
  | recr {cx cx' : Cx} {r : CId} {q : Profile} {args : List Src.Term.Arg}
      {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Src.Rule}
      {ty : Src.Term} {lets : List Term} {refs : List Ref} {g : GlobalId}
      {argTerms : List (Term × Mode)} :
      I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
      BindR cx (args.zipIdx.map fun (a, i) =>
        (a, decide (np + nmot ≤ i ∧ i < np + nmot + nmin))) lets refs cx' →
      (I.kindAt r q = some .ordinary → refs.getD (np + nmot + nmin + ni) .box ≠ .box) →
      RecArgsR cx' r q np nmot nmin 0 refs argTerms → G (.recStar r q) g →
      SatR cx (.recr r) q args (wrapLets lets (Term.apps (.glob g) argTerms))

/-- A constructor's fields: kept ones erased in order (at `cx'`, after the
parameters' lets), dropped ones irrelevant (S2) and omitted. -/
inductive FieldsR : Cx → Cx → CId → Profile → Nat → List Src.Term.Arg → List Term → Prop
  | nil {cx cx' : Cx} {c : CId} {q : Profile} {j : Nat} : FieldsR cx cx' c q j [] []
  | keptIrr {cx cx' : Cx} {c : CId} {q : Profile} {j : Nat} {a : Src.Term} {m : Src.Mode}
      {r : Src.Rel} {rest : List Src.Term.Arg} {fs : List Term} :
      I.kept c q j = true → r.irrP cx'.prof = true → FieldsR cx cx' c q (j + 1) rest fs →
      FieldsR cx cx' c q j ((a, m, r) :: rest) (.box :: fs)
  | keptRel {cx cx' : Cx} {c : CId} {q : Profile} {j : Nat} {a : Src.Term}
      {r : Src.Rel} {rest : List Src.Term.Arg} {f : Term} {fs : List Term} :
      I.kept c q j = true → r.irrP cx'.prof = false → TR cx' a f →
      FieldsR cx cx' c q (j + 1) rest fs →
      FieldsR cx cx' c q j ((a, .strict, r) :: rest) (f :: fs)
  | drop {cx cx' : Cx} {c : CId} {q : Profile} {j : Nat} {a : Src.Term} {m : Src.Mode}
      {r : Src.Rel} {rest : List Src.Term.Arg} {fs : List Term} :
      I.kept c q j = false → r.irrP cx.prof = true → FieldsR cx cx' c q (j + 1) rest fs →
      FieldsR cx cx' c q j ((a, m, r) :: rest) fs

/-- `minorApp`: a `casesOn` minor applied to its fields after the ι tick. -/
inductive MinorR : Cx → Ref → List (Option Nat) → Term → Prop
  | box {cx : Cx} {fields : List (Option Nat)} :
      MinorR cx .box fields (Term.apps .box (fieldArgs cx fields))
  | lvl {cx : Cx} {l : Nat} {fields : List (Option Nat)} :
      MinorR cx (.lvl l) fields (Term.apps (cx.lvl l) (fieldArgs cx fields))
  | name {cx : Cx} {m body : Src.Term} {p : Nat} {fields : List (Option Nat)} {body' : Term} :
      peelUpTo fields.length m = (p, body) → TR (cx.under (fields.take p)) body body' →
      MinorR cx (.name m) fields (Term.apps (.tick body') ((fieldArgs cx fields).drop p))

/-- A `casesOn`'s alternatives, rule by rule (`ruleAlt`, then `minorApp`
of minor `j`, found at `refs[mbase + j]`). -/
inductive AltsR : Cx → CId → Profile → CId → List Ref → Nat → Nat → List Src.Rule → List Alt →
    Prop
  | nil {cx : Cx} {r : CId} {q : Profile} {ind : CId} {refs : List Ref} {mbase j : Nat} :
      AltsR cx r q ind refs mbase j [] []
  | cons {cx : Cx} {r : CId} {q : Profile} {ind : CId} {refs : List Ref} {mbase j : Nat}
      {rule : Src.Rule} {rules : List Src.Rule} {key : Key.CtorKey} {arity : Nat}
      {fields : List (Option Nat)} {body : Term} {alts : List Alt} :
      RuleAltR I r q cx.depth ind j rule key arity fields →
      MinorR (cx.extra arity) (refs.getD (mbase + j) .box) fields body →
      AltsR cx r q ind refs mbase (j + 1) rules alts →
      AltsR cx r q ind refs mbase j (rule :: rules) (.mk key arity body :: alts)

/-- A recursor spine's arguments to `r⋆` (`recForm`): minors by name. -/
inductive RecArgsR : Cx → CId → Profile → Nat → Nat → Nat → Nat → List Ref →
    List (Term × Mode) → Prop
  | nil {cx : Cx} {r : CId} {q : Profile} {np nmot nmin i : Nat} :
      RecArgsR cx r q np nmot nmin i [] []
  | other {cx : Cx} {r : CId} {q : Profile} {np nmot nmin i : Nat} {ref : Ref}
      {refs : List Ref} {t : Term} {ts : List (Term × Mode)} :
      ¬ IsMinor np nmot nmin i → RefR cx ref t → RecArgsR cx r q np nmot nmin (i + 1) refs ts →
      RecArgsR cx r q np nmot nmin i (ref :: refs) ((t, .strict) :: ts)
  | minorBox {cx : Cx} {r : CId} {q : Profile} {np nmot nmin i : Nat} {refs : List Ref}
      {ts : List (Term × Mode)} :
      IsMinor np nmot nmin i → I.paramIrr r q i = true →
      RecArgsR cx r q np nmot nmin (i + 1) refs ts →
      RecArgsR cx r q np nmot nmin i (.box :: refs) ((.box, .strict) :: ts)
  | minorLvl {cx : Cx} {r : CId} {q : Profile} {np nmot nmin i l : Nat} {refs : List Ref}
      {ts : List (Term × Mode)} :
      IsMinor np nmot nmin i → I.paramIrr r q i = false →
      hasName (minorSig I r q (i - (np + nmot))) = false →
      RecArgsR cx r q np nmot nmin (i + 1) refs ts →
      RecArgsR cx r q np nmot nmin i (.lvl l :: refs) ((cx.lvl l, .name) :: ts)
  | minorName {cx : Cx} {r : CId} {q : Profile} {np nmot nmin i : Nat} {m : Src.Term}
      {t : Term} {refs : List Ref} {ts : List (Term × Mode)} :
      IsMinor np nmot nmin i → I.paramIrr r q i = false →
      hasName (minorSig I r q (i - (np + nmot))) = false → TR cx m t →
      RecArgsR cx r q np nmot nmin (i + 1) refs ts →
      RecArgsR cx r q np nmot nmin i (.name m :: refs) ((t, .name) :: ts)
  | minorFwd {cx : Cx} {r : CId} {q : Profile} {np nmot nmin i v l : Nat} {refs : List Ref}
      {ts : List (Term × Mode)} :
      IsMinor np nmot nmin i → I.paramIrr r q i = false →
      hasName (minorSig I r q (i - (np + nmot))) = true →
      cx.ctx[v]? = some (some l) → cx.minors.lookup l = some (minorSig I r q (i - (np + nmot))) →
      RecArgsR cx r q np nmot nmin (i + 1) refs ts →
      RecArgsR cx r q np nmot nmin i (.name (.var v) :: refs) ((cx.lvl l, .name) :: ts)
  | minorTele {cx : Cx} {r : CId} {q : Profile} {np nmot nmin i : Nat} {m : Src.Term}
      {t t' : Term} {refs : List Ref} {ts : List (Term × Mode)} :
      IsMinor np nmot nmin i → I.paramIrr r q i = false →
      hasName (minorSig I r q (i - (np + nmot))) = true → (∀ v, m ≠ .var v) →
      (minorSig I r q (i - (np + nmot))).length ≤ m.lamCount → TR cx m t →
      Term.setModes (minorSig I r q (i - (np + nmot))) t = some t' →
      RecArgsR cx r q np nmot nmin (i + 1) refs ts →
      RecArgsR cx r q np nmot nmin i (.name m :: refs) ((t', .name) :: ts)

end

/-- The arguments of a recursor rule's minor application (`ruleBody`). -/
inductive RuleArgsR : Cx → List Src.Term.Arg → List (Term × Mode) → Prop
  | nil {cx : Cx} : RuleArgsR cx [] []
  | irr {cx : Cx} {a : Src.Term} {m : Src.Mode} {r : Src.Rel} {rest : List Src.Term.Arg}
      {rest' : List (Term × Mode)} :
      r.irrP cx.prof = true → RuleArgsR cx rest rest' →
      RuleArgsR cx ((a, m, r) :: rest) ((.box, .strict) :: rest')
  | name {cx : Cx} {a : Src.Term} {r : Src.Rel} {a' : Term} {rest : List Src.Term.Arg}
      {rest' : List (Term × Mode)} :
      r.irrP cx.prof = false → TR I G cx a a' → RuleArgsR cx rest rest' →
      RuleArgsR cx ((a, .byName, r) :: rest) ((a', .name) :: rest')
  | strict {cx : Cx} {a : Src.Term} {r : Src.Rel} {a' : Term} {rest : List Src.Term.Arg}
      {rest' : List (Term × Mode)} :
      r.irrP cx.prof = false → TR I G cx a a' → RuleArgsR cx rest rest' →
      RuleArgsR cx ((a, .strict, r) :: rest) ((a', .strict) :: rest')

/-- The context of a recursor rule's body inside `r⋆` (`ruleBody`). -/
def ruleCx (q : Profile) (pre depth : Nat) (minors : List (Nat × List Mode))
    (fields : List (Option Nat)) : Cx :=
  ({ prof := q, ctx := [], depth, minors } : Cx).under ((List.range pre).map some ++ fields)

/-- A recursor rule's body inside `r⋆` (`ruleBody`). -/
inductive RuleBodyR (r : CId) (q : Profile) (pre depth : Nat) (minors : List (Nat × List Mode))
    (rule : Src.Rule) (fields : List (Option Nat)) : Term → Prop
  | var {body : Src.Term} {v : Nat} {args : List Src.Term.Arg} {h : Term}
      {args' : List (Term × Mode)} :
      peelUpTo (pre + rule.fields) rule.rhs = (pre + rule.fields, body) →
      fields.length = rule.fields → body.spineL = (.var v, args) →
      TR I G (ruleCx q pre depth minors fields) (.var v) h →
      RuleArgsR I G (ruleCx q pre depth minors fields) args args' →
      (hasName (args'.map (·.2)) = true →
        ∃ l, (ruleCx q pre depth minors fields).ctx[v]? = some (some l) ∧
          minors.lookup l = some (args'.map (·.2))) →
      RuleBodyR r q pre depth minors rule fields (Term.apps h args')
  | other {body : Src.Term} {t : Term} :
      peelUpTo (pre + rule.fields) rule.rhs = (pre + rule.fields, body) →
      fields.length = rule.fields → (∀ v, body.spineL.1 ≠ .var v) →
      TR I G (ruleCx q pre depth minors fields) body t →
      RuleBodyR r q pre depth minors rule fields t

/-- `r⋆`'s alternatives (`recStarBody`, ordinary). -/
inductive RecAltsR (r : CId) (q : Profile) (pre arity : Nat) (minors : List (Nat × List Mode))
    (ind : CId) : Nat → List Src.Rule → List Alt → Prop
  | nil {j : Nat} : RecAltsR r q pre arity minors ind j [] []
  | cons {j : Nat} {rule : Src.Rule} {rules : List Src.Rule} {key : Key.CtorKey} {n : Nat}
      {fields : List (Option Nat)} {body : Term} {alts : List Alt} :
      RuleAltR I r q arity ind j rule key n fields →
      RuleBodyR I G r q pre (arity + n) minors rule fields body →
      RecAltsR r q pre arity minors ind (j + 1) rules alts →
      RecAltsR r q pre arity minors ind j (rule :: rules) (.mk key n body :: alts)

/-- The binder modes of `r⋆` and its minors with their dispatch signatures. -/
def recModes (r : CId) (q : Profile) (np nmot nmin ni : Nat) : List Mode :=
  (List.range (np + nmot + nmin + ni + 1)).map fun i =>
    if np + nmot ≤ i && i < np + nmot + nmin && !I.paramIrr r q i then Mode.name else .strict

def recMinors (r : CId) (q : Profile) (np nmot nmin ni : Nat) : List (Nat × List Mode) :=
  ((List.range nmin).filter fun j =>
    (recModes I r q np nmot nmin ni).getD (np + nmot + j) .strict == .name).map
      fun j => (np + nmot + j, minorSig I r q j)

/-- The body of `r⋆` at `q` (`recStarBody`). -/
inductive RecStarR (r : CId) (q : Profile) : Term → Prop
  | empty {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Src.Rule}
      {ty : Src.Term} :
      I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) → I.kindAt r q = some .empty →
      RecStarR r q (Term.lams (recModes I r q np nmot nmin ni) .trap)
  | sub {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Src.Rule}
      {ty : Src.Term} {w : Src.PropWhen} {srcs : List Src.FieldSrc} {rule : Src.Rule}
      {body : Term} :
      I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
      I.kindAt r q = some (.subsingleton w srcs) → rules.head? = some rule →
      RuleBodyR I G r q (np + nmot + nmin) (np + nmot + nmin + ni + 1)
        (recMinors I r q np nmot nmin ni) rule
        (srcs.map fun
          | .index i => some (np + nmot + nmin + i)
          | .proof => none) body →
      RecStarR r q (Term.lams (recModes I r q np nmot nmin ni) body)
  | ord {sf k : Bool} {lv np nmot nmin ni : Nat} {ind : CId} {rules : List Src.Rule}
      {ty : Src.Term} {alts : List Alt} :
      I.decl? r = some (.recr sf k lv np nmot nmin ni ind rules ty) →
      I.kindAt r q = some .ordinary → I.unbox? ind q = none →
      RecAltsR I G r q (np + nmot + nmin) (np + nmot + nmin + ni + 1)
        (recMinors I r q np nmot nmin ni) ind 0 rules alts →
      RecStarR r q (Term.lams (recModes I r q np nmot nmin ni) (.case (.var 0) alts none))

/-- The wrapper's context: its `a` strict binders. -/
def wrapCx (q : Profile) (a : Nat) : Cx :=
  { prof := q, ctx := (List.range a).reverse.map some, depth := a }

/-- The body of the wrapper of special head `h` at `q` (`wrapperBody`). -/
inductive WrapR (h : Head) (q : Profile) : Term → Prop
  | prim {op : Src.PrimOp} :
      h = .prim op →
      WrapR h q (Term.lams (List.replicate (headArity I h) .strict)
        (.prim (Prim.ofSrc op) ((List.range (headArity I h)).map fun i =>
          (wrapCx q (headArity I h)).lvl i)))
  | other {c : CId} {body : Term} :
      (h = .ctor c ∨ h = .quotMk c ∨ h = .quotLift c ∨ h = .recr c ∨ h = .cases c) →
      I.headOf c = some h →
      SatR I G (wrapCx q (headArity I h)) h q
        ((List.range (headArity I h)).map fun i =>
          (Src.Term.var (headArity I h - 1 - i), Src.Mode.strict, wrapClass I h c i)) body →
      WrapR h q (Term.lams (List.replicate (headArity I h) .strict) body)

/-- The context of a constant's δ body at `q`. -/
def bodyCx (q : Profile) : Cx := { prof := q, ctx := [], depth := 0 }

/-- The body of the global with key `key` (`keyBody`). -/
inductive BodyR : Key.GKey → Term → Prop
  | const {c : CId} {q : Profile} {b : Src.Term} {body : Term} :
      I.deltaBody c = some b → TR I G (bodyCx q) b body → BodyR (.const c q) body
  | byName {c : CId} {q : Profile} {b : Src.Term} {a : Nat} {b₀ body : Term} :
      I.lazy.get? c = some a → I.deltaBody c = some b → a ≤ b.lamCount →
      TR I G (bodyCx q) b b₀ → Term.setModes (lazyModes I c q a) b₀ = some body →
      BodyR (.byName c q) body
  | recStar {r : CId} {q : Profile} {body : Term} : RecStarR I G r q body → BodyR (.recStar r q) body
  | wrapper {h : Head} {q : Profile} {body : Term} : WrapR I G h q body → BodyR (.wrapper h q) body

/-- Every global `G` names has the key it is named by and a body so related. -/
def ProgR (L : Program) : Prop :=
  ∀ key g, G key g → ∃ gl, L.global? g = some gl ∧ gl.key = key ∧ BodyR I G key gl.body

end Compilatrix.Lam.Erase.Proof
