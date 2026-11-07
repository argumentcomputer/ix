import IxCC.Anf.Proof.Spec.Trees
import IxCC.Anf.Proof.Walk.Prog

/-! # P4: the relation

The specialiser's output `Q` keeps the input `P`'s globals, with some
callers' bodies rewritten, and adds specialisations. Values are related by
the walk relation (`WalkProof.WV`) for two pieces of P4's code:

* **Rewritten code** (`RwClo`, the walk relation's other-pass closures): a
  caller's body (or a local function's, or a join point's) whose calls of
  specialised globals call specialisations (`RwE`), at a call site that
  builds exactly the specialisation called (`SiteOk`), with definitions that
  hold of the source environment (`DefsOk`).
* **Specialisation bodies**: the walk of the callee's body (redirecting its
  recursive calls), after a prologue that rebuilds the caller's definitions
  the masked arguments' value trees need. A specialisation built at a call
  site is a `Site`; `Site.Ok` collects what its construction established.
  P4's walk configurations (`V`) are the plain walk over `P` (the prologue's
  local functions) and the redirecting walk of a site, for an activation
  (`Site.Act`): source arguments whose masked ones are the roots' values at
  the site, specialisation arguments whose level holes stand for the
  caller's levels there (`Site.Lvls`, related pairs) (M2.3). -/

set_option autoImplicit false

namespace IxCC.Anf.Specialize.Proof

open Walk (Ent Cfg)
open WalkProof (WV WVs VOk)

/-! ## Specialisations built at call sites -/

/-- A specialisation built at a call site: the caller's definitions and
source environment there, the site's trees and roots, the callee, the
specialisation's id, and its prologue, level map and walked body. -/
structure Site where
  defs : Src.NatMap Def
  ρs : List Val
  t : Trees
  roots : List (Nat × Opd)
  g : GlobalId
  gd : GDef
  s : GlobalId
  pro : List Bind
  m : List (Nat × Opd)
  body : Exp

namespace Site

variable (D : Site)

/-- The callee's arity. -/
def n : Nat := D.gd.ps.length

/-- The specialisation's arity (its holes). -/
def H : Nat := D.t.holes.length

/-- The level holes' operands in the specialisation. -/
def m0 : List (Nat × Opd) := D.t.levelHoles.map fun (l, h) => (l, .lvl h)

/-- The redirection of the callee's calls to the specialisation. -/
def r : Walk.Redirect := specRedirect D.defs D.roots D.m D.t D.g D.n D.s

/-- The walk environment of the callee's parameters. -/
def σ : List Ent := (List.range D.n).reverse.map fun i => Ent.opd (specParam D.defs D.roots D.m D.t i)

/-- The walk configuration of the specialisation's body. -/
def cfg (P : Program) : Cfg := { prog := P, redirect := some D.r }

/-- An activation: the callee's arguments, whose masked ones are the roots'
values at the site, and the specialisation's arguments. -/
def Act (vs Hv : List Val) : Prop :=
  vs.length = D.n ∧ Hv.length = D.H ∧ ∀ i o, D.roots.lookup i = some o → o.val D.ρs = vs[i]?

/-- The holes standing for the caller's levels: the level's value at the
site and the hole's value, as a pair of `prs`. -/
def Lvls (Hv : List Val) (prs : List (Val × Val)) : Prop :=
  ∀ (k l : Nat), D.t.holes[k]? = some (.level l) →
    ∃ v w, (Opd.lvl l).val D.ρs = some v ∧ Hv[k]? = some w ∧ (v, w) ∈ prs

end Site

/-- What a specialisation's construction established: the callee and the
output's global, the caller's definitions, the trees' invariants (holes for
the unmasked parameters, covered roots), the prologue and the walk of the
callee's body. -/
structure Site.Ok (P Q : Program) (D : Site) : Prop where
  hg : P.global? D.g = some D.gd
  hs : ∃ gdS, Q.global? D.s = some gdS ∧ gdS.ps.length = D.H ∧ gdS.body = binds D.pro D.body
  defs : DefsOk P D.defs D.ρs
  trees : TreesOk D.defs D.ρs.length D.n [] D.t
  roots : ∀ i o, D.roots.lookup i = some o → i < D.n ∧ Covered D.defs D.t o ∧ InRange D.ρs.length o
  params : ∀ i, i < D.n → D.roots.lookup i = none → ∃ h : Nat, D.t.holes[h]? = some (HoleSrc.param i)
  pro : prologue P D.defs D.m0 D.H (sortNats D.t.needed) = .ok (D.pro, D.m)
  walk : ∃ fuel s s', (Walk.walk (D.cfg P) fuel { σ := D.σ }
    { d := D.H + D.pro.length, dj := 0, facts := .leaf } D.gd.body .ret).run s = .ok (D.body, s')

/-- P4's walk configurations: the plain walk over the input, and the walk of
a specialisation's body in one of its activations. -/
def V (P Q : Program) : Cfg → List Val → List Val → List (Val × Val) → Prop := fun C ρ ρ' prs =>
  C = { prog := P } ∨ ∃ (D : Site) (vs Hv : List Val), D.Ok P Q ∧ C = D.cfg P ∧ D.Act vs Hv ∧
    D.Lvls Hv prs ∧ vs.reverse <:+ ρ ∧ Hv.reverse <:+ ρ'

/-! ## Rewritten code -/

/-- A rewritten call site: the specialisation the site builds with id `s`
is the output's global `s`, and the call passes the holes' values. -/
def SiteOk (P Q : Program) (defs : Src.NatMap Def) (d : Nat) (g : GlobalId) (as : List Atom) (s : GlobalId)
    (args : List Atom) : Prop :=
  ∃ (inv : Nat) (fkey : Key.GKey) (gd : GDef) (mask : List Bool) (t : Trees) (keys : List Key.ArgKey)
    (roots : List (Nat × Opd)) (spec : GDef),
    P.global? g = some gd ∧ fixedOk gd g mask = true ∧
    siteTrees P defs fkey inv d mask as = (t, keys, roots) ∧
    buildSpec P defs t roots g gd (Key.GKey.spec gd.key keys) s = .ok spec ∧
    (∃ gdS, Q.global? s = some gdS ∧ gdS.ps.length = spec.ps.length ∧ gdS.body = spec.body) ∧
    args = siteArgs t d as

mutual

/-- A term and its rewrite, under definitions of its levels, at depth `d`. -/
inductive RwE (P Q : Program) : Src.NatMap Def → Nat → Exp → Exp → Prop
  | bind {defs : Src.NatMap Def} {d : Nat} {c : Ixon.V3.LetContract} {b b' : Bind} {body body' : Exp} {df : Def} :
      RwB P Q defs d b b' → DfOk P defs d b df → RwE P Q (defs.insert d df) (d + 1) body body' →
      RwE P Q defs d (.bind c b body) (.bind c b' body')
  | join {defs : Src.NatMap Def} {d n : Nat} {r : Bool} {jb jb' body body' : Exp} :
      RwE P Q (blankDefs defs d n) (d + n) jb jb' → RwE P Q defs d body body' →
      RwE P Q defs d (.join n r jb body) (.join n r jb' body')
  | case {defs : Src.NatMap Def} {d : Nat} {x : Atom} {alts alts' : List Alt} {dflt dflt' : Option Exp} :
      RwAlts P Q defs d alts alts' → RwOpt P Q defs d dflt dflt' →
      RwE P Q defs d (.case x alts dflt) (.case x alts' dflt')
  | tick {defs : Src.NatMap Def} {d : Nat} {e e' : Exp} : RwE P Q defs d e e' → RwE P Q defs d (.tick e) (.tick e')
  | jump {defs : Src.NatMap Def} {d j : Nat} {as : List Atom} : RwE P Q defs d (.jump j as) (.jump j as)
  | ret {defs : Src.NatMap Def} {d : Nat} {a : Atom} : RwE P Q defs d (.ret a) (.ret a)
  | trap {defs : Src.NatMap Def} {d : Nat} : RwE P Q defs d .trap .trap

/-- A binding and its rewrite. -/
inductive RwB (P Q : Program) : Src.NatMap Def → Nat → Bind → Bind → Prop
  | same {defs : Src.NatMap Def} {d : Nat} {b : Bind} : RwB P Q defs d b b
  | fn {defs : Src.NatMap Def} {d : Nat} {ps : List Ixon.V3.BinderContract} {fb fb' : Exp} :
      RwE P Q (blankDefs defs d ps.length) (d + ps.length) fb fb' → RwB P Q defs d (.fn ps fb) (.fn ps fb')
  | call {defs : Src.NatMap Def} {d : Nat} {g s : GlobalId} {as args : List Atom} :
      SiteOk P Q defs d g as s args → RwB P Q defs d (.call g as) (.call s args)

/-- Alternatives and their rewrites. -/
inductive RwAlts (P Q : Program) : Src.NatMap Def → Nat → List Alt → List Alt → Prop
  | nil {defs : Src.NatMap Def} {d : Nat} : RwAlts P Q defs d [] []
  | cons {defs : Src.NatMap Def} {d n : Nat} {key : Key.CtorKey} {b b' : Exp} {alts alts' : List Alt} :
      RwE P Q (blankDefs defs d n) (d + n) b b' → RwAlts P Q defs d alts alts' →
      RwAlts P Q defs d (.mk key n b :: alts) (.mk key n b' :: alts')

/-- A default alternative and its rewrite. -/
inductive RwOpt (P Q : Program) : Src.NatMap Def → Nat → Option Exp → Option Exp → Prop
  | none {defs : Src.NatMap Def} {d : Nat} : RwOpt P Q defs d none none
  | some {defs : Src.NatMap Def} {d : Nat} {e e' : Exp} : RwE P Q defs d e e' → RwOpt P Q defs d (some e) (some e')

end

/-- A body and its rewrite over `nn` parameters and a captured environment
`ρ`, with definitions that hold whatever the arguments. -/
def RwClo (P Q : Program) : Nat → List Val → Exp → Exp → Prop := fun nn ρ b b' =>
  ∃ defs, RwE P Q defs (ρ.length + nn) b b' ∧
    ∀ args : List Val, args.length = nn → DefsOk P defs (args.reverse ++ ρ)

/-- P4's value relation. -/
abbrev R4 (P Q : Program) : Val → Val → Prop := WV Q (V P Q) (RwClo P Q)

/-- Join closures of rewritten code over related environments. -/
inductive JRw (P Q : Program) : List JClo → List JClo → Prop
  | nil : JRw P Q [] []
  | cons {ρj ρj' : List Val} {Jj Jj' J J' : List JClo} {ar : Nat} {b b' : Exp} {r : Bool} :
      WVs Q (V P Q) (RwClo P Q) ρj ρj' → JRw P Q Jj Jj' → RwClo P Q ar ρj b b' → JRw P Q J J' →
      JRw P Q (.mk ρj Jj ar b r :: J) (.mk ρj' Jj' ar b' r :: J')

end IxCC.Anf.Specialize.Proof
