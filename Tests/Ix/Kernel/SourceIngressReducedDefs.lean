import Lean

/-! # Fields whose occurrence of the block reduces away (CQX.8)

Lean's kernel finds a block's nested occurrences syntactically and tests a
constructor field's positivity after whnf (`check_positivity`), so a field
that mentions the block only under a definition that drops the argument is
an ordinary, nonrecursive field: `K True (Box T)` with `K a _ := a` whnfs to
`True`. IxC's in-process modeller tested the mention syntactically and
declined such blocks; it now tests the field after rewriting its carriers
into the auxiliary family, whose install by the fold tests positivity after
whnf, as Lean does.

The blocks are built with `addDecl`, as lane P's reproducer
(`Tests/Ix/Compile/AuxCert/NestedSortUK.lean`), and checked by Lean's kernel
when this module builds:

* `V : Type`: nested through `BoxT : Type → Type`,
  `V.mk : K True (BoxT V) → V`, whose expanded block has the auxiliary
  `BoxT V` (Lean's `V.rec` has a motive for it, `V.rec_1` eliminates it);
* `W : Type`: nested, `W.mk : K' (BoxT W) → W` with `K' _ := True → True`;
* `A`, `B`: mutual, `A.mk : K True B → A` (the modeller's mutual rung);
* `S`: a single inductive, `S.mk : K True S → S` (the native route, which
  already tests after whnf: a regression check);
* `T`, `U`: lane P's reproducer and aux-cert's `NestedSortU`, nested at
  `Sort u` through the `Sort u`-polymorphic `Box`. Lean gives them a
  `Prop`-only recursor (the level may be zero and the expanded block has two
  members), and the modeller declines a non-`Prop` nested block with a small
  eliminator (its `_impl.unpack` eliminates into `Sort u`): a residual of
  the modeller that CQX.8 does not touch, which they now reach past the
  field test. (`Box` itself eliminates into `Prop` only, its field's sort
  `Sort u` may be `Prop`; the modeller declines a block nested through such
  a container whatever its own level, hence `BoxT` for `V` and `W`.) -/

open Lean Meta Elab Command

namespace Tests.Ix.Kernel.SourceIngressReducedDefs

universe u

/-- A proposition that ignores its second argument. -/
def K (a : Prop) (_ : Sort u) : Prop := a

/-- A proposition that ignores its argument. -/
def K' (_ : Sort u) : Prop := True → True

end Tests.Ix.Kernel.SourceIngressReducedDefs

-- `Box.{u} (α : Sort u) : Sort u`, one constructor with one field `α`.
run_meta do
  let u : Level := Level.param `u
  let ty := mkForall `α .default (mkSort u) (mkSort u)
  let ctorTy := mkForall `α .implicit (mkSort u)
    (mkForall `a .default (mkBVar 0)
      (mkApp (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.Box [u]) (mkBVar 1)))
  let ctor : Constructor := Constructor.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.Box.mk ctorTy
  let it : InductiveType := InductiveType.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.Box ty [ctor]
  addDecl (Declaration.inductDecl [`u] 1 [it] false)

-- `T.{u} : Sort u` with `mk : K True (Box T) → T` (lane P's reproducer).
run_meta do
  let u : Level := Level.param `u
  let t := mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.T [u]
  let field := mkApp2 (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.K [u]) (mkConst ``True)
    (mkApp (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.Box [u]) t)
  let ctor : Constructor :=
    Constructor.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.T.mk (mkForall `h .default field t)
  let it : InductiveType :=
    InductiveType.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.T (mkSort u) [ctor]
  addDecl (Declaration.inductDecl [`u] 0 [it] false)

-- `U.{u} : Sort u` with `mk : K' (Box U) → U` (aux-cert's `NestedSortU`).
run_meta do
  let u : Level := Level.param `u
  let t := mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.U [u]
  let field := mkApp (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.K' [u])
    (mkApp (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.Box [u]) t)
  let ctor : Constructor :=
    Constructor.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.U.mk (mkForall `h .default field t)
  let it : InductiveType :=
    InductiveType.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.U (mkSort u) [ctor]
  addDecl (Declaration.inductDecl [`u] 0 [it] false)

-- `BoxT (α : Type) : Type`, `Box` at `Type`: a container with a large
-- eliminator (`Box.{u}` eliminates into `Prop` only, its field's sort `Sort u`
-- may be `Prop`).
run_meta do
  let ty := mkForall `α .default (mkSort Level.one) (mkSort Level.one)
  let ctorTy := mkForall `α .implicit (mkSort Level.one)
    (mkForall `a .default (mkBVar 0)
      (mkApp (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.BoxT []) (mkBVar 1)))
  let ctor : Constructor := Constructor.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.BoxT.mk ctorTy
  let it : InductiveType := InductiveType.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.BoxT ty [ctor]
  addDecl (Declaration.inductDecl [] 1 [it] false)

-- `V : Type` with `mk : K True (BoxT V) → V`.
run_meta do
  let v := mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.V []
  let field := mkApp2 (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.K [Level.one])
    (mkConst ``True) (mkApp (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.BoxT []) v)
  let ctor : Constructor :=
    Constructor.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.V.mk (mkForall `h .default field v)
  addDecl (Declaration.inductDecl [] 0
    [InductiveType.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.V (mkSort Level.one) [ctor]] false)

-- `W : Type` with `mk : K' (BoxT W) → W`.
run_meta do
  let w := mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.W []
  let field := mkApp (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.K' [Level.one])
    (mkApp (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.BoxT []) w)
  let ctor : Constructor :=
    Constructor.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.W.mk (mkForall `h .default field w)
  addDecl (Declaration.inductDecl [] 0
    [InductiveType.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.W (mkSort Level.one) [ctor]] false)

-- `A B : Type`, mutual, with `A.mk : K True B → A` and `B.mk : B`.
run_meta do
  let a := mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.A []
  let b := mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.B []
  let field := mkApp2 (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.K [Level.one])
    (mkConst ``True) b
  let aCtor : Constructor :=
    Constructor.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.A.mk (mkForall `h .default field a)
  let bCtor : Constructor := Constructor.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.B.mk b
  addDecl (Declaration.inductDecl [] 0
    [InductiveType.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.A (mkSort Level.one) [aCtor],
     InductiveType.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.B (mkSort Level.one) [bCtor]] false)

-- `S : Type` with `S.mk : K True S → S`.
run_meta do
  let s := mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.S []
  let field := mkApp2 (mkConst `Tests.Ix.Kernel.SourceIngressReducedDefs.K [Level.one])
    (mkConst ``True) s
  let ctor : Constructor :=
    Constructor.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.S.mk (mkForall `h .default field s)
  addDecl (Declaration.inductDecl [] 0
    [InductiveType.mk `Tests.Ix.Kernel.SourceIngressReducedDefs.S (mkSort Level.one) [ctor]] false)

namespace Tests.Ix.Kernel.SourceIngressReducedDefs

/-- `T`'s recursor eliminates into `Prop` only and has a motive for `Box T`. -/
theorem t_rec (x : T.{u}) : True :=
  T.rec (motive_1 := fun _ => True) (motive_2 := fun _ => True)
    (fun _ => trivial) (fun _ _ => trivial) x

/-- `V`'s recursor eliminates into any sort, has a motive for `Box V` and no
hypothesis for the field. -/
noncomputable def v_rec (x : V) : Nat :=
  V.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (fun _ => 0) (fun _ n => n + 1) x

/-- `A`'s recursor has no hypothesis for the field. -/
theorem a_rec (x : A) : True :=
  A.rec (motive_1 := fun _ => True) (motive_2 := fun _ => True) (fun _ => trivial) trivial x

/-- `S`'s recursor has no hypothesis for the field. -/
theorem s_rec (x : S) : True := S.rec (motive := fun _ => True) (fun _ => trivial) x

end Tests.Ix.Kernel.SourceIngressReducedDefs

/-! ## A field whose recursive occurrence whnf reveals

The converse case (aux-cert's `SurgAlias`, AuxGen M3): `C.a : Id' D → C`
mentions the mutual member `D` only behind a reducible alias, which Lean's
kernel unfolds before it tests positivity, so the field is recursive and
Lean's `C.rec` gives it an inductive hypothesis. The modeller's mutual rung
classified the field syntactically, as ordinary, and the fold rejected the
block ("recursor rules are not the generated ones"); the rung now reads the
recursive fields off Lean's minor premises. -/

namespace Tests.Ix.Kernel.SourceIngressReducedDefs

abbrev Id' (α : Type) : Type := α

mutual
inductive C
  | nil : C
  | a : Id' D → C
inductive D
  | nil : D
  | b : D → D
end

noncomputable def c_rec : C → Nat :=
  @C.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1)

theorem c_rec_a : c_rec (.a (.b .nil)) = 2 := rfl

end Tests.Ix.Kernel.SourceIngressReducedDefs
