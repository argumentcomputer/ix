import Tests.Ix.Kernel.TutorialMeta

/-! # Reductions no kernel may perform beyond Lean's (fixtures)

The primitive fast paths of the Rust kernel and `Ix.Tc` recognized three
class methods by their TYPE argument alone and never read the instance (the
IxVM circuit had the second, on `BitVec.ofNat` operands of raw literals):

* `OfNat.ofNat (BitVec w) n inst`, read as `BitVec.ofNat w n`;
* `decide (@LT.lt (BitVec w) inst a b) dec`, decided as `BitVec.ult w a b`;
* `@SizeOf.sizeOf Unit inst x` (and `PUnit`), reduced to `1`.

A class's instance is an ordinary argument a prover chooses, so each rule
made a false equation hold by `rfl`. Two further rules, in all three
kernels, equated terms Lean's kernel keeps apart, though nothing false
follows from them: `System.Platform.numBits ≡ 64`
(`System.Platform.getNumBits` is an opaque) and
`(Decidable.rec … d).val ≡ Decidable.rec (… .val) d` on a variable `d`.

The `bad_thm`s state each of these by `Eq.refl`, installed without Lean's
kernel check (`TutorialMeta.unchecked`, `debug.skipKernelTC`); every kernel
must reject them. `false*` are ordinary, kernel-checked derivations of
`False` from the false equations, so a kernel that accepts the closure of
one of them certifies a proof of `False`. The `good_thm`s are controls
every kernel must accept: the same shapes with the canonical instances, the
true values of the non-canonical instances, and the reductions the removed
rules short-cut, done honestly.

`Tests.Ix.Kernel.FastPaths` (`kernel-fast-paths`) checks every probe's
closure with the Rust kernel, `Ix.Tc` and IxC. In the `ixvm` runner, the
IxVM arena checks the registered cases subject-only (`verify_const`) and the
exploit suite checks every probe's closure through `verify_claim`.
-/

open Tests.Ix.Kernel.TutorialMeta

-- The instances below are deliberately non-canonical and passed explicitly;
-- they are not declared as instances.
set_option warn.classDefReducibility false

namespace Tests.Ix.Kernel.FastPathDefs

/-- A non-canonical `LT (BitVec 8)`: nothing is less than anything. -/
def weirdLT : LT (BitVec 8) := ⟨fun _ _ => False⟩

/-- A non-canonical `OfNat (BitVec 8) 5`: the numeral `5` is `0#8`. -/
def weirdOfNat : OfNat (BitVec 8) 5 := ⟨BitVec.ofNat 8 0⟩

/-- A non-canonical `SizeOf Unit`: every unit has size 7. -/
def weirdSizeOf : SizeOf Unit := ⟨fun _ => 7⟩

/-! ## Must be rejected

`bad_thm` declares the name it is given, without the current namespace, so
the names are written in full. -/

/- `decide` of a proposition that unfolds to `False`, claimed `true`. -/
bad_thm Tests.Ix.Kernel.FastPathDefs.badLt :
    @decide (@LT.lt (BitVec 8) weirdLT 0 1) instDecidableFalse = true :=
  unchecked (Eq.refl true)

/- The same with the operands written `BitVec.ofNat` of raw literals: IxVM's
rule read only that spelling, not the numerals above. -/
bad_thm Tests.Ix.Kernel.FastPathDefs.badLtOfNat :
    @decide (@LT.lt (BitVec 8) weirdLT (BitVec.ofNat (nat_lit 8) (nat_lit 0))
        (BitVec.ofNat (nat_lit 8) (nat_lit 1)))
      instDecidableFalse = true :=
  unchecked (Eq.refl true)

/- `(0#8).toNat`, claimed `5`. -/
bad_thm Tests.Ix.Kernel.FastPathDefs.badOfNat :
    (@OfNat.ofNat (BitVec 8) 5 weirdOfNat).toNat = 5 :=
  unchecked (@Eq.refl Nat 5)

/- `7`, claimed `1`. -/
bad_thm Tests.Ix.Kernel.FastPathDefs.badSizeOf :
    @SizeOf.sizeOf Unit weirdSizeOf () = 1 :=
  unchecked (@Eq.refl Nat 1)

/- The platform's word size is an opaque's value, not definitionally `64`. -/
bad_thm Tests.Ix.Kernel.FastPathDefs.numBits64 : System.Platform.numBits = 64 :=
  unchecked (@Eq.refl Nat 64)

/- A commuting conversion: true for every value of `d`, but Lean's kernel
does not move a projection inside a recursor over a variable. -/
bad_thm Tests.Ix.Kernel.FastPathDefs.finCommute :
    ∀ (p : Prop) (d : Decidable p) (f g : Fin 3),
      (@Decidable.rec p (fun _ => Fin 3) (fun _ => f) (fun _ => g) d).val =
        @Decidable.rec p (fun _ => Nat) (fun _ => f.val) (fun _ => g.val) d :=
  unchecked (fun (p : Prop) (d : Decidable p) (f g : Fin 3) =>
    @Eq.refl Nat (@Decidable.rec p (fun _ => Nat) (fun _ => f.val) (fun _ => g.val) d))

/-! ## Derivations of `False`

Each is accepted by Lean's kernel given its `bad` lemma; only that lemma's
own check stands between it and a proof of `False`. They unfold the
instance and use congruence, so they do not depend on how a kernel reduces
the class method. -/

theorem falseLt : False :=
  (@of_decide_eq_true (@LT.lt (BitVec 8) weirdLT 0 1) instDecidableFalse badLt :)

theorem falseLtOfNat : False :=
  (@of_decide_eq_true (@LT.lt (BitVec 8) weirdLT (BitVec.ofNat (nat_lit 8) (nat_lit 0))
      (BitVec.ofNat (nat_lit 8) (nat_lit 1)))
    instDecidableFalse badLtOfNat :)

theorem falseOfNat : False := by
  have h : (@OfNat.ofNat (BitVec 8) 5 weirdOfNat) = BitVec.ofNat 8 0 := rfl
  have h3 : (BitVec.ofNat 8 0).toNat = 0 := rfl
  have h4 : (5 : Nat) = 0 := badOfNat.symm.trans ((congrArg BitVec.toNat h).trans h3)
  exact absurd h4 (by decide)

theorem falseSizeOf : False := by
  have h : @SizeOf.sizeOf Unit weirdSizeOf = fun _ => 7 := rfl
  have h2 : (1 : Nat) = 7 := badSizeOf.symm.trans (congrFun h ())
  exact absurd h2 (by decide)

/-! ## Must be accepted -/

-- The three shapes with the canonical instances.
good_thm Tests.Ix.Kernel.FastPathDefs.okLt : decide ((0 : BitVec 8) < 1) = true := rfl
good_thm Tests.Ix.Kernel.FastPathDefs.okOfNat : (5 : BitVec 8).toNat = 5 := rfl
good_thm Tests.Ix.Kernel.FastPathDefs.okSizeOf : sizeOf () = 1 := rfl

-- The non-canonical instances' true values: a kernel that reads the
-- instance computes these, one that ignores it contradicts them.
good_thm Tests.Ix.Kernel.FastPathDefs.weirdLtVal :
    @decide (@LT.lt (BitVec 8) weirdLT 0 1) instDecidableFalse = false := rfl
good_thm Tests.Ix.Kernel.FastPathDefs.weirdOfNatVal :
    (@OfNat.ofNat (BitVec 8) 5 weirdOfNat).toNat = 0 := rfl
good_thm Tests.Ix.Kernel.FastPathDefs.weirdSizeOfVal :
    @SizeOf.sizeOf Unit weirdSizeOf () = 7 := rfl

-- `BitVec.ult` on numerals: the `OfNat.ofNat` arguments unfold to
-- `BitVec.ofNat` before the `BitVec.ult` rule reads them.
good_thm Tests.Ix.Kernel.FastPathDefs.okUlt : BitVec.ult (5 : BitVec 8) 7 = true := rfl

-- `PUnit`'s size on a variable, through structure eta on `PUnit.rec`.
good_thm Tests.Ix.Kernel.FastPathDefs.okSizeOfVar : ∀ x : Unit, sizeOf x = 1 :=
  fun _ => rfl
good_thm Tests.Ix.Kernel.FastPathDefs.okSizeOfPUnitVar : ∀ x : PUnit.{2}, sizeOf x = 1 :=
  fun _ => rfl

-- `Fin.val` of a `Decidable.rec` whose major is a constructor: ι-reduction,
-- then the projection.
good_thm Tests.Ix.Kernel.FastPathDefs.okFinRec :
    ∀ (p : Prop) (h : p) (f g : Fin 3),
      (@Decidable.rec p (fun _ => Fin 3) (fun _ => f) (fun _ => g) (.isTrue h)).val = g.val :=
  fun _ _ _ _ => rfl

end Tests.Ix.Kernel.FastPathDefs
