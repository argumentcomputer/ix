import Ix.CompileCert.ImageShape
import Ix.CompileCert.ExpressionSteps
import Ix.CompileCert.CliqueRowsCoverage
import Ix.CompileCert.SourceConstructorPositions
import IxC.Kernel.Rules.Derived
import IxC.Kernel.Verify.InstList

/-! # Raw reader conversion for the closed O6 recursor case

These are raw, ungraded kernel reductions. Raw reader .never markers are
not claimed to be validated annotations, and no value-model theorem is
applied to them. The actual pass and reading witnesses must supply every
source/target correspondence; no conversion or image law is an input.
-/

namespace Ix.CompileCert.O6RecRead

open Ix.Kernel (Mode)
open Ix.CompileCert.ExpressionState (Related)

variable {md : Mode} {keyOf : Ix.Name → Ix.Kernel.Key md} {levelOf : Ix.Level → Ix.Kernel.Level}

abbrev Rel := Related (fun n k => k = keyOf n) (fun l u => u = levelOf l)

theorem levels_unique {xs : List Ix.Level} {ys zs : List Ix.Kernel.Level}
    (h : List.Forall₂ (fun l u => u = levelOf l) xs ys)
    (h' : List.Forall₂ (fun l u => u = levelOf l) xs zs) : ys = zs := by
  induction h generalizing zs with
  | nil => cases h'; rfl
  | cons head _ tail =>
    cases h' with
    | cons head' rest => rw [head, head', tail rest]

/-- The common functional key/level graphs fix a raw reading uniquely,
including the actual semantic-contract metadata cases. -/
theorem related_unique {source : Ix.Expr} {a b : Ix.Kernel.Expr md}
    (h : Rel (keyOf := keyOf) (levelOf := levelOf) source a)
    (h' : Rel (keyOf := keyOf) (levelOf := levelOf) source b) : a = b := by
  induction h generalizing b with
  | bvar => cases h'; rfl
  | sort _ meaning => cases h' with | sort _ meaning' => rw [meaning, meaning']
  | const _ _ _ mapped universes =>
    cases h' with
    | const _ _ _ mapped' universes' =>
      rw [mapped, mapped', levels_unique universes universes']
  | app _ _ _ ihf iha => cases h' with | app _ hf ha => rw [ihf hf, iha ha]
  | lam _ _ _ _ _ iht ihb => cases h' with | lam _ _ _ ht hb => rw [iht ht, ihb hb]
  | all _ _ _ _ _ iht ihb => cases h' with | all _ _ _ ht hb => rw [iht ht, ihb hb]
  | letE _ _ _ _ _ _ iht ihv ihb => cases h' with | letE _ _ _ ht hv hb => rw [iht ht, ihv hv, ihb hb]
  | nat => cases h'; rfl
  | str => cases h'; rfl
  | proj _ _ mapped _ ih =>
    cases h' with
    | proj _ _ mapped' hv => rw [mapped.trans mapped'.symm, ih hv]
  | mdata _ _ plain _ ih =>
    cases h' with
    | mdata _ _ _ hb => exact ih hb
    | contract _ _ _ frame _ _ _ => rw [plain] at frame; cases frame
  | contract _ _ _ frame read _ lowered ih =>
    cases h' with
    | mdata _ _ plain _ => rw [plain] at frame; cases frame
    | contract _ _ _ _ read' hb lowered' =>
      have same := Except.ok.inj (read.symm.trans read')
      cases same
      have eq := ih hb
      rw [eq, lowered'] at lowered
      exact (Option.some.inj lowered).symm

/-- The raw reader's lambda prefix. Gates are syntactic facts, not semantic
or typing certificates. The domains can be arbitrary raw reader terms. -/
inductive Lambdas : Nat → Ix.Kernel.Expr md → Ix.Kernel.Expr md → Prop
  | zero (body) : Lambdas 0 body body
  | step {n ty body tail} {m : Ix.Kernel.BinderMeta} (gate : m.pw.isNever = true) (rest : Lambdas n body tail) :
      Lambdas (n + 1) (.lam ty body m) tail

theorem Lambdas.instantiate {n : Nat} {e body : Ix.Kernel.Expr md}
    (h : Lambdas n e body) (arg : Ix.Kernel.Expr md) (depth : Nat) :
    Lambdas n (e.instantiate1 arg depth) (body.instantiate1 arg (depth + n)) := by
  induction h generalizing depth with
  | zero => exact .zero _
  | step gate _ ih =>
    exact .step gate (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (depth + 1))

theorem red_spine {env : Ix.Kernel.Env md} {d : Nat} {a b : Ix.Kernel.Expr md}
    (h : Ix.Kernel.Rules.Red env d a b) (args : List (Ix.Kernel.Expr md)) :
    Ix.Kernel.Rules.Red env d (Ix.Kernel.Expr.mkAppN a args) (Ix.Kernel.Expr.mkAppN b args) := by
  induction args generalizing a b with
  | nil => exact h
  | cons x xs ih => exact ih (.appFn h)

/-- The raw beta chain is constructed from the actual lambda prefix, not
given as a conversion premise. The bulk-instantiation law is unconditional. -/
theorem Lambdas.beta {env : Ix.Kernel.Env md} {d n : Nat} {e body : Ix.Kernel.Expr md}
    (h : Lambdas n e body) (args : List (Ix.Kernel.Expr md)) (length : args.length = n) :
    Ix.Kernel.Rules.Red env d (Ix.Kernel.Expr.mkAppN e args) (body.instantiateList args.reverse) := by
  induction n generalizing e body args with
  | zero =>
    have eq : args = [] := List.eq_nil_of_length_eq_zero length
    subst args
    cases h
    simp only [Ix.Kernel.Expr.mkAppN, List.reverse_nil, Ix.Kernel.Expr.instantiateList_nil]
    exact .refl
  | succ n ih =>
    cases h with
    | step gate rest =>
      cases args with
      | nil => simp at length
      | cons a args =>
        have len : args.length = n := by simpa using length
        have hnext := rest.instantiate a 0
        have tailRed := ih hnext args len
        have eq : body.instantiateList (a :: args).reverse =
            (body.instantiate1 a n).instantiateList args.reverse := by
          rw [List.reverse_cons, Ix.Kernel.Expr.instantiateList_append_one]
          simp only [List.length_reverse, len, Nat.zero_add]
        rw [eq]
        exact .trans (red_spine (.betaGate gate) args) (by simpa only [Nat.zero_add] using tailRed)

theorem related_app_inv {f a : Ix.Expr} {target : Ix.Kernel.Expr md}
    (h : Rel (keyOf := keyOf) (levelOf := levelOf) (Ix.Expr.mkApp f a) target) :
    ∃ fk ak, Rel (keyOf := keyOf) (levelOf := levelOf) f fk ∧
      Rel (keyOf := keyOf) (levelOf := levelOf) a ak ∧ target = .app fk ak := by
  cases h with | app _ hf ha => exact ⟨_, _, hf, ha, rfl⟩

theorem related_apps_inv (args : List Ix.Expr) {f : Ix.Expr} {target : Ix.Kernel.Expr md}
    (h : Rel (keyOf := keyOf) (levelOf := levelOf) (args.foldl Ix.Expr.mkApp f) target) :
    ∃ fk ks, Rel (keyOf := keyOf) (levelOf := levelOf) f fk ∧
      List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) args ks ∧
      target = Ix.Kernel.Expr.mkAppN fk ks := by
  induction args generalizing f target with
  | nil => exact ⟨target, [], h, .nil, rfl⟩
  | cons a args ih =>
    obtain ⟨fa, ks, hfa, rest, eq⟩ := ih h
    obtain ⟨fk, ak, hf, ha, rfl⟩ := related_app_inv hfa
    exact ⟨fk, ak :: ks, hf, .cons ha rest, eq⟩

theorem related_apps {f : Ix.Expr} {fk : Ix.Kernel.Expr md}
    (hf : Rel (keyOf := keyOf) (levelOf := levelOf) f fk)
    {args : List Ix.Expr} {ks : List (Ix.Kernel.Expr md)}
    (h : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) args ks) :
    Rel (keyOf := keyOf) (levelOf := levelOf) (args.foldl Ix.Expr.mkApp f) (Ix.Kernel.Expr.mkAppN fk ks) := by
  induction h generalizing f fk with
  | nil => exact hf
  | cons ha _ ih => exact ih (.app _ hf ha)

theorem related_stripLams {n : Nat} {source body : Ix.Expr} {target : Ix.Kernel.Expr md}
    (h : Rel (keyOf := keyOf) (levelOf := levelOf) source target)
    (stripped : Ix.Compile.Pass.Opt.stripLams n source = some body) :
    ∃ tail, Lambdas n target tail ∧ Rel (keyOf := keyOf) (levelOf := levelOf) body tail := by
  induction n generalizing source target with
  | zero => have eq : source = body := Option.some.inj stripped; subst source; exact ⟨_, .zero _, h⟩
  | succ n ih =>
    cases source with
    | lam name type value info hash =>
      cases h with
      | lam _ _ _ _ bodyRel =>
        obtain ⟨tail, chain, related⟩ := ih bodyRel stripped
        exact ⟨tail, .step rfl chain, related⟩
    | _ => cases stripped

theorem strip_subst_go (params : Array Ix.Name) (us : Array Ix.Level)
    {n : Nat} {source body : Ix.Expr} (h : Ix.Compile.Pass.Opt.stripLams n source = some body) :
    Ix.Compile.Pass.Opt.stripLams n (Ix.Compile.Canon.substLevels.go params us source) =
      some (Ix.Compile.Canon.substLevels.go params us body) := by
  induction n generalizing source with
  | zero => have eq : source = body := Option.some.inj h; subst source; rfl
  | succ n ih =>
    cases source with
    | lam _ _ value _ _ => exact ih h
    | _ => cases h

theorem strip_subst (params : Array Ix.Name) (us : Array Ix.Level)
    {n : Nat} {source body : Ix.Expr} (h : Ix.Compile.Pass.Opt.stripLams n source = some body) :
    Ix.Compile.Pass.Opt.stripLams n (Ix.Compile.Canon.substLevels params us source) =
      some (Ix.Compile.Canon.substLevels params us body) := by
  unfold Ix.Compile.Canon.substLevels
  split
  · exact h
  · exact strip_subst_go params us h

theorem app_spine_subst_go (params : Array Ix.Name) (us : Array Ix.Level) (source : Ix.Expr) :
    Ix.Compile.Canon.getAppFnArgs (Ix.Compile.Canon.substLevels.go params us source) =
      (Ix.Compile.Canon.substLevels.go params us (Ix.Compile.Canon.getAppFnArgs source).1,
        (Ix.Compile.Canon.getAppFnArgs source).2.map (Ix.Compile.Canon.substLevels.go params us)) := by
  induction source with
  | app f a _ ih _ =>
    change ((Ix.Compile.Canon.getAppFnArgs (Ix.Compile.Canon.substLevels.go params us f)).1,
      (Ix.Compile.Canon.getAppFnArgs (Ix.Compile.Canon.substLevels.go params us f)).2.push
        (Ix.Compile.Canon.substLevels.go params us a)) = _
    rw [ih]
    simp only [Ix.Compile.Canon.getAppFnArgs, Array.map_push]
  | _ => simp only [Ix.Compile.Canon.getAppFnArgs, Ix.Compile.Canon.substLevels.go, Array.map_empty] <;> rfl

open Ix.Compile.Pass.Opt in
theorem telescope_rec {opt : OptEnv} {s : RecShape} {head : Ix.Name} {n : Nat}
    (h : standardTelescope opt s .kRec head = some n) : n = s.arity := by
  unfold standardTelescope at h
  obtain ⟨ci, _, h⟩ := ImageShape.bind_some h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact (Option.some.inj h).symm

open Ix.Compile.Pass.Opt in
/-- All pass data below come from the real successful recursor branch. -/
theorem o6_rec_output {opt : OptEnv} {o : Occ} {out : Ix.Expr} {r : Ix.Name}
    {block : OptBlock} {s : RecShape} (pass : O6.apply opt o = some out)
    (kind : classify o.head = some (.kRec, r)) (hb : opt.blockOf o.head = some block)
    (hs : block.shapes.get? r = some s) :
    ∃ ls ms mins, s.isSelection = true ∧ s.arity ≤ o.args.size ∧ O5.levels s o.us = some ls ∧
      pick (o.args.extract s.np (s.np + s.nm)) s.motiveSrc = some ms ∧
      pick (o.args.extract (s.np + s.nm) (s.np + s.nm + s.nmin)) (s.minorSrc.filterMap id) = some mins ∧
      out = Ix.Compile.Canon.mkAppN (Ix.Expr.mkConst s.ixRec ls)
        (o.args.extract 0 s.np ++ ms ++ mins ++
          o.args.extract (s.np + s.nm + s.nmin) s.arity ++ o.args.extract s.arity o.args.size) := by
  unfold O6.apply at pass
  obtain ⟨kr, hk, pass⟩ := ImageShape.bind_some pass
  rw [kind] at hk
  cases Option.some.inj hk
  have allowed : ((AuxKind.kRec != .kRec) && (AuxKind.kRec != .kRecOn)) = false := rfl
  simp only [allowed, Bool.false_eq_true, ↓reduceIte] at pass
  obtain ⟨actualBlock, hblock, pass⟩ := ImageShape.bind_some pass
  rw [hb] at hblock
  cases Option.some.inj hblock
  obtain ⟨actualShape, hshape, pass⟩ := ImageShape.bind_some pass
  rw [hs] at hshape
  cases Option.some.inj hshape
  split at pass
  · cases pass
  · rename_i selected
    have selected : s.isSelection = true := by simpa using selected
    obtain ⟨n, telescope, pass⟩ := ImageShape.bind_some pass
    have eq := telescope_rec telescope
    subst n
    split at pass
    · cases pass
    · rename_i enough
      have enough : s.arity ≤ o.args.size := Nat.le_of_not_gt enough
      obtain ⟨ls, hl, pass⟩ := ImageShape.bind_some pass
      obtain ⟨ms, hm, pass⟩ := ImageShape.bind_some pass
      have isRec : (AuxKind.kRec == .kRec) = true := rfl
      simp only [isRec, ↓reduceIte] at pass
      obtain ⟨mins, hn, pass⟩ := ImageShape.bind_some pass
      exact ⟨ls, ms, mins, selected, enough, hl, hm, hn, (Option.some.inj pass).symm⟩

theorem related_getApps {source : Ix.Expr} {target : Ix.Kernel.Expr md}
    (h : Rel (keyOf := keyOf) (levelOf := levelOf) source target) :
    ∃ fk ks, Rel (keyOf := keyOf) (levelOf := levelOf) (Ix.Compile.Canon.getAppFnArgs source).1 fk ∧
      List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf))
        (Ix.Compile.Canon.getAppFnArgs source).2.toList ks ∧ target = Ix.Kernel.Expr.mkAppN fk ks := by
  induction source generalizing target with
  | app f a hash ih _ =>
    cases h with
    | app _ hf ha =>
      obtain ⟨fk, ks, head, args, rfl⟩ := ih hf
      rename_i argK
      refine ⟨fk, ks ++ [argK], head, ?_, ?_⟩
      · simpa only [Ix.Compile.Canon.getAppFnArgs, Array.toList_push] using
          Loop.forall₂_append args (List.Forall₂.cons ha .nil)
      · exact (Ix.Kernel.Rules.Expr.mkAppN_append_one' _ _ _).symm
  | _ => exact ⟨target, [], h, .nil, rfl⟩

theorem app_spine_subst (params : Array Ix.Name) (us : Array Ix.Level) (source : Ix.Expr) :
    Ix.Compile.Canon.getAppFnArgs (Ix.Compile.Canon.substLevels params us source) =
      (Ix.Compile.Canon.substLevels params us (Ix.Compile.Canon.getAppFnArgs source).1,
        (Ix.Compile.Canon.getAppFnArgs source).2.map (Ix.Compile.Canon.substLevels params us)) := by
  unfold Ix.Compile.Canon.substLevels
  split
  · rw [Array.map_id']
  · exact app_spine_subst_go params us source

open Ix.Compile.Pass.Opt in
theorem o5_levels_result {s : RecShape} {us ls : Array Ix.Level} (h : O5.levels s us = some ls) :
    s.levelsAt us = ls := by
  unfold O5.levels at h
  split at h
  · exact Option.some.inj h
  · split at h
    · split at h
      · exact Option.some.inj h
      · cases h
    · cases h

open Ix.Compile.Pass.Opt in
/-- The empty substitution shortcut agrees with the actual O5 guards when
the occurrence supplies the source header's number of universe arguments. -/
theorem o5_subst_levels {s : RecShape} {us ls : Array Ix.Level}
    (arity : us.size = s.levelParams.size) (h : O5.levels s us = some ls) :
    (if s.levelParams.isEmpty || us.isEmpty then s.ixLevels else s.levelsAt us) = ls := by
  have emptyEq : s.levelParams.isEmpty = us.isEmpty := by simp [Array.isEmpty, arity]
  by_cases empty : s.levelParams.isEmpty = true
  · have ps : s.levelParams.size = 0 := by simpa [Array.isEmpty] using empty
    have hu : us = #[] := Array.eq_empty_iff_size_eq_zero.mpr (arity.trans ps)
    subst us
    cases levels : s.ixLevels with
    | mk values =>
      cases values with
      | nil => simpa [O5.levels, levels, ps, RecShape.levelsAt, empty] using h
      | cons u rest =>
        cases rest with
        | nil => cases u <;> simp_all [O5.levels, RecShape.levelsAt, Ix.Compile.Canon.substLevel]
        | cons _ _ => simp [O5.levels, levels, ps] at h
  · have both : (s.levelParams.isEmpty || us.isEmpty) = false := by simp [← emptyEq, empty]
    simpa only [both, Bool.false_eq_true, ↓reduceIte] using o5_levels_result h

theorem instantiate_apps (f : Ix.Kernel.Expr md) (args values : List (Ix.Kernel.Expr md)) :
    (Ix.Kernel.Expr.mkAppN f args).instantiateList values =
      Ix.Kernel.Expr.mkAppN (f.instantiateList values) (args.map (·.instantiateList values)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih =>
    simpa only [Ix.Kernel.Expr.mkAppN, Ix.Kernel.Expr.instantiateList, List.map_cons] using ih (.app f a)

/-- A checked selector's reversed de-Bruijn index retrieves the original
closed argument. Closedness is essential: kernel instantiation does not lift. -/
theorem instantiate_bvar_lookup {args : List (Ix.Kernel.Expr md)} {n i : Nat} {arg : Ix.Kernel.Expr md}
    (length : args.length = n) (found : args[i]? = some arg)
    (closed : ∀ a ∈ args, a.looseBVarsBounded 0 = true) :
    (Ix.Kernel.Expr.bvar (n - 1 - i)).instantiateList args.reverse = arg := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  have rev : args.reverse[n - 1 - i]? = some arg :=
    (List.getElem?_reverse' (by omega)).trans found
  obtain ⟨revBound, same⟩ := List.getElem?_eq_some_iff.mp rev
  have hclosed := closed _ (List.mem_reverse.mp (List.getElem_mem revBound))
  simp only [Ix.Kernel.Expr.instantiateList, Nat.not_lt_zero, Nat.sub_zero, revBound, ↓reduceIte, ↓reduceDIte]
  rw [Ix.Kernel.Expr.instantiateList_eq_self hclosed, same]

theorem forall₂_of_lookup {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (length : xs.length = ys.length)
    (each : ∀ (i : Nat) (x : α) (y : β), xs[i]? = some x → ys[i]? = some y → R x y) : List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil => have eq : ys = [] := List.eq_nil_of_length_eq_zero length.symm; subst ys; exact .nil
  | cons x xs ih =>
    cases ys with
    | nil => simp at length
    | cons y ys => exact .cons (each 0 x y rfl rfl) (ih (by simpa using length)
        (fun i x y hx hy => each (i + 1) x y hx hy))

theorem option_mapM {α β : Type} {f : α → Option β} {xs : Array α} {ys : Array β}
    (run : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs.toList ys.toList := by
  have lists : ∀ (as : List α) (bs : List β), as.mapM f = some bs → List.Forall₂ (fun x y => f x = some y) as bs := by
    intro as
    induction as with
    | nil => intro bs h; cases h; exact .nil
    | cons a as ih =>
      intro bs h
      rw [List.mapM_cons] at h
      obtain ⟨b, hb, h⟩ := ImageShape.bind_some h
      obtain ⟨rest, hr, h⟩ := ImageShape.bind_some h
      cases h
      exact .cons hb (ih rest hr)
  rw [Array.mapM_eq_mapM_toList] at run
  cases hl : xs.toList.mapM f with
  | none => rw [hl] at run; cases run
  | some bs => rw [hl] at run; cases run; simpa using lists _ _ hl

theorem allSome_filter {xs : Array (Option Nat)} (h : xs.all Option.isSome = true) :
    List.Forall₂ (fun o n => o = some n) xs.toList (xs.filterMap id).toList := by
  cases xs with
  | mk xs =>
    simp only [Array.toList_filterMap]
    change List.Forall₂ _ xs (xs.filterMap id)
    have all : ∀ o ∈ xs, o.isSome = true := by
      intro o ho
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
      exact Array.all_eq_true.mp h i hi
    clear h
    induction xs with
    | nil => exact .nil
    | cons o xs ih =>
      cases o with
      | none => have := all none (by simp); cases this
      | some n => exact .cons rfl (ih (fun o ho => all o (by simp [ho])))

theorem append4_at {α : Type} (a b c d : Array α) (i : Nat) :
    (a ++ b ++ c ++ d)[i]? = if i < a.size then a[i]? else if i < a.size + b.size then b[i - a.size]?
      else if i < a.size + b.size + c.size then c[i - a.size - b.size]? else d[i - a.size - b.size - c.size]? := by
  simp only [Array.getElem?_append, Array.size_append, Nat.sub_sub]
  split <;> split <;> simp_all <;> omega

theorem extract_at {α : Type} {xs : Array α} {start stop i : Nat}
    (fit : stop ≤ xs.size) (inside : i < stop - start) :
    (xs.extract start stop)[i]? = xs[start + i]? := by
  simp only [Array.getElem?_extract, Nat.min_eq_left fit, inside, ↓reduceIte]

def Selects (n : Nat) (input : Array Ix.Expr) (bodyArg arg : Ix.Expr) : Prop :=
  ∃ i hash, i < n ∧ bodyArg = .bvar (n - 1 - i) hash ∧ input[i]? = some arg

open Ix.Compile.Pass.Opt in
/-- The actual recognized positions produce the SAME arguments as the
executed pass's successful picks; this identity is proved, never assumed. -/
theorem data_picks {value body : Ix.Expr} {getRec : Ix.Name → Option Ix.RecursorVal}
    {s : RecShape} {bs input ms mins : Array Ix.Expr} {iv : Ix.RecursorVal} {hash : Address}
    (data : ImageShape.Data value getRec s body bs iv hash) (selected : s.isSelection = true)
    (enough : s.arity ≤ input.size)
    (hm : pick (input.extract s.np (s.np + s.nm)) s.motiveSrc = some ms)
    (hn : pick (input.extract (s.np + s.nm) (s.np + s.nm + s.nmin)) (s.minorSrc.filterMap id) = some mins) :
    List.Forall₂ (Selects s.arity input) bs.toList
      (input.extract 0 s.np ++ ms ++ mins ++ input.extract (s.np + s.nm + s.nmin) s.arity).toList := by
  have reads := data.reads
  have limit : s.np + s.nm + s.nmin + s.ni + 1 ≤ input.size := enough
  obtain ⟨_, _, _, _, _, bsize, _, _, motives, minors⟩ := data
  have mrel := option_mapM hm
  have nrel := option_mapM hn
  have somes := allSome_filter selected
  have msize : ms.size = iv.numMotives := by simpa [motives.1] using (CliqueRowsCoverage.forall₂_lengths mrel).symm
  have nsize : mins.size = iv.numMinors := by
    have h1 := (CliqueRowsCoverage.forall₂_lengths nrel).symm
    have h2 := (CliqueRowsCoverage.forall₂_lengths somes).symm
    simpa only [Array.length_toList] using h1.trans (h2.trans minors.1)
  have psize : (input.extract 0 s.np).size = s.np := by simp [Array.size_extract]; omega
  have tsize : (input.extract (s.np + s.nm + s.nmin) s.arity).size = s.ni + 1 := by
    rw [Array.size_extract, Nat.min_eq_left enough]; simp [RecShape.arity]; omega
  apply forall₂_of_lookup (by
    simp only [Array.length_toList, Array.size_append, psize, msize, nsize, tsize]; omega)
  intro i b a hbList haList
  have hb : bs[i]? = some b := by simpa using hbList
  have ha : (input.extract 0 s.np ++ ms ++ mins ++ input.extract (s.np + s.nm + s.nmin) s.arity)[i]? = some a :=
    by simpa only [Array.getElem?_toList] using haList
  have ib : i < bs.size := (Array.getElem?_eq_some_iff.mp hb).1
  rw [append4_at, psize, msize, nsize] at ha
  split at ha
  · rename_i hi
    obtain ⟨h, hbodyAt⟩ := reads.1 i hi
    have eq := Option.some.inj (hb.symm.trans hbodyAt)
    refine ⟨i, h, by simp [RecShape.arity]; omega, eq, ?_⟩
    rw [extract_at (xs := input) (start := 0) (stop := s.np) (by omega) (by omega)] at ha
    simpa only [Nat.zero_add] using ha
  · rename_i hp
    split at ha
    · rename_i hi
      have ji : i - s.np < s.motiveSrc.size := by rw [motives.1]; omega
      have get := Array.getElem?_eq_some_getElem! s.motiveSrc (i - s.np) ji
      obtain ⟨jbound, h, hbodyAt⟩ := reads.2.2.1 _ _ get
      obtain ⟨arg, target, source⟩ := SourceConstructorPositions.forall₂_getElem? mrel
        (i := i - s.np) (by simpa only [Array.getElem?_toList] using get)
      have targetA : ms[i - s.np]? = some arg := by simpa only [Array.getElem?_toList] using target
      have same : arg = a := Option.some.inj (targetA.symm.trans ha)
      have index : s.np + (i - s.np) = i := by omega
      rw [index] at hbodyAt
      refine ⟨s.np + s.motiveSrc[i - s.np]!, h, by simp [RecShape.arity]; omega,
        Option.some.inj (hb.symm.trans hbodyAt), ?_⟩
      rw [extract_at (xs := input) (start := s.np) (stop := s.np + s.nm) (by omega) (by omega), same] at source
      exact source
    · rename_i hmEnd
      split at ha
      · rename_i hi
        have ji : i - s.np - iv.numMotives < (s.minorSrc.filterMap id).size := by
          have length := CliqueRowsCoverage.forall₂_lengths somes
          have count : s.minorSrc.size = iv.numMinors := minors.1
          simp only [Array.length_toList] at length; omega
        have get := Array.getElem?_eq_some_getElem! (s.minorSrc.filterMap id) (i - s.np - iv.numMotives) ji
        obtain ⟨o, original, same⟩ := SourceConstructorPositions.forall₂_getElem? (CliqueRowsCoverage.forall₂_swap somes)
          (i := i - s.np - iv.numMotives) (by simpa only [Array.getElem?_toList] using get)
        rw [same] at original
        obtain ⟨jbound, h, hbodyAt⟩ := reads.2.2.2.1 (i - s.np - iv.numMotives) _
          (by simpa only [Array.getElem?_toList] using original)
        obtain ⟨arg, target, source⟩ := SourceConstructorPositions.forall₂_getElem? nrel
          (i := i - s.np - iv.numMotives) (by simpa only [Array.getElem?_toList] using get)
        have targetA : mins[i - s.np - iv.numMotives]? = some arg := by simpa only [Array.getElem?_toList] using target
        have sameArg : arg = a := Option.some.inj (targetA.symm.trans ha)
        have index : s.np + iv.numMotives + (i - s.np - iv.numMotives) = i := by omega
        rw [index] at hbodyAt
        refine ⟨s.np + s.nm + (s.minorSrc.filterMap id)[i - s.np - iv.numMotives]!, h,
          by simp [RecShape.arity]; omega, Option.some.inj (hb.symm.trans hbodyAt), ?_⟩
        rw [extract_at (xs := input) (start := s.np + s.nm) (stop := s.np + s.nm + s.nmin)
          (by omega) (by omega), sameArg] at source
        exact source
      · rename_i hnEnd
        let j := i - s.np - iv.numMotives - iv.numMinors
        have jb : j < s.ni + 1 := by dsimp [j]; omega
        obtain ⟨h, hbodyAt⟩ := reads.2.1 j jb
        have index : s.np + iv.numMotives + iv.numMinors + j = i := by dsimp [j]; omega
        rw [index] at hbodyAt
        refine ⟨s.np + s.nm + s.nmin + j, h, by simp [RecShape.arity]; omega,
          Option.some.inj (hb.symm.trans hbodyAt), ?_⟩
        rw [extract_at (xs := input) (start := s.np + s.nm + s.nmin) (stop := s.arity) enough
          (by simp [RecShape.arity]; dsimp [j] at jb; omega)] at ha
        exact ha

theorem selects_subst {n : Nat} {input bs : Array Ix.Expr} {out : List Ix.Expr}
    (h : List.Forall₂ (Selects n input) bs.toList out) (params : Array Ix.Name) (us : Array Ix.Level) :
    bs.map (Ix.Compile.Canon.substLevels params us) = bs := by
  have eq : bs.map (Ix.Compile.Canon.substLevels params us) = bs.map id := by
    apply Array.map_congr_left
    intro b hb
    obtain ⟨_, _, i, hash, _, rfl, _⟩ := Ix.Cert.ReaderUnits.forall₂_mem_right
      (CliqueRowsCoverage.forall₂_swap h) b (Array.mem_toList_iff.mpr hb)
    unfold Ix.Compile.Canon.substLevels; split <;> rfl
  exact eq.trans (Array.map_id bs)

theorem selects_read {n : Nat} {input : Array Ix.Expr} {bs out : List Ix.Expr}
    {ks args : List (Ix.Kernel.Expr md)}
    (selected : List.Forall₂ (Selects n input) bs out)
    (read : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) bs ks)
    (inputRead : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) input.toList args)
    (enough : n ≤ args.length) (closed : ∀ a ∈ args, a.looseBVarsBounded 0 = true) :
    List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) out
      (ks.map (·.instantiateList (args.take n).reverse)) := by
  induction selected generalizing ks with
  | nil => cases read; exact .nil
  | @cons b a bs out head rest ih =>
    cases read with
    | cons hb ht =>
      obtain ⟨i, hash, bound, rfl, found⟩ := head
      cases hb
      obtain ⟨arg, atArg, related⟩ := SourceConstructorPositions.forall₂_getElem? inputRead
        (i := i) (by simpa only [Array.getElem?_toList] using found)
      have atTake : (args.take n)[i]? = some arg := by rwa [List.getElem?_take_of_lt bound]
      have eq := instantiate_bvar_lookup (n := n) (by simp [Nat.min_eq_left enough]) atTake
        (fun x hx => closed x (List.mem_of_mem_take hx))
      exact .cons (by simpa only [Ix.Kernel.Expr.mkBvar_eq, eq] using related) (ih ht)

theorem forall₂_drop {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (n : Nat) : List.Forall₂ R (xs.drop n) (ys.drop n) := by
  induction n generalizing xs ys with
  | zero => exact h
  | succ n ih => cases h with | nil => exact .nil | cons _ tail => exact ih tail

theorem closed_spine (f : Ix.Kernel.Expr md) (args : List (Ix.Kernel.Expr md))
    (h : (f.mkAppN args).looseBVarsBounded 0 = true) :
    f.looseBVarsBounded 0 = true ∧ ∀ a ∈ args, a.looseBVarsBounded 0 = true := by
  induction args generalizing f with
  | nil => exact ⟨h, by simp⟩
  | cons a args ih =>
    obtain ⟨head, tail⟩ := ih (.app f a) h
    have ⟨hf, ha⟩ : f.looseBVarsBounded 0 = true ∧ a.looseBVarsBounded 0 = true := by
      simpa only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] using head
    exact ⟨hf, fun x hx => (List.mem_cons.mp hx).elim (fun eq => eq.symm ▸ ha) (tail x)⟩

theorem apps_append (f : Ix.Kernel.Expr md) (a b : List (Ix.Kernel.Expr md)) :
    f.mkAppN (a ++ b) = (f.mkAppN a).mkAppN b := by
  induction a generalizing f with | nil => rfl | cons x xs ih => exact ih (.app f x)

theorem subst_const_related {params : Array Ix.Name} {us levels ls : Array Ix.Level}
    {n : Ix.Name} {hash : Address} {k : Ix.Kernel.Expr md}
    (read : Rel (keyOf := keyOf) (levelOf := levelOf)
      (Ix.Compile.Canon.substLevels params us (.const n levels hash)) k)
    (actual : (if params.isEmpty || us.isEmpty then levels else levels.map (Ix.Compile.Canon.substLevel params us)) = ls) :
    Rel (keyOf := keyOf) (levelOf := levelOf) (Ix.Expr.mkConst n ls) k := by
  unfold Ix.Compile.Canon.substLevels at read
  split at read <;> rename_i skip
  all_goals
    simp only [skip, ↓reduceIte] at actual
    subst ls
    cases read with | const _ _ _ names universes => exact .const _ _ _ names universes

open Ix.Compile.Pass Ix.Compile.Pass.Opt in
/-- The real closed recursor pass reduces its actual raw image-application
reading to its actual output reading. The real build/source/image/matcher
and reader successes are retained; no image law or conversion is assumed.
This raw Red is ungraded: it is NOT a statement about annotated subjects,
under-binder occurrences, fallback development or value preservation. -/
theorem o6_rec_raw_reader_red (env : Ix.Kernel.Env md) (depth : Nat)
    {opt : OptEnv} {o : Occ} {output : Ix.Expr} {r : Ix.Name} {block : OptBlock} {s : RecShape}
    {inp : ViewInput} {all : Array Ix.Name} {view : BlockView} {rv : Ix.RecursorVal}
    {img : Ix.Compile.Image.Image}
    (pass : O6.apply opt o = some output) (kind : classify o.head = some (.kRec, r))
    (blockLookup : opt.blockOf o.head = some block) (shapeLookup : block.shapes.get? r = some s)
    (built : buildView inp all = .ok view) (source : inp.const? r = some (.recInfo rv))
    (generated : view.image inp r = .ok img)
    (recognized : readShape r img.levelParams rv.numParams rv.numMotives rv.numMinors rv.numIndices
      img.value (ImageShape.viewRecInfo view) = some s)
    (universeArity : o.us.size = img.levelParams.size)
    {baseReader outReader : Ix.Kernel.Reader.MemberReader md} {baseWire outWire : Ixon.Expr}
    {baseK outputK : Ix.Kernel.Expr md}
    (_baseRead : baseReader.read baseWire = .ok baseK) (_outRead : outReader.read outWire = .ok outputK)
    (baseRelated : Rel (keyOf := keyOf) (levelOf := levelOf)
      (Ix.Compile.Canon.mkAppN (Ix.Compile.Canon.substLevels img.levelParams o.us img.value) o.args) baseK)
    (outRelated : Rel (keyOf := keyOf) (levelOf := levelOf) output outputK)
    (closed : baseK.looseBVarsBounded 0 = true) : Ix.Kernel.Rules.Red env depth baseK outputK := by
  obtain ⟨ls, ms, mins, selected, enough, levelsRun, pickM, pickN, outputEq⟩ :=
    o6_rec_output pass kind blockLookup shapeLookup
  obtain ⟨_, _, _, body, bs, iv, hash, _, _, _, _, _, _, _, data, _⟩ :=
    ImageShape.production_origin built source generated recognized
  have params : s.levelParams = img.levelParams := (ImageShape.readShape_result recognized).2.1
  have picked := data_picks data selected enough pickM pickN
  have noLevels := selects_subst picked img.levelParams o.us
  have readBase : Rel (keyOf := keyOf) (levelOf := levelOf)
      (o.args.toList.foldl Ix.Expr.mkApp (Ix.Compile.Canon.substLevels img.levelParams o.us img.value)) baseK := by
    simpa only [Ix.Compile.Canon.mkAppN, Array.foldl_toList] using baseRelated
  obtain ⟨imageK, argsK, imageRel, argsRel, baseEq⟩ := related_apps_inv o.args.toList readBase
  have closedArgs := (closed_spine imageK argsK (baseEq ▸ closed)).2
  have fit : s.arity ≤ argsK.length := by
    have sizes := CliqueRowsCoverage.forall₂_lengths argsRel
    simp only [Array.length_toList] at sizes; omega
  obtain ⟨bodyK, chain, bodyRel⟩ := related_stripLams imageRel (strip_subst img.levelParams o.us data.1)
  obtain ⟨headK, bodyArgsK, headRel, bodyArgsRel, bodyEq⟩ := related_getApps bodyRel
  simp only [app_spine_subst, data.2.1, noLevels] at headRel bodyArgsRel
  have instantiatedLevels :
      (if img.levelParams.isEmpty || o.us.isEmpty then s.ixLevels
        else s.ixLevels.map (Ix.Compile.Canon.substLevel img.levelParams o.us)) = ls := by
    rw [← params]
    exact o5_subst_levels (by rwa [params]) levelsRun
  have headOut := subst_const_related headRel instantiatedLevels
  have argumentsOut := selects_read picked bodyArgsRel argsRel fit closedArgs
  have more : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf))
      (o.args.extract s.arity o.args.size).toList (argsK.drop s.arity) := by
    have extraEq : (o.args.extract s.arity o.args.size).toList = o.args.toList.drop s.arity := by
      rw [Array.toList_extract, List.extract_eq_take_drop]
      have len : (o.args.toList.drop s.arity).length = o.args.size - s.arity := by simp
      rw [← len, List.take_length]
    rw [extraEq]
    exact forall₂_drop argsRel s.arity
  have converted : Rel (keyOf := keyOf) (levelOf := levelOf) output
      (headK.mkAppN (bodyArgsK.map (·.instantiateList (argsK.take s.arity).reverse) ++ argsK.drop s.arity)) := by
    rw [outputEq]
    simpa only [Ix.Compile.Canon.mkAppN, ← Array.foldl_toList, Array.toList_append] using
      related_apps headOut (Loop.forall₂_append argumentsOut more)
  have outputSame := related_unique converted outRelated
  have fixedHead : headK.instantiateList (argsK.take s.arity).reverse = headK := by
    cases headOut; simp only [Ix.Kernel.Expr.instantiateList]
  have beta := chain.beta (env := env) (d := depth) (argsK.take s.arity) (by simp [Nat.min_eq_left fit])
  have expanded := red_spine beta (argsK.drop s.arity)
  simpa only [baseEq, bodyEq, instantiate_apps, fixedHead, ← apps_append,
    List.take_append_drop, outputSame] using expanded

end Ix.CompileCert.O6RecRead
