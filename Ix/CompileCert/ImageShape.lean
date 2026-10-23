import Ix.Compile.Pass.Opt.Engine
import Ix.CompileCert.Loop
import Ix.CompileCert.ImageOrigin

/-! # What the production image-shape recognizer actually checked

Successful Option/range loops retain exact argument positions and selectors.
Safe optional lookups eliminate every default-index ambiguity, while cached
Expr hashes remain existential witnesses. The permutation corollary and
production-view adapter use the same successful recognizer result. No image
recognition completeness, development law or recursor simulation is claimed.
-/

namespace Ix.CompileCert.ImageShape

open Ix (Name Expr RecursorVal Level)
open Ix.Compile.Pass.Opt
open Ix.Compile.Canon (getAppFnArgs)

theorem bind_some {α β : Type} {x : Option α} {f : α → Option β} {y : β}
    (h : (x >>= f) = some y) : ∃ a, x = some a ∧ f a = some y := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem range_inv {σ : Type} {N : Nat} {body : Nat → σ → Option (ForInStep σ)}
    (I : Nat → σ → Prop)
    (step : ∀ i, i < N → ∀ s, I i s → ∀ r, body i s = some r →
      ∃ t, r = .yield t ∧ I (i + 1) t)
    {s out : σ} (start : I 0 s) (run : forIn [:N] s body = some out) : I N out := by
  have walk : ∀ n k, k + n ≤ N → ∀ s out, I k s →
      forIn (List.range' k n) s body = some out → I (k + n) out := by
    intro n
    induction n with
    | zero =>
      intro k hk s out hs h
      have eq : s = out := by simpa using h
      subst out; simpa using hs
    | succ n ih =>
      intro k hk s out hs h
      rw [List.range'_succ, List.forIn_cons] at h
      obtain ⟨r, hr, h⟩ := bind_some h
      obtain ⟨t, rfl, ht⟩ := step k (by omega) s hs r hr
      have tail := ih (k + 1) (by omega) t out ht h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at run
  simpa using walk N 0 (by omega) s out start (by simpa [Std.Legacy.Range.size] using run)

def position (arity : Nat) : Expr → Option Nat
  | .bvar k _ => if k < arity then some (arity - 1 - k) else none
  | _ => none

theorem position_shape {arity p : Nat} {e : Expr} (h : position arity e = some p) :
    p < arity ∧ ∃ hash, e = .bvar (arity - 1 - p) hash := by
  cases e with
  | bvar k hash =>
    by_cases hk : k < arity
    · have eq : arity - 1 - k = p := by simpa [position, hk] using h
      refine ⟨by omega, hash, ?_⟩
      congr 1; omega
    · simp [position, hk] at h
  | _ => cases h

def Indexed {α : Type} (R : Nat → α → Prop) (xs : Array α) : Prop :=
  ∀ i x, xs[i]? = some x → R i x

theorem indexed_push {α : Type} {R : Nat → α → Prop} {xs : Array α} {x : α}
    (h : Indexed R xs) (hx : R xs.size x) : Indexed R (xs.push x) := by
  intro i y hy
  rw [Array.getElem?_push] at hy
  split at hy
  · rename_i hi; cases Option.some.inj hy; exact hi ▸ hx
  · exact h i y hy

theorem nodup_push {α : Type} [BEq α] [LawfulBEq α] {xs : Array α} {x : α}
    (h : xs.toList.Nodup) (fresh : xs.contains x = false) : (xs.push x).toList.Nodup := by
  rw [Array.toList_push, List.nodup_append]
  refine ⟨h, by simp, ?_⟩
  intro a ha b hb eq
  have hb : b = x := List.mem_singleton.mp hb
  subst b; subst a
  have hc := Array.contains_eq_true_of_mem (Array.mem_toList_iff.mp ha)
  rw [fresh] at hc; cases hc

def Motives (arity np nm : Nat) (args : Array Expr) (count : Nat) (xs : Array Nat) : Prop :=
  xs.size = count ∧ xs.toList.Nodup ∧
    Indexed (fun i n => n < nm ∧ position arity args[np + i]! = some (np + n)) xs

def Minors (arity np nm nmin offset : Nat) (args : Array Expr) (count : Nat)
    (xs : Array (Option Nat) × Array Expr) : Prop :=
  xs.1.size = count ∧ xs.2.size = count ∧ (xs.1.toList.filterMap id).Nodup ∧
    Indexed (fun i n => ∀ j, n = some j → j < nmin ∧
      position arity args[offset + i]! = some (np + nm + j)) xs.1 ∧
    Indexed (fun i e => e = args[offset + i]!) xs.2

theorem motive_push {arity np nm count : Nat} {args : Array Expr} {xs : Array Nat} {p : Nat}
    (h : Motives arity np nm args count xs) (lo : np ≤ p) (hi : p < np + nm)
    (fresh : xs.contains (p - np) = false)
    (pos : position arity args[np + count]! = some p) :
    Motives arity np nm args (count + 1) (xs.push (p - np)) := by
  refine ⟨by simp [h.1], nodup_push h.2.1 fresh, indexed_push h.2.2 ?_⟩
  refine ⟨by omega, ?_⟩
  have eq : np + (p - np) = p := by omega
  simpa only [h.1, eq] using pos

theorem minor_push {arity np nm nmin offset count : Nat} {args : Array Expr}
    {xs : Array (Option Nat) × Array Expr} {v : Option Nat}
    (h : Minors arity np nm nmin offset args count xs)
    (valid : ∀ j, v = some j → j < nmin ∧ position arity args[offset + count]! = some (np + nm + j))
    (fresh : ∀ j, v = some j → xs.1.contains (some j) = false) :
    Minors arity np nm nmin offset args (count + 1)
      (xs.1.push v, xs.2.push args[offset + count]!) := by
  refine ⟨by simp [h.1], by simp [h.2.1], ?_,
    indexed_push h.2.2.2.1 (by simpa only [h.1] using valid),
    indexed_push h.2.2.2.2 (by rw [h.2.1])⟩
  cases v with
  | none => simpa [Array.toList_push] using h.2.2.1
  | some j =>
    have hn : j ∉ xs.1.toList.filterMap id := by
      intro hj
      obtain ⟨o, ho, eq⟩ := List.mem_filterMap.mp hj
      change o = some j at eq
      subst o
      have hc := Array.contains_eq_true_of_mem (Array.mem_toList_iff.mp ho)
      rw [fresh j rfl] at hc; cases hc
    simp only [Array.toList_push, List.filterMap_append, List.filterMap_cons,
      id_eq, List.filterMap_nil]
    refine List.nodup_append.mpr ⟨h.2.2.1, by simp, ?_⟩
    intro a ha b hb eq
    have hb : b = j := List.mem_singleton.mp hb
    subst b; subst a; exact hn ha

/-- Exact structural facts of one successful recognizer run. Cached hashes
are retained as witnesses; no reconstructed-expression equality is claimed. -/
def Data (value : Expr) (ixRecInfo : Name → Option RecursorVal) (s : RecShape)
    (body : Expr) (args : Array Expr) (iv : RecursorVal) (hash : Address) : Prop :=
    stripLams s.arity value = some body ∧
    getAppFnArgs body = (.const s.ixRec s.ixLevels hash, args) ∧ ixRecInfo s.ixRec = some iv ∧
    iv.numParams = s.np ∧ iv.numIndices = s.ni ∧
    args.size = s.np + iv.numMotives + iv.numMinors + s.ni + 1 ∧
    (∀ i, i < s.np → position s.arity args[i]! = some i) ∧
    (∀ i, i < s.ni + 1 → position s.arity args[s.np + iv.numMotives + iv.numMinors + i]! =
      some (s.np + s.nm + s.nmin + i)) ∧
    Motives s.arity s.np s.nm args iv.numMotives s.motiveSrc ∧
    Minors s.arity s.np s.nm s.nmin (s.np + iv.numMotives) args iv.numMinors (s.minorSrc, s.minorTerms)

def Result (value : Expr) (ixRecInfo : Name → Option RecursorVal) (s : RecShape) : Prop :=
  ∃ body args iv hash, Data value ixRecInfo s body args iv hash

theorem readShape_result {r : Name} {lps : Array Name} {np nm nmin ni : Nat}
    {value : Expr} {ixRecInfo : Name → Option RecursorVal} {s : RecShape}
    (h : readShape r lps np nm nmin ni value ixRecInfo = some s) :
    s.leanRec = r ∧ s.levelParams = lps ∧ s.np = np ∧ s.nm = nm ∧ s.nmin = nmin ∧ s.ni = ni ∧
      Result value ixRecInfo s := by
  unfold readShape at h
  obtain ⟨body, hb, h⟩ := bind_some h
  cases happ : getAppFnArgs body with
  | mk head args =>
    rw [happ] at h
    cases head with
    | const target levels hash =>
      obtain ⟨iv, hiv, h⟩ := bind_some h
      dsimp only at h
      split at h
      · cases h
      · rename_i badCounts
        have counts : iv.numParams = np ∧ iv.numIndices = ni := by
          simpa [Bool.or_eq_true] using badCounts
        split at h
        · cases h
        · rename_i badSize
          have size : args.size = np + iv.numMotives + iv.numMinors + ni + 1 := by simpa using badSize
          obtain ⟨_, hparams, h⟩ := bind_some h
          obtain ⟨_, htail, h⟩ := bind_some h
          obtain ⟨motives, hmotives, h⟩ := bind_some h
          obtain ⟨minors, hminors, h⟩ := bind_some h
          have eq : s = ⟨r, lps, np, nm, nmin, ni, target, levels, motives,
              minors.1, minors.2⟩ := (Option.some.inj h).symm
          subst s
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, body, args, iv, hash, hb, happ, hiv,
            counts.1, counts.2, size, ?_, ?_, ?_, ?_⟩
          · apply range_inv (fun k (_ : PUnit) => ∀ i, i < k → position (np + nm + nmin + ni + 1) args[i]! = some i)
              (run := hparams) (start := by simp)
            intro k hk u hu result hr
            change (if position (np + nm + nmin + ni + 1) args[k]! != some k then none
              else some (.yield PUnit.unit)) = some result at hr
            by_cases good : position (np + nm + nmin + ni + 1) args[k]! = some k
            · have eq : .yield PUnit.unit = result := by simpa [good] using hr
              subst result
              refine ⟨PUnit.unit, rfl, ?_⟩
              intro i hi
              by_cases eq : i = k
              · exact eq ▸ good
              · exact hu i (by omega)
            · simp [good] at hr
          · apply range_inv (fun k (_ : PUnit) => ∀ i, i < k →
                position (np + nm + nmin + ni + 1) args[np + iv.numMotives + iv.numMinors + i]! = some (np + nm + nmin + i))
              (run := htail) (start := by simp)
            intro k hk u hu result hr
            change (if position (np + nm + nmin + ni + 1) args[np + iv.numMotives + iv.numMinors + k]! !=
              some (np + nm + nmin + k) then none else some (.yield PUnit.unit)) = some result at hr
            by_cases good : position (np + nm + nmin + ni + 1) args[np + iv.numMotives + iv.numMinors + k]! =
                some (np + nm + nmin + k)
            · have eq : .yield PUnit.unit = result := by simpa [good] using hr
              subst result
              refine ⟨PUnit.unit, rfl, ?_⟩
              intro i hi
              by_cases eq : i = k
              · exact eq ▸ good
              · exact hu i (by omega)
            · simp [good] at hr
          · apply range_inv (Motives (np + nm + nmin + ni + 1) np nm args)
              (run := hmotives) (start := by simp [Motives, Indexed])
            intro k hk xs hx result hr
            obtain ⟨p, hp, hr⟩ := bind_some hr
            split at hr
            · cases hr
            · rename_i good
              have good : np ≤ p ∧ p < np + nm ∧ xs.contains (p - np) = false := by
                simpa [Bool.or_eq_true, or_assoc] using good
              have eq : .yield (xs.push (p - np)) = result := Option.some.inj hr
              subst result
              exact ⟨_, rfl, motive_push hx good.1 good.2.1 good.2.2 hp⟩
          · apply range_inv (Minors (np + nm + nmin + ni + 1) np nm nmin (np + iv.numMotives) args)
              (run := hminors) (start := by simp [Minors, Indexed])
            intro k hk xs hx result hr
            change (match position (np + nm + nmin + ni + 1) args[np + iv.numMotives + k]! with
              | some p => if (decide (p < np + nm) || decide (p ≥ np + nm + nmin) ||
                  xs.1.contains (some (p - np - nm))) = true then none
                else some (.yield (xs.1.push (some (p - np - nm)), xs.2.push args[np + iv.numMotives + k]!))
              | none => some (.yield (xs.1.push none, xs.2.push args[np + iv.numMotives + k]!))) = some result at hr
            cases hp : position (np + nm + nmin + ni + 1) args[np + iv.numMotives + k]! with
            | none =>
              rw [hp] at hr
              have eq := Option.some.inj hr
              subst result
              exact ⟨_, rfl, minor_push hx (by simp) (by simp)⟩
            | some p =>
              rw [hp] at hr
              by_cases bad : (decide (p < np + nm) || decide (p ≥ np + nm + nmin) ||
                  xs.1.contains (some (p - np - nm))) = true
              · simp only [bad, ↓reduceIte] at hr; cases hr
              · simp only [bad] at hr
                have good : np + nm ≤ p ∧ p < np + nm + nmin ∧ xs.1.contains (some (p - np - nm)) = false := by
                  simpa [Bool.or_eq_true, or_assoc] using bad
                have eq := Option.some.inj hr
                subst result
                refine ⟨_, rfl, minor_push hx ?_ ?_⟩
                · intro j hj; cases Option.some.inj hj
                  refine ⟨by omega, ?_⟩
                  have eq : np + nm + (p - np - nm) = p := by omega
                  simpa only [eq] using hp
                · intro j hj; cases Option.some.inj hj; exact good.2.2
    | _ => cases h

/-- Successful permutation recognition has exactly the source motive/minor
ranges. The premise is the same actual recognizer result as the structure. -/
theorem readShape_permutations {r : Name} {lps : Array Name} {np nm nmin ni : Nat}
    {value : Expr} {ixRecInfo : Name → Option RecursorVal} {s : RecShape}
    (h : readShape r lps np nm nmin ni value ixRecInfo = some s) (permuted : s.isPerm = true) :
    s.motiveSrc.toList.Perm (List.range nm) ∧
      (s.minorSrc.toList.filterMap id).Perm (List.range nmin) := by
  obtain ⟨_, _, _, hnm, hnmin, _, _, args, iv, _, _, _, _, _, _, _, _, _, motives, minors⟩ := readShape_result h
  simp only [RecShape.isPerm, Bool.and_eq_true] at permuted
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, coverM⟩, coverN⟩ := permuted
  constructor
  · rw [← hnm]
    apply (List.perm_ext_iff_of_nodup motives.2.1 List.nodup_range).mpr
    intro n; constructor
    · intro hn
      obtain ⟨i, hi⟩ := Array.getElem?_of_mem (Array.mem_toList_iff.mp hn)
      exact List.mem_range.mpr (motives.2.2 i n hi).1
    · intro hn
      exact Array.mem_toList_iff.mpr (Array.mem_of_contains_eq_true (List.all_eq_true.mp coverM n hn))
  · rw [← hnmin]
    apply (List.perm_ext_iff_of_nodup minors.2.2.1 List.nodup_range).mpr
    intro n; constructor
    · intro hn
      obtain ⟨o, ho, eq⟩ := List.mem_filterMap.mp hn
      change o = some n at eq; subst o
      obtain ⟨i, hi⟩ := Array.getElem?_of_mem (Array.mem_toList_iff.mp ho)
      exact List.mem_range.mpr (minors.2.2.2.1 i (some n) hi n rfl).1
    · intro hn
      exact List.mem_filterMap.mpr ⟨some n,
        Array.mem_toList_iff.mpr (Array.mem_of_contains_eq_true (List.all_eq_true.mp coverN n hn)), rfl⟩

theorem position_read {arity i p : Nat} {args : Array Expr} (bound : i < args.size)
    (h : position arity args[i]! = some p) :
    ∃ hash, args[i]? = some (.bvar (arity - 1 - p) hash) := by
  obtain ⟨_, hash, eq⟩ := position_shape h
  exact ⟨hash, (Array.getElem?_eq_some_getElem! args i bound).trans (congrArg some eq)⟩

/-- Ordinary optional lookups make all bounds explicit, including the actual
minor-term slice. Every bvar hash is the original one, not reconstructed. -/
def Reads (s : RecShape) (args : Array Expr) (iv : RecursorVal) : Prop :=
  (∀ i, i < s.np → ∃ hash, args[i]? = some (.bvar (s.arity - 1 - i) hash)) ∧
  (∀ i, i < s.ni + 1 → ∃ hash, args[s.np + iv.numMotives + iv.numMinors + i]? =
    some (.bvar (s.arity - 1 - (s.np + s.nm + s.nmin + i)) hash)) ∧
  (∀ i n, s.motiveSrc[i]? = some n → n < s.nm ∧ ∃ hash, args[s.np + i]? =
    some (.bvar (s.arity - 1 - (s.np + n)) hash)) ∧
  (∀ i n, s.minorSrc[i]? = some (some n) → n < s.nmin ∧ ∃ hash, args[s.np + iv.numMotives + i]? =
    some (.bvar (s.arity - 1 - (s.np + s.nm + n)) hash)) ∧
  ∀ i e, s.minorTerms[i]? = some e → args[s.np + iv.numMotives + i]? = some e

theorem Data.reads {value : Expr} {ixRecInfo : Name → Option RecursorVal} {s : RecShape}
    {body : Expr} {args : Array Expr} {iv : RecursorVal} {hash : Address}
    (h : Data value ixRecInfo s body args iv hash) : Reads s args iv := by
  obtain ⟨_, _, _, _, _, size, params, tail, motives, minors⟩ := h
  refine ⟨fun i hi => position_read (by omega) (params i hi),
    fun i hi => position_read (by omega) (tail i hi), ?_, ?_, ?_⟩
  · intro i n hi
    have bound := (Array.getElem?_eq_some_iff.mp hi).1
    obtain ⟨hn, pos⟩ := motives.2.2 i n hi
    exact ⟨hn, position_read (by have := motives.1; omega) pos⟩
  · intro i n hi
    have bound := (Array.getElem?_eq_some_iff.mp hi).1
    obtain ⟨hn, pos⟩ := minors.2.2.2.1 i (some n) hi n rfl
    exact ⟨hn, position_read (by have count : s.minorSrc.size = iv.numMinors := minors.1; omega) pos⟩
  · intro i e hi
    have bound := (Array.getElem?_eq_some_iff.mp hi).1
    have same := minors.2.2.2.2 i e hi
    exact (Array.getElem?_eq_some_getElem! args _
      (by have count : s.minorTerms.size = iv.numMinors := minors.2.1; omega)).trans (congrArg some same.symm)

/-- Data and safe indexing use the SAME body/argument witnesses recovered
from this successful run. No default array access survives the interface. -/
theorem readShape_reads {r : Name} {lps : Array Name} {np nm nmin ni : Nat}
    {value : Expr} {ixRecInfo : Name → Option RecursorVal} {s : RecShape}
    (h : readShape r lps np nm nmin ni value ixRecInfo = some s) :
    ∃ body args iv hash, Data value ixRecInfo s body args iv hash ∧ Reads s args iv := by
  obtain ⟨_, _, _, _, _, _, body, args, iv, hash, data⟩ := readShape_result h
  exact ⟨body, args, iv, hash, data, data.reads⟩

/-- The recursor lookup used inside optBlockOf, with its actual view table. -/
def viewRecInfo (view : Ix.Compile.Pass.BlockView) (n : Name) : Option RecursorVal :=
  match view.canonConsts.get? n with
  | some (.recInfo rv) => some rv
  | _ => none

/-- Build, source lookup, image and matcher are their actual successful calls.
This retains the complete local provenance together; extracting those calls
from a driver memo/table lookup remains the later publication obligation. -/
theorem production_origin {inp : Ix.Compile.Pass.ViewInput} {all : Array Name}
    {view : Ix.Compile.Pass.BlockView} {r : Name} {rv : RecursorVal}
    {img : Ix.Compile.Image.Image} {s : RecShape}
    (built : Ix.Compile.Pass.buildView inp all = .ok view)
    (source : inp.const? r = some (.recInfo rv)) (generated : view.image inp r = .ok img)
    (recognized : readShape r img.levelParams rv.numParams rv.numMotives rv.numMinors rv.numIndices
      img.value (viewRecInfo view) = some s) :
    ∃ (canon : Ix.Compile.Canon.BlockCanon) (raw : Ix.Compile.Image.Image) (p : ImageOrigin.Prefix)
      (body : Expr) (args : Array Expr) (iv : RecursorVal) (hash : Address),
      Ix.Compile.Pass.canonBlockCompiled inp.env (fun n => (inp.addr? n).isSome) all = .ok canon ∧
      Ix.Compile.Image.ImageSpec.ofBlock Ix.Compile.Pass.viewNaming inp.const? canon = .ok view.spec ∧
      inp.const? r = some (.recInfo rv) ∧
      Ix.Compile.Image.imageOf {} (view.const? inp) view.spec r = .ok raw ∧
      p.Ran {} (view.const? inp) view.spec r ∧ p.Result view.spec r raw ∧
      img.value = Ix.Compile.Canon.canonicalizeConstNames view.back raw.value ∧
      Data img.value (viewRecInfo view) s body args iv hash ∧ Reads s args iv := by
  obtain ⟨canon, hc, _, hs, _, _⟩ := ImageOrigin.buildView_origin built
  obtain ⟨raw, p, hg, ran, result, eq⟩ := ImageOrigin.view_image_origin generated
  obtain ⟨body, args, iv, hash, data, reads⟩ := readShape_reads recognized
  exact ⟨canon, raw, p, body, args, iv, hash, hc, hs, source, hg, ran, result,
    congrArg Ix.Compile.Image.Image.value eq, data, reads⟩

end Ix.CompileCert.ImageShape
