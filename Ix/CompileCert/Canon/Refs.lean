import Ix.CompileCert.Canon.Cache
import Ix.Compile.Canon.Graph
import Batteries.Tactic.OpenPrivate

/-!
# M7 L1, the references of an expression

`Ix.Compile.Canon.refsExpr e acc` adds to `acc` the constants and projection structures `e`
names, visiting each distinct subterm once **by its cached hash**. `refsExpr_sound`: everything
it adds occurs in `e`. `refsExpr_complete`: when no two distinct subterms of `e` share a hash
(`HashCons e`: the cached hashes are collision-free on `e`, as they are for terms built by the
hashing constructors short of a Blake3 collision), everything that occurs in `e` is added. So
on such input the reference graph of `Graph.lean` is the graph of occurrence.
-/

open private Ix.Compile.Canon.refsExpr.go from Ix.Compile.Canon.Graph

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Expr)

instance lawfulBEq_address : LawfulBEq Address where
  rfl := addr_beq_iff.2 rfl
  eq_of_beq h := addr_beq_iff.1 h

instance lawfulHashable_address : LawfulHashable Address where
  hash_eq a b h := by rw [addr_beq_iff.1 h]

/-- `n` occurs in `e`, as a constant or as a projection's structure. -/
inductive Occ : Expr → Name → Prop
  | const (n : Name) (us : Array Ix.Level) (h : Address) : Occ (.const n us h) n
  | proj (n : Name) (i : Nat) (s : Expr) (h : Address) : Occ (.proj n i s h) n
  | projS {n : Name} {i : Nat} {s : Expr} {h : Address} {m : Name} : Occ s m → Occ (.proj n i s h) m
  | appF {f a : Expr} {h : Address} {m : Name} : Occ f m → Occ (.app f a h) m
  | appA {f a : Expr} {h : Address} {m : Name} : Occ a m → Occ (.app f a h) m
  | lamT {n : Name} {t b : Expr} {bi : Lean.BinderInfo} {h : Address} {m : Name} :
      Occ t m → Occ (.lam n t b bi h) m
  | lamB {n : Name} {t b : Expr} {bi : Lean.BinderInfo} {h : Address} {m : Name} :
      Occ b m → Occ (.lam n t b bi h) m
  | forallT {n : Name} {t b : Expr} {bi : Lean.BinderInfo} {h : Address} {m : Name} :
      Occ t m → Occ (.forallE n t b bi h) m
  | forallB {n : Name} {t b : Expr} {bi : Lean.BinderInfo} {h : Address} {m : Name} :
      Occ b m → Occ (.forallE n t b bi h) m
  | letT {n : Name} {t v b : Expr} {nd : Bool} {h : Address} {m : Name} :
      Occ t m → Occ (.letE n t v b nd h) m
  | letV {n : Name} {t v b : Expr} {nd : Bool} {h : Address} {m : Name} :
      Occ v m → Occ (.letE n t v b nd h) m
  | letB {n : Name} {t v b : Expr} {nd : Bool} {h : Address} {m : Name} :
      Occ b m → Occ (.letE n t v b nd h) m
  | mdata {d : Array (Name × Ix.DataValue)} {x : Expr} {h : Address} {m : Name} :
      Occ x m → Occ (.mdata d x h) m

/-- `s` is a subterm of `e`. -/
inductive Sub : Expr → Expr → Prop
  | refl (e : Expr) : Sub e e
  | appF {s f a : Expr} {h : Address} : Sub s f → Sub s (.app f a h)
  | appA {s f a : Expr} {h : Address} : Sub s a → Sub s (.app f a h)
  | lamT {s t b : Expr} {n : Name} {bi : Lean.BinderInfo} {h : Address} : Sub s t → Sub s (.lam n t b bi h)
  | lamB {s t b : Expr} {n : Name} {bi : Lean.BinderInfo} {h : Address} : Sub s b → Sub s (.lam n t b bi h)
  | forallT {s t b : Expr} {n : Name} {bi : Lean.BinderInfo} {h : Address} :
      Sub s t → Sub s (.forallE n t b bi h)
  | forallB {s t b : Expr} {n : Name} {bi : Lean.BinderInfo} {h : Address} :
      Sub s b → Sub s (.forallE n t b bi h)
  | letT {s t v b : Expr} {n : Name} {nd : Bool} {h : Address} : Sub s t → Sub s (.letE n t v b nd h)
  | letV {s t v b : Expr} {n : Name} {nd : Bool} {h : Address} : Sub s v → Sub s (.letE n t v b nd h)
  | letB {s t v b : Expr} {n : Name} {nd : Bool} {h : Address} : Sub s b → Sub s (.letE n t v b nd h)
  | mdata {s x : Expr} {d : Array (Name × Ix.DataValue)} {h : Address} : Sub s x → Sub s (.mdata d x h)
  | projS {s x : Expr} {n : Name} {i : Nat} {h : Address} : Sub s x → Sub s (.proj n i x h)

theorem Sub.trans {s c e : Expr} (h₁ : Sub s c) (h₂ : Sub c e) : Sub s e := by
  induction h₂ with
  | refl => exact h₁
  | appF _ ih => exact .appF ih
  | appA _ ih => exact .appA ih
  | lamT _ ih => exact .lamT ih
  | lamB _ ih => exact .lamB ih
  | forallT _ ih => exact .forallT ih
  | forallB _ ih => exact .forallB ih
  | letT _ ih => exact .letT ih
  | letV _ ih => exact .letV ih
  | letB _ ih => exact .letB ih
  | mdata _ ih => exact .mdata ih
  | projS _ ih => exact .projS ih

theorem Sub.size {s e : Expr} (h : Sub s e) : exprSize s ≤ exprSize e := by
  induction h <;> (try simp only [exprSize]) <;> omega

/-- No two distinct subterms of `e` share a cached hash. -/
def HashCons (root : Expr) : Prop :=
  ∀ s t, Sub s root → Sub t root → s.getHash = t.getHash → s = t

/-! ## Soundness -/

theorem go_sound : ∀ (e : Expr) (st : Std.HashSet Name × Std.HashSet Address) (n : Name),
    (Ix.Compile.Canon.refsExpr.go e st).1.contains n = true → st.1.contains n = true ∨ ∃ m, Occ e m ∧ (m == n) = true := by
  intro e
  induction e with
  | const nm us h =>
    intro st n hn
    unfold Ix.Compile.Canon.refsExpr.go at hn
    split at hn
    · exact .inl hn
    · simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hn
      rcases hn with hn | hn
      · exact .inr ⟨nm, .const nm us h, hn⟩
      · exact .inl hn
  | app f a h ihf iha =>
    intro st n hn
    unfold Ix.Compile.Canon.refsExpr.go at hn
    split at hn
    · exact .inl hn
    · rcases iha _ n hn with hn | ⟨m, hm, e⟩
      · rcases ihf _ n hn with hn | ⟨m, hm, e⟩
        · exact .inl hn
        · exact .inr ⟨m, .appF hm, e⟩
      · exact .inr ⟨m, .appA hm, e⟩
  | lam nm t b bi h iht ihb =>
    intro st n hn
    unfold Ix.Compile.Canon.refsExpr.go at hn
    split at hn
    · exact .inl hn
    · rcases ihb _ n hn with hn | ⟨m, hm, e⟩
      · rcases iht _ n hn with hn | ⟨m, hm, e⟩
        · exact .inl hn
        · exact .inr ⟨m, .lamT hm, e⟩
      · exact .inr ⟨m, .lamB hm, e⟩
  | forallE nm t b bi h iht ihb =>
    intro st n hn
    unfold Ix.Compile.Canon.refsExpr.go at hn
    split at hn
    · exact .inl hn
    · rcases ihb _ n hn with hn | ⟨m, hm, e⟩
      · rcases iht _ n hn with hn | ⟨m, hm, e⟩
        · exact .inl hn
        · exact .inr ⟨m, .forallT hm, e⟩
      · exact .inr ⟨m, .forallB hm, e⟩
  | letE nm t v b nd h iht ihv ihb =>
    intro st n hn
    unfold Ix.Compile.Canon.refsExpr.go at hn
    split at hn
    · exact .inl hn
    · rcases ihb _ n hn with hn | ⟨m, hm, e⟩
      · rcases ihv _ n hn with hn | ⟨m, hm, e⟩
        · rcases iht _ n hn with hn | ⟨m, hm, e⟩
          · exact .inl hn
          · exact .inr ⟨m, .letT hm, e⟩
        · exact .inr ⟨m, .letV hm, e⟩
      · exact .inr ⟨m, .letB hm, e⟩
  | proj nm i s h ihs =>
    intro st n hn
    unfold Ix.Compile.Canon.refsExpr.go at hn
    split at hn
    · exact .inl hn
    · simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hn
      rcases hn with hn | hn
      · exact .inr ⟨nm, .proj nm i s h, hn⟩
      · rcases ihs _ n hn with hn | ⟨m, hm, e⟩
        · exact .inl hn
        · exact .inr ⟨m, .projS hm, e⟩
  | mdata d x h ihx =>
    intro st n hn
    unfold Ix.Compile.Canon.refsExpr.go at hn
    split at hn
    · exact .inl hn
    · rcases ihx _ n hn with hn | ⟨m, hm, e⟩
      · exact .inl hn
      · exact .inr ⟨m, .mdata hm, e⟩
  | bvar i h =>
    intro st n hn; unfold Ix.Compile.Canon.refsExpr.go at hn; split at hn <;> exact .inl hn
  | fvar x h =>
    intro st n hn; unfold Ix.Compile.Canon.refsExpr.go at hn; split at hn <;> exact .inl hn
  | mvar x h =>
    intro st n hn; unfold Ix.Compile.Canon.refsExpr.go at hn; split at hn <;> exact .inl hn
  | sort u h =>
    intro st n hn; unfold Ix.Compile.Canon.refsExpr.go at hn; split at hn <;> exact .inl hn
  | lit l h =>
    intro st n hn; unfold Ix.Compile.Canon.refsExpr.go at hn; split at hn <;> exact .inl hn

/-- **Soundness**: `refsExpr e acc` adds only names (`==` to names) occurring in `e`. -/
theorem refsExpr_sound (e : Expr) (acc : Std.HashSet Name) (n : Name)
    (h : (refsExpr e acc).contains n = true) : acc.contains n = true ∨ ∃ m, Occ e m ∧ (m == n) = true :=
  go_sound e (acc, {}) n h

/-! ## Completeness on collision-free input -/

/-- Every name occurring in a subterm with hash `h` is collected. -/
def Done (root : Expr) (names : Std.HashSet Name) (h : Address) : Prop :=
  ∀ t, Sub t root → t.getHash = h → ∀ n, Occ t n → names.contains n = true

/-- Each visited hash is that of a subterm larger than `k` (still being visited), or done. -/
def Pre (root : Expr) (st : Std.HashSet Name × Std.HashSet Address) (k : Nat) : Prop :=
  ∀ h, st.2.contains h = true → (∃ t, Sub t root ∧ t.getHash = h ∧ k < exprSize t) ∨ Done root st.1 h

/-- What a visit keeps, and that every hash it adds is done. -/
def Post (root : Expr) (st r : Std.HashSet Name × Std.HashSet Address) : Prop :=
  (∀ n, st.1.contains n = true → r.1.contains n = true) ∧
  (∀ h, st.2.contains h = true → r.2.contains h = true) ∧
  (∀ h, r.2.contains h = true → st.2.contains h = true ∨ Done root r.1 h)

section complete
variable {root : Expr}

theorem done_mono {s s' : Std.HashSet Name} {h : Address} (hd : Done root s h)
    (hm : ∀ n, s.contains n = true → s'.contains n = true) : Done root s' h :=
  fun t ht hh n ho => hm n (hd t ht hh n ho)

theorem Post.refl' (st : Std.HashSet Name × Std.HashSet Address) : Post root st st :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => .inl h⟩

theorem Post.trans' {st r1 r2 : Std.HashSet Name × Std.HashSet Address} (p1 : Post root st r1)
    (p2 : Post root r1 r2) : Post root st r2 := by
  refine ⟨fun n h => p2.1 n (p1.1 n h), fun h hh => p2.2.1 h (p1.2.1 h hh), fun h hh => ?_⟩
  rcases p2.2.2 h hh with h1 | h1
  · rcases p1.2.2 h h1 with h2 | h2
    · exact .inl h2
    · exact .inr (done_mono h2 p2.1)
  · exact .inr h1

theorem pre_post {st r : Std.HashSet Name × Std.HashSet Address} {k k' : Nat} (hp : Pre root st k)
    (po : Post root st r) (hk : k' ≤ k) : Pre root r k' := by
  intro h hh
  rcases po.2.2 h hh with h1 | h1
  · rcases hp h h1 with ⟨t, ht, e, hlt⟩ | h2
    · exact .inl ⟨t, ht, e, by omega⟩
    · exact .inr (done_mono h2 po.1)
  · exact .inr h1

theorem pre_enter {st : Std.HashSet Name × Std.HashSet Address} {e : Expr} (hp : Pre root st (exprSize e))
    (he : Sub e root) {k : Nat} (hk : k < exprSize e) :
    Pre root (st.1, st.2.insert e.getHash) k := by
  intro h hh
  simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hh
  rcases hh with hh | hh
  · exact .inl ⟨e, he, (beq_iff_eq.1 hh), hk⟩
  · rcases hp h hh with ⟨t, ht, e', hlt⟩ | h2
    · exact .inl ⟨t, ht, e', by omega⟩
    · exact .inr h2

theorem finish' (hc : HashCons root) {e : Expr} (he : Sub e root)
    {st r : Std.HashSet Name × Std.HashSet Address} (po : Post root (st.1, st.2.insert e.getHash) r)
    (hocc : ∀ n, Occ e n → r.1.contains n = true) :
    Post root st r ∧ Done root r.1 e.getHash := by
  have hd : Done root r.1 e.getHash := fun t ht hh n ho => by
    rw [hc t e ht he hh] at ho; exact hocc n ho
  refine ⟨⟨fun n h => po.1 n h, fun h hh => po.2.1 h ?_, fun h hh => ?_⟩, hd⟩
  · simp only [Std.HashSet.contains_insert, Bool.or_eq_true]; exact .inr hh
  · rcases po.2.2 h hh with h1 | h1
    · simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at h1
      rcases h1 with h1 | h1
      · rw [← beq_iff_eq.1 h1]; exact .inr hd
      · exact .inl h1
    · exact .inr h1

theorem skip' (hc : HashCons root) {e : Expr} (he : Sub e root)
    {st : Std.HashSet Name × Std.HashSet Address} (hp : Pre root st (exprSize e))
    (hv : st.2.contains e.getHash = true) : Post root st st ∧ Done root st.1 e.getHash := by
  refine ⟨Post.refl' st, ?_⟩
  rcases hp _ hv with ⟨t, ht, e', hlt⟩ | h
  · rw [hc t e ht he e'] at hlt; omega
  · exact h

/-- **The visit of a subterm collects its names**, on collision-free input. -/
theorem go_spec (hc : HashCons root) : ∀ (e : Expr), Sub e root →
    ∀ st, Pre root st (exprSize e) →
      Post root st (Ix.Compile.Canon.refsExpr.go e st) ∧
        Done root (Ix.Compile.Canon.refsExpr.go e st).1 e.getHash := by
  intro e
  induction e with
  | const nm us h =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · refine finish' hc he ⟨fun n hn => ?_, fun _ hh => hh, fun _ hh => .inl hh⟩ fun n ho => ?_
      · simp only [Std.HashSet.contains_insert, Bool.or_eq_true]; exact .inr hn
      · cases ho
        simp only [Std.HashSet.contains_insert, name_beq_refl, Bool.true_or]
  | app f a h ihf iha =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · have hf : Sub f root := Sub.trans (.appF (.refl f)) he
      have ha : Sub a root := Sub.trans (.appA (.refl a)) he
      have p0f := pre_enter hp he (k := exprSize f) (by simp only [exprSize]; omega)
      have p0a := pre_enter hp he (k := exprSize a) (by simp only [exprSize]; omega)
      obtain ⟨po1, d1⟩ := ihf hf _ p0f
      obtain ⟨po2, d2⟩ := iha ha _ (pre_post p0a po1 (Nat.le_refl _))
      refine finish' hc he (po1.trans' po2) fun n ho => ?_
      cases ho with
      | appF ho => exact po2.1 n (d1 f hf rfl n ho)
      | appA ho => exact d2 a ha rfl n ho
  | lam nm t b bi h iht ihb =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · have ht : Sub t root := Sub.trans (.lamT (.refl t)) he
      have hb : Sub b root := Sub.trans (.lamB (.refl b)) he
      have p0t := pre_enter hp he (k := exprSize t) (by simp only [exprSize]; omega)
      have p0b := pre_enter hp he (k := exprSize b) (by simp only [exprSize]; omega)
      obtain ⟨po1, d1⟩ := iht ht _ p0t
      obtain ⟨po2, d2⟩ := ihb hb _ (pre_post p0b po1 (Nat.le_refl _))
      refine finish' hc he (po1.trans' po2) fun n ho => ?_
      cases ho with
      | lamT ho => exact po2.1 n (d1 t ht rfl n ho)
      | lamB ho => exact d2 b hb rfl n ho
  | forallE nm t b bi h iht ihb =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · have ht : Sub t root := Sub.trans (.forallT (.refl t)) he
      have hb : Sub b root := Sub.trans (.forallB (.refl b)) he
      have p0t := pre_enter hp he (k := exprSize t) (by simp only [exprSize]; omega)
      have p0b := pre_enter hp he (k := exprSize b) (by simp only [exprSize]; omega)
      obtain ⟨po1, d1⟩ := iht ht _ p0t
      obtain ⟨po2, d2⟩ := ihb hb _ (pre_post p0b po1 (Nat.le_refl _))
      refine finish' hc he (po1.trans' po2) fun n ho => ?_
      cases ho with
      | forallT ho => exact po2.1 n (d1 t ht rfl n ho)
      | forallB ho => exact d2 b hb rfl n ho
  | letE nm t v b nd h iht ihv ihb =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · have ht : Sub t root := Sub.trans (.letT (.refl t)) he
      have hv : Sub v root := Sub.trans (.letV (.refl v)) he
      have hb : Sub b root := Sub.trans (.letB (.refl b)) he
      have p0t := pre_enter hp he (k := exprSize t) (by simp only [exprSize]; omega)
      have p0v := pre_enter hp he (k := exprSize v) (by simp only [exprSize]; omega)
      have p0b := pre_enter hp he (k := exprSize b) (by simp only [exprSize]; omega)
      obtain ⟨po1, d1⟩ := iht ht _ p0t
      obtain ⟨po2, d2⟩ := ihv hv _ (pre_post p0v po1 (Nat.le_refl _))
      obtain ⟨po3, d3⟩ := ihb hb _ (pre_post p0b (po1.trans' po2) (Nat.le_refl _))
      refine finish' hc he ((po1.trans' po2).trans' po3) fun n ho => ?_
      cases ho with
      | letT ho => exact po3.1 n (po2.1 n (d1 t ht rfl n ho))
      | letV ho => exact po3.1 n (d2 v hv rfl n ho)
      | letB ho => exact d3 b hb rfl n ho
  | proj nm i s h ihs =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · have hs : Sub s root := Sub.trans (.projS (.refl s)) he
      have p0s := pre_enter hp he (k := exprSize s) (by simp only [exprSize]; omega)
      obtain ⟨po1, d1⟩ := ihs hs _ p0s
      have po2 : Post root (Ix.Compile.Canon.refsExpr.go s (st.1, st.2.insert (Expr.proj nm i s h).getHash))
          (((Ix.Compile.Canon.refsExpr.go s (st.1, st.2.insert (Expr.proj nm i s h).getHash)).1.insert nm),
            (Ix.Compile.Canon.refsExpr.go s (st.1, st.2.insert (Expr.proj nm i s h).getHash)).2) :=
        ⟨fun n hn => by simp only [Std.HashSet.contains_insert, Bool.or_eq_true]; exact .inr hn,
          fun _ hh => hh, fun _ hh => .inl hh⟩
      refine finish' hc he (po1.trans' po2) fun n ho => ?_
      cases ho with
      | proj => simp only [Std.HashSet.contains_insert, name_beq_refl, Bool.true_or]
      | projS ho => exact po2.1 n (d1 s hs rfl n ho)
  | mdata d x h ihx =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · have hx : Sub x root := Sub.trans (.mdata (.refl x)) he
      have p0x := pre_enter hp he (k := exprSize x) (by simp only [exprSize]; omega)
      obtain ⟨po1, d1⟩ := ihx hx _ p0x
      refine finish' hc he po1 fun n ho => ?_
      cases ho with
      | mdata ho => exact d1 x hx rfl n ho
  | bvar i h =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · exact finish' hc he (Post.refl' _) fun n ho => by cases ho
  | fvar x h =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · exact finish' hc he (Post.refl' _) fun n ho => by cases ho
  | mvar x h =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · exact finish' hc he (Post.refl' _) fun n ho => by cases ho
  | sort u h =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · exact finish' hc he (Post.refl' _) fun n ho => by cases ho
  | lit l h =>
    intro he st hp
    unfold Ix.Compile.Canon.refsExpr.go
    split
    · exact skip' hc he hp ‹_›
    · exact finish' hc he (Post.refl' _) fun n ho => by cases ho

end complete

/-- **Completeness**: on collision-free input, `refsExpr e acc` contains every name occurring in
`e`, besides `acc`. -/
theorem refsExpr_complete {e : Expr} (hc : HashCons e) (acc : Std.HashSet Name) :
    (∀ n, acc.contains n = true → (refsExpr e acc).contains n = true) ∧
      ∀ n, Occ e n → (refsExpr e acc).contains n = true := by
  have hp : Pre e (acc, ∅) (exprSize e) := fun h hh => by
    simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at hh
  obtain ⟨po, d⟩ := go_spec hc e (Sub.refl e) (acc, ∅) hp
  exact ⟨po.1, fun n ho => d e (Sub.refl e) rfl n ho⟩

/-! ## The references of a constant -/

open Ix (ConstantInfo RecursorRule) in
/-- The references of a constant, declaratively (`Graph.lean`'s edges): the names occurring in its
type and value, an inductive's constructors, a constructor's inductive, a recursor's rule
constructors and the names occurring in its rules. -/
inductive RefOcc : ConstantInfo → Name → Prop
  | axiomT {v : Ix.AxiomVal} {n : Name} : Occ v.cnst.type n → RefOcc (.axiomInfo v) n
  | defnT {v : Ix.DefinitionVal} {n : Name} : Occ v.cnst.type n → RefOcc (.defnInfo v) n
  | defnV {v : Ix.DefinitionVal} {n : Name} : Occ v.value n → RefOcc (.defnInfo v) n
  | thmT {v : Ix.TheoremVal} {n : Name} : Occ v.cnst.type n → RefOcc (.thmInfo v) n
  | thmV {v : Ix.TheoremVal} {n : Name} : Occ v.value n → RefOcc (.thmInfo v) n
  | opaqueT {v : Ix.OpaqueVal} {n : Name} : Occ v.cnst.type n → RefOcc (.opaqueInfo v) n
  | opaqueV {v : Ix.OpaqueVal} {n : Name} : Occ v.value n → RefOcc (.opaqueInfo v) n
  | quotT {v : Ix.QuotVal} {n : Name} : Occ v.cnst.type n → RefOcc (.quotInfo v) n
  | inductT {v : Ix.InductiveVal} {n : Name} : Occ v.cnst.type n → RefOcc (.inductInfo v) n
  | inductC {v : Ix.InductiveVal} {n : Name} : n ∈ v.ctors → RefOcc (.inductInfo v) n
  | ctorT {v : Ix.ConstructorVal} {n : Name} : Occ v.cnst.type n → RefOcc (.ctorInfo v) n
  | ctorI (v : Ix.ConstructorVal) : RefOcc (.ctorInfo v) v.induct
  | recT {v : Ix.RecursorVal} {n : Name} : Occ v.cnst.type n → RefOcc (.recInfo v) n
  | recC {v : Ix.RecursorVal} {r : RecursorRule} : r ∈ v.rules → RefOcc (.recInfo v) r.ctor
  | recR {v : Ix.RecursorVal} {r : RecursorRule} {n : Name} : r ∈ v.rules → Occ r.rhs n →
      RefOcc (.recInfo v) n

open Ix (ConstantInfo) in
/-- Every expression of the constant is collision-free. -/
def ConstHashCons : ConstantInfo → Prop
  | .axiomInfo v => HashCons v.cnst.type
  | .defnInfo v => HashCons v.cnst.type ∧ HashCons v.value
  | .thmInfo v => HashCons v.cnst.type ∧ HashCons v.value
  | .opaqueInfo v => HashCons v.cnst.type ∧ HashCons v.value
  | .quotInfo v => HashCons v.cnst.type
  | .inductInfo v => HashCons v.cnst.type
  | .ctorInfo v => HashCons v.cnst.type
  | .recInfo v => HashCons v.cnst.type ∧ ∀ r ∈ v.rules, HashCons r.rhs

theorem foldl_insert_contains_iff : ∀ (l : List Name) (s : Std.HashSet Name) (n : Name),
    (l.foldl (fun x1 x2 => x1.insert x2) s).contains n = true ↔
      s.contains n = true ∨ ∃ k ∈ l, (k == n) = true
  | [], s, n => by simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, or_false]
  | a :: l, s, n => by
    rw [List.foldl_cons, foldl_insert_contains_iff l, Std.HashSet.contains_insert]
    simp only [Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨k, hk, e⟩)
      · exact .inr ⟨a, .inl rfl, h⟩
      · exact .inl h
      · exact .inr ⟨k, .inr hk, e⟩
    · rintro (h | ⟨k, rfl | hk, e⟩)
      · exact .inl (.inr h)
      · exact .inl (.inl e)
      · exact .inr ⟨k, hk, e⟩

/-- The recursor rules' fold. -/
def ruleStep (acc : Std.HashSet Name) (r : Ix.RecursorRule) : Std.HashSet Name :=
  refsExpr r.rhs (acc.insert r.ctor)

theorem ruleFold_sound : ∀ (l : List Ix.RecursorRule) (s : Std.HashSet Name) (n : Name),
    (l.foldl ruleStep s).contains n = true →
      s.contains n = true ∨ ∃ r ∈ l, (r.ctor == n) = true ∨ ∃ m, Occ r.rhs m ∧ (m == n) = true
  | [], s, n, h => .inl h
  | r :: l, s, n, h => by
    rw [List.foldl_cons] at h
    rcases ruleFold_sound l _ n h with h | ⟨r', hr', e⟩
    · rcases refsExpr_sound r.rhs _ n h with h | ⟨m, hm, e⟩
      · rw [Std.HashSet.contains_insert, Bool.or_eq_true] at h
        rcases h with h | h
        · exact .inr ⟨r, List.mem_cons_self .., .inl h⟩
        · exact .inl h
      · exact .inr ⟨r, List.mem_cons_self .., .inr ⟨m, hm, e⟩⟩
    · exact .inr ⟨r', List.mem_cons_of_mem _ hr', e⟩

theorem ruleFold_complete : ∀ (l : List Ix.RecursorRule), (∀ r ∈ l, HashCons r.rhs) →
    ∀ (s : Std.HashSet Name),
      (∀ n, s.contains n = true → (l.foldl ruleStep s).contains n = true) ∧
      (∀ r ∈ l, (l.foldl ruleStep s).contains r.ctor = true) ∧
      (∀ r ∈ l, ∀ n, Occ r.rhs n → (l.foldl ruleStep s).contains n = true)
  | [], _, s => ⟨fun _ h => h, fun _ h => (by cases h), fun _ h => (by cases h)⟩
  | r :: l, hl, s => by
    rw [List.foldl_cons]
    obtain ⟨c1, c2⟩ := refsExpr_complete (hl r (List.mem_cons_self ..)) (s.insert r.ctor)
    obtain ⟨m1, m2, m3⟩ := ruleFold_complete l (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr'))
      (ruleStep s r)
    refine ⟨fun n hn => m1 n (c1 n ?_), fun r' hr' => ?_, fun r' hr' n ho => ?_⟩
    · rw [Std.HashSet.contains_insert, hn, Bool.or_true]
    · rcases List.mem_cons.1 hr' with rfl | hr'
      · exact m1 _ (c1 _ (by rw [Std.HashSet.contains_insert, name_beq_refl, Bool.true_or]))
      · exact m2 r' hr'
    · rcases List.mem_cons.1 hr' with rfl | hr'
      · exact m1 n (c2 n ho)
      · exact m3 r' hr' n ho

open Ix (ConstantInfo) in
/-- **The edges of a constant are sound**: `refsConst c` contains only names (`==` to names)
`c` references. -/
theorem refsConst_sound (c : ConstantInfo) (n : Name) (h : (refsConst c).contains n = true) :
    ∃ m, RefOcc c m ∧ (m == n) = true := by
  cases c with
  | axiomInfo v =>
    rcases refsExpr_sound v.cnst.type _ n h with h | ⟨m, hm, e⟩
    · simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at h
    · exact ⟨m, .axiomT hm, e⟩
  | defnInfo v =>
    rcases refsExpr_sound v.value _ n h with h | ⟨m, hm, e⟩
    · rcases refsExpr_sound v.cnst.type _ n h with h | ⟨m, hm, e⟩
      · simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at h
      · exact ⟨m, .defnT hm, e⟩
    · exact ⟨m, .defnV hm, e⟩
  | thmInfo v =>
    rcases refsExpr_sound v.value _ n h with h | ⟨m, hm, e⟩
    · rcases refsExpr_sound v.cnst.type _ n h with h | ⟨m, hm, e⟩
      · simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at h
      · exact ⟨m, .thmT hm, e⟩
    · exact ⟨m, .thmV hm, e⟩
  | opaqueInfo v =>
    rcases refsExpr_sound v.value _ n h with h | ⟨m, hm, e⟩
    · rcases refsExpr_sound v.cnst.type _ n h with h | ⟨m, hm, e⟩
      · simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at h
      · exact ⟨m, .opaqueT hm, e⟩
    · exact ⟨m, .opaqueV hm, e⟩
  | quotInfo v =>
    rcases refsExpr_sound v.cnst.type _ n h with h | ⟨m, hm, e⟩
    · simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at h
    · exact ⟨m, .quotT hm, e⟩
  | inductInfo v =>
    have h' : (v.ctors.toList.foldl (fun x1 x2 => x1.insert x2) (refsExpr v.cnst.type)).contains n = true := by
      rw [Array.foldl_toList]; exact h
    rcases (foldl_insert_contains_iff _ _ n).1 h' with h | ⟨k, hk, e⟩
    · rcases refsExpr_sound v.cnst.type _ n h with h | ⟨m, hm, e⟩
      · simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at h
      · exact ⟨m, .inductT hm, e⟩
    · exact ⟨k, .inductC (Array.mem_toList_iff.1 hk), e⟩
  | ctorInfo v =>
    have h' : ((refsExpr v.cnst.type).insert v.induct).contains n = true := h
    rw [Std.HashSet.contains_insert, Bool.or_eq_true] at h'
    rcases h' with e | h
    · exact ⟨v.induct, .ctorI v, e⟩
    · rcases refsExpr_sound v.cnst.type _ n h with h | ⟨m, hm, e⟩
      · simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at h
      · exact ⟨m, .ctorT hm, e⟩
  | recInfo v =>
    have h' : (v.rules.toList.foldl ruleStep (refsExpr v.cnst.type)).contains n = true := by
      rw [Array.foldl_toList]; exact h
    rcases ruleFold_sound _ _ n h' with h | ⟨r, hr, e | ⟨m, hm, e⟩⟩
    · rcases refsExpr_sound v.cnst.type _ n h with h | ⟨m, hm, e⟩
      · simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at h
      · exact ⟨m, .recT hm, e⟩
    · exact ⟨r.ctor, .recC (Array.mem_toList_iff.1 hr), e⟩
    · exact ⟨m, .recR (Array.mem_toList_iff.1 hr) hm, e⟩

open Ix (ConstantInfo) in
/-- **The edges of a constant are complete** on collision-free expressions: `refsConst c`
contains every name `c` references. -/
theorem refsConst_complete (c : ConstantInfo) (hc : ConstHashCons c) (n : Name) (h : RefOcc c n) :
    (refsConst c).contains n = true := by
  cases h with
  | axiomT ho => exact (refsExpr_complete hc _).2 n ho
  | defnT ho =>
    exact (refsExpr_complete hc.2 _).1 n ((refsExpr_complete hc.1 _).2 n ho)
  | defnV ho => exact (refsExpr_complete hc.2 _).2 n ho
  | thmT ho =>
    exact (refsExpr_complete hc.2 _).1 n ((refsExpr_complete hc.1 _).2 n ho)
  | thmV ho => exact (refsExpr_complete hc.2 _).2 n ho
  | opaqueT ho =>
    exact (refsExpr_complete hc.2 _).1 n ((refsExpr_complete hc.1 _).2 n ho)
  | opaqueV ho => exact (refsExpr_complete hc.2 _).2 n ho
  | quotT ho => exact (refsExpr_complete hc _).2 n ho
  | inductT ho =>
    rename_i v
    show (v.ctors.foldl (fun x1 x2 => x1.insert x2) (refsExpr v.cnst.type)).contains n = true
    rw [← Array.foldl_toList]
    exact (foldl_insert_contains_iff _ _ n).2 (.inl ((refsExpr_complete hc _).2 n ho))
  | inductC hk =>
    rename_i v
    show (v.ctors.foldl (fun x1 x2 => x1.insert x2) (refsExpr v.cnst.type)).contains n = true
    rw [← Array.foldl_toList]
    exact (foldl_insert_contains_iff _ _ n).2 (.inr ⟨n, Array.mem_toList_iff.2 hk, name_beq_refl n⟩)
  | ctorT ho =>
    rename_i v
    show ((refsExpr v.cnst.type).insert v.induct).contains n = true
    rw [Std.HashSet.contains_insert, (refsExpr_complete hc _).2 n ho, Bool.or_true]
  | ctorI v =>
    show ((refsExpr v.cnst.type).insert v.induct).contains v.induct = true
    rw [Std.HashSet.contains_insert, name_beq_refl, Bool.true_or]
  | recT ho =>
    rename_i v
    show (v.rules.foldl ruleStep (refsExpr v.cnst.type)).contains n = true
    rw [← Array.foldl_toList]
    exact (ruleFold_complete _ (fun r hr => hc.2 r (Array.mem_toList_iff.1 hr)) _).1 n
      ((refsExpr_complete hc.1 _).2 n ho)
  | recC hr =>
    rename_i v r
    show (v.rules.foldl ruleStep (refsExpr v.cnst.type)).contains r.ctor = true
    rw [← Array.foldl_toList]
    exact (ruleFold_complete _ (fun r hr => hc.2 r (Array.mem_toList_iff.1 hr)) _).2.1 r
      (Array.mem_toList_iff.2 hr)
  | recR hr ho =>
    rename_i v r
    show (v.rules.foldl ruleStep (refsExpr v.cnst.type)).contains n = true
    rw [← Array.foldl_toList]
    exact (ruleFold_complete _ (fun r hr => hc.2 r (Array.mem_toList_iff.1 hr)) _).2.2 r
      (Array.mem_toList_iff.2 hr) n ho

end Ix.CompileCert.Canon
