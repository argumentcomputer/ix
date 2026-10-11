module
public import Ix.Compile.Image.TotalSpec
import all Ix.Compile.Image.TotalSpec
public import Ix.Compile.Image.RawExact
public import Std.Data.HashMap.Lemmas
public section

namespace Ix.Compile.Image.TotalMemo

open Ix (Expr)
open TotalSpec

/-- Retain the actual raw input; its digest is only a candidate selector. -/
structure Entry {α β : Type} (spec : α → β) where
  key : α
  value : β
  correct : value = spec key

abbrev Memo {α β : Type} (spec : α → β) := Std.HashMap UInt64 (Entry spec)

structure Answer {β : Type} (expected : β) (σ : Type) where
  value : β
  correct : value = expected
  state : σ

/-- No property of `bucket` is assumed. A collision is a miss unless the
retained raw inputs are equal. Proofs are erased from native execution. -/
def probe {α β : Type} (eq : DecidableEq α) (spec : α → β)
    (memo : Memo spec) (bucket : UInt64) (key : α) :
    Option {value : β // value = spec key} :=
  match memo[bucket]? with
  | none => none
  | some entry =>
    match eq entry.key key with
    | .isFalse _ => none
    | .isTrue same =>
      some ⟨entry.value, entry.correct.trans (congrArg spec same)⟩

def put {α β : Type} (spec : α → β) (memo : Memo spec)
    (bucket : UInt64) (key : α) (value : β) (correct : value = spec key) : Memo spec :=
  memo.insert bucket ⟨key, value, correct⟩

abbrev ShiftKey := Expr × Nat × Nat
abbrev OccursKey := Expr × Nat
def liftAt (key : ShiftKey) : Expr := liftP key.1 key.2.1 key.2.2
def lowerAt (key : ShiftKey) : Expr := lowerP key.1 key.2.1 key.2.2
def occursAt (key : OccursKey) : Bool := occursP key.1 key.2

local instance : DecidableEq Expr := RawExact.exprDecEq

/-- Each component comparison uses the exact expression decision, with its
pointer shortcut, before a stored answer may be returned. -/
def shiftDecEq : DecidableEq ShiftKey := inferInstance
def occursDecEq : DecidableEq OccursKey := inferInstance

abbrev RangeMemo := Memo looseRangeP
abbrev LiftMemo := Memo liftAt
abbrev LowerMemo := Memo lowerAt
abbrev OccursMemo := Memo occursAt

structure ShiftState (spec : ShiftKey → Expr) where
  range : RangeMemo := {}
  values : Memo spec := {}

structure OccursState where
  range : RangeMemo := {}
  values : OccursMemo := {}

/-- State validity is intrinsic, including for arbitrary supplied states.
It places no condition on expressions, hashes, hint functions or source Dom. -/
def Valid {α β : Type} (spec : α → β) (memo : Memo spec) : Prop :=
  ∀ (bucket : UInt64) (entry : Entry spec),
    memo[bucket]? = some entry → entry.value = spec entry.key

theorem valid {α β : Type} (spec : α → β) (memo : Memo spec) : Valid spec memo :=
  fun _ entry _ => entry.correct

theorem valid_empty {α β : Type} (spec : α → β) : Valid spec ({} : Memo spec) :=
  valid spec {}

theorem valid_put {α β : Type} (spec : α → β) (memo : Memo spec)
    (bucket : UInt64) (key : α) (value : β) (correct : value = spec key) :
    Valid spec (put spec memo bucket key value correct) := valid spec _

theorem probe_correct {α β : Type} (eq : DecidableEq α) (spec : α → β)
    (memo : Memo spec) (bucket : UInt64) (key : α)
    (hit : {value : β // value = spec key})
    (_found : probe eq spec memo bucket key = some hit) : hit.val = spec key :=
  hit.property

theorem probe_collision {α β : Type} (eq : DecidableEq α) (spec : α → β)
    (memo : Memo spec) (bucket : UInt64) (key : α) (entry : Entry spec)
    (found : memo[bucket]? = some entry) (different : entry.key ≠ key) :
    probe eq spec memo bucket key = none := by
  unfold probe
  rw [found]
  dsimp only
  cases eq entry.key key with
  | isTrue same => exact (different same).elim
  | isFalse _ => rfl

theorem probe_stored {α β : Type} (eq : DecidableEq α) (spec : α → β)
    (memo : Memo spec) (bucket : UInt64) (entry : Entry spec)
    (found : memo[bucket]? = some entry) :
    (probe eq spec memo bucket entry.key).map Subtype.val = some entry.value := by
  unfold probe
  rw [found]
  dsimp only
  cases eq entry.key entry.key with
  | isTrue _ => rfl
  | isFalse different => exact (different rfl).elim

/-- Structural recursion with the original left-to-right child order and
the original last write after a miss. The hint is unrestricted. -/
def rangeGo (hint : Expr → UInt64) (e : Expr) (memo : RangeMemo) :
    Answer (looseRangeP e) RangeMemo :=
  match probe RawExact.exprDecEq looseRangeP memo (hint e) e with
  | some hit => ⟨hit.val, hit.property, memo⟩
  | none =>
    let r : Answer (looseRangeP e) RangeMemo :=
      match e with
      | .bvar i _ => ⟨i + 1, rfl, memo⟩
      | .app f a _ =>
        let rf := rangeGo hint f memo
        let ra := rangeGo hint a rf.state
        ⟨max rf.value ra.value, congr (congrArg Nat.max rf.correct) ra.correct, ra.state⟩
      | .lam _ t b _ _ | .forallE _ t b _ _ =>
        let rt := rangeGo hint t memo
        let rb := rangeGo hint b rt.state
        ⟨max rt.value (rb.value - 1), congr (congrArg Nat.max rt.correct) (congrArg (fun x : Nat => x - 1) rb.correct), rb.state⟩
      | .letE _ t v b _ _ =>
        let rt := rangeGo hint t memo
        let rv := rangeGo hint v rt.state
        let rb := rangeGo hint b rv.state
        ⟨max (max rt.value rv.value) (rb.value - 1), congr (congrArg Nat.max (congr (congrArg Nat.max rt.correct) rv.correct))
          (congrArg (fun x : Nat => x - 1) rb.correct), rb.state⟩
      | .proj _ _ s _ | .mdata _ s _ =>
        let rs := rangeGo hint s memo
        ⟨rs.value, rs.correct, rs.state⟩
      | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => ⟨0, rfl, memo⟩
    ⟨r.value, r.correct, put looseRangeP r.state (hint e) e r.value r.correct⟩

/-- Exact `liftP` result, carrying the original range and operation tables.
No input well-formedness or property of either hint is required. -/
def liftGo (rangeHint : Expr → UInt64) (hint : ShiftKey → UInt64)
    (e : Expr) (n c : Nat) (st : ShiftState liftAt) :
    Answer (liftP e n c) (ShiftState liftAt) :=
  if hz : n == 0 then
    ⟨e, by rw [liftP.eq_def, ite_eq_left hz], st⟩
  else
    let rr := rangeGo rangeHint e st.range
    let st1 : ShiftState liftAt := { st with range := rr.state }
    if hc : rr.value ≤ c then
      have cut : looseRangeP e ≤ c := by simpa only [rr.correct] using hc
      ⟨e, by rw [liftP.eq_def, ite_eq_right hz, ite_eq_left cut], st1⟩
    else
      have uncut : ¬looseRangeP e ≤ c := by simpa only [rr.correct] using hc
      match probe shiftDecEq liftAt st1.values (hint (e, n, c)) (e, n, c) with
      | some hit => ⟨hit.val, hit.property, st1⟩
      | none =>
        let r : Answer (match e with
        | .bvar i _ => if i ≥ c then Expr.mkBVar (i + n) else e
        | .app f a _ => Expr.mkApp (liftP f n c) (liftP a n c)
        | .lam nm t b bi _ => Expr.mkLam nm (liftP t n c) (liftP b n (c + 1)) bi
        | .forallE nm t b bi _ => Expr.mkForallE nm (liftP t n c) (liftP b n (c + 1)) bi
        | .letE nm t v b nd _ => Expr.mkLetE nm (liftP t n c) (liftP v n c) (liftP b n (c + 1)) nd
        | .proj nm i x _ => Expr.mkProj nm i (liftP x n c)
        | .mdata md x _ => Expr.mkMData md (liftP x n c)
        | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => e) (ShiftState liftAt) :=
          match e with
          | e@same:(.bvar i _) =>
            ⟨if i ≥ c then Expr.mkBVar (i + n) else e,
              congrArg (fun x => if i ≥ c then Expr.mkBVar (i + n) else x) same, st1⟩
          | .app f a _ =>
            let rf := liftGo rangeHint hint f n c st1
            let ra := liftGo rangeHint hint a n c rf.state
            ⟨Expr.mkApp rf.value ra.value, by rw [rf.correct, ra.correct], ra.state⟩
          | .lam nm t b bi _ =>
            let rt := liftGo rangeHint hint t n c st1
            let rb := liftGo rangeHint hint b n (c + 1) rt.state
            ⟨Expr.mkLam nm rt.value rb.value bi, by rw [rt.correct, rb.correct], rb.state⟩
          | .forallE nm t b bi _ =>
            let rt := liftGo rangeHint hint t n c st1
            let rb := liftGo rangeHint hint b n (c + 1) rt.state
            ⟨Expr.mkForallE nm rt.value rb.value bi, by rw [rt.correct, rb.correct], rb.state⟩
          | .letE nm t v b nd _ =>
            let rt := liftGo rangeHint hint t n c st1
            let rv := liftGo rangeHint hint v n c rt.state
            let rb := liftGo rangeHint hint b n (c + 1) rv.state
            ⟨Expr.mkLetE nm rt.value rv.value rb.value nd, by
              rw [rt.correct, rv.correct, rb.correct], rb.state⟩
          | .proj nm i x _ =>
            let rx := liftGo rangeHint hint x n c st1
            ⟨Expr.mkProj nm i rx.value, by rw [rx.correct], rx.state⟩
          | .mdata md x _ =>
            let rx := liftGo rangeHint hint x n c st1
            ⟨Expr.mkMData md rx.value, by rw [rx.correct], rx.state⟩
          | e@same:(.fvar ..) | e@same:(.mvar ..) | e@same:(.sort ..)
          | e@same:(.const ..) | e@same:(.lit ..) =>
            ⟨e, same, st1⟩
        have correct : r.value = liftP e n c := by
          rw [liftP.eq_def, ite_eq_right hz, ite_eq_right uncut]
          exact r.correct
        ⟨r.value, correct,
          { r.state with values := put liftAt r.state.values (hint (e, n, c)) (e, n, c) r.value correct }⟩

/-- Exact `lowerP` result, carrying the original range and operation tables.
No input well-formedness or property of either hint is required. -/
def lowerGo (rangeHint : Expr → UInt64) (hint : ShiftKey → UInt64)
    (e : Expr) (n c : Nat) (st : ShiftState lowerAt) :
    Answer (lowerP e n c) (ShiftState lowerAt) :=
  if hz : n == 0 then
    ⟨e, by rw [lowerP.eq_def, ite_eq_left hz], st⟩
  else
    let rr := rangeGo rangeHint e st.range
    let st1 : ShiftState lowerAt := { st with range := rr.state }
    if hc : rr.value ≤ c then
      have cut : looseRangeP e ≤ c := by simpa only [rr.correct] using hc
      ⟨e, by rw [lowerP.eq_def, ite_eq_right hz, ite_eq_left cut], st1⟩
    else
      have uncut : ¬looseRangeP e ≤ c := by simpa only [rr.correct] using hc
      match probe shiftDecEq lowerAt st1.values (hint (e, n, c)) (e, n, c) with
      | some hit => ⟨hit.val, hit.property, st1⟩
      | none =>
        let r : Answer (match e with
        | .bvar i _ => if i ≥ c + n then Expr.mkBVar (i - n) else e
        | .app f a _ => Expr.mkApp (lowerP f n c) (lowerP a n c)
        | .lam nm t b bi _ => Expr.mkLam nm (lowerP t n c) (lowerP b n (c + 1)) bi
        | .forallE nm t b bi _ => Expr.mkForallE nm (lowerP t n c) (lowerP b n (c + 1)) bi
        | .letE nm t v b nd _ => Expr.mkLetE nm (lowerP t n c) (lowerP v n c) (lowerP b n (c + 1)) nd
        | .proj nm i x _ => Expr.mkProj nm i (lowerP x n c)
        | .mdata md x _ => Expr.mkMData md (lowerP x n c)
        | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => e) (ShiftState lowerAt) :=
          match e with
          | e@same:(.bvar i _) =>
            ⟨if i ≥ c + n then Expr.mkBVar (i - n) else e,
              congrArg (fun x => if i ≥ c + n then Expr.mkBVar (i - n) else x) same, st1⟩
          | .app f a _ =>
            let rf := lowerGo rangeHint hint f n c st1
            let ra := lowerGo rangeHint hint a n c rf.state
            ⟨Expr.mkApp rf.value ra.value, by rw [rf.correct, ra.correct], ra.state⟩
          | .lam nm t b bi _ =>
            let rt := lowerGo rangeHint hint t n c st1
            let rb := lowerGo rangeHint hint b n (c + 1) rt.state
            ⟨Expr.mkLam nm rt.value rb.value bi, by rw [rt.correct, rb.correct], rb.state⟩
          | .forallE nm t b bi _ =>
            let rt := lowerGo rangeHint hint t n c st1
            let rb := lowerGo rangeHint hint b n (c + 1) rt.state
            ⟨Expr.mkForallE nm rt.value rb.value bi, by rw [rt.correct, rb.correct], rb.state⟩
          | .letE nm t v b nd _ =>
            let rt := lowerGo rangeHint hint t n c st1
            let rv := lowerGo rangeHint hint v n c rt.state
            let rb := lowerGo rangeHint hint b n (c + 1) rv.state
            ⟨Expr.mkLetE nm rt.value rv.value rb.value nd, by
              rw [rt.correct, rv.correct, rb.correct], rb.state⟩
          | .proj nm i x _ =>
            let rx := lowerGo rangeHint hint x n c st1
            ⟨Expr.mkProj nm i rx.value, by rw [rx.correct], rx.state⟩
          | .mdata md x _ =>
            let rx := lowerGo rangeHint hint x n c st1
            ⟨Expr.mkMData md rx.value, by rw [rx.correct], rx.state⟩
          | e@same:(.fvar ..) | e@same:(.mvar ..) | e@same:(.sort ..)
          | e@same:(.const ..) | e@same:(.lit ..) =>
            ⟨e, same, st1⟩
        have correct : r.value = lowerP e n c := by
          rw [lowerP.eq_def, ite_eq_right hz, ite_eq_right uncut]
          exact r.correct
        ⟨r.value, correct,
          { r.state with values := put lowerAt r.state.values (hint (e, n, c)) (e, n, c) r.value correct }⟩

/-- Exact occurrence test, evaluating the same child calls in order before
combining their Boolean results. -/
def occursGo (rangeHint : Expr → UInt64) (hint : OccursKey → UInt64)
    (e : Expr) (k : Nat) (st : OccursState) : Answer (occursP e k) OccursState :=
  let rr := rangeGo rangeHint e st.range
  let st1 : OccursState := { st with range := rr.state }
  if hc : rr.value ≤ k then
    have cut : looseRangeP e ≤ k := by simpa only [rr.correct] using hc
    ⟨false, by rw [occursP.eq_def, ite_eq_left cut], st1⟩
  else
    have uncut : ¬looseRangeP e ≤ k := by simpa only [rr.correct] using hc
    match probe occursDecEq occursAt st1.values (hint (e, k)) (e, k) with
    | some hit => ⟨hit.val, hit.property, st1⟩
    | none =>
      let r : Answer (match e with
        | .bvar i _ => i == k
        | .app f a _ => occursP f k || occursP a k
        | .lam _ t b _ _ | .forallE _ t b _ _ => occursP t k || occursP b (k + 1)
        | .letE _ t v b _ _ => occursP t k || occursP v k || occursP b (k + 1)
        | .proj _ _ x _ | .mdata _ x _ => occursP x k
        | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => false) OccursState :=
        match e with
        | .bvar i _ => ⟨i == k, rfl, st1⟩
        | .app f a _ =>
          let rf := occursGo rangeHint hint f k st1
          let ra := occursGo rangeHint hint a k rf.state
          ⟨rf.value || ra.value, by rw [rf.correct, ra.correct], ra.state⟩
        | .lam _ t b _ _ | .forallE _ t b _ _ =>
          let rt := occursGo rangeHint hint t k st1
          let rb := occursGo rangeHint hint b (k + 1) rt.state
          ⟨rt.value || rb.value, by rw [rt.correct, rb.correct], rb.state⟩
        | .letE _ t v b _ _ =>
          let rt := occursGo rangeHint hint t k st1
          let rv := occursGo rangeHint hint v k rt.state
          let rb := occursGo rangeHint hint b (k + 1) rv.state
          ⟨rt.value || rv.value || rb.value, by rw [rt.correct, rv.correct, rb.correct], rb.state⟩
        | .proj _ _ x _ | .mdata _ x _ =>
          let rx := occursGo rangeHint hint x k st1
          ⟨rx.value, rx.correct, rx.state⟩
        | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => ⟨false, rfl, st1⟩
      have correct : r.value = occursP e k := by
        rw [occursP.eq_def, ite_eq_right uncut]
        exact r.correct
      ⟨r.value, correct,
        { r.state with values := put occursAt r.state.values (hint (e, k)) (e, k) r.value correct }⟩

/-- Full result laws for arbitrary hints and every representable state. -/
theorem rangeGo_result (hint : Expr → UInt64) (e : Expr) (memo : RangeMemo) :
    (rangeGo hint e memo).value = looseRangeP e := (rangeGo hint e memo).correct

theorem rangeGo_hit_state (hint : Expr → UInt64) (e : Expr) (memo : RangeMemo)
    (hit : {value : Nat // value = looseRangeP e})
    (found : probe RawExact.exprDecEq looseRangeP memo (hint e) e = some hit) :
    (rangeGo hint e memo).state = memo := by
  rw [rangeGo.eq_def, found]

theorem liftGo_result (rangeHint : Expr → UInt64) (hint : ShiftKey → UInt64)
    (e : Expr) (n c : Nat) (st : ShiftState liftAt) :
    (liftGo rangeHint hint e n c st).value = liftP e n c :=
  (liftGo rangeHint hint e n c st).correct

theorem lowerGo_result (rangeHint : Expr → UInt64) (hint : ShiftKey → UInt64)
    (e : Expr) (n c : Nat) (st : ShiftState lowerAt) :
    (lowerGo rangeHint hint e n c st).value = lowerP e n c :=
  (lowerGo rangeHint hint e n c st).correct

theorem occursGo_result (rangeHint : Expr → UInt64) (hint : OccursKey → UInt64)
    (e : Expr) (k : Nat) (st : OccursState) :
    (occursGo rangeHint hint e k st).value = occursP e k :=
  (occursGo rangeHint hint e k st).correct

/-- Empty-state entry points for the pure-core compilation bridge. Carried
state callers use the workers above and retain the actual resulting tables. -/
def rangeFast (e : Expr) : Nat := (rangeGo hash e {}).value
def liftFast (e : Expr) (n c : Nat) : Expr := (liftGo hash hash e n c {}).value
def lowerFast (e : Expr) (n c : Nat) : Expr := (lowerGo hash hash e n c {}).value
def occursFast (e : Expr) (k : Nat) : Bool := (occursGo hash hash e k {}).value

end Ix.Compile.Image.TotalMemo
