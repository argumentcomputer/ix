import Compilatrix.Ixby.SymbolicSource
import Compilatrix.Ixby.SymbolicTarget

/-! Symbolic data correspondence retains complete constructor identities and
opaque parameter positions. Its interpretation is ordinary host `Data`. -/

namespace Compilatrix.Ixby

inductive DataExpr where
  | parameter (index : Nat)
  | nat (value : Nat)
  | str (value : String)
  | ctor (address : Ixon.Address) (tag : Nat) (fields : List DataExpr)
  | erased
  deriving Repr, Inhabited

def DataExpr.instantiate (input : Nat → Data) : DataExpr → Data
  | .parameter index => input index
  | .nat n => .nat n
  | .str s => .str s
  | .ctor address tag fields => .ctor address tag (fields.map (DataExpr.instantiate input))
  | .erased => .erased

mutual
  def DataExpr.equal : DataExpr → DataExpr → Bool
    | .parameter a, .parameter b => a == b
    | .nat a, .nat b => a == b
    | .str a, .str b => a == b
    | .ctor a t xs, .ctor b u ys => a == b && t == u && DataExpr.equalFields xs ys
    | .erased, .erased => true
    | _, _ => false
  def DataExpr.equalFields : List DataExpr → List DataExpr → Bool
    | [], [] => true
    | x :: xs, y :: ys => DataExpr.equal x y && DataExpr.equalFields xs ys
    | _, _ => false
end

theorem DataExpr.eq_of_equal (a : DataExpr) : ∀ b, DataExpr.equal a b = true → a = b := by
  induction a using DataExpr.rec
      (motive_2 := fun xs => ∀ ys, DataExpr.equalFields xs ys = true → xs = ys) with
  | parameter n => intro b h; cases b <;> simp_all [DataExpr.equal]
  | nat n => intro b h; cases b <;> simp_all [DataExpr.equal]
  | str s => intro b h; cases b <;> simp_all [DataExpr.equal]
  | ctor address tag fields ih =>
      intro b h
      cases b <;> simp_all [DataExpr.equal]
      exact ih _ h.2
  | erased => intro b h; cases b <;> simp_all [DataExpr.equal]
  | nil => rename_i ys h; cases ys <;> simp_all [DataExpr.equalFields]
  | cons head tail ihHead ihTail =>
      rename_i ys h
      cases ys <;> simp_all [DataExpr.equalFields]
      exact ⟨ihHead _ h.1, ihTail _ h.2⟩

def DataExpr.ofSource : Nat → SymbolicSource.Value → Option DataExpr
  | 0, _ => none
  | fuel + 1, value => match value with
    | .parameter index => some (.parameter index)
    | .lit (.nat n) => some (.nat n)
    | .lit (.str s) => some (.str s)
    | .erased => some .erased
    | .ctor address tag fields => return .ctor address tag (← fields.mapM (DataExpr.ofSource fuel))
    | _ => none

def DataExpr.ofTarget (source : Source) : Nat → SymbolicTarget.Value → Option DataExpr
  | 0, _ => none
  | fuel + 1, value => match value with
    | .parameter index => some (.parameter index)
    | .ctor id fields => do
        if id == boxId 0 then
          if fields.isEmpty then some .erased else none
        else if id == boxId 1 then
          match fields.toList with
          | [.scalar (.nat n)] => some (.nat n)
          | _ => none
        else if id == boxId 2 then
          match fields.toList with
          | [.scalar (.str s)] => some (.str s)
          | _ => none
        else
          let ctor ← source.constructors.find? (fun ctor => ctor.id == id)
          if fields.size != ctor.fields then none else
            return .ctor ctor.address ctor.tag (← fields.toList.mapM (DataExpr.ofTarget source fuel))
    | _ => none

namespace SymbolicData

theorem mapM_getElem? {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (accepted : xs.mapM f = some ys) (index : Nat) :
    (xs[index]? >>= f) = ys[index]? := by
  induction xs generalizing ys index with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at accepted
      subst ys
      simp
  | cons x xs ih =>
      simp only [List.mapM_cons, Bind.bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at accepted
      obtain ⟨y, hy, ys, hys, rfl⟩ := accepted
      cases index with
      | zero => simpa using hy
      | succ index => simpa using ih hys index

theorem mapM_transfer {α β γ : Type} {f : α → Option β} {g : α → Option γ} {h : β → γ}
    (sound : ∀ a b, f a = some b → g a = some (h b)) {xs : List α} {ys : List β}
    (accepted : xs.mapM f = some ys) : xs.mapM g = some (ys.map h) := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at accepted
      subst ys
      rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, Bind.bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at accepted
      obtain ⟨y, hy, ys, hys, rfl⟩ := accepted
      simp [List.mapM_cons, sound x y hy, ih hys]

theorem map_of_mapM {α β γ : Type} {f : α → Option β} {g : α → γ} {h : β → γ}
    (sound : ∀ a b, f a = some b → g a = h b) {xs : List α} {ys : List β}
    (accepted : xs.mapM f = some ys) : xs.map g = ys.map h := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at accepted
      subst ys
      rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, Bind.bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at accepted
      obtain ⟨y, hy, ys, hys, rfl⟩ := accepted
      simp [sound x y hy, ih hys]

end SymbolicData

theorem DataExpr.ofSource_sound {fuel value expr}
    (accepted : DataExpr.ofSource fuel value = some expr) (input : Nat → Data) :
    value.instantiate (fun i => (input i).toValue) = (expr.instantiate input).toValue := by
  induction fuel generalizing value expr with
  | zero => simp [DataExpr.ofSource] at accepted
  | succ fuel ih =>
      cases value <;> simp only [DataExpr.ofSource] at accepted
      all_goals try contradiction
      · cases accepted
        simp [SymbolicSource.Value.instantiate, DataExpr.instantiate]
      · rename_i address tag fields
        simp only [Bind.bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at accepted
        obtain ⟨terms, ht, rfl⟩ := accepted
        have mapped := SymbolicData.map_of_mapM (fun _ _ h => ih h) ht
        simpa [SymbolicSource.Value.instantiate, DataExpr.instantiate, Data.toValue,
          List.map_map, Function.comp_def] using congrArg (IxIR0.Value.ctor address tag) mapped
      · rename_i literal
        cases literal <;> cases accepted <;>
          simp [SymbolicSource.Value.instantiate, DataExpr.instantiate, Data.toValue]
      · cases accepted
        simp [SymbolicSource.Value.instantiate, DataExpr.instantiate, Data.toValue]

theorem decodeData_add_fuel {source fuel value data}
    (accepted : decodeData source fuel value = some data) (extra : Nat) :
    decodeData source (fuel + extra) value = some data := by
  induction fuel generalizing value data with
  | zero => simp [decodeData] at accepted
  | succ fuel ih =>
      cases value <;> try (simp only [decodeData] at accepted; contradiction)
      rename_i id fields
      simp only [decodeData] at accepted
      simp only [Nat.succ_add, decodeData]
      split at accepted
      · rename_i erased
        simpa only [erased, ↓reduceIte] using accepted
      · rename_i notErased
        simp only [notErased, Bool.false_eq_true, ↓reduceIte]
        split at accepted
        · rename_i natBox
          simpa only [natBox, ↓reduceIte] using accepted
        · rename_i notNat
          simp only [notNat, Bool.false_eq_true, ↓reduceIte]
          split at accepted
          · rename_i strBox
            simpa only [strBox, ↓reduceIte] using accepted
          · rename_i notStr
            simp only [notStr, Bool.false_eq_true, ↓reduceIte]
            simp only [Bind.bind, Option.bind_eq_some_iff] at accepted
            obtain ⟨ctor, hc, h⟩ := accepted
            split at h
            · contradiction
            · rename_i arity
              simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
              obtain ⟨decoded, hd, rfl⟩ := h
              have arityEq : fields.size = ctor.fields := by simpa using arity
              have mapped := SymbolicData.mapM_transfer (h := fun d => d) (fun _ _ h => ih h) hd
              simp [hc, arityEq, mapped, Bind.bind, Option.bind]

theorem decodeData_mono {source fuel larger value data} (le : fuel ≤ larger)
    (accepted : decodeData source fuel value = some data) :
    decodeData source larger value = some data := by
  have result := decodeData_add_fuel accepted (larger - fuel)
  simpa only [Nat.add_sub_of_le le] using result

theorem observe_add_fuel {fuel value data}
    (accepted : observe fuel value = some data) (extra : Nat) :
    observe (fuel + extra) value = some data := by
  induction fuel generalizing value data with
  | zero => simp [observe] at accepted
  | succ fuel ih =>
      cases value with
      | clos _ _ _ => simp [observe] at accepted
      | pap _ _ => simp [observe] at accepted
      | erased => simpa [Nat.succ_add, observe] using accepted
      | lit literal => cases literal <;> simpa [Nat.succ_add, observe] using accepted
      | ctor address tag fields =>
          simp only [observe, Bind.bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at accepted
          obtain ⟨decoded, hd, rfl⟩ := accepted
          have mapped := SymbolicData.mapM_transfer (h := fun d => d) (fun _ _ h => ih h) hd
          simp [observe, Nat.succ_add, mapped]

/-- Every finite host data tree has an exact source observation. -/
theorem Data.observe_toValue (data : Data) : ∃ fuel, observe fuel data.toValue = some data := by
  induction data using Data.rec
      (motive_2 := fun values => ∃ fuel, values.mapM (fun d => observe fuel d.toValue) = some values) with
  | nat n => exact ⟨1, by simp [observe, Data.toValue]⟩
  | str s => exact ⟨1, by simp [observe, Data.toValue]⟩
  | erased => exact ⟨1, by simp [observe, Data.toValue]⟩
  | ctor address tag fields ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simp [observe, Data.toValue, List.mapM_map, Function.comp_def, h]⟩
  | nil => exact ⟨1, rfl⟩
  | cons head tail ihHead ihTail =>
      obtain ⟨fh, hh⟩ := ihHead
      obtain ⟨ft, ht⟩ := ihTail
      have headRun := observe_add_fuel hh ft
      have tailRun := SymbolicData.mapM_transfer (h := fun d => d)
        (fun _ _ h => observe_add_fuel h fh) ht
      have tailRun' : tail.mapM (fun d => observe (fh + ft) d.toValue) = some tail := by
        simpa [Nat.add_comm ft fh] using tailRun
      refine ⟨fh + ft, ?_⟩
      simp [List.mapM_cons, headRun, tailRun']

theorem DataExpr.ofTarget_sound {source fuel value expr}
    (accepted : DataExpr.ofTarget source fuel value = some expr)
    (data : Nat → Data) (input : Nat → Ix.Ixby.Value) (depth : Nat)
    (represented : ∀ i, decodeData source depth (input i) = some (data i)) :
    decodeData source (depth + fuel) (value.instantiate input) =
      some (expr.instantiate data) := by
  induction fuel generalizing value expr with
  | zero => simp [DataExpr.ofTarget] at accepted
  | succ fuel ih =>
      cases value <;> simp only [DataExpr.ofTarget] at accepted
      all_goals try contradiction
      · rename_i index
        cases accepted
        simpa [SymbolicTarget.Value.instantiate, DataExpr.instantiate] using
          decodeData_mono (by omega : depth ≤ depth + (fuel + 1)) (represented index)
      · rename_i id fields
        simp only [SymbolicTarget.Value.instantiate, Nat.add_succ, decodeData,
          Array.size_map, Array.toList_map]
        split at accepted
        · rename_i erased
          split at accepted
          · rename_i empty
            cases accepted
            have emptyFields : fields = #[] := by simpa using empty
            simp [erased, emptyFields, DataExpr.instantiate]
          · contradiction
        · rename_i notErased
          simp only [notErased, Bool.false_eq_true, ↓reduceIte]
          split at accepted
          · rename_i natBox
            simp only [natBox, ↓reduceIte]
            split at accepted
            · rename_i n shape
              cases accepted
              simp [shape, SymbolicTarget.Value.instantiate, DataExpr.instantiate]
            · contradiction
          · rename_i notNat
            simp only [notNat, Bool.false_eq_true, ↓reduceIte]
            split at accepted
            · rename_i strBox
              simp only [strBox, ↓reduceIte]
              split at accepted
              · rename_i s shape
                cases accepted
                simp [shape, SymbolicTarget.Value.instantiate, DataExpr.instantiate]
              · contradiction
            · rename_i notStr
              simp only [notStr, Bool.false_eq_true, ↓reduceIte]
              simp only [Bind.bind, Option.bind_eq_some_iff] at accepted
              obtain ⟨ctor, hc, h⟩ := accepted
              split at h
              · contradiction
              · rename_i arity
                simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
                obtain ⟨terms, ht, rfl⟩ := h
                have mapped := SymbolicData.mapM_transfer (fun _ _ h => ih h) ht
                have arityEq : fields.size = ctor.fields := by simpa using arity
                simp [hc, arityEq, DataExpr.instantiate, List.mapM_map, Function.comp_def,
                  mapped, Bind.bind, Option.bind]

end Compilatrix.Ixby
