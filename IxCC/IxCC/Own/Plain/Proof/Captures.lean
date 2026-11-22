import IxCC.Own.Plain.Proof.Environment

/-! Captured environments are borrowed views of already owned root tokens.
Several joins may mention the same root without duplicating its reference
count. The body relation records the exact recursive/nonrecursive join scope
and the separate charged bit used by Fir's first-jump clock discipline. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

structure EntryDen (H : Heap) (owned : List RVal) (captured : List Fir.Var)
    (older : Joins) (ef : Fir.JEntry) (eo : JEntry) : Prop where
  id : eo.id = ef.id
  charged : eo.charged = ef.charged
  params : eo.params = ef.params
  isRec : eo.isRec = ef.isRec
  body : eo.body = lowerCode (captured ++ ef.params)
    (if ef.isRec then (ef.id, captured) :: older else older) ef.body
  env : EnvDen H captured ef.env eo.env
  borrowed : ∃ roots, EnvRoots eo.env captured roots ∧ ∀ v, v ∈ roots → v ∈ owned

theorem EntryDen.transport {H H' : Heap} {owned : List RVal} {captured : List Fir.Var}
    {older : Joins} {ef : Fir.JEntry} {eo : JEntry}
    (h : EntryDen H owned captured older ef eo)
    (hv : ∀ v, v ∈ owned → H.value? v = H'.value? v) :
    EntryDen H' owned captured older ef eo := by
  obtain ⟨roots, hr, hm⟩ := h.borrowed
  exact { h with env := h.env.transport hr (fun v hh => hv v (hm v hh)) }

theorem EntryDen.reframe {H : Heap} {owned owned' : List RVal} {captured : List Fir.Var}
    {older : Joins} {ef : Fir.JEntry} {eo : JEntry}
    (h : EntryDen H owned captured older ef eo)
    (hm : ∀ v, v ∈ owned → v ∈ owned') : EntryDen H owned' captured older ef eo := by
  obtain ⟨roots, hr, hs⟩ := h.borrowed
  exact { h with borrowed := ⟨roots, hr, fun v hh => hm v (hs v hh)⟩ }

theorem EntryDen.charge {H : Heap} {owned : List RVal} {captured : List Fir.Var}
    {older : Joins} {ef : Fir.JEntry} {eo : JEntry}
    (h : EntryDen H owned captured older ef eo) :
    EntryDen H owned captured older { ef with charged := true } { eo with charged := true } :=
  { h with charged := rfl }

inductive StackDen (H : Heap) (owned : List RVal) : Joins → List Fir.JEntry → List JEntry → Prop
  | nil : StackDen H owned [] [] []
  | cons {captured : List Fir.Var} {older : Joins}
      {ef : Fir.JEntry} {eo : JEntry} {jf : List Fir.JEntry} {jo : List JEntry}
      (entry : EntryDen H owned captured older ef eo)
      (rest : StackDen H owned older jf jo) :
      StackDen H owned ((ef.id, captured) :: older) (ef :: jf) (eo :: jo)

theorem StackDen.transport {H H' : Heap} {owned : List RVal} {joins : Joins}
    {jf : List Fir.JEntry} {jo : List JEntry} (h : StackDen H owned joins jf jo)
    (hv : ∀ v, v ∈ owned → H.value? v = H'.value? v) : StackDen H' owned joins jf jo := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (he.transport hv) ih

theorem StackDen.reframe {H : Heap} {owned owned' : List RVal} {joins : Joins}
    {jf : List Fir.JEntry} {jo : List JEntry} (h : StackDen H owned joins jf jo)
    (hm : ∀ v, v ∈ owned → v ∈ owned') : StackDen H owned' joins jf jo := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (he.reframe hm) ih

/-- A declaration borrows the current live roots. There is no increment and
the same owned-root list remains valid for all previously declared entries. -/
theorem entryDen_declare {H : Heap} {owned : List RVal} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} (he : EnvDen H live ρf ρo) (hr : EnvRoots ρo live owned)
    (older : Joins) (j : Fir.JoinId) (ps : List Fir.Var) (rec : Bool) (body : Fir.Code) :
    EntryDen H owned live older
      { id := j, charged := false, env := ρf, params := ps, body, isRec := rec }
      { id := j, charged := false, env := ρo, params := ps
        body := lowerCode (live ++ ps) (if rec then (j, live) :: older else older) body
        isRec := rec } :=
  ⟨rfl, rfl, rfl, rfl, rfl, he, owned, hr, fun _ hm => hm⟩


end IxCC.Own.Plain
