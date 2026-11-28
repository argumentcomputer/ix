import IxCC.Cfg.Rc.Proof.State

set_option autoImplicit false
namespace IxCC.Cfg.Rc

theorem EnvSub.trans {a b c : Own.Env} (ab : EnvSub a b) (bc : EnvSub b c) : EnvSub a c :=
  fun x v h => bc x v (ab x v h)

theorem Joins.extend {limit slotBase self lo : Nat} {ctors : List Lam.CtorInfo}
    {B : Cfg.Proof.Blocks} {ρ target : Own.Env}
    {scope : Cfg.Lower.JScope} {saved : List Own.Plain.JEntry}
    (h : Joins limit ctors slotBase B self ρ lo scope saved) (sub : EnvSub ρ target) :
    Joins limit ctors slotBase B self target lo scope saved := by
  induction h with
  | nil => exact .nil
  | cons tail bound params charge layout env below lower bodySlot boundBody upper scopedNames vb rc ih =>
    exact .cons ih bound params charge layout (env.trans sub) below lower bodySlot boundBody upper scopedNames vb rc

theorem At.extend {F : Fir.Program} {P : Program} {fr : Frame} {ρ target : Own.Env}
    {saved : List Own.Plain.JEntry} {code : Own.Plain.Code} {slots : Src.NatMap Own.RVal}
    (h : At F P fr ρ saved code slots) (sub : EnvSub fr.env target) :
    At F P { fr with env := target } ρ saved code slots := by
  obtain ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    env, below, loSlot, slotSub, scopedNames, vb, rc, joins⟩ := h
  exact ⟨fd, scope, params, acc, next, first, lo, slotBase, lookup, range, layout, cursor,
    env.trans sub, below, loSlot, fun s v hs => sub _ _ (slotSub s v hs),
    scopedNames, vb, rc, joins.extend sub⟩


end IxCC.Cfg.Rc
