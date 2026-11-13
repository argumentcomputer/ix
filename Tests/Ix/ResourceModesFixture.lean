set_option Elab.async false
namespace ModeFixture

inductive E | c₀ | c₁ | c₂

/-- A definition of the shape of a `casesOn`: its value is a recursor spine. -/
noncomputable def cases'.{u} (motive : E → Sort u) (t : E) (m₀ : motive E.c₀) (m₁ : motive E.c₁)
    (m₂ : motive E.c₂) : motive t :=
  @E.rec motive m₀ m₁ m₂ t

noncomputable def main : E := cases' (fun _ => E) E.c₁ E.c₀ E.c₂ E.c₁

noncomputable def mainRec : E := @E.rec (fun _ => E) E.c₀ E.c₁ E.c₂ E.c₁

def k (_x y : E) : E := y
def f : E → E → E := k
def callF : E := f E.c₀ E.c₁

def myAdd (_a b : Nat) : Nat := b
def callAdd : Nat := myAdd (nat_lit 2) (nat_lit 3)

def mkQ : Quot (fun (_ _ : E) => True) := Quot.mk _ E.c₁

end ModeFixture
