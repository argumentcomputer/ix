import Aiur.Modules.Function

/-! Imported DSL declarations: no function constants exist until assembly. -/
namespace FunctionModuleTests

aiur_module Data where
aiur_decls⟦
module Data {
  enum Cell<T> { Mk(T) }
  type Word = Field;
}
⟧
def identity := aiur_fn⟦
  inline fn identity<T>(x: T) -> T { x }
⟧
def read := aiur_fn⟦
  fn read(c: Cell<Word>) -> Word {
    let Cell::Mk(x) = c;
    identity(x)
  }
⟧
def even := aiur_fn⟦
  fn even(n: Field) -> Field {
    match n { 0 => { 1 }, _ => { Other::odd(n - 1) } }
  }
⟧
end

end FunctionModuleTests
