#[derive(serde::Serialize, Clone, Copy, Debug, PartialEq, Eq)]
pub enum Envelope {
  Ordinary,
  SingleBatch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Message<T> {
  pub args: Vec<T>,
  pub multiplicity: T,
}
