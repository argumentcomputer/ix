pub enum BinderInfo {
  Default,
  Implicit,
  StrictImplicit,
  InstImplicit,
  AuxDecl,
}

pub enum ReducibilityHints {
  Opaque,
  Abbrev,
  Regular,
}
