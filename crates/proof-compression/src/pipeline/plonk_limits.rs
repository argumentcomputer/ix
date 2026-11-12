//! PLONK domain and SRS requirements without compiling a circuit or loading powers.

/// The domain bound accepted by the gnark interchange and CUDA backend.
pub const MAX_DOMAIN: usize = 1 << 26;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParameterSize {
  domain: usize,
  opening_powers: usize,
  loaded_powers: usize,
}

impl ParameterSize {
  pub const fn domain(self) -> usize {
    self.domain
  }

  /// Gnark's opening polynomials need three powers beyond the circuit domain.
  pub const fn opening_powers(self) -> usize {
    self.opening_powers
  }

  /// The current Rust SRS loader accepts only power-of-two prefixes.
  pub const fn loaded_powers(self) -> usize {
    self.loaded_powers
  }

  pub fn for_circuit(
    constraints: usize,
    public_inputs: usize,
  ) -> Result<Self, String> {
    if constraints == 0 {
      return Err("PLONK circuit must contain a constraint".into());
    }
    let domain = constraints
      .checked_add(public_inputs)
      .and_then(usize::checked_next_power_of_two)
      .ok_or("PLONK circuit domain overflow")?;
    Self::for_domain(domain)
  }

  pub fn for_domain(domain: usize) -> Result<Self, String> {
    if !(2..=MAX_DOMAIN).contains(&domain) || !domain.is_power_of_two() {
      return Err(format!(
        "PLONK domain must be a power of two in [2, {MAX_DOMAIN}]"
      ));
    }
    let opening_powers = domain.checked_add(3).ok_or("PLONK SRS overflow")?;
    let loaded_powers = opening_powers
      .checked_next_power_of_two()
      .ok_or("PLONK SRS prefix overflow")?;
    Ok(Self { domain, opening_powers, loaded_powers })
  }

  /// `available_powers` is the retained file prefix; `public_max_degree`
  /// comes from the independently admitted verifier parameters. Neither may
  /// be inferred from a requested circuit size.
  pub fn check_capacity(
    self,
    available_powers: usize,
    public_max_degree: usize,
  ) -> Result<(), String> {
    self.check_public_degree(public_max_degree)?;
    if self.loaded_powers > available_powers {
      return Err(format!(
        "PLONK domain {} needs {} opening powers and a {}-power prefix with the current loader, but the SRS retains {} powers",
        self.domain, self.opening_powers, self.loaded_powers, available_powers
      ));
    }
    Ok(())
  }

  pub fn check_public_degree(
    self,
    public_max_degree: usize,
  ) -> Result<(), String> {
    if self.loaded_powers - 1 > public_max_degree {
      return Err(format!(
        "PLONK domain {} needs {} opening powers and a {}-power prefix with the current loader, exceeding admitted maximum degree {}",
        self.domain, self.opening_powers, self.loaded_powers, public_max_degree
      ));
    }
    Ok(())
  }
}

/// Largest domain the current power-of-two prefix loader can serve. This can
/// be smaller than the domain allowed by the protocol's `N + 3` requirement.
pub fn maximum_domain(
  available_powers: usize,
  public_max_degree: usize,
) -> Option<usize> {
  let mut domain = MAX_DOMAIN;
  while domain >= 2 {
    if ParameterSize::for_domain(domain)
      .expect("bounded power of two")
      .check_capacity(available_powers, public_max_degree)
      .is_ok()
    {
      return Some(domain);
    }
    domain /= 2;
  }
  None
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn current_ignition_prefix_caps_constraints_below_two_to_25() {
    let retained = 1 << 26;
    let ceremony_degree = 100_800_000 - 1;
    let maximum = maximum_domain(retained, ceremony_degree).unwrap();
    assert_eq!(maximum, 1 << 25);
    let last = ParameterSize::for_circuit(maximum - 2, 2).unwrap();
    assert_eq!(last.domain, maximum);
    assert!(last.check_capacity(retained, ceremony_degree).is_ok());
    let next = ParameterSize::for_circuit(maximum - 1, 2).unwrap();
    assert_eq!(next.domain, 1 << 26);
    assert_eq!(next.opening_powers, (1 << 26) + 3);
    assert_eq!(next.loaded_powers, 1 << 27);
    assert!(next.check_capacity(retained, ceremony_degree).is_err());
  }

  #[test]
  fn full_ceremony_does_not_remove_loader_rounding_limit() {
    let powers = 100_800_000;
    let size = ParameterSize::for_domain(1 << 26).unwrap();
    assert!(size.opening_powers <= powers);
    assert!(size.check_capacity(powers, powers - 1).is_err());
    assert_eq!(maximum_domain(powers, powers - 1), Some(1 << 25));
  }

  #[test]
  fn retained_and_admitted_limits_are_checked_independently() {
    let size = ParameterSize::for_domain(16).unwrap();
    assert_eq!(size.opening_powers, 19);
    assert_eq!(size.loaded_powers, 32);
    assert!(size.check_capacity(32, 31).is_ok());
    assert!(size.check_capacity(31, 100).is_err());
    assert!(size.check_capacity(100, 30).is_err());
    assert_eq!(maximum_domain(7, usize::MAX), None);
    assert_eq!(maximum_domain(8, 7), Some(4));
  }

  #[test]
  fn rejects_bad_domains_and_overflow_before_allocation() {
    for domain in [0, 1, 3, MAX_DOMAIN + 1, usize::MAX] {
      assert!(ParameterSize::for_domain(domain).is_err());
    }
    assert!(ParameterSize::for_circuit(0, 2).is_err());
    assert!(ParameterSize::for_circuit(usize::MAX, 2).is_err());
    assert!(ParameterSize::for_circuit(MAX_DOMAIN - 1, 2).is_err());
    assert!(ParameterSize::for_circuit(MAX_DOMAIN - 2, 2).is_ok());
  }
}
