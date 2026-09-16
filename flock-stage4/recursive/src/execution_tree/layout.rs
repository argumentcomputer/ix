use anyhow::{Result, ensure};
use ixby_flock::ixby::ixbf_decode::paged::endpoints::{
  Component, FACT_WORDS, PUBLIC_WORDS,
};

/// Layouts come only from the approved compiler, never a proof envelope.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Layout {
  Component(Component),
  Facts { first: usize, end: usize },
  Endpoints,
  Execution,
}
impl Layout {
  pub(super) fn width(self) -> usize {
    match self {
      Self::Component(c) => c.range().len(),
      Self::Facts { first, end } => {
        Component::ALL[first..end].iter().map(|c| c.range().len()).sum()
      },
      Self::Endpoints => PUBLIC_WORDS,
      Self::Execution => 2,
    }
  }
  fn range(self) -> Option<std::ops::Range<usize>> {
    match self {
      Self::Component(c) => Some(c as usize..c as usize + 1),
      Self::Facts { first, end } => Some(first..end),
      _ => None,
    }
  }
  pub(super) fn encode(self) -> Vec<u8> {
    match self {
      Self::Component(c) => vec![0, c as u8],
      Self::Facts { first, end } => {
        vec![1, u8::try_from(first).unwrap(), u8::try_from(end).unwrap()]
      },
      Self::Endpoints => vec![2],
      Self::Execution => vec![3],
    }
  }
}
/// Shared fields, followed by two complete boundary records.
pub(super) fn chain(c: Component) -> Option<(usize, usize)> {
  use Component::*;
  Some(match c {
    ProgramBytes | InputBytes => (3, 3),
    CodeCapture => (3, 39),
    References => (5, 3),
    InputCapture => (3, 37),
    Execution => (3, 27),
    OutputBytes | ProgramCommitment | InputCommitment | OutputCommitment => {
      (7, 1)
    },
    ConstructorIds => return None,
  })
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Relation {
  Chain,
  Concat,
  Close,
}
impl Relation {
  pub(super) fn layout(self, left: Layout, right: Layout) -> Result<Layout> {
    Ok(match self {
      Self::Chain => {
        ensure!(left == right, "component chain layouts differ");
        let Layout::Component(c) = left else {
          anyhow::bail!("chain is not a component")
        };
        ensure!(chain(c).is_some(), "component is not batchable");
        left
      },
      Self::Concat => {
        let a =
          left.range().ok_or_else(|| anyhow::anyhow!("left facts layout"))?;
        let b =
          right.range().ok_or_else(|| anyhow::anyhow!("right facts layout"))?;
        ensure!(
          a.end == b.start,
          "component facts are not adjacent in protocol order"
        );
        Layout::Facts { first: a.start, end: b.end }
      },
      Self::Close => {
        ensure!(
          left == (Layout::Facts { first: 0, end: 11 })
            && right == Layout::Endpoints,
          "closing relation requires every component and its endpoints"
        );
        ensure!(left.width() == FACT_WORDS, "complete facts width");
        Layout::Execution
      },
    })
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn component_layouts_and_closing_order_are_protocol_owned() {
    let mut joined = Layout::Component(Component::ALL[0]);
    for (i, c) in Component::ALL.into_iter().enumerate() {
      let l = Layout::Component(c);
      assert_eq!(l.width(), c.range().len());
      if let Some((shared, boundary)) = chain(c) {
        assert_eq!(shared + 2 * boundary, l.width());
        assert_eq!(Relation::Chain.layout(l, l).unwrap(), l);
      } else {
        assert!(Relation::Chain.layout(l, l).is_err());
      }
      if i > 0 {
        joined = Relation::Concat.layout(joined, l).unwrap();
      }
      assert!(Relation::Close.layout(l, Layout::Endpoints).is_err());
      assert!(Relation::Concat.layout(l, l).is_err());
    }
    assert_eq!(joined.width(), FACT_WORDS);
    assert_eq!(
      Relation::Close.layout(joined, Layout::Endpoints).unwrap().width(),
      2
    );
    assert!(Relation::Close.layout(Layout::Endpoints, joined).is_err());
  }
}
