use rustc_hash::{FxHashMap, FxHashSet};

use crate::FxIndexMap;

use super::bytecode::{Block, Ctrl, Function};
use super::layout::compute_layout;

impl Function {
  pub fn return_groups(&self) -> FxHashSet<String> {
    let mut groups = FxHashSet::default();
    collect_block(&self.body, &mut groups);
    groups
  }

  /// Build a `Function` containing only the control-flow paths that can reach a
  /// `Ctrl::Return` whose group matches `target`. Returns `None` when no such
  /// path exists. `Yield` branches are preserved unconditionally — their
  /// reachability is decided by the surrounding `MatchContinue`'s continuation.
  pub fn filter_group(&self, target: &str) -> Option<Function> {
    let body = filter_block(&self.body, target)?;
    Some(Function {
      body,
      layout: self.layout,
      entry: self.entry,
      constrained: self.constrained,
    })
  }

  /// Renumber selectors in traversal order and recompute the circuit layout.
  /// Intended for functions produced by `filter_group`, whose selector indices
  /// and layout are inherited from the original (pre-filter) function.
  fn fix(mut self) -> Self {
    let mut counter: usize = 0;
    fix_block_sel(&mut self.body, &mut counter);
    self.layout = compute_layout(&self);
    self
  }

  pub fn split(&self) -> FxHashMap<String, Function> {
    self
      .return_groups()
      .into_iter()
      .map(|group| {
        let filtered = self.filter_group(&group).unwrap_or_else(|| {
          panic!("function contains an unreachable group: {group}")
        });
        (group, filtered.fix())
      })
      .collect()
  }
}

fn filter_block(block: &Block, target: &str) -> Option<Block> {
  let ctrl = filter_ctrl(&block.ctrl, target)?;
  Some(Block { ops: block.ops.clone(), ctrl })
}

fn filter_ctrl(ctrl: &Ctrl, target: &str) -> Option<Ctrl> {
  match ctrl {
    Ctrl::Return(sel, group, vs) => {
      if group == target {
        Some(Ctrl::Return(*sel, group.clone(), vs.clone()))
      } else {
        None
      }
    },
    Ctrl::Yield(sel, vs) => Some(Ctrl::Yield(*sel, vs.clone())),
    Ctrl::Match(scrut, cases, default) => {
      let new_cases = filter_cases(cases, target);
      let new_default =
        default.as_ref().and_then(|b| filter_block(b, target).map(Box::new));
      if new_cases.is_empty() && new_default.is_none() {
        None
      } else {
        Some(Ctrl::Match(*scrut, new_cases, new_default))
      }
    },
    Ctrl::MatchContinue(
      scrut,
      cases,
      default,
      output_size,
      shared_aux,
      shared_lookups,
      cont,
    ) => {
      let new_cont = filter_block(cont, target)?;
      let new_cases = filter_cases(cases, target);
      let new_default =
        default.as_ref().and_then(|b| filter_block(b, target).map(Box::new));
      if new_cases.is_empty() && new_default.is_none() {
        None
      } else {
        Some(Ctrl::MatchContinue(
          *scrut,
          new_cases,
          new_default,
          *output_size,
          *shared_aux,
          *shared_lookups,
          Box::new(new_cont),
        ))
      }
    },
  }
}

fn fix_block_sel(block: &mut Block, counter: &mut usize) {
  fix_ctrl_sel(&mut block.ctrl, counter);
}

fn fix_ctrl_sel(ctrl: &mut Ctrl, counter: &mut usize) {
  match ctrl {
    Ctrl::Return(sel, _, _) | Ctrl::Yield(sel, _) => {
      *sel = *counter;
      *counter += 1;
    },
    Ctrl::Match(_, cases, default) => {
      for branch in cases.values_mut() {
        fix_block_sel(branch, counter);
      }
      if let Some(branch) = default {
        fix_block_sel(branch, counter);
      }
    },
    Ctrl::MatchContinue(_, cases, default, _, _, _, cont) => {
      for branch in cases.values_mut() {
        fix_block_sel(branch, counter);
      }
      if let Some(branch) = default {
        fix_block_sel(branch, counter);
      }
      fix_block_sel(cont, counter);
    },
  }
}

fn filter_cases(
  cases: &FxIndexMap<crate::aiur::G, Block>,
  target: &str,
) -> FxIndexMap<crate::aiur::G, Block> {
  let mut new_cases = FxIndexMap::default();
  for (&k, blk) in cases {
    if let Some(b) = filter_block(blk, target) {
      new_cases.insert(k, b);
    }
  }
  new_cases
}

fn collect_block(block: &Block, groups: &mut FxHashSet<String>) {
  collect_ctrl(&block.ctrl, groups);
}

fn collect_ctrl(ctrl: &Ctrl, groups: &mut FxHashSet<String>) {
  match ctrl {
    Ctrl::Return(_, group, _) => {
      groups.insert(group.clone());
    },
    Ctrl::Yield(..) => {},
    Ctrl::Match(_, cases, default) => {
      for branch in cases.values() {
        collect_block(branch, groups);
      }
      if let Some(branch) = default {
        collect_block(branch, groups);
      }
    },
    Ctrl::MatchContinue(_, cases, default, _, _, _, cont) => {
      for branch in cases.values() {
        collect_block(branch, groups);
      }
      if let Some(branch) = default {
        collect_block(branch, groups);
      }
      collect_block(cont, groups);
    },
  }
}
