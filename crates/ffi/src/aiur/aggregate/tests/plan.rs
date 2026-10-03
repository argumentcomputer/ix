use super::super::plan::{PlanOp, leaves_under, subtree_plan};

/// A post-order plan from a nested leaf-count shape: `(a, b)` joins the
/// plans of `a` and `b`; a number is that many balanced leaves.
fn plan_of(shape: &str) -> Vec<PlanOp> {
  fn go(chars: &[u8], at: &mut usize, out: &mut Vec<PlanOp>) -> usize {
    if chars[*at] == b'(' {
      *at += 1;
      let left = go(chars, at, out);
      assert_eq!(chars[*at], b',');
      *at += 1;
      let right = go(chars, at, out);
      assert_eq!(chars[*at], b')');
      *at += 1;
      out.push(PlanOp::Join(left, right));
    } else {
      let start = *at;
      while *at < chars.len() && chars[*at].is_ascii_digit() {
        *at += 1;
      }
      let count: usize =
        std::str::from_utf8(&chars[start..*at]).unwrap().parse().unwrap();
      let ids: Vec<u32> = (0..u32::try_from(count).unwrap()).collect();
      fn balanced(ids: &[u32], out: &mut Vec<PlanOp>) -> usize {
        if ids.len() == 1 {
          out.push(PlanOp::Leaf(ids[0] as usize));
        } else {
          let (l, r) = ids.split_at(ids.len() / 2);
          let left = balanced(l, out);
          let right = balanced(r, out);
          out.push(PlanOp::Join(left, right));
        }
        out.len() - 1
      }
      balanced(&ids, out);
    }
    out.len() - 1
  }
  let mut out = Vec::new();
  go(shape.as_bytes(), &mut 0, &mut out);
  out
}

#[test]
fn subtree_plan_cuts_to_the_target_and_lists_the_joins_above() {
  let sizes = |ops: &[PlanOp], slots: &[usize]| -> Vec<usize> {
    let leaves = leaves_under(ops);
    slots.iter().map(|&s| leaves[s]).collect()
  };
  // Balanced: a size of eight keeps the root whole; a size of two cuts
  // to the depth-2 nodes, with the two depth-1 joins and the root above.
  let ops = plan_of("8");
  let (frontier, upper) = subtree_plan(&ops, 8);
  assert_eq!(frontier, vec![ops.len() - 1]);
  assert!(upper.is_empty());
  let (frontier, upper) = subtree_plan(&ops, 2);
  assert_eq!(sizes(&ops, &frontier), vec![2, 2, 2, 2]);
  assert_eq!(upper.len(), 3);
  assert_eq!(*upper.last().unwrap(), ops.len() - 1);
  // Mathlib's 128-way shape at the top: root = (70, 58), 70 = (38, 32),
  // 58 = (32, 26). A size of eight leaves nothing larger than that.
  let ops = plan_of("((38,32),(32,26))");
  let (frontier, upper) = subtree_plan(&ops, 8);
  let leaves = sizes(&ops, &frontier);
  assert_eq!(leaves.iter().sum::<usize>(), 128);
  assert!(leaves.iter().all(|n| (2..=8).contains(n)));
  // Post-order: every upper join comes after its children.
  let position = |slot: usize| upper.iter().position(|&s| s == slot);
  for &slot in &upper {
    let PlanOp::Join(left, right) = ops[slot] else { panic!("join") };
    for child in [left, right] {
      if let Some(at) = position(child) {
        assert!(at < position(slot).unwrap());
      } else {
        assert!(frontier.contains(&child));
      }
    }
  }
  // A lone leaf beside a subtree: the tree (1 + 32) + 16 has 49 leaves;
  // a size of four means the 33-leaf node must be cut even though one of
  // its children is a raw leaf, which then stands as a one-leaf subtree.
  let ops = plan_of("((1,32),16)");
  let (frontier, _) = subtree_plan(&ops, 4);
  let leaves = sizes(&ops, &frontier);
  assert_eq!(leaves.iter().sum::<usize>(), 1 + 32 + 16);
  assert!(leaves.iter().all(|&n| n <= 4));
  assert_eq!(leaves.iter().filter(|&&n| n == 1).count(), 1);
  // A two-leaf tree at size one: two one-leaf subtrees under the root join.
  let ops = plan_of("2");
  let (frontier, upper) = subtree_plan(&ops, 1);
  assert_eq!(sizes(&ops, &frontier), vec![1, 1]);
  assert_eq!(upper, vec![ops.len() - 1]);
}
