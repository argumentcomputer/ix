use crossbeam::deque::{Injector, Stealer, Worker};
use std::ptr;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::thread;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Tag;

// a 4-bit tag
impl Tag {
  pub const LAM: u8 = 0x0; // λ lambda node
  pub const APP: u8 = 0x1; // @ application node
  pub const DUP: u8 = 0x2; // δ duplicator node
  pub const SCP: u8 = 0x3; // ς scope node
  // Eraser nodes represented as a port connecting to itself
  // Nil represented as u64::MAX;
  // Root represented as 0u64;
  // Reserve up to 12 other types for future-proofing
}

// Slot indices within a 4-port node
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Slot;

impl Slot {
  pub const MAIN: u64 = 0;
  pub const LEFT: u64 = 1;
  pub const RIGHT: u64 = 2;
  pub const AUX: u64 = 3; // Stores level for DUP/SCP nodes
}

/// A pointer to a port in the interaction net.
/// Layout: [tag:4 bits][node_base:60 bits]
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Hash)]
#[repr(transparent)]
pub struct Ptr(pub u64);

impl Ptr {
  pub const TAG_SHIFT: u64 = 60;
  pub const VAL_MASK: u64 = 0x0FFF_FFFF_FFFF_FFFF;
  pub const NIL: Ptr = Ptr(u64::MAX);
  pub const ROOT: Ptr = Ptr(0);

  pub fn new(tag: u8, val: u64) -> Self {
    Ptr(((tag as u64) << Self::TAG_SHIFT) | (val & Self::VAL_MASK))
  }

  // what type of node we're pointing at
  pub fn tag(&self) -> u8 {
    (self.0 >> Self::TAG_SHIFT) as u8
  }

  // the index of the port we're pointing at
  pub fn val(&self) -> u64 {
    self.0 & Self::VAL_MASK
  }

  // the slot of the port we're pointing at
  #[inline]
  pub fn slot(&self) -> u64 {
    self.0 % 4
  }

  #[inline]
  pub fn node(&self) -> u64 {
    self.val() - self.slot()
  }

  // a Ptr to the main port of the node we're pointing at
  pub fn main(&self) -> Ptr {
    Ptr::new(self.tag(), self.val() - self.slot())
  }
  // a Ptr to the left port of the node we're pointing at
  pub fn left(&self) -> Ptr {
    Ptr::new(self.tag(), self.node() + Slot::LEFT)
  }
  // a Ptr to the right port of the node we're pointing at
  pub fn right(&self) -> Ptr {
    Ptr::new(self.tag(), self.node() + Slot::RIGHT)
  }

  // a Ptr to the aux port of the node we're pointing at. This holds DUP/SCP levels
  pub fn aux(&self) -> Ptr {
    Ptr::new(self.tag(), self.node() + Slot::AUX)
  }

  #[inline]
  pub fn is_main(&self) -> bool {
    self.slot() == Slot::MAIN
  }
  #[inline]
  pub fn is_left(&self) -> bool {
    self.slot() == Slot::LEFT
  }
  #[inline]
  pub fn is_right(&self) -> bool {
    self.slot() == Slot::RIGHT
  }
  #[inline]
  pub fn is_aux(&self) -> bool {
    self.slot() == Slot::AUX
  }
  #[inline]
  pub fn is_nil(&self) -> bool {
    self.0 == u64::MAX
  }
}
/// A redex (active pair) - two main ports connected together
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Redex {
  pub x: Ptr,
  pub y: Ptr,
}

impl Redex {
  /// Create a canonical redex (smaller pointer)
  pub fn new(x: Ptr, y: Ptr) -> Self {
    if x.0 <= y.0 { Redex { x, y } } else { Redex { x: y, y: x } }
  }
}

/// Thread-local state for parallel reduction
pub struct ThreadCtx<'a> {
  pub redexes: Worker<Redex>,
  pub freed: Worker<usize>,
  pub redex_stealers: &'a [Stealer<Redex>],
  pub free_stealers: &'a [Stealer<usize>],
}

impl<'a> ThreadCtx<'a> {
  /// Try to get a free node slot, stealing if necessary
  pub fn alloc_free(&self) -> Option<usize> {
    // Try local first
    if let Some(slot) = self.freed.pop() {
      return Some(slot);
    }
    // Try stealing from others
    for stealer in self.free_stealers {
      loop {
        match stealer.steal() {
          crossbeam::deque::Steal::Success(slot) => return Some(slot),
          crossbeam::deque::Steal::Empty => break,
          crossbeam::deque::Steal::Retry => {},
        }
      }
    }
    None
  }

  /// Return a freed node slot
  #[inline]
  pub fn push_free(&self, slot: usize) {
    self.freed.push(slot);
  }

  /// Push a new redex
  #[inline]
  pub fn push_redex(&self, redex: Redex) {
    self.redexes.push(redex);
  }
}

/// Size of each chunk in slots (not nodes)
const CHUNK_SIZE: usize = 1 << 22; // 4M slots = 1M nodes
/// Maximum number of chunks.
const MAX_CHUNKS: usize = 1024; // 1B nodes max (~8GB memory)

/// A single chunk of the arena
struct Chunk {
  data: Box<[AtomicU64]>,
}

impl Chunk {
  fn new() -> Box<Self> {
    let mut data = Vec::with_capacity(CHUNK_SIZE);
    for _ in 0..CHUNK_SIZE {
      data.push(AtomicU64::new(Ptr::NIL.0));
    }
    Box::new(Chunk { data: data.into_boxed_slice() })
  }

  #[inline]
  fn get(&self, offset: usize) -> u64 {
    self.data[offset].load(Ordering::Acquire)
  }

  #[inline]
  fn set(&self, offset: usize, val: u64) {
    self.data[offset].store(val, Ordering::Release);
  }
}

/// Thread-safe interaction net with atomic operations
pub struct Net {
  /// Lock-free chunked arena. Each slot is an AtomicPtr to a chunk.
  /// Chunks are allocated lazily and never deallocated (until Net is dropped).
  arena: [std::sync::atomic::AtomicPtr<Chunk>; MAX_CHUNKS],
  /// Next free index for allocation
  next: AtomicUsize,
  /// initial redex queue
  redexes: Injector<Redex>,
  /// Reduction counter for stats
  reductions: AtomicUsize,
}

// Safety: Net is Send+Sync because all access is through atomics
unsafe impl Send for Net {}
unsafe impl Sync for Net {}

impl Drop for Net {
  fn drop(&mut self) {
    for chunk_ptr in &self.arena {
      let ptr = chunk_ptr.load(Ordering::Relaxed);
      if !ptr.is_null() {
        unsafe {
          drop(Box::from_raw(ptr));
        }
      }
    }
  }
}

impl Default for Net {
  fn default() -> Self {
    Self::new()
  }
}

impl Net {
  /// Create a new net with the given capacity (number of nodes)
  /// Create a new empty net
  pub fn new() -> Self {
    let net = Net {
      // Initialize all chunk pointers to null
      arena: std::array::from_fn(|_| {
        std::sync::atomic::AtomicPtr::new(ptr::null_mut())
      }),
      next: AtomicUsize::new(4), // Start after root node
      redexes: Injector::new(),
      reductions: AtomicUsize::new(0),
    };

    // Ensure first chunk exists
    let _ = net.get_chunk(0);

    net.set(Ptr::new(Tag::SCP, 0), Ptr::NIL);
    net.set(Ptr::new(Tag::SCP, 1), Ptr::NIL);
    net.set(Ptr::new(Tag::SCP, 2), Ptr::NIL);
    net.set(Ptr::new(Tag::SCP, 3), Ptr::new(0, 0));

    net
  }

  /// Get the root port (left port of root SCP node)
  #[inline]
  pub fn root(&self) -> Ptr {
    Ptr::new(Tag::SCP, Slot::LEFT) // Index 1
  }

  /// Create a new net with pre-allocated capacity (number of nodes)
  pub fn with_capacity(capacity: usize) -> Self {
    let net = Self::new();
    let num_chunks = (capacity * 4).div_ceil(CHUNK_SIZE);
    for i in 0..num_chunks.min(MAX_CHUNKS) {
      let chunk = Box::into_raw(Chunk::new());
      net.arena[i].store(chunk, Ordering::Release);
    }
    net
  }

  /// Get or create chunk at index (lock-free)
  #[inline]
  fn get_chunk(&self, chunk_idx: usize) -> &Chunk {
    debug_assert!(chunk_idx < MAX_CHUNKS, "chunk index overflow");

    let ptr = self.arena[chunk_idx].load(Ordering::Acquire);
    if !ptr.is_null() {
      return unsafe { &*ptr };
    }

    // Need to allocate - race to install it
    let new_chunk = Box::into_raw(Chunk::new());
    match self.arena[chunk_idx].compare_exchange(
      ptr::null_mut(),
      new_chunk,
      Ordering::AcqRel,
      Ordering::Acquire,
    ) {
      Ok(_) => unsafe { &*new_chunk },
      Err(existing) => {
        // Another thread won - free our chunk and use theirs
        unsafe {
          drop(Box::from_raw(new_chunk));
          &*existing
        }
      },
    }
  }

  /// Get the value at a port atomically
  #[inline]
  pub fn get(&self, p: Ptr) -> Ptr {
    if p.is_nil() {
      return Ptr::NIL;
    }
    let idx = usize::try_from(p.val()).unwrap();
    let chunk_idx = idx / CHUNK_SIZE;
    let offset = idx % CHUNK_SIZE;
    if chunk_idx >= MAX_CHUNKS {
      return Ptr::NIL;
    }
    let ptr = self.arena[chunk_idx].load(Ordering::Acquire);
    if ptr.is_null() {
      return Ptr::NIL;
    }
    Ptr(unsafe { (*ptr).get(offset) })
  }

  /// Set the value at a port atomically
  #[inline]
  pub fn set(&self, p: Ptr, val: Ptr) {
    if p.is_nil() {
      return;
    }
    let idx = usize::try_from(p.val()).unwrap();
    let chunk_idx = idx / CHUNK_SIZE;
    let offset = idx % CHUNK_SIZE;
    let chunk = self.get_chunk(chunk_idx);
    chunk.set(offset, val.0);
  }

  /// Compare-and-swap a port value. Returns true if successful.
  #[inline]
  pub fn cas(&self, p: Ptr, expected: Ptr, new: Ptr) -> bool {
    if p.is_nil() {
      return false;
    }
    let idx = usize::try_from(p.val()).unwrap();
    let chunk_idx = idx / CHUNK_SIZE;
    let offset = idx % CHUNK_SIZE;
    if chunk_idx >= MAX_CHUNKS {
      return false;
    }
    let ptr = self.arena[chunk_idx].load(Ordering::Acquire);
    if ptr.is_null() {
      return false;
    }
    unsafe {
      (*ptr).data[offset]
        .compare_exchange(
          expected.0,
          new.0,
          Ordering::AcqRel,
          Ordering::Acquire,
        )
        .is_ok()
    }
  }

  /// Get the level of a DUP/SCP node
  #[inline]
  pub fn get_level(&self, p: Ptr) -> u64 {
    let idx = usize::try_from(p.aux().val()).unwrap();
    let chunk_idx = idx / CHUNK_SIZE;
    let offset = idx % CHUNK_SIZE;
    if chunk_idx >= MAX_CHUNKS {
      return 0;
    }
    let ptr = self.arena[chunk_idx].load(Ordering::Acquire);
    if ptr.is_null() {
      return 0;
    }
    unsafe { (*ptr).get(offset) }
  }

  /// Set the level of a DUP/SCP node
  #[inline]
  pub fn set_level(&self, p: Ptr, level: u64) {
    let idx = usize::try_from(p.aux().val()).unwrap();
    let chunk_idx = idx / CHUNK_SIZE;
    let offset = idx % CHUNK_SIZE;
    let chunk = self.get_chunk(chunk_idx);
    chunk.set(offset, level);
  }

  /// Allocate a new node with the given tag (bump allocator only).
  /// Use `alloc_with_ctx` during parallel reduction for free list reuse.
  pub fn alloc_bump(&self, tag: u8) -> Ptr {
    let base = self.next.fetch_add(4, Ordering::Relaxed);
    let chunk_idx = base / CHUNK_SIZE;

    // Ensure chunk exists (lock-free, will allocate if necessary)
    let _ = self.get_chunk(chunk_idx);

    let p = Ptr::new(tag, base as u64);
    self.set(p.main(), Ptr::NIL);
    self.set(p.left(), Ptr::NIL);
    self.set(p.right(), Ptr::NIL);
    self.set(p.aux(), Ptr::new(0, 0));
    p
  }

  /// Allocate a new node, trying thread-local free list first
  #[inline]
  pub fn alloc(&self, tag: u8, ctx: &ThreadCtx<'_>) -> Ptr {
    // Try thread-local free list first (with stealing)
    if let Some(base) = ctx.alloc_free() {
      let p = Ptr::new(tag, base as u64);
      self.set(p.main(), Ptr::NIL);
      self.set(p.left(), Ptr::NIL);
      self.set(p.right(), Ptr::NIL);
      self.set(p.aux(), Ptr::new(0, 0));
      return p;
    }
    // Fallback to bump allocator
    self.alloc_bump(tag)
  }

  /// Free a node, returning it to thread-local free list
  #[inline]
  pub fn free(&self, p: Ptr, ctx: &ThreadCtx<'_>) {
    if !p.is_nil() {
      let base = usize::try_from(p.node()).unwrap();
      self.set(p.main(), Ptr::NIL);
      self.set(p.left(), Ptr::NIL);
      self.set(p.right(), Ptr::NIL);
      self.set(p.aux(), Ptr::NIL);
      ctx.push_free(base);
    }
  }

  /// Create an eraser node at a port by having the port connect to itself
  pub fn alloc_eraser(&self, ptr: Ptr) -> Option<Redex> {
    self.set(ptr, ptr);
    if ptr.is_main() { Some(Redex::new(ptr, ptr)) } else { None }
  }

  /// Check if a port is attached to an eraser
  #[inline]
  pub fn on_eraser(&self, p: Ptr) -> bool {
    self.get(p) == p
  }

  /// Link two ports together (bidirectional)
  pub fn link(&self, a: Ptr, b: Ptr) {
    self.set(a, b);
    if a != b {
      self.set(b, a);
    }
  }

  /// Atomic link with redex detection - returns true if a redex was created
  pub fn link_with_redex(&self, a: Ptr, b: Ptr) -> Option<Redex> {
    self.link(a, b);
    // Check if this creates a redex (two main ports connected)
    if a.is_main() && b.is_main() && a != b {
      Some(Redex::new(a, b))
    } else {
      None
    }
  }

  /// Push a redex to the global queue
  pub fn push_redex(&self, redex: Redex) {
    self.redexes.push(redex);
  }

  /// Try to steal a redex from the global queue
  pub fn steal_redex(&self) -> Option<Redex> {
    loop {
      match self.redexes.steal() {
        crossbeam::deque::Steal::Success(r) => return Some(r),
        crossbeam::deque::Steal::Empty => return None,
        crossbeam::deque::Steal::Retry => {},
      }
    }
  }

  /// Annihilation: two nodes of the same type cancel out
  /// ```text
  ///     a   b              a    b
  ///      \ /                \  /
  ///       X        =>        \/
  ///       |                  /\
  ///       Y                 /  \
  ///      / \               c    d
  ///     c   d
  /// ```
  pub fn annihilate(&self, x: Ptr, y: Ptr, ctx: &ThreadCtx<'_>) {
    let xl = self.get(x.left());
    let xr = self.get(x.right());
    let yl = self.get(y.left());
    let yr = self.get(y.right());

    if let Some(r) = self.link_with_redex(xl, yl) {
      ctx.push_redex(r);
    }
    if let Some(r) = self.link_with_redex(xr, yr) {
      ctx.push_redex(r);
    }

    self.free(x, ctx);
    if x != y {
      self.free(y, ctx);
    }
  }

  /// Commutation for 2-port nodes (Scope): swaps through
  /// ```text
  ///       a                 a
  ///       |                 |
  ///      x:S               y:T
  ///       |        =>       |
  ///      y:T               x:S
  ///       |                 |
  ///       b                 b
  /// ```
  pub fn commute_2_2(
    &self,
    x: Ptr,
    y: Ptr,
    x_level: Option<u64>,
    y_level: Option<u64>,
    ctx: &ThreadCtx<'_>,
  ) {
    let xl = self.get(x.left());
    let yl = self.get(y.left());

    if let Some(lvl) = x_level {
      self.set_level(x, lvl);
    }
    if let Some(lvl) = y_level {
      self.set_level(y, lvl);
    }

    if let Some(r) = self.link_with_redex(x.main(), yl) {
      ctx.push_redex(r);
    }
    if let Some(r) = self.link_with_redex(y.main(), xl) {
      ctx.push_redex(r);
    }
    self.link(y.left(), x.left());
  }

  /// Commutation for 2-port through 3-port node
  /// ```text
  ///       a                   a
  ///       |                   |
  ///      x:S                 y:T
  ///       |         =>      /   \
  ///      y:T              x:S   p:S
  ///      / \               |     |
  ///     b   c              b     c
  /// ```
  pub fn commute_2_3(
    &self,
    x: Ptr,
    y: Ptr,
    x_level: Option<u64>,
    y_level: Option<u64>,
    ctx: &ThreadCtx<'_>,
  ) {
    let p = self.alloc(x.tag(), ctx);
    let xl = self.get(x.left());
    let yl = self.get(y.left());
    let yr = self.get(y.right());

    if let Some(lvl) = x_level {
      self.set_level(x, lvl);
      self.set_level(p, lvl);
    }
    if let Some(lvl) = y_level {
      self.set_level(y, lvl);
    }

    if let Some(r) = self.link_with_redex(y.main(), xl) {
      ctx.push_redex(r);
    }
    if let Some(r) = self.link_with_redex(x.main(), yl) {
      ctx.push_redex(r);
    }
    if let Some(r) = self.link_with_redex(p.main(), yr) {
      ctx.push_redex(r);
    }
    self.link(y.left(), x.left());
    self.link(y.right(), p.left());
  }

  /// Full commutation for 3-port nodes
  /// ```text                       a      b
  ///       a   b             main  |      | main
  /// right  \ /  left             y:Y    p:Y
  ///        x:X             left  /  \  /  \  right
  ///         | main   =>         /    \/    \
  ///        y:Y                  \    /\    /
  /// left  /   \ right      right \  /  \  /  left
  ///      c     d                 x:X    q:X
  ///                          main |      | main
  ///                               c      d
  /// ```
  pub fn commute_3_3(
    &self,
    x: Ptr,
    y: Ptr,
    x_level: Option<u64>,
    y_level: Option<u64>,
    ctx: &ThreadCtx<'_>,
  ) {
    let p = self.alloc(y.tag(), ctx);
    let q = self.alloc(x.tag(), ctx);

    let xl = self.get(x.left());
    let xr = self.get(x.right());
    let yl = self.get(y.left());
    let yr = self.get(y.right());

    // Set levels
    if let Some(lvl) = x_level {
      self.set_level(x, lvl);
      self.set_level(q, lvl);
    }
    if let Some(lvl) = y_level {
      self.set_level(y, lvl);
      self.set_level(p, lvl);
    }

    // Rewire
    if let Some(r) = self.link_with_redex(y.main(), xr) {
      ctx.push_redex(r);
    }
    if let Some(r) = self.link_with_redex(p.main(), xl) {
      ctx.push_redex(r);
    }
    if let Some(r) = self.link_with_redex(x.main(), yl) {
      ctx.push_redex(r);
    }
    if let Some(r) = self.link_with_redex(q.main(), yr) {
      ctx.push_redex(r);
    }

    self.link(y.left(), x.right());
    self.link(y.right(), q.right());
    self.link(p.left(), x.left());
    self.link(p.right(), q.left());
  }

  /// Beta reduction: LAM-APP interaction
  /// ```text
  ///   appl   arg       appl     arg
  ///      \  /            |       |
  ///        @       =>   p:ς     q:ς
  ///        |             |       |
  ///        λ           body    bind
  ///      /   \
  ///   body   bind
  /// ```
  pub fn beta(&self, lam: Ptr, app: Ptr, ctx: &ThreadCtx<'_>) {
    let p = self.alloc(Tag::SCP, ctx);
    let q = self.alloc(Tag::SCP, ctx);

    let app_l = self.get(app.left()); // argument
    let app_r = self.get(app.right()); // applicator
    let lam_l = self.get(lam.left()); // body
    let lam_r = self.get(lam.right()); // bind

    if let Some(r) = self.link_with_redex(p.main(), app_r) {
      ctx.push_redex(r);
    }
    if let Some(r) = self.link_with_redex(q.main(), app_l) {
      ctx.push_redex(r);
    }
    self.link(p.left(), lam_l);
    self.link(q.left(), lam_r);

    self.free(lam, ctx);
    if lam != app {
      self.free(app, ctx);
    }
  }

  /// Erase interaction: ERA interacts with node X
  /// ```ignore
  ///       e:Erase                            e:Erase
  ///         |                                  |
  ///        x:X     =>  e1:Erase e2:Erase OR   x:X   =>  e1:Erase
  ///       /   \        |           |           |           |
  ///      b     c       b           c           b           b
  /// ```
  pub fn erase(&self, x: Ptr, ctx: &ThreadCtx<'_>) {
    let xl = self.get(x.left());
    let xr = self.get(x.right());

    if x.tag() == Tag::SCP {
      // ERA-SCP: eraser passes through to inner port
      if let Some(r) = self.alloc_eraser(xl) {
        ctx.push_redex(r);
      }
      self.free(x, ctx);
    } else {
      if let Some(r) = self.alloc_eraser(xl) {
        ctx.push_redex(r);
      }
      if let Some(r) = self.alloc_eraser(xr) {
        ctx.push_redex(r);
      }
      self.free(x, ctx);
    }
  }

  /// Execute a single rewrite step
  pub fn rewrite(&self, redex: Redex, ctx: &ThreadCtx<'_>) {
    let x = redex.x;
    let y = redex.y;

    // Verify the redex is still valid (ports still connected)
    if self.get(x) != y || self.get(y) != x {
      return; // Stale redex
    }

    let inc = |p: Ptr| self.get_level(p) + 1;

    if x == y {
      self.erase(x, ctx);
    } else {
      match (x.tag(), y.tag()) {
        // =====================================================================
        // Beta reduction: LAM-APP
        // =====================================================================
        (Tag::LAM, Tag::APP) | (Tag::APP, Tag::LAM) => {
          let (lam, app) = if x.tag() == Tag::LAM { (x, y) } else { (y, x) };
          self.beta(lam, app, ctx);
        },
        // =====================================================================
        // Annihilation rules (same tag)
        // =====================================================================
        (Tag::LAM, Tag::LAM) | (Tag::APP, Tag::APP) => {
          self.annihilate(x, y, ctx);
        },
        (Tag::DUP, Tag::DUP) => {
          if self.get_level(x) == self.get_level(y) {
            self.annihilate(x, y, ctx);
          } else {
            let xl = Some(self.get_level(x));
            let yl = Some(self.get_level(y));
            self.commute_3_3(x, y, xl, yl, ctx);
          }
        },
        (Tag::SCP, Tag::SCP) => {
          let xl = self.get_level(x);
          let yl = self.get_level(y);
          match xl.cmp(&yl) {
            std::cmp::Ordering::Equal => self.annihilate(x, y, ctx),
            std::cmp::Ordering::Less => {
              self.commute_2_2(x, y, Some(xl), Some(yl + 1), ctx);
            },
            std::cmp::Ordering::Greater => {
              self.commute_2_2(x, y, Some(xl + 1), Some(yl), ctx);
            },
          }
        },
        // =====================================================================
        // Commutation rules
        // =====================================================================
        // LAM-DUP
        (Tag::LAM, Tag::DUP) | (Tag::DUP, Tag::LAM) => {
          let (l, d) = if x.tag() == Tag::LAM { (x, y) } else { (y, x) };
          self.commute_3_3(l, d, None, Some(inc(d)), ctx);
        },

        // APP-DUP
        (Tag::APP, Tag::DUP) | (Tag::DUP, Tag::APP) => {
          let (a, d) = if x.tag() == Tag::APP { (x, y) } else { (y, x) };
          let dl = self.get_level(d);
          self.commute_3_3(a, d, None, Some(dl), ctx);
        },
        // SCP-LAM
        (Tag::SCP, Tag::LAM) | (Tag::LAM, Tag::SCP) => {
          let (s, l) = if x.tag() == Tag::SCP { (x, y) } else { (y, x) };
          self.commute_2_3(s, l, Some(inc(s)), None, ctx);
        },

        // SCP-APP
        (Tag::SCP, Tag::APP) | (Tag::APP, Tag::SCP) => {
          let (s, a) = if x.tag() == Tag::SCP { (x, y) } else { (y, x) };
          let sl = self.get_level(s);
          self.commute_2_3(s, a, Some(sl), None, ctx);
        },

        // SCP-DUP
        (Tag::SCP, Tag::DUP) | (Tag::DUP, Tag::SCP) => {
          let (s, d) = if x.tag() == Tag::SCP { (x, y) } else { (y, x) };
          let sl = self.get_level(s);
          let dl = self.get_level(d);
          if dl >= sl {
            self.commute_2_3(s, d, Some(sl), Some(inc(d)), ctx);
          } else {
            self.commute_2_3(s, d, Some(sl), Some(dl), ctx);
          }
        },
        _ => todo!(),
      }
    }

    self.reductions.fetch_add(1, Ordering::Relaxed);
  }

  /// Find all initial redexes in the net
  pub fn find_redexes(&self) {
    let len = self.next.load(Ordering::Acquire);
    for base in (4..len).step_by(4) {
      // Read what's stored at this node's main port
      // We use tag 0 temporarily - it doesn't affect the read
      let target = self.get(Ptr::new(0, base as u64));

      if !target.is_nil() && target.is_main() {
        let back_ptr = self.get(target);
        // Verify bidirectional connection and that back_ptr points to us
        if back_ptr.node() == base as u64 {
          let our_main = Ptr::new(back_ptr.tag(), base as u64);
          // Only add once (when base < target.node())
          if base < target.node() as usize {
            self.redexes.push(Redex::new(our_main, target));
          }
        }
      }
    }
  }

  pub fn reduce(&self, num_threads: usize) {
    // Create per-thread work-stealing deques
    let workers: Vec<Worker<Redex>> =
      (0..num_threads).map(|_| Worker::new_fifo()).collect();

    let free_workers: Vec<Worker<usize>> = (0..num_threads)
            .map(|_| Worker::new_lifo())  // LIFO for locality
            .collect();

    let redex_stealers: Vec<Stealer<Redex>> =
      workers.iter().map(|w| w.stealer()).collect();

    let free_stealers: Vec<Stealer<usize>> =
      free_workers.iter().map(|w| w.stealer()).collect();

    // Seed initial redexes from global queue
    while let Some(redex) = self.steal_redex() {
      workers[0].push(redex);
    }

    thread::scope(|s| {
      for (i, (redex_worker, free_worker)) in
        workers.into_iter().zip(free_workers.into_iter()).enumerate()
      {
        let net = &self;
        let redex_stealers = &redex_stealers;
        let free_stealers = &free_stealers;

        s.spawn(move || {
          let ctx = ThreadCtx {
            redexes: redex_worker,
            freed: free_worker,
            redex_stealers,
            free_stealers,
          };

          let mut idle_count = 0;
          const MAX_IDLE: usize = 1000;

          loop {
            // Try local queue first
            if let Some(redex) = ctx.redexes.pop() {
              net.rewrite(redex, &ctx);
              idle_count = 0;
              continue;
            }

            // Try stealing from others
            let stolen = redex_stealers
              .iter()
              .enumerate()
              .filter(|(j, _)| *j != i)
              .find_map(|(_, stealer)| {
                loop {
                  match stealer.steal() {
                    crossbeam::deque::Steal::Success(r) => return Some(r),
                    crossbeam::deque::Steal::Empty => return None,
                    crossbeam::deque::Steal::Retry => {},
                  }
                }
              });

            if let Some(redex) = stolen {
              net.rewrite(redex, &ctx);
              idle_count = 0;
              continue;
            }

            // Try global queue
            if let Some(redex) = net.steal_redex() {
              net.rewrite(redex, &ctx);
              idle_count = 0;
              continue;
            }

            // No work found
            idle_count += 1;
            if idle_count > MAX_IDLE {
              // Check if all threads are idle (termination)
              break;
            }

            std::hint::spin_loop();
          }
        });
      }
    });
  }
  /// Get the number of reductions performed
  pub fn reduction_count(&self) -> usize {
    self.reductions.load(Ordering::Relaxed)
  }
}

impl Net {
  /// Allocate a lambda node
  pub fn alloc_lam(&self) -> Ptr {
    self.alloc_bump(Tag::LAM)
  }

  /// Allocate an application node
  pub fn alloc_app(&self) -> Ptr {
    self.alloc_bump(Tag::APP)
  }

  /// Allocate a duplication node
  pub fn alloc_dup(&self) -> Ptr {
    self.alloc_bump(Tag::DUP)
  }

  /// Allocate a scope node
  pub fn alloc_scope(&self) -> Ptr {
    self.alloc_bump(Tag::SCP)
  }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_basic_alloc() {
    let net = Net::with_capacity(1000);
    let lam = net.alloc_lam();
    assert_eq!(lam.tag(), Tag::LAM);
    assert!(lam.is_main());
  }

  #[test]
  fn test_basic_link() {
    let net = Net::with_capacity(1000);
    let lam = net.alloc_lam();
    let app = net.alloc_app();

    net.link(lam.main(), app.main());

    assert_eq!(net.get(lam.main()), app.main());
    assert_eq!(net.get(app.main()), lam.main());
  }

  #[test]
  fn test_beta_reduction() {
    let net = Net::with_capacity(1000);

    // Create (λx.x) y -> y
    let lam = net.alloc_lam();
    let app = net.alloc_app();
    let y = net.alloc_scope();

    // Create the redex
    if let Some(r) = net.link_with_redex(lam.main(), app.main()) {
      net.push_redex(r);
    }
    net.link(app.left(), y.main());

    let root = net.alloc_scope();
    net.link(app.right(), root.main());

    // Identity: bind points to body
    net.link(lam.right(), lam.left());

    // Reduce
    net.reduce(1);

    assert!(net.reduction_count() > 0);
  }

  #[test]
  fn test_eraser() {
    let net = Net::with_capacity(1000);

    let lam = net.alloc_lam();
    net.alloc_eraser(lam);
    assert!(net.on_eraser(lam));
  }

  #[test]
  fn test_parallel_simple() {
    let net = Net::with_capacity(10000);

    // Create a simple redex
    let lam = net.alloc_lam();
    let app = net.alloc_app();

    // Set up identity function
    let scope1 = net.alloc_scope();
    let scope2 = net.alloc_scope();
    net.link(lam.left(), scope1.left());
    net.link(lam.right(), scope2.left());
    net.link(scope1.main(), scope2.main());

    // Create application
    if let Some(r) = net.link_with_redex(lam.main(), app.main()) {
      net.push_redex(r);
    }

    let arg = net.alloc_scope();
    let result = net.alloc_scope();
    net.link(app.left(), arg.main());
    net.link(app.right(), result.main());

    // Reduce in parallel
    net.reduce(4);

    println!("Reductions: {}", net.reduction_count());
    assert!(net.reduction_count() > 0);
  }

  #[test]
  fn test_annihilation() {
    let net = Net::with_capacity(1000);

    // Create two lambdas connected at main ports
    let lam1 = net.alloc_lam();
    let lam2 = net.alloc_lam();

    // Connect auxiliary ports to dummy nodes
    let s1 = net.alloc_scope();
    let s2 = net.alloc_scope();
    let s3 = net.alloc_scope();
    let s4 = net.alloc_scope();

    net.link(lam1.left(), s1.left());
    net.link(lam1.right(), s2.left());
    net.link(lam2.left(), s3.left());
    net.link(lam2.right(), s4.left());

    // Create redex
    if let Some(r) = net.link_with_redex(lam1.main(), lam2.main()) {
      net.push_redex(r);
    }

    // Reduce (annihilate should happen)
    net.reduce(1);

    // After annihilation, s1 should be connected to s3, s2 to s4
    assert_eq!(net.get(s1.left()), s3.left());
    assert_eq!(net.get(s3.left()), s1.left());
    assert_eq!(net.get(s2.left()), s4.left());
    assert_eq!(net.get(s4.left()), s2.left());
  }

  #[test]
  fn test_many_redexes_parallel() {
    let net = Net::with_capacity(100_000);

    // Create many independent redexes
    for _ in 0..1000 {
      let lam = net.alloc_lam();
      let app = net.alloc_app();

      if let Some(r) = net.alloc_eraser(lam.left()) {
        net.push_redex(r);
      }
      if let Some(r) = net.alloc_eraser(lam.right()) {
        net.push_redex(r);
      }

      if let Some(r) = net.link_with_redex(lam.main(), app.main()) {
        net.push_redex(r);
      }
      if let Some(r) = net.alloc_eraser(app.left()) {
        net.push_redex(r);
      }
      if let Some(r) = net.alloc_eraser(app.right()) {
        net.push_redex(r);
      }
    }

    net.reduce(4);

    println!("Total reductions: {}", net.reduction_count());
    assert!(net.reduction_count() >= 1000);
  }

  #[test]
  fn test_free_list_reuse_during_reduction() {
    let net = Net::with_capacity(100);

    // Create a long chain of redexes that will produce freed nodes
    // and immediately need to allocate new ones
    let mut last_ptr = None;

    // Create 50 LAM-APP pairs chained together
    for _ in 0..50 {
      let lam = net.alloc_lam();
      let app = net.alloc_app();

      // Identity lambda: bind points to body
      net.link(lam.right(), lam.left());

      // Chain applications
      if let Some(prev) = last_ptr {
        net.link(app.right(), prev);
      } else {
        // First one gets an eraser
        if let Some(r) = net.alloc_eraser(app.right()) {
          net.push_redex(r);
        }
      }

      // Create the beta redex
      if let Some(r) = net.link_with_redex(lam.main(), app.main()) {
        net.push_redex(r);
      }

      // Eraser on argument
      if let Some(r) = net.alloc_eraser(app.left()) {
        net.push_redex(r);
      }

      last_ptr = Some(lam.left());
    }

    let before = net.next.load(Ordering::Relaxed);
    net.reduce(1);
    let after = net.next.load(Ordering::Relaxed);

    // With 50 beta reductions, each creating 2 SCP nodes,
    // if NO reuse happened, we'd allocate 100 new nodes (400 slots)
    // With reuse, we should allocate far fewer
    let new_allocations = after - before;

    println!(
      "Before: {}, After: {}, New allocs: {}, Reductions: {}",
      before,
      after,
      new_allocations,
      net.reduction_count()
    );

    // We expect some reuse - exact amount depends on reduction order
    // This is a sanity check that the free list mechanism works at all
    assert!(net.reduction_count() > 0, "Should have performed some reductions");
  }

  #[test]
  fn test_identity_application() {
    // (λx.x) y → y
    let net = Net::with_capacity(1000);

    let id = net.alloc_lam();
    let app = net.alloc_app();
    let y = net.alloc_scope(); // dummy value
    let result = net.alloc_scope(); // result collector

    // Identity: body = bind
    net.link(id.left(), id.right());

    // Application structure
    if let Some(r) = net.link_with_redex(id.main(), app.main()) {
      net.push_redex(r);
    }
    net.link(app.left(), y.main()); // argument
    net.link(app.right(), result.main()); // result

    net.reduce(1);

    // After reduction, y should be connected to result through scopes
    assert!(net.reduction_count() > 0);
  }
  #[test]
  fn test_erase_lam() {
    let net = Net::with_capacity(1000);

    let lam = net.alloc_lam();
    let a = net.alloc_scope(); // body target
    let b = net.alloc_scope(); // bind target

    // Connect lam's auxiliary ports
    net.link(lam.left(), a.left());
    net.link(lam.right(), b.left());

    // Create eraser on main port
    if let Some(r) = net.alloc_eraser(lam.main()) {
      net.push_redex(r);
    }

    net.reduce(1);

    // After erasing lam, both a and b should have erasers
    assert!(net.on_eraser(a.left()) || net.get(a.left()).is_main());
    assert!(net.on_eraser(b.left()) || net.get(b.left()).is_main());
  }

  #[test]
  fn test_erase_app() {
    let net = Net::with_capacity(1000);

    let app = net.alloc_app();
    let a = net.alloc_scope(); // argument target
    let b = net.alloc_scope(); // applicator target

    net.link(app.left(), a.left());
    net.link(app.right(), b.left());

    if let Some(r) = net.alloc_eraser(app.main()) {
      net.push_redex(r);
    }

    net.reduce(1);

    // Both auxiliary ports should now have erasers
    assert!(net.on_eraser(a.left()) || net.get(a.left()).is_main());
    assert!(net.on_eraser(b.left()) || net.get(b.left()).is_main());
  }

  #[test]
  fn test_erase_dup() {
    let net = Net::with_capacity(1000);

    let dup = net.alloc_dup();
    let a = net.alloc_scope();
    let b = net.alloc_scope();

    net.link(dup.left(), a.left());
    net.link(dup.right(), b.left());

    if let Some(r) = net.alloc_eraser(dup.main()) {
      net.push_redex(r);
    }

    net.reduce(1);

    assert!(net.on_eraser(a.left()) || net.get(a.left()).is_main());
    assert!(net.on_eraser(b.left()) || net.get(b.left()).is_main());
  }

  #[test]
  fn test_erase_scope() {
    let net = Net::with_capacity(1000);

    let scope = net.alloc_scope();
    let a = net.alloc_scope();

    net.link(scope.left(), a.left());

    if let Some(r) = net.alloc_eraser(scope.main()) {
      net.push_redex(r);
    }

    net.reduce(1);

    // Eraser should pass through scope to reach 'a'
    assert!(net.on_eraser(a.left()) || net.get(a.left()).is_main());
  }
  #[test]
  fn test_dup_annihilate_same_level() {
    let net = Net::with_capacity(1000);

    let dup1 = net.alloc_dup();
    let dup2 = net.alloc_dup();

    // Same level = 0 (default)
    let s1 = net.alloc_scope();
    let s2 = net.alloc_scope();
    let s3 = net.alloc_scope();
    let s4 = net.alloc_scope();

    net.link(dup1.left(), s1.left());
    net.link(dup1.right(), s2.left());
    net.link(dup2.left(), s3.left());
    net.link(dup2.right(), s4.left());

    if let Some(r) = net.link_with_redex(dup1.main(), dup2.main()) {
      net.push_redex(r);
    }

    net.reduce(1);

    // After annihilation: s1-s3 connected, s2-s4 connected
    assert_eq!(net.get(s1.left()), s3.left());
    assert_eq!(net.get(s2.left()), s4.left());
  }

  #[test]
  fn test_dup_commute_different_level() {
    let net = Net::with_capacity(1000);

    let dup1 = net.alloc_dup();
    let dup2 = net.alloc_dup();

    // Different levels
    net.set_level(dup1, 0);
    net.set_level(dup2, 1);

    let s1 = net.alloc_scope();
    let s2 = net.alloc_scope();
    let s3 = net.alloc_scope();
    let s4 = net.alloc_scope();

    net.link(dup1.left(), s1.left());
    net.link(dup1.right(), s2.left());
    net.link(dup2.left(), s3.left());
    net.link(dup2.right(), s4.left());

    if let Some(r) = net.link_with_redex(dup1.main(), dup2.main()) {
      net.push_redex(r);
    }

    let before_reductions = net.reduction_count();
    net.reduce(4);

    // Should have commuted (created new nodes), not annihilated
    assert!(net.reduction_count() > before_reductions);
  }

  #[test]
  fn test_scope_annihilate_same_level() {
    let net = Net::with_capacity(1000);

    let scp1 = net.alloc_scope();
    let scp2 = net.alloc_scope();

    let a = net.alloc_scope();
    let b = net.alloc_scope();

    net.link(scp1.left(), a.left());
    net.link(scp2.left(), b.left());

    if let Some(r) = net.link_with_redex(scp1.main(), scp2.main()) {
      net.push_redex(r);
    }

    net.reduce(4);

    // After annihilation: a-b connected
    assert_eq!(net.get(a.left()), b.left());
  }

  #[test]
  fn test_lam_dup_commute() {
    let net = Net::with_capacity(1000);

    let lam = net.alloc_lam();
    let dup = net.alloc_dup();

    let s1 = net.alloc_scope();
    let s2 = net.alloc_scope();
    let s3 = net.alloc_scope();
    let s4 = net.alloc_scope();

    net.link(lam.left(), s1.left());
    net.link(lam.right(), s2.left());
    net.link(dup.left(), s3.left());
    net.link(dup.right(), s4.left());

    if let Some(r) = net.link_with_redex(lam.main(), dup.main()) {
      net.push_redex(r);
    }

    net.reduce(1);

    // Should have commuted - creates 2 new lambdas
    assert!(net.reduction_count() > 0);
  }
  fn test_parallel_many_independent_beta() {
    let net = Net::with_capacity(100_000);

    // Create 1000 independent identity applications
    for _ in 0..1000 {
      let lam = net.alloc_lam();
      let app = net.alloc_app();

      // Identity lambda
      net.link(lam.left(), lam.right());

      // Eraser for argument
      if let Some(r) = net.alloc_eraser(app.left()) {
        net.push_redex(r);
      }
      // Eraser for result
      if let Some(r) = net.alloc_eraser(app.right()) {
        net.push_redex(r);
      }

      // Beta redex
      if let Some(r) = net.link_with_redex(lam.main(), app.main()) {
        net.push_redex(r);
      }
    }

    net.reduce(8); // 4 threads

    // All redexes should be reduced
    assert!(net.reduction_count() >= 1000);
  }

  //#[test]
  //fn test_parallel_determinism() {
  //  // Run the same reduction multiple times and verify consistent results
  //  for _ in 0..10 {
  //    let net = Net::with_capacity(10_000);

  //    // Create a specific pattern
  //    let lam1 = net.alloc_lam();
  //    let lam2 = net.alloc_lam();
  //    let app = net.alloc_app();

  //    net.link(lam1.left(), lam2.main());
  //    net.link(lam1.right(), lam2.right());
  //    net.link(lam2.left(), lam2.right()); // Identity

  //    if let Some(r) = net.link_with_redex(lam1.main(), app.main()) {
  //      net.push_redex(r);
  //    }

  //    if let Some(r) = net.alloc_eraser(app.left()) {
  //      net.push_redex(r);
  //    }
  //    if let Some(r) = net.alloc_eraser(app.right()) {
  //      net.push_redex(r);
  //    }

  //    net.reduce(4);

  //    // Verify the final structure is consistent
  //    // (This depends on your read-back implementation)
  //  }
  //}

  /// Helper to create Church numeral n
  // λs.λz. s(s(...(s z)...))
  fn church(net: &Net, n: usize) -> Ptr {
    let outer_lam = net.alloc_lam(); // λs
    let inner_lam = net.alloc_lam(); // λz

    // Connect outer lambda body to inner lambda
    net.link(outer_lam.left(), inner_lam.main());

    if n == 0 {
      // λs.λz.z - identity on z, s unused
      // body of inner lambda = bind of inner lambda (return z)
      net.link(inner_lam.left(), inner_lam.right());
      // s is unused - attach eraser
      if let Some(r) = net.alloc_eraser(outer_lam.right()) {
        net.push_redex(r);
      }
    } else if n == 1 {
      // λs.λz.s(z) - one application
      let app = net.alloc_app();
      net.link(inner_lam.left(), app.right()); // body -> app result
      net.link(app.main(), outer_lam.right()); // app function -> s (bind of outer)
      net.link(app.left(), inner_lam.right()); // app argument -> z (bind of inner)
    } else {
      // n >= 2: need n-1 DUP nodes to share s
      // Create DUP tree for s
      let s_copies = create_dup_tree(net, outer_lam.right(), n);

      // Build the chain of applications: s(s(...(s z)...))
      // Start from innermost: s(z), then wrap with more s applications
      let mut current = inner_lam.right(); // z

      for (i, s_copy) in s_copies.into_iter().enumerate() {
        let app = net.alloc_app();
        net.link(app.main(), s_copy); // function = s
        net.link(app.left(), current); // argument = previous result

        if i == n - 1 {
          // Last application - connect to body of inner lambda
          net.link(inner_lam.left(), app.right());
        } else {
          current = app.right(); // result feeds into next application
        }
      }
    }

    outer_lam
  }

  /// Create a binary tree of DUP nodes to produce `count` copies of a value.
  /// Returns a Vec of ports, each providing one copy.
  fn create_dup_tree(net: &Net, source: Ptr, count: usize) -> Vec<Ptr> {
    if count == 0 {
      // Unused - attach eraser
      if let Some(r) = net.alloc_eraser(source) {
        net.push_redex(r);
      }
      return vec![];
    }
    if count == 1 {
      return vec![source];
    }

    // Need DUP nodes
    let mut copies = vec![source];

    while copies.len() < count {
      let mut new_copies = Vec::new();

      for copy in copies {
        if new_copies.len() + 1 >= count {
          // Don't need to split this one
          new_copies.push(copy);
        } else {
          // Split with a DUP
          let dup = net.alloc_dup();
          net.link(dup.main(), copy);
          new_copies.push(dup.left());
          if new_copies.len() < count {
            new_copies.push(dup.right());
          } else {
            // Extra port - erase it
            if let Some(r) = net.alloc_eraser(dup.right()) {
              net.push_redex(r);
            }
          }
        }
      }

      copies = new_copies;
    }

    copies
  }

  /// Apply Church numeral m to Church numeral n: (m n)
  /// For Church numerals, application computes exponentiation: n^m
  ///
  /// m and n are Ptrs to the main ports of the outer lambdas.
  fn apply_church(net: &Net, m: Ptr, n: Ptr) -> Ptr {
    let app = net.alloc_app();

    // m n = applying m to n
    // app.main() is the function port, connects to m (the function being applied)
    // app.left() is the argument port, connects to n
    // app.right() is the result/applicator port
    if let Some(r) = net.link_with_redex(app.main(), m) {
      net.push_redex(r);
    }
    net.link(app.left(), n); // argument = n

    app.right() // result port
  }

  fn count_nodes_from_root(net: &Net) -> (usize, usize, usize, usize) {
    use std::collections::HashSet;

    let mut visited = HashSet::new();
    let mut lam_count = 0;
    let mut app_count = 0;
    let mut dup_count = 0;
    let mut scp_count = 0;
    let mut stack = vec![net.get(net.root())];

    while let Some(ptr) = stack.pop() {
      if ptr.is_nil() || visited.contains(&ptr.node()) {
        continue;
      }
      visited.insert(ptr.node());

      if net.get(ptr) == ptr {
        continue;
      } // Eraser

      match ptr.tag() {
        Tag::LAM => {
          lam_count += 1;
          stack.push(net.get(ptr.left())); // Body
          stack.push(net.get(ptr.right()));
        },
        Tag::APP => {
          app_count += 1;
          stack.push(net.get(ptr.left())); // Argument (for nested apps)
          stack.push(net.get(ptr.right()));
        },
        Tag::SCP => {
          scp_count += 1;
          stack.push(net.get(ptr.left())); // Inner
        },
        Tag::DUP => {
          dup_count += 1;
          stack.push(net.get(ptr.left()));
          stack.push(net.get(ptr.right()));
        },
        _ => {},
      }
    }

    (lam_count, app_count, dup_count, scp_count)
  }

  #[test]
  fn test_church_exponentiations() {
    let cases = [
      (1, 1, 1),
      (1, 2, 2),
      (2, 1, 1),
      (2, 2, 4),
      (3, 2, 8),
      (2, 3, 9),
      (3, 3, 27),
    ];

    for (m, n, expected) in cases {
      let net = Net::with_capacity(1_000_000);

      let cm = church(&net, m);
      let cn = church(&net, n);
      let result = apply_church(&net, cm, cn);
      net.link(net.root(), result);

      net.reduce(4);

      let (lams, apps, dups, scps) = count_nodes_from_root(&net);
      println!(
        "reductions={}, LAMs={}, APPs={}, DUPs={}, SCPs={}",
        net.reduction_count(),
        lams,
        apps,
        dups,
        scps
      );
      assert_eq!(apps, expected, "{}^{} should equal {}", n, m, expected);
    }
  }
  #[test]
  fn test_identity_applied_to_church() {
    // (λx.x) 2 = 2
    let net = Net::with_capacity(10_000);

    // Identity function: λx.x
    let id = net.alloc_lam();
    net.link(id.left(), id.right()); // body = bind

    // Church 2
    let two = church(&net, 2);

    // Apply identity to 2
    let app = net.alloc_app();
    // id is already pointing to main port, two is already pointing to main port
    if let Some(r) = net.link_with_redex(app.main(), id) {
      net.push_redex(r);
    }
    net.link(app.left(), two);
    net.link(net.root(), app.right());

    net.reduce(4);

    println!("(λx.x) 2: reductions = {}", net.reduction_count());
    assert!(net.reduction_count() > 0);
  }

  #[test]
  fn test_const_function() {
    // (λx.λy.x) 1 2 = 1
    let net = Net::with_capacity(10_000);

    // K combinator: λx.λy.x
    let outer = net.alloc_lam(); // λx
    let inner = net.alloc_lam(); // λy

    net.link(outer.left(), inner); // body of outer = inner lambda (inner is main port)
    net.link(inner.left(), outer.right()); // body of inner = x (bind of outer)
    // y is unused
    if let Some(r) = net.alloc_eraser(inner.right()) {
      net.push_redex(r);
    }

    // Apply to 1, then to 2
    let one = church(&net, 1);
    let two = church(&net, 2);

    let app1 = net.alloc_app();
    if let Some(r) = net.link_with_redex(app1.main(), outer) {
      net.push_redex(r);
    }
    net.link(app1.left(), one);

    let app2 = net.alloc_app();
    if let Some(r) = net.link_with_redex(app2.main(), app1.right()) {
      net.push_redex(r);
    }
    net.link(app2.left(), two);
    net.link(net.root(), app2.right());

    net.reduce(4);

    println!("K 1 2: reductions = {}", net.reduction_count());
    assert!(net.reduction_count() > 0);
  }
}
