/// The `TopLevel` is an abstraction that allows executing arbitrary Eiur-rs program.
/// Roughly it works as following: user instantiates the `TopLevel` object using one or
/// more functions (of type `Function`) that express one or more finite computations.
/// The `TopLevel` implementation defines an execution algorithm which takes a tuple
/// (`FuncIdx`, `Vec<Value>`) as input and returns `QueryRecord` as output. The input
/// provides information about what exact function to invoke (`FuncIdx`) as well as what
/// data (`Vec<Value>`) to use for this function. The output (`QueryRecord`) contains
/// result of the provided function execution over provided data.
///
pub struct Toplevel {
    pub functions: Vec<Function>,
}

impl Toplevel {
    pub fn get_function(&self, f: FuncIdx) -> &Function {
        &self.functions[f.to_usize()]
    }
}

/// `Function` is an abstraction that expresses some finite computation
pub struct Function {
    pub input_size: u32,
    pub output_size: u32,
    pub body: Block,
}

/// `Prim` defines primitive data types currently supported by Eiur-rs language
#[derive(Clone, Copy)]
pub enum Prim {
    U64(u64),
    Bool(bool),
}

/// `ValIdx` is a pointer to a particular value stored in the inner stack of the
/// `TopLevel` execution algorithm
#[derive(Clone, Copy)]
pub struct ValIdx(pub u32);

impl ValIdx {
    pub fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// `FuncIdx` is a pointer to a function that needs to be executed by a `TopLevel` execution
/// algorithm
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct FuncIdx(pub u32);

impl FuncIdx {
    pub fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// `Op` enumerates operations currently supported by Eiur-rs
pub enum Op {
    Prim(Prim),
    Add(ValIdx, ValIdx),
    Sub(ValIdx, ValIdx),
    Mul(ValIdx, ValIdx),
    And(ValIdx, ValIdx),
    Lt(ValIdx, ValIdx),
    Xor(ValIdx, ValIdx),
    /// A call operation takes 3 elements, function index, arguments, and output size
    Call(FuncIdx, Vec<ValIdx>, u32),
}

/// `SelIdx` serves as a selector of the particular code branch that is executed and
/// requires constraining for the proving system
#[derive(Clone, Copy)]
pub struct SelIdx(pub u32);

impl SelIdx {
    pub fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// `Ctrl` expresses the control flows of the program
pub enum Ctrl {
    If(ValIdx, Block, Block),
    If64(ValIdx, Block, Block),
    Return(SelIdx, Vec<ValIdx>),
}

/// `Block` serves as a body of the user-defined Eiur program / computation. May reference inner
/// blocks via `Ctrl`
pub struct Block {
    pub ops: Vec<Op>,
    pub ctrl: Box<Ctrl>,
    pub return_idents: Vec<SelIdx>,
}
