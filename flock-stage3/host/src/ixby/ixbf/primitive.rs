/// Explicit complete-functional opcodes. These are not native proof opcodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Primitive {
  NatAdd,
  NatSub,
  NatMul,
  NatDiv,
  NatMod,
  NatEq,
  NatLt,
  StringAppend,
  StringLength,
  StringEq,
  Word32Add,
  Word32Sub,
  Word32Mul,
  Word32And,
  Word32Or,
  Word32Xor,
  Word32Shl,
  Word32Shr,
  Word32Rotr,
  Word32Eq,
  Word32Lt,
  Word32ToBytes,
  BytesToWord32,
  Word32ToField,
  FieldAdd,
  FieldSub,
  FieldMul,
  FieldInverse,
  FieldEq,
  FieldToBytes,
  BytesToField,
  ExtensionAdd,
  ExtensionSub,
  ExtensionMul,
  ExtensionInverse,
  ExtensionEq,
  ExtensionPack,
  ExtensionFirst,
  ExtensionSecond,
  BytesLength,
  BytesGet,
  BytesAppend,
  BytesSlice,
  BytesEq,
  Blake3,
  NatToWord32,
  Word32ToNat,
  FieldToNat,
  NatToField,
  ArrayEmpty,
  ArrayLength,
  ArrayGet,
  ArraySet,
  ArrayPush,
  ByteBuilderEmpty,
  ByteBuilderAppend,
  ByteBuilderFreeze,
  ByteBuilderLength,
}

impl Primitive {
  pub const ALL: [Self; 58] = [
    Self::NatAdd,
    Self::NatSub,
    Self::NatMul,
    Self::NatDiv,
    Self::NatMod,
    Self::NatEq,
    Self::NatLt,
    Self::StringAppend,
    Self::StringLength,
    Self::StringEq,
    Self::Word32Add,
    Self::Word32Sub,
    Self::Word32Mul,
    Self::Word32And,
    Self::Word32Or,
    Self::Word32Xor,
    Self::Word32Shl,
    Self::Word32Shr,
    Self::Word32Rotr,
    Self::Word32Eq,
    Self::Word32Lt,
    Self::Word32ToBytes,
    Self::BytesToWord32,
    Self::Word32ToField,
    Self::FieldAdd,
    Self::FieldSub,
    Self::FieldMul,
    Self::FieldInverse,
    Self::FieldEq,
    Self::FieldToBytes,
    Self::BytesToField,
    Self::ExtensionAdd,
    Self::ExtensionSub,
    Self::ExtensionMul,
    Self::ExtensionInverse,
    Self::ExtensionEq,
    Self::ExtensionPack,
    Self::ExtensionFirst,
    Self::ExtensionSecond,
    Self::BytesLength,
    Self::BytesGet,
    Self::BytesAppend,
    Self::BytesSlice,
    Self::BytesEq,
    Self::Blake3,
    Self::NatToWord32,
    Self::Word32ToNat,
    Self::FieldToNat,
    Self::NatToField,
    Self::ArrayEmpty,
    Self::ArrayLength,
    Self::ArrayGet,
    Self::ArraySet,
    Self::ArrayPush,
    Self::ByteBuilderEmpty,
    Self::ByteBuilderAppend,
    Self::ByteBuilderFreeze,
    Self::ByteBuilderLength,
  ];

  pub fn is_conversion(self) -> bool {
    matches!(
      self,
      Self::NatToWord32
        | Self::Word32ToNat
        | Self::FieldToNat
        | Self::NatToField
    )
  }

  pub fn from_opcode(opcode: u8) -> Option<Self> {
    Self::ALL.get(usize::from(opcode)).copied()
  }

  pub fn opcode(self) -> u8 {
    self as u8
  }

  pub fn arity(self) -> usize {
    match self {
      Self::ArrayEmpty | Self::ByteBuilderEmpty => 0,
      Self::StringLength
      | Self::Word32ToBytes
      | Self::BytesToWord32
      | Self::Word32ToField
      | Self::FieldInverse
      | Self::FieldToBytes
      | Self::BytesToField
      | Self::ExtensionInverse
      | Self::ExtensionFirst
      | Self::ExtensionSecond
      | Self::BytesLength
      | Self::Blake3
      | Self::NatToWord32
      | Self::Word32ToNat
      | Self::FieldToNat
      | Self::NatToField
      | Self::ArrayLength
      | Self::ByteBuilderFreeze
      | Self::ByteBuilderLength => 1,
      Self::BytesSlice | Self::ArraySet => 3,
      _ => 2,
    }
  }

  /// Name correspondence only. This does NOT certify primitive semantics,
  /// translate an image, or authorize any native setup/profile upgrade.
  pub fn native_opcode(self) -> Option<u8> {
    const OPCODES: [Option<u8>; 58] = [
      Some(35),
      Some(36),
      Some(37),
      Some(38),
      Some(39),
      Some(40),
      Some(41),
      None,
      None,
      None,
      Some(0),
      Some(1),
      Some(2),
      Some(3),
      Some(4),
      Some(5),
      Some(6),
      Some(7),
      Some(8),
      Some(9),
      Some(10),
      Some(11),
      Some(12),
      Some(13),
      Some(14),
      Some(15),
      Some(16),
      Some(17),
      Some(18),
      Some(19),
      Some(20),
      Some(21),
      Some(22),
      Some(23),
      Some(24),
      Some(25),
      Some(26),
      Some(27),
      Some(28),
      Some(29),
      Some(30),
      Some(31),
      Some(32),
      Some(33),
      Some(34),
      None,
      None,
      None,
      None,
      None,
      None,
      None,
      None,
      None,
      None,
      None,
      None,
      None,
    ];
    OPCODES[usize::from(self.opcode())]
  }
}
